#lang racket/base

;; ============================================================
;; Bitset: High-performance integer set using bit vectors
;; ============================================================
;;
;; Uses Racket's arbitrary-precision integers as bit vectors.
;; Bit n is set means element n is in the set.
;; Efficient for dense sets of small non-negative integers.
;; ============================================================

(require racket/match racket/sequence)
(require (for-syntax racket/base))

;; ========================================
;; Core Constants
;; ========================================

(define bitset-empty 0)

;; ========================================
;; Predicates
;; ========================================

(define (bitset? v)
  (and (integer? v) (>= v 0))
  ) ; define bitset?

(define (bitset-empty? s)
  (zero? s))

(define bitset-member? bitwise-bit-set?)

(define (bitset-equal? s1 s2)
  (= s1 s2)
  ) ; define bitset-equal?

(define (bitset-subset? s1 s2)
  ;; s1 ⊆ s2 iff s1 ∩ s2 = s1
  (= s1 (bitwise-and s1 s2))
  ) ; define bitset-subset?

(define (bitset-disjoint? s1 s2)
  (zero? (bitwise-and s1 s2))
  ) ; define bitset-disjoint?

;; ========================================
;; Element Operations
;; ========================================

(define (bitset-add s n)
  (bitwise-ior s (arithmetic-shift 1 n))
  ) ; define bitset-add

(define (bitset-remove s n)
  (bitwise-and s (bitwise-not (arithmetic-shift 1 n)))
  ) ; define bitset-remove

;; ========================================
;; Set Operations
;; ========================================

(define bitset-union bitwise-ior)
(define bitset-intersection bitwise-and)

(define (bitset-subtract s1 s2)
  (bitwise-and s1 (bitwise-not s2))
  ) ; define bitset-subtract

;; ========================================
;; Counting
;; ========================================

;; Fast popcount using divide-and-conquer for small integers
;; Falls back to loop for arbitrary precision
(define (bitset-count s)
  (cond
    ;; Fast path for fixnum-sized integers (use bit manipulation tricks)
    [(<= s #xFFFFFFFFFFFFFFFF)  ; 64-bit
     (let* ([s (- s (bitwise-and (arithmetic-shift s -1) #x5555555555555555))]
            [s (+ (bitwise-and s #x3333333333333333)
                  (bitwise-and (arithmetic-shift s -2) #x3333333333333333))]
            [s (bitwise-and (+ s (arithmetic-shift s -4)) #x0F0F0F0F0F0F0F0F)]
            [s (* s #x0101010101010101)])
       (bitwise-and (arithmetic-shift s -56) #xFF))]
    ;; Fallback for bignum: process 64 bits at a time
    [else
     (let loop ([s s] [count 0])
       (if (zero? s)
           count
           (loop (arithmetic-shift s -64)
                 (+ count (bitset-count (bitwise-and s #xFFFFFFFFFFFFFFFF))))
           ) ; if: zero? s
       ) ; let loop
     ]
    ) ; cond: bitset-count strategy
  ) ; define bitset-count

;; ========================================
;; Boundary Operations
;; ========================================

;; Minimum element (rightmost bit)
;; Precondition: s != 0
(define (bitset-min s)
  (sub1 (integer-length (bitwise-and s (- s))))
  ) ; define bitset-min

;; Maximum element (leftmost bit)
;; Precondition: s != 0
(define (bitset-max s)
  (sub1 (integer-length s))
  ) ; define bitset-max

;; ========================================
;; Iteration
;; ========================================

;; Iterate from lowest to highest bit (ascending order)
(define (in-bitset s)
  (make-do-sequence
    (lambda ()
      (initiate-sequence
        #:init-pos s
        #:pos->element bitset-min
        #:continue-with-pos? (compose not zero?)
        #:next-pos (lambda (s)
                     (bitwise-xor s (arithmetic-shift 1 (bitset-min s))))
        ) ; initiate-sequence
      ) ; lambda
    ) ; make-do-sequence
  ) ; define in-bitset

;; Iterate from highest to lowest bit (descending order)
(define (in-bitset/reverse s)
  (make-do-sequence
    (lambda ()
      (initiate-sequence
        #:init-pos s
        #:pos->element bitset-max
        #:continue-with-pos? (compose not zero?)
        #:next-pos (lambda (s)
                     (bitwise-xor s (arithmetic-shift 1 (bitset-max s))))
        ) ; initiate-sequence
      ) ; lambda
    ) ; make-do-sequence
  ) ; define in-bitset/reverse

;; ========================================
;; Conversions
;; ========================================

(define (seq->bitset s)
  (for/fold ([bs 0]) ([i s])
    (bitset-add bs i))
  ) ; define seq->bitset

(define (bitset->list s)
  (for/list ([i (in-bitset s)]) i))

(define (bitset->vector s)
  (list->vector (bitset->list s))
  ) ; define bitset->vector

(define (list->bitset lst)
  (seq->bitset lst))

(define (vector->bitset vec)
  (seq->bitset (in-vector vec))
  ) ; define vector->bitset

;; ========================================
;; Constructors
;; ========================================

;; (bitset 0 2 5) => 37
(define (bitset . elements)
  (list->bitset* elements))

(define (list->bitset* lst)
  (for/fold ([s 0]) ([i lst])
    (bitset-add s i))
  ) ; define list->bitset*

;; ========================================
;; Comprehensions
;; ========================================

(define-syntax (for/bitset stx)
  (syntax-case stx ()
    [(_ clauses body ...)
     #'(for/fold ([s bitset-empty]) clauses
         (bitset-add s (let () body ...))
         )]
    ) ; syntax-case
  ) ; define-syntax for/bitset

(define-syntax (for*/bitset stx)
  (syntax-case stx ()
    [(_ clauses body ...)
     #'(for*/fold ([s bitset-empty]) clauses
         (bitset-add s (let () body ...))
         )]
    ) ; syntax-case
  ) ; define-syntax for*/bitset

;; ========================================
;; gen:set Protocol
;; ========================================

(require racket/set racket/generic)

(struct bitset-wrapper (bits)
  #:transparent
  #:methods gen:set
  [(define (set-member? sw v)
     (and (exact-nonnegative-integer? v)
          (bitset-member? (bitset-wrapper-bits sw) v)))
   (define (set-empty? sw)
     (bitset-empty? (bitset-wrapper-bits sw)))
   (define (set-count sw)
     (bitset-count (bitset-wrapper-bits sw)))
   (define (set-add sw v)
     (bitset-wrapper
      (bitset-add (bitset-wrapper-bits sw) v)))
   (define (set-remove sw v)
     (bitset-wrapper
      (bitset-remove (bitset-wrapper-bits sw) v)))
   (define (set->stream sw)
     (sequence->stream
      (in-bitset (bitset-wrapper-bits sw))))
   (define (in-set sw)
     (in-bitset (bitset-wrapper-bits sw)))]
  #:methods gen:equal+hash
  [(define (equal-proc sw1 sw2 rec)
     (= (bitset-wrapper-bits sw1) (bitset-wrapper-bits sw2)))
   (define (hash-proc sw rec)
     (rec (bitset-wrapper-bits sw)))
   (define (hash2-proc sw rec)
     (rec (bitset-wrapper-bits sw)))])

;; Convert to gen:set compatible wrapper
(define (bitset->set s)
  (bitset-wrapper s))

;; ========================================
;; Match Expanders
;; ========================================

;; Match empty bitset
(define-match-expander bitset-empty-pat
  (lambda (stx)
    (syntax-case stx ()
      [(_) #'(? bitset-empty?)]
      ) ; syntax-case
    ) ; lambda
  ) ; define-match-expander bitset-empty-pat

;; Extract minimum element + rest (like cons for lists)
;; (bitset-cons min-pat rest-pat)
(define (bitset-pop-min-helper s)
  (if (zero? s)
      #f
      (let ([m (bitset-min s)])
        (cons m (bitset-remove s m)))
      ) ; let
  ) ; define bitset-pop-min-helper

(define-match-expander bitset-cons
  (lambda (stx)
    (syntax-case stx ()
      [(_ min-pat rest-pat)
       #'(? bitset?
           (app bitset-pop-min-helper
                (cons min-pat rest-pat)))]
      ) ; syntax-case
    ) ; lambda
  ) ; define-match-expander bitset-cons

;; Extract maximum element + rest
;; (bitset-rev max-pat rest-pat)
(define (bitset-pop-max-helper s)
  (if (zero? s)
      #f
      (let ([m (bitset-max s)])
        (cons m (bitset-remove s m)))
      ) ; let
  ) ; define bitset-pop-max-helper

(define-match-expander bitset-rev
  (lambda (stx)
    (syntax-case stx ()
      [(_ max-pat rest-pat)
       #'(? bitset?
           (app bitset-pop-max-helper
                (cons max-pat rest-pat)))]
      ) ; syntax-case
    ) ; lambda
  ) ; define-match-expander bitset-rev

;; Check if all specified elements exist
;; (bitset-has n1 n2 ...) - matches if all n's are in the set
(define-match-expander bitset-has
  (lambda (stx)
    (syntax-case stx ()
      [(_ n ...)
       #'(? bitset?
           (? (lambda (s)
                (and (bitset-member? s n) ...))))]
      ) ; syntax-case
    ) ; lambda
  ) ; define-match-expander bitset-has

;; bitset* - dual use as constructor and match expander
;; Constructor: (bitset* 0 2 5) => creates bitset
;; Match: (match s [(bitset* 0 2) ...]) => checks membership
(define-match-expander bitset*
  ;; Match transformer
  (lambda (stx)
    (syntax-case stx ()
      [(_ n ...)
       #'(? bitset?
           (? (lambda (s)
                (and (bitset-member? s n) ...))))]
      ) ; syntax-case
    ) ; lambda match-transformer
  ;; Expression transformer (constructor)
  (lambda (stx)
    (syntax-case stx ()
      [(_ elem ...)
       #'(list->bitset* (list elem ...))]
      ) ; syntax-case
    ) ; lambda expression-transformer
  ) ; define-match-expander bitset*

;; ========================================
;; Exports
;; ========================================

;; Constants
(provide bitset-empty)

;; Predicates
(provide bitset? bitset-empty? bitset-member?)
(provide bitset-equal? bitset-subset? bitset-disjoint?)

;; Element operations
(provide bitset-add bitset-remove)

;; Set operations
(provide bitset-union bitset-intersection bitset-subtract)

;; Counting
(provide bitset-count)

;; Boundary
(provide bitset-min bitset-max)

;; Iteration
(provide in-bitset in-bitset/reverse)

;; Conversions
(provide seq->bitset bitset->list bitset->vector)
(provide list->bitset vector->bitset)

;; Constructors
(provide bitset bitset* list->bitset*)

;; Comprehensions
(provide for/bitset for*/bitset)

;; gen:set wrapper
(provide bitset-wrapper bitset-wrapper? bitset-wrapper-bits)
(provide bitset->set)

;; Match expanders
(provide bitset-empty-pat bitset-cons bitset-rev bitset-has)
;; Note: bitset* is both constructor and match expander
