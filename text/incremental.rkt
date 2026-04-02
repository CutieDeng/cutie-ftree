#lang racket/base

;; text/incremental: O(k log n) incremental insert/delete
;;
;; Key insight: boundary flag changes propagate locally until a "stable point"
;; - word-start: stable after whitespace
;; - para-start: stable after newline
;;
;; Complexity: O(k log n) where k = number of elements needing update
;; In practice, k is small (typically < 10 for most edits)

(require racket/match)
(require "../private/core.rkt" "../private/core-algorithm.rkt")
(require "measure.rkt" "elem.rkt")

;; ========================================
;; Text Core Configuration
;; ========================================

(define text-core (ft:config
  text-measure-empty
  text-elem->measure
  text-measure-append))

;; ========================================
;; Context State for Propagation
;; ========================================

(struct boundary-ctx
  (prev-char           ; previous character or #f
   after-blank-line?   ; are we after a blank line?
   line-has-content?)  ; does current line have non-whitespace?
  #:transparent)

(define (boundary-ctx-initial)
  (boundary-ctx #f #t #f))

(define (boundary-ctx-advance ctx char)
  (match-define (boundary-ctx _ abl? lhc?) ctx)
  (define ws? (ascii-whitespace? char))
  (define newline? (char=? char #\newline))
  (define has-content? (not ws?))
  (define next-abl?
    (cond
      [newline? (not lhc?)]
      [else (and abl? ws?)]
      ))
  (define next-lhc-base (or lhc? has-content?))
  (define next-lhc?
    (if newline?
        #f
        next-lhc-base))
  (boundary-ctx
    char
    next-abl?
    next-lhc?))

(define (make-elem-from-ctx ctx char)
  (match-define (boundary-ctx prev-char abl? _) ctx)
  (define ws? (ascii-whitespace? char))
  (define prev-ws?
    (if prev-char
        (ascii-whitespace? prev-char)
        #f))
  (define word-start?
    (cond
      [ws? #f]
      [prev-char prev-ws?]
      [else #t]
      ))
  (define word-start^^ word-start?)
  (define para-start?
    (and (not ws?) abl?))
  (text-elem
    char
    word-start^^
    (char=? char #\newline)
    para-start?))

;; ========================================
;; Stability Detection
;; ========================================

;; Stable when flags match, or after newline (para resets)
(define (stable-point? old-elem new-elem)
  (define new-word? (text-elem-word-start? new-elem))
  (define new-para? (text-elem-para-start? new-elem))
  (define new-line-end? (text-elem-line-end? new-elem))
  (define same-word?
    (eq? (text-elem-word-start? old-elem)
         new-word?))
  (define same-para?
    (eq? (text-elem-para-start? old-elem)
         new-para?))
  (or (and same-word? same-para?)
      new-line-end?))

(define (elem-changed? old-elem new-elem)
  (define new-word? (text-elem-word-start? new-elem))
  (define new-para? (text-elem-para-start? new-elem))
  (define same-word?
    (eq? (text-elem-word-start? old-elem)
         new-word?))
  (define same-para?
    (eq? (text-elem-para-start? old-elem)
         new-para?))
  (if same-word?
      (not same-para?)
      #t))

;; ========================================
;; Context Extraction (O(log n) amortized)
;; ========================================

;; Extract context by scanning backwards from position
;; We need: prev-char, after-blank-line?, line-has-content?
(define (extract-context-at ft pos)
  (define ft-m (measure:ft text-core ft 0))
  (define len (text-measure-chars ft-m))
  (if (= pos 0)
      (boundary-ctx-initial)
      (let ()
        ;; Get prev-char
        (define prev-pos (sub1 pos))
        (define prev-char (get-char-at ft prev-pos))

        ;; Scan backwards to determine after-blank-line? and line-has-content?
        ;; This is the expensive part - worst case O(n) but typically short
        (define-values (abl? lhc?)
          (scan-backwards-for-state ft pos))

        (define ctx^ (boundary-ctx prev-char abl? lhc?))
        ctx^))
  ) ; define extract-context-at

;; Scan backwards to find paragraph state
;; Returns: (values after-blank-line? line-has-content?)
(define (scan-start-state)
  (values #t #f))

(define (scan-backwards-for-state ft pos)
  (let loop ([p (sub1 pos)]
             [found-newline? #f]
             [line-content? #f])
    (cond
      [(< p 0)
        ;; Reached start of text
        (cond
          [found-newline?
           (values (not line-content?) #f)]
          [else
           (scan-start-state)]
          )]
      [else
        (define c (get-char-at ft p))
        (define ws? (ascii-whitespace? c))
        (define newline? (char=? c #\newline))
        (cond
          [newline?
           (cond
             [found-newline?
              (values #t line-content?)]    ; blank line
             [else
              (loop (sub1 p) #t #f)]
             )]
          [ws?
           (loop (sub1 p) found-newline? line-content?)]
          [else
           ;; Found content
           (if found-newline?
               (values #f line-content?)    ; non-blank line before
               (loop (sub1 p) found-newline? #t))
           ] ; cond else
          ) ; cond newline/ws/else
        ] ; outer cond else
      ) ; cond p<0/else
    )) ; let loop

;; Get character at position (O(log n))
(define (get-char-at ft pos)
  (define elem (get-elem-at ft pos 0))
  (text-elem-char elem))

(define (get-elem-at ft pos depth)
  (match ft
    [(ft:empty) (error 'get-elem-at "empty tree")]
    [(ft:single node) (get-elem-in-node node pos depth)]
    [(ft:deep _ lhs inner rhs)
      (define lhs-m (measure:digit text-core lhs depth))
      (define lhs-sz (text-measure-chars lhs-m))
      (define inner-depth (add1 depth))
      (define inner-m (measure:ft text-core inner inner-depth))
      (define inner-sz (text-measure-chars inner-m))
      (define split-pos (+ lhs-sz inner-sz))
      (define rhs-pos (- pos lhs-sz inner-sz))
      (cond
        [(< pos lhs-sz) (get-elem-in-digit lhs pos depth)]
        [(< pos split-pos)
         (get-elem-at inner (- pos lhs-sz) inner-depth)]
        [else
         (get-elem-in-digit rhs rhs-pos depth)]
        ) ; cond
      ] ; ft:deep
    )) ; match ft

(define (get-elem-in-digit digit pos depth)
  (match digit
    [(digit:1 a) (get-elem-in-node a pos depth)]
    [(digit:2 a b)
      (define a-m (measure:node text-core a depth))
      (define a-sz (text-measure-chars a-m))
      (cond
        [(< pos a-sz)
         (get-elem-in-node a pos depth)]
        [else
         (define pos^ (- pos a-sz))
         (get-elem-in-node b pos^ depth)]
        )]
    [(digit:3 a b c)
      (define a-m (measure:node text-core a depth))
      (define b-m (measure:node text-core b depth))
      (define a-sz (text-measure-chars a-m))
      (define b-sz (text-measure-chars b-m))
      (define b-end (+ a-sz b-sz))
      (cond
        [(< pos a-sz) (get-elem-in-node a pos depth)]
        [(< pos b-end)
         (let ()
           (define pos^ (- pos a-sz))
           (define result (get-elem-in-node b pos^ depth))
           result)]
        [else
         (let ()
          (define pos^ (- pos a-sz b-sz))
           (define result (get-elem-in-node c pos^ depth))
           result)
         ] ; cond else
        )]
    [(digit:4 a b c d)
      (define a-m (measure:node text-core a depth))
      (define b-m (measure:node text-core b depth))
      (define c-m (measure:node text-core c depth))
      (define a-sz (text-measure-chars a-m))
      (define b-sz (text-measure-chars b-m))
      (define c-sz (text-measure-chars c-m))
      (define b-end (+ a-sz b-sz))
      (define c-end (+ b-end c-sz))
      (cond
        [(< pos a-sz) (get-elem-in-node a pos depth)]
        [(< pos b-end)
         (let ()
           (define pos^ (- pos a-sz))
           (define result (get-elem-in-node b pos^ depth))
           result)]
        [(< pos c-end)
         (let ()
           (define pos^ (- pos a-sz b-sz))
           (define result (get-elem-in-node c pos^ depth))
           result)]
        [else
         (let ()
           (define pos^ (- pos a-sz b-sz c-sz))
           (define result (get-elem-in-node d pos^ depth))
           result)
         ] ; cond else
        ) ; cond
      ] ; digit:4
    )) ; match digit

(define (get-elem-in-node node pos depth)
  (match depth
    [0 node]
    [_
     (define sub-depth (sub1 depth))
     (match node
       [(node:2 _ a b)
       (define a-m (measure:node text-core a sub-depth))
       (define a-sz (text-measure-chars a-m))
       (cond
         [(< pos a-sz)
          (get-elem-in-node a pos sub-depth)]
         [else
          (define pos^ (- pos a-sz))
          (get-elem-in-node b pos^ sub-depth)]
         )]
       [(node:3 _ a b c)
        (define a-m (measure:node text-core a sub-depth))
        (define b-m (measure:node text-core b sub-depth))
        (define a-sz (text-measure-chars a-m))
        (define b-sz (text-measure-chars b-m))
        (define b-end (+ a-sz b-sz))
        (cond
          [(< pos a-sz) (get-elem-in-node a pos sub-depth)]
          [(< pos b-end)
           (let ()
             (define pos^ (- pos a-sz))
             (define result (get-elem-in-node b pos^ sub-depth))
             result)]
          [else
           (let ()
             (define pos^ (- pos a-sz b-sz))
             (define result (get-elem-in-node c pos^ sub-depth))
             result)
           ] ; cond else
          )
        ] ; match node:3
       ) ; match node
     ] ; depth>0
    )) ; match depth

;; ========================================
;; Simple List-based Implementation
;; Convert to list, modify, convert back.
;; This is O(n) but correct. Optimizations can come later.
;; ========================================

;; Convert ft to list of elements
(define (ft->list ft)
  (ft->elem-list ft 0))

(define (ft->elem-list ft depth)
  (match ft
    [(ft:empty) '()]
    [(ft:single node) (node->elem-list node depth)]
    [(ft:deep _ lhs inner rhs)
      (define lhs-elems (digit->elem-list lhs depth))
      (define inner-depth (add1 depth))
      (define inner-elems (ft->elem-list inner inner-depth))
      (define rhs-elems (digit->elem-list rhs depth))
      (define lhs+inner (append lhs-elems inner-elems))
      (define all-elems (append lhs+inner rhs-elems))
      all-elems
      ] ; ft:deep
    )) ; match ft

(define (digit->elem-list digit depth)
  (match digit
    [(digit:1 a) (node->elem-list a depth)]
    [(digit:2 a b)
     (define a-elems (node->elem-list a depth))
     (define b-elems (node->elem-list b depth))
     (append a-elems b-elems)]
    [(digit:3 a b c)
     (define a-elems (node->elem-list a depth))
     (define b-elems (node->elem-list b depth))
     (define c-elems (node->elem-list c depth))
     (append a-elems b-elems c-elems)]
    [(digit:4 a b c d)
     (define a-elems (node->elem-list a depth))
     (define b-elems (node->elem-list b depth))
     (define c-elems (node->elem-list c depth))
     (define d-elems (node->elem-list d depth))
     (define abc-elems (append a-elems b-elems c-elems))
     (define all-elems (append abc-elems d-elems))
     all-elems
     ] ; digit:4
    )) ; match digit

(define (node->elem-list node depth)
  (match depth
    [0 (list node)]
    [_
     (define sub-depth (sub1 depth))
     (match node
       [(node:2 _ a b)
        (define a-elems (node->elem-list a sub-depth))
        (define b-elems (node->elem-list b sub-depth))
        (append a-elems b-elems)]
       [(node:3 _ a b c)
        (define a-elems (node->elem-list a sub-depth))
        (define b-elems (node->elem-list b sub-depth))
       (define c-elems (node->elem-list c sub-depth))
       (define ab-elems (append a-elems b-elems))
       (append ab-elems c-elems)]
       ) ; match node
     ] ; match depth>0
    )) ; match depth

;; Convert list of elements to ft
(define (list->ft elems)
  (match elems
    ['() (ft:empty)]
    [(list a) (ft:single a)]
    [_
     (define empty-ft (ft:empty))
     (for/fold ([ft empty-ft]) ([elem elems])
       (consR:impl text-core ft elem 0))
     ] ; match _
    )) ; match elems

;; Split list at position
(define (list-take lst n)
  (if (or (= n 0) (null? lst))
      '()
      (let ()
        (define head (car lst))
        (define tail (cdr lst))
        (define n^ (sub1 n))
        (define rest (list-take tail n^))
        (cons head rest)
        ) ; let
      ) ; if
  ) ; define list-take

(define (list-drop lst n)
  (if (or (= n 0) (null? lst))
      lst
      (let ()
        (define tail (cdr lst))
        (define n^ (sub1 n))
        (list-drop tail n^)
        ) ; let
      ) ; if
  ) ; define list-drop

;; ========================================
;; Incremental Insert (O(n) for now)
;; ========================================

(define (incremental-insert ft pos char)
  (define ft-m (measure:ft text-core ft 0))
  (define len (text-measure-chars ft-m))
  (cond
    [(= len 0)
      (define elem (make-elem-from-ctx (boundary-ctx-initial) char))
      (values (ft:single elem) 1)]
    [else
      ;; Get context at insertion point
      (define ctx (extract-context-at ft pos))

      ;; Create new element
      (define new-elem (make-elem-from-ctx ctx char))

      ;; Convert to list, insert, and propagate
      (define elems (ft->list ft))
      (define prefix (list-take elems pos))
      (define suffix (list-drop elems pos))

      ;; Propagate through suffix
      (define new-ctx (boundary-ctx-advance ctx char))
      (define-values (updated-suffix update-count)
        (propagate-through-list new-ctx suffix))

      ;; Rebuild tree
      (define new-elems (append prefix (list new-elem) updated-suffix))
      (define new-ft (list->ft new-elems))
      (values new-ft (add1 update-count))
      ] ; cond else
    ))

;; ========================================
;; Incremental Delete (O(n) for now)
;; ========================================

(define (incremental-delete ft pos)
  (define ft-m (measure:ft text-core ft 0))
  (define len (text-measure-chars ft-m))
  (cond
    [(= len 1)
      (values (ft:empty) 0)]
    [else
      ;; Get context at deletion point
      (define ctx (extract-context-at ft pos))

      ;; Convert to list and remove element
      (define elems (ft->list ft))
      (define prefix (list-take elems pos))
      (define after-pos (add1 pos))
      (define suffix (list-drop elems after-pos))  ; skip the deleted element

      ;; Propagate through suffix
      (define-values (updated-suffix update-count)
        (propagate-through-list ctx suffix))

      ;; Rebuild tree
      (define new-elems (append prefix updated-suffix))
      (define new-ft (list->ft new-elems))
      (values new-ft update-count)
      ] ; cond else
    ))

;; ========================================
;; Propagation Through List (O(k))
;; ========================================

;; Propagate boundary updates through list, stopping at stable point
(define (propagate-through-list ctx elems)
  (let loop ([ctx ctx]
             [remaining elems]
             [result '()]
             [count 0]
             [prev-changed? #t])
    (match remaining
      ['()
        (values (reverse result) count)]
      [(cons old-elem rest)
        (define char (text-elem-char old-elem))
        (define new-elem (make-elem-from-ctx ctx char))
        (define new-ctx (boundary-ctx-advance ctx char))
        (define changed? (elem-changed? old-elem new-elem))

        (cond
          ;; If stable and nothing changed, append rest unchanged
          [(and (not prev-changed?) (not changed?) (stable-point? old-elem new-elem))
            (values (append (reverse result) remaining) count)]
          [else
            (loop new-ctx
                  rest
                  (cons new-elem result)
                  (if changed? (add1 count) count)
                  changed?)
            ] ; cond else
          ) ; cond
        ] ; match cons
      ) ; match remaining
    )) ; let loop

;; ========================================
;; Exports
;; ========================================

(provide
  text-core
  incremental-insert
  incremental-delete
  boundary-ctx
  boundary-ctx-initial
  boundary-ctx-advance
  extract-context-at
  propagate-through-list)
