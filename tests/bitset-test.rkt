#lang racket/base

(require rackunit racket/match racket/set)
(require "../bitset.rkt")

;; ========================================
;; Basic Predicates
;; ========================================

(test-case "bitset?"
  (check-true (bitset? 0))
  (check-true (bitset? 1))
  (check-true (bitset? 100))
  (check-false (bitset? -1))
  (check-false (bitset? 1.5))
  (check-false (bitset? "hello")))

(test-case "bitset-empty?"
  (check-true (bitset-empty? bitset-empty))
  (check-true (bitset-empty? 0))
  (check-false (bitset-empty? 1))
  (check-false (bitset-empty? (bitset 0))))

;; ========================================
;; Constructors
;; ========================================

(test-case "bitset constructor"
  (check-equal? (bitset) 0)
  (check-equal? (bitset 0) 1)
  (check-equal? (bitset 1) 2)
  (check-equal? (bitset 0 1) 3)
  (check-equal? (bitset 0 2 5) 37))  ; 100101 = 37

(test-case "list->bitset* constructor"
  (check-equal? (list->bitset* '()) 0)
  (check-equal? (list->bitset* '(0 1 2)) 7)
  (check-equal? (list->bitset* '(3 5 7)) (+ 8 32 128)))

(test-case "bitset* constructor syntax"
  (check-equal? (bitset* 0 1 2) 7)
  (check-equal? (bitset*) 0))

;; ========================================
;; Element Operations
;; ========================================

(test-case "bitset-add"
  (check-equal? (bitset-add 0 0) 1)
  (check-equal? (bitset-add 0 3) 8)
  (check-equal? (bitset-add 1 1) 3)
  (check-equal? (bitset-add 1 0) 1))  ; already present

(test-case "bitset-remove"
  (check-equal? (bitset-remove 1 0) 0)
  (check-equal? (bitset-remove 3 1) 1)
  (check-equal? (bitset-remove 7 0) 6)
  (check-equal? (bitset-remove 0 5) 0))  ; not present

(test-case "bitset-member?"
  (define s (bitset 0 2 5))
  (check-true (bitset-member? s 0))
  (check-true (bitset-member? s 2))
  (check-true (bitset-member? s 5))
  (check-false (bitset-member? s 1))
  (check-false (bitset-member? s 3))
  (check-false (bitset-member? s 100)))

;; ========================================
;; Set Operations
;; ========================================

(test-case "bitset-union"
  (check-equal? (bitset-union (bitset 0 1) (bitset 2 3)) (bitset 0 1 2 3))
  (check-equal? (bitset-union (bitset 0 1) (bitset 1 2)) (bitset 0 1 2))
  (check-equal? (bitset-union 0 (bitset 1)) (bitset 1)))

(test-case "bitset-intersection"
  (check-equal? (bitset-intersection (bitset 0 1 2) (bitset 1 2 3)) (bitset 1 2))
  (check-equal? (bitset-intersection (bitset 0 1) (bitset 2 3)) 0)
  (check-equal? (bitset-intersection (bitset 0 1 2) (bitset 0 1 2)) (bitset 0 1 2)))

(test-case "bitset-subtract"
  (check-equal? (bitset-subtract (bitset 0 1 2 3) (bitset 1 3)) (bitset 0 2))
  (check-equal? (bitset-subtract (bitset 0 1) (bitset 2 3)) (bitset 0 1))
  (check-equal? (bitset-subtract (bitset 0 1) (bitset 0 1 2)) 0))

;; ========================================
;; Comparison Operations
;; ========================================

(test-case "bitset-equal?"
  (check-true (bitset-equal? (bitset 0 1) (bitset 0 1)))
  (check-true (bitset-equal? 0 bitset-empty))
  (check-false (bitset-equal? (bitset 0) (bitset 1))))

(test-case "bitset-subset?"
  (check-true (bitset-subset? 0 (bitset 0 1 2)))
  (check-true (bitset-subset? (bitset 1) (bitset 0 1 2)))
  (check-true (bitset-subset? (bitset 0 1 2) (bitset 0 1 2)))
  (check-false (bitset-subset? (bitset 0 1 2) (bitset 1 2)))
  (check-false (bitset-subset? (bitset 3) (bitset 0 1 2))))

(test-case "bitset-disjoint?"
  (check-true (bitset-disjoint? (bitset 0 1) (bitset 2 3)))
  (check-true (bitset-disjoint? 0 (bitset 1 2 3)))
  (check-false (bitset-disjoint? (bitset 0 1) (bitset 1 2)))
  (check-false (bitset-disjoint? (bitset 5) (bitset 5))))

;; ========================================
;; Counting
;; ========================================

(test-case "bitset-count"
  (check-equal? (bitset-count 0) 0)
  (check-equal? (bitset-count 1) 1)
  (check-equal? (bitset-count (bitset 0 1 2)) 3)
  (check-equal? (bitset-count (bitset 0 5 10 15 20)) 5)
  (check-equal? (bitset-count 255) 8))  ; 11111111

;; ========================================
;; Boundary Operations
;; ========================================

(test-case "bitset-min"
  (check-equal? (bitset-min (bitset 5)) 5)
  (check-equal? (bitset-min (bitset 0 5 10)) 0)
  (check-equal? (bitset-min (bitset 3 7 15)) 3))

(test-case "bitset-max"
  (check-equal? (bitset-max (bitset 5)) 5)
  (check-equal? (bitset-max (bitset 0 5 10)) 10)
  (check-equal? (bitset-max (bitset 3 7 15)) 15))

;; ========================================
;; Iteration
;; ========================================

(test-case "in-bitset"
  (check-equal? (for/list ([i (in-bitset (bitset 0 2 5 7))]) i)
                '(0 2 5 7))
  (check-equal? (for/list ([i (in-bitset 0)]) i)
                '()))

(test-case "in-bitset/rev"
  (check-equal? (for/list ([i (in-bitset/rev (bitset 0 2 5 7))]) i)
                '(7 5 2 0))
  (check-equal? (for/list ([i (in-bitset/rev 0)]) i)
                '()))

;; ========================================
;; Conversions
;; ========================================

(test-case "bitset->list"
  (check-equal? (bitset->list 0) '())
  (check-equal? (bitset->list (bitset 0 2 5)) '(0 2 5)))

(test-case "bitset->vector"
  (check-equal? (bitset->vector 0) '#())
  (check-equal? (bitset->vector (bitset 1 3 5)) '#(1 3 5)))

(test-case "list->bitset"
  (check-equal? (list->bitset '()) 0)
  (check-equal? (list->bitset '(0 2 5)) (bitset 0 2 5)))

(test-case "vector->bitset"
  (check-equal? (vector->bitset '#()) 0)
  (check-equal? (vector->bitset '#(1 3 5)) (bitset 1 3 5)))

(test-case "seq->bitset"
  (check-equal? (seq->bitset (in-range 5)) (bitset 0 1 2 3 4)))

;; ========================================
;; Comprehensions
;; ========================================

(test-case "for/bitset"
  (check-equal? (for/bitset ([i (in-range 5)]) i)
                (bitset 0 1 2 3 4))
  (check-equal? (for/bitset ([i (in-range 10)] #:when (even? i)) i)
                (bitset 0 2 4 6 8)))

(test-case "for*/bitset"
  (check-equal? (for*/bitset ([i (in-range 3)] [j (in-range 3)] #:when (< i j))
                  (+ (* i 10) j))
                (bitset 1 2 12)))

;; ========================================
;; gen:set Protocol
;; ========================================

(test-case "bitset->set wrapper"
  (define sw (bitset->set (bitset 0 2 5)))
  (check-true (set-member? sw 0))
  (check-true (set-member? sw 2))
  (check-false (set-member? sw 1))
  (check-equal? (set-count sw) 3)
  (check-false (set-empty? sw))
  (check-true (set-empty? (bitset->set 0))))

(test-case "gen:set operations"
  (define sw (bitset->set (bitset 0 2)))
  (define sw2 (set-add sw 5))
  (check-true (set-member? sw2 5))
  (define sw3 (set-remove sw2 0))
  (check-false (set-member? sw3 0)))

;; ========================================
;; Match Expanders
;; ========================================

(test-case "bitset-empty-pat"
  (check-true (match 0 [(bitset-empty-pat) #t] [_ #f]))
  (check-false (match (bitset 0) [(bitset-empty-pat) #t] [_ #f])))

(test-case "bitset-cons"
  (match (bitset 2 5 7)
    [(bitset-cons min rest)
     (check-equal? min 2)
     (check-equal? rest (bitset 5 7))]
    [_ (fail "should match")])
  ;; Empty set should not match
  (check-false (match 0 [(bitset-cons _ _) #t] [_ #f])))

(test-case "bitset-rev"
  (match (bitset 2 5 7)
    [(bitset-rev max rest)
     (check-equal? max 7)
     (check-equal? rest (bitset 2 5))]
    [_ (fail "should match")]))

(test-case "bitset-has"
  (define s (bitset 0 2 5 7))
  (check-true (match s [(bitset-has 0) #t] [_ #f]))
  (check-true (match s [(bitset-has 0 2 5) #t] [_ #f]))
  (check-false (match s [(bitset-has 1) #t] [_ #f]))
  (check-false (match s [(bitset-has 0 1) #t] [_ #f])))

(test-case "bitset* as match"
  (define s (bitset 0 2 5 7))
  (check-true (match s [(bitset* 0 2) #t] [_ #f]))
  (check-false (match s [(bitset* 1 3) #t] [_ #f])))

(test-case "nested bitset-cons"
  (match (bitset 1 3 5 7)
    [(bitset-cons a (bitset-cons b rest))
     (check-equal? a 1)
     (check-equal? b 3)
     (check-equal? rest (bitset 5 7))]
    [_ (fail "should match")]))

(test-case "recursive iteration with match"
  (define (collect-elements s)
    (match s
      [(bitset-empty-pat) '()]
      [(bitset-cons x xs) (cons x (collect-elements xs))]))
  (check-equal? (collect-elements (bitset 1 3 5 7)) '(1 3 5 7)))

(displayln "All bitset tests passed!")
