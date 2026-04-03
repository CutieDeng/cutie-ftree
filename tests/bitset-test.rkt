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
  (define str-bitset? (bitset? "hello"))
  (check-false str-bitset?))

(test-case "bitset-empty?"
  (check-true (bitset-empty? bitset-empty))
  (check-true (bitset-empty? 0))
  (check-false (bitset-empty? 1))
  (define bit0 (bitset 0))
  (define bit0-empty? (bitset-empty? bit0))
  (check-false bit0-empty?))

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
  (define expected (+ 8 32 128))
  (check-equal? (list->bitset* '(3 5 7)) expected))

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
  (define has-100? (bitset-member? s 100))
  (check-false has-100?))

;; ========================================
;; Set Operations
;; ========================================

(test-case "bitset-union"
  (check-equal? (bitset-union (bitset 0 1) (bitset 2 3)) (bitset 0 1 2 3))
  (check-equal? (bitset-union (bitset 0 1) (bitset 1 2)) (bitset 0 1 2))
  (define one (bitset 1))
  (check-equal? (bitset-union 0 one) one))

(test-case "bitset-intersection"
  (check-equal? (bitset-intersection (bitset 0 1 2) (bitset 1 2 3)) (bitset 1 2))
  (check-equal? (bitset-intersection (bitset 0 1) (bitset 2 3)) 0)
  (define s012 (bitset 0 1 2))
  (check-equal? (bitset-intersection s012 s012) s012))

(test-case "bitset-subtract"
  (check-equal? (bitset-subtract (bitset 0 1 2 3) (bitset 1 3)) (bitset 0 2))
  (check-equal? (bitset-subtract (bitset 0 1) (bitset 2 3)) (bitset 0 1))
  (check-equal? (bitset-subtract (bitset 0 1) (bitset 0 1 2)) 0))

;; ========================================
;; Comparison Operations
;; ========================================

(test-case "bitset-equal?"
  (define s01 (bitset 0 1))
  (define s01-equal? (bitset-equal? s01 s01))
  (check-true s01-equal?)
  (check-true (bitset-equal? 0 bitset-empty))
  (define s0 (bitset 0))
  (define s1 (bitset 1))
  (define s0=s1? (bitset-equal? s0 s1))
  (check-false s0=s1?))

(test-case "bitset-subset?"
  (define s012 (bitset 0 1 2))
  (check-true (bitset-subset? 0 s012))
  (check-true (bitset-subset? (bitset 1) s012))
  (check-true (bitset-subset? s012 s012))
  (define s12 (bitset 1 2))
  (define s3 (bitset 3))
  (check-false (bitset-subset? s012 s12))
  (define s3-subset-s012?
    (bitset-subset? s3 s012))
  (check-false s3-subset-s012?))

(test-case "bitset-disjoint?"
  (define s01 (bitset 0 1))
  (define s23 (bitset 2 3))
  (check-true (bitset-disjoint? s01 s23))
  (define s123 (bitset 1 2 3))
  (define s12 (bitset 1 2))
  (check-true (bitset-disjoint? 0 s123))
  (check-false (bitset-disjoint? s01 s12))
  (define s5 (bitset 5))
  (define s5-disjoint? (bitset-disjoint? s5 s5))
  (check-false s5-disjoint?))

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
  (define s (bitset 0 2 5 7))
  (define elems (for/list ([i (in-bitset s)]) i))
  (check-equal? elems '(0 2 5 7))
  (define empty-elems (for/list ([i (in-bitset 0)]) i))
  (define empty-list '())
  (check-equal? empty-elems empty-list))

(test-case "in-bitset/reverse"
  (define s (bitset 0 2 5 7))
  (define elems (for/list ([i (in-bitset/reverse s)]) i))
  (check-equal? elems '(7 5 2 0))
  (define empty-elems (for/list ([i (in-bitset/reverse 0)]) i))
  (define empty-list '())
  (check-equal? empty-elems empty-list))

;; ========================================
;; Conversions
;; ========================================

(test-case "bitset->list"
  (check-equal? (bitset->list 0) '())
  (define s (bitset 0 2 5))
  (define expected '(0 2 5))
  (check-equal? (bitset->list s) expected))

(test-case "bitset->vector"
  (check-equal? (bitset->vector 0) '#())
  (define s (bitset 1 3 5))
  (define expected '#(1 3 5))
  (check-equal? (bitset->vector s) expected))

(test-case "list->bitset"
  (check-equal? (list->bitset '()) 0)
  (define s (bitset 0 2 5))
  (check-equal? (list->bitset '(0 2 5)) s))

(test-case "vector->bitset"
  (check-equal? (vector->bitset '#()) 0)
  (define s (bitset 1 3 5))
  (check-equal? (vector->bitset '#(1 3 5)) s))

(test-case "seq->bitset"
  (define s (bitset 0 1 2 3 4))
  (check-equal? (seq->bitset (in-range 5)) s))

;; ========================================
;; Comprehensions
;; ========================================

(test-case "for/bitset"
  (define i-seq-all (in-range 5))
  (define s-all (for/bitset ([i i-seq-all]) i))
  (define expected-all (bitset 0 1 2 3 4))
  (check-equal? s-all expected-all)
  (define i-seq-even (in-range 10))
  (define s-even (for/bitset ([i i-seq-even] #:when (even? i)) i))
  (define expected-even (bitset 0 2 4 6 8))
  (check-equal? s-even expected-even))

(test-case "for*/bitset"
  (define i-seq (in-range 3))
  (define j-seq (in-range 3))
  (define s
    (for*/bitset ([i i-seq] [j j-seq] #:when (< i j))
      (define value (+ (* i 10) j))
      value))
  (define expected (bitset 1 2 12))
  (check-equal? s expected))

;; ========================================
;; gen:set Protocol
;; ========================================

(test-case "bitset->set wrapper"
  (define s (bitset 0 2 5))
  (define sw (bitset->set s))
  (check-true (set-member? sw 0))
  (check-true (set-member? sw 2))
  (check-false (set-member? sw 1))
  (check-equal? (set-count sw) 3)
  (check-false (set-empty? sw))
  (define empty-sw (bitset->set 0))
  (define empty-sw? (set-empty? empty-sw))
  (check-true empty-sw?))

(test-case "gen:set operations"
  (define s (bitset 0 2))
  (define sw (bitset->set s))
  (define sw2 (set-add sw 5))
  (check-true (set-member? sw2 5))
  (define sw3 (set-remove sw2 0))
  (define has-0? (set-member? sw3 0))
  (check-false has-0?))

;; ========================================
;; Match Expanders
;; ========================================

(test-case "bitset-empty-pat"
  (define (empty-pat? x)
    (match x
      [(bitset-empty-pat) #t]
      [_ #f]
      ))
  (define m0 (empty-pat? 0))
  (check-true m0)
  (define non-empty (bitset 0))
  (define m1 (empty-pat? non-empty))
  (check-false m1))

(test-case "bitset-cons"
  (define expected-rest (bitset 5 7))
  (match-define (bitset-cons min rest) (bitset 2 5 7))
  (check-equal? min 2)
  (check-equal? rest expected-rest)
  ;; Empty set should not match
  (define (cons-pat? x)
    (match x
      [(bitset-cons _ _) #t]
      [_ #f]
      ))
  (define m0 (cons-pat? 0))
  (check-false m0))

(test-case "bitset-rev"
  (define expected-rest (bitset 2 5))
  (match-define (bitset-rev max rest) (bitset 2 5 7))
  (check-equal? max 7)
  (check-equal? rest expected-rest))

(test-case "bitset-has"
  (define s (bitset 0 2 5 7))
  (define (has-pat-0? x)
    (match x
      [(bitset-has 0) #t]
      [_ #f]
      ))
  (define (has-pat-025? x)
    (match x
      [(bitset-has 0 2 5) #t]
      [_ #f]
      ))
  (define (has-pat-1? x)
    (match x
      [(bitset-has 1) #t]
      [_ #f]
      ))
  (define (has-pat-01? x)
    (match x
      [(bitset-has 0 1) #t]
      [_ #f]
      ))
  (define m0 (has-pat-0? s))
  (define m1 (has-pat-025? s))
  (define m2 (has-pat-1? s))
  (define m3 (has-pat-01? s))
  (check-true m0)
  (check-true m1)
  (check-false m2)
  (check-false m3))

(test-case "bitset* as match"
  (define s (bitset 0 2 5 7))
  (define (bitset*-02? x)
    (match x
      [(bitset* 0 2) #t]
      [_ #f]
      ))
  (define (bitset*-13? x)
    (match x
      [(bitset* 1 3) #t]
      [_ #f]
      ))
  (define m0 (bitset*-02? s))
  (define m1 (bitset*-13? s))
  (check-true m0)
  (check-false m1))

(test-case "nested bitset-cons"
  (define expected-rest (bitset 5 7))
  (match-define (bitset-cons a (bitset-cons b rest)) (bitset 1 3 5 7))
  (check-equal? a 1)
  (check-equal? b 3)
  (check-equal? rest expected-rest))

(test-case "recursive iteration with match"
  (define (collect-elements s)
    (match s
      [(bitset-empty-pat) '()]
      [(bitset-cons x xs)
       (define tail (collect-elements xs))
       (cons x tail)
       ]
      ))
  (define sample (bitset 1 3 5 7))
  (define collected (collect-elements sample))
  (define expected '(1 3 5 7))
  (check-equal? collected expected))

(displayln "All bitset tests passed!")
