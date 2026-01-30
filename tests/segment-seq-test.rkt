#lang racket/base

(require rackunit racket/list)
(require "../segment-seq.rkt")

(printf "Running segment-seq tests...\n")

;; ========================================
;; Sum Segment Tree Tests
;; ========================================

(test-case "empty sum sequence"
  (define ss (segment-seq-sum))
  (check-true (segment-seq-empty? ss))
  (check-equal? (segment-seq-length ss) 0)
  (check-equal? (segment-seq-aggregate ss) 0))

(test-case "build from list - sum"
  (define ss (list->segment-seq '(1 2 3 4 5) 0 +))
  (check-equal? (segment-seq-length ss) 5)
  (check-equal? (segment-seq-aggregate ss) 15)
  (check-equal? (segment-seq->list ss) '(1 2 3 4 5)))

(test-case "random access"
  (define ss (list->segment-seq '(10 20 30 40 50) 0 +))
  (check-equal? (segment-seq-ref ss 0) 10)
  (check-equal? (segment-seq-ref ss 2) 30)
  (check-equal? (segment-seq-ref ss 4) 50))

(test-case "set element"
  (define ss (list->segment-seq '(1 2 3 4 5) 0 +))
  (define ss2 (segment-seq-set ss 2 100))
  (check-equal? (segment-seq-ref ss2 2) 100)
  (check-equal? (segment-seq-aggregate ss2) (+ 1 2 100 4 5))
  ;; Original unchanged
  (check-equal? (segment-seq-ref ss 2) 3))

(test-case "range query - sum"
  (define ss (list->segment-seq '(1 2 3 4 5 6 7 8 9 10) 0 +))
  ;; Full range
  (check-equal? (segment-seq-range-query ss 0 10) 55)
  ;; Single element
  (check-equal? (segment-seq-range-query ss 0 1) 1)
  (check-equal? (segment-seq-range-query ss 4 5) 5)
  ;; Subranges
  (check-equal? (segment-seq-range-query ss 0 5) 15)   ; 1+2+3+4+5
  (check-equal? (segment-seq-range-query ss 5 10) 40)  ; 6+7+8+9+10
  (check-equal? (segment-seq-range-query ss 2 7) 25)   ; 3+4+5+6+7
  ;; Empty range
  (check-equal? (segment-seq-range-query ss 3 3) 0))

(test-case "insert"
  (define ss (list->segment-seq '(1 2 3) 0 +))
  ;; Insert at beginning
  (define ss1 (segment-seq-insert ss 0 100))
  (check-equal? (segment-seq->list ss1) '(100 1 2 3))
  (check-equal? (segment-seq-aggregate ss1) 106)
  ;; Insert at end
  (define ss2 (segment-seq-insert ss 3 100))
  (check-equal? (segment-seq->list ss2) '(1 2 3 100))
  ;; Insert in middle
  (define ss3 (segment-seq-insert ss 1 100))
  (check-equal? (segment-seq->list ss3) '(1 100 2 3)))

(test-case "delete"
  (define ss (list->segment-seq '(1 2 3 4 5) 0 +))
  (define ss2 (segment-seq-delete ss 2))
  (check-equal? (segment-seq->list ss2) '(1 2 4 5))
  (check-equal? (segment-seq-aggregate ss2) 12))

(test-case "push/pop operations"
  (define ss (segment-seq-sum))
  (define ss1 (segment-seq-push-back ss 1))
  (define ss2 (segment-seq-push-back ss1 2))
  (define ss3 (segment-seq-push-front ss2 0))
  (check-equal? (segment-seq->list ss3) '(0 1 2))

  (define-values (ss4 v1) (segment-seq-pop-back ss3))
  (check-equal? v1 2)
  (check-equal? (segment-seq->list ss4) '(0 1))

  (define-values (ss5 v2) (segment-seq-pop-front ss4))
  (check-equal? v2 0)
  (check-equal? (segment-seq->list ss5) '(1)))

(test-case "split and concat"
  (define ss (list->segment-seq '(1 2 3 4 5) 0 +))
  (define-values (left right) (segment-seq-split ss 2))
  (check-equal? (segment-seq->list left) '(1 2))
  (check-equal? (segment-seq->list right) '(3 4 5))
  (check-equal? (segment-seq-aggregate left) 3)
  (check-equal? (segment-seq-aggregate right) 12)

  ;; Concat back
  (define ss2 (segment-seq-concat left right))
  (check-equal? (segment-seq->list ss2) '(1 2 3 4 5)))

;; ========================================
;; Min Segment Tree Tests
;; ========================================

(test-case "min segment tree"
  (define ss (list->segment-seq '(5 2 8 1 9 3) +inf.0 min))
  (check-equal? (segment-seq-aggregate ss) 1)
  (check-= (segment-seq-range-query ss 0 3) 2 0.001)  ; min(5,2,8)
  (check-= (segment-seq-range-query ss 3 6) 1 0.001)  ; min(1,9,3)
  (check-= (segment-seq-range-query ss 1 4) 1 0.001)) ; min(2,8,1)

(test-case "max segment tree"
  (define ss (list->segment-seq '(5 2 8 1 9 3) -inf.0 max))
  (check-equal? (segment-seq-aggregate ss) 9)
  (check-= (segment-seq-range-query ss 0 3) 8 0.001)  ; max(5,2,8)
  (check-= (segment-seq-range-query ss 3 6) 9 0.001)  ; max(1,9,3)
  (check-= (segment-seq-range-query ss 2 5) 9 0.001)) ; max(8,1,9)

;; ========================================
;; Custom Aggregation Tests
;; ========================================

(test-case "product aggregation"
  (define ss (list->segment-seq '(1 2 3 4) 1 *))
  (check-equal? (segment-seq-aggregate ss) 24)
  (check-equal? (segment-seq-range-query ss 0 2) 2)   ; 1*2
  (check-equal? (segment-seq-range-query ss 1 4) 24)) ; 2*3*4

(test-case "custom extract function"
  ;; Store pairs, aggregate by second element
  (define ss (list->segment-seq
               '((a . 10) (b . 20) (c . 30))
               0
               +
               cdr))
  (check-equal? (segment-seq-aggregate ss) 60)
  (check-equal? (segment-seq-range-query ss 0 2) 30))

;; ========================================
;; Large Scale Test
;; ========================================

(test-case "large sequence"
  (define n 1000)
  (define lst (for/list ([i (in-range n)]) i))
  (define ss (list->segment-seq lst 0 +))

  (check-equal? (segment-seq-length ss) n)
  (check-equal? (segment-seq-aggregate ss) (/ (* (sub1 n) n) 2))

  ;; Random access
  (check-equal? (segment-seq-ref ss 500) 500)

  ;; Range query: sum of [100, 200)
  (define expected (for/sum ([i (in-range 100 200)]) i))
  (check-equal? (segment-seq-range-query ss 100 200) expected))

(test-case "immutability"
  (define ss1 (list->segment-seq '(1 2 3) 0 +))
  (define ss2 (segment-seq-set ss1 1 100))
  (define ss3 (segment-seq-insert ss1 0 999))

  ;; ss1 unchanged
  (check-equal? (segment-seq->list ss1) '(1 2 3))
  (check-equal? (segment-seq->list ss2) '(1 100 3))
  (check-equal? (segment-seq->list ss3) '(999 1 2 3)))

(printf "All segment-seq tests passed!\n")
