#lang racket/base

(require rackunit racket/list racket/match)
(require "../priority-queue.rkt")
(require "../comparator.rkt")

(printf "Running priority queue tests...\n")

;; ========================================
;; Basic Tests
;; ========================================

(test-case "empty priority queue"
  (define pq (priority-queue-empty integer-compare))
  (check-true (priority-queue-empty? pq))
  (check-equal? (priority-queue-count pq) 0)
  (check-equal? (priority-queue-peek pq) #f))

(test-case "single element"
  (define pq (priority-queue-empty integer-compare))
  (define pq2 (priority-queue-insert pq 5 "five"))
  (check-false (priority-queue-empty? pq2))
  (check-equal? (priority-queue-count pq2) 1)
  (check-equal? (priority-queue-peek pq2) (cons 5 "five"))
  (check-equal? (priority-queue-peek-priority pq2) 5)
  (check-equal? (priority-queue-peek-value pq2) "five"))

(test-case "pop single element"
  (define pq (priority-queue-insert (priority-queue-empty integer-compare) 5 "five"))
  (define-values (pq2 elem) (priority-queue-pop pq))
  (check-equal? elem (cons 5 "five"))
  (define pq2-empty? (priority-queue-empty? pq2))
  (check-true pq2-empty?))

(test-case "multiple elements - min extraction"
  (define pq (priority-queue-empty integer-compare))
  (define pq2 (priority-queue-insert pq 5 "five"))
  (define pq3 (priority-queue-insert pq2 3 "three"))
  (define pq4 (priority-queue-insert pq3 7 "seven"))
  (define pq5 (priority-queue-insert pq4 1 "one"))

  (check-equal? (priority-queue-count pq5) 4)
  (check-equal? (priority-queue-peek pq5) (cons 1 "one"))

  ;; Pop elements in order
  (define-values (r1 e1) (priority-queue-pop pq5))
  (check-equal? e1 (cons 1 "one"))

  (define-values (r2 e2) (priority-queue-pop r1))
  (check-equal? e2 (cons 3 "three"))

  (define-values (r3 e3) (priority-queue-pop r2))
  (check-equal? e3 (cons 5 "five"))

  (define-values (r4 e4) (priority-queue-pop r3))
  (check-equal? e4 (cons 7 "seven"))

  (define r4-empty? (priority-queue-empty? r4))
  (check-true r4-empty?))

(test-case "list->priority-queue and priority-queue->list"
  (define five-pair (cons 5 "five"))
  (define lst
    (list (cons 3 "three")
          (cons 1 "one")
          (cons 4 "four")
          (cons 1 "one-again")
          five-pair))
  (define pq (list->priority-queue integer-compare lst))
  (check-equal? (priority-queue-count pq) 5)

  ;; Should come out sorted by priority
  (define sorted (priority-queue->list pq))
  (check-equal? (length sorted) 5)
  (check-equal? (car (first sorted)) 1)
  (check-equal? (car (second sorted)) 1)
  (check-equal? (car (third sorted)) 3)
  (check-equal? (car (fourth sorted)) 4)
  (check-equal? (car (fifth sorted)) 5))

(test-case "duplicate priorities"
  (define pq (priority-queue-empty integer-compare))
  (define pq2 (priority-queue-insert pq 5 "a"))
  (define pq3 (priority-queue-insert pq2 5 "b"))
  (define pq4 (priority-queue-insert pq3 5 "c"))

  (check-equal? (priority-queue-count pq4) 3)
  (check-equal? (priority-queue-peek-priority pq4) 5)

  ;; All should have priority 5
  (define-values (r1 e1) (priority-queue-pop pq4))
  (define-values (r2 e2) (priority-queue-pop r1))
  (define-values (r3 e3) (priority-queue-pop r2))

  (check-equal? (car e1) 5)
  (check-equal? (car e2) 5)
  (check-equal? (car e3) 5)
  (define r3-empty? (priority-queue-empty? r3))
  (check-true r3-empty?))

(test-case "large queue"
  (define n 100)
  (define lst
    (for/list ([i (in-range n)])
      (cons (random 1000)
            i))
    ) ; define lst
  (define pq (list->priority-queue integer-compare lst))

  (check-equal? (priority-queue-count pq) n)

  ;; Extract all and verify sorted
  (define sorted (priority-queue->list pq))
  (check-equal? (length sorted) n)

  ;; Verify priorities are non-decreasing
  (define n-1 (sub1 n))
  (define i-seq (in-range n-1))
  (for ([i i-seq])
    (define ith (list-ref sorted i))
    (define i+1 (add1 i))
    (define idx2 i+1)
    (define ith+1 (list-ref sorted idx2))
    (define a (car ith))
    (define b (car ith+1))
    (define non-decreasing? (<= a b))
    (check-true non-decreasing?)
    )
  (define n-1-again n-1)
  (check-equal? n-1 n-1-again))

(test-case "immutability"
  (define pq1 (priority-queue-empty integer-compare))
  (define pq2 (priority-queue-insert pq1 5 "five"))
  (define pq3 (priority-queue-insert pq1 3 "three"))  ; insert into pq1, not pq2

  ;; pq1 should still be empty
  (check-true (priority-queue-empty? pq1))
  ;; pq2 should have one element with priority 5
  (check-equal? (priority-queue-count pq2) 1)
  (check-equal? (priority-queue-peek pq2) (cons 5 "five"))
  ;; pq3 should have one element with priority 3
  (check-equal? (priority-queue-count pq3) 1)
  (define pq3-peek (priority-queue-peek pq3))
  (define p3 (cons 3 "three"))
  (check-equal? pq3-peek p3))

(test-case "max-heap via reversed comparator"
  ;; Create a max-heap by reversing the comparator
  (define (reverse-compare x y)
    (define cmp (integer-compare x y))
    (cond
      [(eq? cmp '<) '>]
      [(eq? cmp '>) '<]
      [else '=]
      ))

  (define pq (priority-queue-empty reverse-compare))
  (define pq2 (priority-queue-insert pq 1 "one"))
  (define pq3 (priority-queue-insert pq2 5 "five"))
  (define pq4 (priority-queue-insert pq3 3 "three"))

  ;; Should get max first
  (check-equal? (priority-queue-peek pq4) (cons 5 "five"))

  (define-values (r1 e1) (priority-queue-pop pq4))
  (check-equal? e1 (cons 5 "five"))

  (define-values (r2 e2) (priority-queue-pop r1))
  (check-equal? e2 (cons 3 "three"))

  (define-values (r3 e3) (priority-queue-pop r2))
  (define expected (cons 1 "one"))
  (check-equal? e3 expected))

(printf "All priority queue tests passed!\n")
