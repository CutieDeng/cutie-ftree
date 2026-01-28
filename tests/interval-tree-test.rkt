#lang racket/base

(require rackunit racket/list racket/match)
(require "../interval-tree.rkt")

(printf "Running interval tree tests...\n")

;; ========================================
;; Basic Tests
;; ========================================

(test-case "empty interval tree"
  (define it (interval-tree-empty))
  (check-true (interval-tree-empty? it))
  (check-equal? (interval-tree-search it 0 10) '()))

(test-case "single interval"
  (define it (interval-tree-empty))
  (define it2 (interval-tree-insert it 5 10 "a"))
  (check-false (interval-tree-empty? it2))

  ;; Query that overlaps
  (check-equal? (length (interval-tree-search it2 7 8)) 1)
  (check-equal? (interval-tree-search it2 7 8) '((5 10 "a")))

  ;; Query at boundary
  (check-equal? (length (interval-tree-search it2 10 15)) 1)
  (check-equal? (length (interval-tree-search it2 0 5)) 1)

  ;; Query that doesn't overlap
  (check-equal? (interval-tree-search it2 11 15) '())
  (check-equal? (interval-tree-search it2 0 4) '()))

(test-case "multiple non-overlapping intervals"
  (define it (interval-tree-empty))
  (define it2 (interval-tree-insert it 1 3 "a"))
  (define it3 (interval-tree-insert it2 5 7 "b"))
  (define it4 (interval-tree-insert it3 9 11 "c"))

  ;; Point queries
  (check-equal? (length (interval-tree-search it4 2 2)) 1)
  (check-equal? (length (interval-tree-search it4 6 6)) 1)
  (check-equal? (length (interval-tree-search it4 10 10)) 1)
  (check-equal? (length (interval-tree-search it4 4 4)) 0)

  ;; Range query that hits one
  (check-equal? (length (interval-tree-search it4 0 2)) 1)

  ;; Range query that hits all
  (check-equal? (length (interval-tree-search it4 0 15)) 3))

(test-case "overlapping intervals"
  (define it (interval-tree-empty))
  (define it2 (interval-tree-insert it 1 10 "a"))
  (define it3 (interval-tree-insert it2 5 15 "b"))
  (define it4 (interval-tree-insert it3 8 12 "c"))

  ;; Query in overlap region
  (define results (interval-tree-search it4 9 9))
  (check-equal? (length results) 3)

  ;; Query that hits two
  (check-equal? (length (interval-tree-search it4 2 6)) 2)

  ;; Query that hits one
  (check-equal? (length (interval-tree-search it4 13 14)) 1))

(test-case "point query"
  (define it (interval-tree-empty))
  (define it2 (interval-tree-insert it 0 10 "a"))
  (define it3 (interval-tree-insert it2 5 15 "b"))

  (check-equal? (length (interval-tree-search-point it3 3)) 1)
  (check-equal? (length (interval-tree-search-point it3 7)) 2)
  (check-equal? (length (interval-tree-search-point it3 12)) 1)
  (check-equal? (length (interval-tree-search-point it3 20)) 0))

(test-case "list conversion"
  (define lst '((1 5 "a") (3 7 "b") (10 20 "c")))
  (define it (list->interval-tree lst))

  (check-equal? (length (interval-tree->list it)) 3)
  (check-equal? (length (interval-tree-search it 4 4)) 2)
  (check-equal? (length (interval-tree-search it 15 15)) 1))

(test-case "large tree"
  (define n 100)
  ;; Create n intervals: [i, i+10]
  (define it
    (for/fold ([t (interval-tree-empty)]) ([i (in-range n)])
      (interval-tree-insert t i (+ i 10) i)))

  ;; Query at point 50 should hit intervals 40-50
  (define results (interval-tree-search-point it 50))
  (check-equal? (length results) 11)

  ;; Query at point 5 should hit intervals 0-5
  (check-equal? (length (interval-tree-search-point it 5)) 6)

  ;; Range query
  (check-true (> (length (interval-tree-search it 45 55)) 10)))

(test-case "immutability"
  (define it1 (interval-tree-empty))
  (define it2 (interval-tree-insert it1 1 5 "a"))
  (define it3 (interval-tree-insert it1 10 20 "b"))  ; insert into it1, not it2

  ;; it1 should still be empty
  (check-true (interval-tree-empty? it1))
  ;; it2 should have interval [1,5]
  (check-equal? (length (interval-tree-search it2 3 3)) 1)
  (check-equal? (length (interval-tree-search it2 15 15)) 0)
  ;; it3 should have interval [10,20]
  (check-equal? (length (interval-tree-search it3 3 3)) 0)
  (check-equal? (length (interval-tree-search it3 15 15)) 1))

(test-case "boundary conditions"
  (define it (interval-tree-empty))
  (define it2 (interval-tree-insert it 5 10 "a"))

  ;; Exact boundary overlap
  (check-equal? (length (interval-tree-search it2 10 10)) 1)
  (check-equal? (length (interval-tree-search it2 5 5)) 1)

  ;; Just outside
  (check-equal? (length (interval-tree-search it2 11 11)) 0)
  (check-equal? (length (interval-tree-search it2 4 4)) 0)

  ;; Query interval touching boundary
  (check-equal? (length (interval-tree-search it2 10 15)) 1)
  (check-equal? (length (interval-tree-search it2 0 5)) 1))

(test-case "negative intervals"
  (define it (interval-tree-empty))
  (define it2 (interval-tree-insert it -10 -5 "neg"))
  (define it3 (interval-tree-insert it2 -3 3 "cross"))
  (define it4 (interval-tree-insert it3 5 10 "pos"))

  (check-equal? (length (interval-tree-search it4 -7 -7)) 1)
  (check-equal? (length (interval-tree-search it4 0 0)) 1)
  (check-equal? (length (interval-tree-search it4 7 7)) 1)
  (check-equal? (length (interval-tree-search it4 -2 2)) 1)
  (check-equal? (length (interval-tree-search it4 -20 20)) 3))

(printf "All interval tree tests passed!\n")
