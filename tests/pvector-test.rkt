#lang racket/base

(require rackunit racket/list racket/match racket/random)
(require "../pvector.rkt")

(define (sum-pvector-elements l)
  (define len
    (pvector-length l))
  (define i-seq
    (in-range len))
  (for/fold ([sum 0]) ([i i-seq])
    (define v
      (pvector-ref l i))
    (+ sum v)
    ))

(define (repeat-insert pv idx n)
  (define i-seq
    (in-range n))
  (for/fold ([out pv]) ([i i-seq])
    (pvector-insert out idx i)
    ))

;; ========================================
;; Basic cons-right tests
;; ========================================

(test-case "pvector-cons-right adds elements correctly"
  (define l0
    (pvector-empty))
  (define l1 (pvector-cons-right l0 1))
  (define l2 (pvector-cons-right l1 1))
  (define l3 (pvector-cons-right l2 1))
  (define l4 (pvector-cons-right l3 1))
  (define l5 (pvector-cons-right l4 1))
  (define l6 (pvector-cons-right l5 1))
  (define l7 (pvector-cons-right l6 1))
  (define sum-v
    (sum-pvector-elements l7))
  (check-equal? 7 sum-v))

;; ========================================
;; Basic cons-left tests
;; ========================================

(test-case "pvector-cons-left adds elements correctly"
  (define l0
    (pvector-empty))
  (define l1 (pvector-cons-left l0 1))
  (define l2 (pvector-cons-left l1 1))
  (define l3 (pvector-cons-left l2 1))
  (define l4 (pvector-cons-left l3 1))
  (define l5 (pvector-cons-left l4 1))
  (define l6 (pvector-cons-left l5 1))
  (define l7 (pvector-cons-left l6 1))
  (define sum-v
    (sum-pvector-elements l7))
  (check-equal? 7 sum-v))

;; ========================================
;; Split-at tests
;; ========================================

(test-case "pvector-split-at works correctly"
  (define l0
    (pvector-empty))
  (define l1 (pvector-cons-left l0 1))
  (define l2 (pvector-cons-left l1 1))
  (define l3 (pvector-cons-left l2 1))
  (define l4 (pvector-cons-left l3 1))
  (define l5 (pvector-cons-left l4 1))
  (define l6 (pvector-cons-left l5 1))
  (define l7 (pvector-cons-left l6 1))
  (define-values (left right)
    (pvector-split-at l7 4))
  (define sum-v1
    (sum-pvector-elements left))
  (define sum-v2
    (sum-pvector-elements right))
  (check-equal? 4 sum-v1)
  (check-equal? 3 sum-v2))

;; ========================================
;; Insert tests
;; ========================================

(test-case "pvector-insert at position 0"
  (define f0
    (pvector-empty))
  (define f
    (repeat-insert f0 0 10))
  (check-equal? (pvector-length f) 10))

(test-case "pvector-insert at position 1"
  (define f0
    (pvector-cons-left (pvector-empty) 5))
  (define f
    (repeat-insert f0 1 10))
  (check-equal? (pvector-length f) 11))

(test-case "pvector-insert large scale"
  (define f0
    (pvector-cons-left (pvector-empty) 5))
  (define f
    (repeat-insert f0 1 20))
  (check-equal? (pvector-length f) 21))

;; ========================================
;; Additional tests
;; ========================================

(test-case "pvector-empty creates empty vector"
  (check-pred pvector-empty? (pvector-empty))
  (check-equal? (pvector-length (pvector-empty)) 0))

(test-case "pvector-ref and pvector-set work correctly"
  (define src
    '(0 1 2 3 4))
  (define pv
    (list->pvector src))
  (check-equal? (pvector-ref pv 2) 2)
  (define pv2 (pvector-set pv 2 42))
  (check-equal? (pvector-ref pv2 2) 42)
  ;; Original vector unchanged (persistence)
  (check-equal? (pvector-ref pv 2) 2))

(test-case "pvector-split works correctly"
  (define src
    '(0 1 2 3 4 5 6))
  (define pv
    (list->pvector src))
  (define-values (left mid right) (pvector-split pv 3))
  (check-equal? (pvector->list left) '(0 1 2))
  (check-equal? mid 3)
  (define right-list
    (pvector->list right))
  (define expected-right
    '(4 5 6))
  (check-equal? right-list expected-right))

(test-case "pvector-append works correctly"
  (define left-src
    '(1 2 3))
  (define right-src
    '(4 5 6))
  (define pv1
    (list->pvector left-src))
  (define pv2
    (list->pvector right-src))
  (define pv3 (pvector-append pv1 pv2))
  (define pv3-list
    (pvector->list pv3))
  (define expected
    '(1 2 3 4 5 6))
  (check-equal? pv3-list expected))

(test-case "vector conversion roundtrip"
  (define v #(10 20 30 40 50))
  (define pv (vector->pvector v))
  (define v2 (pvector->vector pv))
  (check-equal? v v2))

(test-case "list conversion roundtrip"
  (define lst '(a b c d e))
  (define pv (list->pvector lst))
  (define lst2 (pvector->list pv))
  (check-equal? lst lst2))

(test-case "pvector-delete works correctly"
  (define src
    '(0 1 2 3 4))
  (define pv
    (list->pvector src))
  (define-values (pv2 deleted) (pvector-delete pv 2))
  (check-equal? deleted 2)
  (define pv2-list
    (pvector->list pv2))
  (define expected
    '(0 1 3 4))
  (check-equal? pv2-list expected))

(test-case "pvector-take and pvector-drop work correctly"
  (define src
    '(0 1 2 3 4 5 6 7 8 9))
  (define pv
    (list->pvector src))
  (check-equal? (pvector->list (pvector-take pv 5)) '(0 1 2 3 4))
  (define dropped
    (pvector-drop pv 5))
  (define dropped-list
    (pvector->list dropped))
  (define expected
    '(5 6 7 8 9))
  (check-equal? dropped-list expected))

(test-case "in-pvector sequence iteration"
  (define src
    '(1 2 3 4 5))
  (define pv
    (list->pvector src))
  (define v-seq
    (in-pvector pv))
  (define sum
    (for/fold ([s 0]) ([v v-seq])
      (+ s v)
      ))
  (check-equal? sum 15))

(test-case "large pvector operations"
  (define pv (pvector-empty))
  (define i-seq
    (in-range 1000))
  (set! pv
    (for/fold ([out pv]) ([i i-seq])
      (pvector-cons-right out i)
      ))
  (check-equal? (pvector-length pv) 1000)
  (define i-seq-2
    (in-range 1000))
  (for ([i i-seq-2])
    (define got
      (pvector-ref pv i))
    (check-equal? got i))
  )

(define (list-set* xs idx value)
  (define prefix
    (take xs idx))
  (define next-idx
    (add1 idx))
  (define suffix
    (drop xs next-idx))
  (append prefix (list value) suffix))

(define (list-insert* xs idx value)
  (define prefix
    (take xs idx))
  (define suffix
    (drop xs idx))
  (append prefix (list value) suffix))

(define (list-delete* xs idx)
  (define prefix
    (take xs idx))
  (define next-idx
    (add1 idx))
  (define suffix
    (drop xs next-idx))
  (append prefix suffix))

(define (apply-list-op xs op)
  (match op
    [(list 'noop) xs]
    [(list 'cons-right value)
     (define tail
       (list value))
     (append xs tail)]
    [(list 'cons-left value) (cons value xs)]
    [(list 'insert idx value) (list-insert* xs idx value)]
    [(list 'set idx value) (list-set* xs idx value)]
    [(list 'delete idx) (list-delete* xs idx)]
    ))

(define (apply-pvector-op pv op)
  (match op
    [(list 'noop) pv]
    [(list 'cons-right value) (pvector-cons-right pv value)]
    [(list 'cons-left value) (pvector-cons-left pv value)]
    [(list 'insert idx value) (pvector-insert pv idx value)]
    [(list 'set idx value) (pvector-set pv idx value)]
    [(list 'delete idx)
     (define-values (pv^ _) (pvector-delete pv idx))
     pv^]
    ) ; match: op
  ) ; define apply-pvector-op

(define (generate-seeded-pvector-ops seed steps)
  (random-seed seed)
  (define empty-xs
    '())
  (define empty-ops
    '())
  (let loop ([step 0] [xs empty-xs] [ops empty-ops])
    (cond
      [(= step steps) (reverse ops)]
      [else
       (define len (length xs))
       (define choice (random 8))
       (define op
         (cond
           [(or (= choice 0) (= choice 1))
            (define v
              (random 1000))
            (list 'cons-right v)]
           [(= choice 2)
            (define v
              (random 1000))
            (list 'cons-left v)]
           [(and (= choice 3) (> len 0))
            (define idx
              (random len))
            (define v
              (random 1000))
            (list 'set idx v)]
           [(and (= choice 4) (> len 0))
            (define idx
              (random len))
            (list 'delete idx)]
           [(= choice 5)
            (define idx-bound
              (add1 len))
            (define idx 0)
            (when (> len 0)
              (define rand-idx
                (random idx-bound))
              (set! idx rand-idx))
            (define v
              (random 1000))
            (list 'insert idx v)]
           [else '(noop)]
           ))
       (define next-step
         (add1 step))
       (define next-xs
         (apply-list-op xs op))
       (define next-ops
         (cons op ops))
       (loop next-step next-xs next-ops)]
      ) ; cond: step
    ) ; let loop
  ) ; define generate-seeded-pvector-ops

(test-case "seeded mixed operations regression"
  ;; 回归覆盖：
  ;; 1. 中间子树 insert 后 node:3 重建使用了错误子节点。
  ;; 2. split 右侧分支错误复用了右残片，delete 会重复元素。
  ;; 3. split 中 node 回填左右树时漏传 depth，导致高层 measure 失真。
  (define ops (generate-seeded-pvector-ops 20260328 200))
  (let loop ([remaining ops] [pv (pvector-empty)] [xs '()] [step 0])
    (cond
      [(null? remaining) (void)]
      [else
       (define op (car remaining))
       (define pv^ (apply-pvector-op pv op))
       (define xs^ (apply-list-op xs op))
       (check-equal? (pvector->list pv^) xs^)
       (check-equal? (pvector-length pv^) (length xs^))
       (define n
         (length xs^))
       (define check-seq
         (in-range n))
       (for ([i check-seq])
         (define msg
           (format "step ~a index ~a op ~s" step i op))
         (check-equal?
          (pvector-ref pv^ i)
          (list-ref xs^ i)
          msg))
       (define next-remaining
         (cdr remaining))
       (define next-step
         (add1 step))
       (loop next-remaining pv^ xs^ next-step)]
      ) ; cond: remaining
    ) ; let loop
  ) ; test-case seeded mixed operations regression
