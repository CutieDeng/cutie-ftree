#lang racket/base

(require rackunit racket/list racket/match racket/random)
(require "../pvector.rkt")

;; ========================================
;; Basic cons-right tests
;; ========================================

(test-case "pvector-cons-right adds elements correctly"
  (let ([l (pvector-empty)])
    (set! l (pvector-cons-right l 1))
    (set! l (pvector-cons-right l 1))
    (set! l (pvector-cons-right l 1))
    (set! l (pvector-cons-right l 1))
    (set! l (pvector-cons-right l 1))
    (set! l (pvector-cons-right l 1))
    (set! l (pvector-cons-right l 1))
    (define sum-v (for/fold ([sum 0]) ([i (in-range (pvector-length l))])
      (define v (pvector-ref l i))
      (+ sum v)))
    (check-equal? 7 sum-v)))

;; ========================================
;; Basic cons-left tests
;; ========================================

(test-case "pvector-cons-left adds elements correctly"
  (let ([l (pvector-empty)])
    (set! l (pvector-cons-left l 1))
    (set! l (pvector-cons-left l 1))
    (set! l (pvector-cons-left l 1))
    (set! l (pvector-cons-left l 1))
    (set! l (pvector-cons-left l 1))
    (set! l (pvector-cons-left l 1))
    (set! l (pvector-cons-left l 1))
    (define sum-v (for/fold ([sum 0]) ([i (in-range (pvector-length l))])
      (define v (pvector-ref l i))
      (+ sum v)))
    (check-equal? 7 sum-v)))

;; ========================================
;; Split-at tests
;; ========================================

(test-case "pvector-split-at works correctly"
  (let ([l (pvector-empty)])
    (set! l (pvector-cons-left l 1))
    (set! l (pvector-cons-left l 1))
    (set! l (pvector-cons-left l 1))
    (set! l (pvector-cons-left l 1))
    (set! l (pvector-cons-left l 1))
    (set! l (pvector-cons-left l 1))
    (set! l (pvector-cons-left l 1))
    (define-values (l1 l2) (pvector-split-at l 4))
    (define sum-v1 (for/fold ([sum 0]) ([i (in-range (pvector-length l1))])
      (define v (pvector-ref l1 i))
      (+ sum v)))
    (define sum-v2 (for/fold ([sum 0]) ([i (in-range (pvector-length l2))])
      (define v (pvector-ref l2 i))
      (+ sum v)))
    (check-equal? 4 sum-v1)
    (check-equal? 3 sum-v2)))

;; ========================================
;; Insert tests
;; ========================================

(test-case "pvector-insert at position 0"
  (let ([f (pvector-empty)])
    (set! f (for/fold ([f f]) ([i (in-range 10)]) (pvector-insert f 0 i)))
    (check-equal? (pvector-length f) 10)))

(test-case "pvector-insert at position 1"
  (let ([f (pvector-cons-left (pvector-empty) 5)])
    (set! f (for/fold ([f f]) ([i (in-range 10)]) (pvector-insert f 1 i)))
    (check-equal? (pvector-length f) 11)))

(test-case "pvector-insert large scale"
  (let ([f (pvector-cons-left (pvector-empty) 5)])
    (set! f (for/fold ([f f]) ([i (in-range 20)]) (pvector-insert f 1 i)))
    (check-equal? (pvector-length f) 21)))

;; ========================================
;; Additional tests
;; ========================================

(test-case "pvector-empty creates empty vector"
  (check-pred pvector-empty? (pvector-empty))
  (check-equal? (pvector-length (pvector-empty)) 0))

(test-case "pvector-ref and pvector-set work correctly"
  (define pv (list->pvector '(0 1 2 3 4)))
  (check-equal? (pvector-ref pv 2) 2)
  (define pv2 (pvector-set pv 2 42))
  (check-equal? (pvector-ref pv2 2) 42)
  ;; Original vector unchanged (persistence)
  (check-equal? (pvector-ref pv 2) 2))

(test-case "pvector-split works correctly"
  (define pv (list->pvector '(0 1 2 3 4 5 6)))
  (define-values (left mid right) (pvector-split pv 3))
  (check-equal? (pvector->list left) '(0 1 2))
  (check-equal? mid 3)
  (check-equal? (pvector->list right) '(4 5 6)))

(test-case "pvector-append works correctly"
  (define pv1 (list->pvector '(1 2 3)))
  (define pv2 (list->pvector '(4 5 6)))
  (define pv3 (pvector-append pv1 pv2))
  (check-equal? (pvector->list pv3) '(1 2 3 4 5 6)))

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
  (define pv (list->pvector '(0 1 2 3 4)))
  (define-values (pv2 deleted) (pvector-delete pv 2))
  (check-equal? deleted 2)
  (check-equal? (pvector->list pv2) '(0 1 3 4)))

(test-case "pvector-take and pvector-drop work correctly"
  (define pv (list->pvector '(0 1 2 3 4 5 6 7 8 9)))
  (check-equal? (pvector->list (pvector-take pv 5)) '(0 1 2 3 4))
  (check-equal? (pvector->list (pvector-drop pv 5)) '(5 6 7 8 9)))

(test-case "in-pvector sequence iteration"
  (define pv (list->pvector '(1 2 3 4 5)))
  (define sum (for/fold ([s 0]) ([v (in-pvector pv)]) (+ s v)))
  (check-equal? sum 15))

(test-case "large pvector operations"
  (define pv (pvector-empty))
  (set! pv (for/fold ([pv pv]) ([i (in-range 1000)])
    (pvector-cons-right pv i)))
  (check-equal? (pvector-length pv) 1000)
  (for ([i (in-range 1000)])
    (check-equal? (pvector-ref pv i) i)))

(define (list-set* xs idx value)
  (append (take xs idx) (list value) (drop xs (add1 idx))))

(define (apply-list-op xs op)
  (match op
    [(list 'noop) xs]
    [(list 'cons-right value) (append xs (list value))]
    [(list 'cons-left value) (cons value xs)]
    [(list 'insert idx value) (append (take xs idx) (list value) (drop xs idx))]
    [(list 'set idx value) (list-set* xs idx value)]
    [(list 'delete idx) (append (take xs idx) (drop xs (add1 idx)))]))

(define (apply-pvector-op pv op)
  (match op
    [(list 'noop) pv]
    [(list 'cons-right value) (pvector-cons-right pv value)]
    [(list 'cons-left value) (pvector-cons-left pv value)]
    [(list 'insert idx value) (pvector-insert pv idx value)]
    [(list 'set idx value) (pvector-set pv idx value)]
    [(list 'delete idx)
      (define-values (pv^ _) (pvector-delete pv idx))
      pv^]))

(define (generate-seeded-pvector-ops seed steps)
  (random-seed seed)
  (let loop ([step 0] [xs '()] [ops '()])
    (cond
      [(= step steps) (reverse ops)]
      [else
       (define len (length xs))
       (define choice (random 8))
       (define op
         (cond
           [(or (= choice 0) (= choice 1))
            (list 'cons-right (random 1000))]
           [(= choice 2)
            (list 'cons-left (random 1000))]
           [(and (= choice 3) (> len 0))
            (list 'set (random len) (random 1000))]
           [(and (= choice 4) (> len 0))
            (list 'delete (random len))]
           [(= choice 5)
            (list 'insert (if (= len 0) 0 (random (add1 len))) (random 1000))]
           [else '(noop)]))
       (loop (add1 step) (apply-list-op xs op) (cons op ops))]
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
       (for ([i (in-range (length xs^))])
         (check-equal?
          (pvector-ref pv^ i)
          (list-ref xs^ i)
          (format "step ~a index ~a op ~s" step i op)))
       (loop (cdr remaining) pv^ xs^ (add1 step))]
      ) ; cond: remaining
    ) ; let loop
  ) ; test-case seeded mixed operations regression
