#lang racket/base

(require racket/match racket/list)
(require "private/core.rkt" "private/core-algorithm.rkt")
(require "comparator.rkt")

;; ========================================
;; Priority Queue based on Finger Tree
;; ========================================
;;
;; Persistent priority queue using Hinze & Paterson's split technique:
;; - O(1) peek, count, empty?
;; - O(log n) amortized insert
;; - O(log n) amortized pop (via split + concat)

(struct priority-queue (cmp-fn ft count) #:transparent)

(define pq-empty-measure +inf.0)

(define (make-pq-config cmp-fn)
  (ft:config
    (lambda () pq-empty-measure)
    (match-lambda [(cons priority _) priority])
    (lambda (p0 p1)
      (cond
        [(eqv? p0 pq-empty-measure) p1]
        [(eqv? p1 pq-empty-measure) p0]
        [else (match (cmp-fn p0 p1)
                ['< p0]
                ['> p1]
                ['= p0])]))))

;; ========================================
;; Basic Operations
;; ========================================

(define (priority-queue-empty cmp-fn)
  (priority-queue cmp-fn (ft:empty) 0))

(define (priority-queue-empty? pq)
  (ft:empty? (priority-queue-ft pq)))

(define (pq-count pq)
  (priority-queue-count pq))

;; ========================================
;; Insert - O(log n) amortized
;; ========================================

(define (priority-queue-insert pq priority value)
  (match-define (priority-queue cmp-fn ft cnt) pq)
  (define core (make-pq-config cmp-fn))
  (priority-queue cmp-fn (consR:impl core ft (cons priority value) 0) (add1 cnt)))

;; ========================================
;; Peek - O(1)
;; ========================================

(define (priority-queue-peek pq)
  (match-define (priority-queue cmp-fn ft _) pq)
  (match ft
    [(ft:empty) #f]
    [(ft:single a) a]
    [(ft:deep target _ _ _)
      (find-min ft target)]))

;; O(log n) find using measure
(define (find-min ft target)
  (match ft
    [(ft:single a) a]
    [(ft:deep _ left inner right)
      (cond
        [(eqv? (digit-min left) target)
          (digit-find-target left target)]
        [(eqv? (ft-measure inner) target)
          (find-min-inner inner target)]
        [else
          (digit-find-target right target)])]))

(define (digit-min d)
  (match d
    [(digit:1 a) (car a)]
    [(digit:2 a b) (min (car a) (car b))]
    [(digit:3 a b c) (min (car a) (min (car b) (car c)))]
    [(digit:4 a b c d) (min (min (car a) (car b)) (min (car c) (car d)))]))

(define (ft-measure ft)
  (match ft
    [(ft:empty) pq-empty-measure]
    [(ft:single n) (node-measure n)]
    [(ft:deep v _ _ _) v]))

(define (node-measure n)
  (match n [(node:2 v _ _) v] [(node:3 v _ _ _) v]))

(define (digit-find-target d target)
  (for/or ([e (digit->list d)])
    (and (eqv? (car e) target) e)))

(define (find-min-inner ft target)
  (match ft
    [(ft:single n) (find-min-node n target)]
    [(ft:deep _ left inner right)
      (cond
        [(eqv? (digit-node-min left) target)
          (for/or ([n (digit->list left)])
            (and (eqv? (node-measure n) target)
                 (find-min-node n target)))]
        [(eqv? (ft-measure inner) target)
          (find-min-inner inner target)]
        [else
          (for/or ([n (digit->list right)])
            (and (eqv? (node-measure n) target)
                 (find-min-node n target)))])]))

(define (digit-node-min d)
  (for/fold ([m pq-empty-measure]) ([n (digit->list d)])
    (min-p m (node-measure n))))

(define (min-p a b)
  (if (eqv? a pq-empty-measure) b (if (eqv? b pq-empty-measure) a (min a b))))

(define (find-min-node n target)
  (match n
    [(node:2 _ a b)
      (if (pair? a)
          (if (eqv? (car a) target) a b)
          (or (and (eqv? (node-measure a) target) (find-min-node a target))
              (find-min-node b target)))]
    [(node:3 _ a b c)
      (if (pair? a)
          (cond [(eqv? (car a) target) a]
                [(eqv? (car b) target) b]
                [else c])
          (or (and (eqv? (node-measure a) target) (find-min-node a target))
              (and (eqv? (node-measure b) target) (find-min-node b target))
              (find-min-node c target)))]))

;; ========================================
;; Pop - O(log n) via split (Hinze & Paterson)
;; ========================================
;;
;; Uses the general split operation with a monotonic predicate.
;; The predicate finds where the accumulated minimum equals the target.
;;
;; Algorithm:
;; 1. Get target = global minimum from tree measure (O(1))
;; 2. Split at first position where acc <= target (O(log n))
;; 3. Concat left and right parts (O(log n))
;; Total: O(log n) amortized

(define (priority-queue-pop pq)
  (match-define (priority-queue cmp-fn ft cnt) pq)
  (match ft
    [(ft:empty) (values pq #f)]
    [(ft:single a) (values (priority-queue cmp-fn (ft:empty) 0) a)]
    [(ft:deep target _ _ _)
      (define core (make-pq-config cmp-fn))
      ;; Predicate: accumulated min <= target (becomes true at min element)
      (define (pred acc)
        (or (eqv? acc target)
            (and (not (eqv? acc pq-empty-measure))
                 (not (eqv? target pq-empty-measure))
                 (match (cmp-fn acc target)
                   ['< #t]
                   ['= #t]
                   ['> #f]))))
      ;; Split tree at min element
      (define-values (left elem right) (split:impl core pred ft 0))
      ;; Concat left and right to form remaining tree
      (define new-ft (concat:impl core left right 0))
      (values (priority-queue cmp-fn new-ft (sub1 cnt)) elem)]))

;; ========================================
;; Convenience functions
;; ========================================

(define (priority-queue-peek-value pq)
  (match (priority-queue-peek pq)
    [#f #f]
    [(cons _ v) v]))

(define (priority-queue-peek-priority pq)
  (match (priority-queue-peek pq)
    [#f #f]
    [(cons p _) p]))

(define (priority-queue-pop-value pq)
  (define-values (new-pq elem) (priority-queue-pop pq))
  (values new-pq (and elem (cdr elem))))

(define (list->priority-queue cmp-fn lst)
  (for/fold ([pq (priority-queue-empty cmp-fn)]) ([elem lst])
    (priority-queue-insert pq (car elem) (cdr elem))))

(define (priority-queue->list pq)
  (let loop ([pq pq] [acc '()])
    (define-values (new-pq elem) (priority-queue-pop pq))
    (if elem
        (loop new-pq (cons elem acc))
        (reverse acc))))

;; ========================================
;; Exports
;; ========================================

(provide
  priority-queue
  priority-queue?
  priority-queue-empty
  list->priority-queue
  priority-queue-empty?
  (rename-out [pq-count priority-queue-count])
  priority-queue-insert
  priority-queue-peek
  priority-queue-peek-value
  priority-queue-peek-priority
  priority-queue-pop
  priority-queue-pop-value
  priority-queue->list)
