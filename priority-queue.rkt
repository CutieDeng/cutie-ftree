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
        [else
         (match (cmp-fn p0 p1)
                ['< p0]
                ['> p1]
                ['= p0]
                ) ; match: cmp-fn result
         ]
        ) ; cond: empty measure cases
      ) ; lambda: combine
    ) ; ft:config
  ) ; define make-pq-config

;; ========================================
;; Basic Operations
;; ========================================

(define (priority-queue-empty cmp-fn)
  (priority-queue cmp-fn (ft:empty) 0))

(define (priority-queue-empty? pq)
  (define ft (priority-queue-ft pq))
  (ft:empty? ft))

(define (pq-count pq)
  (priority-queue-count pq))

;; ========================================
;; Insert - O(log n) amortized
;; ========================================

(define (priority-queue-insert pq priority value)
  (match-define (priority-queue cmp-fn ft cnt) pq)
  (define core (make-pq-config cmp-fn))
  (define elem (cons priority value))
  (define ft^ (consR:impl core ft elem 0))
  (define cnt^ (add1 cnt))
  (priority-queue cmp-fn ft^ cnt^))

;; ========================================
;; Peek - O(1)
;; ========================================

(define (priority-queue-peek pq)
  (match-define (priority-queue cmp-fn ft _) pq)
  (match ft
    [(ft:empty) #f]
    [(ft:single a) a]
    [(ft:deep target _ _ _)
      (find-min ft target)
    ] ; ft:deep
    )) ; match ft

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
          (digit-find-target right target)]
        ) ; cond
      ] ; ft:deep
    )) ; match ft

(define (digit-min d)
  (match d
    [(digit:1 a) (car a)]
    [(digit:2 a b)
     (define a^ (car a))
     (define b^ (car b))
     (min a^ b^)]
    [(digit:3 a b c)
     (define a^ (car a))
     (define b^ (car b))
     (define c^ (car c))
     (define bc-min (min b^ c^))
     (min a^ bc-min)]
    [(digit:4 a b c d)
     (define a^ (car a))
     (define b^ (car b))
     (define c^ (car c))
     (define d^ (car d))
     (define ab-min (min a^ b^))
     (define cd-min (min c^ d^))
     (define min^ (min ab-min cd-min))
     min^]
    ))

(define (ft-measure ft)
  (match ft
    [(ft:empty) pq-empty-measure]
    [(ft:single n) (node-measure n)]
    [(ft:deep v _ _ _) v]
    ))

(define (node-measure n)
  (match n
    [(node:2 v _ _) v]
    [(node:3 v _ _ _) v]
    ))

(define (digit-find-target d target)
  (define elems (digit->list d))
  (define (target? e)
    (eqv? (car e) target))
  (for/or ([e elems])
    (define match? (target? e))
    (if match? e #f))
  ) ; for/or: scan digit elements

(define (find-min-inner ft target)
  (match ft
    [(ft:single n) (find-min-node n target)]
    [(ft:deep _ left inner right)
     (cond
       [(eqv? (digit-node-min left) target)
       (define left-nodes (digit->list left))
       (for/or ([n left-nodes])
         (if (eqv? (node-measure n) target)
             (find-min-node n target)
             #f)
         )]
       [(eqv? (ft-measure inner) target)
        (find-min-inner inner target)]
       [else
       (define right-nodes (digit->list right))
       (for/or ([n right-nodes])
         (if (eqv? (node-measure n) target)
             (find-min-node n target)
             #f)
         )]
       ) ; cond: choose search region
     ]
    ) ; match: ft
  ) ; define find-min-inner

(define (digit-node-min d)
  (define nodes (digit->list d))
  (for/fold ([m pq-empty-measure]) ([n nodes])
    (define n^ (node-measure n))
    (define m^ (min-p m n^))
    m^))

(define (min-p a b)
  (cond
    [(eqv? a pq-empty-measure) b]
    [(eqv? b pq-empty-measure) a]
    [else (min a b)]
    ))

(define (find-min-node n target)
  (match n
    [(node:2 _ a b)
     (if (pair? a)
         (if (eqv? (car a) target) a b)
         (let ()
           (define in-a?
             (eqv? (node-measure a) target))
           (if in-a?
               (find-min-node a target)
               (find-min-node b target))
           ) ; let
         )] ; if: pair? a
    [(node:3 _ a b c)
     (if (pair? a)
         (cond
           [(eqv? (car a) target) a]
           [(eqv? (car b) target) b]
           [else c]
           ) ; cond: leaf node:3
         (or (and (eqv? (node-measure a) target)
                  (find-min-node a target))
             (and (eqv? (node-measure b) target)
                  (find-min-node b target))
             (find-min-node c target))
         )] ; if: pair? a
    ) ; match: n
  ) ; define find-min-node

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
        (define cmp-res (cmp-fn acc target))
        (define cmp-ok?
          (match cmp-res
            ['< #t]
            ['= #t]
            ['> #f]
            ))
        (define acc-is-target? (eqv? acc target))
        (define bounded?
          (and (not (eqv? acc pq-empty-measure))
               (not (eqv? target pq-empty-measure))
               cmp-ok?))
        (or acc-is-target? bounded?)
        )
      ;; Split tree at min element
      (define-values (left elem right) (split:impl core pred ft 0))
      ;; Concat left and right to form remaining tree
      (define new-ft (concat:impl core left right 0))
      (values (priority-queue cmp-fn new-ft (sub1 cnt)) elem)]
    ) ; match: ft
  ) ; define priority-queue-pop

;; ========================================
;; Convenience functions
;; ========================================

(define (priority-queue-peek-value pq)
  (match (priority-queue-peek pq)
    [#f #f]
    [(cons _ v) v]
    ))

(define (priority-queue-peek-priority pq)
  (match (priority-queue-peek pq)
    [#f #f]
    [(cons p _) p]
    ))

(define (priority-queue-pop-value pq)
  (define-values (new-pq elem) (priority-queue-pop pq))
  (define value (if elem (cdr elem) #f))
  (values new-pq value))

(define (list->priority-queue cmp-fn lst)
  (define pq0 (priority-queue-empty cmp-fn))
  (for/fold ([pq pq0])
            ([elem lst])
    (define priority (car elem))
    (define value (cdr elem))
    (define pq^ (priority-queue-insert pq priority value))
    pq^))

(define (priority-queue->list pq)
  (define acc0 '())
  (let loop ([pq pq] [acc acc0])
    (define-values (new-pq elem) (priority-queue-pop pq))
    (if elem
        (loop new-pq (cons elem acc))
        (let ()
          (define out (reverse acc))
          out)
        )
    ) ; if: elem
  ) ; let loop

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
