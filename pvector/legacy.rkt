#lang racket/base

;; ========================================
;; Legacy pvector implementations using digit-add-list
;; These are kept for compatibility and feature completeness
;; but are slower than the default zero-allocation implementations
;; ========================================

(require racket/match)
(require "../private/core.rkt" "../private/core-algorithm.rkt")

(define core/size (ft:config (lambda () 0) (lambda (_) 1) +))

;; ========================================
;; List-based ref implementation
;; ========================================

(define (find-in-list lst idx depth)
  (match-define (cons head lst^) lst)
  (define sz (measure:node core/size head depth))
  (cond [(>= idx sz) (find-in-list lst^ (- idx sz) depth)]
    [else (pvector-ref-node/list head idx depth)]))

(define node->list (match-lambda
  [(node:2 _ a b) `(,a ,b)]
  [(node:3 _ a b c) `(,a ,b ,c)]))

(define (pvector-ref-node/list node idx depth)
  (match depth
    [0 (=> e) (when (zero? idx) (e)) (error 'pvector-ref/list "unreachable")]
    [0 node]
    [_ (define lst (node->list node))
      (find-in-list lst idx (sub1 depth))]))

(define (pvector-ref-digit/list digit idx depth)
  (define lst (digit-add-list digit '()))
  (find-in-list lst idx depth))

(define (pvector-ref/list:impl pv idx depth)
  (match pv
    [(ft:single r) (pvector-ref-node/list r idx depth)]
    [(ft:deep _ lhs inner rhs)
      (define lhs-measure (measure:digit core/size lhs depth))
      (define inner-measure (+ lhs-measure (measure:ft core/size inner (add1 depth))))
      (cond
        [(< idx lhs-measure) (pvector-ref-digit/list lhs idx depth)]
        [(< idx inner-measure) (pvector-ref/list:impl inner (- idx lhs-measure) (add1 depth))]
        [else (pvector-ref-digit/list rhs (- idx inner-measure) depth)])]))

(define (pvector-ref/list pv idx)
  (cond
    [(< idx 0) (error 'pvector-ref/list "index out of bounds: ~a" idx)]
    [(>= idx (measure:ft core/size pv 0)) (error 'pvector-ref/list "index out of bounds: ~a" idx)]
    [else (pvector-ref/list:impl pv idx 0)]))

;; ========================================
;; List-based set implementation
;; ========================================

(define (update-in-list:impl lst idx value depth rest)
  (match-define (cons head lst^) lst)
  (define sz (measure:node core/size head depth))
  (cond [(>= idx sz) (update-in-list:impl lst^ (- idx sz) value depth (cons head rest))]
    [else (for/fold ([init (cons (pvector-set-node/list head idx value depth) rest)]) ([r lst^])
      (cons r init))]))

(define (update-in-list lst idx value depth)
  (reverse (update-in-list:impl lst idx value depth '())))

(define (list->node lst depth)
  (match lst
    [`(,a ,b) (node:2 (+ (measure:node core/size a depth) (measure:node core/size b depth)) a b)]
    [`(,a ,b ,c) (node:3
      (+ (measure:node core/size a depth)
        (measure:node core/size b depth) (measure:node core/size c depth))
      a b c)]))

(define (pvector-set-node/list node idx value depth)
  (match depth
    [0 (=> e) (when (zero? idx) (e)) (error 'pvector-set/list "unreachable")]
    [0 value]
    [_ (define lst (node->list node))
      (list->node (update-in-list lst idx value (sub1 depth)) (sub1 depth))]))

(define (pvector-set-digit/list digit idx value depth)
  (define lst (digit-add-list digit '()))
  (define m (update-in-list lst idx value depth))
  (list->digit m depth))

(define (pvector-set/list:impl pv idx value depth)
  (match pv
    [(ft:single r) (ft:single (pvector-set-node/list r idx value depth))]
    [(ft:deep old lhs inner rhs)
      (define lhs-measure (measure:digit core/size lhs depth))
      (define inner-measure (+ lhs-measure (measure:ft core/size inner (add1 depth))))
      (cond
        [(< idx lhs-measure) (ft:deep old (pvector-set-digit/list lhs idx value depth) inner rhs)]
        [(< idx inner-measure) (ft:deep old lhs (pvector-set/list:impl inner (- idx lhs-measure) value (add1 depth)) rhs)]
        [(< idx old) (ft:deep old lhs inner (pvector-set-digit/list rhs (- idx inner-measure) value depth))]
        [else (error 'pvector-set/list "unreachable")])]))

(define (pvector-set/list pv idx val)
  (cond
    [(< idx 0) (error 'pvector-set/list "index out of bounds: ~a" idx)]
    [(>= idx (measure:ft core/size pv 0)) (error 'pvector-set/list "index out of bounds: ~a" idx)]
    [else (pvector-set/list:impl pv idx val 0)]))

;; ========================================
;; Exports
;; ========================================

(provide
  pvector-ref/list
  pvector-set/list
  ;; Internal helpers (for testing/debugging)
  node->list
  find-in-list
  update-in-list)
