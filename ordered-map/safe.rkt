#lang racket/base

(require racket/contract)
(require "../ordered-map.rkt")
(require "../comparator.rkt")

;; ========================================
;; Contract Definitions
;; ========================================

(define ordered-map/c
  (flat-named-contract 'ordered-map ordered-map?))

(define query-mode/c
  (flat-named-contract 'query-mode (or/c '< '<= '> '>=)))

;; ========================================
;; Contract-Protected Exports
;; ========================================

(provide/contract
  ;; Type predicate
  [ordered-map? (-> any/c boolean?)]
  [ordered-map-empty? (-> ordered-map/c boolean?)]

  ;; Construction
  [ordered-map-empty (-> (comparator/c any/c) ordered-map/c)]

  ;; Size
  [ordered-map-count (-> ordered-map/c exact-nonnegative-integer?)]

  ;; Min/Max access
  [ordered-map-min (-> ordered-map/c (or/c #f pair?))]
  [ordered-map-max (-> ordered-map/c (or/c #f pair?))]

  ;; Query
  [ordered-map-query (-> ordered-map/c any/c (or/c #f pair?))]

  [ordered-map-query-weak
    (-> ordered-map/c any/c query-mode/c (or/c #f pair?))]

  [ordered-map-has-key? (-> ordered-map/c any/c boolean?)]

  ;; Dict-style access
  [ordered-map-ref
    (->* (ordered-map/c any/c) (any/c) any/c)]

  [ordered-map-set
    (-> ordered-map/c any/c any/c ordered-map/c)]

  ;; Insert/Delete
  [ordered-map-insert
    (-> ordered-map/c any/c any/c boolean? ordered-map/c)]

  [ordered-map-delete
    (-> ordered-map/c any/c (values ordered-map/c (or/c #f pair?)))]

  ;; Collection operations
  [ordered-map-keys (-> ordered-map/c (listof any/c))]
  [ordered-map-values (-> ordered-map/c (listof any/c))]

  ;; Sequence
  [in-ordered-map (-> ordered-map/c sequence?)]
)
