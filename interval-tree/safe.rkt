#lang racket/base

(require racket/contract)
(require "../interval-tree.rkt")

;; ========================================
;; Contract Definitions
;; ========================================

(define interval-tree/c
  (flat-named-contract 'interval-tree interval-tree?))

(define endpoint/c
  (or/c real? +inf.0 -inf.0))

;; ========================================
;; Contract-Protected Exports
;; ========================================

(provide/contract
  ;; Type predicate
  [interval-tree? (-> any/c boolean?)]
  [interval-tree-empty? (-> interval-tree/c boolean?)]

  ;; Construction
  [interval-tree-empty (-> interval-tree/c)]
  [list->interval-tree (-> (listof (list/c endpoint/c endpoint/c any/c)) interval-tree/c)]

  ;; Size
  [interval-tree-count (-> interval-tree/c exact-nonnegative-integer?)]

  ;; Insert
  [interval-tree-insert (-> interval-tree/c endpoint/c endpoint/c any/c interval-tree/c)]

  ;; Query
  [interval-tree-search (-> interval-tree/c endpoint/c endpoint/c (listof (list/c endpoint/c endpoint/c any/c)))]
  [interval-tree-search-point (-> interval-tree/c endpoint/c (listof (list/c endpoint/c endpoint/c any/c)))]

  ;; Delete
  [interval-tree-delete (-> interval-tree/c endpoint/c endpoint/c any/c interval-tree/c)]

  ;; Conversion
  [interval-tree->list (-> interval-tree/c (listof (list/c endpoint/c endpoint/c any/c)))])
