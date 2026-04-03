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
(define interval-entry/c
  (list/c endpoint/c endpoint/c any/c))
(define interval-list/c
  (listof interval-entry/c))

;; ========================================
;; Contract-Protected Exports
;; ========================================

(provide/contract
  ;; Type predicate
  [interval-tree? (-> any/c boolean?)]
  [interval-tree-empty? (-> interval-tree/c boolean?)]

  ;; Construction
  [interval-tree-empty (-> interval-tree/c)]
  [list->interval-tree (-> interval-list/c interval-tree/c)]

  ;; Size
  [interval-tree-count (-> interval-tree/c exact-nonnegative-integer?)]

  ;; Insert
  [interval-tree-insert (-> interval-tree/c endpoint/c endpoint/c any/c interval-tree/c)]

  ;; Query
  [interval-tree-search
   (-> interval-tree/c endpoint/c endpoint/c
       interval-list/c)]
  [interval-tree-search-point
   (-> interval-tree/c endpoint/c
       interval-list/c)]

  ;; Delete
  [interval-tree-delete (-> interval-tree/c endpoint/c endpoint/c any/c interval-tree/c)]

  ;; Conversion
  [interval-tree->list
   (-> interval-tree/c interval-list/c)]
  ) ; provide/contract
