#lang racket/base

;; ============================================================
;; Bitset: Contract-protected version
;; ============================================================

(require racket/contract)
(require "../bitset.rkt")

;; ========================================
;; Contract Definitions
;; ========================================

(define bitset/c
  (flat-named-contract 'bitset bitset?))

(define element/c
  (flat-named-contract 'element exact-nonnegative-integer?))

(define nonempty-bitset/c
  (and/c bitset/c (not/c bitset-empty?)))

;; ========================================
;; Contract-Protected Exports
;; ========================================

(provide/contract
  ;; Constants
  [bitset-empty bitset/c]

  ;; Predicates
  [bitset? (-> any/c boolean?)]
  [bitset-empty? (-> any/c boolean?)]
  [bitset-member? (-> bitset/c element/c boolean?)]
  [bitset-equal? (-> bitset/c bitset/c boolean?)]
  [bitset-subset? (-> bitset/c bitset/c boolean?)]
  [bitset-disjoint? (-> bitset/c bitset/c boolean?)]

  ;; Element operations
  [bitset-add (-> bitset/c element/c bitset/c)]
  [bitset-remove (-> bitset/c element/c bitset/c)]

  ;; Set operations
  [bitset-union (-> bitset/c bitset/c bitset/c)]
  [bitset-intersection (-> bitset/c bitset/c bitset/c)]
  [bitset-subtract (-> bitset/c bitset/c bitset/c)]

  ;; Counting
  [bitset-count (-> bitset/c exact-nonnegative-integer?)]

  ;; Boundary (require non-empty)
  [bitset-min (-> nonempty-bitset/c element/c)]
  [bitset-max (-> nonempty-bitset/c element/c)]

  ;; Iteration
  [in-bitset (-> bitset/c sequence?)]
  [in-bitset/reverse (-> bitset/c sequence?)]

  ;; Conversions
  [seq->bitset (-> sequence? bitset/c)]
  [bitset->list (-> bitset/c (listof element/c))]
  [bitset->vector (-> bitset/c (vectorof element/c))]
  [list->bitset (-> (listof element/c) bitset/c)]
  [vector->bitset (-> (vectorof element/c) bitset/c)]
  [list->bitset* (-> (listof element/c) bitset/c)]

  ;; gen:set wrapper
  [bitset-wrapper? (-> any/c boolean?)]
  [bitset-wrapper-bits (-> bitset-wrapper? bitset/c)]
  [bitset->set (-> bitset/c bitset-wrapper?)]
)

;; Syntax (no contracts needed)
(require (only-in "../bitset.rkt"
  bitset bitset*
  for/bitset for*/bitset
  bitset-empty-pat bitset-cons bitset-rev bitset-has))

(provide bitset bitset*)
(provide for/bitset for*/bitset)
(provide bitset-empty-pat bitset-cons bitset-rev bitset-has)

;; Re-export struct
(provide bitset-wrapper)
