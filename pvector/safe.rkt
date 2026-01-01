#lang racket/base

(require racket/contract)
(require "../pvector.rkt")

;; ========================================
;; Contract Definitions
;; ========================================

(define pvector/c
  (flat-named-contract 'pvector pvector?))

(define index/c
  (flat-named-contract 'index exact-nonnegative-integer?))

;; ========================================
;; Contract-Protected Exports
;; ========================================

(provide/contract
  ;; Type predicates
  [pvector? (-> any/c boolean?)]
  [pvector-empty? (-> any/c boolean?)]

  ;; Construction
  [pvector-empty (-> pvector/c)]

  ;; Length
  [pvector-length (-> pvector/c index/c)]

  ;; Element access with dependent contracts
  [pvector-ref
    (->i ([pv pvector/c]
          [idx (pv) (and/c index/c (</c (pvector-length pv)))])
         [result any/c])]

  [pvector-set
    (->i ([pv pvector/c]
          [idx (pv) (and/c index/c (</c (pvector-length pv)))]
          [val any/c])
         [result pvector/c])]

  ;; Add/remove from ends
  [pvector-cons-left (-> pvector/c any/c pvector/c)]
  [pvector-cons-right (-> pvector/c any/c pvector/c)]

  [pvector-pop-left
    (-> (and/c pvector/c (not/c pvector-empty?))
        (values any/c pvector/c))]

  [pvector-pop-right
    (-> (and/c pvector/c (not/c pvector-empty?))
        (values any/c pvector/c))]

  ;; View ends (non-destructive)
  [pvector-view-left
    (-> (and/c pvector/c (not/c pvector-empty?)) any/c)]

  [pvector-view-right
    (-> (and/c pvector/c (not/c pvector-empty?)) any/c)]

  ;; Concatenation
  [pvector-append (-> pvector/c pvector/c pvector/c)]

  ;; Split operations
  [pvector-split
    (->i ([pv (and/c pvector/c (not/c pvector-empty?))]
          [idx (pv) (and/c index/c (</c (pvector-length pv)))])
         (values [left pvector/c] [mid any/c] [right pvector/c]))]

  [pvector-split-at
    (->i ([pv pvector/c]
          [pos (pv) (and/c index/c (<=/c (pvector-length pv)))])
         (values [left pvector/c] [right pvector/c]))]

  [pvector-split-at-right
    (->i ([pv pvector/c]
          [pos (pv) (and/c index/c (<=/c (pvector-length pv)))])
         (values [right pvector/c] [left pvector/c]))]

  ;; Slice operations
  [pvector-take
    (->i ([pv pvector/c]
          [n (pv) (and/c index/c (<=/c (pvector-length pv)))])
         [result pvector/c])]

  [pvector-drop
    (->i ([pv pvector/c]
          [n (pv) (and/c index/c (<=/c (pvector-length pv)))])
         [result pvector/c])]

  [pvector-take-right
    (->i ([pv pvector/c]
          [n (pv) (and/c index/c (<=/c (pvector-length pv)))])
         [result pvector/c])]

  [pvector-drop-right
    (->i ([pv pvector/c]
          [n (pv) (and/c index/c (<=/c (pvector-length pv)))])
         [result pvector/c])]

  [pvector-copy
    (->i ([pv pvector/c]
          [start (pv) (and/c index/c (<=/c (pvector-length pv)))]
          [end (pv start) (and/c index/c (<=/c (pvector-length pv)) (>=/c start))])
         [result pvector/c])]

  ;; Insert and delete
  [pvector-insert
    (->i ([pv pvector/c]
          [idx (pv) (and/c index/c (<=/c (pvector-length pv)))]
          [val any/c])
         [result pvector/c])]

  [pvector-delete
    (->i ([pv (and/c pvector/c (not/c pvector-empty?))]
          [idx (pv) (and/c index/c (</c (pvector-length pv)))])
         (values [result pvector/c] [deleted any/c]))]

  ;; Conversion
  [vector->pvector (-> vector? pvector/c)]
  [pvector->vector (-> pvector/c vector?)]
  [list->pvector (-> list? pvector/c)]
  [pvector->list (-> pvector/c list?)]

  ;; Sequence (generator-based)
  [in-pvector (-> pvector/c sequence?)]
  [in-pvector-reverse (-> pvector/c sequence?)]
  [in-pvector-indexed (-> pvector/c sequence?)]

  ;; Sequence (index-based)
  [in-pvector/index (-> pvector/c sequence?)]
)

;; Comprehensions (syntax, no contracts needed)
(require (only-in "../pvector.rkt" for/pvector for*/pvector pvector pvector*))
(provide for/pvector for*/pvector)

;; Match expanders (syntax)
(provide pvector pvector*)
