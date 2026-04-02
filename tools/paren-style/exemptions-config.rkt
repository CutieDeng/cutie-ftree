#lang racket/base

(provide built-in-exemption-specs)

;; Data-driven exemption specs. Keep each entry narrow and explicit.
;; Fields:
;; 1. id symbol
;; 2. description string
;; 3. exact run-length integer
;; 4. regular expression (anchored full-line match)
;; 5. optional path regular expression (#f means global)
;; 6. optional semantic-kind symbol (#f means any)
;; 7. optional ast-tag symbol (#f means any)
(define built-in-exemption-specs
  (list
   (list
   'for-head-placeholder
   "Allow `(for/... ([_ (_)]))` single-clause header lines at run=3."
    3
    #px".*"
    #f
    'for-header
    'for-head-placeholder)
   (list
   'for-head-single-seq
   "Allow `(for/... ([id (in-foo atom)]))` single-clause header lines at run=3."
    3
    #px".*"
    #f
    'for-header
    'for-head-single-seq)
   (list
   'for-head-two-atom-seq
   "Allow `(for/... ([id (in-foo atom atom)]))` single-clause header lines at run=3."
    3
    #px".*"
    #f
    'for-header
    'for-head-two-atom-seq)
   (list
    'safe-contract-arrow-header
    "Allow `->i` contract header lines at run=3 in safe modules."
    3
    #px"^\\s*\\(->i\\b"
    #px"(^|/)(bitset|interval-tree|ordered-map|priority-queue|pvector|text)/safe[.]rkt$"
    'contract-header
    'contract-header)
   (list
    'for-clause-placeholder
    "Allow exactly `[_ (_)]` for-clause style lines at run=3, scoped to safe modules."
    3
    #px".*"
    #px"(^|/)(bitset|interval-tree|ordered-map|priority-queue|pvector|text)/safe[.]rkt$"
    'for-clause
    'for-clause-placeholder)
   (list
    'for-clause-single-seq
    "Allow `[id (in-foo atom)]` for-clause style lines at run=3, scoped to safe modules."
    3
    #px".*"
    #px"(^|/)(bitset|interval-tree|ordered-map|priority-queue|pvector|text)/safe[.]rkt$"
    'for-clause
    'for-clause-single-seq)
   (list
    'for-clause-two-atom-seq
    "Allow `[id (in-foo atom atom)]` for-clause style lines at run=3, scoped to safe modules."
    3
    #px".*"
    #px"(^|/)(bitset|interval-tree|ordered-map|priority-queue|pvector|text)/safe[.]rkt$"
    'for-clause
    'for-clause-two-atom-seq)))
