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
    'for-clause-two-atom-seq)
   (list
    'contract-test-mk-pv-run3
    "Allow `mk-pv` helper lines at run=3 in contract test."
    3
    #px"^\\s*\\(mk-pv\\b"
    #px"(^|/)tests/contract-test[.]rkt$"
    #f
    #f)
   (list
    'contract-test-mk-pv-run4
    "Allow `mk-pv` helper lines at run=4 in contract test."
    4
    #px"^\\s*\\(mk-pv\\b"
    #px"(^|/)tests/contract-test[.]rkt$"
    #f
    #f)
   (list
    'contract-test-mk-om-run3
    "Allow `mk-om` helper lines at run=3 in contract test."
    3
    #px"^\\s*\\(mk-om(?:/kv)?\\b"
    #px"(^|/)tests/contract-test[.]rkt$"
    #f
    #f)
   (list
    'contract-test-mk-om-run4
    "Allow `mk-om` helper lines at run=4 in contract test."
    4
    #px"^\\s*\\(mk-om(?:/kv)?\\b"
    #px"(^|/)tests/contract-test[.]rkt$"
    #f
    #f)
   (list
    'contract-test-check-exn-run3
    "Allow check-exn/check-not-exn wrapper lines at run=3 in contract test."
    3
    #px"^\\s*\\(check-(?:exn|not-exn)\\b"
    #px"(^|/)tests/contract-test[.]rkt$"
    #f
    #f)
   (list
    'contract-test-check-exn-run4
    "Allow check-exn/check-not-exn wrapper lines at run=4 in contract test."
    4
    #px"^\\s*\\(check-(?:exn|not-exn)\\b"
    #px"(^|/)tests/contract-test[.]rkt$"
    #f
    #f)
   (list
    'contract-test-check-exn-run5
    "Allow check-exn/check-not-exn wrapper lines at run=5 in contract test."
    5
    #px"^\\s*\\(check-(?:exn|not-exn)\\b"
    #px"(^|/)tests/contract-test[.]rkt$"
    #f
    #f)
   (list
    'contract-test-thunk-lambda-run3
    "Allow thunk lambda call lines at run=3 in contract test."
    3
    #px"^\\s*\\(lambda\\s*\\(\\)\\s*\\("
    #px"(^|/)tests/contract-test[.]rkt$"
    #f
    #f)
   (list
    'contract-test-thunk-lambda-run4
    "Allow thunk lambda call lines at run=4 in contract test."
    4
    #px"^\\s*\\(lambda\\s*\\(\\)\\s*\\("
    #px"(^|/)tests/contract-test[.]rkt$"
    #f
    #f)
   (list
    'contract-test-thunk-lambda-run5
    "Allow thunk lambda call lines at run=5 in contract test."
    5
    #px"^\\s*\\(lambda\\s*\\(\\)\\s*\\("
    #px"(^|/)tests/contract-test[.]rkt$"
    #f
    #f)
   (list
    'contract-test-thunk-lambda-run6
    "Allow thunk lambda call lines at run=6 in contract test."
    6
    #px"^\\s*\\(lambda\\s*\\(\\)\\s*\\("
    #px"(^|/)tests/contract-test[.]rkt$"
    #f
    #f)
   (list
    'contract-test-blame-regexp-run4
    "Allow blame-message regexp checks at run=4 in contract test."
    4
    #px"^\\s*\\(regexp-match\\?\\b"
    #px"(^|/)tests/contract-test[.]rkt$"
    #f
    #f)
   ))
