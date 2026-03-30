#lang racket/base

(provide built-in-exemption-specs)

;; Data-driven exemption specs. Keep each entry narrow and explicit.
;; Fields:
;; 1. id symbol
;; 2. description string
;; 3. exact run-length integer
;; 4. regular expression (anchored full-line match)
;; 5. optional path regular expression (#f means global)
(define built-in-exemption-specs
  (list
   (list
    'for-clause-placeholder
    "Allow exactly `[_ (_)]` for-clause style lines at run=3, scoped to safe modules."
    3
    #px"^\\s*\\[_\\s+\\(_\\)\\](?:[\\)\\]]+)?\\s*$"
    #px"(^|/)(bitset|interval-tree|ordered-map|priority-queue|pvector|text)/safe[.]rkt$")
   (list
    'for-clause-single-seq
    "Allow `[id (in-foo atom)]` for-clause style lines at run=3, scoped to safe modules."
    3
    #px"^\\s*\\[[A-Za-z_][A-Za-z0-9_:+\\-*/?!<>=]*\\s+\\(in-[A-Za-z0-9_:+\\-*/?!<>=]+\\s+[^()\\[\\]\\s]+\\)\\](?:[\\)\\]]+)?\\s*$"
    #px"(^|/)(bitset|interval-tree|ordered-map|priority-queue|pvector|text)/safe[.]rkt$")
   (list
    'for-clause-two-atom-seq
    "Allow `[id (in-foo atom atom)]` for-clause style lines at run=3, scoped to safe modules."
    3
    #px"^\\s*\\[[A-Za-z_][A-Za-z0-9_:+\\-*/?!<>=]*\\s+\\(in-[A-Za-z0-9_:+\\-*/?!<>=]+\\s+[^()\\[\\]\\s]+\\s+[^()\\[\\]\\s]+\\)\\](?:[\\)\\]]+)?\\s*$"
    #px"(^|/)(bitset|interval-tree|ordered-map|priority-queue|pvector|text)/safe[.]rkt$")))
