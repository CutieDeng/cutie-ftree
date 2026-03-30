#lang racket/base

(provide built-in-rule-specs)

;; Data-driven rule specs.
;; Fields:
;; 1. id symbol
;; 2. description string
;; 3. kind symbol
;;
;; Kinds:
;; - 'max-run-threshold : compare line run-length against checker-config-max-run
(define built-in-rule-specs
  (list
   (list
    'dense-closing-run
    "Line contains a dense closing run (parens/brackets) beyond the configured threshold."
    'max-run-threshold)))
