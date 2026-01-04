#lang racket/base

;; ============================================================
;; DEPRECATED: Use cutie-ftree/graph/scc.rkt instead
;; ============================================================
;;
;; This module re-exports from graph/scc.rkt for backward compatibility.
;; New code should import directly from:
;;   (require "cutie-ftree/graph/scc.rkt")
;; or
;;   (require "cutie-ftree/graph-algorithms.rkt")
;;
;; ============================================================

(require "graph/scc.rkt")

(provide
  ;; Concrete API (Graph type)
  graph-scc
  graph-condensation)
