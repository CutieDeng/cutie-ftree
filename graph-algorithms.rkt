#lang racket/base

;; ============================================================
;; Graph Algorithms: Unified Exports
;; ============================================================
;;
;; Re-exports all graph algorithms from cutie-ftree/graph/ submodules.
;;
;; Usage:
;;   (require "cutie-ftree/graph-algorithms.rkt")
;;
;; Or import specific modules:
;;   (require "cutie-ftree/graph/scc.rkt")
;;   (require "cutie-ftree/graph/traversal.rkt")
;;   (require "cutie-ftree/graph/reachability.rkt")
;;
;; ============================================================

(require "graph/scc.rkt"
         "graph/traversal.rkt"
         "graph/reachability.rkt")

(provide
  ;; ============================================================
  ;; SCC Algorithms (from graph/scc.rkt)
  ;; ============================================================

  ;; Concrete API (Graph type)
  graph-scc              ; Graph -> pvector[bitset]
  graph-condensation     ; Graph -> (values node->scc scc-nodes scc-successors)

  ;; Parameterized API (callbacks)
  scc-tarjan             ; node-compare nodes get-successors -> pvector[pvector]
  scc-kosaraju           ; node-compare nodes get-successors get-predecessors -> pvector[pvector]
  condensation-graph     ; node-compare nodes get-successors -> (values ...)

  ;; Utilities
  scc-id                 ; node->scc-id node -> integer
  scc-members            ; scc-nodes scc-id -> pvector

  ;; ============================================================
  ;; Traversal Algorithms (from graph/traversal.rkt)
  ;; ============================================================

  ;; Concrete API (Graph type)
  graph-dfs-preorder          ; Graph start -> pvector[vertex-val]
  graph-dfs-postorder         ; Graph start -> pvector[vertex-val]
  graph-dfs-reverse-postorder ; Graph start -> pvector[vertex-val]
  graph-bfs                   ; Graph start -> pvector[vertex-val]
  graph-topo-sort             ; Graph -> pvector[vertex-val] or #f

  ;; Parameterized API (callbacks)
  dfs-preorder           ; node-compare get-successors start -> pvector
  dfs-postorder          ; node-compare get-successors start -> pvector
  dfs-reverse-postorder  ; node-compare get-successors start -> pvector
  bfs                    ; node-compare get-successors start -> pvector
  topology-sort          ; node-compare nodes get-successors get-predecessors -> pvector or #f

  ;; ============================================================
  ;; Reachability Algorithms (from graph/reachability.rkt)
  ;; ============================================================

  ;; Concrete API (Graph type)
  graph-reachable-from      ; Graph start -> bitset
  graph-reachable-from-set  ; Graph starts -> bitset
  graph-find-path           ; Graph start end -> pvector or #f
  graph-all-paths           ; Graph start end -> pvector[pvector]

  ;; Parameterized API (callbacks)
  reachable-from       ; node-compare get-successors start -> pvector
  reachable-from-set   ; node-compare get-successors starts -> ordered-map
  find-path            ; node-compare get-successors start end -> pvector or #f
  all-paths            ; node-compare get-successors start end -> pvector[pvector]
  )
