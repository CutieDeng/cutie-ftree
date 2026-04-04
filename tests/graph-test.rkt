#lang racket/base

(require rackunit)
(require "../graph.rkt")
(require "../bitset.rkt")
(require "../pvector.rkt")

;; Helper: check if pvector contains a vertex-id with given val
(define (pvector-has-vertex-val? pv val)
  (define (same-vertex? v)
    (define v-val (vertex-id-val v))
    (= v-val val))
  (define vs (in-pvector pv))
  (for/or ([v (in-pvector pv)])
    (same-vertex? v))
  )

;; Helper: check if pvector contains an edge-id with given val
(define (pvector-has-edge-val? pv val)
  (define (same-edge? e)
    (define e-val (edge-id-val e))
    (= e-val val))
  (define es (in-pvector pv))
  (for/or ([e es])
    (same-edge? e))
  )

;; ========================================
;; Basic Construction
;; ========================================

(test-case "graph-empty"
  (check-true (graph? graph-empty))
  (check-equal? (graph-vertex-count graph-empty) 0)
  (check-equal? (graph-edge-count graph-empty) 0))

;; ========================================
;; Vertex Operations
;; ========================================

(test-case "graph-add-vertex"
  (define-values (g1 v0) (graph-add-vertex graph-empty))
  (check-true (vertex-id? v0))
  (check-equal? (vertex-id-val v0) 0)
  (check-equal? (graph-vertex-count g1) 1)
  (check-true (graph-vertex? g1 v0))

  (define-values (g2 v1) (graph-add-vertex g1))
  (check-equal? (vertex-id-val v1) 1)
  (check-equal? (graph-vertex-count g2) 2)
  (check-true (graph-vertex? g2 v0))
  (define has-v1? (graph-vertex? g2 v1))
  (check-true has-v1?))

(test-case "graph-remove-vertex"
  (define-values (g1 v0) (graph-add-vertex graph-empty))
  (define-values (g2 v1) (graph-add-vertex g1))

  (check-equal? (graph-vertex-count g2) 2)

  ;; Remove v0 (no edges)
  (define g3 (graph-remove-vertex g2 v0))
  (check-equal? (graph-vertex-count g3) 1)
  (check-false (graph-vertex? g3 v0))
  (define has-v1? (graph-vertex? g3 v1))
  (check-true has-v1?))

(test-case "graph-remove-vertex with edges fails"
  (define-values (g1 v0) (graph-add-vertex graph-empty))
  (define-values (g2 v1) (graph-add-vertex g1))
  (define-values (g3 e0) (graph-add-edge g2 v0 v1))

  ;; Remove v0 should fail (has out-edge)
  (define (remove-v0) (graph-remove-vertex g3 v0))
  (check-exn exn:fail? remove-v0)
  ;; Remove v1 should fail (has in-edge)
  (define (remove-v1) (graph-remove-vertex g3 v1))
  (check-exn exn:fail? remove-v1))

(test-case "graph-remove-vertex*"
  (define-values (g1 v0) (graph-add-vertex graph-empty))
  (define-values (g2 v1) (graph-add-vertex g1))
  (define-values (g3 e0) (graph-add-edge g2 v0 v1))

  (check-equal? (graph-vertex-count g3) 2)
  (check-equal? (graph-edge-count g3) 1)

  ;; Remove v0 with cascade (should also remove e0)
  (define g4 (graph-remove-vertex* g3 v0))
  (check-equal? (graph-vertex-count g4) 1)
  (check-equal? (graph-edge-count g4) 0)
  (check-false (graph-vertex? g4 v0))
  (check-true (graph-vertex? g4 v1))
  (define has-e0? (graph-edge? g4 e0))
  (check-false has-e0?))

(test-case "vertex-id-no-recycling"
  (define-values (g1 v0) (graph-add-vertex graph-empty))
  (define-values (g2 v1) (graph-add-vertex g1))
  (check-equal? (vertex-id-val v0) 0)
  (check-equal? (vertex-id-val v1) 1)

  ;; Remove v0
  (define g3 (graph-remove-vertex g2 v0))

  ;; Add new vertex - should NOT recycle, use next ID
  (define-values (g4 v2) (graph-add-vertex g3))
  (check-equal? (vertex-id-val v2) 2))

;; ========================================
;; Edge Operations
;; ========================================

(test-case "graph-add-edge"
  (define-values (g1 v0) (graph-add-vertex graph-empty))
  (define-values (g2 v1) (graph-add-vertex g1))
  (define-values (g3 e0) (graph-add-edge g2 v0 v1))

  (check-true (edge-id? e0))
  (check-equal? (edge-id-val e0) 0)
  (check-equal? (graph-edge-count g3) 1)
  (check-true (graph-edge? g3 e0))

  (check-equal? (graph-edge-src g3 e0) v0)
  (check-equal? (graph-edge-dst g3 e0) v1))

(test-case "graph-add-edge self-loop"
  (define-values (g1 v0) (graph-add-vertex graph-empty))
  (define-values (g2 e0) (graph-add-edge g1 v0 v0))

  (check-equal? (graph-edge-src g2 e0) v0)
  (check-equal? (graph-edge-dst g2 e0) v0)
  (check-equal? (graph-in-degree g2 v0) 1)
  (check-equal? (graph-out-degree g2 v0) 1))

(test-case "graph-add-edge-pair"
  (define-values (g1 v0) (graph-add-vertex graph-empty))
  (define-values (g2 v1) (graph-add-vertex g1))
  (define-values (g3 e0 e1) (graph-add-edge-pair g2 v0 v1))

  (check-equal? (graph-edge-count g3) 2)
  (check-equal? (graph-edge-src g3 e0) v0)
  (check-equal? (graph-edge-dst g3 e0) v1)
  (check-equal? (graph-edge-src g3 e1) v1)
  (check-equal? (graph-edge-dst g3 e1) v0)

  ;; Check pairing
  (check-equal? (graph-edge-pair g3 e0) e1)
  (check-equal? (graph-edge-pair g3 e1) e0))

(test-case "graph-remove-edge"
  (define-values (g1 v0) (graph-add-vertex graph-empty))
  (define-values (g2 v1) (graph-add-vertex g1))
  (define-values (g3 e0) (graph-add-edge g2 v0 v1))

  (define g4 (graph-remove-edge g3 e0))
  (check-equal? (graph-edge-count g4) 0)
  (define has-e0? (graph-edge? g4 e0))
  (check-false has-e0?))

(test-case "graph-remove-edge with paired"
  (define-values (g1 v0) (graph-add-vertex graph-empty))
  (define-values (g2 v1) (graph-add-vertex g1))
  (define-values (g3 e0 e1) (graph-add-edge-pair g2 v0 v1))

  ;; Remove single edge (pair link removed but pair edge kept)
  (define g4 (graph-remove-edge g3 e0))
  (check-equal? (graph-edge-count g4) 1)
  (check-false (graph-edge? g4 e0))
  (check-true (graph-edge? g4 e1))
  (check-false (graph-edge-pair g4 e1))  ; pair link removed

  ;; Remove with cascade (removes paired edge too)
  (define-values (g5 e2 e3) (graph-add-edge-pair g2 v0 v1))
  (define g6 (graph-remove-edge* g5 e2))
  (check-equal? (graph-edge-count g6) 0)
  (check-false (graph-edge? g6 e2))
  (define has-e3? (graph-edge? g6 e3))
  (check-false has-e3?))

(test-case "graph-remove-edge-between"
  (define-values (g1 v0) (graph-add-vertex graph-empty))
  (define-values (g2 v1) (graph-add-vertex g1))
  (define-values (g3 e0) (graph-add-edge g2 v0 v1))

  ;; Remove single edge by vertices
  (define g4 (graph-remove-edge-between g3 v0 v1))
  (check-equal? (graph-edge-count g4) 0)
  (check-false (graph-edge? g4 e0))

  ;; Error: no edge
  (define (remove-between-empty) (graph-remove-edge-between g4 v0 v1))
  (check-exn exn:fail? remove-between-empty)

  ;; Error: multiple edges
  (define-values (g5 e1) (graph-add-edge g3 v0 v1))
  (define (remove-between-multi) (graph-remove-edge-between g5 v0 v1))
  (check-exn exn:fail? remove-between-multi))

(test-case "graph-remove-edges-between"
  (define-values (g1 v0) (graph-add-vertex graph-empty))
  (define-values (g2 v1) (graph-add-vertex g1))
  (define-values (g3 e0) (graph-add-edge g2 v0 v1))
  (define-values (g4 e1) (graph-add-edge g3 v0 v1))
  (define-values (g5 e2) (graph-add-edge g4 v0 v1))

  (check-equal? (graph-edge-count g5) 3)

  ;; Remove all edges between v0 and v1
  (define g6 (graph-remove-edges-between g5 v0 v1))
  (check-equal? (graph-edge-count g6) 0)
  (check-false (graph-edge? g6 e0))
  (check-false (graph-edge? g6 e1))
  (check-false (graph-edge? g6 e2))

  ;; Remove from empty is ok (no-op)
  (define g7 (graph-remove-edges-between g6 v0 v1))
  (check-equal? (graph-edge-count g7) 0))

(test-case "edge-id-no-recycling"
  (define-values (g1 v0) (graph-add-vertex graph-empty))
  (define-values (g2 v1) (graph-add-vertex g1))
  (define-values (g3 e0) (graph-add-edge g2 v0 v1))
  (define-values (g4 e1) (graph-add-edge g3 v1 v0))
  (check-equal? (edge-id-val e0) 0)
  (check-equal? (edge-id-val e1) 1)

  ;; Remove e0
  (define g5 (graph-remove-edge g4 e0))

  ;; Add new edge - should NOT recycle, use next ID
  (define-values (g6 e2) (graph-add-edge g5 v0 v1))
  (check-equal? (edge-id-val e2) 2))

;; ========================================
;; Multi-edge Support
;; ========================================

(test-case "multi-edge"
  (define-values (g1 v0) (graph-add-vertex graph-empty))
  (define-values (g2 v1) (graph-add-vertex g1))
  (define-values (g3 e0) (graph-add-edge g2 v0 v1))
  (define-values (g4 e1) (graph-add-edge g3 v0 v1))
  (define-values (g5 e2) (graph-add-edge g4 v0 v1))

  (check-equal? (graph-edge-count g5) 3)

  (define edges-between (graph-edges-between g5 v0 v1))
  (check-equal? (pvector-length edges-between) 3)
  (define e0-val (edge-id-val e0))
  (define e1-val (edge-id-val e1))
  (define e2-val (edge-id-val e2))
  (check-true (pvector-has-edge-val? edges-between e0-val))
  (check-true (pvector-has-edge-val? edges-between e1-val))
  (define has-e2? (pvector-has-edge-val? edges-between e2-val))
  (check-true has-e2?))

;; ========================================
;; Adjacency Queries
;; ========================================

(test-case "graph-in-edges and graph-out-edges"
  (define-values (g1 v0) (graph-add-vertex graph-empty))
  (define-values (g2 v1) (graph-add-vertex g1))
  (define-values (g3 v2) (graph-add-vertex g2))
  (define-values (g4 e0) (graph-add-edge g3 v0 v1))
  (define-values (g5 e1) (graph-add-edge g4 v0 v2))
  (define-values (g6 e2) (graph-add-edge g5 v1 v2))

  ;; v0: out={e0,e1}, in={}
  (check-equal? (pvector-length (graph-out-edges g6 v0)) 2)
  (check-equal? (pvector-length (graph-in-edges g6 v0)) 0)

  ;; v1: out={e2}, in={e0}
  (check-equal? (pvector-length (graph-out-edges g6 v1)) 1)
  (check-equal? (pvector-length (graph-in-edges g6 v1)) 1)

  ;; v2: out={}, in={e1,e2}
  (check-equal? (pvector-length (graph-out-edges g6 v2)) 0)
  (check-equal? (pvector-length (graph-in-edges g6 v2)) 2))

(test-case "graph-in-degree and graph-out-degree"
  (define-values (g1 v0) (graph-add-vertex graph-empty))
  (define-values (g2 v1) (graph-add-vertex g1))
  (define-values (g3 e0) (graph-add-edge g2 v0 v1))
  (define-values (g4 e1) (graph-add-edge g3 v0 v1))

  (check-equal? (graph-out-degree g4 v0) 2)
  (check-equal? (graph-in-degree g4 v0) 0)
  (check-equal? (graph-out-degree g4 v1) 0)
  (check-equal? (graph-in-degree g4 v1) 2))

(test-case "graph-edges-between"
  (define-values (g1 v0) (graph-add-vertex graph-empty))
  (define-values (g2 v1) (graph-add-vertex g1))
  (define-values (g3 v2) (graph-add-vertex g2))
  (define-values (g4 e0) (graph-add-edge g3 v0 v1))
  (define-values (g5 e1) (graph-add-edge g4 v0 v1))

  (check-equal? (pvector-length (graph-edges-between g5 v0 v1)) 2)
  (check-equal? (pvector-length (graph-edges-between g5 v1 v0)) 0)
  (check-equal? (pvector-length (graph-edges-between g5 v0 v2)) 0))

(test-case "graph-has-edge-to?"
  (define-values (g1 v0) (graph-add-vertex graph-empty))
  (define-values (g2 v1) (graph-add-vertex g1))
  (define-values (g3 e0) (graph-add-edge g2 v0 v1))

  (check-true (graph-has-edge-to? g3 v0 v1))
  (define has-back-edge? (graph-has-edge-to? g3 v1 v0))
  (check-false has-back-edge?))

(test-case "graph-successors"
  (define-values (g1 v0) (graph-add-vertex graph-empty))
  (define-values (g2 v1) (graph-add-vertex g1))
  (define-values (g3 v2) (graph-add-vertex g2))
  (define-values (g4 e0) (graph-add-edge g3 v0 v1))
  (define-values (g5 e1) (graph-add-edge g4 v0 v2))

  (define succs (graph-successors g5 v0))
  (check-equal? (pvector-length succs) 2)
  (define v1-val (vertex-id-val v1))
  (define v2-val (vertex-id-val v2))
  (check-true (pvector-has-vertex-val? succs v1-val))
  (define has-v2? (pvector-has-vertex-val? succs v2-val))
  (check-true has-v2?))

(test-case "graph-predecessors"
  (define-values (g1 v0) (graph-add-vertex graph-empty))
  (define-values (g2 v1) (graph-add-vertex g1))
  (define-values (g3 v2) (graph-add-vertex g2))
  (define-values (g4 e0) (graph-add-edge g3 v0 v2))
  (define-values (g5 e1) (graph-add-edge g4 v1 v2))

  (define preds (graph-predecessors g5 v2))
  (check-equal? (pvector-length preds) 2)
  (define v0-val (vertex-id-val v0))
  (define v1-val (vertex-id-val v1))
  (check-true (pvector-has-vertex-val? preds v0-val))
  (define has-v1? (pvector-has-vertex-val? preds v1-val))
  (check-true has-v1?))

;; ========================================
;; Iteration
;; ========================================

(test-case "in-graph-vertices"
  (define-values (g1 v0) (graph-add-vertex graph-empty))
  (define-values (g2 v1) (graph-add-vertex g1))
  (define-values (g3 v2) (graph-add-vertex g2))

  (define verts
    (for/list ([v (in-graph-vertices g3)])
      v))
  (check-equal? (length verts) 3)
  (check-not-false (member v0 verts))
  (check-not-false (member v1 verts))
  (define has-v2? (member v2 verts))
  (check-not-false has-v2?))

(test-case "in-graph-edges"
  (define-values (g1 v0) (graph-add-vertex graph-empty))
  (define-values (g2 v1) (graph-add-vertex g1))
  (define-values (g3 e0) (graph-add-edge g2 v0 v1))
  (define-values (g4 e1) (graph-add-edge g3 v1 v0))

  (define edges
    (for/list ([e (in-graph-edges g4)])
      e))
  (check-equal? (length edges) 2)
  (check-not-false (member e0 edges))
  (define has-e1? (member e1 edges))
  (check-not-false has-e1?))

(test-case "in-graph-successors"
  (define-values (g1 v0) (graph-add-vertex graph-empty))
  (define-values (g2 v1) (graph-add-vertex g1))
  (define-values (g3 v2) (graph-add-vertex g2))
  (define-values (g4 e0) (graph-add-edge g3 v0 v1))
  (define-values (g5 e1) (graph-add-edge g4 v0 v2))

  (define succs
    (for/list ([v (in-graph-successors g5 v0)])
      v))
  (check-equal? (length succs) 2))

;; ========================================
;; Complex Scenarios
;; ========================================

(test-case "diamond graph"
  ;;     v0
  ;;    /  \
  ;;   v1  v2
  ;;    \  /
  ;;     v3
  (define-values (g1 v0) (graph-add-vertex graph-empty))
  (define-values (g2 v1) (graph-add-vertex g1))
  (define-values (g3 v2) (graph-add-vertex g2))
  (define-values (g4 v3) (graph-add-vertex g3))
  (define-values (g5 e01) (graph-add-edge g4 v0 v1))
  (define-values (g6 e02) (graph-add-edge g5 v0 v2))
  (define-values (g7 e13) (graph-add-edge g6 v1 v3))
  (define-values (g8 e23) (graph-add-edge g7 v2 v3))

  (check-equal? (graph-vertex-count g8) 4)
  (check-equal? (graph-edge-count g8) 4)

  (check-equal? (graph-out-degree g8 v0) 2)
  (check-equal? (graph-in-degree g8 v3) 2)

  (check-equal? (pvector-length (graph-successors g8 v0)) 2)
  (check-equal? (pvector-length (graph-predecessors g8 v3)) 2))

(test-case "remove vertex in middle"
  (define-values (g1 v0) (graph-add-vertex graph-empty))
  (define-values (g2 v1) (graph-add-vertex g1))
  (define-values (g3 v2) (graph-add-vertex g2))
  (define-values (g4 e01) (graph-add-edge g3 v0 v1))
  (define-values (g5 e12) (graph-add-edge g4 v1 v2))

  ;; Remove v1 (middle vertex) with cascade
  (define g6 (graph-remove-vertex* g5 v1))

  (check-equal? (graph-vertex-count g6) 2)
  (check-equal? (graph-edge-count g6) 0)
  (check-true (graph-vertex? g6 v0))
  (check-false (graph-vertex? g6 v1))
  (define has-v2? (graph-vertex? g6 v2))
  (check-true has-v2?))

(displayln "All graph tests passed!")
