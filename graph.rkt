#lang racket/base

;; ============================================================
;; Graph: Safe MultiGraph API
;; ============================================================
;;
;; This is the safe, user-facing API for the Graph module.
;;
;; Key safety features:
;; - vertex-id and edge-id constructors are NOT exported
;; - Only graph operations can create valid IDs
;; - Type validation on all inputs
;; - Returns (pvector vertex-id) instead of raw bitsets
;;
;; For performance-critical internal code, use:
;;   (require cutie-ftree/graph/unsafe)
;; ============================================================

(require racket/match
         "pvector.rkt"
         "bitset.rkt"
         "ordered-map.rkt"
         "comparator.rkt"
         "graph/unsafe.rkt")

;; ========================================
;; ID Types (struct definitions)
;; ========================================

;; Keep struct definitions here for safe API
;; The constructors are NOT exported
(struct vertex-id (val) #:transparent)
(struct edge-id (val) #:transparent)

(define (vertex-id-compare a b)
  (integer-compare (vertex-id-val a) (vertex-id-val b))
  ) ; define vertex-id-compare

(define (edge-id-compare a b)
  (integer-compare (edge-id-val a) (edge-id-val b))
  ) ; define edge-id-compare

;; ========================================
;; Input Validation Helpers
;; ========================================

(define (check-vertex-id who g v pos)
  (unless (vertex-id? v)
    (raise-argument-error who "vertex-id?" pos v))
  (unless (graph-vertex?-impl g (vertex-id-val v))
    (error who "vertex does not exist in graph: ~a" v))
  ) ; define check-vertex-id

(define (check-edge-id who g e pos)
  (unless (edge-id? e)
    (raise-argument-error who "edge-id?" pos e))
  (unless (graph-edge?-impl g (edge-id-val e))
    (error who "edge does not exist in graph: ~a" e))
  ) ; define check-edge-id

;; ========================================
;; Vertex Operations (Safe API)
;; ========================================

;; Add a new vertex, returns (values new-graph vertex-id)
(define (graph-add-vertex g)
  (define-values (g* vid) (graph-add-vertex-impl g))
  (values g* (vertex-id vid))
  ) ; define graph-add-vertex

;; Check if vertex exists
(define (graph-vertex? g v)
  (if (vertex-id? v)
      (let ()
        (define vid (vertex-id-val v))
        (graph-vertex?-impl g vid))
      #f)
  ) ; define graph-vertex?

;; Get all vertices as pvector of vertex-id
(define (graph-vertices-set g)
  (define vertices (graph-vertices-set-impl g))
  (define vertices-seq (in-bitset vertices))
  (for/pvector ([v vertices-seq])
    (vertex-id v))
  ) ; define graph-vertices-set

;; Get vertex count (cached)
(define (graph-vertex-count g)
  (graph-vertex-count-impl g)
  ) ; define graph-vertex-count

;; Remove vertex (must have no edges)
(define (graph-remove-vertex g v)
  (check-vertex-id 'graph-remove-vertex g v 1)
  (define vid (vertex-id-val v))

  ;; Check no edges
  (define in-e (graph-in-edges-impl g vid))
  (define out-e (graph-out-edges-impl g vid))
  (unless (bitset-empty? in-e)
    (error 'graph-remove-vertex "vertex has in-edges: ~a" v))
  (unless (bitset-empty? out-e)
    (error 'graph-remove-vertex "vertex has out-edges: ~a" v))

  (graph-remove-vertex-impl g vid)
  ) ; define graph-remove-vertex

;; Remove vertex and all its edges (cascade delete)
(define (graph-remove-vertex* g v)
  (check-vertex-id 'graph-remove-vertex* g v 1)
  (define vid (vertex-id-val v))

  ;; Collect all edges to remove
  (define in-e (graph-in-edges-impl g vid))
  (define out-e (graph-out-edges-impl g vid))
  (define all-edges (bitset-union in-e out-e))
  (define all-edges-seq (in-bitset all-edges))

  ;; Remove all edges first
  (define g1
    (for/fold ([g g])
              ([eid all-edges-seq])
      (if (graph-edge?-impl g eid)
          (graph-remove-edge-impl g eid)
          g))
    ) ; define g1

  ;; Now remove the vertex itself
  (graph-remove-vertex-impl g1 vid)
  ) ; define graph-remove-vertex*

;; ========================================
;; Edge Operations (Safe API)
;; ========================================

;; Add edge from src to dst, returns (values new-graph edge-id)
(define (graph-add-edge g src dst)
  (check-vertex-id 'graph-add-edge g src 1)
  (check-vertex-id 'graph-add-edge g dst 2)
  (define src-id (vertex-id-val src))
  (define dst-id (vertex-id-val dst))
  (define-values (g* eid)
    (graph-add-edge-impl g src-id dst-id))
  (values g* (edge-id eid))
  ) ; define graph-add-edge

;; Add edge pair (bidirectional), returns (values new-graph edge1 edge2)
(define (graph-add-edge-pair g v1 v2)
  (check-vertex-id 'graph-add-edge-pair g v1 1)
  (check-vertex-id 'graph-add-edge-pair g v2 2)
  (define v1-id (vertex-id-val v1))
  (define v2-id (vertex-id-val v2))
  (define-values (g* e1 e2)
    (graph-add-edge-pair-impl g v1-id v2-id))
  (values g* (edge-id e1) (edge-id e2))
  ) ; define graph-add-edge-pair

;; Check if edge exists
(define (graph-edge? g e)
  (if (edge-id? e)
      (let ()
        (define eid (edge-id-val e))
        (graph-edge?-impl g eid))
      #f)
  ) ; define graph-edge?

;; Get all edges as pvector of edge-id
(define (graph-edges-set g)
  (define edges (graph-edges-set-impl g))
  (define edges-seq (in-bitset edges))
  (for/pvector ([e edges-seq])
    (edge-id e))
  ) ; define graph-edges-set

;; Get edge count (cached)
(define (graph-edge-count g)
  (graph-edge-count-impl g)
  ) ; define graph-edge-count

;; Get edge source vertex
(define (graph-edge-src g e)
  (check-edge-id 'graph-edge-src g e 1)
  (define eid (edge-id-val e))
  (define v (graph-edge-src-impl g eid))
  (vertex-id v)
  ) ; define graph-edge-src

;; Get edge destination vertex
(define (graph-edge-dst g e)
  (check-edge-id 'graph-edge-dst g e 1)
  (define eid (edge-id-val e))
  (define v (graph-edge-dst-impl g eid))
  (vertex-id v)
  ) ; define graph-edge-dst

;; Get edge endpoints as (values src dst)
(define (graph-edge-endpoints g e)
  (check-edge-id 'graph-edge-endpoints g e 1)
  (define eid (edge-id-val e))
  (define-values (src dst) (graph-edge-endpoints-impl g eid))
  (values (vertex-id src) (vertex-id dst))
  ) ; define graph-edge-endpoints

;; Get paired edge (or #f)
(define (graph-edge-pair g e)
  (check-edge-id 'graph-edge-pair g e 1)
  (define eid (edge-id-val e))
  (define paired (graph-edge-pair-impl g eid))
  (and paired (edge-id paired))
  ) ; define graph-edge-pair

;; Remove single edge
(define (graph-remove-edge g e)
  (check-edge-id 'graph-remove-edge g e 1)
  (graph-remove-edge-impl g (edge-id-val e))
  ) ; define graph-remove-edge

;; Remove edge and its paired edge (if exists)
(define (graph-remove-edge* g e)
  (check-edge-id 'graph-remove-edge* g e 1)
  (graph-remove-edge*-impl g (edge-id-val e))
  ) ; define graph-remove-edge*

;; Remove the single edge between src and dst (error if 0 or >1 edges)
(define (graph-remove-edge-between g src dst)
  (check-vertex-id 'graph-remove-edge-between g src 1)
  (check-vertex-id 'graph-remove-edge-between g dst 2)
  (define src-id (vertex-id-val src))
  (define dst-id (vertex-id-val dst))
  (define edges
    (graph-edges-between-impl g src-id dst-id))
  (cond
    [(bitset-empty? edges)
     (error 'graph-remove-edge-between "no edge from ~a to ~a" src dst)]
    [(> (bitset-count edges) 1)
     (error 'graph-remove-edge-between "multiple edges from ~a to ~a, use graph-remove-edges-between" src dst)]
    [else
     (define eid (bitset-min edges))
     (graph-remove-edge-impl g eid)]
    ) ; cond: edge multiplicity
  ) ; define graph-remove-edge-between

;; Remove all edges from src to dst
(define (graph-remove-edges-between g src dst)
  (check-vertex-id 'graph-remove-edges-between g src 1)
  (check-vertex-id 'graph-remove-edges-between g dst 2)
  (define src-id (vertex-id-val src))
  (define dst-id (vertex-id-val dst))
  (define edges
    (graph-edges-between-impl g src-id dst-id))
  (define edges-seq (in-bitset edges))
  (for/fold ([g g])
            ([eid edges-seq])
    (graph-remove-edge-impl g eid))
  ) ; define graph-remove-edges-between

;; ========================================
;; Adjacency Queries (Safe API)
;; ========================================

;; Get in-edges of vertex as pvector of edge-id
(define (graph-in-edges g v)
  (check-vertex-id 'graph-in-edges g v 1)
  (define vid (vertex-id-val v))
  (define edges (graph-in-edges-impl g vid))
  (define edges-seq (in-bitset edges))
  (for/pvector ([e edges-seq])
    (edge-id e))
  ) ; define graph-in-edges

;; Get out-edges of vertex as pvector of edge-id
(define (graph-out-edges g v)
  (check-vertex-id 'graph-out-edges g v 1)
  (define vid (vertex-id-val v))
  (define edges (graph-out-edges-impl g vid))
  (define edges-seq (in-bitset edges))
  (for/pvector ([e edges-seq])
    (edge-id e))
  ) ; define graph-out-edges

;; Get in-degree
(define (graph-in-degree g v)
  (check-vertex-id 'graph-in-degree g v 1)
  (define vid (vertex-id-val v))
  (graph-in-degree-impl g vid))

;; Get out-degree
(define (graph-out-degree g v)
  (check-vertex-id 'graph-out-degree g v 1)
  (define vid (vertex-id-val v))
  (graph-out-degree-impl g vid))

;; Get edges from src to dst as pvector of edge-id
(define (graph-edges-between g src dst)
  (check-vertex-id 'graph-edges-between g src 1)
  (check-vertex-id 'graph-edges-between g dst 2)
  (define src-id (vertex-id-val src))
  (define dst-id (vertex-id-val dst))
  (define edges (graph-edges-between-impl g src-id dst-id))
  (define edges-seq (in-bitset edges))
  (for/pvector ([e edges-seq])
    (edge-id e))
  ) ; define graph-edges-between

;; Check if there's any edge from src to dst
(define (graph-has-edge-to? g src dst)
  (check-vertex-id 'graph-has-edge-to? g src 1)
  (check-vertex-id 'graph-has-edge-to? g dst 2)
  (define src-id (vertex-id-val src))
  (define dst-id (vertex-id-val dst))
  (graph-has-edge-to?-impl g src-id dst-id))

;; Get successor vertices as pvector of vertex-id
(define (graph-successors g v)
  (check-vertex-id 'graph-successors g v 1)
  (define v-id (vertex-id-val v))
  (define vids (graph-successors-impl g v-id))
  (define vids-seq (in-bitset vids))
  (for/pvector ([vid vids-seq])
    (vertex-id vid))
  ) ; define graph-successors

;; Get predecessor vertices as pvector of vertex-id
(define (graph-predecessors g v)
  (check-vertex-id 'graph-predecessors g v 1)
  (define v-id (vertex-id-val v))
  (define vids (graph-predecessors-impl g v-id))
  (define vids-seq (in-bitset vids))
  (for/pvector ([vid vids-seq])
    (vertex-id vid))
  ) ; define graph-predecessors

;; ========================================
;; Iteration (Safe API)
;; ========================================

(require racket/generator)

;; Iterate over vertex-ids
(define (in-graph-vertices g)
  (in-generator
    (define vertices (graph-vertices-set-impl g))
    (for ([v (in-bitset vertices)])
      (define v^ (vertex-id v))
      (yield v^))
    ) ; in-generator
  ) ; define in-graph-vertices

;; Iterate over edge-ids
(define (in-graph-edges g)
  (in-generator
    (define edges (graph-edges-set-impl g))
    (for ([e (in-bitset edges)])
      (define e^ (edge-id e))
      (yield e^))
    ) ; in-generator
  ) ; define in-graph-edges

;; Iterate over (edge-id src dst) tuples for out-edges of a vertex
(define (in-graph-out-edges g v)
  (check-vertex-id 'in-graph-out-edges g v 1)
  (define vid (vertex-id-val v))
  (in-generator
    (define out-edges (graph-out-edges-impl g vid))
    (for ([eid (in-bitset out-edges)])
      (define-values (src dst) (graph-edge-endpoints-impl g eid))
      (define eid^ (edge-id eid))
      (define src^ (vertex-id src))
      (define dst^ (vertex-id dst))
      (define triple (values eid^ src^ dst^))
      (yield triple))
    ) ; in-generator
  ) ; define in-graph-out-edges

;; Iterate over successor vertex-ids
(define (in-graph-successors g v)
  (check-vertex-id 'in-graph-successors g v 1)
  (in-generator
    (define v-id (vertex-id-val v))
    (define succs (graph-successors-impl g v-id))
    (for ([vid (in-bitset succs)])
      (define v^ (vertex-id vid))
      (yield v^))
    ) ; in-generator
  ) ; define in-graph-successors

;; Iterate over predecessor vertex-ids
(define (in-graph-predecessors g v)
  (check-vertex-id 'in-graph-predecessors g v 1)
  (in-generator
    (define v-id (vertex-id-val v))
    (define preds (graph-predecessors-impl g v-id))
    (for ([vid (in-bitset preds)])
      (define v^ (vertex-id vid))
      (yield v^))
    ) ; in-generator
  ) ; define in-graph-predecessors

;; ========================================
;; Exports
;; ========================================

;; ID Types - NO constructors exported!
(provide vertex-id? vertex-id-val)
(provide edge-id? edge-id-val)
(provide vertex-id-compare edge-id-compare)

;; Graph struct - re-export from unsafe
(provide graph graph? graph-empty)

;; Vertex operations
(provide graph-add-vertex)
(provide graph-remove-vertex graph-remove-vertex*)
(provide graph-vertex? graph-vertices-set graph-vertex-count)

;; Edge operations
(provide graph-add-edge graph-add-edge-pair)
(provide graph-remove-edge graph-remove-edge*)
(provide graph-remove-edge-between graph-remove-edges-between)
(provide graph-edge? graph-edges-set graph-edge-count)
(provide graph-edge-src graph-edge-dst graph-edge-endpoints)
(provide graph-edge-pair)

;; Adjacency queries
(provide graph-in-edges graph-out-edges)
(provide graph-in-degree graph-out-degree)
(provide graph-edges-between graph-has-edge-to?)
(provide graph-successors graph-predecessors)

;; Iteration
(provide in-graph-vertices in-graph-edges)
(provide in-graph-out-edges)
(provide in-graph-successors in-graph-predecessors)
