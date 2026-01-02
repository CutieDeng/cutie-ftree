#lang racket/base

;; ============================================================
;; Graph: MultiGraph with automatic ID management
;; ============================================================
;;
;; Features:
;; - Automatic vertex/edge ID allocation (monotonically increasing)
;; - Multi-edge support (multiple edges between same vertices)
;; - Edge pairing (for bidirectional relationships)
;; - O(1) cached counts
;; - Three-level adjacency map: src → dst → edges
;; ============================================================

(require racket/match)
(require "bitset.rkt")
(require "ordered-map.rkt")
(require "comparator.rkt")

;; ========================================
;; ID Types
;; ========================================

(struct vertex-id (val) #:transparent)
(struct edge-id (val) #:transparent)

(define (vertex-id-compare a b)
  (integer-compare (vertex-id-val a) (vertex-id-val b)))

(define (edge-id-compare a b)
  (integer-compare (edge-id-val a) (edge-id-val b)))

;; ========================================
;; Graph Structure
;; ========================================

(struct graph
  (
    ;; ID Management
    next-vertex-id    ; integer: next new vertex ID
    next-edge-id      ; integer: next new edge ID

    ;; Active sets
    vertices          ; bitset: active vertex ID values
    edges             ; bitset: active edge ID values

    ;; Cache
    vertex-count*     ; integer: number of vertices
    edge-count*       ; integer: number of edges

    ;; Edge → Endpoint mapping
    edge-src*         ; ordered-map: edge-val → vertex-val
    edge-dst*         ; ordered-map: edge-val → vertex-val

    ;; Edge pairing
    edge-pair*        ; ordered-map: edge-val → edge-val

    ;; Vertex adjacency
    in-edges*         ; ordered-map: vertex-val → bitset
    out-edges*        ; ordered-map: vertex-val → bitset

    ;; Three-level nesting: adjacency[src][dst] = {edges...}
    adjacency         ; ordered-map: vertex-val → ordered-map → bitset
  )
  #:transparent)

;; ========================================
;; Constructor
;; ========================================

(define graph-empty
  (graph
    0                                      ; next-vertex-id
    0                                      ; next-edge-id
    bitset-empty                           ; vertices
    bitset-empty                           ; edges
    0                                      ; vertex-count*
    0                                      ; edge-count*
    (ordered-map-empty integer-compare)    ; edge-src*
    (ordered-map-empty integer-compare)    ; edge-dst*
    (ordered-map-empty integer-compare)    ; edge-pair*
    (ordered-map-empty integer-compare)    ; in-edges*
    (ordered-map-empty integer-compare)    ; out-edges*
    (ordered-map-empty integer-compare)))  ; adjacency

;; ========================================
;; ID Allocation Helpers
;; ========================================

;; Allocate a new vertex ID (always uses next available)
(define (alloc-vertex-id g)
  (match-define (graph next-v next-e verts edges
                       v-cnt e-cnt e-src e-dst e-pair
                       in-e out-e adj) g)
  (values (graph (add1 next-v) next-e
                 verts edges v-cnt e-cnt e-src e-dst e-pair
                 in-e out-e adj)
          next-v))

;; Allocate a new edge ID (always uses next available)
(define (alloc-edge-id g)
  (match-define (graph next-v next-e verts edges
                       v-cnt e-cnt e-src e-dst e-pair
                       in-e out-e adj) g)
  (values (graph next-v (add1 next-e)
                 verts edges v-cnt e-cnt e-src e-dst e-pair
                 in-e out-e adj)
          next-e))

;; ========================================
;; Vertex Operations
;; ========================================

;; Add a new vertex, returns (values new-graph vertex-id)
(define (graph-add-vertex g)
  (define-values (g1 vid) (alloc-vertex-id g))
  (match-define (graph next-v next-e verts edges
                       v-cnt e-cnt e-src e-dst e-pair
                       in-e out-e adj) g1)
  (values
    (graph next-v next-e
           (bitset-add verts vid)
           edges
           (add1 v-cnt)
           e-cnt
           e-src e-dst e-pair
           (ordered-map-set in-e vid bitset-empty)
           (ordered-map-set out-e vid bitset-empty)
           (ordered-map-set adj vid (ordered-map-empty integer-compare)))
    (vertex-id vid)))

;; Check if vertex exists
(define (graph-vertex? g v)
  (bitset-member? (graph-vertices g) (vertex-id-val v)))

;; Get all vertices as bitset
(define (graph-vertices-set g)
  (graph-vertices g))

;; Get vertex count (cached)
(define (graph-vertex-count g)
  (graph-vertex-count* g))

;; Remove vertex (must have no edges, otherwise error)
(define (graph-remove-vertex g v)
  (define vid (vertex-id-val v))
  (unless (graph-vertex? g v)
    (error 'graph-remove-vertex "vertex does not exist: ~a" v))

  ;; Check no edges
  (define in-e (graph-in-edges g v))
  (define out-e (graph-out-edges g v))
  (unless (bitset-empty? in-e)
    (error 'graph-remove-vertex "vertex has in-edges: ~a" v))
  (unless (bitset-empty? out-e)
    (error 'graph-remove-vertex "vertex has out-edges: ~a" v))

  ;; Remove the vertex
  (match-define (graph next-v next-e verts edges
                       v-cnt e-cnt e-src e-dst e-pair
                       in-e-map out-e-map adj) g)

  (define-values (new-in-e _1) (ordered-map-delete in-e-map vid))
  (define-values (new-out-e _2) (ordered-map-delete out-e-map vid))
  (define-values (new-adj _3) (ordered-map-delete adj vid))

  (graph next-v next-e
         (bitset-remove verts vid)
         edges
         (sub1 v-cnt)
         e-cnt
         e-src e-dst e-pair
         new-in-e new-out-e new-adj))

;; Remove vertex and all its edges (cascade delete)
(define (graph-remove-vertex* g v)
  (define vid (vertex-id-val v))
  (unless (graph-vertex? g v)
    (error 'graph-remove-vertex* "vertex does not exist: ~a" v))

  ;; Collect all edges to remove
  (define in-e (graph-in-edges g v))
  (define out-e (graph-out-edges g v))
  (define all-edges (bitset-union in-e out-e))

  ;; Remove all edges first
  (define g1
    (for/fold ([g g]) ([eid (in-bitset all-edges)])
      (if (graph-edge? g (edge-id eid))
          (graph-remove-edge g (edge-id eid))
          g)))

  ;; Now remove the vertex itself
  (graph-remove-vertex g1 v))

;; ========================================
;; Edge Operations
;; ========================================

;; Add edge from src to dst, returns (values new-graph edge-id)
(define (graph-add-edge g src dst)
  (define src-v (vertex-id-val src))
  (define dst-v (vertex-id-val dst))
  (unless (graph-vertex? g src)
    (error 'graph-add-edge "source vertex does not exist: ~a" src))
  (unless (graph-vertex? g dst)
    (error 'graph-add-edge "destination vertex does not exist: ~a" dst))

  (define-values (g1 eid) (alloc-edge-id g))
  (match-define (graph next-v next-e verts edges
                       v-cnt e-cnt e-src e-dst e-pair
                       in-e out-e adj) g1)

  ;; Update edge endpoints
  (define new-e-src (ordered-map-set e-src eid src-v))
  (define new-e-dst (ordered-map-set e-dst eid dst-v))

  ;; Update in-edges and out-edges
  (define src-out (ordered-map-ref out-e src-v bitset-empty))
  (define dst-in (ordered-map-ref in-e dst-v bitset-empty))
  (define new-out-e (ordered-map-set out-e src-v (bitset-add src-out eid)))
  (define new-in-e (ordered-map-set in-e dst-v (bitset-add dst-in eid)))

  ;; Update adjacency (three-level)
  (define src-adj (ordered-map-ref adj src-v (ordered-map-empty integer-compare)))
  (define src-dst-edges (ordered-map-ref src-adj dst-v bitset-empty))
  (define new-src-adj (ordered-map-set src-adj dst-v (bitset-add src-dst-edges eid)))
  (define new-adj (ordered-map-set adj src-v new-src-adj))

  (values
    (graph next-v next-e
           verts
           (bitset-add edges eid)
           v-cnt
           (add1 e-cnt)
           new-e-src new-e-dst e-pair
           new-in-e new-out-e new-adj)
    (edge-id eid)))

;; Add edge pair (bidirectional), returns (values new-graph edge1 edge2)
(define (graph-add-edge-pair g v1 v2)
  (define-values (g1 e1) (graph-add-edge g v1 v2))
  (define-values (g2 e2) (graph-add-edge g1 v2 v1))

  ;; Link them as pairs
  (define e1-val (edge-id-val e1))
  (define e2-val (edge-id-val e2))
  (match-define (graph next-v next-e verts edges
                       v-cnt e-cnt e-src e-dst e-pair
                       in-e out-e adj) g2)

  (define new-e-pair
    (ordered-map-set (ordered-map-set e-pair e1-val e2-val) e2-val e1-val))

  (values
    (graph next-v next-e verts edges
           v-cnt e-cnt e-src e-dst new-e-pair
           in-e out-e adj)
    e1 e2))

;; Check if edge exists
(define (graph-edge? g e)
  (bitset-member? (graph-edges g) (edge-id-val e)))

;; Get all edges as bitset
(define (graph-edges-set g)
  (graph-edges g))

;; Get edge count (cached)
(define (graph-edge-count g)
  (graph-edge-count* g))

;; Get edge source vertex
(define (graph-edge-src g e)
  (define eid (edge-id-val e))
  (match (ordered-map-query (graph-edge-src* g) eid)
    [#f (error 'graph-edge-src "edge does not exist: ~a" e)]
    [(cons _ v) (vertex-id v)]))

;; Get edge destination vertex
(define (graph-edge-dst g e)
  (define eid (edge-id-val e))
  (match (ordered-map-query (graph-edge-dst* g) eid)
    [#f (error 'graph-edge-dst "edge does not exist: ~a" e)]
    [(cons _ v) (vertex-id v)]))

;; Get edge endpoints as (values src dst)
(define (graph-edge-endpoints g e)
  (values (graph-edge-src g e) (graph-edge-dst g e)))

;; Get paired edge (or #f)
(define (graph-edge-pair g e)
  (define eid (edge-id-val e))
  (match (ordered-map-query (graph-edge-pair* g) eid)
    [#f #f]
    [(cons _ paired-id) (edge-id paired-id)]))

;; Remove single edge (unlinks pair if exists, but doesn't delete pair)
(define (graph-remove-edge g e)
  (define eid (edge-id-val e))
  (unless (graph-edge? g e)
    (error 'graph-remove-edge "edge does not exist: ~a" e))

  ;; Get endpoints
  (define src-v (vertex-id-val (graph-edge-src g e)))
  (define dst-v (vertex-id-val (graph-edge-dst g e)))

  ;; Check for paired edge
  (define paired (graph-edge-pair g e))

  (match-define (graph next-v next-e verts edges
                       v-cnt e-cnt e-src e-dst e-pair
                       in-e out-e adj) g)

  ;; Remove from edge-src and edge-dst
  (define-values (new-e-src _1) (ordered-map-delete e-src eid))
  (define-values (new-e-dst _2) (ordered-map-delete e-dst eid))

  ;; Remove from edge-pair (unlink both directions if paired)
  (define new-e-pair
    (cond
      [paired
       (define paired-val (edge-id-val paired))
       (define-values (p1 _3) (ordered-map-delete e-pair eid))
       (define-values (p2 _4) (ordered-map-delete p1 paired-val))
       p2]
      [else
       (define-values (p1 _3) (ordered-map-delete e-pair eid))
       p1]))

  ;; Remove from out-edges[src]
  (define src-out (ordered-map-ref out-e src-v bitset-empty))
  (define new-out-e (ordered-map-set out-e src-v (bitset-remove src-out eid)))

  ;; Remove from in-edges[dst]
  (define dst-in (ordered-map-ref in-e dst-v bitset-empty))
  (define new-in-e (ordered-map-set in-e dst-v (bitset-remove dst-in eid)))

  ;; Remove from adjacency[src][dst]
  (define src-adj (ordered-map-ref adj src-v (ordered-map-empty integer-compare)))
  (define src-dst-edges (ordered-map-ref src-adj dst-v bitset-empty))
  (define new-src-dst-edges (bitset-remove src-dst-edges eid))
  (define new-src-adj
    (if (bitset-empty? new-src-dst-edges)
        (let-values ([(m _) (ordered-map-delete src-adj dst-v)]) m)
        (ordered-map-set src-adj dst-v new-src-dst-edges)))
  (define new-adj (ordered-map-set adj src-v new-src-adj))

  (graph next-v next-e
         verts
         (bitset-remove edges eid)
         v-cnt
         (sub1 e-cnt)
         new-e-src new-e-dst new-e-pair
         new-in-e new-out-e new-adj))

;; Remove edge and its paired edge (if exists)
(define (graph-remove-edge* g e)
  (define paired (graph-edge-pair g e))
  (define g1 (graph-remove-edge g e))
  (if (and paired (graph-edge? g1 paired))
      (graph-remove-edge g1 paired)
      g1))

;; ========================================
;; Adjacency Queries
;; ========================================

;; Get in-edges of vertex (bitset)
(define (graph-in-edges g v)
  (define vid (vertex-id-val v))
  (ordered-map-ref (graph-in-edges* g) vid bitset-empty))

;; Get out-edges of vertex (bitset)
(define (graph-out-edges g v)
  (define vid (vertex-id-val v))
  (ordered-map-ref (graph-out-edges* g) vid bitset-empty))

;; Get in-degree
(define (graph-in-degree g v)
  (bitset-count (graph-in-edges g v)))

;; Get out-degree
(define (graph-out-degree g v)
  (bitset-count (graph-out-edges g v)))

;; Get edges from src to dst (bitset)
(define (graph-edges-between g src dst)
  (define src-v (vertex-id-val src))
  (define dst-v (vertex-id-val dst))
  (define src-adj (ordered-map-ref (graph-adjacency g) src-v #f))
  (if src-adj
      (ordered-map-ref src-adj dst-v bitset-empty)
      bitset-empty))

;; Check if there's any edge from src to dst
(define (graph-has-edge-to? g src dst)
  (not (bitset-empty? (graph-edges-between g src dst))))

;; Get successor vertices (bitset of vertex vals)
(define (graph-successors g v)
  (define vid (vertex-id-val v))
  (define v-adj (ordered-map-ref (graph-adjacency g) vid #f))
  (if v-adj
      (for/bitset ([kv (in-ordered-map v-adj)])
        (car kv))
      bitset-empty))

;; Get predecessor vertices (bitset of vertex vals)
(define (graph-predecessors g v)
  (define vid (vertex-id-val v))
  (define in-e (graph-in-edges g v))
  (for/bitset ([eid (in-bitset in-e)])
    (vertex-id-val (graph-edge-src g (edge-id eid)))))

;; ========================================
;; Iteration
;; ========================================

(require racket/generator)

;; Iterate over vertex-ids
(define (in-graph-vertices g)
  (in-generator
    (for ([v (in-bitset (graph-vertices g))])
      (yield (vertex-id v)))))

;; Iterate over edge-ids
(define (in-graph-edges g)
  (in-generator
    (for ([e (in-bitset (graph-edges g))])
      (yield (edge-id e)))))

;; Iterate over (edge-id src dst) tuples for out-edges of a vertex
(define (in-graph-out-edges g v)
  (in-generator
    (for ([eid (in-bitset (graph-out-edges g v))])
      (define e (edge-id eid))
      (yield (values e (graph-edge-src g e) (graph-edge-dst g e))))))

;; Iterate over successor vertex-ids
(define (in-graph-successors g v)
  (in-generator
    (for ([vid (in-bitset (graph-successors g v))])
      (yield (vertex-id vid)))))

;; Iterate over predecessor vertex-ids
(define (in-graph-predecessors g v)
  (in-generator
    (for ([vid (in-bitset (graph-predecessors g v))])
      (yield (vertex-id vid)))))

;; ========================================
;; Exports
;; ========================================

;; ID Types
(provide vertex-id vertex-id? vertex-id-val)
(provide edge-id edge-id? edge-id-val)
(provide vertex-id-compare edge-id-compare)

;; Graph struct
(provide graph graph? graph-empty)

;; Vertex operations
(provide graph-add-vertex)
(provide graph-remove-vertex graph-remove-vertex*)
(provide graph-vertex? graph-vertices-set graph-vertex-count)

;; Edge operations
(provide graph-add-edge graph-add-edge-pair)
(provide graph-remove-edge graph-remove-edge*)
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
