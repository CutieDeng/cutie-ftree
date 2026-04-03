#lang racket/base

;; ============================================================
;; Graph Unsafe Implementation Layer
;; ============================================================
;;
;; This module provides low-level graph operations that work directly
;; with raw integer vertex/edge IDs. These are intended for:
;; - Internal library use (scc.rkt, traversal.rkt, etc.)
;; - Performance-critical algorithms
;;
;; WARNING: These functions do NOT validate inputs. The caller is
;; responsible for ensuring vertex/edge IDs are valid.
;;
;; Users should prefer the safe API in cutie-ftree/graph.rkt
;; ============================================================

(require racket/match)
(require "../bitset.rkt")
(require "../ordered-map.rkt")
(require "../comparator.rkt")

;; ========================================
;; Graph Structure (re-export)
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
    (ordered-map-empty integer-compare))
  ) ; define graph-empty

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
;; Vertex Operations (Impl - raw integers)
;; ========================================

;; Add a new vertex, returns (values new-graph vertex-id-val)
;; Returns RAW INTEGER, not vertex-id struct
(define (graph-add-vertex-impl g)
  (define-values (g1 vid) (alloc-vertex-id g))
  (match-define (graph next-v next-e verts edges
                       v-cnt e-cnt e-src e-dst e-pair
                       in-e out-e adj) g1)
  (define empty-adj (ordered-map-empty integer-compare))
  (values
    (graph next-v next-e
           (bitset-add verts vid)
           edges
           (add1 v-cnt)
           e-cnt
           e-src e-dst e-pair
           (ordered-map-set in-e vid bitset-empty)
           (ordered-map-set out-e vid bitset-empty)
           (ordered-map-set adj vid empty-adj))
    vid)
  ) ; define graph-add-vertex-impl

;; Check if vertex exists (takes raw integer)
(define (graph-vertex?-impl g vid)
  (bitset-member? (graph-vertices g) vid))

;; Get all vertices as bitset (of raw integers)
(define (graph-vertices-set-impl g)
  (graph-vertices g))

;; Get vertex count (cached)
(define (graph-vertex-count-impl g)
  (graph-vertex-count* g))

;; Remove vertex (takes raw integer, must have no edges)
(define (graph-remove-vertex-impl g vid)
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

;; ========================================
;; Edge Operations (Impl - raw integers)
;; ========================================

;; Add edge from src to dst, returns (values new-graph edge-id-val)
;; Takes/returns RAW INTEGERS
(define (graph-add-edge-impl g src-v dst-v)
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
  (define new-out-e
    (ordered-map-set out-e src-v (bitset-add src-out eid))
    ) ; define new-out-e
  (define new-in-e
    (ordered-map-set in-e dst-v (bitset-add dst-in eid))
    ) ; define new-in-e

  ;; Update adjacency (three-level)
  (define src-adj
    (ordered-map-ref adj src-v (ordered-map-empty integer-compare))
    ) ; define src-adj
  (define src-dst-edges (ordered-map-ref src-adj dst-v bitset-empty))
  (define new-src-adj
    (ordered-map-set src-adj dst-v (bitset-add src-dst-edges eid))
    ) ; define new-src-adj
  (define new-adj (ordered-map-set adj src-v new-src-adj))

  (values
    (graph next-v next-e
           verts
           (bitset-add edges eid)
           v-cnt
           (add1 e-cnt)
           new-e-src new-e-dst e-pair
           new-in-e new-out-e new-adj)
    eid)
  ) ; define graph-add-edge-impl

;; Add edge pair (bidirectional), returns (values new-graph edge1-val edge2-val)
(define (graph-add-edge-pair-impl g v1 v2)
  (define-values (g1 e1) (graph-add-edge-impl g v1 v2))
  (define-values (g2 e2) (graph-add-edge-impl g1 v2 v1))

  ;; Link them as pairs
  (match-define (graph next-v next-e verts edges
                       v-cnt e-cnt e-src e-dst e-pair
                       in-e out-e adj) g2)

  (define new-e-pair
    (ordered-map-set (ordered-map-set e-pair e1 e2) e2 e1))

  (values
    (graph next-v next-e verts edges
           v-cnt e-cnt e-src e-dst new-e-pair
           in-e out-e adj)
    e1 e2))

;; Check if edge exists (takes raw integer)
(define (graph-edge?-impl g eid)
  (bitset-member? (graph-edges g) eid))

;; Get all edges as bitset (of raw integers)
(define (graph-edges-set-impl g)
  (graph-edges g))

;; Get edge count (cached)
(define (graph-edge-count-impl g)
  (graph-edge-count* g))

;; Get edge source vertex (returns raw integer)
(define (graph-edge-src-impl g eid)
  (match (ordered-map-query (graph-edge-src* g) eid)
    [#f #f]
    [(cons _ v) v]
    ) ; match: edge src
  ) ; define graph-edge-src-impl

;; Get edge destination vertex (returns raw integer)
(define (graph-edge-dst-impl g eid)
  (match (ordered-map-query (graph-edge-dst* g) eid)
    [#f #f]
    [(cons _ v) v]
    ) ; match: edge dst
  ) ; define graph-edge-dst-impl

;; Get edge endpoints as (values src-val dst-val)
(define (graph-edge-endpoints-impl g eid)
  (values (graph-edge-src-impl g eid) (graph-edge-dst-impl g eid))
  ) ; define graph-edge-endpoints-impl

;; Get paired edge (returns raw integer or #f)
(define (graph-edge-pair-impl g eid)
  (match (ordered-map-query (graph-edge-pair* g) eid)
    [#f #f]
    [(cons _ paired-id) paired-id]
    ) ; match: edge pair
  ) ; define graph-edge-pair-impl

;; Remove single edge (takes raw integer)
(define (graph-remove-edge-impl g eid)
  ;; Get endpoints
  (define src-v (graph-edge-src-impl g eid))
  (define dst-v (graph-edge-dst-impl g eid))

  ;; Check for paired edge
  (define paired (graph-edge-pair-impl g eid))

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
       (define-values (p1 _3) (ordered-map-delete e-pair eid))
       (define-values (p2 _4) (ordered-map-delete p1 paired))
       p2]
      [else
       (define-values (p1 _3) (ordered-map-delete e-pair eid))
       p1]
      ) ; cond: paired edge exists?
    ) ; define new-e-pair

  ;; Remove from out-edges[src]
  (define src-out (ordered-map-ref out-e src-v bitset-empty))
  (define new-out-e
    (ordered-map-set out-e src-v (bitset-remove src-out eid))
    ) ; define new-out-e

  ;; Remove from in-edges[dst]
  (define dst-in (ordered-map-ref in-e dst-v bitset-empty))
  (define new-in-e
    (ordered-map-set in-e dst-v (bitset-remove dst-in eid))
    ) ; define new-in-e

  ;; Remove from adjacency[src][dst]
  (define src-adj
    (ordered-map-ref adj src-v (ordered-map-empty integer-compare))
    ) ; define src-adj
  (define (drop-dst-bucket src-adj* dst-v*)
    (define (delete-two)
      (ordered-map-delete src-adj* dst-v*))
    (call-with-values
      delete-two
      (lambda (m _)
        (define out m)
        out
        ) ; lambda: pick first value
      ) ; call-with-values
    ) ; define drop-dst-bucket
  (define src-dst-edges (ordered-map-ref src-adj dst-v bitset-empty))
  (define new-src-dst-edges (bitset-remove src-dst-edges eid))
  (define new-src-adj
    (if (bitset-empty? new-src-dst-edges)
        (drop-dst-bucket src-adj dst-v)
        (ordered-map-set src-adj dst-v new-src-dst-edges))
    ) ; define new-src-adj
  (define new-adj (ordered-map-set adj src-v new-src-adj))

  (graph next-v next-e
         verts
         (bitset-remove edges eid)
         v-cnt
         (sub1 e-cnt)
         new-e-src new-e-dst new-e-pair
         new-in-e new-out-e new-adj))

;; Remove edge and its paired edge (takes raw integer)
(define (graph-remove-edge*-impl g eid)
  (define paired (graph-edge-pair-impl g eid))
  (define g1 (graph-remove-edge-impl g eid))
  (if (and paired (graph-edge?-impl g1 paired))
      (graph-remove-edge-impl g1 paired)
      g1))

;; ========================================
;; Adjacency Queries (Impl - raw integers)
;; ========================================

;; Get in-edges of vertex (bitset of edge vals)
(define (graph-in-edges-impl g vid)
  (ordered-map-ref (graph-in-edges* g) vid bitset-empty))

;; Get out-edges of vertex (bitset of edge vals)
(define (graph-out-edges-impl g vid)
  (ordered-map-ref (graph-out-edges* g) vid bitset-empty))

;; Get in-degree
(define (graph-in-degree-impl g vid)
  (bitset-count (graph-in-edges-impl g vid))
  ) ; define graph-in-degree-impl

;; Get out-degree
(define (graph-out-degree-impl g vid)
  (bitset-count (graph-out-edges-impl g vid))
  ) ; define graph-out-degree-impl

;; Get edges from src to dst (bitset of edge vals)
(define (graph-edges-between-impl g src-v dst-v)
  (define src-adj (ordered-map-ref (graph-adjacency g) src-v #f))
  (if src-adj
      (ordered-map-ref src-adj dst-v bitset-empty)
      bitset-empty)
  ) ; define graph-edges-between-impl

;; Check if there's any edge from src to dst
(define (graph-has-edge-to?-impl g src-v dst-v)
  (define edges-between
    (graph-edges-between-impl g src-v dst-v))
  (not (bitset-empty? edges-between))
  ) ; define graph-has-edge-to?-impl

;; Get successor vertices (bitset of vertex vals)
(define (graph-successors-impl g vid)
  (define v-adj (ordered-map-ref (graph-adjacency g) vid #f))
  (if v-adj
      (let ()
        (define kv-seq (in-ordered-map v-adj))
        (for/bitset ([kv kv-seq])
          (car kv))
        )
      bitset-empty)
  ) ; define graph-successors-impl

;; Get predecessor vertices (bitset of vertex vals)
(define (graph-predecessors-impl g vid)
  (define in-e (graph-in-edges-impl g vid))
  (define eid-seq (in-bitset in-e))
  (for/bitset ([eid eid-seq])
    (graph-edge-src-impl g eid))
  ) ; define graph-predecessors-impl

;; ========================================
;; Exports
;; ========================================

(provide
 ;; Graph struct (for internal access)
 graph graph? graph-empty
 graph-vertices graph-edges
 graph-vertex-count* graph-edge-count*
 graph-edge-src* graph-edge-dst* graph-edge-pair*
 graph-in-edges* graph-out-edges*
 graph-adjacency
 graph-next-vertex-id graph-next-edge-id

 ;; ID allocation (internal)
 alloc-vertex-id
 alloc-edge-id

 ;; Vertex operations
 graph-add-vertex-impl
 graph-vertex?-impl
 graph-vertices-set-impl
 graph-vertex-count-impl
 graph-remove-vertex-impl

 ;; Edge operations
 graph-add-edge-impl
 graph-add-edge-pair-impl
 graph-edge?-impl
 graph-edges-set-impl
 graph-edge-count-impl
 graph-edge-src-impl
 graph-edge-dst-impl
 graph-edge-endpoints-impl
 graph-edge-pair-impl
 graph-remove-edge-impl
 graph-remove-edge*-impl

 ;; Adjacency queries
 graph-in-edges-impl
 graph-out-edges-impl
 graph-in-degree-impl
 graph-out-degree-impl
 graph-edges-between-impl
 graph-has-edge-to?-impl
 graph-successors-impl
 graph-predecessors-impl)
