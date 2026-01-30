#lang racket/base

;; ============================================================
;; Simple Graph: Optimized for interference graphs
;; ============================================================
;;
;; Uses pvector[bitset] for O(log n) edge operations.
;; Designed for undirected graphs with integer vertices [0, n).
;; ============================================================

(require "pvector.rkt"
         "bitset.rkt")

;; ========================================
;; Data Structure
;; ========================================

;; simple-graph: undirected graph with vertices [0, n)
;; - size: integer - number of vertices
;; - adjacency: pvector[bitset] - adj[v] = bitset of neighbors
(struct simple-graph (size adjacency) #:transparent)

;; ========================================
;; Construction
;; ========================================

;; Create an empty graph with n vertices
(define (simple-graph-create n)
  (define adj
    (for/fold ([pv (pvector-empty)])
              ([_ (in-range n)])
      (pvector-cons-right pv bitset-empty)))
  (simple-graph n adj))

;; ========================================
;; Modification
;; ========================================

;; Add an undirected edge between v1 and v2
;; Returns new graph (functional update)
(define (simple-graph-add-edge g v1 v2)
  (define adj (simple-graph-adjacency g))
  ;; Add v2 to v1's neighbors
  (define adj1
    (pvector-set adj v1
                 (bitset-add (pvector-ref adj v1) v2)))
  ;; Add v1 to v2's neighbors
  (define adj2
    (pvector-set adj1 v2
                 (bitset-add (pvector-ref adj1 v2) v1)))
  (simple-graph (simple-graph-size g) adj2))

;; ========================================
;; Query
;; ========================================

;; Check if edge exists between v1 and v2 - O(log n)
(define (simple-graph-has-edge? g v1 v2)
  (define adj (simple-graph-adjacency g))
  (bitset-member? (pvector-ref adj v1) v2))

;; Get neighbors of v as a bitset - O(log n)
(define (simple-graph-neighbors g v)
  (pvector-ref (simple-graph-adjacency g) v))

;; Get degree of v - O(log n)
(define (simple-graph-degree g v)
  (bitset-count (pvector-ref (simple-graph-adjacency g) v)))

;; Get number of vertices
(define (simple-graph-vertex-count g)
  (simple-graph-size g))

;; Get number of edges (each undirected edge counted once)
(define (simple-graph-edge-count g)
  (quotient
   (for/sum ([i (in-range (simple-graph-size g))])
     (simple-graph-degree g i))
   2))

;; ========================================
;; Iteration
;; ========================================

;; Iterate over neighbors of v (returns sequence of integers)
(define (in-simple-graph-neighbors g v)
  (in-bitset (simple-graph-neighbors g v)))

;; ========================================
;; Exports
;; ========================================

(provide
 ;; Struct
 (struct-out simple-graph)

 ;; Construction
 simple-graph-create

 ;; Modification
 simple-graph-add-edge

 ;; Query
 simple-graph-has-edge?
 simple-graph-neighbors
 simple-graph-degree
 simple-graph-vertex-count
 simple-graph-edge-count

 ;; Iteration
 in-simple-graph-neighbors)
