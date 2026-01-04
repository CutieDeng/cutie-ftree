#lang racket/base

(require rackunit
         racket/list)
(require "../graph.rkt")
(require "../graph/scc.rkt")
(require "../bitset.rkt")
(require "../pvector.rkt")
(require "../ordered-map.rkt")
(require "../comparator.rkt")

;; ========================================
;; Helper Functions
;; ========================================

;; Build a graph from adjacency list: '((0 . (1 2)) (1 . (2)) ...)
;; Returns (values graph vertex-id-list)
(define (build-graph-from-adj adj-list)
  (define n (length adj-list))
  ;; Add vertices
  (define-values (g vertices)
    (for/fold ([g graph-empty]
               [verts '()])
              ([_ (in-range n)])
      (define-values (g* v) (graph-add-vertex g))
      (values g* (cons v verts))))
  (define vertex-vec (list->vector (reverse vertices)))

  ;; Add edges
  (define final-g
    (for/fold ([g g])
              ([entry adj-list])
      (define src-idx (car entry))
      (define dst-indices (cdr entry))
      (for/fold ([g* g])
                ([dst-idx dst-indices])
        (define-values (g** _) (graph-add-edge g*
                                               (vector-ref vertex-vec src-idx)
                                               (vector-ref vertex-vec dst-idx)))
        g**)))

  (values final-g (vector->list vertex-vec)))

;; Convert pvector[bitset] to list[list[int]] for easier comparison
(define (sccs->lists sccs)
  (for/list ([scc (in-pvector sccs)])
    (sort (for/list ([v (in-bitset scc)]) v) <)))

;; ========================================
;; Basic SCC Tests
;; ========================================

(test-case "scc-empty-graph"
  (define sccs (graph-scc graph-empty))
  (check-equal? (pvector-length sccs) 0))

(test-case "scc-single-vertex"
  (define-values (g v) (graph-add-vertex graph-empty))
  (define sccs (graph-scc g))
  (check-equal? (pvector-length sccs) 1)
  (check-equal? (bitset-count (pvector-ref sccs 0)) 1)
  (check-true (bitset-member? (pvector-ref sccs 0) (vertex-id-val v))))

(test-case "scc-two-disconnected-vertices"
  (define-values (g1 v0) (graph-add-vertex graph-empty))
  (define-values (g2 v1) (graph-add-vertex g1))
  (define sccs (graph-scc g2))
  (check-equal? (pvector-length sccs) 2)
  ;; Each vertex is its own SCC
  (check-equal? (bitset-count (pvector-ref sccs 0)) 1)
  (check-equal? (bitset-count (pvector-ref sccs 1)) 1))

(test-case "scc-simple-chain"
  ;; 0 -> 1 -> 2
  ;; Three SCCs: {0}, {1}, {2}
  (define-values (g verts) (build-graph-from-adj '((0 . (1)) (1 . (2)) (2 . ()))))
  (define sccs (graph-scc g))
  (check-equal? (pvector-length sccs) 3)
  ;; Reverse topo order: sink first
  ;; {2} is sink, {0} is source
  (define scc-lists (sccs->lists sccs))
  (check-equal? (car scc-lists) '(2))  ; sink SCC first
  (check-equal? (last scc-lists) '(0)))  ; source SCC last

(test-case "scc-simple-cycle"
  ;; 0 -> 1 -> 2 -> 0 (cycle)
  ;; One SCC: {0, 1, 2}
  (define-values (g verts) (build-graph-from-adj '((0 . (1)) (1 . (2)) (2 . (0)))))
  (define sccs (graph-scc g))
  (check-equal? (pvector-length sccs) 1)
  (check-equal? (bitset-count (pvector-ref sccs 0)) 3)
  (define scc-lists (sccs->lists sccs))
  (check-equal? (car scc-lists) '(0 1 2)))

(test-case "scc-two-cycles-connected"
  ;; 0 -> 1 -> 0  (cycle1: {0,1})
  ;; 1 -> 2 -> 3 -> 2 (cycle2: {2,3})
  ;; Two SCCs: {0,1} and {2,3}
  (define-values (g verts) (build-graph-from-adj '((0 . (1)) (1 . (0 2)) (2 . (3)) (3 . (2)))))
  (define sccs (graph-scc g))
  (check-equal? (pvector-length sccs) 2)
  (define scc-lists (sccs->lists sccs))
  ;; {2,3} is sink (no outgoing edges to other SCCs)
  (check-equal? (car scc-lists) '(2 3))
  (check-equal? (cadr scc-lists) '(0 1)))

(test-case "scc-classic-example"
  ;; Classic example with 8 vertices
  ;; Graph: https://en.wikipedia.org/wiki/Strongly_connected_component
  ;;
  ;; 0 -> 1
  ;; 1 -> 2
  ;; 2 -> 0  (SCC1: {0,1,2})
  ;; 2 -> 3
  ;; 3 -> 4  (SCC2: {3})
  ;; 4 -> 5
  ;; 5 -> 6
  ;; 6 -> 4  (SCC3: {4,5,6})
  ;; 6 -> 7  (SCC4: {7})
  ;;
  (define-values (g verts)
    (build-graph-from-adj
     '((0 . (1))
       (1 . (2))
       (2 . (0 3))
       (3 . (4))
       (4 . (5))
       (5 . (6))
       (6 . (4 7))
       (7 . ()))))

  (define sccs (graph-scc g))
  (check-equal? (pvector-length sccs) 4)

  (define scc-lists (sccs->lists sccs))
  ;; Reverse topo order: sinks first
  ;; {7} has no outgoing - sink
  ;; {4,5,6} -> {7}
  ;; {3} -> {4,5,6}
  ;; {0,1,2} -> {3}
  (check-equal? (car scc-lists) '(7))
  (check-equal? (cadr scc-lists) '(4 5 6))
  (check-equal? (caddr scc-lists) '(3))
  (check-equal? (cadddr scc-lists) '(0 1 2)))

;; ========================================
;; Condensation Graph Tests
;; ========================================

(test-case "condensation-simple-chain"
  ;; 0 -> 1 -> 2
  (define-values (g verts) (build-graph-from-adj '((0 . (1)) (1 . (2)) (2 . ()))))
  (define-values (node->scc scc-nodes scc-successors) (graph-condensation g))

  ;; 3 SCCs
  (check-equal? (pvector-length scc-nodes) 3)

  ;; Check node->scc mapping
  ;; Each vertex should be in a different SCC
  (define q0 (ordered-map-query node->scc 0))
  (define q1 (ordered-map-query node->scc 1))
  (define q2 (ordered-map-query node->scc 2))
  (check-not-false q0)
  (check-not-false q1)
  (check-not-false q2)
  (define scc-of-v0 (cdr q0))  ; SCC ID containing vertex 0
  (define scc-of-v1 (cdr q1))  ; SCC ID containing vertex 1
  (define scc-of-v2 (cdr q2))  ; SCC ID containing vertex 2
  (check-true (not (= scc-of-v0 scc-of-v1)))
  (check-true (not (= scc-of-v1 scc-of-v2)))

  ;; Check scc-successors
  ;; Graph: 0 -> 1 -> 2
  ;; So: SCC(v0) -> SCC(v1) -> SCC(v2)
  (define succ-of-v0-scc (scc-successors scc-of-v0))
  (check-true (bitset-member? succ-of-v0-scc scc-of-v1))

  (define succ-of-v1-scc (scc-successors scc-of-v1))
  (check-true (bitset-member? succ-of-v1-scc scc-of-v2)))

(test-case "condensation-cycle"
  ;; 0 -> 1 -> 2 -> 0 (one SCC)
  (define-values (g verts) (build-graph-from-adj '((0 . (1)) (1 . (2)) (2 . (0)))))
  (define-values (node->scc scc-nodes scc-successors) (graph-condensation g))

  ;; 1 SCC
  (check-equal? (pvector-length scc-nodes) 1)

  ;; All nodes map to same SCC
  (define scc0 (cdr (ordered-map-query node->scc 0)))
  (define scc1 (cdr (ordered-map-query node->scc 1)))
  (define scc2 (cdr (ordered-map-query node->scc 2)))
  (check-equal? scc0 scc1)
  (check-equal? scc1 scc2)

  ;; No successors (self-contained)
  (check-true (bitset-empty? (scc-successors scc0))))

(test-case "condensation-diamond"
  ;;     1
  ;;    / \
  ;;   0   3
  ;;    \ /
  ;;     2
  ;; All separate SCCs
  (define-values (g verts)
    (build-graph-from-adj '((0 . (1 2)) (1 . (3)) (2 . (3)) (3 . ()))))
  (define-values (node->scc scc-nodes scc-successors) (graph-condensation g))

  ;; 4 SCCs
  (check-equal? (pvector-length scc-nodes) 4)

  ;; Check all have different SCC IDs
  (define ids
    (for/list ([i (in-range 4)])
      (cdr (ordered-map-query node->scc i))))
  (check-equal? (length (remove-duplicates ids)) 4))

(displayln "All graph-scc tests passed!")
