#lang racket/base

;; ============================================================
;; Graph Algorithms: Strongly Connected Components
;; ============================================================
;;
;; Two API flavors:
;;   1. Concrete: Direct Graph type input (graph-scc, graph-condensation)
;;   2. Parameterized: Accepts any graph via callbacks (scc-tarjan, scc-kosaraju)
;;
;; Concrete API uses bitset for efficiency with integer vertex IDs.
;; Parameterized API uses pvector for arbitrary node types.
;;
;; ============================================================

(require racket/dict
         "../bitset.rkt"
         "../pvector.rkt"
         "../ordered-map.rkt"
         "../comparator.rkt"
         "unsafe.rkt")  ; Use unsafe impl for performance

(provide
  ;; Concrete API (Graph type)
  graph-scc
  graph-condensation

  ;; Parameterized API (callbacks)
  scc-tarjan
  scc-kosaraju
  condensation-graph

  ;; Utilities
  scc-id
  scc-members)

;; ============================================================
;; Concrete API: Graph Type Input
;; ============================================================

;; graph-scc: Graph -> pvector[bitset]
;;
;; Computes strongly connected components of a graph.
;; Returns a pvector where each element is a bitset of vertex-id-vals
;; representing one SCC.
;;
;; The order is reverse topological order (Tarjan's natural output):
;; - Sink SCCs (no outgoing edges to other SCCs) appear first
;; - Source SCCs appear last
;;
(define (graph-scc g)
  (define vertices (graph-vertices-set-impl g))  ; bitset of active vertex vals

  ;; Tarjan state
  (define index-counter 0)
  (define index (ordered-map-empty integer-compare))    ; vertex-val -> int
  (define lowlink (ordered-map-empty integer-compare))  ; vertex-val -> int
  (define on-stack bitset-empty)                        ; bitset of vertex-vals
  (define stack (pvector-empty))                        ; pvector of vertex-vals
  (define sccs (pvector-empty))                         ; pvector of bitset

  (define (strongconnect v)
    ;; v is a vertex-id-val (integer)
    (set! index (ordered-map-set index v index-counter))
    (set! lowlink (ordered-map-set lowlink v index-counter))
    (set! index-counter (add1 index-counter))

    (set! stack (pvector-cons-right stack v))
    (set! on-stack (bitset-add on-stack v))

    ;; Visit successors - graph-successors-impl returns bitset of vertex vals
    ;; Use in-bitset/reverse for ~5x better iteration performance
    (define succs (graph-successors-impl g v))
    (define succs-seq (in-bitset/reverse succs))
    (for ([w succs-seq])
      (cond
        [(not (ordered-map-has-key? index w))
         ;; w not yet visited
         (strongconnect w)
         (define v-low (dict-ref lowlink v 0))
         (define w-low (dict-ref lowlink w 0))
         (define new-low (min v-low w-low))
         (define lowlink^ (ordered-map-set lowlink v new-low))
         (set! lowlink lowlink^)
         ] ; cond branch: unvisited
        [(bitset-member? on-stack w)
         ;; w is on stack, part of current SCC
         (define v-low (dict-ref lowlink v 0))
         (define w-index (dict-ref index w 0))
         (define new-low (min v-low w-index))
         (define lowlink^ (ordered-map-set lowlink v new-low))
         (set! lowlink lowlink^)
         ] ; cond branch: on-stack
        ) ; cond
      ) ; for succs

    ;; If v is root of an SCC, pop the SCC from stack
    (when (= (dict-ref lowlink v 0) (dict-ref index v 0))
      (define-values (scc new-stack)
        (let loop ([component bitset-empty] [stk stack])
          (define-values (top stk*) (pvector-pop-right stk))
          (set! on-stack (bitset-remove on-stack top))
          (define new-component (bitset-add component top))
          (if (= top v)
              (values new-component stk*)
              (loop new-component stk*))
          ) ; let loop body
        ) ; let loop
      (set! stack new-stack)
      (define sccs^ (pvector-cons-right sccs scc))
      (set! sccs sccs^)
      ) ; when root-scc
    ) ; define strongconnect

  ;; Visit all vertices (use in-bitset/reverse for ~5x better performance)
  (define vertices-seq (in-bitset/reverse vertices))
  (for ([v vertices-seq])
    (unless (ordered-map-has-key? index v)
      (strongconnect v)
      ))

  sccs)

;; graph-condensation: Graph -> (values node->scc scc-nodes scc-successors)
;;
;; Builds the condensation graph (DAG of SCCs).
;;
;; Returns:
;;   node->scc     : ordered-map[vertex-val -> scc-idx]
;;   scc-nodes     : pvector[bitset] - same as graph-scc output
;;   scc-successors: procedure (scc-idx -> bitset of scc-idx)
;;
(define (graph-condensation g)
  (define sccs (graph-scc g))
  (define num-sccs (pvector-length sccs))

  ;; Build vertex -> SCC ID mapping
  (define sccs-seq (in-pvector sccs))
  (define id-seq (in-naturals))
  (define node->scc0 (ordered-map-empty integer-compare))
  (define node->scc
    (for/fold ([m node->scc0])
              ([scc sccs-seq]
               [id id-seq])
      (define scc-seq (in-bitset/reverse scc))
      (for/fold ([m* m]) ([v scc-seq])
        (ordered-map-set m* v id)
        ) ; inner for/fold
      )) ; outer for/fold

  ;; Build SCC adjacency (bitset-based)
  (define vertices (graph-vertices-set-impl g))
  (define vertices-seq (in-bitset/reverse vertices))
  (define scc-adj0 (ordered-map-empty integer-compare))
  (define empty-scc-neighbors bitset-empty)
  (define scc-adj
    (for/fold ([adj scc-adj0])
              ([v vertices-seq])
      (define src-scc (dict-ref node->scc v 0))
      (define succs (graph-successors-impl g v))
      (define succs-seq (in-bitset/reverse succs))
      (for/fold ([adj* adj])
                ([w succs-seq])
        (define dst-scc (dict-ref node->scc w 0))
        (if (= src-scc dst-scc)
            adj*
            (let ()
              (define existing (dict-ref adj* src-scc empty-scc-neighbors))
              (define updated (bitset-add existing dst-scc))
              (ordered-map-set adj* src-scc updated))
            ) ; if same-scc
        ) ; inner for/fold
      )) ; outer for/fold

  ;; SCC successors function
  (define (scc-successors scc-id)
    (dict-ref scc-adj scc-id bitset-empty))

  (values node->scc sccs scc-successors))

;; ============================================================
;; Parameterized API: Callbacks
;; ============================================================

;; scc-tarjan: Find SCCs using Tarjan's algorithm
;; Parameters:
;;   node-compare   : comparator for nodes
;;   nodes          : pvector of nodes - all nodes
;;   get-successors : node -> pvector of nodes
;; Returns: pvector of pvector - list of SCCs in reverse topological order
;;
(define (scc-tarjan node-compare nodes get-successors)
  (define index-counter 0)
  (define index (ordered-map-empty node-compare))
  (define lowlink (ordered-map-empty node-compare))
  (define on-stack (ordered-map-empty node-compare))
  (define stack (pvector-empty))
  (define sccs (pvector-empty))

  (define (strongconnect node)
    ;; Set index and lowlink
    (set! index (ordered-map-set index node index-counter))
    (set! lowlink (ordered-map-set lowlink node index-counter))
    (set! index-counter (+ index-counter 1))

    ;; Push to stack
    (set! stack (pvector-cons-right stack node))
    (set! on-stack (ordered-map-set on-stack node #t))

    ;; Visit successors
    (define succs (get-successors node))
    (for ([succ (in-pvector succs)])
      (cond
        [(not (ordered-map-has-key? index succ))
         ;; Not visited
         (strongconnect succ)
         (define node-low (dict-ref lowlink node 0))
         (define succ-low (dict-ref lowlink succ 0))
         (define new-low (min node-low succ-low))
         (define lowlink^ (ordered-map-set lowlink node new-low))
         (set! lowlink lowlink^)
         ] ; cond branch: unvisited
        [(ordered-map-has-key? on-stack succ)
         ;; On stack, part of current SCC
         (define node-low (dict-ref lowlink node 0))
         (define succ-index (dict-ref index succ 0))
         (define new-low (min node-low succ-index))
         (define lowlink^ (ordered-map-set lowlink node new-low))
         (set! lowlink lowlink^)
         ] ; cond branch: on-stack
        ) ; cond
      ) ; for succs

    ;; If root of SCC, pop and record
    (when (= (dict-ref lowlink node 0)
             (dict-ref index node 0))
      (define-values (scc new-stack)
        (let loop ([component (pvector-empty)] [stk stack])
          (define-values (top stk*) (pvector-pop-right stk))
          (set! on-stack (ordered-map-delete* on-stack top))
          (define new-component (pvector-cons-left component top))
          (if (equal? top node)
              (values new-component stk*)
              (loop new-component stk*))
          ) ; let loop body
        ) ; let loop
      (set! stack new-stack)
      (define sccs^ (pvector-cons-right sccs scc))
      (set! sccs sccs^)
      ) ; when root-scc
    ) ; define strongconnect

  (for ([node (in-pvector nodes)])
    (unless (ordered-map-has-key? index node)
      (strongconnect node)
      ))

  sccs)

;; scc-kosaraju: Find SCCs using Kosaraju's algorithm
;; Parameters:
;;   node-compare     : comparator for nodes
;;   nodes            : pvector of nodes - all nodes
;;   get-successors   : node -> pvector of nodes
;;   get-predecessors : node -> pvector of nodes
;; Returns: pvector of pvector - list of SCCs (each SCC is a pvector of nodes)
;;
(define (scc-kosaraju node-compare nodes get-successors get-predecessors)
  ;; Phase 1: DFS on original graph, record finish order
  (define visited (ordered-map-empty node-compare))
  (define finish-order (pvector-empty))

  (define (dfs1 node)
    (unless (ordered-map-has-key? visited node)
      (set! visited (ordered-map-set visited node #t))
      (define succs (get-successors node))
      (for ([succ (in-pvector succs)])
        (dfs1 succ))
      (define finish-order^ (pvector-cons-right finish-order node))
      (set! finish-order finish-order^)
      ))

  (for ([node (in-pvector nodes)])
    (dfs1 node))

  ;; Phase 2: DFS on reversed graph in reverse finish order
  (set! visited (ordered-map-empty node-compare))
  (define sccs (pvector-empty))

  (define (dfs2 node component)
    (cond
      [(ordered-map-has-key? visited node) component]
      [else
       (set! visited (ordered-map-set visited node #t))
       (define new-component (pvector-cons-right component node))
       (define preds (get-predecessors node))
       (define preds-seq (in-pvector preds))
       (for/fold ([comp new-component])
                 ([pred preds-seq])
         (dfs2 pred comp)
         ) ; for/fold preds
       ] ; cond else
      )) ; cond

  ;; Process in reverse finish order
  (define reversed-finish (pvector-reverse finish-order))
  (for ([node (in-pvector reversed-finish)])
    (unless (ordered-map-has-key? visited node)
      (define empty-component (pvector-empty))
      (define component (dfs2 node empty-component))
      (define sccs^ (pvector-cons-right sccs component))
      (set! sccs sccs^)
      ))

  sccs)

;; condensation-graph: Build condensation graph (DAG of SCCs)
;; Parameters:
;;   node-compare   : comparator for nodes
;;   nodes          : pvector of nodes - all nodes
;;   get-successors : node -> pvector of nodes
;; Returns: (values
;;            node->scc-id  : ordered-map - maps node to SCC id
;;            scc-nodes     : pvector - maps SCC id to pvector of nodes
;;            scc-successors : procedure - scc-id -> pvector of scc-ids)
;;
(define (condensation-graph node-compare nodes get-successors)
  (define sccs (scc-tarjan node-compare nodes get-successors))
  (define num-sccs (pvector-length sccs))

  ;; Build node -> SCC id mapping
  (define sccs-seq (in-pvector sccs))
  (define id-seq (in-naturals))
  (define node->scc-id0 (ordered-map-empty node-compare))
  (define node->scc-id
    (for/fold ([m node->scc-id0])
              ([scc sccs-seq]
               [id id-seq])
      (define nodes-seq (in-pvector scc))
      (for/fold ([m* m])
                ([node nodes-seq])
        (ordered-map-set m* node id)
        ) ; inner for/fold
      )) ; outer for/fold

  ;; Build SCC adjacency using ordered-map of ordered-map (as set)
  (define nodes-seq (in-pvector nodes))
  (define scc-adj0 (ordered-map-empty integer-compare))
  (define empty-neighbor-map (ordered-map-empty integer-compare))
  (define scc-adj
    (for/fold ([adj scc-adj0])
              ([node nodes-seq])
      (define src-scc (dict-ref node->scc-id node 0))
      (define succs (get-successors node))
      (define succs-seq (in-pvector succs))
      (for/fold ([adj* adj])
                ([succ succs-seq])
        (define dst-scc (dict-ref node->scc-id succ 0))
        (if (= src-scc dst-scc)
            adj*
            (let ()
              (define existing (dict-ref adj* src-scc empty-neighbor-map))
              (define updated (ordered-map-set existing dst-scc #t))
              (ordered-map-set adj* src-scc updated))
            ) ; if same-scc
        ) ; inner for/fold
      )) ; outer for/fold

  ;; SCC successors function
  (define (scc-successors scc-id)
    (define empty-adj (ordered-map-empty integer-compare))
    (define adj-map (dict-ref scc-adj scc-id empty-adj))
    (define keys (ordered-map-keys adj-map))
    (list->pvector keys))

  (values node->scc-id sccs scc-successors))

;; ============================================================
;; Internal Utilities
;; ============================================================

;; Reverse a pvector (using efficient reverse iteration)
(define (pvector-reverse pv)
  (define rev-seq (in-pvector-reverse pv))
  (for/pvector ([x rev-seq])
    x))

;; Helper: delete without error if key doesn't exist
(define (ordered-map-delete* om key)
  (cond
    [(ordered-map-has-key? om key)
     (define-values (m _removed) (ordered-map-delete om key))
     m]
    [else om]
    ) ; cond
  ) ; define ordered-map-delete*

;; Get SCC id for a node
;; Parameters:
;;   node->scc-id : ordered-map from condensation-graph
;;   node         : node
;; Returns: integer SCC id
;;
(define (scc-id node->scc-id node)
  (dict-ref node->scc-id node #f))

;; Get members of an SCC
;; Parameters:
;;   scc-nodes : pvector from condensation-graph
;;   scc-id    : integer SCC id
;; Returns: pvector of nodes
;;
(define (scc-members scc-nodes scc-id)
  (pvector-ref scc-nodes scc-id))
