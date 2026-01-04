#lang racket/base

;; ============================================================
;; Graph Algorithms: Traversal
;; ============================================================
;;
;; Two API flavors:
;;   1. Concrete: Direct Graph type input (graph-dfs-*, graph-bfs, graph-topo-sort)
;;   2. Parameterized: Accepts any graph via callbacks (dfs-*, bfs, topology-sort)
;;
;; ============================================================

(require racket/dict
         "../bitset.rkt"
         "../pvector.rkt"
         "../ordered-map.rkt"
         "../comparator.rkt"
         "unsafe.rkt")  ; Use unsafe impl for performance

;; Import vertex-id accessor from safe API
(require (only-in "../graph.rkt" vertex-id-val vertex-id?))

;; ============================================================
;; Internal Utilities
;; ============================================================

;; Reverse a pvector (using efficient reverse iteration)
(define (pvector-reverse pv)
  (for/pvector ([x (in-pvector-reverse pv)])
    x))

(provide
  ;; Concrete API (Graph type)
  graph-dfs-preorder
  graph-dfs-postorder
  graph-dfs-reverse-postorder
  graph-bfs
  graph-topo-sort

  ;; Parameterized API (callbacks)
  dfs-preorder
  dfs-postorder
  dfs-reverse-postorder
  bfs
  topology-sort)

;; ============================================================
;; Concrete API: Graph Type Input
;; ============================================================

;; graph-dfs-preorder: Graph, vertex-id -> pvector[vertex-val]
;;
;; DFS preorder traversal starting from given vertex.
;; Returns pvector of vertex-id-vals in preorder.
;;
(define (graph-dfs-preorder g start)
  (define visited bitset-empty)
  (define start-val (vertex-id-val start))

  (define (visit v result)
    (cond
      [(bitset-member? visited v) result]
      [else
       (set! visited (bitset-add visited v))
       (define result* (pvector-cons-right result v))
       (for/fold ([r result*])
                 ([succ (in-bitset/rev (graph-successors-impl g v))])
         (visit succ r))]))

  (visit start-val (pvector-empty)))

;; graph-dfs-postorder: Graph, vertex-id -> pvector[vertex-val]
;;
;; DFS postorder traversal starting from given vertex.
;; Returns pvector of vertex-id-vals in postorder.
;;
(define (graph-dfs-postorder g start)
  (define visited bitset-empty)
  (define start-val (vertex-id-val start))

  (define (visit v result)
    (cond
      [(bitset-member? visited v) result]
      [else
       (set! visited (bitset-add visited v))
       (define result*
         (for/fold ([r result])
                   ([succ (in-bitset/rev (graph-successors-impl g v))])
           (visit succ r)))
       (pvector-cons-right result* v)]))

  (visit start-val (pvector-empty)))

;; graph-dfs-reverse-postorder: Graph, vertex-id -> pvector[vertex-val]
;;
;; DFS reverse postorder traversal (topological order for DAGs).
;; Returns pvector of vertex-id-vals in reverse postorder.
;;
(define (graph-dfs-reverse-postorder g start)
  (pvector-reverse (graph-dfs-postorder g start)))

;; graph-bfs: Graph, vertex-id -> pvector[vertex-val]
;;
;; Breadth-first search starting from given vertex.
;; Returns pvector of vertex-id-vals in BFS order.
;;
(define (graph-bfs g start)
  (define start-val (vertex-id-val start))
  (define visited (bitset-add bitset-empty start-val))

  (let loop ([queue (pvector-cons-right (pvector-empty) start-val)]
             [result (pvector-empty)])
    (cond
      [(pvector-empty? queue) result]
      [else
       (define-values (v queue*) (pvector-pop-left queue))
       (define result* (pvector-cons-right result v))

       (define-values (new-queue new-visited)
         (for/fold ([q queue*] [vis visited])
                   ([succ (in-bitset/rev (graph-successors-impl g v))])
           (cond
             [(bitset-member? vis succ) (values q vis)]
             [else
              (values (pvector-cons-right q succ)
                      (bitset-add vis succ))])))

       (set! visited new-visited)
       (loop new-queue result*)])))

;; graph-topo-sort: Graph -> pvector[vertex-val] or #f
;;
;; Topological sort using Kahn's algorithm.
;; Returns pvector of vertex-id-vals in topological order,
;; or #f if a cycle exists.
;;
(define (graph-topo-sort g)
  (define vertices (graph-vertices-set-impl g))
  (define in-degree (ordered-map-empty integer-compare))

  ;; Calculate in-degrees
  (for ([v (in-bitset/rev vertices)])
    (define preds (graph-predecessors-impl g v))
    (set! in-degree
          (ordered-map-set in-degree v (bitset-count preds))))

  ;; Find nodes with zero in-degree
  (define initial-queue
    (for/fold ([q (pvector-empty)])
              ([v (in-bitset/rev vertices)])
      (if (= (dict-ref in-degree v 0) 0)
          (pvector-cons-right q v)
          q)))

  (define vertex-count (bitset-count vertices))

  (let loop ([queue initial-queue]
             [result (pvector-empty)]
             [degrees in-degree])
    (cond
      [(pvector-empty? queue)
       ;; Check if all nodes are processed (no cycle)
       (if (= (pvector-length result) vertex-count)
           result
           #f)]
      [else
       (define-values (v queue*) (pvector-pop-left queue))
       (define result* (pvector-cons-right result v))

       (define-values (new-queue new-degrees)
         (for/fold ([q queue*] [d degrees])
                   ([succ (in-bitset/rev (graph-successors-impl g v))])
           (define new-deg (- (dict-ref d succ 0) 1))
           (define d* (ordered-map-set d succ new-deg))
           (if (= new-deg 0)
               (values (pvector-cons-right q succ) d*)
               (values q d*))))

       (loop new-queue result* new-degrees)])))

;; ============================================================
;; Parameterized API: Callbacks
;; ============================================================

;; dfs-preorder: DFS preorder traversal
;; Parameters:
;;   node-compare   : comparator for nodes
;;   get-successors : node -> pvector of nodes
;;   start          : node - starting node
;; Returns: pvector of nodes in preorder
;;
(define (dfs-preorder node-compare get-successors start)
  (define visited (ordered-map-empty node-compare))

  (define (visit node result)
    (cond
      [(ordered-map-has-key? visited node) result]
      [else
       (set! visited (ordered-map-set visited node #t))
       (define result* (pvector-cons-right result node))
       (for/fold ([r result*])
                 ([succ (in-pvector (get-successors node))])
         (visit succ r))]))

  (visit start (pvector-empty)))

;; dfs-postorder: DFS postorder traversal
;; Parameters:
;;   node-compare   : comparator for nodes
;;   get-successors : node -> pvector of nodes
;;   start          : node - starting node
;; Returns: pvector of nodes in postorder
;;
(define (dfs-postorder node-compare get-successors start)
  (define visited (ordered-map-empty node-compare))

  (define (visit node result)
    (cond
      [(ordered-map-has-key? visited node) result]
      [else
       (set! visited (ordered-map-set visited node #t))
       (define result*
         (for/fold ([r result])
                   ([succ (in-pvector (get-successors node))])
           (visit succ r)))
       (pvector-cons-right result* node)]))

  (visit start (pvector-empty)))

;; dfs-reverse-postorder: DFS reverse postorder (topological order for DAGs)
;; Parameters:
;;   node-compare   : comparator for nodes
;;   get-successors : node -> pvector of nodes
;;   start          : node - starting node
;; Returns: pvector of nodes in reverse postorder
;;
(define (dfs-reverse-postorder node-compare get-successors start)
  (pvector-reverse (dfs-postorder node-compare get-successors start)))

;; bfs: Breadth-first search
;; Parameters:
;;   node-compare   : comparator for nodes
;;   get-successors : node -> pvector of nodes
;;   start          : node - starting node
;; Returns: pvector of nodes in BFS order
;;
(define (bfs node-compare get-successors start)
  (define visited (ordered-map-empty node-compare))
  (set! visited (ordered-map-set visited start #t))

  (let loop ([queue (pvector-cons-right (pvector-empty) start)]
             [result (pvector-empty)])
    (cond
      [(pvector-empty? queue) result]
      [else
       (define-values (node queue*) (pvector-pop-left queue))
       (define result* (pvector-cons-right result node))

       (define-values (new-queue new-visited)
         (for/fold ([q queue*] [v visited])
                   ([succ (in-pvector (get-successors node))])
           (cond
             [(ordered-map-has-key? v succ) (values q v)]
             [else
              (values (pvector-cons-right q succ)
                      (ordered-map-set v succ #t))])))

       (set! visited new-visited)
       (loop new-queue result*)])))

;; topology-sort: Topological sort using Kahn's algorithm
;; Parameters:
;;   node-compare     : comparator for nodes
;;   nodes            : pvector of nodes - all nodes
;;   get-successors   : node -> pvector of nodes
;;   get-predecessors : node -> pvector of nodes
;; Returns: pvector of nodes in topological order, or #f if cycle exists
;;
(define (topology-sort node-compare nodes get-successors get-predecessors)
  (define in-degree (ordered-map-empty node-compare))

  ;; Calculate in-degrees
  (for ([node (in-pvector nodes)])
    (set! in-degree
          (ordered-map-set in-degree node
                           (pvector-length (get-predecessors node)))))

  ;; Find nodes with zero in-degree
  (define initial-queue
    (for/fold ([q (pvector-empty)])
              ([node (in-pvector nodes)])
      (if (= (dict-ref in-degree node 0) 0)
          (pvector-cons-right q node)
          q)))

  (let loop ([queue initial-queue]
             [result (pvector-empty)]
             [degrees in-degree])
    (cond
      [(pvector-empty? queue)
       ;; Check if all nodes are processed (no cycle)
       (if (= (pvector-length result) (pvector-length nodes))
           result
           #f)]
      [else
       (define-values (node queue*) (pvector-pop-left queue))
       (define result* (pvector-cons-right result node))

       (define-values (new-queue new-degrees)
         (for/fold ([q queue*] [d degrees])
                   ([succ (in-pvector (get-successors node))])
           (define new-deg (- (dict-ref d succ 0) 1))
           (define d* (ordered-map-set d succ new-deg))
           (if (= new-deg 0)
               (values (pvector-cons-right q succ) d*)
               (values q d*))))

       (loop new-queue result* new-degrees)])))
