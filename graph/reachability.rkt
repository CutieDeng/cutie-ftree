#lang racket/base

;; ============================================================
;; Graph Algorithms: Reachability and Path Finding
;; ============================================================
;;
;; Two API flavors:
;;   1. Concrete: Direct Graph type input (graph-reachable-*, graph-find-path)
;;   2. Parameterized: Accepts any graph via callbacks (reachable-*, find-path)
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

(provide
  ;; Concrete API (Graph type)
  graph-reachable-from
  graph-reachable-from-set
  graph-find-path
  graph-all-paths

  ;; Parameterized API (callbacks)
  reachable-from
  reachable-from-set
  find-path
  all-paths)

;; ============================================================
;; Concrete API: Graph Type Input
;; ============================================================

;; graph-reachable-from: Graph, vertex-id -> bitset
;;
;; Find all vertices reachable from start.
;; Returns bitset of vertex-id-vals reachable from start.
;;
(define (graph-reachable-from g start)
  (define start-val (vertex-id-val start))
  (define visited bitset-empty)

  (define (visit v)
    (unless (bitset-member? visited v)
      (set! visited (bitset-add visited v))
      (define succs (graph-successors-impl g v))
      (define succ-seq (in-bitset/reverse succs))
      (for ([succ succ-seq])
        (visit succ)
        )
      ) ; unless: unseen vertex
    ) ; define visit

  (visit start-val)
  visited
  ) ; define graph-reachable-from

;; graph-reachable-from-set: Graph, bitset -> bitset
;;
;; Find all vertices reachable from any vertex in starts.
;; Returns bitset of vertex-id-vals reachable from any start.
;;
(define (graph-reachable-from-set g starts)
  (define visited bitset-empty)

  (define (visit v)
    (unless (bitset-member? visited v)
      (set! visited (bitset-add visited v))
      (define succs (graph-successors-impl g v))
      (define succ-seq (in-bitset/reverse succs))
      (for ([succ succ-seq])
        (visit succ)
        )
      ) ; unless: unseen vertex
    ) ; define visit

  (for ([start (in-bitset/reverse starts)])
    (visit start))

  visited
  ) ; define graph-reachable-from-set

;; graph-find-path: Graph, vertex-id, vertex-id -> pvector[vertex-val] or #f
;;
;; Find a path from start to end (if exists).
;; Returns pvector of vertex-id-vals (path), or #f if no path.
;;
(define (graph-find-path g start end)
  (define start-val (vertex-id-val start))
  (define end-val (vertex-id-val end))
  (define visited bitset-empty)

  (define (search v path)
    (cond
      [(= v end-val)
       (pvector-cons-right path v)]
      [(bitset-member? visited v) #f]
      [else
       (set! visited (bitset-add visited v))
       (define path* (pvector-cons-right path v))
       (define succs (graph-successors-impl g v))
       (define succ-seq (in-bitset/reverse succs))
       (for/or ([succ succ-seq])
         (search succ path*))
       ]
      ) ; cond: search
    ) ; define search

  (search start-val (pvector-empty))
  ) ; define graph-find-path

;; graph-all-paths: Graph, vertex-id, vertex-id -> pvector[pvector[vertex-val]]
;;
;; Find all paths from start to end.
;; Returns pvector of pvectors (all paths).
;;
(define (graph-all-paths g start end)
  (define start-val (vertex-id-val start))
  (define end-val (vertex-id-val end))

  (define (search v path visited)
    (cond
      [(= v end-val)
       (define one-path (pvector-cons-right path v))
       (pvector-cons-right (pvector-empty) one-path)
       ]
      [(bitset-member? visited v) (pvector-empty)]
      [else
       (define new-visited (bitset-add visited v))
       (define path* (pvector-cons-right path v))
       (define succs (graph-successors-impl g v))
       (define succ-seq (in-bitset/reverse succs))
       (define paths0 (pvector-empty))
       (for/fold ([paths paths0])
                 ([succ succ-seq])
         (define found (search succ path* new-visited))
         (pvector-append paths found))
       ]
      ) ; cond: search
    ) ; define search

  (search start-val (pvector-empty) bitset-empty)
  ) ; define graph-all-paths

;; ============================================================
;; Parameterized API: Callbacks
;; ============================================================

;; reachable-from: Find all nodes reachable from start
;; Parameters:
;;   node-compare   : comparator for nodes
;;   get-successors : node -> pvector of nodes
;;   start          : node - starting node
;; Returns: pvector of nodes reachable from start
;;
(define (reachable-from node-compare get-successors start)
  (define visited (ordered-map-empty node-compare))

  (define (visit node result)
    (cond
      [(ordered-map-has-key? visited node) result]
      [else
       (set! visited (ordered-map-set visited node #t))
       (define result* (pvector-cons-right result node))
       (define succs (get-successors node))
       (define succ-seq (in-pvector succs))
       (for/fold ([r result*])
                 ([succ succ-seq])
         (visit succ r))
       ]
      ) ; cond: visit
    ) ; define visit

  (visit start (pvector-empty))
  ) ; define reachable-from

;; reachable-from-set: Find all nodes reachable from any node in starts
;; Parameters:
;;   node-compare   : comparator for nodes
;;   get-successors : node -> pvector of nodes
;;   starts         : pvector of nodes - starting nodes
;; Returns: ordered-map (as set) of reachable nodes
;;
(define (reachable-from-set node-compare get-successors starts)
  (define visited (ordered-map-empty node-compare))

  (define (visit node)
    (unless (ordered-map-has-key? visited node)
      (set! visited (ordered-map-set visited node #t))
      (define succs (get-successors node))
      (define succ-seq (in-pvector succs))
      (for ([succ succ-seq])
        (visit succ)
        )
      ) ; unless: unseen node
    ) ; define visit

  (for ([start (in-pvector starts)])
    (visit start))

  visited
  ) ; define reachable-from-set

;; find-path: Find a path from start to end (if exists)
;; Parameters:
;;   node-compare   : comparator for nodes
;;   get-successors : node -> pvector of nodes
;;   start          : node
;;   end            : node
;; Returns: pvector of nodes (path), or #f if no path
;;
(define (find-path node-compare get-successors start end)
  (define visited (ordered-map-empty node-compare))

  (define (search node path)
    (cond
      [(equal? node end)
       (pvector-cons-right path node)]
      [(ordered-map-has-key? visited node) #f]
      [else
       (set! visited (ordered-map-set visited node #t))
       (define path* (pvector-cons-right path node))
       (define succs (get-successors node))
       (define succ-seq (in-pvector succs))
       (for/or ([succ succ-seq])
         (search succ path*))
       ]
      ) ; cond: search
    ) ; define search

  (search start (pvector-empty))
  ) ; define find-path

;; all-paths: Find all paths from start to end
;; Parameters:
;;   node-compare   : comparator for nodes
;;   get-successors : node -> pvector of nodes
;;   start          : node
;;   end            : node
;; Returns: pvector of pvector (all paths)
;;
(define (all-paths node-compare get-successors start end)
  (define (search node path visited)
    (cond
      [(equal? node end)
       (define one-path (pvector-cons-right path node))
       (pvector-cons-right (pvector-empty) one-path)
       ]
      [(ordered-map-has-key? visited node) (pvector-empty)]
      [else
       (define new-visited (ordered-map-set visited node #t))
       (define path* (pvector-cons-right path node))
       (define succs (get-successors node))
       (define succ-seq (in-pvector succs))
       (define paths0 (pvector-empty))
       (for/fold ([paths paths0])
                 ([succ succ-seq])
         (define found (search succ path* new-visited))
         (pvector-append paths found))
       ]
      ) ; cond: search
    ) ; define search

  (search start (pvector-empty) (ordered-map-empty node-compare))
  ) ; define all-paths
