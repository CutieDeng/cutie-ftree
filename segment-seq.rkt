#lang racket/base

(require racket/match racket/list)
(require "private/core.rkt" "private/core-algorithm.rkt")

;; ========================================
;; Segment Sequence based on Finger Tree
;; ========================================
;;
;; Dynamic segment tree supporting:
;; - O(log n) random access (ref/set)
;; - O(log n) range aggregate queries (sum, min, max, etc.)
;; - O(log n) insert at any position
;; - O(log n) delete at any position
;; - O(log n) split at any position
;; - O(1) amortized push/pop at ends
;; - O(log n) concat
;;
;; Measure: (size . aggregate) where size enables indexing

(struct segment-seq (config ft count) #:transparent)
(struct seg-config (identity combine extract) #:transparent)

(define (make-ft-config cfg)
  (match-define (seg-config id comb extract) cfg)
  (define (empty-measure)
    (cons 0 id)
    ) ; define empty-measure
  (define (elem-measure elem)
    (define agg (extract elem))
    (cons 1 agg)
    ) ; define elem-measure
  (define (merge-measure m1 m2)
    (define size1 (car m1))
    (define size2 (car m2))
    (define agg1 (cdr m1))
    (define agg2 (cdr m2))
    (define size-sum (+ size1 size2))
    (define agg-sum (comb agg1 agg2))
    (cons size-sum agg-sum)
    ) ; define merge-measure
  (ft:config
   empty-measure
   elem-measure
   merge-measure
   ) ; ft:config
  ) ; define make-ft-config

;; ========================================
;; Measure helpers
;; ========================================

(define (node-size cfg node depth)
  (if (= depth 0)
      1
      (let ()
        (define node-measure
          (match node
            [(node:2 v _ _) v]
            [(node:3 v _ _ _) v]
            ) ; match: node
          )
        (car node-measure)
        ) ; let: node measure at depth>0
      ) ; if: depth=0?
  ) ; define node-size

(define (digit-size cfg digit depth)
  (match digit
    [(digit:1 a) (node-size cfg a depth)]
    [(digit:2 a b)
     (define a-sz (node-size cfg a depth))
     (define b-sz (node-size cfg b depth))
     (+ a-sz b-sz)
     ] ; match branch: digit:2
    [(digit:3 a b c)
     (define a-sz (node-size cfg a depth))
     (define b-sz (node-size cfg b depth))
     (define c-sz (node-size cfg c depth))
     (+ a-sz b-sz c-sz)
     ] ; match branch: digit:3
    [(digit:4 a b c d)
     (define a-sz (node-size cfg a depth))
     (define b-sz (node-size cfg b depth))
     (define c-sz (node-size cfg c depth))
     (define d-sz (node-size cfg d depth))
     (+ a-sz b-sz c-sz d-sz)
     ] ; match branch: digit:4
    ) ; match: digit
  ) ; define digit-size

(define (ft-size cfg ft depth)
  (match ft
    [(ft:empty) 0]
    [(ft:single a) (node-size cfg a depth)]
    [(ft:deep v _ _ _) (car v)]
    ) ; match: ft
  ) ; define ft-size

(define (ft-agg cfg ft depth)
  (match ft
    [(ft:empty) (seg-config-identity cfg)]
    [(ft:single a)
     (if (= depth 0)
         ((seg-config-extract cfg) a)
         (let ()
           (define node-measure
             (match a
               [(node:2 v _ _) v]
               [(node:3 v _ _ _) v]
               ) ; match: ft single node
             )
           (cdr node-measure)
           ) ; let: node aggregate
         ) ; if: depth=0?
     ] ; match branch: ft:single
    [(ft:deep v _ _ _) (cdr v)]
    ) ; match: ft
  ) ; define ft-agg

;; ========================================
;; Constructors
;; ========================================

(define (segment-seq-new identity combine [extract values])
  (segment-seq (seg-config identity combine extract) (ft:empty) 0))

(define (segment-seq-sum) (segment-seq-new 0 +))
(define (segment-seq-min) (segment-seq-new +inf.0 min))
(define (segment-seq-max) (segment-seq-new -inf.0 max))
(define (segment-seq-product) (segment-seq-new 1 *))

(define (segment-seq-empty? ss)
  (zero? (segment-seq-count ss))
  ) ; define segment-seq-empty?
(define (segment-seq-length ss) (segment-seq-count ss))

(define (list->segment-seq lst identity combine [extract values])
  (define cfg (seg-config identity combine extract))
  (define core (make-ft-config cfg))
  (define init-ft (ft:empty))
  (define built-ft
    (for/fold ([t init-ft]) ([elem lst])
      (consR:impl core t elem 0)
      ) ; for/fold: list->ft
    ) ; define built-ft
  (segment-seq cfg
               built-ft
               (length lst))
  ) ; define list->segment-seq

;; ========================================
;; Random Access - O(log n) using direct navigation
;; ========================================

(define (segment-seq-ref ss idx)
  (match-define (segment-seq cfg ft cnt) ss)
  (when (or (< idx 0) (>= idx cnt))
    (error 'segment-seq-ref "index out of bounds: ~a (size: ~a)" idx cnt))
  (ref-ft cfg ft idx 0))

(define (ref-ft cfg ft idx depth)
  (match ft
    [(ft:single a) (ref-node cfg a idx depth)]
    [(ft:deep _ left inner right)
     (define left-sz (digit-size cfg left depth))
     (define inner-depth (add1 depth))
     (define inner-sz (ft-size cfg inner inner-depth))
     (define inner-start left-sz)
     (define right-start (+ left-sz inner-sz))
     (cond
       [(< idx left-sz) (ref-digit cfg left idx depth)]
       [(< idx right-start)
        (ref-ft cfg inner (- idx inner-start) inner-depth)
        ] ; cond branch: in inner
       [else
        (ref-digit cfg right (- idx right-start) depth)
        ] ; cond branch: in right
       ) ; cond: ft:deep ref
     ] ; match branch: ft:deep
    ) ; match: ft
  ) ; define ref-ft

(define (ref-digit cfg digit idx depth)
  (match digit
    [(digit:1 a) (ref-node cfg a idx depth)]
    [(digit:2 a b)
     (define a-sz (node-size cfg a depth))
     (if (< idx a-sz)
         (ref-node cfg a idx depth)
         (ref-node cfg b (- idx a-sz) depth)
         ) ; if: idx in a?
     ] ; match branch: digit:2
    [(digit:3 a b c)
     (define a-sz (node-size cfg a depth))
     (define b-sz (node-size cfg b depth))
     (cond
       [(< idx a-sz) (ref-node cfg a idx depth)]
       [(< idx (+ a-sz b-sz)) (ref-node cfg b (- idx a-sz) depth)]
       [else
        (ref-node cfg c (- idx a-sz b-sz) depth)
        ] ; cond branch: digit:3 c
       ) ; cond: digit:3
     ] ; match branch: digit:3
    [(digit:4 a b c d)
     (define a-sz (node-size cfg a depth))
     (define b-sz (node-size cfg b depth))
     (define c-sz (node-size cfg c depth))
     (cond
       [(< idx a-sz) (ref-node cfg a idx depth)]
       [(< idx (+ a-sz b-sz)) (ref-node cfg b (- idx a-sz) depth)]
       [(< idx (+ a-sz b-sz c-sz)) (ref-node cfg c (- idx a-sz b-sz) depth)]
       [else
        (ref-node cfg d (- idx a-sz b-sz c-sz) depth)
        ] ; cond branch: digit:4 d
       ) ; cond: digit:4
     ] ; match branch: digit:4
    ) ; match: digit
  ) ; define ref-digit

(define (ref-node cfg node idx depth)
  (if (= depth 0)
      node
      (match node
        [(node:2 _ a b)
         (define sub-depth (sub1 depth))
         (define a-sz (node-size cfg a sub-depth))
         (if (< idx a-sz)
             (ref-node cfg a idx sub-depth)
             (ref-node cfg b (- idx a-sz) sub-depth)
             ) ; if: idx in node:2 left?
         ] ; match branch: node:2
        [(node:3 _ a b c)
         (define sub-depth (sub1 depth))
         (define a-sz (node-size cfg a sub-depth))
         (define b-sz (node-size cfg b sub-depth))
         (define b-start a-sz)
         (define c-start (+ a-sz b-sz))
         (cond
           [(< idx b-start) (ref-node cfg a idx sub-depth)]
           [(< idx c-start) (ref-node cfg b (- idx b-start) sub-depth)]
           [else
            (ref-node cfg c (- idx c-start) sub-depth)
            ] ; cond branch: node:3 right
           ) ; cond: node:3
         ] ; match branch: node:3
        ) ; match: node
      ) ; if: depth=0?
  ) ; define ref-node

;; ========================================
;; Set - O(log n)
;; ========================================

(define (segment-seq-set ss idx val)
  (match-define (segment-seq cfg ft cnt) ss)
  (when (or (< idx 0) (>= idx cnt))
    (error 'segment-seq-set "index out of bounds: ~a (size: ~a)" idx cnt))
  (define core (make-ft-config cfg))
  (define new-ft (set-ft cfg core ft idx val 0))
  (segment-seq cfg new-ft cnt)
  ) ; define segment-seq-set

(define (set-ft cfg core ft idx val depth)
  (match ft
    [(ft:single a)
     (define a^ (set-node cfg core a idx val depth))
     (ft:single a^)
     ] ; match branch: ft:single
    [(ft:deep _ left inner right)
     (define left-sz (digit-size cfg left depth))
     (define inner-depth (add1 depth))
     (define inner-sz (ft-size cfg inner inner-depth))
     (define as (ft:config-assoc core))
     (define right-start (+ left-sz inner-sz))
     (cond
       [(< idx left-sz)
        (define new-left (set-digit cfg core left idx val depth))
        (define left-m (measure:digit core new-left depth))
        (define inner-m (measure:ft core inner inner-depth))
        (define right-m (measure:digit core right depth))
        (define new-v (as (as left-m inner-m) right-m))
        (ft:deep new-v new-left inner right)]
       [(< idx right-start)
        (define new-inner (set-ft cfg core inner (- idx left-sz) val inner-depth))
        (define left-m (measure:digit core left depth))
        (define inner-m (measure:ft core new-inner inner-depth))
        (define right-m (measure:digit core right depth))
        (define new-v (as (as left-m inner-m) right-m))
        (ft:deep new-v left new-inner right)]
       [else
        (define new-right (set-digit cfg core right (- idx right-start) val depth))
        (define left-m (measure:digit core left depth))
        (define inner-m (measure:ft core inner inner-depth))
        (define right-m (measure:digit core new-right depth))
        (define new-v (as (as left-m inner-m) right-m))
        (ft:deep new-v left inner new-right)]
       ) ; cond: set-ft path
     ] ; match branch: ft:deep
    ) ; match: ft
  ) ; define set-ft

(define (set-digit cfg core digit idx val depth)
  (match digit
    [(digit:1 a)
     (define a^ (set-node cfg core a idx val depth))
     (digit:1 a^)
     ] ; match branch: digit:1
    [(digit:2 a b)
     (define a-sz (node-size cfg a depth))
     (if (< idx a-sz)
         (digit:2 (set-node cfg core a idx val depth) b)
         (digit:2 a (set-node cfg core b (- idx a-sz) val depth))
         ) ; if: set in digit:2
     ] ; match branch: digit:2
    [(digit:3 a b c)
     (define a-sz (node-size cfg a depth))
     (define b-sz (node-size cfg b depth))
     (cond
       [(< idx a-sz) (digit:3 (set-node cfg core a idx val depth) b c)]
       [(< idx (+ a-sz b-sz)) (digit:3 a (set-node cfg core b (- idx a-sz) val depth) c)]
       [else
        (digit:3 a b (set-node cfg core c (- idx a-sz b-sz) val depth))
        ] ; cond branch: set digit:3 c
       ) ; cond: digit:3
     ] ; match branch: digit:3
    [(digit:4 a b c d)
     (define a-sz (node-size cfg a depth))
     (define b-sz (node-size cfg b depth))
     (define c-sz (node-size cfg c depth))
     (cond
       [(< idx a-sz) (digit:4 (set-node cfg core a idx val depth) b c d)]
       [(< idx (+ a-sz b-sz)) (digit:4 a (set-node cfg core b (- idx a-sz) val depth) c d)]
       [(< idx (+ a-sz b-sz c-sz)) (digit:4 a b (set-node cfg core c (- idx a-sz b-sz) val depth) d)]
       [else
        (digit:4 a b c (set-node cfg core d (- idx a-sz b-sz c-sz) val depth))
        ] ; cond branch: set digit:4 d
       ) ; cond: digit:4
     ] ; match branch: digit:4
    ) ; match: digit
  ) ; define set-digit

(define (set-node cfg core node idx val depth)
  (if (= depth 0)
      val
      (match node
        [(node:2 _ a b)
         (define sub-depth (sub1 depth))
         (define a-sz (node-size cfg a sub-depth))
         (if (< idx a-sz)
             (build-node2 core (set-node cfg core a idx val sub-depth) b sub-depth)
             (build-node2 core a (set-node cfg core b (- idx a-sz) val sub-depth) sub-depth)
             ) ; if: set in node:2
         ] ; match branch: node:2
        [(node:3 _ a b c)
         (define sub-depth (sub1 depth))
         (define a-sz (node-size cfg a sub-depth))
         (define b-sz (node-size cfg b sub-depth))
         (define b-start a-sz)
         (define c-start (+ a-sz b-sz))
         (cond
           [(< idx b-start)
            (build-node3 core (set-node cfg core a idx val sub-depth) b c sub-depth)
            ] ; cond branch: set node:3 a
           [(< idx c-start)
            (build-node3 core a (set-node cfg core b (- idx b-start) val sub-depth) c sub-depth)
            ] ; cond branch: set node:3 b
           [else
            (build-node3 core a b (set-node cfg core c (- idx c-start) val sub-depth) sub-depth)
            ] ; cond branch: set node:3 c
           ) ; cond: node:3
         ] ; match branch: node:3
        ) ; match: node
      ) ; if: depth=0?
  ) ; define set-node

;; ========================================
;; Push/Pop - O(1) amortized
;; ========================================

(define (segment-seq-push-back ss val)
  (match-define (segment-seq cfg ft cnt) ss)
  (define core (make-ft-config cfg))
  (define ft^ (consR:impl core ft val 0))
  (segment-seq cfg ft^ (add1 cnt))
  ) ; define segment-seq-push-back

(define (segment-seq-push-front ss val)
  (match-define (segment-seq cfg ft cnt) ss)
  (define core (make-ft-config cfg))
  (define ft^ (consL:impl core ft val 0))
  (segment-seq cfg ft^ (add1 cnt))
  ) ; define segment-seq-push-front

(define (segment-seq-pop-back ss)
  (match-define (segment-seq cfg ft cnt) ss)
  (when (zero? cnt) (error 'segment-seq-pop-back "empty"))
  (define-values (elem new-ft) (hdR:impl (make-ft-config cfg) ft 0))
  (values (segment-seq cfg new-ft (sub1 cnt)) elem))

(define (segment-seq-pop-front ss)
  (match-define (segment-seq cfg ft cnt) ss)
  (when (zero? cnt) (error 'segment-seq-pop-front "empty"))
  (define-values (elem new-ft) (hdL:impl (make-ft-config cfg) ft 0))
  (values (segment-seq cfg new-ft (sub1 cnt)) elem))

;; ========================================
;; Insert - O(log n) using direct insertion with split propagation
;; Based on pvector's approach
;; ========================================

(define (segment-seq-insert ss idx val)
  (match-define (segment-seq cfg ft cnt) ss)
  (when (or (< idx 0) (> idx cnt))
    (error 'segment-seq-insert "index out of bounds: ~a (size: ~a)" idx cnt))
  (define core (make-ft-config cfg))
  (cond
    [(ft:empty? ft)
     (segment-seq cfg (ft:single val) 1)]
    [(= idx cnt)
     (define ft^ (consR:impl core ft val 0))
     (segment-seq cfg ft^ (add1 cnt))
     ] ; cond branch: append
    [else
     (define new-ft (seg-insert-ft core cfg ft idx val 0))
     (segment-seq cfg new-ft (add1 cnt))
     ] ; cond branch: insert middle
    ) ; cond: segment-seq-insert
  ) ; define segment-seq-insert

;; Insert into ft, returns new ft
(define (seg-insert-ft core cfg ft idx val depth)
  (match ft
    [(ft:single x)
     (define-values (x0 x1) (seg-insert-node core cfg x idx val depth))
     (if x1
         (let ()
           (define as (ft:config-assoc core))
           (define x0m (seg-node-measure core x0 depth))
           (define x1m (seg-node-measure core x1 depth))
           (define v (as x0m x1m))
           (define empty-inner (ft:empty))
           (ft:deep v (digit:1 x0) empty-inner (digit:1 x1))
           ) ; let: single split
         (ft:single x0)
         ) ; if: node split
     ] ; match branch: ft:single
    [(ft:deep _ left inner right)
     (define left-sz (measure:digit core left depth))
     (define inner-depth (add1 depth))
     (define inner-sz (measure:ft core inner inner-depth))
     (define right-m (measure:digit core right depth))
     (define left-sz-val (car left-sz))
     (define inner-sz-val (car inner-sz))
     (define left-inner-sz (+ left-sz-val inner-sz-val))
     (cond
       [(<= left-inner-sz idx)
        ;; Insert in right digit
        (define right-lst (seg-insert-digit core cfg right (- idx left-inner-sz) val depth))
        (seg-handle-right-insert core left inner right-lst depth)]
       [(<= left-sz-val idx)
        ;; Insert in inner
        (define inner^ (seg-insert-ft core cfg inner (- idx left-sz-val) val inner-depth))
        (define as (ft:config-assoc core))
        (define new-v (as (as left-sz (measure:ft core inner^ inner-depth))
                          right-m))
        (ft:deep new-v left inner^ right)]
       [else
       ;; Insert in left digit
        (define left-lst (seg-insert-digit core cfg left idx val depth))
        (seg-handle-left-insert core left-lst inner right depth)]
       ) ; cond: ft:deep
     ] ; match branch: ft:deep
    ) ; match: ft
  ) ; define seg-insert-ft

;; Insert into node, returns (values new-node maybe-split-node)
(define (seg-insert-node core cfg node idx val depth)
  (if (= depth 0)
      ;; At element level: "split" means insert before
      (values val node)
      (match node
        [(node:2 _ x0 x1)
         (define sub-depth (sub1 depth))
         (define x0-m (seg-node-measure core x0 sub-depth))
         (define x0-sz (car x0-m))
         (cond
           [(<= x0-sz idx)
            ;; Insert in x1
           (define-values (x1^ x2^) (seg-insert-node core cfg x1 (- idx x0-sz) val sub-depth))
           (if x2^
               (values (build-node3 core x0 x1^ x2^ sub-depth) #f)
               (values (build-node2 core x0 x1^ sub-depth) #f)
               ) ; if: x2^ split
           ] ; cond branch: insert in x1
           [else
           ;; Insert in x0
            (define-values (x0^ x1^) (seg-insert-node core cfg x0 idx val sub-depth))
            (if x1^
                (values (build-node3 core x0^ x1^ x1 sub-depth) #f)
                (values (build-node2 core x0^ x1 sub-depth) #f)
                ) ; if: x1^ split
            ] ; cond branch: insert in x0
           ) ; cond: node:2
         ] ; match branch: node:2
        [(node:3 _ x0 x1 x2)
         (define sub-depth (sub1 depth))
         (define x0-m (seg-node-measure core x0 sub-depth))
         (define x1-m (seg-node-measure core x1 sub-depth))
         (define x0-sz (car x0-m))
         (define x1-sz (car x1-m))
         (define x0-x1-sz (+ x0-sz x1-sz))
         (cond
           [(<= x0-x1-sz idx)
            ;; Insert in x2
            (define-values (x2^ x3^) (seg-insert-node core cfg x2 (- idx x0-x1-sz) val sub-depth))
            (if x3^
                ;; Split: (x0 x1) and (x2^ x3^)
                (values (build-node2 core x0 x1 sub-depth)
                        (build-node2 core x2^ x3^ sub-depth))
                (values (build-node3 core x0 x1 x2^ sub-depth) #f)
                ) ; if: x3^ split
           ] ; cond branch: insert in x2
           [(<= x0-sz idx)
            ;; Insert in x1
            (define-values (x1^ x2^) (seg-insert-node core cfg x1 (- idx x0-sz) val sub-depth))
            (if x2^
                ;; Split: (x0 x1^) and (x2^ x2)
                (values (build-node2 core x0 x1^ sub-depth)
                        (build-node2 core x2^ x2 sub-depth))
                (values (build-node3 core x0 x1^ x2 sub-depth) #f)
                ) ; if: x2^ split
           ] ; cond branch: insert in x1
           [else
           ;; Insert in x0
            (define-values (x0^ x1^) (seg-insert-node core cfg x0 idx val sub-depth))
            (if x1^
                ;; Split: (x0^ x1^) and (x1 x2)
                (values (build-node2 core x0^ x1^ sub-depth)
                        (build-node2 core x1 x2 sub-depth))
                (values (build-node3 core x0^ x1 x2 sub-depth) #f)
                ) ; if: x1^ split
            ] ; cond branch: insert in x0
           ) ; cond: node:3
         ] ; match branch: node:3
        ) ; match: node
      ) ; if: depth
  ) ; define seg-insert-node

;; Insert into digit, returns list of nodes (1-5 elements)
(define (seg-insert-digit core cfg digit idx val depth)
  (define nodes
    (match digit
      [(digit:1 a) (list a)]
      [(digit:2 a b) (list a b)]
      [(digit:3 a b c) (list a b c)]
      [(digit:4 a b c d) (list a b c d)]
      )) ; match: digit
  (let loop ([ns nodes] [pos 0] [acc '()] [done #f])
    (match ns
      ['()
       (if done
           (reverse acc)
           (error 'seg-insert-digit "index out of bounds")
           ) ; if: insert happened
       ] ; match branch: end
      [(cons n rest)
       (if done
           (loop rest pos (cons n acc) #t)
           (let ()
             (define n-measure (seg-node-measure core n depth))
             (define n-sz (car n-measure))
             (cond
               [(<= (+ pos n-sz) idx)
                ;; idx is past this node, skip it
                (loop rest (+ pos n-sz) (cons n acc) #f)]
               [else
                ;; Insert in this node
                (define-values (n0 n1) (seg-insert-node core cfg n (- idx pos) val depth))
                (if n1
                    (loop rest pos (cons n1 (cons n0 acc)) #t)
                    (loop rest pos (cons n0 acc) #t)
                    ) ; if: node split?
                ] ; cond branch: insert here
               ) ; cond: insert position
             ) ; let: n-sz
           ) ; if: done
       ]
      ) ; match: ns
    ) ; let loop
  ) ; define seg-insert-digit

;; Handle left digit insert result (possibly 5 nodes -> overflow)
(define (seg-handle-left-insert core left-lst inner right depth)
  (define as (ft:config-assoc core))
  (define inner-depth (add1 depth))
  (match left-lst
    [(list x0 x1 x2 x3 x4)
     ;; Overflow: push (x2 x3 x4) as node to inner
     (define pushed (build-node3 core x2 x3 x4 depth))
     (define inner^ (consL:impl core inner pushed inner-depth))
     (define new-left (digit:2 x0 x1))
     (define left-m (measure:digit core new-left depth))
     (define inner-m (measure:ft core inner^ inner-depth))
     (define right-m (measure:digit core right depth))
     (define new-v (as (as left-m inner-m) right-m))
     (ft:deep new-v new-left inner^ right)]
    [_
     (define new-left (list->digit left-lst depth))
     (define left-m (measure:digit core new-left depth))
     (define inner-m (measure:ft core inner inner-depth))
     (define right-m (measure:digit core right depth))
     (define new-v (as (as left-m inner-m) right-m))
     (ft:deep new-v new-left inner right)]
    ) ; match: left-lst
  ) ; define seg-handle-left-insert

;; Handle right digit insert result (possibly 5 nodes -> overflow)
(define (seg-handle-right-insert core left inner right-lst depth)
  (define as (ft:config-assoc core))
  (define inner-depth (add1 depth))
  (match right-lst
    [(list x0 x1 x2 x3 x4)
     ;; Overflow: push (x0 x1 x2) as node to inner
     (define pushed (build-node3 core x0 x1 x2 depth))
     (define inner^ (consR:impl core inner pushed inner-depth))
     (define new-right (digit:2 x3 x4))
     (define left-m (measure:digit core left depth))
     (define inner-m (measure:ft core inner^ inner-depth))
     (define right-m (measure:digit core new-right depth))
     (define new-v (as (as left-m inner-m) right-m))
     (ft:deep new-v left inner^ new-right)]
    [_
     (define new-right (list->digit right-lst depth))
     (define left-m (measure:digit core left depth))
     (define inner-m (measure:ft core inner inner-depth))
     (define right-m (measure:digit core new-right depth))
     (define new-v (as (as left-m inner-m) right-m))
     (ft:deep new-v left inner new-right)]
    ) ; match: right-lst
  ) ; define seg-handle-right-insert

;; Helper: get measure of a node
(define (seg-node-measure core node depth)
  (if (= depth 0)
      ((ft:config-measure core) node)
      (match node
        [(node:2 v _ _) v]
        [(node:3 v _ _ _) v]
        ) ; match: node
      ) ; if: depth=0?
  ) ; define seg-node-measure

;; Helper: convert list to digit
(define (list->digit lst depth)
  (match lst
    [(list a) (digit:1 a)]
    [(list a b) (digit:2 a b)]
    [(list a b c) (digit:3 a b c)]
    [(list a b c d) (digit:4 a b c d)]
    ) ; match: lst
  ) ; define list->digit

;; ========================================
;; Split - O(log n) following pvector's approach
;; ========================================

;; Convert node list to ft (0-4 nodes)
(define (seg-digit-list->ft core lst depth)
  (match lst
    ['() (ft:empty)]
    [(list a) (ft:single a)]
    [(list a b)
     (define as (ft:config-assoc core))
     (define empty-inner (ft:empty))
     (define left-digit (digit:1 a))
     (define right-digit (digit:1 b))
     (define v
       (as (seg-node-measure core a depth)
           (seg-node-measure core b depth))
       ) ; define v
     (ft:deep v left-digit empty-inner right-digit)]
    [(list a b c)
     (define as (ft:config-assoc core))
     (define empty-inner (ft:empty))
     (define left-digit (digit:1 a))
     (define right-digit (digit:2 b c))
     (define v
       (as (as (seg-node-measure core a depth)
               (seg-node-measure core b depth))
           (seg-node-measure core c depth))
       ) ; define v
     (ft:deep v left-digit empty-inner right-digit)]
    [(list a b c d)
     (define as (ft:config-assoc core))
     (define empty-inner (ft:empty))
     (define left-digit (digit:2 a b))
     (define right-digit (digit:2 c d))
     (define v
       (as (as (as (seg-node-measure core a depth)
                   (seg-node-measure core b depth))
               (seg-node-measure core c depth))
           (seg-node-measure core d depth))
       ) ; define v
     (ft:deep v left-digit empty-inner right-digit)]
    ) ; match: lst
  ) ; define seg-digit-list->ft

;; Convert node list to ft (0-7 nodes for combining digit + digit)
(define (seg-digit-list2->ft core lst depth)
  (if (<= (length lst) 4)
      (seg-digit-list->ft core lst depth)
      (let ([as (ft:config-assoc core)]
            [m (lambda (n)
                 (seg-node-measure core n depth)
                 ) ; lambda: node measure mapper
             ])
        (define empty-value (ft:config-empty-value core))
        (define init (empty-value))
        (define v
          (for/fold ([acc init]) ([n lst])
            (as acc (m n))
            ) ; for/fold: aggregate measures
          ) ; define v
        (match lst
          [(list a b c d e)
           (define empty-inner (ft:empty))
           (define left-digit (digit:2 a b))
           (define right-digit (digit:3 c d e))
           (ft:deep v left-digit empty-inner right-digit)]
          [(list a b c d e f)
           (define empty-inner (ft:empty))
           (define left-digit (digit:3 a b c))
           (define right-digit (digit:3 d e f))
           (ft:deep v left-digit empty-inner right-digit)]
          [(list a b c d e f g)
           (define empty-inner (ft:empty))
           (define left-digit (digit:3 a b c))
           (define right-digit (digit:4 d e f g))
           (ft:deep v left-digit empty-inner right-digit)]
          ) ; match: lst
        ) ; let: as/m
      ) ; if: <=4?
  ) ; define seg-digit-list2->ft

;; Combine node list with ft to form (digit, new-ft)
;; If list is empty, pop from ft and unwrap the node
(define (seg-digit-list+ft->digit core lst ft depth pop-fn)
  (match lst
    ['()
     ;; Pop a node from ft, unwrap its children to form digit
     (define inner-depth (add1 depth))
     (define-values (h ft^) (pop-fn core ft inner-depth))
     (values (seg-node->digit core h inner-depth) ft^)]
    [(list a) (values (digit:1 a) ft)]
    [(list a b) (values (digit:2 a b) ft)]
    [(list a b c) (values (digit:3 a b c) ft)]
    [(list a b c d) (values (digit:4 a b c d) ft)]
    ) ; match: lst
  ) ; define seg-digit-list+ft->digit

;; Convert node to digit (unwrap node's children)
(define (seg-node->digit core node depth)
  (match node
    [(node:2 _ a b) (digit:2 a b)]
    [(node:3 _ a b c) (digit:3 a b c)]
    ) ; match: node
  ) ; define seg-node->digit

;; Convert digit to node list
(define (seg-digit->list digit)
  (match digit
    [(digit:1 a) (list a)]
    [(digit:2 a b) (list a b)]
    [(digit:3 a b c) (list a b c)]
    [(digit:4 a b c d) (list a b c d)]
    ) ; match: digit
  ) ; define seg-digit->list

;; Combine left digit with inner ft to form depth-level ft
(define (seg-left-digit+ft->ft core digit ft depth)
  (match ft
    [(ft:empty)
     (seg-digit-list->ft core (seg-digit->list digit) depth)]
    [_
     (define inner-depth (add1 depth))
     (define-values (r ft^) (hdR:impl core ft inner-depth))
     (build-ft0 core digit ft^ (seg-node->digit core r inner-depth) depth)]
    ) ; match: ft
  ) ; define seg-left-digit+ft->ft

;; Combine right digit with inner ft to form depth-level ft
(define (seg-right-digit+ft->ft core digit ft depth)
  (match ft
    [(ft:empty)
     (seg-digit-list->ft core (seg-digit->list digit) depth)]
    [_
     (define inner-depth (add1 depth))
     (define-values (l ft^) (hdL:impl core ft inner-depth))
     (build-ft0 core (seg-node->digit core l inner-depth) ft^ digit depth)]
    ) ; match: ft
  ) ; define seg-right-digit+ft->ft

;; Split digit: returns (remaining-idx, left-list, middle, right-list)
(define (seg-split-digit core digit idx depth)
  (define (m n)
    (car (seg-node-measure core n depth))
    ) ; define m
  (match digit
    [(digit:1 a)
     (if (< idx (m a))
         (values idx '() a '())
         (error 'seg-split-digit "index out of bounds")
         ) ; if: idx in digit:1
     ] ; match branch: digit:1
    [(digit:2 a b)
     (define a-sz (m a))
     (define b-sz (m b))
     (define b-start a-sz)
     (define b-end (+ a-sz b-sz))
     (cond
       [(< idx b-start)
        (values idx '() a (list b))
        ] ; cond branch: digit:2 left
       [(< idx b-end)
        (values (- idx a-sz) (list a) b '())
        ] ; cond branch: digit:2 right
       [else (error 'seg-split-digit "index out of bounds")]
       ) ; cond: digit:2
     ] ; match branch: digit:2
    [(digit:3 a b c)
     (define a-sz (m a))
     (define b-sz (m b))
     (define c-sz (m c))
     (define ab-sz (+ a-sz b-sz))
     (define abc-sz (+ ab-sz c-sz))
     (cond
       [(< idx a-sz)
        (values idx '() a (list b c))
        ] ; cond branch: digit:3 left
       [(< idx ab-sz)
        (values (- idx a-sz) (list a) b (list c))
        ] ; cond branch: digit:3 middle
       [(< idx abc-sz)
        (values (- idx ab-sz) (list a b) c '())
        ] ; cond branch: digit:3 right
       [else (error 'seg-split-digit "index out of bounds")]
       ) ; cond: digit:3
     ] ; match branch: digit:3
    [(digit:4 a b c d)
     (define a-sz (m a))
     (define b-sz (m b))
     (define c-sz (m c))
     (define d-sz (m d))
     (define ab-sz (+ a-sz b-sz))
     (define abc-sz (+ ab-sz c-sz))
     (define abcd-sz (+ abc-sz d-sz))
     (cond
       [(< idx a-sz)
        (values idx '() a (list b c d))
        ] ; cond branch: digit:4 first
       [(< idx ab-sz)
        (values (- idx a-sz) (list a) b (list c d))
        ] ; cond branch: digit:4 second
       [(< idx abc-sz)
        (values (- idx ab-sz) (list a b) c (list d))
        ] ; cond branch: digit:4 third
       [(< idx abcd-sz)
        (values (- idx abc-sz) (list a b c) d '())
        ] ; cond branch: digit:4 fourth
       [else (error 'seg-split-digit "index out of bounds")]
       ) ; cond: digit:4
     ] ; match branch: digit:4
    ) ; match: digit
  ) ; define seg-split-digit

;; Split node: returns (remaining-idx, left-list, middle, right-list)
;; Children are at depth-1 level
(define (seg-split-node core node idx depth)
  (define child-depth (sub1 depth))
  (define (m n)
    (car (seg-node-measure core n child-depth))
    ) ; define m
  (match node
    [(node:2 v a b)
     (define a-sz (m a))
     (define node-sz (car v))
     (cond
       [(< idx a-sz)
        (values idx '() a (list b))
        ] ; cond branch: node:2 left
       [(< idx node-sz)
        (values (- idx a-sz) (list a) b '())
        ] ; cond branch: node:2 right
       [else (error 'seg-split-node "index out of bounds")]
       ) ; cond: node:2
     ] ; match branch: node:2
    [(node:3 v a b c)
     (define a-sz (m a))
     (define b-sz (m b))
     (define node-sz (car v))
     (define ab-sz (+ a-sz b-sz))
     (cond
       [(< idx a-sz)
        (values idx '() a (list b c))
        ] ; cond branch: node:3 left
       [(< idx ab-sz)
        (values (- idx a-sz) (list a) b (list c))
        ] ; cond branch: node:3 middle
       [(< idx node-sz)
        (values (- idx ab-sz) (list a b) c '())
        ] ; cond branch: node:3 right
       [else (error 'seg-split-node "index out of bounds")]
       ) ; cond: node:3
     ] ; match branch: node:3
    ) ; match: node
  ) ; define seg-split-node

;; Main split implementation: returns (remaining-idx, left-ft, middle, right-ft)
(define (seg-split:impl core ft idx depth)
  (match ft
    [(ft:empty) (error 'seg-split:impl "empty tree")]
    [(ft:single v)
     (define v-m (seg-node-measure core v depth))
     (define v-size (car v-m))
     (if (< idx v-size)
         (values idx (ft:empty) v (ft:empty))
         (error 'seg-split:impl "index out of bounds")
         ) ; if: idx in single
     ] ; match branch: ft:single
    [(ft:deep total-measure lhs inner rhs)
     (define lhs-m (measure:digit core lhs depth))
     (define lhs-sz (car lhs-m))
     (define inner-depth (add1 depth))
     (define inner-m (measure:ft core inner inner-depth))
     (define inner-sz (car inner-m))
     (define lhs-inner-sz (+ lhs-sz inner-sz))
     (cond
       [(< idx lhs-sz)
        ;; Split in left digit
        (define-values (idx^ l m r) (seg-split-digit core lhs idx depth))
       (define left (seg-digit-list->ft core l depth))
        (match inner
          [(ft:empty)
           (define rhs-list (seg-digit->list rhs))
           (define merged-right-list (append r rhs-list))
           (define right^ (seg-digit-list2->ft core merged-right-list depth))
           (values idx^ left m right^)
           ] ; match branch: inner empty
          [_
           (define-values (right-digit inner^) (seg-digit-list+ft->digit core r inner depth hdL:impl))
           (define right^ (build-ft0 core right-digit inner^ rhs depth))
           (values idx^ left m right^)
           ] ; match branch: inner non-empty
          ) ; match: inner after lhs split
        ]
       [(< idx lhs-inner-sz)
        ;; Split in inner
        (define-values (rest-idx l-inner m-node r-inner)
          (seg-split:impl core inner (- idx lhs-sz) inner-depth))
        (define left (seg-left-digit+ft->ft core lhs l-inner depth))
        (define right (seg-right-digit+ft->ft core rhs r-inner depth))
        ;; Split the middle node
        (define-values (idx^ l^ m^ r^) (seg-split-node core m-node rest-idx inner-depth))
        ;; Append l^ to left, prepend r^ to right
        (define left^
          (for/fold ([t left]) ([n l^])
            (consR:impl core t n depth)
            ) ; for/fold: append l^
          ) ; define left^
        (define right^
          (for/foldr ([t right]) ([n r^])
            (consL:impl core t n depth)
            ) ; for/foldr: prepend r^
          ) ; define right^
        (values idx^ left^ m^ right^)]
       [(< idx (car total-measure))
        ;; Split in right digit
        (define-values (idx^ l m r) (seg-split-digit core rhs (- idx lhs-inner-sz) depth))
        (define right (seg-digit-list->ft core r depth))
        (match inner
          [(ft:empty)
           (define lhs-list (seg-digit->list lhs))
           (define merged-left-list (append lhs-list l))
           (define left^ (seg-digit-list2->ft core merged-left-list depth))
           (values idx^ left^ m right)
           ] ; match branch: inner empty
          [_
           (define-values (left-digit inner^) (seg-digit-list+ft->digit core l inner depth hdR:impl))
           (define left^ (build-ft0 core lhs inner^ left-digit depth))
           (values idx^ left^ m right)
           ] ; match branch: inner non-empty
          ) ; match: inner after rhs split
        ]
       [else (error 'seg-split:impl "index out of bounds")]
       ) ; cond: ft:deep
     ]
    ) ; match: ft
  ) ; define seg-split:impl

;; Public split: returns (left-ft, middle-elem, right-ft) at depth 0
(define (seg-split core ft idx)
  (define-values (rem-idx l m r) (seg-split:impl core ft idx 0))
  (unless (zero? rem-idx) (error 'seg-split "internal error: rem-idx should be 0"))
  (values l m r))

(define (segment-seq-split ss idx)
  (match-define (segment-seq cfg ft cnt) ss)
  (when (or (< idx 0) (> idx cnt))
    (error 'segment-seq-split "index out of bounds: ~a (size: ~a)" idx cnt))
  (cond
    [(= idx 0) (values (segment-seq cfg (ft:empty) 0) ss)]
    [(= idx cnt)
     (define empty-ss (segment-seq cfg (ft:empty) 0))
     (values ss empty-ss)
     ] ; cond branch: split at end
    [else
     (define core (make-ft-config cfg))
     (define-values (l m r) (seg-split core ft idx))
     (define r^ (consL:impl core r m 0))
     (define right-cnt (- cnt idx))
     (define right-ss (segment-seq cfg r^ right-cnt))
     (values (segment-seq cfg l idx) right-ss)
     ] ; cond branch: split in middle
    ) ; cond: segment-seq-split
  ) ; define segment-seq-split

;; ========================================
;; Delete - O(log n) using split + concat
;; ========================================

(define (segment-seq-delete ss idx)
  (match-define (segment-seq cfg ft cnt) ss)
  (when (or (< idx 0) (>= idx cnt))
    (error 'segment-seq-delete "index out of bounds: ~a (size: ~a)" idx cnt))
  (define core (make-ft-config cfg))
  (cond
    [(= cnt 1)
     (segment-seq cfg (ft:empty) 0)]
    [(= idx 0)
     (define-values (_elem new-ft) (hdL:impl core ft 0))
     (define new-cnt (sub1 cnt))
     (segment-seq cfg new-ft new-cnt)
     ] ; cond branch: drop first
    [(= idx (sub1 cnt))
     (define-values (_elem new-ft) (hdR:impl core ft 0))
     (define new-cnt (sub1 cnt))
     (segment-seq cfg new-ft new-cnt)
     ] ; cond branch: drop last
    [else
     ;; O(log n) using split
     (define-values (l _m r) (seg-split core ft idx))
     (define joined (concat:impl core l r 0))
     (segment-seq cfg joined (sub1 cnt))
     ] ; cond branch: delete middle
    ) ; cond: segment-seq-delete
  ) ; define segment-seq-delete

;; ========================================
;; Range Query - O(log n)
;; Collects aggregate by traversing only necessary subtrees
;; ========================================

(define (segment-seq-range-query ss lo hi)
  (match-define (segment-seq cfg ft cnt) ss)
  (cond
    [(>= lo hi) (seg-config-identity cfg)]
    [(or (< lo 0) (> hi cnt))
     (error 'segment-seq-range-query "out of bounds")]
    [(and (= lo 0) (= hi cnt))
     (ft-agg cfg ft 0)]
    [else
     (range-query-ft cfg ft lo hi 0)
     ] ; cond branch: partial range
    ) ; cond: segment-seq-range-query
  ) ; define segment-seq-range-query

(define (range-query-ft cfg ft lo hi depth)
  (match ft
    [(ft:empty) (seg-config-identity cfg)]
    [(ft:single a)
     (define a-size (node-size cfg a depth))
     (if (and (= lo 0) (= hi a-size))
         (if (= depth 0)
             ((seg-config-extract cfg) a)
             (let ()
               (define node-measure
                 (match a
                   [(node:2 v _ _) v]
                   [(node:3 v _ _ _) v]
                   ) ; match: ft single node
                 )
               (cdr node-measure)
               ) ; let: ft single aggregate
             ) ; if: depth=0?
         (range-query-node cfg a lo hi depth)
         ) ; if: full cover?
     ] ; match branch: ft:single
    [(ft:deep _ left inner right)
     (define left-sz (digit-size cfg left depth))
     (define inner-depth (add1 depth))
     (define inner-sz (ft-size cfg inner inner-depth))
     (define right-start (+ left-sz inner-sz))
     (define comb (seg-config-combine cfg))
     (define id (seg-config-identity cfg))

     ;; Collect from each region that overlaps [lo, hi)
     (define left-contrib
       (if (< lo left-sz)
           (range-query-digit cfg left (max 0 lo) (min left-sz hi) depth)
           id))
     (define inner-contrib
       (if (and (< lo right-start) (> hi left-sz))
           (range-query-ft cfg inner
                          (max 0 (- lo left-sz))
                          (min inner-sz (- hi left-sz))
                          inner-depth)
           id))
     (define right-contrib
       (if (> hi right-start)
           (range-query-digit cfg right
                             (max 0 (- lo right-start))
                             (- hi right-start)
                             depth)
           id))
     (comb (comb left-contrib inner-contrib) right-contrib)]
    ) ; match: ft
  ) ; define range-query-ft

(define (range-query-digit cfg digit lo hi depth)
  (define comb (seg-config-combine cfg))
  (define id (seg-config-identity cfg))
  (define elems
    (match digit
      [(digit:1 a) (list a)]
      [(digit:2 a b) (list a b)]
      [(digit:3 a b c) (list a b c)]
      [(digit:4 a b c d) (list a b c d)]
      ) ; match: digit
    ) ; define elems
  (define-values (result _next-pos)
    (for/fold ([acc id] [pos 0]) ([e elems])
      (define e-sz (node-size cfg e depth))
      (define e-end (+ pos e-sz))
      (define starts-before-hi? (< pos hi))
      (define ends-after-lo? (> e-end lo))
      (define overlap? (and starts-before-hi? ends-after-lo?))
      (define acc^
        (if overlap?
            (let ()
              (define lo-covers? (<= lo pos))
              (define hi-covers? (>= hi e-end))
              (define full-cover? (and lo-covers? hi-covers?))
              (define e-agg
                (if full-cover?
                    (if (= depth 0)
                        ((seg-config-extract cfg) e)
                        (let ()
                          (define node-measure
                            (match e
                              [(node:2 v _ _) v]
                              [(node:3 v _ _ _) v]
                              ) ; match: range digit node
                            )
                          (cdr node-measure)
                          ) ; let: node aggregate
                        ) ; if: depth=0?
                    (let ()
                      (define lo-pos (- lo pos))
                      (define hi-pos (- hi pos))
                      (define sub-lo (max 0 lo-pos))
                      (define sub-hi (min e-sz hi-pos))
                      (range-query-node cfg e sub-lo sub-hi depth)
                      ) ; let: partial overlap range
                    ) ; if: full-cover?
                )
              (comb acc e-agg)
              ) ; let: overlap handling
            acc
            ) ; if: overlap?
        ) ; define acc^
      (values acc^ e-end)
      ) ; for/fold: range-query-digit
    ) ; define-values: result
  result
  ) ; define range-query-digit

(define (range-query-node cfg node lo hi depth)
  (if (= depth 0)
      ((seg-config-extract cfg) node)
      (let ()
        (define comb (seg-config-combine cfg))
        (define id (seg-config-identity cfg))
        (define child-depth (sub1 depth))
        (define children
          (match node
            [(node:2 _ a b) (list a b)]
            [(node:3 _ a b c) (list a b c)]
            )) ; match: node
        (define-values (result _)
          (for/fold ([acc id] [pos 0]) ([c children])
            (define c-sz (node-size cfg c child-depth))
            (define c-end (+ pos c-sz))
            (values
             (if (and (< pos hi) (> c-end lo))
                 (comb acc
                       (if (and (<= lo pos) (>= hi c-end))
                           ;; Full child in range
                           (if (= child-depth 0)
                               ((seg-config-extract cfg) c)
                               (let ()
                                 (define node-measure
                                   (match c
                                     [(node:2 v _ _) v]
                                     [(node:3 v _ _ _) v]
                                     ) ; match: range child node
                                   )
                                 (cdr node-measure)
                                 ) ; let: child aggregate
                               )
                           ;; Partial
                           (let ()
                             (define lo-pos (- lo pos))
                             (define hi-pos (- hi pos))
                             (define sub-lo (max 0 lo-pos))
                             (define sub-hi (min c-sz hi-pos))
                             (range-query-node cfg c sub-lo sub-hi child-depth)
                             ) ; let: range-query-node args
                           ))
                 acc)
             c-end))
            ) ; for/fold: range-query-node
        result)
    ) ; let: comb id
  ) ; define range-query-node

;; ========================================
;; Concat
;; ========================================

(define (segment-seq-concat ss1 ss2)
  (match-define (segment-seq cfg1 ft1 cnt1) ss1)
  (match-define (segment-seq cfg2 ft2 cnt2) ss2)
  (define core1 (make-ft-config cfg1))
  (define joined (concat:impl core1 ft1 ft2 0))
  (segment-seq cfg1 joined (+ cnt1 cnt2))
  ) ; define segment-seq-concat

;; ========================================
;; Conversion
;; ========================================

(define (segment-seq->list ss)
  (match-define (segment-seq cfg ft _) ss)
  (define core (make-ft-config cfg))
  (define init-acc '())
  (let loop ([t ft] [acc init-acc])
    (define-values (elem rest) (hdL:impl core t 0))
    (if elem
        (loop rest (cons elem acc))
        (reverse acc)
        ) ; if: elem exists?
    ) ; let loop
  ) ; define segment-seq->list

(define (segment-seq-aggregate ss)
  (match-define (segment-seq cfg ft _) ss)
  (ft-agg cfg ft 0))

;; ========================================
;; Exports
;; ========================================

(provide
  segment-seq segment-seq?
  segment-seq-new segment-seq-sum segment-seq-min segment-seq-max segment-seq-product
  list->segment-seq
  segment-seq-empty? segment-seq-length
  segment-seq-ref segment-seq-set
  segment-seq-insert segment-seq-delete
  segment-seq-push-back segment-seq-push-front segment-seq-pop-back segment-seq-pop-front
  segment-seq-range-query segment-seq-aggregate
  segment-seq-split segment-seq-concat
  segment-seq->list)
