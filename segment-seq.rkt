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
  (ft:config
    (lambda () (cons 0 id))
    (lambda (elem) (cons 1 (extract elem)))
    (lambda (m1 m2)
      (cons (+ (car m1) (car m2))
            (comb (cdr m1) (cdr m2))))))

;; ========================================
;; Measure helpers
;; ========================================

(define (node-size cfg node depth)
  (if (= depth 0)
      1
      (car (match node
             [(node:2 v _ _) v]
             [(node:3 v _ _ _) v]))))

(define (digit-size cfg digit depth)
  (match digit
    [(digit:1 a) (node-size cfg a depth)]
    [(digit:2 a b) (+ (node-size cfg a depth) (node-size cfg b depth))]
    [(digit:3 a b c) (+ (node-size cfg a depth) (node-size cfg b depth) (node-size cfg c depth))]
    [(digit:4 a b c d) (+ (node-size cfg a depth) (node-size cfg b depth)
                          (node-size cfg c depth) (node-size cfg d depth))]))

(define (ft-size cfg ft depth)
  (match ft
    [(ft:empty) 0]
    [(ft:single a) (node-size cfg a depth)]
    [(ft:deep v _ _ _) (car v)]))

(define (ft-agg cfg ft depth)
  (match ft
    [(ft:empty) (seg-config-identity cfg)]
    [(ft:single a)
     (if (= depth 0)
         ((seg-config-extract cfg) a)
         (cdr (match a [(node:2 v _ _) v] [(node:3 v _ _ _) v])))]
    [(ft:deep v _ _ _) (cdr v)]))

;; ========================================
;; Constructors
;; ========================================

(define (segment-seq-new identity combine [extract values])
  (segment-seq (seg-config identity combine extract) (ft:empty) 0))

(define (segment-seq-sum) (segment-seq-new 0 +))
(define (segment-seq-min) (segment-seq-new +inf.0 min))
(define (segment-seq-max) (segment-seq-new -inf.0 max))
(define (segment-seq-product) (segment-seq-new 1 *))

(define (segment-seq-empty? ss) (zero? (segment-seq-count ss)))
(define (segment-seq-length ss) (segment-seq-count ss))

(define (list->segment-seq lst identity combine [extract values])
  (define cfg (seg-config identity combine extract))
  (define core (make-ft-config cfg))
  (segment-seq cfg
               (for/fold ([t (ft:empty)]) ([elem lst])
                 (consR:impl core t elem 0))
               (length lst)))

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
     (define inner-sz (ft-size cfg inner (add1 depth)))
     (cond
       [(< idx left-sz) (ref-digit cfg left idx depth)]
       [(< idx (+ left-sz inner-sz)) (ref-ft cfg inner (- idx left-sz) (add1 depth))]
       [else (ref-digit cfg right (- idx left-sz inner-sz) depth)])]))

(define (ref-digit cfg digit idx depth)
  (match digit
    [(digit:1 a) (ref-node cfg a idx depth)]
    [(digit:2 a b)
     (define a-sz (node-size cfg a depth))
     (if (< idx a-sz) (ref-node cfg a idx depth) (ref-node cfg b (- idx a-sz) depth))]
    [(digit:3 a b c)
     (define a-sz (node-size cfg a depth))
     (define b-sz (node-size cfg b depth))
     (cond
       [(< idx a-sz) (ref-node cfg a idx depth)]
       [(< idx (+ a-sz b-sz)) (ref-node cfg b (- idx a-sz) depth)]
       [else (ref-node cfg c (- idx a-sz b-sz) depth)])]
    [(digit:4 a b c d)
     (define a-sz (node-size cfg a depth))
     (define b-sz (node-size cfg b depth))
     (define c-sz (node-size cfg c depth))
     (cond
       [(< idx a-sz) (ref-node cfg a idx depth)]
       [(< idx (+ a-sz b-sz)) (ref-node cfg b (- idx a-sz) depth)]
       [(< idx (+ a-sz b-sz c-sz)) (ref-node cfg c (- idx a-sz b-sz) depth)]
       [else (ref-node cfg d (- idx a-sz b-sz c-sz) depth)])]))

(define (ref-node cfg node idx depth)
  (if (= depth 0)
      node
      (match node
        [(node:2 _ a b)
         (define a-sz (node-size cfg a (sub1 depth)))
         (if (< idx a-sz)
             (ref-node cfg a idx (sub1 depth))
             (ref-node cfg b (- idx a-sz) (sub1 depth)))]
        [(node:3 _ a b c)
         (define a-sz (node-size cfg a (sub1 depth)))
         (define b-sz (node-size cfg b (sub1 depth)))
         (cond
           [(< idx a-sz) (ref-node cfg a idx (sub1 depth))]
           [(< idx (+ a-sz b-sz)) (ref-node cfg b (- idx a-sz) (sub1 depth))]
           [else (ref-node cfg c (- idx a-sz b-sz) (sub1 depth))])])))

;; ========================================
;; Set - O(log n)
;; ========================================

(define (segment-seq-set ss idx val)
  (match-define (segment-seq cfg ft cnt) ss)
  (when (or (< idx 0) (>= idx cnt))
    (error 'segment-seq-set "index out of bounds: ~a (size: ~a)" idx cnt))
  (define core (make-ft-config cfg))
  (segment-seq cfg (set-ft cfg core ft idx val 0) cnt))

(define (set-ft cfg core ft idx val depth)
  (match ft
    [(ft:single a) (ft:single (set-node cfg core a idx val depth))]
    [(ft:deep _ left inner right)
     (define left-sz (digit-size cfg left depth))
     (define inner-sz (ft-size cfg inner (add1 depth)))
     (define as (ft:config-assoc core))
     (cond
       [(< idx left-sz)
        (define new-left (set-digit cfg core left idx val depth))
        (define new-v (as (as (measure:digit core new-left depth)
                              (measure:ft core inner (add1 depth)))
                          (measure:digit core right depth)))
        (ft:deep new-v new-left inner right)]
       [(< idx (+ left-sz inner-sz))
        (define new-inner (set-ft cfg core inner (- idx left-sz) val (add1 depth)))
        (define new-v (as (as (measure:digit core left depth)
                              (measure:ft core new-inner (add1 depth)))
                          (measure:digit core right depth)))
        (ft:deep new-v left new-inner right)]
       [else
        (define new-right (set-digit cfg core right (- idx left-sz inner-sz) val depth))
        (define new-v (as (as (measure:digit core left depth)
                              (measure:ft core inner (add1 depth)))
                          (measure:digit core new-right depth)))
        (ft:deep new-v left inner new-right)])]))

(define (set-digit cfg core digit idx val depth)
  (match digit
    [(digit:1 a) (digit:1 (set-node cfg core a idx val depth))]
    [(digit:2 a b)
     (define a-sz (node-size cfg a depth))
     (if (< idx a-sz)
         (digit:2 (set-node cfg core a idx val depth) b)
         (digit:2 a (set-node cfg core b (- idx a-sz) val depth)))]
    [(digit:3 a b c)
     (define a-sz (node-size cfg a depth))
     (define b-sz (node-size cfg b depth))
     (cond
       [(< idx a-sz) (digit:3 (set-node cfg core a idx val depth) b c)]
       [(< idx (+ a-sz b-sz)) (digit:3 a (set-node cfg core b (- idx a-sz) val depth) c)]
       [else (digit:3 a b (set-node cfg core c (- idx a-sz b-sz) val depth))])]
    [(digit:4 a b c d)
     (define a-sz (node-size cfg a depth))
     (define b-sz (node-size cfg b depth))
     (define c-sz (node-size cfg c depth))
     (cond
       [(< idx a-sz) (digit:4 (set-node cfg core a idx val depth) b c d)]
       [(< idx (+ a-sz b-sz)) (digit:4 a (set-node cfg core b (- idx a-sz) val depth) c d)]
       [(< idx (+ a-sz b-sz c-sz)) (digit:4 a b (set-node cfg core c (- idx a-sz b-sz) val depth) d)]
       [else (digit:4 a b c (set-node cfg core d (- idx a-sz b-sz c-sz) val depth))])]))

(define (set-node cfg core node idx val depth)
  (if (= depth 0)
      val
      (match node
        [(node:2 _ a b)
         (define a-sz (node-size cfg a (sub1 depth)))
         (if (< idx a-sz)
             (build-node2 core (set-node cfg core a idx val (sub1 depth)) b (sub1 depth))
             (build-node2 core a (set-node cfg core b (- idx a-sz) val (sub1 depth)) (sub1 depth)))]
        [(node:3 _ a b c)
         (define a-sz (node-size cfg a (sub1 depth)))
         (define b-sz (node-size cfg b (sub1 depth)))
         (cond
           [(< idx a-sz) (build-node3 core (set-node cfg core a idx val (sub1 depth)) b c (sub1 depth))]
           [(< idx (+ a-sz b-sz)) (build-node3 core a (set-node cfg core b (- idx a-sz) val (sub1 depth)) c (sub1 depth))]
           [else (build-node3 core a b (set-node cfg core c (- idx a-sz b-sz) val (sub1 depth)) (sub1 depth))])])))

;; ========================================
;; Push/Pop - O(1) amortized
;; ========================================

(define (segment-seq-push-back ss val)
  (match-define (segment-seq cfg ft cnt) ss)
  (segment-seq cfg (consR:impl (make-ft-config cfg) ft val 0) (add1 cnt)))

(define (segment-seq-push-front ss val)
  (match-define (segment-seq cfg ft cnt) ss)
  (segment-seq cfg (consL:impl (make-ft-config cfg) ft val 0) (add1 cnt)))

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
     (segment-seq cfg (consR:impl core ft val 0) (add1 cnt))]
    [else
     (segment-seq cfg (seg-insert-ft core cfg ft idx val 0) (add1 cnt))]))

;; Insert into ft, returns new ft
(define (seg-insert-ft core cfg ft idx val depth)
  (match ft
    [(ft:single x)
     (define-values (x0 x1) (seg-insert-node core cfg x idx val depth))
     (if x1
         (let ([as (ft:config-assoc core)])
           (ft:deep (as (seg-node-measure core x0 depth)
                        (seg-node-measure core x1 depth))
                    (digit:1 x0) (ft:empty) (digit:1 x1)))
         (ft:single x0))]
    [(ft:deep _ left inner right)
     (define left-sz (measure:digit core left depth))
     (define inner-sz (measure:ft core inner (add1 depth)))
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
        (define inner^ (seg-insert-ft core cfg inner (- idx left-sz-val) val (add1 depth)))
        (define as (ft:config-assoc core))
        (define new-v (as (as left-sz (measure:ft core inner^ (add1 depth)))
                          (measure:digit core right depth)))
        (ft:deep new-v left inner^ right)]
       [else
        ;; Insert in left digit
        (define left-lst (seg-insert-digit core cfg left idx val depth))
        (seg-handle-left-insert core left-lst inner right depth)])]))

;; Insert into node, returns (values new-node maybe-split-node)
(define (seg-insert-node core cfg node idx val depth)
  (if (= depth 0)
      ;; At element level: "split" means insert before
      (values val node)
      (match node
        [(node:2 _ x0 x1)
         (define x0-sz (car (seg-node-measure core x0 (sub1 depth))))
         (cond
           [(<= x0-sz idx)
            ;; Insert in x1
            (define-values (x1^ x2^) (seg-insert-node core cfg x1 (- idx x0-sz) val (sub1 depth)))
            (if x2^
                (values (build-node3 core x0 x1^ x2^ (sub1 depth)) #f)
                (values (build-node2 core x0 x1^ (sub1 depth)) #f))]
           [else
            ;; Insert in x0
            (define-values (x0^ x1^) (seg-insert-node core cfg x0 idx val (sub1 depth)))
            (if x1^
                (values (build-node3 core x0^ x1^ x1 (sub1 depth)) #f)
                (values (build-node2 core x0^ x1 (sub1 depth)) #f))])]
        [(node:3 _ x0 x1 x2)
         (define x0-sz (car (seg-node-measure core x0 (sub1 depth))))
         (define x1-sz (car (seg-node-measure core x1 (sub1 depth))))
         (define x0-x1-sz (+ x0-sz x1-sz))
         (cond
           [(<= x0-x1-sz idx)
            ;; Insert in x2
            (define-values (x2^ x3^) (seg-insert-node core cfg x2 (- idx x0-x1-sz) val (sub1 depth)))
            (if x3^
                ;; Split: (x0 x1) and (x2^ x3^)
                (values (build-node2 core x0 x1 (sub1 depth))
                        (build-node2 core x2^ x3^ (sub1 depth)))
                (values (build-node3 core x0 x1 x2^ (sub1 depth)) #f))]
           [(<= x0-sz idx)
            ;; Insert in x1
            (define-values (x1^ x2^) (seg-insert-node core cfg x1 (- idx x0-sz) val (sub1 depth)))
            (if x2^
                ;; Split: (x0 x1^) and (x2^ x2)
                (values (build-node2 core x0 x1^ (sub1 depth))
                        (build-node2 core x2^ x2 (sub1 depth)))
                (values (build-node3 core x0 x1^ x2 (sub1 depth)) #f))]
           [else
            ;; Insert in x0
            (define-values (x0^ x1^) (seg-insert-node core cfg x0 idx val (sub1 depth)))
            (if x1^
                ;; Split: (x0^ x1^) and (x1 x2)
                (values (build-node2 core x0^ x1^ (sub1 depth))
                        (build-node2 core x1 x2 (sub1 depth)))
                (values (build-node3 core x0^ x1 x2 (sub1 depth)) #f))])])))

;; Insert into digit, returns list of nodes (1-5 elements)
(define (seg-insert-digit core cfg digit idx val depth)
  (define nodes (match digit
                  [(digit:1 a) (list a)]
                  [(digit:2 a b) (list a b)]
                  [(digit:3 a b c) (list a b c)]
                  [(digit:4 a b c d) (list a b c d)]))
  (let loop ([ns nodes] [pos 0] [acc '()] [done #f])
    (match ns
      ['()
       (if done
           (reverse acc)
           (error 'seg-insert-digit "index out of bounds"))]
      [(cons n rest)
       (if done
           (loop rest pos (cons n acc) #t)
           (let ([n-sz (car (seg-node-measure core n depth))])
             (cond
               [(<= (+ pos n-sz) idx)
                ;; idx is past this node, skip it
                (loop rest (+ pos n-sz) (cons n acc) #f)]
               [else
                ;; Insert in this node
                (define-values (n0 n1) (seg-insert-node core cfg n (- idx pos) val depth))
                (if n1
                    (loop rest pos (cons n1 (cons n0 acc)) #t)
                    (loop rest pos (cons n0 acc) #t))])))])))

;; Handle left digit insert result (possibly 5 nodes -> overflow)
(define (seg-handle-left-insert core left-lst inner right depth)
  (define as (ft:config-assoc core))
  (match left-lst
    [(list x0 x1 x2 x3 x4)
     ;; Overflow: push (x2 x3 x4) as node to inner
     (define pushed (build-node3 core x2 x3 x4 depth))
     (define inner^ (consL:impl core inner pushed (add1 depth)))
     (define new-left (digit:2 x0 x1))
     (define new-v (as (as (measure:digit core new-left depth)
                           (measure:ft core inner^ (add1 depth)))
                       (measure:digit core right depth)))
     (ft:deep new-v new-left inner^ right)]
    [_
     (define new-left (list->digit left-lst depth))
     (define new-v (as (as (measure:digit core new-left depth)
                           (measure:ft core inner (add1 depth)))
                       (measure:digit core right depth)))
     (ft:deep new-v new-left inner right)]))

;; Handle right digit insert result (possibly 5 nodes -> overflow)
(define (seg-handle-right-insert core left inner right-lst depth)
  (define as (ft:config-assoc core))
  (match right-lst
    [(list x0 x1 x2 x3 x4)
     ;; Overflow: push (x0 x1 x2) as node to inner
     (define pushed (build-node3 core x0 x1 x2 depth))
     (define inner^ (consR:impl core inner pushed (add1 depth)))
     (define new-right (digit:2 x3 x4))
     (define new-v (as (as (measure:digit core left depth)
                           (measure:ft core inner^ (add1 depth)))
                       (measure:digit core new-right depth)))
     (ft:deep new-v left inner^ new-right)]
    [_
     (define new-right (list->digit right-lst depth))
     (define new-v (as (as (measure:digit core left depth)
                           (measure:ft core inner (add1 depth)))
                       (measure:digit core new-right depth)))
     (ft:deep new-v left inner new-right)]))

;; Helper: get measure of a node
(define (seg-node-measure core node depth)
  (if (= depth 0)
      ((ft:config-measure core) node)
      (match node
        [(node:2 v _ _) v]
        [(node:3 v _ _ _) v])))

;; Helper: convert list to digit
(define (list->digit lst depth)
  (match lst
    [(list a) (digit:1 a)]
    [(list a b) (digit:2 a b)]
    [(list a b c) (digit:3 a b c)]
    [(list a b c d) (digit:4 a b c d)]))

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
     (ft:deep (as (seg-node-measure core a depth)
                  (seg-node-measure core b depth))
              (digit:1 a) (ft:empty) (digit:1 b))]
    [(list a b c)
     (define as (ft:config-assoc core))
     (ft:deep (as (as (seg-node-measure core a depth)
                      (seg-node-measure core b depth))
                  (seg-node-measure core c depth))
              (digit:1 a) (ft:empty) (digit:2 b c))]
    [(list a b c d)
     (define as (ft:config-assoc core))
     (ft:deep (as (as (as (seg-node-measure core a depth)
                          (seg-node-measure core b depth))
                      (seg-node-measure core c depth))
                  (seg-node-measure core d depth))
              (digit:2 a b) (ft:empty) (digit:2 c d))]))

;; Convert node list to ft (0-7 nodes for combining digit + digit)
(define (seg-digit-list2->ft core lst depth)
  (if (<= (length lst) 4)
      (seg-digit-list->ft core lst depth)
      (let ([as (ft:config-assoc core)]
            [m (lambda (n) (seg-node-measure core n depth))])
        (define v (for/fold ([acc ((ft:config-empty-value core))]) ([n lst])
                    (as acc (m n))))
        (match lst
          [(list a b c d e)
           (ft:deep v (digit:2 a b) (ft:empty) (digit:3 c d e))]
          [(list a b c d e f)
           (ft:deep v (digit:3 a b c) (ft:empty) (digit:3 d e f))]
          [(list a b c d e f g)
           (ft:deep v (digit:3 a b c) (ft:empty) (digit:4 d e f g))]))))

;; Combine node list with ft to form (digit, new-ft)
;; If list is empty, pop from ft and unwrap the node
(define (seg-digit-list+ft->digit core lst ft depth pop-fn)
  (match lst
    ['()
     ;; Pop a node from ft, unwrap its children to form digit
     (define-values (h ft^) (pop-fn core ft (add1 depth)))
     (values (seg-node->digit core h (add1 depth)) ft^)]
    [(list a) (values (digit:1 a) ft)]
    [(list a b) (values (digit:2 a b) ft)]
    [(list a b c) (values (digit:3 a b c) ft)]
    [(list a b c d) (values (digit:4 a b c d) ft)]))

;; Convert node to digit (unwrap node's children)
(define (seg-node->digit core node depth)
  (match node
    [(node:2 _ a b) (digit:2 a b)]
    [(node:3 _ a b c) (digit:3 a b c)]))

;; Convert digit to node list
(define (seg-digit->list digit)
  (match digit
    [(digit:1 a) (list a)]
    [(digit:2 a b) (list a b)]
    [(digit:3 a b c) (list a b c)]
    [(digit:4 a b c d) (list a b c d)]))

;; Combine left digit with inner ft to form depth-level ft
(define (seg-left-digit+ft->ft core digit ft depth)
  (match ft
    [(ft:empty)
     (seg-digit-list->ft core (seg-digit->list digit) depth)]
    [_
     (define-values (r ft^) (hdR:impl core ft (add1 depth)))
     (build-ft0 core digit ft^ (seg-node->digit core r (add1 depth)) depth)]))

;; Combine right digit with inner ft to form depth-level ft
(define (seg-right-digit+ft->ft core digit ft depth)
  (match ft
    [(ft:empty)
     (seg-digit-list->ft core (seg-digit->list digit) depth)]
    [_
     (define-values (l ft^) (hdL:impl core ft (add1 depth)))
     (build-ft0 core (seg-node->digit core l (add1 depth)) ft^ digit depth)]))

;; Split digit: returns (remaining-idx, left-list, middle, right-list)
(define (seg-split-digit core digit idx depth)
  (define m (lambda (n) (car (seg-node-measure core n depth))))
  (match digit
    [(digit:1 a)
     (if (< idx (m a))
         (values idx '() a '())
         (error 'seg-split-digit "index out of bounds"))]
    [(digit:2 a b)
     (define a-sz (m a))
     (cond
       [(< idx a-sz) (values idx '() a (list b))]
       [(< idx (+ a-sz (m b))) (values (- idx a-sz) (list a) b '())]
       [else (error 'seg-split-digit "index out of bounds")])]
    [(digit:3 a b c)
     (define a-sz (m a))
     (define ab-sz (+ a-sz (m b)))
     (cond
       [(< idx a-sz) (values idx '() a (list b c))]
       [(< idx ab-sz) (values (- idx a-sz) (list a) b (list c))]
       [(< idx (+ ab-sz (m c))) (values (- idx ab-sz) (list a b) c '())]
       [else (error 'seg-split-digit "index out of bounds")])]
    [(digit:4 a b c d)
     (define a-sz (m a))
     (define ab-sz (+ a-sz (m b)))
     (define abc-sz (+ ab-sz (m c)))
     (cond
       [(< idx a-sz) (values idx '() a (list b c d))]
       [(< idx ab-sz) (values (- idx a-sz) (list a) b (list c d))]
       [(< idx abc-sz) (values (- idx ab-sz) (list a b) c (list d))]
       [(< idx (+ abc-sz (m d))) (values (- idx abc-sz) (list a b c) d '())]
       [else (error 'seg-split-digit "index out of bounds")])]))

;; Split node: returns (remaining-idx, left-list, middle, right-list)
;; Children are at depth-1 level
(define (seg-split-node core node idx depth)
  (define m (lambda (n) (car (seg-node-measure core n (sub1 depth)))))
  (match node
    [(node:2 v a b)
     (define a-sz (m a))
     (cond
       [(< idx a-sz) (values idx '() a (list b))]
       [(< idx (car v)) (values (- idx a-sz) (list a) b '())]
       [else (error 'seg-split-node "index out of bounds")])]
    [(node:3 v a b c)
     (define a-sz (m a))
     (define ab-sz (+ a-sz (m b)))
     (cond
       [(< idx a-sz) (values idx '() a (list b c))]
       [(< idx ab-sz) (values (- idx a-sz) (list a) b (list c))]
       [(< idx (car v)) (values (- idx ab-sz) (list a b) c '())]
       [else (error 'seg-split-node "index out of bounds")])]))

;; Main split implementation: returns (remaining-idx, left-ft, middle, right-ft)
(define (seg-split:impl core ft idx depth)
  (match ft
    [(ft:empty) (error 'seg-split:impl "empty tree")]
    [(ft:single v)
     (if (< idx (car (seg-node-measure core v depth)))
         (values idx (ft:empty) v (ft:empty))
         (error 'seg-split:impl "index out of bounds"))]
    [(ft:deep total-measure lhs inner rhs)
     (define lhs-sz (car (measure:digit core lhs depth)))
     (define inner-sz (car (measure:ft core inner (add1 depth))))
     (define lhs-inner-sz (+ lhs-sz inner-sz))
     (cond
       [(< idx lhs-sz)
        ;; Split in left digit
        (define-values (idx^ l m r) (seg-split-digit core lhs idx depth))
        (define left (seg-digit-list->ft core l depth))
        (match inner
          [(ft:empty)
           (values idx^ left m (seg-digit-list2->ft core (append r (seg-digit->list rhs)) depth))]
          [_
           (define-values (right-digit inner^) (seg-digit-list+ft->digit core r inner depth hdL:impl))
           (values idx^ left m (build-ft0 core right-digit inner^ rhs depth))])]
       [(< idx lhs-inner-sz)
        ;; Split in inner
        (define-values (rest-idx l-inner m-node r-inner)
          (seg-split:impl core inner (- idx lhs-sz) (add1 depth)))
        (define left (seg-left-digit+ft->ft core lhs l-inner depth))
        (define right (seg-right-digit+ft->ft core rhs r-inner depth))
        ;; Split the middle node
        (define-values (idx^ l^ m^ r^) (seg-split-node core m-node rest-idx (add1 depth)))
        ;; Append l^ to left, prepend r^ to right
        (define left^ (for/fold ([t left]) ([n l^]) (consR:impl core t n depth)))
        (define right^ (for/foldr ([t right]) ([n r^]) (consL:impl core t n depth)))
        (values idx^ left^ m^ right^)]
       [(< idx (car total-measure))
        ;; Split in right digit
        (define-values (idx^ l m r) (seg-split-digit core rhs (- idx lhs-inner-sz) depth))
        (define right (seg-digit-list->ft core r depth))
        (match inner
          [(ft:empty)
           (values idx^ (seg-digit-list2->ft core (append (seg-digit->list lhs) l) depth) m right)]
          [_
           (define-values (left-digit inner^) (seg-digit-list+ft->digit core l inner depth hdR:impl))
           (values idx^ (build-ft0 core lhs inner^ left-digit depth) m right)])]
       [else (error 'seg-split:impl "index out of bounds")])]))

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
    [(= idx cnt) (values ss (segment-seq cfg (ft:empty) 0))]
    [else
     (define core (make-ft-config cfg))
     (define-values (l m r) (seg-split core ft idx))
     (values (segment-seq cfg l idx)
             (segment-seq cfg (consL:impl core r m 0) (- cnt idx)))]))

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
     (segment-seq cfg new-ft (sub1 cnt))]
    [(= idx (sub1 cnt))
     (define-values (_elem new-ft) (hdR:impl core ft 0))
     (segment-seq cfg new-ft (sub1 cnt))]
    [else
     ;; O(log n) using split
     (define-values (l _m r) (seg-split core ft idx))
     (segment-seq cfg (concat:impl core l r 0) (sub1 cnt))]))

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
     (range-query-ft cfg ft lo hi 0)]))

(define (range-query-ft cfg ft lo hi depth)
  (match ft
    [(ft:empty) (seg-config-identity cfg)]
    [(ft:single a)
     (if (and (= lo 0) (= hi (node-size cfg a depth)))
         (if (= depth 0)
             ((seg-config-extract cfg) a)
             (cdr (match a [(node:2 v _ _) v] [(node:3 v _ _ _) v])))
         (range-query-node cfg a lo hi depth))]
    [(ft:deep _ left inner right)
     (define left-sz (digit-size cfg left depth))
     (define inner-sz (ft-size cfg inner (add1 depth)))
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
                          (add1 depth))
           id))
     (define right-contrib
       (if (> hi right-start)
           (range-query-digit cfg right
                             (max 0 (- lo right-start))
                             (- hi right-start)
                             depth)
           id))
     (comb (comb left-contrib inner-contrib) right-contrib)]))

(define (range-query-digit cfg digit lo hi depth)
  (define comb (seg-config-combine cfg))
  (define id (seg-config-identity cfg))
  (define elems (match digit
                  [(digit:1 a) (list a)]
                  [(digit:2 a b) (list a b)]
                  [(digit:3 a b c) (list a b c)]
                  [(digit:4 a b c d) (list a b c d)]))
  (define-values (result _)
    (for/fold ([acc id] [pos 0]) ([e elems])
      (define e-sz (node-size cfg e depth))
      (define e-end (+ pos e-sz))
      (values
       (if (and (< pos hi) (> e-end lo))
           (comb acc
                 (if (and (<= lo pos) (>= hi e-end))
                     ;; Entire element is in range
                     (if (= depth 0)
                         ((seg-config-extract cfg) e)
                         (cdr (match e [(node:2 v _ _) v] [(node:3 v _ _ _) v])))
                     ;; Partial - recurse into node
                     (range-query-node cfg e (max 0 (- lo pos)) (min e-sz (- hi pos)) depth)))
           acc)
       e-end)))
  result)

(define (range-query-node cfg node lo hi depth)
  (if (= depth 0)
      ((seg-config-extract cfg) node)
      (let ([comb (seg-config-combine cfg)]
            [id (seg-config-identity cfg)])
        (define children (match node
                           [(node:2 _ a b) (list a b)]
                           [(node:3 _ a b c) (list a b c)]))
        (define-values (result _)
          (for/fold ([acc id] [pos 0]) ([c children])
            (define c-sz (node-size cfg c (sub1 depth)))
            (define c-end (+ pos c-sz))
            (values
             (if (and (< pos hi) (> c-end lo))
                 (comb acc
                       (if (and (<= lo pos) (>= hi c-end))
                           ;; Full child in range
                           (if (= (sub1 depth) 0)
                               ((seg-config-extract cfg) c)
                               (cdr (match c [(node:2 v _ _) v] [(node:3 v _ _ _) v])))
                           ;; Partial
                           (range-query-node cfg c (max 0 (- lo pos)) (min c-sz (- hi pos)) (sub1 depth))))
                 acc)
             c-end)))
        result)))

;; ========================================
;; Concat
;; ========================================

(define (segment-seq-concat ss1 ss2)
  (match-define (segment-seq cfg1 ft1 cnt1) ss1)
  (match-define (segment-seq cfg2 ft2 cnt2) ss2)
  (segment-seq cfg1 (concat:impl (make-ft-config cfg1) ft1 ft2 0) (+ cnt1 cnt2)))

;; ========================================
;; Conversion
;; ========================================

(define (segment-seq->list ss)
  (match-define (segment-seq cfg ft _) ss)
  (define core (make-ft-config cfg))
  (let loop ([t ft] [acc '()])
    (define-values (elem rest) (hdL:impl core t 0))
    (if elem (loop rest (cons elem acc)) (reverse acc))))

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
