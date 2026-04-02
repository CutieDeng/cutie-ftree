#lang racket/base

; ordl

(require racket/match racket/bool)
(require racket/trace)
(require "private/core.rkt" "private/core-algorithm.rkt")

(require racket/dict)

(struct ordered-map (cmp-fn ft)
  #:transparent
  #:methods gen:dict
  [
    (define (dict-ref dict key
      [default
       (lambda ()
         (error "key not found" key))
       ])
      (match (ordered-map-query dict key)
        [#f (if (procedure? default) (default) default)]
        [(cons _ x) x]
        ) ; match: ordered-map-query
      ) ; define dict-ref
    (define (dict-set dict key val)
      (ordered-map-insert dict key val #t)
      ) ; define dict-set
    (define (dict-remove dict key)
      (match-define-values (r _) (ordered-map-delete dict key)) r)
    (define (dict-iterate-first dict)
      (ordered-map-max dict))
    (define (dict-iterate-next dict pos)
      (ordered-map-query-weak dict (car pos) '<))
    (define (dict-iterate-key dict k) (car k))
    (define (dict-iterate-value dict k) (cdr k))
    ] ; #:methods gen:dict
  ) ; struct ordered-map

;; 复合测量值结构：同时存储最小键和元素计数
(struct om-measure (min-key count) #:transparent)

(define ordered-map-core (ft:config
   (lambda () (om-measure #f 0))
   (match-lambda
     [(cons k _) (om-measure k 1)]
     ) ; match-lambda
   (lambda (m0 m1)
     (om-measure
      (om-measure-min-key m0)
      (+ (om-measure-count m0) (om-measure-count m1))
      )
     ) ; lambda: combine measures
   ) ; ft:config
  ) ; define ordered-map-core

(define (ordered-map-empty? ordl)
  (match-define (ordered-map _ f) ordl)
  (match f
    [(ft:empty) #t]
    [_ #f]
    ) ; match: f
  ) ; define ordered-map-empty?

(define (ordered-map-min o)
  (match-define (ordered-map _ f) o)
  (match f
    [(ft:empty) #f]
    [_ (hdL-view f)]
    ) ; match: f
  ) ; define ordered-map-min

(define (ordered-map-max o)
  (match-define (ordered-map _ f) o)
  (match f
    [(ft:empty) #f]
    [_ (hdR-view f)]
    ) ; match: f
  ) ; define ordered-map-max

(define (ordered-map-min-key o)
  (match-define (ordered-map _ f) o)
  (match f
    [(ft:single (cons k _)) k]
    [(ft:deep (om-measure k _) _ _ _) k]
    ) ; match: f
  ) ; define ordered-map-min-key

(define (ordered-map-min-key-node node depth)
  (match depth
    [0 (car node)]
    [_
     (match node
       [(or (node:2 (om-measure k _) _ _)
            (node:3 (om-measure k _) _ _ _))
        k]
       ) ; match: node
     ]
    ) ; match: depth
  ) ; define ordered-map-min-key-node

(define (ordered-map-min-key-ft ft depth)
  (match ft
    [(ft:single v) (ordered-map-min-key-node v depth)]
    [(ft:deep (om-measure k _) _ _ _) k]
    ) ; match: ft
  ) ; define ordered-map-min-key-ft

(define ordered-map-size-changed? (make-parameter #f))

(define (ordered-map-min-key-digit digit depth)
  (match digit
    [(or (digit:1 x) (digit:2 x _) (digit:3 x _ _) (digit:4 x _ _ _)) (ordered-map-min-key-node x depth)]
    ) ; match: digit
  ) ; define ordered-map-min-key-digit

;; 辅助函数：获取节点的元素计数
(define (node-count node depth)
  (match depth
    [0 1]
    [_
     (match node
       [(node:2 (om-measure _ c) _ _) c]
       [(node:3 (om-measure _ c) _ _ _) c]
       ) ; match: node
     ]
    ) ; match: depth
  ) ; define node-count

;; 辅助函数：获取 digit 的元素计数
(define (digit-count digit depth)
  (match digit
    [(digit:1 a) (node-count a depth)]
    [(digit:2 a b)
     (+ (node-count a depth)
        (node-count b depth)
        )
     ]
    [(digit:3 a b c)
     (+ (node-count a depth)
        (node-count b depth)
        (node-count c depth)
        )
     ]
    [(digit:4 a b c d)
     (+ (node-count a depth)
        (node-count b depth)
        (node-count c depth)
        (node-count d depth)
        )
     ]
    ) ; match: digit
  ) ; define digit-count

;; 辅助函数：获取 ft 的元素计数
(define (ft-count ft depth)
  (match ft
    [(ft:empty) 0]
    [(ft:single v) (node-count v depth)]
    [(ft:deep (om-measure _ c) _ _ _) c]
    ) ; match: ft
  ) ; define ft-count

;; 构建带正确 measure 的 node:2
(define (make-node2 min-key x0 x1 depth)
  (node:2
   (om-measure
    min-key
    (+ (node-count x0 depth) (node-count x1 depth))
    )
   x0
   x1)
  ) ; define make-node2

;; 构建带正确 measure 的 node:3
(define (make-node3 min-key x0 x1 x2 depth)
  (node:3
   (om-measure
    min-key
    (+ (node-count x0 depth) (node-count x1 depth) (node-count x2 depth))
    )
   x0
   x1
   x2)
  ) ; define make-node3

;; 构建带正确 measure 的 ft:deep
(define (make-ft-deep min-key left inner right depth)
  (ft:deep
   (om-measure
    min-key
    (+ (digit-count left depth) (ft-count inner (add1 depth)) (digit-count right depth))
    )
   left
   inner
   right)
  ) ; define make-ft-deep

(define (ordered-map-query-node:impl node cmp-fn key depth)
  (match depth
    [0
     (define cmp-rst (cmp-fn (car node) key))
     (match cmp-rst
       ['= node]
       [(or '< '>) #f]
       ) ; match: cmp-rst at depth 0
    ]
    [_
     (define sub-depth (sub1 depth))
     (match node
       [(node:2 _ x0 x1)
        (define x1-key
          (ordered-map-min-key-node x1 sub-depth))
        (define x1-cmp-rst (cmp-fn x1-key key))
        (match x1-cmp-rst
          [(or '= '<)
           (ordered-map-query-node:impl x1 cmp-fn key sub-depth)]
          ['>
           (ordered-map-query-node:impl x0 cmp-fn key sub-depth)]
          ) ; match: x1-cmp-rst
        ]
       [(node:3 _ x0 x1 x2)
        (define x2-key
          (ordered-map-min-key-node x2 sub-depth))
        (define x2-cmp-rst (cmp-fn x2-key key))
        (match x2-cmp-rst
          [(or '= '<)
           (ordered-map-query-node:impl x2 cmp-fn key sub-depth)]
          ['>
           (define x1-key
             (ordered-map-min-key-node x1 sub-depth))
           (define x1-cmp-rst (cmp-fn x1-key key))
           (match x1-cmp-rst
             [(or '= '<)
              (ordered-map-query-node:impl x1 cmp-fn key sub-depth)]
             ['>
              (ordered-map-query-node:impl x0 cmp-fn key sub-depth)]
             ) ; match: x1-cmp-rst
           ]
          ) ; match: x2-cmp-rst
        ]
       ) ; match: node
    ]
    ) ; match: depth
  ) ; define ordered-map-query-node:impl

(define (ordered-map-query-ft:impl ft cmp-fn key depth)
  (match ft
    [(ft:empty) #f]
    [(ft:single node) (ordered-map-query-node:impl node cmp-fn key depth)]
    [(ft:deep _ left inner right)
     (define inner-depth (add1 depth))
     (define right-v (ordered-map-min-key-digit right depth))
     (define right-v-cmp-rst (cmp-fn right-v key))
     (match right-v-cmp-rst
       [(or '= '<) (ordered-map-query-digit:impl right cmp-fn key depth)]
       ['> (=> f)
        (match inner
          [(ft:empty) (f)]
          [_ (void)]
          ) ; match: inner emptiness
        (define inner-v
          (ordered-map-min-key-ft inner inner-depth))
        (define inner-v-cmp-rst (cmp-fn inner-v key))
        (match inner-v-cmp-rst
          [(or '= '<)
           (ordered-map-query-ft:impl inner cmp-fn key inner-depth)]
          ['> (f)]
          ) ; match: inner-v-cmp-rst
        ]
       ['> (ordered-map-query-digit:impl left cmp-fn key depth)]
       ) ; match: right-v-cmp-rst
    ]
    ) ; match: ft
  ) ; define ordered-map-query-ft:impl

(define (ordered-map-query-digit:impl digit cmp-fn key depth)
  (define l
    (reverse
     (digit-add-list digit '())
     ))
  (let loop0 ([l l])
    (match l
      [(cons lh l*)
       (define v (ordered-map-min-key-node lh depth))
       (define v-cmp-rst (cmp-fn v key))
       (match v-cmp-rst
         [(or '= '<) (ordered-map-query-node:impl lh cmp-fn key depth)]
         ['> (loop0 l*)]
         ) ; match: v-cmp-rst
      ]
      ['() #f]
      ) ; match: l
    ) ; let loop0
  ) ; define ordered-map-query-digit:impl

(define (ordered-map-query o k)
  (match-define (ordered-map cmp-fn ft) o)
  (ordered-map-query-ft:impl ft cmp-fn k 0)
  ) ; define ordered-map-query

; return node, #f / node, node2
; never in depth 0
(define (ordered-map-insert-node:impl node cmp-fn key value depth replace?)
  (match depth
    [1
     (match node
       [(node:2 _
                (and x0 (cons k0 _))
                (and x1 (cons k1 _))
                )
       (define k1-cmp-rst (cmp-fn k1 key))
       (match k1-cmp-rst
          ['=
           (if replace?
               (values (make-node2 k0 x0 (cons key value) 0) #f)
               (values node #f)
               )]
          ['<
           (ordered-map-size-changed? #t)
           (values (make-node3 k0 x0 x1 (cons key value) 0) #f)]
          ['>
           (define k0-cmp-rst (cmp-fn k0 key))
           (match k0-cmp-rst
             ['=
              (if replace?
                  (values (make-node2 key (cons key value) x1 0) #f)
                  (values node #f)
                  )]
             ['<
              (ordered-map-size-changed? #t)
              (values (make-node3 k0 x0 (cons key value) x1 0) #f)]
             ['>
              (ordered-map-size-changed? #t)
              (values (make-node3 key (cons key value) x0 x1 0) #f)]
             ) ; match: k0-cmp-rst
           ]
          ) ; match: k1-cmp-rst
        ]
       [(node:3 _
                (and x0 (cons k0 _))
                (and x1 (cons k1 _))
                (and x2 (cons k2 _))
                )
        (define k1-cmp-rst (cmp-fn k1 key))
        (match k1-cmp-rst
          ['=
           (if replace?
               (values (make-node3 k0 x0 (cons key value) x2 0) #f)
               (values node #f)
               )]
          ['<
           (define k2-cmp-rst (cmp-fn k2 key))
           (match k2-cmp-rst
             ['=
              (if replace?
                  (values (make-node3 k0 x0 x1 (cons key value) 0) #f)
                  (values node #f)
                  )]
             ['<
              (ordered-map-size-changed? #t)
              (values
               (make-node2 k0 x0 x1 0)
               (make-node2 k2 x2 (cons key value) 0)
               )]
             ['>
              (ordered-map-size-changed? #t)
              (values
               (make-node2 k0 x0 x1 0)
               (make-node2 key (cons key value) x2 0)
               )]
             ) ; match: k2-cmp-rst
           ]
          ['>
           (define k0-cmp-rst (cmp-fn k0 key))
           (match k0-cmp-rst
             ['=
              (if replace?
                  (values (make-node3 key (cons key value) x1 x2 0) #f)
                  (values node #f)
                  )]
             ['<
              (ordered-map-size-changed? #t)
              (values
               (make-node2 k0 x0 (cons key value) 0)
               (make-node2 k1 x1 x2 0)
               )]
             ['>
              (ordered-map-size-changed? #t)
              (values
               (make-node2 key (cons key value) x0 0)
               (make-node2 k1 x1 x2 0)
               )]
             ) ; match: k0-cmp-rst
           ]
          ) ; match: k1-cmp-rst
        ]
       ) ; match: node at depth 1
     ]
    [_
     (define sub-depth (sub1 depth))
     (match node
      [(node:2 (om-measure k0 _) x0 x1)
        (define k1 (ordered-map-min-key-node x1 sub-depth))
        (match (cmp-fn k1 key)
          [(or '= '<)
           (define-values (node0 node1)
             (ordered-map-insert-node:impl x1 cmp-fn key value sub-depth replace?))
           (cond
             [(and (eq? x1 node0) (not node1)) (values node #f)]
             [node1 (values (make-node3 k0 x0 node0 node1 sub-depth) #f)]
             [(not node1) (values (make-node2 k0 x0 node0 sub-depth) #f)]
             )
           ]
          ['>
           (define-values (node0 node1)
             (ordered-map-insert-node:impl x0 cmp-fn key value sub-depth replace?))
           (cond
             [(and (eq? x0 node0) (not node1)) (values node #f)]
             [node1 (values (make-node3 k0 node0 node1 x1 sub-depth) #f)]
             [(not node1) (values (make-node2 k0 node0 x1 sub-depth) #f)]
             )
           ] ; match: cmp-fn k1 key for node:2
        )
      ]
      [(node:3 (om-measure k0 _) x0 x1 x2)
        (define k1 (ordered-map-min-key-node x1 sub-depth))
        (match (cmp-fn k1 key)
          ['<
            (define k2 (ordered-map-min-key-node x2 sub-depth))
            (match (cmp-fn k2 key)
              [(or '< '=)
               (define-values (node0 node1)
                 (ordered-map-insert-node:impl x2 cmp-fn key value sub-depth replace?))
               (cond
                 [(and (eq? x2 node0) (not node1)) (values node #f)]
                 [node1 (values
                   (make-node2 k0 x0 x1 sub-depth)
                   (make-node2
                    (ordered-map-min-key-node node0 sub-depth)
                    node0
                    node1
                    sub-depth)
                   )]
                 [(not node1)
                  (values (make-node3 k0 x0 x1 node0 sub-depth) #f)]
                 )
               ]
              ['>
               (define-values (node0 node1)
                 (ordered-map-insert-node:impl x1 cmp-fn key value sub-depth replace?))
               (cond
                 [(and (eq? x1 node0) (not node1)) (values node #f)]
                 [node1 (values
                   (make-node2 k0 x0 node0 sub-depth)
                   (make-node2
                    (ordered-map-min-key-node node1 sub-depth)
                    node1
                    x2
                    sub-depth)
                   )]
                 [(not node1)
                  (values (make-node3 k0 x0 node0 x2 sub-depth) #f)]
                 )
               ]
            )
          ]
          ['=
           (define-values (node0 node1)
             (ordered-map-insert-node:impl x1 cmp-fn key value sub-depth replace?))
           (cond
             [(and (eq? x1 node0) (not node1)) (values node #f)]
             [node1 (values
               (make-node2 k0 x0 node0 sub-depth)
               (make-node2
                (ordered-map-min-key-node node1 sub-depth)
                node1
                x2
                sub-depth)
               )]
             [(not node1)
              (values (make-node3 k0 x0 node0 x2 sub-depth) #f)]
             )
           ]
          ['>
           (define-values (node0 node1)
             (ordered-map-insert-node:impl x0 cmp-fn key value sub-depth replace?))
           (cond
             [(and (eq? x0 node0) (not node1)) (values node #f)]
             [node1 (values
               (make-node2 k0 node0 node1 sub-depth)
               (make-node2 k1 x1 x2 sub-depth)
               )]
             [(not node1)
              (values (make-node3 k0 node0 x1 x2 sub-depth) #f)]
             )
           ]
        ) ; match: cmp-fn k1 key for node:3
      ]
      ) ; match: node at depth > 1
     ]
    ) ; match: depth
  ) ; define ordered-map-insert-node:impl

; return ft
(define (ordered-map-insert-ft:impl ft cmp-fn key value depth replace?)
  (match ft
    [(ft:single x)
     (match depth
        [0
         (match-define (cons k0 _) x)
         (match (cmp-fn k0 key)
           ['<
            (ordered-map-size-changed? #t)
            (make-ft-deep k0 (digit:1 x) (ft:empty) (digit:1 (cons key value)) 0)]
           ['= (if replace? (ft:single (cons key value)) ft)]
           ['>
            (ordered-map-size-changed? #t)
            (make-ft-deep key (digit:1 (cons key value)) (ft:empty) (digit:1 x) 0)]
           ) ; match: cmp-fn k0 key
        ]
        [_
          (define-values (node0 node1)
            (ordered-map-insert-node:impl x cmp-fn key value depth replace?))
          (cond
            [(and (eq? x node0) (not node1)) ft]
            [node1
             (make-ft-deep (ordered-map-min-key-node node0 depth) (digit:1 node0) (ft:empty) (digit:1 node1) depth)]
            [(not node1) (ft:single node0)]
          )
        ]
        ) ; match: depth
    ]
    [(ft:deep (om-measure o _) left inner right)
     (define inner-depth (add1 depth))
     (define right-v (ordered-map-min-key-digit right depth))
     (match (cmp-fn right-v key)
       [(or '< '=)
        (define right^ (ordered-map-insert-digit:impl right cmp-fn key value depth replace?))
        (cond
          [(eq? right^ right) ft]
          [else
           (match right^
             [`(,x0 ,x1 ,x2 ,x3 ,x4)
              (define right^^ (digit:2 x3 x4))
              (define node0
                (make-node3 (ordered-map-min-key-node x0 depth) x0 x1 x2 depth))
              (define inner^
                (consR:impl ordered-map-core inner node0 inner-depth))
              (make-ft-deep o left inner^ right^^ depth)]
             [r
              (define right^^ (list->digit r depth))
              (make-ft-deep o left inner right^^ depth)]
             ) ; match: right^
           ]
          ) ; cond: right insert result
        ]
       ['>
        (match inner
          [(ft:empty)
           (define left^
             (ordered-map-insert-digit:impl left cmp-fn key value depth replace?))
           (cond
             [(eq? left left^) ft]
             [else
              (match left^
                [`(,x0 ,x1 ,x2 ,x3 ,x4)
                 (define left^^ (digit:2 x0 x1))
                 (define node0
                   (make-node3 (ordered-map-min-key-node x2 depth) x2 x3 x4 depth))
                 (define inner^
                   (consL:impl ordered-map-core inner node0 inner-depth))
                 (make-ft-deep o left^^ inner^ right depth)]
                [l
                 (define left^^ (list->digit l depth))
                 (make-ft-deep o left^^ inner right depth)]
                ) ; match: left^ with empty inner
              ]
             ) ; cond: left insert result with empty inner
           ]
          [_
           (define inner-v
             (ordered-map-min-key-ft inner inner-depth))
           (match (cmp-fn inner-v key)
             [(or '< '=)
              (define inner^
                (ordered-map-insert-ft:impl inner cmp-fn key value inner-depth replace?))
              (if (eq? inner inner^)
                  ft
                  (make-ft-deep o left inner^ right depth)
                  )]
             ['>
              (define left^
                (ordered-map-insert-digit:impl left cmp-fn key value depth replace?))
              (cond
                [(eq? left left^) ft]
                [else
                 (match left^
                  [`(,x0 ,x1 ,x2 ,x3 ,x4)
                    (define left^^ (digit:2 x0 x1))
                    (define node0
                      (make-node3 (ordered-map-min-key-node x2 depth) x2 x3 x4 depth))
                    (define inner^
                      (consL:impl ordered-map-core inner node0 inner-depth))
                    (make-ft-deep o left^^ inner^ right depth)]
                   [l
                    (define left^^ (list->digit l depth))
                    (make-ft-deep o left^^ inner right depth)]
                   ) ; match: left^ with non-empty inner
                 ]
                ) ; cond: left insert result with non-empty inner
              ]
             ) ; match: cmp-fn inner-v key
           ]
          ) ; match: inner
        ]
       ) ; match: cmp-fn right-v key
    ]
    ) ; match: ft
  ) ; define ordered-map-insert-ft:impl

; return list (1 ~ 5)
(define (ordered-map-insert-digit:impl digit cmp-fn key value depth replace?)
  (define kv (cons key value))
  (match depth
    [0
      (match digit
        [(digit:1
          (and x0 (cons k0 _))
          )
          (match (cmp-fn k0 key)
            ['<
             (ordered-map-size-changed? #t)
             (list x0 kv)]
            ['= (if replace? (list kv) digit)]
          )
        ]
        [(digit:2
          (and x0 (cons k0 _))
          (and x1 (cons k1 _))
          )
          (match (cmp-fn k1 key)
            ['<
             (ordered-map-size-changed? #t)
             (list x0 x1 kv)]
            ['= (if replace? (list x0 kv) digit)]
            ['> 
              (match (cmp-fn k0 key)
                ['<
                 (ordered-map-size-changed? #t)
                 (list x0 kv x1)]
                ['= (if replace? (list kv x1) digit)]
              )]
          )
        ]
        [(digit:3
          (and x0 (cons k0 _))
          (and x1 (cons k1 _))
          (and x2 (cons k2 _))
          )
          (match (cmp-fn k1 key)
            ['< 
              (match (cmp-fn k2 key)
                ['<
                 (ordered-map-size-changed? #t)
                 (list x0 x1 x2 kv)]
                ['= (if replace? (list x0 x1 kv) digit)]
                ['>
                 (ordered-map-size-changed? #t)
                 (list x0 x1 kv x2)]
              )]
            ['= (if replace? (list x0 kv x2) digit)]
            ['>
              (match (cmp-fn k0 key)
                ['<
                 (ordered-map-size-changed? #t)
                 (list x0 kv x1 x2)]
                ['= (if replace? (list kv x1 x2) digit)]
              )]
          )
        ]
        [(digit:4
          (and x0 (cons k0 _))
          (and x1 (cons k1 _))
          (and x2 (cons k2 _))
          (and x3 (cons k3 _))
          )
          (match (cmp-fn k2 key)
            ['< 
              (match (cmp-fn k3 key)
                ['<
                 (ordered-map-size-changed? #t)
                 (list x0 x1 x2 x3 kv)]
                ['= (if replace? (list x0 x1 x2 kv) digit)]
                ['>
                 (ordered-map-size-changed? #t)
                 (list x0 x1 x2 kv x3)]
              )]
            ['= (if replace? (list x0 x1 kv x3) digit)]
            ['> 
              (match (cmp-fn k1 key)
                ['<
                 (ordered-map-size-changed? #t)
                 (list x0 x1 kv x2 x3)]
                ['= (if replace? (list x0 kv x2 x3) digit)]
                ['>
                  (match (cmp-fn k0 key)
                    ['<
                     (ordered-map-size-changed? #t)
                     (list x0 kv x1 x2 x3)]
                    ['= (if replace? (list kv x1 x2 x3) digit)]
                  )]
              )]
          )
        ]
      )
    ]
    [_
      (match digit
        [(digit:1 x0)
          (define-values (node0 node1)
            (ordered-map-insert-node:impl x0 cmp-fn key value depth replace?))
          (cond
            [(and (eq? node0 x0) (not node1)) digit]
            [node1 (list node0 node1)]
            [(not node1) (list node0)]
          )
        ]
        [(digit:2 x0 x1)
          (define k1 (ordered-map-min-key-node x1 depth))
          (match (cmp-fn k1 key)
            [(or '< '=)
              (define-values (node0 node1)
                (ordered-map-insert-node:impl x1 cmp-fn key value depth replace?))
              (cond
                [(and (eq? x1 node0) (not node1)) digit]
                [node1 (list x0 node0 node1)]
                [(not node1) (list x0 node0)]
              )
            ]
            ['> 
              (define-values (node0 node1)
                (ordered-map-insert-node:impl x0 cmp-fn key value depth replace?))
              (cond
                [(and (eq? x0 node0) (not node1)) digit]
                [node1 (list node0 node1 x1)]
                [(not node1) (list node0 x1)]
              )
            ]
          )
        ]
        [(digit:3 x0 x1 x2)
          (define k1 (ordered-map-min-key-node x1 depth))
          (match (cmp-fn k1 key)
            ['< (=> f)
              (match (cmp-fn (ordered-map-min-key-node x2 depth) key)
                [(or '< '=) 
                  (define-values (node0 node1)
                    (ordered-map-insert-node:impl x2 cmp-fn key value depth replace?))
                  (cond
                    [(and (eq? x2 node0) (not node1)) digit]
                    [node1 (list x0 x1 node0 node1)]
                    [(not node1) (list x0 x1 node0)]
                  )
                ]
                ['> (f)]
              )
            ]
            [(or '< '=)
              (define-values (node0 node1)
                (ordered-map-insert-node:impl x1 cmp-fn key value depth replace?))
              (cond
                [(and (eq? x1 node0) (not node1)) digit]
                [node1 (list x0 node0 node1 x2)]
                [(not node1) (list x0 node0 x2)]
              )
            ]
            ['> 
              (define-values (node0 node1)
                (ordered-map-insert-node:impl x0 cmp-fn key value depth replace?))
              (cond
                [(and (eq? x0 node0) (not node1)) digit]
                [node1 (list node0 node1 x1 x2)]
                [(not node1) (list node0 x1 x2)]
              )
            ]
          )
        ]
        [(digit:4 x0 x1 x2 x3)
          (define k2 (ordered-map-min-key-node x2 depth))
          (match (cmp-fn k2 key)
            ['< (=> f)
              (define k3 (ordered-map-min-key-node x3 depth))
              (match (cmp-fn k3 key)
                [(or '< '=) 
                  (define-values (node0 node1)
                    (ordered-map-insert-node:impl x3 cmp-fn key value depth replace?))
                  (cond
                    [(and (eq? x3 node0) (not node1)) digit]
                    [node1 (list x0 x1 x2 node0 node1)]
                    [(not node1) (list x0 x1 x2 node0)]
                  )
                ]
                ['> (f)]
              )
            ]
            [(or '< '=)
              (define-values (node0 node1)
                (ordered-map-insert-node:impl x2 cmp-fn key value depth replace?))
              (cond
                [(and (eq? x2 node0) (not node1)) digit]
                [node1 (list x0 x1 node0 node1 x3)]
                [(not node1) (list x0 x1 node0 x3)]
              )
            ]
            ['>
              (define k1 (ordered-map-min-key-node x1 depth))
              (match (cmp-fn k1 key)
                [(or '< '=)
                  (define-values (node0 node1)
                    (ordered-map-insert-node:impl x1 cmp-fn key value depth replace?))
                  (cond
                    [(and (eq? x1 node0) (not node1)) digit]
                    [node1 (list x0 node0 node1 x2 x3)]
                    [(not node1) (list x0 node0 x2 x3)]
                  )
                ]
                ['>
                  (define-values (node0 node1)
                    (ordered-map-insert-node:impl x0 cmp-fn key value depth replace?))
                  (cond
                    [(and (eq? x0 node0) (not node1)) digit]
                    [node1 (list node0 node1 x1 x2 x3)]
                    [(not node1) (list node0 x1 x2 x3)]
                  )
                ]
              )
            ]
          )
        ]
      )
    ]
  )
)

(define (ordered-map-insert-ft-wrap ft cmp-fn key value replace?)
  (match ft
    [(ft:empty)
     (ordered-map-size-changed? #t)
     (define kv (cons key value))
     (ft:single kv)]
    [(ft:single _) (ordered-map-insert-ft:impl ft cmp-fn key value 0 replace?)]
    [(ft:deep (om-measure o _) _ _ _)
     (match (cmp-fn o key)
       [(or '< '=) (ordered-map-insert-ft:impl ft cmp-fn key value 0 replace?)]
       ['> (ordered-map-size-changed? #t) (consL:impl ordered-map-core ft (cons key value) 0)]
       ) ; match: cmp-fn o key
    ]
    ) ; match: ft
  ) ; define ordered-map-insert-ft-wrap

(define (ordered-map-insert ordl key value replace?)
  (match-define (ordered-map cmp-fn k) ordl)
  (define k^
    (ordered-map-insert-ft-wrap k cmp-fn key value replace?))
  (cond
    [(eq? k k^) ordl]
    [else (ordered-map cmp-fn k^)]
    ) ; cond: structural change
  ) ; define ordered-map-insert

; node, sub-node, del
(define (ordered-map-delete-node:impl node cmp-fn key depth)
  (match depth
    [1 (match node
      [(node:2 _
               (and x0 (cons k0 _))
               (and x1 (cons k1 _))
               )
        (match (cmp-fn k1 key)
          ['= (values #f x0 x1)]
          ['< (values node #f #f)]
          ['> (match (cmp-fn k0 key)
            ['= (values #f x1 x0)]
            ['< (values node #f #f)]
          )]
        )
      ]
      [(node:3 _
               (and x0 (cons k0 _))
               (and x1 (cons k1 _))
               (and x2 (cons k2 _))
               )
        (match (cmp-fn k1 key)
          ['= (values (make-node2 k0 x0 x2 0) #f x1)]
          ['< (match (cmp-fn k2 key)
            ['= (values (make-node2 k0 x0 x1 0) #f x2)]
            [(or '< '>) (values node #f #f)]
          )]
          ['> (match (cmp-fn k0 key)
            ['= (values (make-node2 k1 x1 x2 0) #f x0)]
            ['< (values node #f #f)]
          )]
        )
      ]
    )]
    [_ (define sub-depth (sub1 depth))
       (define sub2-depth (- depth 2))
       (match node
      [(node:2 (om-measure k0 _) x0 x1)
        (match (cmp-fn (ordered-map-min-key-node x1 sub-depth) key)
          [(or '= '<)
            (define-values (node0 subnode ret) (ordered-map-delete-node:impl x1 cmp-fn key sub-depth))
            (match* (node0 subnode)
              [(_ #f)
               (if (eq? x1 node0)
                   (values node #f ret)
                   (values (make-node2 k0 x0 node0 sub-depth) #f ret)
                   )]
              [(#f _) (match x0
                [(node:2 _ x00 x01)
                  (define subnode^ (make-node3 k0 x00 x01 subnode sub2-depth))
                  (values #f subnode^ ret)
                ]
                [(node:3 _ x00 x01 x02)
                  (define node^ (make-node2 k0 (make-node2 k0 x00 x01 sub2-depth) (make-node2 (ordered-map-min-key-node x02 sub2-depth) x02 subnode sub2-depth) sub-depth))
                  (values node^ #f ret)
                ]
              )]
            )
          ]
          ['>
            (define-values (node0 subnode ret) (ordered-map-delete-node:impl x0 cmp-fn key sub-depth))
            (match* (node0 subnode)
              [(_ #f)
               (if (eq? x0 node0)
                   (values node #f ret)
                   (values
                    (make-node2
                     (ordered-map-min-key-node node0 sub-depth)
                     node0
                     x1
                     sub-depth)
                    #f
                    ret)
                   )]
              [(#f _) (match x1
                [(node:2 _ x10 x11)
                  (define subnode^ (make-node3 (ordered-map-min-key-node subnode sub2-depth) subnode x10 x11 sub2-depth))
                  (values #f subnode^ ret)
                ]
                [(node:3 _ x10 x11 x12)
                  (define k0^ (ordered-map-min-key-node subnode sub2-depth))
                  (define node^ (make-node2 k0^
                    (make-node2 k0^ subnode x10 sub2-depth) (make-node2 (ordered-map-min-key-node x11 sub2-depth) x11 x12 sub2-depth) sub-depth))
                  (values node^ #f ret)
                ]
              )]
            )
          ]
        )
      ]
      [(node:3 (om-measure k0 _) x0 x1 x2)
        (match (cmp-fn (ordered-map-min-key-node x1 sub-depth) key)
          ['< (=> h)
            (match (cmp-fn (ordered-map-min-key-node x2 sub-depth) key)
              [(or '< '=)
                (define-values (node0 subnode ret) (ordered-map-delete-node:impl x2 cmp-fn key sub-depth))
                (match* (node0 subnode)
                  [(_ #f)
                   (if (eq? x2 node0)
                       (values node #f ret)
                       (values (make-node3 k0 x0 x1 node0 sub-depth) #f ret)
                       )]
                  [(#f _) (match x1
                    [(node:2 _ x10 x11)
                      (define node0^ (make-node3 (ordered-map-min-key-node x10 sub2-depth) x10 x11 subnode sub2-depth))
                      (values (make-node2 k0 x0 node0^ sub-depth) #f ret)
                    ]
                    [(node:3 _ x10 x11 x12)
                      (define node^ (make-node3 k0 x0 (make-node2 (ordered-map-min-key-node x10 sub2-depth) x10 x11 sub2-depth)
                        (make-node2 (ordered-map-min-key-node x12 sub2-depth) x12 subnode sub2-depth) sub-depth))
                      (values node^ #f ret)
                    ]
                  )]
                )
              ]
              ['> (h)]
            )
          ]
          [(or '< '=)
            (define-values (node0 subnode ret) (ordered-map-delete-node:impl x1 cmp-fn key sub-depth))
            (match* (node0 subnode)
              [(_ #f)
               (if (eq? x1 node0)
                   (values node #f ret)
                   (values (make-node3 k0 x0 node0 x2 sub-depth) #f ret)
                   )]
              [(#f _) (match x2
                [(node:2 _ x20 x21)
                  (define node0^ (make-node3 (ordered-map-min-key-node subnode sub2-depth) subnode x20 x21 sub2-depth))
                  (values (make-node2 k0 x0 node0^ sub-depth) #f ret)
                ]
                [(node:3 _ x20 x21 x22)
                  (define node^ (make-node3 k0 x0 (make-node2 (ordered-map-min-key-node subnode sub2-depth) subnode x20 sub2-depth)
                    (make-node2 (ordered-map-min-key-node x21 sub2-depth) x21 x22 sub2-depth) sub-depth))
                  (values node^ #f ret)
                ]
              )]
            )
          ]
          ['>
            (define-values (node0 subnode ret) (ordered-map-delete-node:impl x0 cmp-fn key sub-depth))
            (match* (node0 subnode)
              [(_ #f)
               (if (eq? x0 node0)
                   (values node #f ret)
                   (values
                    (make-node3
                     (ordered-map-min-key-node node0 sub-depth)
                     node0
                     x1
                     x2
                     sub-depth)
                    #f
                    ret)
                   )]
              [(#f _) (match x1
                [(node:2 _ x10 x11)
                  (define subnode^ (make-node3 (ordered-map-min-key-node subnode sub2-depth) subnode x10 x11 sub2-depth))
                  (values (make-node2 (ordered-map-min-key-node subnode^ sub-depth) subnode^ x2 sub-depth) #f ret)
                ]
                [(node:3 _ x10 x11 x12)
                  (define k0^ (ordered-map-min-key-node subnode sub2-depth))
                  (define node^ (make-node3 k0^
                    (make-node2 k0^ subnode x10 sub2-depth) (make-node2 (ordered-map-min-key-node x11 sub2-depth) x11 x12 sub2-depth) x2 sub-depth))
                  (values node^ #f ret)
                ]
              )]
            )
          ]
        )
      ]
    )]
  )
)

(define (ordered-map-node-mergeR node subnode depth)
  (define sub-depth (sub1 depth))
  (match node
    [(node:2 (om-measure o _) x0 x1)
     (values (make-node3 o x0 x1 subnode sub-depth) #f)]
    [(node:3 (om-measure o _) x0 x1 x2)
     (values (make-node2 o x0 x1 sub-depth)
             (make-node2
              (ordered-map-min-key-node x2 sub-depth)
              x2
              subnode
              sub-depth)
             )]
    ) ; match: node
  ) ; define ordered-map-node-mergeR

(define (ordered-map-node-mergeL node subnode depth)
  (define sub-depth (sub1 depth))
  (match node
    [(node:2 _ x0 x1) (values (make-node3 (ordered-map-min-key-node subnode sub-depth) subnode x0 x1 sub-depth) #f)]
    [(node:3 _ x0 x1 x2) (values
      (make-node2 (ordered-map-min-key-node subnode sub-depth) subnode x0 sub-depth)
      (make-node2 (ordered-map-min-key-node x1 sub-depth) x1 x2 sub-depth))
    ]
    ) ; match: node
  ) ; define ordered-map-node-mergeL

; ordered-map-delete-node:impl
; list, subnode, ret
(define (ordered-map-delete-digit:impl digit cmp-fn key depth)
  (match depth
    [0
     (match digit
       [(digit:1
         (and x0 (cons k0 _))
         )
        (match (cmp-fn k0 key)
          ['< (values digit #f #f)]
          ['= (values '() #f x0)]
          )]
       [(digit:2
         (and x0 (cons k0 _))
         (and x1 (cons k1 _))
         )
        (match (cmp-fn k1 key)
          ['< (values digit #f #f)]
          ['= (values (list x0) #f x1)]
          ['>
           (match (cmp-fn k0 key)
             ['< (values digit #f #f)]
             ['= (values (list x1) #f x0)]
             )]
          )]
       [(digit:3
         (and x0 (cons k0 _))
         (and x1 (cons k1 _))
         (and x2 (cons k2 _))
         )
        (match (cmp-fn k1 key)
          ['<
           (match (cmp-fn k2 key)
             [(or '< '>) (values digit #f #f)]
             ['= (values (list x0 x1) #f x2)]
             )]
          ['= (values (list x0 x2) #f x1)]
          ['>
           (match (cmp-fn k0 key)
             ['< (values digit #f #f)]
             ['= (values (list x1 x2) #f x0)]
             )]
          )]
       [(digit:4
         (and x0 (cons k0 _))
         (and x1 (cons k1 _))
         (and x2 (cons k2 _))
         (and x3 (cons k3 _))
         )
        (match (cmp-fn k2 key)
          ['<
           (match (cmp-fn k3 key)
             [(or '< '>) (values digit #f #f)]
             ['= (values (list x0 x1 x2) #f x3)]
             )]
          ['= (values (list x0 x1 x3) #f x2)]
          ['>
           (match (cmp-fn k1 key)
             ['< (values digit #f #f)]
             ['= (values (list x0 x2 x3) #f x1)]
             ['>
              (match (cmp-fn k0 key)
                ['< (values digit #f #f)]
                ['= (values (list x1 x2 x3) #f x0)]
                )]
             )]
          )]
       ) ; match: digit at depth 0
     ]
    [_
     (match digit
       [(digit:1 x0)
        (define-values (node0 subnode ret) (ordered-map-delete-node:impl x0 cmp-fn key depth))
        (cond
          [(eq? x0 node0) (values digit #f ret)]
          [node0 (values (list node0) #f ret)]
          [subnode (values '() subnode ret)]
          )]
       [(digit:2 x0 x1)
        (match (cmp-fn (ordered-map-min-key-node x1 depth) key)
          [(or '< '=)
           (define-values (node0 subnode ret) (ordered-map-delete-node:impl x1 cmp-fn key depth))
           (cond
             [(eq? x1 node0) (values digit #f ret)]
             [node0 (values (list x0 node0) #f ret)]
             [subnode
              (define-values (x0^ x1^) (ordered-map-node-mergeR x0 subnode depth))
              (values (if x1^ (list x0^ x1^) (list x0^)) #f ret)]
             )]
          ['>
           (define-values (node0 subnode ret) (ordered-map-delete-node:impl x0 cmp-fn key depth))
           (cond
             [(eq? x0 node0) (values digit #f ret)]
             [node0 (values (list node0 x1) #f ret)]
             [subnode
              (define-values (x0^ x1^) (ordered-map-node-mergeL x1 subnode depth))
              (values (if x1^ (list x0^ x1^) (list x0^)) #f ret)]
             )]
          )]
       [(digit:3 x0 x1 x2)
        (match (cmp-fn (ordered-map-min-key-node x1 depth) key)
          ['< (=> f)
           (match (cmp-fn (ordered-map-min-key-node x2 depth) key)
             [(or '< '=)
              (define-values (node0 subnode ret) (ordered-map-delete-node:impl x2 cmp-fn key depth))
              (cond
                [(eq? x2 node0) (values digit #f ret)]
                [node0 (values (list x0 x1 node0) #f ret)]
                [subnode
                 (define-values (x1^ x2^) (ordered-map-node-mergeR x1 subnode depth))
                 (values (if x2^ (list x0 x1^ x2^) (list x0 x1^)) #f ret)]
                )]
             ['> (f)]
             )]
          [(or '< '=)
           (define-values (node0 subnode ret) (ordered-map-delete-node:impl x1 cmp-fn key depth))
           (cond
             [(eq? x1 node0) (values digit #f ret)]
             [node0 (values (list x0 node0 x2) #f ret)]
             [subnode
              (define-values (x0^ x1^) (ordered-map-node-mergeR x0 subnode depth))
              (values (if x1^ (list x0^ x1^ x2) (list x0^ x2)) #f ret)]
             )]
          ['>
           (define-values (node0 subnode ret) (ordered-map-delete-node:impl x0 cmp-fn key depth))
           (cond
             [(eq? x0 node0) (values digit #f ret)]
             [node0 (values (list node0 x1 x2) #f ret)]
             [subnode
              (define-values (x0^ x1^) (ordered-map-node-mergeL x1 subnode depth))
              (values (if x1^ (list x0^ x1^ x2) (list x0^ x2)) #f ret)]
             )]
          )]
       [(digit:4 x0 x1 x2 x3)
        (match (cmp-fn (ordered-map-min-key-node x2 depth) key)
          ['< (=> f)
           (match (cmp-fn (ordered-map-min-key-node x3 depth) key)
             [(or '< '=)
              (define-values (node0 subnode ret) (ordered-map-delete-node:impl x3 cmp-fn key depth))
              (cond
                [(eq? x3 node0) (values digit #f ret)]
                [node0 (values (list x0 x1 x2 node0) #f ret)]
                [subnode
                 (define-values (x2^ x3^) (ordered-map-node-mergeR x2 subnode depth))
                 (values (if x3^ (list x0 x1 x2^ x3^) (list x0 x1 x2^)) #f ret)]
                )]
             ['> (f)]
             )]
          [(or '< '=)
           (define-values (node0 subnode ret) (ordered-map-delete-node:impl x2 cmp-fn key depth))
           (cond
             [(eq? x2 node0) (values digit #f ret)]
             [node0 (values (list x0 x1 node0 x3) #f ret)]
             [subnode
              (define-values (x1^ x2^) (ordered-map-node-mergeR x1 subnode depth))
              (values (if x2^ (list x0 x1^ x2^ x3) (list x0 x1^ x3)) #f ret)]
             )]
          ['>
           (match (cmp-fn (ordered-map-min-key-node x1 depth) key)
             [(or '< '=)
              (define-values (node0 subnode ret) (ordered-map-delete-node:impl x0 cmp-fn key depth))
              (cond
                [(eq? x1 node0) (values digit #f ret)]
                [node0 (values (list x0 node0 x2 x3) #f ret)]
                [subnode
                 (define-values (x0^ x1^) (ordered-map-node-mergeR x0 subnode depth))
                 (values (if x1^ (list x0^ x1^ x2 x3) (list x0^ x2 x3)) #f ret)]
                )]
             ['>
              (define-values (node0 subnode ret) (ordered-map-delete-node:impl x0 cmp-fn key depth))
              (cond
                [(eq? x0 node0) (values digit #f ret)]
                [node0 (values (list node0 x1 x2 x3) #f ret)]
                [subnode
                 (define-values (x0^ x1^) (ordered-map-node-mergeL x1 subnode depth))
                 (values (if x1^ (list x0^ x1^ x2 x3) (list x0^ x2 x3)) #f ret)]
                )]
             )]
          )]
       ) ; match: digit at depth > 0
     ]
    ) ; match: depth
  ) ; define ordered-map-delete-digit:impl

(define (left-inner-mergeR left inner subright o depth)
  (match inner
    [(ft:empty)
     (match left
       [(digit:1 x0)
       (define-values (r0 r1) (ordered-map-node-mergeR x0 subright depth))
       (if r1
           (make-ft-deep o (digit:1 r0) (ft:empty) (digit:1 r1) depth)
            (ft:single r0)
            )]
       [(digit:2 x0 x1)
        (define-values (r0 r1) (ordered-map-node-mergeR x1 subright depth))
        (make-ft-deep o (digit:1 x0) (ft:empty) (if r1 (digit:2 r0 r1) (digit:1 r0)) depth)]
       [(digit:3 x0 x1 x2)
        (define-values (r0 r1) (ordered-map-node-mergeR x2 subright depth))
        (make-ft-deep o (digit:2 x0 x1) (ft:empty) (if r1 (digit:2 r0 r1) (digit:1 r0)) depth)]
       [(digit:4 x0 x1 x2 x3)
        (define-values (r0 r1) (ordered-map-node-mergeR x3 subright depth))
        (make-ft-deep o (digit:3 x0 x1 x2) (ft:empty) (if r1 (digit:2 r0 r1) (digit:1 r0)) depth)]
       ) ; match: left
    ]
    [_
     (define inner-depth (add1 depth))
     (define-values (r inner^)
       (hdR:impl ordered-map-core inner inner-depth))
     (define-values (r0 r1) (ordered-map-node-mergeR r subright depth))
     (make-ft-deep o left inner^ (if r1 (digit:2 r0 r1) (digit:1 r0)) depth)]
    ) ; match: inner
  ) ; define left-inner-mergeR

(define (right-inner-mergeL right inner subleft depth)
  (match inner
    [(ft:empty)
     (match right
       [(digit:1 x0)
       (define-values (r0 r1) (ordered-map-node-mergeL x0 subleft depth))
       (if r1
           (make-ft-deep (ordered-map-min-key-node r0 depth) (digit:1 r0) (ft:empty) (digit:1 r1) depth)
            (ft:single r0)
            )]
       [(digit:2 x0 x1)
        (define-values (r0 r1) (ordered-map-node-mergeL x0 subleft depth))
        (make-ft-deep (ordered-map-min-key-node r0 depth) (if r1 (digit:2 r0 r1) (digit:1 r0)) (ft:empty) (digit:1 x1) depth)]
       [(digit:3 x0 x1 x2)
        (define-values (r0 r1) (ordered-map-node-mergeL x0 subleft depth))
        (make-ft-deep (ordered-map-min-key-node r0 depth) (if r1 (digit:2 r0 r1) (digit:1 r0)) (ft:empty) (digit:2 x1 x2) depth)]
       [(digit:4 x0 x1 x2 x3)
        (define-values (r0 r1) (ordered-map-node-mergeL x0 subleft depth))
        (make-ft-deep (ordered-map-min-key-node r0 depth) (if r1 (digit:2 r0 r1) (digit:1 r0)) (ft:empty) (digit:3 x1 x2 x3) depth)]
       ) ; match: right
    ]
    [_
     (define inner-depth (add1 depth))
     (define-values (l inner^)
       (hdL:impl ordered-map-core inner inner-depth))
     (define-values (r0 r1) (ordered-map-node-mergeL l subleft depth))
     (make-ft-deep (ordered-map-min-key-node r0 depth) (if r1 (digit:2 r0 r1) (digit:1 r0)) inner^ right depth)]
    ) ; match: inner
  ) ; define right-inner-mergeL

; ft, subnode, rst
(define (ordered-map-delete-ft:impl ft cmp-fn key depth)
  (match ft
    [(ft:deep (om-measure o _) left inner right)
     (define right-v (ordered-map-min-key-digit right depth))
     (match (cmp-fn right-v key)
       [(or '< '=)
        (match-define-values (right^ subright ret) (ordered-map-delete-digit:impl right cmp-fn key depth))
        (cond
          [(eq? right right^) (values ft #f ret)]
          [(not (null? right^))
           (define right^^ (list->digit right^ depth))
           (values (make-ft-deep o left inner right^^ depth) #f ret)]
          [subright
           (define ft^ (left-inner-mergeR left inner subright o depth))
           (values ft^ #f ret)]
          [(= depth 0)
           (define ft^
             (match inner
               [(ft:empty)
                (match left
                  [(digit:1 n) (ft:single n)]
                  [(digit:2 n0 n1) (make-ft-deep (ordered-map-min-key-node n0 0) (digit:1 n0) (ft:empty) (digit:1 n1) 0)]
                  [(digit:3 n0 n1 n2) (make-ft-deep (ordered-map-min-key-node n0 0) (digit:2 n0 n1) (ft:empty) (digit:1 n2) 0)]
                  [(digit:4 n0 n1 n2 n3) (make-ft-deep (ordered-map-min-key-node n0 0) (digit:2 n0 n1) (ft:empty) (digit:2 n2 n3) 0)]
                  )]
               [_
                (define-values (new-right inner^) (hdR:impl ordered-map-core inner 1))
                (define right^^
                  (match new-right
                    [(node:2 _ n0 n1) (digit:2 n0 n1)]
                    [(node:3 _ n0 n1 n2) (digit:3 n0 n1 n2)]
                    ))
                (make-ft-deep o left inner^ right^^ depth)]
               )) ; match: inner for right deletion collapse
           (values ft^ #f ret)]
          ) ; cond: right branch deletion result
        ]
       ['> (=> h)
        (match inner
          [(ft:empty) (h)]
          [_
           (define inner-depth (add1 depth))
           (define inner-v (ordered-map-min-key-ft inner inner-depth))
           (match (cmp-fn inner-v key)
             [(or '< '=)
              (match-define-values
                (inner^ subinner ret)
                (ordered-map-delete-ft:impl inner cmp-fn key inner-depth)
                )
              (cond
                [(eq? inner inner^) (values ft #f ret)]
                [inner^ (values (make-ft-deep o left inner^ right depth) #f ret)]
                [subinner
                 (define ft^
                   (match* (left right)
                     [((digit:4 x0 x1 x2 x3) (digit:4 _ _ _ _))
                      (define node0 (make-node3 (ordered-map-min-key-node x2 depth) x2 x3 subinner depth))
                      (define left^ (digit:2 x0 x1))
                      (make-ft-deep o left^ (ft:single node0) right depth)]
                     [((digit:4 _ _ _ _) _)
                      (define right^
                        (match right
                          [(digit:1 x) (digit:2 subinner x)]
                          [(digit:2 x0 x1) (digit:3 subinner x0 x1)]
                          [(digit:3 x0 x1 x2) (digit:4 subinner x0 x1 x2)]
                          ))
                      (make-ft-deep o left (ft:empty) right^ depth)]
                     [(_ _)
                      (define left^
                        (match left
                          [(digit:1 x) (digit:2 x subinner)]
                          [(digit:2 x0 x1) (digit:3 x0 x1 subinner)]
                          [(digit:3 x0 x1 x2) (digit:4 x0 x1 x2 subinner)]
                          ))
                      (make-ft-deep o left^ (ft:empty) right depth)]
                     )) ; match*: left right
                 (values ft^ #f ret)]
                ) ; cond: delete from inner
              ]
             ['> (h)]
             ) ; match: cmp-fn inner-v key
           ]
          ) ; match: inner
        ]
       ['>
        (match-define-values (left^ subleft ret) (ordered-map-delete-digit:impl left cmp-fn key depth))
        (cond
          [(eq? left left^) (values ft #f ret)]
          [(not (null? left^))
           (define left^^ (list->digit left^ depth))
           (values (make-ft-deep (ordered-map-min-key-digit left^^ depth) left^^ inner right depth) #f ret)]
          [subleft
           (define ft^ (right-inner-mergeL right inner subleft depth))
           (values ft^ #f ret)]
          [(= depth 0)
           (define ft^
             (match inner
               [(ft:empty)
                (match right
                  [(digit:1 n) (ft:single n)]
                  [(digit:2 n0 n1) (make-ft-deep (ordered-map-min-key-node n0 0) (digit:1 n0) (ft:empty) (digit:1 n1) 0)]
                  [(digit:3 n0 n1 n2) (make-ft-deep (ordered-map-min-key-node n0 0) (digit:2 n0 n1) (ft:empty) (digit:1 n2) 0)]
                  [(digit:4 n0 n1 n2 n3) (make-ft-deep (ordered-map-min-key-node n0 0) (digit:2 n0 n1) (ft:empty) (digit:2 n2 n3) 0)]
                  )]
               [_
                (define-values (new-left inner^) (hdL:impl ordered-map-core inner 1))
                (define-values (left^^ o^)
                  (match new-left
                    [(node:2 (om-measure o^ _) n0 n1) (values (digit:2 n0 n1) o^)]
                    [(node:3 (om-measure o^ _) n0 n1 n2) (values (digit:3 n0 n1 n2) o^)]
                    ))
                (make-ft-deep o^ left^^ inner^ right 0)]
               )) ; match: inner for left deletion collapse
           (values ft^ #f ret)]
          ) ; cond: left branch deletion result
        ]
       ) ; match: cmp-fn right-v key
    ]
    [(ft:single x)
     (define k (ordered-map-min-key-node x depth))
     (match depth
       [0
        (match (cmp-fn k key)
          ['= (values (ft:empty) #f x)]
          ['< (values ft #f #f)]
          )]
       [_
        (match-define-values (node0 subnode ret) (ordered-map-delete-node:impl x cmp-fn key depth))
        (cond
          [(eq? x node0) (values ft #f ret)]
          [node0 (values (ft:single node0) #f ret)]
          [subnode (values #f subnode ret)]
          )]
       ) ; match: depth for ft:single
    ]
    ) ; match: ft
  ) ; define ordered-map-delete-ft:impl

(define (ordered-map-delete-ft-wrap ft cmp-fn key)
  (match ft
    [(ft:empty) (values ft #f)]
    [(ft:single _)
     (match-define-values (ft^ _ ret) (ordered-map-delete-ft:impl ft cmp-fn key 0))
     (values ft^ ret)]
    [(ft:deep (om-measure o _) _ _ _)
     (match (cmp-fn o key)
       [(or '< '=)
        (match-define-values (ft^ _ ret) (ordered-map-delete-ft:impl ft cmp-fn key 0))
        (values ft^ ret)]
       ['> (values ft #f)]
       ) ; match: cmp-fn o key
     ]
    ) ; match: ft
  ) ; define ordered-map-delete-ft-wrap

(define (ordered-map-delete ft key)
  (match-define (ordered-map cmp-fn ft^) ft)
  (match-define-values (ft^^ ret) (ordered-map-delete-ft-wrap ft^ cmp-fn key))
  (values (if (eq? ft^ ft^^) ft (ordered-map cmp-fn ft^^)) ret)
  ) ; define ordered-map-delete

;; ========================================
;; Constructor
;; ========================================

(define (ordered-map-empty cmp-fn)
  (ordered-map cmp-fn (ft:empty))
  ) ; define ordered-map-empty

;; ----------------------------------------
;; Quick initialization (like hash)
;; ----------------------------------------
;; (make-ordered-map cmp-fn k1 v1 k2 v2 ...)

(define (make-ordered-map cmp-fn . kvs)
  (let loop ([kvs kvs]
             [om (ordered-map-empty cmp-fn)]
             )
    (match kvs
      ['() om]
      [(list k v rest ...)
       (loop rest
             (ordered-map-set om k v)
             )]
      [_ (error 'make-ordered-map "expected even number of key-value arguments")]
      ) ; match: kvs
    ) ; let loop
  ) ; define make-ordered-map

;; Macro version for compile-time checking
(require (for-syntax racket/base))
(define-syntax (ordered-map: stx)
  (syntax-case stx ()
    [(_ cmp-fn)
     #'(ordered-map-empty cmp-fn)]
    [(_ cmp-fn k v rest ...)
     #'(ordered-map-set
        (ordered-map: cmp-fn rest ...)
        k
        v)
     ]
    )) ; syntax-case

;; ========================================
;; Additional gen:dict methods
;; ========================================

;; O(1) - 直接从根节点的 measure 获取
(define (ordered-map-count om)
  (match-define (ordered-map _ ft) om)
  (ft-count ft 0))

;; ========================================
;; 序数查询 API
;; ========================================

;; O(log n) - 查询 key 的排名（比 key 小的元素数量，0-indexed）
;; 如果 key 不存在，返回 #f
(define (ordered-map-rank om key)
  (match-define (ordered-map cmp-fn ft) om)
  (ordered-map-rank-ft ft cmp-fn key 0 0))

(define (ordered-map-rank-ft ft cmp-fn key depth acc)
  (match ft
    [(ft:empty) #f]
    [(ft:single node) (ordered-map-rank-node node cmp-fn key depth acc)]
    [(ft:deep _ left inner right)
     (define inner-depth (add1 depth))
     (define right-v (ordered-map-min-key-digit right depth))
     (match (cmp-fn right-v key)
       [(or '< '=)
        (define left-count (digit-count left depth))
        (define inner-count (ft-count inner inner-depth))
        (ordered-map-rank-digit
         right
         cmp-fn
         key
         depth
         (+ acc left-count inner-count)
         )]
       ['>
        (match inner
          [(ft:empty)
           (ordered-map-rank-digit left cmp-fn key depth acc)]
          [_
           (define inner-v (ordered-map-min-key-ft inner inner-depth))
           (match (cmp-fn inner-v key)
             [(or '< '=)
              (define left-count (digit-count left depth))
              (ordered-map-rank-ft
               inner
               cmp-fn
               key
               inner-depth
               (+ acc left-count)
               )]
             ['> (ordered-map-rank-digit left cmp-fn key depth acc)]
             ) ; match: cmp-fn inner-v key
           ]
          ) ; match: inner
        ]
       ) ; match: cmp-fn right-v key
     ]
    ) ; match: ft
  ) ; define ordered-map-rank-ft

(define (ordered-map-rank-digit digit cmp-fn key depth acc)
  (match digit
    [(digit:1 x)
     (ordered-map-rank-node x cmp-fn key depth acc)]
    [(digit:2 x0 x1)
     (define k1 (ordered-map-min-key-node x1 depth))
     (match (cmp-fn k1 key)
       [(or '< '=)
        (ordered-map-rank-node x1 cmp-fn key depth
                               (+ acc
                                  (node-count x0 depth)
                                  )
                               )]
       ['> (ordered-map-rank-node x0 cmp-fn key depth acc)]
       )]
    [(digit:3 x0 x1 x2)
     (define k1 (ordered-map-min-key-node x1 depth))
     (match (cmp-fn k1 key)
       ['<
        (define k2 (ordered-map-min-key-node x2 depth))
        (match (cmp-fn k2 key)
          [(or '< '=)
           (ordered-map-rank-node x2 cmp-fn key depth
                                  (+ acc
                                     (node-count x0 depth)
                                     (node-count x1 depth)
                                     )
                                  )]
          ['>
           (ordered-map-rank-node x1 cmp-fn key depth
                                  (+ acc
                                     (node-count x0 depth)
                                     )
                                  )]
          )]
       [(or '= '>)
        (match (cmp-fn k1 key)
          ['=
           (ordered-map-rank-node x1 cmp-fn key depth
                                  (+ acc
                                     (node-count x0 depth)
                                     )
                                  )]
          ['> (ordered-map-rank-node x0 cmp-fn key depth acc)]
          )]
       )]
    [(digit:4 x0 x1 x2 x3)
     (define k1 (ordered-map-min-key-node x1 depth))
     (match (cmp-fn k1 key)
       ['<
        (define k2 (ordered-map-min-key-node x2 depth))
        (match (cmp-fn k2 key)
          ['<
           (define k3 (ordered-map-min-key-node x3 depth))
           (match (cmp-fn k3 key)
             [(or '< '=)
              (ordered-map-rank-node x3 cmp-fn key depth
                                     (+ acc
                                        (node-count x0 depth)
                                        (node-count x1 depth)
                                        (node-count x2 depth))
                                     )]
             ['>
              (ordered-map-rank-node x2 cmp-fn key depth
                                     (+ acc
                                        (node-count x0 depth)
                                        (node-count x1 depth)
                                        )
                                     )]
             )]
          [(or '= '>)
           (match (cmp-fn k2 key)
             ['=
              (ordered-map-rank-node x2 cmp-fn key depth
                                     (+ acc
                                        (node-count x0 depth)
                                        (node-count x1 depth)
                                        )
                                     )]
             ['>
              (ordered-map-rank-node x1 cmp-fn key depth
                                     (+ acc
                                        (node-count x0 depth)
                                        )
                                     )]
             )]
          )]
       [(or '= '>)
        (match (cmp-fn k1 key)
          ['=
           (ordered-map-rank-node x1 cmp-fn key depth
                                  (+ acc
                                     (node-count x0 depth)
                                     )
                                  )]
          ['> (ordered-map-rank-node x0 cmp-fn key depth acc)]
          )]
       )]
    ) ; match: digit
  ) ; define ordered-map-rank-digit

(define (ordered-map-rank-node node cmp-fn key depth acc)
  (match depth
    [0
     (match (cmp-fn (car node) key)
       ['= acc]
       [_ #f]
       )]
    [_
     (define sub-depth (sub1 depth))
     (match node
       [(node:2 _ x0 x1)
       (define k1 (ordered-map-min-key-node x1 sub-depth))
       (match (cmp-fn k1 key)
          [(or '< '=)
           (ordered-map-rank-node x1 cmp-fn key
                                  sub-depth
                                  (+ acc
                                     (node-count x0 sub-depth)
                                     )
                                  )]
          ['> (ordered-map-rank-node x0 cmp-fn key sub-depth acc)]
          )]
       [(node:3 _ x0 x1 x2)
        (define k1 (ordered-map-min-key-node x1 sub-depth))
        (match (cmp-fn k1 key)
          ['<
           (define k2 (ordered-map-min-key-node x2 sub-depth))
           (match (cmp-fn k2 key)
             [(or '< '=)
              (ordered-map-rank-node x2 cmp-fn key
                                     sub-depth
                                     (+ acc
                                        (node-count x0 sub-depth)
                                        (node-count x1 sub-depth)
                                        )
                                     )]
             ['>
              (ordered-map-rank-node x1 cmp-fn key
                                     sub-depth
                                     (+ acc
                                        (node-count x0 sub-depth)
                                        )
                                     )]
             )]
          [(or '= '>)
           (match (cmp-fn k1 key)
             ['=
              (ordered-map-rank-node x1 cmp-fn key
                                     sub-depth
                                     (+ acc
                                        (node-count x0 sub-depth)
                                        )
                                     )]
             ['> (ordered-map-rank-node x0 cmp-fn key sub-depth acc)]
             )]
          )]
       ) ; match: node
     ]
    ) ; match: depth
  ) ; define ordered-map-rank-node

;; O(log n) - 查询第 rank 小的元素（0-indexed）
;; 如果 rank 越界，返回 #f
(define (ordered-map-select om rank)
  (match-define (ordered-map _ ft) om)
  (cond
    [(< rank 0) #f]
    [(>= rank (ft-count ft 0)) #f]
    [else (ordered-map-select-ft ft rank 0)]
    ) ; cond: rank bounds
  ) ; define ordered-map-select

(define (ordered-map-select-ft ft rank depth)
  (match ft
    [(ft:single node) (ordered-map-select-node node rank depth)]
    [(ft:deep _ left inner right)
     (define inner-depth (add1 depth))
     (define left-count (digit-count left depth))
     (cond
       [(< rank left-count)
        (ordered-map-select-digit left rank depth)]
       [else
        (define inner-count (ft-count inner inner-depth))
        (define left-inner-count (+ left-count inner-count))
        (cond
          [(< rank left-inner-count)
           (ordered-map-select-ft inner (- rank left-count) inner-depth)]
          [else
           (ordered-map-select-digit right (- rank left-inner-count) depth)]
          ) ; cond: inner vs right
        ]
       ) ; cond: left vs inner/right
     ]
    ) ; match: ft
  ) ; define ordered-map-select-ft

(define (ordered-map-select-digit digit rank depth)
  (match digit
    [(digit:1 x) (ordered-map-select-node x rank depth)]
    [(digit:2 x0 x1)
     (define c0 (node-count x0 depth))
     (if (< rank c0)
         (ordered-map-select-node x0 rank depth)
         (ordered-map-select-node x1 (- rank c0) depth))
     ]
    [(digit:3 x0 x1 x2)
     (define c0 (node-count x0 depth))
     (cond
       [(< rank c0) (ordered-map-select-node x0 rank depth)]
       [else
        (define c1 (node-count x1 depth))
        (if (< rank (+ c0 c1))
            (ordered-map-select-node x1 (- rank c0) depth)
            (ordered-map-select-node x2 (- rank c0 c1) depth))
        ]
       )]
    [(digit:4 x0 x1 x2 x3)
     (define c0 (node-count x0 depth))
     (cond
       [(< rank c0) (ordered-map-select-node x0 rank depth)]
       [else
        (define c1 (node-count x1 depth))
        (cond
          [(< rank (+ c0 c1)) (ordered-map-select-node x1 (- rank c0) depth)]
          [else
           (define c2 (node-count x2 depth))
           (if (< rank (+ c0 c1 c2))
               (ordered-map-select-node x2 (- rank c0 c1) depth)
               (ordered-map-select-node x3 (- rank c0 c1 c2) depth))
           ]
          )]
       )]
    ) ; match: digit
  ) ; define ordered-map-select-digit

(define (ordered-map-select-node node rank depth)
  (match depth
    [0 node]
    [_
     (define sub-depth (sub1 depth))
     (match node
       [(node:2 _ x0 x1)
        (define c0 (node-count x0 sub-depth))
        (if (< rank c0)
            (ordered-map-select-node x0 rank sub-depth)
            (ordered-map-select-node x1 (- rank c0) sub-depth)
            )
        ]
       [(node:3 _ x0 x1 x2)
        (define c0 (node-count x0 sub-depth))
        (cond
          [(< rank c0) (ordered-map-select-node x0 rank sub-depth)]
          [else
           (define c1 (node-count x1 sub-depth))
           (if (< rank (+ c0 c1))
               (ordered-map-select-node x1 (- rank c0) sub-depth)
               (ordered-map-select-node x2 (- rank c0 c1) sub-depth)
               )
           ]
          )]
       ) ; match: node
     ]
    ) ; match: depth
  ) ; define ordered-map-select-node

;; O(log n) - 返回小于 key 的元素数量
(define (ordered-map-count-less-than om key)
  (match-define (ordered-map cmp-fn ft) om)
  (ordered-map-count-less-than-ft ft cmp-fn key 0))

(define (ordered-map-count-less-than-ft ft cmp-fn key depth)
  (match ft
    [(ft:empty) 0]
    [(ft:single node) (ordered-map-count-less-than-node node cmp-fn key depth)]
    [(ft:deep _ left inner right)
     (define inner-depth (add1 depth))
     (define right-v (ordered-map-min-key-digit right depth))
     (match (cmp-fn right-v key)
       ['<
        (define left-count (digit-count left depth))
        (define inner-count (ft-count inner inner-depth))
        (+ left-count
           inner-count
           (ordered-map-count-less-than-digit right cmp-fn key depth)
           )]
       [(or '= '>)
        (match inner
          [(ft:empty)
           (ordered-map-count-less-than-digit left cmp-fn key depth)]
          [_
           (define inner-v (ordered-map-min-key-ft inner inner-depth))
           (match (cmp-fn inner-v key)
             ['<
              (define left-count (digit-count left depth))
              (+ left-count
                 (ordered-map-count-less-than-ft inner cmp-fn key inner-depth)
                 )]
             [(or '= '>)
              (ordered-map-count-less-than-digit left cmp-fn key depth)]
             )]
          )]
       )]
    ) ; match: ft
  ) ; define ordered-map-count-less-than-ft

(define (ordered-map-count-less-than-digit digit cmp-fn key depth)
  (match digit
    [(digit:1 x) (ordered-map-count-less-than-node x cmp-fn key depth)]
    [(digit:2 x0 x1)
     (define k1 (ordered-map-min-key-node x1 depth))
     (match (cmp-fn k1 key)
       ['<
        (+ (node-count x0 depth)
           (ordered-map-count-less-than-node x1 cmp-fn key depth)
           )]
       [(or '= '>) (ordered-map-count-less-than-node x0 cmp-fn key depth)]
       )]
    [(digit:3 x0 x1 x2)
     (define k1 (ordered-map-min-key-node x1 depth))
     (match (cmp-fn k1 key)
       ['<
        (define k2 (ordered-map-min-key-node x2 depth))
        (match (cmp-fn k2 key)
          ['<
           (+ (node-count x0 depth)
              (node-count x1 depth)
              (ordered-map-count-less-than-node x2 cmp-fn key depth)
              )]
          [(or '= '>)
           (+ (node-count x0 depth)
              (ordered-map-count-less-than-node x1 cmp-fn key depth)
              )]
          )]
       [(or '= '>) (ordered-map-count-less-than-node x0 cmp-fn key depth)]
       )]
    [(digit:4 x0 x1 x2 x3)
     (define k1 (ordered-map-min-key-node x1 depth))
     (match (cmp-fn k1 key)
       ['<
        (define k2 (ordered-map-min-key-node x2 depth))
        (match (cmp-fn k2 key)
          ['<
           (define k3 (ordered-map-min-key-node x3 depth))
           (match (cmp-fn k3 key)
             ['<
              (+ (node-count x0 depth) (node-count x1 depth) (node-count x2 depth)
                 (ordered-map-count-less-than-node x3 cmp-fn key depth)
                 )]
             [(or '= '>)
              (+ (node-count x0 depth) (node-count x1 depth)
                 (ordered-map-count-less-than-node x2 cmp-fn key depth)
                 )]
             )]
          [(or '= '>)
           (+ (node-count x0 depth)
              (ordered-map-count-less-than-node x1 cmp-fn key depth)
              )]
          )]
       [(or '= '>) (ordered-map-count-less-than-node x0 cmp-fn key depth)]
       )]
    ) ; match: digit
  ) ; define ordered-map-count-less-than-digit

(define (ordered-map-count-less-than-node node cmp-fn key depth)
  (match depth
    [0
     (match (cmp-fn (car node) key)
       ['< 1]
       [_ 0]
       )]
    [_
     (define sub-depth (sub1 depth))
     (match node
       [(node:2 _ x0 x1)
        (define k1 (ordered-map-min-key-node x1 sub-depth))
        (match (cmp-fn k1 key)
          ['<
           (+ (node-count x0 sub-depth)
              (ordered-map-count-less-than-node x1 cmp-fn key sub-depth)
              )]
          [(or '= '>)
           (ordered-map-count-less-than-node x0 cmp-fn key sub-depth)]
          )]
       [(node:3 _ x0 x1 x2)
        (define k1 (ordered-map-min-key-node x1 sub-depth))
        (match (cmp-fn k1 key)
          ['<
           (define k2 (ordered-map-min-key-node x2 sub-depth))
           (match (cmp-fn k2 key)
             ['<
              (+ (node-count x0 sub-depth)
                 (node-count x1 sub-depth)
                 (ordered-map-count-less-than-node x2 cmp-fn key sub-depth)
                 )]
             [(or '= '>)
              (+ (node-count x0 sub-depth)
                 (ordered-map-count-less-than-node x1 cmp-fn key sub-depth)
                 )]
             )]
          [(or '= '>)
           (ordered-map-count-less-than-node x0 cmp-fn key sub-depth)]
          )]
       ) ; match: node
     ]
    ) ; match: depth
  ) ; define ordered-map-count-less-than-node

(define (ordered-map-has-key? om key)
  (if (ordered-map-query om key) #t #f))

(define (ordered-map-keys om)
  (for/list ([kv (in-ordered-map om)])
    (car kv))
  ) ; define ordered-map-keys

(define (ordered-map-values om)
  (for/list ([kv (in-ordered-map om)])
    (cdr kv))
  ) ; define ordered-map-values

;; ========================================
;; Sequence support
;; ========================================

(require racket/sequence racket/generator)

;; Original lazy implementation using query-weak (renamed)
(define (in-ordered-map/lazy om)
  (make-do-sequence
    (lambda ()
      (initiate-sequence
        #:init-pos (ordered-map-min om)
        #:next-pos (lambda (pos) (if pos (ordered-map-query-weak om (car pos) '>) #f))
        #:pos->element (lambda (pos) pos)
        #:continue-with-pos? (lambda (pos) (if pos #t #f))
        ) ; initiate-sequence
      ) ; lambda
    ) ; make-do-sequence
  ) ; define in-ordered-map/lazy

;; Generator-based ascending traversal (more efficient)
(define (in-ordered-map om)
  (in-generator
    (define (yield-node node depth)
      (match depth
        [0 (yield node)]
        [_
         (define sub-depth (sub1 depth))
         (match node
           [(node:2 _ x0 x1)
            (yield-node x0 sub-depth)
            (yield-node x1 sub-depth)]
           [(node:3 _ x0 x1 x2)
            (yield-node x0 sub-depth)
            (yield-node x1 sub-depth)
            (yield-node x2 sub-depth)]
           ) ; match: node
         ]
        ) ; match: depth
      ) ; define yield-node
    (define (yield-digit digit depth)
      (match digit
        [(digit:1 x0) (yield-node x0 depth)]
        [(digit:2 x0 x1) (yield-node x0 depth) (yield-node x1 depth)]
        [(digit:3 x0 x1 x2) (yield-node x0 depth) (yield-node x1 depth) (yield-node x2 depth)]
        [(digit:4 x0 x1 x2 x3) (yield-node x0 depth) (yield-node x1 depth) (yield-node x2 depth) (yield-node x3 depth)]
        ) ; match: digit
      ) ; define yield-digit
    (define (yield-ft ft depth)
      (match ft
        [(ft:empty) (void)]
        [(ft:single node) (yield-node node depth)]
        [(ft:deep _ left inner right)
         (yield-digit left depth)
         (yield-ft inner (add1 depth))
         (yield-digit right depth)]
        ) ; match: ft
      ) ; define yield-ft
    (match-define (ordered-map _ ft) om)
    (yield-ft ft 0)
    ) ; in-generator
  ) ; define in-ordered-map

;; Generator-based descending traversal
(define (in-ordered-map-reverse om)
  (in-generator
    (define (yield-node node depth)
      (match depth
        [0 (yield node)]
        [_
         (define sub-depth (sub1 depth))
         (match node
           [(node:2 _ x0 x1)
            (yield-node x1 sub-depth)
            (yield-node x0 sub-depth)]
           [(node:3 _ x0 x1 x2)
            (yield-node x2 sub-depth)
            (yield-node x1 sub-depth)
            (yield-node x0 sub-depth)]
           ) ; match: node
         ]
        ) ; match: depth
      ) ; define yield-node
    (define (yield-digit digit depth)
      (match digit
        [(digit:1 x0) (yield-node x0 depth)]
        [(digit:2 x0 x1) (yield-node x1 depth) (yield-node x0 depth)]
        [(digit:3 x0 x1 x2) (yield-node x2 depth) (yield-node x1 depth) (yield-node x0 depth)]
        [(digit:4 x0 x1 x2 x3) (yield-node x3 depth) (yield-node x2 depth) (yield-node x1 depth) (yield-node x0 depth)]
        ) ; match: digit
      ) ; define yield-digit
    (define (yield-ft ft depth)
      (match ft
        [(ft:empty) (void)]
        [(ft:single node) (yield-node node depth)]
        [(ft:deep _ left inner right)
         (yield-digit right depth)
         (yield-ft inner (add1 depth))
         (yield-digit left depth)]
        ) ; match: ft
      ) ; define yield-ft
    (match-define (ordered-map _ ft) om)
    (yield-ft ft 0)
    ) ; in-generator
  ) ; define in-ordered-map-reverse

;; ========================================
;; Key/Value only sequences (like in-dict-keys/values)
;; ========================================

(define (in-ordered-map-keys om)
  (in-generator
    (for ([kv (in-ordered-map om)])
      (define key (car kv))
      (yield key))
    ) ; in-generator
  ) ; define in-ordered-map-keys

(define (in-ordered-map-values om)
  (in-generator
    (for ([kv (in-ordered-map om)])
      (define val (cdr kv))
      (yield val))
    ) ; in-generator
  ) ; define in-ordered-map-values

;; ========================================
;; for/ordered-map comprehension
;; ========================================

(require (for-syntax racket/base))

(define-syntax (for/ordered-map stx)
  (syntax-case stx ()
    [(_ cmp-fn clauses body ...)
      #'(for/fold ([m
                    (ordered-map-empty cmp-fn)]
                   )
            clauses
          (let ([kv
                 (let ()
                   body ...
                   )
                 ])
            (ordered-map-insert m (car kv) (cdr kv) #t)
            )
          )]
    ) ; syntax-case
  ) ; define-syntax for/ordered-map

(define-syntax (for*/ordered-map stx)
  (syntax-case stx ()
    [(_ cmp-fn clauses body ...)
      #'(for*/fold ([m
                     (ordered-map-empty cmp-fn)]
                    )
            clauses
          (let ([kv
                 (let ()
                   body ...
                   )
                 ])
            (ordered-map-insert m (car kv) (cdr kv) #t)
            )
          )]
    ) ; syntax-case
  ) ; define-syntax for*/ordered-map

;; ========================================
;; Match expander for ordered-map
;; ========================================

(require racket/match)

;; Match empty ordered-map
(define-match-expander ordered-map-empty-pat
  (lambda (stx)
    (syntax-case stx ()
      [(_) #'(? ordered-map-empty?)]
      ) ; syntax-case
    ) ; lambda
  ) ; define-match-expander ordered-map-empty-pat

;; Match and extract entries as list: (ordered-map-pairs pairs-pat)
(define-match-expander ordered-map-pairs
  (lambda (stx)
    (syntax-case stx ()
      [(_ pairs-pat)
       #'(? ordered-map?
            (app (lambda (om) (for/list ([kv (in-ordered-map om)]) kv))
                 pairs-pat)
            )]
      ) ; syntax-case
    ) ; lambda
  ) ; define-match-expander ordered-map-pairs

;; ----------------------------------------
;; Key-based extraction pattern
;; ----------------------------------------
;; (ordered-map* [key-expr val-pat] ...)           - all keys must exist
;; (ordered-map* [key-expr val-pat default] ...)   - use default if missing
;; Can mix both forms in one pattern

(require (for-syntax racket/list))

(define-for-syntax (parse-binding stx binding)
  ;; Returns: (values key-expr val-pat has-default? default-expr)
  (syntax-case binding ()
    [[key-expr val-pat default-expr]
     (values #'key-expr #'val-pat #t #'default-expr)]
    [[key-expr val-pat]
     (values #'key-expr #'val-pat #f #f)]
    [_
     (raise-syntax-error
      'ordered-map*
      "expected [key val-pat] or [key val-pat default]"
      stx
      binding)]
    ) ; syntax-case
  ) ; define-for-syntax parse-binding

(define-for-syntax (build-query-expr key has-default? default-expr)
  (if has-default?
      #`(match (ordered-map-query om #,key)
          [#f #,default-expr]
          [(cons _ v) v])
      #`(ordered-map-query om #,key))
  ) ; define-for-syntax build-query-expr

(define-for-syntax (build-pat-expr pat has-default?)
  (if has-default?
      pat
      #`(cons _ #,pat))
  ) ; define-for-syntax build-pat-expr

(define-match-expander ordered-map*
  (lambda (stx)
    (syntax-case stx ()
      [(_ binding ...)
       (let ()
         (define bindings
           (syntax->list
            #'(binding ...)
            ))
         (define parsed
           (for/list ([b bindings])
             (define-values (k p h? d) (parse-binding stx b))
             (list k p h? d)
             ))
         (with-syntax ([(query-expr ...)
                        (for/list ([p parsed])
                          (build-query-expr (first p) (third p) (fourth p))
                          )]
                       [(pat-expr ...)
                        (for/list ([p parsed])
                          (build-pat-expr (second p) (third p))
                          )
                        ])
            #'(? ordered-map?
               (app (lambda (om) (list query-expr ...))
                    (list pat-expr ...))
               )
            )
         )
       ]
      ) ; syntax-case
    ) ; lambda
  ) ; define-match-expander ordered-map*

;; ========================================
;; Ref and Set (dict-style)
;; ========================================

(define (ordered-map-ref om key
                         [default
                          (lambda ()
                            (error "key not found" key))
                          ])
  (match (ordered-map-query om key)
    [#f (if (procedure? default) (default) default)]
    [(cons _ v) v]
    ) ; match: ordered-map-query
  ) ; define ordered-map-ref

(define (ordered-map-set om key val)
  (ordered-map-insert om key val #t))

;; ========================================
;; Exports
;; ========================================

(provide ordered-map-size-changed?)
(provide (struct-out ordered-map))
(provide ordered-map-empty? ordered-map-min ordered-map-max)
(provide ordered-map-query ordered-map-query-weak)
(provide ordered-map-delete ordered-map-insert)
(provide ordered-map-empty make-ordered-map ordered-map:)
(provide ordered-map-ref ordered-map-set)
(provide ordered-map-count ordered-map-has-key? ordered-map-keys ordered-map-values)
;; 序数查询 API
(provide ordered-map-rank ordered-map-select ordered-map-count-less-than)
(provide (struct-out om-measure))
(provide in-ordered-map in-ordered-map-reverse in-ordered-map/lazy)
(provide in-ordered-map-keys in-ordered-map-values)
;; Comprehensions
(provide for/ordered-map for*/ordered-map)
;; Match expanders
(provide ordered-map-empty-pat ordered-map-pairs)
(provide ordered-map*)

;; ========================================
;; Weak Query Implementation
;; ========================================

(define (ordered-map-query-weak-node:impl node cmp-fn key mode depth)
  (match depth
    [0
     (define cmp-rst (cmp-fn (car node) key))
     (match* (cmp-rst mode)
       [('= (or '>= '<=)) node]
       [('< (or '< '<=)) node]
       [('> (or '> '>=)) node]
       [(_ _) #f]
       ) ; match*: cmp-rst mode
     ]
    [_
     (define sub-depth (sub1 depth))
     (match node
       [(node:2 _ x0 x1)
        (define x1-key
          (ordered-map-min-key-node x1 sub-depth))
        (define x1-cmp-rst (cmp-fn x1-key key))
        (match* (x1-cmp-rst mode)
          [('= (or '>= '<= '>))
           (ordered-map-query-weak-node:impl x1 cmp-fn key mode sub-depth)]
          [('< _)
           (ordered-map-query-weak-node:impl x1 cmp-fn key mode sub-depth)]
          [(_ (or '< '<=))
           (ordered-map-query-weak-node:impl x0 cmp-fn key mode sub-depth)]
          [(_ _)
           (define tmp
             (ordered-map-query-weak-node:impl x0 cmp-fn key mode sub-depth))
           (if tmp
               tmp
               (ordered-map-query-weak-node:impl x1 cmp-fn key mode sub-depth)
               )]
          ) ; match*: x1-cmp-rst mode
        ]
       [(node:3 _ x0 x1 x2)
        (define x2-key
          (ordered-map-min-key-node x2 sub-depth))
        (define x2-cmp-rst (cmp-fn x2-key key))
        (match* (x2-cmp-rst mode)
          [('= (or '>= '<= '>))
           (ordered-map-query-weak-node:impl x2 cmp-fn key mode sub-depth)]
          [('< _)
           (ordered-map-query-weak-node:impl x2 cmp-fn key mode sub-depth)]
          [(_ _)
           (define x1-key
             (ordered-map-min-key-node x1 sub-depth))
           (define x1-cmp-rst (cmp-fn x1-key key))
           (match* (x1-cmp-rst mode)
             [('= (or '>= '<=))
              (ordered-map-query-weak-node:impl x1 cmp-fn key mode sub-depth)]
             [('= '>)
              (define tmp
                (ordered-map-query-weak-node:impl x1 cmp-fn key mode sub-depth))
              (if tmp
                  tmp
                  (ordered-map-query-weak-node:impl x2 cmp-fn key mode sub-depth)
                  )]
             [('< (or '<= '<))
              (ordered-map-query-weak-node:impl x1 cmp-fn key mode sub-depth)]
             [('< (or '>= '>))
              (define tmp
                (ordered-map-query-weak-node:impl x1 cmp-fn key mode sub-depth))
              (if tmp
                  tmp
                  (ordered-map-query-weak-node:impl x2 cmp-fn key mode sub-depth)
                  )]
             [('= '<)
              (ordered-map-query-weak-node:impl x0 cmp-fn key mode sub-depth)]
             [('> (or '<= '<))
              (ordered-map-query-weak-node:impl x0 cmp-fn key mode sub-depth)]
             [('> (or '>= '>))
              (define tmp
                (ordered-map-query-weak-node:impl x0 cmp-fn key mode sub-depth))
              (if tmp
                  tmp
                  (ordered-map-query-weak-node:impl x1 cmp-fn key mode sub-depth)
                  )]
             ) ; match*: x1-cmp-rst mode
           ]
          ) ; match*: x2-cmp-rst mode
        ]
       ) ; match: node
     ]
    ) ; match: depth
  ) ; define ordered-map-query-weak-node:impl

(define (ordered-map-query-weak-ft:impl ft cmp-fn key mode depth)
  (match ft
    [(ft:empty) #f]
    [(ft:single node) (ordered-map-query-weak-node:impl node cmp-fn key mode depth)]
    [(ft:deep _ left inner right)
     (define inner-depth (add1 depth))
     (define right-v (ordered-map-min-key-digit right depth))
     (define right-v-cmp-rst (cmp-fn right-v key))
     (match* (right-v-cmp-rst mode)
       [('= (or '<= '>= '>)) (ordered-map-query-weak-digit:impl right cmp-fn key mode depth)]
       [('< _) (ordered-map-query-weak-digit:impl right cmp-fn key mode depth)]
       [(_ _)
       (match inner
          [(ft:empty)
           (match mode
             [(or '< '<=)
              (ordered-map-query-weak-digit:impl left cmp-fn key mode depth)]
             [_
              (define tmp
                (ordered-map-query-weak-digit:impl left cmp-fn key mode depth))
              (if tmp
                  tmp
                  (ordered-map-query-weak-digit:impl right cmp-fn key mode depth)
                  )]
             ) ; match: mode
           ]
          [_
           (define inner-v
             (ordered-map-min-key-ft inner inner-depth))
           (define inner-v-cmp-rst (cmp-fn inner-v key))
           (match* (inner-v-cmp-rst mode)
             [('= (or '<= '>= '>))
              (ordered-map-query-weak-ft:impl inner cmp-fn key mode inner-depth)]
             [('< (or '>= '>))
              (define tmp
                (ordered-map-query-weak-ft:impl inner cmp-fn key mode inner-depth))
              (if tmp
                  tmp
                  (ordered-map-query-weak-digit:impl right cmp-fn key mode depth)
                  )]
             [('< _)
              (ordered-map-query-weak-ft:impl inner cmp-fn key mode inner-depth)]
             [(_ (or '<= '<))
              (ordered-map-query-weak-digit:impl left cmp-fn key mode depth)]
             [(_ _)
              (define tmp
                (ordered-map-query-weak-digit:impl left cmp-fn key mode depth))
              (if tmp
                  tmp
                  (ordered-map-query-weak-ft:impl inner cmp-fn key mode inner-depth)
                  )]
             ) ; match*: inner-v-cmp-rst mode
           ]
          ) ; match: inner
        ]
       ) ; match*: right-v-cmp-rst mode
     ]
    ) ; match: ft
  ) ; define ordered-map-query-weak-ft:impl

(define (ordered-map-query-weak-digit:impl digit cmp-fn key mode depth)
  (match digit
    [(digit:1 x0)
     (ordered-map-query-weak-node:impl x0 cmp-fn key mode depth)]
    [(digit:2 x0 x1)
     (define x1-v (ordered-map-min-key-node x1 depth))
     (match* ((cmp-fn x1-v key) mode)
       [('= (or '<= '>= '>)) (ordered-map-query-weak-node:impl x1 cmp-fn key mode depth)]
       [('< _) (ordered-map-query-weak-node:impl x1 cmp-fn key mode depth)]
       [(_ (or '< '<=)) (ordered-map-query-weak-node:impl x0 cmp-fn key mode depth)]
       [(_ _)
        (define tmp
          (ordered-map-query-weak-node:impl x0 cmp-fn key mode depth))
        (if tmp
            tmp
            (ordered-map-query-weak-node:impl x1 cmp-fn key mode depth)
            )]
       ) ; match*: cmp-fn x1-v key / mode
     ]
    [(digit:3 x0 x1 x2)
     (define x1-v (ordered-map-min-key-node x1 depth))
     (match* ((cmp-fn x1-v key) mode)
       [('= (or '<= '>=)) (ordered-map-query-weak-node:impl x1 cmp-fn key mode depth)]
       [('= '>)
        (define tmp
          (ordered-map-query-weak-node:impl x1 cmp-fn key mode depth))
        (if tmp
            tmp
            (ordered-map-query-weak-node:impl x2 cmp-fn key mode depth)
            )]
       [('< _)
        (define x2-v (ordered-map-min-key-node x2 depth))
        (match* ((cmp-fn x2-v key) mode)
          [('= (or '<= '>= '>)) (ordered-map-query-weak-node:impl x2 cmp-fn key mode depth)]
          [('< _) (ordered-map-query-weak-node:impl x2 cmp-fn key mode depth)]
          [(_ (or '<= '<)) (ordered-map-query-weak-node:impl x1 cmp-fn key mode depth)]
          [(_ _)
           (define tmp
             (ordered-map-query-weak-node:impl x1 cmp-fn key mode depth))
           (if tmp
               tmp
               (ordered-map-query-weak-node:impl x2 cmp-fn key mode depth)
               )]
          ) ; match*: cmp-fn x2-v key / mode
        ]
       [(_ (or '< '<=))
        (ordered-map-query-weak-node:impl x0 cmp-fn key mode depth)]
       [(_ _)
        (define tmp
          (ordered-map-query-weak-node:impl x0 cmp-fn key mode depth))
        (if tmp
            tmp
            (ordered-map-query-weak-node:impl x1 cmp-fn key mode depth)
            )]
       ) ; match*: cmp-fn x1-v key / mode
     ]
    [(digit:4 x0 x1 x2 x3)
     (define x2-v (ordered-map-min-key-node x2 depth))
     (match* ((cmp-fn x2-v key) mode)
       [('= (or '<= '>=)) (ordered-map-query-weak-node:impl x2 cmp-fn key mode depth)]
       [('= '>)
        (define tmp
          (ordered-map-query-weak-node:impl x2 cmp-fn key mode depth))
        (if tmp
            tmp
            (ordered-map-query-weak-node:impl x3 cmp-fn key mode depth)
            )]
       [('< _)
        (define x3-v (ordered-map-min-key-node x3 depth))
        (match* ((cmp-fn x3-v key) mode)
          [('= (or '<= '>= '>)) (ordered-map-query-weak-node:impl x3 cmp-fn key mode depth)]
          [('< _) (ordered-map-query-weak-node:impl x3 cmp-fn key mode depth)]
          [(_ (or '<= '<)) (ordered-map-query-weak-node:impl x2 cmp-fn key mode depth)]
          [(_ _)
           (define tmp
             (ordered-map-query-weak-node:impl x2 cmp-fn key mode depth))
           (if tmp
               tmp
               (ordered-map-query-weak-node:impl x3 cmp-fn key mode depth)
               )]
          ) ; match*: cmp-fn x3-v key / mode
        ]
       [(_ (or '< '<=))
        (define x1-v (ordered-map-min-key-node x1 depth))
        (match* ((cmp-fn x1-v key) mode)
          [('= (or '<= '>= '>)) (ordered-map-query-weak-node:impl x1 cmp-fn key mode depth)]
          [('< _) (ordered-map-query-weak-node:impl x1 cmp-fn key mode depth)]
          [(_ (or '< '<=)) (ordered-map-query-weak-node:impl x0 cmp-fn key mode depth)]
          ) ; match*: cmp-fn x1-v key / mode
        ]
       [(_ _)
        (define x1-v (ordered-map-min-key-node x1 depth))
        (match* ((cmp-fn x1-v key) mode)
          [('= (or '<= '>=)) (ordered-map-query-weak-node:impl x1 cmp-fn key mode depth)]
          [('= '>)
           (define tmp
             (ordered-map-query-weak-node:impl x1 cmp-fn key mode depth))
           (if tmp
               tmp
               (ordered-map-query-weak-node:impl x2 cmp-fn key mode depth)
               )]
          [('< _)
           (define tmp
             (ordered-map-query-weak-node:impl x1 cmp-fn key mode depth))
           (if tmp
               tmp
               (ordered-map-query-weak-node:impl x2 cmp-fn key mode depth)
               )]
          [(_ (or '< '<=)) (assert-unreachable)]
          [(_ _)
           (define tmp
             (ordered-map-query-weak-node:impl x0 cmp-fn key mode depth))
           (if tmp
               tmp
               (ordered-map-query-weak-node:impl x1 cmp-fn key mode depth)
               )]
          ) ; match*: cmp-fn x1-v key / mode
        ]
       ) ; match*: cmp-fn x2-v key / mode
     ]
    ) ; match: digit
  ) ; define ordered-map-query-weak-digit:impl

(define (ordered-map-query-weak om key mode)
  (match-define (ordered-map cmp-fn ft^) om)
  (ordered-map-query-weak-ft:impl ft^ cmp-fn key mode 0)
  ) ; define ordered-map-query-weak
