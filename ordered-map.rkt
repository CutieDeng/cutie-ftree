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
      [default (lambda () (error "key not found" key))])
      (match (ordered-map-query dict key) [#f (if (procedure? default) (default) default)] [(cons _ x) x]))
    (define (dict-set dict key val)
      (ordered-map-insert dict key val #t)
    )
    (define (dict-remove dict key)
      (match-define-values (r _) (ordered-map-delete dict key)) r)
    (define (dict-iterate-first dict)
      (ordered-map-max dict))
    (define (dict-iterate-next dict pos)
      (ordered-map-query-weak dict (car pos) '<))
    (define (dict-iterate-key dict k) (car k))
    (define (dict-iterate-value dict k) (cdr k))
  ]
)

(define ordered-map-core (ft:config 
  (lambda () #f) (match-lambda [(cons k _) k]) (lambda (k0 k1) k0)
))

(define (ordered-map-empty? ordl)
  (match-define (ordered-map _ f) ordl)
  (match f [(ft:empty) #t] [_ #f])
)

(define (ordered-map-min o)
  (match-define (ordered-map _ f) o)
  (match f
    [(ft:empty) #f]
    [_ (hdL-view f)]
  )
)

(define (ordered-map-max o)
  (match-define (ordered-map _ f) o)
  (match f
    [(ft:empty) #f]
    [_ (hdR-view f)]
  )
)

(define (ordered-map-min-key o)
  (match-define (ordered-map _ f) o)
  (match f
    [(ft:single (cons k _)) k]
    [(ft:deep k _ _ _) k]
  )
)

(define (ordered-map-min-key-node node depth)
  (match depth
    [0 (car node)]
    [_ (match node
      [(or (node:2 k _ _) (node:3 k _ _ _)) k]
    )]
  )
)

(define (ordered-map-min-key-ft ft depth)
  (match ft
    [(ft:single v) (ordered-map-min-key-node v depth)]
    [(ft:deep k _ _ _) k]
  )
)

(define ordered-map-size-changed? (make-parameter #f))

(define (ordered-map-min-key-digit digit depth)
  (match digit
    [(or (digit:1 x) (digit:2 x _) (digit:3 x _ _) (digit:4 x _ _ _)) (ordered-map-min-key-node x depth)]
  )
)

(define (ordered-map-query-node:impl node cmp-fn key depth)
  (match depth
    [0
      (define cmp-rst (cmp-fn (car node) key))
      (match cmp-rst
        ['= node]
        [(or '< '>) #f]
      )
    ]
    [_
      (match node
        [(node:2 _ x0 x1)
          (define x1-key (ordered-map-min-key-node x1 (sub1 depth)))
          (define x1-cmp-rst (cmp-fn x1-key key))
          (match x1-cmp-rst
            [(or '= '<) (ordered-map-query-node:impl x1 cmp-fn key (sub1 depth))]
            ['> (ordered-map-query-node:impl x0 cmp-fn key (sub1 depth))]
          )
        ]
        [(node:3 _ x0 x1 x2)
          (define x2-key (ordered-map-min-key-node x2 (sub1 depth)))
          (define x2-cmp-rst (cmp-fn x2-key key))
          (match x2-cmp-rst
            [(or '= '<) (ordered-map-query-node:impl x2 cmp-fn key (sub1 depth))]
            ['>
              (define x1-key (ordered-map-min-key-node x1 (sub1 depth)))
              (define x1-cmp-rst (cmp-fn x1-key key))
              (match x1-cmp-rst
                [(or '= '<) (ordered-map-query-node:impl x1 cmp-fn key (sub1 depth))]
                ['> (ordered-map-query-node:impl x0 cmp-fn key (sub1 depth))]
              )
            ]
          )
        ]
      )
    ]
  )
)

(define (ordered-map-query-ft:impl ft cmp-fn key depth)
  (match ft
    [(ft:empty) #f]
    [(ft:single node) (ordered-map-query-node:impl node cmp-fn key depth)]
    [(ft:deep _ left inner right)
      (define right-v (ordered-map-min-key-digit right depth))
      (define right-v-cmp-rst (cmp-fn right-v key))
      (match right-v-cmp-rst
        [(or '= '<) (ordered-map-query-digit:impl right cmp-fn key depth)]
        ['> (=> f)
          (match inner [(ft:empty) (f)] [_ (void)])
          (define inner-v (ordered-map-min-key-ft inner (add1 depth)))
          (define inner-v-cmp-rst (cmp-fn inner-v key))
          (match inner-v-cmp-rst
            [(or '= '<) (ordered-map-query-ft:impl inner cmp-fn key (add1 depth))]
            ['> (f)]
          )
        ]
        ['> (ordered-map-query-digit:impl left cmp-fn key depth)]
      )
    ]
  )
)

(define (ordered-map-query-digit:impl digit cmp-fn key depth)
  (define l (reverse (digit-add-list digit '())))
  (let loop0 ([l l])
    (match l 
      [(cons lh l*)
        (define v (ordered-map-min-key-node lh depth))
        (define v-cmp-rst (cmp-fn v key))
        (match v-cmp-rst
          [(or '= '<) (ordered-map-query-node:impl lh cmp-fn key depth)]
          ['> (loop0 l*)]
        )
      ]
      ['() #f]
    )
  )
)

(define (ordered-map-query o k)
  (match-define (ordered-map cmp-fn ft) o)
  (ordered-map-query-ft:impl ft cmp-fn k 0)
)

; return node, #f / node, node2
; never in depth 0
(define (ordered-map-insert-node:impl node cmp-fn key value depth replace?)
  (match depth
    [1 (match node
      [(node:2 _ (and x0 (cons k0 _)) (and x1 (cons k1 _)))
        (define k1-cmp-rst (cmp-fn k1 key))
        (match k1-cmp-rst
          ['= (if replace? (values (node:2 k0 x0 (cons key value)) #f) (values node #f))]
          ['< (ordered-map-size-changed? #t) (values (node:3 k0 x0 x1 (cons key value)) #f)]
          ['> (define k0-cmp-rst (cmp-fn k0 key))
            (match k0-cmp-rst
              ['= (if replace? (values (node:2 key (cons key value) x1) #f) (values node #f))]
              ['< (ordered-map-size-changed? #t) (values (node:3 k0 x0 (cons key value) x1) #f)]
              ['> (ordered-map-size-changed? #t) (values (node:3 key (cons key value) x0 x1) #f)]
            )
          ]
        )
      ]
      [(node:3 _ (and x0 (cons k0 _)) (and x1 (cons k1 _)) (and x2 (cons k2 _)))
        (define k1-cmp-rst (cmp-fn k1 key))
        (match k1-cmp-rst
          ['= (if replace? (values (node:3 k0 x0 (cons key value) x2) #f) (values node #f))]
          ['< (define k2-cmp-rst (cmp-fn k2 key))
            (match k2-cmp-rst
              ['= (if replace?
                (values (node:3 k0 x0 x1 (cons key value)) #f)
                (values node #f))]
              ['< (ordered-map-size-changed? #t) (values (node:2 k0 x0 x1) (node:2 k2 x2 (cons key value)))]
              ['> (ordered-map-size-changed? #t) (values (node:2 k0 x0 x1) (node:2 key (cons key value) x2))]
            )
          ]
          ['> (define k0-cmp-rst (cmp-fn k0 key))
            (match k0-cmp-rst
              ['= (if replace? 
                (values (node:3 key (cons key value) x1 x2) #f)
                (values node #f))]
              ['< (ordered-map-size-changed? #t) (values (node:2 k0 x0 (cons key value)) (node:2 k1 x1 x2))]
              ['> (ordered-map-size-changed? #t) (values (node:2 key (cons key value) x0) (node:2 k1 x1 x2))]
            )
          ]
        )
      ]
    )]
    [_ (match node
      [(node:2 k0 x0 x1)
        (define k1 (ordered-map-min-key-node x1 (sub1 depth)))
        (match (cmp-fn k1 key)
          [(or '= '<) (define-values (node0 node1)
            (ordered-map-insert-node:impl x1 cmp-fn key value (sub1 depth) replace?))
            (cond
              [(and (eq? x1 node0) (not node1)) (values node #f)]
              [node1 (values (node:3 k0 x0 node0 node1) #f)]
              [(not node1) (values (node:2 k0 x0 node0) #f)])
          ]
          ['> (define-values (node0 node1)
            (ordered-map-insert-node:impl x0 cmp-fn key value (sub1 depth) replace?))
            (cond
              [(and (eq? x0 node0) (not node1)) (values node #f)]
              [node1 (values (node:3 k0 node0 node1 x1) #f)]
              [(not node1) (values (node:2 k0 node0 x1) #f)])
          ]
        )
      ]
      [(node:3 k0 x0 x1 x2)
        (define k1 (ordered-map-min-key-node x1 (sub1 depth)))
        (match (cmp-fn k1 key)
          ['<
            (define k2 (ordered-map-min-key-node x2 (sub1 depth)))
            (match (cmp-fn k2 key)
              [(or '< '=) (define-values (node0 node1)
                (ordered-map-insert-node:impl x2 cmp-fn key value (sub1 depth) replace?))
                (cond
                  [(and (eq? x2 node0) (not node1)) (values node #f)]
                  [node1 (values 
                    (node:2 k0 x0 x1)
                    (node:2 (ordered-map-min-key-node node0 (sub1 depth)) node0 node1))]
                  [(not node1)
                    (values (node:3 k0 x0 x1 node0) #f)]
                )
              ]
              ['> (define-values (node0 node1)
                (ordered-map-insert-node:impl x1 cmp-fn key value (sub1 depth) replace?))
                (cond
                  [(and (eq? x1 node0) (not node1)) (values node #f)]
                  [node1 (values 
                    (node:2 k0 x0 node0)
                    (node:2 (ordered-map-min-key-node node1 (sub1 depth)) node1 x2))]
                  [(not node1)
                    (values (node:3 k0 x0 node0 x2) #f)]
                )
              ]
            )
          ]
          ['= (define-values (node0 node1)
            (ordered-map-insert-node:impl x1 cmp-fn key value (sub1 depth) replace?))
            (cond
              [(and (eq? x1 node0) (not node1)) (values node #f)]
              [node1 (values 
                (node:2 k0 x0 node0)
                (node:2 (ordered-map-min-key-node node1 (sub1 depth)) node1 x2))]
              [(not node1)
                (values (node:3 k0 x0 node0 x2) #f)]
            )
          ]
          ['> (define-values (node0 node1)
            (ordered-map-insert-node:impl x0 cmp-fn key value (sub1 depth) replace?))
            (cond
              [(and (eq? x0 node0) (not node1)) (values node #f)]
              [node1 (values 
                (node:2 k0 node0 node1)
                (node:2 k1 x1 x2))]
              [(not node1)
                (values (node:3 k0 node0 x1 x2) #f)]
            )
          ]
        )
      ]
    )]
  )
)

; return ft
(define (ordered-map-insert-ft:impl ft cmp-fn key value depth replace?)
  (match ft
    [(ft:single x)
      (match depth
        [0 (match-define (cons k0 _) x)
          (match (cmp-fn k0 key)
            ['< (ordered-map-size-changed? #t) (ft:deep k0 (digit:1 x) (ft:empty) (digit:1 (cons key value)))]
            ['= (if replace? (ft:single (cons key value)) ft)]
            ['> (ordered-map-size-changed? #t) (ft:deep key (digit:1 (cons key value)) (ft:empty) (digit:1 x))]
          )
        ]
        [_
          (define-values (node0 node1) (ordered-map-insert-node:impl x cmp-fn key value depth replace?))
          (cond
            [(and (eq? x node0) (not node1)) ft]
            [node1 (ft:deep (ordered-map-min-key-node node0 depth) (digit:1 node0) (ft:empty) (digit:1 node1))]
            [(not node1) (ft:single node0)]
          )
        ]
      )
    ]
    [(ft:deep o left inner right)
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
                  (define node0 (node:3 (ordered-map-min-key-node x0 depth) x0 x1 x2))
                  (define inner^ (consR:impl ordered-map-core inner node0 (add1 depth)))
                  (ft:deep o left inner^ right^^)
                ]
                [r
                  (define right^^ (list->digit r depth))
                  (ft:deep o left inner right^^)
                ]
              )
            ]
          )
        ]
        ['> 
          (match inner
            [(ft:empty) (define left^ 
              (ordered-map-insert-digit:impl left cmp-fn key value depth replace?))
              (cond
                [(eq? left left^) ft]
                [else
                  (match left^
                    [`(,x0 ,x1 ,x2 ,x3 ,x4)
                      (define left^^ (digit:2 x0 x1))
                      (define node0 (node:3 (ordered-map-min-key-node x2 depth) x2 x3 x4))
                      (define inner^ (consL:impl ordered-map-core inner node0 (add1 depth)))
                      (ft:deep o left^^ inner^ right)
                    ]
                    [l
                      (define left^^ (list->digit l depth))
                      (ft:deep o left^^ inner right)
                    ]
                  )
                ]
              )
            ]
            [_
              (define inner-v (ordered-map-min-key-ft inner (add1 depth)))
              (match (cmp-fn inner-v key)
                [(or '< '=)
                  (define inner^ (ordered-map-insert-ft:impl inner cmp-fn key value (add1 depth) replace?))
                  (if (eq? inner inner^) ft (ft:deep o left inner^ right))
                ]
                ['>
                  (define left^ 
                  (ordered-map-insert-digit:impl left cmp-fn key value depth replace?))
                  (cond
                    [(eq? left left^) ft]
                    [else
                      (match left^
                        [`(,x0 ,x1 ,x2 ,x3 ,x4)
                          (define left^^ (digit:2 x0 x1))
                          (define node0 (node:3 (ordered-map-min-key-node x2 depth) x2 x3 x4))
                          (define inner^ (consL:impl ordered-map-core inner node0 (add1 depth)))
                          (ft:deep o left^^ inner^ right)
                        ]
                        [l
                          (define left^^ (list->digit l depth))
                          (ft:deep o left^^ inner right)
                        ]
                      )
                    ]
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

; return list (1 ~ 5)
(define (ordered-map-insert-digit:impl digit cmp-fn key value depth replace?)
  (define kv (cons key value))
  (match depth
    [0
      (match digit
        [(digit:1 (and x0 (cons k0 _)))
          (match (cmp-fn k0 key)
            ['< (ordered-map-size-changed? #t) (list x0 kv)]
            ['= (if replace? (list kv) digit)]
          )
        ]
        [(digit:2 (and x0 (cons k0 _)) (and x1 (cons k1 _)))
          (match (cmp-fn k1 key)
            ['< (ordered-map-size-changed? #t) (list x0 x1 kv)]
            ['= (if replace? (list x0 kv) digit)]
            ['> 
              (match (cmp-fn k0 key)
                ['< (ordered-map-size-changed? #t) (list x0 kv x1)]
                ['= (if replace? (list kv x1) digit)]
              )]
          )
        ]
        [(digit:3 (and x0 (cons k0 _)) (and x1 (cons k1 _)) (and x2 (cons k2 _)))
          (match (cmp-fn k1 key)
            ['< 
              (match (cmp-fn k2 key)
                ['< (ordered-map-size-changed? #t) (list x0 x1 x2 kv)]
                ['= (if replace? (list x0 x1 kv) digit)]
                ['> (ordered-map-size-changed? #t) (list x0 x1 kv x2)]
              )]
            ['= (if replace? (list x0 kv x2) digit)]
            ['>
              (match (cmp-fn k0 key)
                ['< (ordered-map-size-changed? #t) (list x0 kv x1 x2)]
                ['= (if replace? (list kv x1 x2) digit)]
              )]
          )
        ]
        [(digit:4 (and x0 (cons k0 _)) (and x1 (cons k1 _)) (and x2 (cons k2 _)) (and x3 (cons k3 _)))
          (match (cmp-fn k2 key)
            ['< 
              (match (cmp-fn k3 key)
                ['< (ordered-map-size-changed? #t) (list x0 x1 x2 x3 kv)]
                ['= (if replace? (list x0 x1 x2 kv) digit)]
                ['> (ordered-map-size-changed? #t) (list x0 x1 x2 kv x3)]
              )]
            ['= (if replace? (list x0 x1 kv x3) digit)]
            ['> 
              (match (cmp-fn k1 key)
                ['< (ordered-map-size-changed? #t) (list x0 x1 kv x2 x3)]
                ['= (if replace? (list x0 kv x2 x3) digit)]
                ['>
                  (match (cmp-fn k0 key)
                    ['< (ordered-map-size-changed? #t) (list x0 kv x1 x2 x3)]
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
          (define-values (node0 node1) (ordered-map-insert-node:impl x0 cmp-fn key value depth replace?))
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
              (define-values (node0 node1) (ordered-map-insert-node:impl x1 cmp-fn key value depth replace?))
              (cond
                [(and (eq? x1 node0) (not node1)) digit]
                [node1 (list x0 node0 node1)]
                [(not node1) (list x0 node0)]
              )
            ]
            ['> 
              (define-values (node0 node1) (ordered-map-insert-node:impl x0 cmp-fn key value depth replace?))
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
                  (define-values (node0 node1) (ordered-map-insert-node:impl x2 cmp-fn key value depth replace?))
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
              (define-values (node0 node1) (ordered-map-insert-node:impl x1 cmp-fn key value depth replace?))
              (cond
                [(and (eq? x1 node0) (not node1)) digit]
                [node1 (list x0 node0 node1 x2)]
                [(not node1) (list x0 node0 x2)]
              )
            ]
            ['> 
              (define-values (node0 node1) (ordered-map-insert-node:impl x0 cmp-fn key value depth replace?))
              (cond
                [(and (eq? x0 node0) (not node1)) digit]
                [node1 (list node0 node1 x1 x2)]
                [(not node1) (list node0 x1 x2)]
              )
            ]
          )
        ]
        [(digit:4 x0 x1 x2 x3)
          (match (cmp-fn (ordered-map-min-key-node x2 depth) key)
            ['< (=> f)
              (match (cmp-fn (ordered-map-min-key-node x3 depth) key)
                [(or '< '=) 
                  (define-values (node0 node1) (ordered-map-insert-node:impl x3 cmp-fn key value depth replace?))
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
              (define-values (node0 node1) (ordered-map-insert-node:impl x2 cmp-fn key value depth replace?))
              (cond
                [(and (eq? x2 node0) (not node1)) digit]
                [node1 (list x0 x1 node0 node1 x3)]
                [(not node1) (list x0 x1 node0 x3)]
              )
            ]
            ['>
              (match (cmp-fn (ordered-map-min-key-node x1 depth) key)
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
    [(ft:empty) (ordered-map-size-changed? #t) (ft:single (cons key value))]
    [(ft:single _) (ordered-map-insert-ft:impl ft cmp-fn key value 0 replace?)]
    [(ft:deep o _ _ _)
      (match (cmp-fn o key)
        [(or '< '=) (ordered-map-insert-ft:impl ft cmp-fn key value 0 replace?)]
        ['> (ordered-map-size-changed? #t) (consL:impl ordered-map-core ft (cons key value) 0)]
      )
    ]
  )
)

(define (ordered-map-insert ordl key value replace?)
  (match-define (ordered-map cmp-fn k) ordl)
  (define k^ (ordered-map-insert-ft-wrap k cmp-fn key value replace?))
  (cond
    [(eq? k k^) ordl]
    [else (ordered-map cmp-fn k^)]
  )
)

; node, sub-node, del
(define (ordered-map-delete-node:impl node cmp-fn key depth)
  (match depth
    [1 (match node
      [(node:2 _ (and x0 (cons k0 _)) (and x1 (cons k1 _)))
        (match (cmp-fn k1 key)
          ['= (values #f x0 x1)]
          ['< (values node #f #f)]
          ['> (match (cmp-fn k0 key)
            ['= (values #f x1 x0)]
            ['< (values node #f #f)]
          )]
        )
      ]
      [(node:3 _ (and x0 (cons k0 _)) (and x1 (cons k1 _)) (and x2 (cons k2 _)))
        (match (cmp-fn k1 key)
          ['= (values (node:2 k0 x0 x2) #f x1)]
          ['< (match (cmp-fn k2 key)
            ['= (values (node:2 k0 x0 x1) #f x2)]
            [(or '< '>) (values node #f #f)]
          )]
          ['> (match (cmp-fn k0 key)
            ['= (values (node:2 k1 x1 x2) #f x0)]
            ['< (values node #f #f)]
          )]
        )
      ]
    )]
    [_ (match node
      [(node:2 k0 x0 x1)
        (match (cmp-fn (ordered-map-min-key-node x1 depth) key)
          [(or '= '<)
            (define-values (node0 subnode ret) (ordered-map-delete-node:impl x1 cmp-fn key (sub1 depth)))
            (match* (node0 subnode)
              [(_ #f) (if (eq? x1 node0) (values node #f ret) (values (node:2 k0 x0 node0) #f ret))]
              [(#f _) (match x0
                [(node:2 _ x00 x01)
                  (define subnode^ (node:3 k0 x00 x01 subnode))
                  (values #f subnode^ ret)
                ]
                [(node:3 _ x00 x01 x02)
                  (define node^ (node:2 k0 (node:2 k0 x00 x01) (node:2 (ordered-map-min-key-node x02 (- depth 2)) x02 subnode)))
                  (values node^ #f ret)
                ]
              )]
            )
          ]
          ['>
            (define-values (node0 subnode ret) (ordered-map-delete-node:impl x0 cmp-fn key (sub1 depth)))
            (match* (node0 subnode)
              [(_ #f) (if (eq? x0 node0) (values node #f ret) 
                (values (node:2 (ordered-map-min-key-node node0 (sub1 depth)) node0 x1) #f ret))]
              [(#f _) (match x1
                [(node:2 _ x10 x11)
                  (define subnode^ (node:3 (ordered-map-min-key-node subnode (- depth 2)) subnode x10 x11))
                  (values #f subnode^ ret)
                ]
                [(node:3 _ x10 x11 x12)
                  (define k0^ (ordered-map-min-key-node subnode (- depth 2)))
                  (define node^ (node:2 k0^ 
                    (node:2 k0^ subnode x10) (node:2 (ordered-map-min-key-node x11 (- depth 2)) x11 x12)))
                  (values node^ #f ret)
                ]
              )]
            )
          ]
        )
      ]
      [(node:3 k0 x0 x1 x2)
        (match (cmp-fn (ordered-map-min-key-node x1 depth) key)
          ['< (=> h)
            (match (cmp-fn (ordered-map-min-key-node x2 depth) key)
              [(or '< '=)
                (define-values (node0 subnode ret) (ordered-map-delete-node:impl x2 cmp-fn key (sub1 depth)))
                (match* (node0 subnode)
                  [(_ #f) (if (eq? x2 node0) (values node #f ret) (values (node:3 k0 x0 x1 node0) #f ret))]
                  [(#f _) (match x1
                    [(node:2 _ x10 x11)
                      (define node0^ (node:3 (ordered-map-min-key-node x10 (- depth 2)) x10 x11 subnode))
                      (values (node:2 k0 x0 node0^) #f ret)
                    ]
                    [(node:3 _ x10 x11 x12)
                      (define node^ (node:3 k0 x0 (node:2 (ordered-map-min-key-node x10 (- depth 2)) x10 x11) 
                        (node:2 (ordered-map-min-key-node x12 (- depth 2)) x12 subnode)))
                      (values node^ #f ret)
                    ]
                  )]
                )
              ]
              ['> (h)]
            )
          ]
          [(or '< '=)
            (define-values (node0 subnode ret) (ordered-map-delete-node:impl x1 cmp-fn key (sub1 depth)))
            (match* (node0 subnode)
              [(_ #f) (if (eq? x1 node0) (values node #f ret) (values (node:3 k0 x0 node0 x2) #f ret))]
              [(#f _) (match x2
                [(node:2 _ x20 x21)
                  (define node0^ (node:3 (ordered-map-min-key-node subnode (- depth 2)) subnode x20 x21))
                  (values (node:2 k0 x0 node0^) #f ret)
                ]
                [(node:3 _ x20 x21 x22)
                  (define node^ (node:3 k0 x0 (node:2 (ordered-map-min-key-node subnode (- depth 2)) subnode x20) 
                    (node:2 (ordered-map-min-key-node x21 (- depth 2)) x21 x22)))
                  (values node^ #f ret)
                ]
              )]
            )
          ]
          ['>
            (define-values (node0 subnode ret) (ordered-map-delete-node:impl x0 cmp-fn key (sub1 depth)))
            (match* (node0 subnode)
              [(_ #f) (if (eq? x0 node0) (values node #f ret) 
                (values (node:3 (ordered-map-min-key-node node0 (sub1 depth)) node0 x1 x2) #f ret))]
              [(#f _) (match x1
                [(node:2 _ x10 x11)
                  (define subnode^ (node:3 (ordered-map-min-key-node subnode (- depth 2)) subnode x10 x11))
                  (values (node:2 (ordered-map-min-key-node subnode^ (sub1 depth)) subnode^ x2) #f ret)
                ]
                [(node:3 _ x10 x11 x12)
                  (define k0^ (ordered-map-min-key-node subnode (- depth 2)))
                  (define node^ (node:3 k0^ 
                    (node:2 k0^ subnode x10) (node:2 (ordered-map-min-key-node x11 (- depth 2)) x11 x12) x2))
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
  (match node
    [(node:2 o x0 x1)
      (values (node:3 o x0 x1 subnode) #f)
    ]
    [(node:3 o x0 x1 x2)
      (values (node:2 o x0 x1) (node:2 (ordered-map-min-key-node x2 (sub1 depth)) x2 subnode))
    ]
  )
)

(define (ordered-map-node-mergeL node subnode depth)
  (match node
    [(node:2 _ x0 x1) (values (node:3 (ordered-map-min-key-node subnode (sub1 depth)) subnode x0 x1) #f)]
    [(node:3 _ x0 x1 x2) (values 
      (node:2 (ordered-map-min-key-node subnode (sub1 depth)) subnode x0)
      (node:2 (ordered-map-min-key-node x1 (sub1 depth) x1 x2))
      )]
  )
)

; ordered-map-delete-node:impl
; list, subnode, ret
(define (ordered-map-delete-digit:impl digit cmp-fn key depth)
  (match depth
    [0 (match digit
      [(digit:1 (and x0 (cons k0 _))) 
        (match (cmp-fn k0 key)
          ['< (values digit #f #f)]
          ['= (values '() #f x0)]
        )
      ]
      [(digit:2 (and x0 (cons k0 _)) (and x1 (cons k1 _)))
        (match (cmp-fn k1 key)
          ['< (values digit #f #f)]
          ['= (values (list x0) #f x1)]
          ['> (match (cmp-fn k0 key)
            ['< (values digit #f #f)]
            ['= (values (list x1) #f x0)]
          )]
        )
      ]
      [(digit:3 (and x0 (cons k0 _)) (and x1 (cons k1 _)) (and x2 (cons k2 _)))
        (match (cmp-fn k1 key)
          ['< (match (cmp-fn k2 key)
            [(or '< '>) (values digit #f #f)]
            ['= (values (list x0 x1) #f x2)]
          )]
          ['= (values (list x0 x2) #f x1)]
          ['> (match (cmp-fn k0 key)
            ['< (values digit #f #f)]
            ['= (values (list x1 x2) #f x0)]
          )]
        )
      ]
      [(digit:4 (and x0 (cons k0 _)) (and x1 (cons k1 _)) (and x2 (cons k2 _)) (and x3 (cons k3 _)))
        (match (cmp-fn k2 key)
          ['< (match (cmp-fn k3 key)
            [(or '< '>) (values digit #f #f)]
            ['= (values (list x0 x1 x2) #f x3)]
          )]
          ['= (values (list x0 x1 x3) #f x2)]
          ['> (match (cmp-fn k1 key)
            ['< (values digit #f #f)]
            ['= (values (list x0 x2 x3) #f x1)]
            ['> (match (cmp-fn k0 key)
              ['< (values digit #f #f)]
              ['= (values (list x1 x2 x3) #f x0)]
            )]
          )]
        )
      ]
    )]
    [_ (match digit
      [(digit:1 x0) (define-values (node0 subnode ret) (ordered-map-delete-node:impl x0 cmp-fn key depth))
        (cond
          [(eq? x0 node0) (values digit #f ret)]
          [node0 (values (list node0) #f ret)]
          [subnode (values '() subnode ret)]
        )
      ]
      [(digit:2 x0 x1)
        (match (cmp-fn (ordered-map-min-key-node x1 depth) key)
          [(or '< '=) (define-values (node0 subnode ret) (ordered-map-delete-node:impl x1 cmp-fn key depth))
            (cond
              [(eq? x1 node0) (values digit #f ret)]
              [node0 (values (list x0 node0) #f ret)]
              [subnode 
                (define-values (x0^ x1^) (ordered-map-node-mergeR x0 subnode depth))
                (values (if x1^ (list x0^ x1^) (list x0^)) #f ret)
              ]
            )
          ]
          ['> (define-values (node0 subnode ret) (ordered-map-delete-node:impl x0 cmp-fn key depth))
            (cond
              [(eq? x0 node0) (values digit #f ret)]
              [node0 (values (list node0 x1) #f ret)]
              [subnode
                (define-values (x0^ x1^) (ordered-map-node-mergeL x1 subnode depth))
                (values (if x1^ (list x0^ x1^) (list x0^)) #f ret)
              ]
            )
          ]
        )
      ]
      [(digit:3 x0 x1 x2)
        (match (cmp-fn (ordered-map-min-key-node x1 depth) key)
          ['< (=> f)
            (match (cmp-fn (ordered-map-min-key-node x2 depth) key)
              [(or '< '=)
                (define-values (node0 subnode ret) (ordered-map-delete-node:impl x2 cmp-fn key depth))
                (cond
                  [(eq? x2 node0) (values digit #f ret)]
                  [node0 (values (list x0 x1 node0) #f ret)]
                  [subnode (define-values (x1^ x2^) (ordered-map-node-mergeR x1 subnode depth))
                    (values (if x2^ (list x0 x1^ x2^) (list x0 x1^)) #f ret)
                  ]
                )
              ]
              ['> (f)]
            )
          ]
          [(or '< '=)
            (define-values (node0 subnode ret) (ordered-map-delete-node:impl x1 cmp-fn key depth))
            (cond
              [(eq? x1 node0) (values digit #f ret)]
              [node0 (values (list x0 node0 x2) #f ret)]
              [subnode (define-values (x0^ x1^) (ordered-map-node-mergeR x0 subnode depth))
                (values (if x1^ (list x0^ x1^ x2) (list x0^ x2)) #f ret)
              ]
            )
          ]
          ['> (define-values (node0 subnode ret) (ordered-map-delete-node:impl x0 cmp-fn key depth))
            (cond
              [(eq? x0 node0) (values digit #f ret)]
              [node0 (values (list node0 x1 x2) #f ret)]
              [subnode
                (define-values (x0^ x1^) (ordered-map-node-mergeL x1 subnode depth))
                (values (if x1^ (list x0^ x1^ x2) (list x0^ x2)) #f ret)
              ]
            )
          ]
        )
      ]
      [(digit:4 x0 x1 x2 x3)
        (match (cmp-fn (ordered-map-min-key-node x2 depth) key)
          ['< (=> f)
            (match (cmp-fn (ordered-map-min-key-node x3 depth) key)
              [(or '< '=)
                (define-values (node0 subnode ret) (ordered-map-delete-node:impl x3 cmp-fn key depth))
                (cond
                  [(eq? x3 node0) (values digit #f ret)]
                  [node0 (values (list x0 x1 x2 node0) #f ret)]
                  [subnode (define-values (x2^ x3^) (ordered-map-node-mergeR x2 subnode depth))
                    (values (if x3^ (list x0 x1 x2^ x3^) (list x0 x1 x2^)) #f ret)
                  ]
                )
              ]
              ['> (f)]
            )
          ]
          [(or '< '=)
            (define-values (node0 subnode ret) (ordered-map-delete-node:impl x2 cmp-fn key depth))
            (cond
              [(eq? x2 node0) (values digit #f ret)]
              [node0 (values (list x0 x1 node0 x3) #f ret)]
              [subnode (define-values (x1^ x2^) (ordered-map-node-mergeR x1 subnode depth))
                (values (if x2^ (list x0 x1^ x2^ x3) (list x0 x1^ x3)) #f ret)
              ]
            )
          ]
          ['> (match (cmp-fn (ordered-map-min-key-node x1 depth) key)
            [(or '< '=)
              (define-values (node0 subnode ret) (ordered-map-delete-node:impl x0 cmp-fn key depth))
              (cond
                [(eq? x1 node0) (values digit #f ret)]
                [node0 (values (list x0 node0 x2 x3) #f ret)]
                [subnode
                  (define-values (x0^ x1^) (ordered-map-node-mergeR x0 subnode depth))
                  (values (if x1^ (list x0^ x1^ x2 x3) (list x0^ x2 x3)) #f ret)
                ]
              )
            ]
            ['>
              (define-values (node0 subnode ret) (ordered-map-delete-node:impl x0 cmp-fn key depth))
              (cond
                [(eq? x0 node0) (values digit #f ret)]
                [node0 (values (list node0 x1 x2 x3) #f ret)]
                [subnode
                  (define-values (x0^ x1^) (ordered-map-node-mergeL x1 subnode depth))
                  (values (if x1^ (list x0^ x1^ x2 x3) (list x0^ x2 x3)) #f ret)
                ]
              )
            ]
          )]
        )
      ]
    )]
  )
)

(define (left-inner-mergeR left inner subright o depth)
  (match inner
    [(ft:empty)
      (match left
        [(digit:1 x0)
          (define-values (r0 r1) (ordered-map-node-mergeR x0 subright depth))
          (if r1 (ft:deep o (digit:1 r0) (ft:empty) (digit:1 r1)) (ft:single r0))
        ]
        [(digit:2 x0 x1)
          (define-values (r0 r1) (ordered-map-node-mergeR x1 subright depth))
          (ft:deep o (digit:1 x0) (ft:empty) (if r1 (digit:2 r0 r1) (digit:1 r0)))
        ]
        [(digit:3 x0 x1 x2)
          (define-values (r0 r1) (ordered-map-node-mergeR x2 subright depth))
          (ft:deep o (digit:2 x0 x1) (ft:empty) (if r1 (digit:2 r0 r1) (digit:1 r0)))
        ]
        [(digit:4 x0 x1 x2 x3)
          (define-values (r0 r1) (ordered-map-node-mergeR x3 subright depth))
          (ft:deep o (digit:3 x0 x1 x2) (ft:empty) (if r1 (digit:2 r0 r1) (digit:1 r0)))
        ]
      )
    ]
    [_ 
      (define-values (r inner^) (hdR:impl ordered-map-core inner (add1 depth)))
      (define-values (r0 r1) (ordered-map-node-mergeR r subright depth))
      (ft:deep o left inner^ (if r1 (digit:2 r0 r1) (digit:1 r0)))
    ]
  )
)

(define (right-inner-mergeL right inner subleft depth)
  (match inner
    [(ft:empty)
      (match right
        [(digit:1 x0)
          (define-values (r0 r1) (ordered-map-node-mergeL x0 subleft depth))
          (if r1 (ft:deep (ordered-map-min-key-node r0 depth) (digit:1 r0) (ft:empty) (digit:1 r1)) (ft:single r0))
        ]
        [(digit:2 x0 x1)
          (define-values (r0 r1) (ordered-map-node-mergeL x0 subleft depth))
          (ft:deep (ordered-map-min-key-node r0 depth) (if r1 (digit:2 r0 r1) (digit:1 r0)) (ft:empty) (digit:1 x1))
        ]
        [(digit:3 x0 x1 x2)
          (define-values (r0 r1) (ordered-map-node-mergeL x0 subleft depth))
          (ft:deep (ordered-map-min-key-node r0 depth) (if r1 (digit:2 r0 r1) (digit:1 r0)) (ft:empty) (digit:2 x1 x2))
        ]
        [(digit:4 x0 x1 x2 x3)
          (define-values (r0 r1) (ordered-map-node-mergeL x0 subleft depth))
          (ft:deep (ordered-map-min-key-node r0 depth) (if r1 (digit:2 r0 r1) (digit:1 r0)) (ft:empty) (digit:3 x1 x2 x3))
        ]
      )
    ]
    [_ 
      (define-values (l inner^) (hdL:impl ordered-map-core inner (add1 depth)))
      (define-values (r0 r1) (ordered-map-node-mergeL l subleft depth))
      (ft:deep (ordered-map-min-key-node r0 depth) (if r1 (digit:2 r0 r1) (digit:1 r0)) inner^ right)
    ]
  )
)

; ft, subnode, rst
(define (ordered-map-delete-ft:impl ft cmp-fn key depth)
  (match ft
    [(ft:deep o left inner right)
      (define right-v (ordered-map-min-key-digit right depth))
      (match (cmp-fn right-v key)
        [(or '< '=)
          (match-define-values (right^ subright ret) (ordered-map-delete-digit:impl right cmp-fn key depth))
          (cond
            [(eq? right right^) (values ft #f ret)]
            [(not (null? right^)) (define right^^ (list->digit right^ depth)) 
              (values (ft:deep o left inner right^^) #f ret)]
            [subright
              (define ft^ (left-inner-mergeR left inner subright o depth))
              (values ft^ #f ret)
            ]
            [(= depth 0)
              (define ft^
                (match inner
                  [(ft:empty)
                    (match left
                      [(digit:1 n) (ft:single n)]
                      [(digit:2 n0 n1) (ft:deep (ordered-map-min-key-node n0 0) (digit:1 n0) (ft:empty) (digit:1 n1))]
                      [(digit:3 n0 n1 n2) (ft:deep (ordered-map-min-key-node n0 0) (digit:2 n0 n1) (ft:empty) (digit:1 n2))]
                      [(digit:4 n0 n1 n2 n3) (ft:deep (ordered-map-min-key-node n0 0) (digit:2 n0 n1) (ft:empty) (digit:2 n2 n3))]
                    )
                  ]
                  [_
                    (define-values (new-right inner^) (hdR:impl ordered-map-core inner 1))
                    (define right^^
                      (match new-right
                        [(node:2 _ n0 n1) (digit:2 n0 n1)]
                        [(node:3 _ n0 n1 n2) (digit:3 n0 n1 n2)]
                      ))
                    (ft:deep o left inner^ right^^)
                  ]
                ))
              (values ft^ #f ret)
            ]
          )
        ]
        ['> (=> h)
          (match inner
            [(ft:empty) (h)]
            [_ (define inner-v (ordered-map-min-key-ft inner (add1 depth)))
              (match (cmp-fn inner-v key)
                [(or '< '=)
                  (match-define-values (inner^ subinner ret) (ordered-map-delete-ft:impl inner cmp-fn key (add1 depth)))
                  (cond
                    [(eq? inner inner^) (values ft #f ret)]
                    [inner^ (values (ft:deep o left inner^ right) #f ret)]
                    [subinner (begin
                      (define ft^ (match* (left right)
                        [((digit:4 x0 x1 x2 x3) (digit:4 _ _ _ _))
                          (define node0 (node:3 (ordered-map-min-key-node x2 depth) x2 x3 subinner))
                          (define left^ (digit:2 x0 x1))
                          (ft:deep o left^ (ft:single node0) right)
                        ]
                        [((digit:4 _ _ _ _) _)
                          (define right^ (match right
                            [(digit:1 x) (digit:2 subinner x)]
                            [(digit:2 x0 x1) (digit:3 subinner x0 x1)]
                            [(digit:3 x0 x1 x2) (digit:4 subinner x0 x1 x2)]
                          ))
                          (ft:deep o left (ft:empty) right^)
                        ]
                        [(_ _)
                          (define left^ (match left
                            [(digit:1 x) (digit:2 x subinner)]
                            [(digit:2 x0 x1) (digit:3 x0 x1 subinner)]
                            [(digit:3 x0 x1 x2) (digit:4 x0 x1 x2 subinner)]
                          ))
                          (ft:deep o left^ (ft:empty) right)
                        ]
                      ))
                      (values ft^ #f ret)
                    )]
                  )
                ]
                ['> (h)]
              )
            ]
          )
        ]
        ['>
          (match-define-values (left^ subleft ret) (ordered-map-delete-digit:impl left cmp-fn key depth))
          (cond
            [(eq? left left^) (values ft #f ret)]
            [(not (null? left^)) (define left^^ (list->digit left^ depth))
              (values (ft:deep (ordered-map-min-key-digit left^^ depth) left^^ inner right) #f ret)
            ]
            [subleft
              (define ft^ (right-inner-mergeL right inner subleft depth))
              (values ft^ #f ret)
            ]
            [(= depth 0)
              (define ft^
                (match inner
                  [(ft:empty)
                    (match right
                      [(digit:1 n) (ft:single n)]
                      [(digit:2 n0 n1) (ft:deep (ordered-map-min-key-node n0 0) (digit:1 n0) (ft:empty) (digit:1 n1))]
                      [(digit:3 n0 n1 n2) (ft:deep (ordered-map-min-key-node n0 0) (digit:2 n0 n1) (ft:empty) (digit:1 n2))]
                      [(digit:4 n0 n1 n2 n3) (ft:deep (ordered-map-min-key-node n0 0) (digit:2 n0 n1) (ft:empty) (digit:2 n2 n3))]
                    )
                  ]
                  [_
                    (define-values (new-left inner^) (hdL:impl ordered-map-core inner 1))
                    (define-values (left^^ o^)
                      (match new-left
                        [(node:2 o^ n0 n1) (values (digit:2 n0 n1) o^)]
                        [(node:3 o^ n0 n1 n2) (values (digit:3 n0 n1 n2) o^)]
                      ))
                    (ft:deep o^ left^^ inner^ right)
                  ]
                ))
              (values ft^ #f ret)
            ]
          )
        ]
      )
    ]
    [(ft:single x)
      (define k (ordered-map-min-key-node x depth))
      (match depth
        [0
          (match (cmp-fn k key)
            ['= (values (ft:empty) #f x)]
            ['< (values ft #f #f)]
          )
        ]
        [_
          (match-define-values (node0 subnode ret) (ordered-map-delete-node:impl x cmp-fn key depth))
          (cond
            [(eq? x node0) (values ft #f ret)]
            [node0 (values (ft:single node0) #f ret)]
            [subnode (values #f subnode ret)]
          )
        ]
      )
    ]
  )
)

(define (ordered-map-delete-ft-wrap ft cmp-fn key)
  (match ft
    [(ft:empty) (values ft #f)]
    [(ft:single _) (match-define-values (ft^ _ ret) (ordered-map-delete-ft:impl ft cmp-fn key 0)) (values ft^ ret)]
    [(ft:deep o _ _ _) (match (cmp-fn o key)
      [(or '< '=) 
        (match-define-values (ft^ _ ret) (ordered-map-delete-ft:impl ft cmp-fn key 0))
        (values ft^ ret)]
      ['> (values ft #f)]
    )]
  )
)

(define (ordered-map-delete ft key)
  (match-define (ordered-map cmp-fn ft^) ft)
  (match-define-values (ft^^ ret) (ordered-map-delete-ft-wrap ft^ cmp-fn key))
  (values (if (eq? ft^ ft^^) ft (ordered-map cmp-fn ft^^)) ret)
)

;; ========================================
;; Constructor
;; ========================================

(define (ordered-map-empty cmp-fn)
  (ordered-map cmp-fn (ft:empty)))

;; ========================================
;; Additional gen:dict methods
;; ========================================

(define (ordered-map-count om)
  (define (count-ft ft depth)
    (match ft
      [(ft:empty) 0]
      [(ft:single node) (count-node node depth)]
      [(ft:deep _ left inner right)
        (+ (count-digit left depth)
           (count-ft inner (add1 depth))
           (count-digit right depth))]))
  (define (count-node node depth)
    (match depth
      [0 1]
      [_ (match node
        [(node:2 _ a b) (+ (count-node a (sub1 depth)) (count-node b (sub1 depth)))]
        [(node:3 _ a b c) (+ (count-node a (sub1 depth)) (count-node b (sub1 depth)) (count-node c (sub1 depth)))])]))
  (define (count-digit digit depth)
    (match digit
      [(digit:1 a) (count-node a depth)]
      [(digit:2 a b) (+ (count-node a depth) (count-node b depth))]
      [(digit:3 a b c) (+ (count-node a depth) (count-node b depth) (count-node c depth))]
      [(digit:4 a b c d) (+ (count-node a depth) (count-node b depth) (count-node c depth) (count-node d depth))]))
  (match-define (ordered-map _ ft) om)
  (count-ft ft 0))

(define (ordered-map-has-key? om key)
  (if (ordered-map-query om key) #t #f))

(define (ordered-map-keys om)
  (for/list ([kv (in-ordered-map om)]) (car kv)))

(define (ordered-map-values om)
  (for/list ([kv (in-ordered-map om)]) (cdr kv)))

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
        #:continue-with-pos? (lambda (pos) (if pos #t #f))))))

;; Generator-based ascending traversal (more efficient)
(define (in-ordered-map om)
  (in-generator
    (define (yield-node node depth)
      (match depth
        [0 (yield node)]
        [_ (match node
          [(node:2 _ x0 x1)
            (yield-node x0 (sub1 depth))
            (yield-node x1 (sub1 depth))]
          [(node:3 _ x0 x1 x2)
            (yield-node x0 (sub1 depth))
            (yield-node x1 (sub1 depth))
            (yield-node x2 (sub1 depth))])]))
    (define (yield-digit digit depth)
      (match digit
        [(digit:1 x0) (yield-node x0 depth)]
        [(digit:2 x0 x1) (yield-node x0 depth) (yield-node x1 depth)]
        [(digit:3 x0 x1 x2) (yield-node x0 depth) (yield-node x1 depth) (yield-node x2 depth)]
        [(digit:4 x0 x1 x2 x3) (yield-node x0 depth) (yield-node x1 depth) (yield-node x2 depth) (yield-node x3 depth)]))
    (define (yield-ft ft depth)
      (match ft
        [(ft:empty) (void)]
        [(ft:single node) (yield-node node depth)]
        [(ft:deep _ left inner right)
          (yield-digit left depth)
          (yield-ft inner (add1 depth))
          (yield-digit right depth)]))
    (match-define (ordered-map _ ft) om)
    (yield-ft ft 0)))

;; Generator-based descending traversal
(define (in-ordered-map-reverse om)
  (in-generator
    (define (yield-node node depth)
      (match depth
        [0 (yield node)]
        [_ (match node
          [(node:2 _ x0 x1)
            (yield-node x1 (sub1 depth))
            (yield-node x0 (sub1 depth))]
          [(node:3 _ x0 x1 x2)
            (yield-node x2 (sub1 depth))
            (yield-node x1 (sub1 depth))
            (yield-node x0 (sub1 depth))])]))
    (define (yield-digit digit depth)
      (match digit
        [(digit:1 x0) (yield-node x0 depth)]
        [(digit:2 x0 x1) (yield-node x1 depth) (yield-node x0 depth)]
        [(digit:3 x0 x1 x2) (yield-node x2 depth) (yield-node x1 depth) (yield-node x0 depth)]
        [(digit:4 x0 x1 x2 x3) (yield-node x3 depth) (yield-node x2 depth) (yield-node x1 depth) (yield-node x0 depth)]))
    (define (yield-ft ft depth)
      (match ft
        [(ft:empty) (void)]
        [(ft:single node) (yield-node node depth)]
        [(ft:deep _ left inner right)
          (yield-digit right depth)
          (yield-ft inner (add1 depth))
          (yield-digit left depth)]))
    (match-define (ordered-map _ ft) om)
    (yield-ft ft 0)))

;; ========================================
;; Ref and Set (dict-style)
;; ========================================

(define (ordered-map-ref om key [default (lambda () (error "key not found" key))])
  (match (ordered-map-query om key)
    [#f (if (procedure? default) (default) default)]
    [(cons _ v) v]))

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
(provide ordered-map-empty)
(provide ordered-map-ref ordered-map-set)
(provide ordered-map-count ordered-map-has-key? ordered-map-keys ordered-map-values)
(provide in-ordered-map in-ordered-map-reverse in-ordered-map/lazy)

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
      )
    ]
    [_
      (match node
        [(node:2 _ x0 x1)
          (define x1-key (ordered-map-min-key-node x1 (sub1 depth)))
          (define x1-cmp-rst (cmp-fn x1-key key))
          (match* (x1-cmp-rst mode)
            [('= (or '>= '<= '>)) (ordered-map-query-weak-node:impl x1 cmp-fn key mode (sub1 depth))]
            [('< _) (ordered-map-query-weak-node:impl x1 cmp-fn key mode (sub1 depth))]
            [(_ (or '< '<=)) 
              (ordered-map-query-weak-node:impl x0 cmp-fn key mode (sub1 depth))]
            [(_ _)
              (define tmp (ordered-map-query-weak-node:impl x0 cmp-fn key mode (sub1 depth)))
              (if tmp tmp (ordered-map-query-weak-node:impl x1 cmp-fn key mode (sub1 depth)))
            ]
          )
        ]
        [(node:3 _ x0 x1 x2)
          (define x2-key (ordered-map-min-key-node x2 (sub1 depth)))
          (define x2-cmp-rst (cmp-fn x2-key key))
          (match* (x2-cmp-rst mode)
            [('= (or '>= '<= '>)) (ordered-map-query-weak-node:impl x2 cmp-fn key mode (sub1 depth))]
            [('< _) (ordered-map-query-weak-node:impl x2 cmp-fn key mode (sub1 depth))]
            [(_ _)
              (define x1-key (ordered-map-min-key-node x1 (sub1 depth)))
              (define x1-cmp-rst (cmp-fn x1-key key))
              (match* (x1-cmp-rst mode)
                [('= (or '>= '<=)) (ordered-map-query-weak-node:impl x1 cmp-fn key mode (sub1 depth))]
                [('= '>) (define tmp (ordered-map-query-weak-node:impl x1 cmp-fn key mode (sub1 depth)))
                  (if tmp tmp (ordered-map-query-weak-node:impl x2 cmp-fn key mode (sub1 depth)))
                ]
                [('< (or '<= '<)) (ordered-map-query-weak-node:impl x1 cmp-fn key mode (sub1 depth))]
                [('< (or '>= '>)) (define tmp (ordered-map-query-weak-node:impl x1 cmp-fn key mode (sub1 depth)))
                  (if tmp tmp (ordered-map-query-weak-node:impl x2 cmp-fn key mode (sub1 depth)))]
                [('= '<) (ordered-map-query-weak-node:impl x0 cmp-fn key mode (sub1 depth))]
                [('> (or '<= '<)) (ordered-map-query-weak-node:impl x0 cmp-fn key mode (sub1 depth))]
                [('> (or '>= '>))
                  (define tmp (ordered-map-query-weak-node:impl x0 cmp-fn key mode (sub1 depth)))
                  (if tmp tmp (ordered-map-query-weak-node:impl x1 cmp-fn key mode (sub1 depth)))
                ]
              )
            ]
          )
        ]
      )
    ]
  )
)

(define (ordered-map-query-weak-ft:impl ft cmp-fn key mode depth)
  (match ft
    [(ft:empty) #f]
    [(ft:single node) (ordered-map-query-weak-node:impl node cmp-fn key mode depth)]
    [(ft:deep _ left inner right)
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
                  (define tmp (ordered-map-query-weak-digit:impl left cmp-fn key mode depth))
                  (if tmp tmp (ordered-map-query-weak-digit:impl right cmp-fn key mode depth))
                ]
              )
            ] 
            [_ 
              (define inner-v (ordered-map-min-key-ft inner (add1 depth)))
              (define inner-v-cmp-rst (cmp-fn inner-v key))
              (match* (inner-v-cmp-rst mode)
                [('= (or '<= '>= '>)) (ordered-map-query-weak-ft:impl inner cmp-fn key mode (add1 depth))]
                [('< (or '>= '>)) (define tmp (ordered-map-query-weak-ft:impl inner cmp-fn key mode (add1 depth)))
                  (if tmp tmp (ordered-map-query-weak-digit:impl right cmp-fn key mode depth))]
                [('< _) (ordered-map-query-weak-ft:impl inner cmp-fn key mode (add1 depth))]
                [(_ (or '<= '<))
                  (ordered-map-query-weak-digit:impl left cmp-fn key mode depth)]
                [(_ _)
                  (define tmp (ordered-map-query-weak-digit:impl left cmp-fn key mode depth))
                  (if tmp tmp (ordered-map-query-weak-ft:impl inner cmp-fn key mode (add1 depth)))
                ]
              )
            ])
        ]
      )
    ]
  )
)

(define (ordered-map-query-weak-digit:impl digit cmp-fn key mode depth)
  (match digit
    [(digit:1 x0)
      (ordered-map-query-weak-node:impl x0 cmp-fn key mode depth)
    ]
    [(digit:2 x0 x1)
      (define x1-v (ordered-map-min-key-node x1 depth))
      (match* ((cmp-fn x1-v key) mode)
        [('= (or '<= '>= '>)) (ordered-map-query-weak-node:impl x1 cmp-fn key mode depth)]
        [('< _) (ordered-map-query-weak-node:impl x1 cmp-fn key mode depth)]
        [(_ (or '< '<=)) (ordered-map-query-weak-node:impl x0 cmp-fn key mode depth)]
        [(_ _)
          (define tmp (ordered-map-query-weak-node:impl x0 cmp-fn key mode depth))
          (if tmp tmp (ordered-map-query-weak-node:impl x1 cmp-fn key mode depth))
        ]
      )
    ]
    [(digit:3 x0 x1 x2)
      (define x1-v (ordered-map-min-key-node x1 depth))
      (match* ((cmp-fn x1-v key) mode)
        [('= (or '<= '>=)) (ordered-map-query-weak-node:impl x1 cmp-fn key mode depth)]
        [('= '>) (define tmp (ordered-map-query-weak-node:impl x1 cmp-fn key mode depth))
          (if tmp tmp (ordered-map-query-weak-node:impl x2 cmp-fn key mode depth))]
        [('< _)
          (define x2-v (ordered-map-min-key-node x2 depth))
          (match* ((cmp-fn x2-v key) mode)
            [('= (or '<= '>= '>)) (ordered-map-query-weak-node:impl x2 cmp-fn key mode depth)]
            [('< _) (ordered-map-query-weak-node:impl x2 cmp-fn key mode depth)]
            [(_ (or '<= '<)) (ordered-map-query-weak-node:impl x1 cmp-fn key mode depth)]
            [(_ _) (define tmp (ordered-map-query-weak-node:impl x1 cmp-fn key mode depth))
              (if tmp tmp (ordered-map-query-weak-node:impl x2 cmp-fn key mode depth))]
          )
        ]
        [(_ (or '< '<=))
          (ordered-map-query-weak-node:impl x0 cmp-fn key mode depth)
        ]
        [(_ _)
          (define tmp (ordered-map-query-weak-node:impl x0 cmp-fn key mode depth))
          (if tmp tmp (ordered-map-query-weak-node:impl x1 cmp-fn key mode depth))
        ]
      )
    ]
    [(digit:4 x0 x1 x2 x3)
      (define x2-v (ordered-map-min-key-node x2 depth))
      (match* ((cmp-fn x2-v key) mode)
        [('= (or '<= '>=)) (ordered-map-query-weak-node:impl x2 cmp-fn key mode depth)]
        [('= '>) (define tmp (ordered-map-query-weak-node:impl x2 cmp-fn key mode depth))
          (if tmp tmp (ordered-map-query-weak-node:impl x3 cmp-fn key mode depth))]
        [('< _)
          (define x3-v (ordered-map-min-key-node x3 depth))
          (match* ((cmp-fn x3-v key) mode)
            [('= (or '<= '>= '>)) (ordered-map-query-weak-node:impl x3 cmp-fn key mode depth)]
            [('< _) (ordered-map-query-weak-node:impl x3 cmp-fn key mode depth)]
            [(_ (or '<= '<)) (ordered-map-query-weak-node:impl x2 cmp-fn key mode depth)]
            [(_ _) (define tmp (ordered-map-query-weak-node:impl x2 cmp-fn key mode depth))
              (if tmp tmp (ordered-map-query-weak-node:impl x3 cmp-fn key mode depth))]
          )
        ]
        [(_ (or '< '<=))
          (define x1-v (ordered-map-min-key-node x1 depth))
          (match* ((cmp-fn x1-v key) mode)
            [('= (or '<= '>= '>)) (ordered-map-query-weak-node:impl x1 cmp-fn key mode depth)]
            [('< _) (ordered-map-query-weak-node:impl x1 cmp-fn key mode depth)]
            [(_ (or '< '<=)) (ordered-map-query-weak-node:impl x0 cmp-fn key mode depth)]
          )
        ]
        [(_ _)
          (define x1-v (ordered-map-min-key-node x1 depth))
          (match* ((cmp-fn x1-v key) mode)
            [('= (or '<= '>=)) (ordered-map-query-weak-node:impl x1 cmp-fn key mode depth)]
            [('= '>) (define tmp (ordered-map-query-weak-node:impl x1 cmp-fn key mode depth))
              (if tmp tmp (ordered-map-query-weak-node:impl x2 cmp-fn key mode depth))]
            [('< _) (define tmp (ordered-map-query-weak-node:impl x1 cmp-fn key mode depth))
              (if tmp tmp (ordered-map-query-weak-node:impl x2 cmp-fn key mode depth))]
            [(_ (or '< '<=)) (assert-unreachable)]
            [(_ _)
              (define tmp (ordered-map-query-weak-node:impl x0 cmp-fn key mode depth))
              (if tmp tmp (ordered-map-query-weak-node:impl x1 cmp-fn key mode depth))
            ]
          )
        ]
      )
    ]
  )
)

(define (ordered-map-query-weak om key mode)
  (match-define (ordered-map cmp-fn ft^) om)
  (ordered-map-query-weak-ft:impl ft^ cmp-fn key mode 0)
)
