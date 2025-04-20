#lang racket/base

; ordl

(require racket/match racket/bool)
(require racket/trace)
(require "core.rkt" "core-algorithm.rkt")

(require racket/dict)

(struct Ordl (cmp-fn ft)
  #:transparent
  #:methods gen:dict
  [
    (define (dict-ref dict key
      [default (lambda () (error "key not found" key))])
      (match (ordl-query dict key) [#f (if (procedure? default) (default) default)] [(cons _ x) x]))
    (define (dict-set dict key val)
      (ordl-insert dict key val #t)
    )
    (define (dict-remove dict key)
      (match-define-values (r _) (ordl-delete dict key)) r)
    (define (dict-iterate-first dict)
      (ordl-max dict))
    (define (dict-iterate-next dict pos)
      (ordl-query-weak dict (car pos) 'lt))
    (define (dict-iterate-key dict k) (car k))
    (define (dict-iterate-value dict k) (cdr k))
  ]
)

(define ordl-core (FingerTreeWrap 
  (lambda () #f) (match-lambda [(cons k _) k]) (lambda (k0 k1) k0)
))

(define (ordl-empty? ordl)
  (match-define (Ordl _ f) ordl)
  (match f [(Empty) #t] [_ #f])
)

(define (ordl-min o)
  (match-define (Ordl _ f) o)
  (match f
    [(Empty) #f]
    [_ (hdL-view f)]
  )
)

(define (ordl-max o)
  (match-define (Ordl _ f) o)
  (match f
    [(Empty) #f]
    [_ (hdR-view f)]
  )
)

(define (ordl-min-key o)
  (match-define (Ordl _ f) o)
  (match f
    [(Single (cons k _)) k]
    [(Deep k _ _ _) k]
  )
)

(define (ordl-min-key-node node depth)
  (match depth
    [0 (car node)]
    [_ (match node
      [(or (Node2 k _ _) (Node3 k _ _ _)) k]
    )]
  )
)

(define (ordl-min-key-ft ft depth)
  (match ft
    [(Single v) (ordl-min-key-node v depth)]
    [(Deep k _ _ _) k]
  )
)

(define ordl-size-changed? (make-parameter #f))

(define (ordl-min-key-digit digit depth)
  (match digit
    [(or (One x) (Two x _) (Three x _ _) (Four x _ _ _)) (ordl-min-key-node x depth)]
  )
)

(define (ordl-query-node:impl node cmp-fn key depth)
  (match depth
    [0
      (define cmp-rst (cmp-fn (car node) key))
      (match cmp-rst
        ['eq node]
        [(or 'lt 'gt) #f]
      )
    ]
    [_
      (match node
        [(Node2 _ x0 x1)
          (define x1-key (ordl-min-key-node x1 (sub1 depth)))
          (define x1-cmp-rst (cmp-fn x1-key key))
          (match x1-cmp-rst
            [(or 'eq 'lt) (ordl-query-node:impl x1 cmp-fn key (sub1 depth))]
            ['gt (ordl-query-node:impl x0 cmp-fn key (sub1 depth))]
          )
        ]
        [(Node3 _ x0 x1 x2)
          (define x2-key (ordl-min-key-node x2 (sub1 depth)))
          (define x2-cmp-rst (cmp-fn x2-key key))
          (match x2-cmp-rst
            [(or 'eq 'lt) (ordl-query-node:impl x2 cmp-fn key (sub1 depth))]
            ['gt
              (define x1-key (ordl-min-key-node x1 (sub1 depth)))
              (define x1-cmp-rst (cmp-fn x1-key key))
              (match x1-cmp-rst
                [(or 'eq 'lt) (ordl-query-node:impl x1 cmp-fn key (sub1 depth))]
                ['gt (ordl-query-node:impl x0 cmp-fn key (sub1 depth))]
              )
            ]
          )
        ]
      )
    ]
  )
)

(define (ordl-query-ft:impl ft cmp-fn key depth)
  (match ft
    [(Empty) #f]
    [(Single node) (ordl-query-node:impl node cmp-fn key depth)]
    [(Deep _ left inner right)
      (define right-v (ordl-min-key-digit right depth))
      (define right-v-cmp-rst (cmp-fn right-v key))
      (match right-v-cmp-rst
        [(or 'eq 'lt) (ordl-query-digit:impl right cmp-fn key depth)]
        ['gt (=> f)
          (match inner [(Empty) (f)] [_ (void)])
          (define inner-v (ordl-min-key-ft inner (add1 depth)))
          (define inner-v-cmp-rst (cmp-fn inner-v key))
          (match inner-v-cmp-rst
            [(or 'eq 'lt) (ordl-query-ft:impl inner cmp-fn key (add1 depth))]
            ['gt (f)]
          )
        ]
        ['gt (ordl-query-digit:impl left cmp-fn key depth)]
      )
    ]
  )
)

(define (ordl-query-digit:impl digit cmp-fn key depth)
  (define l (reverse (digit-add-list digit '())))
  (let loop0 ([l l])
    (match l 
      [(cons lh l*)
        (define v (ordl-min-key-node lh depth))
        (define v-cmp-rst (cmp-fn v key))
        (match v-cmp-rst
          [(or 'eq 'lt) (ordl-query-node:impl lh cmp-fn key depth)]
          ['gt (loop0 l*)]
        )
      ]
      ['() #f]
    )
  )
)

(define (ordl-query o k)
  (match-define (Ordl cmp-fn ft) o)
  (ordl-query-ft:impl ft cmp-fn k 0)
)

; return node, #f / node, node2
; never in depth 0
(define (ordl-insert-node:impl node cmp-fn key value depth replace?)
  (match depth
    [1 (match node
      [(Node2 _ (and x0 (cons k0 _)) (and x1 (cons k1 _)))
        (define k1-cmp-rst (cmp-fn k1 key))
        (match k1-cmp-rst
          ['eq (if replace? (values (Node2 k0 x0 (cons key value)) #f) (values node #f))]
          ['lt (ordl-size-changed? #t) (values (Node3 k0 x0 x1 (cons key value)) #f)]
          ['gt (define k0-cmp-rst (cmp-fn k0 key))
            (match k0-cmp-rst
              ['eq (if replace? (values (Node2 key (cons key value) x1) #f) (values node #f))]
              ['lt (ordl-size-changed? #t) (values (Node3 k0 x0 (cons key value) x1) #f)]
              ['gt (ordl-size-changed? #t) (values (Node3 key (cons key value) x0 x1) #f)]
            )
          ]
        )
      ]
      [(Node3 _ (and x0 (cons k0 _)) (and x1 (cons k1 _)) (and x2 (cons k2 _)))
        (define k1-cmp-rst (cmp-fn k1 key))
        (match k1-cmp-rst
          ['eq (if replace? (values (Node3 k0 x0 (cons key value) x2) #f) (values node #f))]
          ['lt (define k2-cmp-rst (cmp-fn k2 key))
            (match k2-cmp-rst
              ['eq (if replace?
                (values (Node3 k0 x0 x1 (cons key value)) #f)
                (values node #f))]
              ['lt (ordl-size-changed? #t) (values (Node2 k0 x0 x1) (Node2 k2 x2 (cons key value)))]
              ['gt (ordl-size-changed? #t) (values (Node2 k0 x0 x1) (Node2 key (cons key value) x2))]
            )
          ]
          ['gt (define k0-cmp-rst (cmp-fn k0 key))
            (match k0-cmp-rst
              ['eq (if replace? 
                (values (Node3 key (cons key value) x1 x2) #f)
                (values node #f))]
              ['lt (ordl-size-changed? #t) (values (Node2 k0 x0 (cons key value)) (Node2 k1 x1 x2))]
              ['gt (ordl-size-changed? #t) (values (Node2 key (cons key value) x0) (Node2 k1 x1 x2))]
            )
          ]
        )
      ]
    )]
    [_ (match node
      [(Node2 k0 x0 x1)
        (define k1 (ordl-min-key-node x1 (sub1 depth)))
        (match (cmp-fn k1 key)
          [(or 'eq 'lt) (define-values (node0 node1)
            (ordl-insert-node:impl x1 cmp-fn key value (sub1 depth) replace?))
            (cond
              [(and (eq? x1 node0) (not node1)) (values node #f)]
              [node1 (values (Node3 k0 x0 node0 node1) #f)]
              [(not node1) (values (Node2 k0 x0 node0) #f)])
          ]
          ['gt (define-values (node0 node1)
            (ordl-insert-node:impl x0 cmp-fn key value (sub1 depth) replace?))
            (cond
              [(and (eq? x0 node0) (not node1)) (values node #f)]
              [node1 (values (Node3 k0 node0 node1 x1) #f)]
              [(not node1) (values (Node2 k0 node0 x1) #f)])
          ]
        )
      ]
      [(Node3 k0 x0 x1 x2)
        (define k1 (ordl-min-key-node x1 (sub1 depth)))
        (match (cmp-fn k1 key)
          ['lt
            (define k2 (ordl-min-key-node x2 (sub1 depth)))
            (match (cmp-fn k2 key)
              [(or 'lt 'eq) (define-values (node0 node1)
                (ordl-insert-node:impl x2 cmp-fn key value (sub1 depth) replace?))
                (cond
                  [(and (eq? x2 node0) (not node1)) (values node #f)]
                  [node1 (values 
                    (Node2 k0 x0 x1)
                    (Node2 (ordl-min-key-node node0 (sub1 depth)) node0 node1))]
                  [(not node1)
                    (values (Node3 k0 x0 x1 node0) #f)]
                )
              ]
              ['gt (define-values (node0 node1)
                (ordl-insert-node:impl x1 cmp-fn key value (sub1 depth) replace?))
                (cond
                  [(and (eq? x1 node0) (not node1)) (values node #f)]
                  [node1 (values 
                    (Node2 k0 x0 node0)
                    (Node2 (ordl-min-key-node node1 (sub1 depth)) node1 x2))]
                  [(not node1)
                    (values (Node3 k0 x0 node0 x2) #f)]
                )
              ]
            )
          ]
          ['eq (define-values (node0 node1)
            (ordl-insert-node:impl x1 cmp-fn key value (sub1 depth) replace?))
            (cond
              [(and (eq? x1 node0) (not node1)) (values node #f)]
              [node1 (values 
                (Node2 k0 x0 node0)
                (Node2 (ordl-min-key-node node1 (sub1 depth)) node1 x2))]
              [(not node1)
                (values (Node3 k0 x0 node0 x2) #f)]
            )
          ]
          ['gt (define-values (node0 node1)
            (ordl-insert-node:impl x0 cmp-fn key value (sub1 depth) replace?))
            (cond
              [(and (eq? x0 node0) (not node1)) (values node #f)]
              [node1 (values 
                (Node2 k0 node0 node1)
                (Node2 k1 x1 x2))]
              [(not node1)
                (values (Node3 k0 node0 x1 x2) #f)]
            )
          ]
        )
      ]
    )]
  )
)

; return ft
(define (ordl-insert-ft:impl ft cmp-fn key value depth replace?)
  (match ft
    [(Single x)
      (match depth
        [0 (match-define (cons k0 _) x)
          (match (cmp-fn k0 key)
            ['lt (ordl-size-changed? #t) (Deep k0 (One x) (Empty) (One (cons key value)))]
            ['eq (if replace? (Single (cons key value)) ft)]
            ['gt (ordl-size-changed? #t) (Deep key (One (cons key value)) (Empty) (One x))]
          )
        ]
        [_
          (define-values (node0 node1) (ordl-insert-node:impl x cmp-fn key value depth replace?))
          (cond
            [(and (eq? x node0) (not node1)) ft]
            [node1 (Deep (ordl-min-key-node node0 depth) (One node0) (Empty) (One node1))]
            [(not node1) (Single node0)]
          )
        ]
      )
    ]
    [(Deep o left inner right)
      (define right-v (ordl-min-key-digit right depth))
      (match (cmp-fn right-v key)
        [(or 'lt 'eq)
          (define right^ (ordl-insert-digit:impl right cmp-fn key value depth replace?))
          (cond
            [(eq? right^ right) ft]
            [else
              (match right^
                [`(,x0 ,x1 ,x2 ,x3 ,x4)
                  (define right^^ (Two x3 x4))
                  (define node0 (Node3 (ordl-min-key-node x0 depth) x0 x1 x2))
                  (define inner^ (consR:impl ordl-core inner node0 (add1 depth)))
                  (Deep o left inner^ right^^)
                ]
                [r
                  (define right^^ (list->digit r depth))
                  (Deep o left inner right^^)
                ]
              )
            ]
          )
        ]
        ['gt 
          (match inner
            [(Empty) (define left^ 
              (ordl-insert-digit:impl left cmp-fn key value depth replace?))
              (cond
                [(eq? left left^) ft]
                [else
                  (match left^
                    [`(,x0 ,x1 ,x2 ,x3 ,x4)
                      (define left^^ (Two x0 x1))
                      (define node0 (Node3 (ordl-min-key-node x2 depth) x2 x3 x4))
                      (define inner^ (consL:impl ordl-core inner node0 (add1 depth)))
                      (Deep o left^^ inner^ right)
                    ]
                    [l
                      (define left^^ (list->digit l depth))
                      (Deep o left^^ inner right)
                    ]
                  )
                ]
              )
            ]
            [_
              (define inner-v (ordl-min-key-ft inner (add1 depth)))
              (match (cmp-fn inner-v key)
                [(or 'lt 'eq)
                  (define inner^ (ordl-insert-ft:impl inner cmp-fn key value (add1 depth) replace?))
                  (if (eq? inner inner^) ft (Deep o left inner^ right))
                ]
                ['gt
                  (define left^ 
                  (ordl-insert-digit:impl left cmp-fn key value depth replace?))
                  (cond
                    [(eq? left left^) ft]
                    [else
                      (match left^
                        [`(,x0 ,x1 ,x2 ,x3 ,x4)
                          (define left^^ (Two x0 x1))
                          (define node0 (Node3 (ordl-min-key-node x2 depth) x2 x3 x4))
                          (define inner^ (consL:impl ordl-core inner node0 (add1 depth)))
                          (Deep o left^^ inner^ right)
                        ]
                        [l
                          (define left^^ (list->digit l depth))
                          (Deep o left^^ inner right)
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
(define (ordl-insert-digit:impl digit cmp-fn key value depth replace?)
  (define kv (cons key value))
  (match depth
    [0
      (match digit
        [(One (and x0 (cons k0 _)))
          (match (cmp-fn k0 key)
            ['lt (ordl-size-changed? #t) (list x0 kv)]
            ['eq (if replace? (list kv) digit)]
          )
        ]
        [(Two (and x0 (cons k0 _)) (and x1 (cons k1 _)))
          (match (cmp-fn k1 key)
            ['lt (ordl-size-changed? #t) (list x0 x1 kv)]
            ['eq (if replace? (list x0 kv) digit)]
            ['gt 
              (match (cmp-fn k0 key)
                ['lt (ordl-size-changed? #t) (list x0 kv x1)]
                ['eq (if replace? (list kv x1) digit)]
              )]
          )
        ]
        [(Three (and x0 (cons k0 _)) (and x1 (cons k1 _)) (and x2 (cons k2 _)))
          (match (cmp-fn k1 key)
            ['lt 
              (match (cmp-fn k2 key)
                ['lt (ordl-size-changed? #t) (list x0 x1 x2 kv)]
                ['eq (if replace? (list x0 x1 kv) digit)]
                ['gt (ordl-size-changed? #t) (list x0 x1 kv x2)]
              )]
            ['eq (if replace? (list x0 kv x2) digit)]
            ['gt
              (match (cmp-fn k0 key)
                ['lt (ordl-size-changed? #t) (list x0 kv x1 x2)]
                ['eq (if replace? (list kv x1 x2) digit)]
              )]
          )
        ]
        [(Four (and x0 (cons k0 _)) (and x1 (cons k1 _)) (and x2 (cons k2 _)) (and x3 (cons k3 _)))
          (match (cmp-fn k2 key)
            ['lt 
              (match (cmp-fn k3 key)
                ['lt (ordl-size-changed? #t) (list x0 x1 x2 x3 kv)]
                ['eq (if replace? (list x0 x1 x2 kv) digit)]
                ['gt (ordl-size-changed? #t) (list x0 x1 x2 kv x3)]
              )]
            ['eq (if replace? (list x0 x1 kv x3) digit)]
            ['gt 
              (match (cmp-fn k1 key)
                ['lt (ordl-size-changed? #t) (list x0 x1 kv x2 x3)]
                ['eq (if replace? (list x0 kv x2 x3) digit)]
                ['gt
                  (match (cmp-fn k0 key)
                    ['lt (ordl-size-changed? #t) (list x0 kv x1 x2 x3)]
                    ['eq (if replace? (list kv x1 x2 x3) digit)]
                  )]
              )]
          )
        ]
      )
    ]
    [_
      (match digit
        [(One x0)
          (define-values (node0 node1) (ordl-insert-node:impl x0 cmp-fn key value depth replace?))
          (cond
            [(and (eq? node0 x0) (not node1)) digit]
            [node1 (list node0 node1)]
            [(not node1) (list node0)]
          )
        ]
        [(Two x0 x1)
          (define k1 (ordl-min-key-node x1 depth))
          (match (cmp-fn k1 key)
            [(or 'lt 'eq)
              (define-values (node0 node1) (ordl-insert-node:impl x1 cmp-fn key value depth replace?))
              (cond
                [(and (eq? x1 node0) (not node1)) digit]
                [node1 (list x0 node0 node1)]
                [(not node1) (list x0 node0)]
              )
            ]
            ['gt 
              (define-values (node0 node1) (ordl-insert-node:impl x0 cmp-fn key value depth replace?))
              (cond
                [(and (eq? x0 node0) (not node1)) digit]
                [node1 (list node0 node1 x1)]
                [(not node1) (list node0 x1)]
              )
            ]
          )
        ]
        [(Three x0 x1 x2)
          (define k1 (ordl-min-key-node x1 depth))
          (match (cmp-fn k1 key)
            ['lt (=> f)
              (match (cmp-fn (ordl-min-key-node x2 depth) key)
                [(or 'lt 'eq) 
                  (define-values (node0 node1) (ordl-insert-node:impl x2 cmp-fn key value depth replace?))
                  (cond
                    [(and (eq? x2 node0) (not node1)) digit]
                    [node1 (list x0 x1 node0 node1)]
                    [(not node1) (list x0 x1 node0)]
                  )
                ]
                ['gt (f)]
              )
            ]
            [(or 'lt 'eq)
              (define-values (node0 node1) (ordl-insert-node:impl x1 cmp-fn key value depth replace?))
              (cond
                [(and (eq? x1 node0) (not node1)) digit]
                [node1 (list x0 node0 node1 x2)]
                [(not node1) (list x0 node0 x2)]
              )
            ]
            ['gt 
              (define-values (node0 node1) (ordl-insert-node:impl x0 cmp-fn key value depth replace?))
              (cond
                [(and (eq? x0 node0) (not node1)) digit]
                [node1 (list node0 node1 x1)]
                [(not node1) (list node0 x1)]
              )
            ]
          )
        ]
        [(Four x0 x1 x2 x3)
          (match (cmp-fn (ordl-min-key-node x2 depth) key)
            ['lt (=> f)
              (match (cmp-fn (ordl-min-key-node x3 depth) key)
                [(or 'lt 'eq) 
                  (define-values (node0 node1) (ordl-insert-node:impl x3 cmp-fn key value depth replace?))
                  (cond
                    [(and (eq? x3 node0) (not node1)) digit]
                    [node1 (list x0 x1 x2 node0 node1)]
                    [(not node1) (list x0 x1 x2 node0)]
                  )
                ]
                ['gt (f)]
              )
            ]
            [(or 'lt 'eq)
              (define-values (node0 node1) (ordl-insert-node:impl x2 cmp-fn key value depth replace?))
              (cond
                [(and (eq? x2 node0) (not node1)) digit]
                [node1 (list x0 x1 node0 node1 x3)]
                [(not node1) (list x0 x1 node0 x3)]
              )
            ]
            ['gt
              (match (cmp-fn (ordl-min-key-node x1 depth) key)
                [(or 'lt 'eq)
                  (define-values (node0 node1) 
                    (ordl-insert-node:impl x1 cmp-fn key value depth replace?))
                  (cond
                    [(and (eq? x1 node0) (not node1)) digit]
                    [node1 (list x0 node0 node1 x2 x3)]
                    [(not node1) (list x0 node0 x2 x3)]
                  )
                ]
                ['gt
                  (define-values (node0 node1)
                    (ordl-insert-node:impl x0 cmp-fn key value depth replace?))
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

(define (ordl-insert-ft-wrap ft cmp-fn key value replace?)
  (match ft
    [(Empty) (ordl-size-changed? #t) (Single (cons key value))]
    [(Single _) (ordl-insert-ft:impl ft cmp-fn key value 0 replace?)]
    [(Deep o _ _ _)
      (match (cmp-fn o key)
        [(or 'lt 'eq) (ordl-insert-ft:impl ft cmp-fn key value 0 replace?)]
        ['gt (ordl-size-changed? #t) (consL:impl ordl-core ft (cons key value) 0)]
      )
    ]
  )
)

(define (ordl-insert ordl key value replace?)
  (match-define (Ordl cmp-fn k) ordl)
  (define k^ (ordl-insert-ft-wrap k cmp-fn key value replace?))
  (cond
    [(eq? k k^) ordl]
    [else (Ordl cmp-fn k^)]
  )
)

; node, sub-node, del
(define (ordl-delete-node:impl node cmp-fn key depth)
  (match depth
    [1 (match node
      [(Node2 _ (and x0 (cons k0 _)) (and x1 (cons k1 _)))
        (match (cmp-fn k1 key)
          ['eq (values #f x0 x1)]
          ['lt (values node #f #f)]
          ['gt (match (cmp-fn k0 key)
            ['eq (values #f x1 x0)]
            ['lt (values node #f #f)]
          )]
        )
      ]
      [(Node3 _ (and x0 (cons k0 _)) (and x1 (cons k1 _)) (and x2 (cons k2 _)))
        (match (cmp-fn k1 key)
          ['eq (values (Node2 k0 x0 x2) #f x1)]
          ['lt (match (cmp-fn k2 key)
            ['eq (values (Node2 k0 x0 x1) #f x2)]
            [(or 'lt 'gt) (values node #f #f)]
          )]
          ['gt (match (cmp-fn k0 key)
            ['eq (values (Node2 k1 x1 x2) #f x0)]
            ['lt (values node #f #f)]
          )]
        )
      ]
    )]
    [_ (match node
      [(Node2 k0 x0 x1)
        (match (cmp-fn (ordl-min-key-node x1 depth) key)
          [(or 'eq 'lt)
            (define-values (node0 subnode ret) (ordl-delete-node:impl x1 cmp-fn key (sub1 depth)))
            (match* (node0 subnode)
              [(_ #f) (if (eq? x1 node0) (values node #f ret) (values (Node2 k0 x0 node0) #f ret))]
              [(#f _) (match x0
                [(Node2 _ x00 x01)
                  (define subnode^ (Node3 k0 x00 x01 subnode))
                  (values #f subnode^ ret)
                ]
                [(Node3 _ x00 x01 x02)
                  (define node^ (Node2 k0 (Node2 k0 x00 x01) (Node2 (ordl-min-key-node x02 (- depth 2)) x02 subnode)))
                  (values node^ #f ret)
                ]
              )]
            )
          ]
          ['gt
            (define-values (node0 subnode ret) (ordl-delete-node:impl x0 cmp-fn key (sub1 depth)))
            (match* (node0 subnode)
              [(_ #f) (if (eq? x0 node0) (values node #f ret) 
                (values (Node2 (ordl-min-key-node node0 (sub1 depth)) node0 x1) #f ret))]
              [(#f _) (match x1
                [(Node2 _ x10 x11)
                  (define subnode^ (Node3 (ordl-min-key-node subnode (- depth 2)) subnode x10 x11))
                  (values #f subnode^ ret)
                ]
                [(Node3 _ x10 x11 x12)
                  (define k0^ (ordl-min-key-node subnode (- depth 2)))
                  (define node^ (Node2 k0^ 
                    (Node2 k0^ subnode x10) (Node2 (ordl-min-key-node x11 (- depth 2)) x11 x12)))
                  (values node^ #f ret)
                ]
              )]
            )
          ]
        )
      ]
      [(Node3 k0 x0 x1 x2)
        (match (cmp-fn (ordl-min-key-node x1 depth) key)
          ['lt (=> h)
            (match (cmp-fn (ordl-min-key-node x2 depth) key)
              [(or 'lt 'eq)
                (define-values (node0 subnode ret) (ordl-delete-node:impl x2 cmp-fn key (sub1 depth)))
                (match* (node0 subnode)
                  [(_ #f) (if (eq? x2 node0) (values node #f ret) (values (Node3 k0 x0 x1 node0) #f ret))]
                  [(#f _) (match x1
                    [(Node2 _ x10 x11)
                      (define node0^ (Node3 (ordl-min-key-node x10 (- depth 2)) x10 x11 subnode))
                      (values (Node2 k0 x0 node0^) #f ret)
                    ]
                    [(Node3 _ x10 x11 x12)
                      (define node^ (Node3 k0 x0 (Node2 (ordl-min-key-node x10 (- depth 2)) x10 x11) 
                        (Node2 (ordl-min-key-node x12 (- depth 2)) x12 subnode)))
                      (values node^ #f ret)
                    ]
                  )]
                )
              ]
              ['gt (h)]
            )
          ]
          [(or 'lt 'eq)
            (define-values (node0 subnode ret) (ordl-delete-node:impl x1 cmp-fn key (sub1 depth)))
            (match* (node0 subnode)
              [(_ #f) (if (eq? x1 node0) (values node #f ret) (values (Node3 k0 x0 node0 x2) #f ret))]
              [(#f _) (match x2
                [(Node2 _ x20 x21)
                  (define node0^ (Node3 (ordl-min-key-node subnode (- depth 2)) subnode x20 x21))
                  (values (Node2 k0 x0 node0^) #f ret)
                ]
                [(Node3 _ x20 x21 x22)
                  (define node^ (Node3 k0 x0 (Node2 (ordl-min-key-node subnode (- depth 2)) subnode x20) 
                    (Node2 (ordl-min-key-node x21 (- depth 2)) x21 x22)))
                  (values node^ #f ret)
                ]
              )]
            )
          ]
          ['gt
            (define-values (node0 subnode ret) (ordl-delete-node:impl x0 cmp-fn key (sub1 depth)))
            (match* (node0 subnode)
              [(_ #f) (if (eq? x0 node0) (values node #f ret) 
                (values (Node3 (ordl-min-key-node node0 (sub1 depth)) node0 x1 x2) #f ret))]
              [(#f _) (match x1
                [(Node2 _ x10 x11)
                  (define subnode^ (Node3 (ordl-min-key-node subnode (- depth 2)) subnode x10 x11))
                  (values (Node2 (ordl-min-key-node subnode^ (sub1 depth)) subnode^ x2) #f ret)
                ]
                [(Node3 _ x10 x11 x12)
                  (define k0^ (ordl-min-key-node subnode (- depth 2)))
                  (define node^ (Node3 k0^ 
                    (Node2 k0^ subnode x10) (Node2 (ordl-min-key-node x11 (- depth 2)) x11 x12) x2))
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

(define (ordl-node-mergeR node subnode depth)
  (match node
    [(Node2 o x0 x1)
      (values (Node3 o x0 x1 subnode) #f)
    ]
    [(Node3 o x0 x1 x2)
      (values (Node2 o x0 x1) (Node2 (ordl-min-key-node x2 (sub1 depth)) x2 subnode))
    ]
  )
)

(define (ordl-node-mergeL node subnode depth)
  (match node
    [(Node2 _ x0 x1) (values (Node3 (ordl-min-key-node subnode (sub1 depth)) subnode x0 x1) #f)]
    [(Node3 _ x0 x1 x2) (values 
      (Node2 (ordl-min-key-node subnode (sub1 depth)) subnode x0)
      (Node2 (ordl-min-key-node x1 (sub1 depth) x1 x2))
      )]
  )
)

; ordl-delete-node:impl
; list, subnode, ret
(define (ordl-delete-digit:impl digit cmp-fn key depth)
  (match depth
    [0 (match digit
      [(One (and x0 (cons k0 _))) 
        (match (cmp-fn k0 key)
          ['lt (values digit #f #f)]
          ['eq (values '() #f x0)]
        )
      ]
      [(Two (and x0 (cons k0 _)) (and x1 (cons k1 _)))
        (match (cmp-fn k1 key)
          ['lt (values digit #f #f)]
          ['eq (values (list x0) #f x1)]
          ['gt (match (cmp-fn k0 key)
            ['lt (values digit #f #f)]
            ['eq (values (list x1) #f x0)]
          )]
        )
      ]
      [(Three (and x0 (cons k0 _)) (and x1 (cons k1 _)) (and x2 (cons k2 _)))
        (match (cmp-fn k1 key)
          ['lt (match (cmp-fn k2 key)
            [(or 'lt 'gt) (values digit #f #f)]
            ['eq (values (list x0 x1) #f x2)]
          )]
          ['eq (values (list x0 x2) #f x1)]
          ['gt (match (cmp-fn k0 key)
            ['lt (values digit #f #f)]
            ['eq (values (list x1 x2) #f x0)]
          )]
        )
      ]
      [(Four (and x0 (cons k0 _)) (and x1 (cons k1 _)) (and x2 (cons k2 _)) (and x3 (cons k3 _)))
        (match (cmp-fn k2 key)
          ['lt (match (cmp-fn k3 key)
            [(or 'lt 'gt) (values digit #f #f)]
            ['eq (values (list x0 x1 x2) #f x3)]
          )]
          ['eq (values (list x0 x1 x3) #f x2)]
          ['gt (match (cmp-fn k1 key)
            ['lt (values digit #f #f)]
            ['eq (values (list x0 x2 x3) #f x1)]
            ['gt (match (cmp-fn k0 key)
              ['lt (values digit #f #f)]
              ['eq (values (list x1 x2 x3) #f x0)]
            )]
          )]
        )
      ]
    )]
    [_ (match digit
      [(One x0) (define-values (node0 subnode ret) (ordl-delete-node:impl x0 cmp-fn key depth))
        (cond
          [(eq? x0 node0) (values digit #f ret)]
          [node0 (values (list node0) #f ret)]
          [subnode (values '() subnode ret)]
        )
      ]
      [(Two x0 x1)
        (match (cmp-fn (ordl-min-key-node x1 depth) key)
          [(or 'lt 'eq) (define-values (node0 subnode ret) (ordl-delete-node:impl x1 cmp-fn key depth))
            (cond
              [(eq? x1 node0) (values digit #f ret)]
              [node0 (values (list x0 node0) #f ret)]
              [subnode 
                (define-values (x0^ x1^) (ordl-node-mergeR x0 subnode depth))
                (values (if x1^ (list x0^ x1^) (list x0^)) #f ret)
              ]
            )
          ]
          ['gt (define-values (node0 subnode ret) (ordl-delete-node:impl x0 cmp-fn key depth))
            (cond
              [(eq? x0 node0) (values digit #f ret)]
              [node0 (values (list node0 x1) #f ret)]
              [subnode
                (define-values (x0^ x1^) (ordl-node-mergeL x1 subnode depth))
                (values (if x1^ (list x0^ x1^) (list x0^)) #f ret)
              ]
            )
          ]
        )
      ]
      [(Three x0 x1 x2)
        (match (cmp-fn (ordl-min-key-node x1 depth) key)
          ['lt (=> f)
            (match (cmp-fn (ordl-min-key-node x2 depth) key)
              [(or 'lt 'eq)
                (define-values (node0 subnode ret) (ordl-delete-node:impl x2 cmp-fn key depth))
                (cond
                  [(eq? x2 node0) (values digit #f ret)]
                  [node0 (values (list x0 x1 node0) #f ret)]
                  [subnode (define-values (x1^ x2^) (ordl-node-mergeR x1 subnode depth))
                    (values (if x2^ (list x0 x1^ x2^) (list x0 x1^)) #f ret)
                  ]
                )
              ]
              ['gt (f)]
            )
          ]
          [(or 'lt 'eq)
            (define-values (node0 subnode ret) (ordl-delete-node:impl x1 cmp-fn key depth))
            (cond
              [(eq? x1 node0) (values digit #f ret)]
              [node0 (values (list x0 node0 x2) #f ret)]
              [subnode (define-values (x0^ x1^) (ordl-node-mergeR x0 subnode depth))
                (values (if x1^ (list x0^ x1^ x2) (list x0^ x2)) #f ret)
              ]
            )
          ]
          ['gt (define-values (node0 subnode ret) (ordl-delete-node:impl x0 cmp-fn key depth))
            (cond
              [(eq? x0 node0) (values digit #f ret)]
              [node0 (values (list node0 x1 x2) #f ret)]
              [subnode
                (define-values (x0^ x1^) (ordl-node-mergeL x1 subnode depth))
                (values (if x1^ (list x0^ x1^ x2) (list x0^ x2)) #f ret)
              ]
            )
          ]
        )
      ]
      [(Four x0 x1 x2 x3)
        (match (cmp-fn (ordl-min-key-node x2 depth) key)
          ['lt (=> f)
            (match (cmp-fn (ordl-min-key-node x3 depth) key)
              [(or 'lt 'eq)
                (define-values (node0 subnode ret) (ordl-delete-node:impl x3 cmp-fn key depth))
                (cond
                  [(eq? x3 node0) (values digit #f ret)]
                  [node0 (values (list x0 x1 x2 node0) #f ret)]
                  [subnode (define-values (x2^ x3^) (ordl-node-mergeR x2 subnode depth))
                    (values (if x3^ (list x0 x1 x2^ x3^) (list x0 x1 x2^)) #f ret)
                  ]
                )
              ]
              ['gt (f)]
            )
          ]
          [(or 'lt 'eq)
            (define-values (node0 subnode ret) (ordl-delete-node:impl x2 cmp-fn key depth))
            (cond
              [(eq? x2 node0) (values digit #f ret)]
              [node0 (values (list x0 x1 node0 x3) #f ret)]
              [subnode (define-values (x1^ x2^) (ordl-node-mergeR x1 subnode depth))
                (values (if x2^ (list x0 x1^ x2^ x3) (list x0 x1^ x3)) #f ret)
              ]
            )
          ]
          ['gt (match (cmp-fn (ordl-min-key-node x1 depth) key)
            [(or 'lt 'eq)
              (define-values (node0 subnode ret) (ordl-delete-node:impl x0 cmp-fn key depth))
              (cond
                [(eq? x1 node0) (values digit #f ret)]
                [node0 (values (list x0 node0 x2 x3) #f ret)]
                [subnode
                  (define-values (x0^ x1^) (ordl-node-mergeR x0 subnode depth))
                  (values (if x1^ (list x0^ x1^ x2 x3) (list x0^ x2 x3)) #f ret)
                ]
              )
            ]
            ['gt
              (define-values (node0 subnode ret) (ordl-delete-node:impl x0 cmp-fn key depth))
              (cond
                [(eq? x0 node0) (values digit #f ret)]
                [node0 (values (list node0 x1 x2 x3) #f ret)]
                [subnode
                  (define-values (x0^ x1^) (ordl-node-mergeL x1 subnode depth))
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
    [(Empty)
      (match left
        [(One x0)
          (define-values (r0 r1) (ordl-node-mergeR x0 subright depth))
          (if r1 (Deep o (One r0) (Empty) (One r1)) (Single r0))
        ]
        [(Two x0 x1)
          (define-values (r0 r1) (ordl-node-mergeR x1 subright depth))
          (Deep o (One x0) (Empty) (if r1 (Two r0 r1) (One r0)))
        ]
        [(Three x0 x1 x2)
          (define-values (r0 r1) (ordl-node-mergeR x2 subright depth))
          (Deep o (Two x0 x1) (Empty) (if r1 (Two r0 r1) (One r0)))
        ]
        [(Four x0 x1 x2 x3)
          (define-values (r0 r1) (ordl-node-mergeR x3 subright depth))
          (Deep o (Three x0 x1 x2) (Empty) (if r1 (Two r0 r1) (One r0)))
        ]
      )
    ]
    [_ 
      (define-values (r inner^) (hdR:impl ordl-core inner (add1 depth)))
      (define-values (r0 r1) (ordl-node-mergeR r subright depth))
      (Deep o left inner^ (if r1 (Two r0 r1) (One r0)))
    ]
  )
)

(define (right-inner-mergeL right inner subleft depth)
  (match inner
    [(Empty)
      (match right
        [(One x0)
          (define-values (r0 r1) (ordl-node-mergeL x0 subleft depth))
          (if r1 (Deep (ordl-min-key-node r0 depth) (One r0) (Empty) (One r1)) (Single r0))
        ]
        [(Two x0 x1)
          (define-values (r0 r1) (ordl-node-mergeL x0 subleft depth))
          (Deep (ordl-min-key-node r0 depth) (if r1 (Two r0 r1) (One r0)) (Empty) (One x1))
        ]
        [(Three x0 x1 x2)
          (define-values (r0 r1) (ordl-node-mergeL x0 subleft depth))
          (Deep (ordl-min-key-node r0 depth) (if r1 (Two r0 r1) (One r0)) (Empty) (Two x1 x2))
        ]
        [(Four x0 x1 x2 x3)
          (define-values (r0 r1) (ordl-node-mergeL x0 subleft depth))
          (Deep (ordl-min-key-node r0 depth) (if r1 (Two r0 r1) (One r0)) (Empty) (Three x1 x2 x3))
        ]
      )
    ]
    [_ 
      (define-values (l inner^) (hdL:impl ordl-core inner (add1 depth)))
      (define-values (r0 r1) (ordl-node-mergeL l subleft depth))
      (Deep (ordl-min-key-node r0 depth) (if r1 (Two r0 r1) (One r0)) inner^ right)
    ]
  )
)

; ft, subnode, rst
(define (ordl-delete-ft:impl ft cmp-fn key depth)
  (match ft
    [(Deep o left inner right)
      (define right-v (ordl-min-key-digit right depth))
      (match (cmp-fn right-v key)
        [(or 'lt 'eq)
          (match-define-values (right^ subright ret) (ordl-delete-digit:impl right cmp-fn key depth))
          (cond
            [(eq? right right^) (values ft #f ret)]
            [right^ (define right^^ (list->digit right^ depth)) 
              (values (Deep o left inner right^^) #f ret)]
            [subright
              (define ft^ (left-inner-mergeR left inner subright o depth))
              (values ft^ #f ret)
            ]
          )
        ]
        ['gt (=> h)
          (match inner
            [(Empty) (h)]
            [_ (define inner-v (ordl-min-key-ft inner (add1 depth)))
              (match (cmp-fn inner-v key)
                [(or 'lt 'eq)
                  (match-define-values (inner^ subinner ret) (ordl-delete-ft:impl inner cmp-fn key (add1 depth)))
                  (cond
                    [(eq? inner inner^) (values ft #f ret)]
                    [inner^ (values (Deep o left inner^ right) #f ret)]
                    [subinner (begin
                      (match* (left right)
                        [((Four x0 x1 x2 x3) (Four _ _ _ _))
                          (define node0 (Node3 (ordl-min-key-node x2 depth) x2 x3 subinner))
                          (define left^ (Two x0 x1))
                          (Deep o left^ (Single node0) right)
                        ]
                        [((Four _ _ _ _) _)
                          (define right^ (match right
                            [(One x) (Two subinner x)]
                            [(Two x0 x1) (Three subinner x0 x1)]
                            [(Three x0 x1 x2) (Four subinner x0 x1 x2)]
                          ))
                          (Deep o left (Empty) right^)
                        ]
                        [(_ _)
                          (define left^ (match left
                            [(One x) (Two x subinner)]
                            [(Two x0 x1) (Three x0 x1 subinner)]
                            [(Three x0 x1 x2) (Four x0 x1 x2 subinner)]
                          ))
                          (Deep o left^ (Empty) right)
                        ]
                      )
                    )]
                  )
                ]
                ['gt (h)]
              )
            ]
          )
        ]
        ['gt
          (match-define-values (left^ subleft ret) (ordl-delete-digit:impl left cmp-fn key depth))
          (cond
            [(eq? left left^) (values ft #f ret)]
            [left^ (define left^^ (list->digit left^ depth))
              (values (Deep (ordl-min-key-digit left^^ depth) left^^ inner right) #f ret)
            ]
            [subleft
              (define ft^ (right-inner-mergeL right inner subleft depth))
              (values ft^ #f ret)
            ]
          )
        ]
      )
    ]
    [(Single (and x (cons k _)))
      (match depth
        [0
          (match (cmp-fn k key)
            ['eq (values (Empty) #f x)]
            ['lt (values ft #f #f)]
          )
        ]
        [_
          (match-define-values (node0 subnode ret) (ordl-delete-node:impl x cmp-fn key depth))
          (cond
            [(eq? x node0) (values ft #f ret)]
            [node0 (values (Single node0) #f ret)]
            [subnode (values #f subnode ret)]
          )
        ]
      )
    ]
  )
)

(define (ordl-delete-ft-wrap ft cmp-fn key)
  (match ft
    [(Empty) (values ft #f)]
    [(Single _) (match-define-values (ft^ _ ret) (ordl-delete-ft:impl ft cmp-fn key 0)) (values ft^ ret)]
    [(Deep o _ _ _) (match (cmp-fn o key)
      [(or 'lt 'eq) 
        (match-define-values (ft^ _ ret) (ordl-delete-ft:impl ft cmp-fn key 0))
        (values ft^ ret)]
      ['gt (values ft #f)]
    )]
  )
)

(define (ordl-delete ft key)
  (match-define (Ordl cmp-fn ft^) ft)
  (match-define-values (ft^^ ret) (ordl-delete-ft-wrap ft^ cmp-fn key))
  (values (if (eq? ft^ ft^^) ft (Ordl cmp-fn ft^^)) ret)
)

(define (integer-compare x0 x1)
  (cond
    [(< x0 x1) 'lt]
    [(= x0 x1) 'eq]
    [(> x0 x1) 'gt]
  )
)

(define (symbol-compare x0 x1)
  (cond
    [(symbol<? x0 x1) 'lt]
    [(symbol=? x0 x1) 'eq]
    [(symbol<? x1 x0) 'gt]
    [else (assert-unreachable)]
  )
)

(define (make-ordl-empty cmp-fn)
  (Ordl cmp-fn (Empty))
)

(define (ordl-make-empty cmp-fn) (Ordl cmp-fn (Empty)))

(define (make-empty-ordl cmp-fn) (Ordl cmp-fn (Empty)))

(define (test6)
  (define ordl (make-ordl-empty symbol-compare))
  (define append '((name . "Code - Insiders") (publish . 2025) (Window . 1.0)))
  (for ([a append])
    (set! ordl (ordl-insert ordl (car a) (cdr a) #f))
  )
  (define append2 '((name . "UE5") (publish . 2024)))
  (displayln ordl)
  (for ([a append2])
    (set! ordl (ordl-insert ordl (car a) (cdr a) #f))
  )
  (displayln ordl)
  (for ([a append2])
    (set! ordl (ordl-insert ordl (car a) (cdr a) #t))
  )
  (define append3 '((Help . "Help") (View . Window) (Go . "Back")))
  (for ([a append3])
    (set! ordl (ordl-insert ordl (car a) (cdr a) #f))
  )
  (displayln ordl)
)

(define (test7)
  (define ordl (make-ordl-empty integer-compare))
  (for ([i (in-range 1000)])
    (set! ordl (ordl-insert ordl i (* i i) #f))
  )
  ordl
)



(module+ test
  (require rackunit)
)

(module+ test
  (define int-ordl0 (make-empty-ordl integer-compare))
  (check-equal? (ordl-query int-ordl0 0) #f "Query [Empty] 0 = #f")
)

(module+ test
  (define int-ordl1 (make-empty-ordl integer-compare))
  (set! int-ordl1 (ordl-insert int-ordl1 0 0 #t))
  (check-equal? (ordl-query int-ordl1 0) (cons 0 0) "Query [(0, 0)] 0 = (0, 0)")
)

(module+ test
  (define int-ordl2 (make-empty-ordl integer-compare))
  (set! int-ordl2 (ordl-insert int-ordl2 0 "int" #f))
  (set! int-ordl2 (ordl-insert int-ordl2 0 "float" #f))
  (check-equal? (ordl-query int-ordl2 0) (cons 0 "int") "Query [(0, int)] 0 = (0, int)")
)

(module+ test
  (define int-ordl3 (make-empty-ordl integer-compare))
  (set! int-ordl3 (ordl-insert int-ordl3 0 "int" #f))
  (define int-ordl3-back int-ordl3)
  (set! int-ordl3 (ordl-insert int-ordl3 0 "float" #f))
  (check-eq? int-ordl3-back int-ordl3 "Insert [(0, int)] (0 float) = ignored")
)

(module+ test
  (define int-ordl4 (make-empty-ordl integer-compare))
  (set! int-ordl4 (ordl-insert int-ordl4 0 "int" #t))
  (define int-ordl4-back int-ordl4)
  (set! int-ordl4 (ordl-insert int-ordl4 0 "float" #t))
  (check-not-eq? int-ordl4-back int-ordl4 "Insert! [(0, int)] (0 double) = [(0, double)]")
)

(module+ test
  (define int-ordl5 (make-empty-ordl integer-compare))
  (set! int-ordl5 (ordl-insert int-ordl5 0 "int" #t))
  (set! int-ordl5 (ordl-insert int-ordl5 1 "float" #t))
  (check-equal? (ordl-query int-ordl5 0) (cons 0 "int"))
  (check-equal? (ordl-query int-ordl5 1) (cons 1 "float"))
)

(module+ test
  (define int-ordl6 (make-empty-ordl integer-compare))
  (set! int-ordl6 (for/fold ([io int-ordl6]) ([i (in-range 10)])
    (ordl-insert io i (add1 i) #f)
  ))
  (check-equal? (ordl-query int-ordl6 7) (cons 7 8))
  (check-equal? (ordl-query int-ordl6 10) #f)
)

(module+ test
  (define int-ordl7 (make-empty-ordl integer-compare))
  (set! int-ordl7 (for/fold ([io int-ordl7]) ([i (in-range 10)])
    (ordl-insert io (- 20 i) (add1 i) #f)
  ))
  (check-equal? (ordl-query int-ordl7 0) #f)
  (check-equal? (ordl-query int-ordl7 11) (cons 11 10))
)

(module+ test
  (define int-ordl8 (make-empty-ordl integer-compare))
  ; drop
  (define-values (int-ordl8^ ret) (ordl-delete int-ordl8 1))
  (check-equal? ret #f)
  (check-eq? int-ordl8 int-ordl8^)
)

(module+ test
  (define int-ordl9 (for/fold ([o (make-empty-ordl integer-compare)]) ([i (in-range 15)])
    (ordl-insert o i i #f)    
  ))
  (define-values (int-ordl9^ nine) (ordl-delete int-ordl9 9))
  (check-equal? nine (cons 9 9))
  (check-false (ordl-empty? int-ordl9^))
)

(module+ test
  (define int-ordl10 (for/foldr ([o (make-empty-ordl integer-compare)]) ([i (in-range 31)])
    (ordl-insert o i i #f)
  ))
  (define-values (int-ordl10^ ten) (ordl-delete int-ordl10 10))
  (check-equal? ten (cons 10 10))
)

(module+ test
  (let ([int-ordl-test (make-empty-ordl integer-compare)])
    (set! int-ordl-test (ordl-insert int-ordl-test 1 "one" #f))
    (set! int-ordl-test (ordl-insert int-ordl-test 2 "two" #f))
    (check-equal? (ordl-query int-ordl-test 1) (cons 1 "one") "Query for key 1 should return (1 . \"one\")")
  )
)

(module+ test
  (require racket/format)
  (let ([large-ordl (make-empty-ordl integer-compare)])
    ; Insert 20 elements
    (for ([i (in-range 20)])
      (set! large-ordl (ordl-insert large-ordl i (string-append "value" (~a i)) #f)))
    ; Check if all inserted elements can be queried correctly
    (for ([i (in-range 20)])
      (check-equal? (ordl-query large-ordl i) (cons i (string-append "value" (~a i))) (format "Query for key ~a" i)))
    ; Delete some elements and verify
    (define delete-keys '(5 10 15))
    (for ([key delete-keys])
      (define-values (new-ordl deleted-val) (ordl-delete large-ordl key))
      (check-equal? deleted-val (cons key (string-append "value" (~a key))) (format "Delete key ~a" key))
      (set! large-ordl new-ordl)
      (check-false (ordl-query large-ordl key) (format "Query for deleted key ~a should return #f" key)))
        ; Insert some keys again
    (for ([key delete-keys])
      (set! large-ordl (ordl-insert large-ordl key (string-append "newvalue" (~a key)) #t))
      (check-equal? (ordl-query large-ordl key) (cons key (string-append "newvalue" (~a key))) (format "Query for reinserted key ~a" key)))
  )
)

(define (ordl-query-weak-node:impl node cmp-fn key mode depth)
  (match depth
    [0
      (define cmp-rst (cmp-fn (car node) key))
      (match* (cmp-rst mode)
        [('eq (or 'ge 'le)) node]
        [('lt (or 'lt 'le)) node]
        [('gt (or 'gt 'ge)) node]
        [(_ _) #f]
      )
    ]
    [_
      (match node
        [(Node2 _ x0 x1)
          (define x1-key (ordl-min-key-node x1 (sub1 depth)))
          (define x1-cmp-rst (cmp-fn x1-key key))
          (match* (x1-cmp-rst mode)
            [('eq (or 'ge 'le 'gt)) (ordl-query-weak-node:impl x1 cmp-fn key mode (sub1 depth))]
            [('lt _) (ordl-query-weak-node:impl x1 cmp-fn key mode (sub1 depth))]
            [(_ (or 'lt 'le)) 
              (ordl-query-weak-node:impl x0 cmp-fn key mode (sub1 depth))]
            [(_ _)
              (define tmp (ordl-query-weak-node:impl x0 cmp-fn key mode (sub1 depth)))
              (if tmp tmp (ordl-query-weak-node:impl x1 cmp-fn key mode (sub1 depth)))
            ]
          )
        ]
        [(Node3 _ x0 x1 x2)
          (define x2-key (ordl-min-key-node x2 (sub1 depth)))
          (define x2-cmp-rst (cmp-fn x2-key key))
          (match* (x2-cmp-rst mode)
            [('eq (or 'ge 'le 'gt)) (ordl-query-weak-node:impl x2 cmp-fn key mode (sub1 depth))]
            [('lt _) (ordl-query-weak-node:impl x2 cmp-fn key mode (sub1 depth))]
            [(_ _)
              (define x1-key (ordl-min-key-node x1 (sub1 depth)))
              (define x1-cmp-rst (cmp-fn x1-key key))
              (match* (x1-cmp-rst mode)
                [('eq (or 'ge 'le)) (ordl-query-weak-node:impl x1 cmp-fn key mode (sub1 depth))]
                [('eq 'gt) (define tmp (ordl-query-weak-node:impl x1 cmp-fn key mode (sub1 depth)))
                  (if tmp tmp (ordl-query-weak-node:impl x2 cmp-fn key mode (sub1 depth)))
                ]
                [('lt (or 'le 'lt)) (ordl-query-weak-node:impl x1 cmp-fn key mode (sub1 depth))]
                [('lt (or 'ge 'gt)) (define tmp (ordl-query-weak-node:impl x1 cmp-fn key mode (sub1 depth)))
                  (if tmp tmp (ordl-query-weak-node:impl x2 cmp-fn key mode (sub1 depth)))]
                [('eq 'lt) (ordl-query-weak-node:impl x0 cmp-fn key mode (sub1 depth))]
                [('gt (or 'le 'lt)) (ordl-query-weak-node:impl x0 cmp-fn key mode (sub1 depth))]
                [('gt (or 'ge 'gt))
                  (define tmp (ordl-query-weak-node:impl x0 cmp-fn key mode (sub1 depth)))
                  (if tmp tmp (ordl-query-weak-node:impl x1 cmp-fn key mode (sub1 depth)))
                ]
              )
            ]
          )
        ]
      )
    ]
  )
)

(define (ordl-query-weak-ft:impl ft cmp-fn key mode depth)
  (match ft
    [(Empty) #f]
    [(Single node) (ordl-query-weak-node:impl node cmp-fn key mode depth)]
    [(Deep _ left inner right)
      (define right-v (ordl-min-key-digit right depth))
      (define right-v-cmp-rst (cmp-fn right-v key))
      (match* (right-v-cmp-rst mode)
        [('eq (or 'le 'ge 'gt)) (ordl-query-weak-digit:impl right cmp-fn key mode depth)]
        [('lt _) (ordl-query-weak-digit:impl right cmp-fn key mode depth)]
        [(_ _)
          (match inner 
            [(Empty)
              (match mode
                [(or 'lt 'le)
                  (ordl-query-weak-digit:impl left cmp-fn key mode depth)]
                [_
                  (define tmp (ordl-query-weak-digit:impl left cmp-fn key mode depth))
                  (if tmp tmp (ordl-query-weak-digit:impl right cmp-fn key mode depth))
                ]
              )
            ] 
            [_ 
              (define inner-v (ordl-min-key-ft inner (add1 depth)))
              (define inner-v-cmp-rst (cmp-fn inner-v key))
              (match* (inner-v-cmp-rst mode)
                [('eq (or 'le 'ge 'gt)) (ordl-query-weak-ft:impl inner cmp-fn key mode (add1 depth))]
                [('lt (or 'ge 'gt)) (define tmp (ordl-query-weak-ft:impl inner cmp-fn key mode (add1 depth)))
                  (if tmp tmp (ordl-query-weak-digit:impl right cmp-fn key mode depth))]
                [('lt _) (ordl-query-weak-ft:impl inner cmp-fn key mode (add1 depth))]
                [(_ (or 'le 'lt))
                  (ordl-query-weak-digit:impl left cmp-fn key mode depth)]
                [(_ _)
                  (define tmp (ordl-query-weak-digit:impl left cmp-fn key mode depth))
                  (if tmp tmp (ordl-query-weak-ft:impl inner cmp-fn key mode (add1 depth)))
                ]
              )
            ])
        ]
      )
    ]
  )
)

(define (ordl-query-weak-digit:impl digit cmp-fn key mode depth)
  (match digit
    [(One x0)
      (ordl-query-weak-node:impl x0 cmp-fn key mode depth)
    ]
    [(Two x0 x1)
      (define x1-v (ordl-min-key-node x1 depth))
      (match* ((cmp-fn x1-v key) mode)
        [('eq (or 'le 'ge 'gt)) (ordl-query-weak-node:impl x1 cmp-fn key mode depth)]
        [('lt _) (ordl-query-weak-node:impl x1 cmp-fn key mode depth)]
        [(_ (or 'lt 'le)) (ordl-query-weak-node:impl x0 cmp-fn key mode depth)]
        [(_ _)
          (define tmp (ordl-query-weak-node:impl x0 cmp-fn key mode depth))
          (if tmp tmp (ordl-query-weak-node:impl x1 cmp-fn key mode depth))
        ]
      )
    ]
    [(Three x0 x1 x2)
      (define x1-v (ordl-min-key-node x1 depth))
      (match* ((cmp-fn x1-v key) mode)
        [('eq (or 'le 'ge)) (ordl-query-weak-node:impl x1 cmp-fn key mode depth)]
        [('eq 'gt) (define tmp (ordl-query-weak-node:impl x1 cmp-fn key mode depth))
          (if tmp tmp (ordl-query-weak-node:impl x2 cmp-fn key mode depth))]
        [('lt _)
          (define x2-v (ordl-min-key-node x2 depth))
          (match* ((cmp-fn x2-v key) mode)
            [('eq (or 'le 'ge 'gt)) (ordl-query-weak-node:impl x2 cmp-fn key mode depth)]
            [('lt _) (ordl-query-weak-node:impl x2 cmp-fn key mode depth)]
            [(_ (or 'le 'lt)) (ordl-query-weak-node:impl x1 cmp-fn key mode depth)]
            [(_ _) (define tmp (ordl-query-weak-node:impl x1 cmp-fn key mode depth))
              (if tmp tmp (ordl-query-weak-node:impl x2 cmp-fn key mode depth))]
          )
        ]
        [(_ (or 'lt 'le))
          (ordl-query-weak-node:impl x0 cmp-fn key mode depth)
        ]
        [(_ _)
          (define tmp (ordl-query-weak-node:impl x0 cmp-fn key mode depth))
          (if tmp tmp (ordl-query-weak-node:impl x1 cmp-fn key mode depth))
        ]
      )
    ]
    [(Four x0 x1 x2 x3)
      (define x2-v (ordl-min-key-node x2 depth))
      (match* ((cmp-fn x2-v key) mode)
        [('eq (or 'le 'ge)) (ordl-query-weak-node:impl x2 cmp-fn key mode depth)]
        [('eq 'gt) (define tmp (ordl-query-weak-node:impl x2 cmp-fn key mode depth))
          (if tmp tmp (ordl-query-weak-node:impl x3 cmp-fn key mode depth))]
        [('lt _)
          (define x3-v (ordl-min-key-node x3 depth))
          (match* ((cmp-fn x3-v key) mode)
            [('eq (or 'le 'ge 'gt)) (ordl-query-weak-node:impl x3 cmp-fn key mode depth)]
            [('lt _) (ordl-query-weak-node:impl x3 cmp-fn key mode depth)]
            [(_ (or 'le 'lt)) (ordl-query-weak-node:impl x2 cmp-fn key mode depth)]
            [(_ _) (define tmp (ordl-query-weak-node:impl x2 cmp-fn key mode depth))
              (if tmp tmp (ordl-query-weak-node:impl x3 cmp-fn key mode depth))]
          )
        ]
        [(_ (or 'lt 'le))
          (define x1-v (ordl-min-key-node x1 depth))
          (match* ((cmp-fn x1-v key) mode)
            [('eq (or 'le 'ge 'gt)) (ordl-query-weak-node:impl x1 cmp-fn key mode depth)]
            [('lt _) (ordl-query-weak-node:impl x1 cmp-fn key mode depth)]
            [(_ (or 'lt 'le)) (ordl-query-weak-node:impl x0 cmp-fn key mode depth)]
          )
        ]
        [(_ _)
          (define x1-v (ordl-min-key-node x1 depth))
          (match* ((cmp-fn x1-v key) mode)
            [('eq (or 'le 'ge)) (ordl-query-weak-node:impl x1 cmp-fn key mode depth)]
            [('eq 'gt) (define tmp (ordl-query-weak-node:impl x1 cmp-fn key mode depth))
              (if tmp tmp (ordl-query-weak-node:impl x2 cmp-fn key mode depth))]
            [('lt _) (define tmp (ordl-query-weak-node:impl x1 cmp-fn key mode depth))
              (if tmp tmp (ordl-query-weak-node:impl x2 cmp-fn key mode depth))]
            [(_ (or 'lt 'le)) (assert-unreachable)]
            [(_ _)
              (define tmp (ordl-query-weak-node:impl x0 cmp-fn key mode depth))
              (if tmp tmp (ordl-query-weak-node:impl x1 cmp-fn key mode depth))
            ]
          )
        ]
      )
    ]
  )
)

(define (ordl-query-weak ft key mode)
  (match-define (Ordl cmp-fn ft^) ft)
  (ordl-query-weak-ft:impl ft^ cmp-fn key mode 0)
)

(module+ test
  (let ([t (ordl-make-empty integer-compare)])
    (set! t (for/fold ([t t]) ([i (in-range 100)])
      (ordl-insert t i i #f)))
    (define n1 (ordl-query-weak t -1 'ge))
    (check-equal? n1 (cons 0 0))
  )
)

(module+ test
  (let ([t (ordl-make-empty integer-compare)])
    (set! t (for/fold ([t t]) ([i (in-range 100)])
      (ordl-insert t i i #f)))
    (define cnt (let loop ([current (ordl-min t)] [cnt 0])
      (cond
        [current 
          (loop (ordl-query-weak t (car current) 'gt) (add1 cnt))
        ]
        [else cnt]
      )
    ))
    (check-equal? cnt 100)
  )
)

(module+ test
  (let ([t (ordl-make-empty integer-compare)])
    (set! t (for/fold ([t t]) ([i (in-range 100)])
      (ordl-insert t i i #f)))
    (define cnt (let loop ([current (ordl-max t)] [cnt 0])
      (cond
        [current 
          (loop (ordl-query-weak t (car current) 'lt) (add1 cnt))
        ]
        [else cnt]
      )
    ))
    (check-equal? cnt 100)
  )
)

(module+ test
  (let ([t (ordl-make-empty integer-compare)])
    (set! t (for/fold ([t t]) ([i (in-range 100)])
      (ordl-insert t i i #f)))
    (define cnt (let loop ([current (ordl-max t)] [cnt 0])
      (cond
        [current 
          (loop (ordl-query-weak t (sub1 (car current)) 'le) (add1 cnt))
        ]
        [else cnt]
      )
    ))
    (check-equal? cnt 100)
  )
)

(module+ test
  (let ([t (ordl-make-empty integer-compare)])
    (set! t (for/fold ([t t]) ([i (in-range 100)])
      (ordl-insert t i i #f)))
    (define cnt (let loop ([current (ordl-min t)] [cnt 0])
      (cond
        [current 
          (loop (ordl-query-weak t (add1 (car current)) 'ge) (add1 cnt))
        ]
        [else cnt]
      )
    ))
    (check-equal? cnt 100)
  )
)

(provide ordl-size-changed?)
(provide Ordl)
(provide ordl-empty? ordl-min ordl-max)
(provide ordl-query ordl-query-weak)
(provide ordl-delete ordl-insert)
(provide ordl-make-empty)
(provide integer-compare symbol-compare)

; (trace ordl-insert-node:impl ordl-insert-ft:impl ordl-insert-digit:impl)
