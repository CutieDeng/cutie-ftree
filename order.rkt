#lang racket/base

; ordl

(require racket/match racket/bool)
(require racket/trace)
(require errortrace)
(require "core.rkt")

(struct Ordl (cmp-fn ft) #:transparent)

(define ordl-core (FingerTree 
  (lambda () #f) (match-lambda [(cons k _) k]) (lambda (k0 k1) k0)
))

(define (ordl-min o)
  (match-define (Ordl _ f) o)
  (hdL-view f)
)

(define (ordl-max o)
  (match-define (Ordl _ f) o)
  (hdR-view f)
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
    [(Single node) (ordl-query-node:impl node cmp-fn key depth)]
    [(Deep _ left inner right)
      (define right-v (ordl-min-key-digit right depth))
      (define right-v-cmp-rst (cmp-fn right-v key))
      (match right-v-cmp-rst
        [(or 'eq 'lt) (ordl-query-digit:impl right cmp-fn key depth)]
        ['gt
          (define inner-v (ordl-min-key-ft inner (add1 depth)))
          (define inner-v-cmp-rst (cmp-fn inner-v key))
          (match inner-v-cmp-rst
            [(or 'eq 'lt) (ordl-query-ft:impl inner cmp-fn key (add1 depth))]
            ['gt (ordl-query-digit:impl left cmp-fn key depth)]
          )
        ]
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
      [(Node2 _ (and x0 (cons k0 v0)) (and x1 (cons k1 v1)))
        (define k1-cmp-rst (cmp-fn k1 key))
        (match k1-cmp-rst
          ['eq (if replace? (values (Node2 k0 x0 (cons key value)) #f) (values node #f))]
          ['lt (values (Node3 k0 x0 x1 (cons key value)) #f)]
          ['gt (define k0-cmp-rst (cmp-fn k0 key))
            (match k0-cmp-rst
              ['eq (if replace? (values (Node2 key (cons key value) x1) #f) (values node #f))]
              ['lt (values (Node3 k0 x0 (cons key value) x1) #f)]
              ['gt (values (Node3 key (cons key value) x0 x1) #f)]
            )
          ]
        )
      ]
      [(Node3 _ (and x0 (cons k0 v0)) (and x1 (cons k1 v1)) (and x2 (cons k2 v2)))
        (define k1-cmp-rst (cmp-fn k1 key))
        (match k1-cmp-rst
          ['eq (if replace? (values (Node3 k0 x0 (cons key value) x2) #f) (values node #f))]
          ['lt (define k2-cmp-rst (cmp-fn k2 key))
            (match k2-cmp-rst
              ['eq (if replace?
                (values (Node3 k0 x0 x1 (cons key value)) #f)
                (values node #f))]
              ['lt (values (Node2 k0 x0 x1) (Node2 k2 x2 (cons key value)))]
              ['gt (values (Node2 k0 x0 x1) (Node2 key (cons key value) x2))]
            )
          ]
          ['gt (define k0-cmp-rst (cmp-fn k0 key))
            (match k0-cmp-rst
              ['eq (if replace? 
                (values (Node3 key (cons key value) x1 x2) #f)
                (values node #f))]
              ['lt (values (Node2 k0 x0 (cons key value)) (Node2 k1 x1 x2))]
              ['gt (values (Node2 key (cons key value) x0) (Node2 k1 x1 x2))]
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
              [(not node1) (values (Node2 k0 node0 x1))])
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
                    (values (Node3 k0 x0 x1 node0))]
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
                    (values (Node3 k0 x0 node0 x2))]
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
                (values (Node3 k0 x0 node0 x2))]
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
                (values (Node3 k0 node0 x1 x2))]
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
            ['lt (Deep k0 (One x) (Empty) (One (cons key value)))]
            ['eq (if replace? (Single (cons key value)) ft)]
            ['gt (Deep key (One (cons key value)) (Empty) (One x))]
          )
        ]
        [_
          (define-values (node0 node1) (ordl-insert-node:impl x cmp-fn key value depth replace?))
          (cond
            [(and (eq? x node0) (not node1)) ft]
            [node1 (Deep (ordl-min-key-node node0 depth) node0 (Empty) node1)]
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
            ['lt (list x0 kv)]
            ['eq (if replace? (list kv) digit)]
          )
        ]
        [(Two (and x0 (cons k0 _)) (and x1 (cons k1 _)))
          (match (cmp-fn k1 key)
            ['lt (list x0 x1 kv)]
            ['eq (if replace? (list x0 kv) digit)]
            ['gt 
              (match (cmp-fn k0 key)
                ['lt (list x0 kv x1)]
                ['eq (if replace? (list kv x1) digit)]
              )]
          )
        ]
        [(Three (and x0 (cons k0 _)) (and x1 (cons k1 _)) (and x2 (cons k2 _)))
          (match (cmp-fn k1 key)
            ['lt 
              (match (cmp-fn k2 key)
                ['lt (list x0 x1 x2 kv)]
                ['eq (if replace? (list x0 x1 kv) digit)]
                ['gt (list x0 x1 kv x2)]
              )]
            ['eq (if replace? (list x0 kv x2) digit)]
            ['gt
              (match (cmp-fn k0 key)
                ['lt (list x0 kv x1 x2)]
                ['eq (if replace? (list kv x1 x2) digit)]
                ; ['gt (assert-unreachable)]
              )]
          )
        ]
        [(Four (and x0 (cons k0 _)) (and x1 (cons k1 _)) (and x2 (cons k2 _)) (and x3 (cons k3 _)))
          (match (cmp-fn k2 key)
            ['lt 
              (match (cmp-fn k3 key)
                ['lt (list x0 x1 x2 x3 kv)]
                ['eq (if replace? (list x0 x1 x2 kv) digit)]
                ['gt (list x0 x1 x2 kv x3)]
              )]
            ['eq (if replace? (list x0 x1 kv x3) digit)]
            ['gt 
              (match (cmp-fn k1 key)
                ['lt (list x0 x1 kv x2 x3)]
                ['eq (if replace? (list x0 kv x2 x3) digit)]
                ['gt
                  (match (cmp-fn k0 key)
                    ['lt (list x0 kv x1 x2 x3)]
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
    [(Empty) (Single (cons key value))]
    [(Single _) (ordl-insert-ft:impl ft cmp-fn key value 0 replace?)]
    [(Deep o _ _ _)
      (match (cmp-fn o key)
        [(or 'lt 'eq) (ordl-insert-ft:impl ft cmp-fn key value 0 replace?)]
        ['gt (consL:impl ordl-core ft (cons key value) 0)]
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

(trace ordl-insert-node:impl ordl-insert-ft:impl ordl-insert-digit:impl)
