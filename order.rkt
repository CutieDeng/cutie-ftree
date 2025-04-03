#lang racket/base

; ordl

(require racket/match)
(require "core.rkt")

(struct Ordl (cmp-fn ft))

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
