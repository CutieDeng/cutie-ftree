#lang racket/base

(require racket/match racket/contract)
(require "core.rkt")

(define core/size (FingerTree (lambda () 0) (lambda (_) 1) +))

(define (ral-consl ral value)
    (consL:impl core/size ral value)
)

(define (ral-consr ral value)
    (consR:impl core/size ral value)
)

(define (ral-dropl ral)
    (hdL:impl core/size ral)
)

(define (ral-dropr ral)
    (hdR:impl core/size ral)
)

(define (ral-append ral0 ral1)
    (concat:impl core/size ral0 ral1)
)

(define ral-empty:impl (Empty))
(define (ral-empty) ral-empty:impl)

(define (find-in-list lst idx depth)
    (match-define (cons head lst^) lst)
    (define sz (measure:node core/size head depth))
    (cond [(>= idx sz) (find-in-list lst^ (- idx sz) depth)]
        [else (ral-ref-node:impl head idx depth)])
)
(define node->list (match-lambda
    [(Node2 _ a b) `(,a ,b)]
    [(Node3 _ a b c) `(,a ,b ,c)]))
(define (ral-ref-node:impl node idx depth)
    (match depth
        [0 (=> e) (when (zero? idx) (e)) (assert-unreachable)]
        [0 node]
        [_ (define lst (node->list node))
            (find-in-list lst idx (sub1 depth))
        ]
    )
)
(define (ral-ref-digit:impl digit idx depth)
    (define lst (digit-add-list digit '()))
    (find-in-list lst idx depth)
)

(define (ral-ref:impl ral idx depth)
    (match ral
        [(Single r) (ral-ref-node:impl r idx depth)]
        [(Deep _ lhs inner rhs)
            (define lhs-measure (measure:digit core/size lhs depth))
            (define inner-measure (+ lhs-measure (measure:ft core/size inner (add1 depth))))
            (cond
                [(< idx lhs-measure) (ral-ref-digit:impl lhs idx depth)]
                [(< idx inner-measure) (ral-ref:impl inner (- idx lhs-measure) (add1 depth))]
                [else (ral-ref-digit:impl rhs (- idx inner-measure) depth)]
            )
        ]
    )
)

(define (ral-ref ral idx)
    (cond
        [(< idx 0) #f]
        [(>= idx (measure:ft core/size ral 0)) #f]
        [else (ral-ref:impl ral idx 0)]
    )
)

(define (update-in-list:impl lst idx value depth rest)
    (match-define (cons head lst^) lst)
    (define sz (measure:node core/size head depth))
    (cond [(>= idx sz) (update-in-list:impl lst^ (- idx sz) value depth (cons head rest))]
        [else (for/fold ([init (cons (ral-set-node:impl head idx value depth) rest)]) ([r lst^])
            (cons r init)
        )])
)
(define (update-in-list lst idx value depth)
    (reverse (update-in-list:impl lst idx value depth '()))
)
(define (list->node lst depth)
    (match lst
        [`(,a ,b) (Node2 (+ (measure:node core/size a depth) (measure:node core/size b depth)) a b)]
        [`(,a ,b ,c) (Node3 
            (+ (measure:node core/size a depth) 
                (measure:node core/size b depth) (measure:node core/size c depth))
            a b c)]
    )
)
(define (ral-set-node:impl node idx value depth)
    (match depth
        [0 (=> e) (when (zero? idx) (e)) (assert-unreachable)]
        [0 value]
        [_ (define lst (node->list node))
            (list->node (update-in-list lst idx value (sub1 depth)) (sub1 depth))
        ]
    )
)
(define (list->digit lst _depth)
    (match lst
        [`(,a ,b ,c ,d) (Four a b c d)]
        [`(,a ,b ,c) (Three a b c)]
        [`(,a ,b) (Two a b)]
        [`(,a) (One a)]
    )
)
(define (ral-set-digit:impl digit idx value depth)
    (define lst (digit-add-list digit '()))
    (define m (update-in-list lst idx value depth))
    (list->digit m depth)
)

(define (ral-set:impl ral idx value depth)
    (match ral
        [(Single r) (ral-set-node:impl r idx value depth)]
        [(Deep old lhs inner rhs)
            (define lhs-measure (measure:digit core/size lhs depth))
            (define inner-measure (+ lhs-measure (measure:ft core/size inner (add1 depth))))
            (cond
                [(< idx lhs-measure) (Deep old (ral-set-digit:impl lhs idx value depth) inner rhs)]
                [(< idx inner-measure) (Deep old lhs (ral-set:impl inner (- idx lhs-measure) value (add1 depth)) rhs)]
                [else (Deep old lhs inner (ral-set-digit:impl rhs (- idx inner-measure) value depth))]
            )
        ]
    )
)

(define (ral-set ral idx val)
    (cond
        [(< idx 0) #f]
        [(>= idx (measure:ft core/size ral 0)) #f]
        [else (ral-set:impl ral idx val 0)]
    )
)

(require racket/sequence)

(define (in-ral0 ral)
    (make-do-sequence (lambda () (initiate-sequence 
        #:init-pos (cons ral 0)
        #:next-pos (lambda (x) (match-define (cons ral n) x) (cons ral (add1 n)))
        #:pos->element (lambda (x) (match-define (cons ral n) x) (ral-ref ral n))
        #:continue-with-pos? (lambda (x) 
            (match-define (cons ral n) x) (define nt (measure:ft core/size ral 0)) (< n nt))
    )))
)

(define (ral-length ral) (measure:ft core/size ral 0))

(define (test0)
    (define x (ral-empty))
    (define n 1000000)
    (set! x (for/fold ([x x]) ([i (in-range n)])
        ; (ral-consr x i)
        (ral-consl x i)
    ))
    (printf "init length: ~a\n" (ral-length x))
    (set! x (for/fold ([x x]) ([i (in-range (sub1 n))])
        (define s (ral-set x i 10))
        s
    ))
    (printf "final length: ~a\n" (ral-length x))
    (for ([i (in-range n)])
        (define v (ral-ref x i))
        (unless (= v 10) (printf "idx ~a not equal 10, but ~a\n" i v))
    )
)