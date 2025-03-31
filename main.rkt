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

(define ral-viewl hdL-view)
(define ral-viewR hdR-view)

(provide ral-viewl ral-viewR)

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
    [(< idx 0) (assert-unreachable)]
    [(>= idx (measure:ft core/size ral 0)) (assert-unreachable)]
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
        [(< idx old) (Deep old lhs inner (ral-set-digit:impl rhs (- idx inner-measure) value depth))]
        [else (assert-unreachable)]
      )
    ]
  )
)

(define (ral-set ral idx val)
  (cond
    [(< idx 0) (assert-unreachable)]
    [(>= idx (measure:ft core/size ral 0)) (assert-unreachable)]
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

(define (ral-split ral idx)
  (define-values (i l m r) (ral-split:impl ral idx 0))
  (unless (zero? i) (assert-unreachable))
  (values l m r)
)

(define (ral-split-digit:impl digit idx depth)
  (match digit
    [(One a) (cond [(< idx (measure:node core/size a depth)) (values idx `() a `())] [else (assert-unreachable)])]
    [(Two a b) (cond
      [(< idx (measure:node core/size a depth)) (values idx `() a `(,b))]
      [(< idx (+ (measure:node core/size a depth) (measure:node core/size b depth))) (values (- idx (measure:node core/size a depth)) `(,a) b `())]
      [else (assert-unreachable)]
    )]
    [(Three a b c) (cond
      [(< idx (measure:node core/size a depth)) (values idx `() a `(,b ,c))]
      [(< idx (+ (measure:node core/size a depth) (measure:node core/size b depth))) 
        (values (- idx (measure:node core/size a depth)) `(,a) b `(,c))]
      [(< idx (+ (measure:node core/size a depth) 
        (measure:node core/size b depth) (measure:node core/size c depth))) 
          (values (- idx (measure:node core/size a depth) (measure:node core/size b depth))
            `(,a ,b) c `())]
      [else (assert-unreachable)]
    )]
    [(Four a b c d) (cond
      [(< idx (measure:node core/size a depth)) (values idx `() a `(,b ,c ,d))]
      [(< idx (+ (measure:node core/size a depth) (measure:node core/size b depth))) 
        (values (- idx (measure:node core/size a depth)) `(,a) b `(,c ,d))]
      [(< idx (+ (measure:node core/size a depth) 
        (measure:node core/size b depth) (measure:node core/size c depth))) 
          (values (- idx (measure:node core/size a depth) (measure:node core/size b depth))
            `(,a ,b) c `(,d))]
      [(< idx (+ (measure:node core/size a depth) 
        (measure:node core/size b depth) (measure:node core/size c depth)
        (measure:node core/size d depth))) 
          (values (- idx (measure:node core/size a depth) (measure:node core/size b depth)
            (measure:node core/size c depth))
              `(,a ,b ,c) d `())]
      [else (assert-unreachable)]
    )]
  )
)

(define (digit-list->ft lst depth)
  (match lst
    [`() (ral-empty)]
    [`(,a) (Single a)]
    [`(,a ,b) (Deep (+ (measure:node core/size a depth) (measure:node core/size b depth))
      (One a) (ral-empty) (One b))]
    [`(,a ,b ,c) (Deep (+ (measure:node core/size a depth) (measure:node core/size b depth)
      (measure:node core/size c depth))
      (One a) (ral-empty) (Two b c))]
    [`(,a ,b ,c ,d) (Deep (+ (measure:node core/size a depth) (measure:node core/size b depth)
      (measure:node core/size c depth) (measure:node core/size d depth))
      (Two a b) (ral-empty) (Two c d))]
  )
)
(define (digit-list2->ft lst depth)
  (if (<= (length lst) 4) (digit-list->ft lst depth) 
    (let ([v (for/fold ([i 0]) ([j lst]) (+ i (measure:node core/size j depth)))])
      (match lst
        [`(,a ,b ,c ,d ,e) (Deep v (Two a b) (Empty) (Three c d e))]
        [`(,a ,b ,c ,d ,e ,f) (Deep v (Three a b c) (Empty) (Three d e f))]
        [`(,a ,b ,c ,d ,e ,f ,g) (Deep v (Three a b c) (Empty) (Four d e f g))]
      )
    )
  )
)
(define (digit-list+ft->digit lst ft depth pop)
  (match lst
    ['() (define-values (h ft^) (pop core/size ft (add1 depth))) (values (One h) ft^)]
    [`(,a) (values (One a) ft)]
    [`(,a ,b) (values (Two a b) ft)]
    [`(,a ,b ,c) (values (Three a b c) ft)]
    [`(,a ,b ,c ,d) (values (Four a b c d) ft)]
  )
)

; depth is the level of the node
(define (node->digit node depth)
  (list->digit (node->list node) (sub1 depth))
)

(define (left-digit+ft->ft digit ft depth)
  (match ft
    [(Empty)
      (define digit^ (digit-add-list digit '()))
      (digit-list->ft digit^ depth)]
    [_ (define-values (r ft^) (hdR:impl core/size ft (add1 depth)))
      (build-ft0 core/size digit ft^ (node->digit r (add1 depth)) depth)]
  )
)
(define (right-digit+ft->ft digit ft depth)
  (match ft
    [(Empty)
      (define digit^ (digit-add-list digit '()))
      (digit-list->ft digit^ depth)]
    [_ (define-values (l ft^) (hdL:impl core/size ft (add1 depth)))
      (build-ft0 core/size (node->digit l (add1 depth)) ft^ digit depth)]
  )
)

(define (ral-split-node:impl node idx depth)
  (match node
    [(Node2 v a b) (cond
      [(< idx (measure:node core/size a (sub1 depth))) (values idx `() a `(,b))]
      [(< idx v) (values (- idx (measure:node core/size a (sub1 depth))) `(,a) b `())]
      [else (assert-unreachable)]
    )]
    [(Node3 v a b c) (cond
      [(< idx (measure:node core/size a (sub1 depth))) (values idx `() a `(,b ,c))]
      [(< idx (+ (measure:node core/size a (sub1 depth)) (measure:node core/size b (sub1 depth))))
        (values (- idx (measure:node core/size a (sub1 depth))) `(,a) b `(,c))]
      [(< idx v) (values 
        (- idx (measure:node core/size a (sub1 depth)) (measure:node core/size b (sub1 depth)))
        `(,a ,b) c `()
      )]
    )]
  )
)

(define (ral-split:impl ral idx depth)
  ; (printf "debug, ral-split:impl ~a\n" ral)
  (match ral
    [(Empty) (assert-unreachable)]
    [(Single v)
      (cond
        [(>= idx (measure:node core/size v depth)) (assert-unreachable)]
        [(values idx (ral-empty) v (ral-empty))]
      )
    ]
    [(Deep v lhs inner rhs)
      (define lhs-measure (measure:digit core/size lhs depth))
      (define inner-measure (+ lhs-measure (measure:ft core/size inner (add1 depth))))
      (cond
        [(< idx lhs-measure) (define-values (idx^ l m r) (ral-split-digit:impl lhs idx depth))
          ; (l m r) inner rhs
          (define left (digit-list->ft l depth))
          (match inner
            [(Empty) (values left m (digit-list2->ft (append r (digit-add-list rhs '())) depth))]
            [_ 
              (define-values (right inner^) (digit-list+ft->digit r inner depth hdL:impl))
              (values idx^ left m (build-ft0 core/size right inner^ rhs depth))])]
        [(< idx inner-measure) 
          ; lhs (l m r) rhs
          (define-values (l m r) (ral-split:impl inner (- idx lhs-measure) (add1 depth))) 
          ; (printf "debug, l: ~a, m: ~a, r: ~a\n" l m r)
          (define left (left-digit+ft->ft lhs l depth))
          (define right (right-digit+ft->ft rhs r depth))
          ; (printf "debug, left: ~a; right: ~a\n" left right)
          (define-values (idx^ l^ m^ r^) (ral-split-node:impl m (- idx lhs-measure) (add1 depth)))
          (define left^ (for/fold ([init left]) ([i l^]) (consR:impl core/size init i)))
          (define right^ (for/foldr ([init right]) ([i r^]) (consL:impl core/size init i)))
          (values idx^ left^ m^ right^)
          ]
        [(< idx v) (define-values (idx^ l m r) (ral-split-digit:impl rhs (- idx inner-measure) depth))
          ; lhs inner (l m r)
          (define right (digit-list->ft r depth))
          (match inner
            [(Empty) (values (digit-list2->ft (append (digit-add-list lhs '()) l) depth) m right)]
            [_ 
              (define-values (left inner^) (digit-list+ft->digit r inner depth hdR:impl))
              (values idx^ (build-ft0 core/size lhs inner^ left depth) m right)])]
        [else (assert-unreachable)]
      )
    ]
  )
)

(define (test0)
  (define x (ral-empty))
  (define n 20)
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
  (define-values (l m r) (ral-split x 5))
  (printf "l: ~a\nm: ~a\nr: ~a\n" l m r)
  (for ([i (in-range (ral-length r))] [j (in-ral0 r)])
    (printf "~a: ~a\n" i j)
    ; (printf "~a: ~a\n" i (ral-ref r i))
  )
  (printf "\n")
)
; (test0)

(provide ral-empty ral-consl ral-consr ral-dropl ral-dropr ral-split ral-append)
(provide ral-ref ral-set ral-length)
(provide in-ral0)

(define (vector->node3vector vec start len depth)
  (define new-length (quotient len 3))
  (define new-vec (make-vector new-length))
  (for ([i (in-range new-length)])
    (define x0 (vector-ref vec (+ start (* 3 i))))
    (define x1 (vector-ref vec (+ start 1 (* 3 i))))
    (define x2 (vector-ref vec (+ start 2 (* 3 i))))
    (vector-set! new-vec i (Node3 (+
        (measure:node core/size x0 depth)
        (measure:node core/size x1 depth)
        (measure:node core/size x2 depth)
      ) 
      x0 x1 x2
    ))
  )
  new-vec
)

(define (vector->ral:impl vec sz depth)
  (define vec-len (vector-length vec))
  (cond
    [(<= vec-len 8) (small-vector->ral:impl vec depth)]
    [else
      (match (modulo vec-len 3)
        [0
          (define lhs (Three (vector-ref vec 0) (vector-ref vec 1) (vector-ref vec 2)))
          (define rhs (Three (vector-ref vec (- vec-len 3)) (vector-ref vec (- vec-len 2)) (vector-ref vec (- vec-len 1))))
          ; very creative impl
          (define sub-sz (* 6 (measure:node core/size (vector-ref vec 0) depth)))
          (define mid (vector->node3vector vec 3 (- vec-len 6) depth))
          (Deep sz lhs (vector->ral:impl mid (- sz sub-sz) (add1 depth)) rhs)
        ]
        [1
          (define lhs (Four (vector-ref vec 0) (vector-ref vec 1) (vector-ref vec 2) (vector-ref vec 3)))
          (define rhs (Three (vector-ref vec (- vec-len 3)) (vector-ref vec (- vec-len 2)) (vector-ref vec (- vec-len 1))))
          ; very creative impl
          (define sub-sz (* 7 (measure:node core/size (vector-ref vec 0) depth)))
          (define mid (vector->node3vector vec 4 (- vec-len 7) depth))
          (Deep sz lhs (vector->ral:impl mid (- sz sub-sz) (add1 depth)) rhs)
        ]
        [2
          (define lhs (Four (vector-ref vec 0) (vector-ref vec 1) (vector-ref vec 2) (vector-ref vec 3)))
          (define rhs (Four (vector-ref vec (- vec-len 4)) (vector-ref vec (- vec-len 3)) (vector-ref vec (- vec-len 2)) (vector-ref vec (- vec-len 1))))
          ; very creative impl
          (define sub-sz (* 8 (measure:node core/size (vector-ref vec 0) depth)))
          (define mid (vector->node3vector vec 4 (- vec-len 8) depth))
          (Deep sz lhs (vector->ral:impl mid (- sz sub-sz) (add1 depth)) rhs)
        ]
      )
    ]
  )
)

(define (small-vector->ral:impl vec depth)
  (define v (for/fold ([v 0]) ([k (in-vector vec)]) (+ v (measure:node core/size k depth))))
  (match vec
    [(vector x0) (Single x0)]
    [(vector x0 x1) (Deep v (One x0) (ral-empty) (One x1))]
    [(vector x0 x1 x2) (Deep v (One x0) (ral-empty) (Two x1 x2))]
    [(vector x0 x1 x2 x3) (Deep v (Two x0 x1) (ral-empty) (Two x2 x3))]
    [(vector x0 x1 x2 x3 x4) (Deep v (Two x0 x1) (ral-empty) (Three x2 x3 x4))]
    [(vector x0 x1 x2 x3 x4 x5) (Deep v (Three x0 x1 x2) (ral-empty) (Three x3 x4 x5))]
    [(vector x0 x1 x2 x3 x4 x5 x6) (Deep v (Three x0 x1 x2) (ral-empty) (Four x3 x4 x5 x6))]
    [(vector x0 x1 x2 x3 x4 x5 x6 x7) (Deep v (Four x0 x1 x2 x3) (ral-empty) (Four x4 x5 x6 x7))]
  )
)

(define (vector->ral vec)
  ; ...
  ; (for/fold ([i (ral-empty)]) ([v (in-vector vec)]) (ral-consr i v))
  ; maybe opt
  (vector->ral:impl vec (vector-length vec) 0)
)

(define (ral->vector ral)
  (define vec (make-vector (ral-length ral)))
  (for ([i (in-range (ral-length ral))]) 
    (vector-set! vec i (ral-ref ral i))
  )
  vec
)

(provide vector->ral ral->vector)

(define (test1)
  (define x #[10 20 30 40 50 60 70 80 90])
  (define y (vector->ral x))
  (for ([j (in-ral0 y)]) (printf "~a;" j))
  (printf "\n")
  (define x2 (ral->vector y))
  (printf "x2: ~a\n" x2)
  (printf "eq? ~a" (equal? x x2))
)

(define (ral-copy ral start end)
  (define len (- end start))
  (cond
    [(= len 0) (ral-empty)]
    [(and (= start 0) (= end (ral-length ral))) ral]
    [(= start 0) (match-define-values (l _ _) (ral-split ral end)) l]
    [(= end (ral-length ral)) (match-define-values (_ _ r) (ral-split ral (sub1 start))) r]
    [else (match-define-values (l _ _) (ral-split ral end))
      (match-define-values (_ _ r) (ral-split l (sub1 start)))
      r
    ]
  )
)

(define (ral-empty? ral)
  (match ral
    [(Empty) #t]
    [_ #f]
  )
)

(define (ral-take ral pos)
  (cond
    [(= pos (ral-length ral)) ral]
    [else (match-define-values (l _ _) (ral-split ral pos)) l]
  )
)

(define (ral-take-right ral pos)
  (ral-drop ral (- (ral-length ral) pos))
)

(define (ral-drop ral pos) 
  (cond
    [(= pos 0) ral]
    [else (match-define-values (_ _ r) (ral-split ral (sub1 pos))) r]
  )
)

(define (ral-drop-right ral pos)
  (ral-take ral (- (ral-length ral) pos))
)

(define (ral-split-at ral pos)
  (cond
    [(= pos (ral-length ral)) (values ral (ral-empty))]
    [else
      (match-define-values (l m r) (ral-split ral pos))
      (values l (ral-consl r m))
    ]
  )
)

(define (ral-split-at-right ral pos)
  (match-define-values (l r) (ral-split-at ral (- (ral-length ral) pos)))
  (values r l)
)

(provide ral-empty? ral-take ral-take-right ral-drop ral-drop-right ral-split-at ral-split-at-right)
(provide ral-copy)

(define (ral-fold:impl ral )
  (error 'unimpl)
)
