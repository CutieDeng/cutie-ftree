#lang racket/base

(require racket/match racket/contract racket/sequence)
(require "private/core.rkt" "private/core-algorithm.rkt")

(define core/size (ft:config (lambda () 0) (lambda (_) 1) +))

(define (pvector-cons-left pv value)
  (consL:impl core/size pv value))

(define (pvector-cons-right pv value)
  (consR:impl core/size pv value))

(define (pvector-pop-left pv)
  (hdL:impl core/size pv))

(define (pvector-pop-right pv)
  (hdR:impl core/size pv))

(define pvector-view-left hdL-view)
(define pvector-view-right hdR-view)

(define (pvector-append pv0 pv1)
  (concat:impl core/size pv0 pv1))

(define pvector-empty:impl (ft:empty))
(define (pvector-empty) pvector-empty:impl)

(define (find-in-list lst idx depth)
  (match-define (cons head lst^) lst)
  (define sz (measure:node core/size head depth))
  (cond [(>= idx sz) (find-in-list lst^ (- idx sz) depth)]
    [else (pvector-ref-node:impl head idx depth)]))

(define node->list (match-lambda
  [(node:2 _ a b) `(,a ,b)]
  [(node:3 _ a b c) `(,a ,b ,c)]))

(define (pvector-ref-node:impl node idx depth)
  (match depth
    [0 (=> e) (when (zero? idx) (e)) (assert-unreachable)]
    [0 node]
    [_ (define lst (node->list node))
      (find-in-list lst idx (sub1 depth))]))

(define (pvector-ref-digit:impl digit idx depth)
  (define lst (digit-add-list digit '()))
  (find-in-list lst idx depth))

(define (pvector-ref:impl pv idx depth)
  (match pv
    [(ft:single r) (pvector-ref-node:impl r idx depth)]
    [(ft:deep _ lhs inner rhs)
      (define lhs-measure (measure:digit core/size lhs depth))
      (define inner-measure (+ lhs-measure (measure:ft core/size inner (add1 depth))))
      (cond
        [(< idx lhs-measure) (pvector-ref-digit:impl lhs idx depth)]
        [(< idx inner-measure) (pvector-ref:impl inner (- idx lhs-measure) (add1 depth))]
        [else (pvector-ref-digit:impl rhs (- idx inner-measure) depth)])]))

(define (pvector-ref pv idx)
  (cond
    [(< idx 0) (assert-unreachable)]
    [(>= idx (measure:ft core/size pv 0)) (assert-unreachable)]
    [else (pvector-ref:impl pv idx 0)]))

(define (update-in-list:impl lst idx value depth rest)
  (match-define (cons head lst^) lst)
  (define sz (measure:node core/size head depth))
  (cond [(>= idx sz) (update-in-list:impl lst^ (- idx sz) value depth (cons head rest))]
    [else (for/fold ([init (cons (pvector-set-node:impl head idx value depth) rest)]) ([r lst^])
      (cons r init))]))

(define (update-in-list lst idx value depth)
  (reverse (update-in-list:impl lst idx value depth '())))

(define (list->node lst depth)
  (match lst
    [`(,a ,b) (node:2 (+ (measure:node core/size a depth) (measure:node core/size b depth)) a b)]
    [`(,a ,b ,c) (node:3
      (+ (measure:node core/size a depth)
        (measure:node core/size b depth) (measure:node core/size c depth))
      a b c)]))

(define (pvector-set-node:impl node idx value depth)
  (match depth
    [0 (=> e) (when (zero? idx) (e)) (assert-unreachable)]
    [0 value]
    [_ (define lst (node->list node))
      (list->node (update-in-list lst idx value (sub1 depth)) (sub1 depth))]))

(define (pvector-set-digit:impl digit idx value depth)
  (define lst (digit-add-list digit '()))
  (define m (update-in-list lst idx value depth))
  (list->digit m depth))

(define (pvector-set:impl pv idx value depth)
  (match pv
    [(ft:single r) (pvector-set-node:impl r idx value depth)]
    [(ft:deep old lhs inner rhs)
      (define lhs-measure (measure:digit core/size lhs depth))
      (define inner-measure (+ lhs-measure (measure:ft core/size inner (add1 depth))))
      (cond
        [(< idx lhs-measure) (ft:deep old (pvector-set-digit:impl lhs idx value depth) inner rhs)]
        [(< idx inner-measure) (ft:deep old lhs (pvector-set:impl inner (- idx lhs-measure) value (add1 depth)) rhs)]
        [(< idx old) (ft:deep old lhs inner (pvector-set-digit:impl rhs (- idx inner-measure) value depth))]
        [else (assert-unreachable)])]))

(define (pvector-set pv idx val)
  (cond
    [(< idx 0) (assert-unreachable)]
    [(>= idx (measure:ft core/size pv 0)) (assert-unreachable)]
    [else (pvector-set:impl pv idx val 0)]))

;; Original index-based implementation (O(n log n) total)
(define (in-pvector/index pv)
  (make-do-sequence (lambda () (initiate-sequence
    #:init-pos (cons pv 0)
    #:next-pos (lambda (x) (match-define (cons pv n) x) (cons pv (add1 n)))
    #:pos->element (lambda (x) (match-define (cons pv n) x) (pvector-ref pv n))
    #:continue-with-pos? (lambda (x)
      (match-define (cons pv n) x) (define nt (measure:ft core/size pv 0)) (< n nt))))))

(require racket/generator)

;; Generator-based implementation (O(n) total)
(define (in-pvector pv)
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
    (yield-ft pv 0)))

;; Reverse generator-based implementation
(define (in-pvector-reverse pv)
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
    (yield-ft pv 0)))

(define (pvector-length pv) (measure:ft core/size pv 0))

(define (pvector-split pv idx)
  (define-values (i l m r) (pvector-split:impl pv idx 0))
  (unless (zero? i) (assert-unreachable))
  (values l m r))

(define (pvector-split-digit:impl digit idx depth)
  (match digit
    [(digit:1 a) (cond [(< idx (measure:node core/size a depth)) (values idx `() a `())] [else (assert-unreachable)])]
    [(digit:2 a b) (cond
      [(< idx (measure:node core/size a depth)) (values idx `() a `(,b))]
      [(< idx (+ (measure:node core/size a depth) (measure:node core/size b depth))) (values (- idx (measure:node core/size a depth)) `(,a) b `())]
      [else (assert-unreachable)])]
    [(digit:3 a b c) (cond
      [(< idx (measure:node core/size a depth)) (values idx `() a `(,b ,c))]
      [(< idx (+ (measure:node core/size a depth) (measure:node core/size b depth)))
        (values (- idx (measure:node core/size a depth)) `(,a) b `(,c))]
      [(< idx (+ (measure:node core/size a depth)
        (measure:node core/size b depth) (measure:node core/size c depth)))
          (values (- idx (measure:node core/size a depth) (measure:node core/size b depth))
            `(,a ,b) c `())]
      [else (assert-unreachable)])]
    [(digit:4 a b c d) (cond
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
      [else (assert-unreachable)])]))

(define (digit-list->ft lst depth)
  (match lst
    [`() (pvector-empty)]
    [`(,a) (ft:single a)]
    [`(,a ,b) (ft:deep (+ (measure:node core/size a depth) (measure:node core/size b depth))
      (digit:1 a) (pvector-empty) (digit:1 b))]
    [`(,a ,b ,c) (ft:deep (+ (measure:node core/size a depth) (measure:node core/size b depth)
      (measure:node core/size c depth))
      (digit:1 a) (pvector-empty) (digit:2 b c))]
    [`(,a ,b ,c ,d) (ft:deep (+ (measure:node core/size a depth) (measure:node core/size b depth)
      (measure:node core/size c depth) (measure:node core/size d depth))
      (digit:2 a b) (pvector-empty) (digit:2 c d))]))

(define (digit-list2->ft lst depth)
  (if (<= (length lst) 4) (digit-list->ft lst depth)
    (let ([v (for/fold ([i 0]) ([j lst]) (+ i (measure:node core/size j depth)))])
      (match lst
        [`(,a ,b ,c ,d ,e) (ft:deep v (digit:2 a b) (ft:empty) (digit:3 c d e))]
        [`(,a ,b ,c ,d ,e ,f) (ft:deep v (digit:3 a b c) (ft:empty) (digit:3 d e f))]
        [`(,a ,b ,c ,d ,e ,f ,g) (ft:deep v (digit:3 a b c) (ft:empty) (digit:4 d e f g))]))))

(define (digit-list+ft->digit lst ft depth pop)
  (match lst
    ['() (define-values (h ft^) (pop core/size ft (add1 depth))) (values (digit:1 h) ft^)]
    [`(,a) (values (digit:1 a) ft)]
    [`(,a ,b) (values (digit:2 a b) ft)]
    [`(,a ,b ,c) (values (digit:3 a b c) ft)]
    [`(,a ,b ,c ,d) (values (digit:4 a b c d) ft)]))

(define (node->digit node depth)
  (list->digit (node->list node) (sub1 depth)))

(define (left-digit+ft->ft digit ft depth)
  (match ft
    [(ft:empty)
      (define digit^ (digit-add-list digit '()))
      (digit-list->ft digit^ depth)]
    [_ (define-values (r ft^) (hdR:impl core/size ft (add1 depth)))
      (build-ft0 core/size digit ft^ (node->digit r (add1 depth)) depth)]))

(define (right-digit+ft->ft digit ft depth)
  (match ft
    [(ft:empty)
      (define digit^ (digit-add-list digit '()))
      (digit-list->ft digit^ depth)]
    [_ (define-values (l ft^) (hdL:impl core/size ft (add1 depth)))
      (build-ft0 core/size (node->digit l (add1 depth)) ft^ digit depth)]))

(define (pvector-split-node:impl node idx depth)
  (match node
    [(node:2 v a b) (cond
      [(< idx (measure:node core/size a (sub1 depth))) (values idx `() a `(,b))]
      [(< idx v) (values (- idx (measure:node core/size a (sub1 depth))) `(,a) b `())]
      [else (assert-unreachable)])]
    [(node:3 v a b c) (cond
      [(< idx (measure:node core/size a (sub1 depth))) (values idx `() a `(,b ,c))]
      [(< idx (+ (measure:node core/size a (sub1 depth)) (measure:node core/size b (sub1 depth))))
        (values (- idx (measure:node core/size a (sub1 depth))) `(,a) b `(,c))]
      [(< idx v) (values
        (- idx (measure:node core/size a (sub1 depth)) (measure:node core/size b (sub1 depth)))
        `(,a ,b) c `())])]))

(define (pvector-split:impl pv idx depth)
  (match pv
    [(ft:empty) (assert-unreachable)]
    [(ft:single v)
      (cond
        [(>= idx (measure:node core/size v depth)) (assert-unreachable)]
        [else (values idx (pvector-empty) v (pvector-empty))])]
    [(ft:deep v lhs inner rhs)
      (define lhs-measure (measure:digit core/size lhs depth))
      (define inner-measure (+ lhs-measure (measure:ft core/size inner (add1 depth))))
      (cond
        [(< idx lhs-measure) (define-values (idx^ l m r) (pvector-split-digit:impl lhs idx depth))
          (define left (digit-list->ft l depth))
          (match inner
            [(ft:empty) (values idx^ left m (digit-list2->ft (append r (digit-add-list rhs '())) depth))]
            [_
              (define-values (right inner^) (digit-list+ft->digit r inner depth hdL:impl))
              (values idx^ left m (build-ft0 core/size right inner^ rhs depth))])]
        [(< idx inner-measure)
          (define-values (rest-idx l m r) (pvector-split:impl inner (- idx lhs-measure) (add1 depth)))
          (define left (left-digit+ft->ft lhs l depth))
          (define right (right-digit+ft->ft rhs r depth))
          (define-values (idx^ l^ m^ r^) (pvector-split-node:impl m rest-idx (add1 depth)))
          (define left^ (for/fold ([init left]) ([i l^]) (consR:impl core/size init i)))
          (define right^ (for/foldr ([init right]) ([i r^]) (consL:impl core/size init i)))
          (values idx^ left^ m^ right^)]
        [(< idx v) (define-values (idx^ l m r) (pvector-split-digit:impl rhs (- idx inner-measure) depth))
          (define right (digit-list->ft r depth))
          (match inner
            [(ft:empty) (values idx^ (digit-list2->ft (append (digit-add-list lhs '()) l) depth) m right)]
            [_
              (define-values (left inner^) (digit-list+ft->digit r inner depth hdR:impl))
              (values idx^ (build-ft0 core/size lhs inner^ left depth) m right)])]
        [else (assert-unreachable)])]))

(define (vector->node3vector vec start len depth)
  (define new-length (quotient len 3))
  (define new-vec (make-vector new-length))
  (for ([i (in-range new-length)])
    (define x0 (vector-ref vec (+ start (* 3 i))))
    (define x1 (vector-ref vec (+ start 1 (* 3 i))))
    (define x2 (vector-ref vec (+ start 2 (* 3 i))))
    (vector-set! new-vec i (node:3 (+
        (measure:node core/size x0 depth)
        (measure:node core/size x1 depth)
        (measure:node core/size x2 depth))
      x0 x1 x2)))
  new-vec)

(define (vector->pvector:impl vec sz depth)
  (define vec-len (vector-length vec))
  (cond
    [(<= vec-len 8) (small-vector->pvector:impl vec depth)]
    [else
      (match (modulo vec-len 3)
        [0
          (define lhs (digit:3 (vector-ref vec 0) (vector-ref vec 1) (vector-ref vec 2)))
          (define rhs (digit:3 (vector-ref vec (- vec-len 3)) (vector-ref vec (- vec-len 2)) (vector-ref vec (- vec-len 1))))
          (define sub-sz (* 6 (measure:node core/size (vector-ref vec 0) depth)))
          (define mid (vector->node3vector vec 3 (- vec-len 6) depth))
          (ft:deep sz lhs (vector->pvector:impl mid (- sz sub-sz) (add1 depth)) rhs)]
        [1
          (define lhs (digit:4 (vector-ref vec 0) (vector-ref vec 1) (vector-ref vec 2) (vector-ref vec 3)))
          (define rhs (digit:3 (vector-ref vec (- vec-len 3)) (vector-ref vec (- vec-len 2)) (vector-ref vec (- vec-len 1))))
          (define sub-sz (* 7 (measure:node core/size (vector-ref vec 0) depth)))
          (define mid (vector->node3vector vec 4 (- vec-len 7) depth))
          (ft:deep sz lhs (vector->pvector:impl mid (- sz sub-sz) (add1 depth)) rhs)]
        [2
          (define lhs (digit:4 (vector-ref vec 0) (vector-ref vec 1) (vector-ref vec 2) (vector-ref vec 3)))
          (define rhs (digit:4 (vector-ref vec (- vec-len 4)) (vector-ref vec (- vec-len 3)) (vector-ref vec (- vec-len 2)) (vector-ref vec (- vec-len 1))))
          (define sub-sz (* 8 (measure:node core/size (vector-ref vec 0) depth)))
          (define mid (vector->node3vector vec 4 (- vec-len 8) depth))
          (ft:deep sz lhs (vector->pvector:impl mid (- sz sub-sz) (add1 depth)) rhs)])]))

(define (small-vector->pvector:impl vec depth)
  (define v (for/fold ([v 0]) ([k (in-vector vec)]) (+ v (measure:node core/size k depth))))
  (match vec
    [(vector) (ft:empty)]
    [(vector x0) (ft:single x0)]
    [(vector x0 x1) (ft:deep v (digit:1 x0) (pvector-empty) (digit:1 x1))]
    [(vector x0 x1 x2) (ft:deep v (digit:1 x0) (pvector-empty) (digit:2 x1 x2))]
    [(vector x0 x1 x2 x3) (ft:deep v (digit:2 x0 x1) (pvector-empty) (digit:2 x2 x3))]
    [(vector x0 x1 x2 x3 x4) (ft:deep v (digit:2 x0 x1) (pvector-empty) (digit:3 x2 x3 x4))]
    [(vector x0 x1 x2 x3 x4 x5) (ft:deep v (digit:3 x0 x1 x2) (pvector-empty) (digit:3 x3 x4 x5))]
    [(vector x0 x1 x2 x3 x4 x5 x6) (ft:deep v (digit:3 x0 x1 x2) (pvector-empty) (digit:4 x3 x4 x5 x6))]
    [(vector x0 x1 x2 x3 x4 x5 x6 x7) (ft:deep v (digit:4 x0 x1 x2 x3) (pvector-empty) (digit:4 x4 x5 x6 x7))]))

(define (vector->pvector vec)
  (vector->pvector:impl vec (vector-length vec) 0))

(define (pvector->vector pv)
  (define vec (make-vector (pvector-length pv)))
  (for ([i (in-range (pvector-length pv))])
    (vector-set! vec i (pvector-ref pv i)))
  vec)

(define (pvector-copy pv start end)
  (define len (- end start))
  (cond
    [(= len 0) (pvector-empty)]
    [(and (= start 0) (= end (pvector-length pv))) pv]
    [(= start 0) (match-define-values (l _ _) (pvector-split pv end)) l]
    [(= end (pvector-length pv)) (match-define-values (_ _ r) (pvector-split pv (sub1 start))) r]
    [else (match-define-values (l _ _) (pvector-split pv end))
      (match-define-values (_ _ r) (pvector-split l (sub1 start)))
      r]))

(define (pvector-empty? pv)
  (match pv
    [(ft:empty) #t]
    [_ #f]))

(define (pvector-take pv pos)
  (cond
    [(= pos (pvector-length pv)) pv]
    [else (match-define-values (l _ _) (pvector-split pv pos)) l]))

(define (pvector-take-right pv pos)
  (pvector-drop pv (- (pvector-length pv) pos)))

(define (pvector-drop pv pos)
  (cond
    [(= pos 0) pv]
    [else (match-define-values (_ _ r) (pvector-split pv (sub1 pos))) r]))

(define (pvector-drop-right pv pos)
  (pvector-take pv (- (pvector-length pv) pos)))

(define (pvector-split-at pv pos)
  (cond
    [(= pos (pvector-length pv)) (values pv (pvector-empty))]
    [else
      (match-define-values (l m r) (pvector-split pv pos))
      (values l (pvector-cons-left r m))]))

(define (pvector-split-at-right pv pos)
  (match-define-values (l r) (pvector-split-at pv (- (pvector-length pv) pos)))
  (values r l))

(define pvector? finger-tree?/c)

(define (pvector-insert-ft:impl ft idx value depth)
  (match ft
    [(ft:single x)
      (define-values (x0 x1) (pvector-insert-node:impl x idx value depth))
      (if x1 (ft:deep (add1 (measure:ft core/size ft depth)) (digit:1 x0) (ft:empty) (digit:1 x1)) (ft:single x0))]
    [(ft:deep o left inner right)
      (define left-size (measure:digit core/size left depth))
      (define inner-size (measure:ft core/size inner (add1 depth)))
      (define left-inner-size (+ left-size inner-size))
      (cond
        [(<= left-inner-size idx)
          (define right^ (pvector-insert-digit:impl right (- idx left-inner-size) value depth))
          (match right^
            [`(,x0 ,x1 ,x2, x3 ,x4)
              (define right-pop (build-node3 core/size x0 x1 x2 depth))
              (define inner^ (consR:impl core/size inner right-pop (add1 depth)))
              (ft:deep (add1 o) left inner^ (digit:2 x3 x4))]
            [_ (ft:deep (add1 o) left inner (list->digit right^ depth))])]
        [(<= left-size idx)
          (define inner^ (pvector-insert-ft:impl inner (- idx left-size) value (add1 depth)))
          (ft:deep (add1 o) left inner^ right)]
        [else
          (define left^ (pvector-insert-digit:impl left idx value depth))
          (match left^
            [`(,x0 ,x1 ,x2, x3 ,x4)
              (define left-pop (build-node3 core/size x2 x3 x4 depth))
              (define inner^ (consL:impl core/size inner left-pop (add1 depth)))
              (ft:deep (add1 o) (digit:2 x0 x1) inner^ right)]
            [_ (ft:deep (add1 o) (list->digit left^ depth) inner right)])])]))

(define (pvector-insert-digit:impl digit idx value depth)
  (define l (digit->list digit))
  (match-define-values (r _ i)
    (for/fold ([rst '()] [idx idx] [ignore #f]) ([i l])
      (define s (measure:node core/size i depth))
      (cond
        [ignore
          (values (cons i rst) idx ignore)]
        [(<= s idx)
          (values (cons i rst) (- idx s) ignore)]
        [else
          (define-values (x0 x1) (pvector-insert-node:impl i idx value depth))
          (if x1
            (values (cons x1 (cons x0 rst)) idx #t)
            (values (cons x0 rst) idx #t))])))
  (unless i (assert-unreachable))
  (reverse r))

(define (pvector-insert-node:impl node idx value depth)
  (match depth
    [0 (values value node)]
    [_ (match node
      [(node:2 i x0 x1)
        (define x0-size (measure:node core/size x0 (sub1 depth)))
        (cond
          [(<= x0-size idx)
            (define-values (x1^ x2^) (pvector-insert-node:impl x1 (- idx x0-size) value (sub1 depth)))
            (values (if x2^ (node:3 (add1 i) x0 x1^ x2^) (node:2 (add1 i) x0 x1^)) #f)]
          [else
            (define-values (x0^ x1^) (pvector-insert-node:impl x0 idx value (sub1 depth)))
            (values (if x1^ (node:3 (add1 i) x0^ x1^ x1) (node:2 (add1 i) x0^ x1)) #f)])]
      [(node:3 i x0 x1 x2)
        (define x0-size (measure:node core/size x0 (sub1 depth)))
        (define x1-size (measure:node core/size x1 (sub1 depth)))
        (define x0-x1-size (+ x0-size x1-size))
        (cond
          [(<= x0-x1-size idx)
            (define-values (x2^ x3^)
              (pvector-insert-node:impl x2 (- idx x0-x1-size) value (sub1 depth)))
            (if x3^ (values (node:2 x0-x1-size x0 x1) (node:2 (+
                (measure:node core/size x2^ (sub1 depth)) (measure:node core/size x3^ (sub1 depth)))
                x2^ x3^))
              (values (node:3 (+ i 1) x0 x1 x2^) #f))]
          [(<= x0-size idx)
            (define-values (x1^ x2^)
              (pvector-insert-node:impl x1 (- idx x0-size) value (sub1 depth)))
            (if x2^ (values (node:2 (+ x0-size (measure:node core/size x1^ (sub1 depth))) x0 x1^)
              (node:2 (+ (measure:node core/size x2^ (sub1 depth)) (measure:node core/size x2 (sub1 depth)))
                x2^ x2))
              (values (node:3 (+ i 1) x0 x1 x2^) #f))]
          [else
            (define-values (x0^ x1^) (pvector-insert-node:impl x0 idx value (sub1 depth)))
            (if x1^ (values (node:2 (+ (measure:node core/size x0^ (sub1 depth)) (measure:node core/size x1^ (sub1 depth))) x0^ x1^)
              (node:2 (+ (measure:node core/size x1 (sub1 depth)) (measure:node core/size x2 (sub1 depth)))
                x1 x2))
              (values (node:3 (+ i 1) x0^ x1 x2) #f))])])]))

(define (pvector-insert ft idx value)
  (define ft-size (measure:ft core/size ft 0))
  (cond
    [(= ft-size idx) (consR:impl core/size ft value 0)]
    [(< ft-size idx) (error 'ArgumentError "insert invalid pos ~a in ft (sz ~a)" idx ft-size)]
    [else (pvector-insert-ft:impl ft idx value 0)]))

(define (pvector-delete ft idx)
  (match-define-values (l v r) (pvector-split ft idx))
  (values (pvector-append l r) v))

;; New functions: list conversion
(define (list->pvector lst)
  (vector->pvector (list->vector lst)))

(define (pvector->list pv)
  (for/list ([v (in-pvector pv)]) v))

;; Exports
(provide pvector-delete)
(provide pvector? pvector-empty?)
(provide pvector-take pvector-take-right pvector-drop pvector-drop-right pvector-split-at pvector-split-at-right)
(provide pvector-copy)
(provide pvector-view-left pvector-view-right)
(provide pvector-empty pvector-cons-left pvector-cons-right pvector-pop-left pvector-pop-right pvector-split pvector-append)
(provide pvector-ref pvector-set pvector-length)
(provide in-pvector in-pvector-reverse in-pvector/index)
(provide vector->pvector pvector->vector)
(provide list->pvector pvector->list)
(provide pvector-insert)
