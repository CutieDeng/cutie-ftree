#lang racket/base

(require "core.rkt" racket/match)

(define (measure:node f n depth)
  (match depth
    [0 (match-define (ft:config _ m _) f) (m n)]
    [_ (match n
        [(node:2 v _ _) v]
        [(node:3 v _ _ _) v]
      )]
  )
)

(define (measure:ft f ft depth)
  (match ft
    [(ft:deep v _ _ _) v]
    [(ft:single a) (measure:node f a depth)]
    [(ft:empty) (match-define (ft:config e _ _) f) (e)]
  )
)

(define (measure:digit f d depth)
  (match-define (ft:config _ _ as) f)
  (match d
    [(digit:1 a)
      (measure:node f a depth)]
    [(digit:2 a b)
      (as (measure:node f a depth) (measure:node f b depth))]
    [(digit:3 a b c)
      (as (as (measure:node f a depth) (measure:node f b depth)) (measure:node f c depth))]
    [(digit:4 a b c d)
      (as (as (measure:node f a depth) (measure:node f b depth))
        (as (measure:node f c depth) (measure:node f d depth)))]
  )
)

(define (consL:impl core ft v [depth 0])
  (match ft
    [(ft:empty) (ft:single v)]
    [(ft:single a)
      (match-define (ft:config _ m as) core)
      (define v^ (as (measure:node core v depth) (measure:node core a depth)))
      (ft:deep v^ (digit:1 v) (ft:empty) (digit:1 a))
    ]
    [(ft:deep v^ left inner right)
      (match-define (ft:config _ m as) core)
      (define v^^ (as (measure:node core v depth) v^))
      (match left
        [(digit:4 a b c d)
          (define left^ (digit:2 v a))
          (define n (node:3 (as
            (as (measure:node core b depth) (measure:node core c depth))
            (measure:node core d depth))
            b c d))
          (define inner^ (consL:impl core inner n (+ depth 1)))
          (ft:deep v^^ left^ inner^ right)
        ]
        [_
          (define left^ (match left
            [(digit:1 a) (digit:2 v a)]
            [(digit:2 a b) (digit:3 v a b)]
            [(digit:3 a b c) (digit:4 v a b c)]
          ))
          (ft:deep v^^ left^ inner right)
        ]
      )
    ]
  )
)

(define (consR:impl core ft v [depth 0])
  (match ft
    [(ft:empty) (ft:single v)]
    [(ft:single a)
      (match-define (ft:config _ _ as) core)
      (define v^ (as (measure:node core a depth) (measure:node core v depth)))
      (ft:deep v^ (digit:1 a) (ft:empty) (digit:1 v))
    ]
    [(ft:deep v^ left inner right)
      (match-define (ft:config _ _ as) core)
      (define v^^ (as v^ (measure:node core v depth)))
      (match right
        [(digit:4 a b c d)
          (define right^ (digit:2 d v))
          (define n (node:3 (as
            (as (measure:node core a depth) (measure:node core b depth))
            (measure:node core c depth))
            a b c))
          (define inner^ (consR:impl core inner n (+ depth 1)))
          (ft:deep v^^ left inner^ right^)
        ]
        [_
          (define right^ (match right
            [(digit:1 a) (digit:2 a v)]
            [(digit:2 a b) (digit:3 a b v)]
            [(digit:3 a b c) (digit:4 a b c v)]
          ))
          (ft:deep v^^ left inner right^)
        ]
      )
    ]
  )
)

(define (hdL:impl core ft [depth 0])
  (match ft
    [(ft:empty)
      (values #f ft)
    ]
    [(ft:single a)
      (values a (ft:empty))
    ]
    [(ft:deep _ (digit:1 a) (ft:empty) (digit:1 b))
      (values a (ft:single b))
    ]
    [(ft:deep _ (digit:1 a) (ft:empty) right)
      (match-define (ft:config _ _ as) core)
      (match right
        [(digit:2 b c)
          (values a (ft:deep (as (measure:node core b depth) (measure:node core c depth))
            (digit:1 b) (ft:empty) (digit:1 c)))
        ]
        [(digit:3 b c d)
          (values a (ft:deep
            (as (as (measure:node core b depth) (measure:node core c depth)) (measure:node core d depth))
            (digit:1 b) (ft:empty) (digit:2 c d)))
        ]
        [(digit:4 b c d e)
          (values a (ft:deep
            (as
              (as (measure:node core b depth) (measure:node core c depth))
              (as (measure:node core d depth) (measure:node core e depth)))
            (digit:2 b c) (ft:empty) (digit:2 d e)))
        ]
      )
    ]
    [(ft:deep _ (digit:1 a) inner right)
      (define-values (lhs inner^) (hdL:impl core inner (+ depth 1)))
      (match-define (ft:config _ _ as) core)
      (define-values (left-v left-digit) (match lhs
        [(node:2 v b c) (values v (digit:2 b c))]
        [(node:3 v b c d) (values v (digit:3 b c d))]
        ))
      (values a (ft:deep (as left-v (as (measure:ft core inner (add1 depth)) (measure:digit core right depth)))
        left-digit
        inner^
        right
      ))
    ]
    [(ft:deep _ left inner right)
      (define-values (h lhs^) (match left
        [(digit:2 a b) (values a (digit:1 b))]
        [(digit:3 a b c) (values a (digit:2 b c))]
        [(digit:4 a b c d) (values a (digit:3 b c d))]
      ))
      (match-define (ft:config _ _ as) core)
      (values h (ft:deep
        (as (measure:digit core lhs^ depth) (as (measure:ft core inner (+ depth 1))
          (measure:digit core right depth)))
        lhs^
        inner
        right
      ))
    ]
  )
)

(define (debug:getMaxDepth:impl core ft [depth 0])
  (match ft
    [(ft:deep _ _ inner _)
      (debug:getMaxDepth:impl core inner (+ depth 1))
    ]
    [(or (ft:empty) (ft:single _)) depth]
  )
)

(define (hdR:impl core ft [depth 0])
  (match ft
    [(ft:empty)
      (values #f ft)
    ]
    [(ft:single a)
      (values a (ft:empty))
    ]
    [(ft:deep _ (digit:1 a) (ft:empty) (digit:1 b))
      (values b (ft:single a))
    ]
    [(ft:deep _ left (ft:empty) (digit:1 a))
      (match-define (ft:config _ _ as) core)
      (match left
        [(digit:2 b c)
          (values a (ft:deep (as (measure:node core b depth) (measure:node core c depth))
            (digit:1 b) (ft:empty) (digit:1 c)))
        ]
        [(digit:3 b c d)
          (values a (ft:deep
            (as (as (measure:node core b depth) (measure:node core c depth)) (measure:node core d depth))
            (digit:1 b) (ft:empty) (digit:2 c d)))
        ]
        [(digit:4 b c d e)
          (values a (ft:deep
            (as
              (as (measure:node core b depth) (measure:node core c depth))
              (as (measure:node core d depth) (measure:node core e depth)))
            (digit:2 b c) (ft:empty) (digit:2 d e)))
        ]
      )
    ]
    [(ft:deep _ left inner (digit:1 a))
      (define-values (rhs inner^) (hdR:impl core inner (add1 depth)))
      (match-define (ft:config _ _ as) core)
      (define-values (right-v right-digit) (match rhs
        [(node:2 v b c) (values v (digit:2 b c))]
        [(node:3 v b c d) (values v (digit:3 b c d))]
        ))
      (values a (ft:deep (as (measure:digit core left depth) (as (measure:ft core inner (add1 depth)) right-v))
        left
        inner^
        right-digit
      ))
    ]
    [(ft:deep _ lhs inner right)
      (define-values (h rhs^) (match right
        [(digit:2 a b) (values b (digit:1 a))]
        [(digit:3 a b c) (values c (digit:2 a b))]
        [(digit:4 a b c d) (values d (digit:3 a b c))]
      ))
      (match-define (ft:config _ _ as) core)
      (values h (ft:deep
        (as (as (measure:digit core lhs depth) (measure:ft core inner (+ depth 1)))
          (measure:digit core rhs^ depth))
        lhs
        inner
        rhs^
      ))
    ]
  )
)

(define (digit-add-list digit rest)
  (match digit
    [(digit:1 a) (cons a rest)]
    [(digit:2 a b) (append (list a b) rest)]
    [(digit:3 a b c) (append (list a b c) rest)]
    [(digit:4 a b c d) (append (list a b c d) rest)]
  )
)

(define (digit->list digit)
  (match digit
    [(digit:1 a) (list a)]
    [(digit:2 a b) (list a b)]
    [(digit:3 a b c) (list a b c)]
    [(digit:4 a b c d) (list a b c d)]
  )
)


; 2 .. 8
(define (list->nodes:impl core rest depth)
  (match-define (ft:config _ _ as) core)
  (printf "rest: ~a\n" rest)
  (match rest
    [`(,a ,b ,c ,d) (list
      (node:2 (as (measure:node core a depth) (measure:node core b depth)) a b)
      (node:2 (as (measure:node core c depth) (measure:node core d depth)) c d))]
    [`(,a ,b ,c) (list (node:3
      (as (measure:node core a depth) (as (measure:node core b depth) (measure:node core c depth)))
      a b c))]
    [`(,a ,b) (list (node:2
      (as (measure:node core a depth) (measure:node core b depth))
      a b))]
    [`(,a ,b ,c ,r ...)
      (cons
        (node:3 (as (measure:node core a depth) (as (measure:node core b depth) (measure:node core c depth))) a b c)
        (list->nodes:impl core r depth))]
  )
)

(define (concat:impl core lhs rhs [depth 0])
  (match* (lhs rhs)
    [(_ (ft:empty)) lhs]
    [((ft:empty) _) rhs]
    [((ft:single a) _) (consL:impl core rhs a depth)]
    [(_ (ft:single a)) (consR:impl core lhs a depth)]
    [((ft:deep lhs-v lhs-left lhs-inner lhs-right) (ft:deep rhs-v rhs-left rhs-inner rhs-right))
      (define mid (digit-add-list lhs-right (digit-add-list rhs-left '())))
      (define mid^ (list->nodes:impl core mid depth))
      (define left-inner^ (for/fold ([i lhs-inner]) ([m mid^])
        (consR:impl core i m depth)
      ))
      (define inner^ (concat:impl core left-inner^ rhs-inner (add1 depth)))
      (match-define (ft:config _ _ as) core)
      (define v^ (as lhs-v rhs-v))
      (ft:deep v^ lhs-left inner^ rhs-right)
    ]
  )
)

(define (build-ft0 core lhs inner rhs depth)
  (match-define (ft:config _ _ as) core)
  (define lhs-measure (measure:digit core lhs depth))
  (define mid (measure:ft core inner (add1 depth)))
  (define rhs-measure (measure:digit core rhs depth))
  (define v (as lhs-measure (as mid rhs-measure)))
  (ft:deep v lhs inner rhs)
)

(define (hdL-view ft)
  (match ft
    [(ft:single a) a]
    [(ft:deep _ a _ _) (match a
      [(or (digit:1 x) (digit:2 x _) (digit:3 x _ _) (digit:4 x _ _ _)) x]
    )]
  )
)

(define (hdR-view ft)
  (match ft
    [(ft:single a) a]
    [(ft:deep _ _ _ a) (match a
      [(or (digit:1 x) (digit:2 _ x) (digit:3 _ _ x) (digit:4 _ _ _ x)) x]
    )]
  )
)


(define (list->digit lst _depth)
  (match lst
    [`(,a ,b ,c ,d) (digit:4 a b c d)]
    [`(,a ,b ,c) (digit:3 a b c)]
    [`(,a ,b) (digit:2 a b)]
    [`(,a) (digit:1 a)]
  )
)

(define (build-digit-from-list lst)
  (match lst
    [`(,a ,b ,c ,d) (digit:4 a b c d)]
    [`(,a ,b ,c) (digit:3 a b c)]
    [`(,a ,b) (digit:2 a b)]
    [`(,a) (digit:1 a)]
  )
)

(define (build-node3 core x0 x1 x2 depth)
  (match-define (ft:config _ _ as) core)
  (define c (as (as (measure:node core x0 depth) (measure:node core x1 depth))
    (measure:node core x2 depth)))
  (node:3 c x0 x1 x2)
)

(define (build-node2 core x0 x1 depth)
  (match-define (ft:config _ _ as) core)
  (define c (as (measure:node core x0 depth) (measure:node core x1 depth)) )
  (node:2 c x0 x1)
)

;; ========================================
;; Zero-allocation digit iteration API
;; ========================================

;; digit-fold-left: fold over digit elements left-to-right
;; (digit-fold-left digit init (lambda (acc elem) ...)) -> acc
(define (digit-fold-left digit init f)
  (match digit
    [(digit:1 a) (f init a)]
    [(digit:2 a b) (f (f init a) b)]
    [(digit:3 a b c) (f (f (f init a) b) c)]
    [(digit:4 a b c d) (f (f (f (f init a) b) c) d)]))

;; digit-fold-right: fold over digit elements right-to-left
;; (digit-fold-right digit init (lambda (elem acc) ...)) -> acc
(define (digit-fold-right digit init f)
  (match digit
    [(digit:1 a) (f a init)]
    [(digit:2 a b) (f a (f b init))]
    [(digit:3 a b c) (f a (f b (f c init)))]
    [(digit:4 a b c d) (f a (f b (f c (f d init))))]))

;; digit-for-each: iterate over digit elements (for side effects)
(define (digit-for-each digit f)
  (match digit
    [(digit:1 a) (f a)]
    [(digit:2 a b) (f a) (f b)]
    [(digit:3 a b c) (f a) (f b) (f c)]
    [(digit:4 a b c d) (f a) (f b) (f c) (f d)]))

;; digit-find-by-measure: find element where accumulated measure exceeds target
;; Returns (values remaining-idx found-element)
;; measure-fn: node -> integer (size/measure of node)
(define (digit-find-by-measure digit idx measure-fn)
  (match digit
    [(digit:1 a)
      (values idx a)]
    [(digit:2 a b)
      (define a-sz (measure-fn a))
      (if (< idx a-sz)
        (values idx a)
        (values (- idx a-sz) b))]
    [(digit:3 a b c)
      (define a-sz (measure-fn a))
      (if (< idx a-sz)
        (values idx a)
        (let ([idx (- idx a-sz)])
          (define b-sz (measure-fn b))
          (if (< idx b-sz)
            (values idx b)
            (values (- idx b-sz) c))))]
    [(digit:4 a b c d)
      (define a-sz (measure-fn a))
      (if (< idx a-sz)
        (values idx a)
        (let ([idx (- idx a-sz)])
          (define b-sz (measure-fn b))
          (if (< idx b-sz)
            (values idx b)
            (let ([idx (- idx b-sz)])
              (define c-sz (measure-fn c))
              (if (< idx c-sz)
                (values idx c)
                (values (- idx c-sz) d))))))]))

;; digit-update-by-measure: update element at accumulated measure position
;; Returns new digit with updated element
;; update-fn: (node remaining-idx) -> new-node
(define (digit-update-by-measure digit idx measure-fn update-fn)
  (match digit
    [(digit:1 a)
      (digit:1 (update-fn a idx))]
    [(digit:2 a b)
      (define a-sz (measure-fn a))
      (if (< idx a-sz)
        (digit:2 (update-fn a idx) b)
        (digit:2 a (update-fn b (- idx a-sz))))]
    [(digit:3 a b c)
      (define a-sz (measure-fn a))
      (if (< idx a-sz)
        (digit:3 (update-fn a idx) b c)
        (let ([idx (- idx a-sz)])
          (define b-sz (measure-fn b))
          (if (< idx b-sz)
            (digit:3 a (update-fn b idx) c)
            (digit:3 a b (update-fn c (- idx b-sz))))))]
    [(digit:4 a b c d)
      (define a-sz (measure-fn a))
      (if (< idx a-sz)
        (digit:4 (update-fn a idx) b c d)
        (let ([idx (- idx a-sz)])
          (define b-sz (measure-fn b))
          (if (< idx b-sz)
            (digit:4 a (update-fn b idx) c d)
            (let ([idx (- idx b-sz)])
              (define c-sz (measure-fn c))
              (if (< idx c-sz)
                (digit:4 a b (update-fn c idx) d)
                (digit:4 a b c (update-fn d (- idx c-sz))))))))]))

;; node-fold-left: fold over node children left-to-right
(define (node-fold-left node init f)
  (match node
    [(node:2 _ a b) (f (f init a) b)]
    [(node:3 _ a b c) (f (f (f init a) b) c)]))

;; node-fold-right: fold over node children right-to-left
(define (node-fold-right node init f)
  (match node
    [(node:2 _ a b) (f a (f b init))]
    [(node:3 _ a b c) (f a (f b (f c init)))]))

;; node-find-by-measure: find child in node by accumulated measure
(define (node-find-by-measure node idx measure-fn)
  (match node
    [(node:2 _ a b)
      (define a-sz (measure-fn a))
      (if (< idx a-sz)
        (values idx a)
        (values (- idx a-sz) b))]
    [(node:3 _ a b c)
      (define a-sz (measure-fn a))
      (if (< idx a-sz)
        (values idx a)
        (let ([idx (- idx a-sz)])
          (define b-sz (measure-fn b))
          (if (< idx b-sz)
            (values idx b)
            (values (- idx b-sz) c))))]))

;; node-update-by-measure: update child in node by accumulated measure
(define (node-update-by-measure node idx measure-fn update-fn rebuild-fn)
  (match node
    [(node:2 _ a b)
      (define a-sz (measure-fn a))
      (if (< idx a-sz)
        (rebuild-fn (update-fn a idx) b)
        (rebuild-fn a (update-fn b (- idx a-sz))))]
    [(node:3 _ a b c)
      (define a-sz (measure-fn a))
      (if (< idx a-sz)
        (rebuild-fn (update-fn a idx) b c)
        (let ([idx (- idx a-sz)])
          (define b-sz (measure-fn b))
          (if (< idx b-sz)
            (rebuild-fn a (update-fn b idx) c)
            (rebuild-fn a b (update-fn c (- idx b-sz))))))]))

(provide measure:node measure:ft measure:digit)
(provide consL:impl consR:impl hdL:impl hdR:impl concat:impl)
(provide digit-add-list digit->list)
(provide hdL-view hdR-view)
(provide build-node2 build-node3)
(provide build-digit-from-list list->digit)
(provide build-ft0)

;; New zero-allocation API
(provide digit-fold-left digit-fold-right digit-for-each)
(provide digit-find-by-measure digit-update-by-measure)
(provide node-fold-left node-fold-right)
(provide node-find-by-measure node-update-by-measure)
