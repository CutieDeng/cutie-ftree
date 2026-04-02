#lang racket/base

(require "core.rkt" racket/match)

(define (measure:node f n depth)
  (match depth
    [0 (match-define (ft:config _ m _) f) (m n)]
    [_
     (match n
        [(node:2 v _ _) v]
        [(node:3 v _ _ _) v]
        ) ; match: n
     ]
    ) ; match: depth
  ) ; define measure:node

(define (measure:ft f ft depth)
  (match ft
    [(ft:deep v _ _ _) v]
    [(ft:single a) (measure:node f a depth)]
    [(ft:empty) (match-define (ft:config e _ _) f) (e)]
    ) ; match: ft
  ) ; define measure:ft

(define (measure:digit f d depth)
  (match-define (ft:config _ _ as) f)
  (match d
    [(digit:1 a)
      (measure:node f a depth)]
    [(digit:2 a b)
      (define am (measure:node f a depth))
      (define bm (measure:node f b depth))
      (as am bm)]
    [(digit:3 a b c)
      (define am (measure:node f a depth))
      (define bm (measure:node f b depth))
      (define cm (measure:node f c depth))
      (as (as am bm) cm)]
    [(digit:4 a b c d)
      (define am (measure:node f a depth))
      (define bm (measure:node f b depth))
      (define cm (measure:node f c depth))
      (define dm (measure:node f d depth))
      (as (as am bm)
          (as cm dm))
    ]
    ) ; match: d
  ) ; define measure:digit

(define (consL:impl core ft v [depth 0])
  (match ft
    [(ft:empty) (ft:single v)]
    [(ft:single a)
      (match-define (ft:config _ m as) core)
      (define vm (measure:node core v depth))
      (define am (measure:node core a depth))
      (define v^ (as vm am))
      (ft:deep v^ (digit:1 v) (ft:empty) (digit:1 a))
    ]
    [(ft:deep v^ left inner right)
      (match-define (ft:config _ m as) core)
      (define v^^ (as (measure:node core v depth) v^))
      (match left
        [(digit:4 a b c d)
          (define left^ (digit:2 v a))
          (define bm (measure:node core b depth))
          (define cm (measure:node core c depth))
          (define dm (measure:node core d depth))
          (define n (node:3 (as
            (as bm cm)
            dm)
            b c d))
          (define inner-depth (add1 depth))
          (define inner^ (consL:impl core inner n inner-depth))
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
        ) ; match: left
    ]
    ) ; match: ft
  ) ; define consL:impl

(define (consR:impl core ft v [depth 0])
  (match ft
    [(ft:empty) (ft:single v)]
    [(ft:single a)
      (match-define (ft:config _ _ as) core)
      (define am (measure:node core a depth))
      (define vm (measure:node core v depth))
      (define v^ (as am vm))
      (ft:deep v^ (digit:1 a) (ft:empty) (digit:1 v))
    ]
    [(ft:deep v^ left inner right)
      (match-define (ft:config _ _ as) core)
      (define vm (measure:node core v depth))
      (define v^^ (as v^ vm))
      (match right
        [(digit:4 a b c d)
          (define right^ (digit:2 d v))
          (define am (measure:node core a depth))
          (define bm (measure:node core b depth))
          (define cm (measure:node core c depth))
          (define n (node:3 (as
            (as am bm)
            cm)
            a b c))
          (define inner-depth (add1 depth))
          (define inner^ (consR:impl core inner n inner-depth))
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
        ) ; match: right
    ]
    ) ; match: ft
  ) ; define consR:impl

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
          (define bm (measure:node core b depth))
          (define cm (measure:node core c depth))
          (define v^ (as bm cm))
          (define empty-inner (ft:empty))
          (define tree^
            (ft:deep v^
                     (digit:1 b)
                     empty-inner
                     (digit:1 c)
                     ) ; ft:deep
            ) ; define tree^
          (values a tree^)
        ]
        [(digit:3 b c d)
          (define bm (measure:node core b depth))
          (define cm (measure:node core c depth))
          (define dm (measure:node core d depth))
          (define v^ (as (as bm cm) dm))
          (define empty-inner (ft:empty))
          (define tree^
            (ft:deep v^
                     (digit:1 b)
                     empty-inner
                     (digit:2 c d)
                     ))
          (values a tree^)
        ]
        [(digit:4 b c d e)
          (define bm (measure:node core b depth))
          (define cm (measure:node core c depth))
          (define dm (measure:node core d depth))
          (define em (measure:node core e depth))
          (define dm+em (as dm em))
          (define v^ (as (as bm cm) dm+em))
          (define empty-inner (ft:empty))
          (define tree^
            (ft:deep v^
                     (digit:2 b c)
                     empty-inner
                     (digit:2 d e)
                     ))
          (values a tree^)
        ]
      )
    ]
    [(ft:deep _ (digit:1 a) inner right)
      (define inner-depth (add1 depth))
      (define-values (lhs inner^) (hdL:impl core inner inner-depth))
      (match-define (ft:config _ _ as) core)
      (define-values (left-v left-digit) (match lhs
        [(node:2 v b c)
         (define left^ (digit:2 b c))
         (values v left^)]
        [(node:3 v b c d)
         (define left^ (digit:3 b c d))
         (values v left^)]
        )) ; match: lhs
      (define inner-m (measure:ft core inner^ inner-depth))
      (define right-m (measure:digit core right depth))
      (define tail (as inner-m right-m))
      (define total (as left-v tail))
      (values
       a
       (ft:deep total left-digit inner^ right))
    ]
    [(ft:deep _ left inner right)
      (define-values (h lhs^) (match left
        [(digit:2 a b)
         (define lhs^^ (digit:1 b))
         (values a lhs^^)]
        [(digit:3 a b c)
         (define lhs^^ (digit:2 b c))
         (values a lhs^^)]
        [(digit:4 a b c d)
         (define lhs^^ (digit:3 b c d))
         (values a lhs^^)]
      )) ; match: left
      (match-define (ft:config _ _ as) core)
      (define left-m (measure:digit core lhs^ depth))
      (define inner-depth (add1 depth))
      (define inner-m (measure:ft core inner inner-depth))
      (define right-m (measure:digit core right depth))
      (define tail (as inner-m right-m))
      (define total (as left-m tail))
      (values
       h
       (ft:deep total lhs^ inner right))
    ]
    ) ; match: ft
  ) ; define hdL:impl

(define (debug:getMaxDepth:impl core ft [depth 0])
  (match ft
    [(ft:deep _ _ inner _)
      (debug:getMaxDepth:impl core inner (+ depth 1))
    ]
    [(or (ft:empty) (ft:single _)) depth]
    ) ; match: ft
  ) ; define debug:getMaxDepth:impl

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
          (define bm (measure:node core b depth))
          (define cm (measure:node core c depth))
          (define v^ (as bm cm))
          (define empty-inner (ft:empty))
          (define tree^
            (ft:deep v^
                     (digit:1 b)
                     empty-inner
                     (digit:1 c)
                     ) ; ft:deep
            ) ; define tree^
          (values a tree^)
        ]
        [(digit:3 b c d)
          (define bm (measure:node core b depth))
          (define cm (measure:node core c depth))
          (define dm (measure:node core d depth))
          (define v^ (as (as bm cm) dm))
          (define empty-inner (ft:empty))
          (define tree^
            (ft:deep v^
                     (digit:1 b)
                     empty-inner
                     (digit:2 c d)
                     ))
          (values a tree^)
        ]
        [(digit:4 b c d e)
          (define bm (measure:node core b depth))
          (define cm (measure:node core c depth))
          (define dm (measure:node core d depth))
          (define em (measure:node core e depth))
          (define dm+em (as dm em))
          (define v^ (as (as bm cm) dm+em))
          (define empty-inner (ft:empty))
          (define tree^
            (ft:deep v^
                     (digit:2 b c)
                     empty-inner
                     (digit:2 d e)
                     ))
          (values a tree^)
        ]
      )
    ]
    [(ft:deep _ left inner (digit:1 a))
      (define inner-depth (add1 depth))
      (define-values (rhs inner^) (hdR:impl core inner inner-depth))
      (match-define (ft:config _ _ as) core)
      (define-values (right-v right-digit) (match rhs
        [(node:2 v b c)
         (define right^ (digit:2 b c))
         (values v right^)]
        [(node:3 v b c d)
         (define right^ (digit:3 b c d))
         (values v right^)]
        )) ; match: rhs
      (define left-m (measure:digit core left depth))
      (define mid-m (measure:ft core inner^ inner-depth))
      (define tail (as mid-m right-v))
      (define total (as left-m tail))
      (values
       a
       (ft:deep total left inner^ right-digit))
    ]
    [(ft:deep _ lhs inner right)
      (define-values (h rhs^) (match right
        [(digit:2 a b)
         (define rhs^^ (digit:1 a))
         (values b rhs^^)]
        [(digit:3 a b c)
         (define rhs^^ (digit:2 a b))
         (values c rhs^^)]
        [(digit:4 a b c d)
         (define rhs^^ (digit:3 a b c))
         (values d rhs^^)]
      )) ; match: right
      (match-define (ft:config _ _ as) core)
      (define lhs-m (measure:digit core lhs depth))
      (define inner-depth (add1 depth))
      (define inner-m (measure:ft core inner inner-depth))
      (define rhs-m (measure:digit core rhs^ depth))
      (values
       h
       (ft:deep
        (as (as lhs-m inner-m) rhs-m)
        lhs
        inner
        rhs^))
    ]
    ) ; match: ft
  ) ; define hdR:impl

(define (digit-add-list digit rest)
  (match digit
    [(digit:1 a) (cons a rest)]
    [(digit:2 a b) (append (list a b) rest)]
    [(digit:3 a b c) (append (list a b c) rest)]
    [(digit:4 a b c d) (append (list a b c d) rest)]
    ) ; match: digit
  ) ; define digit-add-list

(define (digit->list digit)
  (match digit
    [(digit:1 a) (list a)]
    [(digit:2 a b) (list a b)]
    [(digit:3 a b c) (list a b c)]
    [(digit:4 a b c d) (list a b c d)]
    ) ; match: digit
  ) ; define digit->list


; 2 .. 8
(define (list->nodes:impl core rest depth)
  (match-define (ft:config _ _ as) core)
  (match rest
   [`(,a ,b ,c ,d)
     (define am (measure:node core a depth))
     (define bm (measure:node core b depth))
     (define cm (measure:node core c depth))
     (define dm (measure:node core d depth))
     (define left-v (as am bm))
     (define right-v (as cm dm))
     (define left-node (node:2 left-v a b))
     (define right-node (node:2 right-v c d))
     (list left-node right-node)]
    [`(,a ,b ,c)
     (define am (measure:node core a depth))
     (define bm (measure:node core b depth))
     (define cm (measure:node core c depth))
     (define mid-v (as bm cm))
     (list
      (node:3
       (as am mid-v)
       a
       b
       c)
     )]
    [`(,a ,b)
      (define am (measure:node core a depth))
      (define bm (measure:node core b depth))
      (define ab-v (as am bm))
      (list
       (node:2
       ab-v
       a
       b)
     )]
    [`(,a ,b ,c ,r ...)
      (define am (measure:node core a depth))
      (define bm (measure:node core b depth))
      (define cm (measure:node core c depth))
      (define mid-v (as bm cm))
     (cons
        (node:3
         (as am mid-v)
         a
         b
         c)
        (list->nodes:impl core r depth)
      )]
    ) ; match: rest
  ) ; define list->nodes:impl

(define (concat:impl core lhs rhs [depth 0])
  (match* (lhs rhs)
    [(_ (ft:empty)) lhs]
    [((ft:empty) _) rhs]
    [((ft:single a) _) (consL:impl core rhs a depth)]
    [(_ (ft:single a)) (consR:impl core lhs a depth)]
    [((ft:deep lhs-v lhs-left lhs-inner lhs-right) (ft:deep rhs-v rhs-left rhs-inner rhs-right))
      (define empty-list '())
      (define rhs-left-list (digit-add-list rhs-left empty-list))
      (define mid (digit-add-list lhs-right rhs-left-list))
      (define mid^ (list->nodes:impl core mid depth))
      ;; mid^ contains nodes at depth+1, so consR into inner at depth+1
      (define inner-depth (add1 depth))
      (define left-inner^
        (for/fold ([i lhs-inner]) ([m mid^])
          (consR:impl core i m inner-depth)
        )) ; for/fold
      (define inner^ (concat:impl core left-inner^ rhs-inner inner-depth))
      (match-define (ft:config _ _ as) core)
      (define v^ (as lhs-v rhs-v))
      (ft:deep v^ lhs-left inner^ rhs-right)
    ]
    ) ; match*: lhs rhs
  ) ; define concat:impl

(define (build-ft0 core lhs inner rhs depth)
  (match-define (ft:config _ _ as) core)
  (define lhs-measure (measure:digit core lhs depth))
  (define inner-depth (add1 depth))
  (define mid (measure:ft core inner inner-depth))
  (define rhs-measure (measure:digit core rhs depth))
  (define mid+rhs (as mid rhs-measure))
  (define v (as lhs-measure mid+rhs))
  (ft:deep v lhs inner rhs)) ; define build-ft0

(define (hdL-view ft)
  (match ft
    [(ft:single a) a]
    [(ft:deep _ a _ _)
     (match a
       [(or (digit:1 x) (digit:2 x _) (digit:3 x _ _) (digit:4 x _ _ _)) x]
       ) ; match: left digit
     ] ; match branch: ft:deep
    ) ; match: ft
  ) ; define hdL-view

(define (hdR-view ft)
  (match ft
    [(ft:single a) a]
    [(ft:deep _ _ _ a)
     (match a
       [(or (digit:1 x) (digit:2 _ x) (digit:3 _ _ x) (digit:4 _ _ _ x)) x]
       ) ; match: right digit
     ] ; match branch: ft:deep
    ) ; match: ft
  ) ; define hdR-view


(define (list->digit lst _depth)
  (match lst
    [`(,a ,b ,c ,d) (digit:4 a b c d)]
    [`(,a ,b ,c) (digit:3 a b c)]
    [`(,a ,b) (digit:2 a b)]
    [`(,a) (digit:1 a)]
    ) ; match: lst
  ) ; define list->digit

(define (build-digit-from-list lst)
  (match lst
    [`(,a ,b ,c ,d) (digit:4 a b c d)]
    [`(,a ,b ,c) (digit:3 a b c)]
    [`(,a ,b) (digit:2 a b)]
    [`(,a) (digit:1 a)]
    ) ; match: lst
  ) ; define build-digit-from-list

(define (build-node3 core x0 x1 x2 depth)
  (match-define (ft:config _ _ as) core)
  (define x0m (measure:node core x0 depth))
  (define x1m (measure:node core x1 depth))
  (define x2m (measure:node core x2 depth))
  (define c
    (as (as x0m x1m) x2m))
  (node:3 c x0 x1 x2)) ; define build-node3

(define (build-node2 core x0 x1 depth)
  (match-define (ft:config _ _ as) core)
  (define x0m (measure:node core x0 depth))
  (define x1m (measure:node core x1 depth))
  (define c (as x0m x1m))
  (node:2 c x0 x1)) ; define build-node2

;; ========================================
;; Zero-allocation digit iteration API
;; ========================================

;; digit-fold-left: fold over digit elements left-to-right
;; (digit-fold-left digit init (lambda (acc elem) ...)) -> acc
(define (digit-fold-left digit init f)
  (match digit
    [(digit:1 a) (f init a)]
    [(digit:2 a b) (f (f init a) b)]
    [(digit:3 a b c)
     (define acc1 (f init a))
     (define acc2 (f acc1 b))
     (f acc2 c)]
    [(digit:4 a b c d)
     (define acc1 (f init a))
     (define acc2 (f acc1 b))
     (define acc3 (f acc2 c))
     (f acc3 d)]
    ) ; match digit
  ) ; define digit-fold-left

;; digit-fold-right: fold over digit elements right-to-left
;; (digit-fold-right digit init (lambda (elem acc) ...)) -> acc
(define (digit-fold-right digit init f)
  (match digit
    [(digit:1 a) (f a init)]
    [(digit:2 a b)
     (define acc1 (f b init))
     (f a acc1)]
    [(digit:3 a b c)
     (define acc1 (f c init))
     (define acc2 (f b acc1))
     (f a acc2)]
    [(digit:4 a b c d)
     (define acc1 (f d init))
     (define acc2 (f c acc1))
     (define acc3 (f b acc2))
     (f a acc3)]
    ) ; match digit
  ) ; define digit-fold-right

;; digit-for-each: iterate over digit elements (for side effects)
(define (digit-for-each digit f)
  (match digit
    [(digit:1 a) (f a)]
    [(digit:2 a b) (f a) (f b)]
    [(digit:3 a b c) (f a) (f b) (f c)]
    [(digit:4 a b c d) (f a) (f b) (f c) (f d)]
    ) ; match digit
  ) ; define digit-for-each

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
          (values (- idx a-sz) b)
      )]
    [(digit:3 a b c)
      (define a-sz (measure-fn a))
      (if (< idx a-sz)
          (values idx a)
          (let ()
            (define idx1 (- idx a-sz))
            (define b-sz (measure-fn b))
            (if (< idx1 b-sz)
                (values idx1 b)
                (values (- idx1 b-sz) c))
            ) ; if idx1 in b
          ) ; let idx1/b-sz
      ] ; digit:3
    [(digit:4 a b c d)
      (define a-sz (measure-fn a))
      (if (< idx a-sz)
          (values idx a)
          (let ()
            (define idx1 (- idx a-sz))
            (define b-sz (measure-fn b))
            (if (< idx1 b-sz)
                (values idx1 b)
                (let ()
                  (define idx2 (- idx1 b-sz))
                  (define c-sz (measure-fn c))
                  (if (< idx2 c-sz)
                      (values idx2 c)
                      (values (- idx2 c-sz) d))
                  ) ; if idx2 in c
                ) ; let idx2/c-sz
            ) ; if idx1 in b
          ) ; let idx1/b-sz
      ] ; digit:4
    )) ; match digit

;; digit-update-by-measure: update element at accumulated measure position
;; Returns new digit with updated element
;; update-fn: (node remaining-idx) -> new-node
(define (digit-update-by-measure digit idx measure-fn update-fn)
  (match digit
    [(digit:1 a)
      (define a^ (update-fn a idx))
      (digit:1 a^)]
    [(digit:2 a b)
      (define a-sz (measure-fn a))
      (if (< idx a-sz)
          (digit:2 (update-fn a idx) b)
          (let ()
            (define idx1 (- idx a-sz))
            (digit:2 a (update-fn b idx1))
          )
      )]
    [(digit:3 a b c)
      (define a-sz (measure-fn a))
      (if (< idx a-sz)
          (digit:3 (update-fn a idx) b c)
          (let ()
            (define idx1 (- idx a-sz))
            (define b-sz (measure-fn b))
            (if (< idx1 b-sz)
                (digit:3 a (update-fn b idx1) c)
                (let ()
                  (define idx2 (- idx1 b-sz))
                  (digit:3 a b (update-fn c idx2))
                )
                ) ; if idx1 in b
            ) ; let idx1/b-sz
          ) ; if idx in a
      ] ; digit:3
    [(digit:4 a b c d)
      (define a-sz (measure-fn a))
      (if (< idx a-sz)
          (digit:4 (update-fn a idx) b c d)
          (let ()
            (define idx1 (- idx a-sz))
            (define b-sz (measure-fn b))
            (if (< idx1 b-sz)
                (digit:4 a (update-fn b idx1) c d)
                (let ()
                  (define idx2 (- idx1 b-sz))
                  (define c-sz (measure-fn c))
                  (if (< idx2 c-sz)
                      (digit:4 a b (update-fn c idx2) d)
                      (let ()
                        (define idx3 (- idx2 c-sz))
                        (digit:4 a b c (update-fn d idx3))
                      )
                      ) ; if idx2 in c
                  ) ; let idx2/c-sz
                ) ; if idx1 in b
            ) ; let idx1/b-sz
          ) ; if idx in a
      ] ; digit:4
    )) ; match digit

;; node-fold-left: fold over node children left-to-right
(define (node-fold-left node init f)
  (match node
    [(node:2 _ a b)
     (define acc1 (f init a))
     (f acc1 b)]
    [(node:3 _ a b c)
     (define acc1 (f init a))
     (define acc2 (f acc1 b))
     (f acc2 c)]
    ) ; match node
  ) ; define node-fold-left

;; node-fold-right: fold over node children right-to-left
(define (node-fold-right node init f)
  (match node
    [(node:2 _ a b)
     (define acc1 (f b init))
     (f a acc1)]
    [(node:3 _ a b c)
     (define acc1 (f c init))
     (define acc2 (f b acc1))
     (f a acc2)]
    ) ; match node
  ) ; define node-fold-right

;; node-find-by-measure: find child in node by accumulated measure
(define (node-find-by-measure node idx measure-fn)
  (match node
    [(node:2 _ a b)
      (define a-sz (measure-fn a))
      (if (< idx a-sz)
          (values idx a)
          (values (- idx a-sz) b)
      )]
    [(node:3 _ a b c)
      (define a-sz (measure-fn a))
      (if (< idx a-sz)
          (values idx a)
          (let ()
            (define idx1 (- idx a-sz))
            (define b-sz (measure-fn b))
            (if (< idx1 b-sz)
                (values idx1 b)
                (values (- idx1 b-sz) c))
            ) ; if idx1 in b
          ) ; let idx1/b-sz
      ] ; node:3
    )) ; match node

;; node-update-by-measure: update child in node by accumulated measure
(define (node-update-by-measure node idx measure-fn update-fn rebuild-fn)
  (match node
    [(node:2 _ a b)
      (define a-sz (measure-fn a))
      (if (< idx a-sz)
          (rebuild-fn (update-fn a idx) b)
          (let ()
            (define idx1 (- idx a-sz))
            (rebuild-fn a (update-fn b idx1))
          )
      )]
    [(node:3 _ a b c)
      (define a-sz (measure-fn a))
      (if (< idx a-sz)
          (rebuild-fn (update-fn a idx) b c)
          (let ()
            (define idx1 (- idx a-sz))
            (define b-sz (measure-fn b))
            (if (< idx1 b-sz)
                (rebuild-fn a (update-fn b idx1) c)
                (let ()
                  (define idx2 (- idx1 b-sz))
                  (rebuild-fn a b (update-fn c idx2))
                )
                ) ; if idx1 in b
            ) ; let idx1/b-sz
          ) ; if idx in a
      ] ; node:3
    )) ; match node

;; ========================================
;; Split Operation (Hinze & Paterson)
;; ========================================
;;
;; split:impl finds the first element where predicate p becomes true
;; on the accumulated measure. Returns (values left elem right).
;;
;; Predicate p must be monotonic: once true, stays true.
;; Complexity: O(log n)

;; Split result: (values left-tree element right-tree)
;; If predicate never becomes true, behavior is undefined.

(define (split:impl core p ft depth)
  (match ft
    [(ft:empty)
     (error 'split:impl "split of empty tree")]
    [(ft:single x)
     (values (ft:empty) x (ft:empty))
    ]
    [(ft:deep _ pr m sf)
     (match-define (ft:config e _ as) core)
     (define i (e))  ; identity
     (define inner-depth (add1 depth))
     (define vpr (as i
                     (measure:digit core pr depth)
               ))
     (define vm (as vpr
                    (measure:ft core m inner-depth)
              ))
     (cond
       [(p vpr)
        ;; Split point is in left digit
       (define-values (l x r) (split-digit core p i pr depth))
        (define right-tree (deep-L core r m sf depth))
        (values (maybe-digit->tree core l depth)
                x
                right-tree)]
       [(p vm)
        ;; Split point is in middle (inner tree)
        (define-values (ml xs mr) (split:impl core p m inner-depth))
        ;; xs is a node, split it further
        (define ml-measure (as vpr
                               (measure:ft core ml inner-depth)
                         ))
        (define-values (l x r) (split-node core p ml-measure xs depth))
        (define right-tree (deep-L core r mr sf depth))
        (values (deep-R core pr ml l depth)
                x
                right-tree)]
       [else
        ;; Split point is in right digit
        (define-values (l x r) (split-digit core p vm sf depth))
        (values (deep-R core pr m l depth)
                x
                (maybe-digit->tree core r depth))
        ] ; cond else
       ) ; cond
     ] ; ft:deep
    )) ; match ft

;; Split a digit, returns (values left-list elem right-list)
;; where left-list and right-list are lists of elements (possibly empty)
(define (split-digit core p i digit depth)
  (match-define (ft:config _ _ as) core)
  (define lst (digit->list digit))
  (let loop ([acc i]
             [before '()]
             [remaining lst])
    (match remaining
      [(cons x rest)
       (define acc+ (as acc
                        (measure:node core x depth)
                  ))
       (if (p acc+)
           (values (reverse before) x rest)
           (loop acc+ (cons x before) rest))
      ]
      ['()
       (error 'split-digit "predicate never became true")]
      ) ; match remaining
    )) ; let loop

;; Split a node (at depth, node contains elements at depth)
(define (split-node core p i node depth)
  (match-define (ft:config _ _ as) core)
  (define empty-list '())
  (match node
    [(node:2 _ a b)
     (define va (as i
                    (measure:node core a depth)
               ))
     (if (p va)
         (values '() a (list b))
         (values (list a) b empty-list)
     )
    ]
    [(node:3 _ a b c)
     (define va (as i
                    (measure:node core a depth)
               ))
     (cond
       [(p va)
        (values '() a (list b c))
       ]
       [else
        (define vb (as va
                       (measure:node core b depth)
                  ))
        (if (p vb)
            (values (list a) b (list c))
            (values (list a b) c empty-list)
        )
        ] ; cond else
       ) ; cond
     ] ; node:3
    )) ; match node

;; Convert possibly-empty list to tree
(define (maybe-digit->tree core lst depth)
  (match lst
    ['() (ft:empty)]
    [(list a) (ft:single a)]
    [(list a b)
     (match-define (ft:config _ _ as) core)
     (ft:deep (as (measure:node core a depth) (measure:node core b depth))
              (digit:1 a) (ft:empty) (digit:1 b))
    ]
    [(list a b c)
     (match-define (ft:config _ _ as) core)
     (define am (measure:node core a depth))
     (define bm (measure:node core b depth))
     (define cm (measure:node core c depth))
     (ft:deep (as am
                  (as bm cm))
              (digit:2 a b) (ft:empty) (digit:1 c))
    ]
    [(list a b c d)
     (match-define (ft:config _ _ as) core)
     (define am (measure:node core a depth))
     (define bm (measure:node core b depth))
     (define cm (measure:node core c depth))
     (define dm (measure:node core d depth))
     (ft:deep (as (as am bm)
                  (as cm dm))
              (digit:2 a b) (ft:empty) (digit:2 c d))
     ] ; list a b c d
    )) ; match lst

;; deep-L: construct tree with possibly empty left part
(define (deep-L core l m sf depth)
  (match l
    ['()
     (match m
       [(ft:empty) (maybe-digit->tree core (digit->list sf) depth)]
       [_
        (define inner-depth (add1 depth))
        (define-values (node m-rest) (hdL:impl core m inner-depth))
        (match-define (ft:config _ _ as) core)
        (define new-left (node->digit node))
        (define left-m (measure:digit core new-left depth))
        (define mid-m (measure:ft core m-rest inner-depth))
        (define right-m (measure:digit core sf depth))
        (define tail (as mid-m right-m))
        (define total (as left-m tail))
        (ft:deep total new-left m-rest sf)
        ] ; match m: non-empty
       ) ; match m
    ]
    [_
     (define new-left (build-digit-from-list l))
     (define inner-depth (add1 depth))
     (match-define (ft:config _ _ as) core)
     (define left-m (measure:digit core new-left depth))
     (define mid-m (measure:ft core m inner-depth))
     (define right-m (measure:digit core sf depth))
     (define tail (as mid-m right-m))
     (define total (as left-m tail))
     (ft:deep total new-left m sf)
    ]
    ) ; match l
  ) ; define deep-L

;; deep-R: construct tree with possibly empty right part
(define (deep-R core pr m r depth)
  (match r
    ['()
     (match m
       [(ft:empty) (maybe-digit->tree core (digit->list pr) depth)]
       [_
        (define inner-depth (add1 depth))
        (define-values (node m-rest) (hdR:impl core m inner-depth))
        (match-define (ft:config _ _ as) core)
        (define new-right (node->digit node))
        (define left-m (measure:digit core pr depth))
        (define mid-m (measure:ft core m-rest inner-depth))
        (define right-m (measure:digit core new-right depth))
        (define tail (as mid-m right-m))
        (define total (as left-m tail))
        (ft:deep total pr m-rest new-right)
        ] ; match m: non-empty
       ) ; match m
    ]
    [_
     (define new-right (build-digit-from-list r))
     (define inner-depth (add1 depth))
     (match-define (ft:config _ _ as) core)
     (define left-m (measure:digit core pr depth))
     (define mid-m (measure:ft core m inner-depth))
     (define right-m (measure:digit core new-right depth))
     (define tail (as mid-m right-m))
     (define total (as left-m tail))
     (ft:deep total pr m new-right)
    ]
    ) ; match r
  ) ; define deep-R

;; node->digit helper
(define (node->digit node)
  (match node
    [(node:2 _ a b) (digit:2 a b)]
    [(node:3 _ a b c) (digit:3 a b c)]
    ) ; match node
  ) ; define node->digit

(provide measure:node measure:ft measure:digit)
(provide consL:impl consR:impl hdL:impl hdR:impl concat:impl split:impl)
(provide deep-L deep-R maybe-digit->tree)
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
