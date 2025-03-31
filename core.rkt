#lang racket/base

(require racket/match racket/contract)

; Digit
(struct One (a) #:transparent)
(struct Two (a b) #:transparent)
(struct Three (a b c) #:transparent)
(struct Four (a b c d) #:transparent)
(define Digit?/c (or/c One? Two? Three? Four?))

; Node
(struct Node2 (v a b) #:transparent)
(struct Node3 (v a b c) #:transparent)
(define Node?/c (or/c Node2? Node3?))

; Finger Tree
(struct Empty () #:transparent)
(struct Single (a) #:transparent)
(struct Deep (v left inner right) #:transparent)
(define finger-tree? (or/c Empty? Single? Deep?))
(provide finger-tree?)

(struct FingerTree (empty-value measure assoc))
(struct FingerTreeWrap (core ft))

(provide FingerTree Empty Single Deep Node2 Node3 One Two Three Four Digit?/c Node?/c)
(provide measure:node measure:ft measure:digit consL:impl consR:impl hdL:impl hdR:impl )
(provide concat:impl)
(provide digit-add-list)

(define (measure:node f n depth)
  (match depth
    [0 (match-define (FingerTree _ m _) f) (m n)]
    [_ (match n
        [(Node2 v _ _) v]
        [(Node3 v _ _ _) v]
      )]
  )
)

(define (measure:ft f ft depth)
  (match ft
    [(Deep v _ _ _) v]
    [(Single a) (measure:node f a depth)]
    [(Empty) (match-define (FingerTree e _ _) f) (e)]
  )
)

(define (measure:digit f d depth)
  (match-define (FingerTree _ _ as) f)
  (match d
    [(One a)
      (measure:node f a depth)]
    [(Two a b)
      (as (measure:node f a depth) (measure:node f b depth))]
    [(Three a b c)
      (as (as (measure:node f a depth) (measure:node f b depth)) (measure:node f c depth))]
    [(Four a b c d)
      (as (as (measure:node f a depth) (measure:node f b depth)) 
        (as (measure:node f c depth) (measure:node f d depth)))]
  )
)

(define (consL:impl core ft v [depth 0])
  (match ft
    [(Empty) (Single v)]
    [(Single a)
      (match-define (FingerTree _ m as) core)
      (define v^ (as (measure:node core v depth) (measure:node core a depth)))
      (Deep v^ (One v) (Empty) (One a))
    ]
    [(Deep v^ left inner right)
      (match-define (FingerTree _ m as) core)
      (define v^^ (as (measure:node core v depth) v^))
      (match left
        [(Four a b c d)
          (define left^ (Two v a))
          (define n (Node3 (as 
            (as (measure:node core b depth) (measure:node core c depth))
            (measure:node core d depth))
            b c d))
          (define inner^ (consL:impl core inner n (+ depth 1)))
          (Deep v^^ left^ inner^ right)
        ]
        [_ 
          (define left^ (match left
            [(One a) (Two v a)]
            [(Two a b) (Three v a b)]
            [(Three a b c) (Four v a b c)]
          ))
          (Deep v^^ left^ inner right)
        ]
      )
    ]
  )
)

(define (consL ft v)
  (match-define (FingerTreeWrap core ft^) ft)
  (FingerTreeWrap core (consL:impl core ft^ v))
)

(define (consR:impl core ft v [depth 0])
  (match ft
    [(Empty) (Single v)]
    [(Single a)
      (match-define (FingerTree _ _ as) core)
      (define v^ (as (measure:node core v depth) (measure:node core a depth)))
      (Deep v^ (One a) (Empty) (One v))
    ]
    [(Deep v^ left inner right)
      (match-define (FingerTree _ _ as) core)
      (define v^^ (as v^ (measure:node core v depth)))
      (match right
        [(Four a b c d)
          (define right^ (Two d v))
          (define n (Node3 (as 
            (as (measure:node core a depth) (measure:node core b depth))
            (measure:node core c depth))
            a b c))
          (define inner^ (consR:impl core inner n (+ depth 1)))
          (Deep v^^ left inner^ right^)
        ]
        [_ 
          (define right^ (match right
            [(One a) (Two a v)]
            [(Two a b) (Three a b v)]
            [(Three a b c) (Four a b c v)]
          ))
          (Deep v^^ left inner right^)
        ]
      )
    ]
  )
)

(define (consR ft v)
  (match-define (FingerTreeWrap core ft^) ft)
  (FingerTreeWrap core (consR:impl core ft^ v))
)

(define (hdL ft)
  (match-define (FingerTreeWrap core f) ft)
  (define-values (h f^) (hdL:impl core f))
  (values h (FingerTreeWrap core f^))
)

(define (hdL:impl core ft [depth 0])
  (match ft
    [(Empty)
      (values #f ft)
    ]
    [(Single a)
      (values a (Empty))
    ]
    [(Deep _ (One a) (Empty) (One b))
      (values a (Single b))
    ]
    [(Deep _ (One a) (Empty) right)
      (match-define (FingerTree _ _ as) core)
      (match right
        [(Two b c)
          (values a (Deep (as (measure:node core b depth) (measure:node core c depth))
            (One b) (Empty) (One c)))
        ]
        [(Three b c d)
          (values a (Deep 
            (as (as (measure:node core b depth) (measure:node core c depth)) (measure:node core d depth))
            (One b) (Empty) (Two c d)))
        ]
        [(Four b c d e)
          (values a (Deep 
            (as 
              (as (measure:node core b depth) (measure:node core c depth))
              (as (measure:node core d depth) (measure:node core e depth)))
            (Two b c) (Empty) (Two d e)))
        ]
      )
    ]
    [(Deep _ (One a) inner right)
      (define-values (lhs inner^) (hdL:impl core inner (+ depth 1)))
      (match-define (FingerTree _ _ as) core)
      (define-values (left-v left-digit) (match lhs
        [(Node2 v b c) (values v (Two b c))]
        [(Node3 v b c d) (values v (Three b c d))]
        ))
      (values a (Deep (as left-v (as (measure:ft core inner (add1 depth)) (measure:digit core right depth)))
        left-digit
        inner^
        right
      ))
    ]
    [(Deep _ left inner right)
      (define-values (h lhs^) (match left
        [(Two a b) (values a (One b))]
        [(Three a b c) (values a (Two b c))]
        [(Four a b c d) (values a (Three b c d))]
      ))
      (match-define (FingerTree _ _ as) core)
      (values h (Deep 
        (as (measure:digit core lhs^ depth) (as (measure:ft core inner (+ depth 1))
          (measure:digit core right depth)))
        lhs^
        inner
        right
      ))
    ]
  )
)

(define (debug:getMaxDepth ft)
  (match-define (FingerTreeWrap core ft^) ft)
  (debug:getMaxDepth:impl core ft^)
)

(define (debug:getMaxDepth:impl core ft [depth 0])
  (match ft
    [(Deep _ _ inner _)
      (debug:getMaxDepth:impl core inner (+ depth 1))
    ]
    [(or (Empty) (Single _)) depth]
  )
)

(define (make-empty-finger-tree empty-value measure assoc)
  (FingerTreeWrap (FingerTree empty-value measure assoc) (Empty))
)

(define size-core (FingerTree (lambda () 0) (lambda (_) 1) +))
(define only-left (FingerTree (lambda () #f) (lambda (x) x) (lambda (l r) (if l l r))))

(define (finger-tree:measure-value ft)
  (match-define (FingerTreeWrap core f) ft)
  (measure:ft core f 0)
)

(define (hdR:impl core ft [depth 0])
  (match ft
    [(Empty)
      (values #f ft)
    ]
    [(Single a)
      (values a (Empty))
    ]
    [(Deep _ (One a) (Empty) (One b))
      (values b (Single a))
    ]
    [(Deep _ left (Empty) (One a))
      (match-define (FingerTree _ _ as) core)
      (match left
        [(Two b c)
          (values a (Deep (as (measure:node core b depth) (measure:node core c depth))
            (One b) (Empty) (One c)))
        ]
        [(Three b c d)
          (values a (Deep 
            (as (as (measure:node core b depth) (measure:node core c depth)) (measure:node core d depth))
            (One b) (Empty) (Two c d)))
        ]
        [(Four b c d e)
          (values a (Deep 
            (as 
              (as (measure:node core b depth) (measure:node core c depth))
              (as (measure:node core d depth) (measure:node core e depth)))
            (Two b c) (Empty) (Two d e)))
        ]
      )
    ]
    [(Deep _ left inner (One a))
      (define-values (rhs inner^) (hdR:impl core inner (add1 depth)))
      (match-define (FingerTree _ _ as) core)
      (define-values (right-v right-digit) (match rhs
        [(Node2 v b c) (values v (Two b c))]
        [(Node3 v b c d) (values v (Three b c d))]
        ))
      (values a (Deep (as (measure:digit core left depth) (as (measure:ft core inner (add1 depth)) right-v))
        left
        inner^
        right-digit
      ))
    ]
    [(Deep _ lhs inner right)
      (define-values (h rhs^) (match right
        [(Two a b) (values b (One a))]
        [(Three a b c) (values c (Two a b))]
        [(Four a b c d) (values d (Three a b c))]
      ))
      (match-define (FingerTree _ _ as) core)
      (values h (Deep 
        (as (as (measure:digit core lhs depth) (measure:ft core inner (+ depth 1)))
          (measure:digit core rhs^ depth))
        lhs
        inner
        rhs^
      ))
    ]
  )
)

(define (hdR ft)
  (match-define (FingerTreeWrap core f) ft)
  (define-values (h f^) (hdR:impl core f))
  (values h (FingerTreeWrap core f^))
)

(define (digit-add-list digit rest)
  (match digit
    [(One a) (cons a rest)]
    [(Two a b) (append (list a b) rest)]
    [(Three a b c) (append (list a b c) rest)]
    [(Four a b c d) (append (list a b c d) rest)]
  )
)

; 2 .. 8
(define (list->nodes:impl core rest depth)
  (match-define (FingerTree _ _ as) core)
  (printf "rest: ~a\n" rest)
  (match rest
    [`(,a ,b ,c ,d) (list 
      (Node2 (as (measure:node core a depth) (measure:node core b depth)) a b) 
      (Node2 (as (measure:node core c depth) (measure:node core d depth)) c d))]
    [`(,a ,b ,c) (list (Node3 
      (as (measure:node core a depth) (as (measure:node core b depth) (measure:node core c depth)))
      a b c))]
    [`(,a ,b) (list (Node2 
      (as (measure:node core a depth) (measure:node core b depth))
      a b))]
    [`(,a ,b ,c ,r ...) 
      (cons 
        (Node3 (as (measure:node core a depth) (as (measure:node core b depth) (measure:node core c depth))) a b c) 
        (list->nodes:impl core r depth))]
  )
)

(define (concat:impl core lhs rhs [depth 0])
  (match* (lhs rhs)
    [(_ (Empty)) lhs]
    [((Empty) _) rhs]
    [((Single a) _) (consL:impl core rhs a depth)]
    [(_ (Single a)) (consR:impl core lhs a depth)]
    [((Deep lhs-v lhs-left lhs-inner lhs-right) (Deep rhs-v rhs-left rhs-inner rhs-right))
      (define mid (digit-add-list lhs-right (digit-add-list rhs-left '())))
      (define mid^ (list->nodes:impl core mid depth))
      (define left-inner^ (for/fold ([i lhs-inner]) ([m mid^])
        (consR:impl core i m depth)
      ))
      (define inner^ (concat:impl core left-inner^ rhs-inner (add1 depth)))
      (match-define (FingerTree _ _ as) core)
      (define v^ (as lhs-v rhs-v))
      (printf "lhs: ~a, rhs: ~a, total: ~a\n" lhs-v rhs-v v^)
      (Deep v^ lhs-left inner^ rhs-right)
    ]
  )
)

(define (concat lhs rhs)
  (unless (eq? (FingerTreeWrap-core lhs) (FingerTreeWrap-core rhs)) (error 'concat "Mismatch concat of different finger tree"))
  (match-define (FingerTreeWrap core f) lhs)
  (match-define (FingerTreeWrap _ f2) rhs)
  (FingerTreeWrap core (concat:impl core f f2))
)

(define (build-ft0 core lhs inner rhs depth)
  (match-define (FingerTree _ m as) core)
  (define lhs-measure (measure:digit core lhs depth))
  (define mid (measure:ft core inner (add1 depth)))
  (define rhs-measure (measure:digit core rhs depth))
  (define v (as lhs-measure (as mid rhs-measure)))
  (Deep v lhs inner rhs)
)

(define (hdL-view ft)
  (match ft
    [(Single a) a]
    [(Deep _ a _ _) (match a
      [(or (One x) (Two x _) (Three x _ _) (Four x _ _ _)) x]
    )]
  )
)

(define (hdR-view ft)
  (match ft
    [(Single a) a]
    [(Deep _ _ _ a) (match a
      [(or (One x) (Two _ x) (Three _ _ x) (Four _ _ _ x)) x]
    )]
  )
)

(provide build-ft0 hdL-view hdR-view)
