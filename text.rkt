#lang racket/base

;; text: High-level text buffer with word/line/paragraph navigation
;; Based on finger-tree with composite measure

(require racket/match racket/generator)
(require "private/core.rkt" "private/core-algorithm.rkt")
(require "text/measure.rkt" "text/elem.rkt")
(require "text/incremental.rkt")

;; ========================================
;; Finger Tree Configuration
;; ========================================

(define text-core
  (ft:config
   text-measure-empty
   text-elem->measure
   text-measure-append
   ) ; ft:config text-core
  ) ; define text-core

;; ========================================
;; Text Buffer Wrapper
;; ========================================

;; text-buffer wraps a finger-tree of text-elem
(struct text-buffer (ft) #:transparent)

;; ========================================
;; Construction
;; ========================================

(define text-empty-impl (ft:empty))

(define (text-empty)
  (text-buffer text-empty-impl)
  ) ; define text-empty

(define (text-empty? tb)
  (match (text-buffer-ft tb)
    [(ft:empty) #t]
    [_ #f]
    ) ; match: text-buffer-ft
  ) ; define text-empty?

;; Convert string to text-buffer
;; Computes boundary flags during construction
(define (string->text str)
  (define chars (string->list str))
  (define ft
    (let loop ([chars chars]
               [ft (ft:empty)]
               [prev-char #f]
               [after-blank-line? #t]  ; Start of text counts as after blank line
               [line-has-content? #f]) ; Track if current line has non-whitespace
      (match chars
        ['() ft]
        [(cons c rest)
          (define ws? (ascii-whitespace? c))
          (define is-newline? (char=? c #\newline))

          ;; Determine if this starts a paragraph
          (define ps? (and (not ws?) after-blank-line?))

          ;; Determine if this starts a word
          (define word-start? (and (not ws?)
                                   (or (not prev-char)
                                       (ascii-whitespace? prev-char))
                                   ) ; or: prev whitespace or BOF
            ) ; define word-start?

          ;; Create element
          (define elem (text-elem c word-start? is-newline? ps?))

          ;; Update state for next iteration
          (define new-line-has-content?
            (if is-newline?
                #f  ; Reset on newline
                (or line-has-content? (not ws?))
                ) ; if: newline resets line-content
            ) ; define new-line-has-content?

          ;; After blank line if:
          ;; - This is a newline AND current line has no content
          ;; - Or we were already after blank line and this is whitespace (but not newline starting content)
          (define new-after-blank-line?
            (cond
              [is-newline? (not line-has-content?)]  ; Blank line if no content before this newline
              [else (and after-blank-line? ws?)]      ; Stay in blank region if whitespace
              ) ; cond: new-after-blank-line?
            ) ; define new-after-blank-line?

          (loop rest
                (consR:impl text-core ft elem)
	                c
	                new-after-blank-line?
	                new-line-has-content?
                  ) ; loop args
          ] ; match branch: cons
        ) ; match: chars
      ) ; let loop
    ) ; define ft
  (text-buffer ft)
  ) ; define string->text

;; Convert text-buffer to string
(define (text->string tb)
  (define ft (text-buffer-ft tb))
  (list->string
    (for/list ([elem (in-text-elems ft)])
      (text-elem-char elem)
      ) ; for/list: elem->char
    ) ; list->string
  ) ; define text->string

;; Internal: iterate over text elements
(define (in-text-elems ft)
  (in-generator
    (define (yield-node node depth)
      (match depth
        [0 (yield node)]
        [_
         (define sub-depth (sub1 depth))
         (match node
           [(node:2 _ x0 x1)
            (yield-node x0 sub-depth)
            (yield-node x1 sub-depth)
            ] ; match branch: node:2
           [(node:3 _ x0 x1 x2)
            (yield-node x0 sub-depth)
            (yield-node x1 sub-depth)
            (yield-node x2 sub-depth)
            ] ; match branch: node:3
           ) ; match: node
         ] ; match branch: depth>0
        ) ; match: depth
      ) ; define yield-node
    (define (yield-digit digit depth)
      (match digit
        [(digit:1 x0) (yield-node x0 depth)]
        [(digit:2 x0 x1)
         (yield-node x0 depth)
         (yield-node x1 depth)
         ] ; match branch: digit:2
        [(digit:3 x0 x1 x2)
         (yield-node x0 depth)
         (yield-node x1 depth)
         (yield-node x2 depth)
         ] ; match branch: digit:3
        [(digit:4 x0 x1 x2 x3)
         (yield-node x0 depth)
         (yield-node x1 depth)
         (yield-node x2 depth)
         (yield-node x3 depth)
         ] ; match branch: digit:4
        ) ; match: digit
      ) ; define yield-digit
    (define (yield-ft ft depth)
      (match ft
        [(ft:empty) (void)]
        [(ft:single node) (yield-node node depth)]
        [(ft:deep _ left inner right)
          (yield-digit left depth)
          (yield-ft inner (add1 depth))
          (yield-digit right depth)
          ] ; match branch: ft:deep
        ) ; match: ft
      ) ; define yield-ft
    (yield-ft ft 0)
    ) ; in-generator
  ) ; define in-text-elems

;; ========================================
;; Measures (O(1))
;; ========================================

(define (text-length tb)
  (text-measure-chars (text-buffer-measure tb))
  ) ; define text-length

(define (text-word-count tb)
  (text-measure-words (text-buffer-measure tb))
  ) ; define text-word-count

(define (text-line-count tb)
  (text-measure-lines (text-buffer-measure tb))
  ) ; define text-line-count

(define (text-para-count tb)
  (text-measure-paras (text-buffer-measure tb))
  ) ; define text-para-count

;; Get the measure from the root
(define (text-buffer-measure tb)
  (measure:ft text-core (text-buffer-ft tb) 0))

;; ========================================
;; Character-level Navigation (O(log n))
;; ========================================

(define (make-char-measure-fn depth)
  (lambda (node)
    (text-measure-chars (measure:node text-core node depth))
    ) ; lambda: node->char count
  ) ; define make-char-measure-fn

(define (text-ref-node:impl node idx depth)
  (match depth
    [0 (text-elem-char node)]
    [_
      (define sub-depth (sub1 depth))
      (define measure-fn (make-char-measure-fn sub-depth))
      (define-values (idx^ child) (node-find-by-measure node idx measure-fn))
      (text-ref-node:impl child idx^ sub-depth)
      ] ; match branch: depth>0
    ) ; match: depth
  ) ; define text-ref-node:impl

(define (text-ref-digit:impl digit idx depth)
  (define measure-fn (make-char-measure-fn depth))
  (define-values (idx^ node) (digit-find-by-measure digit idx measure-fn))
  (text-ref-node:impl node idx^ depth))

(define (text-ref-ft:impl ft idx depth)
  (match ft
    [(ft:single r) (text-ref-node:impl r idx depth)]
    [(ft:deep _ lhs inner rhs)
      (define lhs-measure
        (text-measure-chars (measure:digit text-core lhs depth))
        ) ; define lhs-measure
      (define inner-depth (add1 depth))
      (define inner-size
        (text-measure-chars (measure:ft text-core inner inner-depth))
        ) ; define inner-size
      (define inner-measure (+ lhs-measure inner-size))
      (cond
        [(< idx lhs-measure) (text-ref-digit:impl lhs idx depth)]
        [(< idx inner-measure)
         (text-ref-ft:impl inner (- idx lhs-measure) inner-depth)
         ] ; cond branch: in inner
        [else
         (text-ref-digit:impl rhs (- idx inner-measure) depth)
         ] ; cond branch: in rhs
        ) ; cond: text-ref-ft
      ] ; match branch: ft:deep
    ) ; match: ft
  ) ; define text-ref-ft:impl

(define (text-ref tb pos)
  (define len (text-length tb))
  (cond
    [(< pos 0) (error 'text-ref "index out of bounds: ~a" pos)]
    [(>= pos len) (error 'text-ref "index out of bounds: ~a" pos)]
    [else (text-ref-ft:impl (text-buffer-ft tb) pos 0)]
    ) ; cond: text-ref bounds
  ) ; define text-ref

;; Get the full element at position
(define (text-elem-at-node:impl node idx depth)
  (match depth
    [0 node]
    [_
      (define sub-depth (sub1 depth))
      (define measure-fn (make-char-measure-fn sub-depth))
      (define-values (idx^ child) (node-find-by-measure node idx measure-fn))
      (text-elem-at-node:impl child idx^ sub-depth)
      ] ; match branch: depth>0
    ) ; match: depth
  ) ; define text-elem-at-node:impl

(define (text-elem-at-digit:impl digit idx depth)
  (define measure-fn (make-char-measure-fn depth))
  (define-values (idx^ node) (digit-find-by-measure digit idx measure-fn))
  (text-elem-at-node:impl node idx^ depth))

(define (text-elem-at-ft:impl ft idx depth)
  (match ft
    [(ft:single r) (text-elem-at-node:impl r idx depth)]
    [(ft:deep _ lhs inner rhs)
      (define lhs-measure
        (text-measure-chars (measure:digit text-core lhs depth))
        ) ; define lhs-measure
      (define inner-depth (add1 depth))
      (define inner-size
        (text-measure-chars (measure:ft text-core inner inner-depth))
        ) ; define inner-size
      (define inner-measure (+ lhs-measure inner-size))
      (cond
        [(< idx lhs-measure) (text-elem-at-digit:impl lhs idx depth)]
        [(< idx inner-measure)
         (text-elem-at-ft:impl inner (- idx lhs-measure) inner-depth)
         ] ; cond branch: in inner
        [else
         (text-elem-at-digit:impl rhs (- idx inner-measure) depth)
         ] ; cond branch: in rhs
        ) ; cond: text-elem-at-ft
      ] ; match branch: ft:deep
    ) ; match: ft
  ) ; define text-elem-at-ft:impl

(define (text-elem-at tb pos)
  (define len (text-length tb))
  (cond
    [(< pos 0) (error 'text-elem-at "index out of bounds: ~a" pos)]
    [(>= pos len) (error 'text-elem-at "index out of bounds: ~a" pos)]
    [else (text-elem-at-ft:impl (text-buffer-ft tb) pos 0)]
    ) ; cond: text-elem-at bounds
  ) ; define text-elem-at

;; ========================================
;; Split Operations (O(log n))
;; ========================================

;; Helper for node->digit conversion
(define (node->list node)
  (match node
    [(node:2 _ a b) (list a b)]
    [(node:3 _ a b c) (list a b c)]
    ) ; match: node
  ) ; define node->list

;; Split digit by character index
(define (text-split-digit:impl digit idx depth)
  (define measure-fn (make-char-measure-fn depth))
  (define empty-list '())
  (match digit
    [(digit:1 a)
      (define a-sz (measure-fn a))
      (cond
        [(< idx a-sz) (values idx empty-list a empty-list)]
        [else (error 'text-split-digit "index out of bounds")]
        ) ; cond: digit:1
      ] ; match branch: digit:1
    [(digit:2 a b)
      (define a-sz (measure-fn a))
      (cond
        [(< idx a-sz)
         (values idx '() a (list b))
         ] ; cond branch: digit:2 left
        [else
         (values (- idx a-sz) (list a) b '())
         ] ; cond branch: digit:2 right
        ) ; cond: digit:2
      ] ; match branch: digit:2
    [(digit:3 a b c)
      (define a-sz (measure-fn a))
      (define b-sz (measure-fn b))
      (define c-sz (measure-fn c))
      (define ab-sz (+ a-sz b-sz))
      (define abc-sz (+ ab-sz c-sz))
      (cond
        [(< idx a-sz)
         (values idx '() a (list b c))
         ] ; cond branch: digit:3 left
        [(< idx ab-sz)
         (values (- idx a-sz) (list a) b (list c))
         ] ; cond branch: digit:3 middle
        [(< idx abc-sz)
         (values (- idx ab-sz) (list a b) c '())
         ] ; cond branch: digit:3 right
        [else (error 'text-split-digit "index out of bounds")]
        ) ; cond: digit:3
      ] ; match branch: digit:3
    [(digit:4 a b c d)
      (define a-sz (measure-fn a))
      (define b-sz (measure-fn b))
      (define c-sz (measure-fn c))
      (define d-sz (measure-fn d))
      (define ab-sz (+ a-sz b-sz))
      (define abc-sz (+ ab-sz c-sz))
      (define abcd-sz (+ abc-sz d-sz))
      (cond
        [(< idx a-sz)
         (values idx '() a (list b c d))
         ] ; cond branch: digit:4 first
        [(< idx ab-sz)
         (values (- idx a-sz) (list a) b (list c d))
         ] ; cond branch: digit:4 second
        [(< idx abc-sz)
         (values (- idx ab-sz) (list a b) c (list d))
         ] ; cond branch: digit:4 third
        [(< idx abcd-sz)
         (values (- idx abc-sz) (list a b c) d '())
         ] ; cond branch: digit:4 fourth
        [else (error 'text-split-digit "index out of bounds")]
        ) ; cond: digit:4
      ] ; match branch: digit:4
    ) ; match: digit
  ) ; define text-split-digit:impl

;; Split node by character index
(define (text-split-node:impl node idx depth)
  (define sub-depth (sub1 depth))
  (define measure-fn (make-char-measure-fn sub-depth))
  (match node
    [(node:2 _ a b)
      (define a-sz (measure-fn a))
      (cond
        [(< idx a-sz)
         (values idx '() a (list b))
         ] ; cond branch: node:2 left
        [else
         (values (- idx a-sz) (list a) b '())
         ] ; cond branch: node:2 right
        ) ; cond: node:2
      ] ; match branch: node:2
    [(node:3 _ a b c)
      (define a-sz (measure-fn a))
      (define b-sz (measure-fn b))
      (define c-sz (measure-fn c))
      (define ab-sz (+ a-sz b-sz))
      (define abc-sz (+ ab-sz c-sz))
      (cond
        [(< idx a-sz)
         (values idx '() a (list b c))
         ] ; cond branch: node:3 left
        [(< idx ab-sz)
         (values (- idx a-sz) (list a) b (list c))
         ] ; cond branch: node:3 middle
        [(< idx abc-sz)
         (values (- idx ab-sz) (list a b) c '())
         ] ; cond branch: node:3 right
        [else (error 'text-split-node "index out of bounds")]
        ) ; cond: node:3
      ] ; match branch: node:3
    ) ; match: node
  ) ; define text-split-node:impl

;; Build ft from node list
(define (digit-list->ft lst depth)
  (match lst
    ['() (ft:empty)]
    [(list a) (ft:single a)]
    [(list a b)
      (define am (measure:node text-core a depth))
      (define bm (measure:node text-core b depth))
      (define m (text-measure-append am bm))
      (define empty-inner (ft:empty))
      (define rhs (digit:1 b))
      (define ft^
        (ft:deep m
                 (digit:1 a)
                 empty-inner
                 rhs))
      ft^]
    [(list a b c)
      (define am (measure:node text-core a depth))
      (define bm (measure:node text-core b depth))
      (define cm (measure:node text-core c depth))
      (define abm (text-measure-append am bm))
      (define m (text-measure-append abm cm))
      (define empty-inner (ft:empty))
      (define rhs (digit:2 b c))
      (define ft^
        (ft:deep m
                 (digit:1 a)
                 empty-inner
                 rhs))
      ft^]
    [(list a b c d)
      (define am (measure:node text-core a depth))
      (define bm (measure:node text-core b depth))
      (define cm (measure:node text-core c depth))
      (define dm (measure:node text-core d depth))
      (define abm (text-measure-append am bm))
      (define cdm (text-measure-append cm dm))
      (define m (text-measure-append abm cdm))
      (define empty-inner (ft:empty))
      (define rhs (digit:2 c d))
      (define ft^
        (ft:deep m
                 (digit:2 a b)
                 empty-inner
                 rhs))
      ft^]
    ) ; match: lst
  ) ; define digit-list->ft

(define (digit-list2->ft lst depth)
  (if (<= (length lst) 4)
      (digit-list->ft lst depth)
      (let ()
        (define init (text-measure-empty))
        (define v
          (for/fold ([m init]) ([j lst])
            (text-measure-append m (measure:node text-core j depth))
            ) ; for/fold: measure list
          ) ; define v
        (match lst
          [(list a b c d e)
           (define empty-inner (ft:empty))
           (define rhs (digit:3 c d e))
           (define ft^
             (ft:deep v
                      (digit:2 a b)
                      empty-inner
                      rhs))
           ft^]
          [(list a b c d e f)
           (define empty-inner (ft:empty))
           (define rhs (digit:3 d e f))
           (define ft^
             (ft:deep v
                      (digit:3 a b c)
                      empty-inner
                      rhs))
           ft^]
          [(list a b c d e f g)
           (define empty-inner (ft:empty))
           (define rhs (digit:4 d e f g))
           (define ft^
             (ft:deep v
                      (digit:3 a b c)
                      empty-inner
                      rhs))
           ft^]
          ) ; match: lst
        ) ; let: v
      ) ; if: digit-list2->ft
  ) ; define digit-list2->ft

(define (digit-list+ft->digit lst ft depth pop)
  (match lst
    ['()
      (define inner-depth (add1 depth))
      (define-values (h ft^) (pop text-core ft inner-depth))
      (values (digit:1 h) ft^)]
    [(list a) (values (digit:1 a) ft)]
    [(list a b) (values (digit:2 a b) ft)]
    [(list a b c) (values (digit:3 a b c) ft)]
    [(list a b c d) (values (digit:4 a b c d) ft)]
    ) ; match: lst
  ) ; define digit-list+ft->digit

(define (node->digit node depth)
  (list->digit (node->list node) (sub1 depth))
  ) ; define node->digit

(define (left-digit+ft->ft digit ft depth)
  (match ft
    [(ft:empty)
     (define empty-list '())
     (define digit^ (digit-add-list digit empty-list))
     (digit-list->ft digit^ depth)]
    [_
     (define inner-depth (add1 depth))
     (define-values (r ft^) (hdR:impl text-core ft inner-depth))
     (build-ft0 text-core digit ft^ (node->digit r inner-depth) depth)]
    ) ; match: ft
  ) ; define left-digit+ft->ft

(define (right-digit+ft->ft digit ft depth)
  (match ft
    [(ft:empty)
     (define empty-list '())
     (define digit^ (digit-add-list digit empty-list))
     (digit-list->ft digit^ depth)]
    [_
     (define inner-depth (add1 depth))
     (define-values (l ft^) (hdL:impl text-core ft inner-depth))
     (build-ft0 text-core (node->digit l inner-depth) ft^ digit depth)]
    ) ; match: ft
  ) ; define right-digit+ft->ft

;; Main split implementation
(define (text-split-ft:impl ft idx depth)
  (match ft
    [(ft:empty) (error 'text-split "index out of bounds")]
    [(ft:single v)
     (define vm (measure:node text-core v depth))
     (define m (text-measure-chars vm))
     (cond
       [(>= idx m) (error 'text-split "index out of bounds")]
       [else
        (define empty-ft (ft:empty))
        (values idx empty-ft v empty-ft)]
       ) ; cond: ft:single
     ]
    [(ft:deep _ lhs inner rhs)
     (define lhs-m (measure:digit text-core lhs depth))
     (define lhs-measure (text-measure-chars lhs-m))
     (define inner-depth (add1 depth))
     (define inner-m (measure:ft text-core inner inner-depth))
     (define inner-chars (text-measure-chars inner-m))
     (define inner-measure (+ lhs-measure inner-chars))
     (cond
       [(< idx lhs-measure)
        (define-values (idx^ l m r) (text-split-digit:impl lhs idx depth))
        (define left (digit-list->ft l depth))
         (match inner
           [(ft:empty)
           (define empty-list '())
           (define rhs-list (digit-add-list rhs empty-list))
           (define r+rhs (append r rhs-list))
           (define right^ (digit-list2->ft r+rhs depth))
           (values idx^ left m right^)]
          [_
           (define-values (right inner^) (digit-list+ft->digit r inner depth hdL:impl))
           (define right^ (build-ft0 text-core right inner^ rhs depth))
           (values idx^ left m right^)]
          ) ; match: inner after lhs split
        ]
       [(< idx inner-measure)
        (define-values (rest-idx l m r)
          (text-split-ft:impl inner (- idx lhs-measure) inner-depth))
        (define left (left-digit+ft->ft lhs l depth))
        (define right (right-digit+ft->ft rhs r depth))
        (define-values (idx^ l^ m^ r^) (text-split-node:impl m rest-idx inner-depth))
        ;; l^ and r^ are elements at depth (from the node at depth+1)
        (define left^
          (for/fold ([init left]) ([i l^])
            (consR:impl text-core init i depth)
            ) ; for/fold: append left list
          ) ; define left^
        (define right^
          (for/foldr ([init right]) ([i r^])
            (consL:impl text-core init i depth)
            ) ; for/foldr: prepend right list
          ) ; define right^
        (values idx^ left^ m^ right^)]
       [else
        (define ft-m (measure:ft text-core ft depth))
        (define v (text-measure-chars ft-m))
        (cond
          [(>= idx v) (error 'text-split "index out of bounds")]
          [else
           (define-values (idx^ l m r) (text-split-digit:impl rhs (- idx inner-measure) depth))
           (define right (digit-list->ft r depth))
           (match inner
             [(ft:empty)
              (define empty-list '())
              (define lhs-list (digit-add-list lhs empty-list))
              (define left-list (append lhs-list l))
              (define left^ (digit-list2->ft left-list depth))
              (values idx^ left^ m right)]
             [_
              (define-values (left inner^) (digit-list+ft->digit l inner depth hdR:impl))
              (define left^ (build-ft0 text-core lhs inner^ left depth))
              (values idx^ left^ m right)]
             ) ; match: inner after rhs split
           ]
          ) ; cond: rhs branch bounds
        ]
       ) ; cond: ft:deep
     ]
    ) ; match: ft
  ) ; define text-split-ft:impl

;; Public split function
(define (text-split-at tb pos)
  (define len (text-length tb))
  (cond
    [(= pos 0) (values (text-empty) tb)]
    [(= pos len)
     (define empty-text (text-empty))
     (values tb empty-text)]
    [(or (< pos 0) (> pos len)) (error 'text-split-at "index out of bounds: ~a" pos)]
    [else
      (define-values (_ l m r) (text-split-ft:impl (text-buffer-ft tb) pos 0))
      (define right-ft (consL:impl text-core r m))
      (values (text-buffer l) (text-buffer right-ft))
      ] ; cond branch: split middle
    ) ; cond: text-split-at
  ) ; define text-split-at

;; ========================================
;; Append (O(log n))
;; ========================================

(define (text-append tb1 tb2)
  (define ft1 (text-buffer-ft tb1))
  (define ft2 (text-buffer-ft tb2))
  (text-buffer (concat:impl text-core ft1 ft2))
  ) ; define text-append

;; ========================================
;; Insert/Delete/Set Operations (O(k log n) incremental)
;; ========================================

;; Set character at position (replace) - delete + insert
(define (text-set tb pos char)
  (define len (text-length tb))
  (cond
    [(< pos 0) (error 'text-set "position out of bounds: ~a" pos)]
    [(>= pos len) (error 'text-set "position out of bounds: ~a" pos)]
    [else
      (define tb^ (text-delete tb pos))
      (text-insert tb^ pos char)
      ] ; cond branch: replace
    ) ; cond: text-set
  ) ; define text-set

;; Insert a single character at position (O(k log n))
(define (text-insert tb pos char)
  (define len (text-length tb))
  (cond
    [(< pos 0) (error 'text-insert "position out of bounds: ~a" pos)]
    [(> pos len) (error 'text-insert "position out of bounds: ~a" pos)]
    [else
      (define-values (new-ft _) (incremental-insert (text-buffer-ft tb) pos char))
      (text-buffer new-ft)
      ] ; cond branch: insert in range
    ) ; cond: text-insert
  ) ; define text-insert

;; Insert a string at position (O(m * k log n) where m = string length)
(define (text-insert-string tb pos str)
  (define len (text-length tb))
  (cond
    [(< pos 0) (error 'text-insert-string "position out of bounds: ~a" pos)]
    [(> pos len) (error 'text-insert-string "position out of bounds: ~a" pos)]
    [else
      (define chars0 (string->list str))
      (let loop ([tb tb]
                 [pos^ pos]
                 [chars chars0])
        (match chars
          ['() tb]
          [(cons c rest)
           (define tb^ (text-insert tb pos^ c))
           (loop tb^ (add1 pos^) rest)]
          ) ; match chars
        ) ; let loop
      ] ; cond branch: insert-string in range
    ) ; cond: text-insert-string
  ) ; define text-insert-string

;; Delete character at position (O(k log n))
(define (text-delete tb pos)
  (define len (text-length tb))
  (cond
    [(< pos 0) (error 'text-delete "position out of bounds: ~a" pos)]
    [(>= pos len) (error 'text-delete "position out of bounds: ~a" pos)]
    [else
      (define-values (new-ft _) (incremental-delete (text-buffer-ft tb) pos))
      (text-buffer new-ft)
      ] ; cond branch: delete in range
    ) ; cond: text-delete
  ) ; define text-delete

;; Delete range [start, end) (O((end-start) * k log n))
(define (text-delete-range tb start end)
  (define len (text-length tb))
  (cond
    [(or (< start 0) (> end len) (> start end))
      (error 'text-delete-range "invalid range: ~a to ~a" start end)]
    [(= start end) tb]
    [else
      ;; Delete from end to start to keep indices valid
      (define delete-count (- end start))
      (let loop ([tb tb]
                 [n delete-count])
        (if (zero? n)
            tb
            (let ()
              (define tb^ (text-delete tb start))
              (define n^ (sub1 n))
              (loop tb^ n^)
              ) ; let: next delete step
            ) ; if branch: continue
        ) ; let loop
      ] ; cond branch: delete range
    ) ; cond: text-delete-range
  ) ; define text-delete-range

;; ========================================
;; Word Navigation (O(log n))
;; ========================================

;; Find the character position where word N starts
;; Returns (values start-pos end-pos word-string) or error if out of bounds
(define (text-word-at tb word-idx)
  (define word-count (text-word-count tb))
  (cond
    [(or (< word-idx 0) (>= word-idx word-count))
      (error 'text-word-at "word index out of bounds: ~a" word-idx)]
    [else
      ;; Find start position by searching for (word-idx)th word-start
      (define start-pos (find-nth-word-start tb word-idx))
      ;; Find end position (next whitespace or end of text)
      (define end-pos (find-word-end tb start-pos))
      (define str (text->string tb))
      (define word-str (substring str start-pos end-pos))
      (values start-pos end-pos word-str)
      ] ; cond branch: valid word index
    ) ; cond: text-word-at
  ) ; define text-word-at

;; Find the position of the Nth word start (0-indexed)
(define (find-nth-word-start tb n)
  (find-nth-by-measure tb n text-measure-words text-elem-word-start?)
  ) ; define find-nth-word-start

;; Find the end of word starting at pos
(define (find-word-end tb start-pos)
  (define len (text-length tb))
  (let loop ([pos start-pos])
    (cond
      [(>= pos len) pos]
      [else
        (define c (text-ref tb pos))
        (if (ascii-whitespace? c)
            pos
            (loop (add1 pos))
            ) ; if: whitespace encountered
        ] ; cond branch: scan
      ) ; cond: find-word-end loop
    ) ; let loop
  ) ; define find-word-end

;; Generic helper to find Nth element with a property
(define (find-nth-by-measure tb n measure-accessor flag-accessor)
  (define ft (text-buffer-ft tb))
  (find-nth-by-measure:impl ft n 0 measure-accessor flag-accessor)
  ) ; define find-nth-by-measure

(define (find-nth-by-measure:impl ft n depth measure-accessor flag-accessor)
  (match ft
    [(ft:empty) (error 'find-nth-by-measure "index out of bounds")]
    [(ft:single node)
      (find-nth-in-node node n depth measure-accessor flag-accessor 0)]
    [(ft:deep _ lhs inner rhs)
      (define lhs-m (measure:digit text-core lhs depth))
      (define lhs-count (measure-accessor lhs-m))
      (define lhs-chars (text-measure-chars lhs-m))
      (define inner-depth (add1 depth))
      (define inner-m (measure:ft text-core inner inner-depth))
      (define inner-count (measure-accessor inner-m))
      (define inner-chars (text-measure-chars inner-m))
      (define rhs-start (+ lhs-count inner-count))
      (cond
        [(< n lhs-count)
          (find-nth-in-digit lhs n depth measure-accessor flag-accessor 0)]
        [(< n rhs-start)
          (define inner-pos
            (find-nth-by-measure:impl inner
                                      (- n lhs-count)
                                      inner-depth
                                      measure-accessor
                                      flag-accessor))
          (+ lhs-chars inner-pos)]
        [else
          (+ lhs-chars inner-chars
             (find-nth-in-digit rhs (- n rhs-start) depth measure-accessor flag-accessor 0))
          ] ; cond branch: rhs
        ) ; cond: find-nth-by-measure ft:deep
      ] ; match branch: ft:deep
    ) ; match: ft
  ) ; define find-nth-by-measure:impl

(define (find-nth-in-digit digit n depth measure-accessor flag-accessor char-offset)
  (match digit
    [(digit:1 a)
      (find-nth-in-node a n depth measure-accessor flag-accessor char-offset)]
    [(digit:2 a b)
      (define a-m (measure:node text-core a depth))
      (define a-count (measure-accessor a-m))
      (define a-chars (text-measure-chars a-m))
      (if (< n a-count)
          (find-nth-in-node a n depth measure-accessor flag-accessor char-offset)
          (let ()
            (define n^ (- n a-count))
            (define offset^ (+ char-offset a-chars))
            (find-nth-in-node b n^ depth measure-accessor flag-accessor offset^))
          ) ; if: digit:2 side
      ] ; match branch: digit:2
    [(digit:3 a b c)
      (define a-m (measure:node text-core a depth))
      (define b-m (measure:node text-core b depth))
      (define a-count (measure-accessor a-m))
      (define b-count (measure-accessor b-m))
      (define a-chars (text-measure-chars a-m))
      (define b-chars (text-measure-chars b-m))
      (define b-start a-count)
      (define c-start (+ a-count b-count))
      (cond
        [(< n a-count)
          (find-nth-in-node a n depth measure-accessor flag-accessor char-offset)]
        [(< n c-start)
          (let ()
            (define n^ (- n a-count))
            (define offset^ (+ char-offset a-chars))
            (define result
              (find-nth-in-node b n^ depth measure-accessor flag-accessor offset^))
            result)]
        [else
          (let ()
            (define n^ (- n a-count b-count))
            (define offset^ (+ char-offset a-chars b-chars))
            (define result
              (find-nth-in-node c n^ depth measure-accessor flag-accessor offset^))
            result)
          ] ; cond else
        ) ; cond
      ] ; match branch: digit:3
    [(digit:4 a b c d)
      (define a-m (measure:node text-core a depth))
      (define b-m (measure:node text-core b depth))
      (define c-m (measure:node text-core c depth))
      (define a-count (measure-accessor a-m))
      (define b-count (measure-accessor b-m))
      (define c-count (measure-accessor c-m))
      (define a-chars (text-measure-chars a-m))
      (define b-chars (text-measure-chars b-m))
      (define c-chars (text-measure-chars c-m))
      (define b-start a-count)
      (define c-start (+ a-count b-count))
      (define d-start (+ a-count b-count c-count))
      (cond
        [(< n a-count)
          (find-nth-in-node a n depth measure-accessor flag-accessor char-offset)]
        [(< n c-start)
          (let ()
            (define n^ (- n a-count))
            (define offset^ (+ char-offset a-chars))
            (define result
              (find-nth-in-node b n^ depth measure-accessor flag-accessor offset^))
            result)]
        [(< n d-start)
          (let ()
            (define n^ (- n a-count b-count))
            (define offset^ (+ char-offset a-chars b-chars))
            (define result
              (find-nth-in-node c n^ depth measure-accessor flag-accessor offset^))
            result)]
        [else
          (let ()
            (define n^ (- n a-count b-count c-count))
            (define offset^ (+ char-offset a-chars b-chars c-chars))
            (define result
              (find-nth-in-node d n^ depth measure-accessor flag-accessor offset^))
            result)
          ] ; cond else
        ) ; cond
      ] ; match branch: digit:4
    ) ; match: digit
  ) ; define find-nth-in-digit

(define (find-nth-in-node node n depth measure-accessor flag-accessor char-offset)
  (match depth
    [0
     ;; At leaf level - this should be the element we want
     (if (and (= n 0) (flag-accessor node))
         char-offset
         (error 'find-nth-in-node "element not found")
         ) ; if: leaf match
     ] ; match branch: depth=0
    [_
     (match node
        [(node:2 _ a b)
         (define sub-depth (sub1 depth))
         (define a-m (measure:node text-core a sub-depth))
         (define a-count (measure-accessor a-m))
         (define a-chars (text-measure-chars a-m))
         (if (< n a-count)
             (find-nth-in-node a n sub-depth measure-accessor flag-accessor char-offset)
             (find-nth-in-node b (- n a-count) sub-depth measure-accessor flag-accessor (+ char-offset a-chars))
             ) ; if: node:2 side
         ] ; match branch: node:2
        [(node:3 _ a b c)
         (define sub-depth (sub1 depth))
         (define a-m (measure:node text-core a sub-depth))
         (define b-m (measure:node text-core b sub-depth))
         (define a-count (measure-accessor a-m))
         (define b-count (measure-accessor b-m))
         (define a-chars (text-measure-chars a-m))
         (define b-chars (text-measure-chars b-m))
         (define c-start (+ a-count b-count))
         (cond
           [(< n a-count)
            (find-nth-in-node a n sub-depth measure-accessor flag-accessor char-offset)]
           [(< n c-start)
            (let ()
              (define n^ (- n a-count))
              (define offset^ (+ char-offset a-chars))
              (define result
                (find-nth-in-node b n^ sub-depth measure-accessor flag-accessor offset^))
              result)]
           [else
            (find-nth-in-node c (- n a-count b-count) sub-depth measure-accessor flag-accessor (+ char-offset a-chars b-chars))
            ] ; cond branch: node:3 c
           ) ; cond: node:3
         ] ; match branch: node:3
        ) ; match: node
     ] ; match branch: depth>0
    ) ; match: depth
  ) ; define find-nth-in-node

;; Convert character position to word index
(define (text-char-to-word tb char-pos)
  (define len (text-length tb))
  (define word-count (text-word-count tb))
  (cond
    [(or (< char-pos 0) (>= char-pos len))
      (error 'text-char-to-word "position out of bounds: ~a" char-pos)]
    [(= word-count 0) 0]  ; No words (whitespace only)
    [else
      ;; Count word-starts at or before this position, then subtract 1
      ;; This gives us the 0-indexed word containing this position
      (define count-before (count-before-pos tb char-pos text-measure-words))
      (define elem (text-elem-at tb char-pos))
      (define count-at-or-before
        (if (text-elem-word-start? elem)
            (add1 count-before)
            count-before))
      (max 0 (sub1 count-at-or-before))
      ] ; cond else
    ) ; cond
  ) ; define text-char-to-word

;; Count elements with flag before position
(define (count-before-pos tb pos measure-accessor)
  (if (= pos 0)
      0
      (let ()
        (define-values (prefix _) (text-split-at tb pos))
        (measure-accessor (text-buffer-measure prefix))
      ))
  ) ; define count-before-pos

;; ========================================
;; Line Navigation (O(log n))
;; ========================================

;; Get line at index (0-indexed)
;; Returns (values start-pos end-pos line-string)
(define (text-line-at tb line-idx)
  (define line-count (text-line-count tb))
  (define len (text-length tb))

  ;; Line 0 starts at position 0
  ;; Line N starts after the (N-1)th newline
  (cond
    [(< line-idx 0)
      (error 'text-line-at "line index out of bounds: ~a" line-idx)]
    [(= line-idx 0)
      ;; First line: from start to first newline (or end)
      (define end-pos (find-first-newline tb 0))
      (define actual-end (if end-pos end-pos len))
      (define str (text->string tb))
      (values 0 actual-end (substring str 0 actual-end))
    ]
    [(> line-idx line-count)
      (error 'text-line-at "line index out of bounds: ~a" line-idx)]
    [else
      ;; Line N starts after (N-1)th newline
      (define prev-newline-pos (find-nth-by-measure tb (sub1 line-idx) text-measure-lines text-elem-line-end?))
      (define start-pos (add1 prev-newline-pos))
      (define end-pos (find-first-newline tb start-pos))
      (define actual-end (if end-pos end-pos len))
      (define str (text->string tb))
      (values start-pos actual-end (substring str start-pos actual-end))
      ] ; cond else
    ) ; cond
  ) ; define text-line-at

;; Find first newline from position, or #f if none
(define (find-first-newline tb start-pos)
  (define len (text-length tb))
  (let loop ([pos start-pos])
    (cond
      [(>= pos len) #f]
      [(char=? (text-ref tb pos) #\newline) pos]
      [else
       (loop (add1 pos))
      ] ; cond else
      ) ; cond
    ) ; let loop
  ) ; define find-first-newline

;; Convert character position to line index
(define (text-char-to-line tb char-pos)
  (define len (text-length tb))
  (cond
    [(or (< char-pos 0) (>= char-pos len))
      (error 'text-char-to-line "position out of bounds: ~a" char-pos)]
    [else
      ;; Count newlines before this position
      (count-before-pos tb char-pos text-measure-lines)]
    ))

;; ========================================
;; Paragraph Navigation (O(log n))
;; ========================================

;; Get paragraph at index (0-indexed)
;; Returns (values start-pos end-pos para-string)
(define (text-para-at tb para-idx)
  (define para-count (text-para-count tb))
  (define len (text-length tb))

  (cond
    [(or (< para-idx 0) (>= para-idx para-count))
      (error 'text-para-at "paragraph index out of bounds: ~a" para-idx)]
    [else
      ;; Find start of paragraph (Nth para-start)
      (define start-pos (find-nth-by-measure tb para-idx text-measure-paras text-elem-para-start?))
      ;; Find end of paragraph (next para-start or end of text)
      (define end-pos
        (if (= para-idx (sub1 para-count))
            len
            (let ()
              (define next-para (add1 para-idx))
              (define next-pos
                (find-nth-by-measure tb
                                     next-para
                                     text-measure-paras
                                     text-elem-para-start?))
              (define end-pos^ next-pos)
              end-pos^
              ) ; let: end-pos
            ) ; if: end-pos
        ) ; define end-pos
      ;; Trim trailing whitespace from paragraph
      (define trimmed-end (find-para-content-end tb start-pos end-pos))
      (define str (text->string tb))
      (values start-pos trimmed-end (substring str start-pos trimmed-end))
      ] ; cond else
    ) ; cond
  ) ; define text-para-at

;; Find the last content character in paragraph (excluding trailing whitespace)
(define (find-para-content-end tb start end)
  (define (loop pos)
    (cond
      [(<= pos start) start]
      [else
       (define c (text-ref tb pos))
       (if (ascii-whitespace? c)
           (loop (sub1 pos))
           (add1 pos))
      ] ; cond else
      ) ; cond
    ) ; define loop
  (loop (sub1 end))
  ) ; define find-para-content-end

;; Convert character position to paragraph index
(define (text-char-to-para tb char-pos)
  (define len (text-length tb))
  (define para-count (text-para-count tb))
  (cond
    [(or (< char-pos 0) (>= char-pos len))
      (error 'text-char-to-para "position out of bounds: ~a" char-pos)]
    [(= para-count 0) 0]  ; No paragraphs = whitespace only
    [else
      ;; Count para-starts before or at this position
      (define before-count (count-before-pos tb char-pos text-measure-paras))
      ;; Check if current position is a para-start
      (define elem (text-elem-at tb char-pos))
      (if (text-elem-para-start? elem)
          before-count  ; This is the start of paragraph before-count
          (let ()
            (define prev-count (sub1 before-count))
            (define para-idx^ (max 0 prev-count))
            para-idx^))
      ] ; cond else
    ) ; cond
  )  ; We're in the previous paragraph

;; ========================================
;; Iterators
;; ========================================

;; Iterate over characters
(define (in-text-chars tb)
  (in-generator
    (define ft (text-buffer-ft tb))
    (for ([elem (in-text-elems ft)])
      (yield (text-elem-char elem))
      ) ; for: chars
    ) ; in-generator
  ) ; define in-text-chars

;; Iterate over words as (start end word-string)
(define (in-text-words tb)
  (in-generator
    (define word-count (text-word-count tb))
    (for ([i (in-range word-count)])
      (define-values (s e w) (text-word-at tb i))
      (yield (list s e w))
      ) ; for: words
    ) ; in-generator
  ) ; define in-text-words

;; Iterate over lines as (start end line-string)
(define (in-text-lines tb)
  (in-generator
    (define len (text-length tb))
    (define str (text->string tb))
    (let loop ([start 0] [pos 0])
      (cond
        [(>= pos len)
          (when (< start len)
            (define line (substring str start len))
            (yield (list start len line))
            ) ; when: trailing line
          ] ; cond branch: end
        [(char=? (text-ref tb pos) #\newline)
          (define line (substring str start pos))
          (yield (list start pos line))
          (define next-pos (add1 pos))
          (loop next-pos next-pos)
          ] ; cond branch: newline
        [else
          (loop start (add1 pos))
          ] ; cond branch: continue
        ) ; cond: lines loop
      ) ; let loop
    ) ; in-generator
  ) ; define in-text-lines

;; ========================================
;; Exports
;; ========================================

(provide
  ;; Construction
  text-empty
  text-empty?
  string->text
  text->string

  ;; Measures
  text-length
  text-word-count
  text-line-count
  text-para-count

  ;; Character navigation
  text-ref
  text-set

  ;; Word navigation
  text-word-at
  text-char-to-word

  ;; Line navigation
  text-line-at
  text-char-to-line

  ;; Paragraph navigation
  text-para-at
  text-char-to-para

  ;; Modification
  text-insert
  text-insert-string
  text-delete
  text-delete-range

  ;; Split/append
  text-split-at
  text-append

  ;; Iteration
  in-text-chars
  in-text-words
  in-text-lines

  ;; Internals for testing
  text-buffer
  text-buffer?
  text-buffer-ft
  text-elem-at)
