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

(define text-core (ft:config
  text-measure-empty
  text-elem->measure
  text-measure-append))

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
  (text-buffer text-empty-impl))

(define (text-empty? tb)
  (match (text-buffer-ft tb)
    [(ft:empty) #t]
    [_ #f]))

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
                                       (ascii-whitespace? prev-char))))

          ;; Create element
          (define elem (text-elem c word-start? is-newline? ps?))

          ;; Update state for next iteration
          (define new-line-has-content?
            (if is-newline?
                #f  ; Reset on newline
                (or line-has-content? (not ws?))))

          ;; After blank line if:
          ;; - This is a newline AND current line has no content
          ;; - Or we were already after blank line and this is whitespace (but not newline starting content)
          (define new-after-blank-line?
            (cond
              [is-newline? (not line-has-content?)]  ; Blank line if no content before this newline
              [else (and after-blank-line? ws?)]))   ; Stay in blank region if whitespace

          (loop rest
                (consR:impl text-core ft elem)
                c
                new-after-blank-line?
                new-line-has-content?)])))
  (text-buffer ft))

;; Convert text-buffer to string
(define (text->string tb)
  (define ft (text-buffer-ft tb))
  (list->string
    (for/list ([elem (in-text-elems ft)])
      (text-elem-char elem))))

;; Internal: iterate over text elements
(define (in-text-elems ft)
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
    (yield-ft ft 0)))

;; ========================================
;; Measures (O(1))
;; ========================================

(define (text-length tb)
  (text-measure-chars (text-buffer-measure tb)))

(define (text-word-count tb)
  (text-measure-words (text-buffer-measure tb)))

(define (text-line-count tb)
  (text-measure-lines (text-buffer-measure tb)))

(define (text-para-count tb)
  (text-measure-paras (text-buffer-measure tb)))

;; Get the measure from the root
(define (text-buffer-measure tb)
  (measure:ft text-core (text-buffer-ft tb) 0))

;; ========================================
;; Character-level Navigation (O(log n))
;; ========================================

(define (make-char-measure-fn depth)
  (lambda (node) (text-measure-chars (measure:node text-core node depth))))

(define (text-ref-node:impl node idx depth)
  (match depth
    [0 (text-elem-char node)]
    [_ (define measure-fn (make-char-measure-fn (sub1 depth)))
      (define-values (idx^ child) (node-find-by-measure node idx measure-fn))
      (text-ref-node:impl child idx^ (sub1 depth))]))

(define (text-ref-digit:impl digit idx depth)
  (define measure-fn (make-char-measure-fn depth))
  (define-values (idx^ node) (digit-find-by-measure digit idx measure-fn))
  (text-ref-node:impl node idx^ depth))

(define (text-ref-ft:impl ft idx depth)
  (match ft
    [(ft:single r) (text-ref-node:impl r idx depth)]
    [(ft:deep _ lhs inner rhs)
      (define lhs-measure (text-measure-chars (measure:digit text-core lhs depth)))
      (define inner-measure (+ lhs-measure (text-measure-chars (measure:ft text-core inner (add1 depth)))))
      (cond
        [(< idx lhs-measure) (text-ref-digit:impl lhs idx depth)]
        [(< idx inner-measure) (text-ref-ft:impl inner (- idx lhs-measure) (add1 depth))]
        [else (text-ref-digit:impl rhs (- idx inner-measure) depth)])]))

(define (text-ref tb pos)
  (define len (text-length tb))
  (cond
    [(< pos 0) (error 'text-ref "index out of bounds: ~a" pos)]
    [(>= pos len) (error 'text-ref "index out of bounds: ~a" pos)]
    [else (text-ref-ft:impl (text-buffer-ft tb) pos 0)]))

;; Get the full element at position
(define (text-elem-at-node:impl node idx depth)
  (match depth
    [0 node]
    [_ (define measure-fn (make-char-measure-fn (sub1 depth)))
      (define-values (idx^ child) (node-find-by-measure node idx measure-fn))
      (text-elem-at-node:impl child idx^ (sub1 depth))]))

(define (text-elem-at-digit:impl digit idx depth)
  (define measure-fn (make-char-measure-fn depth))
  (define-values (idx^ node) (digit-find-by-measure digit idx measure-fn))
  (text-elem-at-node:impl node idx^ depth))

(define (text-elem-at-ft:impl ft idx depth)
  (match ft
    [(ft:single r) (text-elem-at-node:impl r idx depth)]
    [(ft:deep _ lhs inner rhs)
      (define lhs-measure (text-measure-chars (measure:digit text-core lhs depth)))
      (define inner-measure (+ lhs-measure (text-measure-chars (measure:ft text-core inner (add1 depth)))))
      (cond
        [(< idx lhs-measure) (text-elem-at-digit:impl lhs idx depth)]
        [(< idx inner-measure) (text-elem-at-ft:impl inner (- idx lhs-measure) (add1 depth))]
        [else (text-elem-at-digit:impl rhs (- idx inner-measure) depth)])]))

(define (text-elem-at tb pos)
  (define len (text-length tb))
  (cond
    [(< pos 0) (error 'text-elem-at "index out of bounds: ~a" pos)]
    [(>= pos len) (error 'text-elem-at "index out of bounds: ~a" pos)]
    [else (text-elem-at-ft:impl (text-buffer-ft tb) pos 0)]))

;; ========================================
;; Split Operations (O(log n))
;; ========================================

;; Helper for node->digit conversion
(define (node->list node)
  (match node
    [(node:2 _ a b) (list a b)]
    [(node:3 _ a b c) (list a b c)]))

;; Split digit by character index
(define (text-split-digit:impl digit idx depth)
  (define measure-fn (make-char-measure-fn depth))
  (match digit
    [(digit:1 a)
      (cond
        [(< idx (measure-fn a)) (values idx '() a '())]
        [else (error 'text-split-digit "index out of bounds")])]
    [(digit:2 a b)
      (define a-sz (measure-fn a))
      (cond
        [(< idx a-sz) (values idx '() a (list b))]
        [else (values (- idx a-sz) (list a) b '())])]
    [(digit:3 a b c)
      (define a-sz (measure-fn a))
      (define ab-sz (+ a-sz (measure-fn b)))
      (cond
        [(< idx a-sz) (values idx '() a (list b c))]
        [(< idx ab-sz) (values (- idx a-sz) (list a) b (list c))]
        [else (values (- idx ab-sz) (list a b) c '())])]
    [(digit:4 a b c d)
      (define a-sz (measure-fn a))
      (define ab-sz (+ a-sz (measure-fn b)))
      (define abc-sz (+ ab-sz (measure-fn c)))
      (cond
        [(< idx a-sz) (values idx '() a (list b c d))]
        [(< idx ab-sz) (values (- idx a-sz) (list a) b (list c d))]
        [(< idx abc-sz) (values (- idx ab-sz) (list a b) c (list d))]
        [else (values (- idx abc-sz) (list a b c) d '())])]))

;; Split node by character index
(define (text-split-node:impl node idx depth)
  (define measure-fn (make-char-measure-fn (sub1 depth)))
  (match node
    [(node:2 _ a b)
      (define a-sz (measure-fn a))
      (cond
        [(< idx a-sz) (values idx '() a (list b))]
        [else (values (- idx a-sz) (list a) b '())])]
    [(node:3 _ a b c)
      (define a-sz (measure-fn a))
      (define ab-sz (+ a-sz (measure-fn b)))
      (cond
        [(< idx a-sz) (values idx '() a (list b c))]
        [(< idx ab-sz) (values (- idx a-sz) (list a) b (list c))]
        [else (values (- idx ab-sz) (list a b) c '())])]))

;; Build ft from node list
(define (digit-list->ft lst depth)
  (match lst
    ['() (ft:empty)]
    [(list a) (ft:single a)]
    [(list a b)
      (define m (text-measure-append
                  (measure:node text-core a depth)
                  (measure:node text-core b depth)))
      (ft:deep m (digit:1 a) (ft:empty) (digit:1 b))]
    [(list a b c)
      (define m (text-measure-append
                  (text-measure-append
                    (measure:node text-core a depth)
                    (measure:node text-core b depth))
                  (measure:node text-core c depth)))
      (ft:deep m (digit:1 a) (ft:empty) (digit:2 b c))]
    [(list a b c d)
      (define m (text-measure-append
                  (text-measure-append
                    (measure:node text-core a depth)
                    (measure:node text-core b depth))
                  (text-measure-append
                    (measure:node text-core c depth)
                    (measure:node text-core d depth))))
      (ft:deep m (digit:2 a b) (ft:empty) (digit:2 c d))]))

(define (digit-list2->ft lst depth)
  (if (<= (length lst) 4)
      (digit-list->ft lst depth)
      (let ([v (for/fold ([m (text-measure-empty)]) ([j lst])
                 (text-measure-append m (measure:node text-core j depth)))])
        (match lst
          [(list a b c d e)
           (ft:deep v (digit:2 a b) (ft:empty) (digit:3 c d e))]
          [(list a b c d e f)
           (ft:deep v (digit:3 a b c) (ft:empty) (digit:3 d e f))]
          [(list a b c d e f g)
           (ft:deep v (digit:3 a b c) (ft:empty) (digit:4 d e f g))]
          ) ; match: lst
        ) ; let: v
      ) ; if: digit-list2->ft
  ) ; define digit-list2->ft

(define (digit-list+ft->digit lst ft depth pop)
  (match lst
    ['()
      (define-values (h ft^) (pop text-core ft (add1 depth)))
      (values (digit:1 h) ft^)]
    [(list a) (values (digit:1 a) ft)]
    [(list a b) (values (digit:2 a b) ft)]
    [(list a b c) (values (digit:3 a b c) ft)]
    [(list a b c d) (values (digit:4 a b c d) ft)]
    ) ; match: lst
  ) ; define digit-list+ft->digit

(define (node->digit node depth)
  (list->digit (node->list node) (sub1 depth)))

(define (left-digit+ft->ft digit ft depth)
  (match ft
    [(ft:empty)
     (define digit^ (digit-add-list digit '()))
     (digit-list->ft digit^ depth)]
    [_
     (define-values (r ft^) (hdR:impl text-core ft (add1 depth)))
     (build-ft0 text-core digit ft^ (node->digit r (add1 depth)) depth)]
    ) ; match: ft
  ) ; define left-digit+ft->ft

(define (right-digit+ft->ft digit ft depth)
  (match ft
    [(ft:empty)
     (define digit^ (digit-add-list digit '()))
     (digit-list->ft digit^ depth)]
    [_
     (define-values (l ft^) (hdL:impl text-core ft (add1 depth)))
     (build-ft0 text-core (node->digit l (add1 depth)) ft^ digit depth)]
    ) ; match: ft
  ) ; define right-digit+ft->ft

;; Main split implementation
(define (text-split-ft:impl ft idx depth)
  (match ft
    [(ft:empty) (error 'text-split "index out of bounds")]
    [(ft:single v)
     (define m (text-measure-chars (measure:node text-core v depth)))
     (cond
       [(>= idx m) (error 'text-split "index out of bounds")]
       [else (values idx (ft:empty) v (ft:empty))]
       ) ; cond: ft:single
     ]
    [(ft:deep _ lhs inner rhs)
     (define lhs-measure (text-measure-chars (measure:digit text-core lhs depth)))
     (define inner-measure
       (+ lhs-measure (text-measure-chars (measure:ft text-core inner (add1 depth)))))
     (cond
       [(< idx lhs-measure)
        (define-values (idx^ l m r) (text-split-digit:impl lhs idx depth))
        (define left (digit-list->ft l depth))
        (match inner
          [(ft:empty)
           (values idx^ left m (digit-list2->ft (append r (digit-add-list rhs '())) depth))]
          [_
           (define-values (right inner^) (digit-list+ft->digit r inner depth hdL:impl))
           (values idx^ left m (build-ft0 text-core right inner^ rhs depth))]
          ) ; match: inner after lhs split
        ]
       [(< idx inner-measure)
        (define-values (rest-idx l m r)
          (text-split-ft:impl inner (- idx lhs-measure) (add1 depth)))
        (define left (left-digit+ft->ft lhs l depth))
        (define right (right-digit+ft->ft rhs r depth))
        (define-values (idx^ l^ m^ r^) (text-split-node:impl m rest-idx (add1 depth)))
        ;; l^ and r^ are elements at depth (from the node at depth+1)
        (define left^
          (for/fold ([init left]) ([i l^])
            (consR:impl text-core init i depth)))
        (define right^
          (for/foldr ([init right]) ([i r^])
            (consL:impl text-core init i depth)))
        (values idx^ left^ m^ right^)]
       [else
        (define v (text-measure-chars (measure:ft text-core ft depth)))
        (cond
          [(>= idx v) (error 'text-split "index out of bounds")]
          [else
           (define-values (idx^ l m r) (text-split-digit:impl rhs (- idx inner-measure) depth))
           (define right (digit-list->ft r depth))
           (match inner
             [(ft:empty)
              (values idx^ (digit-list2->ft (append (digit-add-list lhs '()) l) depth) m right)]
             [_
              (define-values (left inner^) (digit-list+ft->digit l inner depth hdR:impl))
              (values idx^ (build-ft0 text-core lhs inner^ left depth) m right)]
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
    [(= pos len) (values tb (text-empty))]
    [(or (< pos 0) (> pos len)) (error 'text-split-at "index out of bounds: ~a" pos)]
    [else
      (define-values (_ l m r) (text-split-ft:impl (text-buffer-ft tb) pos 0))
      (values (text-buffer l) (text-buffer (consL:impl text-core r m)))]))

;; ========================================
;; Append (O(log n))
;; ========================================

(define (text-append tb1 tb2)
  (text-buffer (concat:impl text-core (text-buffer-ft tb1) (text-buffer-ft tb2))))

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
      (text-insert (text-delete tb pos) pos char)]))

;; Insert a single character at position (O(k log n))
(define (text-insert tb pos char)
  (define len (text-length tb))
  (cond
    [(< pos 0) (error 'text-insert "position out of bounds: ~a" pos)]
    [(> pos len) (error 'text-insert "position out of bounds: ~a" pos)]
    [else
      (define-values (new-ft _) (incremental-insert (text-buffer-ft tb) pos char))
      (text-buffer new-ft)]))

;; Insert a string at position (O(m * k log n) where m = string length)
(define (text-insert-string tb pos str)
  (define len (text-length tb))
  (cond
    [(< pos 0) (error 'text-insert-string "position out of bounds: ~a" pos)]
    [(> pos len) (error 'text-insert-string "position out of bounds: ~a" pos)]
    [else
      (for/fold ([tb tb]) ([c (in-string str)] [i (in-naturals)])
        (text-insert tb (+ pos i) c))]))

;; Delete character at position (O(k log n))
(define (text-delete tb pos)
  (define len (text-length tb))
  (cond
    [(< pos 0) (error 'text-delete "position out of bounds: ~a" pos)]
    [(>= pos len) (error 'text-delete "position out of bounds: ~a" pos)]
    [else
      (define-values (new-ft _) (incremental-delete (text-buffer-ft tb) pos))
      (text-buffer new-ft)]))

;; Delete range [start, end) (O((end-start) * k log n))
(define (text-delete-range tb start end)
  (define len (text-length tb))
  (cond
    [(or (< start 0) (> end len) (> start end))
      (error 'text-delete-range "invalid range: ~a to ~a" start end)]
    [(= start end) tb]
    [else
      ;; Delete from end to start to keep indices valid
      (for/fold ([tb tb]) ([_ (in-range (- end start))])
        (text-delete tb start))]))

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
      (define word-str (substring (text->string tb) start-pos end-pos))
      (values start-pos end-pos word-str)]))

;; Find the position of the Nth word start (0-indexed)
(define (find-nth-word-start tb n)
  (find-nth-by-measure tb n text-measure-words text-elem-word-start?))

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
            (loop (add1 pos)))])))

;; Generic helper to find Nth element with a property
(define (find-nth-by-measure tb n measure-accessor flag-accessor)
  (define ft (text-buffer-ft tb))
  (find-nth-by-measure:impl ft n 0 measure-accessor flag-accessor))

(define (find-nth-by-measure:impl ft n depth measure-accessor flag-accessor)
  (match ft
    [(ft:empty) (error 'find-nth-by-measure "index out of bounds")]
    [(ft:single node)
      (find-nth-in-node node n depth measure-accessor flag-accessor 0)]
    [(ft:deep _ lhs inner rhs)
      (define lhs-count (measure-accessor (measure:digit text-core lhs depth)))
      (define inner-count (measure-accessor (measure:ft text-core inner (add1 depth))))
      (cond
        [(< n lhs-count)
          (find-nth-in-digit lhs n depth measure-accessor flag-accessor 0)]
        [(< n (+ lhs-count inner-count))
          (define lhs-chars (text-measure-chars (measure:digit text-core lhs depth)))
          (+ lhs-chars
             (find-nth-by-measure:impl inner (- n lhs-count) (add1 depth) measure-accessor flag-accessor))]
        [else
          (define lhs-chars (text-measure-chars (measure:digit text-core lhs depth)))
          (define inner-chars (text-measure-chars (measure:ft text-core inner (add1 depth))))
          (+ lhs-chars inner-chars
             (find-nth-in-digit rhs (- n lhs-count inner-count) depth measure-accessor flag-accessor 0))])]))

(define (find-nth-in-digit digit n depth measure-accessor flag-accessor char-offset)
  (match digit
    [(digit:1 a)
      (find-nth-in-node a n depth measure-accessor flag-accessor char-offset)]
    [(digit:2 a b)
      (define a-count (measure-accessor (measure:node text-core a depth)))
      (define a-chars (text-measure-chars (measure:node text-core a depth)))
      (if (< n a-count)
          (find-nth-in-node a n depth measure-accessor flag-accessor char-offset)
          (find-nth-in-node b (- n a-count) depth measure-accessor flag-accessor (+ char-offset a-chars)))]
    [(digit:3 a b c)
      (define a-count (measure-accessor (measure:node text-core a depth)))
      (define b-count (measure-accessor (measure:node text-core b depth)))
      (define a-chars (text-measure-chars (measure:node text-core a depth)))
      (define b-chars (text-measure-chars (measure:node text-core b depth)))
      (cond
        [(< n a-count)
          (find-nth-in-node a n depth measure-accessor flag-accessor char-offset)]
        [(< n (+ a-count b-count))
          (find-nth-in-node b (- n a-count) depth measure-accessor flag-accessor (+ char-offset a-chars))]
        [else
          (find-nth-in-node c (- n a-count b-count) depth measure-accessor flag-accessor (+ char-offset a-chars b-chars))])]
    [(digit:4 a b c d)
      (define a-count (measure-accessor (measure:node text-core a depth)))
      (define b-count (measure-accessor (measure:node text-core b depth)))
      (define c-count (measure-accessor (measure:node text-core c depth)))
      (define a-chars (text-measure-chars (measure:node text-core a depth)))
      (define b-chars (text-measure-chars (measure:node text-core b depth)))
      (define c-chars (text-measure-chars (measure:node text-core c depth)))
      (cond
        [(< n a-count)
          (find-nth-in-node a n depth measure-accessor flag-accessor char-offset)]
        [(< n (+ a-count b-count))
          (find-nth-in-node b (- n a-count) depth measure-accessor flag-accessor (+ char-offset a-chars))]
        [(< n (+ a-count b-count c-count))
          (find-nth-in-node c (- n a-count b-count) depth measure-accessor flag-accessor (+ char-offset a-chars b-chars))]
        [else
          (find-nth-in-node d (- n a-count b-count c-count) depth measure-accessor flag-accessor (+ char-offset a-chars b-chars c-chars))])]))

(define (find-nth-in-node node n depth measure-accessor flag-accessor char-offset)
  (match depth
    [0
     ;; At leaf level - this should be the element we want
     (if (and (= n 0) (flag-accessor node))
         char-offset
         (error 'find-nth-in-node "element not found"))]
    [_
     (match node
        [(node:2 _ a b)
         (define a-count (measure-accessor (measure:node text-core a (sub1 depth))))
         (define a-chars (text-measure-chars (measure:node text-core a (sub1 depth))))
         (if (< n a-count)
             (find-nth-in-node a n (sub1 depth) measure-accessor flag-accessor char-offset)
             (find-nth-in-node b (- n a-count) (sub1 depth) measure-accessor flag-accessor (+ char-offset a-chars)))]
        [(node:3 _ a b c)
         (define a-count (measure-accessor (measure:node text-core a (sub1 depth))))
         (define b-count (measure-accessor (measure:node text-core b (sub1 depth))))
         (define a-chars (text-measure-chars (measure:node text-core a (sub1 depth))))
         (define b-chars (text-measure-chars (measure:node text-core b (sub1 depth))))
         (cond
           [(< n a-count)
            (find-nth-in-node a n (sub1 depth) measure-accessor flag-accessor char-offset)]
           [(< n (+ a-count b-count))
            (find-nth-in-node b (- n a-count) (sub1 depth) measure-accessor flag-accessor (+ char-offset a-chars))]
           [else
            (find-nth-in-node c (- n a-count b-count) (sub1 depth) measure-accessor flag-accessor (+ char-offset a-chars b-chars))]
           ) ; cond: node:3
         ]
        ) ; match: node
     ]
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
      (max 0 (sub1 count-at-or-before))]))

;; Count elements with flag before position
(define (count-before-pos tb pos measure-accessor)
  (if (= pos 0)
      0
      (let ()
        (define-values (prefix _) (text-split-at tb pos))
        (measure-accessor (text-buffer-measure prefix)))))

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
      (values 0 actual-end (substring (text->string tb) 0 actual-end))]
    [(> line-idx line-count)
      (error 'text-line-at "line index out of bounds: ~a" line-idx)]
    [else
      ;; Line N starts after (N-1)th newline
      (define prev-newline-pos (find-nth-by-measure tb (sub1 line-idx) text-measure-lines text-elem-line-end?))
      (define start-pos (add1 prev-newline-pos))
      (define end-pos (find-first-newline tb start-pos))
      (define actual-end (if end-pos end-pos len))
      (values start-pos actual-end (substring (text->string tb) start-pos actual-end))]))

;; Find first newline from position, or #f if none
(define (find-first-newline tb start-pos)
  (define len (text-length tb))
  (let loop ([pos start-pos])
    (cond
      [(>= pos len) #f]
      [(char=? (text-ref tb pos) #\newline) pos]
      [else (loop (add1 pos))])))

;; Convert character position to line index
(define (text-char-to-line tb char-pos)
  (define len (text-length tb))
  (cond
    [(or (< char-pos 0) (>= char-pos len))
      (error 'text-char-to-line "position out of bounds: ~a" char-pos)]
    [else
      ;; Count newlines before this position
      (count-before-pos tb char-pos text-measure-lines)]))

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
            (find-nth-by-measure tb (add1 para-idx) text-measure-paras text-elem-para-start?)))
      ;; Trim trailing whitespace from paragraph
      (define trimmed-end (find-para-content-end tb start-pos end-pos))
      (values start-pos trimmed-end (substring (text->string tb) start-pos trimmed-end))]))

;; Find the last content character in paragraph (excluding trailing whitespace)
(define (find-para-content-end tb start end)
  (let loop ([pos (sub1 end)])
    (cond
      [(<= pos start) start]
      [else
        (define c (text-ref tb pos))
        (if (ascii-whitespace? c)
            (loop (sub1 pos))
            (add1 pos))])))

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
          (max 0 (sub1 before-count)))]))  ; We're in the previous paragraph

;; ========================================
;; Iterators
;; ========================================

;; Iterate over characters
(define (in-text-chars tb)
  (in-generator
    (for ([elem (in-text-elems (text-buffer-ft tb))])
      (yield (text-elem-char elem)))))

;; Iterate over words as (start end word-string)
(define (in-text-words tb)
  (in-generator
    (define word-count (text-word-count tb))
    (for ([i (in-range word-count)])
      (define-values (s e w) (text-word-at tb i))
      (yield (list s e w)))))

;; Iterate over lines as (start end line-string)
(define (in-text-lines tb)
  (in-generator
    (define len (text-length tb))
    (define str (text->string tb))
    (let loop ([start 0] [pos 0])
      (cond
        [(>= pos len)
          (when (< start len)
            (yield (list start len (substring str start len))))]
        [(char=? (text-ref tb pos) #\newline)
          (yield (list start pos (substring str start pos)))
          (loop (add1 pos) (add1 pos))]
        [else
          (loop start (add1 pos))]))))

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
