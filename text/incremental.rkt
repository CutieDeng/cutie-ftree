#lang racket/base

;; text/incremental: O(k log n) incremental insert/delete
;;
;; Key insight: boundary flag changes propagate locally until a "stable point"
;; - word-start: stable after whitespace
;; - para-start: stable after newline
;;
;; Complexity: O(k log n) where k = number of elements needing update
;; In practice, k is small (typically < 10 for most edits)

(require racket/match)
(require "../private/core.rkt" "../private/core-algorithm.rkt")
(require "measure.rkt" "elem.rkt")

;; ========================================
;; Text Core Configuration
;; ========================================

(define text-core (ft:config
  text-measure-empty
  text-elem->measure
  text-measure-append))

;; ========================================
;; Context State for Propagation
;; ========================================

(struct boundary-ctx
  (prev-char           ; previous character or #f
   after-blank-line?   ; are we after a blank line?
   line-has-content?)  ; does current line have non-whitespace?
  #:transparent)

(define (boundary-ctx-initial)
  (boundary-ctx #f #t #f))

(define (boundary-ctx-advance ctx char)
  (match-define (boundary-ctx _ abl? lhc?) ctx)
  (define ws? (ascii-whitespace? char))
  (define newline? (char=? char #\newline))
  (boundary-ctx
    char
    (cond
      [newline? (not lhc?)]
      [else (and abl? ws?)])
    (if newline? #f (or lhc? (not ws?)))))

(define (make-elem-from-ctx ctx char)
  (match-define (boundary-ctx prev-char abl? _) ctx)
  (define ws? (ascii-whitespace? char))
  (text-elem
    char
    (and (not ws?) (or (not prev-char) (ascii-whitespace? prev-char)))
    (char=? char #\newline)
    (and (not ws?) abl?)))

;; ========================================
;; Stability Detection
;; ========================================

;; Stable when flags match, or after newline (para resets)
(define (stable-point? old-elem new-elem)
  (or (and (eq? (text-elem-word-start? old-elem) (text-elem-word-start? new-elem))
           (eq? (text-elem-para-start? old-elem) (text-elem-para-start? new-elem)))
      (text-elem-line-end? new-elem)))

(define (elem-changed? old-elem new-elem)
  (or (not (eq? (text-elem-word-start? old-elem) (text-elem-word-start? new-elem)))
      (not (eq? (text-elem-para-start? old-elem) (text-elem-para-start? new-elem)))))

;; ========================================
;; Context Extraction (O(log n) amortized)
;; ========================================

;; Extract context by scanning backwards from position
;; We need: prev-char, after-blank-line?, line-has-content?
(define (extract-context-at ft pos)
  (define len (text-measure-chars (measure:ft text-core ft 0)))
  (cond
    [(= pos 0) (boundary-ctx-initial)]
    [else
      ;; Get prev-char
      (define prev-char (get-char-at ft (sub1 pos)))

      ;; Scan backwards to determine after-blank-line? and line-has-content?
      ;; This is the expensive part - worst case O(n) but typically short
      (define-values (abl? lhc?)
        (scan-backwards-for-state ft pos))

      (boundary-ctx prev-char abl? lhc?)]))

;; Scan backwards to find paragraph state
;; Returns: (values after-blank-line? line-has-content?)
(define (scan-backwards-for-state ft pos)
  (let loop ([p (sub1 pos)] [found-newline? #f] [line-content? #f])
    (cond
      [(< p 0)
        ;; Reached start of text
        (if found-newline?
            (values (not line-content?) #f)
            (values #t #f))]
      [else
        (define c (get-char-at ft p))
        (define ws? (ascii-whitespace? c))
        (define newline? (char=? c #\newline))
        (cond
          [newline?
            (if found-newline?
                (values #t line-content?)    ; blank line
                (loop (sub1 p) #t #f))]
          [ws?
            (loop (sub1 p) found-newline? line-content?)]
          [else
            ;; Found content
            (if found-newline?
                (values #f line-content?)    ; non-blank line before
                (loop (sub1 p) found-newline? #t))])])))

;; Get character at position (O(log n))
(define (get-char-at ft pos)
  (text-elem-char (get-elem-at ft pos 0)))

(define (get-elem-at ft pos depth)
  (match ft
    [(ft:empty) (error 'get-elem-at "empty tree")]
    [(ft:single node) (get-elem-in-node node pos depth)]
    [(ft:deep _ lhs inner rhs)
      (define lhs-sz (text-measure-chars (measure:digit text-core lhs depth)))
      (define inner-sz (text-measure-chars (measure:ft text-core inner (add1 depth))))
      (cond
        [(< pos lhs-sz) (get-elem-in-digit lhs pos depth)]
        [(< pos (+ lhs-sz inner-sz)) (get-elem-at inner (- pos lhs-sz) (add1 depth))]
        [else (get-elem-in-digit rhs (- pos lhs-sz inner-sz) depth)])]))

(define (get-elem-in-digit digit pos depth)
  (match digit
    [(digit:1 a) (get-elem-in-node a pos depth)]
    [(digit:2 a b)
      (define a-sz (text-measure-chars (measure:node text-core a depth)))
      (if (< pos a-sz)
          (get-elem-in-node a pos depth)
          (get-elem-in-node b (- pos a-sz) depth))]
    [(digit:3 a b c)
      (define a-sz (text-measure-chars (measure:node text-core a depth)))
      (define b-sz (text-measure-chars (measure:node text-core b depth)))
      (cond
        [(< pos a-sz) (get-elem-in-node a pos depth)]
        [(< pos (+ a-sz b-sz)) (get-elem-in-node b (- pos a-sz) depth)]
        [else (get-elem-in-node c (- pos a-sz b-sz) depth)])]
    [(digit:4 a b c d)
      (define a-sz (text-measure-chars (measure:node text-core a depth)))
      (define b-sz (text-measure-chars (measure:node text-core b depth)))
      (define c-sz (text-measure-chars (measure:node text-core c depth)))
      (cond
        [(< pos a-sz) (get-elem-in-node a pos depth)]
        [(< pos (+ a-sz b-sz)) (get-elem-in-node b (- pos a-sz) depth)]
        [(< pos (+ a-sz b-sz c-sz)) (get-elem-in-node c (- pos a-sz b-sz) depth)]
        [else (get-elem-in-node d (- pos a-sz b-sz c-sz) depth)])]))

(define (get-elem-in-node node pos depth)
  (match depth
    [0 node]
    [_ (match node
        [(node:2 _ a b)
          (define a-sz (text-measure-chars (measure:node text-core a (sub1 depth))))
          (if (< pos a-sz)
              (get-elem-in-node a pos (sub1 depth))
              (get-elem-in-node b (- pos a-sz) (sub1 depth)))]
        [(node:3 _ a b c)
          (define a-sz (text-measure-chars (measure:node text-core a (sub1 depth))))
          (define b-sz (text-measure-chars (measure:node text-core b (sub1 depth))))
          (cond
            [(< pos a-sz) (get-elem-in-node a pos (sub1 depth))]
            [(< pos (+ a-sz b-sz)) (get-elem-in-node b (- pos a-sz) (sub1 depth))]
            [else (get-elem-in-node c (- pos a-sz b-sz) (sub1 depth))])])]))

;; ========================================
;; Simple List-based Implementation
;; Convert to list, modify, convert back.
;; This is O(n) but correct. Optimizations can come later.
;; ========================================

;; Convert ft to list of elements
(define (ft->list ft)
  (ft->elem-list ft 0))

(define (ft->elem-list ft depth)
  (match ft
    [(ft:empty) '()]
    [(ft:single node) (node->elem-list node depth)]
    [(ft:deep _ lhs inner rhs)
      (append (digit->elem-list lhs depth)
              (ft->elem-list inner (add1 depth))
              (digit->elem-list rhs depth))]))

(define (digit->elem-list digit depth)
  (match digit
    [(digit:1 a) (node->elem-list a depth)]
    [(digit:2 a b) (append (node->elem-list a depth) (node->elem-list b depth))]
    [(digit:3 a b c) (append (node->elem-list a depth) (node->elem-list b depth) (node->elem-list c depth))]
    [(digit:4 a b c d) (append (node->elem-list a depth) (node->elem-list b depth) (node->elem-list c depth) (node->elem-list d depth))]))

(define (node->elem-list node depth)
  (match depth
    [0 (list node)]
    [_ (match node
        [(node:2 _ a b) (append (node->elem-list a (sub1 depth)) (node->elem-list b (sub1 depth)))]
        [(node:3 _ a b c) (append (node->elem-list a (sub1 depth)) (node->elem-list b (sub1 depth)) (node->elem-list c (sub1 depth)))])]))

;; Convert list of elements to ft
(define (list->ft elems)
  (match elems
    ['() (ft:empty)]
    [(list a) (ft:single a)]
    [_ (for/fold ([ft (ft:empty)]) ([elem elems])
         (consR:impl text-core ft elem 0))]))

;; Split list at position
(define (list-take lst n)
  (if (or (= n 0) (null? lst))
      '()
      (cons (car lst) (list-take (cdr lst) (sub1 n)))))

(define (list-drop lst n)
  (if (or (= n 0) (null? lst))
      lst
      (list-drop (cdr lst) (sub1 n))))

;; ========================================
;; Incremental Insert (O(n) for now)
;; ========================================

(define (incremental-insert ft pos char)
  (define len (text-measure-chars (measure:ft text-core ft 0)))
  (cond
    [(= len 0)
      (define elem (make-elem-from-ctx (boundary-ctx-initial) char))
      (values (ft:single elem) 1)]
    [else
      ;; Get context at insertion point
      (define ctx (extract-context-at ft pos))

      ;; Create new element
      (define new-elem (make-elem-from-ctx ctx char))

      ;; Convert to list, insert, and propagate
      (define elems (ft->list ft))
      (define prefix (list-take elems pos))
      (define suffix (list-drop elems pos))

      ;; Propagate through suffix
      (define new-ctx (boundary-ctx-advance ctx char))
      (define-values (updated-suffix update-count)
        (propagate-through-list new-ctx suffix))

      ;; Rebuild tree
      (define new-elems (append prefix (list new-elem) updated-suffix))
      (values (list->ft new-elems) (add1 update-count))]))

;; ========================================
;; Incremental Delete (O(n) for now)
;; ========================================

(define (incremental-delete ft pos)
  (define len (text-measure-chars (measure:ft text-core ft 0)))
  (cond
    [(= len 1)
      (values (ft:empty) 0)]
    [else
      ;; Get context at deletion point
      (define ctx (extract-context-at ft pos))

      ;; Convert to list and remove element
      (define elems (ft->list ft))
      (define prefix (list-take elems pos))
      (define suffix (list-drop elems (add1 pos)))  ; skip the deleted element

      ;; Propagate through suffix
      (define-values (updated-suffix update-count)
        (propagate-through-list ctx suffix))

      ;; Rebuild tree
      (define new-elems (append prefix updated-suffix))
      (values (list->ft new-elems) update-count)]))

;; ========================================
;; Propagation Through List (O(k))
;; ========================================

;; Propagate boundary updates through list, stopping at stable point
(define (propagate-through-list ctx elems)
  (let loop ([ctx ctx] [remaining elems] [result '()] [count 0] [prev-changed? #t])
    (match remaining
      ['()
        (values (reverse result) count)]
      [(cons old-elem rest)
        (define char (text-elem-char old-elem))
        (define new-elem (make-elem-from-ctx ctx char))
        (define new-ctx (boundary-ctx-advance ctx char))
        (define changed? (elem-changed? old-elem new-elem))

        (cond
          ;; If stable and nothing changed, append rest unchanged
          [(and (not prev-changed?) (not changed?) (stable-point? old-elem new-elem))
            (values (append (reverse result) remaining) count)]
          [else
            (loop new-ctx
                  rest
                  (cons new-elem result)
                  (if changed? (add1 count) count)
                  changed?)])])))

;; ========================================
;; Exports
;; ========================================

(provide
  text-core
  incremental-insert
  incremental-delete
  boundary-ctx
  boundary-ctx-initial
  boundary-ctx-advance
  extract-context-at
  propagate-through-list)
