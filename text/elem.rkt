#lang racket/base

;; text-elem: element type for text buffer
;; Each element is a character with boundary flags

(require racket/match)
(require "measure.rkt")

;; ========================================
;; Element Structure
;; ========================================

;; A text element contains:
;; - char: the character
;; - word-start?: #t if this character starts a new word
;; - line-end?: #t if this character ends a line (is #\newline)
;; - para-start?: #t if this character starts a new paragraph
(struct text-elem (char word-start? line-end? para-start?) #:transparent)

;; ========================================
;; ASCII Whitespace Detection
;; ========================================

;; ASCII whitespace: space, tab, newline, return
(define (ascii-whitespace? c)
  (define is-space? (char=? c #\space))
  (define is-tab? (char=? c #\tab))
  (define is-newline? (char=? c #\newline))
  (define is-return? (char=? c #\return))
  (or is-space?
      is-tab?
      is-newline?
      is-return?))

;; ========================================
;; Boundary Detection Functions
;; ========================================

;; Determine if character starts a word:
;; - Non-whitespace character
;; - Previous character is whitespace or start of text (prev-char = #f)
(define (word-start? char prev-char)
  (define has-prev? (and prev-char #t))
  (define prev-char-is-whitespace?
    (if has-prev?
        (ascii-whitespace? prev-char)
        #f))
  (define prev-is-whitespace?
    prev-char-is-whitespace?)
  (define char-is-whitespace?
    (ascii-whitespace? char))
  (and (not (ascii-whitespace? char))
       (or (not prev-char)
           prev-is-whitespace?))
  )

;; Determine if character ends a line:
;; - Is a newline character
(define (line-end? char)
  (char=? char #\newline))

;; Determine if we're in a blank region:
;; - Only whitespace since last paragraph start
;; prev-blank? indicates if we're currently in a blank region
(define (in-blank-region? char prev-blank?)
  (define char-is-whitespace? (ascii-whitespace? char))
  (and prev-blank? char-is-whitespace?))

;; Determine if character starts a paragraph:
;; - Non-whitespace character
;; - After a blank line or at start of text
;; after-blank-line? indicates if we just saw a blank line
(define (para-start? char after-blank-line?)
  (and (not (ascii-whitespace? char))
       after-blank-line?))

;; ========================================
;; Element Creation from Context
;; ========================================

;; Create a text-elem from a character and context
;; prev-char: previous character or #f for start of text
;; after-blank-line?: #t if we're after a blank line or at start
(define (make-text-elem char prev-char after-blank-line?)
  (define ws? (word-start? char prev-char))
  (define le? (line-end? char))
  (define ps? (para-start? char after-blank-line?))
  (text-elem
    char
    ws?
    le?
    ps?))

;; ========================================
;; Measure Function for ft:config
;; ========================================

;; Convert a text-elem to its measure contribution
(define (text-elem->measure elem)
  (match-define (text-elem _ ws? le? ps?) elem)
  (define para-count
    (if ps? 1 0))
  (text-measure
    1
    (if ws? 1 0)
    (if le? 1 0)
    para-count))

;; ========================================
;; Exports
;; ========================================

(provide
  ;; Structure
  text-elem
  text-elem?
  text-elem-char
  text-elem-word-start?
  text-elem-line-end?
  text-elem-para-start?

  ;; Utilities
  ascii-whitespace?
  word-start?
  line-end?
  para-start?
  in-blank-region?

  ;; Creation
  make-text-elem
  text-elem->measure)
