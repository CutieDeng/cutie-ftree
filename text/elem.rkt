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
  (or (char=? c #\space)
      (char=? c #\tab)
      (char=? c #\newline)
      (char=? c #\return)))

;; ========================================
;; Boundary Detection Functions
;; ========================================

;; Determine if character starts a word:
;; - Non-whitespace character
;; - Previous character is whitespace or start of text (prev-char = #f)
(define (word-start? char prev-char)
  (and (not (ascii-whitespace? char))
       (or (not prev-char)
           (ascii-whitespace? prev-char))))

;; Determine if character ends a line:
;; - Is a newline character
(define (line-end? char)
  (char=? char #\newline))

;; Determine if we're in a blank region:
;; - Only whitespace since last paragraph start
;; prev-blank? indicates if we're currently in a blank region
(define (in-blank-region? char prev-blank?)
  (and prev-blank? (ascii-whitespace? char)))

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
  (text-elem
    char
    (word-start? char prev-char)
    (line-end? char)
    (para-start? char after-blank-line?)))

;; ========================================
;; Measure Function for ft:config
;; ========================================

;; Convert a text-elem to its measure contribution
(define (text-elem->measure elem)
  (match-define (text-elem _ ws? le? ps?) elem)
  (text-measure
    1
    (if ws? 1 0)
    (if le? 1 0)
    (if ps? 1 0)))

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
