#lang racket/base

;; text-measure: composite monoid for text buffer
;; Tracks: character count, word count, line count, paragraph count

(require racket/match)
(require "../private/core.rkt")

;; ========================================
;; Measure Structure
;; ========================================

(struct text-measure (chars words lines paras) #:transparent)

;; ========================================
;; Monoid Operations
;; ========================================

;; Identity element
(define (text-measure-empty)
  (text-measure 0 0 0 0))

;; Combine two measures
(define (text-measure-append m0 m1)
  (text-measure
    (+ (text-measure-chars m0) (text-measure-chars m1))
    (+ (text-measure-words m0) (text-measure-words m1))
    (+ (text-measure-lines m0) (text-measure-lines m1))
    (+ (text-measure-paras m0) (text-measure-paras m1))))

;; ========================================
;; Exports
;; ========================================

(provide
  ;; Structure
  text-measure
  text-measure?
  text-measure-chars
  text-measure-words
  text-measure-lines
  text-measure-paras

  ;; Monoid operations
  text-measure-empty
  text-measure-append)
