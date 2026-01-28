#lang racket/base

;; text/safe: Contract-wrapped text buffer API

(require racket/contract)
(require "../text.rkt")

;; ========================================
;; Contract Definitions
;; ========================================

(define text-buffer/c text-buffer?)
(define char-index/c exact-nonnegative-integer?)
(define word-index/c exact-nonnegative-integer?)
(define line-index/c exact-nonnegative-integer?)
(define para-index/c exact-nonnegative-integer?)

;; ========================================
;; Provide with Contracts
;; ========================================

(provide
  ;; Construction
  (contract-out
    [text-empty (-> text-buffer/c)]
    [text-empty? (-> text-buffer/c boolean?)]
    [string->text (-> string? text-buffer/c)]
    [text->string (-> text-buffer/c string?)])

  ;; Measures
  (contract-out
    [text-length (-> text-buffer/c exact-nonnegative-integer?)]
    [text-word-count (-> text-buffer/c exact-nonnegative-integer?)]
    [text-line-count (-> text-buffer/c exact-nonnegative-integer?)]
    [text-para-count (-> text-buffer/c exact-nonnegative-integer?)])

  ;; Character navigation
  (contract-out
    [text-ref (-> text-buffer/c char-index/c char?)]
    [text-set (-> text-buffer/c char-index/c char? text-buffer/c)])

  ;; Word navigation
  (contract-out
    [text-word-at (-> text-buffer/c word-index/c
                      (values exact-nonnegative-integer?
                              exact-nonnegative-integer?
                              string?))]
    [text-char-to-word (-> text-buffer/c char-index/c exact-nonnegative-integer?)])

  ;; Line navigation
  (contract-out
    [text-line-at (-> text-buffer/c line-index/c
                      (values exact-nonnegative-integer?
                              exact-nonnegative-integer?
                              string?))]
    [text-char-to-line (-> text-buffer/c char-index/c exact-nonnegative-integer?)])

  ;; Paragraph navigation
  (contract-out
    [text-para-at (-> text-buffer/c para-index/c
                      (values exact-nonnegative-integer?
                              exact-nonnegative-integer?
                              string?))]
    [text-char-to-para (-> text-buffer/c char-index/c exact-nonnegative-integer?)])

  ;; Modification
  (contract-out
    [text-insert (-> text-buffer/c char-index/c char? text-buffer/c)]
    [text-insert-string (-> text-buffer/c char-index/c string? text-buffer/c)]
    [text-delete (-> text-buffer/c char-index/c text-buffer/c)]
    [text-delete-range (-> text-buffer/c char-index/c char-index/c text-buffer/c)])

  ;; Split/append
  (contract-out
    [text-split-at (-> text-buffer/c char-index/c
                       (values text-buffer/c text-buffer/c))]
    [text-append (-> text-buffer/c text-buffer/c text-buffer/c)])

  ;; Iteration (sequences don't have simple contracts)
  in-text-chars
  in-text-words
  in-text-lines)
