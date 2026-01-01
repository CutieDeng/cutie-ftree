#lang racket/base

(require racket/contract)

;; ========================================
;; Digit Types (1-4 elements)
;; ========================================

(struct digit:1 (a) #:transparent)
(struct digit:2 (a b) #:transparent)
(struct digit:3 (a b c) #:transparent)
(struct digit:4 (a b c d) #:transparent)

(define digit?/c (or/c digit:1? digit:2? digit:3? digit:4?))

;; ========================================
;; Node Types (2-3 children)
;; v is the cached measure value
;; ========================================

(struct node:2 (v a b) #:transparent)
(struct node:3 (v a b c) #:transparent)

(define node?/c (or/c node:2? node:3?))

;; ========================================
;; Finger Tree Types
;; ========================================

(struct ft:empty () #:transparent)

(struct ft:single (a) #:transparent)

(struct ft:deep (v left inner right) #:transparent)

(define finger-tree?/c (or/c ft:empty? ft:single? ft:deep?))

;; ========================================
;; Finger Tree Configuration
;; empty-value: () -> V
;; measure: A -> V
;; assoc: V V -> V
;; ========================================

(struct ft:config (empty-value measure assoc) #:transparent)

;; ========================================
;; Exports
;; ========================================

(provide
  ;; Digit
  digit:1 digit:1? digit:1-a
  digit:2 digit:2? digit:2-a digit:2-b
  digit:3 digit:3? digit:3-a digit:3-b digit:3-c
  digit:4 digit:4? digit:4-a digit:4-b digit:4-c digit:4-d
  digit?/c

  ;; Node
  node:2 node:2? node:2-v node:2-a node:2-b
  node:3 node:3? node:3-v node:3-a node:3-b node:3-c
  node?/c

  ;; Finger Tree
  ft:empty ft:empty?
  ft:single ft:single? ft:single-a
  ft:deep ft:deep? ft:deep-v ft:deep-left ft:deep-inner ft:deep-right
  finger-tree?/c

  ;; Config
  ft:config ft:config? ft:config-empty-value ft:config-measure ft:config-assoc)
