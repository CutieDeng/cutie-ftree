#lang racket/base

(require racket/contract)
(require "../priority-queue.rkt")
(require "../comparator.rkt")

;; ========================================
;; Contract Definitions
;; ========================================

(define priority-queue/c
  (flat-named-contract 'priority-queue priority-queue?))

;; ========================================
;; Contract-Protected Exports
;; ========================================

(provide/contract
  ;; Type predicate
  [priority-queue? (-> any/c boolean?)]
  [priority-queue-empty? (-> priority-queue/c boolean?)]

  ;; Construction
  [priority-queue-empty (-> (comparator/c any/c) priority-queue/c)]
  [list->priority-queue (-> (comparator/c any/c) (listof pair?) priority-queue/c)]

  ;; Size
  [priority-queue-count (-> priority-queue/c exact-nonnegative-integer?)]

  ;; Insert
  [priority-queue-insert (-> priority-queue/c any/c any/c priority-queue/c)]

  ;; Peek (non-destructive)
  [priority-queue-peek (-> priority-queue/c (or/c #f pair?))]
  [priority-queue-peek-value (-> priority-queue/c any/c)]
  [priority-queue-peek-priority (-> priority-queue/c any/c)]

  ;; Pop (extract minimum)
  [priority-queue-pop (-> priority-queue/c (values priority-queue/c (or/c #f pair?)))]
  [priority-queue-pop-value (-> priority-queue/c (values priority-queue/c any/c))]

  ;; Conversion
  [priority-queue->list (-> priority-queue/c (listof pair?))])
