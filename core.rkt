#lang racket/base

(require racket/contract)

; Digit
(struct One (a) #:transparent)
(struct Two (a b) #:transparent)
(struct Three (a b c) #:transparent)
(struct Four (a b c d) #:transparent)

; Node
(struct Node2 (v a b) #:transparent)
(struct Node3 (v a b c) #:transparent)

(define Digit?/c (or/c One? Two? Three? Four?))

(define Node?/c (or/c Node2? Node3?))

; Finger Tree
(struct Empty ()
  #:transparent
)
(struct Single (a)
  #:transparent
)
(struct Deep (v left inner right)
  #:transparent
; #:guard (struct-guard/c any/c Digit?/c any/c Digit?/c)
)

(define FingerTree? (or/c Empty? Single? Deep?))

(struct FingerTreeWrap (empty-value measure assoc))

(provide FingerTreeWrap Empty Single Deep Node2 Node3 One Two Three Four Digit?/c Node?/c FingerTree?)
