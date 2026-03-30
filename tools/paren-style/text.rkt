#lang racket/base

(provide
 blank-string?
 comment-prefix
 max-closing-run)

(define (blank-string? s)
  (regexp-match? #px"^\\s*$" s))

(define (comment-prefix line)
  (define m (regexp-match-positions #rx";" line))
  (if m
      (substring line 0 (caar m))
      line))

(define (max-closing-run s)
  (for/fold ([best 0]
             [current 0]
             #:result best)
            ([ch (in-string s)])
    (cond
      [(or (char=? ch #\)) (char=? ch #\]))
       (define next (add1 current))
       (values (max best next) next)]
      [else
       (values best 0)])))
