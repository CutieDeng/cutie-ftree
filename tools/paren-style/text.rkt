#lang racket/base

(require racket/string)

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
  ;; Count the longest contiguous run of ')' and ']' across the full code line.
  ;; String literals are ignored so syntax payload text does not create noise.
  (for/fold ([best 0]
             [current 0]
             [in-string? #f]
             [escape? #f]
             #:result best)
            ([ch (in-string s)])
    (cond
      [in-string?
       (cond
         [escape? (values best 0 #t #f)]
         [(char=? ch #\\) (values best 0 #t #t)]
         [(char=? ch #\") (values best 0 #f #f)]
         [else (values best 0 #t #f)])]
      [(char=? ch #\") (values best 0 #t #f)]
      [(or (char=? ch #\)) (char=? ch #\]))
       (define next (add1 current))
       (values (max best next) next #f #f)]
      [else
       (values best 0 #f #f)])))
