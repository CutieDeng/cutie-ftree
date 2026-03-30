#lang racket/base

(require racket/list
         racket/path)

(provide collect-files)

(define (path-hidden? p)
  (define s (path->string p))
  (regexp-match? #rx"(^|/)[.][^/]+" s))

(define (ignored-directory? p)
  (define s (path->string p))
  (or (regexp-match? #rx"(^|/)compiled(/|$)" s)
      (regexp-match? #rx"(^|/).git(/|$)" s)))

(define (rkt-file? p)
  (regexp-match? #rx"[.]rkt$" (path->string p)))

(define (collect-files root)
  (cond
    [(file-exists? root)
     (if (rkt-file? root) (list root) '())]
    [(directory-exists? root)
     (for*/list ([p (in-directory root)]
                 #:when (and (file-exists? p)
                             (rkt-file? p)
                             (not (path-hidden? p))
                             (not (ignored-directory? p))))
       p)]
    [else
     '()]))
