#lang racket/base

(require racket/list
         racket/path)

(provide collect-files)

(define (path-hidden? p)
  (define s (path->string p))
  (regexp-match? #rx"(^|/)[.][^/]+" s))

(define (ignored-directory? p)
  (define s (path->string p))
  (define in-compiled?
    (regexp-match? #rx"(^|/)compiled(/|$)" s))
  (define in-git?
    (regexp-match? #rx"(^|/).git(/|$)" s))
  (or (regexp-match? #rx"(^|/)compiled(/|$)" s)
      in-git?))

(define (rkt-file? p)
  (define p-str (path->string p))
  (regexp-match? #rx"[.]rkt$" p-str))

(define (collect-files root)
  (cond
    [(file-exists? root)
     (if (rkt-file? root)
         (list root)
         '()
         )]
    [(directory-exists? root)
     (for*/list ([p (in-directory root)]
                 #:when (and (file-exists? p)
                             (rkt-file? p)
                             (not (path-hidden? p))
                             (not (ignored-directory? p))
                             ))
       p)]
    [else
     '()]
    ))
