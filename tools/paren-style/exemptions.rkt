#lang racket/base

(require racket/set
         "types.rkt"
         "exemptions-config.rkt")

(provide
 built-in-exemptions
 exempt?
 exemption->summary)

;; The exemption set is intentionally narrow. Each rule targets a single
;; low-ambiguity pattern and only at run-length 3.

(define (spec->exemption spec)
  (define id (list-ref spec 0))
  (define description (list-ref spec 1))
  (define exact-run (list-ref spec 2))
  (define line-rx (list-ref spec 3))
  (define path-rx (if (>= (length spec) 5) (list-ref spec 4) #f))
  (define semantic-kind (if (>= (length spec) 6) (list-ref spec 5) #f))
  (define ast-tag (if (>= (length spec) 7) (list-ref spec 6) #f))
  (exemption
   id
   description
   (lambda (ctx cfg)
     (and (= (line-context-run-length ctx) exact-run)
          (or (not semantic-kind)
              (eq? semantic-kind (line-context-semantic-kind ctx)))
          (or (not ast-tag)
              (set-member? (line-context-semantic-tags ctx) ast-tag))
          (regexp-match? line-rx (line-context-code-prefix ctx))
          (or (not path-rx)
              (regexp-match? path-rx (path->string (line-context-path ctx))))))))

(define built-in-exemptions
  (map spec->exemption built-in-exemption-specs))

(define (exempt? ctx cfg)
  (for/first ([ex (in-list built-in-exemptions)]
              #:when ((exemption-predicate ex) ctx cfg))
    ex))

(define (exemption->summary ex)
  (format "~a: ~a"
          (exemption-id ex)
          (exemption-description ex)))
