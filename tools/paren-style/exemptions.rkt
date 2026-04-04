#lang racket/base

(require racket/set
         racket/string
         "types.rkt"
         "exemptions-config.rkt")

(provide
 built-in-exemptions
 exempt?
 exemption->summary)

;; The exemption set is intentionally narrow. Each rule targets a single
;; low-ambiguity pattern and only at run-length 3.

(define (path-has-suffix? path-str suffixes)
  (for/or ([suffix (in-list suffixes)])
    (string-suffix? path-str suffix))
  ) ; define path-has-suffix?

(define (spec->exemption spec)
  (define id (exemption-spec-id spec))
  (define description (exemption-spec-description spec))
  (define exact-run (exemption-spec-exact-run spec))
  (define line-rx (exemption-spec-line-rx spec))
  (define path-rx (exemption-spec-path-rx spec))
  (define semantic-kind (exemption-spec-semantic-kind spec))
  (define ast-tag (exemption-spec-ast-tag spec))
  (define requires-run-at-line-end?
    (exemption-spec-requires-run-at-line-end? spec))
  (define path-suffixes
    (exemption-spec-path-suffixes spec))
  (define (pred ctx cfg)
    (define ctx-kind (line-context-semantic-kind ctx))
    (define ctx-tags (line-context-semantic-tags ctx))
    (define run-at-line-end?
      (line-context-run-at-line-end? ctx))
    (define code-prefix (line-context-code-prefix ctx))
    (define ctx-path (line-context-path ctx))
    (define ctx-path-str (path->string ctx-path))
    (define ok?
      (and (= (line-context-run-length ctx) exact-run)
           (or (not requires-run-at-line-end?)
               run-at-line-end?)
           (or (not semantic-kind)
               (eq? semantic-kind ctx-kind))
           (or (not ast-tag)
               (set-member? ctx-tags ast-tag))
           (or (not line-rx)
               (regexp-match? line-rx code-prefix))
           (or (not path-rx)
               (regexp-match? path-rx ctx-path-str))
           (or (not path-suffixes)
               (path-has-suffix? ctx-path-str path-suffixes))
           ))
    ok?)
  (exemption id description pred)
  ) ; define spec->exemption

(define built-in-exemptions
  (map spec->exemption built-in-exemption-specs))

(define (exempt? ctx cfg)
  (for/first ([ex (in-list built-in-exemptions)]
              #:when ((exemption-predicate ex) ctx cfg))
    ex))

(define (exemption->summary ex)
  (define id (exemption-id ex))
  (define description (exemption-description ex))
  (format "~a: ~a"
          id
          description))
