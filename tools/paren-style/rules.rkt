#lang racket/base

(require racket/file
         racket/list
         "types.rkt"
         "text.rkt"
         "ast.rkt"
         "rules-config.rkt"
         "exemptions.rkt")

(provide
 built-in-rules
 active-rules
 scan-file
 scan-files
 violation->key)

(define (spec->rule spec)
  (define id (list-ref spec 0))
  (define description (list-ref spec 1))
  (define kind (list-ref spec 2))
  (rule
   id
   description
   (case kind
     [(max-run-threshold)
      (lambda (ctx cfg)
        (>= (line-context-run-length ctx)
            (checker-config-max-run cfg)))]
     [else
      (error 'check-racket-paren-style
             "unknown rule kind in rules-config: ~a"
             kind)])))

(define built-in-rules
  (map spec->rule built-in-rule-specs))

(define (active-rules cfg)
  (define enabled (checker-config-enabled-rules cfg))
  (define disabled (checker-config-disabled-rules cfg))
  (for/list ([r (in-list built-in-rules)]
             #:when (and (or (null? enabled)
                             (member (rule-id r) enabled))
                         (not (member (rule-id r) disabled))))
    r))

(define (line->context path line line-number line-kinds)
  (define code-prefix (comment-prefix line))
  (define run-length (max-closing-run code-prefix))
  (define semantic-kind (semantic-kind-for-line line-kinds line-number))
  (define semantic-tags (semantic-tags-for-line line-kinds line-number))
  (line-context path line-number line code-prefix run-length semantic-kind semantic-tags))

(define (line-violations ctx cfg rules)
  (for/list ([r (in-list rules)]
             #:when ((rule-predicate r) ctx cfg)
             #:unless (exempt? ctx cfg))
    (violation (line-context-path ctx)
               (line-context-line-number ctx)
               (line-context-run-length ctx)
               (line-context-raw-line ctx)
               (rule-id r))))

(define (scan-file path cfg)
  (define rules (active-rules cfg))
  (define lines (file->lines path))
  (define line-kinds (build-ast-line-kinds path))
  (append*
   (for/list ([line (in-list lines)]
              [line-number (in-naturals 1)])
     (line-violations (line->context path line line-number line-kinds) cfg rules))))

(define (scan-files paths cfg)
  (append* (for/list ([p (in-list paths)])
             (scan-file p cfg))))

(define (violation->key v)
  (format "~a\t~a\t~a\t~a"
          (path->string (violation-path v))
          (violation-line-number v)
          (violation-run-length v)
          (violation-rule-id v)))
