#lang racket/base

(require racket/file
         racket/list
         racket/set
         "types.rkt"
         "text.rkt"
         "ast.rkt"
         "tokens.rkt"
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
  (define (pred ctx cfg)
    (case kind
      [(max-run-threshold)
       (define run (line-context-run-length ctx))
       (define max-run (checker-config-max-run cfg))
       (>= run max-run)]
      [else
       (error 'check-racket-paren-style
              "unknown rule kind in rules-config: ~a"
              kind)]
      ))
  (rule
   id
   description
   pred))

(define built-in-rules
  (map spec->rule built-in-rule-specs))

(define (active-rules cfg)
  (define enabled (checker-config-enabled-rules cfg))
  (define disabled (checker-config-disabled-rules cfg))
  (for/list ([r (in-list built-in-rules)]
             #:when (and (or (null? enabled)
                             (member (rule-id r) enabled))
                         (not (member (rule-id r) disabled))
                         ))
    r))

(define (line->context path line line-number line-kinds token-runs)
  (define code-prefix (comment-prefix line))
  (define zero-run-rec
    (line-run-record 0 #f #f #f))
  (define run-rec
    (hash-ref token-runs line-number zero-run-rec))
  (define run-length
    (line-run-record-run run-rec))
  (define run-start-column
    (line-run-record-start-column run-rec))
  (define run-end-column
    (line-run-record-end-column run-rec))
  (define run-at-line-end?
    (line-run-record-at-line-end? run-rec))
  (define semantic-kind (semantic-kind-for-line line-kinds line-number))
  (define semantic-tags0 (semantic-tags-for-line line-kinds line-number))
  (define semantic-tags
    (if run-at-line-end?
        (set-add semantic-tags0 'run-at-line-end)
        semantic-tags0))
  (line-context path
                line-number
                line
                code-prefix
                run-length
                run-start-column
                run-end-column
                run-at-line-end?
                semantic-kind
                semantic-tags))

(define (line-violations ctx cfg rules)
  (for/list ([r (in-list rules)]
             #:when ((rule-predicate r) ctx cfg)
             #:unless (exempt? ctx cfg))
    (define rule-id^ (rule-id r))
    (define v
      (violation (line-context-path ctx)
                 (line-context-line-number ctx)
                 (line-context-run-length ctx)
                 (line-context-raw-line ctx)
                 rule-id^))
    v)
  )

(define (scan-file path cfg)
  (define rules (active-rules cfg))
  (define lines (file->lines path))
  (define token-runs
    (build-token-line-runs path lines))
  (define line-kinds (build-ast-line-kinds path))
  (define line-num-seq (in-naturals 1))
  (define violations-by-line
    (for/list ([line (in-list lines)]
               [line-number line-num-seq])
      (define ctx
        (line->context path line line-number line-kinds token-runs))
      (line-violations ctx cfg rules)
      ))
  (append* violations-by-line))

(define (scan-files paths cfg)
  (define chunks
    (for/list ([p (in-list paths)])
      (scan-file p cfg)
      ))
  (append* chunks))

(define (violation->key v)
  (define v-rule-id (violation-rule-id v))
  (format "~a\t~a\t~a\t~a"
          (path->string (violation-path v))
          (violation-line-number v)
          (violation-run-length v)
          v-rule-id))
