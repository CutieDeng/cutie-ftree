#lang racket/base

(require racket/hash
         racket/list
         racket/string
         "types.rkt")

(provide
 print-config
 print-rules
 print-exemptions
 print-report
 group-by-file
 take-limit)

(define (take-limit xs limit)
  (if limit
      (take xs (min (length xs) limit))
      xs))

(define (group-by-file violations)
  (define counts (make-hash))
  (for ([v (in-list violations)])
    (hash-update! counts (path->string (violation-path v)) add1 0))
  (sort (hash->list counts) > #:key cdr))

(define (print-config cfg)
  (printf "config.max-run=~a\n" (checker-config-max-run cfg))
  (printf "config.fail-on-violation?=~a\n" (checker-config-fail-on-violation? cfg))
  (printf "config.summary-only?=~a\n" (checker-config-summary-only? cfg))
  (printf "config.limit=~a\n" (checker-config-limit cfg))
  (printf "config.baseline-path=~a\n" (or (checker-config-baseline-path cfg) "<none>"))
  (printf "config.write-baseline-path=~a\n" (or (checker-config-write-baseline-path cfg) "<none>"))
  (printf "config.list-rules?=~a\n" (checker-config-list-rules? cfg))
  (printf "config.list-exemptions?=~a\n" (checker-config-list-exemptions? cfg))
  (printf "config.enabled-rules=~a\n" (checker-config-enabled-rules cfg))
  (printf "config.disabled-rules=~a\n" (checker-config-disabled-rules cfg))
  (define fail-path-rx-list
    (checker-config-fail-path-rx-list cfg))
  (printf "config.fail-path-rx-count=~a\n" (length fail-path-rx-list))
  (define input-paths
    (checker-config-input-paths cfg))
  (define input-paths-str
    (string-join input-paths ", "))
  (printf "config.input-paths=~a\n" input-paths-str))

(define (print-rules rules)
  (printf "rules.count=~a\n" (length rules))
  (for ([r (in-list rules)])
    (define rid (rule-id r))
    (define desc (rule-description r))
    (printf "~a: ~a\n"
            rid
            desc)
    ) ; for: rules
  ) ; define print-rules

(define (print-exemptions exemptions)
  (printf "exemptions.count=~a\n" (length exemptions))
  (for ([ex (in-list exemptions)])
    (define ex-id (exemption-id ex))
    (define ex-desc (exemption-description ex))
    (printf "~a: ~a\n"
            ex-id
            ex-desc)
    ) ; for: exemptions
  ) ; define print-exemptions

(define (print-violation v)
  (define raw-line-text
    (violation-line-text v))
  (define v-text
    (string-trim raw-line-text))
  (printf "~a:~a: run=~a rule=~a ~a\n"
          (path->string (violation-path v))
          (violation-line-number v)
          (violation-run-length v)
          (violation-rule-id v)
          v-text)
  ) ; define print-violation

(define (print-report files violations cfg)
  (printf "Checked ~a files, found ~a style warnings.\n"
          (length files)
          (length violations))
  (define limit
    (checker-config-limit cfg))
  (cond
    [(checker-config-summary-only? cfg)
     (define grouped (group-by-file violations))
     (define limited-grouped
       (take-limit grouped limit))
     (for ([entry (in-list limited-grouped)])
       (define path (car entry))
       (define count (cdr entry))
       (printf "~a: ~a warnings\n" path count)
       )
     ] ; cond branch: summary-only
    [else
     (define limited-violations
       (take-limit violations limit))
     (for ([v (in-list limited-violations)])
       (print-violation v)
       )
     ] ; cond branch: full report
    ) ; cond
  ) ; define print-report
