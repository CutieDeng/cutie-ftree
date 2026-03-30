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
  (printf "config.fail-path-rx-count=~a\n" (length (checker-config-fail-path-rx-list cfg)))
  (printf "config.input-paths=~a\n" (string-join (checker-config-input-paths cfg) ", ")))

(define (print-rules rules)
  (printf "rules.count=~a\n" (length rules))
  (for ([r (in-list rules)])
    (printf "~a: ~a\n"
            (rule-id r)
            (rule-description r))))

(define (print-exemptions exemptions)
  (printf "exemptions.count=~a\n" (length exemptions))
  (for ([ex (in-list exemptions)])
    (printf "~a: ~a\n"
            (exemption-id ex)
            (exemption-description ex))))

(define (print-violation v)
  (printf "~a:~a: run=~a rule=~a ~a\n"
          (path->string (violation-path v))
          (violation-line-number v)
          (violation-run-length v)
          (violation-rule-id v)
          (string-trim (violation-line-text v))))

(define (print-report files violations cfg)
  (printf "Checked ~a files, found ~a style warnings.\n"
          (length files)
          (length violations))
  (cond
    [(checker-config-summary-only? cfg)
     (for ([entry (in-list (take-limit (group-by-file violations)
                                       (checker-config-limit cfg)))])
       (define path (car entry))
       (define count (cdr entry))
       (printf "~a: ~a warnings\n" path count))]
    [else
     (for ([v (in-list (take-limit violations (checker-config-limit cfg)))])
       (print-violation v))]))
