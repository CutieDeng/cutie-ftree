#lang racket/base

(require racket/list
         racket/path
         "baseline.rkt"
         "discovery.rkt"
         "exemptions.rkt"
         "report.rkt"
         "rules.rkt"
         "types.rkt")

(provide run-checker)

(define (expand-input-paths cfg)
  (define input-paths
    (checker-config-input-paths cfg))
  (define input-path-objects
    (map string->path input-paths))
  (define discovered
    (append-map collect-files input-path-objects))
  (remove-duplicates
   discovered))

(define (run-checker cfg)
  (define files (expand-input-paths cfg))
  (define raw-violations (scan-files files cfg))
  (define rules (active-rules cfg))

  (when (checker-config-write-baseline-path cfg)
    (write-baseline! (checker-config-write-baseline-path cfg) raw-violations))

  (define filtered-violations
    (if (checker-config-baseline-path cfg)
        (let ()
          (define baseline-path
            (checker-config-baseline-path cfg))
          (define baseline
            (read-baseline baseline-path))
          (apply-baseline raw-violations baseline)
          )
        raw-violations))

  (when (checker-config-show-config? cfg)
    (print-config cfg))

  (when (checker-config-list-exemptions? cfg)
    (print-exemptions built-in-exemptions))

  (when (checker-config-list-rules? cfg)
    (print-rules rules))

  (print-report files filtered-violations cfg)

  (define fail-violations
    (let ()
      (define rxs (checker-config-fail-path-rx-list cfg))
      (define (violation-path-matches-rx? v)
        (define v-path (violation-path v))
        (define v-path-str (path->string v-path))
        (for/or ([rx (in-list rxs)])
          (regexp-match? rx v-path-str)
          ))
      (if (null? rxs)
          filtered-violations
          (let ()
            (define matched
              (for/list ([v (in-list filtered-violations)]
                         #:when (violation-path-matches-rx? v)
                         )
                v))
            matched
            )
          ))
    ) ; define fail-violations

  (and (checker-config-fail-on-violation? cfg)
       (pair? fail-violations))
  )
