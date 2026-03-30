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
  (remove-duplicates
   (append-map collect-files
               (map string->path (checker-config-input-paths cfg)))))

(define (run-checker cfg)
  (define files (expand-input-paths cfg))
  (define raw-violations (scan-files files cfg))
  (define rules (active-rules cfg))

  (when (checker-config-write-baseline-path cfg)
    (write-baseline! (checker-config-write-baseline-path cfg) raw-violations))

  (define filtered-violations
    (if (checker-config-baseline-path cfg)
        (apply-baseline raw-violations
                        (read-baseline (checker-config-baseline-path cfg)))
        raw-violations))

  (when (checker-config-show-config? cfg)
    (print-config cfg))

  (when (checker-config-list-exemptions? cfg)
    (print-exemptions built-in-exemptions))

  (when (checker-config-list-rules? cfg)
    (print-rules rules))

  (print-report files filtered-violations cfg)

  (define fail-violations
    (let ([rxs (checker-config-fail-path-rx-list cfg)])
      (if (null? rxs)
          filtered-violations
          (for/list ([v (in-list filtered-violations)]
                     #:when (for/or ([rx (in-list rxs)])
                              (regexp-match? rx (path->string (violation-path v)))))
            v))))

  (and (checker-config-fail-on-violation? cfg)
       (pair? fail-violations)))
