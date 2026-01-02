#lang racket/base

(require "../pvector.rkt")
(require "../pvector/legacy.rkt")
(require rackunit)

;; ========================================
;; Benchmark: digit-add-list vs zero-allocation digit API
;; ========================================
;;
;; This benchmark compares:
;; - pvector-ref/list (legacy): uses digit-add-list to convert digit to list
;; - pvector-ref (default): uses digit-find-by-measure with zero allocation
;;
;; - pvector-set/list (legacy): uses digit-add-list + list->digit
;; - pvector-set (default): uses digit-update-by-measure with zero allocation

(define (measure-time thunk iterations)
  (collect-garbage)
  (collect-garbage)
  (define start (current-inexact-milliseconds))
  (for ([_ (in-range iterations)])
    (thunk))
  (define end (current-inexact-milliseconds))
  (- end start))

(define (format-result name time iterations)
  (define per-iter (/ time iterations))
  (printf "  ~a: ~a ms (total: ~a ms, ~a iterations)\n"
    name (real->decimal-string per-iter 3) (real->decimal-string time 1) iterations))

(define (run-ref-benchmark pv size iterations label)
  (printf "\n=== pvector-ref Benchmark (~a, size: ~a, iterations: ~a) ===\n" label size iterations)

  ;; Generate random indices to access
  (define indices (for/list ([_ (in-range iterations)])
    (random size)))

  ;; Legacy: uses digit-add-list
  (define time-legacy
    (measure-time
      (lambda ()
        (for ([idx indices])
          (pvector-ref/list pv idx)))
      1))
  (format-result "pvector-ref/list (legacy)" time-legacy 1)

  ;; Default: uses digit-find-by-measure (zero allocation)
  (define time-default
    (measure-time
      (lambda ()
        (for ([idx indices])
          (pvector-ref pv idx)))
      1))
  (format-result "pvector-ref (default)" time-default 1)

  (printf "  Speedup: ~ax\n" (real->decimal-string (/ time-legacy time-default) 2)))

(define (run-set-benchmark pv size iterations label)
  (printf "\n=== pvector-set Benchmark (~a, size: ~a, iterations: ~a) ===\n" label size iterations)

  ;; Generate random indices and values
  (define indices (for/list ([_ (in-range iterations)])
    (random size)))

  ;; Legacy: uses digit-add-list + list->digit
  (define time-legacy
    (measure-time
      (lambda ()
        (for/fold ([p pv]) ([idx indices])
          (pvector-set/list p idx 'new-value)))
      1))
  (format-result "pvector-set/list (legacy)" time-legacy 1)

  ;; Default: uses digit-update-by-measure (zero allocation)
  (define time-default
    (measure-time
      (lambda ()
        (for/fold ([p pv]) ([idx indices])
          (pvector-set p idx 'new-value)))
      1))
  (format-result "pvector-set (default)" time-default 1)

  (printf "  Speedup: ~ax\n" (real->decimal-string (/ time-legacy time-default) 2)))

(define (run-mixed-benchmark pv size iterations label)
  (printf "\n=== Mixed ref+set Benchmark (~a, size: ~a, iterations: ~a) ===\n" label size iterations)

  (define indices (for/list ([_ (in-range iterations)])
    (random size)))

  ;; Legacy
  (define time-legacy
    (measure-time
      (lambda ()
        (for/fold ([p pv]) ([idx indices])
          (define v (pvector-ref/list p idx))
          (pvector-set/list p idx (add1 v))))
      1))
  (format-result "ref+set/list (legacy)" time-legacy 1)

  ;; Default
  (define time-default
    (measure-time
      (lambda ()
        (for/fold ([p pv]) ([idx indices])
          (define v (pvector-ref p idx))
          (pvector-set p idx (add1 v))))
      1))
  (format-result "ref+set (default)" time-default 1)

  (printf "  Speedup: ~ax\n" (real->decimal-string (/ time-legacy time-default) 2)))

;; ========================================
;; Correctness tests first
;; ========================================

(displayln "Verifying correctness: legacy vs default implementations...")

(define test-pv (list->pvector (for/list ([i 1000]) i)))

;; Test ref correctness
(for ([i (in-range 100)])
  (define idx (random 1000))
  (check-equal? (pvector-ref test-pv idx) (pvector-ref/list test-pv idx)
    (format "ref mismatch at index ~a" idx)))

;; Test set correctness
(for ([i (in-range 100)])
  (define idx (random 1000))
  (define new-val (random 10000))
  (define pv1 (pvector-set/list test-pv idx new-val))
  (define pv2 (pvector-set test-pv idx new-val))
  (check-equal? (pvector-ref pv1 idx) new-val)
  (check-equal? (pvector-ref pv2 idx) new-val)
  ;; Check other elements unchanged
  (define other-idx (modulo (+ idx 1) 1000))
  (check-equal? (pvector-ref pv1 other-idx) (pvector-ref pv2 other-idx)))

(displayln "Correctness verified!\n")

;; ========================================
;; Warmup
;; ========================================

(displayln "Warming up JIT...")
(define warmup-pv (list->pvector (for/list ([i 100]) i)))
(for ([_ (in-range 1000)])
  (pvector-ref warmup-pv (random 100))
  (pvector-ref/list warmup-pv (random 100))
  (pvector-set warmup-pv (random 100) 'x)
  (pvector-set/list warmup-pv (random 100) 'x))

;; ========================================
;; Run benchmarks
;; ========================================

(displayln "\n========================================")
(displayln "         BENCHMARK RESULTS")
(displayln "========================================")

;; Small size: 100 elements
(let ([pv (list->pvector (for/list ([i 100]) i))])
  (run-ref-benchmark pv 100 10000 "small")
  (run-set-benchmark pv 100 1000 "small")
  (run-mixed-benchmark pv 100 1000 "small"))

;; Medium size: 1000 elements
(let ([pv (list->pvector (for/list ([i 1000]) i))])
  (run-ref-benchmark pv 1000 10000 "medium")
  (run-set-benchmark pv 1000 1000 "medium")
  (run-mixed-benchmark pv 1000 1000 "medium"))

;; Large size: 10000 elements
(let ([pv (list->pvector (for/list ([i 10000]) i))])
  (run-ref-benchmark pv 10000 10000 "large")
  (run-set-benchmark pv 10000 1000 "large")
  (run-mixed-benchmark pv 10000 1000 "large"))

;; Very large size: 100000 elements
(let ([pv (list->pvector (for/list ([i 100000]) i))])
  (run-ref-benchmark pv 100000 5000 "very large")
  (run-set-benchmark pv 100000 500 "very large")
  (run-mixed-benchmark pv 100000 500 "very large"))

(displayln "\n========================================")
(displayln "         BENCHMARK COMPLETE")
(displayln "========================================")

(displayln "\nConclusion:")
(displayln "- digit-add-list: creates intermediate list, causes allocation")
(displayln "- digit-find/update-by-measure: direct pattern matching, zero allocation")
(displayln "- Expected improvement varies with tree depth (deeper = more benefit)")
