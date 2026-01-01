#lang racket/base

(require racket/format)
(require "../pvector.rkt")
(require "../ordered-map.rkt")
(require "../comparator.rkt")

;; ========================================
;; Benchmark utilities
;; ========================================

(define (time-it name thunk iterations)
  (collect-garbage)
  (collect-garbage)
  (define start (current-inexact-milliseconds))
  (for ([_ (in-range iterations)])
    (thunk))
  (define end (current-inexact-milliseconds))
  (define total-ms (- end start))
  (define per-iter-ms (/ total-ms iterations))
  (printf "  ~a: ~a ms (total: ~a ms, ~a iterations)\n"
    name
    (real->decimal-string per-iter-ms 3)
    (real->decimal-string total-ms 1)
    iterations))

(define (real->decimal-string n digits)
  (define factor (expt 10 digits))
  (define rounded (/ (round (* n factor)) factor))
  (~a rounded))

;; ========================================
;; PVector Benchmark
;; ========================================

(define (benchmark-pvector size iterations)
  (printf "\n=== PVector Benchmark (size: ~a, iterations: ~a) ===\n" size iterations)

  ;; Create test pvector
  (define pv (vector->pvector (build-vector size values)))

  ;; Benchmark: sum all elements using generator
  (time-it "in-pvector (generator)"
    (lambda ()
      (for/fold ([sum 0]) ([v (in-pvector pv)])
        (+ sum v)))
    iterations)

  ;; Benchmark: sum all elements using index-based
  (time-it "in-pvector/index (index-based)"
    (lambda ()
      (for/fold ([sum 0]) ([v (in-pvector/index pv)])
        (+ sum v)))
    iterations)

  ;; Benchmark: reverse traversal
  (time-it "in-pvector-reverse (generator)"
    (lambda ()
      (for/fold ([sum 0]) ([v (in-pvector-reverse pv)])
        (+ sum v)))
    iterations)

  ;; Verify correctness
  (define sum-gen (for/fold ([sum 0]) ([v (in-pvector pv)]) (+ sum v)))
  (define sum-idx (for/fold ([sum 0]) ([v (in-pvector/index pv)]) (+ sum v)))
  (define sum-rev (for/fold ([sum 0]) ([v (in-pvector-reverse pv)]) (+ sum v)))
  (define expected (/ (* (sub1 size) size) 2))
  (unless (and (= sum-gen expected) (= sum-idx expected) (= sum-rev expected))
    (error 'benchmark "Correctness check failed!")))

;; ========================================
;; Ordered-Map Benchmark
;; ========================================

(define (benchmark-ordered-map size iterations)
  (printf "\n=== Ordered-Map Benchmark (size: ~a, iterations: ~a) ===\n" size iterations)

  ;; Create test ordered-map
  (define om
    (for/fold ([m (ordered-map-empty integer-compare)]) ([i (in-range size)])
      (ordered-map-insert m i i #t)))

  ;; Benchmark: sum all keys using generator
  (time-it "in-ordered-map (generator)"
    (lambda ()
      (for/fold ([sum 0]) ([kv (in-ordered-map om)])
        (+ sum (car kv))))
    iterations)

  ;; Benchmark: sum all keys using lazy query-based
  (time-it "in-ordered-map/lazy (query-based)"
    (lambda ()
      (for/fold ([sum 0]) ([kv (in-ordered-map/lazy om)])
        (+ sum (car kv))))
    iterations)

  ;; Benchmark: reverse traversal
  (time-it "in-ordered-map-reverse (generator)"
    (lambda ()
      (for/fold ([sum 0]) ([kv (in-ordered-map-reverse om)])
        (+ sum (car kv))))
    iterations)

  ;; Verify correctness
  (define sum-gen (for/fold ([sum 0]) ([kv (in-ordered-map om)]) (+ sum (car kv))))
  (define sum-lazy (for/fold ([sum 0]) ([kv (in-ordered-map/lazy om)]) (+ sum (car kv))))
  (define sum-rev (for/fold ([sum 0]) ([kv (in-ordered-map-reverse om)]) (+ sum (car kv))))
  (define expected (/ (* (sub1 size) size) 2))
  (unless (and (= sum-gen expected) (= sum-lazy expected) (= sum-rev expected))
    (error 'benchmark "Correctness check failed!")))

;; ========================================
;; Run Benchmarks
;; ========================================

(printf "Warming up JIT...\n")
(benchmark-pvector 100 10)
(benchmark-ordered-map 100 10)

(printf "\n========================================\n")
(printf "         BENCHMARK RESULTS\n")
(printf "========================================\n")

;; Small size
(benchmark-pvector 1000 100)
(benchmark-ordered-map 1000 100)

;; Medium size
(benchmark-pvector 10000 20)
(benchmark-ordered-map 10000 20)

;; Large size
(benchmark-pvector 100000 5)
(benchmark-ordered-map 100000 5)

(printf "\n========================================\n")
(printf "         BENCHMARK COMPLETE\n")
(printf "========================================\n")
