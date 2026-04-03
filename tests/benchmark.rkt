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

(define (sum-pvector-gen pv)
  (define seq (in-pvector pv))
  (for/fold ([sum 0]) ([v seq])
    (+ sum v)
    ))

(define (sum-pvector-index pv)
  (define seq (in-pvector/index pv))
  (for/fold ([sum 0]) ([v seq])
    (+ sum v)
    ))

(define (sum-pvector-rev pv)
  (define seq (in-pvector-reverse pv))
  (for/fold ([sum 0]) ([v seq])
    (+ sum v)
    ))

(define (benchmark-pvector size iterations)
  (printf "\n=== PVector Benchmark (size: ~a, iterations: ~a) ===\n" size iterations)

  ;; Create test pvector
  (define vec (build-vector size values))
  (define pv (vector->pvector vec))

  ;; Benchmark: sum all elements using generator
  (time-it "in-pvector (generator)"
    (lambda ()
      (sum-pvector-gen pv))
    iterations)

  ;; Benchmark: sum all elements using index-based
  (time-it "in-pvector/index (index-based)"
    (lambda ()
      (sum-pvector-index pv))
    iterations)

  ;; Benchmark: reverse traversal
  (time-it "in-pvector-reverse (generator)"
    (lambda ()
      (sum-pvector-rev pv))
    iterations)

  ;; Verify correctness
  (define sum-gen (sum-pvector-gen pv))
  (define sum-idx (sum-pvector-index pv))
  (define sum-rev (sum-pvector-rev pv))
  (define expected (/ (* (sub1 size) size) 2))
  (define bad-msg "Correctness check failed!")
  (define (fail!)
    (error 'benchmark bad-msg))
  (define ok-gen? (= sum-gen expected))
  (define ok-idx? (= sum-idx expected))
  (define ok-rev? (= sum-rev expected))
  (define all-ok?
    (and ok-gen? ok-idx? ok-rev?))
  (define bad?
    (not all-ok?))
  (when bad?
    (fail!))
  )

;; ========================================
;; Ordered-Map Benchmark
;; ========================================

(define (sum-ordered-map-gen om)
  (define seq (in-ordered-map om))
  (for/fold ([sum 0]) ([kv seq])
    (+ sum (car kv))
    ))

(define (sum-ordered-map-lazy om)
  (define seq (in-ordered-map/lazy om))
  (for/fold ([sum 0]) ([kv seq])
    (+ sum (car kv))
    ))

(define (sum-ordered-map-rev om)
  (define seq (in-ordered-map-reverse om))
  (for/fold ([sum 0]) ([kv seq])
    (+ sum (car kv))
    ))

(define (benchmark-ordered-map size iterations)
  (printf "\n=== Ordered-Map Benchmark (size: ~a, iterations: ~a) ===\n" size iterations)

  ;; Create test ordered-map
  (define i-seq (in-range size))
  (define m0 (ordered-map-empty integer-compare))
  (define om
    (for/fold ([m m0]) ([i i-seq])
      (ordered-map-insert m i i #t)
      ))

  ;; Benchmark: sum all keys using generator
  (time-it "in-ordered-map (generator)"
    (lambda ()
      (sum-ordered-map-gen om))
    iterations)

  ;; Benchmark: sum all keys using lazy query-based
  (time-it "in-ordered-map/lazy (query-based)"
    (lambda ()
      (sum-ordered-map-lazy om))
    iterations)

  ;; Benchmark: reverse traversal
  (time-it "in-ordered-map-reverse (generator)"
    (lambda ()
      (sum-ordered-map-rev om))
    iterations)

  ;; Verify correctness
  (define sum-gen (sum-ordered-map-gen om))
  (define sum-lazy (sum-ordered-map-lazy om))
  (define sum-rev (sum-ordered-map-rev om))
  (define expected (/ (* (sub1 size) size) 2))
  (define bad-msg "Correctness check failed!")
  (define (fail!)
    (error 'benchmark bad-msg))
  (define ok-gen? (= sum-gen expected))
  (define ok-lazy? (= sum-lazy expected))
  (define ok-rev? (= sum-rev expected))
  (define all-ok?
    (and ok-gen? ok-lazy? ok-rev?))
  (define bad?
    (not all-ok?))
  (when bad?
    (fail!))
  )

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
