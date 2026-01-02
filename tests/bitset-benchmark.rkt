#lang racket/base

(require "../bitset.rkt")
(require racket/set)

;; ========================================
;; Bitset Performance Benchmark
;; ========================================
;;
;; Compares bitset operations with Racket's built-in set
;; for dense integer sets.
;; ========================================

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
    name (real->decimal-string per-iter 4) (real->decimal-string time 1) iterations))

;; ========================================
;; Construction Benchmark
;; ========================================

(define (run-construction-benchmark size iterations)
  (printf "\n=== Construction Benchmark (size: ~a, iterations: ~a) ===\n" size iterations)

  (define elements (for/list ([i (in-range size)]) i))

  ;; bitset construction
  (define time-bitset
    (measure-time
      (lambda () (list->bitset elements))
      iterations))
  (format-result "bitset (list->bitset)" time-bitset iterations)

  ;; Racket set construction
  (define time-set
    (measure-time
      (lambda () (list->set elements))
      iterations))
  (format-result "racket set (list->set)" time-set iterations)

  (printf "  Speedup: ~ax\n" (real->decimal-string (/ time-set time-bitset) 2)))

;; ========================================
;; Membership Benchmark
;; ========================================

(define (run-membership-benchmark size queries iterations)
  (printf "\n=== Membership Benchmark (size: ~a, queries: ~a, iterations: ~a) ===\n"
          size queries iterations)

  (define bs (for/bitset ([i (in-range size)]) i))
  (define rs (for/set ([i (in-range size)]) i))
  (define query-indices (for/list ([_ (in-range queries)]) (random (* size 2))))

  ;; bitset membership
  (define time-bitset
    (measure-time
      (lambda ()
        (for ([q query-indices])
          (bitset-member? bs q)))
      iterations))
  (format-result "bitset-member?" time-bitset iterations)

  ;; Racket set membership
  (define time-set
    (measure-time
      (lambda ()
        (for ([q query-indices])
          (set-member? rs q)))
      iterations))
  (format-result "set-member?" time-set iterations)

  (printf "  Speedup: ~ax\n" (real->decimal-string (/ time-set time-bitset) 2)))

;; ========================================
;; Set Operations Benchmark
;; ========================================

(define (run-set-ops-benchmark size iterations)
  (printf "\n=== Set Operations Benchmark (size: ~a, iterations: ~a) ===\n" size iterations)

  ;; Create two overlapping sets
  (define bs1 (for/bitset ([i (in-range 0 size)]) i))
  (define bs2 (for/bitset ([i (in-range (quotient size 2) (+ size (quotient size 2)))]) i))
  (define rs1 (for/set ([i (in-range 0 size)]) i))
  (define rs2 (for/set ([i (in-range (quotient size 2) (+ size (quotient size 2)))]) i))

  ;; Union
  (define time-bitset-union
    (measure-time (lambda () (bitset-union bs1 bs2)) iterations))
  (format-result "bitset-union" time-bitset-union iterations)

  (define time-set-union
    (measure-time (lambda () (set-union rs1 rs2)) iterations))
  (format-result "set-union" time-set-union iterations)
  (printf "  Union speedup: ~ax\n" (real->decimal-string (/ time-set-union time-bitset-union) 2))

  ;; Intersection
  (define time-bitset-intersect
    (measure-time (lambda () (bitset-intersection bs1 bs2)) iterations))
  (format-result "bitset-intersection" time-bitset-intersect iterations)

  (define time-set-intersect
    (measure-time (lambda () (set-intersect rs1 rs2)) iterations))
  (format-result "set-intersect" time-set-intersect iterations)
  (printf "  Intersection speedup: ~ax\n" (real->decimal-string (/ time-set-intersect time-bitset-intersect) 2))

  ;; Subtract
  (define time-bitset-subtract
    (measure-time (lambda () (bitset-subtract bs1 bs2)) iterations))
  (format-result "bitset-subtract" time-bitset-subtract iterations)

  (define time-set-subtract
    (measure-time (lambda () (set-subtract rs1 rs2)) iterations))
  (format-result "set-subtract" time-set-subtract iterations)
  (printf "  Subtract speedup: ~ax\n" (real->decimal-string (/ time-set-subtract time-bitset-subtract) 2)))

;; ========================================
;; Iteration Benchmark
;; ========================================

(define (run-iteration-benchmark size iterations)
  (printf "\n=== Iteration Benchmark (size: ~a, iterations: ~a) ===\n" size iterations)

  (define bs (for/bitset ([i (in-range size)]) i))
  (define rs (for/set ([i (in-range size)]) i))

  ;; bitset iteration
  (define time-bitset
    (measure-time
      (lambda ()
        (for/fold ([sum 0]) ([i (in-bitset bs)])
          (+ sum i)))
      iterations))
  (format-result "in-bitset" time-bitset iterations)

  ;; bitset reverse iteration
  (define time-bitset-rev
    (measure-time
      (lambda ()
        (for/fold ([sum 0]) ([i (in-bitset/rev bs)])
          (+ sum i)))
      iterations))
  (format-result "in-bitset/rev" time-bitset-rev iterations)

  ;; Racket set iteration
  (define time-set
    (measure-time
      (lambda ()
        (for/fold ([sum 0]) ([i (in-set rs)])
          (+ sum i)))
      iterations))
  (format-result "in-set" time-set iterations)

  (printf "  Iteration speedup: ~ax\n" (real->decimal-string (/ time-set time-bitset) 2)))

;; ========================================
;; Count Benchmark
;; ========================================

(define (run-count-benchmark size iterations)
  (printf "\n=== Count Benchmark (size: ~a, iterations: ~a) ===\n" size iterations)

  (define bs (for/bitset ([i (in-range size)]) i))
  (define rs (for/set ([i (in-range size)]) i))

  ;; bitset count
  (define time-bitset
    (measure-time (lambda () (bitset-count bs)) iterations))
  (format-result "bitset-count" time-bitset iterations)

  ;; Racket set count
  (define time-set
    (measure-time (lambda () (set-count rs)) iterations))
  (format-result "set-count" time-set iterations)

  (printf "  Speedup: ~ax\n" (real->decimal-string (/ time-set time-bitset) 2)))

;; ========================================
;; Add/Remove Benchmark
;; ========================================

(define (run-add-remove-benchmark size ops iterations)
  (printf "\n=== Add/Remove Benchmark (size: ~a, ops: ~a, iterations: ~a) ===\n"
          size ops iterations)

  (define bs (for/bitset ([i (in-range size)]) i))
  (define rs (for/set ([i (in-range size)]) i))
  (define add-indices (for/list ([_ (in-range ops)]) (+ size (random size))))
  (define remove-indices (for/list ([_ (in-range ops)]) (random size)))

  ;; bitset add
  (define time-bitset-add
    (measure-time
      (lambda ()
        (for/fold ([s bs]) ([i add-indices])
          (bitset-add s i)))
      iterations))
  (format-result "bitset-add" time-bitset-add iterations)

  ;; Racket set add
  (define time-set-add
    (measure-time
      (lambda ()
        (for/fold ([s rs]) ([i add-indices])
          (set-add s i)))
      iterations))
  (format-result "set-add" time-set-add iterations)
  (printf "  Add speedup: ~ax\n" (real->decimal-string (/ time-set-add time-bitset-add) 2))

  ;; bitset remove
  (define time-bitset-remove
    (measure-time
      (lambda ()
        (for/fold ([s bs]) ([i remove-indices])
          (bitset-remove s i)))
      iterations))
  (format-result "bitset-remove" time-bitset-remove iterations)

  ;; Racket set remove
  (define time-set-remove
    (measure-time
      (lambda ()
        (for/fold ([s rs]) ([i remove-indices])
          (set-remove s i)))
      iterations))
  (format-result "set-remove" time-set-remove iterations)
  (printf "  Remove speedup: ~ax\n" (real->decimal-string (/ time-set-remove time-bitset-remove) 2)))

;; ========================================
;; Subset/Disjoint Benchmark
;; ========================================

(define (run-predicate-benchmark size iterations)
  (printf "\n=== Predicate Benchmark (size: ~a, iterations: ~a) ===\n" size iterations)

  (define bs1 (for/bitset ([i (in-range size)]) i))
  (define bs2 (for/bitset ([i (in-range (quotient size 2))]) i))  ; subset of bs1
  (define rs1 (for/set ([i (in-range size)]) i))
  (define rs2 (for/set ([i (in-range (quotient size 2))]) i))

  ;; subset?
  (define time-bitset-subset
    (measure-time (lambda () (bitset-subset? bs2 bs1)) iterations))
  (format-result "bitset-subset?" time-bitset-subset iterations)

  (define time-set-subset
    (measure-time (lambda () (subset? rs2 rs1)) iterations))
  (format-result "subset?" time-set-subset iterations)
  (printf "  Subset speedup: ~ax\n" (real->decimal-string (/ time-set-subset time-bitset-subset) 2)))

;; ========================================
;; Run All Benchmarks
;; ========================================

(displayln "========================================")
(displayln "      BITSET PERFORMANCE BENCHMARK")
(displayln "========================================")
(displayln "\nComparing bitset vs Racket's built-in set")
(displayln "for dense integer sets.")

;; Warmup
(displayln "\nWarming up JIT...")
(define warmup-bs (for/bitset ([i (in-range 100)]) i))
(define warmup-rs (for/set ([i (in-range 100)]) i))
(for ([_ (in-range 1000)])
  (bitset-member? warmup-bs (random 100))
  (set-member? warmup-rs (random 100))
  (bitset-union warmup-bs warmup-bs)
  (set-union warmup-rs warmup-rs))

(displayln "\n========================================")
(displayln "           BENCHMARK RESULTS")
(displayln "========================================")

;; Small sets
(run-construction-benchmark 100 1000)
(run-membership-benchmark 100 1000 100)
(run-set-ops-benchmark 100 10000)
(run-iteration-benchmark 100 1000)
(run-count-benchmark 100 10000)
(run-add-remove-benchmark 100 100 100)
(run-predicate-benchmark 100 10000)

;; Medium sets
(run-construction-benchmark 1000 100)
(run-membership-benchmark 1000 1000 100)
(run-set-ops-benchmark 1000 1000)
(run-iteration-benchmark 1000 100)
(run-count-benchmark 1000 1000)
(run-add-remove-benchmark 1000 100 100)
(run-predicate-benchmark 1000 10000)

;; Large sets
(run-construction-benchmark 10000 10)
(run-membership-benchmark 10000 1000 10)
(run-set-ops-benchmark 10000 100)
(run-iteration-benchmark 10000 10)
(run-count-benchmark 10000 100)
(run-add-remove-benchmark 10000 100 10)
(run-predicate-benchmark 10000 1000)

(displayln "\n========================================")
(displayln "         BENCHMARK COMPLETE")
(displayln "========================================")

(displayln "\nConclusion:")
(displayln "- bitset uses O(1) bitwise operations for set ops")
(displayln "- Racket set uses hash-based implementation")
(displayln "- bitset is ideal for dense integer sets with small values")
(displayln "- Racket set is better for sparse/large-value/non-integer sets")
