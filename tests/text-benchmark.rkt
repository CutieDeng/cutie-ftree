#lang racket/base

;; text-benchmark: Performance tests for text buffer

(require "../text.rkt")

(define (time-it label thunk)
  (collect-garbage)
  (collect-garbage)
  (define start (current-inexact-milliseconds))
  (define result (thunk))
  (define end (current-inexact-milliseconds))
  (printf "~a: ~a ms\n" label (- end start))
  result)

;; Generate test string with paragraphs
(define (make-test-string n-chars)
  (define base "The quick brown fox jumps over the lazy dog. ")
  (define base-len
    (string-length base))
  (define para-break "\n\n")
  (let loop ([result ""] [remaining n-chars])
    (cond
      [(<= remaining 0)
       (define trimmed-length
         (min (string-length result) n-chars))
       (substring result 0 trimmed-length)]
      [(= (modulo (string-length result) 500) 0)
       (define next-result
         (string-append result para-break))
       (define next-remaining
         (- remaining 2))
       (loop next-result next-remaining)]
      [else
       (define next-result
         (string-append result base))
       (define next-remaining
         (- remaining base-len))
       (loop next-result next-remaining)]
      )
    )
  )

(define (run-repeat count thunk)
  (define iter-seq
    (in-range count))
  (for ([_ iter-seq])
    (void (thunk))
    ))

(define (time-to-text label s)
  (define (job)
    (string->text s))
  (time-it label job))

(define (time-length label tb)
  (define (op)
    (text-length tb))
  (define (job)
    (run-repeat 10000 op))
  (time-it label job))

(define (time-ref label tb idx)
  (define (op)
    (text-ref tb idx))
  (define (job)
    (run-repeat 1000 op))
  (time-it label job))

(define (time-word-at label tb idx)
  (define (op)
    (text-word-at tb idx))
  (define (job)
    (run-repeat 100 op))
  (time-it label job))

(define (time-split-at label tb idx)
  (define (op)
    (text-split-at tb idx))
  (define (job)
    (run-repeat 100 op))
  (time-it label job))

(printf "Text Buffer Benchmark\n")
(printf "=====================\n\n")

;; Test construction
(printf "Construction:\n")
(define str-1k (make-test-string 1000))
(define str-10k (make-test-string 10000))
(define str-100k (make-test-string 100000))

(define tb-1k
  (time-to-text "  1K chars -> text" str-1k))
(define tb-10k
  (time-to-text " 10K chars -> text" str-10k))
(define tb-100k
  (time-to-text "100K chars -> text" str-100k))

(printf "\n")

;; Test measures (should be O(1))
(printf "Measures (should be O(1)):\n")
(time-length "  1K length" tb-1k)
(time-length " 10K length" tb-10k)
(time-length "100K length" tb-100k)

(printf "\n")

;; Test character access (should be O(log n))
(printf "Character access (should be O(log n)):\n")
(time-ref "  1K text-ref middle" tb-1k 500)
(time-ref " 10K text-ref middle" tb-10k 5000)
(time-ref "100K text-ref middle" tb-100k 50000)

(printf "\n")

;; Test word navigation (should be O(log n))
(printf "Word navigation:\n")
(define wc-1k (text-word-count tb-1k))
(define wc-10k (text-word-count tb-10k))
(define wc-100k (text-word-count tb-100k))
(printf "  Word counts: 1K=~a, 10K=~a, 100K=~a\n" wc-1k wc-10k wc-100k)

(define wc-mid-1k
  (quotient wc-1k 2))
(define wc-mid-10k
  (quotient wc-10k 2))
(define wc-mid-100k
  (quotient wc-100k 2))

(time-word-at "  1K word-at middle" tb-1k wc-mid-1k)
(time-word-at " 10K word-at middle" tb-10k wc-mid-10k)
(time-word-at "100K word-at middle" tb-100k wc-mid-100k)

(printf "\n")

;; Test split (should be O(log n))
(printf "Split (should be O(log n)):\n")
(time-split-at "  1K split middle" tb-1k 500)
(time-split-at " 10K split middle" tb-10k 5000)
(time-split-at "100K split middle" tb-100k 50000)

(printf "\nBenchmark complete.\n")
