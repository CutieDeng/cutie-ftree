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
  (define para-break "\n\n")
  (let loop ([result ""] [remaining n-chars])
    (cond
      [(<= remaining 0) (substring result 0 (min (string-length result) n-chars))]
      [(= (modulo (string-length result) 500) 0)
       (loop (string-append result para-break) (- remaining 2))]
      [else
       (loop (string-append result base) (- remaining (string-length base)))])))

(printf "Text Buffer Benchmark\n")
(printf "=====================\n\n")

;; Test construction
(printf "Construction:\n")
(define str-1k (make-test-string 1000))
(define str-10k (make-test-string 10000))
(define str-100k (make-test-string 100000))

(define tb-1k (time-it "  1K chars -> text" (lambda () (string->text str-1k))))
(define tb-10k (time-it " 10K chars -> text" (lambda () (string->text str-10k))))
(define tb-100k (time-it "100K chars -> text" (lambda () (string->text str-100k))))

(printf "\n")

;; Test measures (should be O(1))
(printf "Measures (should be O(1)):\n")
(time-it "  1K length" (lambda () (for ([_ (in-range 10000)]) (text-length tb-1k))))
(time-it " 10K length" (lambda () (for ([_ (in-range 10000)]) (text-length tb-10k))))
(time-it "100K length" (lambda () (for ([_ (in-range 10000)]) (text-length tb-100k))))

(printf "\n")

;; Test character access (should be O(log n))
(printf "Character access (should be O(log n)):\n")
(time-it "  1K text-ref middle" (lambda () (for ([_ (in-range 1000)]) (text-ref tb-1k 500))))
(time-it " 10K text-ref middle" (lambda () (for ([_ (in-range 1000)]) (text-ref tb-10k 5000))))
(time-it "100K text-ref middle" (lambda () (for ([_ (in-range 1000)]) (text-ref tb-100k 50000))))

(printf "\n")

;; Test word navigation (should be O(log n))
(printf "Word navigation:\n")
(define wc-1k (text-word-count tb-1k))
(define wc-10k (text-word-count tb-10k))
(define wc-100k (text-word-count tb-100k))
(printf "  Word counts: 1K=~a, 10K=~a, 100K=~a\n" wc-1k wc-10k wc-100k)

(time-it "  1K word-at middle" (lambda () (for ([_ (in-range 100)]) (text-word-at tb-1k (quotient wc-1k 2)))))
(time-it " 10K word-at middle" (lambda () (for ([_ (in-range 100)]) (text-word-at tb-10k (quotient wc-10k 2)))))
(time-it "100K word-at middle" (lambda () (for ([_ (in-range 100)]) (text-word-at tb-100k (quotient wc-100k 2)))))

(printf "\n")

;; Test split (should be O(log n))
(printf "Split (should be O(log n)):\n")
(time-it "  1K split middle" (lambda () (for ([_ (in-range 100)]) (text-split-at tb-1k 500))))
(time-it " 10K split middle" (lambda () (for ([_ (in-range 100)]) (text-split-at tb-10k 5000))))
(time-it "100K split middle" (lambda () (for ([_ (in-range 100)]) (text-split-at tb-100k 50000))))

(printf "\nBenchmark complete.\n")
