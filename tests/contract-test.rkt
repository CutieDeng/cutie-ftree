#lang racket/base

(require rackunit)
(require racket/contract)
(require "../pvector/safe.rkt")
(require "../ordered-map/safe.rkt")
(require "../comparator.rkt")

;; ========================================
;; Contract Attachment Demonstration
;; ========================================

;; Case 1: Contract on module boundary (provide/contract)
;; - Contract is checked when value CROSSES the boundary
;; - After crossing, the value is "wrapped" or checked

;; Case 2: Contract on binding (define/contract)
;; - Contract is checked when value is ASSIGNED to the binding
;; - For functions: checked on EACH call

;; Case 3: Value wrapper (pvectorof/ordered-mapof)
;; - Contract TRAVELS with the value
;; - Checked on EVERY operation via *-functions

;; ========================================
;; Test: pvectorof contracts
;; ========================================

(test-case "pvectorof: first-order check"
  ;; First-order check happens immediately
  (check-true (contract-first-order-passes? (pvectorof integer?)
                (list->pvector '(1 2 3))))
  (check-false (contract-first-order-passes? (pvectorof integer?)
                 (list->pvector '(1 "two" 3))))
  (check-false (contract-first-order-passes? (pvectorof integer?)
                 "not a pvector")))

(test-case "pvectorof: boundary check"
  ;; Contract checked when crossing define/contract boundary
  (check-not-exn
    (lambda ()
      (contract (pvectorof integer?) (list->pvector '(1 2 3)) 'pos 'neg)))

  (check-exn exn:fail:contract?
    (lambda ()
      (contract (pvectorof integer?) (list->pvector '(1 "bad" 3)) 'pos 'neg))))

(test-case "pvectorof: wrapper preserves contract"
  (define/contract pv (pvectorof integer?)
    (list->pvector '(1 2 3)))

  ;; The wrapper type is created
  (check-true (contracted-pvector? pv))

  ;; Operations return wrapped values
  (define pv2 (pvector-cons-right* pv 4))
  (check-true (contracted-pvector? pv2))

  ;; Contract is still enforced on new value
  (check-exn exn:fail:contract?
    (lambda () (pvector-cons-right* pv2 "bad"))))

(test-case "pvectorof: input vs output blame"
  (define/contract pv (pvectorof integer?)
    (list->pvector '(1 2 3)))

  ;; Output check: ref returns checked value
  (check-equal? (pvector-ref* pv 0) 1)

  ;; Input check: cons-right checks the new element
  (check-exn exn:fail:contract?
    (lambda () (pvector-cons-right* pv "not-int")))

  ;; Input check: set checks the new value
  (check-exn exn:fail:contract?
    (lambda () (pvector-set* pv 0 "not-int")))

  ;; Input check: insert checks the new element
  (check-exn exn:fail:contract?
    (lambda () (pvector-insert* pv 0 "not-int"))))

(test-case "pvectorof: iteration with contract"
  (define/contract pv (pvectorof integer?)
    (list->pvector '(1 2 3)))

  ;; Iteration uses prop:sequence, elements are checked
  (check-equal? (for/list ([v pv]) v) '(1 2 3)))

(test-case "pvectorof: pop returns checked values"
  (define/contract pv (pvectorof integer?)
    (list->pvector '(1 2 3)))

  (define-values (elem rest) (pvector-pop-left* pv))
  (check-equal? elem 1)
  (check-true (contracted-pvector? rest)))

;; ========================================
;; Test: ordered-mapof contracts
;; ========================================

(test-case "ordered-mapof: first-order check"
  (define om (for/ordered-map integer-compare ([i 3]) (cons i (number->string i))))

  (check-true (contract-first-order-passes? (ordered-mapof integer? string?) om))
  (check-false (contract-first-order-passes? (ordered-mapof integer? integer?) om))
  (check-false (contract-first-order-passes? (ordered-mapof string? string?) om)))

(test-case "ordered-mapof: boundary check"
  (check-not-exn
    (lambda ()
      (contract (ordered-mapof integer? string?)
        (for/ordered-map integer-compare ([i 3]) (cons i (format "~a" i)))
        'pos 'neg)))

  (check-exn exn:fail:contract?
    (lambda ()
      (contract (ordered-mapof integer? string?)
        (for/ordered-map integer-compare ([i 3]) (cons i i)) ;; value is int, not string
        'pos 'neg))))

(test-case "ordered-mapof: wrapper preserves contract"
  (define/contract om (ordered-mapof integer? string?)
    (for/ordered-map integer-compare ([i 3]) (cons i (format "v~a" i))))

  (check-true (contracted-ordered-map? om))

  ;; Operations return wrapped values
  (define om2 (ordered-map-set* om 10 "ten"))
  (check-true (contracted-ordered-map? om2))

  ;; Contract still enforced
  (check-exn exn:fail:contract?
    (lambda () (ordered-map-set* om2 20 999)))) ;; value should be string

(test-case "ordered-mapof: key and value contracts"
  (define/contract om (ordered-mapof integer? string?)
    (ordered-map-empty integer-compare))

  ;; Valid key and value
  (check-not-exn (lambda () (ordered-map-set* om 1 "one")))

  ;; Invalid key type
  (check-exn exn:fail:contract?
    (lambda () (ordered-map-set* om "bad-key" "value")))

  ;; Invalid value type
  (check-exn exn:fail:contract?
    (lambda () (ordered-map-set* om 1 12345))))

(test-case "ordered-mapof: query returns checked values"
  (define/contract om (ordered-mapof integer? string?)
    (for/ordered-map integer-compare ([i 3]) (cons i (format "v~a" i))))

  ;; ref returns string (checked)
  (check-equal? (ordered-map-ref* om 1) "v1")

  ;; query returns pair with checked key and value
  (define result (ordered-map-query* om 1))
  (check-equal? result '(1 . "v1"))

  ;; min/max return checked pairs
  (check-equal? (ordered-map-min* om) '(0 . "v0"))
  (check-equal? (ordered-map-max* om) '(2 . "v2")))

(test-case "ordered-mapof: iteration with contract"
  (define/contract om (ordered-mapof integer? string?)
    (for/ordered-map integer-compare ([i 3]) (cons i (format "v~a" i))))

  ;; Iteration checks each key-value pair
  (check-equal?
    (for/list ([kv om]) kv)
    '((0 . "v0") (1 . "v1") (2 . "v2"))))

;; ========================================
;; Test: Contract behavior comparison
;; ========================================

(test-case "compare: unwrapped vs wrapped operations"
  ;; Without contract wrapper - no runtime checks
  (define pv-raw (list->pvector '(1 2 3)))
  (check-false (contracted-pvector? pv-raw))

  ;; With contract wrapper - runtime checks on *-operations
  (define/contract pv-wrapped (pvectorof integer?)
    (list->pvector '(1 2 3)))
  (check-true (contracted-pvector? pv-wrapped))

  ;; Raw pvector allows anything (no contract)
  (check-not-exn (lambda () (pvector-cons-right pv-raw "string")))

  ;; Wrapped pvector rejects non-integers
  (check-exn exn:fail:contract?
    (lambda () (pvector-cons-right* pv-wrapped "string"))))

(test-case "compare: contract location matters"
  ;; Contract on function parameter - checked on call
  (define/contract (process-ints pv)
    (-> (pvectorof integer?) integer?)
    ;; pv is now a contracted-pvector, iterate directly (uses prop:sequence)
    (for/fold ([sum 0]) ([v pv])
      (+ sum v)))

  ;; Valid call
  (check-equal? (process-ints (list->pvector '(1 2 3))) 6)

  ;; Invalid call - contract checked at call boundary
  (check-exn exn:fail:contract?
    (lambda () (process-ints (list->pvector '(1 "two" 3))))))

;; ========================================
;; Test: Nested contracts
;; ========================================

(test-case "nested: pvectorof with complex element contract"
  (define/contract pv (pvectorof (cons/c integer? string?))
    (list->pvector (list (cons 1 "a") (cons 2 "b"))))

  (check-true (contracted-pvector? pv))
  (check-equal? (pvector-ref* pv 0) '(1 . "a"))

  ;; Must add valid pair
  (check-not-exn
    (lambda () (pvector-cons-right* pv (cons 3 "c"))))

  ;; Invalid pair rejected
  (check-exn exn:fail:contract?
    (lambda () (pvector-cons-right* pv (cons "bad" "c")))))

;; ========================================
;; Summary output
;; ========================================

(displayln "")
(displayln "Contract System Summary:")
(displayln "========================")
(displayln "")
(displayln "1. pvectorof / ordered-mapof create WRAPPER structures")
(displayln "   - contracted-pvector? / contracted-ordered-map? check wrapper type")
(displayln "")
(displayln "2. Contracts are checked at:")
(displayln "   - Boundary crossing (define/contract, provide/contract)")
(displayln "   - Every *-operation (pvector-ref*, ordered-map-set*, etc.)")
(displayln "   - Iteration (for loops over wrapped values)")
(displayln "")
(displayln "3. Use *-suffixed operations to maintain contract enforcement:")
(displayln "   - pvector-ref* instead of pvector-ref")
(displayln "   - ordered-map-set* instead of ordered-map-set")
(displayln "")
