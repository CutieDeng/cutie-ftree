#lang racket/base

(require racket/contract)

;; ========================================
;; Comparison Result Contract
;; ========================================

(define comparison-result/c (or/c '< '= '>))

;; ========================================
;; Parameterized Comparator Contract
;; ========================================

;; (comparator/c type/c) creates a contract for a comparator function
;; that accepts two values of type/c and returns a comparison result
(define (comparator/c type/c)
  (-> type/c type/c comparison-result/c))

;; Predefined comparator contracts
(define integer-comparator/c (comparator/c integer?))
(define string-comparator/c (comparator/c string?))
(define symbol-comparator/c (comparator/c symbol?))

;; ========================================
;; Built-in Comparators
;; ========================================

(define (integer-compare x0 x1)
  (cond
    [(< x0 x1) '<]
    [(= x0 x1) '=]
    [else '>]
    ) ; cond: integer-compare
  ) ; define integer-compare

(define (string-compare x0 x1)
  (cond
    [(string<? x0 x1) '<]
    [(string=? x0 x1) '=]
    [else '>]
    ) ; cond: string-compare
  ) ; define string-compare

(define (symbol-compare x0 x1)
  (string-compare (symbol->string x0) (symbol->string x1))
  ) ; define symbol-compare

;; ========================================
;; Comparator Constructors
;; ========================================

;; Create a comparator from less-than and equal-to predicates
(define (make-comparator less-than? equal-to?)
  (lambda (a b)
    (cond
      [(less-than? a b) '<]
      [(equal-to? a b) '=]
      [else '>]
      ) ; cond: make-comparator lambda
    ) ; lambda
  ) ; define make-comparator

;; Create a comparator from a cmp-style function (returns -1, 0, 1)
(define (comparator-from-cmp cmp)
  (lambda (a b)
    (define r (cmp a b))
    (cond
      [(negative? r) '<]
      [(zero? r) '=]
      [else '>]
      ) ; cond: comparator-from-cmp lambda
    ) ; lambda
  ) ; define comparator-from-cmp

;; ========================================
;; Exports
;; ========================================

(provide
  ;; Contracts
  comparison-result/c
  comparator/c
  integer-comparator/c
  string-comparator/c
  symbol-comparator/c

  ;; Built-in comparators
  integer-compare
  string-compare
  symbol-compare

  ;; Constructors
  make-comparator
  comparator-from-cmp)
