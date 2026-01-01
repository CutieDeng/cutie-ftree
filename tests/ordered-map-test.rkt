#lang racket/base

(require rackunit)
(require racket/format)
(require "../ordered-map.rkt")
(require "../comparator.rkt")

;; ========================================
;; Basic Query Tests
;; ========================================

(test-case "Query empty map returns #f"
  (define m (ordered-map-empty integer-compare))
  (check-equal? (ordered-map-query m 0) #f))

(test-case "Query single element map"
  (define m (ordered-map-empty integer-compare))
  (set! m (ordered-map-insert m 0 0 #t))
  (check-equal? (ordered-map-query m 0) (cons 0 0)))

(test-case "Insert without replace keeps original"
  (define m (ordered-map-empty integer-compare))
  (set! m (ordered-map-insert m 0 "int" #f))
  (set! m (ordered-map-insert m 0 "float" #f))
  (check-equal? (ordered-map-query m 0) (cons 0 "int")))

(test-case "Insert without replace returns same object"
  (define m (ordered-map-empty integer-compare))
  (set! m (ordered-map-insert m 0 "int" #f))
  (define m-back m)
  (set! m (ordered-map-insert m 0 "float" #f))
  (check-eq? m-back m))

(test-case "Insert with replace modifies value"
  (define m (ordered-map-empty integer-compare))
  (set! m (ordered-map-insert m 0 "int" #t))
  (define m-back m)
  (set! m (ordered-map-insert m 0 "float" #t))
  (check-not-eq? m-back m)
  (check-equal? (ordered-map-query m 0) (cons 0 "float")))

(test-case "Query multiple elements"
  (define m (ordered-map-empty integer-compare))
  (set! m (ordered-map-insert m 0 "int" #t))
  (set! m (ordered-map-insert m 1 "float" #t))
  (check-equal? (ordered-map-query m 0) (cons 0 "int"))
  (check-equal? (ordered-map-query m 1) (cons 1 "float")))

;; ========================================
;; Range Insert Tests
;; ========================================

(test-case "Insert range 0-9"
  (define m (ordered-map-empty integer-compare))
  (set! m (for/fold ([io m]) ([i (in-range 10)])
    (ordered-map-insert io i (add1 i) #f)))
  (check-equal? (ordered-map-query m 7) (cons 7 8))
  (check-equal? (ordered-map-query m 10) #f))

(test-case "Insert range in reverse order"
  (define m (ordered-map-empty integer-compare))
  (set! m (for/fold ([io m]) ([i (in-range 10)])
    (ordered-map-insert io (- 20 i) (add1 i) #f)))
  (check-equal? (ordered-map-query m 0) #f)
  (check-equal? (ordered-map-query m 11) (cons 11 10)))

;; ========================================
;; Delete Tests
;; ========================================

(test-case "Delete from empty map returns #f"
  (define m (ordered-map-empty integer-compare))
  (define-values (m^ ret) (ordered-map-delete m 1))
  (check-equal? ret #f)
  (check-eq? m m^))

(test-case "Delete existing element"
  (define m (for/fold ([o (ordered-map-empty integer-compare)]) ([i (in-range 15)])
    (ordered-map-insert o i i #f)))
  (define-values (m^ nine) (ordered-map-delete m 9))
  (check-equal? nine (cons 9 9))
  (check-false (ordered-map-empty? m^)))

(test-case "Delete from large map"
  (define m (for/foldr ([o (ordered-map-empty integer-compare)]) ([i (in-range 31)])
    (ordered-map-insert o i i #f)))
  (define-values (m^ ten) (ordered-map-delete m 10))
  (check-equal? ten (cons 10 10)))

;; ========================================
;; Large Scale Tests
;; ========================================

(test-case "Large scale insert, query, delete, reinsert"
  (let ([m (ordered-map-empty integer-compare)])
    ;; Insert 20 elements
    (for ([i (in-range 20)])
      (set! m (ordered-map-insert m i (string-append "value" (~a i)) #f)))
    ;; Check if all inserted elements can be queried correctly
    (for ([i (in-range 20)])
      (check-equal? (ordered-map-query m i) (cons i (string-append "value" (~a i)))))
    ;; Delete some elements and verify
    (define delete-keys '(5 10 15))
    (for ([key delete-keys])
      (define-values (new-m deleted-val) (ordered-map-delete m key))
      (check-equal? deleted-val (cons key (string-append "value" (~a key))))
      (set! m new-m)
      (check-false (ordered-map-query m key)))
    ;; Insert some keys again
    (for ([key delete-keys])
      (set! m (ordered-map-insert m key (string-append "newvalue" (~a key)) #t))
      (check-equal? (ordered-map-query m key) (cons key (string-append "newvalue" (~a key)))))))

;; ========================================
;; Weak Query Tests
;; ========================================

(test-case "ordered-map-query-weak >= finds correct element"
  (define m (ordered-map-empty integer-compare))
  (for ([i (in-range 100)])
    (set! m (ordered-map-insert m i i #f)))
  (check-equal? (ordered-map-query-weak m -1 '>=) (cons 0 0))
  (check-equal? (ordered-map-query-weak m 50 '>=) (cons 50 50)))

(test-case "ordered-map-query-weak <= finds correct element"
  (define m (ordered-map-empty integer-compare))
  (for ([i (in-range 100)])
    (set! m (ordered-map-insert m i i #f)))
  (check-equal? (ordered-map-query-weak m 100 '<=) (cons 99 99)))

;; ========================================
;; Iteration Tests
;; ========================================

(test-case "Iterate forward with >"
  (define m (ordered-map-empty integer-compare))
  (for ([i (in-range 10)])
    (set! m (ordered-map-insert m i i #f)))
  (define cnt 0)
  (let loop ([current (ordered-map-min m)])
    (when current
      (set! cnt (add1 cnt))
      (loop (ordered-map-query-weak m (car current) '>))))
  (check-equal? cnt 10))

(test-case "Iterate backward with <"
  (define m (ordered-map-empty integer-compare))
  (for ([i (in-range 10)])
    (set! m (ordered-map-insert m i i #f)))
  (define cnt 0)
  (let loop ([current (ordered-map-max m)])
    (when current
      (set! cnt (add1 cnt))
      (loop (ordered-map-query-weak m (car current) '<))))
  (check-equal? cnt 10))

;; ========================================
;; Additional Tests
;; ========================================

(test-case "ordered-map-empty? works correctly"
  (define m (ordered-map-empty integer-compare))
  (check-pred ordered-map-empty? m)
  (set! m (ordered-map-insert m 1 1 #f))
  (check-false (ordered-map-empty? m)))

(test-case "ordered-map-min and ordered-map-max"
  (define m (ordered-map-empty integer-compare))
  (for ([i '(5 3 7 1 9)])
    (set! m (ordered-map-insert m i i #f)))
  (check-equal? (ordered-map-min m) (cons 1 1))
  (check-equal? (ordered-map-max m) (cons 9 9)))

(test-case "ordered-map-count works correctly"
  (define m (ordered-map-empty integer-compare))
  (check-equal? (ordered-map-count m) 0)
  (for ([i (in-range 10)])
    (set! m (ordered-map-insert m i i #f)))
  (check-equal? (ordered-map-count m) 10))

(test-case "ordered-map-has-key? works correctly"
  (define m (ordered-map-empty integer-compare))
  (set! m (ordered-map-insert m 5 "five" #f))
  (check-true (ordered-map-has-key? m 5))
  (check-false (ordered-map-has-key? m 10)))

(test-case "ordered-map-keys and ordered-map-values"
  (define m (ordered-map-empty integer-compare))
  (for ([i '(3 1 4 1 5)])
    (set! m (ordered-map-insert m i (* i 10) #f)))
  (define keys (ordered-map-keys m))
  (define vals (ordered-map-values m))
  ;; Should have unique keys (1, 3, 4, 5)
  (check-equal? (length keys) 4)
  (check-equal? (length vals) 4))

(test-case "in-ordered-map sequence iteration"
  (define m (ordered-map-empty integer-compare))
  (for ([i (in-range 5)])
    (set! m (ordered-map-insert m i i #f)))
  (define sum (for/fold ([s 0]) ([kv (in-ordered-map m)])
    (+ s (cdr kv))))
  (check-equal? sum 10))  ; 0+1+2+3+4

(test-case "ordered-map-ref and ordered-map-set"
  (define m (ordered-map-empty integer-compare))
  (set! m (ordered-map-set m 1 "one"))
  (set! m (ordered-map-set m 2 "two"))
  (check-equal? (ordered-map-ref m 1) "one")
  (check-equal? (ordered-map-ref m 2) "two")
  (check-equal? (ordered-map-ref m 3 "default") "default"))
