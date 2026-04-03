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
  (define got
    (ordered-map-query m 0))
  (define expected
    (cons 0 0))
  (check-equal? got expected))

(test-case "Insert without replace keeps original"
  (define m (ordered-map-empty integer-compare))
  (set! m (ordered-map-insert m 0 "int" #f))
  (set! m (ordered-map-insert m 0 "float" #f))
  (define got
    (ordered-map-query m 0))
  (define expected
    (cons 0 "int"))
  (check-equal? got expected))

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
  (define got
    (ordered-map-query m 0))
  (define expected
    (cons 0 "float"))
  (check-equal? got expected))

(test-case "Query multiple elements"
  (define m (ordered-map-empty integer-compare))
  (set! m (ordered-map-insert m 0 "int" #t))
  (set! m (ordered-map-insert m 1 "float" #t))
  (check-equal? (ordered-map-query m 0) (cons 0 "int"))
  (define got
    (ordered-map-query m 1))
  (define expected
    (cons 1 "float"))
  (check-equal? got expected))

;; ========================================
;; Range Insert Tests
;; ========================================

(test-case "Insert range 0-9"
  (define m (ordered-map-empty integer-compare))
  (define i-seq
    (in-range 10))
  (set! m
    (for/fold ([io m]) ([i i-seq])
      (ordered-map-insert io i (add1 i) #f)
      ))
  (check-equal? (ordered-map-query m 7) (cons 7 8))
  (check-equal? (ordered-map-query m 10) #f))

(test-case "Insert range in reverse order"
  (define m (ordered-map-empty integer-compare))
  (define i-seq
    (in-range 10))
  (set! m
    (for/fold ([io m]) ([i i-seq])
      (ordered-map-insert io (- 20 i) (add1 i) #f)
      ))
  (check-equal? (ordered-map-query m 0) #f)
  (define got
    (ordered-map-query m 11))
  (define expected
    (cons 11 10))
  (check-equal? got expected))

;; ========================================
;; Delete Tests
;; ========================================

(test-case "Delete from empty map returns #f"
  (define m (ordered-map-empty integer-compare))
  (define-values (m^ ret) (ordered-map-delete m 1))
  (check-equal? ret #f)
  (check-eq? m m^))

(test-case "Delete existing element"
  (define o0
    (ordered-map-empty integer-compare))
  (define i-seq
    (in-range 15))
  (define m
    (for/fold ([o o0]) ([i i-seq])
      (ordered-map-insert o i i #f)
      ))
  (define-values (m^ nine) (ordered-map-delete m 9))
  (check-equal? nine (cons 9 9))
  (define empty?
    (ordered-map-empty? m^))
  (check-false empty?))

(test-case "Delete from large map"
  (define o0
    (ordered-map-empty integer-compare))
  (define i-seq
    (in-range 31))
  (define m
    (for/foldr ([o o0]) ([i i-seq])
      (ordered-map-insert o i i #f)
      ))
  (define-values (m^ ten) (ordered-map-delete m 10))
  (define expected
    (cons 10 10))
  (check-equal? ten expected))

;; ========================================
;; Large Scale Tests
;; ========================================

(test-case "Large scale insert, query, delete, reinsert"
  (define m (ordered-map-empty integer-compare))
  (define i-seq
    (in-range 20))
  ;; Insert 20 elements
  (for ([i i-seq])
    (define i-str
      (~a i))
    (define value
      (string-append "value" i-str))
    (define next-m
      (ordered-map-insert m i value #f))
    (set! m next-m))
  ;; Check if all inserted elements can be queried correctly
  (define i-seq-2
    (in-range 20))
  (for ([i i-seq-2])
    (define got
      (ordered-map-query m i))
    (define i-str
      (~a i))
    (define value
      (string-append "value" i-str))
    (define expected
      (cons i value))
    (check-equal? got expected))
  ;; Delete some elements and verify
  (define delete-keys '(5 10 15))
  (for ([key delete-keys])
    (define-values (new-m deleted-val) (ordered-map-delete m key))
    (define key-str
      (~a key))
    (define value
      (string-append "value" key-str))
    (define expected-deleted
      (cons key value))
    (check-equal? deleted-val expected-deleted)
    (set! m new-m)
    (define key-found?
      (ordered-map-query m key))
    (check-false key-found?))
  ;; Insert some keys again
  (for ([key delete-keys])
    (define key-str
      (~a key))
    (define value
      (string-append "newvalue" key-str))
    (define next-m
      (ordered-map-insert m key value #t))
    (set! m next-m)
    (define got
      (ordered-map-query m key))
    (define expected
      (cons key value))
    (check-equal? got expected)
    )
  )

;; ========================================
;; Weak Query Tests
;; ========================================

(test-case "ordered-map-query-weak >= finds correct element"
  (define m (ordered-map-empty integer-compare))
  (define i-seq
    (in-range 100))
  (for ([i i-seq])
    (define next-m
      (ordered-map-insert m i i #f))
    (set! m next-m))
  (define got-min
    (ordered-map-query-weak m -1 '>=))
  (define expected-min
    (cons 0 0))
  (check-equal? got-min expected-min)
  (define got-50
    (ordered-map-query-weak m 50 '>=))
  (define expected-50
    (cons 50 50))
  (check-equal? got-50 expected-50))

(test-case "ordered-map-query-weak <= finds correct element"
  (define m (ordered-map-empty integer-compare))
  (define i-seq
    (in-range 100))
  (for ([i i-seq])
    (define next-m
      (ordered-map-insert m i i #f))
    (set! m next-m))
  (define got
    (ordered-map-query-weak m 100 '<=))
  (define expected
    (cons 99 99))
  (check-equal? got expected))

;; ========================================
;; Iteration Tests
;; ========================================

(test-case "Iterate forward with >"
  (define m (ordered-map-empty integer-compare))
  (define i-seq
    (in-range 10))
  (for ([i i-seq])
    (define next-m
      (ordered-map-insert m i i #f))
    (set! m next-m))
  (define cnt 0)
  (define start
    (ordered-map-min m))
  (let loop ([current start])
    (when current
      (set! cnt (add1 cnt))
      (define next
        (ordered-map-query-weak m (car current) '>))
      (loop next)
      ))
  (check-equal? cnt 10))

(test-case "Iterate backward with <"
  (define m (ordered-map-empty integer-compare))
  (define i-seq
    (in-range 10))
  (for ([i i-seq])
    (define next-m
      (ordered-map-insert m i i #f))
    (set! m next-m))
  (define cnt 0)
  (define start
    (ordered-map-max m))
  (let loop ([current start])
    (when current
      (set! cnt (add1 cnt))
      (define next
        (ordered-map-query-weak m (car current) '<))
      (loop next)
      ))
  (check-equal? cnt 10))

;; ========================================
;; Additional Tests
;; ========================================

(test-case "ordered-map-empty? works correctly"
  (define m (ordered-map-empty integer-compare))
  (check-pred ordered-map-empty? m)
  (set! m (ordered-map-insert m 1 1 #f))
  (define empty?
    (ordered-map-empty? m))
  (check-false empty?))

(test-case "ordered-map-min and ordered-map-max"
  (define m (ordered-map-empty integer-compare))
  (define minmax-keys
    '(5 3 7 1 9))
  (define i-seq
    (in-list minmax-keys))
  (for ([i i-seq])
    (define next-m
      (ordered-map-insert m i i #f))
    (set! m next-m))
  (check-equal? (ordered-map-min m) (cons 1 1))
  (define max-kv
    (ordered-map-max m))
  (define expected-max
    (cons 9 9))
  (check-equal? max-kv expected-max))

(test-case "ordered-map-count works correctly"
  (define m (ordered-map-empty integer-compare))
  (check-equal? (ordered-map-count m) 0)
  (define i-seq
    (in-range 10))
  (for ([i i-seq])
    (define next-m
      (ordered-map-insert m i i #f))
    (set! m next-m))
  (check-equal? (ordered-map-count m) 10))

(test-case "ordered-map-has-key? works correctly"
  (define m (ordered-map-empty integer-compare))
  (set! m (ordered-map-insert m 5 "five" #f))
  (check-true (ordered-map-has-key? m 5))
  (define has-10?
    (ordered-map-has-key? m 10))
  (check-false has-10?))

(test-case "ordered-map-keys and ordered-map-values"
  (define m (ordered-map-empty integer-compare))
  (define kv-keys
    '(3 1 4 1 5))
  (define i-seq
    (in-list kv-keys))
  (for ([i i-seq])
    (define next-m
      (ordered-map-insert m i (* i 10) #f))
    (set! m next-m))
  (define keys (ordered-map-keys m))
  (define vals (ordered-map-values m))
  ;; Should have unique keys (1, 3, 4, 5)
  (check-equal? (length keys) 4)
  (check-equal? (length vals) 4))

(test-case "in-ordered-map sequence iteration"
  (define m (ordered-map-empty integer-compare))
  (define i-seq
    (in-range 5))
  (for ([i i-seq])
    (define next-m
      (ordered-map-insert m i i #f))
    (set! m next-m))
  (define kv-seq
    (in-ordered-map m))
  (define sum
    (for/fold ([s 0]) ([kv kv-seq])
      (+ s (cdr kv))
      ))
  (check-equal? sum 10))  ; 0+1+2+3+4

(test-case "ordered-map-ref and ordered-map-set"
  (define m (ordered-map-empty integer-compare))
  (set! m (ordered-map-set m 1 "one"))
  (set! m (ordered-map-set m 2 "two"))
  (check-equal? (ordered-map-ref m 1) "one")
  (check-equal? (ordered-map-ref m 2) "two")
  (check-equal? (ordered-map-ref m 3 "default") "default"))

;; ========================================
;; Ordinal Query Tests
;; ========================================

(test-case "ordered-map-rank on empty map"
  (define m (ordered-map-empty integer-compare))
  (check-equal? (ordered-map-rank m 5) #f))

(test-case "ordered-map-rank basic"
  (define m (ordered-map-empty integer-compare))
  (define rank-keys
    '(10 20 30 40 50))
  (define i-seq
    (in-list rank-keys))
  (for ([i i-seq])
    (define next-m
      (ordered-map-insert m i i #f))
    (set! m next-m))
  ;; ranks are 0-indexed
  (check-equal? (ordered-map-rank m 10) 0)
  (check-equal? (ordered-map-rank m 20) 1)
  (check-equal? (ordered-map-rank m 30) 2)
  (check-equal? (ordered-map-rank m 40) 3)
  (check-equal? (ordered-map-rank m 50) 4)
  ;; non-existent key
  (check-equal? (ordered-map-rank m 25) #f)
  (check-equal? (ordered-map-rank m 0) #f)
  (check-equal? (ordered-map-rank m 100) #f))

(test-case "ordered-map-select on empty map"
  (define m (ordered-map-empty integer-compare))
  (check-equal? (ordered-map-select m 0) #f))

(test-case "ordered-map-select basic"
  (define m (ordered-map-empty integer-compare))
  (define select-keys
    '(10 20 30 40 50))
  (define i-seq
    (in-list select-keys))
  (for ([i i-seq])
    (define next-m
      (ordered-map-insert m i (* i 2) #f))
    (set! m next-m))
  ;; select by rank (0-indexed)
  (check-equal? (ordered-map-select m 0) (cons 10 20))
  (check-equal? (ordered-map-select m 1) (cons 20 40))
  (check-equal? (ordered-map-select m 2) (cons 30 60))
  (check-equal? (ordered-map-select m 3) (cons 40 80))
  (check-equal? (ordered-map-select m 4) (cons 50 100))
  ;; out of bounds
  (check-equal? (ordered-map-select m -1) #f)
  (check-equal? (ordered-map-select m 5) #f)
  (check-equal? (ordered-map-select m 100) #f))

(test-case "ordered-map-count-less-than on empty map"
  (define m (ordered-map-empty integer-compare))
  (check-equal? (ordered-map-count-less-than m 5) 0))

(test-case "ordered-map-count-less-than basic"
  (define m (ordered-map-empty integer-compare))
  (define count-lt-keys
    '(10 20 30 40 50))
  (define i-seq
    (in-list count-lt-keys))
  (for ([i i-seq])
    (define next-m
      (ordered-map-insert m i i #f))
    (set! m next-m))
  (check-equal? (ordered-map-count-less-than m 0) 0)
  (check-equal? (ordered-map-count-less-than m 10) 0)
  (check-equal? (ordered-map-count-less-than m 15) 1)
  (check-equal? (ordered-map-count-less-than m 20) 1)
  (check-equal? (ordered-map-count-less-than m 25) 2)
  (check-equal? (ordered-map-count-less-than m 50) 4)
  (check-equal? (ordered-map-count-less-than m 100) 5))

(test-case "ordinal queries large scale"
  (define m (ordered-map-empty integer-compare))
  (define i-seq
    (in-range 0 1000 2))
  (for ([i i-seq])  ; even numbers 0, 2, 4, ..., 998
    (define next-m
      (ordered-map-insert m i i #f))
    (set! m next-m))
  ;; 500 elements total
  (check-equal? (ordered-map-count m) 500)
  ;; rank of element 100 is 50 (elements 0,2,4,...,98 come before)
  (check-equal? (ordered-map-rank m 100) 50)
  ;; select rank 50 should give us 100
  (check-equal? (ordered-map-select m 50) (cons 100 100))
  ;; count-less-than 100 is 50
  (check-equal? (ordered-map-count-less-than m 100) 50)
  ;; odd number doesn't exist
  (check-equal? (ordered-map-rank m 101) #f)
  ;; count-less-than 101 is still 51 (0,2,...,100)
  (check-equal? (ordered-map-count-less-than m 101) 51))

(test-case "rank and select are inverse operations"
  (define m (ordered-map-empty integer-compare))
  (define i-seq
    (in-range 100))
  (for ([i i-seq])
    (define key
      (* i 7))
    (define next-m
      (ordered-map-insert m key i #f))
    (set! m next-m))  ; keys: 0, 7, 14, 21, ...
  ;; for each key, rank then select should give back the same element
  (for ([i (in-range 100)])
    (define key (* i 7))
    (define rank (ordered-map-rank m key))
    (check-equal? rank i)
    (define elem (ordered-map-select m rank))
    (define elem-key
      (car elem))
    (check-equal? elem-key key)
    )
  )
