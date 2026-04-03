#lang racket/base

(require rackunit racket/match)
(require "../ordered-map.rkt")
(require "../comparator.rkt")

;; ========================================
;; Test ordered-map* match expander
;; ========================================

(define test-pairs
  (list
    (cons 1 "one")
    (cons 3 "three")
    (cons 5 "five")
    (cons 7 "seven")
    ))

(define test-pairs-seq
  (in-list test-pairs))

(define test-om0
  (ordered-map-empty integer-compare))

(define test-om
  (for/fold ([om test-om0])
            ([kv test-pairs-seq])
    (ordered-map-set om (car kv) (cdr kv))
    ))

;; Test: single key extraction
(test-case "ordered-map* single key"
  (match test-om
    [(ordered-map* [3 v])
     (check-equal? v "three")]
    [_
     (fail "should match")]
    ))

;; Test: multiple keys extraction
(test-case "ordered-map* multiple keys"
  (match test-om
    [(ordered-map* [1 v1] [5 v5] [7 v7])
     (check-equal? v1 "one")
     (check-equal? v5 "five")
     (check-equal? v7 "seven")]
    [_
     (fail "should match")]
    ))

;; Test: missing key should not match
(test-case "ordered-map* missing key"
  (define matched?
    (match test-om
      [(ordered-map* [1 _] [999 _]) #t]
      [_ #f]
      ))
  (check-false matched?))

;; Test: all keys missing should not match
(test-case "ordered-map* all keys missing"
  (define matched?
    (match test-om
      [(ordered-map* [100 _] [200 _]) #t]
      [_ #f]
      ))
  (check-false matched?))

;; Test: value pattern matching
(test-case "ordered-map* value pattern"
  (match test-om
    [(ordered-map* [3 s])
     (check-true (string? s))
     (check-equal? s "three")]
    [_
     (fail "should match string pattern")]
    ))

;; Test: value pattern mismatch
(test-case "ordered-map* value pattern mismatch"
  (define matched?
    (match test-om
      [(ordered-map* [3 s])
       (number? s)]
      [_ #f]
      ))
  (check-false matched?))

;; Test: empty bindings (just type check)
(test-case "ordered-map* no bindings"
  (match test-om
    [(ordered-map*) #t]
    [_
     (fail "should match")]
    ))

;; Test: with computed key
(test-case "ordered-map* computed key"
  (define k (+ 1 2))
  (match test-om
    [(ordered-map* [k v])
     (check-equal? v "three")]
    [_
     (fail "should match")]
    ))

;; ========================================
;; Test ordered-map* with defaults
;; ========================================

;; Test: all keys exist (with default syntax)
(test-case "ordered-map* with defaults - all exist"
  (match test-om
    [(ordered-map* [1 v1 #f] [3 v3 #f])
     (check-equal? v1 "one")
     (check-equal? v3 "three")
     ]
    ))

;; Test: some keys missing - use default
(test-case "ordered-map* with defaults - some missing"
  (match test-om
    [(ordered-map* [1 v1 "default1"] [999 v999 "default999"])
     (check-equal? v1 "one")
     (check-equal? v999 "default999")
     ]
    ))

;; Test: all keys missing - all defaults
(test-case "ordered-map* all defaults"
  (match test-om
    [(ordered-map* [100 v100 "d100"] [200 v200 "d200"])
     (check-equal? v100 "d100")
     (check-equal? v200 "d200")
     ]
    ))

;; Test: default with expression
(test-case "ordered-map* default expression"
  (define default-v
    (+ 1 2 3))
  (match test-om
    [(ordered-map* [999 v default-v])
     (check-equal? v 6)
     ]
    ))

;; Test: pattern on default value
(test-case "ordered-map* pattern with default"
  (match test-om
    [(ordered-map* [1 (? string? s) #f])
     (check-equal? s "one")]
    [_
     (fail "should match")]
    ))

;; Test: mixed - some required, some optional
(test-case "ordered-map* mixed required and optional"
  (match test-om
    [(ordered-map* [1 v1] [3 v3] [999 v999 "missing"])
     (check-equal? v1 "one")
     (check-equal? v3 "three")
     (check-equal? v999 "missing")]
    [_
     (fail "should match")]
    ))

;; ========================================
;; Test with empty map
;; ========================================

(define empty-om (ordered-map-empty integer-compare))

(test-case "ordered-map* on empty map"
  (define matched?
    (match empty-om
      [(ordered-map* [1 _]) #t]
      [_ #f]
      ))
  (check-false matched?))

(test-case "ordered-map* on empty map with default"
  (match empty-om
    [(ordered-map* [1 v "default"])
     (check-equal? v "default")
     ]
    ))

(test-case "ordered-map-empty-pat"
  (check-true
    (match empty-om
      [(ordered-map-empty-pat) #t]
      [_ #f]
      ))
  (define matched-empty?
    (match test-om
      [(ordered-map-empty-pat) #t]
      [_ #f]
      ))
  (check-false matched-empty?))

;; ========================================
;; Test with string keys
;; ========================================

(define string-pairs
  (list
    (cons "apple" 1)
    (cons "banana" 2)
    (cons "cherry" 3)
    ))

(define string-pairs-seq
  (in-list string-pairs))

(define string-om0
  (ordered-map-empty string-compare))

(define string-om
  (for/fold ([om string-om0])
            ([kv string-pairs-seq])
    (ordered-map-set om (car kv) (cdr kv))
    ))

(test-case "ordered-map* string keys"
  (match string-om
    [(ordered-map* ["apple" a] ["cherry" c])
     (check-equal? a 1)
     (check-equal? c 3)]
    [_
     (fail "should match")]
    ))

(test-case "ordered-map* string keys with default"
  (match string-om
    [(ordered-map* ["apple" a 0] ["durian" d 99])
     (check-equal? a 1)
     (check-equal? d 99)
     ]
    ))

;; ========================================
;; Test quick initialization
;; ========================================

(test-case "make-ordered-map function"
  (define om (make-ordered-map integer-compare 1 "one" 3 "three" 5 "five"))
  (check-equal? (ordered-map-count om) 3)
  (check-equal? (ordered-map-keys om) '(1 3 5))
  (check-equal? (ordered-map-ref om 3) "three"))

(test-case "ordered-map: macro"
  (define om (ordered-map: integer-compare 1 "one" 3 "three" 5 "five"))
  (check-equal? (ordered-map-count om) 3)
  (check-equal? (ordered-map-ref om 1) "one")
  (check-equal? (ordered-map-ref om 5) "five"))

(test-case "ordered-map: empty"
  (define om (ordered-map: integer-compare))
  (define om-empty?
    (ordered-map-empty? om))
  (check-true om-empty?))

(test-case "make-ordered-map with match"
  (define om (make-ordered-map integer-compare 1 "a" 2 "b" 3 "c"))
  (match om
    [(ordered-map* [1 v1] [2 v2] [3 v3])
     (check-equal? v1 "a")
     (check-equal? v2 "b")
     (check-equal? v3 "c")]
    [_
     (fail "should match")]
    ))

(displayln "All ordered-map match tests passed!")
