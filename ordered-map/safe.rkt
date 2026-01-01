#lang racket/base

(require racket/contract)
(require "../ordered-map.rkt")
(require "../comparator.rkt")

;; ========================================
;; Contract Definitions
;; ========================================

(define ordered-map/c
  (flat-named-contract 'ordered-map ordered-map?))

(define query-mode/c
  (flat-named-contract 'query-mode (or/c '< '<= '> '>=)))

;; ordered-mapof: like hash/c, checks all keys and values satisfy contracts
(define (ordered-mapof key/c value/c)
  (define key-ctc (coerce-contract 'ordered-mapof key/c))
  (define val-ctc (coerce-contract 'ordered-mapof value/c))
  (make-contract
    #:name (build-compound-type-name 'ordered-mapof key-ctc val-ctc)
    #:first-order (lambda (v)
      (and (ordered-map? v)
           (for/and ([kv (in-ordered-map v)])
             (and ((contract-first-order key-ctc) (car kv))
                  ((contract-first-order val-ctc) (cdr kv))))))
    #:late-neg-projection (lambda (blame)
      (define key-proj ((contract-late-neg-projection key-ctc)
                        (blame-add-context blame "a key of")))
      (define val-proj ((contract-late-neg-projection val-ctc)
                        (blame-add-context blame "a value of")))
      (lambda (v neg-party)
        (unless (ordered-map? v)
          (raise-blame-error blame v #:missing-party neg-party
            '(expected: "ordered-map?" given: "~e") v))
        ;; Check all entries, rebuild the map with contracted values
        (define cmp (ordered-map-cmp-fn v))
        (for/fold ([m (ordered-map-empty cmp)]) ([kv (in-ordered-map v)])
          (define k (key-proj (car kv) neg-party))
          (define val (val-proj (cdr kv) neg-party))
          (ordered-map-insert m k val #t))))))

;; ========================================
;; Contract-Protected Exports
;; ========================================

(provide/contract
  ;; Type predicate
  [ordered-map? (-> any/c boolean?)]
  [ordered-map-empty? (-> ordered-map/c boolean?)]

  ;; Construction
  [ordered-map-empty (-> (comparator/c any/c) ordered-map/c)]

  ;; Size
  [ordered-map-count (-> ordered-map/c exact-nonnegative-integer?)]

  ;; Min/Max access
  [ordered-map-min (-> ordered-map/c (or/c #f pair?))]
  [ordered-map-max (-> ordered-map/c (or/c #f pair?))]

  ;; Query
  [ordered-map-query (-> ordered-map/c any/c (or/c #f pair?))]

  [ordered-map-query-weak
    (-> ordered-map/c any/c query-mode/c (or/c #f pair?))]

  [ordered-map-has-key? (-> ordered-map/c any/c boolean?)]

  ;; Dict-style access
  [ordered-map-ref
    (->* (ordered-map/c any/c) (any/c) any/c)]

  [ordered-map-set
    (-> ordered-map/c any/c any/c ordered-map/c)]

  ;; Insert/Delete
  [ordered-map-insert
    (-> ordered-map/c any/c any/c boolean? ordered-map/c)]

  [ordered-map-delete
    (-> ordered-map/c any/c (values ordered-map/c (or/c #f pair?)))]

  ;; Collection operations
  [ordered-map-keys (-> ordered-map/c (listof any/c))]
  [ordered-map-values (-> ordered-map/c (listof any/c))]

  ;; Sequence (generator-based)
  [in-ordered-map (-> ordered-map/c sequence?)]
  [in-ordered-map-reverse (-> ordered-map/c sequence?)]
  [in-ordered-map-keys (-> ordered-map/c sequence?)]
  [in-ordered-map-values (-> ordered-map/c sequence?)]

  ;; Sequence (lazy query-based)
  [in-ordered-map/lazy (-> ordered-map/c sequence?)]
)

;; Comprehensions (syntax, no contracts needed)
(require (only-in "../ordered-map.rkt" for/ordered-map for*/ordered-map ordered-map-empty-pat ordered-map-pairs))
(provide for/ordered-map for*/ordered-map)

;; Match expanders (syntax)
(provide ordered-map-empty-pat ordered-map-pairs)

;; Parameterized contracts
(provide ordered-mapof)
