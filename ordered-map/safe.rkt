#lang racket/base

(require racket/contract racket/generator)
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
;; Returns a wrapped ordered-map that enforces contracts on all operations
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
      (define key-proj-out ((contract-late-neg-projection key-ctc)
                            (blame-add-context blame "a key of")))
      (define val-proj-out ((contract-late-neg-projection val-ctc)
                            (blame-add-context blame "a value of")))
      (define key-proj-in ((contract-late-neg-projection key-ctc)
                           (blame-add-context (blame-swap blame) "a key of")))
      (define val-proj-in ((contract-late-neg-projection val-ctc)
                           (blame-add-context (blame-swap blame) "a value of")))
      (lambda (v neg-party)
        (unless (ordered-map? v)
          (raise-blame-error blame v #:missing-party neg-party
            '(expected: "ordered-map?" given: "~e") v))
        ;; Verify existing entries
        (for ([kv (in-ordered-map v)])
          (key-proj-out (car kv) neg-party)
          (val-proj-out (cdr kv) neg-party))
        ;; Return wrapped ordered-map
        (contracted-ordered-map v key-proj-out val-proj-out key-proj-in val-proj-in neg-party)))))

;; Wrapper struct for contracted ordered-map
(struct contracted-ordered-map (om key-proj-out val-proj-out key-proj-in val-proj-in neg-party)
  #:transparent
  #:property prop:sequence
  (lambda (com)
    (in-generator
      (for ([kv (in-ordered-map (contracted-ordered-map-om com))])
        (yield (cons ((contracted-ordered-map-key-proj-out com) (car kv) (contracted-ordered-map-neg-party com))
                     ((contracted-ordered-map-val-proj-out com) (cdr kv) (contracted-ordered-map-neg-party com)))))))
  #:methods gen:custom-write
  [(define (write-proc com port mode)
     (fprintf port "#<contracted-ordered-map:~a>" (ordered-map-count (contracted-ordered-map-om com))))])

;; Helper: unwrap if contracted
(define (unwrap-om v)
  (if (contracted-ordered-map? v) (contracted-ordered-map-om v) v))

;; Helper: rewrap result with same contract
(define (rewrap-om com result)
  (if (contracted-ordered-map? com)
      (contracted-ordered-map result
        (contracted-ordered-map-key-proj-out com)
        (contracted-ordered-map-val-proj-out com)
        (contracted-ordered-map-key-proj-in com)
        (contracted-ordered-map-val-proj-in com)
        (contracted-ordered-map-neg-party com))
      result))

;; Helper: check key on input
(define (check-key-in com key)
  (if (contracted-ordered-map? com)
      ((contracted-ordered-map-key-proj-in com) key (contracted-ordered-map-neg-party com))
      key))

;; Helper: check value on input
(define (check-val-in com val)
  (if (contracted-ordered-map? com)
      ((contracted-ordered-map-val-proj-in com) val (contracted-ordered-map-neg-party com))
      val))

;; Helper: check key-value pair on output
(define (check-kv-out com kv)
  (if (and kv (contracted-ordered-map? com))
      (cons ((contracted-ordered-map-key-proj-out com) (car kv) (contracted-ordered-map-neg-party com))
            ((contracted-ordered-map-val-proj-out com) (cdr kv) (contracted-ordered-map-neg-party com)))
      kv))

;; Contracted ordered-map operations
(define (com-ref om key [default (lambda () (error "key not found" key))])
  (define result (ordered-map-ref (unwrap-om om) (check-key-in om key) default))
  (if (contracted-ordered-map? om)
      ((contracted-ordered-map-val-proj-out om) result (contracted-ordered-map-neg-party om))
      result))

(define (com-set om key val)
  (rewrap-om om (ordered-map-set (unwrap-om om) (check-key-in om key) (check-val-in om val))))

(define (com-insert om key val replace?)
  (rewrap-om om (ordered-map-insert (unwrap-om om) (check-key-in om key) (check-val-in om val) replace?)))

(define (com-delete om key)
  (define-values (result deleted) (ordered-map-delete (unwrap-om om) (check-key-in om key)))
  (values (rewrap-om om result) (check-kv-out om deleted)))

(define (com-query om key)
  (check-kv-out om (ordered-map-query (unwrap-om om) (check-key-in om key))))

(define (com-query-weak om key mode)
  (check-kv-out om (ordered-map-query-weak (unwrap-om om) (check-key-in om key) mode)))

(define (com-min om)
  (check-kv-out om (ordered-map-min (unwrap-om om))))

(define (com-max om)
  (check-kv-out om (ordered-map-max (unwrap-om om))))

(define (com-count om)
  (ordered-map-count (unwrap-om om)))

(define (com-empty? om)
  (ordered-map-empty? (unwrap-om om)))

(define (com-has-key? om key)
  (ordered-map-has-key? (unwrap-om om) (check-key-in om key)))

;; Type check that accepts both
(define (com? v)
  (or (ordered-map? v) (contracted-ordered-map? v)))

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
(provide ordered-mapof contracted-ordered-map?)

;; Contracted operations (work with both ordered-map and contracted-ordered-map)
(provide
  (rename-out
    [com? ordered-map?*]
    [com-ref ordered-map-ref*]
    [com-set ordered-map-set*]
    [com-insert ordered-map-insert*]
    [com-delete ordered-map-delete*]
    [com-query ordered-map-query*]
    [com-query-weak ordered-map-query-weak*]
    [com-min ordered-map-min*]
    [com-max ordered-map-max*]
    [com-count ordered-map-count*]
    [com-empty? ordered-map-empty?*]
    [com-has-key? ordered-map-has-key?*]))
