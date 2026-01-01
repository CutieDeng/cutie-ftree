#lang racket/base

(require racket/contract racket/generator)
(require "../pvector.rkt")

;; ========================================
;; Contract Definitions
;; ========================================

(define pvector/c
  (flat-named-contract 'pvector pvector?))

(define index/c
  (flat-named-contract 'index exact-nonnegative-integer?))

;; pvectorof: like listof, checks all elements satisfy the contract
;; Returns a wrapped pvector that enforces contracts on all operations
(define (pvectorof elem/c)
  (define elem-ctc (coerce-contract 'pvectorof elem/c))
  (make-contract
    #:name (build-compound-type-name 'pvectorof elem-ctc)
    #:first-order (lambda (v)
      (and (pvector? v)
           (for/and ([e (in-pvector v)])
             ((contract-first-order elem-ctc) e))))
    #:late-neg-projection (lambda (blame)
      (define elem-proj ((contract-late-neg-projection elem-ctc)
                         (blame-add-context blame "an element of")))
      (define elem-proj-in ((contract-late-neg-projection elem-ctc)
                            (blame-add-context (blame-swap blame) "an element of")))
      (lambda (v neg-party)
        (unless (pvector? v)
          (raise-blame-error blame v #:missing-party neg-party
            '(expected: "pvector?" given: "~e") v))
        ;; Verify existing elements
        (for ([e (in-pvector v)])
          (elem-proj e neg-party))
        ;; Return wrapped pvector
        (contracted-pvector v elem-proj elem-proj-in neg-party)))))

;; Wrapper struct for contracted pvector
(struct contracted-pvector (pv elem-proj-out elem-proj-in neg-party)
  #:transparent
  #:property prop:sequence
  (lambda (cpv)
    (in-generator
      (for ([e (in-pvector (contracted-pvector-pv cpv))])
        (yield ((contracted-pvector-elem-proj-out cpv) e (contracted-pvector-neg-party cpv))))))
  #:methods gen:custom-write
  [(define (write-proc cpv port mode)
     (fprintf port "#<contracted-pvector:~a>" (pvector-length (contracted-pvector-pv cpv))))])

;; Helper: unwrap if contracted
(define (unwrap-pv v)
  (if (contracted-pvector? v) (contracted-pvector-pv v) v))

;; Helper: rewrap result with same contract
(define (rewrap-pv cpv result)
  (if (contracted-pvector? cpv)
      (contracted-pvector result
        (contracted-pvector-elem-proj-out cpv)
        (contracted-pvector-elem-proj-in cpv)
        (contracted-pvector-neg-party cpv))
      result))

;; Helper: check element on input
(define (check-elem-in cpv elem)
  (if (contracted-pvector? cpv)
      ((contracted-pvector-elem-proj-in cpv) elem (contracted-pvector-neg-party cpv))
      elem))

;; Helper: check element on output
(define (check-elem-out cpv elem)
  (if (contracted-pvector? cpv)
      ((contracted-pvector-elem-proj-out cpv) elem (contracted-pvector-neg-party cpv))
      elem))

;; Contracted pvector operations
(define (cpv-ref pv idx)
  (check-elem-out pv (pvector-ref (unwrap-pv pv) idx)))

(define (cpv-set pv idx val)
  (rewrap-pv pv (pvector-set (unwrap-pv pv) idx (check-elem-in pv val))))

(define (cpv-cons-left pv val)
  (rewrap-pv pv (pvector-cons-left (unwrap-pv pv) (check-elem-in pv val))))

(define (cpv-cons-right pv val)
  (rewrap-pv pv (pvector-cons-right (unwrap-pv pv) (check-elem-in pv val))))

(define (cpv-pop-left pv)
  (define-values (elem rest) (pvector-pop-left (unwrap-pv pv)))
  (values (check-elem-out pv elem) (rewrap-pv pv rest)))

(define (cpv-pop-right pv)
  (define-values (elem rest) (pvector-pop-right (unwrap-pv pv)))
  (values (check-elem-out pv elem) (rewrap-pv pv rest)))

(define (cpv-view-left pv)
  (check-elem-out pv (pvector-view-left (unwrap-pv pv))))

(define (cpv-view-right pv)
  (check-elem-out pv (pvector-view-right (unwrap-pv pv))))

(define (cpv-insert pv idx val)
  (rewrap-pv pv (pvector-insert (unwrap-pv pv) idx (check-elem-in pv val))))

(define (cpv-delete pv idx)
  (define-values (rest elem) (pvector-delete (unwrap-pv pv) idx))
  (values (rewrap-pv pv rest) (check-elem-out pv elem)))

(define (cpv-length pv)
  (pvector-length (unwrap-pv pv)))

(define (cpv-empty? pv)
  (pvector-empty? (unwrap-pv pv)))

(define (cpv-take pv n)
  (rewrap-pv pv (pvector-take (unwrap-pv pv) n)))

(define (cpv-drop pv n)
  (rewrap-pv pv (pvector-drop (unwrap-pv pv) n)))

(define (cpv-append pv1 pv2)
  ;; Use pv1's contract if it has one, otherwise pv2's
  (define result (pvector-append (unwrap-pv pv1) (unwrap-pv pv2)))
  (cond
    [(contracted-pvector? pv1) (rewrap-pv pv1 result)]
    [(contracted-pvector? pv2) (rewrap-pv pv2 result)]
    [else result]))

;; Type check that accepts both
(define (cpv? v)
  (or (pvector? v) (contracted-pvector? v)))

;; ========================================
;; Contract-Protected Exports
;; ========================================

(provide/contract
  ;; Type predicates
  [pvector? (-> any/c boolean?)]
  [pvector-empty? (-> any/c boolean?)]

  ;; Construction
  [pvector-empty (-> pvector/c)]

  ;; Length
  [pvector-length (-> pvector/c index/c)]

  ;; Element access with dependent contracts
  [pvector-ref
    (->i ([pv pvector/c]
          [idx (pv) (and/c index/c (</c (pvector-length pv)))])
         [result any/c])]

  [pvector-set
    (->i ([pv pvector/c]
          [idx (pv) (and/c index/c (</c (pvector-length pv)))]
          [val any/c])
         [result pvector/c])]

  ;; Add/remove from ends
  [pvector-cons-left (-> pvector/c any/c pvector/c)]
  [pvector-cons-right (-> pvector/c any/c pvector/c)]

  [pvector-pop-left
    (-> (and/c pvector/c (not/c pvector-empty?))
        (values any/c pvector/c))]

  [pvector-pop-right
    (-> (and/c pvector/c (not/c pvector-empty?))
        (values any/c pvector/c))]

  ;; View ends (non-destructive)
  [pvector-view-left
    (-> (and/c pvector/c (not/c pvector-empty?)) any/c)]

  [pvector-view-right
    (-> (and/c pvector/c (not/c pvector-empty?)) any/c)]

  ;; Concatenation
  [pvector-append (-> pvector/c pvector/c pvector/c)]

  ;; Split operations
  [pvector-split
    (->i ([pv (and/c pvector/c (not/c pvector-empty?))]
          [idx (pv) (and/c index/c (</c (pvector-length pv)))])
         (values [left pvector/c] [mid any/c] [right pvector/c]))]

  [pvector-split-at
    (->i ([pv pvector/c]
          [pos (pv) (and/c index/c (<=/c (pvector-length pv)))])
         (values [left pvector/c] [right pvector/c]))]

  [pvector-split-at-right
    (->i ([pv pvector/c]
          [pos (pv) (and/c index/c (<=/c (pvector-length pv)))])
         (values [right pvector/c] [left pvector/c]))]

  ;; Slice operations
  [pvector-take
    (->i ([pv pvector/c]
          [n (pv) (and/c index/c (<=/c (pvector-length pv)))])
         [result pvector/c])]

  [pvector-drop
    (->i ([pv pvector/c]
          [n (pv) (and/c index/c (<=/c (pvector-length pv)))])
         [result pvector/c])]

  [pvector-take-right
    (->i ([pv pvector/c]
          [n (pv) (and/c index/c (<=/c (pvector-length pv)))])
         [result pvector/c])]

  [pvector-drop-right
    (->i ([pv pvector/c]
          [n (pv) (and/c index/c (<=/c (pvector-length pv)))])
         [result pvector/c])]

  [pvector-copy
    (->i ([pv pvector/c]
          [start (pv) (and/c index/c (<=/c (pvector-length pv)))]
          [end (pv start) (and/c index/c (<=/c (pvector-length pv)) (>=/c start))])
         [result pvector/c])]

  ;; Insert and delete
  [pvector-insert
    (->i ([pv pvector/c]
          [idx (pv) (and/c index/c (<=/c (pvector-length pv)))]
          [val any/c])
         [result pvector/c])]

  [pvector-delete
    (->i ([pv (and/c pvector/c (not/c pvector-empty?))]
          [idx (pv) (and/c index/c (</c (pvector-length pv)))])
         (values [result pvector/c] [deleted any/c]))]

  ;; Conversion
  [vector->pvector (-> vector? pvector/c)]
  [pvector->vector (-> pvector/c vector?)]
  [list->pvector (-> list? pvector/c)]
  [pvector->list (-> pvector/c list?)]

  ;; Sequence (generator-based)
  [in-pvector (-> pvector/c sequence?)]
  [in-pvector-reverse (-> pvector/c sequence?)]
  [in-pvector-indexed (-> pvector/c sequence?)]

  ;; Sequence (index-based)
  [in-pvector/index (-> pvector/c sequence?)]
)

;; Comprehensions (syntax, no contracts needed)
(require (only-in "../pvector.rkt" for/pvector for*/pvector pvector pvector*))
(provide for/pvector for*/pvector)

;; Match expanders (syntax)
(provide pvector pvector*)

;; Parameterized contracts
(provide pvectorof contracted-pvector?)

;; Contracted operations (work with both pvector and contracted-pvector)
(provide
  (rename-out
    [cpv? pvector?*]           ;; accepts both types
    [cpv-ref pvector-ref*]
    [cpv-set pvector-set*]
    [cpv-cons-left pvector-cons-left*]
    [cpv-cons-right pvector-cons-right*]
    [cpv-pop-left pvector-pop-left*]
    [cpv-pop-right pvector-pop-right*]
    [cpv-view-left pvector-view-left*]
    [cpv-view-right pvector-view-right*]
    [cpv-insert pvector-insert*]
    [cpv-delete pvector-delete*]
    [cpv-length pvector-length*]
    [cpv-empty? pvector-empty?*]
    [cpv-take pvector-take*]
    [cpv-drop pvector-drop*]
    [cpv-append pvector-append*]))
