#lang racket/base

(provide built-in-exemption-specs
         (struct-out exemption-spec)
         validate-exemption-spec!
         ensure-unique-exemption-spec-ids!)

;; Data-driven exemption specs. Keep each entry narrow and explicit.
;; Fields:
;; 1. id symbol
;; 2. description string
;; 3. exact run-length integer
;; 4. optional regular expression (anchored full-line match; #f means any)
;; 5. optional path regular expression (#f means global)
;; 6. optional semantic-kind symbol (#f means any)
;; 7. optional ast-tag symbol (#f means any)
;; 8. optional requires-run-at-line-end? boolean (#f means no constraint)
;; 9. optional exact path suffix list (e.g. '("tests/contract-test.rkt"))
;;    #f means no suffix constraint.
(struct exemption-spec
  (id
   description
   exact-run
   line-rx
   path-rx
   semantic-kind
   ast-tag
   requires-run-at-line-end?
   path-suffixes)
  #:transparent)

(define safe-module-suffixes
  '("bitset/safe.rkt"
    "interval-tree/safe.rkt"
    "ordered-map/safe.rkt"
    "priority-queue/safe.rkt"
    "pvector/safe.rkt"
    "text/safe.rkt"))

(define contract-test-suffixes
  '("tests/contract-test.rkt"))

(define (validate-exemption-spec! spec)
  (define id
    (exemption-spec-id spec))
  (define run
    (exemption-spec-exact-run spec))
  (define line-rx
    (exemption-spec-line-rx spec))
  (define path-rx
    (exemption-spec-path-rx spec))
  (define semantic-kind
    (exemption-spec-semantic-kind spec))
  (define ast-tag
    (exemption-spec-ast-tag spec))
  (define requires-run-at-line-end?
    (exemption-spec-requires-run-at-line-end? spec))
  (define path-suffixes
    (exemption-spec-path-suffixes spec))
  (unless (and (integer? run)
               (> run 0))
    (error 'check-racket-paren-style
           "invalid exemption exact-run for id ~a: ~a"
           id
           run))
  (unless (or (not line-rx)
              (regexp? line-rx))
    (error 'check-racket-paren-style
           "invalid exemption line-rx for id ~a: ~a"
           id
           line-rx))
  (unless (or (not path-rx)
              (regexp? path-rx))
    (error 'check-racket-paren-style
           "invalid exemption path-rx for id ~a: ~a"
           id
           path-rx))
  (unless (or (not semantic-kind)
              (symbol? semantic-kind))
    (error 'check-racket-paren-style
           "invalid exemption semantic-kind for id ~a: ~a"
           id
           semantic-kind))
  (unless (or (not ast-tag)
              (symbol? ast-tag))
    (error 'check-racket-paren-style
           "invalid exemption ast-tag for id ~a: ~a"
           id
           ast-tag))
  (unless (or (eq? requires-run-at-line-end? #t)
              (eq? requires-run-at-line-end? #f))
    (error 'check-racket-paren-style
           "invalid exemption requires-run-at-line-end? for id ~a: ~a"
           id
           requires-run-at-line-end?))
  (unless (or (not path-suffixes)
              (and (list? path-suffixes)
                   (andmap string? path-suffixes))
              )
    (error 'check-racket-paren-style
           "invalid exemption path-suffixes for id ~a: ~a"
           id
           path-suffixes))
  spec
  ) ; define validate-exemption-spec!

(define (ensure-unique-exemption-spec-ids! specs)
  (define seen (make-hash))
  (for ([spec (in-list specs)])
    (define id (exemption-spec-id spec))
    (when (hash-has-key? seen id)
      (error 'check-racket-paren-style
             "duplicate exemption id: ~a"
             id))
    (hash-set! seen id #t))
  specs
  ) ; define ensure-unique-exemption-spec-ids!

(define (make-run3-tag-specs group desc-template semantic-kind ast-tags suffixes)
  (for/list ([ast-tag (in-list ast-tags)])
    (define id
      (string->symbol
       (format "~a-~a-run3"
               group
               ast-tag))
      ) ; define id
    (define description
      (format desc-template ast-tag))
    (exemption-spec
     id
     description
     3
     #f #f
     semantic-kind
     ast-tag
     #t
     suffixes))
  ) ; define make-run3-tag-specs

(define (make-contract-test-run-specs key desc-template runs ast-tag)
  (for/list ([run (in-list runs)])
    (define id
      (string->symbol
       (format "contract-test-~a-run~a"
               key
               run))
      ) ; define id
    (define description
      (format desc-template run))
    (exemption-spec
     id
     description
     run
     #f #f #f
     ast-tag
     #f
     contract-test-suffixes))
  ) ; define make-contract-test-run-specs

(define built-in-exemption-specs
  (let* ([specs0
          (append
           (make-run3-tag-specs
            "for-head"
            "Allow for-header tag `~a` at run=3."
            'for-header
            '(for-head-placeholder
              for-head-single-seq
              for-head-two-atom-seq)
            #f)
           (make-run3-tag-specs
            "safe-for-clause"
            "Allow for-clause tag `~a` at run=3 in safe modules."
            'for-clause
            '(for-clause-placeholder
              for-clause-single-seq
              for-clause-two-atom-seq)
            safe-module-suffixes)
           (list
            (exemption-spec
             'safe-contract-arrow-header
             "Allow `->i` contract header lines at run=3 in safe modules."
             3 #f #f
             'contract-header
             'contract-header
             #t
             safe-module-suffixes))
           (make-contract-test-run-specs
            "mk-pv"
            "Allow `mk-pv` helper lines at run=~a in contract test."
            '(3 4)
            'mk-pv-call)
           (make-contract-test-run-specs
            "mk-om"
            "Allow `mk-om` helper lines at run=~a in contract test."
            '(3 4)
            'mk-om-call)
           (make-contract-test-run-specs
            "mk-om/kv"
            "Allow `mk-om/kv` helper lines at run=~a in contract test."
            '(3 4)
            'mk-om/kv-call)
           (make-contract-test-run-specs
            "check-exn"
            "Allow check-exn/check-not-exn wrapper lines at run=~a in contract test."
            '(3 4 5)
            'check-exn-call)
           (make-contract-test-run-specs
            "check-not-exn"
            "Allow check-not-exn wrapper lines at run=~a in contract test."
            '(3 4 5)
            'check-not-exn-call)
           (make-contract-test-run-specs
            "thunk-lambda"
            "Allow thunk lambda call lines at run=~a in contract test."
            '(3 4 5 6)
            'thunk-lambda)
           (make-contract-test-run-specs
            "blame-regexp"
            "Allow blame-message regexp checks at run=~a in contract test."
            '(4)
            'regexp-match-call))
         ]
         [specs1
          (map validate-exemption-spec!
               specs0)]
         [specs2
          (ensure-unique-exemption-spec-ids!
           specs1)
          ])
    specs2)
  ) ; define built-in-exemption-specs
