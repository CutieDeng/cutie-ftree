#lang racket/base

(require rackunit
         racket/file
         racket/path
         racket/set
         "../tools/paren-style/ast.rkt"
         "../tools/paren-style/exemptions-config.rkt"
         "../tools/paren-style/rules.rkt"
         "../tools/paren-style/text.rkt"
         "../tools/paren-style/types.rkt")

(define paths0 '("."))
(define symbols0 '())
(define default-cfg
  (checker-config 3
                  #f
                  #f
                  #f
                  #f
                  #f
                  paths0
                  #f
                  #f
                  #f
                  symbols0
                  symbols0
                  symbols0))

(define (with-temp-file rel-path content proc)
  (define tmp-root (make-temporary-file "paren-style-test~a" 'directory))
  (dynamic-wind
      void
      (lambda ()
        (define target (build-path tmp-root rel-path))
        (make-directory* (path-only target))
        (call-with-output-file target
          (lambda (out)
            (display content out))
          #:exists 'replace)
        (proc target))
      (lambda ()
        (delete-directory/files tmp-root))
      ))

(test-case "max-closing-run counts full-line runs and skips string literals"
  (check-equal? (max-closing-run "(foo (bar))) baz") 3)
  (check-equal? (max-closing-run "(foo \")))))\" (bar))") 2)
  (check-equal? (max-closing-run "[(x y)]))   ") 4))

(test-case "AST semantic kinds classify for header and clause lines"
  (define (check-path path)
    (define kinds (build-ast-line-kinds path))
    (check-eq? (semantic-kind-for-line kinds 1) 'for-header)
    (check-eq? (semantic-kind-for-line kinds 2) 'for-clause)
    (check-eq? (semantic-kind-for-line kinds 3) 'generic))
  (with-temp-file
   "example.rkt"
   "(for (\n  [e (in-list xs)])\n  e)\n"
   check-path))

(test-case "AST semantic tags classify clause shape"
  (define (check-path path)
    (define kinds (build-ast-line-kinds path))
    (define head-tag 'for-head-single-seq)
    (define line-1-tags
      (semantic-tags-for-line kinds 1))
    (define has-head-tag?
      (set-member? line-1-tags head-tag))
    (check-true (set-member? (semantic-tags-for-line kinds 2)
                             'for-clause-single-seq))
    (check-true has-head-tag?))
  (with-temp-file
   "example.rkt"
   "(for (\n  [e (in-list xs)])\n  e)\n"
   check-path))

(test-case "AST semantic tags classify checker helper call shapes"
  (define (check-path path)
    (define kinds
      (build-ast-line-kinds path))
    (check-true (set-member? (semantic-tags-for-line kinds 1)
                             'check-exn-call))
    (check-true (set-member? (semantic-tags-for-line kinds 2)
                             'thunk-lambda))
    (check-true (set-member? (semantic-tags-for-line kinds 3)
                             'regexp-match-call))
    (check-true (set-member? (semantic-tags-for-line kinds 4)
                             'mk-pv-call))
    (check-true (set-member? (semantic-tags-for-line kinds 5)
                             'mk-om/kv-call))
    ) ; define check-path
  (with-temp-file
   "example.rkt"
   "(check-exn exn:fail? (lambda () (f x)))\n(lambda () (g y))\n(regexp-match? #rx\"a\" s)\n(mk-pv '(1 2 3))\n(mk-om/kv 3 values values)\n"
   check-path))

(test-case "for clause placeholder exempted only in scoped safe modules"
  (define for-clause-form "(for (\n  [_ (_)])\n  1)\n")
  (define (check-safe safe-path)
    (define empty-vs '())
    (check-equal? (scan-file safe-path default-cfg) empty-vs))
  (define (check-non-safe non-safe-path)
    (define vs (scan-file non-safe-path default-cfg))
    (check-equal? (length vs) 1))
  (with-temp-file
   (build-path "bitset" "safe.rkt")
   for-clause-form
   check-safe)
  (with-temp-file
   (build-path "bitset" "core.rkt")
   for-clause-form
   check-non-safe))

(test-case "for clause exemption is narrow to exact run-length"
  (define (check-safe safe-path)
    (define vs (scan-file safe-path default-cfg))
    (check-equal? (length vs) 1))
  (with-temp-file
   (build-path "bitset" "safe.rkt")
   "(for (\n  [_ (_)]))\n"
   check-safe))

(test-case "for header single clause is exempt"
  (define (check-path path)
    (define empty-vs '())
    (check-equal? (scan-file path default-cfg) empty-vs))
  (with-temp-file
   "example.rkt"
   "(for ([e (in-list xs)])\n  e)\n"
   check-path))

(test-case "for header exemption requires run at line end"
  (define (check-path path)
    (define vs (scan-file path default-cfg))
    (check-equal? (length vs) 1))
  (with-temp-file
   "example.rkt"
   "(for ([e (in-list xs)]) ; trailing comment\n  e)\n"
   check-path))

(test-case "for header multi clause is not exempt"
  (define (check-path path)
    (define vs (scan-file path default-cfg))
    (check-equal? (length vs) 1))
  (with-temp-file
   "example.rkt"
   "(for ([e (in-list xs)] [i (in-naturals)])\n  e)\n"
   check-path))

(test-case "safe module ->i header line exempted by AST semantic kind"
  (define (check-path path)
    (define vs (scan-file path default-cfg))
    (check-equal? (length vs) 1)
    (define first-v (car vs))
    (check-equal? (violation-line-number first-v) 4))
  (with-temp-file
   (build-path "pvector" "safe.rkt")
   "(provide/contract\n [f\n  (->i ([x any/c])\n       [result any/c])])\n"
   check-path))

(test-case "safe ->i exemption requires run at line end"
  (define (check-path path)
    (define vs (scan-file path default-cfg))
    (check-equal? (length vs) 1)
    (define line-nos
      (map violation-line-number vs))
    (check-not-false (member 4 line-nos))
    ) ; define check-path
  (with-temp-file
   (build-path "pvector" "safe.rkt")
   "(provide/contract\n [f\n  (->i ([x any/c]) ; trailing comment\n       [result any/c])])\n"
   check-path))

(test-case "contract-test call-shape exemptions are path scoped"
  (define form
    "(check-exn exn:fail? (lambda () (f x)))\n")
  (define (check-contract-test path)
    (check-equal? (scan-file path default-cfg)
                  '())
    ) ; define check-contract-test
  (define (check-other path)
    (define vs
      (scan-file path default-cfg))
    (check-equal? (length vs) 1))
  (with-temp-file
   (build-path "tests" "contract-test.rkt")
   form
   check-contract-test)
  (with-temp-file
   (build-path "tests" "other-test.rkt")
   form
   check-other))

(test-case "exemption spec validation rejects non-positive run"
  (define bad-spec
    (exemption-spec 'bad-run
                    "bad run"
                    0
                    #f #f #f #f #f #f))
  (check-exn exn:fail?
             (lambda ()
               (validate-exemption-spec! bad-spec))
             ) ; lambda
  ) ; test-case

(test-case "exemption spec validation rejects non-string path suffixes"
  (define bad-spec
    (exemption-spec 'bad-suffix
                    "bad suffixes"
                    3
                    #f #f #f #f #f
                    '(1 "ok"))
    ) ; define bad-spec
  (check-exn exn:fail?
             (lambda ()
               (validate-exemption-spec! bad-spec))
             ) ; lambda
  ) ; test-case

(test-case "exemption spec validation rejects duplicate ids"
  (define spec-a
    (exemption-spec 'dup-id
                    "dup a"
                    3
                    #f #f #f #f #f #f))
  (define spec-b
    (exemption-spec 'dup-id
                    "dup b"
                    4
                    #f #f #f #f #f #f))
  (check-exn exn:fail?
             (lambda ()
               (ensure-unique-exemption-spec-ids!
                (list spec-a spec-b))
               ) ; ensure unique ids
             ) ; lambda
  ) ; test-case
