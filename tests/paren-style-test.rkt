#lang racket/base

(require rackunit
         racket/file
         racket/path
         racket/set
         "../tools/paren-style/ast.rkt"
         "../tools/paren-style/rules.rkt"
         "../tools/paren-style/text.rkt"
         "../tools/paren-style/types.rkt")

(define default-cfg
  (checker-config 3
                  #f
                  #f
                  #f
                  #f
                  #f
                  '(".")
                  #f
                  #f
                  #f
                  '()
                  '()
                  '()))

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
        (delete-directory/files tmp-root))))

(test-case "max-closing-run counts full-line runs and skips string literals"
  (check-equal? (max-closing-run "(foo (bar))) baz") 3)
  (check-equal? (max-closing-run "(foo \")))))\" (bar))") 2)
  (check-equal? (max-closing-run "[(x y)]))   ") 4))

(test-case "AST semantic kinds classify for header and clause lines"
  (with-temp-file
   "example.rkt"
   "(for (\n  [e (in-list xs)])\n  e)\n"
   (lambda (path)
     (define kinds (build-ast-line-kinds path))
     (check-eq? (semantic-kind-for-line kinds 1) 'for-header)
     (check-eq? (semantic-kind-for-line kinds 2) 'for-clause)
     (check-eq? (semantic-kind-for-line kinds 3) 'generic))))

(test-case "AST semantic tags classify clause shape"
  (with-temp-file
   "example.rkt"
   "(for (\n  [e (in-list xs)])\n  e)\n"
   (lambda (path)
     (define kinds (build-ast-line-kinds path))
     (check-true (set-member? (semantic-tags-for-line kinds 2)
                              'for-clause-single-seq))
     (check-true (set-member? (semantic-tags-for-line kinds 1)
                              'for-head-single-seq)))))

(test-case "for clause placeholder exempted only in scoped safe modules"
  (define for-clause-form "(for (\n  [_ (_)])\n  1)\n")
  (with-temp-file
   (build-path "bitset" "safe.rkt")
   for-clause-form
   (lambda (safe-path)
     (check-equal? (scan-file safe-path default-cfg) '())))
  (with-temp-file
   (build-path "bitset" "core.rkt")
   for-clause-form
   (lambda (non-safe-path)
     (check-equal? (length (scan-file non-safe-path default-cfg)) 1))))

(test-case "for clause exemption is narrow to exact run-length"
  (with-temp-file
   (build-path "bitset" "safe.rkt")
   "(for (\n  [_ (_)]))\n"
   (lambda (safe-path)
     (check-equal? (length (scan-file safe-path default-cfg)) 1))))

(test-case "for header single clause is exempt"
  (with-temp-file
   "example.rkt"
   "(for ([e (in-list xs)])\n  e)\n"
   (lambda (path)
     (check-equal? (scan-file path default-cfg) '()))))

(test-case "for header multi clause is not exempt"
  (with-temp-file
   "example.rkt"
   "(for ([e (in-list xs)] [i (in-naturals)])\n  e)\n"
   (lambda (path)
     (check-equal? (length (scan-file path default-cfg)) 1))))

(test-case "safe module ->i header line exempted by AST semantic kind"
  (with-temp-file
   (build-path "pvector" "safe.rkt")
   "(provide/contract\n [f\n  (->i ([x any/c])\n       [result any/c])])\n"
   (lambda (path)
     (define vs (scan-file path default-cfg))
     (check-equal? (length vs) 1)
     (check-equal? (violation-line-number (car vs)) 4))))
