#lang racket/base

(require racket/file
         racket/list
         racket/set
         "rules.rkt"
         "text.rkt")

(provide
 read-baseline
 write-baseline!
 apply-baseline)

(define (read-baseline path)
  (define lines
    (if (file-exists? path)
        (file->lines path)
        '()
        ))
  (define acc0 (set))
  (for/fold ([acc acc0])
            ([line (in-list lines)]
             #:unless (blank-string? line))
    (set-add acc line)
    ))

(define (write-baseline! path violations)
  (define keys
    (sort (map violation->key violations) string<?))
  (make-parent-directory* path)
  (call-with-output-file path
    (lambda (out)
      (for ([key (in-list keys)])
        (fprintf out "~a\n" key)
        ))
    #:exists 'truncate/replace))

(define (apply-baseline violations baseline-set)
  (define (in-baseline? v)
    (define key (violation->key v))
    (set-member? baseline-set key))
  (for/list ([v (in-list violations)]
             #:unless (in-baseline? v))
    v))
