#lang racket/base

(require racket/list
         racket/set)

(provide build-ast-line-kinds
         semantic-kind-for-line
         semantic-tags-for-line)

(define for-head-symbols
  '(for for* for/list for*/list for/vector for*/vector
        for/and for*/and for/or for*/or for/sum for*/sum
        for/product for*/product for/first for*/first
        for/last for*/last for/fold for*/fold))

(define (for-head? sym)
  (member sym for-head-symbols))

(define (mark-kind! tbl line kind)
  (when (exact-positive-integer? line)
    (hash-set! tbl line
               (set-add (hash-ref tbl line (set))
                        kind))
    ) ; when line positive
  ) ; define mark-kind!

(define (non-compound-atom? v)
  (and (not (pair? v))
       (not (vector? v))
       (not (box? v))
       (not (hash? v))
       )
  ) ; define non-compound-atom?

(define (in-seq-symbol? sym)
  (and (symbol? sym)
       (regexp-match? #px"^in-" (symbol->string sym))
       )
  ) ; define in-seq-symbol?

(define (classify-for-clause clause-stx)
  (define d (syntax->datum clause-stx))
  (cond
    [(and (list? d)
          (= (length d) 2)
          (symbol? (first d))
          (equal? (first d) '_)
          (list? (second d))
          (= (length (second d)) 1)
          (equal? (first (second d)) '_))
     'for-clause-placeholder]
    [(and (list? d)
          (= (length d) 2)
          (symbol? (first d))
          (list? (second d))
          (>= (length (second d)) 2)
          (in-seq-symbol?
           (first (second d)))
          (= (sub1
              (length (second d)))
             1)
          (non-compound-atom?
           (second (second d)))
          )
     'for-clause-single-seq]
    [(and (list? d)
          (= (length d) 2)
          (symbol? (first d))
          (list? (second d))
          (>= (length (second d)) 3)
          (in-seq-symbol?
           (first (second d)))
          (= (sub1
              (length (second d)))
             2)
          (non-compound-atom?
           (second (second d)))
          (non-compound-atom?
           (third (second d)))
          )
     'for-clause-two-atom-seq]
    [else
     #f]
    ) ; cond: classify-for-clause
  ) ; define classify-for-clause

(define (head-symbol stx)
  (define lst (syntax->list stx))
  (and lst
       (pair? lst)
       (identifier? (car lst))
       (syntax-e (car lst))
       )
  ) ; define head-symbol

(define (mark-for-clauses! stx tbl)
  (define lst (syntax->list stx))
  (when (and lst (>= (length lst) 2))
    (define clauses-stx (list-ref lst 1))
    (define clauses (syntax->list clauses-stx))
    (when clauses
      (for ([clause (in-list clauses)])
        (define line (syntax-line clause))
        (mark-kind! tbl line 'for-clause)
        (define clause-tag (classify-for-clause clause))
        (when clause-tag
          (mark-kind! tbl line clause-tag))
        ) ; for clause
      (when (= (length clauses) 1)
        (define hline (syntax-line stx))
        (define head-tag
          (case (classify-for-clause (first clauses))
            [(for-clause-placeholder) 'for-head-placeholder]
            [(for-clause-single-seq) 'for-head-single-seq]
            [(for-clause-two-atom-seq) 'for-head-two-atom-seq]
            [else #f]
            ))
        (when head-tag
          (mark-kind! tbl hline head-tag))
        ) ; when single-clause for
      ) ; when clauses
    ) ; when for head with clauses arg
  ) ; define mark-for-clauses!

(define (walk-ast stx tbl)
  (when (syntax? stx)
    (define sym (head-symbol stx))
    (define line (syntax-line stx))
    (when sym
      (cond
        [(for-head? sym)
         (mark-kind! tbl line 'for-header)
         (mark-for-clauses! stx tbl)]
        [(or (eq? sym 'match) (eq? sym 'match*))
         (mark-kind! tbl line 'match-header)]
        [(eq? sym '->i)
         (mark-kind! tbl line 'contract-header)]
        )) ; cond: semantic heads
    (define lst (syntax->list stx))
    (cond
      [lst
       (for ([child (in-list lst)])
         (walk-ast child tbl))
       ]
      [else
       (define se (syntax-e stx))
       (when (vector? se)
         (for ([x (in-vector se)])
           (walk-ast x tbl))
         )
       ] ; else: non-list syntax
      ) ; cond: recurse walk
    ) ; when syntax?
  ) ; define walk-ast

(define (file-starts-with-lang? path)
  (with-handlers ([exn:fail?
                   (lambda (_e) #f)])
    (call-with-input-file path
      (lambda (in)
        (define first-line (read-line in 'any))
        (and (string? first-line)
             (regexp-match? #px"^\\s*#lang\\b" first-line))
        ) ; and: starts with #lang
      ) ; lambda in
    ) ; call-with-input-file
  ) ; define file-starts-with-lang?

(define (walk-file-forms! path tbl #:skip-lang? [skip-lang? #f])
  (call-with-input-file path
    (lambda (in)
      (port-count-lines! in)
      (when skip-lang?
        (read-line in 'any))
      (let loop ()
        (define stx (read-syntax path in))
        (unless (eof-object? stx)
          (walk-ast stx tbl)
          (loop))
        ) ; let loop
      ) ; lambda in
    ) ; call-with-input-file
  ) ; define walk-file-forms!

(define (build-ast-line-kinds path)
  (define tbl (make-hash))
  (with-handlers ([exn:fail:read?
                   (lambda (_e)
                     ;; Best-effort fallback: accept reader forms.
                     (with-handlers ([exn:fail:read?
                                      (lambda (_e2) tbl)])
                       (parameterize ([read-accept-reader #t])
                         (walk-file-forms! path tbl #:skip-lang? #f))
                       ) ; parameterize fallback reader
                     ) ; with-handlers fallback
                   ])
    (walk-file-forms! path tbl
                      #:skip-lang? (file-starts-with-lang? path)))
  tbl)

(define (semantic-kind-for-line line-kinds line-number)
  (define kinds
    (hash-ref line-kinds line-number (set)))
  (cond
    [(set-member? kinds 'for-header) 'for-header]
    [(set-member? kinds 'for-clause) 'for-clause]
    [(set-member? kinds 'match-header) 'match-header]
    [(set-member? kinds 'contract-header) 'contract-header]
    [else 'generic]
    ) ; cond: semantic-kind
  ) ; define semantic-kind-for-line

(define (semantic-tags-for-line line-kinds line-number)
  (hash-ref line-kinds line-number (set))
  ) ; define semantic-tags-for-line
