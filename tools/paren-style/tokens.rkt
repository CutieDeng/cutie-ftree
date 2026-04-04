#lang racket/base

(require racket/file
         racket/string
         syntax-color/racket-lexer)

(provide
 (struct-out line-run-record)
 build-token-line-runs)

(struct line-run-record
  (run
   start-column
   end-column
   at-line-end?)
  #:transparent)

(define (closing-char? ch)
  (define close-round?
    (char=? ch #\)))
  (define close-square?
    (char=? ch #\]))
  (or close-round?
      close-square?))

(define (ensure-line-default! tbl line)
  (unless (hash-has-key? tbl line)
    (define zero-rec
      (line-run-record 0 #f #f #f))
    (define target-line line)
    (hash-set! tbl target-line zero-rec)
    ))

(define (update-line-best! tbl line run start-col end-col)
  (ensure-line-default! tbl line)
  (define old (hash-ref tbl line))
  (define old-run (line-run-record-run old))
  (when (> run old-run)
    (define rec
      (line-run-record run start-col end-col #f))
    (define target-line line)
    (hash-set! tbl target-line rec)
    ))

(define (line-end-column line)
  (string-length line))

(define (finalize-line-end-tags! tbl lines)
  (define line-count (length lines))
  (define stop-line
    (add1 line-count))
  (define line-seq
    (in-range 1 stop-line))
  (for ([line-no line-seq])
    (ensure-line-default! tbl line-no)
    (define old-rec
      (hash-ref tbl line-no))
    (define run (line-run-record-run old-rec))
    (define start-col (line-run-record-start-column old-rec))
    (define end-col (line-run-record-end-column old-rec))
    (define idx
      (sub1 line-no))
    (define line-str
      (list-ref lines idx))
    (define eol-col (line-end-column line-str))
    (define at-line-end?
      (and (exact-positive-integer? run)
           end-col
           (= end-col eol-col)
           ))
    (define new-rec
      (line-run-record run start-col end-col at-line-end?))
    (define target-line line-no)
    (hash-set! tbl target-line new-rec)
    ))

(define (build-token-line-runs path lines)
  ;; Compute max run-lengths from lexical tokens instead of raw text.
  ;; This provides precise source positions and avoids counting delimiters
  ;; inside strings/comments as structural closing runs.
  (define src (file->string path))
  (define in (open-input-string src))
  (define line->best (make-hash))
  (define line 1)
  (define col 1)
  (define current-run 0)
  (define current-run-start-col #f)

  (define (consume-char ch structural-token?)
    (cond
      [(char=? ch #\newline)
       (set! current-run 0)
       (set! current-run-start-col #f)
       (set! line (add1 line))
       (set! col 1)]
      [else
       (define structural-closer?
         (and structural-token?
              (closing-char? ch)
              ))
       (define closer?
         structural-closer?)
       (if closer?
           (begin
             (when (= current-run 0)
               (set! current-run-start-col col))
             (set! current-run (add1 current-run))
             (update-line-best! line->best
                                line
                                current-run
                                current-run-start-col
                                col))
           (begin
             (set! current-run 0)
             (set! current-run-start-col #f)
             ))
       (define next-col
         (add1 col))
       (set! col next-col)
       ]
      )
    )

  (let loop ()
    (define-values (lexeme type _paren _start _end)
      (racket-lexer in))
    (unless (eq? type 'eof)
      (define structural-token?
        (eq? type 'parenthesis))
      (for ([ch (in-string lexeme)])
        (consume-char ch structural-token?))
      (loop)
      ))

  (finalize-line-end-tags! line->best lines)
  line->best)
