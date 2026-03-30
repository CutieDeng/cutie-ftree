#lang racket/base

(require racket/cmdline
         "types.rkt")

(provide parse-cli)

(define (parse-int s flag-name)
  (define n (string->number s))
  (unless (and (integer? n) (exact? n) (>= n 0))
    (error 'check-racket-paren-style
           "~a expects a non-negative integer, got: ~a"
           flag-name
           s))
  n)

(define (parse-cli argv)
  (define max-run 3)
  (define fail-on-violation? #f)
  (define summary-only? #f)
  (define limit #f)
  (define baseline-path #f)
  (define write-baseline-path #f)
  (define show-config? #f)
  (define list-exemptions? #f)
  (define list-rules? #f)
  (define enabled-rules '())
  (define disabled-rules '())
  (define fail-path-rx-list '())
  (define input-paths '("."))

  (parameterize ([current-command-line-arguments argv])
    (command-line
     #:program "check-racket-paren-style.rkt"
     #:once-each
     [("--max-run")
      n
      "Report lines with this many consecutive closing parens/brackets before comments"
      (set! max-run (parse-int n "--max-run"))]
     [("--fail-on-violation")
      "Exit non-zero if any violation is found"
      (set! fail-on-violation? #t)]
     [("--summary-only")
      "Print grouped per-file counts instead of every violation"
      (set! summary-only? #t)]
     [("--limit")
      n
      "Limit printed rows in either detailed or summary mode"
      (set! limit (parse-int n "--limit"))]
     [("--baseline")
      path
      "Ignore violations already listed in the baseline file"
      (set! baseline-path path)]
     [("--write-baseline")
      path
      "Write the current violation set to a baseline file"
      (set! write-baseline-path path)]
     [("--show-config")
      "Print active checker configuration"
      (set! show-config? #t)]
     [("--list-exemptions")
      "Print all built-in exemption rules"
      (set! list-exemptions? #t)]
     [("--list-rules")
      "Print all built-in style rules"
      (set! list-rules? #t)]
     [("--enable-rule")
      rule-id
      "Enable only these rule ids (repeatable). Example: --enable-rule dense-closing-run"
      (set! enabled-rules (cons (string->symbol rule-id) enabled-rules))]
     [("--disable-rule")
      rule-id
      "Disable specific rule ids (repeatable)."
      (set! disabled-rules (cons (string->symbol rule-id) disabled-rules))]
     [("--fail-path-rx")
      rx
      "Only fail on violations whose file path matches this regexp (repeatable)."
      (set! fail-path-rx-list (cons (regexp rx) fail-path-rx-list))]
     #:args paths
     (unless (null? paths)
       (set! input-paths paths))))

  (checker-config max-run
                  fail-on-violation?
                  summary-only?
                  limit
                  baseline-path
                  write-baseline-path
                  input-paths
                  show-config?
                  list-exemptions?
                  list-rules?
                  (reverse enabled-rules)
                  (reverse disabled-rules)
                  (reverse fail-path-rx-list)))
