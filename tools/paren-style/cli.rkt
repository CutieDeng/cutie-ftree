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
      (define parsed-max-run
        (parse-int n "--max-run"))
      (set! max-run parsed-max-run)
      ]
     [("--fail-on-violation")
      "Exit non-zero if any violation is found"
      (set! fail-on-violation? #t)]
     [("--summary-only")
      "Print grouped per-file counts instead of every violation"
      (set! summary-only? #t)]
     [("--limit")
      n
      "Limit printed rows in either detailed or summary mode"
      (define parsed-limit
        (parse-int n "--limit"))
      (set! limit parsed-limit)
      ]
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
      (define rule-sym (string->symbol rule-id))
      (set! enabled-rules (cons rule-sym enabled-rules))
      ]
     [("--disable-rule")
      rule-id
      "Disable specific rule ids (repeatable)."
      (define rule-sym (string->symbol rule-id))
      (set! disabled-rules (cons rule-sym disabled-rules))
      ]
     [("--fail-path-rx")
      rx
      "Only fail on violations whose file path matches this regexp (repeatable)."
      (define rx^ (regexp rx))
      (set! fail-path-rx-list (cons rx^ fail-path-rx-list))
      ]
     #:args paths
     (unless (null? paths)
       (set! input-paths paths))
     ))

  (define enabled-rules^
    (reverse enabled-rules))
  (define disabled-rules^
    (reverse disabled-rules))
  (define fail-path-rx-list^
    (reverse fail-path-rx-list))
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
                  enabled-rules^
                  disabled-rules^
                  fail-path-rx-list^))
