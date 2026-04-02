#lang racket/base

(provide
 (struct-out checker-config)
 (struct-out line-context)
 (struct-out rule)
 (struct-out exemption)
 (struct-out violation))

(struct checker-config
  (max-run
   fail-on-violation?
   summary-only?
   limit
   baseline-path
   write-baseline-path
   input-paths
   show-config?
   list-exemptions?
   list-rules?
   enabled-rules
   disabled-rules
   fail-path-rx-list)
  #:transparent)

(struct line-context
  (path
   line-number
   raw-line
   code-prefix
   run-length
   semantic-kind
   semantic-tags)
  #:transparent)

(struct rule
  (id
   description
   predicate)
  #:transparent)

(struct exemption
  (id
   description
   predicate)
  #:transparent)

(struct violation
  (path
   line-number
   run-length
   line-text
   rule-id)
  #:transparent)
