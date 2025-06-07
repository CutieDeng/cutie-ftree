#lang racket

(require "ral-0.rkt")
(provide (all-from-out "ral-0.rkt"))

(define-match-expander ral (#%plain-lambda (stx)
  (syntax-case stx (length unlength atom)
    [(_ (hd length sz))
      (syntax (? (lambda (s) (= (ral-length s) sz)) hd))
    ]
    [(_ (hd unlength))
      (syntax (? ral? hd))
    ]
    [(_ (hd atom))
      (syntax (? (lambda (s) (= (ral-length s) 1)) (app ral-viewl hd)))]
    [(self (hd length sz) rest ...)
      (syntax (? (lambda (s) (>= (ral-length s) sz)) (app (lambda (s) (let-values ([(lhs rhs) (ral-split-at s sz)]) (cons lhs rhs))) (cons hd (self rest ...)))))
    ]
    [(self (hd unlength) rest ... (rhd length sz)) 
      (syntax (? (lambda (s) (>= (ral-length s) sz)) (app (lambda (s) (let-values ([(rhs lhs) (ral-split-at-right s sz)]) (cons lhs rhs))) (cons (self (hd unlength) rest ...) rhd))))
    ]
    [(_ (hd atom) rest ...)
      (syntax (app (lambda (s) (let-values ([(v ft) (ral-dropl s)]) (cons v ft))) (cons (? (lambda (x) x) hd) (self rest ...))))
    ]
    [(_ (hd unlength) rest ... (rhd atom))
      (syntax (app (lambda (s) (let-values ([(v ft) (ral-dropr s)]) (cons v ft))) (cons (? (lambda (x) x) rhd) (self (hd unlength) rest ...))))
    ]
    [(_ (_ unlength) rest ... (_ unlength))
      (error 'unlength "unsupport complex unlength matching")
    ]
  )))

(provide ral)
