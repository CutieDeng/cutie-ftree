#!/usr/bin/env racket
#lang racket/base

(require "paren-style/cli.rkt"
         "paren-style/engine.rkt")

(define argv (current-command-line-arguments))
(define cfg
  (parse-cli argv))

(when (run-checker cfg)
  (exit 1))
