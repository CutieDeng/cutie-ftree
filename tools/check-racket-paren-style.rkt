#!/usr/bin/env racket
#lang racket/base

(require "paren-style/cli.rkt"
         "paren-style/engine.rkt")

(define cfg
  (parse-cli (current-command-line-arguments)))

(when (run-checker cfg)
  (exit 1))
