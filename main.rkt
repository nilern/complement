#lang racket/base

(module+ main
  (require "parse.rkt")
  (require "eval.rkt")

  (define input
    (open-input-string (vector-ref (current-command-line-arguments) 0)))
  (eval-Core (parse input)))
