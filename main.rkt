#lang racket/base

(module+ main
  (require racket/pretty
           "parse.rkt" "passes.rkt" "eval.rkt" "eval-cps.rkt")

  (define input
    (open-input-string (vector-ref (current-command-line-arguments) 0)))

  (define cst (parse input))
  (pretty-print cst)

  (printf "\n===\n\n")

  (define acst (alphatize cst))
  (pretty-print acst)

  (printf "\n---\n\n")
  
  (eval-Cst acst)

  (printf "\n===\n\n")

  (define dcst (infer-decls acst))
  (pretty-print dcst)

  (printf "\n===\n\n")

  (define ddcst (lex-straighten dcst))
  (pretty-print ddcst)

  (printf "\n===\n\n")

  (define lcst (introduce-dyn-env ddcst))
  (pretty-print lcst)

  (printf "\n===\n\n")

  (define ast (add-dispatch lcst))
  (pretty-print ast)

  (printf "\n===\n\n")

  (define cps (cps-convert ast))
  (pretty-print cps)

  (printf "\n---\n\n")

  (eval-CPS cps))
