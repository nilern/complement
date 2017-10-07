#lang racket/base

(module+ main
  (require racket/pretty
           nanopass/base
           "langs.rkt"
           "parse.rkt" "cst-passes.rkt" "ast-passes.rkt" "cps-passes.rkt" "cpcps-passes.rkt"
           "eval.rkt" "eval-cps.rkt" "eval-cpcps.rkt")

  (define input (current-input-port))

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

  (eval-CPS cps)

  (printf "\n===\n\n")

  (define cpcps
    (let ([stats (analyze-closures cps)])
      (closure-convert cps stats)))
  (pretty-print cpcps)

  (printf "\n---\n\n")

  (eval-CPCPS cpcps)

  (printf "\n===\n\n")

  (define cpcps* (cpcps-shrink cpcps))
  (pretty-print cpcps*)

  (printf "\n---\n\n")

  (eval-CPCPS cpcps))
