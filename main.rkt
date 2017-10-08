#lang racket/base

(module+ main
  (require racket/pretty
           nanopass/base
           "langs.rkt"
           "parse.rkt" "cst-passes.rkt" "ast-passes.rkt" "cps-passes.rkt" "cpcps-passes.rkt"
           "eval.rkt" "eval-cps.rkt" "eval-cpcps.rkt")

  (define passes
    (list parse
          alphatize
          infer-decls
          lex-straighten
          introduce-dyn-env
          add-dispatch
          cps-convert
          (lambda (cps) (closure-convert cps (analyze-closures cps)))
          cpcps-shrink
          select-instructions))

  (define evals
    (list eval-Cst
          eval-Cst
          #f
          #f
          #f
          #f
          eval-CPS
          eval-CPCPS
          eval-CPCPS
          #f))

  (define (main)
    (define input (current-input-port))
  	(for/fold ([ir input])
              ([pass passes] [eval evals])
      (define ir* (pass ir))
      (pretty-print ir*)
      (when eval
        (display "\n---\n\n")
        (pretty-print (eval ir*)))
      (display "\n===\n\n")
      ir*)
    (void))

  (main))
