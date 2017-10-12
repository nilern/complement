#lang racket/base

(module+ main
  (require (only-in racket/function identity) racket/pretty (only-in srfi/26 cute)
           nanopass/base
           "langs.rkt"
           "parse.rkt" "cst-passes.rkt" "ast-passes.rkt" "cps-passes.rkt"
           (prefix-in cpcps: "cpcps-passes.rkt") "register-allocation.rkt" "codegen.rkt"
           "eval.rkt" "eval-cps.rkt" "eval-cpcps.rkt")

  (define cps-ltab (make-hash))
  (define cps-vtab (make-hash))
  (define register-mapping #f)

  (define passes
    (list parse
          alphatize
          infer-decls
          lex-straighten
          introduce-dyn-env
          add-dispatch
          cps-convert
          (lambda (cps)
            (census cps cps-ltab cps-vtab 1)
            (relax-edges cps cps-ltab cps-vtab))
          (lambda (cps) (closure-convert cps (analyze-closures cps) cps-ltab))
          cpcps:select-instructions
          cpcps:shrink
          identity
          (cute harmonize-ifs <> register-mapping)))

  (define evals
    (list eval-Cst
          eval-Cst
          #f
          #f
          #f
          #f
          eval-CPS
          eval-CPS
          eval-CPCPS
          #f
          #f
          (lambda (cpcps)
            (set! register-mapping (allocate-registers cpcps))
            register-mapping)
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
