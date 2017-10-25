#lang racket/base

(module+ main
  (require (only-in racket/function identity) (only-in srfi/26 cute) racket/pretty
           nanopass/base
           "langs.rkt"
           "parse.rkt" "cst-passes.rkt" "ast-passes.rkt" "cps-passes.rkt"
           (prefix-in cpcps: "cpcps-passes.rkt") "register-allocation.rkt" "codegen.rkt"
           "eval.rkt" "eval-cps.rkt" "eval-cpcps.rkt")

  (define cps-ltab (make-hash))
  (define cps-vtab (make-hash))
  (define liveness (make-hash))
  (define dom-forests (make-hash))

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
          cpcps:select-instructions ; TODO: move this after `cpcps:shrink`
          cpcps:shrink
          (cute allocate-registers <> liveness dom-forests)
          (cute schedule-moves <> liveness dom-forests)
          collect-constants ; TODO: move this after serialize-conts
          serialize-conts
          fallthrough))

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
          #f
          #f
          #f
          #f
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
