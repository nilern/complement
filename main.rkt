#lang racket/base

(module+ main
  (require racket/match racket/cmdline (only-in racket/function identity) (only-in srfi/26 cute)
           racket/pretty
           nanopass/base
           "langs.rkt"
           "passes/parse.rkt" "passes/cst.rkt" "passes/ast.rkt" "passes/cps.rkt"
           (prefix-in cpcps: "passes/cpcps.rkt") "passes/register-allocation.rkt"
           "passes/codegen.rkt" (only-in "passes/bytecode.rkt" serialize-chunk)
           "eval/cst.rkt" "eval/cps.rkt" "eval/cpcps.rkt")

  (define output (current-output-port))
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
          fallthrough
          resolve
          assemble-chunk
          (lambda (chunk) (serialize-chunk chunk output))))

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
          #f
          #f
          #f
          #f))

  (define (main)
    (define verbose #f)
    (define eval-flag #f)
    (define input
      (command-line
        #:once-each
        [("-o") output-filename "Name of output file"
         (set! output (open-output-file output-filename #:mode 'binary #:exists 'truncate))]
        [("-v") "Verbose mode"
         (set! verbose #t)]
        [("-e" "--eval") "Evaluate. Implies --verbose"
         (set! verbose #t)
         (set! eval-flag #t)]
        #:args input-filenames
        (match input-filenames
          ['() (current-input-port)]
          [(list input-filename) (open-input-file input-filename)]
          [_ (error "too many input files")])))

  	(for/fold ([ir input])
              ([pass passes] [eval evals])
      (define ir* (pass ir))
      (when verbose
        (pretty-print ir*)
        (when (and eval-flag eval)
          (display "\n---\n\n")
          (let ([value (time (eval ir*))])
            (pretty-print value)))
        (display "\n===\n\n"))
      ir*)
    (void))

  (main))
