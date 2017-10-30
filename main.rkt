#lang racket/base

(module+ main
  (require racket/match racket/cmdline (only-in racket/function identity) (only-in srfi/26 cute)
           racket/pretty
           nanopass/base
           "langs.rkt"
           "parse.rkt" "cst-passes.rkt" "ast-passes.rkt" "cps-passes.rkt"
           (prefix-in cpcps: "cpcps-passes.rkt") "register-allocation.rkt" "codegen.rkt"
           (only-in "bytecode.rkt" serialize-chunk)
           "eval.rkt" "eval-cps.rkt" "eval-cpcps.rkt"
           (prefix-in vm: "vm.rkt"))

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
          vm:run
          #f))

  (define (main)
    (define verbose #f)
    (define input
      (command-line
        #:once-each
        [("-o") output-filename "Name of output file"
         (set! output (open-output-file output-filename #:mode 'binary #:exists 'truncate))]
        [("-v") "Verbose mode"
         (set! verbose #t)]
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
        (when eval
          (display "\n---\n\n")
          (let ([value (time (eval ir*))])
            (pretty-print value)))
        (display "\n===\n\n"))
      ir*)
    (void))

  (main))
