#lang racket/base

(module+ main
  (require racket/match
           racket/cmdline
           racket/pretty

           (only-in "passes/parse.rkt" parse)
           (prefix-in cst: "passes/cst.rkt")
           (only-in "passes/ast.rkt" cps-convert)
           (prefix-in cps: "passes/cps.rkt")
           (prefix-in cpcps: "passes/cpcps.rkt")
           (only-in "passes/register-allocation.rkt" allocate-registers)
           (prefix-in codegen: "passes/codegen.rkt")
           (only-in "passes/bytecode.rkt" serialize-chunk)
           (only-in "eval/cst.rkt" eval-Cst)
           (only-in "eval/cps.rkt" eval-CPS)
           (only-in "eval/cpcps.rkt" eval-CPCPS))

  (define output (current-output-port))
  (define cps-ltab (make-hash))
  (define cps-vtab (make-hash))

  (define passes
    (list parse
          cst:alphatize
          cst:infer-decls
          cst:lex-straighten
          cst:introduce-dyn-env
          cst:add-dispatch

          cps-convert
          (lambda (cps)
            (cps:census cps cps-ltab cps-vtab 1)
            (cps:relax-edges cps cps-ltab cps-vtab))
          (lambda (cps) (cps:closure-convert cps (cps:analyze-closures cps) cps-ltab))

          cpcps:select-instructions ; TODO: move this after `cpcps:shrink`
          cpcps:shrink
          allocate-registers
          codegen:collect-constants ; TODO: move this after serialize-conts
          codegen:serialize-conts
          codegen:fallthrough
          codegen:resolve
          codegen:assemble-chunk
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
