#lang racket/base

;;; TODO: Primop infrastructure for evaluators (and assembly?)
;;; TODO: Missing evaluators
;;; TODO: FFI calls

(module+ main
  (require racket/match
           racket/cmdline
           racket/pretty
           (only-in srfi/26 cute)

           (only-in "util.rkt" when-let)

           (only-in "passes/parse.rkt" parse)
           (only-in "passes/frontend.rkt" alphatize lex-straighten introduce-dyn-env add-dispatch)

           (only-in "passes/cps.rkt" (census cps-census))
           (only-in "passes/cps-convert.rkt" cps-convert relax-edges)

           (only-in "passes/closure-convert.rkt" analyze-closures closure-convert)
           (rename-in "passes/closure-convert.rkt" (shrink cpcps-shrink))
           (prefix-in ltab: (submod "passes/cpcps.rkt" label-table))

           (only-in "passes/instruction-selection.rkt" select-instructions)
           (only-in "passes/register-allocation.rkt" allocate-registers)
           (only-in "passes/codegen.rkt" linearize resolve collect-constants assemble)

           (only-in "eval/cst.rkt" eval-Cst)
           (only-in "eval/cps.rkt" eval-CPS)
           (only-in "eval/cpcps.rkt" eval-CPCPS))

  (define input  (current-input-port))
  (define output (current-output-port))

  (struct pass (dependencies action evaluator))

  (define passes
    (hash
      ;; TODO: Fill out missing syntax:
      'parse             (pass '() (lambda () (parse input)) eval-Cst)
      'alphatize         (pass '(parse) alphatize eval-Cst)
      'lex-straighten    (pass '(alphatize) lex-straighten eval-Cst)
      'introduce-dyn-env (pass '(lex-straighten) introduce-dyn-env #f)
      'add-dispatch      (pass '(introduce-dyn-env) add-dispatch #f)

      'cps-convert      (pass '(add-dispatch) cps-convert eval-CPS)
      'cps-census       (pass '(cps-convert) (cute cps-census <> 1) #f)
      'relax-edges      (pass '(cps-convert cps-census)
                              (lambda (ir census-tables)
                                (relax-edges ir (hash-ref census-tables 'label-table)
                                                (hash-ref census-tables 'var-table)))
                              eval-CPS)

      'analyze-closures (pass '(relax-edges) analyze-closures #f)
      'closure-convert  (pass '(relax-edges cps-census analyze-closures)
                              (lambda (ir census-tables closure-stats)
                                (closure-convert ir closure-stats
                                                 (hash-ref census-tables 'label-table)))
                              eval-CPCPS)
      'cpcps-label-table   (pass '(closure-convert) ltab:make #f)
      'cpcps-shrink        (pass '(closure-convert cpcps-label-table) cpcps-shrink eval-CPCPS)

      'select-instructions (pass '(cpcps-shrink) select-instructions #f)
      'allocate-registers  (pass '(select-instructions cpcps-label-table) allocate-registers #f)
      'linearize           (pass '(allocate-registers cpcps-label-table) linearize #f)
      'resolve             (pass '(linearize) resolve #f)
      'collect-constants   (pass '(resolve) collect-constants #f)
      'assemble            (pass '(collect-constants) (cute assemble <> output) #f)))

  (define (perform-upto f pass-name)
    (define results (make-hash))
    (let upto ([pass-name pass-name])
      (if (hash-has-key? results pass-name)
        (hash-ref results pass-name)
        (let* ([pass (hash-ref passes pass-name)]
               [dep-results (map upto (pass-dependencies pass))]
               [result (f pass-name pass dep-results)])
          (hash-set! results pass-name result)
          result))))

  (define (main)
    (define verbose #f)
    (define evaluate #f)
    (define required-pass 'assemble)
    (command-line
      #:once-each
      [("-o") output-filename "Name of output file."
       (set! output (open-output-file output-filename #:mode 'binary #:exists 'truncate))]
      [("-v") "Verbose mode."
       (set! verbose #t)]
      [("-e" "--eval") "Evaluate. Implies --verbose."
       (set! verbose #t)
       (set! evaluate #t)]
      [("-p" "--pass") pass-name
       "(For compiler debugging:) only compile upto (and including) the pass called pass-name."
       (set! required-pass (string->symbol pass-name))]
      #:args input-filenames
      (set! input (match input-filenames
                    ['() (current-input-port)]
                    [(list input-filename) (open-input-file input-filename)]
                    [_ (error "too many input files")])))

    (perform-upto (lambda (pass-name pass deps)
                    (when verbose
                      (printf "# ~a:\n\n" pass-name))
                    (let ([result (apply (pass-action pass) deps)])
                      (when verbose
                        (pretty-print result)
                        (when evaluate
                          (when-let (evalf (pass-evaluator pass))
                            (display "\n---\n\n")
                            (pretty-print (time (evalf result)))))
                        (display "\n===\n\n"))
                      result))
                  required-pass)
    (void))

  (main))
