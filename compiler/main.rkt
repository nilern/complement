#lang racket/base

;;; TODO: Primop infrastructure for evaluators (and assembly?)
;;; TODO: Missing evaluators

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

  (define input  (current-input-port))  ; Where to read source code from
  (define output (current-output-port)) ; Where to write bytecode

  ;;; TODO: Use direct references instead of names for pass-dependencies. More straightforward and
  ;;;       prevents creating loops (which make no sense and are not handled by perform-upto) by
  ;;;       accident.

  ;; A compilation pass.
  (struct pass (dependencies ; Needs the results of the passes named here.
                action       ; The function that implements the pass functionality.
                evaluator))  ; An evaluator function for the resulting IR (can also be #f).

  ;; Pass registry.
  (define passes
    (hash
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

  ;; OPTIMIZE: Prune results from `results` when they will not be needed any longer.
  ;;
  ;; Post-order walk of the pass dependency DAG rooted at the pass called `pass-name`. A pass is
  ;; visited by calling `f` on the pass name, the pass value and the results of its dependencies.
  (define (perform-upto f pass-name)
    (define results (make-hash))
    (let upto ([pass-name pass-name])
      (if (hash-has-key? results pass-name) ; Have we already run the pass?
        (hash-ref results pass-name)        ; Return cached result.
        (let* ([pass (hash-ref passes pass-name)]
               [dep-results (map upto (pass-dependencies pass))] ; Recur on dependencies.
               [result (f pass-name pass dep-results)])
          (hash-set! results pass-name result) ; Cache the result.
          result))))

  (define (main)
    (define verbose #f)  ; Verbose output (print IR:s etc.).
    (define evaluate #f) ; Evaluate each IR.
    (define required-pass 'assemble) ; The last pass to be run. By default, emit bytecode.
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
                    (let ([result (apply (pass-action pass) deps)]) ; Perform the pass action.
                      (when verbose
                        (pretty-print result)
                        (when evaluate
                          (when-let (evalf (pass-evaluator pass)) ; Evaluate the resulting IR.
                            (display "\n---\n\n")
                            (pretty-print (time (evalf result)))))
                        (display "\n===\n\n"))
                      result))
                  required-pass)
    (void))

  (main))
