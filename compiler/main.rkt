#lang racket/base

(module+ main
  (require racket/match
           racket/cmdline
           racket/pretty
           (only-in srfi/26 cute)

           (only-in "util.rkt" when-let)
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

  (define input  (current-input-port))
  (define output (current-output-port))

  (struct pass (action dependencies evaluator))

  (define passes
    (hash
      'source-port       (pass (lambda () input) '() #f)
      'parse             (pass parse '(source-port) eval-Cst)
      'alphatize         (pass cst:alphatize '(parse) eval-Cst)
      'infer-decls       (pass cst:infer-decls '(alphatize) #f)
      'lex-straighten    (pass cst:lex-straighten '(infer-decls) #f)
      'introduce-dyn-env (pass cst:introduce-dyn-env '(lex-straighten) #f)
      'add-dispatch      (pass cst:add-dispatch '(introduce-dyn-env) #f)

      'cps-convert      (pass cps-convert '(add-dispatch) eval-CPS)
      'cps-census       (pass (lambda (cps)
                                (let ([ltab (make-hash)] [vtab (make-hash)])
                                   (cps:census cps ltab vtab 1)
                                   (hash 'label-table ltab 'var-table vtab)))
                              '(cps-convert) #f)
      'relax-edges      (pass (lambda (ir census-tables)
                                (cps:relax-edges ir (hash-ref census-tables 'label-table)
                                                 (hash-ref census-tables 'var-table)))
                              '(cps-convert cps-census) eval-CPS)
      'analyze-closures (pass cps:analyze-closures '(relax-edges) #f)
      'closure-convert  (pass (lambda (ir census-tables closure-stats)
                                (cps:closure-convert ir closure-stats
                                                     (hash-ref census-tables 'label-table)))
                              '(relax-edges cps-census analyze-closures) eval-CPCPS)

      'select-instructions (pass cpcps:select-instructions '(closure-convert) #f)
      'cpcps-shrink        (pass cpcps:shrink '(select-instructions) #f)
      'allocate-registers  (pass allocate-registers '(cpcps-shrink) #f)
      'collect-constants   (pass codegen:collect-constants '(allocate-registers) #f)
      'serialize-conts     (pass codegen:serialize-conts '(collect-constants) #f)
      'fallthrough         (pass codegen:fallthrough '(serialize-conts) #f)
      'resolve             (pass codegen:resolve '(fallthrough) #f)
      'assemble-chunk      (pass codegen:assemble-chunk '(resolve) #f)
      'serialize-chunk     (pass (cute serialize-chunk <> output) '(assemble-chunk) #f)))

  (define (perform-upto f pass-name)
    (define results (make-hash))
    (let upto ([pass-name pass-name])
      (if (hash-has-key? results pass-name)
        (hash-ref results pass-name)
        (let* ([pass (hash-ref passes pass-name)]
               [result (f pass-name pass (map upto (pass-dependencies pass)))])
          (hash-set! results pass-name result)
          result))))

  (define (main)
    (define verbose #f)
    (define evaluate #f)
    (define required-pass 'serialize-chunk)
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
                    (let ([result (apply (pass-action pass) deps)])
                      (when verbose
                        (printf "# ~a:\n\n" pass-name)
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
