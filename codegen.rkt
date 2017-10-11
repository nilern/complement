#lang racket/base

(provide harmonize-ifs)
(require (only-in srfi/26 cute) nanopass/base
         "langs.rkt" (prefix-in kenv: (submod "util.rkt" cont-env))
         (only-in "util.rkt" unzip-hash))

(define-pass harmonize-ifs : RegisterizableCPCPS (ir reg-map) -> InstrCPCPS ()
  (definitions
    (define (calling-convention kenv var)
      (nanopass-case (InstrCPCPS Var) var
        [(lex ,n) (error "TODO: unimplemented")]
        [(label ,n)
         (nanopass-case (RegisterizableCPCPS Cont) (kenv:ref kenv n)
           [(cont (,n* ...) ,s* ... ,t) (map (cute hash-ref reg-map <>) n*)])]
        [(proc ,n) (error "TODO: unimplemented")])))

  (CFG : CFG (ir) -> CFG ()
    [(cfg ([,n1* ,k*] ...) (,n2* ...))
     (define kenv (kenv:inject n1* k*))
     (define cfg-builder (make-hash))
     (for ([label n1*] [cont k*])
       (Cont cont label kenv cfg-builder))
     (define-values (labels conts) (unzip-hash cfg-builder))
     `(cfg ([,labels ,conts] ...) (,n2* ...))])

  (Cont : Cont (ir label kenv cfg-builder) -> Cont ()
    [(cont (,n* ...) ,[s*] ... ,t)
     (hash-set! cfg-builder label `(cont (,n* ...) ,s* ... ,(Transfer t kenv)))])
  (Transfer : Transfer (ir kenv) -> Transfer ()
    [(goto ,[x] ,[a*] ...) `(goto ,x ,a* ...)]
    [(if ,[a?] (,[x1] ,[a1*] ...) (,[x2] ,[a2*] ...))
     (define cconv1 (calling-convention kenv x1))
     (define cconv2 (calling-convention kenv x2))
     (if (and (equal? cconv1 cconv2) (equal? a1* a2*))
       `(if ,a? ,x1 ,x2 ,a1* ...)
       (error "TODO: unimplemented"))]
    [(halt ,[a]) `(halt ,a)]))
