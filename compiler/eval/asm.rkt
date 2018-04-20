#lang racket/base

(provide eval-InstrCPCPS)
(require racket/match
         (only-in racket/undefined undefined)
         (only-in srfi/26 cute)
         (only-in threading ~>)
         nanopass/base

         (only-in "../langs.rkt" InstrCPCPS)
         (prefix-in primops: "../primops.rkt")
         (only-in "../util.rkt" zip-hash)
         (only-in "../nanopass-util.rkt" define/nanopass))

(define-pass eval-InstrCPCPS : InstrCPCPS (prog) -> * ()
  (definitions
    (define/nanopass (InstrCPCPS Var) (unwrap-reg x)
      [(reg ,i) i]
      [else (error "not a register" x)])

    ;; A more convenient function code repr than (IR Program) provides.
    (struct $codeobj (kenv entry))

    ;; Register file and code memory.
    (define-values (regs fenv)
      (nanopass-case (InstrCPCPS Program) prog
        [(prog ([,n* ,blocks*] ...) ,i ,n)
         (values (make-vector i undefined)
                 (for/hash ([flabel n*] [cfg blocks*])
                   (values flabel
                           (nanopass-case (InstrCPCPS CFG) cfg
                             [(cfg ([,n1* ,k*] ...) (,n2* ...))
                              ($codeobj (zip-hash n1* k*) (car n2*))]))))]))
    ;; A subcont is essentially the remainder of the cont being executed.
    (struct $subcont (stmts transfer))

    ;; Move to the next Stmt (or Transfer).
    (define (sub-continue subcont curr-fn)
      (match subcont
        [($subcont (cons stmt stmts) transfer)
         (Stmt stmt curr-fn ($subcont stmts transfer))]
        [($subcont '() transfer) (Transfer transfer curr-fn)]))

    (define primapply (primops:primapply primops:vm-ops))

    ;; A code pointer consists of fn and continuation labels.
    (struct $code-ptr (fn-label cont-label))

    ;; Jump to the code pointer.
    (define (goto code-ptr curr-fn)
      (match-define ($code-ptr fn-label cont-label) code-ptr)
      (define cont (~> fenv (hash-ref fn-label) $codeobj-kenv (hash-ref cont-label)))
      (nanopass-case (InstrCPCPS Cont) cont
        [(cont ([,n* ,i*] ...) ,s* ... ,t)
         (sub-continue ($subcont s* t) fn-label)])))

  ;; Run the program.
  (Program : Program (ir) -> * ()
    [(prog ([,n* ,blocks*] ...) ,i ,n)
     (goto ($code-ptr n ($codeobj-entry (hash-ref fenv n))) n)])

  ;; Execute the Stmt and the rest of the cont.
  (Stmt : Stmt (stmt curr-fn subcont) -> * ()
    [(def (,n ,i) ,e)
     (vector-set! regs i (Expr e curr-fn))
     (sub-continue subcont curr-fn)]
    [,e
     (Expr e curr-fn)
     (sub-continue subcont curr-fn)])

  (Expr : Expr (expr curr-fn) -> * ()
    [,a                         (Atom a curr-fn)]
    [(primcall0 ,p)             (primapply p '())]
    [(primcall1 ,p ,a)          (primapply p (map (cute Atom <> curr-fn) (list a)))]
    [(primcall2 ,p ,a1 ,a2) (guard (eq? p '__swap)) ; HACK (?)
     (define i1 (unwrap-reg a1))
     (define i2 (unwrap-reg a2))
     (define temp (vector-ref regs i1))
     (vector-set! regs i1 (vector-ref regs i2))
     (vector-set! regs i2 temp)]
    [(primcall2 ,p ,a1 ,a2)     (primapply p (map (cute Atom <> curr-fn) (list a1 a2)))]
    [(primcall3 ,p ,a1 ,a2 ,a3) (primapply p (map (cute Atom <> curr-fn) (list a1 a2 a3)))])

  ;; Perform a Transfer.
  (Transfer : Transfer (_ curr-fn) -> * ()
    [(goto ,x) (goto (Var x curr-fn) curr-fn)]
    [(ffncall ,x) (error "unimplemented")]
    [(if ,a? ,x1 ,x2)
     (define x
       (match (Atom a? curr-fn)
         [#t x1]
         [#f x2]))
     (goto (Var x curr-fn) curr-fn)]
    [(halt ,a) (Atom a curr-fn)]
    [(raise ,a) (error "unimplemented")])

  ;; Evaluate an Atom.
  (Atom : Atom (_ curr-fn) -> * ()
    [(const ,c) c]
    [,x         (Var x curr-fn)])

  ;; Look up the value of a Var. `label` and `proc` produce appropriate $code-ptr:s.
  (Var : Var (_ curr-fn) -> * ()
    [(reg ,i)   (vector-ref regs i)]
    [(label ,n) ($code-ptr curr-fn n)]
    [(proc ,n)  ($code-ptr n ($codeobj-entry (hash-ref fenv n)))]))
