#lang racket/base

(provide eval-Asm)
(require racket/match
         (only-in racket/list first second)
         (only-in racket/function identity)
         (only-in racket/undefined undefined)
         (only-in srfi/26 cute)
         (only-in threading ~>>)
         nanopass/base

         (only-in "../langs.rkt" Asm)
         (prefix-in primops: "../primops.rkt")
         (only-in "../nanopass-util.rkt" define/nanopass))

(define-pass eval-Asm : Asm (prog) -> * ()
  (definitions
    (define/nanopass (Asm Var) (unwrap-reg x)
      [(reg ,i) i]
      [else (error "not a register" x)])

    ;; A more convenient function code repr than (IR Program) provides.
    (struct $codeobj (kenv entry))

    ;; Register file and code memory.
    (define-values (regs fenv)
      (nanopass-case (Asm Program) prog
        [(prog ([,n* ,blocks*] ...) ,i ,n)
         (values (make-vector i undefined)
                 (for/hash ([flabel n*] [cfg blocks*])
                   (values flabel
                           (nanopass-case (Asm CFG) cfg
                             [(cfg ([,n1* ,k*] ...) (,n2* ...))
                              ($codeobj (map cons n1* k*) (car n2*))]))))]))

    (define primapply (primops:primapply primops:vm-ops))

    ;; A code pointer consists of fn and continuation labels.
    (struct $code-ptr (fn-label cont-label))

    ;; A program counter is more specific than a code pointer, also containing the code remaining
    ;; in the current cont.
    (struct $pc (fn-label cont-label stmts transfer))

    ;; Continue evaluation at the start of the next cont.
    (define (next-cont flabel klabel)
      (match-let* ([(cons klabel cont)
                    (let loop ([kenv ($codeobj-kenv (hash-ref fenv flabel))])
                      (match kenv
                        [(cons (cons k _) kenv*)
                         (if (eq? k klabel)
                           (first kenv*)
                           (loop kenv*))]
                        ['() (error "label not found in" klabel flabel)]))])
        (nanopass-case (Asm Cont) cont
          [(cont ([,n* ,i*] ...) ,s* ... ,t) (next-instr ($pc flabel klabel s* t))])))

    ;; Continue evaluation at the next instruction.
    (define/match (next-instr _)
      [(($pc flabel klabel (cons stmt stmts) transfer))
       (Stmt stmt ($pc flabel klabel stmts transfer))]
      [((and pc ($pc flabel klabel '() (and (? identity) transfer))))
       (Transfer transfer pc)]
      [(($pc flabel klabel '() _)) (next-cont flabel klabel)])

    ;; Jump to the give $code-ptr.
    (define/match (goto _)
      [(($code-ptr fn-label cont-label))
       (define cont (~>> (hash-ref fenv fn-label) $codeobj-kenv
                         (assq cont-label) cdr))
       (nanopass-case (Asm Cont) cont
         [(cont ([,n* ,i*] ...) ,s* ... ,t) (next-instr ($pc fn-label cont-label s* t))])]))

  ;; Run the program.
  (Program : Program (ir) -> * ()
    [(prog ([,n* ,blocks*] ...) ,i ,n)
     (goto ($code-ptr n ($codeobj-entry (hash-ref fenv n))))])

  ;; Execute the Stmt and the rest of the cont.
  (Stmt : Stmt (stmt pc) -> * ()
    [(def (,n ,i) ,e)
     (vector-set! regs i (Expr e ($pc-fn-label pc)))
     (next-instr pc)]
    [,e
     (Expr e ($pc-fn-label pc))
     (next-instr pc)])

  ;; Evaluate an Expr (and perform side effects).
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
  (Transfer : Transfer (_ pc) -> * ()
    [(br ,n)  (goto ($code-ptr ($pc-fn-label pc) n))]
    [(jmp ,i) (goto (vector-ref regs i))]
    [(ffncall ,x) (error "unimplemented")]
    [(brf ,a? ,n)
     (match (Atom a? ($pc-fn-label pc))
       [#t (next-cont ($pc-fn-label pc) ($pc-cont-label pc))]
       [#f (goto ($code-ptr ($pc-fn-label pc) n))]
       [v (error "not a boolean" v)])]
    [(halt ,a) (Atom a ($pc-fn-label pc))]
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
