#lang racket/base

(provide eval-ConstPoolAsm)
(require racket/match
         data/gvector
         (only-in racket/undefined undefined)
         (only-in srfi/26 cute)
         (only-in threading ~>)
         nanopass/base

         (only-in "../langs.rkt" ConstPoolAsm)
         (prefix-in primops: "../primops.rkt")
         (only-in "../nanopass-util.rkt" define/nanopass))


(define-pass eval-ConstPoolAsm : ConstPoolAsm (prog) -> * ()
  (definitions
    (define/nanopass (ConstPoolAsm Var) (unwrap-reg x)
      [(reg ,i) i]
      [else (error "not a register" x)])

    ;; These form a sum type for instructions:
    (struct $stmt (stmt) #:transparent)
    (struct $transfer (transfer) #:transparent)

    (struct $codeobj (instrs consts))

    ;; Register file and code memory.
    (define-values (regs fenv)
      (nanopass-case (ConstPoolAsm Program) prog
        [(prog ([,n* ,f*] ...) ,i1 (,n ,i2))
         (values (make-vector i1 undefined)
                 (for/vector ([f f*])
                   (define acc (make-gvector))
                   (nanopass-case (ConstPoolAsm Fn) f
                     [(fn (,c* ...) ([,n1* ,k*] ...) ([,n2* ,i*] ...))
                      (for ([cont k*])
                        (nanopass-case (ConstPoolAsm Cont) cont
                          [(cont ([,n* ,i*] ...) ,s* ... ,t)
                           (for ([stmt s*])
                             (gvector-add! acc ($stmt stmt)))
                           (when t
                             (gvector-add! acc ($transfer t)))]))
                      ($codeobj (gvector->vector acc) (list->vector c*))])))]))

    (define primapply (primops:primapply primops:vm-ops))

    ;; A code pointer consists of fn and instr indices.
    (struct $code-ptr (fn-index instr-index) #:transparent)

    ;; A program counter also has the instrs of the current fn.
    (struct $pc (fn-index instr-index cob) #:transparent)

    ;; Continue evaluation at the next instruction.
    (define/match (next-instr _)
      [(($pc fn-index instr-index (and cob ($codeobj instrs _))))
       (define pc* ($pc fn-index (+ instr-index 1) cob))
       (match (vector-ref instrs instr-index)
         [($stmt stmt)         (Stmt stmt pc*)]
         [($transfer transfer) (Transfer transfer pc*)])])

    ;; Jump to the given $code-ptr.
    (define/match (goto _)
      [(($code-ptr fn-index instr-index))
       (define cob (vector-ref fenv fn-index))
       (next-instr ($pc fn-index instr-index cob))]))

  ;; Run the program.
  (Program : Program (ir) -> * ()
    [(prog ([,n* ,f*] ...) ,i1 (,n ,i2)) (goto ($code-ptr i2 0))])

  ;; Execute the Stmt and the rest of the cont.
  (Stmt : Stmt (stmt pc) -> * ()
    [(def (,n ,i) ,e)
     (vector-set! regs i (Expr e pc))
     (next-instr pc)]
    [,e
     (Expr e pc)
     (next-instr pc)])

  ;; Evaluate an Expr (and perform side effects).
  (Expr : Expr (expr pc) -> * ()
    [,a                         (Atom a pc)]
    [(primcall0 ,p)             (primapply p '())]
    [(primcall1 ,p ,a)          (primapply p (map (cute Atom <> pc) (list a)))]
    [(primcall2 ,p ,a1 ,a2) (guard (eq? p '__swap)) ; HACK (?)
     (define i1 (unwrap-reg a1))
     (define i2 (unwrap-reg a2))
     (define temp (vector-ref regs i1))
     (vector-set! regs i1 (vector-ref regs i2))
     (vector-set! regs i2 temp)]
    [(primcall2 ,p ,a1 ,a2)     (primapply p (map (cute Atom <> pc) (list a1 a2)))]
    [(primcall3 ,p ,a1 ,a2 ,a3) (primapply p (map (cute Atom <> pc) (list a1 a2 a3)))])

  ;; Perform a Transfer.
  (Transfer : Transfer (_ pc) -> * ()
    [(br ,n ,i)   (goto ($code-ptr ($pc-fn-index pc)
                                   (+ ($pc-instr-index pc) i)))]
    [(jmp ,i)     (goto (vector-ref regs i))]
    [(ffncall ,x) (error "unimplemented")]
    [(brf ,a? ,n ,i)
     (match (Atom a? pc)
       [#t (next-instr pc)]
       [#f (goto ($code-ptr ($pc-fn-index pc)
                            (+ ($pc-instr-index pc) i)))]
       [v (error "not a boolean" v)])]
    [(halt ,a)  (Atom a pc)]
    [(raise ,a) (error "unimplemented")])

  ;; Evaluate an Atom.
  (Atom : Atom (_ pc) -> * ()
    [(const ,i) (~> pc $pc-cob $codeobj-consts (vector-ref i))]
    [,x         (Var x pc)])

  ;; Look up the value of a Var. `label` and `proc` produce appropriate $code-ptr:s.
  (Var : Var (_ pc) -> * ()
    [(reg ,i)      (vector-ref regs i)]
    [(label ,n ,i) ($code-ptr ($pc-fn-index pc) (+ ($pc-instr-index pc) i))]
    [(proc ,n ,i)  ($code-ptr i 0)]))
