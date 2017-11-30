#lang racket/base

(provide collect-constants serialize-conts fallthrough resolve assemble-chunk)
(require racket/match
         (only-in racket/list remove-duplicates)
         data/gvector
         (only-in srfi/26 cute)
         (only-in threading ~>)
         nanopass/base

         (only-in "../langs.rkt" InstrCPCPS ConstPoolCPCPS Asm ResolvedAsm)
         (prefix-in bytecode: "bytecode.rkt")
         (prefix-in cfg: "../cfg.rkt")
         (only-in "../util.rkt" zip-hash))

;;; TODO: pull out names into debug info tables

(define-pass collect-constants : InstrCPCPS (ir) -> ConstPoolCPCPS ()
  (definitions
    (define (make-const-acc)
      (cons (make-gvector) (make-hash)))

    (define (push-const! const-acc const)
      (match-define (cons index rev-index) const-acc)
      (if (hash-has-key? rev-index const)
        (hash-ref rev-index const)
        (let ([i (gvector-count index)])
          (gvector-add! index const)
          (hash-set! rev-index const i)
          i)))

    (define (build-consts const-acc)
      (gvector->list (car const-acc))))

  (CFG : CFG (ir) -> Fn ()
    [(cfg ([,n1* ,k*] ...) (,n2* ...))
     (define const-acc (make-const-acc))
     (define conts (map (cute Cont <> const-acc) k*))
     `(fn (,(build-consts const-acc) ...) ([,n1* ,conts] ...) (,n2* ...))])

  (Cont : Cont (ir const-acc) -> Cont ()
    [(cont ([,n* ,i*] ...) ,[s*] ... ,[t]) `(cont ([,n* ,i*] ...) ,s* ... ,t)])

  (Stmt : Stmt (ir const-acc) -> Stmt ()
    [(def (,n ,i) ,[e]) `(def (,n ,i) ,e)])

  (Expr : Expr (ir const-acc) -> Expr ()
    [(primcall0 ,p)                   `(primcall0 ,p)]
    [(primcall1 ,p ,[a])              `(primcall1 ,p ,a)]
    [(primcall2 ,p ,[a1] ,[a2])       `(primcall2 ,p ,a1 ,a2)]
    [(primcall3 ,p ,[a1] ,[a2] ,[a3]) `(primcall3 ,p ,a1 ,a2 ,a3)])

  (Transfer : Transfer (ir const-acc) -> Transfer ()
    [(if ,[a?] ,[x1] ,[x2]) `(if ,a? ,x1 ,x2)]
    [(halt ,[a]) `(halt ,a)])

  (Atom : Atom (ir const-acc) -> Atom ()
    [(const ,c) `(const ,(push-const! const-acc c))]))

(define-pass cpcpcps-cfg : ConstPoolCPCPS (ir) -> * ()
  (definitions
    (define (make-entry)
      (make-hash `((callees . ()) (callers . ()))))

    (define (add-edge! cfg caller callee)
      (~> (hash-ref! cfg caller make-entry)
          (hash-update! 'callees (cute cons callee <>)))
      (~> (hash-ref! cfg callee make-entry)
          (hash-update! 'callers (cute cons caller <>)))))

  (Fn : Fn (ir) -> * ()
    [(fn (,c* ...) ([,n1* ,k*] ...) (,n2* ...))
     (define cfg (make-hash))
     (for-each (cute Cont <> <> cfg) k* n1*)
     (for/hash ([(label entry) cfg])
       (values label
               (for/hash ([(k vs) entry])
                 (values k (remove-duplicates vs)))))])


  (Cont : Cont (ir label cfg) -> * ()
    [(cont ([,n* ,i*] ...) ,s* ... ,t)
     (unless (hash-has-key? cfg label)
       (hash-set! cfg label (make-entry)))
     (Transfer t label cfg)])

  (Transfer : Transfer (ir label cfg) -> * ()
    [(goto ,x) (Callee x label cfg)]
    [(if ,a? ,x1 ,x2) (Callee x1 label cfg) (Callee x2 label cfg)]
    [(halt ,a) (void)])

  (Callee : Var (ir label cfg) -> * ()
    [(label ,n) (add-edge! cfg label n)]
    [else (void)])

  (Fn ir))

;; TODO: Also serialize procs, at least putting emtry first.
(define-pass serialize-conts : ConstPoolCPCPS (ir) -> ConstPoolCPCPS ()
  (Fn : Fn (ir) -> Fn ()
    [(fn (,c* ...) ([,n1* ,k*] ...) (,n2* ...))
     (define kenv (zip-hash n1* k*))
     (define rpo (cfg:reverse-postorder (cpcpcps-cfg ir) (reverse n2*)))
     `(fn (,c* ...) ([,rpo ,(map (cute hash-ref kenv <>) rpo)] ...) (,n2* ...))]))

(define-pass fallthrough : ConstPoolCPCPS (ir) -> Asm ()
  (Fn : Fn (ir) -> Fn ()
    [(fn (,c* ...) ([,n1* ,k*] ...) (,n2* ...))
     `(fn (,c* ...)
          ([,n1* ,(for/list ([cont k*] [next-label (in-sequences (cdr n1*) (in-value #f))])
                    (Cont cont next-label))] ...)
          (,n2* ...))])

  (Cont : Cont (ir next-label) -> Cont ()
    [(cont ([,n* ,i*] ...) ,[s*] ... ,[t]) `(cont ([,n* ,i*] ...) ,s* ... ,t)])

  (Transfer : Transfer (ir next-label) -> Transfer ()
    [(goto (label ,n)) (guard (eq? n next-label)) `(br #f)]
    [(goto (label ,n)) `(br ,n)]
    [(goto ,[x]) `(jmp ,x)]
    [(if ,[a?] (label ,n1) (label ,n2)) (guard (eq? n1 next-label)) `(brf ,a? ,n2)]
    [(if ,[a?] ,[x1] ,[x2]) (error "if has unimplementable destinations" ir)]))

(define-pass resolve : Asm (ir) -> ResolvedAsm ()
  (definitions
    (define (transfer-length transfer)
      (nanopass-case (Asm Transfer) transfer
        [(br ,n) (guard (not n)) 0]
        [else 1]))

    (define (cont-length cont)
      (nanopass-case (Asm Cont) cont
        [(cont ([,n* ,i*] ...) ,s* ... ,t) (+ (length s*) (transfer-length t))]))

    (define (make-label-env labels conts)
      (define pc 0)
      (for/hash ([label labels] [cont conts])
        (values label
                (begin0
                  pc
                  (set! pc (+ pc (cont-length cont)))))))

    (define (resolve-label label-env pc label)
      (- (hash-ref label-env label) (unbox pc))))

  (Program : Program (ir) -> Program ()
    [(prog ([,n* ,f*] ...) ,i ,n)
     (define proc-env
       (for/hash ([(name i) (in-indexed n*)])
         (values name i)))
     (define fns
       (for/list ([f f*])
         (Fn f proc-env)))
     `(prog ([,n* ,fns] ...) ,i (,n ,(hash-ref proc-env n)))])

  (Fn : Fn (ir proc-env) -> Fn ()
    [(fn (,c* ...) ([,n1* ,k*] ...) (,n2* ...))
     (define label-env (make-label-env n1* k*))
     (define pc (box 0))
     (define conts
       (for/list ([cont k*])
         (Cont cont proc-env label-env pc)))
     `(fn (,c* ...)
          ([,n1* ,conts] ...)
          ([,n2* ,(map (cute hash-ref label-env <>) n2*)] ...))])

  (Cont : Cont (ir proc-env label-env pc) -> Cont ()
    [(cont ([,n* ,i*] ...) ,s* ... ,t)
     (define stmts
       (for/list ([stmt s*])
         (set-box! pc (+ (unbox pc) 1))
         (Stmt stmt proc-env label-env pc)))
     (set-box! pc (+ (unbox pc) (transfer-length t)))
     (define transfer (Transfer t proc-env label-env pc))
     `(cont ([,n* ,i*] ...) ,stmts ... ,transfer)])

  (Stmt : Stmt (ir proc-env label-env pc) -> Stmt ())

  (Expr : Expr (ir proc-env label-env pc) -> Expr ())

  (Transfer : Transfer (ir proc-env label-env pc) -> Transfer ()
    [(br ,n) (guard (not n)) `(br #f #f)]
    [(br ,n) `(br ,n ,(resolve-label label-env pc n))]
    [(brf ,[a?] ,n) `(brf ,a? ,n ,(resolve-label label-env pc n))])

  (Atom : Atom (ir proc-env label-env pc) -> Atom ())

  (Var : Var (ir proc-env label-env pc) -> Var ()
    [(label ,n) `(label ,n ,(resolve-label label-env pc n))]
    [(proc ,n) `(proc ,n ,(hash-ref proc-env n))]))

(define-pass assemble-chunk : ResolvedAsm (ir) -> * ()
  (Program : Program (ir) -> * ()
    [(prog ([,n* ,f*] ...) ,i1 (,n ,i2))
     (bytecode:$chunk i1 (for/vector ([name n*] [f f*]) (Fn f name)) i2)])

  (Fn : Fn (ir name) -> * ()
    [(fn (,c* ...) ([,n1* ,k*] ...) ([,n2* ,i*] ...))
     (define instr-acc (make-gvector))
     (for-each (cute Cont <> instr-acc) k*)
     (bytecode:$code-object name
                           (list->vector c*)
                           (gvector->vector instr-acc))])

  (Cont : Cont (ir instr-acc) -> * ()
    [(cont ([,n* ,i*] ...) ,s* ... ,t)
     (for-each (cute Stmt <> instr-acc) s*)
     (Transfer t instr-acc)])

  (Stmt : Stmt (ir instr-acc) -> * ()
    [(def (,n ,i) ,e) (Expr e i instr-acc)]
    [,e (Expr e #f instr-acc)])

  (Expr : Expr (ir dest-reg instr-acc) -> * ()
    [(primcall0 ,p)             (gvector-add! instr-acc (bytecode:encode-stmt p dest-reg))]
    [(primcall1 ,p ,a)          (gvector-add! instr-acc (bytecode:encode-stmt p dest-reg a))]
    [(primcall2 ,p ,a1 ,a2)     (gvector-add! instr-acc (bytecode:encode-stmt p dest-reg a1 a2))]
    [(primcall3 ,p ,a1 ,a2 ,a3) (gvector-add! instr-acc (bytecode:encode-stmt p dest-reg a1 a2 a3))]
    [,a                         (gvector-add! instr-acc (bytecode:encode-stmt '__mov dest-reg a))])

  (Transfer : Transfer (ir instr-acc) -> * ()
    [(br ,n ,i) (guard (not n)) (void)]
    [(br ,n ,i)      (gvector-add! instr-acc (bytecode:encode-transfer '__br i))]
    [(jmp ,x)        (gvector-add! instr-acc (bytecode:encode-transfer '__jmp x))]
    [(brf ,a? ,n ,i) (gvector-add! instr-acc (bytecode:encode-transfer '__brf a? i))]
    [(halt ,a)       (gvector-add! instr-acc (bytecode:encode-transfer '__halt a))]))
