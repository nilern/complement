#lang racket/base

(provide collect-constants linearize resolve assemble)
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

;; TODO: Also serialize procs, at least putting entry first.
(define-pass linearize : ConstPoolCPCPS (ir) -> Asm ()
  (Fn : Fn (ir) -> Fn ()
    [(fn (,c* ...) ([,n1* ,k*] ...) (,n2* ...))
     (define kenv (zip-hash n1* k*))
     (define rpo (cfg:reverse-postorder (cpcpcps-cfg ir) (reverse n2*)))
     `(fn (,c* ...)
          ([,rpo ,(for/list ([label rpo]
                             [next-label (in-sequences (cdr rpo) (in-value #f))])
                    (let ([cont (hash-ref kenv label)])
                      (Cont cont next-label)))] ...)
          (,n2* ...))])

  (Cont : Cont (ir next-label) -> Cont ()
    [(cont ([,n* ,i*] ...) ,[s*] ... ,[t]) `(cont ([,n* ,i*] ...) ,s* ... ,t)])

  (Transfer : Transfer (ir next-label) -> Transfer ()
    [(goto (label ,n)) (guard (eq? n next-label)) #f]
    [(goto (label ,n)) `(br ,n)]
    [(goto ,[x]) `(jmp ,x)]
    [(if ,[a?] (label ,n1) (label ,n2)) (guard (eq? n1 next-label)) `(brf ,a? ,n2)]
    [(if ,[a?] ,[x1] ,[x2]) (error "if has unimplementable destinations" ir)]))

(define-pass resolve : Asm (ir) -> ResolvedAsm ()
  (definitions
    (define (transfer-length transfer)
      (if transfer 1 0))

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
     (define transfer (if t (Transfer t proc-env label-env pc) #f))
     `(cont ([,n* ,i*] ...) ,stmts ... ,transfer)])

  (Stmt : Stmt (ir proc-env label-env pc) -> Stmt ())

  (Expr : Expr (ir proc-env label-env pc) -> Expr ())

  (Transfer : Transfer (ir proc-env label-env pc) -> Transfer ()
    [(br ,n) `(br ,n ,(resolve-label label-env pc n))]
    [(brf ,[a?] ,n) `(brf ,a? ,n ,(resolve-label label-env pc n))])

  (Atom : Atom (ir proc-env label-env pc) -> Atom ())

  (Var : Var (ir proc-env label-env pc) -> Var ()
    [(label ,n) `(label ,n ,(resolve-label label-env pc n))]
    [(proc ,n) `(proc ,n ,(hash-ref proc-env n))]))

(define-pass assemble : ResolvedAsm (ir out) -> * ()
  (definitions
    (define (serialize-usize n out)
      (write-bytes (integer->integer-bytes n 8 #f) out))

    (define (serialize-instr instr out)
      (write-bytes (integer->integer-bytes instr 4 #f) out))

    (define (serialize-raw-string str out)
      (serialize-usize (string-length str) out)
      (write-string str out))

    (define (serialize-const const out)
      (cond
        [(fixnum? const)
         (write-byte 0 out)
         (serialize-usize const out)]
        [(char? const)
         (write-byte 1 out)
         (write-char const out)]
        [(symbol? const)
         (write-byte 2 out)
         (serialize-raw-string (symbol->string const) out)]
        [(string? const)
         (write-byte 3 out)
         (serialize-raw-string const out)]
        [else (error "unable to serialize constant" const)]))

    (define (instr-len cont)
      (nanopass-case (ResolvedAsm Cont) cont
        [(cont ([,n* ,i*] ...) ,s* ... ,t) (+ (length s*) (if t 1 0))])))

  (Program : Program (ir) -> * ()
    [(prog ([,n* ,f*] ...) ,i1 (,n ,i2))
     (serialize-usize i1 out)
     (serialize-usize i2 out)
     (serialize-usize (length n*) out)
     (for ([name n*] [f f*]) (Fn f name))])

  (Fn : Fn (ir name) -> * ()
    [(fn (,c* ...) ([,n1* ,k*] ...) ([,n2* ,i*] ...))
     (serialize-raw-string (symbol->string name) out)
     (serialize-usize (length c*) out)
     (for ([c c*]) (serialize-const c out))
     (serialize-usize (foldl + 0 (map instr-len k*)) out)
     (for ([k k*]) (Cont k))])

  (Cont : Cont (ir) -> * ()
    [(cont ([,n* ,i*] ...) ,s* ... ,t)
     (for ([stmt s*]) (Stmt stmt))
     (when t (Transfer t))])

  (Stmt : Stmt (ir) -> * ()
    [(def (,n ,i) ,e) (Expr e i)]
    [,e (Expr e #f)])

  (Expr : Expr (ir dest-reg) -> * ()
    [(primcall0 ,p)             (serialize-instr (bytecode:encode-stmt p dest-reg) out)]
    [(primcall1 ,p ,a)          (serialize-instr (bytecode:encode-stmt p dest-reg a) out)]
    [(primcall2 ,p ,a1 ,a2)     (serialize-instr (bytecode:encode-stmt p dest-reg a1 a2) out)]
    [(primcall3 ,p ,a1 ,a2 ,a3) (serialize-instr (bytecode:encode-stmt p dest-reg a1 a2 a3) out)]
    [,a                         (serialize-instr (bytecode:encode-stmt '__mov dest-reg a) out)])

  (Transfer : Transfer (ir) -> * ()
    [(br ,n ,i)      (serialize-instr (bytecode:encode-transfer '__br i) out)]
    [(jmp ,x)        (serialize-instr (bytecode:encode-transfer '__jmp x) out)]
    [(brf ,a? ,n ,i) (serialize-instr (bytecode:encode-transfer '__brf a? i) out)]
    [(halt ,a)       (serialize-instr (bytecode:encode-transfer '__halt a) out)]))