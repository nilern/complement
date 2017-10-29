#lang racket/base

(provide schedule-moves collect-constants serialize-conts fallthrough resolve assemble-chunk)
(require racket/match racket/stream (only-in racket/function thunk) (only-in srfi/26 cute)
         (only-in racket/list remove-duplicates) racket/set racket/dict data/gvector
         (only-in threading ~>)
         nanopass/base
         (rename-in "langs.rkt" (InstrCPCPS-Atom=? atom=?)
                                (InstrCPCPS-Atom-hash hash-atom))
         (prefix-in ops: "primops.rkt") (prefix-in bytecode: "bytecode.rkt")
         (prefix-in reg-pool: (submod "register-allocation.rkt" reg-pool))
         (prefix-in cfg: "cfg.rkt")
         (only-in "util.rkt" zip-hash unzip-hash when-let-values while-let-values))

;;; TODO: Assemble code objects and bytecode files
;;; TODO: pull out names into debug info tables
                    
(define (dict-take! kvs k)
  (begin0
    (dict-ref kvs k)
    (dict-remove! kvs k)))

(define-custom-hash-types atom-hash
  atom=?
  hash-atom)

(define-pass schedule-moves : RegCPCPS (ir livenesses dom-forests) -> InstrCPCPS ()
  (definitions
    (define (atom-in-reg? atom reg)
      (nanopass-case (InstrCPCPS Atom) atom
        [(reg ,i) (guard (= i reg)) #t]
        [else #f]))
  
    (define (deallocate-atom! reg-pool atom)
      (nanopass-case (InstrCPCPS Atom) atom
        [(reg ,i) (reg-pool:deallocate! reg-pool i)]
        [else (void)]))
  
    (define make-move-graph
      (let* ([unknown-arg-moves!
              (lambda (move-graph args)
                (for ([(arg reg) (in-indexed args)]
                      #:when (not (atom-in-reg? arg reg)))
                  (add-move! move-graph arg reg)))])
        (lambda (kenv callee args)
          (with-output-language (InstrCPCPS Var)
            (define move-graph (make-mutable-atom-hash))
            (define callee*
              (nanopass-case (InstrCPCPS Var) callee
                [(reg ,i)
                 (unknown-arg-moves! move-graph args)
                 (define fallback-reg (length args))
                 (if (< i fallback-reg)
                   (begin
                     (add-move! move-graph callee fallback-reg)
                     `(reg ,fallback-reg))
                   callee)]
                [(label ,n)
                 (nanopass-case (RegCPCPS Cont) (hash-ref kenv n)
                   [(cont ([,n* ,i*] ...) ,s* ... ,t)
                    (for ([arg args] [reg i*]
                          #:when (not (atom-in-reg? arg reg)))
                      (add-move! move-graph arg reg))])
                 callee]
                [(proc ,n)
                 (unknown-arg-moves! move-graph args)
                 callee]))
            (values callee* move-graph)))))

    (define (add-move! move-graph arg reg)
      (~> (dict-ref! move-graph arg mutable-set)
          (set-add! reg)))

    (define (change-src! move-graph src new-src)
      (define dests (dict-take! move-graph src))
      (set-remove! dests (unwrap-reg new-src))
      (unless (set-empty? dests)
        (dict-set! move-graph new-src dests)))

    (define (take-move! move-graph reg-pool src dest-var)
      (change-src! move-graph src dest-var)
      (deallocate-atom! reg-pool src))

    (define (take-leaf-move! move-graph reg-pool stmt-acc)
      (with-output-language (InstrCPCPS Var)
        (let/ec return
          (define-values (src dest dest-var)
            (let/ec finish
              (for* ([(src dests) (in-dict move-graph)]
                     [dest dests])
                (define dest-var `(reg ,dest))
                (unless (dict-has-key? move-graph dest-var)
                  (finish src dest dest-var)))
              (return #f #f #f)))
          (take-move! move-graph reg-pool src dest-var)
          (values #t dest src))))

    (define (break-cycle! move-graph reg-pool stmt-acc)
      (with-output-language (InstrCPCPS Var)
        (if (not (dict-empty? move-graph))
          (let-values ([(src dests) (stream-first (sequence->stream (in-dict move-graph)))])
            (define dest (reg-pool:allocate! reg-pool))
            (take-move! move-graph reg-pool src `(reg ,dest))
            (values #t dest src))
          (values #f #f #f))))

    (define (unwrap-reg atom)
      (nanopass-case (InstrCPCPS Atom) atom
        [(reg ,i) i]
        [else (error "not a register" atom)]))

    (define (emit-stmt! stmt-acc name reg expr)
      (with-output-language (InstrCPCPS Stmt)
        (gvector-add! stmt-acc (if name `(def (,name ,reg) ,expr) expr))))

    (define (emit-move! stmt-acc dest src)
      (emit-stmt! stmt-acc (gensym 'arg) dest src)))

  (Program : Program (ir) -> Program ()
      [(prog ([,n* ,blocks*] ...) ,n)
       `(prog ([,n* ,(map (cute CFG <> <>) blocks* n*)] ...) ,n)])

  (CFG : CFG (ir name) -> CFG ()
    [(cfg ([,n1* ,k*] ...) (,n2* ...))
     (define liveness (hash-ref livenesses name))
     (define dom-forest (hash-ref dom-forests name))
     (define kenv (zip-hash n1* k*))
     (define env (make-hash))
     (define cont-acc (make-hash))
     (for ([entry n2*])
       (let loop ([dom-tree (hash-ref dom-forest entry)])
         (match-define (cons label children) dom-tree)
         (Cont (hash-ref kenv label) label kenv env (hash-ref liveness label) cont-acc)
         (for ([child children])
           (loop child))))
     (define-values (labels conts) (unzip-hash cont-acc))
     `(cfg ([,labels ,conts] ...) (,n2* ...))])

  (Cont : Cont (ir label kenv env liveness cont-acc) -> Cont ()
    [(cont ([,n* ,i*] ...) ,s* ... ,t)
     (define reg-pool (reg-pool:make))
     (define stmt-acc (make-gvector))
     (for ([freevar (hash-ref liveness 'freevars)])
       (reg-pool:preallocate! reg-pool (hash-ref env freevar)))
     (for ([param n*] [reg i*])
       (reg-pool:preallocate! reg-pool reg)
       (hash-set! env param reg))
     (for ([stmt s*] [luses (hash-ref liveness 'stmt-last-uses)])
       (Stmt stmt env reg-pool luses stmt-acc))
     (define transfer (Transfer t kenv reg-pool stmt-acc))
     (hash-set! cont-acc label `(cont ([,n* ,i*] ...) ,(gvector->list stmt-acc) ... ,transfer))])

  (Stmt : Stmt (ir env reg-pool luses stmt-acc) -> Stmt ()
    [(def (,n ,i) ,e)
     (reg-pool:deallocate-luses! reg-pool env luses)
     (reg-pool:preallocate! reg-pool i)
     (hash-set! env n i)
     (Expr e n i reg-pool stmt-acc)]
    [,e
     (reg-pool:deallocate-luses! reg-pool env luses)
     (Expr e #f #f reg-pool stmt-acc)])

  (Expr : Expr (ir name reg reg-pool stmt-acc) -> Expr ()
    [(primcall0 ,p)         (emit-stmt! stmt-acc name reg `(primcall0 ,p))]
    [(primcall1 ,p ,a)      (emit-stmt! stmt-acc name reg `(primcall1 ,p ,(Atom a)))]
    [(primcall2 ,p ,a1 ,a2) (emit-stmt! stmt-acc name reg `(primcall2 ,p ,(Atom a1) ,(Atom a2)))]
    [(primcall3 ,p ,a1 ,a2 ,a3)
     (emit-stmt! stmt-acc name reg `(primcall3 ,p ,(Atom a1) ,(Atom a2) ,(Atom a3)))]
    [,a (emit-stmt! stmt-acc name reg (Atom a))])

  ;; NOTE: This doesn't need to `deallocate-luses!` since any children start with fresh reg-pools.
  (Transfer : Transfer (ir kenv reg-pool stmt-acc) -> Transfer ()
    [(goto ,x ,a* ...)
     (define-values (callee move-graph) (make-move-graph kenv (Var x) (map Atom a*)))
     (let emit-moves ()
       (while-let-values [(found? dest src) (take-leaf-move! move-graph reg-pool stmt-acc)]
         (emit-move! stmt-acc dest src))
       (when-let-values [(found? dest src) (break-cycle! move-graph reg-pool stmt-acc)]
         (emit-move! stmt-acc dest src)
         (emit-moves)))
     `(goto ,callee)]
    [(if ,a? ,x1 ,x2) `(if ,(Atom a?) ,(Var x1) ,(Var x2))]
    [(halt ,a) `(halt ,(Atom a))])

  (Atom : Atom (ir) -> Atom ()
    [(const ,c) `(const ,c)]
    [,x (Var x)])

  (Var : Var (ir) -> Var ()
    [(reg ,i) `(reg ,i)]
    [(label ,n) `(label ,n)]
    [(proc ,n) `(proc ,n)]))

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
    [(prog ([,n* ,f*] ...) ,n)
     (define proc-env
       (for/hash ([(name i) (in-indexed n*)])
         (values name i)))
     (define fns
       (for/list ([f f*])
         (Fn f proc-env)))
     `(prog ([,n* ,fns] ...) (,n ,(hash-ref proc-env n)))])

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
    [(prog ([,n* ,f*] ...) (,n ,i))
     (bytecode:$chunk (for/vector ([name n*] [f f*]) (Fn f name)) i)])

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
