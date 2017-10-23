#lang racket/base

(provide schedule-moves)
(require racket/match racket/stream (only-in racket/function thunk) (only-in srfi/26 cute)
         racket/set racket/dict data/gvector (only-in threading ~>)
         nanopass/base
         (rename-in "langs.rkt" (InstrCPCPS-Atom=? atom=?)
                                (InstrCPCPS-Atom-hash hash-atom))
         (prefix-in reg-pool: (submod "register-allocation.rkt" reg-pool))
         (only-in "util.rkt" zip-hash unzip-hash when-let-values while-let-values))

;;; TODO: constant pools
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
