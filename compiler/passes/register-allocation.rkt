#lang racket/base

(provide allocate-registers)
(require racket/match
         (only-in racket/stream stream-first)
         racket/set
         racket/dict
         data/gvector
         (only-in srfi/26 cute)
         (only-in threading ~>)
         nanopass/base

         (rename-in "../langs.rkt" (InstrCPCPS-Atom=? atom=?) (InstrCPCPS-Atom-hash hash-atom))
         (prefix-in cfg: "../cfg.rkt")
         (only-in "../util.rkt" zip-hash unzip-hash when-let-values while-let-values))

(define-pass cfg-liveness : RegisterizableCPCPS (ir) -> * ()
  (definitions
    (struct $luses-builder (stmt-luses transfer-luses))

    (define (make-luses-builder transfer-luses)
      ($luses-builder '() transfer-luses))

    (define (push-luses luses-builder luses)
      (match-define ($luses-builder stmt-luses transfer-luses) luses-builder)
      ($luses-builder (cons luses stmt-luses) transfer-luses))

    (define (ensure-luses luses-builder freevars names)
      (define (splice luses)
        (set-union luses (set-subtract names freevars)))
      (match luses-builder
        [($luses-builder (cons first-luses rest-luses) transfer-luses)
         ($luses-builder (cons (splice first-luses) rest-luses) transfer-luses)]
        [($luses-builder '() transfer-luses)
         ($luses-builder '() (splice transfer-luses))]))

    (define (build-luses luses-builder)
      (match-define ($luses-builder stmt-luses transfer-luses) luses-builder)
      (values stmt-luses transfer-luses))

    (define (freevars+luses prev-freevars local-freevars)
      (values (set-union local-freevars prev-freevars)
              (set-subtract local-freevars prev-freevars)))

    (define (arglist atoms)
      (foldl set-union (set) (map Atom atoms))))

  (CFG : CFG (ir) -> * ()
    [(cfg ([,n1* ,k*] ...) (,n2* ...))
     (define kenv (zip-hash n1* k*))
     (define cont-acc (make-hash))
     (for ([name n2*])
       (Cont (hash-ref kenv name) name kenv cont-acc))
     cont-acc])

  (Cont : Cont (ir name kenv cont-acc) -> * ()
    [(cont (,n* ...) ,s* ... ,t)
     (unless (hash-has-key? cont-acc name)
       (let*-values ([(transfer-freevars transfer-luses) (Transfer t kenv cont-acc)]
                     [(body-freevars luses-builder)
                      (let body ([stmts s*])
                        (match stmts
                          ['() (values transfer-freevars (make-luses-builder transfer-luses))]
                          [(cons stmt stmts)
                           (let*-values ([(freevars luses-builder) (body stmts)]
                                         [(freevars luses-builder)
                                          (Stmt stmt freevars luses-builder)])
                             (values freevars luses-builder))]))]
                     [(params) (list->set n*)]
                     [(stmt-luses transfer-luses)
                      (build-luses (ensure-luses luses-builder body-freevars params))])
         (hash-set! cont-acc name
           (hash 'freevars (set-subtract body-freevars params)
                 'stmt-last-uses stmt-luses
                 'transfer-luses transfer-luses))))])

  (Stmt : Stmt (ir freevars luses-builder) -> * ()
    [(def ,n ,e)
     (define-values (freevars* luses) (freevars+luses freevars (Expr e)))
     (values (set-remove freevars* n)
             (push-luses (ensure-luses luses-builder freevars (set n)) luses))]
    [,e
     (define-values (freevars* luses) (freevars+luses freevars (Expr e)))
     (values freevars* (push-luses luses-builder luses))])

  (Expr : Expr (ir) -> * ()
    [(primcall0 ,p) (set)]
    [(primcall1 ,p ,a) (Atom a)]
    [(primcall2 ,p ,a1 ,a2) (set-union (Atom a1) (Atom a2))]
    [(primcall3 ,p ,a1 ,a2 ,a3) (set-union (Atom a1) (Atom a2) (Atom a3))]
    [,a (Atom a)])

  (Transfer : Transfer (ir kenv cont-acc) -> * ()
    [(goto ,x ,a* ...)
     (freevars+luses (Callee x kenv cont-acc) (set-union (Var x) (arglist a*)))]
    [(ffncall ,x ,a* ...)
     (freevars+luses (Callee x kenv cont-acc) (set-union (Var x) (arglist a*)))]
    [(if ,a? ,x1 ,x2)
     (freevars+luses (set-union (Callee x1 kenv cont-acc) (Callee x2 kenv cont-acc))
                     (set-union (Atom a?) (Var x1) (Var x2)))]
    [(halt ,a)
     (define freevars (Atom a))
     (values freevars freevars)]
    [(raise ,a)
     (define freevars (Atom a))
     (values freevars freevars)])

  (Atom : Atom (ir) -> * ()
    [(const ,c) (set)]
    [,x (Var x)])

  (Var : Var (ir) -> * ()
    [(lex ,n) (set n)]
    [(label ,n) (set)]
    [(proc ,n) (set)])

  (Callee : Var (ir kenv cont-acc) -> * ()
    [(lex ,n) (set)]
    [(label ,n)
     (Cont (hash-ref kenv n) n kenv cont-acc)
     (hash-ref (hash-ref cont-acc n) 'freevars)]
    [(proc ,n) (set)])

  (CFG ir))

;; OPTIMIZE: A lot of linear searches here.
(module reg-pool racket/base
  (provide make count preallocate! allocate! deallocate! deallocate-luses!)
  (require racket/match racket/list racket/set
           (only-in srfi/26 cute) (only-in srfi/1 find)
           (only-in "../util.rkt" if-let))

  (struct $reg-pool ([stack #:mutable] [capacity #:mutable]))

  (define (make) ($reg-pool '() 0))

  (define count $reg-pool-capacity)

  (define (push! reg-pool reg)
    (set-$reg-pool-stack! reg-pool (cons reg ($reg-pool-stack reg-pool))))

  (define (pop! reg-pool)
    (match-define (cons reg stack*) ($reg-pool-stack reg-pool))
    (set-$reg-pool-stack! reg-pool stack*)
    reg)

  (define (grow! reg-pool target-capacity)
    (for ([reg (in-range ($reg-pool-capacity reg-pool) target-capacity)])
      (push! reg-pool reg))
    (set-$reg-pool-capacity! reg-pool target-capacity))

  (define (preallocate! reg-pool reg)
    (unless (< reg ($reg-pool-capacity reg-pool))
      (grow! reg-pool (+ reg 1)))
    (let ([stack ($reg-pool-stack reg-pool)])
      (if (memq reg stack)
        (set-$reg-pool-stack! reg-pool (filter-not (cute eq? <> reg) stack))
        (error (format "unable to preallocate ~s" reg)))))

  (define (allocate! reg-pool hints)
    ;; Ensure that every hinted-at register exists:
    (for ([reg hints])
      (unless (< reg ($reg-pool-capacity reg-pool))
        (grow! reg-pool (+ reg 1))))
    ;; Ensure that we always have some register to return:
    (when (null? ($reg-pool-stack reg-pool))
      (grow! reg-pool (+ ($reg-pool-capacity reg-pool) 1)))
    (let ([stack ($reg-pool-stack reg-pool)])
      (if-let [res (find (cute set-member? hints <>) stack)]
        (begin
          ;; We were able to satisfy some hint.
          (set-$reg-pool-stack! reg-pool (filter-not (cute eq? <> res) stack))
          res)
        (pop! reg-pool))))

  (define deallocate! push!)

  (define (deallocate-luses! reg-pool env luses)
    (for ([name luses])
      (push! reg-pool (hash-ref env name)))))

(require (prefix-in reg-pool: (submod "." reg-pool)))

;; TODO: Return multiple values instead of mutating `liveness` and `dom-forests`.
(define-pass allocate : RegisterizableCPCPS (ir ltabs livenesses dom-forests) -> RegCPCPS ()
  (definitions
    ;; Get the parameter list of a (RegisterizableCPCPS Cont).
    (define (cont-params cont)
      (nanopass-case (RegisterizableCPCPS Cont) cont
        [(cont (,n* ...) ,s* ... ,t) n*]))

    ;; Make an empty hint table.
    (define (make-hint-table) (make-hash))

    ;; Add hints due to the fact that `label` gets called with args.
    (define (interim-hint! hint-table env label args)
      (hash-set! hint-table label
        (for/list ([hints (hash-ref hint-table label empty-hint-env)]
                   [arg args])
          (nanopass-case (RegisterizableCPCPS Atom) arg
            [(lex ,n) (set-add hints (hash-ref env n))]
            [else hints]))))

    ;; Replace hints of `label` since registers have been allocated for its parameters.
    (define (final-hint! hint-table label param-regs)
      (hash-set! hint-table label (map set param-regs)))

    ;; The empty hint env.
    (define empty-hint-env (hash))

    ;; A hint env for a call to an escaping continuation.
    (define (conventional-hint-env args)
      (for/fold ([env empty-hint-env])
                ([(arg i) (in-indexed args)])
        (nanopass-case (RegisterizableCPCPS Atom) arg
          [(lex ,n) (hash-set env n (set i))]
          [else env])))

    ;; A hint env for a known continuation, using the knowledge currently available.
    (define (internal-hint-env hint-table label args)
      (for/fold ([env empty-hint-env])
                ([hints (hash-ref hint-table label (map (lambda (_) (set)) args))]
                 [arg args])
        (nanopass-case (RegisterizableCPCPS Atom) arg
          [(lex ,n) (hash-set env n hints)]
          [else env])))

    ;; A hint env for a continuation based on its Transfer.
    (define (cont-hint-env hint-table transfer)
      (nanopass-case (RegisterizableCPCPS Transfer) transfer
        [(goto ,x ,a* ...)
         (nanopass-case (RegisterizableCPCPS Var) x
           [(label ,n) (internal-hint-env hint-table n a*)]
           [else (conventional-hint-env a*)])]
        [(if ,a? ,x1 ,x2) empty-hint-env]
        [(ffncall ,x ,a* ...) (conventional-hint-env a*)]
        [(halt ,a) empty-hint-env]
        [(raise ,a) empty-hint-env]))

    ;; Get the hint set for a variable.
    (define hint-ref (cute hash-ref <> <> (set))))

  (Program : Program (ir) -> Program ()
    [(prog ([,n* ,blocks*] ...) ,n)
     `(prog ([,n* ,(map (cute CFG <> <>) blocks* n*)] ...) ,n)])

  (CFG : CFG (ir name) -> CFG ()
    [(cfg ([,n1* ,k*] ...) (,n2* ...))
     (define ltab (hash-ref ltabs name))
     (define dom-forest (cfg:dominator-forest ltab (cfg:reverse-postorder ltab n2*) n2*))
     (hash-set! dom-forests name dom-forest)
     (define liveness (cfg-liveness ir))
     (hash-set! livenesses name liveness)
     (define env (make-hash))
     (define kenv (zip-hash n1* k*))
     (define cont-acc (make-hash))
     (define hint-table (make-hint-table))
     (for ([entry n2*])
       (let loop ([dom-tree (hash-ref dom-forest entry)])
         (match-define (cons label children) dom-tree)
         (Cont (hash-ref kenv label) label env ltab liveness hint-table cont-acc)
         (for ([child children])
           (loop child))))
     (define-values (labels conts) (unzip-hash cont-acc))
     `(cfg ([,labels ,conts] ...) (,n2* ...))])

  (Cont : Cont (ir label env ltab liveness hint-table cont-acc) -> Cont ()
    [(cont (,n* ...) ,s* ... ,t)
     (unless (hash-has-key? cont-acc label)
       (define cont-liveness (hash-ref liveness label))
       (define hint-env (cont-hint-env hint-table t))
       (define reg-pool (reg-pool:make))
       (define param-regs
         (if (hash-ref (hash-ref ltab label) 'escapes?)
           (for/list ([(param i) (in-indexed n*)])
             (reg-pool:preallocate! reg-pool i)
             (hash-set! env param i)
             i)
           (begin
             (for ([freevar (hash-ref cont-liveness 'freevars)])
               (reg-pool:preallocate! reg-pool (hash-ref env freevar)))
             (for/list ([param n*])
               (define reg (reg-pool:allocate! reg-pool (hint-ref hint-env param)))
               (hash-set! env param reg)
               reg))))
       (define stmts
         (for/list ([stmt s*] [luses (hash-ref cont-liveness 'stmt-last-uses)])
           (Stmt stmt env reg-pool luses hint-env)))
       (define transfer (Transfer t env hint-table cont-acc))
       (hash-set! cont-acc label `(cont ([,n* ,param-regs] ...) ,stmts ... ,transfer))
       (final-hint! hint-table label param-regs))])

  (Stmt : Stmt (ir env reg-pool luses hint-env) -> Stmt ()
    [(def ,n ,e)
     (reg-pool:deallocate-luses! reg-pool env luses)
     (define reg (reg-pool:allocate! reg-pool (hint-ref hint-env n)))
     (hash-set! env n reg)
     `(def (,n ,reg) ,(Expr e env))]
    [,e
     (reg-pool:deallocate-luses! reg-pool env luses)
     (Expr e env)])

  (Expr : Expr (ir env) -> Expr ()
    [(primcall0 ,p)             `(primcall0 ,p)]
    [(primcall1 ,p ,a)          `(primcall1 ,p ,(Atom a env))]
    [(primcall2 ,p ,a1 ,a2)     `(primcall2 ,p ,(Atom a1 env) ,(Atom a2 env))]
    [(primcall3 ,p ,a1, a2, a3) `(primcall3 ,p ,(Atom a1 env) ,(Atom a2 env) ,(Atom a3 env))]
    [,a (Atom a env)])

  ;; NOTE: This doesn't need to `deallocate-luses!` since any children start with fresh reg-pools.
  (Transfer : Transfer (ir env hint-table cont-acc) -> Transfer ()
    [(goto ,x ,a* ...)
     (nanopass-case (RegisterizableCPCPS Var) x
       [(label ,n) (guard (not (hash-has-key? cont-acc n)))
        (interim-hint! hint-table env n a*)]
       [else (void)])
     `(goto ,(Var x env) ,(map (cute Atom <> env) a*) ...)]
    [(ffncall ,x ,a* ...) `(ffncall ,(Var x env) ,(map (cute Atom <> env) a*) ...)]
    [(if ,a? ,x1 ,x2) `(if ,(Atom a? env) ,(Var x1 env) ,(Var x2 env))])

  (Atom : Atom (ir env) -> Atom ()
    [(const ,c) `(const ,c)]
    [,x (Var x env)])

  (Var : Var (ir env) -> Var ()
    [(lex ,n) `(reg ,(hash-ref env n))]
    [(label ,n) `(label ,n)]
    [(proc ,n) `(proc ,n)]))

(define (dict-take! kvs k)
  (begin0
    (dict-ref kvs k)
    (dict-remove! kvs k)))

(define-custom-hash-types atom-hash
  atom=?
  hash-atom)

;; OPTIMIZE: Use a swap instruction (when VM gets one).
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
            (define dest (reg-pool:allocate! reg-pool (set)))
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
       (define max-regs (box 0))
       (define f* (map (cute CFG <> <> max-regs) blocks* n*))
       `(prog ([,n* ,f*] ...) ,(unbox max-regs) ,n)])

  (CFG : CFG (ir name max-regs) -> CFG ()
    [(cfg ([,n1* ,k*] ...) (,n2* ...))
     (define liveness (hash-ref livenesses name))
     (define dom-forest (hash-ref dom-forests name))
     (define kenv (zip-hash n1* k*))
     (define env (make-hash))
     (define cont-acc (make-hash))
     (for ([entry n2*])
       (let loop ([dom-tree (hash-ref dom-forest entry)])
         (match-define (cons label children) dom-tree)
         (Cont (hash-ref kenv label) label kenv env (hash-ref liveness label) cont-acc max-regs)
         (for ([child children])
           (loop child))))
     (define-values (labels conts) (unzip-hash cont-acc))
     `(cfg ([,labels ,conts] ...) (,n2* ...))])

  (Cont : Cont (ir label kenv env liveness cont-acc max-regs) -> Cont ()
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
     (set-box! max-regs (max (unbox max-regs) (reg-pool:count reg-pool)))
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

  ;; TODO: Factor out the contents of the goto and ffncall cases.
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
    [(ffncall ,x ,a* ...)
     (define-values (callee move-graph) (make-move-graph kenv (Var x) (map Atom a*)))
     (let emit-moves ()
       (while-let-values [(found? dest src) (take-leaf-move! move-graph reg-pool stmt-acc)]
         (emit-move! stmt-acc dest src))
       (when-let-values [(found? dest src) (break-cycle! move-graph reg-pool stmt-acc)]
         (emit-move! stmt-acc dest src)
         (emit-moves)))
     `(ffncall ,callee)]
    [(if ,a? ,x1 ,x2) `(if ,(Atom a?) ,(Var x1) ,(Var x2))]
    [(halt ,a) `(halt ,(Atom a))]
    [(raise ,a) `(raise ,(Atom a))])

  (Atom : Atom (ir) -> Atom ()
    [(const ,c) `(const ,c)]
    [,x (Var x)])

  (Var : Var (ir) -> Var ()
    [(reg ,i) `(reg ,i)]
    [(label ,n) `(label ,n)]
    [(proc ,n) `(proc ,n)]))

(define (allocate-registers ir ltabs)
  (let ((livenesses (make-hash))
        (dom-forests (make-hash)))
    (~> (allocate ir ltabs livenesses dom-forests)
        (schedule-moves livenesses dom-forests))))
