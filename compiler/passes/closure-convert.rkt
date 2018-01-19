#lang racket/base

(provide analyze-closures closure-convert shrink)
(require racket/match
         (only-in racket/list append-map)
         racket/set
         data/gvector
         (only-in srfi/26 cute)
         (only-in threading ~>)
         nanopass/base

         "../langs.rkt"
         (prefix-in cfg: "../cfg.rkt")
         (only-in "../util.rkt" zip-hash unzip-hash))

(define-pass make-cfg : CPS (ir) -> * ()
  (definitions
    (define (make-entry)
      (make-hash `((callers . ,(mutable-set)) (callees . ,(mutable-set))))))

  (CFG : CFG (ir) -> * ()
    [(cfg ([,n* ,k*] ...) ,n)
     (define cfg-edges (make-hash))
     (for ([label n*])
       (hash-set! cfg-edges label (make-entry)))
     (for ([label n*] [cont k*])
       (Cont cont label cfg-edges))
     cfg-edges])

  (Cont : Cont (ir label cfg-edges) -> * ()
    [(cont (,n* ...) ,s* ... ,t) (Transfer t label cfg-edges)])

  (Transfer : Transfer (ir label cfg-edges) -> * ()
    [(continue ,x ,a* ...) (Callee x label cfg-edges)]
    [(if ,a? ,x1 ,x2)
     (Callee x1 label cfg-edges)
     (Callee x2 label cfg-edges)]
    [(call ,x1 ,x2 ,a* ...) (Callee x1 label cfg-edges)]
    [(ffncall ,x1 ,x2 ,a* ...) (void)]
    [(halt ,a) (void)])

  (Callee : Var (ir label cfg-edges) -> * ()
    [(lex ,n) (void)]
    [(label ,n)
     (~> (hash-ref cfg-edges label)
         (hash-ref 'callees)
         (set-add! n))
     (~> (hash-ref cfg-edges n)
         (hash-ref 'callers)
         (set-add! label))]))

(define-pass analyze-closures : CPS (ir) -> * ()
  (definitions
    (define (make-entry) (make-hash (list (cons 'freevars (mutable-set)))))

    (define (freevars table label)
      (~> (hash-ref table label)
          (hash-ref 'freevars)))

    (define (use-clover! table label name)
      (~> (freevars table label)
          (set-add! name)))

    (define (transitively! table label env src-label)
      (define fvs (freevars table label))
      (for ([fv (freevars table src-label)]
            #:when (not (set-member? env fv)))
        (set-add! fvs fv))))

  (CFG : CFG (ir stats visited) -> * ()
    [(cfg ([,n* ,k*] ...) ,n)
     (define kenv (zip-hash n* k*))
     (Cont (hash-ref kenv n) n kenv stats visited)])

  (Cont : Cont (ir label kenv stats visited) -> * ()
    [(cont (,n* ...) ,s* ... ,t)
     (unless (set-member? visited label)
       (set-add! visited label)
       (hash-set! stats label (make-entry))
       (~> (list->set n*)
           (foldl (cute Stmt <> label <> kenv stats visited) _ s*)
           (Transfer t label _ kenv stats visited)))])

  (Stmt : Stmt (ir label env kenv stats visited) -> * ()
    [(def ,n ,e)
     (Expr e label env kenv stats visited)
     (set-add env n)]
    [,e
     (Expr e label env kenv stats visited)
     env])

  (Transfer : Transfer (ir label env kenv stats visited) -> * ()
    [(continue ,x ,a* ...)
     (Var x #t label env kenv stats visited)
     (for ([aexpr a*])
       (Atom aexpr label env kenv stats visited))]
    [(if ,a? ,x1 ,x2)
     (Atom a? label env kenv stats visited)
     (Var x1 #t label env kenv stats visited)
     (Var x2 #t label env kenv stats visited)]
    [(call ,x1 ,x2 ,a* ...)
     (Var x1 #t label env kenv stats visited)
     (Var x2 #f label env kenv stats visited)
     (for ([aexpr a*])
       (Atom aexpr label env kenv stats visited))]
    [(ffncall ,x1 ,x2 ,a* ...)
     (Var x1 #t label env kenv stats visited)
     (Var x2 #f label env kenv stats visited)
     (for ([aexpr a*])
       (Atom aexpr label env kenv stats visited))]
    [(halt ,a) (Atom a label env kenv stats visited)])

  (Expr : Expr (ir label env kenv stats visited) -> * ()
    [(fn ,blocks)
     (CFG blocks stats visited)
     (nanopass-case (CPS CFG) blocks
       [(cfg ([,n* ,k*] ...) ,n) (transitively! stats label env n)])]
    [(primcall ,p ,a* ...)
     (for ([aexpr a*])
       (Atom aexpr label env kenv stats visited))]
    [,a (Atom a label env kenv stats visited)])

  (Atom : Atom (ir label env kenv stats visited) -> * ()
    [,x (Var x #f label env kenv stats visited)]
    [(const ,c) (void)])

  (Var : Var (ir call? label env kenv stats visited) -> * ()
    [(lex ,n) (unless (set-member? env n) (use-clover! stats label n))]
    [(label ,n)
     (Cont (hash-ref kenv n) n kenv stats visited)
     (transitively! stats label env n)])

  (let ([visited (mutable-set)]
        [stats (make-hash)])
    (CFG ir stats visited)
    stats))

(define-pass closure-convert : CPS (ir stats ltab) -> CPCPS ()
  (definitions
    (define (fv-params env freevars)
      (for/list ([fv freevars])
        (hash-ref env fv fv)))

    (define (fv-lexen env freevars)
      (with-output-language (CPCPS Atom)
        (for/list ([fv freevars])
          `(lex ,(hash-ref env fv fv)))))

    (define (fv-loads fn-entry? closure env freevars)
      (with-output-language (CPCPS Stmt)
        (for/list ([(fv i) (in-indexed freevars)])
          (if fn-entry?
            `(def ,(hash-ref env fv fv) (primcall __fnGet (lex ,closure) (const ,i)))
            `(def ,(hash-ref env fv fv) (primcall __contGet (lex ,closure) (const ,i)))))))

    (struct $cont-acc (conts entry-point return-points))

    (define (make-cont-acc entry)
      ($cont-acc (make-hash) entry (mutable-set)))

    (define (emit-cont! cont-acc interface label cont)
      (match-define ($cont-acc conts entry return-points) cont-acc)
      (when (and (eq? interface 'closed) (not (eq? label entry)))
        (set-add! return-points label))
      (hash-set! conts label cont))

    (define build-cfg
      (with-output-language (CPCPS CFG)
        (match-lambda
          [($cont-acc conts entry return-points)
           (let-values ([(labels conts) (unzip-hash conts)])
             `(cfg ([,labels ,conts] ...) (,entry ,(set->list return-points) ...)))]))))

  (CFG : CFG (ir fn-acc) -> CFG ()
    [(cfg ([,n* ,k*] ...) ,n)
     (define cfg-edges (make-cfg ir))
     (define entries
       (filter (lambda (label) (> (hash-ref (hash-ref ltab label) 'escapes) 0)) n*))
     (define rpo (cfg:reverse-postorder cfg-edges entries))
     (define dom-forest (cfg:dominator-forest cfg-edges rpo entries))
     (define kenv (zip-hash n* k*))
     (define cont-acc (make-cont-acc n))
     (for ([entry entries])
       (let loop ([dom-tree (hash-ref dom-forest entry)] [env (hash)])
         (match-define (cons label children) dom-tree)
         (define env* (Cont (hash-ref kenv label) label (eq? label n) env fn-acc cont-acc))
         (for ([child children])
           (loop child env*))))
     (build-cfg cont-acc)])

  (Cont : Cont (ir label fn-entry? env fn-acc cont-acc) -> Cont ()
    [(cont (,n* ...) ,s* ... ,t)
     (define freevars (hash-ref (hash-ref stats label) 'freevars))
     (define ltab-entry (hash-ref ltab label))
     (define called? (> (hash-ref ltab-entry 'calls) 0))
     (define escapes? (> (hash-ref ltab-entry 'escapes) 0))
     (cond
      [called?
       (when escapes? (error (format "~s is both called and escaping" label)))
       (define if-owned? (hash-ref ltab-entry 'if-owned?))
       (let* ([env (if if-owned?
                     env
                     (for/fold ([env env])
                               ([fv freevars])
                       (hash-set env fv (gensym fv))))]
              [stmt-acc (make-gvector)])
         (for ([stmt s*])
           (Stmt stmt env fn-acc stmt-acc))
         (let ([transfer (Transfer t env stmt-acc)])
           (if if-owned?
             (emit-cont! cont-acc 'dominated label `(cont (,n* ...)
                                                      ,(gvector->list stmt-acc) ...
                                                      ,transfer))
             (emit-cont! cont-acc 'lifted label `(cont (,(fv-params env freevars) ... ,n* ...)
                                                   ,(gvector->list stmt-acc) ...
                                                   ,transfer))))
         env)]
      [escapes?
       (let ([closure (gensym label)]
             [env (for/fold ([env env])
                            ([fv freevars])
                    (hash-set env fv (gensym fv)))]
             [stmt-acc (make-gvector)])
         (for ([stmt s*])
           (Stmt stmt env fn-acc stmt-acc))
         (let ([transfer (Transfer t env stmt-acc)])
           (emit-cont! cont-acc 'closed label `(cont (,closure ,n* ...)
                                                     ,(fv-loads fn-entry? closure env freevars) ...
                                                     ,(gvector->list stmt-acc) ...
                                                     ,transfer)))
         env)])
     #| NOTE: unreachable continuations get implicitly eliminated here |# ])

  (Stmt : Stmt (ir env fn-acc stmt-acc) -> Stmt ()
    [(def ,n ,e) (gvector-add! stmt-acc `(def ,n ,(Expr e env fn-acc stmt-acc)))]
    [,e (gvector-add! stmt-acc (Expr e env fn-acc stmt-acc))])

  (Transfer : Transfer (ir env stmt-acc) -> Transfer ()
    [(continue ,x ,a* ...)
     (define-values (x* extra-args) (Jumpee x env stmt-acc))
     `(goto ,x* ,extra-args ... ,(map (cute Atom <> env stmt-acc) a*) ...)]
    [(if ,a? ,x1 ,x2)
     (define-values (x1* _) (Jumpee x1 env stmt-acc))
     (define-values (x2* _*) (Jumpee x2 env stmt-acc))
     `(if ,(Atom a? env stmt-acc) ,x1* ,x2*)]
    [(call ,x1 ,x2 ,a* ...)
     (define-values (x1* extra-args) (Callee x1 env stmt-acc))
     `(goto ,x1* ,extra-args ...
            ,(Escape x2 env stmt-acc) ,(map (cute Atom <> env stmt-acc) a*) ...)]
    [(ffncall ,x1 ,x2 ,a* ...)
     (define callee (Escape x1 env stmt-acc))
     `(ffncall ,callee ,callee ,(Escape x2 env stmt-acc)
               ,(map (cute Atom <> env stmt-acc) a*) ...)]
    [(halt ,a) `(halt ,(Atom a env stmt-acc))])

  (Expr : Expr (ir env fn-acc stmt-acc) -> Expr ()
    [(fn ,blocks)
     (define f (gensym 'f))
     (hash-set! fn-acc f (CFG blocks fn-acc))
     (nanopass-case (CPS CFG) blocks
       [(cfg ([,n* ,k*] ...) ,n)
        (define freevars (hash-ref (hash-ref stats n) 'freevars))
        `(primcall __fnNew (proc ,f) ,(fv-lexen env freevars) ...)])]
    [(primcall ,p ,a* ...) `(primcall ,p ,(map (cute Atom <> env stmt-acc) a*) ...)]
    [,a (Atom a env stmt-acc)])

  (Atom : Atom (ir env stmt-acc) -> Atom ()
    [,x (Escape x env stmt-acc)]
    [(const ,c) `(const ,c)])

  (Escape : Var (ir env stmt-acc) -> Var ()
    [(lex ,n) `(lex ,(hash-ref env n n))]
    [(label ,n)
     (define cont (gensym n))
     (define ltab-entry (hash-ref stats n))
     (define freevars (hash-ref ltab-entry 'freevars))
     (gvector-add! stmt-acc (with-output-language (CPCPS Stmt)
                              `(def ,cont (primcall __contNew (label ,n)
                                                              ,(fv-lexen env freevars) ...))))
     `(lex ,cont)])

  (Callee : Var (ir env stmt-acc) -> Var ()
    [(lex ,n)
     (define codeptr (gensym n))
     (gvector-add! stmt-acc (with-output-language (CPCPS Stmt)
                              `(def ,codeptr (primcall __fnCode (lex ,(hash-ref env n n))))))
     (values `(lex ,codeptr) (list `(lex ,(hash-ref env n n))))]
    [(label ,n) (error "(label n) as callee")])

  (Jumpee : Var (ir env stmt-acc) -> Var ()
    [(lex ,n)
     (define codeptr (gensym n))
     (gvector-add! stmt-acc (with-output-language (CPCPS Stmt)
                              `(def ,codeptr (primcall __contCode (lex ,(hash-ref env n n))))))
     (values `(lex ,codeptr) (list `(lex ,(hash-ref env n n))))]
    [(label ,n)
     (values `(label ,n)
             (if (hash-ref (hash-ref ltab n) 'if-owned?)
               '()
               (fv-lexen env (hash-ref (hash-ref stats n) 'freevars))))])

  (let ([fn-acc (make-hash)]
        [entry (gensym 'main)])
    (hash-set! fn-acc entry (CFG ir fn-acc))
    (define-values (fn-names fns) (unzip-hash fn-acc))
    `(prog ([,fn-names ,fns] ...) ,entry)))

(define-pass shrink : CPCPS (ir ltabs) -> CPCPS ()
  (definitions
    (define (emit-stmt! stmt-acc name expr)
      (with-output-language (CPCPS Stmt)
        (gvector-add! stmt-acc (if name `(def ,name ,expr) expr))))

    (define (ltab-arglists ltab caller callee)
      (nanopass-case (CPCPS Transfer) (hash-ref (hash-ref ltab caller) 'transfer)
        [(goto (label ,n) ,a* ...) (if (eq? n callee) (list a*) '())]
        [(goto ,x ,a* ...) '()]
        [(if ,a? (label ,n1) (label ,n2))
         (if (eq? n1 callee)
           (if (eq? n2 callee) (list '() '()) (list '()))
           (if (eq? n2 callee) (list '()) '()))]
        [(if ,a? (label ,n1) ,x2)
         (if (eq? n1 callee) (list '()) '())]
        [(if ,a? ,x1 (label ,n2))
         (if (eq? n2 callee) (list '()) '())]
        [(if ,a? ,x1 ,x2) '()]
        [(halt ,a) '()]))

    (define (join-atoms atoms)
      (define (join2 atom1 atom2)
        (if (equal? atom1 atom2) atom1 #f))
      (match atoms
        ['() #f]
        [(cons atom atoms) (foldl join2 atom atoms)]))

    (define (shrink-call label keep-indices callee args)
      (nanopass-case (CPCPS Var) callee
        [(lex ,n) (values callee args)]
        [(label ,n)
         (values callee
                 (if (eq? n label)
                   (for/list ([(arg i) (in-indexed args)]
                              #:when (set-member? keep-indices i))
                     arg)
                   args))]
        [(proc ,n) (values callee args)]))

    (define (params! ltab label params)
      (let* ([callers (hash-ref (hash-ref ltab label) 'callers)]
             [arglists (append-map (cute ltab-arglists ltab <> label) callers)]
             [env (make-hash)]
             [keep-indices (mutable-set)]
             [params* (for/fold ([params '()])
                                ([(param index) (in-indexed params)]
                                 [aexprs (apply map list arglists)]) ;; OPTIMIZE: is `apply` slow?
                        (match (join-atoms aexprs)
                          [#f (set-add! keep-indices index)
                              (cons param params)]
                          [atom (hash-set! env param (car aexprs))
                                params]))])
        (for ([caller callers])
          (hash-update! (hash-ref ltab caller) 'transfer
                        (cute ShrinkTransfer <> label keep-indices)))
        (values (reverse params*) env))))

  (Program : Program (ir) -> Program ()
    [(prog ([,n* ,blocks*] ...) ,n)
     `(prog ([,n* ,(map CFG blocks* n*)] ...) ,n)])

  (CFG : CFG (ir name) -> CFG ()
    [(cfg ([,n1* ,k*] ...) (,n2* ...))
     (define ltab (hash-ref ltabs name))
     (define kenv (zip-hash n1* k*))
     (for ([label (cfg:reverse-postorder ltab n2*)])
       (Cont (hash-ref kenv label) label ltab))
     (define-values (rlabels rconts)
       (with-output-language (CPCPS Cont)
         (for/fold ([labels '()] [conts '()])
                   ([(label ltab-entry) ltab])
           (values (cons label labels)
                   (cons `(cont (,(hash-ref ltab-entry 'params) ...)
                            ,(hash-ref ltab-entry 'stmts) ...
                            ,(hash-ref ltab-entry 'transfer))
                         conts)))))
     `(cfg ([,(reverse rlabels) ,(reverse rconts)] ...) (,n2* ...))])

  (Cont : Cont (ir label ltab) -> * ()
    [(cont (,n* ...) ,s* ... ,t)
     (define ltab-entry (hash-ref ltab label))
     (define-values (params env)
       (if (hash-ref ltab-entry 'escapes?)
         (values n* (make-hash))
         (params! ltab label n*)))
     (hash-set! ltab-entry 'params params)
     (define stmt-acc (make-gvector))
     (for ([stmt s*])
       (Stmt stmt env stmt-acc))
     (hash-set! ltab-entry 'stmts (gvector->list stmt-acc))
     (hash-set! ltab-entry 'transfer (Transfer t env))])

  (Stmt : Stmt (ir env stmt-acc) -> * ()
    [(def ,n ,e) (Expr e n env stmt-acc)]
    [,e (Expr e #f env stmt-acc)])

  (Transfer : Transfer (ir env) -> Transfer ()
    [(goto ,x ,a* ...) `(goto ,(Var x env) ,(map (cute Atom <> env) a*) ...)]
    [(ffncall ,x ,a* ...) `(ffncall ,(Var x env) ,(map (cute Atom <> env) a*) ...)]
    [(if ,a? ,x1 ,x2) `(if ,(Atom a? env) ,(Var x1 env) ,(Var x2 env))]
    [(halt ,a) `(halt ,(Atom a env))])

  (ShrinkTransfer : Transfer (ir label keep-indices) -> Transfer ()
    [(goto ,x ,a* ...)
     (define-values (callee args) (shrink-call label keep-indices x a*))
     `(goto ,callee ,args ...)]
    [(ffncall ,x ,a* ...) `(ffncall ,x ,a* ...)]
    [(if ,a? ,x1 ,x2)
     (define-values (callee1 _) (shrink-call label keep-indices x1 '()))
     (define-values (callee2 _*) (shrink-call label keep-indices x2 '()))
     `(if ,a? ,callee1 ,callee2)]
    [(halt ,a) ir])

  (Expr : Expr (ir name env stmt-acc) -> Expr ()
    [(primcall ,p ,a* ...)
     (emit-stmt! stmt-acc name `(primcall ,p ,(map (cute Atom <> env) a*) ...))]
    [,a (hash-set! env name (Atom a env))])

  (Atom : Atom (ir env) -> Atom ()
    [(const ,c) ir]
    [,x (Var x env)])

  (Var : Var (ir env) -> Var ()
    [(lex ,n) (hash-ref env n ir)]
    [(label ,n) ir]
    [(proc ,n) ir]))
