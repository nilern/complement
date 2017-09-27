#lang racket

(provide alphatize infer-decls lex-straighten introduce-dyn-env add-dispatch
         cps-convert analyze-closures closure-convert)
(require racket/hash data/gvector (only-in srfi/26 cute) (only-in threading ~> ~>>)
         nanopass/base
         (only-in "util.rkt" clj-group-by unzip-hash) "langs.rkt")

(define-pass alphatize : Cst (cst) -> Cst ()
  (definitions
    (define (param-bindings params)
      (for/fold ([env (hash)])
                ([param params])
        (nanopass-case (Cst Var) param
          [(lex ,n) (hash-set env n (gensym n))]
          [else env])))

    (define (block-bindings stmts)
      (for/fold ([env (hash)])
                ([stmt stmts])
        (nanopass-case (Cst Stmt) stmt
          [(def (lex ,n) ,e) (hash-set env n (gensym n))]
          [else env])))

    (define (push-frame env bindings)
      (hash-union env bindings #:combine (λ (_ v) v))))

  (Expr : Expr (cst env) -> Expr ()
    [(block ,s* ... ,e)
     (define env* (push-frame env (block-bindings s*)))
     `(block ,(map (cute Stmt <> env*) s*) ... ,(Expr e env*))])

  (Stmt : Stmt (cst env) -> Stmt ())

  (Case : Case (cst env) -> Case ()
    [(case (,x* ...) ,e? ,e)
     (define env* (push-frame env (param-bindings x*)))
     `(case (,(map (cute Var <> env*) x*) ...) ,(Expr e? env*) ,(Expr e env*))])

  (Var : Var (cst env) -> Var ()
    [(lex ,n) `(lex ,(hash-ref env n))])

  (Expr cst (hash)))

(define-pass infer-decls : Cst (cst) -> DeclCst ()
  (definitions
    (define (binders stmts)
      (define (stmt-binders stmt)
        (with-output-language (DeclCst Var)
          (nanopass-case (DeclCst Stmt) stmt
            [(def (lex ,n) ,e) (list `(lex ,n))]
            [(def (dyn ,n) ,e) (list `(dyn ,n))]
            [,e '()])))
      (append-map stmt-binders stmts)))

  (Expr : Expr (cst) -> Expr ()
    [(block ,[s*] ... ,[e]) `(block (,(binders s*) ...) ,s* ... ,e)]))

(define-pass lex-straighten : DeclCst (cst) -> DynDeclCst ()
  (definitions
    (define (env:empty) (hash))

    (define (env:push-fn parent binders)
      (for/fold ([env parent])
                ([binder binders])
        (hash-set env binder 'plain)))

    (define (env:push-block parent binders)
      (for/fold ([env parent])
                ([binder binders])
        (hash-set env binder (box #f))))

    (define env:ref hash-ref)

    (define (lex-params decls)
      (reverse (for/fold ([lex-decls '()])
                         ([decl decls])
                 (nanopass-case (DynDeclCst Var) decl
                   [(lex ,n) (cons n lex-decls)]
                   [(dyn ,n) lex-decls]))))

    (define (partition-decls decls)
      (define-values (lex-decls dyn-decls)
        (for/fold ([lex-decls '()] [dyn-decls '()])
                  ([decl decls])
          (nanopass-case (DeclCst Var) decl
            [(lex ,n) (values (cons n lex-decls) dyn-decls)]
            [(dyn ,n) (values lex-decls (cons n dyn-decls))])))
      (values (reverse lex-decls) (reverse dyn-decls)))

    (with-output-language (DynDeclCst Stmt)
      (define (emit-init env name)
        (match (env:ref env name)
          [(or 'plain (box 'plain) (box #f)) #f]
          [(box 'boxed) `(def (lex ,name) (primcall __boxNew))]))
      (define (emit-set env name expr)
        (match (env:ref env name)
          [(or 'plain (box 'plain)) `(def (lex ,name) ,expr)]
          [(and loc (box #f))
           (set-box! loc 'plain)
           `(def (lex ,name) ,expr)]
          [(box 'boxed) `(primcall __boxSet (lex ,name) ,expr)])))
    (with-output-language (DynDeclCst Expr)
      (define (emit-get env name)
        (match (env:ref env name)
          [(or 'plain (box 'plain)) `(lex ,name)]
          [(and loc (box status))
           (unless status (set-box! loc 'boxed))
           `(primcall __boxGet (lex ,name))]))))

  (Expr : Expr (cst env) -> Expr ()
    [(block (,x* ...) ,s* ... ,e)
     (define-values (lex-decls dyn-decls) (partition-decls x*))
     (define env* (env:push-block env lex-decls))
     (define stmts (map (cute Stmt <> env*) s*))
     (define expr (Expr e env*))
     `(block (,dyn-decls ...)
             ,(append (filter identity (map (cute emit-init env* <>) lex-decls))
                      stmts) ...
             ,expr)]
    [(lex ,n) (emit-get env n)])

  (Stmt : Stmt (cst env) -> Stmt ()
    [(def (lex ,n) ,[e]) (emit-set env n e)])

  (Case : Case (cst env) -> Case ()
    [(case (,[x*] ...) ,e? ,e)
     (define lex-decls (lex-params x*))
     (define env* (env:push-fn env lex-decls))
     `(case (,x* ...) ,(Expr e? env*) ,(Expr e env*))])

  (Expr cst (env:empty)))

(define-pass introduce-dyn-env : DynDeclCst (cst) -> LexCst ()
  (definitions
    (with-output-language (LexCst Expr)
      (define (block-bindings decls)
        (for/list ([decl decls])
          (list `(const ,decl) `(primcall __boxNew))))

      (define (fn-bindings params)
        (define-values (bindings lex-params)
          (for/fold ([bindings '()] [lex-params '()])
                    ([param params])
            (nanopass-case (DynDeclCst Var) param
              [(lex ,n) (values bindings (cons n lex-params))]
              [(dyn ,n)
               (define n* (gensym n))
               (values (cons (list `(const ,n) n*) bindings)
                       (cons n* lex-params))])))
        (values (reverse bindings) (reverse lex-params))))

    (with-output-language (LexCst Stmt)
      (define (emit-init denv-name)
        `(def ,denv-name (primcall __denvNew)))
      (define (emit-push denv-name bindings)
        (match bindings
          ['() (values #f denv-name)]
          [_ (define denv-name* (gensym 'denv))
             (values `(def ,denv-name* (primcall __denvPush ,denv-name ,(flatten bindings) ...))
                     denv-name*)])))

    (with-output-language (LexCst Expr)
      (define (emit-get denv-name name)
        `(primcall __denvGet ,denv-name (const ,name)))
      (define (emit-set denv-name name expr)
        `(primcall __boxSet ,(emit-get denv-name name) ,expr))))

  (Expr : Expr (cst denv-name) -> Expr ()
    [(block (,n* ...) ,s* ... ,e)
     (let*-values ([(bindings) (block-bindings n*)]
                   [(push denv-name*) (emit-push denv-name bindings)]
                   [(stmts) (map (cute Stmt <> denv-name*) s*)]
                   [(expr) (Expr e denv-name*)])
       (if push
         `(block ,push ,stmts ... ,expr)
         `(block ,stmts ... ,expr)))]
    [(fn ,fc* ...)
     (define denv-name (gensym 'denv))
     `(fn ,denv-name ,(map (cute Case <> denv-name) fc*) ...)]
    [(call ,[e] ,[e*] ...) `(call ,e ,(cons denv-name e*) ...)])

  (Stmt : Stmt (cst denv-name) -> Stmt ()
    [(def (lex ,n) ,[e]) `(def ,n ,e)]
    [(def (dyn ,n) ,[e]) (emit-set denv-name n e)]
    [else (Expr cst denv-name)])

  (Case : Case (cst denv-name) -> Case ()
    [(case (,x* ...) ,e? ,e)
     (let*-values ([(bindings lex-params) (fn-bindings x*)]
                   [(push denv-name) (emit-push denv-name bindings)])
       `(case (,lex-params ...) ,(Expr e? denv-name)
          ,(if push
             (with-output-language (LexCst Expr)
               `(block ,push ,(Expr e denv-name)))
             (Expr e denv-name))))])

  (Var : Var (cst denv-name) -> Expr ()
    [(lex ,n) n]
    [(dyn ,n) (emit-get denv-name n)])

  (let ([denv-name (gensym 'denv)])
    `(block ,(emit-init denv-name) ,(Expr cst denv-name))))

(define-pass add-dispatch : LexCst (ir) -> Ast ()
  (definitions
    (with-output-language (Ast Expr)
      (define (emit-cases argv cases)
        (match cases
          [(cons (list params cond body) cases*)
           `(block ,(for/list ([(p i) (in-indexed params)])
                      (with-output-language (Ast Stmt)
                        `(def ,p (primcall __tupleGet ,argv (const ,i))))) ...
                   ;; TODO: constant fold the branch (if possible) right away:
                   (if ,cond ,body ,(emit-cases argv cases*)))]
          ['() `(primcall __raise (const PreCondition))]))

      (define (emit-arities argv argc arities)
        (match arities
          [(cons (cons arity cases) arities*)
           `(if (primcall __iEq ,argc (const ,arity))
              ,(emit-cases argv cases)
              ,(emit-arities argv argc arities*))]
          ['() `(primcall __raise (const Arity))]))))

  (Expr : Expr (ir) -> Expr ()
    [(fn ,n (case (,n** ...) ,[e?*] ,[e*]) ...)
     (let* ([argv (gensym 'argv)]
            [argc (gensym 'argc)]
            [arities (~>> (map list n** e?* e*)
                          (clj-group-by (compose1 length car))
                          hash->list
                          (sort _ < #:key car))])
       `(fn (,n ,argv)
          (block
            (def ,argc (primcall __tupleLength ,argv))
            ,(emit-arities argv argc arities))))]
    [(call ,[e1] ,[e2] ,[e*] ...)
     `(call ,e1 ,e2 (primcall __tupleNew ,e* ...))]))

;; TODO: __raise doesn't return so turning it into a Transfer (just like we did
;;       with __halt) should compress the output of this somewhat
(define-pass cps-convert : Ast (ir) -> CPS ()
  (definitions
    (struct $cont:fn (cont arges) #:transparent)
    (struct $cont:if (cont then else) #:transparent)
    (struct $cont:args (cont arges callee argas) #:transparent)
    (struct $cont:primargs (cont arges op argas) #:transparent)
    (struct $cont:block (cont stmts expr) #:transparent)
    (struct $cont:def (cont name) #:transparent)
    (struct $cont:return (name) #:transparent)
    (struct $cont:halt () #:transparent)

    (struct $cfg-builder (entry labels conts))

    (define (make-cfg-builder entry)
      ($cfg-builder entry (make-gvector) (make-gvector)))

    (define (emit-cont! builder label cont)
      (gvector-add! ($cfg-builder-labels builder) label)
      (gvector-add! ($cfg-builder-conts builder) cont))

    (define (build-cfg builder)
      (values (gvector->list ($cfg-builder-labels builder))
              (gvector->list ($cfg-builder-conts builder))
              ($cfg-builder-entry builder)))

    (struct $cont-builder (label formals stmts))

    (define (make-cont-builder label formals)
      ($cont-builder label formals (make-gvector)))

      (define (emit-stmt! builder name expr)
        (with-output-language (CPS Stmt)
          (gvector-add! ($cont-builder-stmts builder)
                        (if name `(def ,name ,expr) expr))))

    (define (trivialize! builder name expr)
      (nanopass-case (CPS Expr) expr
        [,a a]
        [else (define name* (if name name (gensym 'v)))
              (emit-stmt! builder name* expr)
              (with-output-language (CPS Var) `(lex ,name*))]))

    (define (trivialize-cont! cont cfg-builder)
      (define (trivialize! param continue)
        (with-output-language (CPS Transfer)
          (define label (gensym 'k))
          (define cont-builder (make-cont-builder label (list param)))
          (continue cont-builder)
          (with-output-language (CPS Var) `(label ,label))))

      (match cont
        [($cont:return ret) ret]
        [($cont:def cont param)
         (trivialize!
          param
          (match cont
            [($cont:block cont* '() expr) (cute Expr expr cont* <> cfg-builder)]
            [($cont:block cont* (cons stmt stmts) e)
             (define cont** ($cont:block cont* stmts e))
             (cute Stmt stmt cont** <> cfg-builder)]))]
        [_
         (with-output-language (CPS Var)
           (define param (gensym 'v))
           (trivialize! param (cute continue cont `(lex ,param) #f <> cfg-builder)))]))

    (define (build-cont/transfer cont-builder transfer)
      (with-output-language (CPS Cont)
        (match-define ($cont-builder label formals stmts) cont-builder)
        (values label `(cont (,formals ...)
                             ,(gvector->list stmts) ...
                             ,transfer))))

    (define (build-cont/atom cont-builder aexpr . labels)
      (with-output-language (CPS Transfer)
        (build-cont/transfer
         cont-builder
         (match labels
           ['() `(halt ,aexpr)]
           [(list label) `(continue ,label ,aexpr)]
           [(list label1 label2) `(if ,aexpr ,label1 ,label2)]))))

    (define (build-cont/call cont-builder f label args)
      (with-output-language (CPS Transfer)
        (build-cont/transfer cont-builder `(call ,f ,label ,args ...))))

    (with-output-language (CPS Expr)
      (define (continue cont expr name-hint cont-builder cfg-builder)
        (match cont
          [($cont:fn cont* '())
           (define aexpr (trivialize! cont-builder name-hint expr))
           (define cont*-label (trivialize-cont! cont* cfg-builder))
           (let-values ([(label cont) (build-cont/call cont-builder aexpr cont*-label '())])
             (emit-cont! cfg-builder label cont))]
          [($cont:fn cont* (cons arge arges))
           (define aexpr (trivialize! cont-builder name-hint expr))
           (Expr arge ($cont:args cont* arges aexpr '()) cont-builder cfg-builder)]
          [($cont:if cont* then-expr else-expr)
           (define aexpr (trivialize! cont-builder name-hint expr))
           (define then-label (gensym 'k))
           (define else-label (gensym 'k))
           (let-values ([(label cont) (build-cont/atom cont-builder aexpr `(label ,then-label)
                                                                          `(label ,else-label))])
             (emit-cont! cfg-builder label cont))
           (define join ($cont:return (trivialize-cont! cont* cfg-builder)))
           (Expr then-expr join (make-cont-builder then-label '()) cfg-builder)
           (Expr else-expr join (make-cont-builder else-label '()) cfg-builder)]
          [($cont:args cont* '() f argas)
           (define aexpr (trivialize! cont-builder name-hint expr))
           (define cont*-label (trivialize-cont! cont* cfg-builder))
           (let-values ([(label cont)
                         (build-cont/call cont-builder f cont*-label (reverse (cons aexpr argas)))])
             (emit-cont! cfg-builder label cont))]
          [($cont:args cont* (cons arge arges) f argas)
           (define aexpr (trivialize! cont-builder name-hint expr))
           (Expr arge ($cont:args cont* arges f (cons aexpr argas))
                 cont-builder cfg-builder)]
          [($cont:primargs cont* '() op argas)
           (define aexpr (trivialize! cont-builder name-hint expr))
           (continue cont* `(primcall ,op ,(reverse (cons aexpr argas)) ...) #f
                     cont-builder cfg-builder)]
          [($cont:primargs cont* (cons arge arges) op argas)
           (define aexpr (trivialize! cont-builder name-hint expr))
           (Expr arge ($cont:primargs cont* arges op (cons aexpr argas))
                 cont-builder cfg-builder)]
          [($cont:block cont* '() e)
           (emit-stmt! cont-builder name-hint expr)
           (Expr e cont* cont-builder cfg-builder)]
          [($cont:block cont* (cons stmt stmts) e)
           (emit-stmt! cont-builder name-hint expr)
           (Stmt stmt ($cont:block cont* stmts e) cont-builder cfg-builder)]
          [($cont:def cont* name)
           (continue cont* expr name cont-builder cfg-builder)]
          [($cont:return ret)
           (define aexpr (trivialize! cont-builder name-hint expr))
           (define-values (label cont) (build-cont/atom cont-builder aexpr ret))
           (emit-cont! cfg-builder label cont)]
          [($cont:halt)
           (define aexpr (trivialize! cont-builder name-hint expr))
           (define-values (label cont) (build-cont/atom cont-builder aexpr))
           (emit-cont! cfg-builder label cont)]))))

  (Expr : Expr (expr cont cont-builder cfg-builder) -> Expr ()
    [(fn (,n* ...) ,e)
     (define f
       (let* ([entry (gensym 'entry)]
              [ret (gensym 'ret)]
              [cont-builder (make-cont-builder entry (cons ret n*))]
              [cfg-builder (make-cfg-builder entry)]
              [transfer (Expr e ($cont:return `(lex ,ret)) cont-builder cfg-builder)])
         (define-values (labels conts entry) (build-cfg cfg-builder))
         `(fn ([,labels ,conts] ...) ,entry)))
     (continue cont f #f cont-builder cfg-builder)]
    [(if ,e? ,e1 ,e2) (Expr e? ($cont:if cont e1 e2) cont-builder cfg-builder)]
    [(block ,e) (Expr e cont cont-builder cfg-builder)]
    [(block ,s ,s* ... ,e)
     (Stmt s ($cont:block cont s* e) cont-builder cfg-builder)]
    [(call ,e ,e* ...) (Expr e ($cont:fn cont e*) cont-builder cfg-builder)]
    [(primcall ,p) (continue cont `(primcall ,p) #f cont-builder cfg-builder)]
    [(primcall ,p ,e ,e* ...)
     (Expr e ($cont:primargs cont e* p '()) cont-builder cfg-builder)]
    [,n (continue cont `(lex ,n) #f cont-builder cfg-builder)]
    [(const ,c) (continue cont `(const ,c) #f cont-builder cfg-builder)])

  (Stmt : Stmt (stmt cont cont-builder cfg-builder) -> Stmt ()
    [(def ,n ,e) (Expr e ($cont:def cont n) cont-builder cfg-builder)]
    [,e (Expr e cont cont-builder cfg-builder)])

  (let* ([entry (gensym 'main)]
         [cont-builder (make-cont-builder entry '())]
         [cfg-builder (make-cfg-builder entry)]
         [transfer (Expr ir ($cont:halt) cont-builder cfg-builder)])
    (define-values (labels conts entry) (build-cfg cfg-builder))
    `(prog ([,labels ,conts] ...) ,entry)))

(module label-table racket/base
  (provide new call! escape! use-clover! transitively!)
  (require racket/set (only-in srfi/26 cute) (only-in threading ~>))

  (define (new) (make-hash))

  (define ref! (cute hash-ref! <> <> make-hash))

  (define (freevars! table label)
    (~> (ref! table label)
        (hash-ref! 'freevars mutable-set)))

  (define (call! table label)
    (~> (ref! table label)
        (hash-set! 'called? #t)))

  (define (escape! table label)
    (~> (ref! table label)
        (hash-set! 'escapes? #t)))

  (define (use-clover! table label name)
    (~> (freevars! table label)
        (set-add! name)))

  (define (transitively! table label env src-label)
    (define freevars (freevars! table label))
    (for ([fv (freevars! table src-label)]
          #:when (not (set-member? env fv)))
      (set-add! freevars fv))))

(require (prefix-in ltab: (submod "." label-table))
         (prefix-in kenv: (submod "util.rkt" cont-env)))

(define-pass analyze-closures : CPS (ir) -> * ()
  (Program : Program (ir stats visited) -> * ()
    [(prog ([,n* ,k*] ...) ,n)
     (define kenv (kenv:inject n* k*))
     (ltab:escape! stats n)
     (Cont (kenv:ref kenv n) n kenv stats visited)])

  (Cont : Cont (ir label kenv stats visited) -> * ()
    [(cont (,n* ...) ,s* ... ,t)
     (unless (set-member? visited label)
       (set-add! visited label)
       (~> (list->set n*)
           (foldl (cute Stmt <> label <> kenv stats visited) _ s*)
           (Transfer t label _ kenv stats visited)))])

  (Stmt : Stmt (ir label env kenv stats visited) -> * ()
    [(def ,n ,e)
     (Expr e label env kenv stats visited)
     (set-add env n)]
    [,e (Expr e label env kenv stats visited)])

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
    [(halt ,a) (Atom a label env kenv stats visited)])

  (Expr : Expr (ir label env kenv stats visited) -> * ()
    [(fn ([,n* ,k*] ...) ,n)
     (define kenv (kenv:inject n* k*))
     (ltab:escape! stats n)
     (Cont (kenv:ref kenv n) n kenv stats visited)
     (ltab:transitively! stats label env n)]
    [(primcall ,p ,a* ...)
     (for ([aexpr a*])
       (Atom aexpr label env kenv stats visited))]
    [,a (Atom a label env kenv stats visited)])

  (Atom : Atom (ir label env kenv stats visited) -> * ()
    [,x (Var x #f label env kenv stats visited)]
    [(const ,c) (void)])

  (Var : Var (ir call? label env kenv stats visited) -> * ()
    [(lex ,n) (unless (set-member? env n) (ltab:use-clover! stats label n))]
    [(label ,n)
     ((if call? ltab:call! ltab:escape!) stats n)
     (Cont (kenv:ref kenv n) n kenv stats visited)
     (ltab:transitively! stats label env n)])

  (let ([visited (mutable-set)]
        [stats (ltab:new)])
    (Program ir stats visited)
    stats))

(define-pass closure-convert : CPS (ir stats) -> CPCPS ()
  (definitions
    (define (fv-params env freevars)
      (for/list ([fv freevars])
        (hash-ref env fv fv)))

    (define (fv-lexen env freevars)
      (with-output-language (CPCPS Atom)
        (for/list ([fv freevars])
          `(lex ,(hash-ref env fv fv)))))

    (define (fv-loads closure env freevars)
      (with-output-language (CPCPS Stmt)
        (for/list ([(fv i) (in-indexed freevars)])
          `(def ,(hash-ref env fv fv) (primcall __fnGet (lex ,closure) (const ,i))))))

    (define (emit-cont! cont-acc interface label cont)
      (define label* (match interface
                       ['lifted label]
                       ['closed (gensym label)]))
      (hash-set! cont-acc label cont)
      (hash-set! (hash-ref stats label) interface label)))

  (Program : Program (ir) -> Program ()
    [(prog ([,n* ,k*] ...) ,n)
     (define fn-acc (make-hash))
     (define cont-acc (make-hash))
     (for ([label n*] [cont k*])
       (Cont cont label fn-acc cont-acc))
     (define-values (fn-names fns) (unzip-hash fn-acc))
     (define-values (labels conts) (unzip-hash cont-acc))
     `(prog ([,fn-names ,fns] ...)
            ([,labels ,conts] ...) ,n)])

  (Cont : Cont (ir label fn-acc cont-acc) -> Cont ()
    [(cont (,n* ...) ,s* ... ,t)
     (define ltab-entry (hash-ref stats label))
     (define freevars (hash-ref ltab-entry 'freevars))
     (define called? (hash-has-key? ltab-entry 'called?))
     (define escapes? (hash-has-key? ltab-entry 'escapes?))
     (when called?
       (let* ([env (for/hash ([fv freevars]) (values fv (gensym fv)))]
              [stmt-acc (make-gvector)])
         (for ([stmt s*])
           (Stmt stmt env fn-acc stmt-acc))
         (let ([transfer (Transfer t env stmt-acc)])
           (emit-cont! cont-acc 'lifted label `(cont (,(fv-params env freevars) ... ,n* ...)
                                                     ,(gvector->list stmt-acc) ...
                                                     ,transfer)))))
     (when escapes?
       (let ([closure (gensym label)]
             [env (for/hash ([fv freevars]) (values fv (gensym fv)))])
         (if called?
           (emit-cont! cont-acc 'closed label
             `(cont (,closure ,n* ...)
                    ,(fv-loads closure env freevars) ...
                    (goto (label ,label) ,(fv-lexen env freevars) ... ,n* ...)))
           (let ([stmt-acc (make-gvector)])
             (for ([stmt s*])
               (Stmt stmt env fn-acc stmt-acc))
             (let ([transfer (Transfer t env stmt-acc)])
               (emit-cont! cont-acc 'closed label `(cont (,closure ,n* ...)
                                                         ,(fv-loads closure env freevars) ...
                                                         ,(gvector->list stmt-acc) ...
                                                         ,transfer)))))))
     ; NOTE: unreachable continuations get implicitly eliminated here
     ])

  (Stmt : Stmt (ir env fn-acc stmt-acc) -> Stmt ()
    [(def ,n ,e) (gvector-add! stmt-acc `(def ,n ,(Expr e env fn-acc stmt-acc)))]
    [,e (gvector-add! stmt-acc (Expr e env fn-acc stmt-acc))])

  (Transfer : Transfer (ir env stmt-acc) -> Transfer ()
    [(continue ,x ,a* ...)
     (define-values (x* extra-args) (Jumpee x env stmt-acc))
     `(goto ,x* ,extra-args ... ,(map (cute Atom <> env stmt-acc) a*) ...)]
    [(if ,a? ,x1 ,x2)
     (define-values (x1* extra-args1) (Jumpee x1 env stmt-acc))
     (define-values (x2* extra-args2) (Jumpee x2 env stmt-acc))
     `(if ,(Atom a? env stmt-acc) (,x1* ,extra-args1 ...) (,x2* ,extra-args2 ...))]
    [(call ,x1 ,x2 ,a* ...)
     (define-values (x1* extra-args) (Callee x1 env stmt-acc))
     `(goto ,x1* ,extra-args ...
            ,(Escape x2 env stmt-acc) ,(map (cute Atom <> env stmt-acc) a*) ...)]
    [(halt ,a) `(halt ,(Atom a env stmt-acc))])

  (Expr : Expr (ir env fn-acc stmt-acc) -> Expr ()
    [(fn ([,n* ,k*] ...) ,n)
     (define cont-acc (make-hash))
     (for ([label n*] [cont k*])
       (Cont cont label fn-acc cont-acc))
     (define-values (labels conts) (unzip-hash cont-acc))
     (define f (gensym 'f))
     (hash-set! fn-acc f (with-output-language (CPCPS Fn) `(fn ([,labels ,conts] ...) ,n)))
     (define freevars (hash-ref (hash-ref stats n) 'freevars))
     `(primcall __fnNew (proc ,f) ,(fv-lexen env freevars) ...)]
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
     (define label (hash-ref ltab-entry 'closed))
     (define freevars (hash-ref ltab-entry 'freevars))
     (gvector-add! stmt-acc (with-output-language (CPCPS Stmt)
                              `(def ,cont (primcall __contNew (label ,label)
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
     (define freevars (hash-ref (hash-ref stats n) 'freevars))
     (values `(label ,n) (fv-lexen env freevars))]))
