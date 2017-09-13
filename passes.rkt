#lang racket

(provide alphatize infer-decls lex-straighten introduce-dyn-env cps-convert)
(require racket/hash nanopass/base
         "langs.rkt")

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
     `(block ,(map (λ (stmt) (Stmt stmt env*)) s*) ...
             ,(Expr e env*))]
    [(fn (,x* ...) ,e)
     (define env* (push-frame env (param-bindings x*)))
     `(fn (,(map (λ (var) (Var var env*)) x*) ...)
          ,(Expr e env*))])

  (Stmt : Stmt (cst env) -> Stmt ())
    
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
    [(fn (,[x*] ...) ,e)
     (define lex-decls (lex-params x*))
     (define env* (env:push-fn env lex-decls))
     `(fn (,x* ...) ,(Expr e env*))]
    [(block (,x* ...) ,s* ... ,e)
     (define-values (lex-decls dyn-decls) (partition-decls x*))
     (define env* (env:push-block env lex-decls))
     (define stmts (map (λ (stmt) (Stmt stmt env*)) s*))
     (define expr (Expr e env*))
     `(block (,dyn-decls ...)
             ,(append (filter identity
                              (map (λ (ldecl) (emit-init env* ldecl))
                                   lex-decls))
                      stmts) ...
             ,expr)]
    [(lex ,n) (emit-get env n)])

  (Stmt : Stmt (cst env) -> Stmt ()
    [(def (lex ,n) ,[e]) (emit-set env n e)])

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
             (values `(def ,denv-name* (primcall __denvPush ,denv-name
                                                 ,(flatten bindings) ...))
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
                   [(stmts) (map (λ (stmt) (Stmt stmt denv-name*)) s*)]
                   [(expr) (Expr e denv-name*)])
       (if push
         `(block ,push ,stmts ... ,expr)
         `(block ,stmts ... ,expr)))]
    [(fn (,x* ...) ,e)
     (let*-values ([(bindings lex-params) (fn-bindings x*)]
                   [(push denv-name*) (emit-push denv-name bindings)]
                   [(body) (Expr e denv-name*)])
       `(fn (,denv-name ,lex-params ...)
          ,(if push
             `(block ,push ,body)
             body)))]
    [(call ,[e] ,[e*] ...) `(call ,e ,(cons denv-name e*) ...)])
        
  (Stmt : Stmt (cst denv-name) -> Stmt ()
    [(def (lex ,n) ,[e]) `(def ,n ,e)]
    [(def (dyn ,n) ,[e]) (emit-set denv-name n e)]
    [else (Expr cst denv-name)])

  (Var : Var (cst denv-name) -> Expr ()
    [(lex ,n) n]
    [(dyn ,n) (emit-get denv-name n)])

  (let ([denv-name (gensym 'denv)])
    `(block ,(emit-init denv-name)
            ,(Expr cst denv-name))))

(define-pass cps-convert : LexCst (cst) -> CPS ()
  (definitions
    (struct $cont:fn (cont arges) #:transparent)
    (struct $cont:args (cont arges callee argas) #:transparent)
    (struct $cont:primargs (cont arges op argas) #:transparent)
    (struct $cont:block (cont stmts expr) #:transparent)
    (struct $cont:def (cont name) #:transparent)
    (struct $cont:return (name) #:transparent)
    (struct $cont:halt () #:transparent)

    (with-output-language (CPS Stmt)
      (define (trivialize stmts name expr)
        (nanopass-case (CPS Expr) expr
          [,a (values a stmts)]
          [else (define name* (if name name (gensym 'v)))
                (values name* (cons `(def ,name* ,expr) stmts))]))
      
      (define (emit-stmt stmts name expr)
        (cons (if name `(def ,name ,expr) expr) stmts)))
    (with-output-language (CPS Cont)
      (define (emit-cont formals stmts transfer)
        `(cont (,formals ...) ,stmts ... ,transfer)))
    (with-output-language (CPS Transfer)
      (define (emit-transfer label expr stmts labels conts)
        (if label
          (nanopass-case (CPS Expr) expr
            [,a (values `(continue ,label ,expr) stmts labels conts)]
            [(call ,a ,a* ...)
             (values `(call ,a ,label ,a* ...) stmts labels conts)]
            [else (define v (gensym 'v))
                  (emit-transfer label v (emit-stmt stmts v expr) labels conts)])
          (nanopass-case (CPS Expr) expr
            [,a (values `(halt ,a) stmts labels conts)]
            [else (define v (gensym 'v))
                  (emit-transfer label v (emit-stmt stmts v expr) labels conts)]))))
    (with-output-language (CPS Expr)                  
      (define (continue cont expr expr-name stmt-acc label-acc cont-acc)
        (match cont
          [($cont:fn cont* '())
           (define-values (aexpr stmt-acc*) (trivialize stmt-acc expr-name expr))
           (continue cont* `(call ,aexpr) #f stmt-acc* label-acc cont-acc)]
          [($cont:fn cont* (cons arge arges))
           (define-values (aexpr stmt-acc*) (trivialize stmt-acc expr-name expr))
           (Expr arge ($cont:args cont* arges aexpr '()) stmt-acc* label-acc cont-acc)]
          [($cont:args cont* '() f argas)
           (define-values (aexpr stmt-acc*) (trivialize stmt-acc expr-name expr))
           (continue cont* `(call ,f ,(reverse (cons aexpr argas)) ...) #f
                     stmt-acc* label-acc cont-acc)]
          [($cont:args cont* (cons arge arges) f argas)
           (define-values (aexpr stmt-acc*) (trivialize stmt-acc expr-name expr))
           (Expr arge ($cont:args cont* arges f (cons aexpr argas))
                 stmt-acc* label-acc cont-acc)]
          [($cont:primargs cont* '() op argas)
           (define-values (aexpr stmt-acc*) (trivialize stmt-acc expr-name expr))
           (continue cont* `(primcall ,op ,(reverse (cons aexpr argas)) ...) #f
                     stmt-acc* label-acc cont-acc)]
          [($cont:primargs cont* (cons arge arges) op argas)
           (define-values (aexpr stmt-acc*) (trivialize stmt-acc expr-name expr))
           (Expr arge ($cont:primargs cont* arges op (cons aexpr argas))
                 stmt-acc* label-acc cont-acc)]
          [($cont:block cont* '() e)
           (Expr e cont* (emit-stmt stmt-acc expr-name expr) label-acc cont-acc)]
          [($cont:block cont* (cons stmt stmts) e)
           (Stmt stmt ($cont:block cont* stmts e)
                 (emit-stmt stmt-acc expr-name expr) label-acc cont-acc)]
          [($cont:def cont* name)
           (continue cont* expr name stmt-acc label-acc cont-acc)]
          [($cont:return label) (emit-transfer label expr stmt-acc label-acc cont-acc)]
          [($cont:halt) (emit-transfer #f expr stmt-acc label-acc cont-acc)]))))
  
  (Expr : Expr (expr cont stmt-acc label-acc cont-acc)
        -> Transfer (stmt-acc* label-acc* cont-acc*)
    [(fn (,n* ...) ,e)
     (define f
       (let*-values (((entry) (gensym 'entry))
                     ((ret) (gensym 'ret))
                     ((transfer stmts labels conts)
                      (Expr e ($cont:return ret) '() '() '())))
         (with-output-language (CPS Expr)
           `(fn ([,(cons entry (reverse labels))
                  ,(cons (emit-cont (cons ret n*) (reverse stmts) transfer)
                         (reverse conts))] ...)
                ,entry))))
     (continue cont f #f stmt-acc label-acc cont-acc)]
    [(block ,s* ... ,e)
     (match s*
       ['() (Expr e cont stmt-acc label-acc cont-acc)]
       [(cons stmt stmts)
        (Stmt stmt ($cont:block cont stmts e) stmt-acc label-acc cont-acc)])]
    [(call ,e ,e* ...)
     (Expr e ($cont:fn cont e*) stmt-acc label-acc cont-acc)]
    [(primcall ,p ,e* ...)
     (match e*
       ['() (with-output-language (CPS Expr)
              (continue cont `(primcall ,p) #f stmt-acc label-acc cont-acc))]
       [(cons arge arges)
        (Expr arge ($cont:primargs cont arges p '()) stmt-acc label-acc cont-acc)])]
    [,n (continue cont n #f stmt-acc label-acc cont-acc)]
    [(const ,c) (with-output-language (CPS Expr)
                  (continue cont `(const ,c) #f stmt-acc label-acc cont-acc))])

  (Stmt : Stmt (stmt cont stmt-acc label-acc cont-acc)
        -> Transfer (stmt-acc* label-acc* label-acc* cont-acc*)
    [(def ,n ,e) (Expr e ($cont:def cont n) stmt-acc label-acc cont-acc)]
    [,e (Expr e cont stmt-acc label-acc cont-acc)])

  (let*-values (((entry) (gensym 'main))
                ((transfer stmts labels conts)
                 (Expr cst ($cont:halt) '() '() '())))
    `(prog ([,(cons entry (reverse labels))
             ,(cons (emit-cont '() (reverse stmts) transfer)
                    (reverse conts))] ...)
           ,entry)))
