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
    (define (partition-decls decls)
      (define-values (lex-decls dyn-decls)
        (for/fold ([lex-decls '()] [dyn-decls '()])
                  ([decl decls])
          (nanopass-case (DeclCst Var) decl
            [(lex ,n) (values (cons n lex-decls) dyn-decls)]
            [(dyn ,n) (values lex-decls (cons n dyn-decls))])))
      (values (reverse lex-decls) (reverse dyn-decls)))
    
    (with-output-language (DynDeclCst Stmt)
      (define (emit-init name)
        `(def (lex ,name) (primcall __boxNew))))
    (with-output-language (DynDeclCst Expr)
      (define (emit-set name expr)
        `(primcall __boxSet (lex ,name) ,expr))
      (define (emit-get name)
        `(primcall __boxGet (lex ,name)))))
  
 (Expr : Expr (cst) -> Expr ()
    [(block (,x* ...) ,[s*] ... ,[e])
     (define-values (lex-decls dyn-decls) (partition-decls x*))
     `(block (,dyn-decls ...)
             ,(append (map emit-init lex-decls) s*) ...
             ,e)])

  (Stmt : Stmt (cst) -> Stmt ()
    [(def (lex ,n) ,[e]) (emit-set n e)])

  (Var : Var (cst) -> Expr ()
    [(lex ,n) (emit-get n)])) ; FIXME: should not emit __boxGet for fn params

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
      (define (emit-push denv-name* denv-name bindings)
        `(def ,denv-name*
           (primcall __denvPush ,denv-name ,(flatten bindings) ...))))
      
    (with-output-language (LexCst Expr)
      (define (emit-get denv-name name)
        `(primcall __denvGet ,denv-name (const ,name)))
      (define (emit-set denv-name name expr)
        `(primcall __boxSet ,(emit-get denv-name name) ,expr))))
  
  (Expr : Expr (cst denv-name) -> Expr ()
    [(block (,n* ...) ,s* ... ,e)
     (define denv-name* (gensym 'denv))
     (define bindings (block-bindings n*))
     `(block ,(emit-push denv-name* denv-name bindings)
             ,(map (λ (stmt) (Stmt stmt denv-name*)) s*) ...
             ,(Expr e denv-name*))]
    [(fn (,x* ...) ,e)
     (define denv-name* (gensym 'denv))
     (define-values (bindings lex-params) (fn-bindings x*))
     `(fn (,denv-name ,lex-params ...)
        (block ,(emit-push denv-name* denv-name bindings)
               ,(Expr e denv-name*)))]
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
    (struct $cont:halt (name) #:transparent)

    (with-output-language (CPS Stmt)
      (define (trivialize stmts name expr)
        (nanopass-case (CPS Expr) expr
          [,a (values a stmts)]
          [else (define name* (if name name (gensym 'v)))
                (values name* (cons `(def ,name* ,expr) stmts))]))
      
      (define (emit-stmt stmts name expr)
        (cons (if name `(def ,name ,expr) expr) stmts)))
    
    (with-output-language (CPS Transfer)
      (define (emit-transfer label expr stmts conts)
        (nanopass-case (CPS Expr) expr
          [,a (values `(continue ,label ,expr) stmts conts)]
          [(call ,a ,a* ...) (values `(call ,a ,label ,a* ...) stmts conts)]
          [else (define v (gensym 'v))
                (emit-transfer label v (emit-stmt stmts v expr) conts)])))
    (with-output-language (CPS Expr)                  
      (define (continue cont expr expr-name stmt-acc cont-acc)
        (match cont
          [($cont:fn cont* '())
           (define-values (aexpr stmt-acc*) (trivialize stmt-acc expr-name expr))
           (continue cont* `(call ,aexpr) #f stmt-acc* cont-acc)]
          [($cont:fn cont* (cons arge arges))
           (define-values (aexpr stmt-acc*) (trivialize stmt-acc expr-name expr))
           (Expr arge ($cont:args cont* arges aexpr '()) stmt-acc* cont-acc)]
          [($cont:args cont* '() f argas)
           (define-values (aexpr stmt-acc*) (trivialize stmt-acc expr-name expr))
           (continue cont* `(call ,f ,(reverse (cons aexpr argas)) ...) #f
                     stmt-acc* cont-acc)]
          [($cont:args cont* (cons arge arges) f argas)
           (define-values (aexpr stmt-acc*) (trivialize stmt-acc expr-name expr))
           (Expr arge ($cont:args cont* arges f (cons aexpr argas))
                 stmt-acc* cont-acc)]
          [($cont:primargs cont* '() op argas)
           (define-values (aexpr stmt-acc*) (trivialize stmt-acc expr-name expr))
           (continue cont* `(primcall ,op ,(reverse (cons aexpr argas)) ...) #f
                     stmt-acc* cont-acc)]
          [($cont:primargs cont* (cons arge arges) op argas)
           (define-values (aexpr stmt-acc*) (trivialize stmt-acc expr-name expr))
           (Expr arge ($cont:primargs cont* arges op (cons aexpr argas))
                 stmt-acc* cont-acc)]
          [($cont:block cont* '() e)
           (Expr e cont* (emit-stmt stmt-acc expr-name expr) cont-acc)]
          [($cont:block cont* (cons stmt stmts) e)
           (Stmt stmt ($cont:block cont* stmts e)
                 (emit-stmt stmt-acc expr-name expr) cont-acc)]
          [($cont:def cont* name)
           (continue cont* expr name stmt-acc cont-acc)]
          [($cont:halt label) (emit-transfer label expr stmt-acc cont-acc)]))))
  
  (Expr : Expr (expr cont stmt-acc cont-acc) -> Transfer (stmt-acc* cont-acc*)
    [(fn (,n* ...) ,e)
     (define f
       (let*-values (((entry) (gensym 'entry))
                     ((ret) (gensym 'ret))
                     ((transfer stmts conts)
                      (Expr e ($cont:halt ret) '() '())))
         (with-output-language (CPS Expr)
           `(fn (cont ,entry (,ret ,n* ...) ,(reverse stmts) ... ,transfer)
                ,(reverse conts) ...
                ,entry))))
     (continue cont f #f stmt-acc cont-acc)]
    [(block ,s* ... ,e)
     (match s*
       ['() (Expr e cont stmt-acc cont-acc)]
       [(cons stmt stmts)
        (Stmt stmt ($cont:block cont stmts e) stmt-acc cont-acc)])]
    [(call ,e ,e* ...)
     (Expr e ($cont:fn cont e*) stmt-acc cont-acc)]
    [(primcall ,p ,e* ...)
     (match e*
       ['() (with-output-language (CPS Expr)
              (continue cont `(primcall ,p) #f stmt-acc cont-acc))]
       [(cons arge arges)
        (Expr arge ($cont:primargs cont arges p '()) stmt-acc cont-acc)])]
    [,n (continue cont n #f stmt-acc cont-acc)]
    [(const ,c) (with-output-language (CPS Expr)
                  (continue cont `(const ,c) #f stmt-acc cont-acc))])

  (Stmt : Stmt (stmt cont stmt-acc cont-acc) -> Transfer (stmt-acc* cont-acc*)
    [(def ,n ,e) (Expr e ($cont:def cont n) stmt-acc cont-acc)]
    [,e (Expr e cont stmt-acc cont-acc)])

  (let*-values (((entry) (gensym 'main))
                ((ret) (gensym 'halt))
                ((transfer stmts conts) (Expr cst ($cont:halt ret) '() '())))
    `(fn (cont ,entry (,ret) ,(reverse stmts) ... ,transfer)
         ,(reverse conts) ...
         ,entry)))
