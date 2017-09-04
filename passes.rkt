#lang racket

(provide alphatize infer-decls introduce-dyn-env straighten-blocks)
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

(define-pass introduce-dyn-env : DeclCst (cst) -> LexDeclCst ()
  (definitions
    (with-output-language (LexDeclCst Expr)
      (define (block-bindings decls)
        (define-values (bindings lex-decls)
          (for/fold ([bindings '()] [lex-decls '()])
                    ([decl decls])
            (nanopass-case (DeclCst Var) decl
              [(lex ,n) (values bindings (cons n lex-decls))]
              [(dyn ,n)
               (values (cons (list `(const ,n) `(primcall __boxNew)) bindings)
                       lex-decls)])))
        (values (reverse bindings) (reverse lex-decls)))

      (define (fn-bindings decls)
        (define-values (bindings lex-params)
          (for/fold ([bindings '()] [lex-params '()])
                    ([decl decls])
            (nanopass-case (DeclCst Var) decl
              [(lex ,n) (values bindings (cons n lex-params))]
              [(dyn ,n)
               (define n* (gensym n))
               (values (cons (list `(const ,n) n*) bindings)
                       (cons n* lex-params))])))
        (values (reverse bindings) (reverse lex-params))))
    
    (with-output-language (LexDeclCst Stmt)
      (define (emit-init denv-name)
        `(def ,denv-name (primcall __denvNew)))
      (define (emit-push denv-name* denv-name bindings)
        `(def ,denv-name*
           (primcall __denvPush ,denv-name ,(flatten bindings) ...))))
      
    (with-output-language (LexDeclCst Expr)
      (define (emit-get denv-name name)
        `(primcall __denvGet ,denv-name (const ,name)))
      (define (emit-set denv-name name expr)
        `(primcall __boxSet ,(emit-get denv-name name) ,expr))))
  
  (Expr : Expr (cst denv-name) -> Expr ()
    [(block (,x* ...) ,s* ... ,e)
     (define denv-name* (gensym 'denv))
     (define-values (bindings lex-decls) (block-bindings x*))
     `(block (,denv-name* ,lex-decls ...)
             ,(emit-push denv-name* denv-name bindings)
             ,(map (λ (stmt) (Stmt stmt denv-name*)) s*) ...
             ,(Expr e denv-name*))]
    [(fn (,x* ...) ,e)
     (define denv-name* (gensym 'denv))
     (define-values (bindings lex-params) (fn-bindings x*))
     `(fn (,denv-name ,lex-params ...)
        (block (,denv-name*)
               ,(emit-push denv-name* denv-name bindings)
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
    `(block (,denv-name)
            ,(emit-init denv-name)
            ,(Expr cst denv-name))))

(define-pass straighten-blocks : LexDeclCst (cst) -> LexCst ()
  (definitions
    (with-output-language (LexCst Stmt)
      (define (emit-init name)
        `(def ,name (primcall __boxNew))))
    (with-output-language (LexCst Expr)
      (define (emit-set name expr)
        `(primcall __boxSet ,name ,expr))
      (define (emit-get name)
        `(primcall __boxGet ,name))))
  
  (Expr : Expr (cst) -> Expr ()
    [(block (,n* ...) ,[s*] ... ,[e])
     `(block ,(append (map emit-init n*) s*) ... ,e)]
    [(fn (,n* ...) ,[e]) `(fn (,n* ...) ,e)]
    [,n (emit-get n)])

  (Stmt : Stmt (cst) -> Stmt ()
    [(def ,n ,[e]) (emit-set n e)]))
