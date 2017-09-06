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
    [(lex ,n) (emit-get n)]))

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
    (struct $cont:halt () #:transparent)

    (with-output-language (CPS Atom)
      (define (emit-atom aexpr)
        (if (name? aexpr)
          aexpr
          `(const ,aexpr))))
    (with-output-language (CPS Expr)
      (define (emit-cont cont cont-name)
        (match cont
          [($cont:halt) cont-name]
          [_
           (define v (gensym 'v))
           `(fn (,v) ,(eval-expr v cont cont-name))]))

      (define (emit-continue cont-name arg)
        `(call ,cont-name ,(emit-atom arg)))
      (define (emit-call cont cont-name f args)
        (match (emit-cont cont cont-name)
          [(and (? name?) k) `(call ,f ,k ,(map emit-atom args) ...)]
          [kfn
           (define k (gensym 'k))
           `(block (def ,k ,kfn)
                   (call ,f ,k ,(map emit-atom args) ...))]))
      (define (emit-primcall cont cont-name primop args)
        (match (emit-cont cont cont-name)
          [(and (? name?) k) `(primcall ,primop ,k ,(map emit-atom args) ...)]
          [kfn
           (define k (gensym 'k))
           `(block (def ,k ,kfn)
                   (primcall ,primop ,k ,(map emit-atom args) ...))]))
    
      (define (continue cont cont-name aexpr)
        (match cont
          [($cont:fn cont* arges)
           (match arges
             ['() (emit-call cont* cont-name aexpr '())]
             [(cons arge arges)
              (eval-expr arge ($cont:args cont* arges aexpr '()) cont-name)])]
          [($cont:args cont* '() f argas)
           (emit-call cont* cont-name f (reverse (cons aexpr argas)))]
          [($cont:args cont* (cons arge arges) f argas)
           (eval-expr arge ($cont:args cont* arges f (cons aexpr argas)) cont-name)]
          [($cont:primargs cont* '() op argas)
           (emit-primcall cont* cont-name op (reverse (cons aexpr argas)))]
          [($cont:primargs cont* (cons arge arges) op argas)
           (define cont** ($cont:primargs cont* arges op (cons aexpr argas)))
           (eval-expr arge cont** cont-name)]
          [($cont:block cont* '() expr)
           (eval-expr expr cont* cont-name)]
          [($cont:block cont* (cons stmt stmts) expr)
           (eval-stmt stmt ($cont:block cont* stmts expr) cont-name)]
          [($cont:def cont* name)
           `(block (def ,name ,aexpr)
                   ,(eval-expr name cont* cont-name))]
          [($cont:halt) (emit-continue cont-name aexpr)]))))
  
  (eval-expr : Expr (expr cont cont-name) -> Expr ()
    [(fn (,n* ...) ,e)
     (define f (gensym 'f))
     (define k (gensym 'k))
     `(block
        (def ,f (fn (,k ,n* ...) ,(eval-expr e ($cont:halt) k)))
        ,(continue cont cont-name f))]
    [(block ,s* ... ,e)
     (match s*
       ['() (eval-expr e cont cont-name)]
       [(cons stmt stmts)
        (eval-stmt stmt ($cont:block cont stmts e) cont-name)])]
    [(call ,e ,e* ...)
     (eval-expr e ($cont:fn cont e*) cont-name)]
    [(primcall ,p ,e* ...)
     (match e*
       ['() (emit-primcall cont cont-name p '())]
       [(cons arge arges)
        (eval-expr arge ($cont:primargs cont arges p '()) cont-name)])]
    [,n (continue cont cont-name n)]
    [(const ,c) (continue cont cont-name c)])

  (eval-stmt : Stmt (stmt cont cont-name) -> Expr ()
    [(def ,n ,e) (eval-expr e ($cont:def cont n) cont-name)]
    [,e (eval-expr e cont cont-name)])

  (let ((k (gensym 'halt)))
    `(fn (,k) ,(eval-expr cst ($cont:halt) k))))
