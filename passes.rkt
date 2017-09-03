#lang racket

(provide alphatize introduce-dyn-env)
(require racket/hash nanopass/base
         "langs.rkt")

(define-pass alphatize : Core (cst) -> Core ()
  (definitions
    (define (param-bindings params)
      (for/fold ([env (hash)])
                ([param params])
        (nanopass-case (Core Var) param
          [(lex ,n) (hash-set env n (gensym n))]
          [else env])))
    
    (define (block-bindings stmts)
      (for/fold ([env (hash)])
                ([stmt stmts])
        (nanopass-case (Core Stmt) stmt
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

(define-pass introduce-dyn-env : Core (cst) -> LexCore ()
  (definitions
    (define (block-bindings stmts)
      (define (stmt-bindings stmt)
        (with-output-language (LexCore Expr)
          (nanopass-case (Core Stmt) stmt
            [(def (dyn ,n) ,e) (list (list `(const ,n) `(primcall __boxNew)))]
            [else '()])))
      (append-map stmt-bindings stmts))
    
    (define (params-bindings params)
      (define (param-bindings param)
        (with-output-language (LexCore Expr)
          (nanopass-case (Core Var) param
            [(dyn ,n)
             (define n* (gensym n))
             (values (list (list `(const ,n) n*)) n*)]
            [(lex ,n) (values '() n)])))
      
      (define-values (bindings params*)
        (for/fold ([bindings '()] [params* '()])
                  ([param params])
          (define-values (bindings* param*) (param-bindings param))
          (values (append bindings* bindings) (cons param* params*))))
      (values (reverse bindings) (reverse params*))))
  
  (Expr : Expr (cst env-name) -> Expr ()
    [(block ,s* ... ,e)
     (define bindings (block-bindings s*))
     (define env-name* (gensym 'denv))
     (define push (with-output-language (LexCore Stmt)
                    `(def ,env-name*
                       (primcall __denvPush ,env-name
                                 ,(append-map identity bindings) ...))))
     `(block ,(cons push (map (λ (stmt) (Stmt stmt env-name*)) s*)) ...
             ,(Expr e env-name*))]
    [(fn (,x* ...) ,e)
     (define env-name (gensym 'denv))
     (define env-name* (gensym 'denv))
     (define-values (bindings params) (params-bindings x*))
     (define push (with-output-language (LexCore Stmt)
                    `(def ,env-name*
                       (primcall __denvPush ,env-name
                                 ,(append-map identity bindings) ...))))
     `(fn (,(cons env-name params) ...)
        (block ,(list push) ...
               ,(Expr e env-name*)))]
    [(call ,[e] ,[e*] ...) `(call ,e ,(cons env-name e*) ...)]
    [(lex ,n) n]
    [(dyn ,n) `(primcall __denvGet ,env-name (const ,n))])
        
  (Stmt : Stmt (cst env-name) -> Stmt ()
    [(def (lex ,n) ,[e]) `(def ,n ,e)]
    [(def (dyn ,n) ,[e])
     `(primcall __boxSet (primcall __denvGet ,env-name (const ,n)) ,e)]
    [else (Expr cst env-name)])

  (let* ([env-name (gensym 'denv)]
         [init (with-output-language (LexCore Stmt)
                 `(def ,env-name (primcall __denvNew)))])
  `(block ,(list init) ...
          ,(Expr cst env-name))))
