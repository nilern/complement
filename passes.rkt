#lang racket

(provide alphatize)
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
          [else env]))))
  
  (Expr : Expr (cst env) -> Expr ()
    [(block ,s* ... ,e)
     (define env* (hash-union env (block-bindings s*)))
     `(block ,(map (λ (stmt) (Stmt stmt env*)) s*) ...
             ,(Expr e env*))]
    [(fn (,x* ...) ,e)
     (define env* (hash-union env (param-bindings x*)))
     `(fn (,(map (λ (var) (Var var env*)) x*) ...)
          ,(Expr e env*))])

  (Stmt : Stmt (cst env) -> Stmt ())
    
  (Var : Var (cst env) -> Var ()
    [(lex ,n) `(lex ,(hash-ref env n))])

  (Expr cst (hash)))
