#lang racket/base

(provide eval-Cst)

(require racket/match
         nanopass/base

         "langs.rkt")

;;;; Value

(module value racket/base
  (provide $fn)
  
  (struct $fn (params body lenv)))

;;;; Environment

(module env racket/base
  (provide empty push-block push-fn ref)
  (require racket/undefined racket/match)

  (struct $env (bindings parent) #:transparent)

  (define (empty) (hash))

  (define (push-fn parent bindings)
    (for/fold ([env parent])
              ([binding bindings])
      (hash-set env (car binding) (cdr binding))))

  (define (push-block parent binders)
    (for/fold ([env parent])
              ([binder binders])
      (hash-set env binder (box undefined))))

  (define ref hash-ref))

;;;; Continuations

(module cont racket/base
  (provide $fn $args $block $def $halt)

  (struct $fn (cont lenv denv arges))
  (struct $args (cont lenv denv arges f argvs))
  (struct $block (cont lenv denv stmts expr) #:transparent)
  (struct $def (cont lenv denv var) #:transparent)
  (struct $halt () #:transparent))

(require (prefix-in value: (submod "." value))
         (prefix-in env: (submod "." env))
         (prefix-in cont: (submod "." cont)))

;;;; Analysis

(define (block-binders stmts)
  (define (stmt-binders stmt)
    (nanopass-case (Cst Stmt) stmt
      [(def (lex ,n) ,e) (values (list n) '())]
      [(def (dyn ,n) ,e) (values '() (list n))]
      [,e (values '() '())]))

  (for/fold ([lbs '()] [dbs '()])
            ([stmt stmts])
    (define-values (slbs sdbs) (stmt-binders stmt))
    (values (append slbs lbs) (append sdbs dbs))))

(define (fn-binders params args)
  (define (param-binders param arg)
    (nanopass-case (Cst Var) param
      [(lex ,n) (values (list (cons n arg)) '())]
      [(dyn ,n) (values '() (list (cons n arg)))]))

  (define-values (lbs dbs)
    (for/fold ([lbs '()] [dbs '()])
              ([param params]
               [arg args])
      (define-values (plbs pdbs) (param-binders param arg))
      (values (append plbs lbs) (append pdbs dbs))))
  (values (reverse lbs) (reverse dbs)))

;;;; Eval

(define (eval-expr cont lenv denv expr)
  (nanopass-case (Cst Expr) expr
    [(fn (,x* ...) ,e)
     (continue cont (value:$fn x* e lenv))]
    [(call ,e ,e* ...)
     (define cont* (cont:$fn cont lenv denv e*))
     (eval-expr cont* lenv denv e)]
    [(block ,s* ... ,e)
     (match s*
       ['() (eval-expr cont lenv denv e)]
       [(cons stmt stmts)
        (define-values (lbs dbs) (block-binders s*))
        (let* ([lenv* (env:push-block lenv lbs)]
               [denv* (env:push-block denv dbs)]
               [cont* (cont:$block cont lenv* denv* stmts e)])
          (eval-stmt cont* lenv* denv* stmt))])]
    [(const ,c) (continue cont c)]
    [,x (define-values (env name) (nanopass-case (Cst Var) x
                                    [(lex ,n) (values lenv n)]
                                    [(dyn ,n) (values denv n)]))
        (continue cont (match (env:ref env name)
                         [(box val) val]
                         [val val]))]))

(define (eval-stmt cont lenv denv stmt)
  (nanopass-case (Cst Stmt) stmt
    [(def ,x ,e)
     (eval-expr (cont:$def cont lenv denv x) lenv denv e)]
    [,e (eval-expr cont lenv denv e)]))

;;;; Continue

(define (continue cont value)
  (match cont
    [(cont:$fn cont* lenv denv (cons arge arges))
     (define cont** (cont:$args cont* lenv denv arges value '()))
     (eval-expr cont** lenv denv arge)]
    [(cont:$fn cont* _ denv '())
     (apply cont* denv value '())]

    [(cont:$args cont* lenv denv (cons arge arges) f argvs)
     (define cont** (cont:$args cont* lenv denv arges f (cons value argvs)))
     (eval-expr cont** lenv denv arge)]
    [(cont:$args cont* _ denv '() f argvs)
     (apply cont* denv f (reverse (cons value argvs)))]

    [(cont:$block cont* lenv denv '() e)
     (eval-expr cont* lenv denv e)]
    [(cont:$block cont* lenv denv (cons s s*) e)
     (eval-stmt (cont:$block cont* lenv denv s* e) lenv denv s)]
    
    [(cont:$def cont* lenv denv var)
     (set-box! (nanopass-case (Cst Var) var
                 [(lex ,n) (env:ref lenv n)]
                 [(dyn ,n) (env:ref denv n)])
               value)
     (continue cont* value)]
    
    [(cont:$halt) value]))

;;;; Apply

(define (apply cont denv f args)
  (match-define (value:$fn params body lenv) f)
  (define-values (lbs dbs) (fn-binders params args))
  (let* ([lenv* (env:push-fn lenv lbs)]
         [denv* (env:push-fn denv dbs)])
    (eval-expr cont lenv* denv* body)))

;;;; API

(define (eval-Cst expr)
  (eval-expr (cont:$halt) (env:empty) (env:empty) expr))
