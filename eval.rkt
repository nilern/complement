#lang racket/base

(provide eval-Core)

(require racket/match
         nanopass/base

         "langs.rkt")

;;;; Value

(module value racket/base
  (provide $fn unwrap)
  (require racket/match)
  
  (struct $fn (params body lenv))

  (define unwrap
    (match-lambda
      [(box v) (unwrap v)]
      [v v])))

;;;; Environment

(module env racket/base
  (provide empty push-block push-fn ref)
  (require racket/undefined racket/match)

  (struct $env (bindings parent) #:transparent)

  (define (empty) ($env #f '()))

  (define (push-fn parent bindings)
    ($env bindings parent))

  (define (push-block parent binders)
    ($env (map (λ (name) (cons name (box undefined)))
               binders)
          parent))

  (define (ref env name)
    (match-define ($env bs p) env)
    (match (assq name bs)
      [#f (ref p name)]
      [(cons _ value) value])))

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
    (nanopass-case (Core Stmt) stmt
      [(def (lex ,n) ,e) (values (list n) '())]
      [(def (dyn ,n) ,e) (values '() (list n))]
      [,e (values '() '())]))

  (for/fold ([lbs '()] [dbs '()])
            ([stmt stmts])
    (define-values (slbs sdbs) (stmt-binders stmt))
    (values (append slbs lbs) (append sdbs dbs))))

(define (fn-binders params args)
  (define (param-binders param arg)
    (nanopass-case (Core Var) param
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
  (nanopass-case (Core Expr) expr
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
    [(const ,c)       (continue cont c)]
    [(lex ,n) (continue cont (env:ref lenv n))]
    [(dyn ,n) (continue cont (env:ref denv n))]))

(define (eval-stmt cont lenv denv stmt)
  (nanopass-case (Core Stmt) stmt
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
     (set-box! (nanopass-case (Core Var) var
                 [(lex ,n) (env:ref lenv n)]
                 [(dyn ,n) (env:ref denv n)])
               value)
     (continue cont* value)]
    
    [(cont:$halt) value]))

;;;; Apply

(define (apply cont denv f args)
  (match-define (value:$fn params body lenv) (value:unwrap f))
  (define-values (lbs dbs) (fn-binders params args))
  (let* ([lenv* (env:push-fn lenv lbs)]
         [denv* (env:push-fn denv dbs)])
    (eval-expr cont lenv* denv* body)))

;;;; API

(define (eval-Core expr)
  (eval-expr (cont:$halt) (env:empty) (env:empty) expr))
