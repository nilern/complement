#lang racket/base

(provide eval-Core)

(require racket/match
         nanopass/base

         "langs.rkt")

;;;; Environment

(module env racket/base
  (provide empty push-block ref)
  (require racket/undefined racket/match)

  (struct $env (bindings parent) #:transparent)

  (define (empty) ($env #f '()))

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
  (provide $block $def $halt)
  
  (struct $block (cont lenv denv stmts expr) #:transparent)
  (struct $def (cont lenv denv var) #:transparent)
  (struct $halt () #:transparent))

(require (prefix-in env: (submod "." env))
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

;;;; Eval

(define (eval-expr cont lenv denv expr)
  (nanopass-case (Core Expr) expr
    [(block ,s* ... ,e)
     (match s*
       ['() (eval-expr cont lenv denv e)]
       [(cons stmt stmts)
        (define-values (lbs dbs) (block-binders s*))
        (let* ([lenv* (env:push-block lenv lbs)]
               [denv* (env:push-block denv dbs)]
               [cont* (cont:$block cont lenv* denv* stmts e)])
          (eval-stmt cont* lenv* denv* stmt))])]
    [,c       (continue cont c)]
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

;;;; API

(define (eval-Core expr)
  (eval-expr (cont:$halt) (env:empty) (env:empty) expr))
