#lang racket/base

(provide eval-Cst)

(require racket/undefined racket/match (only-in racket/function curry)
         nanopass/base
         "langs.rkt")

;;;; Value

(module value racket/base
  (provide $fn)
  
  (struct $fn (cases lenv)))

;;;; Continuations

(module cont racket/base
  (provide $fn $args $precond $primargs $block $def $halt)

  (struct $fn (cont lenv denv arges) #:transparent)
  (struct $args (cont lenv denv arges f argvs) #:transparent)
  (struct $precond (cont lenv denv body f* args) #:transparent)
  (struct $primargs (cont lenv denv arges op argvs) #:transparent)
  (struct $block (cont lenv denv stmts expr) #:transparent)
  (struct $def (cont lenv denv var) #:transparent)
  (struct $halt () #:transparent))

;;;; Environments

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

;;;; Eval

(require (prefix-in value: (submod "." value))
         (prefix-in cont: (submod "." cont))
         (prefix-in env: (submod "." env)))

(define-pass eval-Cst : Cst (ir) -> * ()
  (definitions
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

    (define (lookup lenv denv var)
      (nanopass-case (Cst Var) var
        [(lex ,n) (env:ref lenv n)]
        [(dyn ,n) (env:ref denv n)]))
    
    (define (continue cont value)
      (match cont
        [(cont:$fn cont* lenv denv (cons arge arges))
         (define cont** (cont:$args cont* lenv denv arges value '()))
         (Expr arge cont** lenv denv)]
        [(cont:$fn cont* _ denv '())
         (apply cont* denv value '())]
        
        [(cont:$args cont* lenv denv (cons arge arges) f argvs)
         (define cont** (cont:$args cont* lenv denv arges f (cons value argvs)))
         (Expr arge cont** lenv denv)]
        [(cont:$args cont* _ denv '() f argvs)
         (apply cont* denv f (reverse (cons value argvs)))]

        [(cont:$precond cont* lenv denv body f* args)
         (match value
           [#t (Expr body cont* lenv denv)]
           [#f (apply cont* denv f* args)])]

        [(cont:$primargs cont* lenv denv (cons arge arges) op argvs)
         (define cont** (cont:$primargs cont* lenv denv arges op (cons value argvs)))
         (Expr arge cont** lenv denv)]
        [(cont:$primargs cont* _ _ '() op argvs)
         (continue cont* (primapply op (reverse (cons value argvs))))]

        [(cont:$block cont* lenv denv '() e)
         (Expr e cont* lenv denv)]
        [(cont:$block cont* lenv denv (cons s s*) e)
         (Stmt s (cont:$block cont* lenv denv s* e) lenv denv)]
    
        [(cont:$def cont* lenv denv var)
         (set-box! (lookup lenv denv var) value)
         (continue cont* value)] ; `value` is arbitrary here, it won't be used
    
        [(cont:$halt) value]))

    (define (apply cont denv f args)
      (define (accepts? argc case)
        (nanopass-case (Cst Case) case
          [(case (,x* ...) ,e? ,e) (= (length x*) argc)]))
      
      (match-define (value:$fn cases lenv) f)
      (match (filter (curry accepts? (length args)) cases)
        [(cons case cases)
         (nanopass-case (Cst Case) case
           [(case (,x* ...) ,e? ,e)
            (let*-values ([(lbs dbs) (fn-binders x* args)]
                          [(lenv*) (env:push-fn lenv lbs)]
                          [(denv*) (env:push-fn denv dbs)]
                          [(f*) (value:$fn cases lenv)]
                          [(cont*) (cont:$precond cont lenv* denv* e f* args)])
              (Expr e? cont* lenv* denv*))])]
        ['() (error "argc")]))
    
    (define (primapply op args)
      (match* (op args)
        [('__iEq (list a b)) (= a b)]
        [('__denvNew '()) (env:empty)]
        [('__tupleNew _) (list->vector args)]
        [('__tupleLength (list tuple)) (vector-length tuple)]
        [('__tupleGet (list tuple index)) (vector-ref tuple index)]
        [('__boxNew '()) (box undefined)]
        [('__boxSet (list loc val)) (set-box! loc val)]
        [('__boxGet (list loc)) (unbox loc)])))

  (Expr : Expr (expr cont lenv denv) -> * ()
    [(fn ,fc* ...) (continue cont (value:$fn fc* lenv ))]
    [(call ,e ,e* ...)
     (define cont* (cont:$fn cont lenv denv e*))
     (Expr e cont* lenv denv)]
    [(primcall ,p ,e* ...)
     (match e*
       [(cons arge arges)
        (define cont* (cont:$primargs cont lenv denv arges p '()))
        (Expr arge cont* lenv denv)]
       ['() (continue cont (primapply p '()))])]
    [(block ,e) (Expr e cont lenv denv)]
    [(block ,s* ... ,e)
     (let*-values ([(lbs dbs) (block-binders s*)]
                   [(lenv*) (env:push-block lenv lbs)]
                   [(denv*) (env:push-block denv dbs)]
                   [(cont*) (cont:$block cont lenv* denv* (cdr s*) e)])
       (Stmt (car s*) cont* lenv* denv*))]
    [(const ,c) (continue cont c)]
    [,x (continue cont (match (lookup lenv denv x)
                         [(box val) val]
                         [val val]))])

  (Stmt : Stmt (stmt cont lenv denv) -> * ()
    [(def ,x ,e) (Expr e (cont:$def cont lenv denv x) lenv denv)]
    [,e (Expr e cont lenv denv)])

  (Expr ir (cont:$halt) (env:empty) (env:empty)))
