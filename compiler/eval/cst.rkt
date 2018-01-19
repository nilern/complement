#lang racket/base

(provide eval-Cst)

(require racket/undefined
         (only-in racket/list filter-map)
         racket/match
         (only-in srfi/26 cute)
         (only-in threading ~>)
         nanopass/base

         (only-in "../util.rkt" zip-hash)
         "../langs.rkt"
         (prefix-in primops: "../primops.rkt"))

;;;; Value

(module value racket/base
  (provide $closure)

  (struct $closure (cases lenv)))

;;;; Continuations

(module cont racket/base
  (provide $closure $args $precond $primargs $block $def $halt)

  (struct $closure (cont lenv denv arges) #:transparent)
  (struct $args (cont lenv denv arges f argvs) #:transparent)
  (struct $precond (cont lenv denv* body f* args denv) #:transparent)
  (struct $primargs (cont lenv denv arges op argvs) #:transparent)
  (struct $block (cont lenv denv stmts expr) #:transparent)
  (struct $def (cont lenv denv var) #:transparent)
  (struct $halt () #:transparent))

;;;; Environments

(module env racket/base
  (provide empty push-frame ref)
  (require (only-in racket/hash hash-union))

  (define (empty) (hash))

  (define (push-frame parent frame)
    (hash-union parent frame #:combine (lambda (_ v) v)))

  (define ref hash-ref))

;;;; Eval

(require (prefix-in value: (submod "." value))
         (prefix-in cont: (submod "." cont))
         (prefix-in env: (submod "." env)))

(define-pass eval-Cst : Cst (ir) -> * ()
  (definitions
    (define (make-box) (box undefined))

    (define/match (force-box _)
      [((box v)) (if (equal? v undefined) (error "Uninitialized variable") v)]
      [(v) v])

    (define (var-tag x)
      (nanopass-case (Cst Var) x
        [(lex ,n) 'lex]
        [(dyn ,n) 'dyn]))

    (define (var-name x)
      (nanopass-case (Cst Var) x
        [(lex ,n) n]
        [(dyn ,n) n]))

    (define (block-binders stmts)
      (filter-map (lambda (stmt)
                    (nanopass-case (Cst Stmt) stmt
                      [(def ,x ,e) x]
                      [,e #f]))
                  stmts))

    (define (partition-bindings bindings)
      (define (filter-bindings tag bindings)
        (for/hash ([(x v) bindings] #:when (eq? (var-tag x) tag))
          (values (var-name x) v)))
      (values (filter-bindings 'lex bindings)
              (filter-bindings 'dyn bindings)))

    (define (block-frames stmts)
      (~> (block-binders stmts)
          (zip-hash (in-producer make-box))
          partition-bindings))

    (define (case-frames params args)
      (partition-bindings (zip-hash params args)))

    (define (lookup lenv denv var)
      (nanopass-case (Cst Var) var
        [(lex ,n) (env:ref lenv n)]
        [(dyn ,n) (env:ref denv n)]))

    (define primapply (primops:primapply primops:base-ops))

    (define/match (apply _ _* _** _***)
      [((value:$closure (cons case cases) lenv) args cont denv)
       (nanopass-case (Cst Case) case
         [(case (,x* ...) ,e? ,e) (guard (eqv? (length x*) (length args)))
          (let-values ([(lbs dbs) (case-frames x* args)])
            (let ([lenv* (env:push-frame lenv lbs)]
                  [denv* (env:push-frame denv dbs)])
              (Expr e?
                    (cont:$precond cont lenv* denv* e (value:$closure cases lenv) args denv)
                    lenv* denv*)))]
         [(case (,x* ...) ,e? ,e)
          (apply (value:$closure cases lenv) args cont denv)])]
      [((value:$closure '() lenv) _ _ _) (error "No such method")])

    (define/match (continue _ _*)
      [((cont:$closure cont lenv denv (cons arge arges)) f)
       (Expr arge (cont:$args cont lenv denv arges f '()) lenv denv)]
      [((cont:$closure cont _ denv '()) value) (apply value '() cont denv)]

      [((cont:$args cont lenv denv (cons arge arges) f argvs) value)
       (Expr arge (cont:$args cont lenv denv arges f (cons value argvs)) lenv denv)]
      [((cont:$args cont _ denv '() f argvs) value)
       (apply f (reverse (cons value argvs)) cont denv)]

      [((cont:$precond cont lenv denv body _ _ _) #t) (Expr body cont lenv denv)]
      [((cont:$precond cont _ _ _ f* args denv) #f) (apply f* args cont denv)]

      [((cont:$primargs cont lenv denv (cons arge arges) op argvs) value)
       (Expr arge (cont:$primargs cont lenv denv arges op (cons value argvs)) lenv denv)]
      [((cont:$primargs cont _ _ '() op argvs) value)
       (continue cont (primapply op (reverse (cons value argvs))))]

      [((cont:$block cont lenv denv '() e) _) (Expr e cont lenv denv)]
      [((cont:$block cont lenv denv (cons s s*) e) _)
       (Stmt s (cont:$block cont lenv denv s* e) lenv denv)]

      [((cont:$def cont lenv denv var) value)
       (set-box! (lookup lenv denv var) value)
       (continue cont value)] ; `value` is arbitrary here, it won't be used

      [((cont:$halt) value) value]))

  (Expr : Expr (expr cont lenv denv) -> * ()
    [(fn ,fc* ...) (continue cont (value:$closure fc* lenv ))]
    [(call ,e ,e* ...) (Expr e (cont:$closure cont lenv denv e*) lenv denv)]
    [(primcall ,p) (continue cont (primapply p '()))]
    [(primcall ,p ,e* ...)
     (Expr (car e*) (cont:$primargs cont lenv denv (cdr e*) p '()) lenv denv)]
    [(ffncall ,e1 ,e2) (error "unimplemented")]
    [(macro ,n ,e* ...) (error "unimplemented")]
    [(block ,e) (Expr e cont lenv denv)]
    [(block ,s* ... ,e)
     (define-values (lbs dbs) (block-frames s*))
     (let ([lenv* (env:push-frame lenv lbs)]
           [denv* (env:push-frame denv dbs)])
       (Stmt (car s*) (cont:$block cont lenv* denv* (cdr s*) e) lenv* denv*))]
    [(const ,c) (continue cont c)]
    [,x (continue cont (force-box (lookup lenv denv x)))])

  (Stmt : Stmt (stmt cont lenv denv) -> * ()
    [(def ,x ,e) (Expr e (cont:$def cont lenv denv x) lenv denv)]
    [,e (Expr e cont lenv denv)])

  (Expr ir (cont:$halt) (env:empty) (env:empty)))
