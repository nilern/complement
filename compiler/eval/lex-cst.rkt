#lang racket/base

(provide eval-LexCst)
(require racket/match
         (only-in racket/list filter-map)
         (only-in racket/undefined undefined)
         (only-in threading ~>)
         nanopass/base

         (only-in "../langs.rkt" LexCst)
         (prefix-in cont: "cont.rkt")
         (prefix-in primops: "../primops.rkt")
         (only-in "../util.rkt" zip-hash clj-merge)
         (only-in "../nanopass-util.rkt" define/nanopass))

(define-pass eval-LexCst : LexCst (expr) -> * ()
  (definitions
    (struct $closure (denv-name cases lenv))

    (define/nanopass (LexCst Stmt) (stmt-var _)
      [(def ,n ,e) n]
      [,e #f])

    (define case-bindings zip-hash)

    (define (block-bindings stmts)
      (zip-hash (filter-map stmt-var stmts)
                (in-producer (lambda () (box undefined)))))

    (define (lookup lenv _ var)
      (hash-ref lenv var))

    (define (assign! lenv _ var value)
      (set-box! (lookup lenv undefined var) value))

    (define (continue cont value)
      ((cont:continue Expr Stmt continue apply primapply assign!) cont value))

    (define primapply (primops:primapply primops:portable-ops))

    (define/match (apply _ args _1 _2)
      [(($closure denv-name (cons case cases) lenv) (cons denv case-args) cont _)
       (nanopass-case (LexCst Case) case
         [(case (,n* ...) ,e? ,e) (guard (eqv? (length n*) (length case-args)))
          (define lenv* (~> lenv
                            (hash-set denv-name denv)
                            (clj-merge (case-bindings n* case-args))))
          (Expr e?
                (cont:$precond cont lenv* undefined
                               e ($closure denv-name cases lenv) args undefined)
                lenv* undefined)]
         [(case (,n* ...) ,e? ,e)
          (apply ($closure denv-name cases lenv) args cont undefined)])]
      [(($closure _ '() _1) _2 _3 _4) (error "No such method")]))

  (Stmt : Stmt (stmt cont lenv _) -> * ()
    [(def ,n ,e) (Expr e (cont:$def cont lenv undefined n) lenv undefined)]
    [,e (Expr e cont lenv undefined)])

  (Expr : Expr (expr cont lenv _) -> * ()
    [(fn ,n ,fc* ...) (continue cont ($closure n fc* lenv))]
    [(call ,e ,e* ...) (Expr e (cont:$closure cont lenv undefined e*) lenv undefined)]
    [(primcall ,p) (continue cont (primapply p '()))]
    [(primcall ,p ,e* ...)
     (Expr (car e*) (cont:$primargs cont lenv undefined (cdr e*) p '()) lenv undefined)]
    [(ffncall ,e1 ,e2 ,e3) (error "unimplemented")]
    [(macro ,n ,e* ...) (error "unimplemented")]
    [(block ,e) (Expr e cont lenv undefined)]
    [(block ,s* ... ,e)
     (let ([lenv (clj-merge lenv (block-bindings s*))])
       (Stmt (car s*) (cont:$block cont lenv undefined (cdr s*) e) lenv undefined))]
    [(const ,c) (continue cont c)]
    [,n
     (define value
       (match (lookup lenv undefined n)
         [(box v) (if (equal? v undefined) (error "unbound variable") v)]
         [v v]))
     (continue cont value)])

  (Expr expr (cont:$halt) (hash) (hash)))
