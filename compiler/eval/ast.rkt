#lang racket/base

(provide eval-Ast)
(require racket/match
         (only-in racket/list filter-map)
         (only-in racket/undefined undefined)
         nanopass/base

         (prefix-in cont: "cont.rkt")
         (only-in "../langs.rkt" Ast)
         (prefix-in primops: "../primops.rkt")
         (only-in "../util.rkt" clj-merge zip-hash)
         (only-in "../nanopass-util.rkt" define/nanopass))

(define-pass eval-Ast : Ast (expr) -> * ()
  (definitions
    (struct $closure (params body env))

    (define/nanopass (Ast Stmt) (stmt-var _)
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

    (define primapply (primops:primapply primops:portable-ops))

    (define (apply fn args cont _)
      (match-define ($closure params body lenv) fn)
      (Expr body cont (clj-merge lenv (case-bindings params args)) undefined))

    (define (continue cont value)
      ((cont:continue Expr Stmt continue apply primapply assign!) cont value)))

  (Stmt : Stmt (stmt cont lenv _) -> * ()
    [(def ,n ,e) (Expr e (cont:$def cont lenv undefined n) lenv undefined)]
    [,e (Expr e cont lenv undefined)])

  (Expr : Expr (expr cont lenv _) -> * ()
    [(fn (,n* ...) ,e) (continue cont ($closure n* e lenv))]
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
    [(if ,e? ,e1 ,e2) (Expr e? (cont:$if cont lenv undefined e1 e2) lenv undefined)]
    [(const ,c) (continue cont c)]
    [,n
     (define value
       (match (lookup lenv undefined n)
         [(box v) (if (equal? v undefined) (error "unbound variable") v)]
         [v v]))
     (continue cont value)])

  (Expr expr (cont:$halt) (hash) (hash)))
