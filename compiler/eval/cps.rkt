#lang racket/base

(provide eval-CPS)
(require racket/match racket/hash racket/undefined (only-in srfi/26 cute)
         nanopass/base
         "../util.rkt" "../langs.rkt" (prefix-in primops: "../primops.rkt")
         (prefix-in kenv: (submod "../util.rkt" cont-env)))

;;;; Values

(module value racket/base
  (provide $fn $cont)

  (struct $fn (labels conts entry env) #:transparent)
  (struct $cont (code env) #:transparent))

;;;; Environments

(module env racket/base
  (provide empty push-args insert ref)
  (require "../util.rkt")

  (define (empty) (hash))

  (define (push-args parent formals args)
    (for/fold ([env parent])
              ([formal formals]
               [arg args])
      (hash-set env formal arg)))

  (define insert hash-set)

  (define (ref env name)
    (if (hash-has-key? env name)
      (hash-ref env name)
      (raise (exn:unbound (format "unbound variable ~s" name)
                          (current-continuation-marks))))))

;;;; Eval

(require (prefix-in value: (submod "." value))
         (prefix-in env: (submod "." env)))

;; TODO: dominator scoping rule
(define-pass eval-CPS : CPS (ir) -> * ()
  (definitions
    (define (eval-block stmts transfer env kenv)
      (match stmts
        [(cons stmt stmts*) (Stmt stmt env kenv stmts* transfer)]
        ['() (Transfer transfer env kenv)]))

    (define (apply-label k env kenv args)
      (nanopass-case (CPS Cont) k
        [(cont (,n* ...) ,s* ... ,t)
         (let ([env (env:push-args env n* args)])
           (eval-block s* t env kenv))]))

    (define (apply-cont cont kenv args)
      (match-let ([(value:$cont label env) cont])
        (apply-label label env kenv args)))

    (define (apply-fn f args)
      (match-let* ([(value:$fn labels conts entry env) f]
                   [kenv (kenv:inject labels conts)])
        (apply-label (kenv:ref kenv entry) env kenv args)))

    (define primapply (primops:primapply (hash-union primops:base-ops primops:denv-ops))))

  (CFG : CFG (ir) -> * ()
    [(cfg ([,n* ,k*] ...) ,n)
     (define env (env:empty))
     (define kenv (kenv:inject n* k*))
     (apply-label (kenv:ref kenv n) env kenv '())])

  (Stmt : Stmt (ir env kenv stmts transfer) -> * ()
    [(def ,n ,e) (Expr e env kenv n stmts transfer)]
    [,e (Expr e env kenv #f stmts transfer)])

  (Expr : Expr (ir env kenv name stmts transfer) -> * ()
    [,a
     (define res (Atom a env kenv))
     (define env* (if name (env:insert env name res) env))
     (eval-block stmts transfer env* kenv)]
    [(fn ,blocks)
     (nanopass-case (CPS CFG) blocks
       [(cfg ([,n* ,k*] ...) ,n)
        (define f (value:$fn n* k* n env))
        (define env* (if name (env:insert env name f) env))
        (eval-block stmts transfer env* kenv)])]
    [(primcall ,p ,a* ...)
     (define res (primapply p (map (cute Atom <> env kenv) a*)))
     (define env* (if name (env:insert env name res) env))
     (eval-block stmts transfer env* kenv)])

  (Transfer : Transfer (ir env kenv) -> * ()
    [(continue ,x ,a* ...)
     (apply-cont (Var x env kenv) kenv (map (cute Atom <> env kenv) a*))]
    [(if ,a? ,x1 ,x2)
     (apply-cont (Var (match (Atom a? env kenv) [#t x1] [#f x2]) env kenv) kenv '())]
    [(call ,x1 ,x2 ,a* ...)
     (apply-fn (Var x1 env kenv) (cons (Var x2 env kenv) (map (cute Atom <> env kenv) a*)))]
    [(halt ,a) (Atom a env kenv)])

   (Atom : Atom (ir env kenv) -> * ()
     [(const ,c) c]
     [,x (Var x env kenv)])

  (Var : Var (ir env kenv) -> * ()
    [(lex ,n) (env:ref env n)]
    [(label ,n) (value:$cont (kenv:ref kenv n) env)]))
