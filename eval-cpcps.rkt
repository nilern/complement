#lang racket/base

(provide eval-CPCPS)
(require racket/match racket/undefined (only-in racket/hash hash-union) (only-in srfi/26 cute)
         nanopass/base
         "langs.rkt" (prefix-in primops: "primops.rkt")
         (prefix-in env: (submod "eval-cps.rkt" env))
         (prefix-in kenv: (submod "util.rkt" cont-env)))

;;;; Values

(module value racket/base
  (provide $fn $cont)

  (struct $fn (code env) #:transparent)
  (struct $cont (code env) #:transparent))

;;;; Eval

(require (prefix-in value: (submod "." value)))

;; TODO: dominator scoping rule
(define-pass eval-CPCPS : CPCPS (ir) -> * ()
  (definitions
    (define (eval-block stmts transfer curr-fn env kenv fenv rfenv)
      (match stmts
        [(cons stmt stmts*) (Stmt stmt curr-fn env kenv fenv rfenv stmts* transfer)]
        ['() (Transfer transfer curr-fn env kenv fenv rfenv)]))

    (define (goto k curr-fn env kenv fenv rfenv args)
      (nanopass-case (CPCPS Cont) (kenv:ref kenv k)
        [(cont (,n* ...) ,s* ... ,t)
         (define next-fn (kenv:ref rfenv k))
         (define env* (if (eq? next-fn curr-fn)
                        (env:push-args env n* args)
                        (for/hash ([name n*] [arg args]) (values name arg))))
         (eval-block s* t next-fn env* kenv fenv rfenv)]))

    (define primapply
      (let ([primapply* (primops:primapply (hash-union primops:base-ops primops:denv-ops))])
        (λ (fenv op args)
          (match* (op args)
            [('__fnNew (cons fn freevars)) (value:$fn fn (list->vector freevars))]
            [('__fnCode (list (value:$fn code _))) (kenv:ref fenv code)]
            [('__fnGet (list (or (value:$fn _ freevars) (value:$cont _ freevars)) i))
             (vector-ref freevars i)]
            [('__contNew (cons cont freevars)) (value:$cont cont (list->vector freevars))]
            [('__contCode (list (value:$cont code _))) code]
            [(_ _) (primapply* op args)])))))

  (Program : Program (ir) -> * ()
    [(prog ([,n* ,blocks*] ...) ,n)
     (define-values (kenv fenv rfenv)
       (for/fold ([kenv (hash)]
                  [fenv (hash)]
                  [rfenv (hash)])
                 ([name n*] [fn-cfg blocks*])
         (nanopass-case (CPCPS CFG) fn-cfg
           [(cfg ([,n1* ,k*] ...) (,n2* ...))
            (define entry (car n2*))
            (values (hash-union kenv (kenv:inject n1* k*))
                    (hash-set fenv name entry)
                    (for/fold ([rfenv rfenv])
                              ([label n1*])
                      (hash-set rfenv label name)))])))
     (goto (hash-ref fenv n) n (env:empty) kenv fenv rfenv '())])

  (Stmt : Stmt (ir curr-fn env kenv fenv rfenv stmts transfer) -> * ()
    [(def ,n ,e) (Expr e curr-fn env kenv fenv rfenv n stmts transfer)]
    [,e (Expr e curr-fn env kenv fenv rfenv #f stmts transfer)])

  (Expr : Expr (ir curr-fn env kenv fenv rfenv name stmts transfer) -> * ()
    [,a
     (define res (Atom a env kenv fenv))
     (define env* (if name (env:insert env name res) env))
     (eval-block stmts transfer curr-fn env* kenv fenv rfenv)]
    [(primcall ,p ,a* ...)
     (define res (primapply fenv p (map (cute Atom <> env kenv fenv) a*)))
     (define env* (if name (env:insert env name res) env))
     (eval-block stmts transfer curr-fn env* kenv fenv rfenv)])

  (Transfer : Transfer (ir curr-fn env kenv fenv rfenv) -> * ()
    [(goto ,x ,a* ...)
     (goto (Var x env kenv fenv) curr-fn env kenv fenv rfenv
           (map (cute Atom <> env kenv fenv) a*))]
    [(if ,a? ,x1 ,x2)
     (define x
       (match (Atom a? env kenv fenv)
         [#t x1]
         [#f x2]))
     (goto (Var x env kenv fenv) curr-fn env kenv fenv rfenv '())]
    [(halt ,a) (Atom a env kenv fenv)])

  (Atom : Atom (ir env kenv fenv) -> * ()
    [(const ,c) c]
    [,x (Var x env kenv fenv)])

  (Var : Var (ir env kenv fenv) -> * ()
    [(lex ,n) (env:ref env n)]
    [(label ,n) n]
    [(proc ,n) n]))
