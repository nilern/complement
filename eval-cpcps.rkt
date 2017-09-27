#lang racket/base

(provide eval-CPCPS)
(require racket/match racket/undefined (only-in racket/hash hash-union) (only-in srfi/26 cute)
         nanopass/base
         "langs.rkt" (prefix-in env: (submod "eval-cps.rkt" env))
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
    (define (eval-block stmts transfer curr-label env kenv fenv rfenv)
      (match stmts
        [(cons stmt stmts*) (Stmt stmt curr-label env kenv fenv rfenv stmts* transfer)]
        ['() (Transfer transfer curr-label env kenv fenv rfenv)]))

    (define (goto k curr-label env kenv fenv rfenv args)
      (nanopass-case (CPCPS Cont) (kenv:ref kenv k)
        [(cont (,n* ...) ,s* ... ,t)
         (let ([env (if (eq? k curr-label)
                      (env:push-args env n* args)
                      (for/hash ([name n*] [arg args]) (values name arg)))])
           (eval-block s* t k env kenv fenv rfenv))]))

    (define (primapply fenv op args)
      (match* (op args)
        [('__iEq (list a b)) (= a b)]
        [('__denvNew '()) (env:empty)]
        [('__fnNew (cons fn freevars)) (value:$fn fn (list->vector freevars))]
        [('__fnCode (list (value:$fn code _))) (kenv:ref fenv code)]
        [('__fnGet (list (or (value:$fn _ freevars) (value:$cont _ freevars)) i))
         (vector-ref freevars i)]
        [('__contNew (cons cont freevars)) (value:$cont cont (list->vector freevars))]
        [('__contCode (list (value:$cont code _))) code]
        [('__tupleNew _) (list->vector args)]
        [('__tupleLength (list tuple)) (vector-length tuple)]
        [('__tupleGet (list tuple index)) (vector-ref tuple index)]
        [('__boxNew '()) (box undefined)]
        [('__boxSet (list loc val)) (set-box! loc val)]
        [('__boxGet (list loc)) (unbox loc)])))

  (Program : Program (ir) -> * ()
    [(prog ([,n1* ,f*] ...) ([,n2* ,k*] ...) ,n)
     (define env (env:empty))
     ;; HACK:
     (define-values (kenv fenv rfenv)
       (for/fold ([kenv (kenv:inject n2* k*)]
                  [fenv (hash)]
                  [rfenv (for/hash ([label n2*]) (values label #f))])
                 ([name n1*] [f f*])
         (nanopass-case (CPCPS Fn) f
           [(fn ([,n* ,k*] ...) ,n)
            (values (hash-union kenv (kenv:inject n* k*))
                    (hash-set fenv name n)
                    (for/fold ([rfenv rfenv])
                              ([label n*])
                      (hash-set rfenv label name)))])))
     (goto n n env kenv fenv rfenv '())])

  (Stmt : Stmt (ir curr-label env kenv fenv rfenv stmts transfer) -> * ()
    [(def ,n ,e) (Expr e curr-label env kenv fenv rfenv n stmts transfer)]
    [,e (Expr e curr-label env kenv fenv rfenv #f stmts transfer)])

  (Expr : Expr (ir curr-label env kenv fenv rfenv name stmts transfer) -> * ()
    [,a
     (define res (Atom a env kenv fenv))
     (define env* (if name (env:insert env name res) env))
     (eval-block stmts transfer curr-label env* kenv fenv rfenv)]
    [(primcall ,p ,a* ...)
     (define res (primapply fenv p (map (cute Atom <> env kenv fenv) a*)))
     (define env* (if name (env:insert env name res) env))
     (eval-block stmts transfer curr-label env* kenv fenv rfenv)])

  (Transfer : Transfer (ir curr-label env kenv fenv rfenv) -> * ()
    [(goto ,x ,a* ...)
     (goto (Var x env kenv fenv) curr-label env kenv fenv rfenv
           (map (cute Atom <> env kenv fenv) a*))]
    [(if ,a? (,x1 ,a1* ...) (,x2 ,a2* ...))
     (define-values (x a*)
       (match (Atom a? env kenv fenv)
         [#t (values x1 a1*)]
         [#f (values x2 a2*)]))
     (goto (Var x env kenv fenv) curr-label env kenv fenv rfenv
           (map (cute Atom <> env kenv fenv) a*))]
    [(halt ,a) (Atom a env kenv fenv)])

  (Atom : Atom (ir env kenv fenv) -> * ()
    [(const ,c) c]
    [,x (Var x env kenv fenv)])

  (Var : Var (ir env kenv fenv) -> * ()
    [(lex ,n) (env:ref env n)]
    [(label ,n) n]
    [(proc ,n) n]))
