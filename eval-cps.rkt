#lang racket/base

(provide eval-CPS)
(require racket/match racket/undefined nanopass/base
         "util.rkt" "langs.rkt")

;;;; Values

(module value racket/base
  (provide $fn $cont)

  (struct $fn (labels conts entry env) #:transparent)
  (struct $cont (code env) #:transparent))

;;;; Environments

(module env racket/base
  (provide empty push-args insert ref)
  (require "util.rkt")

  (define (empty) (hash))

  (define (push-args parent formals args)
    (for/fold ([env parent])
              ([formal formals]
               [arg args])
      (hash-set env formal arg)))

  (define insert hash-set)

  (define ref hash-ref))

(module cont-env racket/base
  (provide inject ref)
  (require "util.rkt")

  (define (inject names conts)
    (for/hash ([name names]
               [cont conts])
      (values name cont)))

  (define ref hash-ref))

;;;; Eval

(require (prefix-in value: (submod "." value))
         (prefix-in env: (submod "." env))
         (prefix-in kenv: (submod "." cont-env)))

;; TODO: dominator scoping rule
(define-pass eval-CPS : CPS (ir) -> * ()
  (definitions
    (define (cont-ref env kenv name)
      (with-handlers ([exn:unbound?
                       (lambda (_) (value:$cont (kenv:ref kenv name) env))])
        (env:ref env name)))

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
    
    (define (primapply op args)
      (match* (op args)
        [('__denvNew '()) (env:empty)]
        [('__boxNew '()) (box undefined)]
        [('__boxSet (list loc val)) (set-box! loc val)]
        [('__boxGet (list loc)) (unbox loc)])))

  (Program : Program (ir) -> * ()
    [(prog ([,n* ,k*] ...) ,n)
     (define env (env:empty))
     (define kenv (kenv:inject n* k*))
     (apply-label (kenv:ref kenv n) env kenv '())])

  (Stmt : Stmt (ir env kenv stmts transfer) -> * ()
    [(def ,n ,e) (Expr e env kenv n stmts transfer)]
    [,e (Expr e env kenv #f stmts transfer)])     

  (Expr : Expr (ir env kenv name stmts transfer) -> * ()
    [,a
     (define res (Atom a env))
     (define env* (if name (env:insert env name res) env))
     (eval-block stmts transfer env* kenv)]
    [(fn ([,n* ,k*] ...) ,n)
     (define f (value:$fn n* k* n env))
     (define env* (if name (env:insert env name f) env))
     (eval-block stmts transfer env* kenv)]
    [(primcall ,p ,a* ...)
     (define res (primapply p (map (λ (arg) (Atom arg env)) a*)))
     (define env* (if name (env:insert env name res) env))
     (eval-block stmts transfer env* kenv)]
    [(call ,a ,a* ...)
     (with-output-language (CPS Cont)
       (define code `(cont (,(if name name (gensym '_))) ,stmts ... ,transfer))
       (define cont (value:$cont code env))
       (apply-fn (Atom a env) (cons cont (map (λ (arg) (Atom arg env)) a*))))])

  (Atom : Atom (ir env) -> * ()
    [(const ,c) c]
    [,n (env:ref env n)])

  (Transfer : Transfer (ir env kenv) -> * ()
    [(continue ,n ,a* ...)
     (apply-cont (cont-ref env kenv n) kenv (map (λ (arg) (Atom arg env)) a*))]
    [(if ,a? ,n1 ,n2) (error "unimplemented")] ; TODO
    [(call ,a ,n ,a* ...)
     (apply-fn (Atom a env) (cons (cont-ref env kenv n)
                                  (map (λ (arg) (Atom arg env)) a*)))]
    [(halt ,a) (Atom a env)]))
