#lang racket/base

(provide eval-Cst)
(require (only-in racket/list filter-map)
         racket/match
         nanopass/base

         (only-in "../util.rkt" zip-hash clj-merge)
         (only-in "../nanopass-util.rkt" define/nanopass)
         "../langs.rkt"
         (prefix-in cont: "cont.rkt")
         (only-in "../primops.rkt" primapply))

;;;; Additional value types

(module value racket/base
  (provide $closure make-box force-box)
  (require racket/match (only-in racket/undefined undefined))

  (struct $closure (cases lenv))

  (define (make-box) (box undefined))

  (define/match (force-box _)
    [((box v)) (if (equal? v undefined) (error "Uninitialized variable") v)]
    [(v) v]))

;;;; Eval

(require (prefix-in value: (submod "." value)))

(define-pass eval-Cst : Cst (ir) -> * ()
  (definitions
    (define/nanopass (Cst Var) (var-tag _)
      [(lex ,n) 'lex]
      [(dyn ,n) 'dyn])

    (define/nanopass (Cst Var) (var-name _)
      [(lex ,n) n]
      [(dyn ,n) n])

    (define/nanopass (Cst Stmt) (stmt-var _)
      [(def ,x ,e) x]
      [,e #f])

    (define (partition-bindings bindings)
      (define (filter-bindings tag bindings)
        (for/hash ([(x v) bindings] #:when (eq? (var-tag x) tag))
          (values (var-name x) v)))
      (values (filter-bindings 'lex bindings)
              (filter-bindings 'dyn bindings)))

    (define case-bindings zip-hash)

    (define (block-bindings stmts)
      (zip-hash (filter-map stmt-var stmts) (in-producer value:make-box)))

    (define (lookup lenv denv var)
      (nanopass-case (Cst Var) var
        [(lex ,n) (hash-ref lenv n)]
        [(dyn ,n) (hash-ref denv n)]))

    (define (assign! lenv denv var value)
      (set-box! (lookup lenv denv var) value))

    (define/match (apply _ _* _** _***)
      [((value:$closure (cons case cases) lenv) args cont denv)
       (nanopass-case (Cst Case) case
         [(case (,x* ...) ,e? ,e) (guard (eqv? (length x*) (length args)))
          (let-values ([(lbs dbs) (partition-bindings (case-bindings x* args))])
            (let ([lenv* (clj-merge lenv lbs)]
                  [denv* (clj-merge denv dbs)])
              (Expr e?
                    (cont:$precond cont lenv* denv* e (value:$closure cases lenv) args denv)
                    lenv* denv*)))]
         [(case (,x* ...) ,e? ,e)
          (apply (value:$closure cases lenv) args cont denv)])]
      [((value:$closure '() lenv) _ _ _) (error "No such method")])

    (define (continue cont value)
      ((cont:continue Expr Stmt continue apply primapply assign!) cont value)))

  (Expr : Expr (expr cont lenv denv) -> * ()
    [(fn ,fc* ...) (continue cont (value:$closure fc* lenv))]
    [(call ,e ,e* ...) (Expr e (cont:$closure cont lenv denv e*) lenv denv)]
    [(primcall ,p) (continue cont (primapply p '()))]
    [(primcall ,p ,e* ...)
     (Expr (car e*) (cont:$primargs cont lenv denv (cdr e*) p '()) lenv denv)]
    [(ffncall ,e1 ,e2) (error "unimplemented")]
    [(macro ,n ,e* ...) (error "unimplemented")]
    [(block ,e) (Expr e cont lenv denv)]
    [(block ,s* ... ,e)
     (define-values (lbs dbs) (partition-bindings (block-bindings s*)))
     (let ([lenv* (clj-merge lenv lbs)]
           [denv* (clj-merge denv dbs)])
       (Stmt (car s*) (cont:$block cont lenv* denv* (cdr s*) e) lenv* denv*))]
    [(const ,c) (continue cont c)]
    [,x (continue cont (value:force-box (lookup lenv denv x)))])

  (Stmt : Stmt (stmt cont lenv denv) -> * ()
    [(def ,x ,e) (Expr e (cont:$def cont lenv denv x) lenv denv)]
    [,e (Expr e cont lenv denv)])

  (Expr ir (cont:$halt) (hash) (hash)))
