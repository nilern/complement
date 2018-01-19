#lang racket/base

(provide census)
(require (only-in srfi/26 cute)
         (only-in threading ~>)
         nanopass/base

         "../langs.rkt")

;; TODO: use this in shrinking
;; For every use of a variable, vtab[var]['uses] += delta.
;; For every direct call of a label, ltab[label]['calls] += delta.
;; For every escaping use of a label, ltab[label]['escapes] += delta.
(define-pass census! : CPS (ir delta ltab vtab) -> * ()
  (definitions
    (define (make-var-entry) (make-hash '((uses . 0))))

    (define (make-label-entry) (make-hash '((calls . 0) (escapes . 0))))

    (define add-delta (cute + <> delta))

    (define (used! var-table name)
      (~> (hash-ref! var-table name make-var-entry)
          (hash-update! 'uses add-delta)))

    (define (escapes! label-table name)
      (~> (hash-ref! label-table name make-label-entry)
          (hash-update! 'escapes add-delta)))

    (define (called! label-table name)
      (~> (hash-ref! label-table name make-label-entry)
          (hash-update! 'calls add-delta))))

  (CFG : CFG (ir) -> * ()
    [(cfg ([,n* ,k*] ...) ,n)
     (for-each Cont k*) ; FIXME: Does not catch unreachable code. Use depth first walk from n.
     (escapes! ltab n)])

  (Cont : Cont (ir) -> * ()
    [(cont (,n* ...) ,s* ... ,t)
     (for-each Stmt s*)
     (Transfer t)])

  (Stmt : Stmt (ir) -> * ()
    [(def ,n ,e) (Expr e)]
    [,e (Expr e)])

  (Transfer : Transfer (ir) -> * ()
    [(continue ,x ,a* ...) (Callee x) (for-each Atom a*)]
    [(if ,a? ,x1 ,x2) (Atom a?) (Callee x1) (Callee x2)]
    [(call ,x1 ,x2 ,a* ...) (Callee x1) (Var x2) (for-each Atom a*)]
    [(ffncall ,x1 ,x2 ,a* ...) (Callee x1) (Var x2) (for-each Atom a*)]
    [(halt ,a) (Atom a)])

  (Expr : Expr (ir) -> * ()
    [(fn ,blocks) (CFG blocks)]
    [(primcall ,p ,a* ...) (for-each Atom a*)]
    [,a (Atom a)])

  (Atom : Atom (ir) -> * ()
    [(const ,c) (void)]
    [,x (Var x)])

  (Var : Var (ir) -> * ()
    [(lex ,n) (used! vtab n)]
    [(label ,n) (escapes! ltab n)])

  (Callee : Var (ir) -> * ()
    [(lex ,n) (used! vtab n)]
    [(label ,n) (called! ltab n)]))

;; Build var-table where vtab[var]['uses] is the number of uses of that variable
;; and label-table where ltab[label]['calls] is the number of direct calls of that label
;;                   and ltab[label]['escapes] is the number of escaping uses of that label.
(define (census ir delta)
  (let ([label-table (make-hash)]
        [var-table (make-hash)])
    (census! ir delta label-table var-table)
    (hash 'label-table label-table 'var-table var-table)))
