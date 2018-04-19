#lang racket/base

(provide $closure $args $precond $if $primargs $block $def $halt
         continue)
(require racket/match)

(struct $closure (cont lenv denv arges) #:transparent)
(struct $args (cont lenv denv arges f argvs) #:transparent)
(struct $precond (cont lenv denv* body f* args denv) #:transparent)
(struct $if (cont lenv denv then otherwise))
(struct $primargs (cont lenv denv arges op argvs) #:transparent)
(struct $block (cont lenv denv stmts expr) #:transparent)
(struct $def (cont lenv denv var) #:transparent)
(struct $halt () #:transparent)

(define (continue Expr Stmt continue apply primapply assign!)
  (match-lambda**
    [(($closure cont lenv denv (cons arge arges)) f)
     (Expr arge ($args cont lenv denv arges f '()) lenv denv)]
    [(($closure cont _ denv '()) value) (apply value '() cont denv)]

    [(($args cont lenv denv (cons arge arges) f argvs) value)
     (Expr arge ($args cont lenv denv arges f (cons value argvs)) lenv denv)]
    [(($args cont _ denv '() f argvs) value)
     (apply f (reverse (cons value argvs)) cont denv)]

    [(($precond cont lenv denv body _ _ _) #t) (Expr body cont lenv denv)]
    [(($precond cont _ _ _ f* args denv) #f) (apply f* args cont denv)]

    [(($if cont lenv denv then otherwise) #t) (Expr then cont lenv denv)]
    [(($if cont lenv denv then otherwise) #f) (Expr otherwise cont lenv denv)]

    [(($primargs cont lenv denv (cons arge arges) op argvs) value)
     (Expr arge ($primargs cont lenv denv arges op (cons value argvs)) lenv denv)]
    [(($primargs cont _ _ '() op argvs) value)
     (continue cont (primapply op (reverse (cons value argvs))))]

    [(($block cont lenv denv '() e) _) (Expr e cont lenv denv)]
    [(($block cont lenv denv (cons s s*) e) _)
     (Stmt s ($block cont lenv denv s* e) lenv denv)]

    [(($def cont lenv denv var) value)
     (assign! lenv denv var value)
     (continue cont value)] ; `value` is arbitrary here, it won't be used

    [(($halt) value) value]))
