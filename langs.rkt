#lang racket/base

(provide name? const? primop? Cst DeclCst DynDeclCst LexCst CPS)
(require nanopass/base)

(define (name? name)
  (and (symbol? name)
       (let ([name-str (symbol->string name)])
         (or (< (string-length name-str) 2)
             (not (equal? (substring name-str 0 2) "__"))))))

(define (const? v)
  (or number? char? boolean? symbol?))

(define (primop? name)
  (and (symbol? name)
       (let ([name-str (symbol->string name)])
         (and (>= (string-length name-str) 2)
              (equal? (substring name-str 0 2) "__")))))

(define-language Cst
  (terminals
    (name (n))
    (const (c))
    (primop (p)))
  
  (Expr (e)
    (block s* ... e)
    (fn (x* ...) e)
    (call e e* ...)
    (primcall p e* ...)
    x
    (const c))

  (Stmt (s)
    (def x e)
    e)

  (Var (x)
    (lex n)
    (dyn n)))

(define-language DeclCst
  (extends Cst)

  (Expr (e)
    (- (block s* ... e))
    (+ (block (x* ...) s* ... e))))

(define-language DynDeclCst
  (extends DeclCst)

  (Expr (e)
    (- (block (x* ...) s* ... e))
    (+ (block (n* ...) s* ... e))))

(define-language LexCst
  (extends DynDeclCst)

  (Expr (e)
    (- (block (n* ...) s* ... e))
    (+ (block s* ... e))
    (- (fn (x* ...) e))
    (+ (fn (n* ...) e))
    (- x)
    (+ n))

  (Stmt (s)
    (- (def x e))
    (+ (def n e)))

  (Var (x)
    (- (lex n))
    (- (dyn n))))

(define-language CPS
  (extends LexCst)

  (Expr (e)
;    (- (block s* ... e)) TODO (?)
;    (+ (block s* ... a))
    (- (call e e* ...))
    (+ (call a a* ...))
    (- (primcall p e* ...))
    (+ (primcall p a* ...))
    (- (const c))
    (- n)
    (+ a))

  (Atom (a)
    (+ (const c))
    (+ n)))
