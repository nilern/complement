#lang racket/base

(provide name? const? primop?
         Cst DeclCst DynDeclCst LexCst Ast
         CPS TailCPS)
(require nanopass/base)

(define (name? name)
  (and (symbol? name)
       (let ([name-str (symbol->string name)])
         (or (< (string-length name-str) 2)
             (not (equal? (substring name-str 0 2) "__"))))))

(define (const? v)
  (or (number? v) (char? v) (boolean? v) (symbol? v)))

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
    (fn fc* ...)
    (call e e* ...)
    (primcall p e* ...)
    x
    (const c))

  (Stmt (s)
    (def x e)
    e)

  (Case (fc)
    (case (x* ...) e? e))

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
    (- (fn fc* ...))
    (+ (fn n fc ...))
    (- x)
    (+ n))

  (Stmt (s)
    (- (def x e))
    (+ (def n e)))

  (Case (fc)
    (- (case (x* ...) e? e))
    (+ (case (n* ...) e? e)))

  (Var (x)
    (- (lex n))
    (- (dyn n))))

(define-language Ast
  (extends LexCst)

  (Expr (e)
    (- (fn n fc ...))
    (+ (fn (n* ...) e))
    (+ (if e? e1 e2)))

  (Case (fc)
    (- (case (n* ...) e? e))))

(define-language CPS
  (terminals
    (name (n))
    (const (c))
    (primop (p)))

  (Program ()
    (prog ([n* k*] ...) n))

  (Cont (k)
    (cont (n* ...) s* ... t))

  (Stmt (s)
    (def n e)
    e)

  (Transfer (t)
    (continue n a* ...)
    (call a n a* ...)
    (halt a))
  
  (Expr (e)
    (fn ([n* k*] ...) n)
    (call a a* ...)
    (primcall p a* ...)
    a)

  (Atom (a)
    n
    (const c)))

(define-language TailCPS
  (extends CPS)

  (Expr (e)
    (- (call a a* ...))))
