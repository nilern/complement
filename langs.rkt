#lang racket/base

(provide name? const? primop?
         Cst DeclCst DynDeclCst LexCst Ast CPS CPCPS)
(require nanopass/base)

;;; TODO: restrict (call e e* ...)

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

;;; TODO: make CFG component of programs and functions explicit

(define-language CPS
  (terminals
    (name (n))
    (const (c))
    (primop (p)))

  (CFG (blocks)
    (cfg ([n* k*] ...) n))

  (Cont (k)
    (cont (n* ...) s* ... t))

  (Stmt (s)
    (def n e)
    e)

  (Transfer (t)
    (continue x a* ...)
    (if a? x1 x2)
    (call x1 x2 a* ...)
    (halt a))

  (Expr (e)
    (fn blocks)
    (primcall p a* ...)
    a)

  (Atom (a)
    x
    (const c))

  (Var (x)
    (lex n)
    (label n)))

(define-language CPCPS
  (extends CPS)
  (entry Program)

  (Program ()
    (+ (prog ([n1* f*] ...) blocks)))

  (Fn (f)
    (+ (fn blocks)))

  (CFG (blocks)
    (- (cfg ([n* k*] ...) n))
    (+ (cfg ([n1* k*] ...) (n2* ...))))

  (Transfer (t)
    (- (continue x a* ...))
    (- (if a? x1 x2))
    (- (call x1 x2 a* ...))
    (+ (goto x a* ...))
    (+ (if a? (x1 a1* ...) (x2 a2* ...))))

  (Expr (e)
    (- (fn blocks)))

  (Var (x)
    (+ (proc n))))
