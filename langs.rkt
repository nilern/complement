#lang racket/base

(provide Core parse-Core LexCore)
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

(define-language Core
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

(define-parser parse-Core Core)

(define-language LexCore
  (extends Core)

  (Expr (e)
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
