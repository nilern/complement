#lang racket/base

(provide Core parse-Core)

(require nanopass/base)

(define name? symbol?)

(define const? number?)

(define-language Core
  (terminals
    (name (n))
    (const (c)))
  
  (Expr (e)
    x
    c
    (block s* ... e))

  (Stmt (s)
    (def x e)
    e)

  (Var (x)
    (lex n)
    (dyn n)))

(define-parser parse-Core Core)
