#lang racket/base

(provide define/nanopass)
(require nanopass/base)

(define-syntax define/nanopass
  (syntax-rules (:)
    [(define/nanopass (IR NonTerm) (name param params ...)
       cases ...)
     (define (name param params ...)
       (nanopass-case (IR NonTerm) param
         cases ...))]))
