#lang racket/base

(provide exn:unbound exn:unbound? zip-hash unzip-hash clj-group-by
         while when-let if-let-values when-let-values while-let-values)
(require (only-in srfi/26 cute))

(struct exn:unbound exn:fail ())

(define (zip-hash ks vs)
  (for/hash ([k ks] [v vs])
    (values k v)))

(define (unzip-hash kvs)
  (define-values (ks vs)
    (for/fold ([ks '()] [vs '()])
              ([(k v) kvs])
      (values (cons k ks) (cons v vs))))
  (values (reverse ks) (reverse vs)))

(define (clj-group-by f coll)
  (define groups
    (for/fold ([groups (hash)])
              ([v coll])
      (hash-update groups (f v) (cute cons v <>) '())))
  (for/hash ([(k v) groups])
    (values k (reverse v))))

(define-syntax while
  (syntax-rules ()
    [(while cond stmts ...)
     (let loop ()
       (when cond
         stmts ...
         (loop)))]))

(define-syntax when-let
  (syntax-rules ()
    [(when-let (name condition)
       stmts ...)
     (let ([name condition])
       (when name
         stmts ...))]))

(define-syntax if-let-values
  (syntax-rules ()
    [(if-let-values [(name names ...) prod]
       then
       otherwise)
     (let-values ([(name names ...) prod])
       (if name
         then
         otherwise))]))

(define-syntax when-let-values
  (syntax-rules ()
    [(when-let-values [(name names ...) prod]
       stmts ...)
     (let-values ([(name names ...) prod])
       (when name
         stmts ...))]))

(define-syntax while-let-values
  (syntax-rules ()
    [(while-let-values [(name names ...) prod]
       stmts ...)
     (let loop ()
       (when-let-values [(name names ...) prod]
         stmts ...
         (loop)))]))
