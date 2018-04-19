#lang racket/base

(provide exn:unbound exn:unbound? zip-hash unzip-hash clj-merge clj-group-by gvector-filter!
         while if-let when-let while-let if-let-values when-let-values while-let-values)
(require (only-in racket/hash hash-union)
         data/gvector
         (only-in srfi/26 cute))

;; Exception type for unbound variables in interpreters.
(struct exn:unbound exn:fail ())

;; Make an immutable hash with `ks` as the keys and `vs` as the values.
(define (zip-hash ks vs)
  (for/hash ([k ks] [v vs])
    (values k v)))

;; Return two values: the keys and the values of the hash `kvs` as lists.
(define (unzip-hash kvs)
  (define-values (ks vs)
    (for/fold ([ks '()] [vs '()])
              ([(k v) kvs])
      (values (cons k ks) (cons v vs))))
  (values (reverse ks) (reverse vs)))

;; Merge two hashes, using the value of the latter for keys that both hashes contain.
(define (clj-merge kvs kvs*)
  (hash-union kvs kvs* #:combine (lambda (_ v) v)))

;; Apply `f` to each element of `coll` and create a hash where the keys are the distinct values
;; of those applications and the value behind a key is a list of the elements that produced the key.
(define (clj-group-by f coll)
  (define groups
    (for/fold ([groups (hash)])
              ([v coll])
      (hash-update groups (f v) (cute cons v <>) '())))
  (for/hash ([(k v) groups])
    (values k (reverse v))))

;; `gvector-remove!` all elements from `gvec` for which `(pred elem)` does not return #f.
(define (gvector-filter! pred gvec)
  (let loop ([i 0])
    (if (< i (gvector-count gvec))
      (if (pred (gvector-ref gvec i))
        (begin
          (gvector-remove! gvec i)
          (loop i))
        (loop (+ i 1)))
      (void))))

;; While loop
(define-syntax while
  (syntax-rules ()
    [(while cond stmts ...)
     (let loop ()
       (when cond
         stmts ...
         (loop)))]))

;; Like `if`, but the value of the condition is bound to `name` in `then` and `otherwise`.
(define-syntax if-let
  (syntax-rules ()
    [(if-let [name condition]
       then
       otherwise)
     (let ([name condition])
       (if name
         then
         otherwise))]))

;; Like `when`, but the value of the condition is bound to `name` in `stmts`.
(define-syntax when-let
  (syntax-rules ()
    [(when-let (name condition)
       stmts ...)
     (let ([name condition])
       (when name
         stmts ...))]))

;; Like `while`, but value of condition is bound to `name` in `stmts`.
(define-syntax while-let
  (syntax-rules ()
    [(while-let [name condition] stmts ...)
     (let loop ()
       (when-let [name condition]
         stmts ...
         (loop)))]))

;; Evaluate `prod` and bind the returned values to `name` and `names`. If `name` is not #f, evaluate
;; the `then` branch. Else evaluate the `otherwise` branch.
(define-syntax if-let-values
  (syntax-rules ()
    [(if-let-values [(name names ...) prod]
       then
       otherwise)
     (let-values ([(name names ...) prod])
       (if name
         then
         otherwise))]))

;; Is to `if-let-values` what `when` is to `if`.
(define-syntax when-let-values
  (syntax-rules ()
    [(when-let-values [(name names ...) prod]
       stmts ...)
     (let-values ([(name names ...) prod])
       (when name
         stmts ...))]))

;; Evaluate `prod` and bind the returned values to `name` and `names`. If `name` is not #f, evaluate
;; `stmts` and repeat, just like `while`.
(define-syntax while-let-values
  (syntax-rules ()
    [(while-let-values [(name names ...) prod]
       stmts ...)
     (let loop ()
       (when-let-values [(name names ...) prod]
         stmts ...
         (loop)))]))
