#lang racket/base

(provide exn:unbound exn:unbound? clj-group-by)
(require (only-in racket/function curry))

(struct exn:unbound exn:fail ())

(define (clj-group-by f coll)
  (define groups
    (for/fold ([groups (hash)])
              ([v coll])
      (hash-update groups (f v) (curry cons v) '())))
  (for/hash ([(k v) groups])
    (values k (reverse v))))
