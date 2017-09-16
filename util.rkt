#lang racket/base

(provide exn:unbound exn:unbound? clj-group-by)

(struct exn:unbound exn:fail ())

(define (clj-group-by f coll)
  (for/fold ([groups (hash)])
            ([v coll])
    (hash-update groups (f v) (λ (vs) (cons v vs)) '())))
