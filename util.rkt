#lang racket/base

(provide exn:unbound exn:unbound? clj-group-by)
(require (only-in srfi/26 cute))

(struct exn:unbound exn:fail ())

(define (clj-group-by f coll)
  (define groups
    (for/fold ([groups (hash)])
              ([v coll])
      (hash-update groups (f v) (cute cons <>) '())))
  (for/hash ([(k v) groups])
    (values k (reverse v))))
