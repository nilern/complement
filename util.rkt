#lang racket/base

(provide exn:unbound exn:unbound? zipmap clj-group-by)
(require (only-in srfi/26 cute))

(struct exn:unbound exn:fail ())

(define (hash-env-ref env name)
  (if (hash-has-key? env name)
    (hash-ref env name)
    (raise (exn:unbound (format "unbound variable ~s" name)
                        (current-continuation-marks)))))

(define (zipmap ks vs)
  (for/hash ([k ks] [v vs])
    (values k v)))

(define (clj-group-by f coll)
  (define groups
    (for/fold ([groups (hash)])
              ([v coll])
      (hash-update groups (f v) (cute cons v <>) '())))
  (for/hash ([(k v) groups])
    (values k (reverse v))))

(module* cont-env #f
  (provide (rename-out [zipmap inject]
                       [hash-env-ref ref])))
