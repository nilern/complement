#lang racket/base

(provide primapply base-ops denv-ops)
(require racket/match racket/undefined)

;; Apply a primop to arguments. The curried ops argument is a hash from primop names to
;; implementation functions
(define ((primapply ops) op args)
  (apply (hash-ref ops op) args))

;; Basic data operations.
(define base-ops
  (hash
    '__iEq =
    '__iAdd +
    '__iSub -
    '__iMul *
    '__tupleNew vector
    '__tupleInit vector-set!
    '__tupleLength vector-length
    '__tupleGet vector-ref
    '__boxNew (λ () (box undefined))
    '__boxSet set-box!
    '__boxGet unbox))

;; Operations on dynamic environments.
(define denv-ops
  (hash
    '__denvNew hash
    '__denvPush (λ (denv . kvs)
                  (let loop ([denv denv] [kvs kvs])
                    (match kvs
                      [(list-rest k v kvs) (loop (hash-set denv k v) kvs)]
                      ['() denv])))
    '__denvGet (λ (denv k) (hash-ref denv k))))
