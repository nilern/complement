#lang racket/base

(provide primapply base-ops denv-ops closure-op-names branch-op-names encodings decodings)
(require racket/match racket/undefined)

(define ((primapply ops) op args)
  (apply (hash-ref ops op) args))

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

(define denv-ops
  (hash
    '__denvNew hash
    '__denvPush (λ (denv . kvs)
                  (let loop ([denv denv] [kvs kvs])
                    (match kvs
                      [(list-rest k v kvs) (loop (hash-set denv k v) kvs)]
                      ['() denv])))
    '__denvGet (λ (denv k) (hash-ref denv k))))

(define closure-op-names '(__fnNew __fnCode __fnGet __contNew __contCode))

(define branch-op-names '(__br __brf __jmp __ijmp __tcall __raise __halt))

(define encodings
  (for/hash ([(op i) (in-indexed (in-sequences (in-value '__mov)
                                               (in-hash-keys base-ops)
                                               (in-hash-keys denv-ops)
                                               closure-op-names
                                               branch-op-names))])
    (values op i)))

(define decodings (for/hash ([(k v) encodings]) (values v k)))
