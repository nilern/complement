#lang racket/base

(provide primapply)
(require racket/match racket/undefined)

;;;; Internal utilities

;; Reified primop/instruction.
(struct $op
  (call        ; function that performs the operation
   foldable?)) ; can the operation be constant-folded (if no type, range etc. error would occur)?

;; $op registry
(define ops (make-hash))

;; Prefix a symbol with "__".
(define (prefix-underscores sym)
  (string->symbol (string-append "__" (symbol->string sym))))

;; Syntax sugar for creating a new $op and adding it into the registry.
(define-syntax define-op
  (syntax-rules (-> !)
    [(_ (name . args) -> ! body ...)
     (hash-set! ops (prefix-underscores (quote name))
                ($op (lambda args body ...) #f))]
    [(_ (name . args) body ...)
     (hash-set! ops (prefix-underscores (quote name))
                ($op (lambda args body ...) #t))]))

;;;; Operations

(define-op (iEq a b) (= a b))

(define-op (iAdd a b) (+ a b))
(define-op (iSub a b) (- a b))
(define-op (iMul a b) (* a b))

(define-op (tupleNew . vals) (list->vector vals))
(define-op (tupleInit tup i v) -> !
  (vector-set! tup i v))
(define-op (tupleLength tup) (vector-length tup))
(define-op (tupleGet tup i) (vector-ref tup i))

(define-op (boxNew) (box undefined))
(define-op (boxSet box v) -> !
  (set-box! box v))
(define-op (boxGet box) (unbox box))

(define-op (denvNew) (hash))
(define-op (denvPush denv . kvs)
  (let loop ([denv denv] [kvs kvs])
    (match kvs
      [(list-rest k v kvs) (loop (hash-set denv k v) kvs)]
      ['() denv])))
(define-op (denvGet denv name) (hash-ref denv name))

(struct $fn (code env) #:transparent)
(define-op (fnNew f . freevars)
  ($fn f (list->vector freevars)))
(define-op (fnCode f) ($fn-code f))
(define-op (fnGet f i)
  (vector-ref ($fn-env f) i))

(struct $cont (code env) #:transparent)
(define-op (contNew cont . freevars)
  ($cont cont (list->vector freevars)))
(define-op (contCode k) ($cont-code k))
(define-op (contGet k i)
  (vector-ref ($cont-env k) i))

;;;; API

;; Apply a primop to arguments.
(define (primapply op args)
  (apply ($op-call (hash-ref ops op)) args))
