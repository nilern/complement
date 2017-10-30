#lang racket/base

(provide run)
(require racket/match racket/undefined
         data/gvector
         (only-in "bytecode.rkt" $chunk $code-object
                  decode-op decode-byte-arg decode-short-arg decode-atom-arg)
         (only-in "util.rkt" while))

;; TODO: Determine required register count statically for entire chunk

(struct $code-ptr (proc pc) #:transparent)
(struct $closure ([code #:mutable] env) #:transparent)

(define dyn-env hash)

(define make-registers make-gvector)

(define reg-ref gvector-ref)

(define (reg-set! registers index value)
  (while (<= (gvector-count registers) index)
    (gvector-add! registers undefined))
  (gvector-set! registers index value))

(define (run program)
  (let/ec return
    (match-define ($chunk procs entry) program)
    (define curr-proc (vector-ref procs entry))
    (match-define ($code-object _ consts instrs) curr-proc)
    (define registers (make-gvector))
    (define pc 0)
    
    (while (< pc (vector-length instrs))
      (define instr (vector-ref instrs pc))
      (set! pc (+ pc 1))
      (case (decode-op instr)
        ;; Nullary expr-stmts:
        [(__boxNew)
         (reg-set! registers (decode-byte-arg instr 0) (box undefined))]
        [(__denvNew)
         (reg-set! registers (decode-byte-arg instr 0) (dyn-env))]

        ;; Unary expr-stmts:
        [(__mov)
         (define dest (decode-byte-arg instr 0))
         (define value (decode-atom-arg instr 1 registers consts))
         (reg-set! registers dest value)]
        [(__tupleNew)
         (define dest (decode-byte-arg instr 0))
         (define wsize (decode-atom-arg instr 1 registers consts))
         (reg-set! registers dest (make-vector wsize undefined))]
        [(__fnNew)
         (define dest (decode-byte-arg instr 0))
         (define wsize (decode-atom-arg instr 1 registers consts))
         (reg-set! registers dest ($closure undefined (make-vector wsize undefined)))]
        [(__contNew)
         (define dest (decode-byte-arg instr 0))
         (define wsize (decode-atom-arg instr 1 registers consts))
         (reg-set! registers dest ($closure undefined (make-vector wsize undefined)))]
        [(__boxGet)
         (define dest (decode-byte-arg instr 0))
         (define b (decode-atom-arg instr 1 registers consts))
         (reg-set! registers dest (unbox b))]
        [(__tupleLength)
         (define dest (decode-byte-arg instr 0))
         (define tuple (decode-atom-arg instr 1 registers consts))
         (reg-set! registers dest (vector-length tuple))]
        [(__fnCode)
         (define dest (decode-byte-arg instr 0))
         (define f (decode-atom-arg instr 1 registers consts))
         (reg-set! registers dest ($closure-code f))]
        [(__contCode)
         (define dest (decode-byte-arg instr 0))
         (define cont (decode-atom-arg instr 1 registers consts))
         (reg-set! registers dest ($closure-code cont))]

        ;; Binary expr-stmts:
        [(__iEq)
         (define dest (decode-byte-arg instr 0))
         (define a (decode-atom-arg instr 1 registers consts))
         (define b (decode-atom-arg instr 2 registers consts))
         (reg-set! registers dest (= a b))]
        [(__iAdd)
         (define dest (decode-byte-arg instr 0))
         (define a (decode-atom-arg instr 1 registers consts))
         (define b (decode-atom-arg instr 2 registers consts))
         (reg-set! registers dest (+ a b))]
        [(__iSub)
         (define dest (decode-byte-arg instr 0))
         (define a (decode-atom-arg instr 1 registers consts))
         (define b (decode-atom-arg instr 2 registers consts))
         (reg-set! registers dest (- a b))]
        [(__iMul)
         (define dest (decode-byte-arg instr 0))
         (define a (decode-atom-arg instr 1 registers consts))
         (define b (decode-atom-arg instr 2 registers consts))
         (reg-set! registers dest (* a b))]
        [(__tupleGet)
         (define dest (decode-byte-arg instr 0))
         (define tuple (decode-atom-arg instr 1 registers consts))
         (define index (decode-atom-arg instr 2 registers consts))
         (reg-set! registers dest (vector-ref tuple index))]
        [(__closureGet)
         (define dest (decode-byte-arg instr 0))
         (define f (decode-atom-arg instr 1 registers consts))
         (define index (decode-atom-arg instr 2 registers consts))
         (reg-set! registers dest (vector-ref ($closure-env f) index))]

        ;; Binary eff-stmts:
        [(__boxSet)
         (define box (reg-ref registers (decode-byte-arg instr 0)))
         (define value (decode-atom-arg instr 1 registers consts))
         (set-box! box value)]
        ;; ...with regs and offsets instead of atoms:
        [(__fnInitCode)
         (define f (reg-ref registers (decode-byte-arg instr 0)))
         (define proc-index (decode-short-arg instr))
         (define cob (vector-ref procs proc-index))
         (set-$closure-code! f ($code-ptr cob 0))]
        [(__contInitCode)
         (define cont (reg-ref registers (decode-byte-arg instr 0)))
         (define offset (decode-short-arg instr))
         (define cont-pc (+ pc offset))
         (set-$closure-code! cont ($code-ptr curr-proc cont-pc))]

        ;; Ternary eff-stmts:
        [(__tupleInit)
         (define tuple (reg-ref registers (decode-byte-arg instr 0)))
         (define index (decode-atom-arg instr 1 registers consts))
         (define value (decode-atom-arg instr 2 registers consts))
         (vector-set! tuple index value)]
        [(__closureInit)
         (define f (reg-ref registers (decode-byte-arg instr 0))) 
         (define index (decode-atom-arg instr 1 registers consts))
         (define value (decode-atom-arg instr 2 registers consts))
         (vector-set! ($closure-env f) index value)]

        ;; Branches (offset within curr-proc):
        [(__brf) ; branch if false
         (define cond (decode-atom-arg instr 0 registers consts))
         (define offset (decode-short-arg instr))
         (unless cond
           (set! pc (+ pc offset)))]

        ;; Jumps (overwrite curr-proc etc. and pc):
        [(__ijmp) ; jump through register
         (define dest-reg (decode-byte-arg instr 0))
         (match-define ($code-ptr next-proc next-pc) (reg-ref registers dest-reg))
         (match-define ($code-object _ next-consts next-instrs) next-proc)
         (set! curr-proc next-proc)
         (set! consts next-consts)
         (set! instrs next-instrs)
         (set! pc next-pc)]

        ;; Interop:
        [(__halt) ; return to foreign caller
         (return (decode-atom-arg instr 0 registers consts))]
         
        [else (error "unimplemented instruction" (decode-op instr))]))))
