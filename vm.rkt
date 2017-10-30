#lang racket/base

(provide run)
(require racket/match racket/undefined
         data/gvector
         (only-in "bytecode.rkt" $chunk $chunk-procs $chunk-entry
                  $code-object $code-object-consts $code-object-instrs
                  decode-op decode-byte-arg decode-short-arg decode-atom-arg)
         (only-in "util.rkt" while))

(struct $code-ptr (proc pc) #:transparent)
(struct $closure ([code #:mutable] env) #:transparent)

(define dyn-env hash)

(define const-ref vector-ref)
(define reg-ref vector-ref)
(define reg-set! vector-set!)
(define (atom-ref regs consts instr field-index)
  (match/values (decode-atom-arg instr field-index)
    [(0 ri) (reg-ref regs ri)]
    [(1 ci) (const-ref consts ci)]))

(define (run program)
  (let/ec return
    (match-define ($chunk regc procs entry) program)
    (define registers (make-vector regc undefined))
    (define curr-proc undefined)
    (define consts undefined)
    (define instrs undefined)
    (define pc undefined)
    
    (define-syntax decode
      (syntax-rules (quote byte short reg atom)
        [(decode instr 'byte)
         (decode-byte-arg instr 0)]
        [(decode instr 'byte 'atom)
         (values (decode-byte-arg instr 0)
                 (atom-ref registers consts instr 1))]
        [(decode instr 'byte 'atom 'atom)
         (values (decode-byte-arg instr 0)
                 (atom-ref registers consts instr 1)
                 (atom-ref registers consts instr 2))]
        [(decode instr 'reg)
         (reg-ref registers (decode-byte-arg instr 0))]
        [(decode instr 'reg 'atom)
         (values (reg-ref registers (decode-byte-arg instr 0))
                 (atom-ref registers consts instr 1))]
        [(decode instr 'reg 'short)
         (values (reg-ref registers (decode-byte-arg instr 0))
                 (decode-short-arg instr))]
        [(decode instr 'reg 'atom 'atom)
         (values (reg-ref registers (decode-byte-arg instr 0))
                 (atom-ref registers consts instr 1)
                 (atom-ref registers consts instr 2))]
        [(decode instr 'atom)
         (atom-ref registers consts instr 0)]
        [(decode instr 'atom 'short)
         (values (atom-ref registers consts instr 0)
                 (decode-short-arg instr))]))
    
    (define (call! next-proc next-pc)
      (match-define ($code-object _ next-consts next-instrs) next-proc)
      (set! curr-proc next-proc)
      (set! consts next-consts)
      (set! instrs next-instrs)
      (set! pc next-pc))

    (call! (vector-ref procs entry) 0)
    
    (while (< pc (vector-length instrs))
      (define instr (vector-ref instrs pc))
      (set! pc (+ pc 1))
      (case (decode-op instr)
        ;; Nullary expr-stmts:
        [(__boxNew)
         (define dest (decode instr 'byte))
         (reg-set! registers dest (box undefined))]
        [(__denvNew)
         (define dest (decode instr 'byte))
         (reg-set! registers dest (dyn-env))]

        ;; Unary expr-stmts:
        [(__mov)
         (define-values (dest value) (decode instr 'byte 'atom))
         (reg-set! registers dest value)]
        [(__tupleNew)
         (define-values (dest wsize) (decode instr 'byte 'atom))
         (reg-set! registers dest (make-vector wsize undefined))]
        [(__fnNew)
         (define-values (dest wsize) (decode instr 'byte 'atom))
         (reg-set! registers dest ($closure undefined (make-vector wsize undefined)))]
        [(__contNew)
         (define-values (dest wsize) (decode instr 'byte 'atom))
         (reg-set! registers dest ($closure undefined (make-vector wsize undefined)))]
        [(__boxGet)
         (define-values (dest b) (decode instr 'byte 'atom))
         (reg-set! registers dest (unbox b))]
        [(__tupleLength)
         (define-values (dest tuple) (decode instr 'byte 'atom))
         (reg-set! registers dest (vector-length tuple))]
        [(__fnCode)
         (define-values (dest f) (decode instr 'byte 'atom))
         (reg-set! registers dest ($closure-code f))]
        [(__contCode)
         (define-values (dest cont) (decode instr 'byte 'atom))
         (reg-set! registers dest ($closure-code cont))]

        ;; Binary expr-stmts:
        [(__iEq)
         (define-values (dest a b) (decode instr 'byte 'atom 'atom))
         (reg-set! registers dest (= a b))]
        [(__iAdd)
         (define-values (dest a b) (decode instr 'byte 'atom 'atom))
         (reg-set! registers dest (+ a b))]
        [(__iSub)
         (define-values (dest a b) (decode instr 'byte 'atom 'atom))
         (reg-set! registers dest (- a b))]
        [(__iMul)
         (define-values (dest a b) (decode instr 'byte 'atom 'atom))
         (reg-set! registers dest (* a b))]
        [(__tupleGet)
         (define-values (dest tuple index) (decode instr 'byte 'atom 'atom))
         (reg-set! registers dest (vector-ref tuple index))]
        [(__closureGet)
         (define-values (dest f index) (decode instr 'byte 'atom 'atom))
         (reg-set! registers dest (vector-ref ($closure-env f) index))]

        ;; Binary eff-stmts:
        [(__boxSet)
         (define-values (b value) (decode instr 'reg 'atom))
         (set-box! b value)]
        ;; ...with offsets instead of atoms:
        [(__fnInitCode)
         (define-values (f proc-index) (decode instr 'reg 'short))
         (define cob (vector-ref procs proc-index))
         (set-$closure-code! f ($code-ptr cob 0))]
        [(__contInitCode)
         (define-values (cont offset) (decode instr 'reg 'short))
         (define cont-pc (+ pc offset))
         (set-$closure-code! cont ($code-ptr curr-proc cont-pc))]

        ;; Ternary eff-stmts:
        [(__tupleInit)
         (define-values (tuple index value) (decode instr 'reg 'atom 'atom))
         (vector-set! tuple index value)]
        [(__closureInit)
         (define-values (f index value) (decode instr 'reg 'atom 'atom))
         (vector-set! ($closure-env f) index value)]

        ;; Branches (offset within curr-proc):
        [(__brf) ; branch if false
         (define-values (cond offset) (decode instr 'atom 'short))
         (unless cond
           (set! pc (+ pc offset)))]

        ;; Jumps (overwrite curr-proc etc. and pc):
        [(__ijmp) ; jump through register
         (match-define ($code-ptr next-proc next-pc) (decode instr 'reg))
         (call! next-proc next-pc)]

        ;; Interop:
        [(__halt) ; return to foreign caller
         (return (decode instr 'atom))]
         
        [else (error "unimplemented instruction" (decode-op instr))]))))
