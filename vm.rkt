#lang racket/base

(provide run)
(require racket/match racket/undefined (only-in srfi/26 cute)
         data/gvector
         (only-in "bytecode.rkt" $chunk $code-object
                  decode-op decode-byte-arg decode-short-arg decode-atom-arg)
         (only-in "util.rkt" while))

;; TODO: Determine required register count statically for entire chunk

(struct $code-ptr (proc pc) #:transparent)
(struct $closure ([code #:mutable] env) #:transparent)

(define dyn-env hash)

(define (run program)
  (let/ec return
    (define registers (make-gvector))
    (match-define ($chunk procs entry) program)
    (define curr-proc undefined)
    (define consts undefined)
    (define instrs undefined)
    (define pc undefined)

    (define const-ref (cute vector-ref consts <>))
    (define reg-ref (cute gvector-ref registers <>))
    (define (reg-set! index value)
      (while (<= (gvector-count registers) index)
        (gvector-add! registers undefined))
      (gvector-set! registers index value))

    (define-syntax decode
      (syntax-rules (quote byte short reg atom)
        [(decode instr 'byte)
         (decode-byte-arg instr 0)]
        [(decode instr 'byte 'atom)
         (values (decode-byte-arg instr 0)
                 (decode-atom-arg instr 1 registers consts))]
        [(decode instr 'byte 'atom 'atom)
         (values (decode-byte-arg instr 0)
                 (decode-atom-arg instr 1 registers consts)
                 (decode-atom-arg instr 2 registers consts))]
        [(decode instr 'reg)
         (reg-ref (decode-byte-arg instr 0))]
        [(decode instr 'reg 'atom)
         (values (reg-ref (decode-byte-arg instr 0))
                 (decode-atom-arg instr 1 registers consts))]
        [(decode instr 'reg 'short)
         (values (reg-ref (decode-byte-arg instr 0))
                 (decode-short-arg instr))]
        [(decode instr 'reg 'atom 'atom)
         (values (reg-ref (decode-byte-arg instr 0))
                 (decode-atom-arg instr 1 registers consts)
                 (decode-atom-arg instr 2 registers consts))]
        [(decode instr 'atom)
         (decode-atom-arg instr 0 registers consts)]
        [(decode instr 'atom 'short)
         (values (decode-atom-arg instr 0 registers consts)
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
         (reg-set! dest (box undefined))]
        [(__denvNew)
         (define dest (decode instr 'byte))
         (reg-set! dest (dyn-env))]

        ;; Unary expr-stmts:
        [(__mov)
         (define-values (dest value) (decode instr 'byte 'atom))
         (reg-set! dest value)]
        [(__tupleNew)
         (define-values (dest wsize) (decode instr 'byte 'atom))
         (reg-set! dest (make-vector wsize undefined))]
        [(__fnNew)
         (define-values (dest wsize) (decode instr 'byte 'atom))
         (reg-set! dest ($closure undefined (make-vector wsize undefined)))]
        [(__contNew)
         (define-values (dest wsize) (decode instr 'byte 'atom))
         (reg-set! dest ($closure undefined (make-vector wsize undefined)))]
        [(__boxGet)
         (define-values (dest b) (decode instr 'byte 'atom))
         (reg-set! dest (unbox b))]
        [(__tupleLength)
         (define-values (dest tuple) (decode instr 'byte 'atom))
         (reg-set! dest (vector-length tuple))]
        [(__fnCode)
         (define-values (dest f) (decode instr 'byte 'atom))
         (reg-set! dest ($closure-code f))]
        [(__contCode)
         (define-values (dest cont) (decode instr 'byte 'atom))
         (reg-set! dest ($closure-code cont))]

        ;; Binary expr-stmts:
        [(__iEq)
         (define-values (dest a b) (decode instr 'byte 'atom 'atom))
         (reg-set! dest (= a b))]
        [(__iAdd)
         (define-values (dest a b) (decode instr 'byte 'atom 'atom))
         (reg-set! dest (+ a b))]
        [(__iSub)
         (define-values (dest a b) (decode instr 'byte 'atom 'atom))
         (reg-set! dest (- a b))]
        [(__iMul)
         (define-values (dest a b) (decode instr 'byte 'atom 'atom))
         (reg-set! dest (* a b))]
        [(__tupleGet)
         (define-values (dest tuple index) (decode instr 'byte 'atom 'atom))
         (reg-set! dest (vector-ref tuple index))]
        [(__closureGet)
         (define-values (dest f index) (decode instr 'byte 'atom 'atom))
         (reg-set! dest (vector-ref ($closure-env f) index))]

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
