#lang racket/base

(provide $chunk $code-object encode-stmt encode-transfer
         decode-op decode-byte-arg decode-short-arg decode-atom-arg)
(require racket/match
         data/gvector
         (only-in srfi/26 cute) (only-in threading ~>)
         nanopass/base
         (only-in "langs.rkt" ResolvedAsm)
         (prefix-in ops: "primops.rkt"))

;; FIXME: assert that indices fit into instr fields
         
(struct $chunk (procs entry) #:transparent)
(struct $code-object (name consts instr) #:transparent)

(define bit-and bitwise-and)
(define bit-or bitwise-ior)
(define ash arithmetic-shift)

(define op-width 8)
(define arg-atom-width 8)
(define arg-atom-shift 8)
(define short-arg-shift 16)
(define arg-index-shift 8)
(define arg-atom-index-shift 1)

(define op-mask (- (ash 1 op-width) 1))
(define arg-atom-mask (- (ash 1 arg-atom-width) 1))
(define arg-atom-tag-mask #b1)

(define encode-op (cute hash-ref ops:encodings <>))

(define (encode-arg-atom arg-atom)
  (nanopass-case (ResolvedAsm Atom) arg-atom
    [(reg ,i)      (bit-or (ash i arg-atom-index-shift) 0)]
    [(const ,i)    (bit-or (ash i arg-atom-index-shift) 1)]
    [(label ,n ,i) (error "unimplemented encoding" arg-atom)]
    [(proc ,n ,i)  (error "unimplemented encoding" arg-atom)]))

(define (encode-arg-atoms arg-atoms)
  (foldr (lambda (arg-atom acc)
           (~> (ash acc arg-atom-shift)
               (bit-or (encode-arg-atom arg-atom))))
         0 arg-atoms))
         
(define (encode-astmt op dest-reg encoded-args)
  (~> (ash encoded-args arg-atom-shift)
      (bit-or dest-reg)
      (ash op-width)
      (bit-or (encode-op op))))

(define (encode-stmt op dest-reg . args)
  (if dest-reg
    (match* (op args)
      [((or '__boxNew '__denvNew) '())
       (encode-astmt op dest-reg (encode-arg-atoms args))]
      [((or '__mov
            '__boxGet '__tupleNew '__tupleLength '__fnNew '__fnCode '__contNew '__contCode
            '__raise)
        (list _))
       (encode-astmt op dest-reg (encode-arg-atoms args))]
      [((or '__iEq '__iAdd '__iSub '__iMul '__tupleGet '__closureGet) (list _ _))
       (encode-astmt op dest-reg (encode-arg-atoms args))]
      [(_ _) (error "unimplemented encoding" op)])
    (match* (op args)
      [((or '__fnInitCode) (list dest proc))
       (define dest-reg
         (nanopass-case (ResolvedAsm Atom) dest
           [(reg ,i) i]
           [else (error "not a reg" dest)]))
       (define proc-index
         (nanopass-case (ResolvedAsm Atom) proc
           [(proc ,n ,i) i]
           [else (error "not a proc" proc)]))
       (~> (ash proc-index 16)
           (bit-or (ash dest-reg op-width))
           (bit-or (encode-op op)))]
      [((or '__contInitCode) (list dest label))
       (define dest-reg
         (nanopass-case (ResolvedAsm Atom) dest
           [(reg ,i) i]
           [else (error "not a reg" dest)]))
       (define label-offset
         (nanopass-case (ResolvedAsm Atom) label
           [(label ,n ,i) i]
           [else (error "not a label" label)]))
       (~> (ash label-offset 16)
           (bit-or (ash dest-reg op-width))
           (bit-or (encode-op op)))]
      [((or '__boxSet
            '__tupleInit '__closureInit)
        (cons dest args))
       (define dest-reg
         (nanopass-case (ResolvedAsm Atom) dest
           [(reg ,i) i]
           [else (error "not a reg" dest)]))
       (encode-astmt op dest-reg (encode-arg-atoms args))]
      [(_ _) (error "unimplemented encoding" op)])))
  
(define (encode-transfer op . args)
  (match* (op args)
    [('__br (list i))
     (~> (ash i short-arg-shift)
         (bit-or (encode-op op)))]
    [('__brf (list a? i))
     (~> (ash i short-arg-shift)
         (bit-or (ash (encode-arg-atom a?) arg-atom-shift))
         (bit-or (encode-op op)))]
    [('__jmp (list x))
     (nanopass-case (ResolvedAsm Var) x
       [(label ,n ,i) (~> (ash i arg-index-shift)
                          (bit-or (encode-op '__jmp)))]
       [(reg ,i) (~> (ash i arg-index-shift)
                     (bit-or (encode-op '__ijmp)))]
       [(proc ,n ,i) (~> (ash i arg-index-shift)
                         (bit-or (encode-op '__tcall)))])]
    [('__halt (list a))
     (~> (ash (encode-arg-atom a) arg-atom-shift)
         (bit-or (encode-op op)))]))

(define (decode-op instr)
  (hash-ref ops:decodings (bit-and instr op-mask)))

(define (decode-byte-arg instr index)
  (~> (ash instr (- (* (+ index 1) arg-atom-shift)))
      (bit-and arg-atom-mask)))

(define (decode-short-arg instr)
  (ash instr (- short-arg-shift)))

(define (decode-atom-arg instr index regs consts)
  (define bits (decode-byte-arg instr index))
  (case (bit-and bits arg-atom-tag-mask)
    [(0) (gvector-ref regs (ash bits (- arg-atom-index-shift)))]
    [(1) (vector-ref consts (ash bits (- arg-atom-index-shift)))]))
