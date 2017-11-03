#lang racket/base

(provide (struct-out $chunk) serialize-chunk (struct-out $code-object) encode-stmt encode-transfer)
(require racket/match
         data/gvector
         (only-in srfi/26 cute) (only-in threading ~>)
         nanopass/base
         (only-in "langs.rkt" ResolvedAsm))

;; FIXME: assert that indices fit into instr fields
         
(struct $chunk (reg-demand procs entry) #:transparent)
(struct $code-object (name consts instrs) #:transparent)

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

(define ops
  '(__mov
    __iEq __iAdd __iSub __iMul
    __boxNew __boxSet __boxGet
    __tupleNew __tupleInit __tupleLength __tupleGet
    __fnNew __fnInitCode __fnInit __fnCode __fnGet
    __contNew __contInitCode __contInit __contCode __contGet
    __denvNew __denvPush __denvGet
    __br __brf
    __jmp __ijmp
    __halt __raise))

(define op-encodings
  (for/hash ([(op i) (in-indexed ops)])
    (values op i)))

(define encode-op (cute hash-ref op-encodings <>))

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
      [((or '__iEq '__iAdd '__iSub '__iMul '__tupleGet '__fnGet '__contGet) (list _ _))
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
            '__tupleInit '__fnInit '__contInit)
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

(define (serialize-usize n out)
  (write-bytes (integer->integer-bytes n 8 #f) out))
  
(define (serialize-instr instr out)
  (write-bytes (integer->integer-bytes instr 4 #f) out))

(define (serialize-raw-string str out)
  (serialize-usize (string-length str) out)
  (write-string str out))

(define (serialize-vector vec serialize-elem out)
  (serialize-usize (vector-length vec) out)
  (for ([elem vec])
    (serialize-elem elem out)))

(define (serialize-const const out)
  (cond
    [(fixnum? const)
     (write-byte 0 out)
     (serialize-usize const out)]
    [(char? const)
     (write-byte 1 out)
     (write-char const out)]
    [(symbol? const)
     (write-byte 2 out)
     (serialize-raw-string (symbol->string const) out)]
    [(string? const)
     (write-byte 3 out)
     (serialize-raw-string const out)]
    [else (error "unable to serialize constant" const)]))

(define (serialize-proc proc out)
  (match-define ($code-object name consts instrs) proc)
  (serialize-raw-string (symbol->string name) out)
  (serialize-vector consts serialize-const out)
  (serialize-vector instrs serialize-instr out))

(define (serialize-chunk chunk out)
  (match-define ($chunk regc procs entry) chunk)
  (serialize-usize regc out)
  (serialize-usize entry out)
  (serialize-vector procs serialize-proc out))
