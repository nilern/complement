#lang racket/base

(provide encode-stmt encode-transfer)
(require racket/match
         data/gvector
         (only-in srfi/26 cute) (only-in threading ~>)
         nanopass/base
         (only-in "../langs.rkt" ConstPoolAsm))

;; FIXME: assert that indices fit into instr fields

(define bit-and bitwise-and)
(define bit-or bitwise-ior)
(define ash arithmetic-shift)

(define op-width 8)         ; Operation bit width
(define arg-atom-width 8)   ; Regular argument bit width
(define arg-atom-shift 8)   ; TODO: remove this (since it is arg-atom-width)
(define short-arg-shift 16) ; Long argument bit width
(define arg-index-shift 8)  ; How much to shift a __jmp argument by
(define arg-atom-index-shift 1) ; How much to shift the register/constant index in an atom arg

;; Instruction names grouped by theme (e.g. integer arithmetic).
(define ops
  '((__mov __swap)

    (__iEq __iLt __iLe __iGt __iGe)
    (__iNeg __iAdd __iSub __iMul __iDiv __iRem __iMod)

    (__boxNew __boxSet __boxGet)
    (__tupleNew __tupleInit __tupleLength __tupleGet)
    (__fnNew __fnInitCode __fnInit __fnCode __fnGet)
    (__contNew __contInitCode __contInit __contCode __contGet)
    (__denvNew __denvPush __denvGet)
    (__recNew __recInitType __recInit __recType __recGet)

    (__br __brf)
    (__jmp __ijmp)
    (__halt __raise)

    (__flibOpen __flibSym __ffnNew __ffnInitType __ffnInitCConv __ffnCall)))

;; A map from instruction names to byte encodings.
(define op-encodings
  (for*/hash ([(op-group i) (in-indexed ops)]
             [(op j) (in-indexed op-group)])
    (values op (bit-or (ash i 4) j))))

;; Encode instruction name to a byte (using op-encodings)
(define encode-op (cute hash-ref op-encodings <>))

;; Extract the register index from an atom if applicable, throw otherwise.
(define (unwrap-reg atom)
  (nanopass-case (ConstPoolAsm Atom) atom
    [(reg ,i) i]
    [else (error "not a reg" atom)]))

;; Encode atom argument into a byte.
(define (encode-arg-atom arg-atom)
  (nanopass-case (ConstPoolAsm Atom) arg-atom
    [(reg ,i)      (bit-or (ash i arg-atom-index-shift) 0)]
    [(const ,i)    (bit-or (ash i arg-atom-index-shift) 1)]
    [(label ,n ,i) (error "unimplemented encoding" arg-atom)]
    [(proc ,n ,i)  (error "unimplemented encoding" arg-atom)]))

;; Encode a list of atom arguments, shifting the previous one right.
(define (encode-arg-atoms arg-atoms)
  (foldr (lambda (arg-atom acc)
           (~> (ash acc arg-atom-shift)
               (bit-or (encode-arg-atom arg-atom))))
         0 arg-atoms))

;; Encode a destinational statement using already encoded (e.g. with encode-arg-atoms) args.
(define (encode-astmt op dest-reg encoded-args)
  (~> (ash encoded-args arg-atom-shift)
      (bit-or dest-reg)
      (ash op-width)
      (bit-or (encode-op op))))

;; Encode a statement.
(define (encode-stmt op dest-reg . args)
  (if dest-reg
    ;; Produces value:
    (match* (op args)
      [((or '__boxNew '__denvNew) '())
       (encode-astmt op dest-reg (encode-arg-atoms args))]
      [((or '__ffnNew) (list a))
       (~> (unwrap-reg a)
           (ash arg-atom-shift)
           (bit-or dest-reg)
           (ash arg-atom-shift)
           (bit-or (encode-op op)))]
      [((or '__mov
            '__iNeg
            '__boxGet '__tupleNew '__tupleLength '__fnNew '__fnCode '__contNew '__contCode
            '__recNew '__recType
            '__flibOpen)
        (list _))
       (encode-astmt op dest-reg (encode-arg-atoms args))]
      [((or '__iEq '__iLt '__iLe '__iGt '__iGe
            '__iAdd '__iSub '__iMul '__iDiv '__iRem '__iMod
            '__tupleGet '__fnGet '__contGet '__recGet) (list _ _))
       (encode-astmt op dest-reg (encode-arg-atoms args))]
      [((or '__flibSym) (list a b))
       (define src-reg
         (nanopass-case (ConstPoolAsm Atom) a
           [(reg ,i) i]
           [else (error "not a reg" a)]))
       (~> (ash (encode-arg-atom b) arg-atom-shift)
           (bit-or src-reg)
           (ash arg-atom-shift)
           (bit-or dest-reg)
           (ash arg-atom-shift)
           (bit-or (encode-op op)))]
      [(_ _) (error "unimplemented encoding" op)])
    ;; Does not produce value:
    (match* (op args)
      [((or '__fnInitCode) (list dest proc))
       (define dest-reg
         (nanopass-case (ConstPoolAsm Atom) dest
           [(reg ,i) i]
           [else (error "not a reg" dest)]))
       (define proc-index
         (nanopass-case (ConstPoolAsm Atom) proc
           [(proc ,n ,i) i]
           [else (error "not a proc" proc)]))
       (~> (ash proc-index 16)
           (bit-or (ash dest-reg op-width))
           (bit-or (encode-op op)))]
      [((or '__contInitCode) (list dest label))
       (define dest-reg
         (nanopass-case (ConstPoolAsm Atom) dest
           [(reg ,i) i]
           [else (error "not a reg" dest)]))
       (define label-offset
         (nanopass-case (ConstPoolAsm Atom) label
           [(label ,n ,i) i]
           [else (error "not a label" label)]))
       (~> (ash label-offset 16)
           (bit-or (ash dest-reg op-width))
           (bit-or (encode-op op)))]
      [((or '__ffnInitType) (list a b c))
       (~> (encode-arg-atom c)
           (ash arg-atom-shift)
           (bit-or (unwrap-reg b))
           (ash arg-atom-shift)
           (bit-or (unwrap-reg a))
           (ash arg-atom-shift)
           (bit-or (encode-op op)))]
      [((or '__boxSet
            '__tupleInit '__fnInit '__contInit '__recInitType '__recInit
            '__ffnInitCConv)
        (cons dest args))
       (define dest-reg
         (nanopass-case (ConstPoolAsm Atom) dest
           [(reg ,i) i]
           [else (error "not a reg" dest)]))
       (encode-astmt op dest-reg (encode-arg-atoms args))]
      [('__swap (list a b))
       (~> (unwrap-reg b)
           (ash arg-atom-shift)
           (bit-or (unwrap-reg a))
           (ash arg-atom-shift)
           (bit-or (encode-op op)))]
      [(_ _) (error "unimplemented encoding" op)])))

;; Encode a transfer.
(define (encode-transfer op . args)
  (match* (op args)
    [('__br (list i))
     (~> (ash i short-arg-shift)
         (bit-or (encode-op op)))]
    [('__brf (list a? i))
     (~> (ash i short-arg-shift)
         (bit-or (ash (encode-arg-atom a?) arg-atom-shift))
         (bit-or (encode-op op)))]
    [('__jmp (list i))
     (~> (ash i arg-index-shift)
         (bit-or (encode-op '__ijmp)))]
    [('__ffnCall (list x))
     (nanopass-case (ConstPoolAsm Var) x
       [(reg ,i) (~> (ash i arg-index-shift)
                     (bit-or (encode-op '__ffnCall)))]
       [else (error "unreachable")])]
    [((or '__halt '__raise) (list a))
     (~> (ash (encode-arg-atom a) arg-atom-shift)
         (bit-or (encode-op op)))]))
