#lang racket

(provide analyze-closures closure-convert)
(require data/gvector (only-in srfi/26 cute) (only-in threading ~>)
         nanopass/base
         "langs.rkt" (only-in "util.rkt" clj-group-by unzip-hash)
         (prefix-in kenv: (submod "util.rkt" cont-env)))

(module label-table racket/base
  (provide new call! escape! use-clover! transitively!)
  (require racket/set (only-in srfi/26 cute) (only-in threading ~>))

  (define (new) (make-hash))

  (define ref! (cute hash-ref! <> <> make-hash))

  (define (freevars! table label)
    (~> (ref! table label)
        (hash-ref! 'freevars mutable-set)))

  (define (call! table label)
    (~> (ref! table label)
        (hash-set! 'called? #t)))

  (define (escape! table label)
    (~> (ref! table label)
        (hash-set! 'escapes? #t)))

  (define (use-clover! table label name)
    (~> (freevars! table label)
        (set-add! name)))

  (define (transitively! table label env src-label)
    (define freevars (freevars! table label))
    (for ([fv (freevars! table src-label)]
          #:when (not (set-member? env fv)))
      (set-add! freevars fv))))

(require (prefix-in ltab: (submod "." label-table)))

(define-pass analyze-closures : CPS (ir) -> * ()
  (CFG : CFG (ir stats visited) -> * ()
    [(cfg ([,n* ,k*] ...) ,n)
     (define kenv (kenv:inject n* k*))
     (ltab:escape! stats n)
     (Cont (kenv:ref kenv n) n kenv stats visited)])

  (Cont : Cont (ir label kenv stats visited) -> * ()
    [(cont (,n* ...) ,s* ... ,t)
     (unless (set-member? visited label)
       (set-add! visited label)
       (~> (list->set n*)
           (foldl (cute Stmt <> label <> kenv stats visited) _ s*)
           (Transfer t label _ kenv stats visited)))])

  (Stmt : Stmt (ir label env kenv stats visited) -> * ()
    [(def ,n ,e)
     (Expr e label env kenv stats visited)
     (set-add env n)]
    [,e
     (Expr e label env kenv stats visited)
     env])

  (Transfer : Transfer (ir label env kenv stats visited) -> * ()
    [(continue ,x ,a* ...)
     (Var x #t label env kenv stats visited)
     (for ([aexpr a*])
       (Atom aexpr label env kenv stats visited))]
    [(if ,a? ,x1 ,x2)
     (Atom a? label env kenv stats visited)
     (Var x1 #t label env kenv stats visited)
     (Var x2 #t label env kenv stats visited)]
    [(call ,x1 ,x2 ,a* ...)
     (Var x1 #t label env kenv stats visited)
     (Var x2 #f label env kenv stats visited)
     (for ([aexpr a*])
       (Atom aexpr label env kenv stats visited))]
    [(halt ,a) (Atom a label env kenv stats visited)])

  (Expr : Expr (ir label env kenv stats visited) -> * ()
    [(fn ,blocks)
     (CFG blocks stats visited)
     (nanopass-case (CPS CFG) blocks
       [(cfg ([,n* ,k*] ...) ,n) (ltab:transitively! stats label env n)])]
    [(primcall ,p ,a* ...)
     (for ([aexpr a*])
       (Atom aexpr label env kenv stats visited))]
    [,a (Atom a label env kenv stats visited)])

  (Atom : Atom (ir label env kenv stats visited) -> * ()
    [,x (Var x #f label env kenv stats visited)]
    [(const ,c) (void)])

  (Var : Var (ir call? label env kenv stats visited) -> * ()
    [(lex ,n) (unless (set-member? env n) (ltab:use-clover! stats label n))]
    [(label ,n)
     ((if call? ltab:call! ltab:escape!) stats n)
     (Cont (kenv:ref kenv n) n kenv stats visited)
     (ltab:transitively! stats label env n)])

  (let ([visited (mutable-set)]
        [stats (ltab:new)])
    (CFG ir stats visited)
    stats))

(define-pass closure-convert : CPS (ir stats) -> CPCPS ()
  (definitions
    (define (fv-params env freevars)
      (for/list ([fv freevars])
        (hash-ref env fv fv)))

    (define (fv-lexen env freevars)
      (with-output-language (CPCPS Atom)
        (for/list ([fv freevars])
          `(lex ,(hash-ref env fv fv)))))

    (define (fv-loads closure env freevars)
      (with-output-language (CPCPS Stmt)
        (for/list ([(fv i) (in-indexed freevars)])
          `(def ,(hash-ref env fv fv) (primcall __fnGet (lex ,closure) (const ,i))))))

    (struct $cont-acc (conts entry-point return-points))

    (define (make-cont-acc entry)
      ($cont-acc (make-hash) entry (mutable-set)))

    (define (emit-cont! cont-acc interface label cont)
      (match-define ($cont-acc conts entry return-points) cont-acc)
      (define label* (match interface
                       ['lifted label]
                       ['closed
                        (unless (eq? label entry) (set-add! return-points label))
                        (gensym label)]))
      (hash-set! conts label cont)
      (hash-set! (hash-ref stats label) interface label))

    (define build-cfg
      (with-output-language (CPCPS CFG)
        (match-lambda
          [($cont-acc conts entry return-points)
           (let-values ([(labels conts) (unzip-hash conts)])
             `(cfg ([,labels ,conts] ...) (,entry ,(set->list return-points) ...)))]))))

  (CFG : CFG (ir fn-acc) -> Program ()
    [(cfg ([,n* ,k*] ...) ,n)
     (define cont-acc (make-cont-acc n))
     (for ([label n*] [cont k*])
       (Cont cont label fn-acc cont-acc))
     (build-cfg cont-acc)])

  (Cont : Cont (ir label fn-acc cont-acc) -> Cont ()
    [(cont (,n* ...) ,s* ... ,t)
     (define ltab-entry (hash-ref stats label))
     (define freevars (hash-ref ltab-entry 'freevars))
     (define called? (hash-has-key? ltab-entry 'called?))
     (define escapes? (hash-has-key? ltab-entry 'escapes?))
     (when called?
       (let* ([env (for/hash ([fv freevars]) (values fv (gensym fv)))]
              [stmt-acc (make-gvector)])
         (for ([stmt s*])
           (Stmt stmt env fn-acc stmt-acc))
         (let ([transfer (Transfer t env stmt-acc)])
           (emit-cont! cont-acc 'lifted label `(cont (,(fv-params env freevars) ... ,n* ...)
                                                     ,(gvector->list stmt-acc) ...
                                                     ,transfer)))))
     (when escapes?
       (let ([closure (gensym label)]
             [env (for/hash ([fv freevars]) (values fv (gensym fv)))])
         (if called?
           (emit-cont! cont-acc 'closed label
             `(cont (,closure ,n* ...)
                    ,(fv-loads closure env freevars) ...
                    (goto (label ,label) ,(fv-lexen env freevars) ... ,n* ...)))
           (let ([stmt-acc (make-gvector)])
             (for ([stmt s*])
               (Stmt stmt env fn-acc stmt-acc))
             (let ([transfer (Transfer t env stmt-acc)])
               (emit-cont! cont-acc 'closed label `(cont (,closure ,n* ...)
                                                         ,(fv-loads closure env freevars) ...
                                                         ,(gvector->list stmt-acc) ...
                                                         ,transfer)))))))
     ; NOTE: unreachable continuations get implicitly eliminated here
     ])

  (Stmt : Stmt (ir env fn-acc stmt-acc) -> Stmt ()
    [(def ,n ,e) (gvector-add! stmt-acc `(def ,n ,(Expr e env fn-acc stmt-acc)))]
    [,e (gvector-add! stmt-acc (Expr e env fn-acc stmt-acc))])

  (Transfer : Transfer (ir env stmt-acc) -> Transfer ()
    [(continue ,x ,a* ...)
     (define-values (x* extra-args) (Jumpee x env stmt-acc))
     `(goto ,x* ,extra-args ... ,(map (cute Atom <> env stmt-acc) a*) ...)]
    [(if ,a? ,x1 ,x2)
     (define-values (x1* extra-args1) (Jumpee x1 env stmt-acc))
     (define-values (x2* extra-args2) (Jumpee x2 env stmt-acc))
     `(if ,(Atom a? env stmt-acc) (,x1* ,extra-args1 ...) (,x2* ,extra-args2 ...))]
    [(call ,x1 ,x2 ,a* ...)
     (define-values (x1* extra-args) (Callee x1 env stmt-acc))
     `(goto ,x1* ,extra-args ...
            ,(Escape x2 env stmt-acc) ,(map (cute Atom <> env stmt-acc) a*) ...)]
    [(halt ,a) `(halt ,(Atom a env stmt-acc))])

  (Expr : Expr (ir env fn-acc stmt-acc) -> Expr ()
    [(fn ,blocks)
     (define f (gensym 'f))
     (define cfg (CFG blocks fn-acc))
     (hash-set! fn-acc f (with-output-language (CPCPS Fn) `(fn ,cfg)))
     (nanopass-case (CPS CFG) blocks
       [(cfg ([,n* ,k*] ...) ,n)
        (define freevars (hash-ref (hash-ref stats n) 'freevars))
        `(primcall __fnNew (proc ,f) ,(fv-lexen env freevars) ...)])]
    [(primcall ,p ,a* ...) `(primcall ,p ,(map (cute Atom <> env stmt-acc) a*) ...)]
    [,a (Atom a env stmt-acc)])

  (Atom : Atom (ir env stmt-acc) -> Atom ()
    [,x (Escape x env stmt-acc)]
    [(const ,c) `(const ,c)])

  (Escape : Var (ir env stmt-acc) -> Var ()
    [(lex ,n) `(lex ,(hash-ref env n n))]
    [(label ,n)
     (define cont (gensym n))
     (define ltab-entry (hash-ref stats n))
     (define label (hash-ref ltab-entry 'closed))
     (define freevars (hash-ref ltab-entry 'freevars))
     (gvector-add! stmt-acc (with-output-language (CPCPS Stmt)
                              `(def ,cont (primcall __contNew (label ,label)
                                                              ,(fv-lexen env freevars) ...))))
     `(lex ,cont)])

  (Callee : Var (ir env stmt-acc) -> Var ()
    [(lex ,n)
     (define codeptr (gensym n))
     (gvector-add! stmt-acc (with-output-language (CPCPS Stmt)
                              `(def ,codeptr (primcall __fnCode (lex ,(hash-ref env n n))))))
     (values `(lex ,codeptr) (list `(lex ,(hash-ref env n n))))]
    [(label ,n) (error "(label n) as callee")])

  (Jumpee : Var (ir env stmt-acc) -> Var ()
    [(lex ,n)
     (define codeptr (gensym n))
     (gvector-add! stmt-acc (with-output-language (CPCPS Stmt)
                              `(def ,codeptr (primcall __contCode (lex ,(hash-ref env n n))))))
     (values `(lex ,codeptr) (list `(lex ,(hash-ref env n n))))]
    [(label ,n)
     (define freevars (hash-ref (hash-ref stats n) 'freevars))
     (values `(label ,n) (fv-lexen env freevars))])

  (let*-values ([(fn-acc) (make-hash)]
                [(cfg) (CFG ir fn-acc)]
                [(fn-names fns) (unzip-hash fn-acc)])
     `(prog ([,fn-names ,fns] ...) ,cfg)))
