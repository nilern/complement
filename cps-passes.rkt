#lang racket

(provide census relax-edges analyze-closures closure-convert)
(require data/gvector (only-in srfi/26 cute) (only-in threading ~> ~>>)
         nanopass/base
         "langs.rkt" (only-in "util.rkt" clj-group-by unzip-hash)
         (prefix-in kenv: (submod "util.rkt" cont-env)))

;; TODO: use this in shrinking
(define-pass census : CPS (ir ltab vtab delta) -> * ()
  (definitions
    (define (make-var-entry) (make-hash '((uses . 0))))
    
    (define (make-label-entry) (make-hash '((calls . 0) (escapes . 0))))
    
    (define add-delta (cute + <> delta))
  
    (define (used! var-table name)
      (~> (hash-ref! var-table name make-var-entry)
          (hash-update! 'uses add-delta)))

    (define (escapes! label-table name)
      (~> (hash-ref! label-table name make-label-entry)
          (hash-update! 'escapes add-delta)))
          
    (define (called! label-table name)
      (~> (hash-ref! label-table name make-label-entry)
          (hash-update! 'calls add-delta))))

  (CFG : CFG (ir) -> * ()
    [(cfg ([,n* ,k*] ...) ,n)
     (for-each Cont k*)
     (escapes! ltab n)])

  (Cont : Cont (ir) -> * ()
    [(cont (,n* ...) ,s* ... ,t)
     (for-each Stmt s*)
     (Transfer t)])

  (Stmt : Stmt (ir) -> * ()
    [(def ,n ,e) (Expr e)]
    [,e (Expr e)])
    
  (Transfer : Transfer (ir) -> * ()
    [(continue ,x ,a* ...) (Callee x) (for-each Atom a*)]
    [(if ,a? ,x1 ,x2) (Atom a?) (Callee x1) (Callee x2)]
    [(call ,x1 ,x2 ,a* ...) (Callee x1) (Var x2) (for-each Atom a*)]
    [(halt ,a) (Atom a)])

  (Expr : Expr (ir) -> * ()
    [(fn ,blocks) (CFG blocks)]
    [(primcall ,p ,a* ...) (for-each Atom a*)]
    [,a (Atom a)])

  (Atom : Atom (ir) -> * ()
    [(const ,c) (void)]
    [,x (Var x)])

  (Var : Var (ir) -> * ()
    [(lex ,n) (used! vtab n)]
    [(label ,n) (escapes! ltab n)])

  (Callee : Var (ir) -> * ()
    [(lex ,n) (used! vtab n)]
    [(label ,n) (called! ltab n)]))

(define-pass relax-edges : CPS (ir ltab) -> CPS ()
  (definitions
    (struct $cfg-builder (conts entry))
    
    (define (make-cfg-builder entry)
      ($cfg-builder (make-hash) entry))

    (define (visited? cfg-builder label)
      (hash-has-key? ($cfg-builder-conts cfg-builder) label))

    (define (lk-ref cfg-builder label purpose)
      (~> ($cfg-builder-conts cfg-builder)
          (hash-ref label)
          (hash-ref purpose)))

    (define (label-ref cfg-builder label purpose)
      (car (lk-ref cfg-builder label purpose)))

    (define (cont-ref cfg-builder label purpose)
      (cdr (lk-ref cfg-builder label purpose)))

    (define (add-cont! cfg-builder label purpose cont)
      (define entry (~> ($cfg-builder-conts cfg-builder)
                        (hash-ref! label make-hash)))
      (hash-set! entry purpose (cons (if (= (hash-count entry) 0) label (gensym label))
                                     cont)))

    (define (build-cfg cfg-builder)
      (with-output-language (CPS CFG)
        (define-values (labels conts)
          (for/fold ([labels '()] [conts '()])
                    ([(_ entry) ($cfg-builder-conts cfg-builder)])
            (define lks (hash-values entry))
            (values (append (map car lks) labels) (append (map cdr lks) conts))))
        `(cfg ([,labels ,conts] ...) ,($cfg-builder-entry cfg-builder))))

    (define (adapter-cont label cont)
      (with-output-language (CPS Cont)
        (nanopass-case (CPS Cont) cont
          [(cont (,n* ...) ,s* ... ,t)
           `(cont (,n* ...) (continue (label ,label) (lex ,n*) ...))]))))

  (CFG : CFG (ir) -> CFG ()
    [(cfg ([,n* ,k*] ...) ,n)
     (define kenv (kenv:inject n* k*))
     (define cfg-builder (make-cfg-builder n))
     (Cont (kenv:ref kenv n) n kenv cfg-builder)
     (build-cfg cfg-builder)])

  (Cont : Cont (ir label kenv cfg-builder) -> Cont ()
    [(cont (,n* ...) ,s* ... ,t)
     (unless (visited? cfg-builder label)
       (define default-cont `(cont (,n* ...)
                               ,(map (cute Stmt <> kenv cfg-builder) s*) ...
                               ,(Transfer t kenv cfg-builder)))
       (define ltab-entry (hash-ref ltab label))
       (define called? (> (hash-ref ltab-entry 'calls) 0))
       (define escapes (hash-ref ltab-entry 'escapes))
       (define escapes? (> escapes 0))
       (when called?
         (add-cont! cfg-builder label 'default default-cont))
       (when escapes?
         (if called?
           (begin
             (add-cont! cfg-builder label 'escape (adapter-cont label default-cont))
             (hash-set! ltab (label-ref cfg-builder label 'escape)
                        (make-hash (list (cons 'calls 0) (cons 'escapes escapes))))
             (hash-set! ltab-entry 'escapes 0))
           (add-cont! cfg-builder label 'escape default-cont)))
       #| NOTE: unreachable continuations get implicitly eliminated here |# )])

  (Stmt : Stmt (ir kenv cfg-builder) -> Stmt ()
    [(def ,n ,e) `(def ,n ,(Expr e kenv cfg-builder))]
    [,e (Expr e kenv cfg-builder)])

  (Expr : Expr (ir kenv cfg-builder) -> Expr ()
    [(fn ,[blocks]) `(fn ,blocks)]
    [(primcall ,p ,a* ...)
     `(primcall ,p ,(map (cute Atom <> kenv cfg-builder) a*) ...)]
    [,a (Atom a kenv cfg-builder)])
    
  (Transfer : Transfer (ir kenv cfg-builder) -> Transfer ()
    [(continue ,x ,a* ...)
     `(continue ,(Callee x kenv cfg-builder) ,(map (cute Atom <> kenv cfg-builder) a*) ...)]
    [(if ,a? ,x1 ,x2)
     `(if ,(Atom a? kenv cfg-builder)
        ,(IfCallee x1 kenv cfg-builder)
        ,(IfCallee x2 kenv cfg-builder))]
    [(call ,x1 ,x2 ,a* ...)
     `(call ,(Callee x1 kenv cfg-builder) ,(Var x2 kenv cfg-builder)
            ,(map (cute Atom <> kenv cfg-builder) a*) ...)]
    [(halt ,a) `(halt ,(Atom a kenv cfg-builder))])

  (Atom : Atom (ir kenv cfg-builder) -> Atom ()
    [(const ,c) ir]
    [,x (Var x kenv cfg-builder)])

  (Var : Var (ir kenv cfg-builder) -> Atom ()
    [(lex ,n) ir]
    [(label ,n)
     (Cont (kenv:ref kenv n) n kenv cfg-builder)
     `(label ,(label-ref cfg-builder n 'escape))])

  (Callee : Var (ir kenv cfg-builder) -> Var ()
    [(lex ,n) ir]
    [(label ,n)
     (Cont (kenv:ref kenv n) n kenv cfg-builder)
     `(label ,(label-ref cfg-builder n 'default))])

  (IfCallee : Var (ir kenv cfg-builder) -> Var ()
    [(lex ,n) ir]
    [(label ,n)
     (Cont (kenv:ref kenv n) n kenv cfg-builder)
     (if (> (hash-ref (hash-ref ltab n) 'calls) 1)
       (begin
         (add-cont! cfg-builder n 'critical
                    (adapter-cont n (cont-ref cfg-builder n)))
         (let ([label* (label-ref cfg-builder n 'critical)])
           (hash-set! ltab label* (make-hash '((calls . 1) (escapes . 0))))
           `(label ,label*)))
       (begin
         (Callee ir kenv cfg-builder)
         `(label ,(label-ref cfg-builder n 'default))))]))

(define-pass analyze-closures : CPS (ir) -> * ()
  (definitions
    (define (make-entry) (make-hash (list (cons 'freevars (mutable-set)))))

    (define (freevars! table label)
      (~> (hash-ref! table label make-entry)
          (hash-ref 'freevars)))
    
    (define (use-clover! table label name)
      (~> (freevars! table label)
          (set-add! name)))
  
    (define (transitively! table label env src-label)
      (define freevars (freevars! table label))
      (for ([fv (freevars! table src-label)]
            #:when (not (set-member? env fv)))
        (set-add! freevars fv))))

  (CFG : CFG (ir stats visited) -> * ()
    [(cfg ([,n* ,k*] ...) ,n)
     (define kenv (kenv:inject n* k*))
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
       [(cfg ([,n* ,k*] ...) ,n) (transitively! stats label env n)])]
    [(primcall ,p ,a* ...)
     (for ([aexpr a*])
       (Atom aexpr label env kenv stats visited))]
    [,a (Atom a label env kenv stats visited)])

  (Atom : Atom (ir label env kenv stats visited) -> * ()
    [,x (Var x #f label env kenv stats visited)]
    [(const ,c) (void)])

  (Var : Var (ir call? label env kenv stats visited) -> * ()
    [(lex ,n) (unless (set-member? env n) (use-clover! stats label n))]
    [(label ,n)
     (Cont (kenv:ref kenv n) n kenv stats visited)
     (transitively! stats label env n)])

  (let ([visited (mutable-set)]
        [stats (make-hash)])
    (CFG ir stats visited)
    stats))

(define-pass closure-convert : CPS (ir stats ltab) -> CPCPS ()
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
     (define freevars (hash-ref (hash-ref stats label) 'freevars))
     (define ltab-entry (hash-ref ltab label))
     (define called? (> (hash-ref ltab-entry 'calls) 0))
     (define escapes? (> (hash-ref ltab-entry 'escapes) 0))
     (cond
      [called?
       (when escapes? (error (format "~s is both called and escaping" label)))
       (let* ([env (for/hash ([fv freevars]) (values fv (gensym fv)))]
              [stmt-acc (make-gvector)])
         (for ([stmt s*])
           (Stmt stmt env fn-acc stmt-acc))
         (let ([transfer (Transfer t env stmt-acc)])
           (emit-cont! cont-acc 'lifted label `(cont (,(fv-params env freevars) ... ,n* ...)
                                                     ,(gvector->list stmt-acc) ...
                                                     ,transfer))))]
      [escapes?
       (let ([closure (gensym label)]
             [env (for/hash ([fv freevars]) (values fv (gensym fv)))]
             [stmt-acc (make-gvector)])
         (for ([stmt s*])
           (Stmt stmt env fn-acc stmt-acc))
         (let ([transfer (Transfer t env stmt-acc)])
           (emit-cont! cont-acc 'closed label `(cont (,closure ,n* ...)
                                                     ,(fv-loads closure env freevars) ...
                                                     ,(gvector->list stmt-acc) ...
                                                     ,transfer))))])
     #| NOTE: unreachable continuations get implicitly eliminated here |# ])

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
