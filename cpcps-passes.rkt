#lang racket/base

(provide select-instructions shrink)
(require racket/match racket/list racket/set data/gvector (only-in srfi/26 cute)
         nanopass/base
         "langs.rkt" (prefix-in cfg: "cfg.rkt") (prefix-in kenv: (submod "util.rkt" cont-env)))

;; TODO: DynEnv creation
(define-pass select-instructions : CPCPS (ir) -> RegisterizableCPCPS ()
  (definitions
    (define (varargs-primop? op)
      (case op
        [(__tupleNew __fnNew __contNew __recNew __denvPush) #t]
        [else #f]))
  
    (define (emit-stmt name expr)
      (with-output-language (RegisterizableCPCPS Stmt)
        (if name
          `(def ,name ,expr)
          expr)))

    (define (emit-compound-start name op len)
      (with-output-language (RegisterizableCPCPS Expr)
        (case op
          [(__tupleNew) (emit-stmt name `(primcall1 ,op (const ,len)))]
          [(__fnNew __contNew __recNew) (emit-stmt name `(primcall1 ,op (const ,(- len 1))))])))

    (define (emit-compound-step name op index atom)
      (with-output-language (RegisterizableCPCPS Expr)
        (case op
          [(__tupleNew) `(primcall3 __tupleInit (lex ,name) (const ,index) ,atom)]
          [(__fnNew)
           (if (= index 0)
             `(primcall2 __fnInitCode (lex ,name) ,atom)
             `(primcall3 __fnInit (lex ,name) (const ,(- index 1)) ,atom))]
          [(__contNew)
           (if (= index 0)
             `(primcall2 __contInitCode (lex ,name) ,atom)
             `(primcall3 __contInit (lex ,name) (const ,(- index 1)) ,atom))]
          [(__recNew)
           (if (= index 0)
             `(primcall2 __recInitType (lex ,name) ,atom)
             `(primcall3 __recInit (lex ,name) (const ,(- index 1)) ,atom))]))))

  (Cont : Cont (ir) -> Cont ()
    [(cont (,n* ...) ,s* ... ,[t])
     (define stmt-acc (make-gvector))
     (for ([stmt s*])
       (Stmt stmt stmt-acc))
     `(cont (,n* ...) ,(gvector->list stmt-acc) ... ,t)])

  (Stmt : Stmt (ir stmt-acc) -> Stmt ()
    [(def ,n ,e) (Expr e n stmt-acc)]
    [,e (Expr e #f stmt-acc)])

  (Expr : Expr (ir name stmt-acc) -> Expr ()
    [(primcall ,p ,[a*] ...) (guard (varargs-primop? p))
     (gvector-add! stmt-acc (emit-compound-start name p (length a*)))
     (for ([(atom i) (in-indexed a*)])
       (gvector-add! stmt-acc (emit-compound-step name p i atom)))]
    [(primcall ,p) (gvector-add! stmt-acc (emit-stmt name `(primcall0 ,p)))]
    [(primcall ,p ,[a]) (gvector-add! stmt-acc (emit-stmt name `(primcall1 ,p ,a)))]
    [(primcall ,p ,[a1] ,[a2]) (gvector-add! stmt-acc (emit-stmt name `(primcall2 ,p ,a1 ,a2)))]
    [(primcall ,p ,a* ...) (error "primop argc")]
    [,a (gvector-add! stmt-acc (emit-stmt name (Atom a)))])

  (Atom : Atom (ir) -> Atom ()))

;; Bidirectional direct-call graph of a CFG
(module label-table racket/base
  (provide make)
  (require (only-in srfi/26 cute) nanopass/base
           "langs.rkt")

  ;;; FIXME: callers and callees should disallow duplicates

  (define (make-entry)
    (make-hash '((escapes? . #f) (callers . ()) (callees . ()))))

  (define ref! (cute hash-ref! <> <> make-entry))

  (define (calls! ltab caller callee)
    (hash-update! (ref! ltab caller) 'callees (cute cons callee <>))
    (hash-update! (ref! ltab callee) 'callers (cute cons caller <>)))

  (define (escapes! ltab label)
    (hash-set! (ref! ltab label) 'escapes? #t))

  (define-pass initialize! : RegisterizableCPCPS (ir label ltab) -> * ()
    (Cont : Cont (ir) -> * ()
      [(cont (,n* ...) ,s* ... ,t)
       (for ([stmt s*]) (Stmt stmt))
       (Transfer t)])

    (Stmt : Stmt (ir) -> * ()
      [(def ,n ,e) (Expr e)]
      [,e (Expr e)])

    (Transfer : Transfer (ir) -> * ()
      [(goto ,x ,a* ...) (Callee x) (for ([atom a*]) (Atom atom))]
      [(if ,a? ,x1 ,x2) (Atom a?) (Callee x1) (Callee x2)]
      [(halt ,a) (Atom a)])

    (Expr : Expr (ir) -> * ()
      [(primcall0 ,p) (void)]
      [(primcall1 ,p ,a) (Atom a)]
      [(primcall2 ,p ,a1 ,a2) (Atom a1) (Atom a2)]
      [(primcall3 ,p ,a1 ,a2 ,a3) (Atom a1) (Atom a2) (Atom a3)]
      [,a (Atom a)])

    (Atom : Atom (ir) -> * ()
      [(const ,c) (void)]
      [,x (Var x)])

    (Var : Var (ir) -> * ()
      [(lex ,n) (void)]
      [(label ,n) (escapes! ltab n)]
      [(proc ,n) (void)])

    (Callee : Var (ir) -> * ()
      [(lex ,n) (void)]
      [(label ,n) (calls! ltab label n)]
      [(proc ,n) (void)])

    (Cont ir))

  (define (make labels conts entries)
    (define ltab (make-hash))
    (for ([label labels] [cont conts])
      (initialize! cont label ltab))
    (for ([entry entries])
      (escapes! ltab entry))
    ltab))

(require (prefix-in ltab: (submod "." label-table)))

(define-pass shrink : RegisterizableCPCPS (ir) -> RegisterizableCPCPS ()
  (definitions
    (define (emit-stmt! stmt-acc name expr)
      (with-output-language (RegisterizableCPCPS Stmt)
        (gvector-add! stmt-acc (if name `(def ,name ,expr) expr))))

    (define (ltab-arglists ltab caller callee)
      (nanopass-case (RegisterizableCPCPS Transfer) (hash-ref (hash-ref ltab caller) 'transfer)
        [(goto (label ,n) ,a* ...) (if (eq? n callee) (list a*) '())]
        [(goto ,x ,a* ...) '()]
        [(if ,a? (label ,n1) (label ,n2))
         (if (eq? n1 callee)
           (if (eq? n2 callee) (list '() '()) (list '()))
           (if (eq? n2 callee) (list '()) '()))]
        [(if ,a? (label ,n1) ,x2)
         (if (eq? n1 callee) (list '()) '())]
        [(if ,a? ,x1 (label ,n2))
         (if (eq? n2 callee) (list '()) '())]
        [(if ,a? ,x1 ,x2) '()]
        [(halt ,a) '()]))

    (define (join-atoms atoms)
      (define (join2 atom1 atom2)
        (if (equal? atom1 atom2) atom1 #f))
      (match atoms
        ['() #f]
        [(cons atom atoms) (foldl join2 atom atoms)]))

    (define (shrink-call label keep-indices callee args)
      (nanopass-case (RegisterizableCPCPS Var) callee
        [(lex ,n) (values callee args)]
        [(label ,n)
         (values callee
                 (if (eq? n label)
                   (for/list ([(arg i) (in-indexed args)]
                              #:when (set-member? keep-indices i))
                     arg)
                   args))]
        [(proc ,n) (values callee args)]))

    (define (params! ltab label params)
      (let* ([callers (hash-ref (hash-ref ltab label) 'callers)]
             [arglists (append-map (cute ltab-arglists ltab <> label) callers)]
             [env (make-hash)]
             [keep-indices (mutable-set)]
             [params* (for/fold ([params '()])
                                ([(param index) (in-indexed params)]
                                 [aexprs (apply map list arglists)]) ;; OPTIMIZE: is `apply` slow?
                        (match (join-atoms aexprs)
                          [#f (set-add! keep-indices index)
                              (cons param params)]
                          [atom (hash-set! env param (car aexprs))
                                params]))])
        (for ([caller callers])
          (hash-update! (hash-ref ltab caller) 'transfer
                        (cute ShrinkTransfer <> label keep-indices)))
        (values (reverse params*) env))))

  (CFG : CFG (ir) -> CFG ()
    [(cfg ([,n1* ,k*] ...) (,n2* ...))
     (define ltab (ltab:make n1* k* n2*))
     (define kenv (kenv:inject n1* k*))
     (for ([label (cfg:reverse-postorder ltab n2*)])
       (Cont (kenv:ref kenv label) label ltab))
     (define-values (rlabels rconts)
       (with-output-language (RegisterizableCPCPS Cont)
         (for/fold ([labels '()] [conts '()])
                   ([(label ltab-entry) ltab])
           (values (cons label labels)
                   (cons `(cont (,(hash-ref ltab-entry 'params) ...)
                            ,(hash-ref ltab-entry 'stmts) ...
                            ,(hash-ref ltab-entry 'transfer))
                         conts)))))
     `(cfg ([,(reverse rlabels) ,(reverse rconts)] ...) (,n2* ...))])

  (Cont : Cont (ir label ltab) -> * ()
    [(cont (,n* ...) ,s* ... ,t)
     (define ltab-entry (hash-ref ltab label))
     (define-values (params env)
       (if (hash-ref ltab-entry 'escapes?)
         (values n* (make-hash))
         (params! ltab label n*)))
     (hash-set! ltab-entry 'params params)
     (define stmt-acc (make-gvector))
     (for ([stmt s*])
       (Stmt stmt env stmt-acc))
     (hash-set! ltab-entry 'stmts (gvector->list stmt-acc))
     (hash-set! ltab-entry 'transfer (Transfer t env))])

  (Stmt : Stmt (ir env stmt-acc) -> * ()
    [(def ,n ,e) (Expr e n env stmt-acc)]
    [,e (Expr e #f env stmt-acc)])

  (Transfer : Transfer (ir env) -> Transfer ()
    [(goto ,x ,a* ...) `(goto ,(Var x env) ,(map (cute Atom <> env) a*) ...)]
    [(if ,a? ,x1 ,x2) `(if ,(Atom a? env) ,(Var x1 env) ,(Var x2 env))]
    [(halt ,a) `(halt ,(Atom a env))])

  (ShrinkTransfer : Transfer (ir label keep-indices) -> Transfer ()
    [(goto ,x ,a* ...)
     (define-values (callee args) (shrink-call label keep-indices x a*))
     `(goto ,callee ,args ...)]
    [(if ,a? ,x1 ,x2)
     (define-values (callee1 _) (shrink-call label keep-indices x1 '()))
     (define-values (callee2 _*) (shrink-call label keep-indices x2 '()))
     `(if ,a? ,callee1 ,callee2)]
    [(halt ,a) ir])

  (Expr : Expr (ir name env stmt-acc) -> Expr ()
    [(primcall0 ,p) (emit-stmt! stmt-acc name ir)]
    [(primcall1 ,p ,a) (emit-stmt! stmt-acc name `(primcall1 ,p ,(Atom a env)))]
    [(primcall2 ,p ,a1 ,a2)
     (emit-stmt! stmt-acc name `(primcall2 ,p ,(Atom a1 env) ,(Atom a2 env)))]
    [(primcall3 ,p ,a1 ,a2 ,a3)
     (emit-stmt! stmt-acc name `(primcall3 ,p ,(Atom a1 env) ,(Atom a2 env) ,(Atom a3 env)))]
    [,a (hash-set! env name (Atom a env))])

  (Atom : Atom (ir env) -> Atom ()
    [(const ,c) ir]
    [,x (Var x env)])

  (Var : Var (ir env) -> Var ()
    [(lex ,n) (hash-ref env n ir)]
    [(label ,n) ir]
    [(proc ,n) ir]))
