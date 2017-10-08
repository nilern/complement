#lang racket

(provide cpcps-shrink select-instructions)
(require data/gvector (only-in srfi/26 cute)
         nanopass/base
         "langs.rkt" (prefix-in kenv: (submod "util.rkt" cont-env)))

;; Bidirectional direct-call graph of a CPCPS CFG
(module cpcps-label-table racket/base
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

  (define-pass initialize! : CPCPS (ir label ltab) -> * ()
    (Cont : Cont (ir) -> * ()
      [(cont (,n* ...) ,s* ... ,t)
       (for ([stmt s*]) (Stmt stmt))
       (Transfer t)])

    (Stmt : Stmt (ir) -> * ()
      [(def ,n ,e) (Expr e)]
      [,e (Expr e)])

    (Transfer : Transfer (ir) -> * ()
      [(goto ,x ,a* ...)
       (Callee x)
       (for ([atom a*]) (Atom atom))]
      [(if ,a? (,x1 ,a1* ...) (,x2 ,a2* ...))
       (Atom a?)
       (Callee x1)
       (for ([atom a1*]) (Atom atom))
       (Callee x2)
       (for ([atom a2*]) (Atom atom))]
      [(halt ,a) (Atom a)])

    (Expr : Expr (ir) -> * ()
      [(primcall ,p ,a* ...) (for ([atom a*]) (Atom atom))]
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

(define (cpcps-cfg-rpo label-table entries)
  (define visited (mutable-set))
  (define rpo '())
  (define (visit! label)
    (unless (set-member? visited label)
      (set-add! visited label)
      (for ([succ (hash-ref (hash-ref label-table label) 'callees)])
        (visit! succ))
      (set! rpo (cons label rpo))))
  (for ([entry entries])
    (visit! entry))
  rpo)

;; OPTIMIZE: use worklist algorithm or at least make sure that DAG:s only take the minimum 2 passes
(define (cpcps-cfg-dominator-forest label-table entries)
  (define rpo (cpcps-cfg-rpo label-table entries))
  (define label-rpo-indices (for/hash ([(label i) (in-indexed rpo)])
                              (values label i)))
  (define changed #t)

  (define (olset= set1 set2)
    (eq? (car set1) (car set2)))

  (define (olset-intersect doms1 doms2)
    (let ([idom1-idx (hash-ref label-rpo-indices (car doms1))]
          [idom2-idx (hash-ref label-rpo-indices (car doms2))])
      (cond
        [(< idom1-idx idom2-idx) (olset-intersect (cdr doms1) doms2)]
        [(> idom1-idx idom2-idx) (olset-intersect doms1 (cdr doms2))]
        [else doms1])))

  (define (intersect* dom-chain-hashes)
    (for/fold ([dom-chain-hashes-acc (hash)])
              ([entry entries])
      (define dom-chain
        (for/fold ([dom-chain-acc #f])
                  ([dom-chain-hash dom-chain-hashes]
                   #:when (hash-has-key? dom-chain-hash entry))
          (let ([dom-chain (hash-ref dom-chain-hash entry)])
            (if dom-chain-acc
              (olset-intersect dom-chain-acc dom-chain)
              dom-chain))))
      (if dom-chain
        (hash-set dom-chain-hashes-acc entry dom-chain)
        dom-chain-hashes-acc)))

  (define (init label-table)
    (for/hash ([(label _) label-table])
      (values label
              (if (member label entries)
                (hash label (list label))
                (hash)))))

  (define (update! builder)
    (set! changed #f)
    (for/hash ([label rpo])
      (values label
              (if (member label entries)
                (hash-ref builder label)
                (let ([dom-chain-hash (hash-ref builder label)]
                      [dom-chain-hash*
                       (intersect*
                         (for/list ([label (hash-ref (hash-ref label-table label) 'callers)])
                           (hash-ref builder label)))])
                  (for ([(entry dom-chain*) dom-chain-hash*])
                    (unless (and (hash-has-key? dom-chain-hash entry)
                                 (olset= dom-chain* (hash-ref dom-chain-hash entry)))
                      (set! changed #t)))
                  dom-chain-hash*)))))

  (define (children builder entry label)
    (filter (λ (label*)
              (define dom-chain-hash (hash-ref builder label*))
              (and (hash-has-key? dom-chain-hash entry)
                   (eq? (car (hash-ref dom-chain-hash entry))
                        label)))
            (drop rpo (+ (hash-ref label-rpo-indices label) 1))))

  (define (build builder)
    (for/hash ([entry entries])
      (values entry
              (let build-node ([label entry])
                (cons label (map build-node (children builder entry label)))))))

  (let iterate ([builder (init label-table)])
    (if changed
      (iterate (update! builder))
      (build builder))))

(require (prefix-in cc-ltab: (submod "." cpcps-label-table)))

(define-pass cpcps-shrink : CPCPS (ir) -> CPCPS ()
  (definitions
    (define (emit-stmt! stmt-acc name expr)
      (with-output-language (CPCPS Stmt)
        (gvector-add! stmt-acc (if name `(def ,name ,expr) expr))))

    (define (cc-ltab-arglists ltab caller callee)
      (nanopass-case (CPCPS Transfer) (hash-ref (hash-ref ltab caller) 'transfer)
        [(goto (label ,n) ,a* ...) (if (eq? n callee) (list a*) '())]
        [(goto ,x ,a* ...) '()]
        [(if ,a? ((label ,n1) ,a1* ...) ((label ,n2) ,a2* ...))
         (if (eq? n1 callee)
           (if (eq? n2 callee) (list a1* a2*) (list a1*))
           (if (eq? n2 callee) (list a2*) '()))]
        [(if ,a? ((label ,n1) ,a1* ...) (,x2 ,a2* ...))
         (if (eq? n1 callee) (list a1*) '())]
        [(if ,a? (,x1 ,a1* ...) ((label ,n2) ,a2* ...))
         (if (eq? n2 callee) (list a2*) '())]
        [(if ,a? (,x1 ,a1* ...) (,x2 ,a2* ...)) '()]
        [(halt ,a) '()]))

    (define (join-atoms atoms)
      (define (join2 atom1 atom2)
        (if (equal? atom1 atom2) atom1 #f))
      (match atoms
        ['() #f]
        [(cons atom atoms) (foldl join2 atom atoms)]))

    (define (shrink-call label keep-indices callee args)
      (nanopass-case (CPCPS Var) callee
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
             [arglists (append-map (cute cc-ltab-arglists ltab <> label) callers)]
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
     (define ltab (cc-ltab:make n1* k* n2*))
     (define kenv (kenv:inject n1* k*))
     (for ([label (cpcps-cfg-rpo ltab n2*)])
       (Cont (kenv:ref kenv label) label ltab))
     (define-values (rlabels rconts)
       (with-output-language (CPCPS Cont)
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
    [(if ,a? (,x1 ,a1* ...) (,x2 ,a2* ...))
     `(if ,(Atom a? env)
        (,(Var x1 env) ,(map (cute Atom <> env) a1*) ...)
        (,(Var x2 env) ,(map (cute Atom <> env) a2*) ...))]
    [(halt ,a) `(halt ,(Atom a env))])

  (ShrinkTransfer : Transfer (ir label keep-indices) -> Transfer ()
    [(goto ,x ,a* ...)
     (define-values (callee args) (shrink-call label keep-indices x a*))
     `(goto ,callee ,args ...)]
    [(if ,a? (,x1 ,a1* ...) (,x2 ,a2* ...))
     (define-values (callee1 args1) (shrink-call label keep-indices x1 a1*))
     (define-values (callee2 args2) (shrink-call label keep-indices x2 a2*))
     `(if ,a? (,callee1 ,args1 ...) (,callee2 ,args2 ...))]
    [(halt ,a) ir])

  (Expr : Expr (ir name env stmt-acc) -> Expr ()
    [(primcall ,p ,a* ...)
     (emit-stmt! stmt-acc name `(primcall ,p ,(map (cute Atom <> env) a*) ...))]
    [,a (hash-set! env name (Atom a env))])

  (Atom : Atom (ir env) -> Atom ()
    [(const ,c) ir]
    [,x (Var x env)])

  (Var : Var (ir env) -> Var ()
    [(lex ,n) (hash-ref env n ir)]
    [(label ,n) ir]
    [(proc ,n) ir]))

(define-pass cpcps-cfg-liveness : CPCPS (ir) -> * ()
  (definitions
    (struct $luses-builder (stmt-luses transfer-luses))
  
    (define (make-luses-builder transfer-luses)
      ($luses-builder '() transfer-luses))

    (define (push-luses luses-builder luses)
      (match-define ($luses-builder stmt-luses transfer-luses) luses-builder)
      ($luses-builder (cons luses stmt-luses) transfer-luses))

    (define (ensure-luses luses-builder freevars names)
      (define (splice luses)
        (set-union luses (set-subtract names freevars)))
      (match luses-builder
        [($luses-builder (cons first-luses rest-luses) transfer-luses)
         ($luses-builder (cons (splice first-luses) rest-luses) transfer-luses)]
        [($luses-builder '() transfer-luses)
         ($luses-builder '() (splice transfer-luses))]))

    (define (build-luses luses-builder)
      (match-define ($luses-builder stmt-luses transfer-luses) luses-builder)
      (values stmt-luses transfer-luses))
  
    (define (freevars+luses prev-freevars local-freevars)
      (values (set-union local-freevars prev-freevars)
              (set-subtract local-freevars prev-freevars)))

    (define (arglist atoms)
      (foldl set-union (set) (map Atom atoms))))

  (CFG : CFG (ir) -> * ()
    [(cfg ([,n1* ,k*] ...) (,n2* ...))
     (define kenv (kenv:inject n1* k*))
     (define cont-acc (make-hash))
     (for ([name n2*])
       (Cont (kenv:ref kenv name) name kenv cont-acc))
     cont-acc])

  (Cont : Cont (ir name kenv cont-acc) -> * ()
    [(cont (,n* ...) ,s* ... ,t)
     (unless (hash-has-key? cont-acc name)
       (let*-values ([(transfer-freevars transfer-luses) (Transfer t kenv cont-acc)]
                     [(body-freevars luses-builder)
                      (let body ([stmts s*])
                        (match stmts
                          ['() (values transfer-freevars (make-luses-builder transfer-luses))]
                          [(cons stmt stmts)
                           (let*-values ([(freevars luses-builder) (body stmts)]
                                         [(freevars luses-builder)
                                          (Stmt stmt freevars luses-builder)])
                             (values freevars luses-builder))]))]
                     [(params) (list->set n*)]
                     [(stmt-luses transfer-luses)
                      (build-luses (ensure-luses luses-builder body-freevars params))])
         (hash-set! cont-acc name
           (hash 'freevars (set-subtract body-freevars params)
                 'stmt-last-uses stmt-luses
                 'transfer-luses transfer-luses))))])

  (Stmt : Stmt (ir freevars luses-builder) -> * ()
    [(def ,n ,e)
     (define-values (freevars* luses) (freevars+luses freevars (Expr e)))
     (values (set-remove freevars* n)
             (push-luses (ensure-luses luses-builder freevars (set n)) luses))]
    [,e
     (define-values (freevars* luses) (freevars+luses freevars (Expr e)))
     (values freevars* (push-luses luses-builder luses))])

  (Expr : Expr (ir) -> * ()
    [(primcall ,p ,a* ...) (arglist a*)]
    [,a (Atom a)])

  (Transfer : Transfer (ir kenv cont-acc) -> * ()
    [(goto ,x ,a* ...)
     (freevars+luses (Callee x kenv cont-acc) (set-union (Var x) (arglist a*)))]
    [(if ,a? (,x1 ,a1* ...) (,x2 ,a2* ...))
     (freevars+luses (set-union (Callee x1 kenv cont-acc) (Callee x2 kenv cont-acc))
                     (set-union (Atom a?) (Var x1) (arglist a1*) (Var x2) (arglist a2*)))]
    [(halt ,a)
     (define freevars (Atom a))
     (values freevars freevars)])

  (Atom : Atom (ir) -> * ()
    [(const ,c) (set)]
    [,x (Var x)])

  (Var : Var (ir) -> * ()
    [(lex ,n) (set n)]
    [(label ,n) (set)]
    [(proc ,n) (set)])

  (Callee : Var (ir kenv cont-acc) -> * ()
    [(lex ,n) (set)]
    [(label ,n)
     (Cont (kenv:ref kenv n) n kenv cont-acc)
     (hash-ref (hash-ref cont-acc n) 'freevars)]
    [(proc ,n) (set)])

  (CFG ir))

(define-pass select-instructions : CPCPS (ir) -> RegisterizableCPCPS ()
  (definitions
    (define (varargs-primop? op)
      (case op
        [(__tupleNew __denvPush) #t]
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
          ;; TODO: denv
          )))

    (define (emit-compound-step name op index atom)
      (with-output-language (RegisterizableCPCPS Expr)
        (case op
          [(__tupleNew) `(primcall3 __tupleInit (lex ,name) (const ,index) ,atom)]
          ;; TODO: denv
          ))))

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
    [(primcall ,p ,a* ...) (error "primop argc")]))
