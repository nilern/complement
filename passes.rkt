#lang racket

(provide alphatize infer-decls lex-straighten introduce-dyn-env add-dispatch
         cps-convert remove-nontail-calls)
(require racket/hash data/gvector (only-in threading ~>>) nanopass/base
         (only-in "util.rkt" clj-group-by) "langs.rkt")

(define-pass alphatize : Cst (cst) -> Cst ()
  (definitions
    (define (param-bindings params)
      (for/fold ([env (hash)])
                ([param params])
        (nanopass-case (Cst Var) param
          [(lex ,n) (hash-set env n (gensym n))]
          [else env])))
    
    (define (block-bindings stmts)
      (for/fold ([env (hash)])
                ([stmt stmts])
        (nanopass-case (Cst Stmt) stmt
          [(def (lex ,n) ,e) (hash-set env n (gensym n))]
          [else env])))

    (define (push-frame env bindings)
      (hash-union env bindings #:combine (λ (_ v) v))))
  
  (Expr : Expr (cst env) -> Expr ()
    [(block ,s* ... ,e)
     (define env* (push-frame env (block-bindings s*)))
     `(block ,(map (λ (stmt) (Stmt stmt env*)) s*) ...
             ,(Expr e env*))])

  (Stmt : Stmt (cst env) -> Stmt ())

  (Case : Case (cst env) -> Case ()
    [(case (,x* ...) ,e? ,e)
     (define env* (push-frame env (param-bindings x*)))
     `(case (,(map (λ (p) (Var p env*)) x*) ...) ,(Expr e? env*)
        ,(Expr e env*))])
    
  (Var : Var (cst env) -> Var ()
    [(lex ,n) `(lex ,(hash-ref env n))])

  (Expr cst (hash)))

(define-pass infer-decls : Cst (cst) -> DeclCst ()
  (definitions
    (define (binders stmts)
      (define (stmt-binders stmt)
        (with-output-language (DeclCst Var)
          (nanopass-case (DeclCst Stmt) stmt
            [(def (lex ,n) ,e) (list `(lex ,n))]
            [(def (dyn ,n) ,e) (list `(dyn ,n))]
            [,e '()])))
      (append-map stmt-binders stmts)))
  
  (Expr : Expr (cst) -> Expr ()
    [(block ,[s*] ... ,[e]) `(block (,(binders s*) ...) ,s* ... ,e)]))

(define-pass lex-straighten : DeclCst (cst) -> DynDeclCst ()
  (definitions
    (define (env:empty) (hash))

    (define (env:push-fn parent binders)
      (for/fold ([env parent])
                ([binder binders])
        (hash-set env binder 'plain)))

    (define (env:push-block parent binders)
      (for/fold ([env parent])
                ([binder binders])
        (hash-set env binder (box #f))))

    (define env:ref hash-ref)

    (define (lex-params decls)
      (reverse (for/fold ([lex-decls '()])
                         ([decl decls])
                 (nanopass-case (DynDeclCst Var) decl
                   [(lex ,n) (cons n lex-decls)]
                   [(dyn ,n) lex-decls]))))
    
    (define (partition-decls decls)
      (define-values (lex-decls dyn-decls)
        (for/fold ([lex-decls '()] [dyn-decls '()])
                  ([decl decls])
          (nanopass-case (DeclCst Var) decl
            [(lex ,n) (values (cons n lex-decls) dyn-decls)]
            [(dyn ,n) (values lex-decls (cons n dyn-decls))])))
      (values (reverse lex-decls) (reverse dyn-decls)))

    (with-output-language (DynDeclCst Stmt)
      (define (emit-init env name)
        (match (env:ref env name)
          [(or 'plain (box 'plain) (box #f)) #f]
          [(box 'boxed) `(def (lex ,name) (primcall __boxNew))]))
      (define (emit-set env name expr)
        (match (env:ref env name)
          [(or 'plain (box 'plain)) `(def (lex ,name) ,expr)]
          [(and loc (box #f))
           (set-box! loc 'plain)
           `(def (lex ,name) ,expr)]
          [(box 'boxed) `(primcall __boxSet (lex ,name) ,expr)])))
    (with-output-language (DynDeclCst Expr)
      (define (emit-get env name)
        (match (env:ref env name)
          [(or 'plain (box 'plain)) `(lex ,name)]
          [(and loc (box status))
           (unless status (set-box! loc 'boxed))
           `(primcall __boxGet (lex ,name))]))))
  
  (Expr : Expr (cst env) -> Expr ()
    [(block (,x* ...) ,s* ... ,e)
     (define-values (lex-decls dyn-decls) (partition-decls x*))
     (define env* (env:push-block env lex-decls))
     (define stmts (map (λ (stmt) (Stmt stmt env*)) s*))
     (define expr (Expr e env*))
     `(block (,dyn-decls ...)
             ,(append (filter identity
                              (map (λ (ldecl) (emit-init env* ldecl))
                                   lex-decls))
                      stmts) ...
             ,expr)]
    [(lex ,n) (emit-get env n)])

  (Stmt : Stmt (cst env) -> Stmt ()
    [(def (lex ,n) ,[e]) (emit-set env n e)])

  (Case : Case (cst env) -> Case ()
    [(case (,[x*] ...) ,e? ,e)
     (define lex-decls (lex-params x*))
     (define env* (env:push-fn env lex-decls))
     `(case (,x* ...) ,(Expr e? env*) ,(Expr e env*))])

  (Expr cst (env:empty)))

(define-pass introduce-dyn-env : DynDeclCst (cst) -> LexCst ()
  (definitions
    (with-output-language (LexCst Expr)
      (define (block-bindings decls)
        (for/list ([decl decls])
          (list `(const ,decl) `(primcall __boxNew))))

      (define (fn-bindings params)
        (define-values (bindings lex-params)
          (for/fold ([bindings '()] [lex-params '()])
                    ([param params])
            (nanopass-case (DynDeclCst Var) param
              [(lex ,n) (values bindings (cons n lex-params))]
              [(dyn ,n)
               (define n* (gensym n))
               (values (cons (list `(const ,n) n*) bindings)
                       (cons n* lex-params))])))
        (values (reverse bindings) (reverse lex-params))))
    
    (with-output-language (LexCst Stmt)
      (define (emit-init denv-name)
        `(def ,denv-name (primcall __denvNew)))
      (define (emit-push denv-name bindings)
        (match bindings
          ['() (values #f denv-name)]
          [_ (define denv-name* (gensym 'denv))
             (values `(def ,denv-name* (primcall __denvPush ,denv-name
                                                 ,(flatten bindings) ...))
                     denv-name*)])))
      
    (with-output-language (LexCst Expr)
      (define (emit-get denv-name name)
        `(primcall __denvGet ,denv-name (const ,name)))
      (define (emit-set denv-name name expr)
        `(primcall __boxSet ,(emit-get denv-name name) ,expr))))
  
  (Expr : Expr (cst denv-name) -> Expr ()
    [(block (,n* ...) ,s* ... ,e)
     (let*-values ([(bindings) (block-bindings n*)]
                   [(push denv-name*) (emit-push denv-name bindings)]
                   [(stmts) (map (λ (stmt) (Stmt stmt denv-name*)) s*)]
                   [(expr) (Expr e denv-name*)])
       (if push
         `(block ,push ,stmts ... ,expr)
         `(block ,stmts ... ,expr)))]
    [(fn ,fc* ...)
     (define denv-name (gensym 'denv))
     `(fn ,denv-name ,(map (λ (case) (Case case denv-name)) fc*) ...)]
    [(call ,[e] ,[e*] ...) `(call ,e ,(cons denv-name e*) ...)])
        
  (Stmt : Stmt (cst denv-name) -> Stmt ()
    [(def (lex ,n) ,[e]) `(def ,n ,e)]
    [(def (dyn ,n) ,[e]) (emit-set denv-name n e)]
    [else (Expr cst denv-name)])

  (Case : Case (cst denv-name) -> Case ()
    [(case (,x* ...) ,e? ,e)
     (let*-values ([(bindings lex-params) (fn-bindings x*)]
                   [(push denv-name) (emit-push denv-name bindings)])
       `(case (,lex-params ...) ,(Expr e? denv-name)
          ,(if push
             (with-output-language (LexCst Expr)
               `(block ,push ,(Expr e denv-name)))
             (Expr e denv-name))))])

  (Var : Var (cst denv-name) -> Expr ()
    [(lex ,n) n]
    [(dyn ,n) (emit-get denv-name n)])

  (let ([denv-name (gensym 'denv)])
    `(block ,(emit-init denv-name)
            ,(Expr cst denv-name))))

(define-pass add-dispatch : LexCst (ir) -> Ast ()
  (definitions
    (with-output-language (Ast Expr)
      (define (emit-cases argv cases)
        (match cases
          [(cons (list params cond body) cases*)
           `(block ,(for/list ([(p i) (in-indexed params)])
                      (with-output-language (Ast Stmt)
                        `(def ,p (primcall __tupleGet ,argv (const ,i))))) ...
                   ;; TODO: constant fold the branch (if possible) right away:
                   (if ,cond ,body ,(emit-cases argv cases*)))]
          ['() `(primcall __raise (const PreCondition))]))

      (define (emit-arities argv argc arities)
        (match arities
          [(cons (cons arity cases) arities*)
           `(if (primcall __iEq ,argc (const ,arity))
              ,(emit-cases argv cases)
              ,(emit-arities argv argc arities*))]
          ['() `(primcall __raise (const Arity))]))))
  
  (Expr : Expr (ir) -> Expr ()
    [(fn ,n (case (,n** ...) ,[e?*] ,[e*]) ...)
     (let* ([argv (gensym 'argv)]
            [argc (gensym 'argc)]
            [arities (~>> (map list n** e?* e*)
                          (clj-group-by (compose1 length car))
                          hash->list
                          (sort _ < #:key car))])
       `(fn (,n ,argv)
          (block
            (def ,argc (primcall __tupleLength ,argv))
            ,(emit-arities argv argc arities))))]
    [(call ,[e1] ,[e2] ,[e*] ...)
     `(call ,e1 ,e2 (primcall __tupleNew ,e* ...))]))

;; TODO: cps-convert : Ast (ast) -> CPS ()
(define-pass cps-convert : LexCst (ir) -> CPS ()
  (definitions
    (struct $cont:fn (cont arges) #:transparent)
    (struct $cont:args (cont arges callee argas) #:transparent)
    (struct $cont:primargs (cont arges op argas) #:transparent)
    (struct $cont:block (cont stmts expr) #:transparent)
    (struct $cont:def (cont name) #:transparent)
    (struct $cont:return (name) #:transparent)
    (struct $cont:halt () #:transparent)

    (with-output-language (CPS Stmt)
      (define (trivialize! stmt-acc name expr)
        (nanopass-case (CPS Expr) expr
          [,a a]
          [else (define name* (if name name (gensym 'v)))
                (gvector-add! stmt-acc `(def ,name* ,expr))
                name*]))
      
      (define (emit-stmt! stmt-acc name expr)
        (gvector-add! stmt-acc (if name `(def ,name ,expr) expr))))
    
    (with-output-language (CPS Cont)
      (define (emit-cont! label-acc cont-acc label formals stmts transfer)
        (gvector-add! label-acc label)
        (gvector-add! cont-acc `(cont (,formals ...) ,stmts ... ,transfer))))
    
    (with-output-language (CPS Transfer)
      (define (emit-transfer! stmt-acc label expr)
        (if label
          (nanopass-case (CPS Expr) expr
            [,a `(continue ,label ,expr)]
            [(call ,a ,a* ...) `(call ,a ,label ,a* ...)]
            [else (define v (gensym 'v))
                  (emit-stmt! stmt-acc v expr)
                  (emit-transfer! stmt-acc label v)])
          (nanopass-case (CPS Expr) expr
            [,a `(halt ,a)]
            [else (define v (gensym 'v))
                  (emit-stmt! stmt-acc v expr)
                  (emit-transfer! stmt-acc label v)]))))
    
    (with-output-language (CPS Expr)                  
      (define (continue cont expr expr-name stmt-acc label-acc cont-acc)
        (match cont
          [($cont:fn cont* '())
           (define aexpr (trivialize! stmt-acc expr-name expr))
           (continue cont* `(call ,aexpr) #f stmt-acc label-acc cont-acc)]
          [($cont:fn cont* (cons arge arges))
           (define aexpr (trivialize! stmt-acc expr-name expr))
           (Expr arge ($cont:args cont* arges aexpr '()) stmt-acc label-acc cont-acc)]
          [($cont:args cont* '() f argas)
           (define aexpr (trivialize! stmt-acc expr-name expr))
           (continue cont* `(call ,f ,(reverse (cons aexpr argas)) ...) #f
                     stmt-acc label-acc cont-acc)]
          [($cont:args cont* (cons arge arges) f argas)
           (define aexpr (trivialize! stmt-acc expr-name expr))
           (Expr arge ($cont:args cont* arges f (cons aexpr argas))
                 stmt-acc label-acc cont-acc)]
          [($cont:primargs cont* '() op argas)
           (define aexpr (trivialize! stmt-acc expr-name expr))
           (continue cont* `(primcall ,op ,(reverse (cons aexpr argas)) ...) #f
                     stmt-acc label-acc cont-acc)]
          
          [($cont:primargs cont* (cons arge arges) op argas)
           (define aexpr (trivialize! stmt-acc expr-name expr))
           (Expr arge ($cont:primargs cont* arges op (cons aexpr argas))
                 stmt-acc label-acc cont-acc)]
          [($cont:block cont* '() e)
           (emit-stmt! stmt-acc expr-name expr)
           (Expr e cont* stmt-acc label-acc cont-acc)]
          [($cont:block cont* (cons stmt stmts) e)
           (emit-stmt! stmt-acc expr-name expr)
           (Stmt stmt ($cont:block cont* stmts e) stmt-acc label-acc cont-acc)]
          [($cont:def cont* name)
           (continue cont* expr name stmt-acc label-acc cont-acc)]
          [($cont:return label) (emit-transfer! stmt-acc label expr)]
          [($cont:halt) (emit-transfer! stmt-acc #f expr)]))))
  
  (Expr : Expr (expr cont stmt-acc label-acc cont-acc) -> Expr ()
    [(fn ,n (case (,n* ...) ,e? ,e))
     (define f
       (let* ([entry (gensym 'entry)]
              [ret (gensym 'ret)]
              [stmt-acc (make-gvector)]
              [label-acc (make-gvector)]
              [cont-acc (make-gvector)]
              [transfer (Expr e ($cont:return ret) stmt-acc label-acc cont-acc)])
         (emit-cont! label-acc cont-acc
                     entry (cons ret (cons n n*)) (gvector->list stmt-acc) transfer)
         `(fn ([,(gvector->list label-acc) ,(gvector->list cont-acc)] ...) ,entry)))
     (continue cont f #f stmt-acc label-acc cont-acc)]
    [(block ,e) (Expr e cont stmt-acc label-acc cont-acc)]
    [(block ,s ,s* ... ,e)
     (Stmt s ($cont:block cont s* e) stmt-acc label-acc cont-acc)]
    [(call ,e ,e* ...)
     (Expr e ($cont:fn cont e*) stmt-acc label-acc cont-acc)]
    [(primcall ,p) (continue cont `(primcall ,p) #f stmt-acc label-acc cont-acc)]
    [(primcall ,p ,e ,e* ...)
     (Expr e ($cont:primargs cont e* p '()) stmt-acc label-acc cont-acc)]
    [,n (continue cont n #f stmt-acc label-acc cont-acc)]
    [(const ,c) (continue cont `(const ,c) #f stmt-acc label-acc cont-acc)])

  (Stmt : Stmt (stmt cont stmt-acc label-acc cont-acc) -> Stmt ()
    [(def ,n ,e) (Expr e ($cont:def cont n) stmt-acc label-acc cont-acc)]
    [,e (Expr e cont stmt-acc label-acc cont-acc)])

  (let* ([entry (gensym 'main)]
         [stmt-acc (make-gvector)]
         [label-acc (make-gvector)]
         [cont-acc (make-gvector)]
         [transfer (Expr ir ($cont:halt) stmt-acc label-acc cont-acc)])
    (emit-cont! label-acc cont-acc entry '() (gvector->list stmt-acc) transfer)
    `(prog ([,(gvector->list label-acc) ,(gvector->list cont-acc)] ...) ,entry)))

(define-pass remove-nontail-calls : CPS (ir) -> TailCPS ()
  (definitions
    (with-output-language (TailCPS Stmt)
      (define (emit-stmt! stmt-acc name-hint expr)
        (gvector-add! stmt-acc (if name-hint `(def ,name-hint ,expr) expr))))
      
    (with-output-language (TailCPS Cont)
      (define (emit-cont! label-acc cont-acc name params stmt-acc transfer)
        (gvector-add! label-acc name)
        (gvector-add! cont-acc `(cont (,params ...)
                                      ,(gvector->list stmt-acc) ...
                                      ,transfer))))
    
    (define (eval-block stmts transfer name params stmt-acc label-acc cont-acc)
      (match stmts
        [(cons stmt stmts*)
         (Stmt stmt stmts* transfer name params stmt-acc label-acc cont-acc)]
        ['() (Transfer transfer name params stmt-acc label-acc cont-acc)])))
  
  (Program : Program (ir) -> Program ()
    [(prog ([,n* ,k*] ...) ,n)
     (let ([label-acc (make-gvector)]
           [cont-acc (make-gvector)])
       (for ([label n*] [cont k*])
         (Cont cont label label-acc cont-acc))
       `(prog ([,(gvector->list label-acc) ,(gvector->list cont-acc)] ...)
              ,n))])

  (Cont : Cont (ir name label-acc cont-acc) -> * ()
    [(cont (,n* ...) ,s* ... ,t)
     (define stmt-acc (make-gvector))
     (eval-block s* t name n* stmt-acc label-acc cont-acc)])

  (Stmt : Stmt (ir stmts transfer name params stmt-acc label-acc cont-acc)
        -> * ()
    [(def ,n ,e)
     (Expr e n stmts transfer name params stmt-acc label-acc cont-acc)]
    [,e (Expr e #f stmts transfer name params stmt-acc label-acc cont-acc)])

  (Expr : Expr (ir name-hint stmts transfer name params stmt-acc
                label-acc cont-acc) -> Expr ()
    [,a
     (emit-stmt! stmt-acc name-hint (Atom a))
     (eval-block stmts transfer name params stmt-acc label-acc cont-acc)]
    [(fn ([,n* ,k*] ...) ,n)
     (define expr
       (let ([label-acc (make-gvector)]
             [cont-acc (make-gvector)])
         (for ([label n*] [cont k*])
           (Cont cont label label-acc cont-acc))
         `(fn ([,(gvector->list label-acc) ,(gvector->list cont-acc)] ...) ,n)))
     (emit-stmt! stmt-acc name-hint expr)
     (eval-block stmts transfer name params stmt-acc label-acc cont-acc)]
    [(primcall ,p ,[a*] ...)
     (emit-stmt! stmt-acc name-hint `(primcall ,p ,a* ...))
     (eval-block stmts transfer name params stmt-acc label-acc cont-acc)]
    [(call ,[a] ,[a*] ...)
     (define next-label (gensym 'k))
     (with-output-language (TailCPS Transfer)
       (emit-cont! label-acc cont-acc
                   name params stmt-acc `(call ,a ,next-label ,a* ...)))
     (let ([rv (if name-hint name-hint (gensym '_))]
           [stmt-acc (make-gvector)])
       (eval-block stmts transfer next-label (list rv) stmt-acc
                   label-acc cont-acc))])

  (Transfer : Transfer (ir name params stmt-acc label-acc cont-acc)
            -> Transfer ()
    [(continue ,n ,[a*] ...)
     (emit-cont! label-acc cont-acc
                 name params stmt-acc `(continue ,n ,a* ...))]
    [(call ,[a] ,n ,[a*] ...)
     (emit-cont! label-acc cont-acc name params stmt-acc `(call ,a ,n ,a* ...))]
    [(halt ,[a])
     (emit-cont! label-acc cont-acc name params stmt-acc `(halt ,a))])

  (Atom : Atom (ir) -> Atom ()))
