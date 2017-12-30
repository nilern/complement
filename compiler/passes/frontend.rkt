#lang racket/base

(provide alphatize lex-straighten introduce-dyn-env add-dispatch)
(require racket/match racket/list racket/hash (only-in srfi/26 cute) (only-in threading ~>>)
         (only-in racket/function identity)
         nanopass/base
         "../langs.rkt" (only-in "../util.rkt" clj-group-by))

;; Give each lexical variable a unique name.
(define-pass alphatize : Cst (cst) -> Cst ()
  (definitions
    ;; Renaming-env frame for method params.
    (define (param-bindings params)
      (for/fold ([env (hash)])
                ([param params])
        (nanopass-case (Cst Var) param
          [(lex ,n) (hash-set env n (gensym n))]
          [else env])))

    ;; Renaming-env frame for block definitions.
    (define (block-bindings stmts)
      (for/fold ([env (hash)])
                ([stmt stmts])
        (nanopass-case (Cst Stmt) stmt
          [(def (lex ,n) ,e) (hash-set env n (gensym n))]
          [else env])))

    ;; Extend `env` with `bindings`.
    (define (push-frame env bindings)
      (hash-union env bindings #:combine (λ (_ v) v))))

  (Expr : Expr (cst env) -> Expr ()
    [(block ,s* ... ,e)
     (define env* (push-frame env (block-bindings s*)))
     `(block ,(map (cute Stmt <> env*) s*) ... ,(Expr e env*))])

  (Stmt : Stmt (cst env) -> Stmt ())

  (Case : Case (cst env) -> Case ()
    [(case (,x* ...) ,e? ,e)
     (define env* (push-frame env (param-bindings x*)))
     `(case (,(map (cute Var <> env*) x*) ...) ,(Expr e? env*) ,(Expr e env*))])

  (Var : Var (cst env) -> Var ()
    [(lex ,n) `(lex ,(hash-ref env n))])

  (Expr cst (hash)))

;; Make recursive lexical bindings explicit with box allocations and assignments.
(define-pass lex-straighten : Cst (ir) -> Cst ()
  (definitions
    ;; Empty environment.
    (define (env:empty) (hash))

    ;; Extend environment with method parameters.
    (define (env:push-fn parent binders)
      (for/fold ([env parent])
                ([binder binders])
        (hash-set env binder 'plain)))

    ;; Extend environment with block definitions.
    (define (env:push-block parent binders)
      (for/fold ([env parent])
                ([binder binders])
        (hash-set env binder (box #f))))

    ;; Get the variable description from environment.
    (define env:ref hash-ref)

    ;; Get the lexical names bound by case parameters.
    (define (case-binders params)
      (define (step param binders)
        (nanopass-case (Cst Var) param
          [(lex ,n) (cons n binders)]
          [(dyn ,n) binders]))
      (foldr step '() params))

    ;; Get the lexical names bound in a block.
    (define (block-binders stmts)
      (define (step stmt binders)
        (nanopass-case (Cst Stmt) stmt
          [(def (lex ,n) ,e) (cons n binders)]
          [else binders]))
      (foldr step '() stmts))

    ;; Return box allocation Stmt for name, #f if unnecessary (binding is not recursive).
    (define (emit-init env name)
      (with-output-language (Cst Stmt)
        (match (env:ref env name)
          [(or 'plain (box 'plain) (box #f)) #f]
          [(box 'boxed) `(def (lex ,name) (primcall __boxNew))])))

    ;; Return definition Stmt for name. If binding is recursive, it will be a box assignment instead
    ;; of a definition.
    (define (emit-set env name expr)
      (with-output-language (Cst Stmt)
        (match (env:ref env name)
          [(or 'plain (box 'plain)) `(def (lex ,name) ,expr)]
          [(and loc (box #f))
           (set-box! loc 'plain) ; Was defined before every use, remember that.
           `(def (lex ,name) ,expr)]
          [(box 'boxed) `(primcall __boxSet (lex ,name) ,expr)])))

    ;; return an access Expr for name. If binding is recursive, it will be a box dereference instead
    ;; of a direct variable reference.
    (define (emit-get env name)
      (with-output-language (Cst Expr)
        (match (env:ref env name)
          [(or 'plain (box 'plain)) `(lex ,name)]
          [(and loc (box status))
           (unless status (set-box! loc 'boxed)) ; Was accessed before definition, remember that.
           `(primcall __boxGet (lex ,name))]))))

  (Expr : Expr (ir env) -> Expr ()
    [(block ,s* ... ,e)
     (let* ([binders (block-binders s*)]
            [env (env:push-block env binders)]
            [stmts (map (cute Stmt <> env) s*)]
            [expr (Expr e env)])
       `(block ,(filter identity (map (cute emit-init env <>) binders)) ...
               ,stmts ...
               ,expr))]
    [(lex ,n) (emit-get env n)])

  (Stmt : Stmt (ir env) -> Stmt ()
    [(def (lex ,n) ,[e]) (emit-set env n e)])

  (Case : Case (ir env) -> Case ()
    [(case (,x* ...) ,e? ,e)
     (let ([env (env:push-fn env (case-binders x*))])
       `(case (,x* ...) ,(Expr e? env) ,(Expr e env)))])

  (Expr ir (env:empty)))

;; Reify dynamic environment and pass it around explicitly.
(define-pass introduce-dyn-env : Cst (cst) -> LexCst ()
  (definitions
    ;; A `((const ,name) (primcall __boxNew)) for every dynamic var defined in block.
    (define (block-bindings stmts)
      (with-output-language (LexCst Expr)
        (define (step stmt bindings)
          (nanopass-case (Cst Stmt) stmt
            [(def (dyn ,n) ,e) (cons (list `(const ,n) `(primcall __boxNew)) bindings)]
            [else bindings]))
        (foldr step '() stmts)))

    ;; A `((const ,name) ,param) for every dynamic param and the list of lexical params including
    ;; temps for the dynamic params.
    (define (fn-bindings params)
      (with-output-language (LexCst Expr)
        (define-values (bindings lex-params)
          (for/fold ([bindings '()] [lex-params '()])
                    ([param params])
            (nanopass-case (Cst Var) param
              [(lex ,n) (values bindings (cons n lex-params))]
              [(dyn ,n)
               (define n* (gensym n))
               (values (cons (list `(const ,n) n*) bindings)
                       (cons n* lex-params))])))
        (values (reverse bindings) (reverse lex-params))))

    ;; Code for the allocation of the initial dynamic env.
    (define (emit-init denv-name)
      (with-output-language (LexCst Stmt)
        `(def ,denv-name (primcall __denvNew))))

    ;; Code for the allocation of a new dynamic env frame and the name to use for it. If bindings is
    ;; empty #f is returned instead of code and the name is the denv-name argument.
    (define (emit-push denv-name bindings)
      (with-output-language (LexCst Stmt)
        (match bindings
          ['() (values #f denv-name)]
          [_ (define denv-name* (gensym 'denv))
             (values `(def ,denv-name* (primcall __denvPush ,denv-name ,(flatten bindings) ...))
                     denv-name*)])))

    ;; Code for dynamic var reference.
    (define (emit-get denv-name name)
      (with-output-language (LexCst Expr) `(primcall __denvGet ,denv-name (const ,name))))

    ;; Code for dynamic var initialization.
    (define (emit-set denv-name name expr)
      (with-output-language (LexCst Expr)`(primcall __boxSet ,(emit-get denv-name name) ,expr))))

  (Expr : Expr (cst denv-name) -> Expr ()
    [(block ,s* ... ,e)
     (let*-values ([(bindings) (block-bindings s*)]
                   [(push denv-name*) (emit-push denv-name bindings)]
                   [(stmts) (map (cute Stmt <> denv-name*) s*)]
                   [(expr) (Expr e denv-name*)])
       (if push
         `(block ,push ,stmts ... ,expr)
         `(block ,stmts ... ,expr)))]
    [(fn ,fc* ...)
     (define denv-name (gensym 'denv))
     `(fn ,denv-name ,(map (cute Case <> denv-name) fc*) ...)]
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
    `(block ,(emit-init denv-name) ,(Expr cst denv-name))))

;; Make function method dispatch explicit using if-expressions.
(define-pass add-dispatch : LexCst (ir) -> Ast ()
  (definitions
    ;; Can expr be reduced to a constant value and if so, also that value.
    (define (const-value expr) ; TODO: use option type for this
      (nanopass-case (Ast Expr) expr
        [(const ,c) (values #t c)]
        [else (values #f expr)]))

    ;; Code for the cases of a certain arity, dispatching on the case preconditions.
    (define (emit-cases argv cases)
      (with-output-language (Ast Expr)
        (match cases
          [(cons (list params cond body) cases*)
           (define-values (condv-known? condv) (const-value cond))
           `(block ,(for/list ([(p i) (in-indexed params)])
                      (with-output-language (Ast Stmt)
                        `(def ,p (primcall __tupleGet ,argv (const ,i))))) ...
             ,(match/values (const-value cond)
                [(#t #t) body]
                [(#t #f) (emit-cases argv cases*)]
                [(_ _) `(if ,cond ,body ,(emit-cases argv cases*))]))]
          ['() `(primcall __raise (const PreCondition))])))

    ;; Code for the function body, dispatching on arity.
    (define (emit-arities argv argc arities)
      (with-output-language (Ast Expr)
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
