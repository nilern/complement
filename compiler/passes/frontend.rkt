#lang racket/base

(provide alphatize lex-straighten introduce-dyn-env add-dispatch)
(require racket/match racket/list racket/hash (only-in srfi/26 cute) (only-in threading ~>>)
         (only-in racket/function identity)
         nanopass/base
         "../langs.rkt" (only-in "../util.rkt" clj-group-by))

;; Give each lexical variable a unique name.
(define-pass alphatize : Cst (cst) -> Cst ()
  (definitions
    ;; Renaming-env frame for method param.
    (define (param-bindings param)
      (nanopass-case (Cst Var) param
        [(lex ,n) (hash n (gensym n))]
        [else (hash)]))

    ;; Renaming-env frame for method params.
    (define (params-bindings params)
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
     (define env* (push-frame env (params-bindings x*)))
     `(case (,(map (cute Var <> env*) x*) ...) ,(Expr e? env*) ,(Expr e env*))]
    [(case ,x ,e? ,e)
     (define env* (push-frame env (param-bindings x)))
     `(case ,(Var x env*) ,(Expr e? env*) ,(Expr e env*))])

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

    ;; Get the lexical names bound by a variable.
    (define (var-binders var)
      (nanopass-case (Cst Var) var
        [(lex ,n) (list n)]
        [(dyn ,n) '()]))

    ;; Get the lexical names bound by case parameters.
    (define (case-binders params)
      (append-map var-binders params))

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
       `(case (,x* ...) ,(Expr e? env) ,(Expr e env)))]
    [(case ,x ,e? ,e)
     (let ([env (env:push-fn env (var-binders x))])
       `(case ,x ,(Expr e? env) ,(Expr e env)))])

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

    ;; A `((const ,name) ,param) for every dynamic param and the lexical param (a temp if param is
    ;; dynamic).
    (define (fn-binding param)
      (with-output-language (LexCst Expr)
        (nanopass-case (Cst Var) param
          [(lex ,n) (values '() n)]
          [(dyn ,n)
           (define n* (gensym n))
           (values (list (list `(const ,n) n*)) n*)])))

    ;; A `((const ,name) ,param) for every dynamic param and the list of lexical params including
    ;; temps for the dynamic params.
    (define (fn-bindings params)
      (define-values (bindings lex-params)
        (for/fold ([bindings '()] [lex-params '()])
                  ([param params])
          (let-values ([(bindings* lex-param) (fn-binding param)])
            (values (append bindings* bindings)
                    (cons lex-param lex-params)))))
      (values (reverse bindings) (reverse lex-params)))

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
    [(call ,[e] ,[e*] ...) `(call ,e ,(cons denv-name e*) ...)]
    [(ffncall ,[e1] ,[e2]) `(ffncall ,e1 ,denv-name ,e2)])

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
             (Expr e denv-name))))]
    [(case ,x ,e? ,e)
     (let*-values ([(bindings lex-param) (fn-binding x)]
                   [(push denv-name) (emit-push denv-name bindings)])
       `(case ,lex-param ,(Expr e? denv-name)
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

    ;; Return the fields of a (LexCst Case)
    (define (unapply-case case)
      (nanopass-case (LexCst Case) case
        [(case (,n* ...) ,e? ,e) (values n* (Expr e?) (Expr e))]
        [(case ,n ,e? ,e) (values n (Expr e?) (Expr e))]))

    (define (emit-case-body argv argc case next)
      (with-output-language (Ast Expr)
        (define (emit-inner cond body)
          (match/values (const-value cond)
            [(#t #t) body]
            [(#t #f) `(continue ,next ,argc)] ; OPTIMIZE: These cases should just be skipped
            [(_ _) `(if ,cond ,body (continue ,next ,argc))]))

        (let*-values ([(params cond body) (unapply-case case)]
                      [(condv-known? condv) (const-value cond)])
          (if (list? params)
            `(if (primcall __iEq ,argc (const ,(length params)))
               (block ,(for/list ([(p i) (in-indexed params)])
                         (with-output-language (Ast Stmt)
                           `(def ,p (primcall __tupleGet ,argv (const ,i))))) ...
                 ,(emit-inner cond body))
               (continue ,next ,argc))
            `(block (def ,params ,argv)
               ,(emit-inner cond body))))))

    (define ((emit-case argv) case next)
      (with-output-language (Ast Case)
        (define argc (gensym 'argc))
        `(case (,argc) ,(emit-case-body argv argc case next)))))

  (Expr : Expr (ir) -> Expr ()
    [(fn ,n ,fc* ...)
     (let* ([argv (gensym 'argv)]
            [first-argc (gensym 'argc)]
            [fail-argc (gensym 'argc)]
            [succ-labels (map (lambda (_) (gensym 'k)) (rest fc*))]
            [fail-label (gensym 'k)]
            [labels (append succ-labels (list fail-label))])
       `(fn (,n ,argv)
          ([,succ-labels ,(map (emit-case argv) (rest fc*) (rest labels))] ...
           [,fail-label  (case (,fail-argc) (primcall __raise (const NoSuchMethod)))])
          (block (def ,first-argc (primcall __tupleLength ,argv))
            ,(emit-case-body argv first-argc (first fc*) (first labels)))))]
    [(call ,[e1] ,[e2] ,[e*] ...)
     `(call ,e1 ,e2 (primcall __tupleNew ,e* ...))]))
