#lang racket/base

(provide cps-convert relax-edges)
(require racket/match
         data/gvector
         (only-in srfi/26 cute)
         (only-in threading ~>)
         nanopass/base

         "../langs.rkt"
         (only-in "../util.rkt" zip-hash))

;; TODO: __raise doesn't return so turning it into a Transfer (just like we did
;;       with __halt) should compress the output of this somewhat
;; CPS-convert the AST.
(define-pass cps-convert : Ast (ir) -> CPS ()
  (definitions
    ;; Continuation frames:
    (struct $cont:fn (cont arges) #:transparent)
    (struct $cont:ffn (cont arges) #:transparent)
    (struct $cont:if (cont then else) #:transparent)
    (struct $cont:args (cont arges callee argas) #:transparent)
    (struct $cont:ffnargs (cont arges callee argas) #:transparent)
    (struct $cont:primargs (cont arges op argas) #:transparent)
    (struct $cont:block (cont stmts expr) #:transparent)
    (struct $cont:def (cont name) #:transparent)
    (struct $cont:return (name) #:transparent)
    (struct $cont:halt () #:transparent)

    ;; Control flow graph builder.
    (struct $cfg-builder (entry labels conts))

    ;; Create a cfg-builder with the given entry continuation.
    (define (make-cfg-builder entry)
      ($cfg-builder entry (make-gvector) (make-gvector)))

    ;; Add `cont` into `builder` under `label`.
    (define (emit-cont! builder label cont)
      (gvector-add! ($cfg-builder-labels builder) label)
      (gvector-add! ($cfg-builder-conts builder) cont))

    ;; Build the CFG from the continuations in `builder`.
    (define (build-cfg builder)
      (with-output-language (CPS CFG)
        (match-define ($cfg-builder entry labels conts) builder)
        `(cfg ([,(gvector->list labels) ,(gvector->list conts)] ...) ,entry)))

    ;; Builder for a single continuation.
    (struct $cont-builder (label formals stmts))

    ;; Make a cont-builder for the continuation labeled with the given label and formals.
    (define (make-cont-builder label formals)
      ($cont-builder label formals (make-gvector)))

    ;; Push a statement evaluating `expr` and defining name (if not #f) into (cont-)`builder`.
    (define (emit-stmt! builder name expr)
      (with-output-language (CPS Stmt)
        (gvector-add! ($cont-builder-stmts builder)
                      (if name `(def ,name ,expr) expr))))

    ;; Get a trivial expression for `expr` using (cont-)`builder` if not already trivial. If `name`
    ;; is non-#f and `expr` non-trivial return `name` after emitting into `builder`.
    (define (trivialize! builder name expr)
      (nanopass-case (CPS Expr) expr
        [,a a]
        [else (define name* (if name name (gensym 'v)))
              (emit-stmt! builder name* expr)
              (with-output-language (CPS Var) `(lex ,name*))]))

    ;; Get a trivial expression (that is, `(label ,label)) for cont, emitting into `cfg-builder` if
    ;; necessary.
    (define (trivialize-cont! cont cfg-builder)
      (define (trivialize! param continue)
        (with-output-language (CPS Transfer)
          (define label (gensym 'k))
          (define cont-builder (make-cont-builder label (list param)))
          (continue cont-builder)
          (with-output-language (CPS Var) `(label ,label))))

      (match cont
        [($cont:return ret) ret]
        [($cont:def cont param)
         (trivialize!
          param
          (match cont
            [($cont:block cont* '() expr) (cute Expr expr cont* <> cfg-builder)]
            [($cont:block cont* (cons stmt stmts) e)
             (define cont** ($cont:block cont* stmts e))
             (cute Stmt stmt cont** <> cfg-builder)]))]
        [_
         (with-output-language (CPS Var)
           (define param (gensym 'v))
           (trivialize! param (cute continue cont `(lex ,param) #f <> cfg-builder)))]))

    ;; Build the continuation using the information in `cont-builder` and ending in `transfer`.
    (define (build-cont/transfer cont-builder transfer)
      (with-output-language (CPS Cont)
        (match-define ($cont-builder label formals stmts) cont-builder)
        (values label `(cont (,formals ...)
                             ,(gvector->list stmts) ...
                             ,transfer))))

    ;; TODO: This makes no sense as an abstraction, split into multiple fns.
    ;; Build the continuation using the information in `cont-builder` and with the value of `aexpr`
    ;; halting if `labels` is empty
    ;; calling label if labels is `(,label)
    ;; calling label1 if true and label2 if false when label is `(,label1 ,label2)
    (define (build-cont/atom cont-builder aexpr . labels)
      (with-output-language (CPS Transfer)
        (build-cont/transfer
         cont-builder
         (match labels
           ['() `(halt ,aexpr)]
           [(list label) `(continue ,label ,aexpr)]
           [(list label1 label2) `(if ,aexpr ,label1 ,label2)]))))

    ;; Build the continuation using the information in `cont-builder` and ending in a tail call to
    ;; `f` with `args` and the continuation `label`.
    (define (build-cont/call cont-builder f label args)
      (with-output-language (CPS Transfer)
        (build-cont/transfer cont-builder `(call ,f ,label ,args ...))))

    ;; Like build-cont/call but for foreign function calls.
    (define (build-cont/ffncall cont-builder f label denv args)
      (with-output-language (CPS Transfer)
        (build-cont/transfer cont-builder `(ffncall ,f ,label ,denv ,args))))

    (with-output-language (CPS Expr)
      ;; Emit the code for `cont` and continuing into it with the value of `expr` and using
      ;; `name-hint` to trivialize `expr` when necessary.
      (define (continue cont expr name-hint cont-builder cfg-builder)
        (match cont
          [($cont:fn cont* '())
           (define aexpr (trivialize! cont-builder name-hint expr))
           (define cont*-label (trivialize-cont! cont* cfg-builder))
           (let-values ([(label cont) (build-cont/call cont-builder aexpr cont*-label '())])
             (emit-cont! cfg-builder label cont))]
          [($cont:fn cont* (cons arge arges))
           (define aexpr (trivialize! cont-builder name-hint expr))
           (Expr arge ($cont:args cont* arges aexpr '()) cont-builder cfg-builder)]
          [($cont:ffn cont* (cons arge arges))
           (define aexpr (trivialize! cont-builder name-hint expr))
           (Expr arge ($cont:ffnargs cont* arges aexpr '()) cont-builder cfg-builder)]
          [($cont:if cont* then-expr else-expr)
           (define aexpr (trivialize! cont-builder name-hint expr))
           (define then-label (gensym 'k))
           (define else-label (gensym 'k))
           (let-values ([(label cont) (build-cont/atom cont-builder aexpr `(label ,then-label)
                                                                          `(label ,else-label))])
             (emit-cont! cfg-builder label cont))
           (define join ($cont:return (trivialize-cont! cont* cfg-builder)))
           (Expr then-expr join (make-cont-builder then-label '()) cfg-builder)
           (Expr else-expr join (make-cont-builder else-label '()) cfg-builder)]
          [($cont:args cont* '() f argas)
           (define aexpr (trivialize! cont-builder name-hint expr))
           (define cont*-label (trivialize-cont! cont* cfg-builder))
           (let-values ([(label cont)
                         (build-cont/call cont-builder f cont*-label (reverse (cons aexpr argas)))])
             (emit-cont! cfg-builder label cont))]
          [($cont:args cont* (cons arge arges) f argas)
           (define aexpr (trivialize! cont-builder name-hint expr))
           (Expr arge ($cont:args cont* arges f (cons aexpr argas))
                 cont-builder cfg-builder)]
          [($cont:ffnargs cont* '() f (list denv))
           (define aexpr (trivialize! cont-builder name-hint expr))
           (define cont*-label (trivialize-cont! cont* cfg-builder))
           (let-values ([(label cont) (build-cont/ffncall cont-builder f cont*-label denv aexpr)])
             (emit-cont! cfg-builder label cont))]
          [($cont:ffnargs cont* (cons arge arges) f argas)
           (define aexpr (trivialize! cont-builder name-hint expr))
           (Expr arge ($cont:ffnargs cont* arges f (cons aexpr argas))
                 cont-builder cfg-builder)]
          [($cont:primargs cont* '() op argas)
           (define aexpr (trivialize! cont-builder name-hint expr))
           (continue cont* `(primcall ,op ,(reverse (cons aexpr argas)) ...) #f
                     cont-builder cfg-builder)]
          [($cont:primargs cont* (cons arge arges) op argas)
           (define aexpr (trivialize! cont-builder name-hint expr))
           (Expr arge ($cont:primargs cont* arges op (cons aexpr argas))
                 cont-builder cfg-builder)]
          [($cont:block cont* '() e)
           (emit-stmt! cont-builder name-hint expr)
           (Expr e cont* cont-builder cfg-builder)]
          [($cont:block cont* (cons stmt stmts) e)
           (emit-stmt! cont-builder name-hint expr)
           (Stmt stmt ($cont:block cont* stmts e) cont-builder cfg-builder)]
          [($cont:def cont* name)
           (continue cont* expr name cont-builder cfg-builder)]
          [($cont:return ret)
           (define aexpr (trivialize! cont-builder name-hint expr))
           (define-values (label cont) (build-cont/atom cont-builder aexpr ret))
           (emit-cont! cfg-builder label cont)]
          [($cont:halt)
           (define aexpr (trivialize! cont-builder name-hint expr))
           (define-values (label cont) (build-cont/atom cont-builder aexpr))
           (emit-cont! cfg-builder label cont)]))))

  (Expr : Expr (expr cont cont-builder cfg-builder) -> Expr ()
    [(fn (,n1* ...) ([,n2* ,fc*] ...) ,e)
     (let ([f (let* ([ret (gensym 'ret)]
                     [entry (gensym 'entry)]
                     [cont ($cont:return `(lex ,ret))]
                     [cfg-builder (make-cfg-builder entry)])
                (for-each (cute Case <> <> cont cfg-builder) fc* n2*)
                (Expr e cont (make-cont-builder entry (cons ret n1*)) cfg-builder)
                `(fn ,(build-cfg cfg-builder)))])
       (continue cont f #f cont-builder cfg-builder))]
    [(if ,e? ,e1 ,e2) (Expr e? ($cont:if cont e1 e2) cont-builder cfg-builder)]
    [(block ,e) (Expr e cont cont-builder cfg-builder)]
    [(block ,s ,s* ... ,e)
     (Stmt s ($cont:block cont s* e) cont-builder cfg-builder)]
    [(call ,e ,e* ...) (Expr e ($cont:fn cont e*) cont-builder cfg-builder)]
    [(continue ,n ,e) (Expr e ($cont:return `(label ,n)) cont-builder cfg-builder)]
    [(ffncall ,e1 ,e2 ,e3) (Expr e1 ($cont:ffn cont (list e2 e3)) cont-builder cfg-builder)]
    [(primcall ,p) (continue cont `(primcall ,p) #f cont-builder cfg-builder)]
    [(primcall ,p ,e ,e* ...)
     (Expr e ($cont:primargs cont e* p '()) cont-builder cfg-builder)]
    [,n (continue cont `(lex ,n) #f cont-builder cfg-builder)]
    [(const ,c) (continue cont `(const ,c) #f cont-builder cfg-builder)])

  (Stmt : Stmt (stmt cont cont-builder cfg-builder) -> Stmt ()
    [(def ,n ,e) (Expr e ($cont:def cont n) cont-builder cfg-builder)]
    [,e (Expr e cont cont-builder cfg-builder)])

  (Case : Case (ir label cont cfg-builder) -> Cont ()
    [(case (,n* ...) ,e) (Expr e cont (make-cont-builder label n*) cfg-builder)])

  (let* ([entry (gensym 'main)]
         [cfg-builder (make-cfg-builder entry)])
    (Expr ir ($cont:halt) (make-cont-builder entry '()) cfg-builder)
    (build-cfg cfg-builder)))

;; TODO: Don't mutate the census tables.
;; Remove critical edges.
(define-pass relax-edges : CPS (ir ltab vtab) -> CPS ()
  (definitions
    ;; Control Flow Graph builder.
    (struct $cfg-builder (conts entry))

    ;; Create a cfg-builder with the given entry continuation label.
    (define (make-cfg-builder entry)
      ($cfg-builder (make-hash) entry))

    ;; Has a continuation been emitted into `cfg-builder` under `label`?
    (define (visited? cfg-builder label)
      (hash-has-key? ($cfg-builder-conts cfg-builder) label))

    ;; Get label-cont pair of the cont formerly known by `label`, for `purpose`.
    (define (lk-ref cfg-builder label purpose)
      (~> ($cfg-builder-conts cfg-builder)
          (hash-ref label)
          (hash-ref purpose)))

    ;; Get the label of the cont formerly known by `label`, for `purpose`.
    (define (label-ref cfg-builder label purpose)
      (car (lk-ref cfg-builder label purpose)))

    ;; Get the cont formerly known by `label`, for `purpose`.
    (define (cont-ref cfg-builder label purpose)
      (cdr (lk-ref cfg-builder label purpose)))

    ;; cfg-builder[label][purpose] = (cons label* cont)
    (define (add-cont! cfg-builder label purpose cont)
      (define entry (~> ($cfg-builder-conts cfg-builder)
                        (hash-ref! label make-hash)))
      (hash-set! entry purpose (cons (if (= (hash-count entry) 0) label (gensym label))
                                     cont)))

    ;; Build a CFG using the information in builder.
    (define (build-cfg cfg-builder)
      (with-output-language (CPS CFG)
        (define-values (labels conts)
          (for/fold ([labels '()] [conts '()])
                    ([(_ entry) ($cfg-builder-conts cfg-builder)])
            (define lks (hash-values entry))
            (values (append (map car lks) labels) (append (map cdr lks) conts))))
        (for ([label labels])
          (let ([ltab-entry (hash-ref ltab label)])
            (hash-set! ltab-entry 'if-owned? (hash-has-key? ltab-entry 'if-owned?))))
        `(cfg ([,labels ,conts] ...) ,($cfg-builder-entry cfg-builder))))

    ;; Create a continuation that just delegates to the cont of `label` and `cont`.
    (define (adapter-cont label cont)
      (with-output-language (CPS Cont)
        (nanopass-case (CPS Cont) cont
          [(cont (,n* ...) ,s* ... ,t)
           (define params (map gensym n*))
           (for ([param params])
             (hash-set! vtab param (make-hash '((uses . 0))))) ;; FIXME: 0->1 (?)
           `(cont (,params ...) (continue (label ,label) (lex ,params) ...))]))))

  (CFG : CFG (ir) -> CFG ()
    [(cfg ([,n* ,k*] ...) ,n)
     (define kenv (zip-hash n* k*))
     (define cfg-builder (make-cfg-builder n))
     (Cont (hash-ref kenv n) n kenv cfg-builder)
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
    [(ffncall ,x1 ,x2 ,a* ...)
     `(ffncall ,(Callee x1 kenv cfg-builder) ,(Var x2 kenv cfg-builder)
               ,(map (cute Atom <> kenv cfg-builder) a*) ...)]
    [(halt ,a) `(halt ,(Atom a kenv cfg-builder))])

  (Atom : Atom (ir kenv cfg-builder) -> Atom ()
    [(const ,c) ir]
    [,x (Var x kenv cfg-builder)])

  (Var : Var (ir kenv cfg-builder) -> Atom ()
    [(lex ,n) ir]
    [(label ,n)
     (Cont (hash-ref kenv n) n kenv cfg-builder)
     `(label ,(label-ref cfg-builder n 'escape))])

  (Callee : Var (ir kenv cfg-builder) -> Var ()
    [(lex ,n) ir]
    [(label ,n)
     (Cont (hash-ref kenv n) n kenv cfg-builder)
     `(label ,(label-ref cfg-builder n 'default))])

  (IfCallee : Var (ir kenv cfg-builder) -> Var ()
    [(lex ,n) ir]
    [(label ,n)
     (Cont (hash-ref kenv n) n kenv cfg-builder)
     (if (> (hash-ref (hash-ref ltab n) 'calls) 1)
       (begin
         (add-cont! cfg-builder n 'critical
                    (adapter-cont n (cont-ref cfg-builder n)))
         (let ([label* (label-ref cfg-builder n 'critical)])
           (hash-set! ltab label* (make-hash '((calls . 1) (escapes . 0) (if-owned? . #t))))
           `(label ,label*)))
       (begin
         (Callee ir kenv cfg-builder)
         (hash-set! (hash-ref ltab n) 'if-owned? #t)
         `(label ,(label-ref cfg-builder n 'default))))]))
