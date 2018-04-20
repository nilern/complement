#lang racket/base

(provide eval-CPCPS eval-RegisterizableCPCPS)
(require racket/match
         (only-in srfi/26 cute)
         nanopass/base

         (only-in "../util.rkt" clj-merge zip-hash)
         "../langs.rkt"
         (only-in "../primops.rkt" primapply))

;; TODO: hash<flabel, hash<klabel, cont>>
;; TODO: dominator scoping rule
(define-syntax define-cpcps-eval
  (syntax-rules (:)
   [(_ name : IR Atom (Expr Expr-details ...))
    (define-pass name : IR (prog) -> * ()
      (definitions
        ;; Maps from continuation labels to IR code and from fn labels to entry continuation labels.
        (define-values (kenv fenv)
          (nanopass-case (IR Program) prog
            [(prog ([,n* ,blocks*] (... ...)) ,n)
             (for/fold ([kenv (hash)]
                        [fenv (hash)])
                       ([name n*] [fn-cfg blocks*])
               (nanopass-case (IR CFG) fn-cfg
                 [(cfg ([,n1* ,k*] (... ...)) (,n2* (... ...)))
                  (values (clj-merge kenv (zip-hash n1* k*))
                          (hash-set fenv name (car n2*)))]))]))

        ;; A subcont is essentially the remainder of the cont being executed.
        (struct $subcont (stmts transfer))

        ;; Move to the next Stmt (or Transfer).
        (define (sub-continue subcont curr-fn env)
          (match subcont
            [($subcont (cons stmt stmts) transfer)
             (Stmt stmt curr-fn env ($subcont stmts transfer))]
            [($subcont '() transfer) (Transfer transfer curr-fn env)]))

        ;; A code pointer consists of fn and continuation labels.
        (struct $code-ptr (fn-label cont-label))

        ;; Jump to the code pointer and bind args to params. Implements function calls, jumps to
        ;; local continuations and returns.
        (define (goto code-ptr curr-fn env args)
          (match-define ($code-ptr fn-label cont-label) code-ptr)
          (nanopass-case (IR Cont) (hash-ref kenv cont-label)
            [(cont (,n* (... ...)) ,s* (... ...) ,t)
             (let ([env (let ([env* (zip-hash n* args)])
                          (if (eq? fn-label curr-fn)
                            (clj-merge env env*)
                            env*))])
               (sub-continue ($subcont s* t) fn-label env))])))

      ;; Run the program.
      (Program : Program (ir) -> * ()
        [(prog ([,n* ,blocks*] (... ...)) ,n)
         (goto ($code-ptr n (hash-ref fenv n)) n (hash) '())])

      ;; Execute the Stmt and the rest of the cont.
      (Stmt : Stmt (stmt curr-fn env subcont) -> * ()
        [(def ,n ,e) (sub-continue subcont curr-fn (hash-set env n (Expr e curr-fn env)))]
        [,e
         (Expr e curr-fn env)
         (sub-continue subcont curr-fn env)])

      ;; Evaluate an expression (and perform side effects).
      (Expr Expr-details ...)

      ;; Perform a Transfer.
      (Transfer : Transfer (_ curr-fn env) -> * ()
        [(goto ,x ,a* (... ...))
         (goto (Var x curr-fn env) curr-fn env (map (cute Atom <> curr-fn env) a*))]
        [(ffncall ,x ,a* (... ...)) (error "unimplemented")]
        [(if ,a? ,x1 ,x2)
         (define x
           (match (Atom a? curr-fn env)
             [#t x1]
             [#f x2]))
         (goto (Var x curr-fn env) curr-fn env '())]
        [(halt ,a) (Atom a curr-fn env)]
        [(raise ,a) (error "unimplemented")])

      ;; Evaluate an Atom.
      (Atom : Atom (_ curr-fn env) -> * ()
        [(const ,c) c]
        [,x         (Var x curr-fn env)])

      ;; Look up the value of a Var. `label` and `proc` produce appropriate $code-ptr:s.
      (Var : Var (_ curr-fn env) -> * ()
        [(lex ,n)   (hash-ref env n)]
        [(label ,n) ($code-ptr curr-fn n)]
        [(proc ,n)  ($code-ptr n (hash-ref fenv n))]))]))

(define-cpcps-eval eval-CPCPS : CPCPS
  Atom
  (Expr : Expr (expr curr-fn env) -> * ()
    [,a                    (Atom a curr-fn env)]
    [(primcall ,p ,a* ...) (primapply p (map (cute Atom <> curr-fn env) a*))]))

(define-cpcps-eval eval-RegisterizableCPCPS : RegisterizableCPCPS
  Atom
  (Expr : Expr (expr curr-fn env) -> * ()
    [,a                         (Atom a curr-fn env)]
    [(primcall0 ,p)             (primapply p '())]
    [(primcall1 ,p ,a)          (primapply p (map (cute Atom <> curr-fn env) (list a)))]
    [(primcall2 ,p ,a1 ,a2)     (primapply p (map (cute Atom <> curr-fn env) (list a1 a2)))]
    [(primcall3 ,p ,a1 ,a2 ,a3) (primapply p (map (cute Atom <> curr-fn env) (list a1 a2 a3)))]))
