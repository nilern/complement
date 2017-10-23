#lang racket/base

(provide allocate-registers)
(require racket/match racket/list racket/set (only-in srfi/26 cute)
         nanopass/base
         "langs.rkt"
         (prefix-in ltab: (submod "cpcps-passes.rkt" label-table))
         (prefix-in kenv: (submod "util.rkt" cont-env))
         (prefix-in cfg: "cfg.rkt") (only-in "util.rkt" unzip-hash))

(define-pass cfg-liveness : RegisterizableCPCPS (ir) -> * ()
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
    [(primcall0 ,p) (set)]
    [(primcall1 ,p ,a) (Atom a)]
    [(primcall2 ,p ,a1 ,a2) (set-union (Atom a1) (Atom a2))]
    [(primcall3 ,p ,a1 ,a2 ,a3) (set-union (Atom a1) (Atom a2) (Atom a3))]
    [,a (Atom a)])

  (Transfer : Transfer (ir kenv cont-acc) -> * ()
    [(goto ,x ,a* ...)
     (freevars+luses (Callee x kenv cont-acc) (set-union (Var x) (arglist a*)))]
    [(if ,a? ,x1 ,x2)
     (freevars+luses (set-union (Callee x1 kenv cont-acc) (Callee x2 kenv cont-acc))
                     (set-union (Atom a?) (Var x1) (Var x2)))]
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

(module reg-pool racket/base
  (provide make preallocate! allocate! deallocate! deallocate-luses!)
  (require racket/match racket/list (only-in srfi/26 cute))

  (struct $reg-pool ([stack #:mutable] [capacity #:mutable]))

  (define (make) ($reg-pool '() 0))

  (define (push! reg-pool reg)
    (set-$reg-pool-stack! reg-pool (cons reg ($reg-pool-stack reg-pool))))

  (define (pop! reg-pool)
    (match-define (cons reg stack*) ($reg-pool-stack reg-pool))
    (set-$reg-pool-stack! reg-pool stack*)
    reg)

  (define (grow! reg-pool target-capacity)
    (for ([reg (in-range ($reg-pool-capacity reg-pool) target-capacity)])
      (push! reg-pool reg))
    (set-$reg-pool-capacity! reg-pool target-capacity))

  (define (preallocate! reg-pool reg)
    (unless (< reg ($reg-pool-capacity reg-pool))
      (grow! reg-pool (+ reg 1)))
    (let ([stack ($reg-pool-stack reg-pool)])
      (if (memq reg stack)
        (set-$reg-pool-stack! reg-pool (filter-not (cute eq? <> reg) stack))
        (error (format "unable to preallocate ~s" reg)))))

  (define (allocate! reg-pool)
    (when (null? ($reg-pool-stack reg-pool))
      (grow! reg-pool (+ ($reg-pool-capacity reg-pool) 1)))
    (pop! reg-pool))

  (define deallocate! push!)

  (define (deallocate-luses! reg-pool env luses)
    (for ([name luses])
      (push! reg-pool (hash-ref env name)))))

(require (prefix-in reg-pool: (submod "." reg-pool)))

;; TODO: Improve targeting (to reduce shuffling at callsites) with some sort of hinting mechanism
(define-pass allocate-registers : RegisterizableCPCPS (ir global-liveness global-dom-forests) -> RegCPCPS ()
  (Program : Program (ir) -> Program ()
    [(prog ([,n* ,blocks*] ...) ,n)
     `(prog ([,n* ,(map (cute CFG <> <>) blocks* n*)] ...) ,n)])

  (CFG : CFG (ir name) -> CFG ()
    [(cfg ([,n1* ,k*] ...) (,n2* ...))
     (define ltab (ltab:make n1* k* n2*))
     (define dom-forest (cfg:dominator-forest ltab (cfg:reverse-postorder ltab n2*) n2*))
     (hash-set! global-dom-forests name dom-forest) ; HACK
     (define liveness (cfg-liveness ir))
     (hash-set! global-liveness name liveness) ; HACK
     (define env (make-hash))
     (define kenv (kenv:inject n1* k*))
     (define cont-acc (make-hash))
     (for ([entry n2*])
       (let loop ([dom-tree (hash-ref dom-forest entry)])
         (match-define (cons label children) dom-tree)
         (Cont (kenv:ref kenv label) label env ltab liveness cont-acc)
         (for ([child children])
           (loop child))))
     (define-values (labels conts) (unzip-hash cont-acc))
     `(cfg ([,labels ,conts] ...) (,n2* ...))])

  (Cont : Cont (ir label env ltab liveness cont-acc) -> Cont ()
    [(cont (,n* ...) ,s* ... ,t)
     (unless (hash-has-key? cont-acc label)
       (define cont-liveness (hash-ref liveness label))
       (define reg-pool (reg-pool:make))
       (define param-regs
         (if (hash-ref (hash-ref ltab label) 'escapes?)
           (for/list ([(param i) (in-indexed n*)])
             (reg-pool:preallocate! reg-pool i)
             (hash-set! env param i)
             i)
           (begin
             (for ([freevar (hash-ref cont-liveness 'freevars)])
               (reg-pool:preallocate! reg-pool (hash-ref env freevar)))
             (for/list ([param n*])
               (define reg (reg-pool:allocate! reg-pool))
               (hash-set! env param reg)
               reg))))
       (define stmts
         (for/list ([stmt s*] [luses (hash-ref cont-liveness 'stmt-last-uses)])
           (Stmt stmt env reg-pool luses)))
       (define transfer (Transfer t env))
       (hash-set! cont-acc label `(cont ([,n* ,param-regs] ...) ,stmts ... ,transfer)))])

  (Stmt : Stmt (ir env reg-pool luses) -> Stmt ()
    [(def ,n ,e)
     (reg-pool:deallocate-luses! reg-pool env luses)
     (define reg (reg-pool:allocate! reg-pool))
     (hash-set! env n reg)
     `(def (,n ,reg) ,(Expr e env))]
    [,e
     (reg-pool:deallocate-luses! reg-pool env luses)
     (Expr e env)])

  (Expr : Expr (ir env) -> Expr ()
    [(primcall0 ,p)             `(primcall0 ,p)]
    [(primcall1 ,p ,a)          `(primcall1 ,p ,(Atom a env))]
    [(primcall2 ,p ,a1 ,a2)     `(primcall2 ,p ,(Atom a1 env) ,(Atom a2 env))]
    [(primcall3 ,p ,a1, a2, a3) `(primcall3 ,p ,(Atom a1 env) ,(Atom a2 env) ,(Atom a3 env))]
    [,a (Atom a env)])

  ;; NOTE: This doesn't need to `deallocate-luses!` since any children start with fresh reg-pools.
  (Transfer : Transfer (ir env) -> Transfer ()
    [(goto ,x ,a* ...) `(goto ,(Var x env) ,(map (cute Atom <> env) a*) ...)]
    [(if ,a? ,x1 ,x2) `(if ,(Atom a? env) ,(Var x1 env) ,(Var x2 env))])

  (Atom : Atom (ir env) -> Atom ()
    [(const ,c) `(const ,c)]
    [,x (Var x env)])

  (Var : Var (ir env) -> Var ()
    [(lex ,n) `(reg ,(hash-ref env n))]
    [(label ,n) `(label ,n)]
    [(proc ,n) `(proc ,n)]))
