#lang racket/base

(provide allocate-registers)
(require racket/match racket/list racket/set (only-in srfi/26 cute)
         nanopass/base
         "langs.rkt" (only-in "cpcps-passes.rkt" cfg-rpo)
         (prefix-in ltab: (submod "cpcps-passes.rkt" label-table))
         (prefix-in kenv: (submod "util.rkt" cont-env))
         (only-in "util.rkt" unzip-hash))

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

;; OPTIMIZE: use worklist algorithm or at least make sure that DAG:s only take the minimum 2 passes
(define (cfg-dominator-forest label-table rpo entries)
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

;; TODO: Improve targeting (to reduce shuffling at callsites) with some sort of hinting mechanism
(define-pass allocate-registers : RegisterizableCPCPS (ir) -> * ()
  (definitions
    (struct $reg-pool ([stack #:mutable] [capacity #:mutable]))
  
    (define (make-reg-pool)
      ($reg-pool '() 0))

    (define (pool-push! reg-pool reg)
      (set-$reg-pool-stack! reg-pool (cons reg ($reg-pool-stack reg-pool))))

    (define (pool-pop! reg-pool)
      (match-define (cons reg stack*) ($reg-pool-stack reg-pool))
      (set-$reg-pool-stack! reg-pool stack*)
      reg)

    (define (grow-pool! reg-pool target-capacity)
      (for ([reg (in-range ($reg-pool-capacity reg-pool) target-capacity)])
        (pool-push! reg-pool reg))
      (set-$reg-pool-capacity! reg-pool target-capacity))

    (define (preallocate! reg-pool reg)
      (unless (< reg ($reg-pool-capacity reg-pool))
        (grow-pool! reg-pool (+ reg 1)))
      (let ([stack ($reg-pool-stack reg-pool)])
        (if (memq reg stack)
          (set-$reg-pool-stack! reg-pool (filter-not (cute eq? <> reg) stack))
          (error (format "unable to preallocate ~s" reg)))))

    (define (allocate! reg-pool)
      (when (null? ($reg-pool-stack reg-pool))
        (grow-pool! reg-pool (+ ($reg-pool-capacity reg-pool) 1)))
      (pool-pop! reg-pool))

    (define (deallocate! reg-pool env names)
      (for ([name names])
        (pool-push! reg-pool (hash-ref env name)))))

  (Program : Program (ir) -> * ()
    [(prog ([,n* ,f*] ...) ,blocks)
     (define env (make-hash))
     (CFG blocks env)
     (for ([f f*]) (Fn f env))
     env])

  (Fn : Fn (ir env) -> * ()
    [(fn ,blocks) (CFG blocks env)])

  (CFG : CFG (ir env) -> * ()
    [(cfg ([,n1* ,k*] ...) (,n2* ...))
     (define ltab (ltab:make n1* k* n2*))
     (define dom-forest (cfg-dominator-forest ltab (cfg-rpo ltab n2*) n2*))
     (define liveness (cfg-liveness ir))
     (define kenv (kenv:inject n1* k*))
     (define cont-acc (make-hash))
     (for ([entry n2*])
       (let loop ([dom-tree (hash-ref dom-forest entry)])
         (match-define (cons label children) dom-tree)
         (Cont (kenv:ref kenv label) label env ltab liveness cont-acc)
         (for ([child children])
           (loop child))))])

  (Cont : Cont (ir label env ltab liveness cont-acc) -> * ()
    [(cont (,n* ...) ,s* ... ,t)
     (unless (hash-has-key? cont-acc label)
       (define cont-liveness (hash-ref liveness label))
       (define reg-pool (make-reg-pool))
       (for ([freevar (hash-ref cont-liveness 'freevars)])
         (preallocate! reg-pool (hash-ref env freevar)))
       (when (hash-ref (hash-ref ltab label) 'escapes?)
         (for ([(param i) (in-indexed n*)])
           (preallocate! reg-pool i)
           (hash-set! env param i)))
       (for ([stmt s*] [luses (hash-ref cont-liveness 'stmt-last-uses)])
         (Stmt stmt env reg-pool luses)))])

  (Stmt : Stmt (ir env reg-pool luses) -> * ()
    [(def ,n ,e)
     (deallocate! reg-pool env luses)
     (hash-set! env n (allocate! reg-pool))]
    [,e (deallocate! reg-pool env luses)]))
