#lang racket/base

(provide census shrink)
(require racket/match
         racket/class
         (only-in racket/list first rest empty? filter-map)
         racket/set
         data/gvector
         data/queue
         (only-in srfi/26 cute)
         (only-in threading ~>)
         nanopass/base

         "../langs.rkt"
         (only-in "../util.rkt" zip-hash unzip-hash gvector-filter!
                                while if-let if-let-values when-let while-let-values)
         (only-in "../nanopass-util.rkt" define/nanopass))

(define-pass for-each-usage : CPS (ir callf continuef escapef) -> * ()
  (definitions
    (define visited (mutable-set)))

  (CFG : CFG (ir fn-name) -> * ()
    [(cfg ([,n* ,k*] ...) ,n)
     (define kenv (zip-hash n* k*))
     (Cont (hash-ref kenv n) fn-name n kenv)
     (escapef fn-name #f (with-output-language (CPS Var) `(label ,n)))])

  (Cont : Cont (ir fn-name label kenv) -> * ()
    [(cont (,n* ...) ,s* ... ,t)
     (unless (set-member? visited label)
       (set-add! visited label)
       (for-each (cute Stmt <> fn-name label kenv) s*)
       (Transfer t fn-name label kenv))])

  (Stmt : Stmt (ir fn-name label kenv) -> * ()
    [(def ,n ,e) (Expr e n fn-name label kenv)]
    [,e (Expr e #f fn-name label kenv)])

  (Expr : Expr (ir name fn-name label kenv) -> * ()
    [(fn ,blocks) (CFG blocks name)]
    [(primcall ,p ,a* ...) (for-each (cute Atom <> fn-name label kenv) a*)]
    [,a (Atom a fn-name label kenv)])

  (Transfer : Transfer (ir fn-name label kenv) -> * ()
    [(continue ,x ,a* ...)
     (Child x fn-name kenv)
     (for-each (cute Atom <> fn-name label kenv) a*)
     (continuef fn-name label x a*)]
    [(if ,a? ,x1 ,x2)
     (Child x1 fn-name kenv) (Child x2 fn-name kenv)
     (Atom a? fn-name label kenv)
     (continuef fn-name label x1 '()) (continuef fn-name label x2 '())]
    [(call ,x1 ,x2 ,a* ...)
     (Child x1 fn-name kenv)
     (Var x2 fn-name label kenv) (for-each (cute Atom <> fn-name label kenv) a*)
     (callf fn-name label x1 x2 a*)]
    [(ffncall ,x1 ,x2 ,a* ...)
     (Var x1 fn-name label kenv) (Var x2 fn-name label kenv)
     (for-each (cute Atom <> fn-name label kenv) a*)]
    [(raise ,a) (Atom a fn-name label kenv)]
    [(halt ,a) (Atom a fn-name label kenv)])

  (Atom : Atom (ir fn-name label kenv) -> * ()
    [,x (Var x fn-name label kenv)]
    [(const ,c) (void)])

  (Var : Var (ir fn-name label kenv) -> * ()
    [(lex ,n) (escapef fn-name label ir)]
    [(label ,n)
     (Cont (hash-ref kenv n) fn-name n kenv)
     (escapef fn-name label ir)])

  (Child : Var (ir fn-name kenv) -> * ()
    [(lex ,n) (void)]
    [(label ,n) (Cont (hash-ref kenv n) fn-name n kenv)])

  (CFG ir #t))

;; For every use of a variable, vtab[var]['uses] += delta.
;; For every direct call of a label, ltab[label]['calls] += delta.
;; For every escaping use of a label, ltab[label]['escapes] += delta.
(define (census! ir delta ltab vtab)
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
        (hash-update! 'calls add-delta)))

  (for-each-usage ir
    (lambda (_ _* callee _** _***)
      (nanopass-case (CPS Var) callee
        [(lex ,n)   (used! vtab n)]
        [(label ,n) (called! ltab n)]))
    (lambda (_ _* callee _**)
      (nanopass-case (CPS Var) callee
        [(lex ,n)   (used! vtab n)]
        [(label ,n) (called! ltab n)]))
    (lambda (_ _* var)
      (nanopass-case (CPS Var) var
        [(lex ,n)   (used! vtab n)]
        [(label ,n) (escapes! ltab n)]))))

;; Build var-table where vtab[var]['uses] is the number of uses of that variable
;; and label-table where ltab[label]['calls] is the number of direct calls of that label
;;                   and ltab[label]['escapes] is the number of escaping uses of that label.
(define (census ir delta)
  (let ([label-table (make-hash)]
        [var-table (make-hash)])
    (census! ir delta label-table var-table)
    (hash 'label-table label-table 'var-table var-table)))

;; HACK:
(define (primops:pure? opcode)
  (case opcode
    [(__boxNew __tupleNew __fnNew __contNew __denvNew __recNew) #t]
    [else #f]))

(define/nanopass (CPS Expr) (pure? ir)
  [(fn ,blocks) #t]
  [(primcall ,p ,a* ...) (primops:pure? p)]
  [,a #t])

(define (unify-atoms atoms)
  (define/nanopass (CPS Atom) (unify2 atom1 atom2)
    [(const ,c1)
     (nanopass-case (CPS Atom) atom2
       [(const ,c2) (guard (equal? c1 c2)) atom1]
       [else #f])]
    [(lex ,n1)
     (nanopass-case (CPS Atom) atom2
       [(lex ,n2) (guard (eq? n1 n2)) atom1]
       [else #f])]
    [(label ,n1)
     (nanopass-case (CPS Atom) atom2
       [(label ,n2) (guard (eq? n1 n2)) atom1]
       [else #f])])
  (foldl unify2 (first atoms) (rest atoms)))

(struct $fn (labels entry))
(struct $label ((cont #:mutable) (fn #:mutable)))

(define symbol-table%
  (class object%
    ;;; Fields and initialization

    (define fns (make-hash))
    (define labels (make-hash))

    (super-new)

    ;;; Fn methods

    (define (fn-ref fn-name) (hash-ref fns fn-name))

    (define (fn-labels fn-name) ($fn-labels (fn-ref fn-name)))

    (define (add-fn-label! fn-name label)
      (set-add! ($fn-labels (fn-ref fn-name)) label))

    (define (remove-fn-label! fn-name label)
      (set-remove! ($fn-labels (fn-ref fn-name)) label))

    ;;; Label methods

    (define (label-ref label) (hash-ref labels label))

    (define/public (cont-ref label) ($label-cont (label-ref label)))

    (define/public (cont-forget! fn-name label)
      (remove-fn-label! fn-name label)
      (hash-remove! labels label))

    (define/public (set-cont! label cont) (set-$label-cont! (label-ref label) cont))

    (define/public (label-fn label) ($label-fn (label-ref label)))

    ;;; High-level API

    (define/public (add-fn! fn-name fn-labels conts entry)
      (hash-set! fns fn-name ($fn (list->mutable-set fn-labels) entry))
      (for ([label fn-labels] [cont conts])
        (hash-set! labels label ($label cont fn-name))))

    (define/public (move-label! label src dest)
      (remove-fn-label! src label)
      (add-fn-label! dest label)
      (set-$label-fn! (label-ref label) dest))

    (define/public (build-cfg fn-name)
      (with-output-language (CPS CFG)
        (match-define ($fn label-set entry) (fn-ref fn-name))
        (define-values (labels conts)
          (for/fold ([labels '()] [conts '()])
                    ([label label-set])
            (values (cons label labels) (cons (cont-ref label) conts))))
        `(cfg ([,labels ,conts] ...) ,entry)))))

(define statistics%
  (class object%
    ;;; Fields and initialization

    (define escapes (make-hash))
    (define applications (make-hash))

    (super-new)

    ;;; Escape methods

    (define (escapes-of name)
      (hash-ref! escapes name make-gvector))

    (define (escape-count name)
      (gvector-count (escapes-of name)))

    (define/public (add-escape! name label)
      (gvector-add! (hash-ref! escapes name make-gvector) label))

    (define/public (remove-escape! name label)
      (let/ec return
        (define name-escapes (hash-ref! escapes name make-gvector))
        (for ([(l i) (in-indexed name-escapes)])
          (when (eq? l label)
            (gvector-remove! name-escapes i)
            (return (void))))))

    ;;; Application methods

    (define/public (applications-of name)
      (hash-ref! applications name make-gvector))

    (define (application-count name)
      (gvector-count (applications-of name)))

    (define/public (add-application! name label)
      (gvector-add! (hash-ref! applications name make-gvector) label))

    (define/public (remove-application! name label)
      (let/ec return
        (define name-applications (hash-ref! applications name make-gvector))
        (for ([(l i) (in-indexed name-applications)])
          (when (eq? l label)
            (gvector-remove! name-applications i)
            (return (void))))))

    ;;; High-level API

    (define/public (total-usages name)
      (+ (escape-count name) (application-count name)))

    (define/public (used? name)
      (not (unused? name)))

    (define/public (unused? name)
      (zero? (total-usages name)))

    (define/public (first-order? label)
      (zero? (escape-count label)))

    (define/public (transfer-usages! old new)
      (for ([label (escapes-of old)]) (add-escape! new label))
      (hash-remove! escapes old)
      (for ([label (applications-of old)]) (add-application! new label))
      (hash-remove! applications old))

    (define/public (cont-forget! label)
      (hash-remove! escapes label)
      (for ([(_ escapes*) escapes]) ; OPTIMIZE
        (gvector-filter! (cute eq? <> label) escapes*))
      (hash-remove! applications label)
      (for ([(_ applications*) applications]) ; OPTIMIZE
        (gvector-filter! (cute eq? <> label) applications*)))))

(struct $non-static-eval exn:fail ())

;; FIXME: Since return points are processed before callee bodies, their parameters do not get
;;        propagated and returns cannot be beta-contracted (without residualizing param `def`:s).
;;
;; * Copy and constant propagation including Cont parameters.
;; * Constant folding.
;; * Integration of first-order functions into their only direct caller.
;;     => Some inlining
;;     => Some contification
;; * Merging linear sequences of first-order continuations.
;;     => Longer basic blocks
;; * Elimination of unused (both 'dead' and 'unreachable') code.
(define-pass shrink : CPS (ir) -> CPS ()
  (definitions
    (define current-fn (make-parameter #t))
    (define current-label (make-parameter #f))

    (define transient-program%
      (class object%
        (init cfg)

        ;;;; Fields and minimal initialization

        (define orig-worklists (make-hash))

        (define stats (new statistics%))

        (define symtab (new symbol-table%))

        (define substitution (make-hash))
        (define abstract-heap (make-hash))

        (super-new)

        ;;;; Worklist methods

        (define (orig-worklist-prepend! fn-name callee)
          (enqueue-front! (hash-ref! orig-worklists fn-name make-queue) callee))

        (define (worklist-pop! worklist)
          (if (non-empty-queue? worklist)
            (let ([label (dequeue! worklist)])
              (values label (send symtab cont-ref label)))
            (values #f #f)))

        (define/public (pop-orig-cont! fn-name)
          (worklist-pop! (hash-ref orig-worklists fn-name)))

        ;;;; Statistics methods

        (define/public (total-usages name) (send stats total-usages name))

        (define/public (used? name) (send stats used? name))

        (define/public (unused? name) (send stats unused? name))

        (define/public (add-escape! name label) (send stats add-escape! name label))

        (define/public (remove-escape! name label) (send stats remove-escape! name label))

        (define/public (add-application! name label) (send stats add-application! name label))

        (define/public (remove-application! name label) (send stats remove-application! name label))

        ;;;; Label-continuation-fn mapping methods

        (define/public (cont-ref label) (send symtab cont-ref label))

        (define/public (set-cont! label cont) (send symtab set-cont! label cont))

        (define/public (cont-forget! fn-name label)
          (send symtab cont-forget! fn-name label)
          (send stats cont-forget! label))

        (define/public (enter-function! fn-name labels fn-conts entry)
          (send symtab add-fn! fn-name labels fn-conts entry))

        (define (mergeable-into? caller fn-name)
          (and (send stats first-order? fn-name)
               (for/and ([usage-label (send stats applications-of fn-name)])
                 (eq? (send symtab label-fn usage-label) caller))))

        (define/public (fn-merge-into! fn-name)
          (with-output-language (CPS Cont)
            (define fn-name-worklist (hash-ref orig-worklists fn-name))
            (define merged-names
              (for/list ([(name expr) abstract-heap]
                         #:when (and (not (vector? expr)) ; HACK
                                     (mergeable-into? fn-name name)))
                (nanopass-case (CPS Expr) expr
                  [(fn (cfg ([,n* ,k*] ...) ,n))
                   (enter-function! name n* k* n) ; HACK?
                   (define name-worklist (hash-ref orig-worklists name))
                   (while (non-empty-queue? name-worklist)
                     (enqueue! fn-name-worklist (dequeue! name-worklist)))
                   (send stats remove-escape! n #f)
                   (send stats transfer-usages! name n)
                   (for ([label n*] [cont k*])
                     (send symtab move-label! label name fn-name))
                   (for ([usage-label (send stats applications-of n)])
                     (nanopass-case (CPS Cont) (send symtab cont-ref usage-label)
                       [(cont (,n* ...) ,s* ... (call ,x1 ,x2 ,a* ...))
                        (send symtab set-cont! usage-label
                          `(cont (,n* ...) ,s* ... (continue (label ,n) ,x2 ,a* ...)))]
                       [else (error "fn-merge-into!: callsite not a call")]))
                   name]
                  [else (error "fn-merge-into!: tried to inline non-function")])))
            (for-each (cute hash-remove! abstract-heap <>) merged-names)
            (not (empty? merged-names))))

        (define/public (build-cfg name) (send symtab build-cfg name))

        ;;;; Environment management

        (define/public (propagated fn-name name default)
          (define atom (hash-ref substitution name default))
          (nanopass-case (CPS Atom) atom
            [(label ,n) (guard (not (eq? (send symtab label-fn n) fn-name)))
             default]
            [else atom]))

        (define (label-arglists label)
          (for/list ([usage-label (send stats applications-of label)])
            (nanopass-case (CPS Cont) (send symtab cont-ref usage-label)
              [(cont (,n* ...) ,s* ... (continue ,x1 ,a* ...)) a*]
              [(cont (,n* ...) ,s* ... ,t)
               (error "label-arglists: label callsite is not a continue:" label t)])))

        (define/public (propagate-params! label params)
          (unless (or (not (send stats first-order? label)) (empty? params))
            (define (propagate-param! name . atoms)
              (unless (empty? atoms)
                (when-let [atom (unify-atoms atoms)]
                  (hash-set! substitution name atom))))
            (apply for-each propagate-param! params (label-arglists label))))

        (define/public (compact-params! label params)
          (with-output-language (CPS Cont)
            (define keepers (map (lambda (param) (send stats used? param)) params))
            (define ((compact-arg! usage-label) atom keep)
              (if keep
                atom
                (begin
                  (nanopass-case (CPS Atom) atom
                    [(lex ,n) (send stats remove-escape! n usage-label)]
                    [(label ,n) (send stats remove-escape! n usage-label)]
                    [(const ,c) (void)])
                  #f)))

            (if (and (send stats first-order? label) (not (empty? params)))
              (begin
                (for ([usage-label (send stats applications-of label)])
                  (nanopass-case (CPS Cont) (send symtab cont-ref usage-label)
                    [(cont (,n* ...) ,s* ... (continue ,x1 ,a* ...))
                     (send symtab set-cont! usage-label
                       `(cont (,n* ...)
                          ,s* ...
                          (continue ,x1 ,(filter-map (compact-arg! usage-label) a* keepers) ...)))]
                    [else (error "compact-params: unreachable code reached")]))
                (filter-map (lambda (param keep) (and keep param)) params keepers)) ; OPTIMIZE
              params)))

        (define/public (load name)
          (if (hash-has-key? abstract-heap name)
            (values #t (hash-ref abstract-heap name))
            (values #f #f)))

        (define/public (allocate! name expr)
          (nanopass-case (CPS Expr) expr
            [(fn ,blocks) (hash-set! abstract-heap name expr)]
            [(primcall ,p ,a* ...) (guard (eq? p '__tupleNew))
             (hash-set! abstract-heap name (list->vector a*))]
            [(primcall ,p ,a* ...) (void)] ; TODO
            [,a (hash-set! substitution name expr)]))

        (define/public (deallocate! name)
          (hash-remove! abstract-heap name))

        (define/public (integrated? name)
          (not (hash-has-key? abstract-heap name)))

        ;;;; Completion of field initialization

        (for-each-usage cfg
          (lambda (caller label callee cont args)
            (nanopass-case (CPS Var) callee
              [(lex ,n) (send stats add-application! n label)]
              [(label ,n) (send stats add-application! n label)]))
          (lambda (fn-name label callee args)
            (nanopass-case (CPS Var) callee
              [(lex ,n) (send stats add-application! n label)]
              [(label ,n)
               (send stats add-application! n label)
               (orig-worklist-prepend! fn-name n)]))
          (lambda (fn-name label var)
            (nanopass-case (CPS Var) var
              [(lex ,n) (send stats add-escape! n label)]
              [(label ,n)
               (send stats add-escape! n label)
               (orig-worklist-prepend! fn-name n)])))))

    (define transient-program (make-object transient-program% ir))

    ;;;;

    (define (fold-stmt name expr)
      (define (unused? name)
        (or (not name) (send transient-program unused? name)))

      (let retry ([expr expr] [first-try #t])
        (define pure (pure? expr))
        (if (and (unused? name) pure)
          (begin
            (EliminateExpr expr)
            #f)
          (if first-try
            (retry (FoldExpr expr) #f)
            (begin
              (when pure
                (send transient-program allocate! name expr))
              (if name
                (with-output-language (CPS Stmt) `(def ,name ,expr))
                expr))))))

    (define (constant-fold op args)
      (define/nanopass (CPS Atom) (eval-atom ir)
        [(const ,c) c]
        [(lex ,n)
         (if-let-values [(_ v) (send transient-program load n)]
           v
           (raise ($non-static-eval "not in abstract heap" (current-continuation-marks))))]
        [(label ,n) (raise ($non-static-eval "label" (current-continuation-marks)))])

      (with-output-language (CPS Expr)
        (with-handlers ([$non-static-eval? (lambda (_) #f)])
          (match* (op (map eval-atom args))
            [('__tupleLength `(,(? vector? tup))) `(const ,(vector-length tup))]
            [('__tupleGet `(,(? vector? tup) ,(? fixnum? i)))
             (if (< i (vector-length tup))
               (vector-ref tup i)
               #f)]
            [('__iEq `(,(? fixnum? a) ,(? fixnum? b))) `(const ,(= a b))]
            ;; TODO: more operations...
            [(_ _) #f]))))

    ;;;;

    (define (eliminate-label-ref! application label usage-label)
      (if application
        (send transient-program remove-application! label usage-label)
        (send transient-program remove-escape! label usage-label))
      (when (send transient-program unused? label)
        (EliminateCont (send transient-program cont-ref label) label))))

  ;;;;

  ;; Process one function; driver loops and function merging.
  (CFG : CFG (ir fn-name) -> CFG ()
    [(cfg ([,n* ,k*] ...) ,n)
     (parameterize ([current-fn fn-name])
       (send transient-program enter-function! fn-name n* k* n) ; HACK?

       (define folded-worklist (make-queue))

       ;; FoldCont in reverse postorder (since we only have DAG:s, topologically sorted order):
       (let loop ()
         (while-let-values [(label cont) (send transient-program pop-orig-cont! fn-name)]
           (when-let [folded-cont (FoldCont cont label)]
             (enqueue-front! folded-worklist label)
             (send transient-program set-cont! label folded-cont)))
         ;; When at the end, try to expand CFG by merging in other functions that are only called
         ;; from here and never escape:
         (when (send transient-program fn-merge-into! fn-name)
           (loop)))

       ;; CompactCont in (reversed reverse) postorder:
       (while (non-empty-queue? folded-worklist)
         (let* ([label (dequeue! folded-worklist)]
                [cont (send transient-program cont-ref label)])
           (when-let [compacted-cont (CompactCont cont label)]
             (send transient-program set-cont! label compacted-cont))))

       (send transient-program build-cfg fn-name))])

  ;;;;

  ;;; Elimination of dead/unreachable code, collecting information about variables and using said
  ;;; information for constant/copy propagation and constant folding.

  (FoldCont : Cont (ir label) -> Cont ()
    [(cont (,n* ...) ,s* ... ,t)
     (parameterize ([current-label label])
       (and (send transient-program used? (current-label))
            (begin
              (send transient-program propagate-params! (current-label) n*)
              (let* ([stmts (filter-map FoldStmt s*)]
                     [transfer (FoldTransfer t)])
                `(cont (,n* ...) ,stmts ... ,transfer)))))])

  (FoldStmt : Stmt (ir) -> Stmt ()
    [(def ,n ,e) (fold-stmt n e)]
    [,e (fold-stmt #f e)])

  (FoldExpr : Expr (ir) -> Expr ()
    [(fn ,blocks) ir]
    [(primcall ,p ,a* ...)
     (define args (map FoldAtom a*))
     (if-let [folded-expr (constant-fold p args)]
       (begin
         (DiscoverExpr folded-expr)
         (for-each EliminateAtom args)
         folded-expr)
       `(primcall ,p ,args ...))]
    [,a (FoldAtom a)])

  (FoldTransfer : Transfer (ir) -> Transfer ()
    [(continue ,x ,a* ...) `(continue ,(FoldCallee x) ,(map FoldAtom a*) ...)]
    [(if ,a? ,x1 ,x2)
     (define condition (FoldAtom a?))
     (nanopass-case (CPS Atom) condition
       [(const ,c) (guard (eqv? c #t))
        (EliminateVar x2)
        `(continue ,(FoldCallee x1))]
       [(const ,c) (guard (eqv? c #f))
        (EliminateVar x1)
        `(continue ,(FoldCallee x2))]
       [else `(if ,condition ,(FoldCallee x1) ,(FoldCallee x2))])]
    [(call ,x1 ,x2 ,a* ...) `(call ,(FoldCallee x1) ,(FoldVar x2) ,(map FoldAtom a*) ...)]
    [(ffncall ,x1 ,x2 ,a* ...) `(ffncall ,(FoldVar x1) ,(FoldVar x2) ,(map FoldAtom a*) ...)]
    [(raise ,a) `(raise ,(FoldAtom a))]
    [(halt ,a) `(halt ,(FoldAtom a))])

  (FoldAtom : Atom (ir) -> Atom ()
    [,x (FoldVar x)]
    [(const ,c) ir])

  (FoldVar : Var (ir) -> Atom ()
    [(lex ,n)
     (define ir* (send transient-program propagated (current-fn) n ir))
     (if (eq? ir ir*)
       ir*
       (begin
         (DiscoverAtom ir*)
         (EliminateVar ir)
         ir*))]
    [(label ,n) ir])

  (FoldCallee : Var (ir) -> Var ()
    [(lex ,n)
     (define ir* (send transient-program propagated (current-fn) n ir))
     (if (eq? ir ir*)
       ir*
       (begin
         (DiscoverCallee ir*)
         (EliminateCallee ir)
         ir*))]
    [(label ,n) ir])

  ;;;;

  ;;; More elimination of dead/unreachable code, beta-contraction of continuations (merging linear
  ;;; sequences of basic blocks).

  ;; TODO: CompactTransfer for basic block merging
  (CompactCont : Cont (ir label) -> Cont ()
    [(cont (,n* ...) ,s* ... ,t)
     (parameterize ([current-label label])
       (and (send transient-program used? (current-label))
            (let*-values ([(stmts* transfer) (CompactTransfer t)])
              (let* ([stmts (foldr (lambda (stmt stmts*)
                                     (if-let [stmt* (CompactStmt stmt)]
                                       (cons stmt* stmts*)
                                       stmts*))
                                   stmts* s*)]
                     [params (send transient-program compact-params! (current-label) n*)])
                `(cont (,params ...) ,stmts ... ,transfer)))))])

  (CompactStmt : Stmt (ir) -> Stmt ()
    [(def ,n (fn ,blocks)) (guard (send transient-program integrated? n)) #f]
    [(def ,n ,e)
     (if (and (send transient-program unused? n) (pure? e))
       (begin ; has become useless after StmtForward and needs to be eliminated now
         (EliminateExpr e)
         #f)
       (begin ; remove from abstract heap so that we don't try to inline recursive fns:
         (send transient-program deallocate! n)
         `(def ,n ,(CompactExpr e n))))]
    [,e ir])

  (CompactExpr : Expr (ir name) -> Expr ()
    [(fn ,blocks) `(fn ,(CFG blocks name))]
    [else ir])

  (CompactTransfer : Transfer (ir) -> Stmt (transfer)
    [(continue (label ,n)) (guard (= (send transient-program total-usages n) 1))
     (nanopass-case (CPS Cont) (send transient-program cont-ref n)
       [(cont () ,s* ... ,t)
        (send transient-program cont-forget! (current-fn) n)
        (values s* t)]
       [else (error "unreachable code reached in CompactTransfer")])]
    [else (values '() ir)])

  ;;;;

  ;;; Elimination of labels and conts works similarly to a (naive) refcounting GC. Since CFG:s are
  ;;; DAG:s, this will eliminate all the code which becomes unused when the last reference to a
  ;;; continuation (i.e. some `(label ,n) Var) is eliminated.

  (EliminateCFG : CFG (ir) -> * ()
    [(cfg ([,n* ,k*] ...) ,n) (eliminate-label-ref! #f n (current-label))])

  (EliminateCont : Cont (ir label) -> * ()
    [(cont (,n* ...) ,s* ... ,t)
     (parameterize ([current-label label])
       (for-each EliminateStmt s*) (EliminateTransfer t))])

  (EliminateStmt : Stmt (ir) -> * ()
    [(def ,n ,e) (EliminateExpr e)]
    [,e (EliminateExpr e)])

  (EliminateExpr : Expr (ir) -> * ()
    [(fn ,blocks) (EliminateCFG blocks)]
    [(primcall ,p ,a* ...) (for-each EliminateAtom a*)]
    [,a (EliminateAtom a)])

  (EliminateTransfer : Transfer (ir) -> * ()
    [(continue ,x ,a* ...) (EliminateVar x) (for-each EliminateAtom a*)]
    [(if ,a? ,x1 ,x2) (EliminateAtom a?) (EliminateVar x1) (EliminateVar x2)]
    [(call ,x1 ,x2 ,a* ...) (EliminateVar x1) (EliminateVar x2) (for-each EliminateAtom a*)]
    [(ffncall ,x1 ,x2 ,a* ...) (EliminateVar x1) (EliminateVar x2) (for-each EliminateAtom a*)]
    [(raise ,a) (EliminateAtom a)]
    [(halt ,a) (EliminateAtom a)])

  (EliminateAtom : Atom (ir) -> * ()
    [,x (EliminateVar x)]
    [(const ,c) (void)])

  (EliminateVar : Var (ir) -> * ()
    [(lex ,n) (send transient-program remove-escape! n (current-label))]
    [(label ,n) (eliminate-label-ref! #f n (current-label))])

  (EliminateCallee : Var (ir) -> * ()
    [(lex ,n) (send transient-program remove-application! n (current-label))]
    [(label ,n) (eliminate-label-ref! #t n (current-label))])

  ;;;;

  (DiscoverExpr : Expr (ir) -> * ()
    [(fn ,blocks) (error "unimplemented")]
    [(primcall ,p ,a* ...) (for-each DiscoverAtom a*)]
    [,a (DiscoverAtom a)])

  (DiscoverAtom : Atom (ir) -> * ()
    [,x (DiscoverVar x)]
    [(const ,c) (void)])

  (DiscoverVar : Var (ir) -> * ()
    [(lex ,n) (send transient-program add-escape! n (current-label))]
    [(label ,n) (send transient-program add-escape! n (current-label))])

  (DiscoverCallee : Var (ir) -> * ()
    [(lex ,n) (send transient-program add-application! n (current-label))]
    [(label ,n) (send transient-program add-application! n (current-label))])

  ;;;;

  (CFG ir #t))
