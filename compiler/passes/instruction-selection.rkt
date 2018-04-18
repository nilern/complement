#lang racket/base

(provide select-instructions)
(require data/gvector
         nanopass/base

         "../langs.rkt")

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
    [(primcall ,p ,[a*] ...) (guard (eq? p '__ffnNew)) ; HACK
     (gvector-add! stmt-acc (emit-stmt name `(primcall1 __ffnNew ,(car a*))))
     (gvector-add! stmt-acc `(primcall3 __ffnInitType (lex ,name) ,(cadr a*) ,(caddr a*)))]
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
