#lang racket/base

;; Bidirectional direct-call graph of a CFG
(module label-table racket/base
  (provide make)
  (require (only-in srfi/26 cute) nanopass/base
          "../langs.rkt")

 ;;; FIXME: callers and callees should disallow duplicates

  (define (make-entry)
    (make-hash '((escapes? . #f) (callers . ()) (callees . ()))))

  (define ref! (cute hash-ref! <> <> make-entry))

  (define (calls! ltab caller callee)
    (hash-update! (ref! ltab caller) 'callees (cute cons callee <>))
    (hash-update! (ref! ltab callee) 'callers (cute cons caller <>)))

  (define (escapes! ltab label)
    (hash-set! (ref! ltab label) 'escapes? #t))

  (define-pass make : CPCPS (ir) -> * ()
    (Program : Program (ir) -> * ()
      [(prog ([,n* ,blocks*] ...) ,n)
       (define ltabs (make-hash))
       (for ([name n*] [cfg blocks*]) (CFG cfg name ltabs))
       ltabs])

    (CFG : CFG (ir name ltabs) -> * ()
      [(cfg ([,n1* ,k*] ...) (,n2* ...))
       (define ltab (make-hash))
       (for ([label n1*] [cont k*])
         (Cont cont label ltab))
       (for ([entry n2*])
         (escapes! ltab entry))
       (hash-set! ltabs name ltab)])

    (Cont : Cont (ir label ltab) -> * ()
      [(cont (,n* ...) ,s* ... ,t)
       (for ([stmt s*]) (Stmt stmt label ltab))
       (Transfer t label ltab)])

    (Stmt : Stmt (ir label ltab) -> * ()
      [(def ,n ,e) (Expr e label ltab)]
      [,e (Expr e label ltab)])

    (Transfer : Transfer (ir label ltab) -> * ()
      [(goto ,x ,a* ...)
       (Callee x label ltab)
       (for ([atom a*]) (Atom atom label ltab))]
      [(if ,a? ,x1 ,x2)
       (Atom a? label ltab)
       (Callee x1 label ltab)
       (Callee x2 label ltab)]
      [(halt ,a) (Atom a label ltab)])

    (Expr : Expr (ir label ltab) -> * ()
      [(primcall ,p ,a* ...) (for-each (cute Atom <> label ltab) a*)]
      [,a (Atom a label ltab)])

    (Atom : Atom (ir label ltab) -> * ()
      [(const ,c) (void)]
      [,x (Var x label ltab)])

    (Var : Var (ir label ltab) -> * ()
      [(lex ,n) (void)]
      [(label ,n) (escapes! ltab n)]
      [(proc ,n) (void)])

    (Callee : Var (ir label ltab) -> * ()
      [(lex ,n) (void)]
      [(label ,n) (calls! ltab label n)]
      [(proc ,n) (void)])))
