#lang racket/base

(provide name? const? primop?
         Cst LexCst Ast
         CPS CPCPS RegisterizableCPCPS RegCPCPS InstrCPCPS InstrCPCPS-Atom=? InstrCPCPS-Atom-hash
         Asm ResolvedAsm ConstPoolAsm)
(require nanopass/base)

;;; TODO: Make primcalls "correct by construction"
;;; TODO: restrict (call e e* ...)

(define (name? name)
  (and (symbol? name)
       (let ([name-str (symbol->string name)])
         (or (< (string-length name-str) 2)
             (not (equal? (substring name-str 0 2) "__"))))))

(define (const? v)
  (or (number? v) (char? v) (boolean? v) (string? v) (symbol? v)))

(define (primop? name)
  (and (symbol? name)
       (let ([name-str (symbol->string name)])
         (and (>= (string-length name-str) 2)
              (equal? (substring name-str 0 2) "__")))))

(define-language Cst
  (terminals
    (name (n))
    (const (c))
    (primop (p)))

  (Expr (e)
    (block s* ... e)
    (fn fc* ...)
    (call e e* ...)
    (primcall p e* ...)
    (ffncall e1 e2)
    (macro n e* ...)
    x
    (const c))

  (Stmt (s)
    (def x e)
    e)

  (Case (fc)
    (case (x* ...) e? e)
    (case x e? e))

  (Var (x)
    (lex n)
    (dyn n)))

(define-language LexCst
  (extends Cst)

  (Expr (e)
    (- (fn fc* ...))
    (+ (fn n fc ...))
    (- (ffncall e1 e2))
    (+ (ffncall e1 e2 e3))
    (- x)
    (+ n))

  (Stmt (s)
    (- (def x e))
    (+ (def n e)))

  (Case (fc)
    (- (case (x* ...) e? e))
    (- (case x e? e))
    (+ (case (n* ...) e? e))
    (+ (case n e? e)))

  (Var (x)
    (- (lex n))
    (- (dyn n))))

(define-language Ast
  (extends LexCst)

  (Expr (e)
    (- (fn n fc ...))
    (+ (fn (n1* ...) ([n2* fc*] ...) e))
    (+ (if e? e1 e2))
    (+ (continue n e)))

  (Case (fc)
    (- (case (n* ...) e? e))
    (- (case n e? e))
    (+ (case (n* ...) e))))

(define-language CPS
  (terminals
    (name (n))
    (const (c))
    (primop (p)))

  (CFG (blocks)
    (cfg ([n* k*] ...) n))

  (Cont (k)
    (cont (n* ...) s* ... t))

  (Stmt (s)
    (def n e)
    e)

  (Transfer (t)
    (continue x a* ...)
    (if a? x1 x2)
    (call x1 x2 a* ...)
    (ffncall x1 x2 a* ...) ; TODO: x1 -> n, x2 -> x
    (raise a)
    (halt a))

  (Expr (e)
    (fn blocks)
    (primcall p a* ...)
    a)

  (Atom (a)
    x
    (const c))

  (Var (x)
    (lex n)
    (label n)))

(define-language CPCPS
  (extends CPS)
  (entry Program)

  (Program ()
    (+ (prog ([n* blocks*] ...) n)))

  (CFG (blocks)
    (- (cfg ([n* k*] ...) n))
    (+ (cfg ([n1* k*] ...) (n2* ...))))

  (Transfer (t)
    (- (continue x a* ...))
    (- (call x1 x2 a* ...))
    (+ (goto x a* ...))
    (- (ffncall x1 x2 a* ...))
    (+ (ffncall x a* ...))) ; TODO: x -> n

  (Expr (e)
    (- (fn blocks)))

  (Var (x)
    (+ (proc n))))

(define-language RegisterizableCPCPS
  (extends CPCPS)

  (Expr (e)
    (- (primcall p a* ...))
    (+ (primcall0 p))
    (+ (primcall1 p a))
    (+ (primcall2 p a1 a2))
    (+ (primcall3 p a1 a2 a3))))

(define index? fixnum?)

(define-language RegCPCPS
  (extends RegisterizableCPCPS)

  (terminals
    (+ (index (i))))

  (Cont (k)
    (- (cont (n* ...) s* ... t))
    (+ (cont ([n* i*] ...) s* ... t)))

  (Stmt (s)
    (- (def n e))
    (+ (def (n i) e)))

  (Var (x)
    (- (lex n))
    (+ (reg i))))

(define-language InstrCPCPS
  (extends RegCPCPS)

  (Program ()
    (- (prog ([n* blocks*] ...) n))
    (+ (prog ([n* blocks*] ...) i n)))

  (Transfer (t)
    (- (goto x a* ...))
    (+ (goto x))
    (- (ffncall x a* ...))
    (+ (ffncall x)))) ; TODO. x -> n

(define (InstrCPCPS-Atom-deconstruct atom)
  (nanopass-case (InstrCPCPS Atom) atom
    [(const ,c) (values 0 c)]
    [(reg ,i)   (values 1 i)]
    [(label ,n) (values 2 n)]
    [(proc ,n)  (values 3 n)]))

(define (InstrCPCPS-Atom=? atom1 atom2)
  (define-values (tag1 repr1) (InstrCPCPS-Atom-deconstruct atom1))
  (define-values (tag2 repr2) (InstrCPCPS-Atom-deconstruct atom2))
  (and (equal? tag1 tag2) (equal? repr1 repr2)))

(define (InstrCPCPS-Atom-hash atom)
  (define-values (tag repr) (InstrCPCPS-Atom-deconstruct atom))
  (+ tag (equal-hash-code repr)))

(define-language Asm
  (extends InstrCPCPS)

  (Cont (k)
    (- (cont ([n* i*] ...) s* ... t))
    (+ (cont ([n* i*] ...) s* ... (maybe t))))

  (Transfer (t)
    (- (goto x))
    (+ (br n))
    (+ (jmp x))
    (- (if a? x1 x2))
    (+ (brf a? n))))

(define-language ResolvedAsm
  (extends Asm)

  (Program ()
    (- (prog ([n* blocks*] ...) i n))
    (+ (prog ([n* blocks*] ...) i1 (n i2))))

  (CFG (blocks)
    (- (cfg ([n1* k*] ...) (n2* ...)))
    (+ (cfg ([n1* k*] ...) ([n2* i*] ...))))

  (Transfer (t)
    (- (br n))
    (+ (br n i))
    (- (brf a? n))
    (+ (brf a? n i)))

  (Var (x)
    (- (label n))
    (+ (label n i))
    (- (proc n))
    (+ (proc n i))))

(define-language ConstPoolAsm
  (extends ResolvedAsm)

  (Program ()
    (- (prog ([n* blocks*] ...) i1 (n i2)))
    (+ (prog ([n* f*] ...) i1 (n i2))))

  (CFG (blocks)
    (- (cfg ([n1* k*] ...) ([n2* i*] ...))))

  (Fn (f)
    (+ (fn (c* ...) ([n1* k*] ...) ([n2* i*] ...))))

  (Atom (a)
    (- (const c))
    (+ (const i))))
