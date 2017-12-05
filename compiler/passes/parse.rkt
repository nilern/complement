#lang racket/base

(provide parse)
(require racket/match
         racket/list
         (only-in racket/function negate)
         parser-tools/lex
         (prefix-in : parser-tools/lex-sre)
         parser-tools/yacc
         nanopass/base

         "../langs.rkt")

;;;; # Lexer

(define-tokens payload-toks
  (LEX DYN OP1 OP2 OP3 OP4 OP5 OP6 OP7 PRIMOP
   STRING
   INT CHAR))
(define-empty-tokens empty-toks
  (EOF
   LPAREN RPAREN LBRACKET RBRACKET LBRACE RBRACE
   COMMA SEMICOLON
   = => \|))

(define-lex-abbrevs
  (delimiter (union #\( #\) #\[ #\] #\{ #\} #\" #\' #\`))
  (separator (union #\, #\;))
  (terminator (union delimiter separator whitespace))
  (constituents (complement (:: any-string terminator any-string)))
  (lower-letter (:/ "a" "z"))
  (upper-letter (:/ #\A #\Z))
  (digit (:/ #\0 #\9)))

(define lex
  (lexer-src-pos
    [whitespace (return-without-pos (lex input-port))] ; skip
    [(:: "#" (:* (complement (:: any-string "\n" any-string))) "\n")
     (return-without-pos (lex input-port))] ; skip line comment
    [(eof) 'EOF]
    ["(" 'LPAREN]
    [")" 'RPAREN]
    ["[" 'LBRACKET]
    ["]" 'RBRACKET]
    ["{" 'LBRACE]
    ["}" 'RBRACE]
    ["," 'COMMA]
    [";" 'SEMICOLON]
    ["=>" '=>]
    ["=" '=]
    ["|" '\|]
    [(:: #\| constituents)
     (token-OP1 (string->symbol lexeme))]
    [(:: #\^ constituents)
     (token-OP2 (string->symbol lexeme))]
    [(:: #\& constituents)
     (token-OP3 (string->symbol lexeme))]
    [(:: (union #\= #\!) constituents)
     (token-OP4 (string->symbol lexeme))]
    [(:: (union #\= #\!) constituents)
     (token-OP4 (string->symbol lexeme))]
    [(:: (union #\< #\>) constituents)
     (token-OP5 (string->symbol lexeme))]
    [(:: (union #\+ #\-) constituents)
     (token-OP6 (string->symbol lexeme))]
    [(:: (union #\* #\/ #\%) constituents)
     (token-OP7 (string->symbol lexeme))]
    [(:: "\"" (:* (complement (:: any-string "\"" any-string))) "\"")
     (token-STRING (substring lexeme 1 (- (string-length lexeme) 1)))]
    [(:: "'" (complement (:: any-string "'" any-string)) "'")
     (token-CHAR (string-ref lexeme 1))]
    [(:: "__" (:+ (:or lower-letter upper-letter)))
     (token-PRIMOP (string->symbol lexeme))]
    [(:: "$" (:+ (:or lower-letter upper-letter)))
     (token-DYN (string->symbol (substring lexeme 1)))]
    [(:+ (:or lower-letter upper-letter))
     (token-LEX (string->symbol lexeme))]
    [(:+ digit) (token-INT (string->number lexeme))]))

;;;; # Parser

;;; First, some hacks around LR limitations:

(struct $fn-header (params cond body-start))
(struct $def (var expr))

(define (app->var-list app)
  (define (unwrap-var-expr expr)
    (nanopass-case (Cst Expr) expr
      [,x x]))
  (map unwrap-var-expr app))

(define (parse-decls decls)
  (if ($fn-header? (car decls))
    (let loop ([decls decls]
               [paramss '()]
               [conds '()]
               [bodies '()])
      (match decls
        [(cons ($fn-header params cond stmt) decls)
         (let*-values ([(stmts decls) (splitf-at decls (negate $fn-header?))])
           (loop decls
                 (cons params paramss)
                 (cons cond conds)
                 (cons (extract-block (cons stmt stmts)) bodies)))]
        ['() (with-output-language (Cst Expr)
               `(fn (case (,(reverse paramss) ...) ,(reverse conds)
                      ,(reverse bodies)) ...))]))
    (extract-block decls)))

(define (extract-block decls)
  (let-values ([(stmts expr)
                (let extract ([decls decls])
                  (match decls
                    [(list (and (not (? $fn-header?) (? $def?)) expr))
                     (values '() expr)]
                    [(cons ($def var expr) decls)
                     (define stmt (with-output-language (Cst Stmt) `(def ,var ,expr)))
                     (define-values (stmts expr*) (extract decls))
                     (values (cons stmt stmts) expr*)]
                    [(cons (and (not (? $fn-header?)) stmt) decls)
                     (define-values (stmts expr) (extract decls))
                     (values (cons stmt stmts) expr)]))])
    (with-output-language (Cst Expr)
      `(block ,stmts ... ,expr))))

;;; The actual LALR parser (and some helpers):

(define (binapp l op r)
  (with-output-language (Cst Expr)
    `(call (lex ,op) ,l ,r)))

(define parse-expr
  (parser
    (src-pos)
    (start program)
    (end EOF)
    (tokens payload-toks empty-toks)
    (error (λ (tok-ok? tok-name tok-value start end)
             (printf "parse error ~a\n"
                     (list tok-ok? tok-name tok-value start end))))

    (grammar
      (program
        [(body) $1])

      (body
        [(stmt-list SEMICOLON expr) (extract-block (foldl cons (list $3) $1))]
        [(expr) (extract-block (list $1))])

      (stmt-list
        [(stmt-list SEMICOLON stmt) (cons $3 $1)]
        [(stmt) (list $1)])

      (stmt
        [(var = expr) ($def $1 $3)]
        [(expr) $1])

      (expr [(infix1) $1])

      (infix1
        [(infix1 OP1 infix2) (binapp $1 $2 $3)]
        [(infix2) $1])
      (infix2
        [(infix2 OP2 infix3) (binapp $1 $2 $3)]
        [(infix3) $1])
      (infix3
        [(infix3 OP3 infix4) (binapp $1 $2 $3)]
        [(infix4) $1])
      (infix4
        [(infix4 OP4 infix5) (binapp $1 $2 $3)]
        [(infix5) $1])
      (infix5
        [(infix5 OP5 infix6) (binapp $1 $2 $3)]
        [(infix6) $1])
      (infix6
        [(infix6 OP6 infix7) (binapp $1 $2 $3)]
        [(infix7) $1])
      (infix7
        [(infix7 OP7 app-expr) (binapp $1 $2 $3)]
        [(app-expr) $1])

      (app-expr
        [(app) (match (reverse $1)
                 [(list expr) expr]
                 [(cons f args) (with-output-language (Cst Expr)
                                  `(call ,f ,args ...))])]
        [(primapp) $1])

      (app
        [(simple) (list $1)]
        [(app simple) (cons $2 $1)])

      (primapp
        [(PRIMOP) (with-output-language (Cst Expr) `(primcall ,$1))]
        [(PRIMOP app) (with-output-language (Cst Expr)
                        `(primcall ,$1 ,(reverse $2) ...))])

      (simple
        [(LPAREN expr RPAREN) $2]
        [(LBRACE block RBRACE) $2]
        [(LBRACKET body RBRACKET)
         (with-output-language (Cst Expr)
           `(fn (case () (const #t) ,$2)))]
        [(var) $1]
        [(datum) $1])

      (block
        [(block-decl-list) (parse-decls (reverse $1))])

      (block-decl-list
        [(block-decl) (list $1)]
        [(block-decl-list SEMICOLON block-decl) (cons $3 $1)])

      (block-decl
        [(app => stmt) ($fn-header (app->var-list (reverse $1))
                                   (with-output-language (Cst Expr) `(const #t))
                                   $3)]
        [(app \| expr => stmt) ($fn-header (app->var-list (reverse $1)) $3 $5)]
        [(stmt) $1])

      (var
        [(LEX)               (with-output-language (Cst Var) `(lex ,$1))]
        [(DYN)               (with-output-language (Cst Var) `(dyn ,$1))]
        [(LPAREN OP1 RPAREN) (with-output-language (Cst Var) `(lex ,$2))]
        [(LPAREN OP2 RPAREN) (with-output-language (Cst Var) `(lex ,$2))]
        [(LPAREN OP3 RPAREN) (with-output-language (Cst Var) `(lex ,$2))]
        [(LPAREN OP4 RPAREN) (with-output-language (Cst Var) `(lex ,$2))]
        [(LPAREN OP5 RPAREN) (with-output-language (Cst Var) `(lex ,$2))]
        [(LPAREN OP6 RPAREN) (with-output-language (Cst Var) `(lex ,$2))]
        [(LPAREN OP7 RPAREN) (with-output-language (Cst Var) `(lex ,$2))])

      (datum
        [(LPAREN expr-list RPAREN)
         (with-output-language (Cst Expr) `(primcall __tupleNew ,(reverse $2) ...))]
        [(datom) (with-output-language (Cst Expr) `(const ,$1))])

      (datom
        [(INT) $1]
        [(CHAR) $1]
        [(STRING) $1])

      (expr-list
        [() '()]
        [(expr COMMA) (list $1)]
        [(expr-list-2+) $1])

      (expr-list-2+
        [(expr COMMA expr) (list $3 $1)]
        [(expr-list-2+ COMMA expr) (cons $3 $1)]))))

(define (parse ip)
  (parse-expr (λ () (lex ip))))
