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

;;; TODO: Fill out missing syntax ("(- foo)", "(foo *)", "(_ + 5)" etc.)

;;;; # Lexer

(define-tokens payload-toks
  (LEX DYN OP1 OP2 OP3 OP4 OP5 OP6 OP7 PRIMOP META
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
    [(:: "@" (:+ (:or lower-letter upper-letter)))
     (token-META (string->symbol (substring lexeme 1)))]
    [(:+ (:or lower-letter upper-letter))
     (token-LEX (string->symbol lexeme))]
    [(:+ digit) (token-INT (string->number lexeme))]))

;;;; # Parser

(define (app->var-list app)
  (define (unwrap-var-expr expr)
    (nanopass-case (Cst Expr) expr
      [,x x]))
  (map unwrap-var-expr app))

(define (binapp l op r)
  (with-output-language (Cst Expr)
    `(call (lex ,op) ,l ,r)))

(define (make-case params cond body)
  (with-output-language (Cst Case)
    (if (list? params)
      `(case (,params ...) ,cond ,body)
      `(case ,params ,cond ,body))))

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
        [(stmt-list SEMICOLON expr)
         (with-output-language (Cst Expr)
           `(block ,(reverse $1) ... ,$3))]
        [(expr) $1])

      (stmt-list
        [(stmt-list SEMICOLON stmt) (cons $3 $1)]
        [(stmt) (list $1)])

      (stmt
        [(var = expr) (with-output-language (Cst Stmt) `(def ,$1 ,$3))]
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
        [(primapp) $1]
        [(macro) $1])

      (app
        [(simple) (list $1)]
        [(app simple) (cons $2 $1)])

      (primapp
        [(PRIMOP) (with-output-language (Cst Expr) `(primcall ,$1))]
        [(PRIMOP app) (with-output-language (Cst Expr)
                        (case $1
                          [(__ffnCall)
                           (match (reverse $2)
                             [(list callee args) `(ffncall ,callee ,args)]
                             [_ (error "wrong number of arguments to __ffnCall")])]
                          [else `(primcall ,$1 ,(reverse $2) ...)]))])

      (macro
        [(META)     (with-output-language (Cst Expr) `(macro ,$1))]
        [(META app) (with-output-language (Cst Expr)
                      `(macro ,$1 ,(reverse $2) ...))])

      (simple
        [(LPAREN expr RPAREN) $2]
        [(LBRACE method-list RBRACE)
         (with-output-language (Cst Expr)
           `(fn ,(reverse $2) ...))]
        [(LBRACE body RBRACE) $2]
        [(LBRACKET body RBRACKET)
         (with-output-language (Cst Expr)
           `(fn (case () (const #t) ,$2)))]
        [(var) $1]
        [(datum) $1])

      (method-list
        [(method-list SEMICOLON method) (cons $3 $1)]
        [(method) (list $1)])

      (method
        [(params => expr) (make-case $1 (with-output-language (Cst Expr) `(const #t)) $3)]
        [(params \| expr => expr) (make-case $1 $3 $5)])

      (params
        [(app)   (app->var-list (reverse $1))]
        [(macro) (nanopass-case (Cst Expr) $1
                   [(macro ,n ,x) (guard (eq? n 'args)) x]
                   [(macro ,n ,e* ...) (error "illegal macro call as parameter list")]
                   [else (error "unreachable")])])

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
