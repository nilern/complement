#lang racket/base

(require racket/match racket/list (only-in racket/function negate)
         parser-tools/lex
         (prefix-in : parser-tools/lex-sre)
         parser-tools/yacc
         nanopass/base

         "langs.rkt")

(provide parse)

(define-tokens payload-toks
  (LEX DYN PRIMOP STRING
   INT CHAR))
(define-empty-tokens empty-toks
  (EOF
   LPAREN RPAREN LBRACE RBRACE
   SEMICOLON
   = => \|))

(define-lex-abbrevs
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
    ["{" 'LBRACE]
    ["}" 'RBRACE]
    [";" 'SEMICOLON]
    ["=>" '=>]
    ["=" '=]
    ["|" '\|]
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

(struct $fn-header (params cond body-start))
(struct $def (var expr))

(define (app->var-list app)
  (map (λ (expr) (nanopass-case (Cst Expr) expr [,x x]))
       app))

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
  (define extract
    (match-lambda
      [(list (and (not (? $fn-header?) (? $def?)) expr))
       (values '() expr)]
      [(cons ($def var expr) decls)
       (define stmt (with-output-language (Cst Stmt) `(def ,var ,expr)))
       (define-values (stmts expr*) (extract decls))
       (values (cons stmt stmts) expr*)]
      [(cons (and (not (? $fn-header?)) stmt) decls)
       (define-values (stmts expr) (extract decls))
       (values (cons stmt stmts) expr)]))
  (define-values (stmts expr) (extract decls))
  (with-output-language (Cst Expr) `(block ,stmts ... ,expr)))

(define parse-expr
  (parser
    (src-pos)
    (start block)
    (end EOF)
    (tokens payload-toks empty-toks)
    (error (λ (tok-ok? tok-name tok-value start end)
             (printf "parse error ~a\n"
                     (list tok-ok? tok-name tok-value start end))))

    (grammar
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

      (stmt
        [(var = expr) ($def $1 $3)]
        [(expr) $1])

      (expr
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
        [(var) $1]
        [(datum) $1])

      (var
        [(LEX) (with-output-language (Cst Var) `(lex ,$1))]
        [(DYN) (with-output-language (Cst Var) `(dyn ,$1))])

      (datum
        [(datom) (with-output-language (Cst Expr) `(const ,$1))])

      (datom
        [(INT) $1]
        [(CHAR) $1]
        [(STRING) $1]))))

(define (parse ip)
  (parse-expr (λ () (lex ip))))
