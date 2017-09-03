#lang racket

(require racket/match
         parser-tools/lex
         (prefix-in : parser-tools/lex-sre)
         parser-tools/yacc
         nanopass/base

         "langs.rkt")

(provide parse)

(define-tokens payload-toks
  (LEX DYN
   INT))
(define-empty-tokens empty-toks
  (EOF
   LBRACE RBRACE
   SEMICOLON
   = =>))

(define-lex-abbrevs
  (lower-letter (:/ "a" "z"))
  (upper-letter (:/ #\A #\Z))
  (digit (:/ #\0 #\9)))

(define lex
  (lexer-src-pos
    [whitespace (return-without-pos (lex input-port))] ; skip
    [(eof) 'EOF]
    ["{" 'LBRACE]
    ["}" 'RBRACE]
    [";" 'SEMICOLON]
    ["=>" '=>]
    ["=" '=]
    [(:: "$" (:+ (:or lower-letter upper-letter)))
     (token-DYN (string->symbol (substring lexeme 1)))]
    [(:+ (:or lower-letter upper-letter))
     (token-LEX (string->symbol lexeme))]
    [(:+ digit) (token-INT (string->number lexeme))]))

(struct $fn-header (params body-start))
(struct $def (var expr))

(define (app->var-list app)
  (map (λ (expr) (nanopass-case (Core Expr) expr [,x x]))
       app))

(define parse-decls
  (match-lambda
    [(cons ($fn-header params stmt) decls)
     (define body (extract-block (cons stmt decls)))
     (with-output-language (Core Expr) `(fn (,params ...) ,body))]
    [(and stmts (cons _ _)) (extract-block stmts)]))

(define (extract-block decls)
  (define extract
    (match-lambda
      [(list (and (not (? $fn-header?) (? $def?)) expr))
       (values '() expr)]
      [(cons ($def var expr) decls)
       (define stmt (with-output-language (Core Stmt) `(def ,var ,expr)))
       (define-values (stmts expr*) (extract decls))
       (values (cons stmt stmts) expr*)]
      [(cons (and (not (? $fn-header?)) stmt) decls)
       (define-values (stmts expr) (extract decls))
       (values (cons stmt stmts) expr)]))
  (define-values (stmts expr) (extract decls))
  (with-output-language (Core Expr) `(block ,stmts ... ,expr)))

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
        [(app => stmt) ($fn-header (app->var-list (reverse $1)) $3)]
        [(stmt) $1])

      (stmt
        [(var = expr) ($def $1 $3)]
        [(expr) $1])
     
      (expr
        [(app) (match (reverse $1)
                 [(list expr) expr]
                 [(cons f args) (with-output-language (Core Expr)
                                  `(call ,f ,args ...))])])

      (app
        [(simple) (list $1)]
        [(app simple) (cons $2 $1)])

      (simple
        [(LBRACE block RBRACE) $2]
        [(var) $1]
        [(datum) $1])

      (var
        [(LEX) (with-output-language (Core Var) `(lex ,$1))]
        [(DYN) (with-output-language (Core Var) `(dyn ,$1))])

      (datum
        [(datom) (with-output-language (Core Expr) `(const ,$1))])

      (datom
        [(INT) $1]))))

(define (parse ip)
  (parse-expr (λ () (lex ip))))
