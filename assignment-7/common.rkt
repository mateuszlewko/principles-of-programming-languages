#lang eopl

(require (only-in racket displayln))
(require (only-in racket λ))
(require (only-in racket error))
(require (only-in racket foldl))

(provide (all-defined-out))

(define (zip l1 l2) (map list l1 l2))
(define (zip3 l1 l2 l3) (map list l1 l2 l3))

(define lex
  '((whitespace (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifier
     (letter (arbno (or letter digit "_" "-" "?")))
     symbol)
    (number (digit (arbno digit)) number)
    (number ("-" digit (arbno digit)) number)
    ))


(define grammar
  '((program (expression) a-program)

    (expression (number) const-exp)
    (expression
     ("-" "(" expression "," expression ")")
     diff-exp)

    (expression
     ("zero?" "(" expression ")")
     zero?-exp)

    (expression
     ("if" expression "then" expression "else" expression)
     if-exp)

    (expression (identifier) var-exp)

    (expression
     ("let" identifier "=" expression "in" expression)
     let-exp)

    (expression
     ("proc" "(" identifier ")" expression)
     proc-exp)

    (expression
     ("(" expression expression ")")
     call-exp)

    (expression
     ("letrec"
      identifier "(" identifier ")" "=" expression
      "in" expression)
     letrec-exp)

    ;; 4.06
    (expression ("cons" "(" expression "," expression ")") cons-exp)
    (expression ("car" "(" expression ")") car-exp)
    (expression ("cdr" "(" expression ")") cdr-exp)
    (expression ("emptylist") emptylist-exp)
    (expression ("null?" "(" expression ")") null?-exp)
    (expression ("list" "(" (separated-list expression ",") ")" ) list-exp)

    ;; 4.09
    (expression ("set" identifier "=" expression) assign-exp)
    (expression
      ("begin" expression (arbno ";" expression) "end")
      begin-exp)
    ))

(sllgen:make-define-datatypes lex grammar)
(define scan&parse
  (sllgen:make-string-parser lex grammar))

(define report-expval-extractor-error
  (λ (name curr)
    (error 'expval "Invalid value to extract, expected: ~s, got ~s" name curr)))


(define report-no-binding-found
  (λ (search-var)
    (error 'apply-env "No binding for ~s" search-var)))