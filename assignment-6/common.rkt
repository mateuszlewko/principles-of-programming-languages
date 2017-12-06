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
  '((program (statement) a-program)

    (expression (number) const-exp)
    (expression (identifier) var-exp)

    (statement
     ("{" (separated-list statement ";") "}")
     block-statement)

    (expression
     ("-" "(" expression "," expression ")") diff-exp)
    (expression
     ("+" "(" expression "," expression ")") add-exp)
    (expression
     ("*" "(" expression "," expression ")") multi-exp)

    (expression
     ("zero?" "(" expression ")")
     zero?-exp)

    (expression
     ("not" "(" expression ")")
     not-exp)

    (statement
     ("if" expression "then" statement "else" statement)
     if-statement)

    (expression
       ("if-exp" expression "then" expression "else" expression)
     if-exp)

    (statement
     ("while" expression statement)
     while-statement)

    (expression
     ("proc" "(" (separated-list identifier ",") ")" expression)
     proc-exp)

    (statement
     ("print" expression)
     print-stat)

    (statement
     ("var" identifier "=" expression (arbno "," identifier "=" expression) ";" statement)
     declear-statement)

    (statement
     (identifier "=" expression)
     set-statement)

    (expression
     ("(" expression (arbno expression) ")")
     call-exp)

    (expression
     ("newarray"  "("  expression "," expression ")" )
      newarray-exp)
    (expression
     ("arrayref" "(" expression "," expression ")" )
     arrayref-exp)
    (expression
     ("arrayset" "(" expression "," expression "," expression ")" )
     arrayset-exp)
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