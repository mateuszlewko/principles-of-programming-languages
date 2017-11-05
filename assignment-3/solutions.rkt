#lang eopl

(require (only-in racket displayln))
(require (only-in racket λ))
(require (only-in racket error))
(require rackunit)

(require "list-env.rkt")
(require rackunit)

(define (zip l1 l2) (map list l1 l2))

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
    (expression (identifier) var-exp)
    (expression (number) const-exp)
    (expression ("-" "(" expression "," expression ")") diff-exp)
    (expression ("zero?" "(" expression ")") zero?-exp)
    (expression ("if" expression "then" expression "else" expression) if-exp)
    (expression ("let" identifier "=" expression "in" expression) let-exp)
    (expression ("let*" (arbno identifier "=" expression) "in" expression) let*-exp)
    (expression ("cons" "(" expression "," expression ")") cons-exp)
    (expression ("car" "(" expression ")") car-exp)
    (expression ("cdr" "(" expression ")") cdr-exp)
    (expression ("emptylist") emptylist-exp)
    (expression ("null?" "(" expression ")") null?-exp)
    (expression ("list" "(" (separated-list expression ",") ")" ) list-exp)
  )
)

(sllgen:make-define-datatypes lex grammar)
(define scan&parse
  (sllgen:make-string-parser lex grammar))

(define report-expval-extractor-error
  (λ (name curr)
    (error 'expval "Invalid value to extract, expected: ~s, got ~s" name curr)
  )
)

(define-datatype expval expval?
  (num-val
   (value number?))
  (bool-val
   (boolean boolean?))
  (pair-val
   (car expval?)
   (cdr expval?))
  (emptylist-val))

;; eopl
(define expval->num
  (λ (val)
    (cases expval val
      (num-val (num) num)
      (else (report-expval-extractor-error 'num val)))))

;; eopl
(define expval->bool
  (λ (val)
    (cases expval val
      (bool-val (bool) bool)
      (else (report-expval-extractor-error 'bool val)))))

;; 3.10
(define list-val->cons
  (λ (args)
    (if (null? args)
	    (emptylist-val)
	    (pair-val (car args) (list-val->cons (cdr args))))))

(define expval-car
  (λ (v)
    (cases expval v
	   (pair-val (car cdr) car)
	   (else (report-expval-extractor-error 'car v)))))

(define expval-cdr
  (λ (v)
    (cases expval v
	   (pair-val (car cdr) cdr)
	   (else (report-expval-extractor-error 'cdr v)))))

(define expval-null?
  (λ (v)
    (cases expval v
	   (emptylist-val () (bool-val #t))
	   (else (bool-val #f)))))

(define value-of
  (λ (exp env)
    (define (val-of->num exp) 
      (expval->num (value-of exp env)))

    (define (map-value-of exps)
      (map (λ (exp) (value-of exp env)) exps))

    (define (fold-vars&exps vars exps env)
      (if (or (null? vars)
              (null? exps))
        env
        (let* ([var (car vars)]
                [exp (car exps)]
                [val (value-of exp env)])
          (fold-vars&exps (cdr vars) (cdr exps) (extend-env var val env)))))

    (cases expression exp

      (const-exp (num) 
        (num-val num))

      (var-exp (var) 
        (apply-env env var))
        
      (diff-exp (lhs rhs)
        (num-val
          (- (val-of->num lhs)
             (val-of->num rhs))))

      (zero?-exp (exp)
        (if (zero? (val-of->num exp))
          (bool-val #t)
          (bool-val #f)))

      (if-exp (cond-exp true-exp false-exp)
        (let ([cond (value-of cond-exp env)])
          (if (expval->bool cond)
            (value-of true-exp env)
            (value-of false-exp env))))

      (let-exp (var exp body)
        (let ([val (value-of exp env)])
          (value-of body
            (extend-env var val env)
          )))

      ;; 3.17
      (let*-exp (vars exps body) 
        (let ([env (fold-vars&exps vars exps env)])  
          (value-of body env)))

      ;; 3.09
      (cons-exp (exp1 exp2) 
        (pair-val (value-of exp1 env)
                  (value-of exp2 env)))

      (car-exp (body)
        (expval-car (value-of body env)))
      
      (cdr-exp (body)
        (expval-cdr (value-of body env)))
        
      (emptylist-exp ()
        (emptylist-val))

      (null?-exp (exp)
        (expval-null? (value-of exp env)))

      ;; 3.10
      (list-exp (exp-list) 
        (list-val->cons (map-value-of exp-list)))
)))

(define value-of-program 
  (λ (pgm)
    (cases program pgm
      (a-program (exp1)
        (value-of exp1 (empty-env))))))

(define run
  (λ (source)
    (value-of-program (scan&parse source))))

(define cons-list-prog "let x = 4 
                   in cons(x,
                            cons(cons(-(x, 1),
                                       emptylist),
                                 emptylist))
                  ")

(test-begin 
  (check-equal? 
    (run cons-list-prog) 
    (pair-val 
      (num-val 4)
      (pair-val 
        (pair-val 
          (num-val 3) 
          (emptylist-val)) 
        (emptylist-val))
    )
  ))

(define list-prog "let x = 4
                   in list(x, -(x, 1), -(x, 3))")

(test-begin 
  (check-equal? 
    (run list-prog) 
    (pair-val 
      (num-val 4)
      (pair-val 
        (num-val 3) 
        (pair-val 
          (num-val 1) 
          (emptylist-val)
        )))))

(define let*-prog "let x = 30
                   in let* x = -(x,1) y = -(x,2)
                   in -(x,y)")

(test-begin 
  (check-equal? (num-val 2) (run let*-prog)))
