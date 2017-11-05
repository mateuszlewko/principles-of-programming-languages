#lang eopl

(require (only-in racket displayln))
(require (only-in racket λ))
(require (only-in racket error))
(require rackunit)

(require "list-env.rkt")
(require rackunit)

(define (zip l1 l2) (map list l1 l2))

(define the-lexical-spec
  '((whitespace (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifier
     (letter (arbno (or letter digit "_" "-" "?")))
     symbol)
    (number (digit (arbno digit)) number)
    (number ("-" digit (arbno digit)) number)
    ))

;;; (define-datatype expression expression?
;;;   (const-exp
;;;    (num number?))
;;;   (diff-exp
;;;    (exp1 expression?)
;;;    (exp2 expression?))
;;;   (zero?-exp
;;;    (expr expression?))
;;;   (if-exp
;;;    (predicate-exp expression?)
;;;    (true-res-exp expression?)
;;;    (false-res-exp expression?))
;;;   (var-exp
;;;    (var symbol?))
;;; ;;;   (equal?-exp
;;; ;;;    (exp1 expression?)
;;; ;;;    (exp2 expression?))
;;; ;;;   (less?-exp
;;; ;;;    (exp1 expression?)
;;; ;;;    (exp2 expression?))
;;; ;;;   (greater?-exp
;;; ;;;    (exp1 expression?)
;;; ;;;    (exp2 expression?))
;;; ;;;   (minus-exp
;;; ;;;    (body-exp expression?))
;;; ;;;   (add-exp
;;; ;;;    (exp1 expression?)
;;; ;;;    (exp2 expression?))
;;; ;;;   (mult-exp
;;; ;;;    (exp1 expression?)
;;; ;;;    (exp2 expression?))
;;; ;;;   (div-exp
;;; ;;;    (exp1 expression?)
;;; ;;;    (exp2 expression?))
;;;   (let-exp
;;;    (var symbol?)
;;;    (val expression?)
;;;    (body expression?))

;;;   (emptylist-exp)
;;;   (cons-exp
;;;    (exp1 expression?)
;;;    (exp2 expression?))
;;;   (car-exp
;;;    (body expression?))
;;;   (cdr-exp
;;;    (body expression?))
;;;   (null?-exp
;;;    (body expression?))
;;;   (list-exp
;;;    (args (list-of expression?))))

;;; (define-datatype program program?
;;;   (a-program
;;;     (exp1 expression?)))

;;; (define the-grammar
;;;   '((program (expression) a-program)
    
;;;     (expression (number) const-exp)
;;;     (expression
;;;      ("-" "(" expression "," expression ")")
;;;      diff-exp)
    
;;;     (expression
;;;      ("zero?" "(" expression ")")
;;;      zero?-exp)
    
;;;     (expression
;;;      ("if" expression "then" expression "else" expression)
;;;      if-exp)
    
;;;     (expression (identifier) var-exp)
    
;;;     (expression
;;;      ("let" identifier "=" expression "in" expression)
;;;      let-exp)   
    
;;;     ))

(define the-grammar
  '((program (expression) a-program)
    (expression (identifier) var-exp)
    (expression (number) const-exp)
    (expression ("-" "(" expression "," expression ")") diff-exp)
    ;;; (expression ("+" "(" expression "," expression ")") add-exp)
    ;;; (expression ("*" "(" expression "," expression ")") mult-exp)
    ;;; (expression ("/" "(" expression "," expression ")") div-exp)
    (expression ("zero?" "(" expression ")") zero?-exp)
    ;;; (expression ("equal?" "(" expression "," expression ")") equal?-exp)
    ;;; (expression ("less?" "(" expression "," expression ")") less?-exp)
    ;;; (expression ("greater?" "(" expression "," expression ")") greater?-exp)
    ;;; (expression ("minus" "(" expression ")") minus-exp)
    (expression ("if" expression "then" expression "else" expression) if-exp)
    (expression ("let" identifier "=" expression "in" expression) let-exp)
    ;;; (expression ("let*" (arbno identifier "=" expression) "in" expression) let*-exp)
    (expression ("cons" "(" expression "," expression ")") cons-exp)
    (expression ("car" "(" expression ")") car-exp)
    (expression ("cdr" "(" expression ")") cdr-exp)
    (expression ("emptylist") emptylist-exp)
    (expression ("null?" "(" expression ")") null?-exp)
    (expression ("list" "(" (separated-list expression ",") ")" ) list-exp)
  )
)

(sllgen:make-define-datatypes the-lexical-spec the-grammar)
(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))


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

(define list-val ;; 3.10
  (λ (args)
    (if (null? args)
	    (emptylist-val)
	    (pair-val (car args) (list-val (cdr args)))
    )
  ))

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

  ;;; (define map-value-of 
  ;;;   (λ (exps)
  ;;;      (map (λ (exp) (value-of exp env) exps)) 
  ;;;   ))

(define value-of
  (λ (exp env)
    (cases expression exp

      (const-exp (num) 
        (num-val num))

      (var-exp (var) 
        (apply-env env var))
        
      (diff-exp (lhs rhs)
        (num-val
          (- (expval->num (value-of lhs env))
             (expval->num (value-of rhs env))
          )))

      ;;; (add-exp (exp1 exp2)
      ;;;         (let ((val1 (value-of exp1 env))
      ;;;               (val2 (value-of exp2 env)))
      ;;;           (let ((num1 (expval->num val1))
      ;;;                 (num2 (expval->num val2)))
      ;;;             (num-val
      ;;;               (+ num1 num2)))))
      ;;; (mult-exp (exp1 exp2)
      ;;;           (let ((val1 (value-of exp1 env))
      ;;;                 (val2 (value-of exp2 env)))
      ;;;             (let ((num1 (expval->num val1))
      ;;;                   (num2 (expval->num val2)))
      ;;;               (num-val
      ;;;               (* num1 num2)))))
      ;;; (div-exp (exp1 exp2)
      ;;;         (let ((val1 (value-of exp1 env))
      ;;;               (val2 (value-of exp2 env)))
      ;;;           (let ((num1 (expval->num val1))
      ;;;                 (num2 (expval->num val2)))
      ;;;             (num-val
      ;;;               (/ num1 num2)))))
      (zero?-exp (exp1)
                (let ((val1 (value-of exp1 env)))
                  (let ((num1 (expval->num val1)))
                    (if (zero? num1)
                        (bool-val #t)
                        (bool-val #f)))))

      ;;; (equal?-exp (exp1 exp2)
      ;;;             (let ((val1 (value-of exp1 env))
      ;;;                   (val2 (value-of exp2 env)))
      ;;;               (let ((num1 (expval->num val1))
      ;;;                     (num2 (expval->num val2)))
      ;;;                 (bool-val
      ;;;                 (= num1 num2)))))

      ;;; (less?-exp (exp1 exp2)
      ;;;           (let ((val1 (value-of exp1 env))
      ;;;                 (val2 (value-of exp2 env)))
      ;;;             (let ((num1 (expval->num val1))
      ;;;                   (num2 (expval->num val2)))
      ;;;               (bool-val
      ;;;                 (< num1 num2)))))
      ;;; (greater?-exp (exp1 exp2)
      ;;;               (let ((val1 (value-of exp1 env))
      ;;;                     (val2 (value-of exp2 env)))
      ;;;                 (let ((num1 (expval->num val1))
      ;;;                       (num2 (expval->num val2)))
      ;;;                   (bool-val
      ;;;                   (> num1 num2)))))
      (if-exp (exp1 exp2 exp3)
              (let ((val1 (value-of exp1 env)))
                (if (expval->bool val1)
                    (value-of exp2 env)
                    (value-of exp3 env))))
      ;;; (minus-exp (body-exp)
      ;;;           (let ((val1 (value-of body-exp env)))
      ;;;             (let ((num (expval->num val1)))
      ;;;               (num-val (- 0 num)))))
      (let-exp (var exp body)
        (let ((val1 (value-of exp env)))
          (value-of body
            (extend-env var val1 env)
          )))

      ;;; (let*-exp (vars exps body) ;; 3.17
      ;;;   (let ((vals (map (λ (x) (value-of x env))))) 
      ;;;     (num-val 4)
      ;;;   )
      ;;; )
        ;;; (let ((val1 (value-of exp1 env)))
        ;;;   (value-of body
        ;;;     (extend-env var val1 env)
        ;;;   ))) 

      (emptylist-exp ()
                    (emptylist-val))
      (cons-exp (exp1 exp2) ;; 3.09
                (let ((val1 (value-of exp1 env))
                      (val2 (value-of exp2 env)))
                  (pair-val val1 val2)))
      (car-exp (body)
        (expval-car (value-of body env)))
      (cdr-exp (body)
        (expval-cdr (value-of body env)))
      (null?-exp (exp)
        (expval-null? (value-of exp env)))
      (list-exp (exp-list) ;; 3.10
        (list-val (map (λ (x) (value-of x env)) exp-list)))
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
;;; (define displ)
;;; (displayln (run list-prog))
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
        )
      )
    )
  ))

;;; (define let*-prog "let x = 30
;;;                    in let* x = -(x,1) y = -(x,2)
;;;                    in -(x,y)")

;;; (displayln (run let*-prog))
