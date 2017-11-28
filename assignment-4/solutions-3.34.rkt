#lang eopl

(require (only-in racket displayln))
(require (only-in racket λ))
(require (only-in racket error))
(require (only-in racket filter))
(require (only-in racket findf))
(require rackunit)

(require "common.rkt")

(define-datatype proc proc?
  (procedure
   (var symbol?)
   (body expression?)
   (saved-env procedure?)
  ))

(define-datatype expval expval?
  (num-val
   (value number?))
  (bool-val
   (boolean boolean?))
  (pair-val
   (car expval?)
   (cdr expval?))
  (emptylist-val)
  (proc-val
    (proc proc?))
)

;; environment ;;
(define empty-env
  (λ ()
    (λ (search-var)
      (report-no-binding-found search-var))))

(define apply-env
  (λ (env search-var)
    (env search-var)))

(define extend-env
  (λ (saved-var saved-val saved-env)
    (λ (search-var)
      (if (eqv? search-var saved-var)
        saved-val
        (apply-env saved-env search-var)))))

(define proc-lookup 
  (λ (search-var ids vars bodies)
    (findf (lambda (x) (eqv? search-var (car x))) 
           (zip3 ids vars bodies))
  )
)

(define extend-env-rec
  (λ (ids vars bodies saved-env)
    (λ (search-var)
      (let ([lookup (proc-lookup search-var ids vars bodies)])
        (if lookup 
          (proc-val (procedure (cadr lookup) (caddr lookup) 
                               (extend-env-rec ids vars bodies saved-env)))
          (apply-env saved-env search-var)
        )
      )
    )
  )
)

(define apply-procedure
  (λ (proc1 arg)
    (cases proc proc1
      (procedure (var body saved-env)
        (value-of body (extend-env var arg saved-env))))))

(define expval->num
  (λ (val)
    (cases expval val
      (num-val (num) num)
      (else (report-expval-extractor-error 'num val)))))

(define expval->bool
  (λ (val)
    (cases expval val
      (bool-val (bool) bool)
      (else (report-expval-extractor-error 'bool val)))))

(define list-val->cons
  (λ (args)
    (if (null? args)
	    (emptylist-val)
	    (pair-val (car args) (list-val->cons (cdr args))))))

(define expval->proc
  (λ (v)
    (cases expval v
      (proc-val (proc) proc)
      (else (report-expval-extractor-error 'proc v)))))


(define value-of
  (λ (exp env)
    (define (val-of->num exp) 
      (expval->num (value-of exp env)))
      
    (cases expression exp

      (const-exp (num) 
        (num-val num))

      (var-exp (var) 
        (apply-env env var))
        
      (diff-exp (lhs rhs)
        (num-val
          (- (val-of->num lhs)
             (val-of->num rhs))))

      (zero?-exp (exp1)
        (let ((val1 (value-of exp1 env)))
          (let ((num1 (expval->num val1)))
            (if (zero? num1)
                (bool-val #t)
                (bool-val #f)))))

      (if-exp (exp1 exp2 exp3)
        (let ((val1 (value-of exp1 env)))
          (if (expval->bool val1)
              (value-of exp2 env)
              (value-of exp3 env))))

      (let-exp (var exp body)
        (let ([val (value-of exp env)])
          (value-of body
            (extend-env var val env)
          )))

      (proc-exp (var body)
        (proc-val (procedure var body env)))

      (call-exp (rator rand)
        (let ([proc (expval->proc (value-of rator env))]
              [arg (value-of rand env)])
          (apply-procedure proc arg)))

      (letrec-exp (p-names b-vars p-bodys letrec-body)
        (value-of letrec-body
          (extend-env-rec p-names b-vars p-bodys env)))
    )
  )
)

(define value-of-program 
  (λ (pgm)
    (cases program pgm
      (a-program (exp1)
        (value-of exp1 (empty-env))))))

(define run
  (λ (source)
    (value-of-program (scan&parse source))))


(define letrec-prog1 "
  letrec
    even(x) = if zero?(x) then 1 else (odd -(x,1))
    odd(x) = if zero?(x) then 0 else (even -(x,1))
  in (odd 13)")

(define letrec-prog2 "
  letrec
    even(x) = if zero?(x) then 1 else (odd -(x,1))
    odd(x) = if zero?(x) then 0 else (even -(x,1))
  in (odd 0)")

(test-begin 
  (check-equal? (run letrec-prog1) (num-val 1))
  (check-equal? (run letrec-prog2) (num-val 0))
)     