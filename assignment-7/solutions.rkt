#lang eopl

(require (only-in racket displayln))
(require (only-in racket λ))
(require (only-in racket error))
(require (only-in racket filter))
(require (only-in racket findf))
(require (only-in racket printf))
(require (only-in racket range))

(require rackunit)

(require "store.rkt") 
(require "common.rkt")

(define identifier? symbol?)

(define-datatype expval expval?
  (num-val
   (value number?))
  (bool-val
   (boolean boolean?))
  (proc-val
    (proc proc?))
  (pair-val
   (car expval?)
   (cdr expval?))
  (emptylist-val))

(define expval->num
  (lambda (v)
    (cases expval v
           (num-val (num) num) 
           (else (report-expval-extractor-error 'num v)))))

(define expval->bool
  (lambda (v)
    (cases expval v
           (bool-val (bool) bool)
           (else (report-expval-extractor-error 'bool v)))))

(define expval->proc
  (lambda (v)
    (cases expval v
           (proc-val (proc) proc)
           (else (report-expval-extractor-error 'proc v)))))

(define expval->pair
  (lambda (v)
    (cases expval v
           (pair-val (car cdr)
                     (cons car cdr))
           (else (report-expval-extractor-error 'pair v)))))

(define expval-car
  (lambda (v)
    (cases expval v
           (pair-val (car cdr) car)
           (else (report-expval-extractor-error 'car v)))))

(define expval-cdr
  (lambda (v)
    (cases expval v
           (pair-val (car cdr) cdr)
           (else (report-expval-extractor-error 'cdr v)))))

(define expval-null?
  (lambda (v)
    (cases expval v
           (emptylist-val () (bool-val #t))
           (else (bool-val #f)))))


(define-datatype continuation continuation?
  (end-cont)
  (zero1-cont
   (saved-cont continuation?))
  (let-exp-cont
   (var identifier?)
   (body expression?)
   (saved-env environment?)
   (saved-cont continuation?))
  (if-test-cont
   (exp2 expression?)
   (exp3 expression?)
   (saved-env environment?)
   (saved-cont continuation?))
  (diff1-cont
   (exp2 expression?)
   (saved-env environment?)
   (saved-cont continuation?))
  (diff2-cont
   (val1 expval?)
   (saved-cont continuation?))
  (rator-cont
   (rand expression?)
   (saved-env environment?)
   (saved-cont continuation?))
  (rand-cont
   (val1 expval?)
   (saved-cont continuation?))
  (cons-cont
   (exp2 expression?)
   (saved-env environment?)
   (saved-cont continuation?))
  (cons-cont2
   (val1 expval?)
   (saved-cont continuation?))
  (car-cont
   (saved-cont continuation?))
  (cdr-cont
   (saved-cont continuation?))
  (null?-cont
   (saved-cont continuation?))
  ;;4.06
  (list-cont
   (args (list-of expression?))
   (saved-env environment?)
   (saved-cont continuation?))
  (list-cont-tail
   (args (list-of expression?))
   (prev-args list?)
   (saved-env environment?)
   (saved-cont continuation?))
  (set-rhs-cont 
   (env environment?)
   (var identifier?)
   (cont continuation?))
  (begin-cont 
   (env environment?)
   (exps (list-of expression?))
   (cont continuation?))
  )

(define-datatype proc proc?
  (procedure
   (bvar symbol?)
   (body expression?)
   (env environment?)))

(define-datatype environment environment?
  (empty-env)
  (extend-env
   (bvar symbol?)
   (bval integer?)
   (saved-env environment?))
  (extend-env-rec
   (p-name symbol?)
   (b-var symbol?)
   (p-body expression?)
   (saved-env environment?)))

(define apply-env
  (lambda (env search-sym)
    (cases environment env
           (empty-env ()
                      (error 'apply-env "No binding for ~s" search-sym))
           (extend-env (var val saved-env)
                       (if (eqv? search-sym var)
                           val
                           (apply-env saved-env search-sym)))
           (extend-env-rec (p-name b-var p-body saved-env)
                           (if (eqv? search-sym p-name)
                               (proc-val (procedure b-var p-body env))
                               (apply-env saved-env search-sym))))))

(define apply-env-deref 
  (lambda (env search-sym) 
    (deref (apply-env env search-sym))
  )
)

(define value-of-program
  (lambda (pgm)
    (cases program pgm
           (a-program (exp1)
            (begin 
              (initialize-store!)
              (value-of/k exp1 (empty-env) (end-cont)))
            ))))

;;4.06
(define list->pairs
  (lambda (xs)
    (if (null? xs)
	  (emptylist-val)
	  (pair-val (car xs)
		    (list->pairs (cdr xs))))))

;; value-of/k : Exp * Env * Cont -> FinalAnswer
(define value-of/k
  (lambda (exp env cont)
    (cases expression exp
           (const-exp (num) (apply-cont cont (num-val num)))
           (var-exp (var) (apply-cont cont (apply-env-deref env var)))
           (proc-exp (var body)
                     (apply-cont cont
                                 (proc-val (procedure var body env))))
           (letrec-exp (p-name b-var p-body letrec-body)
                       (value-of/k letrec-body
                                   (extend-env-rec p-name b-var p-body env)
                                   cont))
           (zero?-exp (exp1)
                      (value-of/k exp1 env
                                  (zero1-cont cont)))
           (let-exp (var exp1 body)
                    (value-of/k exp1 env
                                (let-exp-cont var body env cont)))
           (if-exp (exp1 exp2 exp3)
                   (value-of/k exp1 env
                               (if-test-cont exp2 exp3 env cont)))
           (diff-exp (exp1 exp2)
                     (value-of/k exp1 env
                                 (diff1-cont exp2 env cont)))
           (call-exp (rator rand)
                     (value-of/k rator env
                                 (rator-cont rand env cont)))
           (emptylist-exp ()
                          (apply-cont cont (emptylist-val)))
           (cons-exp (exp1 exp2)
                     (value-of/k exp1 env
                                 (cons-cont exp2 env cont)))
           (car-exp (exp)
                    (value-of/k exp env (car-cont cont)))
           (cdr-exp (exp)
                    (value-of/k exp env (cdr-cont cont)))

           (null?-exp (exp)
                      (value-of/k exp env (null?-cont cont)))

            ;; 5.06
            (list-exp (args)
                      (if (null? args)
                        (apply-cont cont (emptylist-val))
                        (value-of/k (car args)
                                    env
                                    (list-cont (cdr args) env cont))))

            ;; 5.09
            (assign-exp (var exp1)
              (value-of/k exp1 env (set-rhs-cont env var cont))
            )

            (begin-exp (exp1 exps)
              (value-of/k exp1 env (begin-cont env exps cont))
            )
)))

;; apply-cont : Cont * ExpVal -> FinalAnswer
(define apply-cont
  (lambda (cont val)
    (cases continuation cont
           (end-cont ()
                     (begin
                       (printf "End of computation.~%") val))
           (zero1-cont (saved-cont)
                       (apply-cont saved-cont
                                   (bool-val
                                    (zero? (expval->num val)))))
           (let-exp-cont (var body saved-env saved-cont)
                         (value-of/k body
                                     (extend-env var (newref val) saved-env) saved-cont))
           (if-test-cont (exp2 exp3 saved-env saved-cont)
                         (if (expval->bool val)
                             (value-of/k exp2 saved-env saved-cont)
                             (value-of/k exp3 saved-env saved-cont)))
           (diff1-cont (exp2 saved-env saved-cont)
                       (value-of/k exp2
                                   saved-env (diff2-cont val saved-cont)))
           (diff2-cont (val1 saved-cont)
                       (let ((num1 (expval->num val1))
                             (num2 (expval->num val)))
                         (apply-cont saved-cont
                                     (num-val (- num1 num2)))))
           (rator-cont (rand saved-env saved-cont)
                       (value-of/k rand saved-env
                                   (rand-cont val saved-cont)))
           (rand-cont (val1 saved-cont)
                      (let ((proc (expval->proc val1)))
                        (apply-procedure/k proc val saved-cont)))

	         (cons-cont (exp2 saved-env saved-cont)
                      (value-of/k exp2 saved-env
                                  (cons-cont2 val saved-cont)))
           (cons-cont2 (val1 saved-cont)
                       (apply-cont saved-cont
                                   (pair-val val1 (pair-val val (emptylist-val)))))
           (car-cont (saved-cont)
                     (apply-cont saved-cont
                                 (expval-car val)))
           (cdr-cont (saved-cont)
                     (apply-cont saved-cont
                                 (expval-cdr val)))

           (null?-cont (saved-cont)
                       (apply-cont saved-cont
                                   (expval-null? val)))

	        ;;4.06
	        (list-cont (args saved-env saved-cont)
	      	      (if (null? args)
                  (apply-cont saved-cont
                        (pair-val val (emptylist-val)))
                  (value-of/k (car args)
                        saved-env
                        (list-cont-tail (cdr args)
                            (list val)
                            saved-env saved-cont))))

	        (list-cont-tail (args prev-args saved-env saved-cont)
	      	      (if (null? args)
                  (apply-cont saved-cont
                        (list->pairs (append prev-args (list val))))
                  (value-of/k (car args)
                        saved-env
                        (list-cont-tail
                          (cdr args)
                          (append prev-args (list val))
                          saved-env
                          saved-cont))))
          ;; 4.09
          (set-rhs-cont (env var saved-cont)
              (begin
                (setref! (apply-env env var) val)
                (apply-cont saved-cont val)))

          (begin-cont (env exps saved-cont)
            (if (null? exps)
              (apply-cont saved-cont val)
              (value-of/k (car exps) env (begin-cont env (cdr exps) saved-cont) )
            )
          )
)))

;; apply-procedure/k : Proc * ExpVal * Cont -> FinalAnswer
(define apply-procedure/k
  (lambda (proc1 arg cont)
    (cases proc proc1
           (procedure (var body saved-env)
                      (value-of/k body
                                  (extend-env var arg saved-env)
                                  cont)))))

(define run
  (lambda (string)
    (value-of-program (scan&parse string))))

(displayln (run "list(1, 2, 3, 4)"))
(displayln (run "
      let x = 3
      in list(x, -(x,1), -(x,2))"))

(displayln (run "
      let x = 0
      in begin
           set x = 5 ;
           list(x, -(x,1), -(x,2))
         end 
      "))
