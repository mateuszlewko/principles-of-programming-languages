#lang eopl

(require (only-in racket displayln))
(require (only-in racket λ))
(require (only-in racket error))
(require (only-in racket filter))
(require (only-in racket findf))
(require rackunit)

;;; 4.04
;;; (value-of)

(require "store.rkt") ;; 4.09
(require "common.rkt")

(define-datatype proc proc?
  (procedure
   (var symbol?)
   (body expression?)
   (saved-env environment?)
  ))

(define-datatype expval expval?
  (num-val
   (value number?))
  (bool-val
   (boolean boolean?))
  (proc-val
    (proc proc?))
  (ref-val
   (ref reference?))
)

;; environment ;;
(define-datatype environment environment?
  (empty-env)
  (extend-env
   (var symbol?)
   (val expval?)
   (saved-env environment?))
  (extend-env-rec*
   (ids (list-of symbol?))
   (vars (list-of symbol?))
   (bodies (list-of expression?))
   (saved-env environment?)))

(define apply-procedure
  (λ (proc1 arg store)
    (cases proc proc1
      (procedure (var body saved-env)
      ;; extend-env for every arg
        (value-of body (extend-env var arg saved-env) store)))))

;; github/eopl
(define apply-env
  (λ (env search-sym)
    (cases environment env
      (empty-env ()
        (error  report-no-binding-found search-sym))
      (extend-env (bvar bval saved-env)
        (if (eqv? search-sym bvar)
            bval
            (apply-env saved-env search-sym)))
      (extend-env-rec* (p-names b-vars p-bodies saved-env)
        (cond
          ((location search-sym p-names)
          => (λ (n)
                (proc-val
                (procedure
                  (list-ref b-vars n)
                  (list-ref p-bodies n)
                  env))))
          (else (apply-env saved-env search-sym)))))))

(define location
  (λ (sym syms)
    (cond
     ((null? syms) #f)
     ((eqv? sym (car syms)) 0)
     ((location sym (cdr syms))
      => (λ (n)
           (+ n 1)))
     (else #f))))

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

(define expval->proc
  (λ (v)
    (cases expval v
      (proc-val (proc) proc)
      (else (report-expval-extractor-error 'proc v)))))

(define expval->ref
  (λ (v)
    (cases expval v
	    (ref-val (ref) ref)
	    (else (report-expval-extractor-error 'reference v)))))

;; eopl
(define-datatype answer answer?
  (an-answer
   (value expval?)
   (store store?)))

(define value-of
  (λ (exp env store)
    (cases expression exp
           (const-exp (num)
              (an-answer (num-val num) store))
           (var-exp (var)
              (an-answer (apply-env env var)
                         store))

           (diff-exp (exp1 exp2)
              (cases answer (value-of exp1 env store)
                (an-answer (val1 new-store)
                  (let ((val2 (value-of exp2 env store)))
                    (cases answer val2
                      (an-answer (val2 new-store)
                          (let ((v1 (expval->num val1))
                                (v2 (expval->num val2)))
                            (an-answer
                              (num-val (- v1 v2))
                              new-store))))))))

           (zero?-exp (exp1)
              (cases answer (value-of exp1 env store)
                (an-answer (val new-store)
                  (if (zero? (expval->num val))
                    (an-answer (bool-val #t) new-store)
                    (an-answer (bool-val #f) new-store)))))

           (if-exp (exp1 exp2 exp3)
              (cases answer (value-of exp1 env store)
                (an-answer (val new-store)
                  (if (expval->bool val)
                    (value-of exp2 env new-store)
                    (value-of exp3 env new-store)))))

           (let-exp (var exp1 body)
              (cases answer (value-of exp1 env store)
                (an-answer (val new-store)
                  (value-of body
                    (extend-env var val env)
                    new-store))))

           (proc-exp (var body)
              (an-answer (proc-val (procedure var body env))
                         store))

           (call-exp (rator rand)
              (cases answer (value-of rator env store)
                (an-answer (proc-exp new-store)
                  (cases answer (value-of rand env store) ;; get value ov every operand
                      (an-answer (arg new-store)
                        (let ([proc (expval->proc proc-exp)])
                          (apply-procedure proc arg store)))))))

           (letrec-exp (p-names b-vars p-bodies letrec-body)
              (value-of letrec-body
                (extend-env-rec* p-names b-vars p-bodies env) store))

           (begin-exp (exp1 exps)
              (letrec
                  ([value-of-begins
                    (λ (e1 es store)
                      (let ((ans (value-of e1 env store)))
                        (if (null? es)
                            ans
                            (value-of-begins (car es) (cdr es) store))))])
                (value-of-begins exp1 exps store)))

           (newref-exp (exp1)
              (cases answer (value-of exp1 env store)
                (an-answer (val new-store)
                  (an-answer (ref-val (newref! val new-store))
                    new-store))))

           (deref-exp (exp1)
              (cases answer (value-of exp1 env store)
                (an-answer (v1 new-store)
                  (let ((ref1 (expval->ref v1)))
                    (an-answer (deref ref1 new-store) new-store)))))

           (setref-exp (exp1 exp2)
              (cases answer (value-of exp1 env store)
                (an-answer (v1 new-store)
                  (cases answer (value-of exp2 env store)
                    (an-answer (v2 new-store)
                      (let ([ref1 (expval->ref v1)])
                        (begin
                          (setref! ref1 v2 new-store)
                          (an-answer (num-val 1) new-store))))))))
           )))

(define value-of-program
  (λ (pgm)
    (cases program pgm
	    (a-program (exp1)
		    (cases answer (value-of exp1 (empty-env) (empty-store))
          (an-answer (value store) value)
        )))))

(define run
  (λ (source)
    (value-of-program (scan&parse source))))

(define expref-prog1 
  "let x = newref(0)
    in letrec even(dummy)
                = if zero? (deref(x))
                    then 1
                    else 
                      begin
                        setref(x, -(deref(x),1));
                        (odd 888)
                      end

              odd(dummy)
                = if zero?(deref(x))
                    then 0
                    else 
                      begin
                        setref(x, -(deref(x),1));
                        (even 888)
                      end
      in begin 
         setref(x, 13); 
         (odd 888) end")

(displayln (run expref-prog1))
(test-begin 
  (check-equal? (run expref-prog1) (num-val 1)) ;; 13 is odd
)     


(define proc-prog1 "
                    let a = 3
                    in let p = proc (x) -(x, a) 
                      in -(a, (p 2))")
(displayln (run proc-prog1))