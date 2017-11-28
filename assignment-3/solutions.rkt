#lang eopl

(require (only-in racket displayln))
(require (only-in racket λ))
(require (only-in racket error))
(require (only-in racket filter))
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
    (expression ("proc" "(" identifier ")" expression) proc-exp)
    ;;; (expression ("by-name-proc" "(" identifier ")" expression) by-name-proc-exp)
    ;;; (expression ("lazy" "(" expression ")") lazy-exp)
    (expression ("(" expression expression ")") call-exp)
    (expression ("-" "(" expression "," expression ")") diff-exp)
    (expression ("let" identifier "=" expression "in" expression) let-exp)
    (expression ("let*" (arbno identifier "=" expression) "in" expression) let*-exp)
    (expression ("cons" "(" expression "," expression ")") cons-exp)
    (expression ("emptylist") emptylist-exp)
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

(define-datatype proc proc?
  (procedure
   (var symbol?)
   (body expression?)
  ;;;  (saved-env environment?)
  ))

;;; (define proc-p?
;;;   (λ (val) (procedure? val)))

;;; (define procedure-p
;;;   (λ (var body)
;;;     (λ (val env)
;;;       (value-of body (extend-env var val env)))))

;;; (define-datatype by-name-proc by-name-proc?
;;;   (by-name-procedure
;;;     (var symbol?)
;;;     (body expression?)
;;;     (saved-env environment?)
;;;   ))

(define proc-p?
  (λ (val) (procedure? val)))

(define procedure-p
  (λ (var body)
    (λ (val env)
      (value-of body (extend-env var val env)))))

(define apply-procedure-env-p
  (λ (proc1 val env)
    (proc1 val env)))

(define-datatype expval expval?
  (num-val
   (value number?))
  (bool-val
   (boolean boolean?))
  (pair-val
   (car expval?)
   (cdr expval?))
  (emptylist-val)
  (proc-val-p 
    (proc proc-p?))
  (proc-val
    (proc proc?))
  ;;; (by-name-proc-val
  ;;;   (proc by-name-proc?))
)

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

;; 3.28
(define expval->proc
  (λ (v)
    (cases expval v
      (proc-val (proc) proc)
      (proc-val-p (proc) proc)
      (else (report-expval-extractor-error 'proc v)))))
      
;; eopl
;;; (define apply-procedure
;;;   (λ (proc arg)
;;;     (cases proc proc
;;;       (procedure (var body saved-env)
;;;         (value-of body (extend-env var arg saved-env))))))

(define extract-free
  (λ (expr already-bound)
    (cases expression expr
      (const-exp (num) '())
     
      (var-exp (var)
        (if (memq var already-bound)
          '()
          '(var)))

      (diff-exp (exp1 exp2)
        (append (extract-free exp1 already-bound)
                (extract-free exp2 already-bound)))
     
      (let-exp (var value body)
        (append (extract-free value already-bound)
                (extract-free body (cons var already-bound))))

      (proc-exp (var body)
        (append (extract-free body (cons var already-bound))))

      (call-exp (var body)
        (append (extract-free var already-bound)
                (extract-free body already-bound)))
      
      (else '()))))

(define only-free-env 
  (λ (curr-env free-vars)
    (if (null? free-vars)
      empty-env
      (let ([env (only-free-env curr-env (cdr free-vars))]
            [var (car free-vars)])
        (if (has-binding? curr-env var)
          (extend-env var (apply-env curr-env var) env)
          env)))))

(define apply-procedure-env
  (λ (proc1 arg env)
    (cases proc proc1
      (procedure (var body)
        (let* ([free (extract-free body '())]
               [free-env (only-free-env env free)])
          (value-of body (extend-env var arg env)) 
        )
      ))))

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

      (emptylist-exp ()
        (emptylist-val))

      ;; 3.10
      (list-exp (exp-list) 
        (list-val->cons (map-value-of exp-list)))

      ;; by-name not finished
      ;;; (by-name-proc-exp (var body)
      ;;;   (by-name-proc (by-name-procedure var body env)))

      ;; 3.26
      ;;; (proc-exp (var body)
      ;;;   (proc-val (procedure var body)))

      ;;; (call-exp (rator rand)
      ;;;   (let ([proc (expval->proc (value-of rator env))]
      ;;;         [arg (value-of rand env)])
      ;;;     (apply-procedure-env proc arg env)))
      
      ;; 3.28

      ;; procedural rep
      (proc-exp (var body)
        (proc-val-p (procedure-p var body)))

      (call-exp (rator rand)
        (let ([proc (expval->proc (value-of rator env))]
              [arg (value-of rand env)])
          (apply-procedure-env-p proc arg env)))

      ;; data-structure rep

      (proc-exp (var body)
        (proc-val (procedure var body)))

      (call-exp (rator rand)
        (let ([proc (expval->proc (value-of rator env))]
              [arg (value-of rand env)])
          (apply-procedure-env proc arg env)))
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

(define cons-list-prog "let x = 4 
                        in cons(x,
                                  cons(cons(-(x, 1),
                                            emptylist),
                                      emptylist))")

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
          (emptylist-val))))))

(define let*-prog "let x = 30
                   in let* x = -(x, 1) y = -(x, 2)
                   in -(x, y)")

(test-begin 
  (check-equal? (num-val 2) (run let*-prog)))

;;; (define proc-prog "let x = 2
;;;                    in let f = proc (z) -(z, x) 
;;;                      in let x = 1
;;;                        in let g = proc (z) -(z, x)
;;;                          in -((f 5), (g 5))")
;;; (test-begin 
;;;   (check-equal? (run proc-prog) -1))                         

(define lazy-proc-call-prog "
                        let a = 3
                        in let* p = proc (x) -(x, a) 
                                a = 5
                          in -(a, (p 2))")
(test-begin 
  (check-equal? (run lazy-proc-call-prog) (num-val 8)))                         