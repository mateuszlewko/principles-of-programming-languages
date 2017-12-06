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

(define-datatype proc proc?
  (procedure
   (vars (list-of symbol?))
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
  (array-val
   (p reference?))
)

(define create-array
  (λ (count value)
    (letrec 
      ([alloc
        (λ (count)
          (if (> count 0)
              (let ((new (newref value)))
                (alloc (- count 1)))
              '()
          ))])
      (let ([arr (newref value)])
        (alloc (- count 1))
        arr))))

(define array-at
  (λ (array pos)
    (deref (+ array pos))))

(define array-set!
  (lambda (array pos val)
    (setref! (+ array pos) val)))

(define-datatype environment environment?
  (empty-env)
  (extended-env
   (vars (list-of symbol?))
   (vals vector?)
   (env environment?)))

(define extend-env 
  (λ (var val env) 
    (extended-env (list var) (make-vector 1 val) env)))

(define extend-env-rec*
  (λ (vars vals env)
    (let* ([vec (make-vector (length vars))]
           [env (extended-env vars vec env)])
      (for-each
        (λ (ix val) (vector-set! vec ix (newref val)))
        (range (length vals)) vals
      )
      env
    )
  ))

(define extend-env-value-of-rec*
  (λ (vars vals env)
    (let* ([vec (make-vector (length vars))]
           [env (extended-env vars vec env)])
      (for-each
        (λ (ix val) (vector-set! vec ix (newref (value-of val env))))
        (range (length vars)) vals
      )
      env
    )
  ))


(define proc-lookup 
  (λ (search-var vars vals)
    (findf (λ (x) (eqv? search-var (car x))) 
           (zip vars vals))
  )
)

(define apply-env
  (λ (env search-var)
    (cases environment env
      (empty-env ()
        (report-no-binding-found search-var))

      (extended-env (vars vals-vec saved-env)
        (let ([lookup (proc-lookup search-var vars (vector->list vals-vec))])
          (if lookup
            (cadr lookup)
            (apply-env saved-env search-var)
          )
        )
      )
    )
  )
)

(define execute-statement
  (λ (stmt env)
    (cases statement stmt

      (print-stat (exp)
        (printf "~a\n" (value-of exp env)))

      (declear-statement (var1 val1 vars vals stmt)
        (let ([vars (cons var1 vars)]
              [vals (cons val1 vals)])
          (execute-statement stmt (extend-env-value-of-rec* vars vals env))))

      (if-statement (test-exp true-statement false-statement)
        (let ([val (value-of test-exp env)])
          (if (expval->bool val)
            (execute-statement true-statement)
            (execute-statement false-statement))))

      (set-statement (var exp)
         (setref!
          (apply-env env var)
          (value-of exp env)))

      (block-statement (statements)
        (for-each (λ (stmt) (execute-statement stmt env)) statements))

      (while-statement (exp stmt)
        (exec-while exp stmt env)))))

(define exec-while
  (λ (exp statement env)
    (if (expval->bool (value-of exp env))
      (begin
        (execute-statement statement env)
        (exec-while exp statement env))
      '() 
    )))


(define apply-procedure
  (λ (proc1 args)
    (cases proc proc1
      (procedure (vars body saved-env)
        (let ([new-env (extend-env-rec* vars args saved-env)])
          (value-of body new-env))))))

;; eopl
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

(define expval->array
  (λ (v)
    (cases expval v
	   (array-val (ref) ref)
	   (else (report-expval-extractor-error 'array v)))))


(define value-of
  (λ (exp env)
    (cases expression exp
      (const-exp (num) (num-val num))
      (var-exp (var) (deref (apply-env env var)))

      (diff-exp (exp1 exp2)
        (let ((val1 (value-of exp1 env))
              (val2 (value-of exp2 env)))
          (let ((num1 (expval->num val1))
                (num2 (expval->num val2)))
            (num-val
            (- num1 num2)))))

      (if-exp (exp1 exp2 exp3)
        (let ((val1 (value-of exp1 env)))
          (if (expval->bool val1)
            (value-of exp2 env)
            (value-of exp3 env))))

      (add-exp (exp1 exp2)
        (let ((val1 (value-of exp1 env))
              (val2 (value-of exp2 env)))
          (let ((num1 (expval->num val1))
                (num2 (expval->num val2)))
            (num-val
              (+ num1 num2)))))

      (multi-exp (exp1 exp2)
        (let ((val1 (value-of exp1 env))
              (val2 (value-of exp2 env)))
          (let ((num1 (expval->num val1))
                (num2 (expval->num val2)))
            (num-val
              (* num1 num2)))))

      (zero?-exp (exp1)
        (let ((val1 (value-of exp1 env)))
          (let ((num1 (expval->num val1)))
            (if (zero? num1)
                (bool-val #t)
                (bool-val #f)))))
      (not-exp (exp)
        (let ((val (value-of exp env)))
          (let ((v (expval->bool val)))
            (if v
                (bool-val #f)
                (bool-val #t)))))

      (proc-exp (var body)
        (proc-val (procedure var body env)))

      (call-exp (rator rands)
        (let ((proc (expval->proc (value-of rator env)))
              (args (map (λ(x) (value-of x env)) rands)))
          (apply-procedure proc args)))

      ;; 4.29
      (newarray-exp (count-exp val-exp)
			 (let ([count (expval->num (value-of count-exp env))]
			       [val (value-of val-exp env)])
			   (array-val (create-array count val))))

      (arrayref-exp (exp1 exp2)
        (let ([p (expval->array (value-of exp1 env))]
              [pos (expval->num (value-of exp2 env))])
          (array-at p pos)))

      (arrayset-exp (exp1 exp2 exp3)
        (let ([p (expval->array (value-of exp1 env))]
              [pos (expval->num (value-of exp2 env))]
              [v3 (value-of exp3 env)])
          (array-set! p pos v3)))
)))

(define value-of-program
  (λ (pgm)
    (initialize-store!)
    (cases program pgm
      (a-program (stmt)
        (execute-statement stmt (empty-env))))))

(define run
  (λ (source)
    (value-of-program (scan&parse source))))

(run "
  var x=3; 
  { print +(x,1) }
")

(run "
  var x=3,y=4,z=0;
  {    
      while not(zero?(x))
      {  
          z = +(z,y); 
          x = -(x,1)
      };

      print z
  }
")

(run "
  var f =  proc(x,y) *(x,y), x = 3; 
  {
    print (f 4 x)
  }
")

(run "
  var f = proc(x,y) *(x,y), g = proc(x) (f x 2), x = 3; 
  {
    print (g x)
  }
")

(run "
  var g = proc(x, cnt) (f *(x, 2) cnt), 
      x = 1,
      f = proc(x, cnt) if-exp zero? (cnt) then x else (g x -(cnt, 1)),
      y = 5;
  {
    print (f x y)
  }
")

(run "
  var a = newarray(10, 5), 
      b = newarray(5, 12),
      p = proc (x) arrayset(a, 0, -5);
  {
    print (p 1);
    print +(arrayref(a, 0), arrayref(a, 1));
    print +(arrayref(b, 0), arrayref(a, 1))
  }
")