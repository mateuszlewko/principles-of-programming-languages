#lang racket

(require (only-in eopl define-datatype))
(require (only-in eopl cases))
(require (only-in eopl list-of))
(require rackunit)

(define report-no-binding-found
  (λ (search-var)
    (error 'apply-env "No binding for ~s" search-var)
  )
)

;;; (define report-invalid-env
;;;   (λ (env)
;;;     (error 'apply-env "Bad environment: ~s" env)
;;;   )
;;; )

;;; eopl 2.5

(define empty-env 
  (λ () '())
)

(define extend-env
  (λ (var val env) 
    (cons (cons var val) env)
  )
)

(define apply-env 
  (λ (env search-var)
    (if (eqv? env (empty-env))    
      (report-no-binding-found search-var)
      (if (eqv? (caar env) search-var)
        (cdar env)
        (apply-env (cdr env) search-var)
      )
    )
  )
)


;;; (displayln "--- eopl 2.5 ---")
;;; (displayln e)
;;; (displayln (apply-env e 'y))
(define e
  (extend-env 'd 6
    (extend-env 'y 8
      (extend-env 'x 7
        (extend-env 'y 14
        (empty-env)
        )
      )
    )
  )
)

(test-begin
  (check-equal? (apply-env e 'y) 8)
  (check-equal? (apply-env e 'd) 6)
)

;;; eopl 2.10
(define extend-env*
  (λ (vars vals env)
    (foldl extend-env env vars vals)
  )
)

(define e2 (extend-env* '(a y) '(1 2) e))

(test-begin
  (check-equal? (apply-env e2 'y) 2)
  (check-equal? (apply-env e2 'a) 1)
)

;;; (displayln "\n--- eopl 2.10 ---")
;;; (displayln e2)

;;; eopl 2.11

;;; ribcage representation

(define rib-empty-env empty-env)

;;; (displayln "\n--- eopl 2.11 ---")

(define rib-extend-env
  (λ (var val env) 
    (if (eqv? env (rib-empty-env))
      (cons (list (list var) (list val)) env)
      (cons
        (list 
          (cons var (caar env)) 
          (cons val (cadar env))
        )
        (cddar env)
      )
    ) 
  )
)

(define rib-extend-env*
  (λ (vars vals env)
    (cons (list vars vals) env)
  )
)

(define rib-find
  (λ (vars vals search-var)
    (if (null? vars)
      #f 
      (if (eqv? (car vars) search-var)
        (car vals)
        (rib-find (cdr vars) (cdr vals) search-var)
      )
    )
  )
)

(define rib-apply-env
  (λ (env search-var)
    (if (eqv? env (rib-empty-env))
      (report-no-binding-found search-var)
      (let ([res (rib-find (caar env) (cadar env) search-var)]) 
        (if (eqv? #f res)
          (rib-apply-env (cdr env) search-var)
          res
        )
      ) 
    )
  )
)

(define rib-e
  (rib-extend-env 'd 6
    (rib-extend-env 'y 8
      (rib-extend-env 'x 7
        (rib-extend-env 'y 14
         (rib-empty-env)
        )
      )
    )
  )
)

(define rib-e* (rib-extend-env* '(a b c) '(1 2 3) rib-e))
(define rib-e2* (rib-extend-env* '(x y z) '(11 21 31) rib-e*))

(test-begin
  (check-equal? rib-e '(((d y x y) (6 8 7 14))))
  (check-equal? rib-e* '(((a b c) (1 2 3)) ((d y x y) (6 8 7 14))))
  (check-equal? (car rib-e) '((d y x y) (6 8 7 14)))
  (check-equal? rib-e2* '(((x y z) (11 21 31)) ((a b c) (1 2 3)) ((d y x y) (6 8 7 14))))
  (check-equal? (rib-apply-env rib-e2* 'x) 11)
  (check-equal? (rib-apply-env rib-e2* 'd) 6)
)

;;; eopl 2.21

(define-datatype d-env d-env?
  (-empty-d-env)
  (-extend-d-env 
    (var symbol?)
    (val number?)
    (d-env d-env?)
  )
)

(define empty-d-env 
  (λ () (-empty-d-env))
)

(define extend-d-env
  (λ (var val env)
    (-extend-d-env var val env)
  )
)

(define search-d-env
  (λ (search-var env)
    (cases d-env env
      (-empty-d-env () 
        #f
      )
      (-extend-d-env (var val env)
        (if (eqv? var search-var)
          val 
          (search-d-env search-var env)
        )
      )
    )
  )
)

(define apply-d-env
  (λ (search-var env)
    (let ([res (search-d-env search-var env)])
      (if (false? res)
        (report-no-binding-found search-var)
        res
      )
    )
  )
)

(define has-binding?
  (λ (search-var env)
    (let ([res (search-d-env search-var env)])
      (if (false? res) #f #t)
    )
  )
)


(define d-e
  (extend-d-env 'd 6
    (extend-d-env 'y 8
      (extend-d-env 'x 7
        (extend-d-env 'y 14
         (empty-d-env)
        )
      )
    )
  )
)

;;; (displayln "\n--- eopl 2.21 ---")
(test-begin 
  (check-equal? (has-binding? 'd d-e) #t)
  (check-equal? (apply-env e2 'y) 2)
  (check-equal? (apply-env e2 'a) 1)
)

;;; eopl 2.28

(define-datatype lc-exp lc-exp?
  (var-exp
   (var symbol?)
  )
  (lambda-exp
   (bound-var symbol?)
   (body      lc-exp?)
  )
  (app-exp
   (rator lc-exp?)
   (rand  lc-exp?)
  )
)

(define unparse
  (λ (exp)
    (cases lc-exp exp
      (var-exp (var)
        (symbol->string var)
      )
      (lambda-exp (bound-var body)
        (format "(lambda (~a) ~a)" bound-var (unparse body))
      )
      (app-exp (rator rand)
        (format "(~a ~a)" (unparse rator) (unparse rand))
      )
    )
  )
)


;;; (displayln "\n--- eopl 2.28 ---")
(define exp 
  (lambda-exp 'x 
    (app-exp
      (var-exp 'f) 
      (app-exp 
        (var-exp 'f)
        (var-exp 'x)
      )
    )
  )
)

(test-begin 
  (check-equal? (unparse exp) "(lambda (x) (f (f x)))")
)

;; eopl 2.29

(define-datatype lc-exps lc-exps?
  (var-exps
   (var symbol?)
  )
  (lambda-exps
   (bound-vars (list-of symbol?))
   (body lc-exps?)
  )
  (app-exps
   (rator lc-exps?)
   (rands (list-of lc-exps?))
  )
)

(define parse-lc-exps 
  (λ (datum)
    (cond 
      ((symbol? datum) (var-exps datum))
      ((pair? datum)
        (if (eqv? (car datum) 'lambda)
          (lambda-exps
            (cadr datum) (parse-lc-exps (caddr datum))
          )
          (app-exps
            (parse-lc-exps (car datum))
            (map parse-lc-exps (cdr datum))
          )
        )
      )
    )
  )
)

;;; (displayln "\n--- eopl 2.29 ---")
(define p (parse-lc-exps '(lambda (a b) (f a b)) ))
(displayln p)

;;; (test-begin 
;;;   (check-equal? 
;;;     (parse-lc-exps '(lambda (a b) (f a b)) )
     
;;;     (lambda-exps 
;;;       (list (var-exps 'a) (var-exps 'b)) 
;;;       (app-exps 
;;;         (var-exps 'f) 
;;;         '((var-exps 'a) (var-exps 'b)) 
;;;       )
;;;     )
;;;   )
;;; )

;;; eopl 2.31
;;; not finished
(define-datatype prefix-exp prefix-exp?
  (const-exp
    (num integer?))
  (diff-exp
    (operand1 prefix-exp?)
    (operand2 prefix-exp?)
  )
)

;;; (define parse-ppn
;;;   (λ (data)
;;;     (if (null? data) 
;;;       '()
;;;       (if (integer? (car data)) 
;;;         (cons (const-exp (car data)) (cdr data))
;;;         (let ([op1 (parse-ppn (cdr data))])
;;;           (let ([op2 (if (null?) parse-ppn (cdr op1))])
;;;             (list (diff-exp (car op1) (car op2)) (cdr op2))
;;;           )
;;;         )
;;;       )
;;;     )
;;;   )
;;; )

;;; type Elem = Int of int | Minus
;;; type Exp = Const of int | Op of Exp * Exp

;;; let rec parse =
;;;   fun data ->
;;;     if data = [] 
;;;     then []
;;;     else 
;;;       match data with 
;;;       | (Int x) :: xs -> (Const x; xs]
;;;       | (Minus) :: xs -> 
;;;         let op1 = parse xs
;;;         let op2 = parse (xs.[1])
;;;         [Op ; ]

;;; (displayln (parse-ppn '(- - 3 2 - 4 - 12 7)))