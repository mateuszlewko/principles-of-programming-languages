#lang eopl

(require (only-in racket displayln))
(require (only-in racket λ))
(require (only-in racket error))
(require (only-in racket foldl))

(provide (all-defined-out))

(define report-no-binding-found
  (λ (search-var)
    (error 'apply-env "No binding for ~s" search-var)))

(define-datatype environment environment?
  (empty-env)

  (extend-env
   (var symbol?)
   (val expval?)
   (saved-env environment?))

  (extend-env-rec
   (ids (list-of symbol?))
   (vars (list-of symbol?))
   (bodies (list-of expression?))
   (saved-env environment?))
)

;;; (define empty-env (λ () (empty-env)))

;;; (define extend-env
;;;   (λ (var val env) 
;;;     (cons (cons var val) env)))

;;; (define extend-env*
;;;   (λ (vars vals env)
;;;     (foldl extend-env env vars vals)))

(define apply-env 
  (λ (env search-var)
    (if (eqv? env (empty-env))    
      (report-no-binding-found search-var)
      (if (eqv? (caar env) search-var)
        (cdar env)
        (apply-env (cdr env) search-var)))))

(define has-binding?
  (λ (env search-var)
    (if (eqv? env (empty-env))    
      #f
      (if (eqv? (caar env) search-var)
        #t
        (has-binding? (cdr env) search-var)))))
  
;;; (define environment? list?)
