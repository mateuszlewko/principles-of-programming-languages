#lang eopl

(require (only-in racket displayln))
(require (only-in racket λ))
(require (only-in racket error))
(require (only-in racket foldl))


(provide (all-defined-out))

(define report-no-binding-found
  (λ (search-var)
    (error 'apply-env "No binding for ~s" search-var)))

(define empty-env 
  (λ () '()))

(define extend-env
  (λ (var val env) 
    (cons (cons var val) env)))

(define extend-env*
  (λ (vars vals env)
    (foldl extend-env env vars vals)))

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
  
(define environment? list?)


;;; (define-datatype environment environment?
;;;   (empty-env-val)
;;;   (extend-env-val 
;;;     (var symbol?)
;;;     (val number?)
;;;     (environment environment?)
;;;   )
;;; )

;;; (define-datatype not-found not-found?
;;;   (not-found-val))

;;; (define empty-env 
;;;   (λ () (empty-env-val)))

;;; (define extend-env
;;;   (λ (var val env)
;;;     (extend-env-val var val env)))

;;; (define search-env
;;;   (λ (search-var env)
;;;     (cases environment env
;;;       (empty-env-val () (not-found-val))
;;;       (extend-env-val (var val env)
;;;         (if (eqv? var search-var)
;;;           val 
;;;           (search-env search-var env)
;;;         )
;;;       )
;;;     )
;;;   )
;;; )

;;; (define apply-env
;;;   (λ (search-var env)
;;;     (let ([res (search-env search-var env)])
;;;       (if (eqv? res (not-found-val))
;;;         (report-no-binding-found search-var)
;;;         res
;;;       ))))

;;; (define has-binding?
;;;   (λ (search-var env)
;;;     (let ([res (search-d-env search-var env)])
;;;       (if (false? res) #f #t)
;;;     )
;;;   )
;;; )