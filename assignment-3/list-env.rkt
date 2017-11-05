#lang racket

(provide (all-defined-out))

(define report-no-binding-found
  (λ (search-var)
    (error 'apply-env "No binding for ~s" search-var)))

(define empty-env 
  (λ () '()))

(define extend-env
  (λ (var val env) 
    (cons (cons var val) env)))

(define apply-env 
  (λ (env search-var)
    (if (eqv? env (empty-env))    
      (report-no-binding-found search-var)
      (if (eqv? (caar env) search-var)
        (cdar env)
        (apply-env (cdr env) search-var)))))