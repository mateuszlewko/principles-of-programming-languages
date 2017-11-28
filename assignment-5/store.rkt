;; task 4.9
#lang eopl

(require (only-in racket displayln))
(require (only-in racket λ))
(require (only-in racket error))
(require (only-in racket foldl))
;;; (require (only-in racket make-gvector))
;;; (require (only-in racket gvector?))
(require data/gvector)

(provide (all-defined-out))

(define store? gvector?)
(define reference? integer?)

(define empty-store make-gvector)

(define newref!
  (λ (val store) 
    (gvector-add! store val) 
    (gvector-count store)))

(define deref
  (λ (ref store) (gvector-ref store ref)))

(define setref!
  (λ (ref val store) (gvector-set! store ref val)))

;;; (define get-store-as-list
;;;   (lambda (store)
;;;     (gvector->list store)))