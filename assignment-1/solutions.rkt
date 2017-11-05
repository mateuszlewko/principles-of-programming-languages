#lang racket

(require rackunit)

;;; task 1; eopl 1.21
(define product 
  (λ (xs ys)
    (if (or (null? xs) (null? ys)) 
      '()
      (cons 
        (map (λ (y) (cons y (first ys)))
             xs
        )
        (product (cdr ys) xs)
      )
    )
  )
)

(displayln "--- eopl 1.21 ---")
(product '(a b c) '(x y))

;;; task 2; eopl 1.26
(define up
  (λ (xs)
    (foldr 
      (λ (x res) 
        (if (list? x) 
          (append x res)
          (cons x res)
        )
      ) 
      '() xs
    )
  )
)

(displayln "\n--- eopl 1.26 ---")
(up '((1 2) (3 4)) )
(up '((x (y)) z) )

;;; task 3; eopl 1.28
(define merge
  (λ (xs ys)
    (if (or (null? xs) (null? ys))
      (append xs ys)
      (if (<= (first xs) (first ys))
        (cons (first xs) (merge (cdr xs) ys))
        (cons (first ys) (merge (cdr ys) xs))
      )
    )
  )
)

(displayln "\n--- eopl 1.28 ---")
(merge '(1 4) '(1 2 8))
(merge '(35 62 81 90 91) '(3 83 85 90))

;;; task 4; eopl 1.30
(define sort/predicate
  (λ (pred loi)
    (if (<= (length loi) 1)
      loi 
      (let-values ([(fst snd) (partition (λ (x) (pred x (first loi))) 
                                         (cdr loi))
                   ]) 
          (append (sort/predicate pred fst)
                  (list (first loi))
                  (sort/predicate pred snd)
          )
      )
    )
  )
)

(displayln "\n--- eopl 1.30 ---")
(sort/predicate < '(8 2 5 2 3))
(sort/predicate > '(8 2 5 2 3))

;;; task 5; eopl 1.34
(define path 
  (λ (n bst)
    (if (or (null? bst) (= n (first bst)))
      '()
      (if (<= n (first bst))
        (append '(left) (path n (cadr bst)))
        (append '(right) (path n (caddr bst)))
      )
    )
  )
)

(displayln "\n--- eopl 1.34 ---")
(path 17 '(14 (7 () (12 () ()))
              (26 (20 (17 () ())
                      ())
                  (31 () ()))))

;;; task 6 - at the end

;;; task 7
(define fact
  (let 
    ( [f 
        (λ (g) 
          (λ (n)
            (if (= n 0)
              1
              (* n ((g g) (- n 1))) ;; added g
            )
          )
        )
      ]
    )
    (f f)
    ;;; (λ (n) ((f fact) n)) ;; added this
  )
)

(displayln "\n--- task 7 ---")
(displayln (fact 3))
(displayln (fact 5))

;;; task 8 
(define fix
  (λ (fn) 
    (λ (arg) 
      ((fn (fix fn)) arg)
    )
  )
)

(define fact-maker
  (λ (h)
    (λ (n)
      (if (= n 0)
        1
        (* n (h (- n 1)))))))

(define fact-with-fix (fix fact-maker))

(displayln "\n--- task 8 ---")
(displayln (fact-with-fix 3))
(displayln (fact-with-fix 5))

;;; task 6

;;; (define exp-maker
;;;   (λ (h)
;;;     (λ (n k)
;;;       (if (= k 0)
;;;         1
;;;         (* n (h n (- k 1)))
;;;       )
;;;     )
;;;   )
;;; )

;;; (define exp-fix
;;;   (λ (fn) 
;;;     (λ (n k) 
;;;       ((fn (exp-fix fn)) n k)
;;;     )
;;;   )
;;; )

(define exp
  (λ (k)
    (if (= k 0)
      (λ (n) 1)

      (λ (n) ((exp (- k 1)) n))
    )
  )
)

(displayln ((exp 10) 2))

(test-begin 
  (check-equal? ((exp 10) 2) 1024)
)

;;; (define exp (exp-fix exp-maker))
;;; (displayln (exp 2 5))
;;; (displayln (exp 2 0))
