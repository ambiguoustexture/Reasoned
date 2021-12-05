;;; Chapter 1 of The Reasoned Schemer: Playthings

;;; Implementation of the language used in 'The Reasoned Schemer,
;;; Second Edition,' by Friedman, Byrd, Kiselyov, and Hemann (MIT
;;; Press, 2018).

;;; The implementation of "a complete relational programming language"
;;; on top of Scheme.

(load "10-under-the-hood.scm")

(run* q
      (== q 'pea))

(run* q
      (== 'pea q))
;;; The order of arguments to `==` does notn matter.

;;; The First Law of ==
;;; (== v w) can be replaced by (== w v).

(run* q succeed)

(run* q
      (== 'pea 'pea))

(run* q
      (== q q))

(run* q
      (fresh (x)
             (== 'pea q)))

(run* q
      (fresh (x)
             (== 'pea x)))

(run* q
      (fresh (x)
             (== (cons x '()) q)))

(run* q
      (fresh (x)
             (== `(,x) q)))
;;; `(,x) is a shorthand for (cons x '()).

(run* q
      (fresh (x)
             (== x q)))

(run* q
      (== '(((pea)) pod) '(((pea)) pod)) )

(run* q
      (== `((( pea)) pod) `(((pea)) ,q)))

(run* q
      (== `(((,q)) pod) '(((pea)) pod)))

(run* q
      (fresh (x)
             (== `(((,q)) pod)
                 `(((,x)) pod) )))

(run* q
      (fresh (x)
             (== `(((,q)) ,x)
                 `(((,x)) pod))))

(run* q
      (fresh (x)
             (== `(,x ,x) q)))

(run* q
      (fresh (x)
             (fresh (y)
             (== `(,q ,y) `((,x ,y) ,x)))))

(run* q
      (fresh (x) 
             (== 'pea q)))

(run* q
      (fresh (x) 
             (fresh (y) 
                    (== `(,x ,y) q) )))

(run* s 
      (fresh (t) 
             (fresh (u) 
                    (== `(,t ,u) s) )))

(run* q
      (fresh (x) 
             (fresh (y) 
                    (== `(,x ,y ,x) q))))

(== '(pea) 'pea)

(== '(,x) 'x)

;;; The Second Law of ==
;;; If x is fresh, then (== v x) succeeds and associates v with x,
;;; unless x occurs in v.

;;; conj2 is short for "two-argument conjunction".
(run* q
      (conj2 succeed succeed))

(run* q
      (conj2 succeed (== 'corn q)))

(run* q
      (conj2 fail  (== 'corn q)))

(run* q
      (conj2 (== 'corn q) (== 'meal q)))

(run* q
      (conj2 (== 'corn q) (== 'corn q)))

;;; disj2 is short for "two-argument disjunctioin".
(run* q
      (disj2 fail fail))

(run* q
      (disj2 (== 'olive q) fail))

(run* q
      (disj2 fail (== 'oil q)))

(run* q
      (disj2 (== 'olive q) (== 'oil q)))

(run* q
      (fresh (x) 
             (fresh (y) 
                    (disj2 
                      (== `(,x ,y) q)
                      (== `(,y ,x) q)))))

(run* x
      (disj2 (== 'olive x) (== 'oil x)))

(run* x 
      (disj2 (== 'oil x) (== 'olive x)))

(run* x
      (disj2 
        (conj2 (== 'olive x) fail)
        (== 'oil x)))

(run* x
      (disj2
        (conj2 (== 'olive x) succeed)
        (== 'oil x)))

(run* x
      (disj2 
        (== 'oil x)
        (conj2 (== 'olive x) succeed)))

(run* x
      (disj2 
        (conj2 (== 'virgin x) fail)
        (disj2 (== 'olive x)  (disj2 succeed (== 'oil x)))))

(run* r
      (fresh (x) 
             (fresh (y) 
                    (conj2 
                      (== 'split x)
                      (conj2 
                        (== 'pea y)
                        (== `(,x ,y) r))))))

(run* r 
      (fresh (x) 
             (fresh (y) 
                    (conj2 
                      (conj2 (== 'split x)
                             (== 'pea   y))
                      (== `(,x ,y) r)))))

(run* r
      (fresh (x y) 
             (conj2 
               (conj2 
                 (== 'split x)
                 (== 'pea   y)) 
               (== `(,x ,y) r))))

(run* (r x y) 
      (conj2 
        (conj2 
          (== 'split x)
          (== 'pea   y))
        (== `(,x ,y) r)))

(run* (x y) 
      (conj2 
        (== 'split x)
        (== 'pea   y)))

(run* (x y) 
      (disj2 
        (conj2 (== 'split x) (== 'pea y))
        (conj2 (== 'red   x) (== 'bead y))))

(run* r
      (fresh (x y) 
             (conj2
               (disj2 
                 (conj2 (== 'split x) (== 'pea  y))
                 (conj2 (== 'red x)   (== 'bean y)))
               (== `(,x ,y soup) r))))

(run* r
      (fresh (x y) 
             (disj2
               (conj2 (== 'split x) (== 'pea y))
               (conj2 (== 'red x)   (== 'bean y)))
             (== `(,x ,y soup) r)))

;;; (fresh (x ...)
;;;        (conj2 
;;;          g1 
;;;          (conj2 g2 g3)))

;;; (fresh (x ...) 
;;;        (g1 g2 g3))

(run* (x y z) 
      (conj2 
        (disj2
          (conj2 (== 'split x) (== 'pea  y))
          (conj2 (== 'red x)   (== 'bean y))) 
        (== 'soup z)))

;;; run* can have more than one goal and act like a conj2, just like fresh.
(run* (x y z) 
      (disj2 
        (conj2 (== 'split x) (== 'pea  y))
        (conj2 (== 'red x)   (== 'bean y)))
      (== 'soup z))

(run* (x y) 
      (conj2 
        (== 'split x)
        (== 'pea y)))

(run* (x y) 
      (== 'split x)
      (== 'pea   y))

;;; the name "defrel" is short for "define relation".
(defrel (teacupo t)
        (disj2 (== 'tea t) (== 'cup t)))

(define (teacupo t) 
  (lambda (s) 
    (lambda () 
      ((disj2 (== 'tea t) (== 'cup t)) s))))

;;; A relation is a kind of function that,
;;; when given arguments, produces a goal.
(run* x 
      (teacupo x))

(run* (x y) 
      (disj2 
        (conj2 (teacupo x) (== #t y)) 
        (conj2 (== #f x)  (== #t y))))
;;; ???
;;; “First (== #f x) associates #f with x, 
;;; then (teacupo x) associates tea with x, and 
;;; finally (teacupo x) associates cup with x.”

(run* (x y) 
      (teacupo x)
      (teacupo x))

;;; “The first (teacupo x) associates tea with x and 
;;; then associates cup with x, 
;;; while the second (teacupo x) already has the correct associations for x, 
;;; so it succeeds without associating anything. 
;;; y remains fresh.”

(run* (x y) 
      (disj2 
        (conj2 (teacupo x) (teacupo x))
        (conj2 (== #f x)   (teacupo y))))

;;; “The run* expression in the previous frame has a pattern 
;;; that appears frequently: 
;;; a disj2 containing conj2s. 
;;; This pattern appears so often 
;;; that introduce a new form, conde.”
;;; “'e' stands for every, 
;;; since every successful conde line 
;;; contributes one or more values.”

(run* (x y) 
     (conde 
       ((teacupo x) (teacupo x))
       ((== #f x)   (teacupo y))))

(run* (x y) 
      (conde 
        ((== 'split x) (== 'pea  y))
        ((== 'red x)   (== 'bean y))))

(run* (x y) 
      (disj2 
        (conj2 (== 'split x) (== 'pea  y))
        (conj2 (== 'red   x) (== 'bean y))))

(run* x
      (disj2 
        (conj2 (== 'olive x) fail) 
        (== 'oil x)))

(run* x
      (conde 
        ((== 'olive x) fail)
        ((== 'oil   x))))

(run* (x y) 
      (conde 
        ((fresh (z) (== 'lentil z))) 
        ((== x y)) ))

(run* (x y) 
      (conde 
        ((== 'split x) (== 'pea    y))
        ((== 'red x)   (== 'bean   y))
        ((== 'green x) (== 'lentil y)) ))

;;; “disj2 and conj2 are unnecessary.”

;;; The Law of conde
;;; Every successful conde line contributes one or more values.
