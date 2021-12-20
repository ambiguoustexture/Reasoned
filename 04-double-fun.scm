;;; Chapter 4 of The Reasoned Schemer: Double Your Fun

;;; Implementation of the language used in 'The Reasoned Schemer,
;;; Second Edition,' by Friedman, Byrd, Kiselyov, and Hemann (MIT
;;; Press, 2018).
(load "10-under-the-hood.scm")

;;; conso
(defrel (conso a d p)
  (== `(,a . ,d) p))

;;; caro
(defrel (caro p a)
  (fresh (d)
         (conso a d p)))

;;; cdro
(defrel (cdro p d)
  (fresh (a)
         (conso a d p)))

;;; nullo
(defrel (nullo x)
  (== '() x))

;;; append
(define (append l t)
  (cond
    ((null? l) t)
    (#t (cons (car l)
              (append (cdr l) t)))))

(append '(a b c) '(d e))

(append '(a b c) '())

(append '() '(d e))

; (append 'a '(d e))
; no meaning.
; The object a, passed as the first argument to cdr,
; is not the correct type.

(append '(d e) 'a)
; Value: (d e . a)

;;; appendo
;;; Introduces additional argument, called out,
;;; that holds the value that would have been produced by
;;; append's value.
(defrel (appendo l t out)
        (conde
          ((nullo l) (== t out))
          ((fresh (res a d)
                  (conso a d l) ; appears to associate values with the variables a and d.
                  (appendo d t res)
                  (conso a res out) ))
          ))

;;; The Translation (Final)

;;; To translate a function into a relation,
;;; first replace define with defrel.
;;; Then unnest expression in each cond line,
;;; and replace each cond line with conde.
;;; To unnest a #t, replace it with #s.
;;; To unnest a #f, replace it with #u.
;;;
;;; If the value of at least one cond line can be a non-Boolean,
;;; add an argument, say out,
;;; to defrel to hold what would have been the function's value.
;;; When unnesting a line whose value is not a Boolean,
;;; ensure that either some value is associated with out,
;;; or that out is the last argument to a recursion.

;;; TBD
;;; redefine loso, lolo and proper-membero.

(run 6 x
     (fresh (y z) 
            (appendo x y z)))

(run 6 y
     (fresh (x z) 
            (appendo x y z)))

(run 6 z
     (fresh (x y)
     (appendo x y z)))

(run 6 (x y z) 
     (appendo x y z))

(run* x 
      (appendo 
        '(cake) 
        '(tastes yummy)
        x))

(run* x
      (fresh (y) 
             (appendo 
               `(cake & ice ,y) 
               '(tastes yummy) 
               x)))

(run* x
      (fresh (y) 
             (appendo 
               `(cake & ice cream)
               y
               x)))

(run 1 x 
     (fresh (y) 
            (appendo 
              `(cake & ice . ,y)
              '(d t)
              x)))
; because the successful (nullo y) 
; associates the empty list with y.

(run 5 y 
     (fresh (x) 
            (appendo 
              `(cake & ice . ,y)
              '(d t)
              x)))

(run 5 x 
     (fresh (y) 
            (appendo 
              `(cake & ice . ,y)
              `(d t . ,y)
              x)))

(run* x
      (fresh (z) 
             (appendo 
               '(cake & ice cream)
               `(d t . ,z)
               x)))

(run 6 x
     (fresh (y) 
            (appendo x y '(cake & ice d t))))
(run 6 y
     (fresh (x) 
            (appendo x y '(cake & ice d t))))

(run 6 (x y) 
     (appendo x y '(cake & ice d t)))

; (run 7 (x y) 
;      (appendo x y '(cake & ice d t)))
; no value, since appendo is still looking for the 7th value.

(defrel (appendo l t out) 
        (conde 
          ((nullo l) (== t out))
          ((fresh (a d res) 
                  (conso a d l)
                  (conso a res out)
                  (appendo d t res)))))

(run* (x y) 
      (appendo x y '(cake & ice d t)))

;;; The First Commandment
;;; 
;;; Within each sequence of goals, 
;;; move non-recursive goals before recursive goals.

;;; swappendo
;;; which is just appendo with its tow conde lines swapped.
(defrel (swappendo l t out) 
        (conde 
          ((fresh (a d res) 
                  (conso a d l) 
                  (conso a res out)
                  (swappendo d t res))) 
          ((nullo l) (== t out))))

(run* (x y) 
      (swappendo x y '(cake & ice d t)))

;;; The Law of Swapping conde lines
;;;
;;; Swapping two conde lines does not affect the values 
;;; contributed by conde.

(define (unwrap x) 
  (cond 
    ((pair? x) (unwrap (car x)))
    (#t x)))

(unwrap '((((pizza)))) )

(unwrap '((((pizza pie) with)) garlic))

;;; unwrapo
(defrel (unwrapo x out)
        (conde 
          ((fresh (a) 
                  (caro x a) 
                  (unwrapo a out))) 
          ((== x out))))

(run* x 
      (unwrapo '(((pizza))) x))

(run* x
      (unwrapo '((((pizza pie) with)) garlic) x))

(run 1 x 
     (unwrapo x 'pizza))

(run 5 x 
     (unwrapo x 'pizza))

(run 5 x
     (unwrapo x '((pizza))))

(run 5 x
     (unwrapo `((,x)) 'pizza))

