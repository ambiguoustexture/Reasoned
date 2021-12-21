;;; Chapter 5 of The Reasoned Schemer: Members Only

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

(define (mem x l) 
  (cond 
    ((null? l) #f)
    ((equal? (car l) x) l)
    (#t (mem x (cdr l)))))

(mem 'fig
     '(roll okra fig beet roll pea))

(mem 'fig
     '(roll okra beet beet roll pea))

(mem 'roll 
     (mem 'fig
          '(roll okra fig beet roll pea)))

;;; memo
(defrel (memo x l out) 
        (conde 
          ((caro l x) (== l out))
          ((fresh (d) 
                  (cdro l d) 
                  (memo x d out)))))

(run* q 
      (memo 'fig '(pea) '(pea)))

(run* out 
      (memo 'fig '(fig pea) out))

(run* r
      (memo r
            '(rool okra fig beet fig pea)
            '(fig beet fig pea) ))

(run* x 
      (memo 'fig '(fig pea) `(pea ,x)))

(run* x
      (memo 'fig '(fig pea) `(,x pea)))

(run* out 
      (memo 'fig '(beet fig pea) out))

(run 1 out 
     (memo 'fig '(fig fig pea) out))

(run* out 
      (memo 'fig '(fig fig pea) out))

(run* out 
      (fresh (x) 
             (memo 'fig `(a ,x c fig e)
                   out)))

(run 5 (x y) 
     (memo 'fig `(fig d fig e . ,y) x))

;;; rember
(define (rember x l) 
  (cond 
    ((null? l) '())
    ((equal? (car l) x) (cdr l))
    (#t (cons (car l) 
              (rember x (cdr l))))))

(rember 'pea '(a b pea d pea e))

;;; rembero
(defrel (rembero x l out) 
        (conde 
          ((nullo l) (== '() out))
          ((conso x out l))
          ((fresh (a d res) 
                  (conso a d l) 
                  (conso a res out)
                  (rembero x d res)))))

(run* out 
      (rembero 'pea '(pea) out))

(run* out 
      (rembero 'pea '(pea pea) out))

(run* out 
     (fresh (y z) 
            (rembero y `(a b ,y d ,z e) 
                     out)))
; In order to remove a, a is associated with y.
; The value of the y in the list is a.
; And, in order to remove b from the list, b is associated with y.
; The value of the y in the list is b.

(run* (y z) 
      (rembero y `(,y d ,z e) `(,y d e)))

(run 4 (y z w out) 
     (rembero y `(,z . ,w) out))

(run 5 (y z w out) 
     (rembero y `(,z . ,w) out))

