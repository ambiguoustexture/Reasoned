;;; Chapter 2 of The Reasoned Schemer: Teaching Old Toys with New Tricks

;;; Implementation of the language used in 'The Reasoned Schemer,
;;; Second Edition,' by Friedman, Byrd, Kiselyov, and Hemann (MIT
;;; Press, 2018).

;;; The implementation of "a complete relational programming language"
;;; on top of Scheme.

(load "10-under-the-hood.scm")

;;; caro
;;; Whereas car expects one argument, caro expects two.
(defrel (caro p a)
        (fresh (d)
               (== (cons a d) p)))

(run* q
      (caro '(a c o r n) q))

(run* q
      (caro '(a c o r n) 'a))

(run* r
      (fresh (x y)
             (caro `(,r ,y) x)
             (== 'pear x)))

(cons
  (car '(grape raisin pear))
  (car '((a) (b) (c))))

(run* r
      (fresh (x y)
             (caro '(grape raisin pear) x)
             (caro '((a) (b) (c)) y)
             (== (cons x y) r)))

(cdr '(grape raisin pear))

(car (cdr (cdr '(a c o r n))))

;;; cdro
(defrel (cdro p d)
        (fresh (a)
               (== (cons a d) p)))
(run* r
      (fresh (v)
             (cdro '(a c o r n) v)
             (fresh (w)
                    (cdro v w)
                    (caro w r))))

(cons
  (cdr '(grape raisin pear))
  (car '((a) (b) (c))) )

(run* r
      (fresh (x y)
             (cdro '(grape raisin pear) x)
             (caro '((a) (b) (c)) y)
             (== (cons x y) r)))

(run* q
      (cdro '(a c o r n) '(c o r n)))

;;; Because (c o r n) is the cdr of (a c o r n).

(run* x
      (cdro '(c o r n) `(,x r n)))

;;; Because (o r n) is the cdr of (c o r n),
;;; so o is associated with x.

(run* l
      (fresh (x)
             (cdro l '(c o r n))
             (caro l x)
             (== 'a x)))
;;; !!!
;;; “because if the cdr of l is (c o r n),
;;; then the list `(,a c o r n) is associated with l,
;;; where a is the variable introduced in the definition of cdro.
;;; The caro of l, a, fuses with x.
;;; When we associate a with x,
;;; we also associate a with a,
;;; so the list (a c o r n) is associated with l.”

;;; conso
(defrel (conso a d p)
        (caro p a)
        (cdro p d))

;;; conso associates the value of (cons '(a b c) '(d e)) with l.
(run* l
      (conso '(a b c) '(d e) l))

(run* x
      (conso x '(a b c) '(d a b c)))
;;; “Since (cons 'd '(a b c)) is (d a b c), conso associates d with x.”

(run* r
      (fresh (x y z)
             (== `(e a d ,x) r)
             (conso y `(a ,z c) r)))

(run* x
      (conso x `(a ,x c) `(d a, x c)))

(run* l
      (fresh (x)
             (== `(d a ,x c) l)
             (conso x `(a ,x c) l)))

(run* l
      (fresh (x)
             (conso x `(a ,x c) l)
             (== `(d a ,x c) l)))

(defrel (conso a d p)
  (== `(,a . ,d) p))

(run* l
      (fresh (d t x y w)
             (conso w '(n u s) t)
             (cdro l t)
             (caro l x)
             (== 'b x)
             (cdro l d)
             (caro d y)
             (== 'o y)))

(null? '(grape raisin pear))

(null? '())

;;;
(defrel (nullo x)
        (== '() x))

(run* q
      (nullo '(grape raisin pear)))

(run* q
      (nullo '()))

(run* x
      (nullo x))

;;;
(pair? '(split . pea))

(pair? '((split) . pea))

(pair? '())

(pair? '(pear ))
;;; It is the pair (pear . ()).

(car '(pear))

(cdr '(pear))

(cons '(split) 'pea)

(run* r
      (fresh (x y)
             (== (cons x (cons y 'salad)) r)))

;;; pairo is not recusive.
(defrel (pairo p)
  (fresh (a d)
         (conso a d p)))

(run* q
      (pairo (cons q q)))

(run* q
      (pairo '()))

(run* q
      (pairo 'pair))

(run* x
      (pairo x))

(run* r
      (pairo (cons r '())))

;;; A singleton is a list of a single value.
;;; singleton? determines if
;;; its argument is a proper list of length one.
(define (singleton? l)
  (cond
   ((pair? l) (null? (cdr l)))
   (else #f)))

(singleton? '((a) (a b) c))

(singleton? '())

(singleton? (cons 'pea '()))

(singleton? '(sauerkraut))

;;;
(define (singleton? l)
  (cond
   ((pair? l) (null? (cdr l)))
   (#t #f)))

;;;
(defrel (singletono l)
  (conde
   ((pairo l)
    (fresh (d)
           (cdro l d)
           (nullo d)))
   (succeed fail)))

;;; “The Translation (Initial)
;;;
;;; To translate a function into a relation,
;;; first replace define with defrel.
;;; Then unnest each expression in each cond line,
;;; and replace each cond with conde.
;;; To unnest a #t, replace it with #s.
;;; To unnest a #f, replace it with #u.”


;;; The expression below is a unnesting of (null? (cdr l)).
;;; First determine the cdr of l and
;;; associate it with the fresh variable d,
;;; and then translate null? to nullo.

(defrel (singletono l)
  (conde
   ((pairo l)
    (fresh (d)
           (cdro l d)
           (nullo d)))))

;;; The Law of #u
;;;
;;; Any conde line that has #u as a top-level goal
;;; cannot contribute values.

(defrel (singletono l)
  (fresh (d)
         (cdro l d)
         (nullo d)))

;;; caro
(defrel (caro p a)
  (fresh (d)
         (conso a d p)))

;;; cdro
(defrel (cdro p d)
  (fresh (a)
         (conso a d p)))

;;; Call with current caro and cdro.
(run* r
      (fresh (x y)
             (cdro '(grape raisin pear) x)
             (caro '((a) (b) (c)) y)
             (== (cons x y) r)))
