;;; Chapter 3 of The Reasoned Schemer: Seeing Old Friends in New Ways

;;; Implementation of the language used in 'The Reasoned Schemer,
;;; Second Edition,' by Friedman, Byrd, Kiselyov, and Hemann (MIT
;;; Press, 2018).

;;; The implementation of "a complete relational programming language"
;;; on top of Scheme.

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

(define (list? l)
  (cond
   ((null? l) #t)
   ((pair? l) (list? (cdr l)))
   (#t #f) ))

(list? '((a) (b) (c)))

(list? '())

(list? 's)

(list? '(d a t e . s))

(defrel (listo l)
  (conde
   ((nullo l) succeed)
   ((pairo l)
    (fresh (d)                          ; An unnseting of (list? (cdr l)).
           (cdro l d)                   ; First determine the cdr of l and
           (listo d)))                  ; associate it with the fresh variable d, and
                                        ; then use d as the argument in the recursion.
   (succeed fail)))

;;; Simplidied
;;; conde lines that have #u as a top-level goal
;;; cannot contribute values.
(defrel (listo l)
  (conde
   ((nullo l) succeed)
   ((fresh (d)
           (cdro l d)
           (listo d)))))

;;; Further simplidied
;;; Any top-level #s can be removed from a conde line.
(defrel (listo l)
  (conde
   ((nullo l))
   ((fresh (d)
           (cdro l d)
           (listo d)))))

;;; The Law of #s
;;;
;;; Any top-level #s can be removed from a conde line.

(run* x
      (listo `(a b ,x d)))
;;; Where a, b, and d are symbols, and x is a variable,
;;; listo gets the cdr of each pair, and
;;; then uses recursion on that cdr.
;;; When listo reaches the end of `(a b ,x d),
;;; it succeeds because (nullo '()) succeeds,
;;; thus leaving x fresh.

;;; A expression which has no value.
;;; (run* x
;;;       (listo `(a b c . ,x)))

;;; Along with the arguments run* expects,
;;; run also expects a positive number n.
;;; If the run expression has a value,
;;; its value is a list of at most n elements.
(run 1 x
     (listo `(a b c . ,x)))
;;; When listo reaches the end of `(a b c . ,x),
;;; (nullo x) succeeds and associates x with the empty list.

(run 5 x
     (listo `(a b c . ,x)))

;;; Each _n corresponds to a fresh variable
;;; that has been introduced in the goal of
;;; the second conde line of listo.

;;; If run* produces a list,
;;; then run n either produces the same list,
;;; or a prefix of that list.

;;; lol?
;;; Which stands for list-of-list?.
;;; As long as
;;; each top-level value in the list l
;;; is a proper list, lol? produces #t.
;;; Otherwise, lol? produces #f.
(define (lol? l)
  (cond
   ((null? l) #t)
   ((list? (car l)) (lol? (cdr l)))
   (#t #f)))

;;; lolo
(defrel (lolo l)
  (conde
   ((nullo l) succeed)
   ((fresh (a)
           (caro l a)
           (listo a))
    (fresh (d)
           (cdro l d)
           (lolo d)))
   (succeed fail)))

;;; simplidied lolo
(defrel (lolo l)
  (conde
   ((nullo l))
   ((fresh (a)
           (caro l a)
           (listo a))
    (fresh (d)
           (cdro l d)
           (lolo d)))))

(run* q
      (fresh (x y)
             (lolo `((a b) (,x c) (d ,y)))))

(run 1 l
     (lolo l))

(run 1 q
     (fresh (x)
            (lolo `((a b) . ,x))))

(run 1 x
     (lolo `((a b) (c d) . ,x)))

(run 5 x
     (lolo `((a b) (c d) . ,x)))

;;; ((a b) (c d) . (() ())) is the same as ((a b) (c d) () ()).

(run 5 x
     (lolo x))

;;; singletono
(defrel (singletono l)
  (fresh (d)
         (cdro l d)
         (nullo d)))

(defrel (singletono l)
  (fresh (a)
         (== `(,a) l)))

;;; loso
;;; Which stands for list of singletons.
(defrel (loso l)
  (conde
   ((nullo l))
   ((fresh (a)
           (caro l a)
           (singletono a))
    (fresh (d)
            (cdro l d)
            (loso d)))))

(run 1 z
     (loso `((g) . ,z)))
;;; The variable l from the definition of loso
;;; starts out as the list `((g) . ,z).
;;; Since this list is not null,
;;; (nullo l) fails and we determine the values
;;; contributed from the second conde line.
;;; In the second conde line, d is fused with z,
;;; the cdr of `((g) . ,z).
;;; The variable d is then passed in the recursion.
;;; Since the variables d and z are fresh,
;;; (nullo l) succeeds and associates () with d and z.

(run 5 z
     (loso `((g) . ,z)))

(run 4 r
     (fresh (w x y z)
            (loso `((g) (e . ,w) (,x . ,y) . ,z))
            (== `(,w (x . ,y) ,z) r)))

(run 3 out
     (fresh (w x y z)
            (== `((g) (e . ,w) (,x . ,y) . ,z) out)
            (loso out)))

;;; member?
(define (member? x l)
  (cond
   ((null? l) #f)
   ((equal? (car l) x) #t)
   (#t (member? x (cdr l)))))

(member? 'olive '(virgin olive oil))

;;; membero
(defrel (membero x l)
  (conde
   ((nullo l) fail)
   ((fresh (a)
           (caro l a)
           (== a x)) succeed) ; equal? unnests to ==.
   (succeed
    (fresh (d)
           (cdro l d)
           (membero x d)))))

;;; simplidied membero
(defrel (membero x l)
  (conde
   ((fresh (a)
           (caro l a)
           (== a x)))
   ((fresh (d)
           (cdro l d)
           (membero x d)))))

;;; further simplidied membero
(defrel (membero x l)
  (conde
   ((caro l x))
   ((fresh (d)
           (cdro l d)
           (membero x d)))))

(run* q
      (membero `olive `(virgin olive oil)))

(run 1 y
     (membero y '(hummus with pita)))

(run 1 y
     (membero y '(with pita)))

(run 1 y
     (membero y '(pita)))

(run* y
     (membero y '()))

(run* y
      (membero y '(hummus with pita)))

(run* y
      (membero y '(pear grape . peaches)))
;;; `(pear grape . peaches) is not a proper list.

(run* x
      (membero 'e `(pasta ,x fagioli)))
;;; The list contains three values
;;; with a variable in the middle.
;;; membero determines
;;; that e is associated with x.
;;; Cause e is the only value
;;; that can be associated with x
;;; so that (membero 'e `(pasta ,x fagioli)) succeeds.
;;; A.K.A, filled in a blank in the list
;;;so that membero succeeds.

(run 1 x
     (membero 'e `(pasta e ,x fagioli)))
;;; Because the recursion reaches e, and succeeds, before it gets to x.

(run 1 x
     (membero 'e `(pasta ,x e fagioli)))
;;; Because the recursion reaches x, and succeeds, before it gets to e.

(run* (x y)
      (membero 'e `(pasta ,x fagioli ,y)))
;;; There are two values in the list.
;;; For the first value when  e is associated with x,
;;; (membero 'e `(pasta ,x fagioli ,y)) succeeds,
;;; leaving y fresh.
;;; Then determine the second value.
;;; Here, e is associated with y,
;;; while leaving x fresh.”

(run* q
      (fresh (x y)
             (== `(pasta ,x fagioli ,y) q)
             (membero `e q)))

(run 1 l
     (membero 'tofu l))
;;; The value of expression above stands for
;;; every list whose car is tofu.

;;; A expression which has no value.
;;; For run* never finishes building the list.
;;; (run* l
;;;       (membero 'tofu l))

(run 5 l
     (membero 'tofu l))

;;; Suppose l is a proper list.
;;; Any proper list could be l’s cdr.

;;; proper-membero
;;; Which the cdr of l in the first conde line
;;; must be a proper list.
(defrel (proper-membero x l)
  (conde
   ((caro l x)
    (fresh (d)
           (cdro l d)
           (listo d)))
   ((fresh (d)
           (cdro l d)
           (proper-membero x d)))))

(run 12 l
     (proper-membero 'tofu l))

;;; de-translate
(define (proper-member? x l)
  (cond
   ((null? l) #f)
   ((equal? (car l) x) (list? (cdr l)))
   (#t (proper-member? x (cdr l)))))
