;;; Chapter 7 of The Reasoned Schemer: A Bit Too Much

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

;;; pairo
(defrel (pairo p)
  (fresh (a d)
         (conso a d p)))

;;; bit-xoro
(defrel (bit-xoro x y r)
        (conde
          ((== 0 x) (== 0 y) (== 0 r))
          ((== 0 x) (== 1 y) (== 1 r))
          ((== 1 x) (== 0 y) (== 1 r))
          ((== 1 x) (== 1 y) (== 0 r))))

;;; bit-nando
(defrel (bit-nando x y r)
        (conde
          ((== 0 x) (== 0 y) (== 1 r))
          ((== 0 x) (== 1 y) (== 1 r))
          ((== 1 x) (== 0 y) (== 1 r))
          ((== 1 x) (== 1 y) (== 0 r))))

;;; bit-xoro
;;; defined with bit-nando
(defrel (bit-xoro x y r)
        (fresh (s t u)
               (bit-nando x y s)
               (bit-nando s y u)
               (bit-nando x s t)
               (bit-nando t u r)))

(run* (x y)
      (bit-xoro x y 0))

(run* (x y)
      (bit-xoro x y 1))

(run* (x y r)
      (bit-xoro x y r))

;;; bit-ando
(defrel (bit-ando x y r)
        (conde
          ((== 0 x) (== 0 y) (== 0 r))
          ((== 0 x) (== 1 y) (== 0 r))
          ((== 1 x) (== 0 y) (== 0 r))
          ((== 1 x) (== 1 y) (== 1 r))))

;;; bit-noto
(defrel (bit-noto x r)
        (bit-nando x x r))

;;; bit-ando
;;; defined with bit-nando
(defrel (bit-ando x y r)
        (fresh (s)
                (bit-nando x y s)
                (bit-noto  s r)))

(run* (x y)
      (bit-ando x y 1))

;;; half-addero
;;; Given the bits x, y, r, and c,
;;; half-addero satisfies x + y = r + 2 * c.
(defrel (half-addero x y r c)
        (bit-xoro x y r)
        (bit-ando x y c))

(run* r
      (half-addero 1 1 r 1))

;;; redefined half-addero
(defrel (half-addero x y r c)
        (conde
          ((== 0 x) (== 0 y) (== 0 r) (== 0 c))
          ((== 0 x) (== 1 y) (== 1 r) (== 0 c))
          ((== 1 x) (== 0 y) (== 1 r) (== 0 c))
          ((== 1 x) (== 1 y) (== 0 r) (== 1 c))))

(run* (x y r c)
      (half-addero x y r c))

;;; full-addero
;;; Given the bits b, x, y, r, and c,
;;; full-addero satisfies b + x + y = r + 2 * c.
(defrel (full-addero b x y r c)
        (fresh (w xy wz)
               (half-addero x y w xy)
               (half-addero w b r wz)
               (bit-xoro xy wz c)))

;;; redefined full-addero
(defrel (full-addero b x y r c)
        (conde
          ((== 0 b) (== 0 x) (== 0 y) (== 0 r) (== 0 c))
          ((== 1 b) (== 0 x) (== 0 y) (== 1 r) (== 0 c))
          ((== 0 b) (== 1 x) (== 0 y) (== 1 r) (== 0 c))
          ((== 1 b) (== 1 x) (== 0 y) (== 0 r) (== 1 c))
          ((== 0 b) (== 0 x) (== 1 y) (== 1 r) (== 0 c))
          ((== 1 b) (== 0 x) (== 1 y) (== 0 r) (== 1 c))
          ((== 0 b) (== 1 x) (== 1 y) (== 0 r) (== 1 c))
          ((== 1 b) (== 1 x) (== 1 y) (== 1 r) (== 1 c))))

(run* (r c)
      (full-addero 0 1 1 r c))

(run* (r c)
      (full-addero 1 1 1 r c))

(run* (b x y r c)
      (full-addero b x y r c))

;;; What is a natural number?
;;; A natural number is an integer greater than or equal to zero.

;;; Each number is represented as list of bits.

;;; The empty list () represents the number zero, but (0) not.
;;; Each nunmber has a unique representation,
;;; therefore (0) cannot also be zero.
;;; Furthermore, (0) does not represent a number.

;;; `(0. ,n) is twice n.
;;; `(1 . ,n) is one more than twice n.

;;; build-num
(define (build-num num)
  (cond
    ((zero? n) '())
    ((even? n)
     (cons 0 (build-num (/ n 2))))
    ((odd? n)
     (cons 1 (build-num (/ (- n 1) 2)))) ))

;;; redefined build-num
(define (build-num n)
  (cond
    ((odd? n)
     (cons 1 (build-num (/ (- n 1) 2))))
    ((and (not (zero? n)) (even? n))
     (cons 0 (build-num (/ n 2))))
    ((zero? n) '())))

;;; For any number n, one and one cond question is true.

;;; poso
;;; (poso r) always succeeds when r is fresh.
(defrel (poso n)
        (fresh (a d)
               (== `(,a . ,d) n)))

(run* q
      (poso '(0 1 1)))

(run* q
      (poso '(1)))

(run* q
      (poso '()))

(run* r
      (poso r))

;;; >1o
(defrel (>1o n)
        (fresh (a ad dd)
               (== `(,a ,ad . ,dd) n)))

(run* q
      (>1o '(0 1 1)))

(run* q
      (>1o '(0 1)))

(run* q
      (>1o '(1)))

(run* q
      (>1o '()))

(run* r
      (>1o r))

;;; gen-addero
;;; addero
;;; given the carry bit b, and the numbers n, m, and r,
;;; gen-addero satisfies b + n + m = r,
;;; provided that n is positive and m and r greater than one.
(defrel (gen-addero b n m r) ; b is a carry bit, and n, m, r are numbers.
        (fresh (a c d e x y z) ; a, c, d, and e are bits, while x, y, and z are numbers.
               (== `(,a . ,x) n)
               (== `(,d . ,y) m) (poso y)
               (== `(,c . ,z) r) (poso z)
               (full-addero b a d c e)
               (addero e x y z)))

(defrel (addero b n m r) ; b is a carry bit, and n, m, r are numbers.
        (conde
          ((== 0 b) (== '() m) (== n r))
          ((== 0 b) (== '() n) (== m r) (poso m))
          ((== 1 b) (== '() m) (addero 0 n '(1) r))
          ((== 1 b) (== '() n) (poso m) (addero 0 '(1) m r))
          ((== '(1) n) (== '(1) m)
          (fresh (a c)
                 (== `(,a ,c) r)
                 (full-addero b 1 1 a c)))
          ((== '(1) n) (gen-addero b n m r))
          ((== '(1) m) (>1o n) (>1o r)
                       (addero b '(1) n r))
          ((>1o n) (gen-addero b n m r))))

(run* s
      (gen-addero 1 '(0 1 1) '(1 1) s))

(run 3 (x y r)
     (addero 0 x y r))
     ; (addero 0 x y r) sums x and y to produce r.

(run 19 (x y r)
     (addero 0 x y r))
; Ground values and nonground values.

;;; The values are the pairs of numbers that sum to five.
(run* (x y)
      (addero 0 x y '(1 0 1)))

;;; +o
(defrel (+o n m k)
        (addero 0 n m k))

(run* (x y)
      (+o x y '(1 0 1)))

;;; -o
(defrel (-o n m k)
        (+o m k n))

(run* q
      (-o '(0 0 0 1) '(1 0 1) q))

(run* q
      (-o '(0 1 1) '(0 0 0 0 1) q))
; negtive numbers not represented.

;;; length
(define (length l)
  (cond
    ((null? l) 0)
    (#t (+ 1 (length (cdr l))))))

;;; lengtho
(defrel (lengtho l n)
        (conde
          ((nullo l) (== '() n))
          ((fresh (d res)
                  (cdro l d)
                  (+o '(1) res n)
                  (lengtho d res)))))

(run 1 n
     (lengtho '(jicama rhubarb guava) n))

(run* ls
      (lengtho ls '(1 0 1)))

(run* q
      (lengtho '(1 0 1) 3))

(run 3 q
     (lengtho q q))

; (run 4 q
;      (lengtho q q))
; no value. since it is still looking for the forth value.

;;; Negative numbers could be represented as `(,sign-bit . ,n),
;;; where n is the representation of natrual numbers.
;;; If sign-bit is 1, then have the negative integers and if it is 0 ...
;;; () still represent zero.
;;; And, sign-bit could be fresh.

;;; sumo
;;; which expects three integres
;;; instead of three natural numbers like +o.

;;; Refrenced from『Reasoned Schemer (92) 符号付き』by kb84tkhr at
;;; https://kb84tkhr.hatenablog.com/entry/2020/02/01/214152
(defrel (sumo n m k)
        (conde
          ((== '() n) (== m k))
          ((== '() m) (pairo n) (== n k))
          ((fresh (ns nn ms mn)
                  (== `(,ns . ,nn) n)
                  (== `(,ms . ,mn) m)
                  (poso nn) (poso mn)
                  (gen-sumo ns nn ms mn k)))))

(defrel (gen-sumo ns nn ms mn k)
        (conde
          ((== ns ms) (fresh (res)
                             (== `(,ns . ,res) k)
                             (+o nn mn res)))
          ((== ns 0) (== ms 1) (diff-sign-sumo ns nn ms mn k))
          ((== ns 1) (== ms 0) (diff-sign-sumo ns nn ms mn k)) ))

(defrel (diff-sign-sumo ns nn ms mn k)
        (fresh (res)
               (conde
                 ((== nn mn) (== '() k))
                 ((poso res) (== `(,ns . ,res) k) (-o nn mn res))
                 ((poso res) (== `(,ms . ,res) k) (-o mn nn res)))))

(run* n (sumo n '(0 1) '(0 0 1)))

