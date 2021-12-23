;;; Chapter 8 of The Reasoned Schemer: Just a Bit More

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

;;; poso
(defrel (poso n)
        (fresh (a d)
               (== `(,a . ,d) n)))

;;; appendo
(defrel (appendo l t out)
        (conde
          ((nullo l) (== t out))
          ((fresh (a d res)
                  (conso a d l)
                  (conso a res out)
                  (appendo d t res)))))

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

;;; bit-noto
(defrel (bit-noto x r)
        (bit-nando x x r))

;;; bit-ando
(defrel (bit-ando x y r)
        (fresh (s)
                (bit-nando x y s)
                (bit-noto  s r)))

;;; half-addero
(defrel (half-addero x y r c)
        (bit-xoro x y r)
        (bit-ando x y c))

;;; full-addero
(defrel (full-addero b x y r c)
        (fresh (w xy wz)
               (half-addero x y w xy)
               (half-addero w b r wz)
               (bit-xoro xy wz c)))

;;; gen-addero
(defrel (gen-addero b n m r)
        (fresh (a c d e x y z)
               (== `(,a . ,x) n)
               (== `(,d . ,y) m) (poso y)
               (== `(,c . ,z) r) (poso z)
               (full-addero b a d c e)
               (addero e x y z)))

;;; addero
(defrel (addero b n m r)
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

;;; +o
(defrel (+o n m k)
        (addero 0 n m k))

;;; -o
(defrel (-o n m k)
        (+o m k n))

;;; >1o
(defrel (>1o n)
        (fresh (a ad dd)
               (== `(,a ,ad . ,dd) n)))

;;; *o
(defrel (*o n m product)
        (conde
          ; The product of zero and anything is zero.
          ((== '() n) (== '() product))
          ; The product of a positive number and zero is equal to zero.
          ((poso n) (== '() m) (== '() product))
          ; The product of one and a positive number is that number.
          ((== '(1) n) (poso m) (== m product))
          ; The product of a number greater than one and one is the number.
          ((>1o n) (== '(1) m) (== n product))
          ; The product of an even positive number and a number greater than one
          ; is an even positive number,
          ; using the equation: n * m = 2 * (nm / 2 ).
          ; For the recursion to have a value,
          ; one of the argument to *o must shrink.
          ((fresh (x z)
                  ; Dividng n by two shinks n.
                  (== `(0 . ,x) n) (poso x)
                  (== `(0 . ,z) product) (poso z)
                  (>1o m)
                  (*o x m z)))
          ; The product of an odd positive number and an even positive number
          ; is the same as the product of the even posotive number and the odd positive number.
          ((fresh (x y)
                  (== `(1 . ,x) n) (poso x)
                  (== `(0 . ,y) m) (poso y)
                  (*o m n product)))
          ; The product of an odd number greater than one
          ; and another number odd number greater that one
          ; is the result of (odd-*o x n m p), where x is (n - 1) / 2.
          ((fresh (x y)
                  (== `(1 . ,x) n) (poso x)
                  (== `(1 . ,y) m) (poso y)
                  (odd-*o x n m product)))
          ))

;;; odd-*o
;;; When x is an odd number greater than one ( (n - 1) / 2 ),
;;; n * m = 2 * (( (n - 1) / 2) * m) + m.
(defrel (odd-*o x n m p)
        (fresh (q)
               (bound-*o q p n m)
               (*o x m q)
               (+o `(0 . ,q) m p)))

;;; hypothetical bound-*o
(defrel (bound-*o q p n m) succeed)

(run 1 (n m) 
     (*o n m '(1)))

(run 10 (x y r)
     (*o x y r))

(run* p
      (*o '(0 1) '(0 0 1) p))
; The value above is corresponded with ((0 1) (_0 _1 . _2) (0 _0 _1 . _2)),
; a nonground value which means
; the product of two and a number greater than one is twice the number.

(run 1 (x y r)
     (== `(,x ,y ,r) '((1 1) (1 1) (1 0 0 1)))
     (*o x y r))
; Means the product of three and three is nine.

; (run 1 (n m) 
;      (>1o n) 
;      (>1o m)
;      (*o n m '(1 1)))
; no value.
; Because *o keeps tring bigger and bigger number 
; to see if their product is three.
; But there is no bound on how big the number can be, 
; *o tries forever.

;;; final bound-*o
(defrel (bound-*o q p n m) 
        (conde 
          ((== '() q) (poso p))
          ((fresh (a0 a1 a2 a3 x y z)
                  (== `(,a0 . ,x) q)
                  (== `(,a1 . ,y) p)
                  (conde 
                    ((== '() n) 
                     (== `(,a2 . ,z) m)
                     (bound-*o x y z '())) 
                    ((== `(,a3 . ,z) n)
                     (bound-*o x y z m)))))))

(run* p 
      (*o '(1 1 1) '(1 1 1 1 1 1) p))

;;; =lo
(defrel (=lo n m) 
        (conde 
          ((== '() n) (== '() m))
          ((== '(1) n) (== '(1) m))
          ((fresh (a x b y) 
                  (== `(,a . ,x) n) (poso x)
                  (== `(,b . ,y) m) (poso y)
                  (=lo x y)))))

(run* (w x y) 
      (=lo `(1 ,w ,x . ,y) '(0 1 1 0 1)))

(run* b
      (=lo '(1) `(,b)))

(run* n
      (=lo `(1 0 1 . ,n) '(0 1 1 0 1)))

(run 5 (y z) 
     (=lo `(1 . ,y) `(1 . ,z)))

(run 5 (y z) 
     (=lo `(1 . ,y) `(0 . ,z)))

(run 5 (y z) 
     (=lo `(1 . ,y) `(0 1 1 0 1 . ,z)))

;;; <lo
(defrel (<lo n m) 
        (conde 
          ((== '() n) (poso m))
          ((== '(1) n) (>1o m))
          ((fresh (a x b y) 
                  (== `(,a . ,x) n) (poso x)
                  (== `(,b . ,y) m) (poso y)
                  (<lo x y)))))

(run 8 (y z) 
     (<lo `(1 . ,y) `(0 1 1 0 1 . ,z)))

; (run 1 n
;      (<lo n n))
; no value.

;;; <=lo 
(defrel (<=lo n m) 
        (conde 
          ((=lo n m)) 
          ((<lo n m))))

(run 8 (n m) 
     (<=lo n m))

(run 1 (n m) 
     (<=lo n m)
     (*o n '(0 1) m))

(run 10 (n m) 
     (<=lo n m) 
     (*o n '(0 1) m))

;;; <o
(defrel (<o n m) 
        (conde 
          ((<lo n m)) 
          ((=lo n m) 
           (fresh (x) 
                  (poso x)
                  (+o n x m)))))

;;; <=o defined with <o
(defrel (<=o n m) 
        (conde 
          ((== n m))
          ((<o n m))))

(run* q 
      (<o '(1 0 1) '(1 1 1)))
; since five is less than seven.

(run* q 
      (<o '(1 1 1) '(1 0 1)))
; since seven is not less than five.

(run* q
      (<o '(1 0 1) '(1 0 1)))
; since five is not less than five.

(run 6 n
     (<o n '(1 0 1)))
; since (_0 1) represents the numbers two and three.

(run 6 m
     (<o '(1 0 1) m))
; since (_0 _1 _2 _3 . _4) represents all the numbers greater than seven.

; (run* n 
;       (<o n n))
; no value.

;;; /o
(defrel (/o n m q r) 
        (conde 
          ; the dividend n is less than the divisor m,
          ((== '() q) (== n r) (<o n m))
          ; the dividend n is equal to the divisor m.
          ((== '(1) q) (== '() r) (== n m) (<o r m))
          ; the dividend n is greater to the divisor m.
          ((<o m n) (<o r m)
                    (fresh (mq) 
                           ; perform division in terms of multiplication and addition.
                           ; using: n = m * q + r.
                           ; If mq is the product of m and q, 
                           ; then n is the sum of mq and r.
                           (<=lo mq n)
                           (*o m q mq)
                           (+o mq r n)))))

(run* m
      (fresh (r) 
             (/o '(1 0 1) m '(1 1 1) r)))
; Tring to find a number m such that dividing five by m produce seven.

;;; splito
;;; (splito n '() l h) moves the lowest bit† of n, 
;;; if any, into l, and moves the remaining bits of n into h; 
;;; (splito n '(1) l h) moves the two lowest bits of n into l 
;;; and moves the remaining bits of n into h; 
;;; and (splito n '(1 1 1 1) l h), (splito n '(0 1 1 1) l h), 
;;; or (splito n '(0 0 0 1) l h) move the five lowest bits of n into l 
;;; and move  the remaining bits into h; and so on.
;;; Since  splito is a relation, 
;;; it can construct n by combining the lower-order bits of l 
;;; with the higher-order bits of h, 
;;; inserting padding (using the length of r) bits.
(defrel (splito n r l h) 
        (conde 
          ((== '() n) (== '() h) (== '() l)) 
          ((fresh (b n^)
                  (== `(0 ,b . ,n^) n) (== '() r)
                  (== `(,b . ,n^) h) (== '() l))) 
          ((fresh (n^)
                  (== `(1 . ,n^) n) (== '() r)
                  (== n^ h) (== '(1) l)))
          ((fresh (b n^ a r^)
                  (== `(0 ,b . ,n^) n)
                  (== `(,a . ,r^) r) (== '() l)
                  (splito `(,b . ,n^) r^ '() h)))
          ((fresh (n^ a r^)
                  (== `(1 . ,n^) n)
                  (== `(,a . ,r^) r) (== '(1) l)
                  (splito n^ r^ '() h)))
          ((fresh (b n^ a r^ l^)
                  (== `(,b . ,n^) n)
                  (== `(,a . ,r^) r)
                  (== `(,b . ,l^) l)
                  (poso l^)
                  (splito n^ r^ l^ h))) ))

(run* (l h) 
      (splito '(0 0 1 0 1) '( ) l h))

(run* (l h) 
      (splito '(0 0 1 0 1) '(1) l h))

(run* (l h) 
      (splito '(0 0 1 0 1) '(0 1) l h))

(run* (l h) 
      (splito '(0 0 1 0 1) '(1 1) l h))

(run* (r l h) 
      (splito '(0 0 1 0 1) r l h))

;;; Now ready for division! 
;;; If split  n (the divisor) in two parts, nhigh and nlow, 
;;; it stands to reason that q is also split into qhigh and qlow.
;;; Consider: n = m · q + r, 
;;; substituting n = nhigh · 2p + nlow 
;;; and q = qhigh · 2p + qlow 
;;; yields nhigh · 2p + nlow = m · qhigh · 2p + m · qlow + r.

;;; We try to divide  nhigh by m obtaining qhigh and rhigh: 
;;; nhigh = m · qhigh + rhigh 
;;; from which we get nhigh · 2p = m · qhigh · 2p + rhigh · 2p. 
;;; Subtracting from the original, obtain the relation 
;;; nlow = m · qlow + r − rhigh · 2p, 
;;; which means that m · qlow + r − nlow must be divisible by 2p 
;;; and the result is rhigh. 
;;; The advantage is that when checking the latter two equations, 
;;; the numbers nlow, qlow, and so on, are all range-limited, 
;;; and must fit within p bits. 
;;; We can therefore check the equations 
;;; without danger of trying higher and higher numbers forever. 

;;; Improved definition of /o, 
;;; which fails when it determines that the relation connot hold. 
(defrel (/o n m q r) 
        (conde 
          ((== '() q) (== r n) (<o n m))
          ((== '(1) q) (=lo m n) (+o r m n) (<o r m))
          ((poso q) (<lo m n) (<o r m) (n-wider-than-mo n m q r))))

;;; n-wider-than-mo
(defrel (n-wider-than-mo n m q r) 
        (fresh (n_high n_low q_high q_low) 
               (fresh (mq_low mrq_low rr r_high) 
                      (splito n r n_low n_high)
                      (splito q r q_low q_high)
                      (conde 
                        ((== '() n_high) 
                         (== '() q_high)
                         (-o n_low r mq_low)
                         (*o m q_low mq_low))
                        ((poso n_high)
                         (*o m q_low mq_low)
                         (+o r mq_low mrq_low)
                         (-o mrq_low n_low rr)
                         (splito rr r '() r_high)
                         (/o n_high m q_high r_high))))))

(run 3 (y z) 
     (/o `(1 0 . ,y) '(0 1) z '()))

;;; logo
;;; which implements the logarithm relation:
;;; (logo n b q r) holds if n = b^q + r,
;;; where 0 <= r and q is the largest number that satisfies relation.
(defrel (logo n b q r) 
        (conde 
          ((== '() q) (<=o n b) (+o r '(1) n))
          ((== '(1) q) (>1o b) (=lo n b) (+o r b n))
          ((== '(1) b) (poso q) (+o r '(1) n))
          ((== '() b) (poso q) (== r n))
          ((== '(0 1) b)
           (fresh (a ad dd) 
                  (poso dd)
                  (== `(,a ,ad . ,dd) n)
                  (exp2o n '() q)
                  (fresh (s) 
                         (splito n dd r s)))) 
          ((<=o '(1 1) b) (<lo b n) 
                          (base-three-or-moreo n b q r))))

;;; base-three-or-moreo
(defrel (base-three-or-moreo n b q r) 
        (fresh (bw1 bw nw nw1 q_low1 q_low s)
               (exp2o b '() bw1)
               (+o bw1 '(1) bw)
               (<lo q n)
               (fresh (q1 bwq1) 
                      (+o q '(1) q1) 
                      (*o bw q1 bwq1)
                      (<o nw1 bwq1)) 
               (exp2o n '() nw1)
               (+o nw1 '(1) nw)
               (/o nw bw q_low1 s)
               (+o q_low '(1) q_low1)
               (<=o q_low q)
               (fresh (bq_low q_high s qd_high qd)
                      (repeated-mulo b q_low bq_low)
                      (/o nw bw1 q_high s)
                      (+o q_low qd_high q_high)
                      (+o q_low qd q)
                      (<=o qd qd_high)
                      (fresh (bqd bq1 bq)
                             (repeated-mulo b qd bqd)
                             (*o bq_low bqd bq)
                             (*o b bq bq1)
                             (+o bq r n)
                             (<o n bq1)))))

;;; exp2o
(defrel (exp2o n b q)
       (conde 
         ((== '(1) n) (== '() q))
         ((>1o n) (== '(1) q) 
             (fresh (s) 
                    (splito n b s '(1)))) 
         ((fresh (q1 b2) 
                 (== `(0 . ,q1) q) (poso q1) 
                 (<lo b n)
                 (appendo b `(1 . ,b) b2)
                 (exp2o n b2 q1)))
         ((fresh (q1 n_high b2 s) 
                 (== `(1 . ,q1) q) (poso q1)
                 (poso n_high)
                 (splito n b s n_high)
                 (appendo b `(1 . ,b) b2)
                 (exp2o n_high b2 q1)))))

;;; repeated-mulo
(defrel (repeated-mulo n q nq) 
        (conde 
          ((poso n) (== '() q) (== '(1) nq))
          ((== '(1) q) (== n nq))
          ((>1o q) 
           (fresh (q1 nq1) 
                  (+o q1 '(1) q) 
                  (repeated-mulo n q1 nq1)
                  (*o nq1 n nq)))))

(run* r 
      (logo '(0 1 1 1) '(0 1) '(1 1) r))

(run 9 (b q r) 
     (logo '(0 0 1 0 0 0 1) b q r))

;;; expo defined with logo
(defrel (expo b q n) 
        (logo n b q '()))

; (run* t 
;       (expo '(1 1) '(1 0 1) t))

;;; +o defined using conde, ==, <o and /o.
;;; seems no need to use conde, ==, and <o, thanks to /o.
(defrel (++o n m k) (/o k m '(1) n))

(run* k (++o '(1 1) '(1 0 1) k))
; since 3 + 5 = 8.
