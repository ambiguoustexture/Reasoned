;;; Chapter 9 of The Reasoned Schemer: Thin ice

;;; Implementation of the language used in 'The Reasoned Schemer,
;;; Second Edition,' by Friedman, Byrd, Kiselyov, and Hemann (MIT
;;; Press, 2018).
(load "10-under-the-hood.scm")

;;; conda is like the so-called soft-cut (also known as if-then-else).
(run* x
      (conda ((== 'olive x) succeed)
             (succeed (== 'oil x))))

;;; The Law of conda
;;;
;;; The first conda line whose question succeeds 
;;; is the only line that can contribute values.

;;; This is a big difference from 
;;; every conde line contributing values to 
;;;; exactly one conda line possibly contributing values 
;;; when the first successful question is discovered.

;;; The "a" in conda stands for a single line,
;;; since at most a single line can succeed.

(run* x
      (conda 
        ((== 'virgin x) fail)
        ((== 'oliver x) succeed)
        (succeed (== 'oil x))))

(run* q
      (fresh (x y) 
             (== 'split x) 
             (== 'pea y) 
             (conda 
               ((== 'split x) (== x y)) 
               (succeed succeed))))

(run* q
      (fresh (x y) 
             (== 'split x)
             (== 'pea y) 
             (conda 
               ((== x y) (== 'split x))
               (succeed succeed))))

;;; Only if the question of a  conda line fails 
;;; do we consider the remaining conda lines. 
;;; If the question succeeds, 
;;; it is as if the remaining conda lines 
;;; have been replaced by a single (#s #u).

;;; not-pastao
(defrel (not-pastao x) 
        (conda 
          ((== 'pasta x) fail)
          (succeed succeed)))

(run* x
      (conda 
        ((not-pastao x) fail)
        ((== 'spaghetti x) succeed)))

(run* x
      (== 'spaghetti x)
      (conda 
        ((not-pastao x) fail)
        ((== 'spaghetti x) succeed)))

;;; The Second Commandment (Initial)
;;;
;;; If prior to determining the question of a conda line a variable is fresh,
;;; it must remain fresh in that line's question.

;;; alwayso
(defrel (alwayso)
        (conde
          (succeed)
          ((alwayso))))

; (run* q
;       (conda 
;         ((alwayso ) succeed)
;         (succeed fail)))
; no value. since run* never finishes building the list of _0 s.

(run* q
      (condu 
        ((alwayso ) succeed)
        (succeed fail)))

;;; condu is like conda, expect that the successful question,
;;; the (alwayso ) succeeds exactly once.

; (run* q
;       (condu 
;         (succeed (alwayso)) 
;         (succeed fail)))
; no value. since run* never finishes building the list of _0 s.

;;; The "u" in condu stands for uni-,
;;; because the successful question of a condu line succeeds exactly once.

; (run 1 q
;      (conda 
;        ((alwayso ) succeed)
;        (succeed fail))
;      fail)
; no value. since the outer #u fails each time (alwayso ) succeeds.

(run 1 q
     (condu
       ((alwayso ) succeed)
       (succeed fail))
     fail)

;;; The Law of condu
;;;
;;; condu behaves like conda, 
;;; except that a successful question succeeds only once.

;;; The Seconda Commandment (Final)
;;;
;;; If prior to determing the question of a conda or condu line a variable is fresh,
;;; it must remain fresh in that line's question.

(defrel (teacupo t) 
        (conde 
          ((== 'tea t))
          ((== 'cup t))))

(defrel (onceo g) 
        (condu 
          (g succeed)
          (succeed fail)))

(run* x
      (onceo (teacupo x)))

(run* r
      (conde 
        ((teacupo r) succeed)
        ((== #f r) succeed)))

(run* r
      (conda 
        ((teacupo r) succeed)
        ((== #f r) succeed)))

(run* r
      (== #f r)
      (conda
        ((teacupo r) succeed)
        ((== #f r) succeed)
        (succeed fail)))

(run* r
      (== #f r)
      (condu
        ((teacupo r) succeed)
        ((== #f r) succeed)
        (succeed fail)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
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

;;; poso
(defrel (poso n)
        (fresh (a d)
               (== `(,a . ,d) n)))

;;; >1o
(defrel (>1o n)
        (fresh (a ad dd)
               (== `(,a ,ad . ,dd) n)))

;;; +o
(defrel (+o n m k)
        (addero 0 n m k))

;;; -o
(defrel (-o n m k)
        (+o m k n))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; bumpo
(defrel (bumpo n x) 
        (conde 
          ((== n x))
          ((fresh (m) 
                  (-o n '(1) m)
                  (bumpo m x)))))

(run* x
     (bumpo '(1 1 1) x))

;;; gen&test+o
(defrel (gen&test+o i j k) 
        (onceo
          (fresh (x y z) 
                 (+o x y z)
                 (== i x)
                 (== j y)
                 (== k z))))

(run* q
      (gen&test+o '(0 0 1) '(1 1) '(1 1 1)))

; (run 1 q
;      (gen&test+o '(0 0 1) '(1 1) '(0 1 1)))
; no value. 

;;; In gen&test+o, (+o x y z) generates various associations for x, y, and z. 
;;; Next, (≡ i x), (≡ j y), and (≡ k z) test if the given triple 
;;; of values i, j , and k is present among the generated triple x, y, and z. 
;;; All the generated triples satisfy, by definition, the relation +o. 
;;; If the triple of values i, j , and k is chosen 
;;; so that i + j is not equal to k, and the definition of +o is correct, 
;;; then that triple of values cannot be found among those generated by +o.

;;; enumerate+o
;;; which determines that (+o x y z) with x, y, and z 
;;; beging eventually generates all triples,
;;; where x + y = z.
;;; At least, enumerate+o determines that for x and y begin () through some n.
(defrel (enumerate+o r n) 
        (fresh (i j k) 
               (bumpo n i)
               (bumpo n j)
               (+o i j k)
               (gen&test+o i j k)
               (== `(,i ,j, k) r)))

(run* s
      (enumerate+o s '(1 1)))

;;; enumerateo
(defrel (enumerateo op r n) 
        (fresh (i j k) 
               (bumpo n i)
               (bumpo n j)
               (op i j k)
               (onceo 
                 (fresh (x y z)
                        (op x y z)
                        (== i x)
                        (== j y)
                        (== k z)))
               (== `(,i ,j, k) r)))

(run* s
      (enumerateo +o s '(1 1)))

