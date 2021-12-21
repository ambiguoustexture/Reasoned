;;; Chapter 6 of The Reasoned Schemer: The Fun Never Ends...

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

;;; alwayso
(defrel (alwayso)
        (conde
          (succeed)
          ((alwayso))))

(run 1 q
     (alwayso))

(run 1 q
     (conde
       (succeed)
       ((alwayso))))
; (alwayso) succeeds any number of times,
; whereas #s succeeds only once.

; (run* q
;       (alwayso))
; no value.

; (run* q
;       (conde
;         (succeed)
;         ((alwayso))))
; no value.

(run 5 a
     (alwayso))

(run 5 q
     (== 'onion q)
     (alwayso))

; (run 1 q
;      (alwayso) fail)
; (alwayso) succeeds, followed by #u,
; which cause (alwayso) to be retried,
; which succeeds again,
; which leads to #u again, etc.

(run 1 q
     (== 'garlic q)
     succeed
     (== 'onion q))

; (run 1 q
;      (== 'garlic q)
;      (alwayso)
;      (== 'onion q))
; no value.

(run 1 q
     (conde 
       ((== 'garlic q)
        (alwayso)) 
       ((== 'onion q))) 
     (== 'onion q))

; (run 2 q
;      (conde 
;        ((== 'garlic q)
;         (alwayso)) 
;        ((== 'onion q))) 
;      (== 'onion q))
; no value.

(run 5 q
     (conde 
       ((== 'garlic q)
        (alwayso)) 
       ((== 'onion q) 
        (alwayso))) 
     (== 'onion q))

;;; nevero
;;; #u is a goal that fails, 
;;; whereas (nevero) is a goal that 
;;; neither succeeds nor fails.
(defrel (nevero) (nevero))

; (run 1 q
;      (nevero))
; no value.

(run 1 q
     fail 
     (nevero))
; #u fails before (nevero) is attempted.

(run 1 q
     (conde 
       (succeed) 
       ((nevero))))
; the first conde line succeeds.

(run 1 q 
     (conde 
       ((nevero)) 
       (succeed)))

; (run 2 q
;      (conde 
;        (succeed)
;        ((nevero))))
; no value.

; (run 1 q
;      (conde 
;        (succeed)
;        ((nevero))) 
;      fail)
; no value.

(run 5 q
     (conde 
       ((nevero))
       ((alwayso))
       ((nevero))))

(run 6 q
     (conde 
       ((== 'spicy q) (nevero)) 
       ((== 'hot q) (nevero))
       ((== 'apple q)
        (alwayso)) 
       ((== 'cider q) 
        (alwayso))))

;;; very-recursiveo
(defrel (very-recursiveo) 
        (conde 
          ((nevero)) 
          ((very-recursiveo)) 
          ((alwayso)) 
          ((very-recursiveo)) 
          ((nevero))))

; (run 1000000 q (very-recursiveo))
; A list of one million _0 values. 
