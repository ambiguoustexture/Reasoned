;;; Copyright © 2018 Daniel P. Friedman, William E. Byrd, Oleg Kiselyov, and Jason Hemann
;;;
;;; Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the “Software”), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:
;;;
;;; The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
;;;
;;; THE SOFTWARE IS PROVIDED “AS IS”, WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.


;;; Implementation of the language used in 'The Reasoned Schemer,
;;; Second Edition,' by Friedman, Byrd, Kiselyov, and Hemann (MIT
;;; Press, 2018).

;;; Chapter 10 of The Reasoned Schemer: Under the Hood

;;; The implementation of "a complete relational programming language"
;;; on top of Scheme.

;;; Each use of var creates a new one-element vector 
;;; representing a unique variable. 
;;; Ignore the vectors’ contents, 
;;; instead distinguishing vectors by their addresses in memory. 
;;; Distinguish variables by their values, 
;;; provided ensure their values are unique 
;;; (for example, using a unique natural number in each variable).
(define var (lambda (x) (vector x)))

;;; A substitution like `((,x . ,z)) is a special kind of list of associations. 
;;; In the substitution `((,x . ,z)), the association `(,x . ,z) 
;;; whose cdr is also a variable 
;;; represents the fusing of that assocaition's two variables. 

(define var? (lambda (x) (vector? x)))

;;; empty-s
;;; A substitution that contains no associations.
(define empty-s '())

;;; walk
;;; If a variable has been walk'd in a substitution s, 
;;; and walk has produced a variable x, then konw that x is fresh.
(define (walk v s) ; A kind of Disjoint Set (or Union-Find) ? 
  ; assv is a function that expects a value v and a list of associations l.
  ; assv either produces the first association in l 
  ; that v as its car using eqv?, 
  ; or produces #f if l has no such association.
  (let ((a (and (var? v) (assv v s)))) 
    (cond 
      ((pair? a) (walk (cdr a) s))
      (else v))))

;;; ext-s
;;; which either extends a substitution s with an association 
;;; between the variable x and the value v,
;;; or it produces #f if extending the substitution 
;;; with the pair `(,x . ,v) would have created a cycle.
(define (ext-s x v s) 
  (cond 
    ((occurs? x v s) ; tests whether or not x occurs in v, 
                     ; using the substitution s (occurs check).
     #f)
    (else (cons `(,x . ,v) s))))

(define (occurs? x v s) 
  (let ((v (walk v s))) 
    (cond 
      ((var? v) (eqv? v x))
      ((pair? v) 
       (or (occurs? x (car v) s) 
           (occurs? x (cdr v) s)))
      (else #f))))

;;; unify, the place where the definition of == relies on,
;;; which produces either #f 
;;; or the ssubstitution s extended with zero or more associations, 
;;; which are cycle conditons.
(define (unify u v s) 
  (let ; Binds u and v to their walk'd values.
       ; If u walks to a variable, then u is fresh, 
       ; and likewise if v walks to a variable, then v is fresh.
    ((u (walk u s)) (v (walk v s))) 
    (cond 
      ((eqv? u v) s) ; If  u and v are the same according to eqv?, 
                     ; do not extend the substitution. 
                     ; eqv? works for strings, characters, numbers, Booleans, 
                     ; symbols, (), and variables.
      ((var? u) (ext-s u v s)) ; If ( var? u) is #t, then u is fresh, 
                               ; and therefore u is the first argument 
                               ; when attempting to extend s.
      ((var? v) (ext-s v u s)) ; If ( var? v) is #t, then v is fresh, 
                               ; and therefore v is the first argument 
                               ; when attempting to extend s.
      ((and (pair? u) (pair? v)) ; When both u and v are pairs, 
                                 ; attempt to unify the  car of u 
                                 ; with the car of v. 
                                 ; If they unify, a substitution gotten, 
                                 ; which could be used to attempt 
                                 ; to unify the cdr of u with the cdr of v.
       (let ((s (unify (car u) (car v) s))) 
         (and s
           (unify (cdr u) (cdr v) s)))) 
      (else #f))))

;;; A stream is either the empty list, 
;;; a pair whose cdr is a stream, or a suspension.
;;; A suspension is a function formed from 
;;; (lambda () body) where 
;;; ((lambda () body)) is a stream.

;;; ==
(define (== u v) 
  (lambda (s) 
    (let ((s (unify u v s))) 
      (if s `(,s) '()))))

;;; #s produces singleton streams,
(define succeed 
  (lambda (s)
    `(,s)))

;;; #u produces the empty stream, 
;;; while goals like (== u v) can produce 
;;; either singleton streams or the empty stream.
(define fail
  (lambda (s)
    '()))

;;; Each of ==, #s, and #u has a (lambda (s) ...).
;;; A goal is a function that epects a substitution and, 
;;; if it returns, produces a stream of substitutions.

;;; From now on, all streams are streams of substitutions.

;;; A conde always could be replaced with uses of ddisj2 and conj2.

;;; disj2
;;; which produces a function that expects a substitution as an argument.
;;; Therefore, if append-inf produces a stream, then disj2 produces a goal.
(define (disj2 g1 g2) 
  (lambda (s) 
    (append-inf (g1 s) (g2 s))))

(define (append-inf s-inf t-inf) ; s-inf and t-inf each must be a stream.
  (cond 
    ((null? s-inf) t-inf)
    ((pair? s-inf) 
     (cons (car s-inf) ; s-inf here must be a suspension. 
       (append-inf (cdr s-inf) t-inf))) 
    (else 
      (lambda () (append-inf t-inf (s-inf))) ; also a suspension.
                                             ; The suspension s-inf 
                                             ; is forced when the suspension 
                                             ; (lambda () 
                                             ;   (append-inf t-inf (s-inf))) 
                                             ; is itself forced.
      )))

;;; take-inf
;;; when given a number n and a stream s-inf, 
;;; if take-inf returns, it produces a list of at most n values.
;;; When n is a number, the expression (and n e) behaves 
;;; the same as the expression e.
;;; When n is #f, the expression (and n e) behaves the same as #f.
;;; Thus, the recursion in take-inf's last cond line 
;;; behaves the same as (take-inf #f (s-inf)).
;;; Furthermore, when n is #f, the first cond question is never true.
;;; Thus if take-inf returns, it produces a list of all the values.
;;; Furthermore, when n is #f, the first cond question is never true.
;;; Thus if take-inf returns, it produces a list of all the values.
(define (take-inf n s-inf) 
  (cond
    ((and n (zero? n)) '())
    ((null? s-inf)     '())
    ((pair? s-inf) 
     (cons (car s-inf) 
       (take-inf (and n (- n 1)) 
         (cdr s-inf))))
    (else (take-inf n (s-inf)))))

;;; map takes a function f and a list ls and builds a list (using cons), 
;;; where each element of that list is produced by applying f 
;;; to the corresponding element of ls.

;;; conj2
(define (conj2 g1 g2) 
  (lambda (s) 
    (append-map-inf g2 (g1 s))))

;;; append-map-inf
;;; If append-map-inf's third cond line and append-inf's third cond line 
;;; were absent, 
;;; append-map-inf would then behave the same as append-map. 
;;; append-map is like map, 
;;; but it uses append instead of cons to build its result.
(define (append-map-inf g s-inf)
  (cond 
    ((null? s-inf) '())
    ((pair? s-inf) 
     (append-inf (g (car s-inf)) 
       (append-map-inf g (cdr s-inf))))
    (else (lambda () 
            (append-map-inf g (s-inf))))))

;;; call/fresh
;;; Defined to introduce variables, 
;;; although name is used, it is ignored.
;;; It expects its second argument to be a lambda expression. 
;;; More specifically, 
;;; that lambda expression should expect a variable and produce a goal. 
;;; That goal then has access to the variable just created. 
(define (call/fresh name f) 
  (f (var name)))

;;; Every variable is presented as a corresponding symbol: 
;;; an underscore followed by a natural number.
;;; These symbols called reified variables.
;;; The association of variables with reified variables 
;;; just be another kind of substitution, called reified-name substitution.

;;; reify-name
(define (reify-name n) 
  (string->symbol 
    (string-append "_"
      (number->string n))))

;;; walk*
;;; which recursive and useful.
;;; The values of ( walk∗ v s) and (walk v s) differ 
;;; when v walks in s to a pair, 
;;; and the pair contains a variable that has an association in s.
;;; If v’s walk’d value is a pair, the second cond line of walk∗ is used. 
;;; Then, walk∗ constructs a new pair of the walk∗’d values in that pair, 
;;; whereas the walk’d value is just v.
;;; If v’s walk’d value is neither a variable nor a pair, 
;;; walk∗ does behave like walk.
;;; If a value is walk∗’d in a substitution s, 
;;; and walk∗ produces a value v, 
;;; then know that each variable in v is fresh.
(define (walk* v s)
  (let ((v (walk v s))) 
    (cond 
      ((var? v) v)
      ((pair? v) 
       (cons 
         (walk* (car v) s)
         (walk* (cdr v) s)))
      (else v))))

;;; project
;;; project behaves like fresh, 
;;; but it binds different values to the lexical variables. 
;;; project binds walk∗’d values, 
;;; whereas fresh binds variables using var.
(define-syntax project
  (syntax-rules () 
    ((project (x ...) g ...)
     (lambda (s) 
       (let ((x (walk* x s)) ...)
         ((conj g ...) s))))))

;;; reify-s
;;; which initially expects a value v
;;; and an empty reified-name substitution r.
;;; Unlike unify, expects only one value in addition to a substitution. 
;;; Also, reify-s cannot produce #f. 
;;; But, like unify, reify-s begins by walking v. 
;;; Then in both cases, 
;;; if the walk’d v is a variable, 
;;; know that it is fresh and use that fresh variable 
;;; to extend the substitution. 
;;; Unlike in unify, no occurs? is needed in reify-s. 
;;; In both cases, if v is a pair, 
;;; first produce a new substitution based on the car of the pair. 
;;; That substitution can then be extended using the cdr of the pair. 
;;; And, there is a case where the substitution remains unchanged.
(define (reify-s v r) 
  (let ((v (walk v r))) ; gives a walk'd (and possibly different) value to v. 
    (cond 
      ((var? v) ; If (var? v) is #t, 
                ; then v is a fresh variable in r, 
                ; and therefore can be used in extending r 
                ; with a reified variable.
       (let ((n (length r))) ; Every time reify-s extends r, 
                             ; length produces a unique number 
                             ; to pass to reify-name. 
         (let ((rn (reify-name n))) 
           (cons `(,v . ,rn) r)))) 
      ((pair? v) ; Extend the reified-name substitution with  v’s car, 
                 ; and extend that substitution 
                 ; to make another reified-name substitution with v’s cdr. 
       (let ((r (reify-s (car v) r))) 
         (reify-s (cdr v) r))) 
      (else r) ; The current reified-name substitution.
      )))

;;; Use walk∗ in the reified-name substitution 
;;; to replace all the variables in the value.

;;; reify
;;; which is not recursive.
(define (reify v) 
  (lambda (s) 
    (let ((v (walk* v s))) 
      (let ((r (reify-s v empty-s))) 
        (walk* v r) ; Each fresh variable in v is replaced 
                    ; by its reified variable 
                    ; in the reified-name substitution r. 
        ))))

;;; run-goal
(define (run-goal n g) 
  (take-inf n (g empty-s)))

;;; ifte
;;; which suggests if-then-else, 
;;; is not recursive, but has a recursive helper called loop created by let, 
;;; produces a goal whose body produces a stream.
(define (ifte g1 g2 g3) 
  (lambda (s) 
    (let loop ((s-inf (g1 s))) 
      (cond 
        ((null? s-inf) (g3 s))
        ((pair? s-inf) 
         (append-map-inf g2 s-inf))
        (else (lambda () 
                (loop (s-inf))))))))

(define (once g) 
  (lambda (s) 
    (let loop ((s-inf (g s))) 
      (cond 
        ((null? s-inf) '())
        ((pair? s-inf) 
         (cons (car s-inf) '()))
        (else (lambda ()
                (loop (s-inf))))))))

;;; Here are the key parts of Appendix A

(define-syntax disj 
  (syntax-rules () 
    ((disj) fail) 
    ((disj g) g)
    ((disj g0 g ...) (disj2 g0 (disj g ...)))))

(define-syntax conj 
  (syntax-rules ()
    ((conj) succeed)
    ((conj g) g)
    ((conj g0 g ...) (conj2 g0 (conj g ...)))))

(define-syntax defrel 
  (syntax-rules ()
    ((defrel (name x ...) g ...)
     (define (name x ...) 
       (lambda (s) 
         (lambda ()
           ((conj g ...) s)))))))

(define-syntax run
  (syntax-rules ()
    ((run n (x0 x ...) g ...)
     (run n q (fresh (x0 x ...)
                (== `(,x0 ,x ...) q) g ...))) 
    ((run n q g ...)
     (let ((q (var 'q))) 
       (map (reify q) 
         (run-goal n (conj g ...)))))))

(define-syntax run* 
  (syntax-rules ()
    ((run* q g ...) (run #f q g ...))))

(define-syntax fresh 
  (syntax-rules ()
    ((fresh () g ...) (conj g ...))
    ((fresh (x0 x ...) g ...)
     (call/fresh 'x_0
       (lambda (x0) 
         (fresh (x ...) g ...))))))

(define-syntax conde
   (syntax-rules ()
     ((conde (g ...) ...)
      (disj (conj g ...) ...))))

(define-syntax conda
  (syntax-rules ()
    ((conda (g0 g ...)) (conj g0 g ...))
    ((conda (g0 g ...) ln ...) 
     (ifte g0 (conj g ...) (conda ln ...)))))

(define-syntax condu
  (syntax-rules ()
    ((condu (g0 g ...) ...)
     (conda ((once g0) g ...) ...))))

