; sapid
; funargs and fixes
; gilles.arcas@gmail.com, https://github.com/GillesArcas/sapid-lisp
; MIT license

; Example from http://people.csail.mit.edu/gregs/ll1-discuss-archive-html/msg03278.html
  
(de mapcar (f x)
    (ifn x
        x
        (cons (funcall f (car x)) (mapcar f (cdr x))) ) )

(de add-to-all (x l)
    ; add x to all elements in l
    (mapcar (lambda (y) (+ y x)) l))
    
; When calling (add-to-all 42 (iota 5)), (funcall f (car x)) is actually equivalent
; to (funcall (lambda (y) (+ y x)) (car x)) which makes the capture clear

; To fix it:

(de add-to-all (x l)
    (mapcar `(lambda (y) (+ y ',x)) l))
    
; Example from http://groups.google.com/group/comp.lang.lisp/browse_thread/thread/9a210cfd3f722f4b

(de mapcar (f x)
    (ifn x
        x
        (cons (funcall f (car x)) (mapcar f (cdr x))) ) )

(de prefix-first (x)
    ; prefixes all elements in x with 1st one: (1 2 3) -> ((1 1) (1 2) (1 3))
    (mapcar (lambda (y) (list (car x) y)) x) )

; Again the funcall form is equivalent to (funcall (lambda (y) (list (car x) y)) (car x))

; Fix:

(de prefix-first (x)
    (mapcar `(lambda (y) (list ',(car x) y)) x) )

; An example resulting in an infinite loop

(de filter (f l)
    (ifn l
        l
        (if (funcall f (car l))
            (cons (car l) (filter f (cdr l))) 
            (filter f (cdr l)) ) ) )
            
(de keep-value (f x l)  
    ; keeps elements in l if (f element x) is true: (keep-value '< 3 '(1 2 3 4 5)) --> (1 2)
    (filter (lambda (y) (funcall f y x)) l) )
    
; The funcall form inside filter is evaluated with f bound to (lambda (y) (funcall f y x))
; So 
; (funcall f (car l)) -->
; (funcall (lambda (y) (funcall f y x)) (car l)) -->
; (funcall (lambda (y) (funcall (lambda (y) (funcall f y x)) y x)) (car l)) --> ...
; and so on giving and infinite recursion

; The fix:    
    
(de keep-value (f x l)  
    (filter `(lambda (y) (funcall ',f y ',x)) l) )
    
; One simpler infinite recursion and fix

(de double-func (f x)
    (funcall (lambda (x) (funcall f x)) x) )

(de double-func (f x)
    (funcall `(lambda (x) (funcall ',f x)) x) )

; This ones results in non tail calls and launchs an error
    
(de foo (f x) (funcall 'foo2 x))
    
(de foo2 (x) (1+ (funcall f x)))

; The fix would be to pass the function
    
(de foo2 (f x) (1+ (funcall f x)))

; Local variables in macros

(dm prog1 (x . l)
    `(let ((x ,x))
        (progn ,@l)
         x) )

(de testprog1 ()
    ; prints foo and returns 42
    (let ((x 'foo))
        (prog1
            42
            (print x) ) ) ) 
    
; testprog1 is expanded into the following which shows how the initial value of x is lost

(de testprog1-expanded ()
    (let ((x 'foo))
        (let ((x 42))
            (progn (print x))
            x ) ) )
    
; In that case, the value of the first expression in prog1 must be saved in some way. The
; standard fix uses gensym.

(dm prog1 (x . l)
    (let ((var (gensym)))
        `(let ((,var ,x))
            (progn ,@l)
             ,var) ) )

; Testing variable values (from testing.l)

; The function (check-env lvar lval) is intended to compare the values of
; variables in list lvar with values in lval.

; It is tempting to use functional style, for instance:

(de check-env (lvar lval)
    (apply 'and (mapcar (lambda (x y) (= (value x) y)) lvar lval)) )

; This fails if x or y is in lvar. Let's try with let-unique:

(de check-env (lvar lval)
    (let-unique (x y)
        (apply 'and (mapcar `(lambda (,x ,y) (= (value ,x) ,y)) lvar lval)) ) )

; This fails because (let-unique x ... ) is equivalent to (let ((x ...)) ...)
; It is better when limiting the scope of let-unique:

(de check-env (lvar lval)
    (apply 'and (mapcar (let-unique (x y)`(lambda (,x ,y) (= (value ,x) ,y))) lvar lval)) )

; However mapcar uses some variables and this does not work for these variables (head and tail).

; Finally, all problems are avoided by using an explicit style which preserves the environment:

(de check-env (lvar lval)
    (or (null lvar)
        (and (= (value (car lvar)) (car lval))
             (check-env (cdr lvar) (cdr lval)) ) ) )

; A trivial case when a typo on a variable catches the value of a variable from the calling function

(de foo (one_variable)
    (setq one_variable 42)
    (bar (1+ one_variable)) )
    
(de bar (one-variable)
    (print one_variable) )
    