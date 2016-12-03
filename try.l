; sapid lisp
; try except implementation
; gilles.arcas@gmail.com, https://github.com/GillesArcas/sapid-lisp
; MIT license

; The try form has the following syntax:

;(try
;    <body>
;    (except <exception name> <binding>
;        <expr*> )
;    (except <exception name> <binding>
;        <expr*> )
;    (else
;        <expr*> )
;    (finally
;        <expr*> ) )

; - <body> is a single expression, <expr*> may contain several expressions.
; - <exception name> is a symbol.
; - <exception name> may be t. In that case, the associated expressions will
;   be evaluated for any exception.
; - <binding> may be nil, a variable, or a list of two variables.
; - When <binding> is a variable, this variable is local to the clause and
;   catches the value of the exception.
; - When <binding> is a list of two variables, they are local to the clause
;   and catch respectively the name and the value of the exception.

; An exception is raised with:

;(raise <exception name>
;    <expr*> )

; - raise evaluates the name of the exception.
; - The value of the last expresion in <expr*> is the value of the exception.
; - raise is equivalent to throw.
; - exit may be used is the exception is not to be evaluated.

; The general try form is equivalent to:

;(protect
;    (lock
;        (lambda (tag val)
;            (selectq tag
;                (() <expr*>)
;                (<exception name> <expr*>)
;                (<exception name> (let ((<var> val)) <expr*>))
;                (<exception name> (let ((<var1> tag)(<var2> val)) <expr*>))
;                (t (throw tag val)) ) )
;        <expr> )
;    <finally expr*> )

(dmd try x
    (expand-try x) )

(de expand-try (form)
    (let ((main (car form))
          (except (filter (lambda (x) (eq (car x) 'except)) form))
          (else    (car (filter (lambda (x) (eq (car x) 'else)) form)))
          (finally (car (filter (lambda (x) (eq (car x) 'finally)) form))) )
        (ifn finally
            (expand-lock main except else)
            `(protect
                ,(expand-lock main except else)
                ,@(cdr finally) ) ) ) )

(de expand-lock (main except else)
    `(lock
        (lambda (tag val)
            (selectq tag
                ,(expand-try-else else)
                ,@(mapcar 'expand-try-except except)
                (t (throw tag val)) ) )
        ,main ) )

(de expand-try-except (except)
    (let ((tag (cadr except)) (var (caddr except)) (expr* (cdddr except)))
        (if (eq var ())
            `(,tag ,@expr*)
            `(,tag (let ((,var val)) ,@expr*)) ) ) )

(de expand-try-except (except)
    (let ((tag (cadr except)) (bind (caddr except)) (expr* (cdddr except)))
        (cond
            ((eq bind ()) `(,tag ,@expr*))
            ((atom bind) `(,tag (let ((,bind val)) ,@expr*)))
            (t `(,tag (let ((,(car bind) tag)(,(cadr bind) val)) ,@expr*))) ) ) )

(de expand-try-else (else)
    `(() ,@(cdr else)) )

(de expand-try-else (else)
    (ifn else
        '(() val)
        `(() ,@(cdr else)) ) )

(dmd raise x
   `(throw ,@x) )

; testing

(de testtry1 (n)
    (let ((r ()))
        (try
            (cond
                ((stringp n) (raise 'StringExcept 0))
                ((consp n) (raise 'SomeExcept 42))
                (t (setq r (+ 1 n))) )
            (except StringExcept r
                (print n " is a string, not a number, returns " r) )
            (except toperror ()
                (print n " is not a number (and not a string) " 2) )
            (except t (e r)
                (print "Exception: " e "," r " .Dont know what happens with " 1) )
            (else
                (print "Ok. Result is: " r) )
            (finally
                (print "This is not the result of try") ) ) ) )

(de testtry ()
    (and (= (testtry1 "a")  0)
         (= (testtry1 '(a)) 1)
         (= (testtry1 'a)   2)
         (= (testtry1 2)    3) ) )
