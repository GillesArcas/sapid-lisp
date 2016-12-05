; sapid lisp
; definitions for function documentation
; gilles.arcas@gmail.com, https://github.com/GillesArcas/sapid-lisp
; MIT license

; interface

(dm describe (name . rest)
    (if (eq rest ())
        (describe-display name)
        (describe-store name (car rest) (cdr rest)) ) )
        
(synonym 'help 'describe)        

(de describe-all (filename)
    (let ((list (sort '< (filter (lambda (x) (getprop x 'describe-text)) (oblist))))
          (out (openo filename)) )
        (with ((output out))
            (mapc (lambda (x) (describe-display x) (terpri)) list) )
        (close out) ) )
        
; implementation
    
(de describe-display (sym)
    ; not used during startup, may use all defined functions
    (ifn (fvalue sym)
        (print sym " : No function definition")
        (let ((fn (fvalue sym)))
            (prin "Description of function: " sym ". ")
            (if (memq (car fn) '(fsubr macro dmacro))
                (print "Does not evaluate all arguments.")
                (print "Evaluates all arguments.") )
            (print (cons sym (getprop sym 'describe-largs))) ) )
    (ifn (getprop sym 'describe-text)
        (print "No description")
        (mapc (lambda (x) (print "    " x)) (getprop sym 'describe-text)) )
    (cons 'quote (cons sym ()))
)

(de describe-store (sym largs text)
    ; used during startup, uses only builtin functions
    (plist sym (cons 'describe-largs (cons largs (plist sym))))
    (plist sym (cons 'describe-text  (cons text  (plist sym)))) 
    (cons 'quote (cons sym ())) )

(de typefn (x) (car (fvalue x)))
(if (eq (typefn 'de ) 'fsubr) (synonym 'subr.de  'de))
(if (eq (typefn 'dm ) 'fsubr) (synonym 'subr.dm  'dm))
(if (eq (typefn 'dmd) 'fsubr) (synonym 'subr.dmd 'dmd))

(de describe-define (define sym largs rest)
    (describe-extract define sym largs rest (cons ()()) ()) )

(de describe-extract (define sym largs body head tail)
    (value 'tail head)
    (while (if (stringp (car body)) (consp (cdr body)))
        (value 'tail (cdr (rplacd tail (cons (car body) ()))))
        (value 'body (cdr body)) )
    (describe-proceed define sym largs (cdr head) body) )
   
(de describe-proceed (define sym largs text body)
    `(progn
        (describe ,sym ,largs ,@text)
        (,define ,sym ,largs ,@body) ) )

; redefinitions of defining functions to handle descriptions
   
(dm de (sym largs . rest) 
    (describe-define 'subr.de sym largs rest) )
    
(dm dm (sym largs . rest) 
    (describe-define 'subr.dm sym largs rest) )
    
(dm dmd (sym largs . rest) 
    (describe-define 'subr.dmd sym largs rest) )
