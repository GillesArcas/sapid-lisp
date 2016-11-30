; sapid lisp
; Tracing
; gilles.arcas@gmail.com, https://github.com/GillesArcas/sapid-lisp
; MIT license

; Interface

(dm trace (f)
    "Trace function f."
    "Returns f if ok, nil if already traced or impossible to trace."
    `(trace-one ',f 'trace-def) )
    
(dm ncall (f) 
    "Count number of calls to f." 
    "Number stored in *trace* value, accessible with (cadr (assq f *trace*))"
    "Returns f if ok, nil if already traced or impossible to trace."
    `(trace-one ',f 'ncall-def))

(dm untrace (f)
    "Stop tracing f."
    `(untrace-one ',f) )

; Defining functions

; use *trace* to store calling count and original definition
; alist of (f count def)
(setq *trace* ())

(de trace-one (f trace-fn)
    (let ((x (assq f *trace*)))
        (if x
            () ; already traced
            (let ((def (fvalue f)))
                (ifn (memq (car def) '(subr0 subr1 subr2 lambda))
                    () ; not tracable
                    (newl *trace* `(,f 0 ,@def)) 
                    (fvalue f (funcall trace-fn f def (trace-larg def)))
                    f ) ) ) ) )

(de trace-larg (def)
    (selectq (car def)
        (subr0 ())
        (subr1 '(x))
        (subr2 '(x y))
        (lambda (cadr def)) ) )

; Form expansion for tracing calls

(de trace-def (f def larg)
    `(lambda ,larg
        (print "> " ',f " " ,@(print-larg larg))
        (print "< " ',f " " (funcall ',def ,@larg)) ) )

(de print-larg (larg)
    (when larg
        (if (atom larg)
            `(',larg " = " ,larg)
            `(',(car larg) " = " ,(car larg) " " ,@(print-larg (cdr larg))) ) ) )

; Form expansion for counting calls

(de ncall-def (f def larg)
    `(lambda ,larg
        (let ((x (assq ',f *trace*)))
            (rplaca (cdr x) (1+ (cadr x))) )
        (funcall ',def ,@larg) ) )

; Restore original definition

(de untrace-one (f)
    (let ((y (assq f *trace*)))
        (ifn y
            ()
            (fvalue f (cddr y))
            (setq *trace* (assq-delete f *trace*))
            f ) ) )


        