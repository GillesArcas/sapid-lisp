; sapid lisp
; Pretty printing
; gilles.arcas@gmail.com, https://github.com/GillesArcas/sapid-lisp
; MIT license

; API

(de pprint (e)
    (setq *print-reader* t)
    (pprin e 0)
    (setq *print-reader* ())
    (terpri)
    e )

(de pprin (e lev)
    (cond 
        ((null e) 
            (prin-atom-user "()") )
        ((atom e) 
            (prin-atom-reader e) )
        ((>= lev *print-level*) 
            (prin-atom-user "&") )
        ((memq (car e) '(de dm dmd)) 
            (pprin-de e lev) )
        ((linep e *outpos*)
            (pprin-h e lev) )
        ((atom (car e))
            (pprin-std e lev) )
        (t
            (pprin-v e lev) ) ) )

(dmd pp (s)
    `(progn (pprint (getdef ',s)) ',s) )
    
; Line predicate: is it possible to output an expression in the line?

(de linep (e n) 
    (> (linep-exp e (- *right-margin* n)) 0) )

(de linep-exp (e n)
    (if (< n 0)
        n
        (if (atom e) (- n (plength e)) (linep-list e (- n 2))) ) )

(de linep-list (e n)
    (if (< n 0)
        n
        (if (atom e)
            (ifn e n (linep-exp e (- n 2)))
            (ifn (cdr e)
                (linep-exp (car e) (1- n))
                (linep-list (cdr e) (1- (linep-exp (car e) n))) ) ) ) )

; Function definition printing 

(de pprin-de (e lev)
    (prin-atom-user "(")
    (prin-atom (car  e)) (prin-atom-user " ")
    (prin-atom (cadr e)) (prin-atom-user " ")
    (prin (caddr e))
    (let ((*left-margin* (+ *left-margin* 3)))
        (terpri)
        (vpprin-list (cdddr e) (1+ lev) 0)
        (prin-atom-user ")") ) )

; Horizontal printing

(synonym 'pprin-h 'prin-exp)

; Vertical printing

(de pprin-v (e lev)
    (prin-atom-user "(")
    (let ((*left-margin* *outpos*))
        (vpprin-list e (1+ lev) 0) )
    (prin-atom-user ")") )

(de vpprin-list (e lev len)
    (cond 
        ((atom e)
            (prin-atom-user ". ")
            (prin-atom-user e) )
        ((>= len *print-length*)
            (prin-atom-user "...") )
        (t
            (pprin (car e) lev)
            (when (cdr e) 
                (terpri) 
                (vpprin-list (cdr e) lev (1+ len)) ) ) ) )

; Standard printing

(de pprin-std (e lev)
    (prin-atom-user "(")
    (pprin (car e) lev)
    (when (cdr e)
        (prin-atom-user " ")
        (let ((*left-margin* (+ *left-margin* 3)))
            (vpprin-list (cdr e) (1+ lev) 1) ) )
    (prin-atom-user " ")
    (prin-atom-user ")") )
