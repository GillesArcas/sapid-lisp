; sapid lisp
; backquote macro character
; gilles.arcas@gmail.com, https://github.com/GillesArcas/sapid-lisp
; MIT license

(value 'back-c '|,|)
(value 'back-a '|@|)

(typech "`" macro-char)
(de |`| () (backquote-main (typech ",") (typech "@") (fvalue '|,|) (fvalue '|@|))) 

(de backquote-main (typech-comma typech-amper fvalue-comma fvalue-amper)
    (typech "," macro-char)
    (fvalue '|,| (lambda () (backquote-read-comma)))
    (typech "@" macro-char)
    (fvalue '|@| (lambda () (backquote-read-amper)))
    (protect
        (backquote (read))
        (typech "," typech-comma)
        (typech "@" typech-amper)
        (fvalue '|,| fvalue-comma)
        (fvalue '|@| fvalue-amper) ) )
      
(de backquote (x)
    (if (atom x)
        (opkwote x)
        (backquote-cons (car x) (cdr x)) ) )
        
(de backquote-read-comma ()
    ((lambda (x)
        (if (q-and (consp x) (eq (car x) back-a))
            x
            (cons back-c x) ) )
      (read) ) )
      
(de backquote-read-amper ()
    (cons back-a (read)) )  

(de opkwote (x)
    (if (q-constantp x)
        x
        (kwote x) ) )

(de backquote-cons (first rest)
    (if (q-or (eq first back-c)
              (eq first back-a) )
        rest
        (if (atom first)
            (backquote-quote first (backquote first) (backquote rest))
            (if (eq (car first) back-c)
                (backquote-comma (cdr first) (backquote rest))
                (if (eq (car first) back-a)
                      (backquote-append (cdr first) (backquote rest))
                      (backquote-quote first (backquote first) (backquote rest)) ) ) ) ) )

(de backquote-comma (x by)
    ; x is a car of the original form where it was preceded by ","
    ; by is the backquotified form of the cdr associated to x
    (list 'cons x by) )

(de backquote-append (x by)
    ; x is a car of the original form where it was preceded by "@"
    ; by is the backquotified form of the cdr associated to x
    (if (eq by ())
        x
        (list 'append x by) ) )

(de backquote-quote (x bx by)
    ; x is a car of the original form
    ; bx its backquotified form
    ; by is the backquotified form of the cdr associated to x
    (if (eq by ())
        (if (q-or (q-constantp bx) (quotedp bx))
            (kwote (list x))
            (list 'list bx) )
        (if (q-and (q-or (q-constantp bx) (quotedp bx)) (quotedp by))
            (kwote (cons x (car (cdr by))))
            (list 'cons bx by) ) ) )

; Addicional definitions

(de atom (x) 
    (eq (consp x) ()) )

(de list x
    x )
    
(dmd q-and (x y)
    (list 'if (list 'eq x ()) () y) )
    
(dmd q-or (x y)
    (list 'if x t y) )
    
(de kwote (x) 
    (list 'quote x) )

(de q-constantp (x)
    (q-or (eq x ()) (q-or (numberp x) (stringp x))) )

(de quotedp (x)
    (if (atom x)
        ()
        (eq (car x) 'quote) ) )
        
(dmd protect (e1 . e*)
    (list 'lock 
        (list 'lambda '(tag val)
            (cons 'progn e*)
            '(if tag (throw tag val) val) )
          e1) )
; Testing
                  
(de backquote-test ()
   (let ((test
     '(
      ;
      ; Atomes
      ;
      ( `a                           'a )
      ( `1                           1  )
      ( `()                          () )
      ;
      ; , et @ externes
      ;
      ( `,a                          a  )
      ( `@a                          a  )
      ;
      ; Pas de , et @
      ;
      ( `(a)                         '(a) )
      ( `(1)                         '(1) )
      ( `(1 c)                       '(1 c) )
      ( `(a 1 c)                     '(a 1 c) )
      ( `((a b))                     '((a b)) )
      ( `((a b) c d)                 '((a b) c d) )
      ( `(a b (c d (e f) g h) i j)   '(a b (c d (e f) g h) i j) )
      ;
      ; Test ,
      ;
      ( `(,a)                        (cons a ()) )
      ( `(,a ,b ,c)                  (cons a (cons b (cons c ()))) )
      ( `((a b) ,c d)                (cons '(a b) (cons c '(d))) )
      ( `((,a b) c d)                (cons (cons a '(b)) '(c d)) )
      ( `((,a b) ,c d)               (cons (cons a '(b)) (cons c '(d))) )
      ;
      ; Test @
      ;
      ( `(@a)                        a )
      ( `(a b ,@c)                   (cons 'a (cons 'b c)) )
      ( `(a ,@b ,@c)                 (cons 'a (append b c)) )
      ( `(,a ,@b)                    (cons a b) )
      ( `(,@a ,@b ,@c)               (append a (append b c)) )
      ) ))

      (every (lambda (x) (equal (car x) (cadr x))) test) 
    ) )
