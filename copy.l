; sapid
; copy implementation analysis
; gilles.arcas@gmail.com, https://github.com/GillesArcas/sapid-lisp
; MIT license

; natural definition

(de copy1 (x)
    (if (atom x)
        x
        (cons (copy1 (car x)) (copy1 (cdr x))) ) )

; iterative on cdr using while

(de copy2 (x)
    (slet ((head (cons ()())) (tail head))
        (while (consp x)
            (setq tail (placdl tail (copy2 (car x))))
            (setq x (cdr x)) )
        (rplacd tail x)
        (cdr head) ) )

; iterative on cdr using tail recursion

(de copy3-1 (x)
    (let ((head (cons ()())))
        (let aux ((x x) (tail head))
            (if (atom x)
                (rplacd tail x)
                (aux (cdr x) (placdl tail (copy3-1 (car x)))) ) )
        (cdr head) ) )

(de copy3-2 (x)
    (let ((head (cons ()())))
        (copy3-2-aux x head)
        (cdr head) ) )

(de copy3-2-aux (x tail)
    (if (atom x)
        (rplacd tail x)
        (copy3-2-aux (cdr x) (placdl tail (copy3-2 (car x)))) ) )

; fully iterative, all calls are tail recursive
; assembler-like coding, registers and stack

(de copy4 (x)
    (let ((R1 x) (R2 ()) (stack ()))      ; two registers, one stack
        (copy4-0 'copy4-end) ) )          ; call copy with argument

(de copy4-0 (cont)                        ; argument to copy in R1
    (if (atom R1)
        (funcall cont)
        (newl stack cont)                 ; push return address
        (newl stack (cdr R1))             ; push cdr
        (setq R1 (car R1))                ; R1 = car
        (copy4-0 'copy4-1) ) )            ; call copy with car

(de copy4-1 ()                            ; R1 = copy car, top = cdr
    (setq R2 (nextl stack))               ; swap R1 and top of stack
    (newl stack R1)
    (setq R1 R2)                          ; R1 = cdr
    (copy4-0 'copy4-2) )                  ; call copy with cdr

(de copy4-2 ()                            ; R1 = copy cdr, top = copy car
    (setq R1 (cons (nextl stack) R1))     ; R1 = cons copy car, copy cdr
    (funcall (nextl stack)) )             ; continue with return address in stack

(de copy4-end ()
    R1 )

; iterative, derived from previous, remove registers and pass value to copy as argument

(de copy5 (x)
    (let ((stack ()))
        (copy5-0 x 'copy5-end) ) )

(de copy5-0 (x cont)
    (if (atom x)
        (funcall cont x)
        (newl stack cont)
        (newl stack (cdr x))
        (copy5-0 (car x) 'copy5-1) ) )

(de copy5-1 (x)
    (let ((y (nextl stack)))
        (newl stack x)
        (copy5-0 y 'copy5-2) ) )

(de copy5-2 (x)
    (let ((y (nextl stack)))
        (funcall (nextl stack) (cons y x)) ) )

(de copy5-end (x)
    x )

; iterative, derived from previous, pass stack as argument

(de copy6 (x)
    (copy6-0 x 'copy6-end ()) )

(de copy6-0 (x cont stack)
    (if (atom x)
        (funcall cont x stack)
        (copy6-0 (car x) 'copy6-1 (mcons (cdr x) cont stack)) ) )

(de copy6-1 (x stack)
    (copy6-0 (car stack) 'copy6-2 (cons x (cdr stack))) )

(de copy6-2 (x stack)
    (funcall (cadr stack) (cons (car stack) x) (cddr stack)) )

(de copy6-end (x stack)
    x )

; variation of previous, continuation after copyX-0 in the stack

(de copy7 (x)
    (copy7-0 x '(copy7-end)) )

(de copy7-0 (x stack)
    (if (atom x)
        (funcall (car stack) x (cdr stack))
        (copy7-0 (car x) (mcons 'copy7-1 (cdr x) stack)) ) )

(de copy7-1 (x stack)
    (copy7-0 (car stack) (mcons 'copy7-2 x (cdr stack)) ) )

(de copy7-2 (x stack)
    (funcall (cadr stack) (cons (car stack) x) (cddr stack)) )

(de copy7-end (x stack)
    x )

; iterative, derived from previous, all in one

(de copy8 (x)
    (let ((copy0 (lambda (x cont stack)
                    (if (atom x)
                        (funcall cont x stack)
                        (funcall copy0 (car x) copy1 (mcons (cdr x) cont stack)) ) ))
          (copy1 (lambda (x stack)
                    (funcall copy0 (car stack) copy2 (cons x (cdr stack))) ))
          (copy2 (lambda (x stack)
                    (funcall (cadr stack) (cons (car stack) x) (cddr stack)) ))
          (copy3 (lambda (x stack)
                    x )) )
        (funcall copy0 x copy3 ()) ) )

; test and bench

(de cantorint (n)
    (if (= n 0)
        ()
        (let ((l (cantorint (1- n))))
            (append l (list l)) ) ) )

(de somedef ()
    (mapcar 'fvalue '(mapc mapcar every some reduce let slet with letn
                        union intersection difference)) )

(de timing (iter func . l)
    (let ((totaltime 0) (t0 0) (time 0))
        (mapc (lambda (x)
                  (print func)
                  (setq t0 (time))
                  (repeat iter (setq y (funcall func x)))
                  (setq time (- (time) t0))
                  (when (nequal x y)
                      (print "Failed")
                      (print x)
                      (print y)
                      (exit toperror "Test failed.") )
                  (print time)
                  (setq totaltime (+ totaltime time)) )
              l )
        (print "Total " func " : " totaltime)) )

(de proceed (iter)
    (let ((l1 (iota 400))
          (l2 (cantorint 10))
          (l3 (somedef))
          (copyfunc '(copy1 copy2 copy3-1 copy3-2 copy4 copy5 copy6 copy7 copy8)) )
        (mapc (lambda (x) (timing iter x l1 l2 l3)) copyfunc)
        (print "All tests ok.") ) )

(de test () (proceed 1))
(de bench () (proceed 10))

; Conclusions

; Pure recursive version and iterative on cdr using while are faster and almost
; equivalent. Completely iterative versions are at least 3 times slower. It
; seems convenient to offer both versions in the library.
