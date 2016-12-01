; sapid lisp
; Testing
; gilles.arcas@gmail.com, sites.google.com/site/sapidlisp

; This module tests various aspects of sapid working: recursion optimization,
; exceptions and part of the API.

; Three test suites are defined using no recursion optimization, tail
; recursion optimization or mutual recursion optimization. 

; Lauch test suite with (test <name of test suite>)
; Bench test suite with (bench <name of test suite> <number of iterations>)


;;; factorial

(setq fac10 3628800)
(setq fac15 1307674368000)
(setq fac20 2432902008176640000)

; recursion

(de fac1 (n)
    (if (= n 1)
        1
        (* n (fac1 (1- n))) ) )

(deftest test-fac1-1 (fac1 10) fac10 (n))
(deftest test-fac1-2 (fac1 20) fac20 (n))

; tail recursion

(de fac2 (n)
    (fac2-aux n n 1) )

(de fac2-aux (n i r)
    (if (= i 1)
        r
        (fac2-aux n (1- i) (* i r)) ) )

(deftest test-fac2-1 (fac2 10) fac10 (n i r))
(deftest test-fac2-2 (fac2 20) fac20 (n i r))

; tail recursion

(de fac3 (n)
    (fac3-aux 1 1) )

(de fac3-aux (i r)
    (if (= i n)
        r
        (incr i)
        (fac3-aux i (* i r)) ) )

(deftest test-fac3-1 (fac3 10) fac10 (n i r))
(deftest test-fac3-2 (fac3 20) fac20 (n i r))

; tail recursion with named let

(de fac4 (n)
    (let aux ((i n) (r 1))
        (if (= i 1)
            r
            (aux (1- i) (* i r)) ) ) )

(deftest test-fac4-1 (fac4 10) fac10 (n i r))
(deftest test-fac4-2 (fac4 20) fac20 (n i r))

; iteration

(de fac5 (n)
    (let ((i 1) (r 1))
        (while (<= i n)
            (setq r (* i r))
            (incr i) )
        r ) )

(deftest test-fac5-1 (fac5 10) fac10 (n i r))
(deftest test-fac5-2 (fac5 20) fac20 (n i r))

; mutual recursion

(de fac6 (n)
    (fac6-aux 1 n 1) )

(de fac6-aux (i n r)
    (if (= i n)
        r
        (fac6-aux2 (1+ i)) ) )

(de fac6-aux2 (i+1)
    (fac6-aux i+1 n (* i+1 r)) )

(deftest test-fac6-1 (fac6 10) fac10 (n i r i+1))
(deftest test-fac6-2 (fac6 20) fac20 (n i r i+1))

; mutual recursion with anonymous function (let is expanded as a lambda)

(de fac7 (n)
    (fac7-aux 1 n 1) )

(de fac7-aux (i n r)
    (if (= i n)
        r
        (let ((i+1 (1+ i)))
            (fac7-aux i+1 n (* i+1 r)) ) ) )

(deftest test-fac7-1 (fac7 10) fac10 (n i r i+1))
(deftest test-fac7-2 (fac7 20) fac20 (n i r i+1))

; Y combinator

(de Y (f)
    ((lambda (x) (funcall x x)) `(lambda (x) (,f `(,x ,x)))) )

(de almost-fac (f)
    `(lambda (n)
        (if (= n 0)
            1
            (* n (funcall ,f (1- n))) ) ) )

(fvalue 'fac8 (Y (fvalue 'almost-fac)))

(deftest test-fac8-1 (fac8 10) fac10 (n))
(deftest test-fac8   (fac8 20) fac20 (n))
(deftest test-fac8-2 (fac8 15) fac15 (n))

; functional

(de fac9 (n)
    (reduce '* (iota n)) )

(deftest test-fac9-1 (fac9 10) fac10 (n))
(deftest test-fac9   (fac9 20) fac20 (n))
(deftest test-fac9-2 (fac9 15) fac15 (n))

(de fac10 (n)
    (apply '* (iota n)) )

(deftest test-fac10-1 (fac10 10) fac10 (n))
(deftest test-fac10   (fac10 20) fac20 (n))
(deftest test-fac10-2 (fac10 15) fac15 (n))

;;; fib

(setq fib15 610)
(setq fib30 832040)
(setq fib50 12586269025)

; recursion

(de fib1 (n)
    (if (< n 3)
        1
        (+ (fib1 (- n 1)) (fib1 (- n 2))) ) )

(deftest test-fib1 (fib1 12) 144 (n))

; tail recursion

(de fib2 (n)
    (if (< n 3)
        1
        (fib2-aux 2 n 1 1) ) )

(de fib2-aux (i n r r-1)
    (if (= i n)
        r
        (fib2-aux (1+ i) n (+ r r-1) r) ) )

(deftest test-fib2-1 (fib2 30) fib30 (n i r r-1))
(deftest test-fib2   (fib2 50) fib50 (n i r r-1))

; iteration

(de fib3 (n)
    (let ((i 1) (r 1) (r-1 0))
        (while (< i n)
            (incr i)
            (setq x r
                  r (+ r r-1)
                  r-1 x ) )
        r ) )

(deftest test-fib3-1 (fib3 30) fib30 (n i r r-1))
(deftest test-fib3   (fib3 50) fib50 (n i r r-1))

; memoization in list of results

(de fib4 (n)
    (let ((memo ()))
        (fib4-aux n) ) )

(de fib4-aux (n)
    (if (< n 3)
        1
        (let ((x (nthcdr (- n 3) memo)))
            (if x
                (car x)
                (let ((r (+ (fib4-aux (- n 1)) (fib4-aux (- n 2)))))
                    (setq memo (append1 memo r))
                    r ) ) ) ) )

(deftest test-fib4   (fib4 50) fib50 (n memo x r))
(deftest test-fib4-2 (fib4 12) 144   (n memo x r))

; memoization in a-list

(de fib5 (n)
    (let ((memo ()))
        (fib5-aux n) ) )

(de fib5-aux (n)
    (if (< n 3)
        1
        (let ((x (assoc n memo)))
            (if x
                (cdr x)
                (let ((r (+ (fib5-aux (- n 1)) (fib5-aux (- n 2)))))
                    (setq memo (acons n r memo))
                    r ) ) ) ) )

(deftest test-fib5   (fib5 50) fib50 (n memo x r))
(deftest test-fib5-2 (fib5 12) 144   (n memo x r))

; Y combinator

(de almost-fib (f)
    `(lambda (n)
        (if (< n 3)
            1
            (+ (funcall ,f (- n 1)) (funcall ,f (- n 2))) ) ) )

(fvalue 'fib6 (Y (fvalue 'almost-fib)))

(deftest test-fib6   (fib6 50) fib50 (n))
(deftest test-fib6-2 (fib6 10) 55    (n)) 

;;; ackermann

(setq ack-3-4 125)

(de ack (m n)
    (if (= m 0)
        (1+ n)
        (if (= n 0)
            (ack (1- m) 1)
            (ack (1- m) (ack m (1- n))) ) ) )

(deftest test-ack   (ack 3 4) 125 (m n))
(deftest test-ack-2 (ack 2 3) 9   (m n))

;;;  Hofstadter sequences (en.wikipedia.org/wiki/Hofstadter_sequence)

;def G(n):
;    return 0 if n == 0 else n - G(G(n - 1))

(de G (n)
    (if (= n 0)
        0
        (- n (G (G (1- n)))) ) )

(deftest test-G   (G 30) 19 (n))
(deftest test-G-2 (G 15) 9  (n))

;def H(n):
;    return 0 if n == 0 else n - H(H(H(n - 1)))

(de H (n)
    (if (= n 0)
        0
        (- n (H (H (H (1- n))))) ) )

(deftest test-H   (H 20) 14 (n))
(deftest test-H-2 (H 10) 7  (n))

;def F(n):
;    return 1 if n == 0 else n - M(F(n - 1))
;def M(n):
;    return 0 if n == 0 else n - F(M(n - 1))

(de F (n)
    (if (= n 0)
        1
        (- n (M (F (1- n)))) ) )

(de M (n)
    (if (= n 0)
        0
        (- n (F (M (1- n)))) ) )

(deftest test-F   (F 30) 19 (n))
(deftest test-F-2 (F 15) 9  (n))

;def Q(n):
;    return 1 if n <= 2 else Q(n - Q(n - 1)) + Q(n - Q(n - 2))

(de Q (n)
    (if (<= n 2)
        1
        (+ (Q (- n (Q (- n 1)))) (Q (- n (Q (- n 2)))) ) ) )

(deftest test-Q   (Q 15) 10 (n)) 
(deftest test-Q-2 (Q 10) 6  (n)) 

;;; collatz

; recursion

(de collatz1 (n)
    (if (= n 1)
        ()
        (if (= (% n 2) 1)
            (cons n (collatz1 (1+ (* 3 n))))
            (cons n (collatz1 (/ n 2))) ) ) )

(deftest test-collatz1   (length (collatz1 27)) 111 (n))
(deftest test-collatz1-2 (length (collatz1 25)) 23  (n))
    
; tail recursion    

(de collatz2 (n)
    (let ((head (cons () ())))
        (collatz2-aux n head)
        (cdr head) ) )

(de collatz2-aux (n tail)
    (print n)
    (if (= n 1)
        ()
        (if (< n 0)
            (error "integer overflow" 'collatz2 n)
            (if (= (% n 2) 1)
                (collatz2-aux (1+ (* 3 n)) (placdl tail n))
                (collatz2-aux (/ n 2) (placdl tail n)) ) ) ) )

(deftest test-collatz2 (length (collatz2 63728127)) 949 (n head tail))

;;; tak from Gabriel benchmarks

; tak

(de tak (x y z)
    (ifn (< y x)
        z
        (tak (tak (1- x) y z)
             (tak (1- y) z x)
             (tak (1- z) x y) ) ) ) 
             
(deftest test-tak (tak 18 12 6) 7 (x y z))
                          
; stak

(de stak (x y z)             
    (stak-aux) )
    
(de stak-aux ()
    (ifn (< y x)
        z
        (let ((x (let ((x (1- x))
                       (y y)
                       (z z) )
                     (stak-aux) )) 
              (y (let ((x (1- y))
                       (y z)
                       (z x) )
                     (stak-aux) )) 
              (z (let ((x (1- z))
                       (y x)
                       (z y) )
                     (stak-aux) )) )
            (stak-aux) ) ) )
            
(deftest test-stak (stak 18 12 6) 7 (x y z))

; ctak

(de ctak (x y z)
    (catch 'ctak (ctak-aux x y z)) )
    
(de ctak-aux (x y z)
    (ifn (< y x)
        (throw 'ctak z) 
        (ctak-aux
            (catch 'ctak 
                (ctak-aux (1- x) y z) )
            (catch 'ctak 
                (ctak-aux (1- y) z x) )
            (catch 'ctak 
                (ctak-aux (1- z) x y) ) ) ) )
     
(deftest test-ctak (ctak 18 12 6) 7 (x y z))

; takl
     
(de listn (n)
    (if (= n 0)
        ()
        (cons n (listn (- n 1))) ) )
 
(de shorterp (x y)
    (and y
        (or (null x)
            (shorterp (cdr x)
                      (cdr y) ) ) ) )
                     
(de mas (x y z)
    (ifn (shorterp y x)
        z
        (mas (mas (cdr x) y z)
             (mas (cdr y) z x)
             (mas (cdr z) x y)) ) )
 
(deftest test-takl (mas (listn 18) (listn 12) (listn 6)) (listn 7) (x y z))
                     
;;; long lists

(deftest test-iota1 (length (iota 1000)) 1000 (n l))

(deftest test-iota2   (car (last (iota 10000))) 10000 (n l))
(deftest test-iota2-2 (car (last (iota 1000))) 1000 (n l))

(deftest test-iota3 (length (reverse (iota 1000))) 1000 (n l))

;;; reverse

(de reverse1 (l)
    (ifn (cdr l)
        l
        (cons (car (reverse1 (cdr l)))
              (reverse1 (cons (car l) (reverse1 (cdr (reverse1 (cdr l)))))) ) ) )

(deftest test-reverse1   (reverse1 (iota 8)) (reverse (iota 8)) (l))
(deftest test-reverse1-2 (reverse1 (iota 5)) (reverse (iota 5)) (l))

;;; mutual recursion

; even/odd

(de even? (n)
    (if (= n 0)
        t
        (odd? (1- n)) ) )

(de odd? (p)
    (if (= p 0)
        nil
        (even? (1- p)) ) )

(deftest test-even?   (list (even? 10000) (even? 10001)) '(t ()) (n p))
(deftest test-even?-2 (list (even? 1000)  (even? 1001))  '(t ()) (n p))
(deftest test-even?-3 (list (even? 10000)  (even? 10001))  '(t ()) (n p))

(de 0mod3 (a)
    (if (= a 0)
        t
        (1mod3 (1- a)) ) )

(de 1mod3 (b)
    (if (= b 0)
        nil
        (2mod3 (1- b)) ) )

(de 2mod3 (c)
    (if (= c 0)
        nil
        (0mod3 (1- c)) ) )

; an automaton checking parity of numbers of A and B in a list (even number of A, odd number of B)

(de EvenEven (ee)
    ; entry point
    (and ee
        (selectq (car ee)
            (A (OddEven (cdr ee)))
            (B (EvenOdd (cdr ee)))
            (t (EvenEven (cdr ee))) ) ) )

(de OddEven (oe)
    (and oe
        (selectq (car oe)
            (A (EvenEven (cdr oe)))
            (B (OddOdd (cdr oe)))
            (t (OddEven (cdr oe))) ) ) )

(de EvenOdd (eo)
    (ifn eo
         t
        (selectq (car eo)
            (A (OddOdd (cdr eo)))
            (B (EvenEven (cdr eo)))
            (t (EvenOdd (cdr eo))) ) ) )

(de OddOdd (oo)
    (and oo
        (selectq (car oo)
            (A (EvenOdd (cdr oo)))
            (B (OddEven (cdr oo)))
            (t (OddOdd (cdr oo))) ) ) )

(de make-automaton-test (n)
    (let ((l ()))
        (repeat n
            (setq l (cons (nth (random 10) '(a b c d e f g h i j)) l)) )
        l ) )

(de is-evenA-oddB (l)
    ; test by counting if number of A is even and number of B is odd
    (let ((nb-A 0) (nb-B 0))
        (while l
            (selectq (car l)
                (A (incr nb-A))
                (B (incr nb-B)) )
            (nextl l) )
        (and (= (% nb-A 2) 0) (= (% nb-B 2) 1)) ) )

(de automatonAB-test (n)
    (let ((l (make-automaton-test n)))
        (eq (EvenEven l) (is-evenA-oddB l)) ) )

(deftest test-automatonAB (automatonAB-test 1000) t (n l ee eo oe oo nb-A nb-B))

;;; (de func ... (func ... (func ...))) recursion: list of symbols

(de randflat (n)
    (let ((l ()))
        (repeat n
            (newl l (nth (random 10) '(a b c d e f g h i j))) )
        l ) )

(de randtree (n)
    (randcut (randflat n)) )
    
(de randcut (l)
    (let ((len (length l)))
        (if (< len 2)
            l
            (let ((n (1+ (random (1- len)))))
                (cons (randcut (firstn n l)) (randcut (nthcdr n l))) ) ) ) )

(de list-of-symbols1 (e)
    (list-of-symbols1-aux e ()) )

(de list-of-symbols1-aux (e r)
    (if (atom e)
        (if (and e (symbolp e) (not (memq e r)))
            (cons e r)
            r )
        (list-of-symbols1-aux (car e)(list-of-symbols1-aux (cdr e) r)) ) )

(de list-of-symbols2 (e)
    (let ((r ()))
        (list-of-symbols2-aux e)
        r ) )

(de list-of-symbols2-aux (e)
    (if (atom e)
        (and e (symbolp e) (not (memq e r))
            (newl r e) )
        (list-of-symbols2-aux (car e))
        (list-of-symbols2-aux (cdr e)) ) )

(de list-of-symbols-test ()
    (let ((l (mapcar 'getdef '(prog1 prog2 mapc1 mapc mapcar1 mapcar mapcdr1 mapcdr))))
        (equal (sort '< (list-of-symbols1 l))(sort '< (list-of-symbols2 l))) ) )

(de list-of-symbols-test-2 ()
    (let ((l (randtree 10)))
        (equal (sort '< (list-of-symbols1 l))(sort '< (list-of-symbols2 l))) ) )

(deftest test-list-of-symbols   (list-of-symbols-test)   t (e r))
(deftest test-list-of-symbols-2 (list-of-symbols-test-2) t (e r))

;;; plists

(de test-plist-ops ()
    (and (progn (plist 'foo ())
                (equal (plist 'foo) ()) )
         (progn (addprop 'foo 42 'ind1)
                (equal (plist 'foo) '(ind1 42)) )
         (progn (addprop 'foo 42 'ind1)
                (equal (plist 'foo) '(ind1 42 ind1 42)) )
         (progn (remprop 'foo 'ind1)
                (equal (plist 'foo) '(ind1 42)) )
         (progn (putprop 'foo 42 'ind1)
                (equal (plist 'foo) '(ind1 42)) )
         (progn (putprop 'foo 'bar 'ind2)
                (equal (plist 'foo) '(ind2 bar ind1 42)) )
         (progn (putprop 'foo '(1 2 3) 'ind3)
                (equal (plist 'foo) '(ind3 (1 2 3) ind2 bar ind1 42)) )
         (progn ()
                (equal (mapcar (lambda (x) (getprop 'foo x)) '(ind1 ind2 ind3)) '(42 bar (1 2 3))) )
         (progn (remprop 'foo 'ind3)
                (equal (plist 'foo) '(ind2 bar ind1 42)) )
         (progn (remprop 'foo 'ind1)
                (equal (plist 'foo) '(ind2 bar)) )
         (progn (remprop 'foo 'ind2)
                (equal (plist 'foo) ()) )
         (progn (plist 'foo (copy '(ind1 bar bar 42)))
                ; plist new value must be copied if test is repeated as putprop uses rplaca
                (equal (getprop 'foo 'bar) 42) )
         (progn (putprop 'foo 13 'bar)
                (and (equal (getprop 'foo 'ind1) 'bar)(equal (getprop 'foo 'bar) '13)) )
) )

(deftest test-plist (test-plist-ops) t (x))

;;; alists

(de test-alist-ops ()
    (let ((alist ()))
        (and (progn (setq alist (acons 'ind1 42 alist))
                    (equal alist '((ind1 . 42))) )
             (progn (setq alist (acons 'ind1 666 alist))
                    (equal alist '((ind1 . 666)(ind1 . 42))) )
             (progn (setq alist (assq-delete 'ind1 alist))
                    (equal alist '((ind1 . 42))) )
             (progn (setq alist (acons 'ind2 'bar alist))
                    (equal alist '((ind2 . bar) (ind1 . 42))) )
             (progn (setq alist (acons 'ind3 '(1 2 3) alist))
                    (equal alist '((ind3 1 2 3) (ind2 . bar) (ind1 . 42))) )
             (progn ()
                    (equal (mapcar (lambda (x) (cassq x alist)) '(ind1 ind2 ind3)) '(42 bar (1 2 3))) )
             (progn (setq alist (assq-delete 'ind3 alist))
                    (equal alist '((ind2 . bar) (ind1 . 42))) )
             (progn (setq alist (assq-delete 'ind1 alist))
                    (equal alist '((ind2 . bar))) )
             (progn (setq alist (assq-delete 'ind2 alist))
                    (equal alist ()) )
) ) )

(deftest test-alist (test-alist-ops) t (x))

;;; sets

(de randnumberlist (n)
    (mapcar `(lambda () (random ,n)) (iota n)) )

(de test-set-ops (n)
    (let ((x (randnumberlist n))(y (randnumberlist n))(z (iota n)))
        (let ((x (intersection x x))(y (intersection y y))) ; remove duplicates
            (let ((r1 (difference z (intersection x y)))
                  (r2 (union (difference z x) (difference z y))) )
                (equal (sort '< r1) (sort '< r2)) ) ) ) )

(deftest test-sets   (test-set-ops 25) t (x y z r1 r2))
(deftest test-sets-2 (test-set-ops  6) t (x y z r1 r2))

;;; test strings

(de strrev1 (s)
    (let ((r "")(i 0)(l (strlen s)))
        (while (< i l)
            (setq r (+ (strnth s i) r))
            (incr i) )
        r ) )
        
(de strrev2 (s)
    (if (<= (strlen s) 1)
        s
        (+ (strnth (strrev2 (strsub s 1)) 0)
              (strrev2 (+ (strnth s 0) (strrev2 (strsub (strrev2 (strsub s 1)) 1)))) ) ) )

(deftest test-strrev (= (strrev1 "abcd") (strrev2 "abcd")) t (s r i l)) 
    
;;; tests of recursion optimization in if and while implementation

(de testiftest (n)
    (if (= n 0)
        t
        (if (testiftest (1- n))
            n
            42 ) ) )

(deftest test-iftest (testiftest 10) 10 (n))
    
(de testwhile1 (n)
    (if (= n 0)
        ()
        (if (= n 1)
            t
            (while (testwhile1 (1- n))
                ;(print n)
                (decr n) ) ) ) )

(deftest test-while1 (testwhile1 10) () (n))
    
(de testwhile2 (n)
    (if (= n 0)
        42
        (while (> n 0)
            (decr n)
            (testwhile2 n) ) ) )

(deftest test-while2 (testwhile2 10) () (n))
    
;;; test error exceptions

(de testexceptions ()
    (and 
        (eq
            (tag toperror ; test UndefSymError
                (value (gensym)) )
            'UndefSymError  ) 
        (eq
            (tag toperror ; test UndefFuncError
                (funcall (gensym)) )
            'UndefFuncError  ) 
        (eq
            (tag toperror ; test UndefFuncError
                (zig 3) )
            'UndefFuncError  ) 
        ;(eq
        ;    (tag toperror ; test UndefTagError
        ;        (throw (gensym)) )
        ;    'UndefTagError  ) 
        (eq
            (tag toperror ; test NotSymbolArgError
                (plist 1) )
            'NotSymbolArgError  ) 
        (eq
            (tag toperror ; test NotNumberArgError
                (let ((x (iota 10)))
                    (rplaca (last x) "not_a_number")
                    (mapadd x 0) ) )
            'NotNumberArgError  ) 
        (eq
            (tag toperror ; test NotStringArgError
                (let ((x (mapcar 'string (iota 10))))
                    (rplaca (last x) 42)
                    (mapadd x "") ) )
            'NotStringArgError  ) 
        (eq
            (tag toperror ; test NotConsArgError
                (rplaca 1 1) )
            'NotConsArgError )
        (eq
            (tag toperror ; test NotListArgError
                (car 1) )
            'NotListArgError )
        (eq
            (tag toperror ; test NotCharArgError
                (typech 1) )
            'NotCharArgError )
        (eq
            (tag toperror ; test NotVarError
                (value t nil) )
            'NotVarError )
        (eq
            (tag toperror ; test ArgNumberError
                (cons nil) )
            'ArgNumberError )
        (eq
            (tag toperror ; test ArgError
                (+ nil nil) )
            'ArgError )
        (eq
            (tag toperror ; test BindingError
                (de foo (n))
                (foo) )
            'BindingError  ) 
        (eq
            (tag toperror ; test IoError
                (openi "jhlqjjqjqgdljqd") )
            'IoError )
        (eq
            (tag toperror ; test IndexError
                (strnth "jhlqjjqjqgdljqd" 1000) )
            'IndexError )
) ) 

(de testexceptions2 ()
    (and
        (eq
            (tag toperror ; test NotNumberArgError
                (let ((x (iota 10)))
                    (rplaca (last x) "not_a_number")
                    (mapadd x 0) ) )
            'NotNumberArgError  ) 
) )               
        
(de mapadd (l s)
    (ifn l
        s
        (mapadd (cdr l) (+ s (car l))) ) )

(de zig (n) (zag n) )
        
(deftest test-exceptions (testexceptions) t (x l s n)) 

;;; test exception functions

(de testprotect (n)
    (let ((x ()))
        (tag foo
            (protect
                (if (< n 10)
                    (setq x 1)
                    (setq x 2)
                    (exit foo 3) )
                (setq x 42) ) )
        x ) )
        
(deftest test-protect (and (= (testprotect 1) 42)(= (testprotect 11) 42)) t (n))
    
(deftest test-try
    ; cf. try.l
    (testtry) t (n r e) )
    
;;; files (not included in test suite)

(de testfile1 ()
    (let ((in (openi "testing.l")))
        (with ((input in))
            (close in)
            (read) ) ) )
    
(de testfile2 ()
    (let ((out (openo "tmp.txt")))
        (with ((output out))
            (close out)
            (print) ) ) )
    
;;; test

(setq no-opt-suite
    '(test-fac1-2 test-fac2-2 test-fac3-2 test-fac4-2 test-fac5-2
      test-fac6-2 test-fac7-2 test-fac8 test-fac9 test-fac10
      test-fib1 test-fib2 test-fib3 test-fib4 test-fib5
      test-ack test-G test-H test-F test-Q
      test-collatz1 test-reverse1
      test-list-of-symbols
      test-plist test-alist test-sets test-strrev
      test-iftest test-while1 test-while2 
      test-exceptions test-protect 
      test-try
) )

(setq tail-opt-suite
    '(test-collatz2 test-iota1 test-iota2 test-iota3) )

(setq mutual-opt-suite
    '(test-even? test-automatonAB) )

(setq no-opt-suite-2
    '(test-fac1-2 test-fac2-2 test-fac3-2 test-fac4-2 test-fac5-2
      test-fac6-2 test-fac7-2
      ;test-fac8-2
      test-fac8-1
      test-fac9-2 test-fac10-2
      test-fib1 test-fib2 test-fib3 
      test-fib4-2
      test-fib5-2
      test-fib6-2
      test-ack-2  
      test-G-2  
      test-H-2 
      test-F-2   
      test-Q-2
      test-collatz1-2
      test-reverse1-2
      test-list-of-symbols-2 
      test-plist test-alist test-sets-2
      test-strrev
      test-iftest test-while1 test-while2
      test-exceptions
      test-protect 
      test-try
) )

(setq no-opt-suite-3
    '(test-fac1-1 test-fac2-1 test-fac3-1 test-fac4-1 test-fac5-1
      test-fac6-1 test-fac7-1 test-fac8-1 test-fac9-1 test-fac10-1
      test-fib1 test-fib2-1 test-fib3-1
      test-fib4-2
      test-fib5-2
      test-fib6-2
      test-ack-2  
      test-G-2  
      test-H-2 
      test-F-2   
      test-Q-2
      test-collatz1-2
      test-reverse1-2
      test-list-of-symbols-2 
      test-plist test-alist test-sets-2
      test-strrev
      test-iftest test-while1 test-while2
      test-exceptions
      test-protect 
      test-try
) )

(setq tail-opt-suite-2
    '(test-collatz2 test-iota1 test-iota2-2 test-iota3) )

(setq tail-opt-suite-3
    (append no-opt-suite-3'(test-iota1 test-iota2-2 test-iota3)) )

(setq mutual-opt-suite-2
    '(test-even?-2 test-automatonAB) )
    
(setq mutual-opt-suite-3
    '(test-even?-3 test-automatonAB) )
    
(setq all-opt-suite (append no-opt-suite tail-opt-suite mutual-opt-suite))   
(setq all-opt-suite-2 (append no-opt-suite-2 tail-opt-suite-2 mutual-opt-suite-2))   
(setq all-opt-suite-3 (append no-opt-suite-3 tail-opt-suite-3 mutual-opt-suite-3))   

(setq tak-suite '(test-tak test-stak test-ctak test-takl))

