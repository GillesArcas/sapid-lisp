; sapid lisp
; Testing
; gilles.arcas@gmail.com, https://github.com/GillesArcas/sapid-lisp
; MIT license

; This module enables to define tests and test suites.

; For each test, three features are checked:
; - the result of the function to be tested,
; - the restoration of the context, at least the values of the variables
;   specified in the test,
; - the evalution stack (the stack explicitely handled by the evaluator) by
;   comparing its height before and after the test.

; A test is defined with deftest:

; (deftest sometest <expression to test> <expression result> <list of variables to check>)

; A test suite is just a list of tests defined with deftest

; (setq test-suite '(test1 test2))

; A test suite is launched with the test function:

; (test test-suite)

; To get a precise timing, the bench function repeats a test suite the given
; number of time:

; (bench <test suite> <repetition>)


; global alist of all tests

(setq *testing* ())

; test defining function

(dm deftest x
    `(newl *testing* ',x) )

; launching a test suite

(de test (test-suite)
    (start-test)
    (let ((t0 (time)))
        (if (apply 'and (mapcar (lambda (x) (apply 'check (assq x *testing*))) test-suite))
            (print "All tests ok.")
            (print "Test suite failed.") )
        (print "Timing : " (- (time) t0)) ) )

(de test (test-suite)
    (makunbound 'check-stack)    
    ; process null test to get stack high with the correct value (same number of instructions as actual test)
    (let ((t0 (time)))
        (if (apply 'and (mapcar (lambda (x) (apply 'check (assq x *testing*))) '(null-test)))
            () 
            () )
        () ) 
    ; process test suite
    (let ((t0 (time)))
        (if (apply 'and (mapcar (lambda (x) (apply 'check (assq x *testing*))) test-suite))
            (print "All tests ok.")
            (print "Test suite failed.") )
        (print "Timing : " (- (time) t0)) )
    t )

(dm check (testname expr res lvar) 
    (let ((lval (mapcar (lambda (x) (random 10000)) lvar))(t0 (time)))
        `(let ,(mapcar (lambda (x y) (list x y)) lvar lval)
            (prin "Testing " ' ,testname ": " ',expr " : ")
            (if (test-result ,expr ,res ',lvar ',lval)
                (print "Ok (" (- (time) ,t0) ")")
                (print "Failure")
                () ) ) ) )

(dm check-null-test (testname expr res lvar) 
    `(let ()
        (if (test-result ()()()()) () ()) ) )

(de test-result (result expected-result lvar lval)
    (and
        (equal result expected-result)
        (check-stack)
        (check-env lvar lval)
        ) )

(de check-stack ()
    (let ((len-stack (length (stack))))
        (ifn (boundp 'check-stack)
            (setq check-stack len-stack)    ; store stack length after first test, returns stack length ie true
            (= check-stack len-stack) ) ) ) ; stack must have same length after each test

(de check-stackXXX ()
    (let ((stack (stack)))
        (mapc (lambda (x) (print (car x))) stack)
        (let ((len-stack (length stack)))
            (ifn (boundp 'check-stack)
                (setq check-stack len-stack)      ; store stack length after first test, returns stack length ie true
                (print check-stack " " len-stack)
                (= check-stack len-stack) ) ) ) ) ; stack must have same length after each test

(de check-env (lvar lval)
    ;(print "check-env " lvar " " lval)
    (or (null lvar)
        (and ;(print ">> " (car lvar) " " (value (car lvar)) " " (car lval))
              (eq (value (car lvar)) (car lval)) ; TODO = ?
             (check-env (cdr lvar) (cdr lval)) ) ) )

; null test

(deftest null-test () () ())
             
; benchmarking

(de bench (suite n)
    "Repeats n times test suite."
    (let ((t-total 0) (t0 0))
        (repeat n
            (setq t0 (time))
            (funcall 'test suite)
            (incr t-total (- (time) t0)) )
        (print "Timing: total time : " t-total " mean time : " (/ t-total n)) ) )
