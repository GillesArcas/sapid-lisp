; sapid lisp
; Standard functions
; gilles.arcas@gmail.com, https://github.com/GillesArcas/sapid-lisp
; MIT license

;;; Summary

; Evaluation functions
;   eval, evlis, eprogn, progn, prog1, prog2, quote

; Application functions
;   apply, funcall

; Map functions
;   mapc, mapcar, mapcdr, filter, every, some, reduce

; Environment functions
;   let, slet, with

; Control functions
;   if, ifn, when, unless, or, and, cond, selectq,
;   while, until, repeat

; Non local control functions
;   catch, tag, throw, exit, protect, lock

; Predicates
;   symbolp, numberp, stringp, consp,
;   null, not, atom, listp, constantp, variablep,
;   eq, equal, neq, nequal

; Symbols
;   oblist, value, boundp, makunbound, setq, newl, nextl, incr, decr,
;   fvalue, de, dm, dmd, typefn, getdef, macroexpand, gensym, let-unique

; Property lists
;   plist, getprop, addprop, putprop, remprop

; Lists
;   car, cdr, c..r, c...r, nth, nthcdr, last, length, memq, member,
;   cons, list, mcons, append1, append, copy, firstn, lastn, reverse,
;   rplaca, rplacd, rplac, displace, placdl, nconc, nreverse

; Association lists
;   acons, assq, cassq, assoc, cassoc, sublis, assq-delete

; Lists as sets
;   union, intersection, difference

; Usual lists
;   kwote, makelist, iota

; Sorting
;   sort, remove-duplicates

; Polymorphic functions
;   =, !=, <, >, <=, >=, +

; Numbers
;   -, *, /, %, power, 1+, 1-, min, max, abs, random

; Strings
;   strlen, strnth, strpos, strsub, symbol, unique, number, string

; Streams
;   openi, openo, close, input, output, prompt

; Reading
;   readchar, peekchar, readline, typech, read, readlines, load, autoload, dmc

; Printing
;   print, prin, terpri

; System and environment
;   toplevel, error, end, time, timing

;;; Evaluation functions

(describe eval (x)
    "Evaluates x and returns the result evaluated." )

(describe evlis (l)
    "Evaluates l and returns the list of elements of l evaluated." )

(describe eprogn (l)
    "Evaluates l, evaluates all elements in the result in sequence, returns last evaluated element." )

(describe progn l
    "Evaluates all elements in l in sequence, returns the last one." )

(dmd prog1 (x . l)
    "Evaluates all elements in l in sequence, returns the first evaluated element."
    (let-unique result
        `(let ((,result ,x))
            ,(optform 'progn l)
            ,result ) ) )

(dmd prog2 (x . l)
    "Evaluates all elements in l in sequence, returns the second evaluated element."
    `(progn ,x (prog1 ,@l)) )

(describe quote (x)
    "Returns x without any evaluation." )

;;; Application functions

(describe apply (f l)
    "Applies f, which must be a function (symbol or lambda), to arguments in l." )

(de funcall (f . l)
    "Applies f, which must be a function (symbol or lambda), to arguments in l."
    (apply f l) )

;;; Map functions

(de mapc1 (f l)
    (while (consp l)
        (funcall f (car l))
        (setq l (cdr l)) ) )
        
(de mapc (f . l)
    "(mapc f l1 l2 ...)"
    "Applies f to cars of l1, l2, ..., then to cadrs, etc."
    "Returns nil."
    "f must be a function."
    (ifn (cdr l)
        (mapc1 f (car l))
        (while (every 'consp l)
            (apply f (mapcar1 'car l))
            (setq l (mapcar1 'cdr l)) ) ) )

(de mapcar1 (f l)
    ; mapcar1: only one argument. Used when defining let and cannot use let.
    ((lambda (head tail)
        (setq tail head)
        (while (consp l)
            (setq tail (placdl tail (funcall f (car l))))
            (setq l (cdr l)) )
        (cdr head) )
     (cons ()()) () ) )
    
(de mapcar (f . l)
    "(mapcar f l1 l2 ...)"
    "Applies f to cars of l1, l2, ..., then to cadrs, etc."
    "Returns the list of results."
    "f must be a function."
    (ifn (cdr l)
        (mapcar1 f (car l))
        (slet ((head (cons () ())) (tail head))
              (while (every 'consp l)
                  (setq tail (placdl tail (apply f (mapcar1 'car l))))
                  (setq l (mapcar1 'cdr l)) )
          (cdr head) ) ) )
    
(de mapcdr1 (f l)
    ; mapcdr1: only one argument
    (slet ((head (cons ()()))(tail head))
        (while l
            (setq tail (placdl tail (funcall f l)))
            (setq l (cdr l)) )
        (cdr head) ) )
    
(de mapcdr (f . l)
    "(mapcdr f l1 l2 ...)"
    "Applies f to cdrs of l1, l2, ..., then to cddrs, etc."
    "Returns the list of results."
    "f must be a function."
    (ifn (cdr l)
        (mapcdr1 f (car l))
        (slet ((head (cons ()())) (tail head))
              (while (every 'consp l)
                  (setq tail (placdl tail (apply f (mapcdr1 'car l))))
                  (setq l (mapcar1 (lambda (x) (cdr x)) l)) )
          (cdr head) ) ) )
    
(de filter (f l)
    "Returns the list of elements in l true for predicate f."
    (slet ((head (cons ()())) (tail head))
        (while l
            (if (funcall f (car l))
                (setq tail (placdl tail (car l))) )
            (setq l (cdr l)) )
        (cdr head) ) )
        
; (every f l) (some f l) (reduce f l)

(de every (f l)
    "Applies f to all elements in l. Returns t if all elements are true."
    (or (null l) (and (funcall f (car l)) (every f (cdr l)))) )

(de some (f l)
    "Applies f to all elements in l. Returns t if at least one element is true."
    (and l (or (funcall f (car l)) (some f (cdr l)))) )

(de reduce (f l)
    "(reduce f '(a b c d)) is equivalent to (f (f (f a b) c) d)."
    (if (atom l)
        ()
        (if (atom (cdr l))
            (car l)
            (let ((r (funcall f (car l) (cadr l)))
                  (l (cddr l)) )
                (while l
                    (setq r (funcall f r (car l)))
                    (nextl l) )
                r ) ) ) )

;;; Environment functions

(dmd let (x . y)
    "Binds symbols to values in parallel and evaluates a body."
    "(let ((v1 x1)(v2 x2)) body) is equivalent to ((lambda (v1 v2) body) x1 x2)"
    "If a symbol follows the keyword let, it gives a name to the lambda and"
    "can be called recursively."
    (if (and x (symbolp x))
        `(letn ,x ,@y)
        `((lambda ,(mapcar 'car x) ,@y) ,@(mapcar 'cadr x) ) ) )

(dmd letn (name l . body)
    ; helper
    (let-unique bak
        (slet ((lvar (mapcar 'car l))
               (larg (mapcar 'cadr l))
               (def  (mcons 'lambda lvar body)) )
            `(let ((,bak (fvalue ',name)))
                (protect
                    (progn
                        (fvalue ',name ',def)
                        (,name ,@larg) )
                    (fvalue ',name ,bak) ) ) ) ) )

(dmd slet (x . y)
    "Sequential let. Same as let except bindings are made in sequence."
    (if (atom x)
        `(progn ,@y)
        `(let ((,(caar x) ,(cadar x))) (slet ,(cdr x) ,@y)) ) )

(dmd with (l . body)
    "Sets values for 0/1 argument and 1/2 argument functions. Evaluates the"
    "body and restore previous values."
    "Ex: (with ((input handle)) ...) reads on handle and restores previous"
    "input stream."
    (slet ((lvar (mapcar (lambda (x) (gensym)) l))
           (save (mapcar (lambda (x y) (list x (firstn (1- (length y)) y)))
                          lvar
                          l ))
           (restore (mapcar (lambda (x y) (append1 (firstn (1- (length y)) y) x))
                          lvar
                          l )) )
        `(let ,save
            (protect
                (progn ,@l ,@body)
                ,@restore ) ) ) )

;;; Control functions

(describe if (x y . z)
    "If test x is true, evaluates y, else evaluates all expressions in z." )

(dmd ifn (x . y)
    "Equivalent to (if (not x) . y)"
    `(if (null ,x) ,@y) )

(dmd when (x . y)
    "If test x is true, evaluates all expressions in y."
    `(if ,x ,(optform 'progn y)) )

(dmd unless (x . y)
    "If test x is false, evaluates all expressions in y."
    `(ifn ,x ,(optform 'progn y)) )

(dmd binary-or (x y)
    (let-unique u
        `(let ((,u ,x)) (if ,u ,u ,y)) ) )

(dmd binary-and (x y)
    `(ifn ,x () ,y) )

(dmd or l
    "Returns the value of the first non null expression in l, nil if none."
    (reduce-macro 'or 'binary-or () l) )

(dmd and l
    "If all expressions in l are true, returns the last one, nil otherwise."
    (reduce-macro 'and 'binary-and t l) )

; Selectors

(dmd cond (e . e*)
    "(cond (test1 seq1) ... (testN seqN))"
    "Executes conditionnaly one of the sequences seq1 .. seqN depending"
    "on the values of tests."
    ; expands cond as a sequence of if
    (if (atom e*)
        (if (eq (car e) t)
            (if (and (atom (cddr e)) (consp (cadr e)))
                (cadr e)
                (cons 'progn (cdr e)) )
            (cons 'when e) )
        `(if ,(car e)
             ,(optform 'progn (cdr e))
              (cond ,@e*) ) ) )

(dmd selectq (selectq-value . clauses)
    "(selectq value (key1 seq1) ... (keyN seqN))"
    "Executes conditionnaly one of the sequences seq1 .. seqN depending"
    "on the given evaluated value. A list of keys may be found in position"
    "of key. Keys are not evaluated."
    (let-unique selector
        `(let ((,selector ,selectq-value))
            (cond ,@(mapcar 'selectq-cond clauses)) ) ) )

(de selectq-cond (selectq-clause) 
    ; transforms a select clause into a cond clause
    (if (eq (car selectq-clause) t)
        selectq-clause
        (let ((func (if (atom (car selectq-clause)) 'equal 'member)))
            `((,func ,selector ,(opkwote (car selectq-clause))) ,@(cdr selectq-clause)) ) ) )

; Loops

(describe while (x . y)
    "Evaluates all expressions in l while test x is true." )

(dmd until (x . y)
    "Evaluates all expressions in l until test x becomes true."
    (let-unique value
        `(progn (while (not (setq ,value ,x)) ,@y) ,value) ) )

(dmd repeat (n . l)
    "Repeats n times expression l."
    (let-unique count
        `(let ((,count ,n))
            (while (> ,count 0)
                ,@l
                (decr ,count) ) ) ) )

;;; Non local control functions

(dmd catch (expr . body)
    "(catch exception body)"
    "When an exception is triggered (with throw or exit) during evaluation of"
    "body, the process is interrupted and the value of exit is returned as"
    "value of catch." 
    "expr must be evaluated to a symbol."
    (let-unique catch-tag
       `(let ((,catch-tag ,expr))
           (lock (lambda (tag val)
                      (cond
                          ((null tag) val)
                          ((eq tag ,catch-tag) val)
                          (t (throw tag val)) ) )
                  ,@body) ) ) )

(describe tag (sym . body)
    "(tag exception body)"
    "When an exception is triggered (with throw or exit) during evaluation of"
    "body, the process is interrupted and the value of exit is returned as"
    "value of tag." 
    "sym must be a symbol.")

(describe throw (expr . body)
   "Interrupts normal flow of instructions, evaluates value of body, and"
   "returns it as value of the enclosing catch or tag."
   "expr must be evaluated to a symbol." )
          
(describe exit (sym . body)
    "Interrupts normal flow of instructions, evaluates value of body, and"
    "returns it as value of the enclosing tag."
    "sym must be a symbol.")

(dmd protect (e1 . e*)
    "Returns evaluation of e1 but always evaluates e*, even in case of exception in e1."
   `(lock (lambda (tag val)
              (progn ,@e*)
              (if tag
                  (throw tag val)
                  val ) )
          ,e1) )
          
(describe lock (lock-function . body)
    "lock-function is a function with two arguments, a tag and an expression." 
    "If during evaluation of body there is an exception, the lock-function is"
    "called with the name and the result of the exception. If there is no"
    "exception, the lock-function is called with nil as first argument and" 
    "evaluation of body as second argument." )
    
;;; Predicates

; Types

(describe symbolp (x)
    "Returns t or nil whether its argument is a symbol." )

(describe numberp (x)
    "Returns t or nil whether its argument is a number." )

(describe stringp (x)
    "Returns t or nil whether its argument is a string." )

(describe consp (x)
    "Returns t or nil whether its argument is a cons." )

(de null (x)
    "Tests equality with nil."
    (eq x ()) )

(de not (x)
    "Negates x, same as testing equality with nil."
    (eq x ()) )

(de atom (x)
    "True if x is not a cons, false otherwise."
    (not (consp x)) )

(de listp (x)
    "True if x is nil or a cons, false otherwise."
    (or (null x) (consp x)) )

(de constantp (x)
    "True if x is nil, t, a number or a string."
    (or (null x)
        (eq x t)
        (numberp x)
        (stringp x) ) )

(de variablep (x)
    "True if x is a symbol different from nil and t."
    (and (symbolp x) (neq x nil) (neq x t)) )

; Equality

(describe eq (x y)
    "Equality of internal representations." )

(de equal (x y)
    "Equality of external representations."
    (if (eq x y)
        t
        (ifn (and (consp x) (consp y))
            (= x y)
            (and (equal (car x) (car y))
                 (equal (cdr x) (cdr y)) ) ) ) )

(de neq (x y)
    "Same as (not (eq x y))"
    (not (eq x y)) )

(de nequal (x y)
    "Same as (not (equal x y))"
    (not (equal x y)) )

;;; Symbols

(describe oblist ()
    "Returns the list of all current symbols." )

; Access to cell value

(describe value (x . y)
    "(value 'x) returns the value of x as a variable."
    "(value 'x y) sets y as the value of x as a variable and returns y." )
    
(describe makunbound (x)
    "Removes the value of x. Accessing to the value of x raises an error." )

(describe boundp (x)
    "Returns t if the value of x is defined, nil otherwise." )

(dmd setq (x y . z)
    "(setq sym1 val1 ... symN valN)"
    "Sets sequentially values to symbols. Symbols are not evaluated."
    (ifn z
        `(value ',x ,y)
        `(progn
              (value ',x ,y)
              (setq ,@z) ) ) )

(dmd newl (s e)
    "Pushes an element at beginning of s which must be evaluated as a list."
    `(setq ,s (cons ,e ,s)) )

(dmd nextl (s)
    "Pops an element at beginning of s which must be evaluated as a list."
    `(prog1
        (car ,s)
        (setq ,s (cdr ,s)) ) )

(dmd incr (s . n)
    "Adds one to the value of s which must be evaluated as a number."
    `(setq ,s (+ ,s ,(ifn n 1 (car n)))) )

(dmd decr (s . n)
    "Substracts one to the value of s which must be evaluated as a number."
    `(setq ,s (- ,s ,(ifn n 1 (car n)))) )

; Access to functional value

(describe fvalue (x . y)
    "(value 'x) returns the functionnal value of x."
    "(value 'x y) sets y as the functionnal value of x and returns y." )
    
(describe de (x . y)
    "Defines x as a lambda function." )

(describe dm (x . y)
    "Defines x as a macro function." )

(describe dmd (x . y)
    "Defines x as a displace macro function." )

(de typefn (x)
    "Returns the type of a function."
    (car (fvalue x)) )

(de getdef (x)
    "Returns the definition form of a function."
    (let ((fv (fvalue x)))
        (selectq (car fv)
            (lambda (mcons 'de x (cdr fv)))
            (macro  (mcons 'dm x (cdr fv)))
            (dmacro (mcons 'dmd x (cdr fv)))
            (t      (mcons 'ds x fv)) ) ) )

(de macroexpand (e)
    "Returns macro expansion of expression e."
    (if (atom e)
        e
        (let ((head (car e)) (tail (mapcar 'macroexpand (cdr e))))
            (if (atom head)
                (ifn (memq (typefn head) '(macro dmacro))
                    (cons head tail)
                    (apply (cons 'lambda (cdr (fvalue head))) tail) )
                (ifn (memq (car head) '(macro dmacro))
                    (cons head tail)
                    (apply (cons 'lambda (cdr head)) tail) ) ) ) ) )

; Symbol generator

(setq *gensym-root* "g")

(setq *gensym-count* 1000)

(de gensym ()
    "Generates a new symbol. This symbol is not interned i.e. reading a"
    "symbol with the same name produces another symbol."
    (incr *gensym-count*)
    (unique (+ *gensym-root* (string *gensym-count*))) )

(dm let-unique (sym . progn)
    "(let-unique sym ...) is equivalent to (let ((sym (gensym))) ...)."
    ; considers only one symbol
    `(let ((,sym (gensym)))
        ,@progn) )

;;; Property lists

(describe plist (sym x)
    "If x is present, sets the plist of symbol sym with x. In any case, returns the P-list of sym." )

;(de memprop.expr (sym ind) TODO en subr en python
(de memprop (sym ind)
    "Returns the sublist of plist starting with indicator ind."
    (let ((list (plist sym)))
        (while (and (consp list) (neq (car list) ind))
            (setq list (cddr list)) )
        list ) )
    
(describe memprop (sym ind)
    "Returns the sublist of plist starting with indicator ind." )
    
(de getprop (sym ind)
    "Returns the value associated with indicator ind."
    (car (cdr (memprop sym ind))) )
        
(de addprop (sym e ind)
    "Adds without testing unicity the value e under indicator ind. Returns e."
    (plist sym (mcons ind e (plist sym)))
    e )

(de putprop (sym e ind)
    "Adds with testing unicity the value e under indicator ind. Returns e."
    (let ((x (memprop sym ind)))
        (ifn x
            (addprop sym e ind)
            (rplaca (cdr x) e) ) )
    e )

(de remprop (sym ind)
    "Remove indicator in plist of sym. Returns nil."
    (let ((pl (plist sym)) (pl-prev ()))
        (while (and pl (neq (car pl) ind))
            (setq pl-prev pl)
            (setq pl (cddr pl)) )
        (when pl
            (if pl-prev
                (rplacd (cdr pl-prev) (cddr pl))
                (plist sym (cddr pl)) ) ) ) )

;;; Lists

; Elements

(describe car (l)
    "Returns first element of list l." )

(describe cdr (l)
    "Returns all less first elements of list l." )

(de caar  (l) (car (car l)))
(de cadr  (l) (car (cdr l)))
(de cdar  (l) (cdr (car l)))
(de cddr  (l) (cdr (cdr l)))

(de caaar (l) (car (car (car l))))
(de caadr (l) (car (car (cdr l))))
(de cadar (l) (car (cdr (car l))))
(de caddr (l) (car (cdr (cdr l))))
(de cdaar (l) (cdr (car (car l))))
(de cdadr (l) (cdr (car (cdr l))))
(de cddar (l) (cdr (cdr (car l))))
(de cdddr (l) (cdr (cdr (cdr l))))

(de nth (n l)
    "Returns 0-based nth car of l, (nth 0 l) --> (car l), (nth 1 l) --> (cadr l), ..."
    (car (nthcdr n l)) )

(describe nthcdr (n l)
    "Returns nth cdr of l, (nthcdr 0 l) --> l, (nthcdr 1 l) --> (cdr l), ..." )

(de last (x)
    "Returns the last element in x."
    (if (atom x)
        x
        (if (atom (cdr x))
            x
            (last (cdr x)) ) ) )

(de length (l)
    "Returns the length of list l (number of cons)."
    (let aux ((l l) (n 0))
        (if (atom l)
            n
            (aux (cdr l) (1+ n)) ) ) )

; Membership

(de memq (e l)
    "Tests membership of e in l using eq."
    (if (atom l)
        ()
        (if (eq e (car l))
            l
            (memq e (cdr l)) ) ) )

(de memq (e l)
    "Tests membership of e in l using eq."
    (while (and (consp l) (neq e (car l)))
        (setq l (cdr l)) )
    (consp l) )

(de member (e l)
    "Tests membership of e in l using equal."
    (if (atom l)
        ()
        (if (equal e (car l))
            l
            (member e (cdr l)) ) ) )

; Construction

(describe cons (x y)
    "Adds x in front of list y." )

(de list x
    "Makes a list with all its arguments."
    x )

(dmd mcons x
    "Multiple conses."
    "(mcons x1 .. xM xN) is equivalent to (cons x1 (cons ... (cons xM xN)))."
    (if (atom (cddr x))
        (cons 'cons x)
        (list 'cons (car x) (cons 'mcons (cdr x))) ) )

(de append1 (l e)
    "Appends e at end of l."
    (append-aux l (list e)))

(de append x
    "Appends a list of lists."
    (if (atom x)
        ()
        (append-aux (car x)
            (if (atom (cddr x))
                (cadr x)
                (apply 'append (cdr x)) ) ) ) )

(de append-aux (l1 l2)
    (if (atom l1)
        l2
        (cons (car l1) (append-aux (cdr l1) l2)) ) )

(de append-aux (l1 l2)
    (slet ((head (cons ()())) (tail head))
        (while (consp l1)
            (setq tail (placdl tail (car l1)))
            (setq l1 (cdr l1)) )
        (rplacd tail l2)
        (cdr head) ) )        
    
(de copy (x)
    "Deep copy of expression x (sublists are copied)."
    (slet ((head (cons ()())) (tail head))
        (while (consp x)
            (setq tail (placdl tail (copy (car x))))
            (setq x (cdr x)) )
        (rplacd tail x)
        (cdr head) ) )        
    
(de copy-iter (x)
    "Iterative version of copy."
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
        
(de firstn (n l)
    "Returns n first elements in list l."
    (let ((head (cons ()())))
        (firstn-aux n l head)
        (cdr head) ) )
        
(de firstn-aux (n l tail)
    (if (or (atom l)(< n 1))
        ()
        (firstn-aux (1- n) (cdr l) (placdl tail (car l))) ) )
            
(de lastn (n l)
    "Returns n last elements in list l."
    (nthcdr (- (length l) n) l) )

(de reverse (l)
    "Reverse list l."
    (reverse-aux l ()) )

(de reverse-aux (l r)
    (if (atom l)
        r
        (reverse-aux (cdr l) (cons (car l) r))  ) )

; Physical modification of lists

(describe rplaca (l e)
    "Replaces the car of l with e. Returns l." )

(describe rplacd (l e)
    "Replaces the cdr of l with e. Returns l." )

(de rplac (l e1 e2)
    "Replaces car and cdr of l with e1 and e2. Returns l."
    (rplaca l e1)
    (rplacd l e2) )

(de displace (l1 l2)
    "Replaces car and cdr of l1 with car and cdr of l2. Returns l1."
    (rplaca l1 (car l2))
    (rplacd l1 (cdr l2)) )

(de placdl (l e) 
    "Appends physically e to l and returns the cons added to l."
    (cdr (rplacd l (cons e ()))) )

(de nconc x
    "Physically concatenates lists."
    (if (atom x)
        ()
        (if (atom (cdr x))
            (car x)
            (rplacd (last (car x)) (apply 'nconc (cdr x)))
            (car x) ) ) )

(de nreverse (l)
    "Physically reverses list l."
    (if (consp l)
        (let ((l l) (l1 ()) (x ()))
            (while (consp (cdr l))
                (setq x (cdr l))
                (setq l1 (rplacd l l1))
                (setq l x) )
            (rplacd l l1) ) ) )

; Association lists

(de acons (key value alist)
    "Adds a pair (key value) to alist."
    (cons (cons key value) alist) )

(de assq (key alist)
    "Returns first association for key in alist. Uses eq."
    (if (atom alist)
        ()
        (if (and (consp (car alist)) (eq key (caar alist)))
            (car alist)
            (assq key (cdr alist))) ) )

(de cassq (key alist)
    "Returns first value associated with key in alist. Uses eq."
    (let ((l (assq key alist)))
        (if (atom l)
            ()
            (cdr l) ) ) )

(de assoc (key alist)
    "Returns first association for key in alist. Uses equal."
    (if (atom alist)
        ()
        (if (and (consp (car alist)) (equal key (caar alist)))
            (car alist)
            (assoc key (cdr alist))) ) )

(de cassoc (key alist)
     "Returns first value associated with key in alist. Uses equal."
    (let ((l (assoc key alist)))
        (if (atom l)
            ()
            (cdr l) ) ) )

(de sublis (alist s)
    "Returns a copy of s where occurrences of the keys from A-list alist"
    "are replaced by their values."
    (if (atom s)
        (let ((x (assq s alist)))
            (if x (cdr x) s) )
        (let ((car (sublis alist (car s)))
              (cdr (sublis alist (cdr s))) )
            (if (and (eq car (car s))
                     (eq cdr (cdr s)) )
                s
                (cons car cdr) ) ) ) )

(de assq-delete (key alist)
    "Deletes first occurrence of association with key in alist."
    (if alist 
        (if (eq key (caar alist))
            (cdr alist)
            (cons (car alist) (assq-delete key (cdr alist))) ) ) )
            
; Sets

(de union (l1 l2)
    "Returns the list of all elements in l1 or l2."
    (let ((r l2))
        (while l1
            (ifn (member (car l1) r)
                (newl r (car l1)) )
            (nextl l1) )
        r ) )

(de intersection (l1 l2)
    "Returns the list of all elements in l1 and l2."
    (let ((r ()))
        (while l1
            (if (member (car l1) l2)
                (newl r (car l1)) )
            (nextl l1) )
        r ) )

(de difference (l1 l2)
    "Returns the list of all elements in l1 but not in l2."
    (let ((r ()))
        (while l1
            (ifn (member (car l1) l2)
                (newl r (car l1)) )
            (nextl l1) )
        r ) )

; Useful lists

(de kwote (x)
    "Returns the list (quote x)."
    (list 'quote x) )

(de makelist (n e)
    "Returns a list of n elements equal to e."
    (if (<= n 0)
        ()
        (cons e (makelist (1- n) e)) ) )

(de iota (n)
    "Generates a list of n elements from 1 to n."
    (iota-aux n ()) )

(de iota-aux (n l)
    (if (= n 0)
        l
        (iota-aux (1- n) (cons n l)) ) )

; Sorting

(de sort (f l)
    "Sorts list l according to predicate f."
    (sort-0 f l 'sort-end ()) )

(de sort-0 (f l cont stack)
    (ifn (cdr l)
        (funcall cont f l stack)
        (let ((n (/ (length l) 2)))
            (sort-0 f (firstn n l) 'sort-1 (mcons (nthcdr n l) cont stack)) ) ) )

(de sort-1 (f l stack)
    (sort-0 f (car stack) 'sort-2 (cons l (cdr stack))) )

(de sort-2 (f l stack)
    (funcall (cadr stack) f (fusion f (car stack) l) (cddr stack)) )

(de sort-end (f l stack)
    l )

(de fusion (f l1 l2)
    (slet ((head (cons ()())) (tail head))
        (while (and (consp l1) (consp l2))
            (if (funcall f (car l1) (car l2))
                (setq tail (placdl tail (car l1)) l1 (cdr l1))
                (setq tail (placdl tail (car l2)) l2 (cdr l2)) ) )
        (ifn l1
            (rplacd tail l2)
            (rplacd tail l1) )
        (cdr head) ) )

(de remove-duplicates (l)
    "Removes consecutive duplicates."
    (ifn l
        ()
        (ifn (cdr l)
            l
            (if (equal (car l) (cadr l))
                (remove-duplicates (cdr l))
                (cons (car l) (remove-duplicates (cdr l))) ) ) ) )

;;; Polymorphic functions

(describe = (x y)
    "Equality of values for number and strings. Same as eq for symbols and cons."
    "False when argument types are different." )

(de != (x y)
    "Same as (not (= x y))"
    (not (= x y)) )

(describe < (x y)
    "Less than predicate for numbers, strings and symbols." )

(describe > (x y)
    "Greater than predicate for numbers, strings and symbols." )

(de <= (x y)
    "Less or equal predicate for numbers, strings and symbols." 
    (if (> x y) () x) )

(de >= (x y)
    "Greater or equal  predicate for numbers, strings and symbols."
    (if (< x y) () x) )

; protect subr definitions
(if (eq (typefn '+) 'subr2) (synonym 'subr.+ '+))
(if (eq (typefn '-) 'subr2) (synonym 'subr.- '-))
(if (eq (typefn '*) 'subr2) (synonym 'subr.* '*))

(dmd + l
    "Adds or concats the arguments."
    (reduce-macro '+ 'subr.+ 0 l) )

;;; Numbers

(dmd - l
    "Substracts all arguments less first to first argument."
    (ifn l
        0
        (ifn (cdr l)
            (list 'subr.- 0 (car l))
            (list 'subr.- (car l) (optform '+ (cdr l))) ) ) )

(dmd * l
    "Multplies its arguments."
    (reduce-macro '* 'subr.* 1 l) )
    
(describe / (x y)
    "Divides x by y (integer division)." )

(describe % (x y)
    "Returns the remainder of x divided by y." )

(de power (x y)
    (if (= y 0)
        1
        (if (= y 1)
            x
            (let ((z (power x (/ y 2))))
                (if (= 0 (% y 2))
                    (* z z)
                    (* z z x) ) ) ) ) )
                    
(de 1+ (n)
    "Returns n + 1."
    (+ n 1) )
    
(de 1- (n)
    "Returns n - 1."
    (- n 1) )

(de min (x y)
    "Returns lowest value."
    (if (< x y) x y) )

(de max (x y)
    "Returns greatest value."
    (if (> x y) x y) )

(de abs (x)
    "Returns absolute value."
    (if (>= x 0) x (- x)) )

; Random numbers

(setq
    ; http://en.wikipedia.org/wiki/Linear_congruential_generator
    random-A 1664525
    random-C 1013904223
   ;random-M 4294967296 TODO
    random-M 1294967296
    random-X 0 )

(de random (n)
    "Returns a random integer less than n."
    (setq random-X (% (+ (* random-A random-X) random-C) random-M))
    (% random-X n) )

;;; Strings

(describe strlen (s)
    "Returns length of string s." )

(describe strnth (s i)
    "Returns 0-based nth character from string s." )
    
(describe strpos (s subs)
    "Returns 0-based position of substring subs in string s." 
    "Returns -1 if not found." )
    
(describe strsub (s i1 i2)
    "Extracts a substring from 0-based index i1 to i2 - 1."
    "i2 may be missing. In that case, the default value is the length of string s."
    "Indexes may be negative. In that case, they are counted from the end of the string." )
    
(describe symbol (x)
    "Returns the symbol which external representation is string x." )

(describe unique (x)
    "Returns a symbol which external representation is string x."
    "This symbol can not be read again." )

(describe number (x)
    "Returns the number which external representation is string x."
    "It is an error if x is not the external representation of a number." )

(describe string (x)
    "Returns the string representation of an atom x."
    "It is an error if x is not an atom." )

;;; Streams

(describe openi (filename)
    "Opens a file for input. Returns a numerical stream handle if ok or raises an error."
    "A stream is used for input with (input ...) function." )

(describe openo (filename)
    "Opens a file for output. Returns a numerical stream handle if ok or raises an error."
    "A stream is used for output with (output ...) function."    )

(describe close (stream-handle)
    "Closes a stream." )

(describe input (stream-handle)
    "Uses a stream for reading. Returns the current input stream if no argument." )

(describe output (stream-handle)
    "Uses a stream for printing. Returns the current output stream if no argument." )
    
(describe prompt (x)
    "Sets the string displayed when waiting for a keyboard input."
    "Retuns the current prompt when no argument." )

;;; Read

(describe readchar ()
    "Reads one character from current input stream." )
    
(describe peekchar ()
    "Accesses, and keeps available for reading, one character from current input stream." )
    
(describe readline ()    
    "Reads one text line from current input stream." )
    
(describe typech (char . type)
    "Returns a number coding the type of the character as used by the reader."
    "If type is present, it becomes the new type of character." )

(describe read ()
    "Reads one expression." )

(de readlines (filename)
    "Reads a text file into a list of strings."
    (let ((in (openi filename)) (head (cons ()())))
        (let ((tail head))
            (with ((input in))
                (tag eof
                    (while t
                        (setq tail (placdl tail (readline))) ) )
                (cdr head) ) ) ) )
                
(describe load (filename)
    "Reads ans evaluates all expressions in file." )
    
(dm autoload (filename . lsym)
    "(autoload filename sym1 ... symN)"
    (let ((loadform `(load ,filename)))
        (mapc (lambda (sym) (funcall 'dm sym 'x loadform `(kwote (apply ',sym x)))) lsym) ) )
        
; Macro character definition
 
(dmd dmc (x . y)
    "Defines a macro-character. Takes a one character string as first argument."
    "Example: (dmc |'| (list (quote quote) (read)))"
    (ifn (and (stringp x) (= (strlen x) 1))
        (exit toperror (print "Not a character in dmc")) )
    (list 'progn
        (list 'typech x macro-char)
        (mcons 'de (symbol x) () y) ) )
        
; Dispatch character
        
(dmc "#" 
    (let ((f (getprop 'sharp (readchar))))
        (ifn f
            ()
            (apply f ())) ) )
            
(dm defsharp (c . l) `(addprop 'sharp (lambda ,@l) ,c))

(defsharp "." () (eval (read)))
(defsharp "+" () (if  (eval (read)) (read) (read) ()))
(defsharp "-" () (ifn (eval (read)) (read) (read) ()))

(defsharp "|" ()
    (let ((inside-comment t))
        (while inside-comment
            (let ((c (readchar)))
                (if (eq c "|")
                    (setq inside-comment (neq (peekchar) "#")) ) ) ) )
    (readchar)
    (read) )
                
;;; Print

; see print.l

;;; Environment and system

(describe toplevel ()
    "Function called by the interpretation loop. May be redefined." )
    
(describe error (errorname func arg)
    "System error function. May be redefined." )
    
(describe end ()
    "Leaves interpreter and returns to system." )

(describe time ()
    "Returns system time in seconds." )

(dm timing (exp . n)
    "Returns the time in seconds to evaluate an expression."
    "If n present, repeats n times the evaluation."
    `(progn
        (repeat ,(if n (car n) 1)
            ,exp )
        (- (time) ,(time)) ) )
        
(describe cls ()
    "Erases console." )
    
(describe implementation ()
    "Returns implementation information as a list of 3 elements interpretes as:"
    "element1: implementation language: currently sapid or pascal"
    "element2: implementation of integers : currently int32 or bignum"
    "element3: recursion optimization: currently tail-rec-opt-none, tail-rec-opt-tail,  tail-rec-opt-mutual" )
    