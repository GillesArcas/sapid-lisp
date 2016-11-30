; sapid lisp
; sapid implementation of sapid evaluator
; gilles.arcas@gmail.com, https://github.com/GillesArcas/sapid-lisp
; MIT license

; some simplifications:
; - host read function is a builtin function of the meta interpretor
;   This has some consequences:
;   . oblist returns all symbols: host + meta (as a consequence of using host intern function)
;   . it is impossible to define new macro characters: the $fvalue cannot been seen by the host read
; - host print function is a builtin function of the meta interpretor

; Configuration

(mapc (lambda (x) (value x nil)) '(NoRecursionOptimization TailRecursionOptimization MutualRecursionOptimization))
(setq MutualRecursionOptimization t)
                                                              
; Symbol values, implementation using plist

(de $value (x . y)
    (if y
        (putprop x (car y) 'value) )
    (getprop x 'value) )

(de $boundp (x)
    (memq 'value (plist x)) )
    
(de $makunbound (x)
    (remprop x 'value) )
    
; Symbol values, implementation using host symbols

(de $value (x . y)
    (if y
        (value (symbol (+ "meta-" (string x))) (car y))
        (value (symbol (+ "meta-" (string x)))) ) )
        
(de $boundp (x)
    (boundp (symbol (+ "meta-" (string x)))) )
    
(de $makunbound (x)
    (makunbound (symbol (+ "meta-" (string x)))) )
    
; Plist    

(de $plist (x . y)
    (if y
        (putprop x (car y) 'plist) )
    (getprop x 'plist) )
    
; Builtin symbols

(de InitSymbols ()
    ; make all fvalue functions as self evaluating
    (mapc (lambda (x) (putprop x 'ssubr 'ftype)(putprop x () 'fval))
          '(fsubr ssubr subr0 subr1 subr2 subr01 subr12 nsubr lambda macro dmacro) )
          
    (putprop 'fsubr  'evalfsubr   'evalfunc)
    (putprop 'ssubr  'evalssubr   'evalfunc)
    (putprop 'subr0  'evalsubr0   'evalfunc)
    (putprop 'subr1  'evalsubr1   'evalfunc)
    (putprop 'subr2  'evalsubr2   'evalfunc)
    (putprop 'nsubr  'evalnsubr   'evalfunc)
    (putprop 'subr01 'evalsubr01  'evalfunc)
    (putprop 'subr12 'evalsubr12  'evalfunc)
    (putprop 'lambda 'evalexpr    'evalfunc)
    (putprop 'macro  'evalmacro   'evalfunc)
    (putprop 'dmacro 'evaldmacro  'evalfunc)
    
    (putprop 'fsubr  'evalfsubr   'applyfunc)
    (putprop 'ssubr  'evalssubr   'applyfunc)
    (putprop 'subr0  'evalsubr0   'applyfunc)
    (putprop 'subr1  'applysubr1  'applyfunc)
    (putprop 'subr2  'applysubr2  'applyfunc)
    (putprop 'subr01 'applysubr01 'applyfunc)
    (putprop 'subr12 'applysubr12 'applyfunc)
    (putprop 'lambda 'applyexpr   'applyfunc)
    (putprop 'macro  'evalmacro   'applyfunc)
    (putprop 'dmacro 'evalmacro   'applyfunc) ; same as macro, no form to rplac
    
    ; make constants
    ($value nil nil)
    ($value t t)
)

; Predicates
    
(de charp (x)
    (and (stringp x) (= (strlen x) 1)) )

; Evaluation stack

(setq Stack ())        

; Evaluation

(de $eval (x)
    (cond 
        ((symbolp x)
            (if ($boundp x)
                ($value x)
                ($error 'UndefSymError 'eval x) ) )
        ((numberp x) x) 
        ((stringp x) x)
        ((consp x) (evalform x (car x) (cdr x))) ) )
        
; Form evaluation

(de evalform (form func larg)
    (cond 
        ((symbolp func)
            (evalfn form func (getprop func 'ftype) (getprop func 'fval) larg) )
        ((consp func)
            (evalfn form func (car func) (cdr func) larg) )
        (t
            ($error 'UndefFuncError 'eval form) ) ) )
        
; Function evaluation        

(de evalfn (form func ftype fval larg)
    (if (getprop ftype 'evalfunc)
        (funcall (getprop ftype 'evalfunc) func fval larg form)
        ($error 'UndefFuncError 'eval form) ) )
        
; Evaluation of builtin functions
; The minimum number of arguments is tested, extra arguments are ignored.        

(de evalssubr (func fval larg form)
    form )

(de evalfsubr (func fval larg form)
    (funcall fval larg) )

(de evalsubr0 (func fval larg form)
    (funcall fval) )

(de evalsubr1 (func fval larg form)
    (assert_condition (consp larg) 'ArgNumberError func 0)
    (funcall fval (evalprotect (car larg))) )

(de evalsubr2 (func fval larg form)
    (assert_condition (consp larg) 'ArgNumberError func 0)
    (assert_condition (consp (cdr larg)) 'ArgNumberError func 1)
    (let ((x (evalprotect (car larg))))
        (funcall fval x (evalprotect (cadr larg))) ) )
        
(de evalnsubr (func fval larg form)
    (apply fval (mapcar 'evalprotect larg)) )

(de evalsubr01 (func fval larg form)
    (if (consp larg) 
        (funcall fval (evalprotect (car larg)))
        (funcall fval) ) )

(de evalsubr12 (func fval larg form)
    (assert_condition (consp larg) 'ArgNumberError func 0)
    (let ((x (evalprotect (car larg))))
        (if (consp (cdr larg))
            (funcall fval x (evalprotect (cadr larg)))
            (funcall fval x) ) ) )

; Evaluation of expr function calls without recursion optimization

#+NoRecursionOptimization
(de evalexpr (func fval larg form . evalargs)
    (bind func fval (car fval) larg (not evalargs))
    (protect
        ($eprogn (cdr fval))
        (unbind) ) )

#+NoRecursionOptimization
(de evalprotect (x)
    ($eval x) )

; Evaluation of expr function calls with tail recursion optimization

#+TailRecursionOptimization
(de evalexpr (func fval larg form . evalargs)
    (bind func fval (car fval) larg (not evalargs))
    (when (istailrec fval)
        (nextl Stack)
        (raise 'TailRecException fval) )
    
    (let ((more-while t) (result ()))
        (try
            (while more-while
                (try
                    (progn
                        (setq result ($eprogn (cdr fval)))
                        (setq more-while ()) )
                    (except TailRecException value
                            () ) ) )          ; tail recursion
        (finally
            (unbind) ) )
            
        result ) )

#+TailRecursionOptimization
(de istailrec (fv)
    ; the binding record of the call to test is already pushed
    ; tests previous one
    (slet ((stackrec (nth 1 Stack)) (assoc (assoc 'lambda stackrec)))
        (and assoc (eq (cadr assoc) fv)) ) )

#-NoRecursionOptimization
(de evalprotect (x)
    (newl Stack '(eval))
    (protect
        ($eval x)
        (nextl Stack) ) )

; Evaluation of expr function calls with tail and mutual recursion optimization

#+MutualRecursionOptimization
(de evalexpr (func fval larg form . evalargs)
    (bind func fval (car fval) larg (not evalargs))
    (when (istailrec fval)
        (nextl Stack)
        (raise 'TailRecException fval) )
    
    (let ((more-while t) (result ()))
        (try
            (while more-while
                (try
                    (progn
                        (setq result ($eprogn (cdr fval)))
                        (setq more-while ()) )
                    (except TailRecException value
                        (if (eq value fval)
                            ()                ; tail recursion
                            (bindmerge)       ; mutual recursion
                            (nextl Stack)
                            (raise 'TailRecException value) ) ) ) ) 
        (except TailRecException value
            (raise 'TailRecException value) )
        (except t (exception value)
            (unbind)
            (raise exception value) )
        (else
            (unbind) ) )
            
        result ) )

#+MutualRecursionOptimization
(de istailrec (fv)
    (tag result
        (let ((i 1))
            (while t
                ; no need to test end of stack
                (slet ((stackrec (nth i Stack)) (assoc (assoc 'lambda stackrec)))
                    (ifn assoc
                        (exit result nil)
                        (if (eq (cadr assoc) fv)
                            (exit result t) ) ) )
                (incr i) )
            (exit result nil) ) ) )

; Binding
        
(de bind (func fval lpar larg evalargs)
    (let ((stackrec ()))
        (newal stackrec 'lambda fval)

        ; store argument values in stack record
        (while (consp lpar)
            (cond
                ((atom larg) 
                    ($error 'BindingError func larg))
                ((not (variablep (car lpar))) 
                    ($error 'NotVarError 'eval (car lpar)))
                (evalargs 
                    (newal stackrec (car lpar) (evalprotect (car larg))) )
                (t 
                    (newal stackrec (car lpar) (car larg))) )
            (nextl lpar)
            (nextl larg) )

        ; store values of possible binding between symbol and list of values
        (if (and (variablep lpar)(listp larg))
            (if evalargs
                (newal stackrec lpar ($evlis larg))
                (newal stackrec lpar larg) ) )

        ; swap cell values and values in stack record
        (let ((rec stackrec))
            (while rec
                (ifn (eq (caar rec) 'lambda)
                    (swap-value (car rec)) )
                (nextl rec) ) )
                
        ; push stack record
        (newl Stack stackrec)
) )            
        
(de unbind ()
    ; pop record
    (let ((stackrec (nextl Stack)))
      
        ; restore environment
        (let ((rec stackrec))
            (while rec
                (ifn (eq (caar rec) 'lambda)
                    (restore-value (car rec)) )
                (nextl rec) ) ) ) )

(de bindmerge ()
    ; merge bindings from top record with previous one
    (let ((stackrec1 (car Stack))
          (stackrec2 (cadr Stack)) )
        (while stackrec1
            (let ((asso (car stackrec1)))
                (if (and (neq (car asso) 'lambda) (null (assoc (car asso) stackrec2)))
                    (rplacd (last stackrec2) (list asso)) )
            (nextl stackrec1) ) ) ) )
        
; Binding helpers    
    
(dmd newal (sym key val)
    ; the value of sym is a alist
    `(setq ,sym (cons (list ,key ,val) ,sym)) )
    
(de swap-value (arec)
    ; called when binding, arec is a pair (symbol value). 
    ; Swap symbol value with value in arec.
    (let ((sym (car arec)) (val (cadr arec)))
        (if ($boundp sym)
            (let ((x ($value sym)))
                ($value sym val)
                (rplaca (cdr arec) x) )
            ($value sym val)
            (rplacd arec ()) ) ) )
            
(de restore-value (arec)
    ; called when unbinding 
    ; arec is a pair (symbol value) or (symbol) if symbol was unbind 
    ; restore symbol value with value in arec or make unbound
    (let ((sym (car arec)))
        (if (cdr arec)
            ($value sym (cadr arec))
            ($makunbound sym) ) ) )
                                   
; Evaluation of macros    

(de evalmacro (func fval larg form)
    (let ((x (applyexpr func fval larg form)))
        ($eval x) ) )

(de evaldmacro (func fval larg form)
    (let ((x (applyexpr func fval larg form)))
        (if (atom x)
            ($eval x)
            ; displaces calling form with expansion
            (displace form x)
            ($eval form) ) ) )

; Apply

(de applyform (func larg)
    (cond 
        ((symbolp func)
            (applyfn func (getprop func 'ftype) (getprop func 'fval) larg) )
        ((consp func)
            (applyfn func (car func) (cdr func) larg) )
        (t
            ($error 'UndefFuncError 'apply func) ) ) )

(de applyfn (func ftype fval larg)
    (if (getprop ftype 'applyfunc)
        (funcall (getprop ftype 'applyfunc) func fval larg nil)
        ($error 'UndefFuncError 'apply func) ) )

(de applysubr1 (func fval larg form)
    (assert_condition (consp larg) 'ArgNumberError func 0)
    (funcall fval (car larg)) )

(de applysubr2 (func fval larg form)
    (assert_condition (consp larg) 'ArgNumberError func 0)
    (assert_condition (consp (cdr larg)) 'ArgNumberError func 1)
    (funcall fval (car larg) (cadr larg)) )
        
(de applynsubr (func fval larg form)
    (apply fval larg) )

(de applysubr01 (func fval larg form)
    (if (consp larg)
        (funcall fval (car larg))
        (funcall fval) ) )

(de applysubr12 (func fval larg form)
    (assert_condition (consp larg) 'ArgNumberError func 0)
    (if (consp (cdr larg))
        (funcall fval (car larg) (cadr larg))
        (funcall fval (car larg)) ) )

(de applyexpr (func fval larg form)
    (evalexpr func fval larg form nil) )
    
; Evaluation of lists

(de $eprogn (x)
    (if (atom x)
        (if (null x)
            ()
            ($error 'NotListArgError "eprogn" x) )
        (while (consp (cdr x))
            (evalprotect (car x))
            (nextl x) )
        (if (null (cdr x))
            ($eval (car x))
            ($error 'NotListArgError "eprogn" (cdr x)) ) ) )

(de $evlis (x)
    (if (atom x)
        (if (null x)
            ()
            ($error 'NotListArgError "evlis" x) )
        (slet ((head (cons ()()))(tail head))
            (while (consp x)
                (setq tail (placdl tail (evalprotect (car x))))
                (nextl x) )
            (if (null x)
                (cdr head)
                ($error 'NotListArgError "evlis" x) ) ) ) )

; Exceptions

(de subr_tag (larg)
    (let ((sym (car larg)) (body (cdr larg)))
        (assert_symbolp sym "tag")
        (newl Stack (list 'tag sym))
        (try
            ($eprogn body) 
        (except t (exception result)
            (if (eq exception sym)
                result
                (raise exception result) ) )
        (finally
            (nextl Stack) ) ) ) )

(de subr_exit (larg)
    (let ((sym (car larg)) (body (cdr larg)))
        (assert_symbolp sym "exit")
        (throw sym ($eprogn body)) ) )

(de subr_lock (larg)
    (let ((func (car larg)) (seq (cdr larg)))
        (newl Stack '(lock))
        (let ((r ()))
            (try
                (setq r ($eprogn seq))
            (except t (exception result)
                ; constructs (exception result) as list of arguments for the lock function
                (applyfn func (car func) (cdr func) (list exception result)) )
            (else
                ; constructs (nil r) as list of arguments for the lock function
                (applyfn func (car func) (cdr func) (list nil r)) )
            (finally
                (nextl Stack) )
            )
        )
    )
)    

(de subr_throw (largs)
    (let ((tag (evalprotect (car largs))) (result ()))
        (newl Stack '(eval))
        (protect
            (setq result ($eprogn (cdr largs)))
            (nextl Stack) )
        (throw tag result) ) )

; Reading
 
(de $load (name) 
    (let ((inp (openi name)))
        (with ((input inp))
            (tag eof
                (while t
                    ;(print ($eval (read))) ) ) )
                    ($eval (read)) (prin ".") ) ) )
        (close inp) ) )
        
; Builtin functions

(de subr_quote (larg) (car larg))

(de subr_if (larg)
    (if (evalprotect (car larg))
        ($eval (cadr larg))
        ($eprogn (cddr larg)) ) )
        
(de subr_while (larg)
    (newl Stack '(eval))
    (protect 
        (while (evalprotect (car larg))
            ($eprogn (cdr larg)) )
        (nextl Stack) ) )

; Symbols

(de subr_value x
    (let ((sym (car x)) (larg (cdr x)))
        (if larg
            (assert_variablep sym "value")
            (assert_symbolp sym "value")
            (assert_boundp sym "value") ) )
    (apply '$value x) )

(de subr_fvalue (sym . val)
    (assert_symbolp sym "fvalue")
    (ifn val
        (getfvalue sym)
        (setfvalue sym (car val)) ) )

(de getfvalue (sym)  
    (let ((ftype (getprop sym 'ftype))(fval (getprop sym 'fval)))
        (ifn ftype 
            ()
            (if (memq ftype '(subr0 subr1 subr2 nsubr fsubr ssubr subr01 subr12 lambda macro dmacro)) 
                (cons ftype fval)
                (error 'ArgError "fvalue" sym)) ) )  )

(de setfvalue (sym val)
    (assert_listp val "fvalue")
    (ifn val
        (remprop sym 'ftype)
        (assert_symbolp (car val) "fvalue")
        (putprop sym (car val) 'ftype)
        (putprop sym (cdr val) 'fval) )
    val )

(de subr_boundp (sym)
    (assert_symbolp sym "boundp")
    (if ($boundp sym) t) )
    
(de subr_makunbound (sym)
    (assert_variablep sym  "makunbound")
    ($makunbound sym)
    sym )

(de $de (x)
    (defun x 'lambda) )
 
(de $dm (x)
    (defun x 'macro) )
 
(de $dmd (x)
    (defun x 'dmacro) )
 
(de defun (x type)
    (putprop (car x) type 'ftype)
    (putprop (car x) (cdr x)  'fval)
    (car x) )

(de subr_plist x
    (let ((sym (car x)))
        (assert_symbolp sym "plist") )
    (apply '$plist x) )

(de subr_memprop (sym ind)
    (let ((list ($plist sym)))
        (while (and (consp list) (neq (car list) ind))
            (setq list (cddr list)) )
        list ) )
    
; Characters

(de subr_typech (char . type)     ; Subr12
    ; ignore type given by sapid lisp implementation
    ; lisp sapid lisp is unable to define new macro characters as it uses host read
    (assert_charp char "typech")
    (typech char) )

; System

(de subr_toplevel ()
    (print "subr_toplevel")
    (let ((x ($eval (read))))
        (print "$= " x) ) )

(de subr_end ()
    (exit exit-sapid "$bye!") )
    
(de subr_stack ()
    Stack )
    
; Load subr definitions   

(de InitSubrs ()    
    (def-subr eval      subr1   $eval)
    (def-subr evlis     subr1   $evlis)
    (def-subr eprogn    subr1   $eprogn)
    (def-subr progn     fsubr   $eprogn)
    (def-subr quote     fsubr   subr_quote)
    (def-subr apply     subr2   applyform)
    (def-subr if        fsubr   subr_if)
    (def-subr while     fsubr   subr_while)
    (def-subr tag       fsubr   subr_tag)
    (def-subr exit      fsubr   subr_exit)
    (def-subr lock      fsubr   subr_lock)
    (def-subr throw     fsubr   subr_throw)
    (def-subr symbolp   subr1   symbolp)
    (def-subr numberp   subr1   numberp)
    (def-subr stringp   subr1   stringp)
    (def-subr consp     subr1   consp)
    (def-subr eq        subr2   eq)
    (def-subr oblist    subr0   oblist)
    (def-subr value     subr12  subr_value)
    (def-subr boundp    subr1   subr_boundp)
    (def-subr makunbound subr1  subr_makunbound)
    (def-subr fvalue    subr12  subr_fvalue)
    (def-subr de        fsubr   $de)
    (def-subr dm        fsubr   $dm)
    (def-subr dmd       fsubr   $dmd)
    (def-subr plist     subr12  subr_plist)
    (def-subr memprop   subr2   subr_memprop)
    (def-subr car       subr1   car)
    (def-subr cdr       subr1   cdr)
    (def-subr rplaca    subr2   rplaca)
    (def-subr rplacd    subr2   rplacd)
    (def-subr cons      subr2   cons)
    (def-subr nthcdr    subr2   nthcdr)
    (def-subr =         subr2   =)
    (def-subr <         subr2   <)
    (def-subr >         subr2   >)
    (def-subr +         subr2   +) ; todo : nsubr
    (def-subr -         subr2   -)
    (def-subr *         subr2   *)
    (def-subr /         subr2   /)
    (def-subr %         subr2   %)
    (def-subr strlen    subr1   strlen)
    (def-subr strnth    subr2   strnth)
    (def-subr strpos    subr2   strpos)
    (def-subr strsub    nsubr   strsub)
    (def-subr symbol    subr1   symbol)
    (def-subr unique    subr1   unique)
    (def-subr number    subr1   number)
    (def-subr string    subr1   string)
    (def-subr openi     subr1   openi)
    (def-subr openo     subr1   openo)
    (def-subr close     subr1   close)
    ;intern('input'   , Subr01, subr_input)
    ;intern('output'  , Subr01, subr_output)
    ;intern('readline', Subr0 , subr_readline)
    (def-subr typech    subr12  subr_typech)
    ;intern('readchar', Subr0 , readchar)
    ;intern('peekchar', Subr0 , peekchar)
    (def-subr read      subr0   read)
    (def-subr load      subr1   $load)
    (def-subr print     nsubr   print) ; nsubr
    (def-subr prin      nsubr   prin)
    (def-subr terpri    subr0   terpri)
    (def-subr toplevel  subr0   subr_toplevel)
    (def-subr time      subr0   time)
    (def-subr end       subr0   subr_end)
    (def-subr cls       subr0   cls)
    (def-subr stack     subr0   subr_stack)
)    
   
(dm def-subr (name ftype fval)
    `(progn
        (putprop ',name ',ftype 'ftype)
        (putprop ',name ',fval  'fval) ) )
   
; Assertions
   
(de assert_condition (condition error_symbol func arg)
    (unless condition
        ($error error_symbol func arg) ) )

(de assert_symbolp (arg func)
    (assert_condition (symbolp arg) 'NotSymbolArgError func arg) )

(de assert_listp (arg func)
    (assert_condition (listp arg) 'NotListArgError func arg) )

(de assert_variablep (arg func)
    (assert_condition (variablep arg) 'NotVarError func arg) )

(de assert_boundp (arg func)
    (assert_condition ($boundp arg) 'UndefSymError func arg) )

(de assert_charp (arg func)
    (assert_condition (charp arg) 'NotCharArgError func arg) )
    
; Error handling                        
                    
(de $error (errorname func val)
    (terpri)
    (print "$* " errorname " : " func " : " val)
    (terpri)
    (exit toperror errorname) )
           
; Main

(de sapid ()
    (InitSymbols)
    (InitSubrs)
    ($load "sapid.ini")
    (print "$loaded....")
    (with ((prompt "$? ")
           (fvalue 'error (lambda (errorname func val) ($error errorname func val)))
           ; has to define toplevel again after redefinition in sapid.ini
           (fvalue 'toplevel (lambda () (subr_toplevel))) )
        (print (prompt))
        (print (fvalue 'error))
        (print (fvalue 'toplevel))
        (tag exit-sapid
            (while t
                (tag toperror
                    (applyform 'toplevel ()) ) ) ) ) )
                        
; Launch

(sapid)   
