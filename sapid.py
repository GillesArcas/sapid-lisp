# sapid lisp
# python implementation
# gilles.arcas@gmail.com, https://github.com/GillesArcas/sapid-lisp
# MIT license

from __future__ import print_function

import sys
import os
import time

# Configuration

TailRecursionOptimization = 'MutualRecursion' # None | 'TailRecursion' | 'MutualRecursion'

# 2/3 compatibility

if sys.version_info < (3,):
    integer_types = (int, long,)
else:
    integer_types = (int,)

if sys.version_info < (3,):
    func_name_attribute = 'func_name'
else:
    func_name_attribute = '__name__'

if sys.version_info < (3,):
    input_func = raw_input
else:
    input_func = input

# Items

# sapid provides 4 types of items: symbol, cons, int and str.
# int (including long) and str are native.

class symbol:
    def __init__(self, pname, ftype=None, fval=None):
        self.pname = pname
        self.cval  = None
        self.ftype = ftype
        self.fval  = fval
        self.plist = Nil
        self.isvar = True
    def __lt__(self, x):
        return self.pname < x.pname
    def __gt__(self, x):
        return self.pname > x.pname
    def __str__(self):
        return self.pname

class cons:
    def __init__(self, car, cdr):
        self.car = car
        self.cdr = cdr
    def __str__(self):
        return '(' + str(self.car) + ' . ' + str(self.cdr) + ')'

# Symbols

Oblist = {}

def intern(x, ftype=None, fval=None):
    # case sensitive

    if x in Oblist:
        y = Oblist[x]
        if ftype != None: y.ftype = ftype
        if fval  != None: y.fval  = fval
        return y
    else:
        Oblist[x] = symbol(x, ftype, fval)
        return Oblist[x]

# Builtin symbols

def InitSymbols():
    global Nil, T, FSubr, SSubr, Subr0, Sub1, Subr2, Subr12, Lambda, Macro, DMacro

    FunctionTypeSymbols = [
        'Subr0', 'Subr1', 'Subr2', 'Subr01', 'Subr12', 'NSubr', 'SSubr',
        'FSubr', 'Lambda', 'Macro', 'DMacro']

    ErrorSymbols = [
        'UndefSymError', 'UndefFuncError', 'UndefTagError', 'NotSymbolArgError',
        'NotNumberArgError', 'NotStringArgError', 'NotConsArgError', 'NotListArgError',
        'NotCharArgError', 'NotVarError', 'ArgNumberError', 'ArgError',
        'BindingError', 'SyntaxError', 'IoError', 'IndexError']

    # Dummy definition for Nil required to intern Nil and give value to its plist.
    # Nil plist is updated latter. Other symbols get the correct plist value.
    Nil = None

    # Intern standard symbols in lower case
    for sym in ['Nil', 'T', 'TopError', 'Eof']:
        globals()[sym] = intern(sym.lower())

    # Intern error symbols in camel case
    for sym in ErrorSymbols:
        globals()[sym] = intern(sym)

    # Make Nil and T constant, complete Nil plist, and make Nil a list.
    Nil.cval  = Nil
    Nil.isvar = False
    T.cval    = T
    T.isvar   = False
    Nil.plist = Nil
    Nil.car   = Nil
    Nil.cdr   = Nil

    # Make function definition form return their own value
    SSubr = intern('ssubr')
    for sym in FunctionTypeSymbols:
        globals()[sym] = intern(sym.lower(), SSubr, subr_selfvalue)

    # Add eval function to each ftype symbol
    FSubr.evalfunc   = evalfsubr
    SSubr.evalfunc   = evalssubr
    Subr0.evalfunc   = evalsubr0
    Subr1.evalfunc   = evalsubr1
    Subr2.evalfunc   = evalsubr2
    Subr01.evalfunc  = evalsubr01
    Subr12.evalfunc  = evalsubr12
    NSubr.evalfunc   = evalnsubr
    Lambda.evalfunc  = evalexpr
    Macro.evalfunc   = evalmacro
    DMacro.evalfunc  = evaldmacro

    # Add apply function to each ftype symbol
    FSubr.applyfunc  = evalfsubr
    SSubr.applyfunc  = evalssubr
    Subr0.applyfunc  = evalsubr0
    Subr1.applyfunc  = applysubr1
    Subr2.applyfunc  = applysubr2
    Subr01.applyfunc = applysubr01
    Subr12.applyfunc = applysubr12
    NSubr.applyfunc  = applynsubr
    Lambda.applyfunc = applyexpr
    Macro.applyfunc  = evalmacro
    DMacro.applyfunc = evalmacro # same as macro, no form to rplac

# Predicates

def symbolp(x):
    return isinstance(x, symbol)

def numberp(x):
    return isinstance(x, integer_types)

def stringp(x):
    return isinstance(x, str)

def consp(x):
    return isinstance(x, cons)

def atom(x):
    return not consp(x)

def listp(x):
    return x == Nil or consp(x)

def null(x):
    return x == Nil

def variablep(x):
    return symbolp(x) and x.isvar

def unboundp(x):
    return x.cval == None

def charp(x):
    return stringp(x) and len(x) == 1

# Evaluation stack

Stack = []

# Evaluation

def eval(x):
    if symbolp(x):
        if unboundp(x):
            error(UndefSymError, 'eval', x)
        else:
            return x.cval

    if numberp(x) or stringp(x):
        return x

    if consp(x):
        return evalform(x, x.car, x.cdr)

# Form evaluation

def evalform(form, func, larg):
    if symbolp(func):
        return evalfn(form, func, func.ftype, func.fval, larg)
    elif consp(func):
        if stringp(func.cdr):
            return evalfn(form, func, func.car, globals()[func.cdr], larg)
        else:
            return evalfn(form, func, func.car, func.cdr, larg)
    else:
        error(UndefFuncError, 'eval', func)

# Function evaluation

def evalfn(form, func, ftype, fval, larg):

    if hasattr(ftype, 'evalfunc'):
        return ftype.evalfunc(func, fval, larg, form)
    else:
        error(UndefFuncError, 'eval', func)

# Evaluation of builtin functions
# The minimum number of arguments is tested, extra arguments are ignored.

def evalssubr(func, fval, larg, form):
    return form

def evalfsubr(func, fval, larg, form):
    return fval(larg)

def evalsubr0(func, fval, larg, form):
    return fval()

def evalsubr1(func, fval, larg, form):
    assert_condition(consp(larg), ArgNumberError, func, 0)
    x = evalprotect(larg.car)
    return fval(x)

def evalsubr2(func, fval, larg, form):
    assert_condition(consp(larg), ArgNumberError, func, 0)
    assert_condition(consp(larg.cdr), ArgNumberError, func, 1)
    x = evalprotect(larg.car)
    y = evalprotect(larg.cdr.car)
    return fval(x, y)

def evalnsubr(func, fval, larg, form):
    evargs = []
    while consp(larg):
        evargs.append(evalprotect(larg.car))
        larg = larg.cdr
    return fval(evargs)

def evalsubr01(func, fval, larg, form):
    x = evalprotect(larg.car) if consp(larg) else None
    return fval(x)

def evalsubr12(func, fval, larg, form):
    assert_condition(consp(larg), ArgNumberError, func, 0)
    x = evalprotect(larg.car)
    y = evalprotect(larg.cdr.car) if consp(larg.cdr) else None
    return fval(x, y)

# Evaluation of expr function calls without recursion optimization

if TailRecursionOptimization == None:
  def evalexpr(func, fval, larg, form, evalargs=True):
      bind(func, fval, fval.car, larg, evalargs)
      try:
          x = eprogn(fval.cdr)
      finally:
          unbind()
      return x

if TailRecursionOptimization == None:
  def evalprotect(expr):
      return eval(expr)

# Evaluation of expr function calls with tail recursion optimization

class TailRecException(Exception):
    def __init__(self, fval):
        self.fval = fval

if TailRecursionOptimization == 'TailRecursion':
  def evalexpr(func, fval, larg, form, evalargs=True):

      bind(func, fval, fval.car, larg, evalargs)
      if istailrec(fval):
          Stack.pop()
          raise TailRecException(fval)

      try:
          while True:
              try:
                  x = eprogn(fval.cdr)
                  break
              except TailRecException:
                  pass
      finally:
          unbind()

      return x

if TailRecursionOptimization == 'TailRecursion':
  def istailrec(fv):
      # the binding record of the call to test is already pushed
      # tests previous one
      i = len(Stack) - 2
      stackrec = Stack[i]
      if 'lambda' not in stackrec:
          return False
      if stackrec['lambda'] == fv:
          return True
      else:
          return False

if TailRecursionOptimization != None:
  def evalprotect(expr):
      # adds something in the stack to avoid tail recursion detection
      try:
          Stack.append({'eval': expr})
          return eval(expr)
      finally:
          Stack.pop()

# Evaluation of expr function calls with tail and mutual recursion optimization

if TailRecursionOptimization == 'MutualRecursion':
  def evalexpr(func, fval, larg, form, evalargs=True):

      bind(func, fval, fval.car, larg, evalargs)
      if istailrec(fval):
          Stack.pop()
          raise TailRecException(fval)

      try:
          while True:
              try:
                  x = eprogn(fval.cdr)
                  break
              except TailRecException as e:
                  if e.fval == fval:
                      pass              # tail recursion
                  else:
                      bindmerge()       # mutual recursion
                      Stack.pop()
                      raise
      except TailRecException:
          raise
      except:
          unbind()
          raise
      else:
          unbind()

      return x

if TailRecursionOptimization == 'MutualRecursion':
  def istailrec(fv):
      # the binding record of the call to test is already pushed
      # compares with previous ones
      i = len(Stack) - 2
      while i >= 0:
          stackrec = Stack[i]
          if 'lambda' not in stackrec:
              return False
          if stackrec['lambda'] == fv:
              return True
          i -= 1
      else:
          return False

# Binding

def bind(func, fval, lpar, larg, evalargs=True):
    # evaluates and saves arguments in stack record

    stackrec = {}
    stackrec['lambda'] = fval

    # store argument values in stack record
    while consp(lpar):
        if atom(larg):
            error(BindingError, func, larg)
        elif not variablep(lpar.car):
            error(NotVarError, func, lpar.car)
        elif evalargs:
            stackrec[lpar.car] = evalprotect(larg.car)
        else:
            stackrec[lpar.car] = larg.car
        lpar = lpar.cdr
        larg = larg.cdr

    # store values of possible binding between symbol and list of values
    if variablep(lpar) and listp(larg):
        if evalargs:
            stackrec[lpar] = evlis(larg)
        else:
            stackrec[lpar] = larg

    # swap cell values and values in stack record
    for key in stackrec.keys():
        if symbolp(key):
            key.cval, stackrec[key] = stackrec[key], key.cval

    # push stack record
    Stack.append(stackrec)

def unbind():
    # pop record
    stackrec = Stack.pop()

    # restore environment
    for key in stackrec.keys():
        if symbolp(key):
            key.cval = stackrec[key]

def bindmerge():
    # merge bindings from top record with previous one
    stackrec1 = Stack[len(Stack) - 1]
    stackrec2 = Stack[len(Stack) - 2]
    for x in stackrec1:
        if x != 'lambda' and x not in stackrec2:
            stackrec2[x] = stackrec1[x]

# Evaluation of macros

def evalmacro(func, fval, larg, form):
    x = applyexpr(func, fval, larg, form)
    return eval(x)

def evaldmacro(func, fval, larg, form):
    x = applyexpr(func, fval, larg, form)
    if atom(x):
        return eval(x)
    else:
        # displaces calling form with expansion
        form.car = x.car
        form.cdr = x.cdr
        return eval(form)

# Apply

def applyform(func, larg):
    if symbolp(func):
        return applyfn(func, func.ftype, func.fval, larg)
    elif consp(func):
        if stringp(func.cdr):
            return applyfn(func, func.car, globals()[func.cdr], larg)
        else:
            return applyfn(func, func.car, func.cdr, larg)
    else:
        error(UndefFuncError, 'apply', func)

def applyfn(func, ftype, fval, larg):
    if hasattr(ftype, 'applyfunc'):
        return ftype.applyfunc(func, fval, larg, None)
    else:
        error(UndefFuncError, 'apply', func)

def applysubr1(func, fval, larg, form):
    assert_condition(consp(larg), ArgNumberError, func, 0)
    return fval(larg.car)

def applysubr2(func, fval, larg, form):
    assert_condition(consp(larg), ArgNumberError, func, 0)
    assert_condition(consp(larg.cdr), ArgNumberError, func, 1)
    return fval(larg.car, larg.cdr.car)

def applynsubr(func, fval, larg, form):
    return fval(hostlist(larg))

def applysubr01(func, fval, larg, form):
    return fval(larg.car if consp(larg) else None)

def applysubr12(func, fval, larg, form):
    assert_condition(consp(larg), ArgNumberError, func, 0)
    return fval(larg.car, larg.cdr.car if consp(larg.cdr) else None)

def applyexpr(func, fval, larg, form):
    return evalexpr(func, fval, larg, form, evalargs=False)

# Evaluation of lists

def eprogn(x):
    if atom(x):
        if x == Nil:
            return Nil
        else:
            error(NotListArgError, 'eprogn', x)
    else:
        while consp(x.cdr):
            evalprotect(x.car)
            x = x.cdr
        if x.cdr == Nil:
            return eval(x.car)
        else:
            error(NotListArgError, 'eprogn', x.cdr)

def evlis(x):
    if atom(x):
        if x == Nil:
            return Nil
        else:
            error(NotListArgError, 'evlis', x)
    else:
        head = cons(Nil, Nil)
        tail = head
        while consp(x):
            tail.cdr = cons(evalprotect(x.car), Nil)
            tail = tail.cdr
            x = x.cdr
        if x == Nil:
            return head.cdr
        else:
            error(NotListArgError, 'evlis', x)

# Exceptions

class EvalException(Exception):
    def __init__(self, tag, result):
        self.tag = tag
        self.result = result

def itag(sym, x):
    Stack.append({'tag':sym})

    try:
        if consp(x):
            r = eprogn(x)
        else:
            r = x()
    except EvalException as e:
        if e.tag == sym:
            return e.result
        else:
            raise
    finally:
        Stack.pop()

    return r

def iexit(sym, seq):
    raise EvalException(sym, eprogn(seq))

def lock(func, seq):
    Stack.append({'lock':None})

    try:
        r = eprogn(seq)
    except EvalException as e:
        # uses (e.tag e.result) as list of arguments for the lock function
        r = applyfn(func, func.car, func.cdr, cons(e.tag, cons(e.result, Nil)))
    else:
        # uses (nil r) as list of arguments for the lock function
        r = applyfn(func, func.car, func.cdr, cons(Nil, cons(r, Nil)))
    finally:
        Stack.pop()

    return r

# Exception subroutines

def subr_tag(larg):                   # FSubr
    assert_symbolp(larg.car, 'tag')
    return itag(larg.car, larg.cdr)

def subr_throw(larg):                 # FSubr
    assert_listp(larg, 'throw')
    tag = evalprotect(larg.car)
    try:
        Stack.append({'eval':None})
        result = eprogn(larg.cdr)
    finally:
        Stack.pop()
    raise EvalException(tag, result)

def subr_exit(larg):                  # FSubr
    assert_symbolp(larg.car, 'exit')
    return iexit(larg.car, larg.cdr)

def subr_lock(larg):                  # FSubr
    assert_listp(larg, 'lock')
    return lock(evalprotect(larg.car), larg.cdr)

# Streams

class TInputStream:
    def __init__(self):
        self.mode = 'r'
        self.inputbuffer = ''
        self.current = 1
        self.last = 0
        self.readinglist = 0

    def readline(self):
        self.inputbuffer += '\n'
        self.current = 0
        self.last = len(self.inputbuffer) - 1

class TInputStreamKeyboard(TInputStream):
    def __init__(self):
        TInputStream.__init__(self)

    def readline(self):
        sys.stdout.write(Prompt)
        self.inputbuffer = input_func()
        TInputStream.readline(self)

class TInputStreamFile(TInputStream):
    def __init__(self, x):
        try:
            self.inputfile = open(findfile(x))
        except:
            error(IoError, 'openi', x)
        TInputStream.__init__(self)

    def close(self):
        self.inputfile.close()

    def readline(self):
        try:
            self.inputbuffer = self.inputfile.readline()
            if self.inputbuffer == '':
                raise StopIteration
            else:
                TInputStream.readline(self)
        except StopIteration:
            if self.readinglist:
                readerror(1)
            else:
                iexit(Eof, Nil)
        except Exception as e:
            error(IoError, 'read', e.args[0])

def findfile(filename):
    if os.path.exists(filename):
        return filename
    else:
        pathname = os.path.join(os.path.dirname(__file__), filename)
        if os.path.exists(pathname):
            return pathname
        else:
            return filename

class TOutputStream:
    def __init__(self):
        self.mode = 'w'

    def flush(self):
        pass

class TOutputStreamConsole(TOutputStream):
    def prinstring(self, x):
        sys.stdout.write(x)

class TOutputStreamFile(TOutputStream):
    def __init__(self, x):
        try:
            self.outputfile = open(x, 'w')
        except:
            error(IoError, 'openo', x)
        TOutputStream.__init__(self)

    def flush(self):
        self.outputfile.flush()

    def close(self):
        self.outputfile.close()

    def prinstring(self, x):
        try:
            self.outputfile.write(x)
        except Exception as e:
            error(IoError, 'print', e.args[0])

def InitStreams():
    global Streams, inputhandle, inputstream, outputhandle, outputstream, Prompt
    Streams = {}
    Prompt = '? '
    # create and set default streams
    Streams[0]   = TInputStreamKeyboard()
    Streams[1]   = TOutputStreamConsole()
    inputhandle  = 0
    outputhandle = 1
    inputstream  = Streams[0]
    outputstream = Streams[1]

def internstream(x):
    global Streams
    handle = max(Streams.keys()) + 1
    Streams[handle] = x
    return handle

def subr_openi(filename):             # Subr1
    return internstream(TInputStreamFile(filename))

def subr_openo(filename):             # Subr1
    return internstream(TOutputStreamFile(filename))

def subr_close(handle):               # Subr1
    try:
        Streams[handle].close()
        Streams[handle] = None
        return T
    except:
        error(IoError, 'close', handle)

def subr_input(handle):               # Subr01
    global inputhandle, inputstream

    if handle != None:
        assert_numberp(handle, 'input')
        assert_condition(is_handle_valid(handle, 'r'), ArgError, 'input', handle)
        inputhandle = handle
        inputstream = Streams[handle]

    return inputhandle

def subr_output(handle):              # Subr01
    global outputhandle, outputstream

    if handle != None:
        assert_numberp(handle, 'output')
        assert_condition(is_handle_valid(handle, 'w'), ArgError, 'output', handle)
        outputhandle = handle
        outputstream = Streams[handle]

    return outputhandle

def is_handle_valid(handle, mode):
    return (0 <= handle < len(Streams) and
           Streams[handle] != None and
           Streams[handle].mode == mode)

def subr_prompt(arg):                 # Subr01
    global Prompt
    if arg != None:
        Prompt = arg
    return Prompt

# Access to input buffer

def readchar():                       # Subr0
    x = peekchar()
    inputstream.current += 1
    return x

def peekchar():                       # Subr0
    if inputstream.current > inputstream.last:
        inputstream.readline()
    return inputstream.inputbuffer[inputstream.current]

def subr_readline():                  # Subr0
    if inputstream.current > inputstream.last:
        inputstream.readline()
    r = inputstream.inputbuffer[inputstream.current:].rstrip()
    inputstream.current = len(inputstream.inputbuffer)
    return r

# Character types

def InitChars():
    global typechar
    global NullCh, QuoteCh, BComCh, EComCh, SepCh, MacroCh
    global StringCh, SymbolCh, SpecialCh, LParCh, RParCh

    (NullCh, QuoteCh, BComCh, EComCh, SepCh, MacroCh,
     StringCh, SymbolCh, SpecialCh, LParCh, RParCh) = range(11)

    typechar = dict(zip([chr(x) for x in range(256)], [NullCh] * 32 + [SymbolCh] * (256 - 32)))

    typechar[';' ] = BComCh
    typechar['\n'] = EComCh
    typechar[' ' ] = SepCh
    typechar['\t'] = SepCh
    typechar['(' ] = LParCh
    typechar[')' ] = RParCh
    typechar['"' ] = StringCh
    typechar['|' ] = SpecialCh

# Reading and access to valid characters

def readcv():
    ch = readchar()
    tc = typechar[ch]

    if tc == BComCh:
        return readcom()
    elif tc == EComCh:
        return ' '
    elif tc == NullCh:
        return readcv()
    else:
        return ch

def peekcv():
    ch = peekchar()
    tc = typechar[ch]

    if tc == BComCh:
        return readcom()
    elif tc == EComCh:
        return ' '
    elif tc == NullCh:
        readchar()
        return peekcv()
    else:
        return ch

def nextcv():
    cv = readcv()
    while typechar[cv] == SepCh:
        cv = readcv()
    return cv

def readcom():
    while typechar[readchar()] != EComCh:
        pass
    return ' '

# Dot may be used in symbol names but not alone. In that case, it is
# considered as the dotted pair marker.

def isdottedpair(cv):
    return cv == '.' and typechar[peekcv()] != SymbolCh

# Reading

def readitem():
    return readinternal(nextcv())

# Reading an item, cv is the first valid character

def readinternal(cv):
    tc = typechar[cv]
    if tc == LParCh:
        return readlist(nextcv())
    elif tc == RParCh:
        return readinternal(nextcv())
    elif tc == StringCh:
        return readstring()
    elif tc == SpecialCh:
        return readspecial()
    elif tc == MacroCh:
        return readmacro(cv)
    elif isdottedpair(cv):
        readerror(2)
    else:
        return readatom(cv)

# Reading symbols and numbers

def readatom(cv):
    x = cv
    while typechar[peekcv()] == SymbolCh:
        x += readcv()
    try:
        return int(x)
    except ValueError:
        return intern(x)

# Reading special symbols and strings

def readspecial():
    return intern(readuntil(SpecialCh))

def readstring():
    return readuntil(StringCh)

def readuntil(delim):
    x = ''
    while True:
        ch = readchar()
        if ch == '\n':
            readerror(3)
        elif typechar[ch] != delim:
            x += ch
        elif typechar[peekchar()] == delim:
            x += readchar()
        else:
            return x

# Reading macro characters

def readmacro(c):
    sym = intern(c)
    func = sym.fval
    return evalexpr(sym, func, Nil, Nil)

# Reading lists

def readlist(cv):
    if typechar[cv] == RParCh:
        return Nil
    elif isdottedpair(cv):
        readerror(2)
    else:
        inputstream.readinglist += 1
        x = readinternal(cv)
        y = readcdr(nextcv())
        inputstream.readinglist -= 1
        return cons(x, y)

def readcdr(cv):
    if typechar[cv] == RParCh:
        return Nil
    elif isdottedpair(cv):
        return readdot(nextcv())
    else:
        x = readinternal(cv)
        y = readcdr(nextcv())
        return cons(x, y)

def readdot(cv):
    if typechar[cv] == RParCh:
        readerror(2)
    else:
        x = readinternal(cv)
        if typechar[nextcv()] != RParCh:
            readerror(2)
        else:
            return x

# Reading error

def readerror(errornum):
    error(SyntaxError, 'read', errornum)

# Loading

def load(filename):
    global inputstream

    inputstreambak = inputstream
    inputstreamnew = TInputStreamFile(filename)
    try:
        inputstream = inputstreamnew
        itag(Eof, loadloop)
    finally:
        inputstream = inputstreambak
    return filename

def loadloop():
    while True:
        eval(readitem())
    return Nil

# Printing atoms

def prinatom(x):
    outputstream.prinstring(str(x))

# Printing lists

def princons(x):
    outputstream.prinstring('(')
    while consp(x.cdr):
        prin(x.car)
        outputstream.prinstring(' ')
        x = x.cdr
    prin(x.car)
    if not null(x.cdr):
        outputstream.prinstring(' . ')
        prin(x.cdr)
    outputstream.prinstring(')')

# Printing functions

def prin(x):
    if atom(x):
        prinatom(x)
    else:
        princons(x)
    return x

def terpri():
    outputstream.prinstring('\n')
    return Nil

def printitem(x):
    prin(x)
    terpri()
    return x

# Subr evaluation

# Evaluation functions

def subr_selfvalue():                 # SSubr, handled in evalfn
    return None

def subr_quote(x):                    # FSubr
    return x.car

# Control functions

def subr_if(larg):                    # FSubr
    if evalprotect(larg.car) != Nil:
        return eval(larg.cdr.car)
    else:
        return eprogn(larg.cdr.cdr)

def subr_while(larg):                 # FSubr
    try:
        Stack.append({'eval':None})

        while eval(larg.car) != Nil:
            eprogn(larg.cdr)
        return Nil
    finally:
        Stack.pop()

# Type predicates

def subr_symbolp(x):                  # Subr1
    return T if symbolp(x) else Nil

def subr_numberp(x):                  # Subr1
    return x if numberp(x) else Nil

def subr_stringp(x):                  # Subr1
    return x if stringp(x) else Nil

def subr_consp(x):                    # Subr1
    return x if consp(x) else Nil

# Equality

def subr_eq(x, y):                    # Subr2
    return T if id(x) == id(y) else Nil

# Symbols

def oblist():                         # Subr0
    head = cons(Nil, Nil)
    tail = head
    for x in Oblist:
        tail.cdr = cons(intern(x), Nil)
        tail = tail.cdr
    return head.cdr

def subr_value(sym, val=None):        # Subr12
    if val == None:
        assert_symbolp(sym, 'value')
        assert_boundp(sym, 'value')
    else:
        assert_variablep(sym, 'value' )
        sym.cval = val

    return sym.cval

def subr_boundp(sym):                 # Subr1
    assert_symbolp(sym, 'boundp')
    return T if sym.cval != None else Nil

def subr_makunbound(sym):             # Subr1
    assert_variablep(sym, 'makunbound')
    sym.cval = None
    return sym

def subr_fvalue(sym, val=None):       # Subr12
    assert_symbolp(sym, 'fvalue')
    if val == None:
        return getfvalue(sym)
    else:
        return setfvalue(sym, val)

def getfvalue(sym):
    if sym.ftype == None:
        return Nil
    elif sym.ftype in [Lambda, Macro, DMacro]:
        return cons(sym.ftype, sym.fval)
    elif hasattr(sym.fval, func_name_attribute):
        return cons(sym.ftype, getattr(sym.fval, func_name_attribute))
    else:
        error(ArgError, 'valfn', sym)

def setfvalue(sym, val):
    assert_listp(val, 'fvalue')
    if val == Nil:
        sym.ftype = None
    else:
        assert_symbolp(val.car, 'fvalue')
        sym.ftype = val.car
        if stringp(val.cdr):
            sym.fval = globals()[val.cdr]
        else:
            sym.fval = val.cdr
    return val

def subr_de (x):                      # FSubr
    return defun(x, Lambda)

def subr_dm (x):                      # FSubr
    return defun(x, Macro)

def subr_dmd(x):                      # FSubr
    return defun(x, DMacro)

def defun(x, type):
    func = x.car
    func.ftype = type
    func.fval = x.cdr
    return func

def subr_plist(sym, val=None):        # Subr12
    assert_symbolp(sym, 'plist')

    if val != None:
        assert_listp(val, 'plist')
        sym.plist = val

    return sym.plist

def subr_memprop(sym, ind):           # Subr2
    assert_symbolp(sym, 'getprop')
    list = sym.plist
    while list != Nil:
        if list.car == ind:
            return list
        else:
            list = list.cdr.cdr

    # not found
    return Nil

# Lists

def subr_car(x):                      # Subr1
    assert_listp(x, 'car')
    return x.car

def subr_cdr(x):                      # Subr1
    assert_listp(x, 'cdr')
    return x.cdr

def subr_cons(x, y):                  # Subr2
    return cons(x, y)

def subr_rplaca(x, y):                # Subr2
    assert_consp(x, 'rplaca')
    x.car = y
    return x

def subr_rplacd(x, y):                # Subr2
    assert_consp(x, 'rplacd')
    x.cdr = y
    return x

def subr_nthcdr(n, l):                # Subr2
    assert_numberp(n, 'nthcdr')
    assert_listp(l, 'nthcdr')
    i = 0
    while i < n and consp(l):
        l = l.cdr
        i += 1
    return l

# Polymorphic functions

def subr_eqval(x, y):                 # Subr2
    return T if x == y else Nil

def subr_lt(x, y):                    # Subr2
    assert_sametype(x, y, '<')
    return T if x < y else Nil

def subr_gt(x, y):                    # Subr2
    assert_sametype(x, y, '>')
    return T if x > y else Nil

def subr_add(x, y):                   # Subr2
    if numberp(x):
        assert_numberp(y, '+')
        return x + y
    if stringp(x):
        assert_stringp(y, '+')
        return x + y
    else:
        error(ArgError, '+', cons(x, y))

# Numbers

def subr_sub(x, y):                   # Subr2
    assert_numberp(x, '-')
    assert_numberp(y, '-')
    return x - y

def subr_mul(x, y):                   # Subr2
    assert_numberp(x, '*')
    assert_numberp(y, '*')
    return x * y

def subr_div(x, y):                   # Subr2
    assert_numberp(x, '/')
    assert_numberp(y, '/')
    return x // y

def subr_mod(x, y):                   # Subr2
    assert_numberp(x, '%')
    assert_numberp(y, '%')
    return x % y

# Characters

def subr_typech(char, type=None):     # Subr12
    assert_charp(char, 'typech')
    c = char[0]
    if type != None:
        typechar[c] = type
    return typechar[c]

# Strings

def subr_strlen(x):                   # Subr1
    assert_stringp(x, 'strlen')
    return len(x)

def subr_strnth(x, n):                # Subr2
    assert_stringp(x, 'strnth')
    assert_numberp(n, 'strnth')
    assert_condition(0 <= n < len(x), IndexError, 'strnth', n)
    return x[n]

def subr_strpos(x, y):                # Subr2
    assert_stringp(x, 'strpos')
    assert_stringp(y, 'strpos')
    return x.find(y)

def subr_strsub(larg):                # NSubr
    assert_condition(2 <= len(larg) <= 3, ArgNumberError, 'strsub', len(larg))
    assert_stringp(larg[0], 'strsub')
    assert_numberp(larg[1], 'strsub')
    if len(larg) == 2:
        return larg[0][larg[1]:]
    else:
        assert_numberp(larg[2], 'strsub')
        return larg[0][larg[1]:larg[2]]

def subr_string(x):                   # Subr1
    return str(x)

def subr_symbol(x):                   # Subr1
    assert_stringp(x, 'symbol')
    return intern(x)

def subr_unique(x):                   # Subr1
    assert_stringp(x, 'unique')
    return symbol(x)

def subr_number(x):                   # Subr1
    assert_stringp(x, 'number')
    try:
        y = int(x)
        return y
    except ValueError:
        error(NotNumberArgError, 'number', x)

# System

def subr_toplevel():                  # Subr0
    x = eval(readitem())
    print('= ', end=' ')
    printitem(x)
    return x

def subr_end():                       # Subr0
    sys.exit()

def subr_time():                      # Subr0
    return int(time.time())

def subr_cls():                       # Subr0
    print(os.system('cls'), chr(13), ' ', chr(13), end=' ')
    return T

def format_stackrec(stackrec):
    if 'eval' in stackrec:
        return cons('eval', cons(stackrec['eval'], Nil))
    if 'tag' in stackrec:
        return cons('tag', cons(stackrec['tag'], Nil))
    if 'lock' in stackrec:
        return cons('lock', Nil)
    if 'lambda' in stackrec:
        return cons('lambda', cons(stackrec['lambda'], Nil))
    return Nil

def subr_stack():                     # Subr0
    return lisplist([format_stackrec(x) for x in Stack])

# Helpers

def lisplist(iterable):
    head = cons(Nil, Nil)
    tail = head
    for x in iterable:
        tail.cdr = cons(x, Nil)
        tail = tail.cdr
    return head.cdr

def hostlist(list):
    r = []
    while consp(list):
        r.append(list.car)
        list = list.cdr
    return r

# Initialisation of builtin functions

def InitSubrs():
    intern('eval'    , Subr1 , eval)
    intern('evlis'   , Subr1 , evlis)
    intern('eprogn'  , Subr1 , eprogn)
    intern('progn'   , FSubr , eprogn)
    intern('quote'   , FSubr , subr_quote)
    intern('apply'   , Subr2 , applyform)
    intern('if'      , FSubr , subr_if)
    intern('while'   , FSubr , subr_while)
    intern('tag'     , FSubr , subr_tag)
    intern('exit'    , FSubr , subr_exit)
    intern('lock'    , FSubr , subr_lock)
    intern('throw'   , FSubr , subr_throw)
    intern('symbolp' , Subr1 , subr_symbolp)
    intern('numberp' , Subr1 , subr_numberp)
    intern('stringp' , Subr1 , subr_stringp)
    intern('consp'   , Subr1 , subr_consp)
    intern('eq'      , Subr2 , subr_eq)
    intern('oblist'  , Subr0 , oblist)
    intern('value'   , Subr12, subr_value)
    intern('boundp'  , Subr1 , subr_boundp)
    intern('makunbound', Subr1, subr_makunbound)
    intern('fvalue'  , Subr12, subr_fvalue)
    intern('de'      , FSubr , subr_de)
    intern('dm'      , FSubr , subr_dm)
    intern('dmd'     , FSubr , subr_dmd)
    intern('plist'   , Subr12, subr_plist)
    intern('memprop' , Subr2,  subr_memprop)
    intern('car'     , Subr1 , subr_car)
    intern('cdr'     , Subr1 , subr_cdr)
    intern('rplaca'  , Subr2 , subr_rplaca)
    intern('rplacd'  , Subr2 , subr_rplacd)
    intern('cons'    , Subr2 , subr_cons)
    intern('nthcdr'  , Subr2 , subr_nthcdr)
    intern('='       , Subr2 , subr_eqval)
    intern('<'       , Subr2 , subr_lt)
    intern('>'       , Subr2 , subr_gt)
    intern('+'       , Subr2 , subr_add)
    intern('-'       , Subr2 , subr_sub)
    intern('*'       , Subr2 , subr_mul)
    intern('/'       , Subr2 , subr_div)
    intern('%'       , Subr2 , subr_mod)
    intern('strlen'  , Subr1 , subr_strlen)
    intern('strnth'  , Subr2 , subr_strnth)
    intern('strpos'  , Subr2 , subr_strpos)
    intern('strsub'  , NSubr , subr_strsub)
    intern('symbol'  , Subr1 , subr_symbol)
    intern('unique'  , Subr1 , subr_unique)
    intern('number'  , Subr1 , subr_number)
    intern('string'  , Subr1 , subr_string)
    intern('openi'   , Subr1 , subr_openi)
    intern('openo'   , Subr1 , subr_openo)
    intern('close'   , Subr1 , subr_close)
    intern('input'   , Subr01, subr_input)
    intern('output'  , Subr01, subr_output)
    intern('prompt'  , Subr01, subr_prompt)
    intern('readline', Subr0 , subr_readline)
    intern('typech'  , Subr12, subr_typech)
    intern('readchar', Subr0 , readchar)
    intern('peekchar', Subr0 , peekchar)
    intern('read'    , Subr0 , readitem)
    intern('load'    , Subr1 , load)
    intern('print'   , Subr1 , printitem)
    intern('prin'    , Subr1 , prin)
    intern('terpri'  , Subr0 , terpri)
    intern('toplevel', Subr0 , subr_toplevel)
    intern('error'   , NSubr , subr_error)
    intern('time'    , Subr0 , subr_time)
    intern('end'     , Subr0 , subr_end)
    intern('cls'     , Subr0 , subr_cls)
    intern('stack'   , Subr0 , subr_stack)

# Assertions

def assert_condition(condition, error_symbol, func, arg):
    if not condition:
        error(error_symbol, func, arg)

def assert_symbolp(arg, func):
    assert_condition(symbolp(arg), NotSymbolArgError, func, arg)

def assert_numberp(arg, func):
    assert_condition(numberp(arg), NotNumberArgError, func, arg)

def assert_stringp(arg, func):
    assert_condition(stringp(arg), NotStringArgError, func, arg)

def assert_consp(arg, func):
    assert_condition(consp(arg), NotConsArgError, func, arg)

def assert_listp(arg, func):
    assert_condition(listp(arg), NotListArgError, func, arg)

def assert_variablep(arg, func):
    assert_condition(variablep(arg), NotVarError, func, arg)

def assert_boundp(arg, func):
    assert_condition(not unboundp(arg), UndefSymError, func, arg)

def assert_sametype(x, y, func):
    if (x.__class__ == y.__class__) or (numberp(x) and numberp(y)):
        return
    else:
        error(ArgError, func, cons(x, y))

def assert_charp(arg, func):
    assert_condition(charp(arg), NotCharArgError, func, arg)

# Error handling

def printerror(error_symbol, func, arg):
    print('\n** ', end=' ')
    prin(error_symbol if unboundp(error_symbol) else error_symbol.cval)
    print(' : ', end=' ')
    prin(func)
    print(' : ', end=' ')
    prin(arg)
    print('\n')

def error(error_symbol, func, arg):
    # enable to redefine error function in lisp
    applyform(intern('error'), lisplist([error_symbol, func, arg]))

def subr_error(larg):                 # NSubr
    assert_condition(len(larg) == 3, ArgNumberError, 'error', len(larg))
    error_symbol, func, arg = larg
    printerror(error_symbol, func, arg)
    # the result is the name of the error.
    # body of exit form being evaluated, constructs ('error_symbol)
    iexit(TopError, cons(cons(intern('quote'), cons(error_symbol, Nil)), Nil))

# Main loop

def mainloop():
    while True:
        try:
            itag(TopError, calltoplevel)
        except SystemExit:
            return
        except EvalException as e:
            printerror(UndefTagError, 'eval', e.tag)
        except (RuntimeError, ZeroDivisionError) as e:
            print('\n** Runtime error: %s\n' % e.args)
        except KeyboardInterrupt:
            print('\n** Interrupt by user.\n')
        except:
            print('\n** Host error.\n')
            raise

def calltoplevel():
    # enable to redefine toplevel function in lisp
    applyform(intern('toplevel'), Nil)

# Main

def init():
    InitChars()
    InitStreams()
    InitSymbols()
    InitSubrs()
    sys.setrecursionlimit(8000)
    if os.path.exists(findfile('sapid.ini')):
        itag(TopError, loadini)

def loadini():
    load('sapid.ini')

init()
if __name__ == '__main__':
    mainloop()
