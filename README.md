# sapid-lisp
Lot of interesting and sapid parentheses

sapid lisp is a lisp interpretor with the following features:
* dynamic binding
* different name spaces for symbol values and functions
* tail recursion and mutual recursion optimization
* currently two implementations: one in python, a second one in sapid lisp itself. Both implementations share the same lisp modules and testing environment.
* most functions are written in lisp
* limited environment: trace, pretty print, help, testing

No more reasons to choose those features than the fact I studied to write a lisp interpretor this way.

The most interesting features is perhaps the way tail recursion optimization is coded with exceptions. This makes natural and easy to transform a non tail recursion optimized interpretor into an optimized one.

Home page [here](https://sites.google.com/site/sapidlisp/).
