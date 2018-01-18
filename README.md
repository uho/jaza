Jaza is an `Animator' for the Z formal specification language.

It is intended to help you:
    * evaluate Z expressions;
    * test Z schemas against example data values;
    * execute some Z specifications.

Copyright (C) Mark Utting, 2000-2005.
Department of Computer Science,
The University of Waikato,
New Zealand.

See COPYING for license and warranty information.

See userman/master.pdf for full documentation
and the examples directory for several example specifications.

Quick Start Guide
=================

1. If you have a compiled version of Jaza, you should be able to
   just execute the 'jaza' program that is in this directory.  

2. If you have the source distribution, you must install Hugs
   (from http://www.haskell.org/hugs), then type:

      runhugs TextUI

Either way, you should see the prompt  "JAZA>".
Then you can type 'help' to see a summary of the available
commands.

Please email marku@cs.waikato.ac.nz if you have problems/questions.


Known Bugs/Limitations
======================
Jun05: A recent optimisation to flatten nested \exists quantifiers,
does not handle the case where there are several \exists quantifiers
at the same level with the same bound variable names.  For example,
\{.... | (\exists x:T1 @...) \land (\exists x:T2 @...) \} can produce
strange errors.  The workaround to this is to rename some of the
bound variables...
(This is also why you should expect one test in tests/scope.jaza to fail.)

Generics, axiomatic definitions, and recursive freetypes are not handled.
