# Description

Levy is a simple implementation of Paul Levy's call-by-push-value
language.  The implementation contains a parser, type-checker, and an
interpreter. It is part of the PL Zoo, see 
<http://math.andrej.com/plzoo/>. 

The Levy language has the following features:

* integers with arithmetical operations *, +, -
* booleans with conditional statements and comparison =, < of integers
* functions
* general recursion (fixpoint operator)
* call-by-push-value features: return, thunk, force, sequence, and let binding

See the file 
[example.levy](http://github.com/robsimmons/levy/blob/datatype/example.levy) 
for concrete syntax, the file
[functions.levy](http://github.com/robsimmons/levy/blob/datatype/functions.levy)
focuses on the concrete syntax of functions.

The Levy# language in this branch of the repository is a modification of Levy
with user-defined datatypes and match statements.
Match statements and user-defined enumerations are discussed in 
[switch.levy](http://github.com/robsimmons/levy/blob/datatype/switch.levy),
full user-defined datatypes are discussed in 
[datatype.levy](http://github.com/robsimmons/levy/blob/datatype/datatype.levy).
Match statements lead to the possibility of non-exhaustive match exceptions;
the possibility of such a runtime error generates a compile-time warning, as
discussed in 
[matching.levy](http://github.com/robsimmons/levy/blob/datatype/matching.levy).

The language is different enough from standard functional languages
that you will not be able to guess how it works without reading about
call-by-push-value first. A good place to start is Paul Levy's FAQ at
<http://www.cs.bham.ac.uk/~pbl/cbpv.html>. There is also a blog post 
about Levy# at 
<http://requestforlogic.blogspot.com/2011/08/embracing-and-extending-levy-language.html> 
aimed at people who may be unfamiliar with call-by-push-value.


# Authors

The authors of Levy are Matija Pretnar <matija@pretnar.info>,
and Andrej Bauer <Andrej.Bauer@andrej.com>, with modifications by
Robert Simmons <robsimmons@gmail.com>. The adaptation to Levy# is by
Robert Simmons.  See the file COPYRIGHT.txt for license information.


# Requirements

You need Objective Caml, http://caml.inria.fr/ version 3.10 or higher.

If you have an older version of Objective Caml you can still compile
the code by hand.


# Compilation

To compile the program run the command

    make

For the native code version run

    make native

If you do not have the make utility, run

    ocamlbuild levy.byte


# Usage

First compile the program. You may then run the interpreter with

    ./levy.byte

If you built the native code version, this would be

    ./levy.native

The file example.levy contains examples that explain the concrete
syntax. You can load it and try it as follows:

    $ ./levy.byte example.levy
