# A Formally Verified Compiler for Lustre

These source files contain the implementation, models, and proof of
correctness of a formally verified Lustre compiler

This file contains instructions for (i) using the compiler from (ii) a local 
opam installation.

The `examples/` subdirectory contains another readme file presenting several
example programs that can be used to test the compiler.

The `pre` operator used in many Lustre programs is not yet treated.
An uninitialized delay `pre e` must be replaced by an initialized one `0 fby e`.

Compiler error messages are still very brutal. In particular the parser only
reports syntax errors with a line number and character offset. We will
implement more helpful messages when we have finalized one or two remaining
details of the final language.

## Using the compiler

To run the compiler:

    ./velus -h

In particular, typing

    ./velus examples/count.lus

will compile the Lustre program in examples/count.lus into an assembler
program examples/count.s.

The compiler also accepts the options

* -dnlustre
  Output the normalized NLustre code into <file>.n.lus

* -dstc
  Output the Stc intermediate code into <file>.stc

* -dsch
  Output the scheduled code into <file>.sch.stc

* -dobc
  Output the Obc intermediate code into <file>.obc

* -dclight
  Output the generated Clight code into <file>.light.c

* -nofusion
  Disable the if/then/else fusion optimization.

* -sync
  Generate an optional `main_sync` entry point and a <file>.sync.c
  containing a simulation that prints the outputs at each cycle and requests
  inputs. In contrast to `main_proved`, this entry point is not formally verified
  but it is useful for testing the dynamic behaviour of compiled programs.
  See `examples/Makefile` for examples.

## Local installation

Vélus has been implemented in Coq.8.9.1. It includes a
modified version of CompCert and depends on menhir.20200624.

To build a self-contained installation for compiling and running
Vélus, we recommend installing an ad-hoc
[opam](https://opam.ocaml.org/) directory:

    $ cd $VELUS_DIR
    $ mkdir opam
    $ opam init --root=opam --compiler=4.07.1
    $ eval `opam config env --root=$VELUS_DIR/opam`
    $ opam repo add coq-released https://coq.inria.fr/opam/released
    $ opam install -j4 coq.8.9.1 menhir.20200624 coq-menhirlib.20200624

To check the proofs and build Vélus:

    $ cd $VELUS
    $ ./configure [options] target
    $ make

The configuration script uses the same options as CompCert's, except one
additional `-compcertdir` option to specify the CompCert directory.

## Documentation

An index, relating the paper to the documentation, is available in [doc/index.html](doc/index.html).
The documentation can be regenerated using `make documentation`.
