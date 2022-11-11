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

## Artifact notes

In this artifact, we provide the totality of the source code of Vélus.
Vélus depends on a tweaked version of CompCert, which is also provided.
We have anonymized this distribution by removing the names of the authors of the
submission from the source code.
The artifact can be compiled and executed using the instructions below.

The `stepper-motor` example presented in the submission is available in the
`examples/stepper-motor/` subdirectory. 
We have already provided the code produced by the compiler after each pass in
the same directory.

The `doc/` folder contains the documentation generated from the Coq source files.
The `index.html` file cross-references the Coq definitions relevant to the different sections of the submission.
It also points to the different parts of the compiler outlined in figure 14 of the submission.

## Using the compiler

To run the compiler:

    ./velus -h

In particular, typing

    ./velus examples/count.lus

will compile the Lustre program in examples/count.lus into an assembler
program examples/count.s.

The compiler also accepts the options

* -dnolast
  Output the Lustre code after compilation of last declarations into <file>.nolast.lus

* -dnoauto
  Output the Lustre code after compilation of state machines into <file>.noauto.lus

* -dnoswitch
  Output the Lustre code after compilation of switch blocks into <file>.noswitch.lus

* -dnolocal
  Output the Lustre code after inlining of local scopes into <file>.nolocal.lus

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

Vélus has been implemented in Coq.8.14.1. It includes a
modified version of CompCert and depends on menhir >= 20190626.


To build a self-contained installation for compiling and running
Vélus, we recommend installing an ad-hoc
[opam](https://opam.ocaml.org/) directory:

    $ cd $VELUS_DIR
    $ mkdir opam
    $ opam init --root=opam --compiler=4.13.1
    $ eval `opam config env --root=$VELUS_DIR/opam`
    $ opam install -j4 ocamlbuild coq.8.15.0 menhir

To check the proofs and build Vélus:

    $ cd $VELUS
    $ ./configure [options] target
    $ make

The configuration script uses the same options as CompCert's, except one
additional `-compcertdir` option to specify the CompCert directory.
