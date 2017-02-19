# Velus: certified Lustre compiler

This development implements and prove the correctness of a certified
Lustre compiler backend.

## Using the compiler

To run the compiler:

    $ $VELUS_DIR/velus -h

In particular, to compile to assembly:

    $ $VELUS_DIR/velus $VELUS_DIR/tests/count.lus

In particular, to compile to assembly and dump the intermediary Clight code:

    $ $VELUS_DIR/velus -dclight $VELUS_DIR/tests/count.lus


## Execution from Docker

Note: this is the easiest method for compiling and running the compiler.


We provide a pre-configured compilation environment in a Docker
container:

    $ cd $VELUS_DIR
    $ sh run.sh

This will start a container, compile the development and give you
access to a Bash shell from which you will be able to run the
compiler.

## Execution from Docker

Note: this is the easiest method for editing, compiling and running
the compiler.


We provide a Virtualbox image including our development as well as
Emacs/proofgeneral and CoqIDE editors.

## Local installation

Note: this is the most efficient method for editing, compiling and
running the compiler.


It also possible to build Velus locally, without resorting to a Docker
image. Velus has been implemented in Coq.8.4.6. It includes a modified
version of CompCert and depends on menhir.20170101.

To build a self-contained installation for compiling and running
Velus, we recommend installing an ad-hoc
[opam](https://opam.ocaml.org/) directory:

    $ cd $VELUS_DIR
    $ mkdir opam
    $ opam init --root=opam --compiler=4.02.3
    $ eval `opam config env --root=$VELUS_DIR/opam`
    $ opam repo add coq-released https://coq.inria.fr/opam/released 
    $ opam install -j4 coq.8.4.6 menhir.20170101

To check the proofs and build Velus:

    $ cd $VELUS
    $ make
