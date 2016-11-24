# Velus: certified Lustre compiler

This development implements and prove the correctness of a certified
Lustre compiler backend.

## Installation

Velus has been implemented in Coq.8.4.6. It includes a modified
version of CompCert and depends on menhir.20161115.

To build a self-contained installation for compiling and running
Velus, we recommend installing an ad-hoc
[opam](https://opam.ocaml.org/) directory:

    $ cd $VELUS_DIR
    $ mkdir opam
    $ opam init --root=opam --compiler=4.01.0
    $ eval `opam config env --root=$VELUS_DIR/opam`
    $ opam repo add coq-released https://coq.inria.fr/opam/released 
    $ opam install -j4 coq.8.4pl4 menhir.20161115

To check the proofs and build Velus:

    $ cd $VELUS_DIR/CompCert
    $ make
    $ cd $VELUS
    $ make

## Using the compiler


To run the compiler:

    $ $VELUS_DIR/velus -h

In particular, to compile to Clight:

    $ $VELUS_DIR/velus -dclight $VELUS_DIR/tests/count.lus

In particular, to compile to assembly:

    $ $VELUS_DIR/velus $VELUS_DIR/tests/count.lus


