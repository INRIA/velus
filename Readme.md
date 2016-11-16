o# Rustre: certified Lustre compiler

This development implements and prove the correctness of a certified
Lustre compiler backend.

## Installation

Rustre has been implemented in Coq.8.4.6. It includes a modified
version of CompCert and depends on menhir.20161115.

To build a self-contained installation for compiling and running
Rustre, we recommend installing an ad-hoc
[opam](https://opam.ocaml.org/) directory:

    $ cd $RUSTRE_DIR
    $ mkdir opam
    $ opam init --root=opam --compiler=4.01.0
    $ eval `opam config env --root=$RUSTRE_DIR/opam`
    $ opam repo add coq-released https://coq.inria.fr/opam/released 
    $ opam install -j4 coq.8.4pl4 menhir.20161115

To check the proofs and build Rustre:

    $ cd $RUSTRE_DIR/CompCert
    $ make
    $ cd $RUSTRE
    $ make

## Using the compiler


To run the compiler:

    $ $RUSTRE_DIR/rustre -h

In particular, to compile to Clight:

    $ $RUSTRE_DIR/rustre -dclight $RUSTRE_DIR/tests/count.lus

In particular, to compile to assembly:

    $ $RUSTRE_DIR/rustre $RUSTRE_DIR/tests/count.lus


