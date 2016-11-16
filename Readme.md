# Rustre: certified Lustre compiler

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
    $ opam init --root=opam --compiler=4.02.3
    $ eval `opam config env --root=$RUSTRE_DIR/opam`
    $ opam repo add coq-released https://coq.inria.fr/opam/released 
    $ opam install -j4 coq.8.4.6 menhir.20161115

To check the proofs and build Rustre:

    $ cd $RUSTRE_DIR
    $ make

## Using the compiler


To run the compiler:

    $ $RUSTRE_DIR/rustre.native -h

