# Velus: certified Lustre compiler

This development implements and prove the correctness of a certified
Lustre compiler backend.

## Execution from Docker

We provide a pre-configured development environment in a Docker
container:

    $ cd $VELUS_DIR
    $ sh run.sh

It will start a container, compile the development and give you access
to a Bash shell (equipped with emacs/proofgeneral & CoqIDE).

## Using the compiler


To run the compiler:

    $ $VELUS_DIR/velus -h

In particular, to compile to assembly:

    $ $VELUS_DIR/velus $VELUS_DIR/tests/count.lus

In particular, to compile to assembly and dump the intermediary Clight code:

    $ $VELUS_DIR/velus -dclight $VELUS_DIR/tests/count.lus

## Local installation

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
