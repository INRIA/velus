#!/bin/sh

# Test if VELUS_DIR is set to avoid going into the home directory
if [ -z ${VELUS_DIR+x} ]; then VELUS_DIR=.; fi

# The architecture to use to configure Compcert
if [ -z ${ARCH+x} ]; then ARCH=ia32-linux; fi

cd $VELUS_DIR
mkdir opam
opam init --root=opam --compiler=4.07.1 -n
eval `opam config env --root=$VELUS_DIR/opam`
opam repo add coq-released https://coq.inria.fr/opam/released
opam install -y -j20 coq.8.9.1 menhir.20200624 coq-menhirlib.20200624
opam pin add coq 8.9.1 # to get the correct version of coqide
make clean
make -C CompCert/ clean
./CompCert/configure $ARCH
make -j
echo "To test the velus compiler, go to the examples/ directory and compile all
examples with 'make'."
echo "If you want to use the CoqIDE editor to browse the Coq development, you
can install it with 'opam install coqide'.  You may need the libgtksourceview2.0-dev package installed in your system."
