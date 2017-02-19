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

## Cross-references 

In the following, we relate the definitions presented in the paper (on
the left, in italics) to their incarnation in the formal development
(on the right, in typewriter font).

 - [Figure 2 "SN-Lustre: abstract syntax"](./NLustre/NLSyntax.v)
   * expression (_e_):  `lexp`
   * control expression (_ce_): `cexp`
   * equation (_eqn_): `equation`
   * declaration (_d_): `node`

 - [Figure 3 "SN-Lustre: example program"](./tests/tracker.lus)

 - [Figure 4 "Obc: abstract syntax"](./Obc/ObcSyntax.v)
   * expression (_e_): `exp`
   * statement (_s_): `stmt`
   * class declaration (_cls_): `class`

 - [Figure 5 "Core of the SN-Lustre to Obc Translation"](./NLustreToObc/Translation.v)
   * _var_: `tovar`
   * _trexp_: `translate_lexp`
   * _trcexp_: `translate_cexp`
   * _ctrl_: `Control`
   * _treqs_: `translate_eqn`
   * _treqss_: `translate_eqns`
   * _treqr_: `translate_reset_eqn`
   * _treqsr_: `translate_reset_eqns`
   * _translate_: `translate_node`

 - Section 3.1 "Semantics Models"
   * ["Representation of streams"](./NLustre/Stream.v)
   * [Dataflow semantics](./NLustre/NLSemantics.v)
     - semantics of variable: `sem_var`
     - semantics of clocks: `sem_clock`
     - semantics of expressions: `sem_lexp`
     - semantics of clocked expressions: `sem_laexp`
     - semantics of control expressions: `sem_cexp`
     - semantics of clocked control expressions: `sem_caexp`
     - semantics of an equation: `sem_equation`
     - semantics of a node: `sem_node`
   * [Figure 6 "Definition of the `fby#` operator"](./NLustre/Stream.v)
     - _hold#_: `hold`
     - _fby#_: `fby`
   * [Imperative semantics](./Obc/ObcSemantics.v)
     - local memory (_env_): `stack`
     - global memory (_mem_): `heap`
     - semantics of expressions: `exp_eval`
     - semantics of statements: `stmt_eval`
   * [Memory](./RMemory.v)

 - Section 3.2 "Correctness"
   * [Memory semantics of equations](./NLustre/MemSemantics.v): `msem_equation`
   * [Figure 7 "SN-Lustre/Obc memory correspondence](./NLustreToObc/Correctness/MemoryCorres.v): `Memory_Corres` and `Memory_Corres_eq`
   * [Lemma 1 "Correctness of the translation"](./NLustreToObc/Correctness.v): `dostep'_correct`

 - [Section 3.3 "Fusion Optimization"](./Obc/Fusion.v)
   * _fuse_: `fuse`
   * Figure 8 "Obc optimization: loop fusion" (_zip_): `zip`
   * _Fusible_: `Fusible`
   * _MayWrite_: `Can_write_in`
   * equivalence relation *s1 \equiv_{fuse} s2*: `fuse_eval_eq`

 - [Section 4 "Generation of Clight"](./ObcToClight/Generation.v)
   * [Big-step judgement for Clight](./CompCert/cfrontend/ClightBigstep.v)
   
 - [Figure 10 "Operator interface: values](./Operators.v)

 - [Section 4.2 "Relating Memories"](./ObcToClight/SepInvariant.v)
   * [Separation assertions](./CompCert/common/Separation.v)
     - _p * q_: `sepconj`
     - _m |= p_: `m_pred`
   * [State representation](./ObcToClight/MoreSeparation.v)
     - _sepall_: `sepall`
   * *match_states*: `staterep`
 - [Section 4.3 "Proof of generation"](ObcToClight/Correctness.v): Lemma `reacts'`