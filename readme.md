# A Formally Verified Compiler for Lustre

These source files contain the implementation, models, and proof of 
correctness of a formally verified Lustre compiler backend.

This file contains instructions for (i) using the compiler, (ii) running 
from docker, a virtual machine, or a local opam installation, and (iii) 
cross-references from material presented in the paper to the source files.

The `tests/` subdirectory contains another readme file presenting several 
example programs that can be used to test the compiler.

Since submitting the paper, we have implemented the scheduling pass (the 
relevant dashed line in Figure 1 becomes solid and elaboration produces 
N-Lustre).

We are still working on the normalization pass, which means that Lustre 
source programs must currently be manually normalized (each `fby` and 
`application` must be given its own equation; `merge` and `if` constructs 
may only appear at the top level of an expression; output variables cannot 
be defined directly by `fby` equations). Also, the `->` and `pre` operators 
used in many Lustre programs are not yet treated. An equation like

    x = e1 -> e2

must instead be "manually compiled" into

    x = if init then e1 else e2
    init = true fby false

and an uninitialized delay `pre e` must be replaced by an initialized one
`0 fby e`.

Compiler error messages are still very brutal. In particular the parser only 
reports syntax errors with a line number and character offset. We will 
implement more helpful messages when we have finalized one or two remaining 
details of the final (unnormalized) language.

## Using the compiler

To run the compiler:

    ./velus -h

In particular, typing

    ./velus tests/count.lus

will compile the Lustre program in tests/count.lus into an assembler program 
tests/count.s.

The compiler also accepts the options

* -snlustre
  Output the scheduled code into <file>.sn.lustre. Use `-fullclocks` to show 
  the full abstract clock paths in the output code (rather than the standard 
  `when` declarations).

* -dobc
  Output the Obc intermediate code into <file>.obc

* -dclight
  Output the generated Clight code into <file>.light.c

* -nofusion
  Disable the if/then/else fusion optimization.

* -sync
  Generate an optional `main_sync` entry point and a <file>.sync.c 
  containing a simulation that prints the outputs at each cycle and requests 
  inputs. In contrast to `main`, this entry point is not formally verified 
  but it is useful for testing the dynamic behaviour of compiled programs.
  The alternative entry point can be selected by compiling using CompCert 
  with `-Wl,-emain_sync` (or with by passing `-emain_sync -m32` to `gcc`).
  See `tests/Makefile` for examples.

## Execution from Docker

Note: this is the easiest method for compiling and running the
compiler, not for interactively editing the compiler. To step through
the proofs, we recommend using a virtual machine or a local
installation (see below).

We provide a pre-configured compilation environment in a Docker
container:

    $ cd $VELUS_DIR
    $ sh run.sh

This will retrieve a container from the dockerhub (~800Mb), start a
container, compile the development (thus checking the proofs) and give
you access to a Bash shell from which you will be able to run the
compiler.

The docker accesses the present files: you can transparently edit them
from the host and compile them in the guest.

## Execution from the Virtualbox image

We provide a Virtualbox image including our development as well as the
Emacs/proofgeneral editor.

## Local installation

Note: this is the most efficient method for editing, compiling, and
running the compiler.

It also possible to build Vélus locally, without resorting to a Docker or
Virtualbox image. Vélus has been implemented in Coq.8.4.6. It includes a
modified version of CompCert and depends on menhir.20170101.

To build a self-contained installation for compiling and running
Vélus, we recommend installing an ad-hoc
[opam](https://opam.ocaml.org/) directory:

    $ cd $VELUS_DIR
    $ mkdir opam
    $ opam init --root=opam --compiler=4.02.3
    $ eval `opam config env --root=$VELUS_DIR/opam`
    $ opam repo add coq-released https://coq.inria.fr/opam/released
    $ opam install -j4 coq.8.4.6 menhir.20170101

To check the proofs and build Vélus:

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
 - [Section 4.3 "Proof of generation"](VelusCorrectness.v): `Theorem behavior_asm`
