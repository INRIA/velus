# Mechanized Semantics and Verified Compilation for a Dataflow Synchronous Language with Reset

## Usage

### Prerequisites

Vélus builds on the following dependencies:

* [OCaml] >= 4.03
* [Coq] = 8.9.0
* [Menhir] >= 20181113
* [OCamlbuild] >= 0.14.0

We recommend installing the [opam] OCaml package manager to install the
dependencies as such:

`opam install coq.8.9.0 menhir ocamlbuild`

In the case where the version of OCaml available in your system package manager
is too old, you should still be able to install a newer version by using an opam
switch.

### Build

Type `./configure <target>` where `<target>` is one of the list given in the
[CompCert manual](http://compcert.inria.fr/man/manual002.html#sec21), e.g.,
`x86_64-linux`.
This will set up the configuration for both the Vélus development and the
CompCert development (in the subdirectory `CompCert/`).

Then, typing `make` will launch the building process of CompCert and Vélus
(this can take almost 25min on a dual core Intel Core i7-6600U).

### Invocation

The compiler can be called with:

`./velus <options> <sourcefile.ext>`

Options are described in the output of `./velus -h`.
On success, the compiler will output an assembly file `<sourcefile.s>`.
If generated with the `-sync` option, this file can be further compiled to
executable code with user IO loop by calling:

`CompCert/ccomp -stdlib CompCert/runtime <sourcefile>.sync.c <sourcefile>.s`

Thus the example of the paper can be executed with the following:

```
./velus -sync examples/nav.lus
CompCert/ccomp -stdlib CompCert/runtime examples/nav.sync.c examples/nav.s
./a.out
```

## Lemmas references

The following table gives the names of the Coq results corresponding to the
numbered lemmas in the paper, and the files where the are stated and proved.
Note that the lemma 3.4 does not correspond to a particular Coq result: it is
given in the paper for clarity but only appear _inside_ another proof in the
development.

| Lemma   | Name                    | Link                                                         |
| :------ | :-----------------------| :----------------------------------------------------------- |
| 2.1     | sem_msem_node           | [NLustre/NLMemSemantics.v](src/NLustre/NLMemSemantics.v)     |
| 2.2     | msem_sem_node           | [NLustre/NLMemSemantics.v](src/NLustre/NLMemSemantics.v)     |
| 2.3     | msem_node_absent_until  | [NLustre/NLMemSemantics.v](src/NLustre/NLMemSemantics.v)     |
| 3.1     | msem_node_initial_state | [NLustreToStc/Correctness.v](src/NLustreToStc/Correctness.v) |
| 3.2     | correctness             | [NLustreToStc/Correctness.v](src/NLustreToStc/Correctness.v) |
| 3.3     | correctness_loop        | [NLustreToStc/Correctness.v](src/NLustreToStc/Correctness.v) |
| 3.5     | exp_correct             | [StcToObc/Correctness.v](src/StcToObc/Correctness.v)         |
| 3.6     | reset_spec              | [StcToObc/Correctness.v](src/StcToObc/Correctness.v)         |
| 3.7     | correctness             | [StcToObc/Correctness.v](src/StcToObc/Correctness.v)         |
| 3.8     | correctness_loop_call   | [StcToObc/Correctness.v](src/StcToObc/Correctness.v)         |


[Ocaml]: http://ocaml.org/
[Coq]: https://coq.inria.fr/
[opam]: https://opam.ocaml.org/
[Menhir]: http://gallium.inria.fr/~fpottier/menhir/
[OCamlbuild]: https://github.com/ocaml/ocamlbuild/
