# Mechanized Semantics and Verified Compilation for a Dataflow Synchronous Language with Reset

These source files contain the implementation, models, and proof of
correctness of a formally verified Lustre compiler backend.
This version of the project is the one referred by the PhD thesis of Lélio Brun.

This file contains instructions for (i) using the compiler, (ii) running
from local opam installation or from docker, and (iii) cross-references from
material presented in the paper to the source files.

The `examples/` subdirectory contains another readme file presenting several
example programs that can be used to test the compiler.

We are still working on the normalization pass, which means that Lustre
source programs must currently be manually normalized (each `fby` and
`application` must be given its own equation; `merge` and `if` constructs
may only appear at the top level of an expression; output variables cannot
be defined directly by `fby` equations). Also, the `->` and `pre` operators
used in many Lustre programs are not yet treated. An equation like
`x = e1 -> e2` must instead be "manually compiled" into
```
x = if init then e1 else e2
init = true fby false
```

and an uninitialized delay `pre e` must be replaced by an initialized one
`0 fby e`.

Compiler error messages are still very brutal. In particular the parser only
reports syntax errors with a line number and character offset. We will
implement more helpful messages when we have finalized one or two remaining
details of the final (unnormalized) language.


## Building the compiler

We describe two ways of building Vélus:
* using a [Docker] container environment, which is easier and still allows
  read/write access to the source files, or
* using a manual local installation, which is better if one wants to
  interactively run the Coq proofs.

If you cloned the repository, do not forget to run `git submodule update --init`
to update the sub-module [CompCert].

In both cases be aware that the building process can take almost 25min on a dual
core Intel Core i7-6600U.

### Docker

The script `rundocker.sh` retrieves a container from the [Docker Hub] (~1Gb),
starts the container, compiles the development (thus checking the proofs) and
gives you access to a Bash shell from which you will be able to run the
compiler.

The container accesses the present files: you can transparently edit them
from the host and compile them in the guest.

### Local installation

#### Prerequisites

Vélus builds on the following dependencies:

* 4.03 ≤ [OCaml] ≤ 4.07.1
* [Coq] = 8.9.0
* 20161201 ≤ [Menhir] ≤ 20181113
* [OCamlbuild] ≥ 0.14.0

We recommend installing the [opam] OCaml package manager to install the
dependencies as follows.
In the case where the version of OCaml available in your system package manager
is too old, you should still be able to install a newer version by using an opam
switch.
```
opam init                                  # if running opam for the first time
opam switch create 4.07.1                  # create a global switch
eval $(opam env)                           # update PATH
opam update                                # sync opam database
opam install coq.8.9.0 menhir ocamlbuild   # install dependencies
```

#### Build

Type `./configure [options] <target>` where `<target>` is one of the list given
in the [CompCert manual](http://compcert.inria.fr/man/manual002.html#sec21),
e.g., `x86_64-linux`.
The configuration script uses the same options as CompCert's, except one
optional `-compcertdir` to specify the CompCert directory.
This will set up the configuration for both the Vélus development and the
CompCert development (in the subdirectory `CompCert/` by default).

Then, typing `make` will launch the building process of CompCert and Vélus.


## Invocation

The compiler can be called with:

`./velus <options> <sourcefile.ext>`

Options are described in the output of `./velus -h`.
In particular, the flags `-dstc`, `-dobc` and `-dclight` enable the generation
of Stc, Obc and Clight intermediate files.
The flag `-nofusion` is used to disable the fusion optimization.

On success, the compiler will output an assembly file `<sourcefile.s>`.
The compiler can be tested against two test suites:
```
make runexamples   # run the compiler on programs in ./examples/
make runtests      # run the compiler on programs in ./tests/
```
The programs in `./examples/` are described in a dedicated `readme.md`.
In particular, the examples `nav.lus`, `ppdp00.lus` and `stopwatch_reset.lus`
use the modular reset construct, as well as the test `ok_resetsoup.lus`.

If generated with the `-sync` option, the generated assembly file can be further
compiled to executable code with user IO loop by calling:

`CompCert/ccomp -stdlib CompCert/runtime <sourcefile>.sync.c <sourcefile>.s`

Thus the running example of the dissertation can be executed with the following:
```
./velus -sync examples/nav_forward.lus
CompCert/ccomp -stdlib CompCert/runtime examples/nav_forward.sync.c examples/nav_forward.s
./a.out
```
The script `compile` can also be used.
It takes the source file, the main node name and generates an executable program
along with intermediate code for all passes.
```
./compile examples/nav_forward nav
examples/nav_forward.exe
```


[Ocaml]: http://ocaml.org/
[Coq]: https://coq.inria.fr/
[opam]: https://opam.ocaml.org/
[Menhir]: http://gallium.inria.fr/~fpottier/menhir/
[OCamlbuild]: https://github.com/ocaml/ocamlbuild/
[Docker]: https://www.docker.com/
[Docker Hub]: https://hub.docker.com/
[CompCert]: http://compcert.inria.fr/
