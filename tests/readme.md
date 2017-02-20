Examples
========

This directory contains several example programs. Typing `make` will compile 
all of them, generating the .obc and .light.c intermediate files and .sync.c 
simulation stubs. The resulting .exe binaries can be executed to interact 
with the programs reaction by reaction.

## Basic examples

* count.lus
  The `count` example is a kind of "Hello World" for Lustre. When run at the 
  command-line, it will calculate the cumulative sum of input integers.

* tracker.lus
  This is the example from the paper. It demonstrates the main features of 
  NLustre --namely, node applications, `fby` equations, and the `merge` and 
  `when` constructs--in a simple way.

* avgvelocity.lus
  Another simple example in the same vein as `tracker.lus`.

## More interesting clocks

* cruise.lus
  This example is adapted from the examples distributed with Lucid 
  Synchrone. The most interesting node is `cruiseControl`. It contains three 
  levels of nested clocks. The intermediate code in `cruise.obc` shows the 
  combined effects of good scheduling and the loop fusion optimization. In 
  this case, a minimum number of if/then/else statements is generated (this 
  is not guaranteed, since the scheduling problem is NP-hard; the scheduler 
  uses a simple greedy algorithm). Writing such nestings of `when`s and 
  `merge`s by hand is difficult. This code is the result of compiling three 
  nested automata and simplifying the results.

* emsoft03.lus
  Some more examples with clocking from the "Clocks as First Class Abstract 
  Types" paper in EMSOFT 2003.

## Larger verification examples

* kind_functionalChain.lus
* cocospec_mono_system.lus
* ums_verif.lus

These programs are adapted from the distributions of
[Kind 2](http://kind2-mc.github.io/kind2/) and
[Lustre v4](http://www-verimag.imag.fr/The-Lustre-Toolbox.html?lang=en).
They are used for demonstrating and testing model checking algorithms.
The code is less interesting from a compilation perspective since it does 
not contain any clocks, but it does demonstrate that the compiler works with 
large source files.

Note that the `assert` construct is parsed, but not implemented.

## Miscellaneous

* new_watch.lus
  David Harel's classic wristwatch example, adapted by Gérard Berry in 
  Esterel, rewritten in Lustre and C for the v4 distribution, and adapted 
  here by replacing the external C functions with bit-blasted versions. The 
  logic of the program is quite sophisticated, even though very few clocked 
  constructs are used. The bit-blasting demonstrates the different integer 
  types and bitwise operators imported from CompCert:
  - `lsl`: logical left shift
  - `lsr`: logical right shift
  - `land`: logical (bitwise) conjunction
  - `lor`: logical (bitwise) disjunction
  - `lxor`: logical (bitwise) exclusive-or
  - `uint32`: unsigned 32-bit integer
  - `0x53550000ULL`: unsigned 64-bit integer hexadecimal literal

* prodcell.lus
  The classical Production Cell case-study as related by Leszek Holenderski 
  in his paper in "Formal Development of Reactive Systems", Claus Lewerentz 
  and Thomas Lindner (eds.), Springer-Verlag, LNCS 891, 1995.

* minus.lus
  A simple example from the Lustre v4 distribution.

* halbwachs.lus
  Some classical examples from "Synchronous Programming of Reactive Systems",
  Nicolas Halbwachs, 1993 Kluwer Academic Publishers.

* pip_ex.lus
  A simple three process model of the Priority Inheritance Protocol.

* landing_gear.lus
  A prototype implementation of the case study from Communications in 
  Computer and Information Science, Volume 433, 2014, "ABZ 2014: The Landing 
  Gear Case Study", Proceedings of the case study track of the 4th 
  International Conference on Abstract State Machines, Alloy, B, TLA, VDM, 
  and Z, Toulouse, France, June 2-6, 2014. (eds.) Frédéric Boniol, Virginie 
  Wiels, Yamine Ait Ameur, Klaus-Dieter Schewe


