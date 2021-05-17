# Datatypes in Vélus

## Sums 

### Parameterized variants 

I think that this should be handled by Obc, i.e., not compiled into records /
unions in Obc. 
This way, Obc would be as expressive as possible and records and variants would
remain two orthogonal issues. 
Moreover it is not clear that compiling variants in Obc would ease the
correctness proof of the subsequent Clight generation. 
Finally, we would have to model unions in Obc, and I see relatively few
advantages besides compilation of variants.

_Question_: is it meant to be used with `merge` and `when`, or only with `match`
and `automaton`? 

**Lustre**
```ocaml
type foo = 
 | Foo of int * int
 | Bar of int
 
node f(x: foo) returns (y: int);
let
  match x with 
  | Foo (a, b) -> y = a + b; 
  | Bar a -> y = 2 * a;
tel
```

_Orthogonal question_: could `y` be defined with a `fby` in one of the branches?

**Obc**
```ocaml
type foo = 
 | Foo of int * int
 | Bar of int
 
class f {
  method step(x: foo) returns (y: int) {
    match x with 
    | Foo (a, b) -> y := a + b; 
    | Bar a -> y := 2 * a;
  }
}
```

**Clight**
```c
struct foo_Foo {
  int Foo_0;
  int Foo_1;
};

struct foo_Bar { 
  int Bar_0;
};

union foo_u {
  struct foo_Foo Foo;
  struct foo_Bar Bar;
};

struct foo {
  int tag;
  union foo_u u;
};

int f_step(struct foo x) {
  int y;
  switch (x.tag) {
  case 0: 
    y = x.u.foo_Foo.Foo_0 + x.u.foo_Foo.Foo_1;
    break;
  case 1: 
    y = 2 * x.u.foo_Bar.Bar_0;
    break;
  }
}
```
A lot of generated composite types, a lot of indirections for field accesses. 
Moreover, should `x` be passed by copy or by reference? 
It seems that the correctness proof will be an actual challenge to be adapted...

For every language, it requires a way to model _binders_, which is not an easy
problem. 
The semantics and compilation would rely on substitutions that could complicate
the reasoning. 

### Simple Enums

Generalization of clocks: no binders.

**Lustre**
```ocaml
type foo = Foo | Bar
 
node f(u: int, x: foo) returns (y: int);
let
  y = merge x (Foo -> 42) (Bar -> u when Bar(x));
tel
```

**Obc**
```ocaml
type foo = Foo | Bar
 
class f {
  method step(u: int, x: foo) returns (y: int) {
    match x with 
    | Foo -> y := 42; 
    | Bar a -> y := u;
  }
}
```

**Clight**
```c
int f_step(int u, int x) {
  int y;
  switch (x) {
  case 0: 
    y = 42;
    break;
  case 1: 
    y = u;
    break;
  }
}
```
Absolutely no additional composite type generated. 
Compilation and correctness should be adapted without too much pain. 

_But_, it will not be easily generalized to the more general setup above.

The dataflow clock semantics is not clear. 
In particular, should we distinguish booleans?

## Records

