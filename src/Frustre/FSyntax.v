
From Coq Require PArith.BinPos.
Definition ident := Coq.PArith.BinPos.positive.
From Coq Require Import ZArith.
From Coq Require Import List.

From Velus Require Import ClockDefs.

(* Types *)

Inductive signedness : Type :=
| Signed: signedness
| Unsigned: signedness.

Inductive intsize : Type :=
| I8: intsize
| I16: intsize
| I32: intsize
| IBool: intsize.

Inductive floatsize : Type :=
| F32: floatsize
| F64: floatsize.

Inductive typ : Type :=
| Tint:   intsize -> signedness -> typ
| Tlong:  signedness -> typ
| Tfloat: floatsize -> typ.

Definition bool_typ : typ := Tint IBool Signed.

(* Constants *)

Inductive float :=
| F754_zero     : bool -> float
| F754_infinity : bool -> float
| F754_nan      : bool -> positive -> float
| F754_finite   : bool -> positive -> Z -> float.

Inductive const : Type :=
| Cint    : Z -> intsize -> signedness -> const
| Clong   : Z -> signedness -> const
| Cfloat  : float -> const
| Csingle : float -> const.

Definition ty_const (c : const) : typ :=
  match c with
  | Cint _ sz sg => Tint sz sg
  | Clong _ sg   => Tlong sg
  | Cfloat _     => Tfloat F64
  | Csingle _    => Tfloat F32
  end.

(* Operators *)

Inductive unop : Type :=
| Onotbool  : unop
| Onotint   : unop
| Oneg      : unop
| Ocast     : typ -> unop.

Inductive binop : Type :=
| Oadd : binop
| Osub : binop
| Omul : binop
| Odiv : binop
| Omod : binop
| Oand : binop
| Oor  : binop
| Oxor : binop
| Oshl : binop
| Oshr : binop
| Oeq  : binop
| One  : binop
| Olt  : binop
| Ogt  : binop
| Ole  : binop
| Oge  : binop.

(* Frustre *)

Definition ann : Type := (typ * nclock)%type.
Definition lann : Type := (list typ * nclock)%type.

Inductive exp : Type :=
| Econst : const -> exp
| Evar   : ident -> ann -> exp
| Eunop  : unop -> exp -> ann -> exp
| Ebinop : binop -> exp -> exp -> ann -> exp

| Efby   : list exp -> list exp -> list ann -> exp
| Earrow : list exp -> list exp -> list ann -> exp
(* | Epre   : list exp -> list ann -> exp *)
| Ewhen  : list exp -> ident -> bool -> lann -> exp
| Emerge : ident -> list exp -> list exp -> lann -> exp
| Eite   : exp -> list exp -> list exp -> lann -> exp

| Eapp   : ident -> list exp -> option exp -> list ann -> exp.

Definition equation : Type := (list ident * list exp)%type.

Record node : Type :=
  mk_node {
      n_name     : ident;
      n_hasstate : bool;
      n_in       : list (ident * (typ * clock));
      n_out      : list (ident * (typ * clock));
      n_vars     : list (ident * (typ * clock));
      n_eqs      : list equation
    }.

Definition global := list node.

