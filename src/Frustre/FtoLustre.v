From Velus Require Import Common.

From Velus Require Import ClockDefs.
From Velus Require Frustre.FSyntax.
From Velus Require Import Lustre.LSyntax.
From Velus Require Import ObcToClight.Interface.

Module F := FSyntax.
Module L := LSyntaxFun Ids Op.

Definition tr_signedness (sg : F.signedness) : Ctypes.signedness :=
  match sg with
  | F.Signed   => Ctypes.Signed
  | F.Unsigned => Ctypes.Unsigned
  end.

Definition tr_intsize (sz : F.intsize) : Ctypes.intsize :=
  match sz with
  | F.I8    => Ctypes.I8
  | F.I16   => Ctypes.I16
  | F.I32   => Ctypes.I32
  | F.IBool => Ctypes.IBool
  end.

Definition tr_floatsize (s : F.floatsize) : Ctypes.floatsize :=
  match s with
  | F.F32 => Ctypes.F32
  | F.F64 => Ctypes.F64
  end.

Definition tr_type (ty : F.typ) : Op.type :=
  match ty with
  | F.Tint sz sg => Op.Tint (tr_intsize sz) (tr_signedness sg)
  | F.Tlong sg   => Op.Tlong (tr_signedness sg)
  | F.Tfloat s   => Op.Tfloat (tr_floatsize s)
  end.

Definition to_fullfloat (f : F.float) : Fappli_IEEE.full_float :=
  match f with
  | F.F754_zero s       => Fappli_IEEE.F754_zero s
  | F.F754_infinity s   => Fappli_IEEE.F754_infinity s
  | F.F754_nan b pl     => Fappli_IEEE.F754_nan b pl
  | F.F754_finite s m e => Fappli_IEEE.F754_finite s m e
  end.

Definition tr_float (f : F.float) : Floats.float.
  apply to_fullfloat in f.
  assert (Fappli_IEEE.valid_binary 53 1024 f = true) as Hok.
  admit. (* TODO: need to check if floats are in range *)
  apply (Fappli_IEEE.FF2B _ _ f Hok).
Defined.

Definition tr_float32 (f : F.float) : Floats.float32.
  apply to_fullfloat in f.
  assert (Fappli_IEEE.valid_binary 24 128 f = true) as Hok.
  admit. (* TODO: need to check if floats are in range *)
  apply (Fappli_IEEE.FF2B _ _ f Hok).
Defined.

Definition tr_constant (c : F.const) : Op.constant :=
  match c with
  | F.Cint v sz sg => Op.Cint (Integers.Int.repr v)
                              (tr_intsize sz) (tr_signedness sg)
  | F.Clong v sg   => Op.Clong (Integers.Int64.repr v)
                               (tr_signedness sg)
  | F.Cfloat f     => Op.Cfloat (tr_float f)
  | F.Csingle f    => Op.Csingle (tr_float32 f)
  end.

Definition tr_unop (op : F.unop) : Op.unop :=
  match op with
  | F.Onotbool => Op.UnaryOp Cop.Onotbool
  | F.Onotint  => Op.UnaryOp Cop.Onotint
  | F.Oneg     => Op.UnaryOp Cop.Oneg
  | F.Ocast ty => Op.CastOp (tr_type ty)
  end.

Definition tr_binop (op : F.binop) : Op.binop :=
  match op with
  | F.Oadd => Cop.Oadd
  | F.Osub => Cop.Osub
  | F.Omul => Cop.Omul
  | F.Odiv => Cop.Odiv
  | F.Omod => Cop.Omod
  | F.Oand => Cop.Oand
  | F.Oor  => Cop.Oor
  | F.Oxor => Cop.Oxor
  | F.Oshl => Cop.Oshl
  | F.Oshr => Cop.Oshr
  | F.Oeq  => Cop.Oeq
  | F.One  => Cop.One
  | F.Olt  => Cop.Olt
  | F.Ogt  => Cop.Ogt
  | F.Ole  => Cop.Ole
  | F.Oge  => Cop.Oge
  end.

Definition tr_ann (a : F.ann) : L.ann :=
  match a with
  | (ty, ck) => (tr_type ty, ck)
  end.

Definition tr_lann (a : F.lann) : L.lann :=
  match a with
  | (tys, ck) => (List.map tr_type tys, ck)
  end.

Fixpoint tr_exp (e : F.exp) : L.exp :=
  match e with
  | F.Econst c => L.Econst (tr_constant c)
  | F.Evar x a => L.Evar x (tr_ann a)
  | F.Eunop op e a => L.Eunop (tr_unop op) (tr_exp e) (tr_ann a)
  | F.Ebinop op e1 e2 a => L.Ebinop (tr_binop op) (tr_exp e1) (tr_exp e2)
                                    (tr_ann a)

  | F.Efby e0s es aa => L.Efby (List.map tr_exp e0s) (List.map tr_exp es)
                               (List.map tr_ann aa)
  | F.Ewhen es x b a => L.Ewhen (List.map tr_exp es) x b (tr_lann a)
  | F.Emerge x ets efs a => L.Emerge x (List.map tr_exp ets)
                                       (List.map tr_exp efs) (tr_lann a)
  | F.Eite e ets efs a => L.Eite (tr_exp e) (List.map tr_exp ets)
                                            (List.map tr_exp efs) (tr_lann a)
  | F.Eapp f es aa => L.Eapp f (List.map tr_exp es) (List.map tr_ann aa)
  end.

Definition tr_equation (eq : F.equation) : L.equation :=
  match eq with
  | (xs, es) => (xs, List.map tr_exp es)
  end.

Definition tr_decl (xtc : F.ident * (F.typ * F.clock)) : (ident * (Op.type * clock)) :=
  match xtc with
  | (x, (ty, ck)) => (x, (tr_type ty, ck))
  end.

Definition tr_node (n : F.node) : L.node.
  refine ({| L.n_name := n.(F.n_name);
             L.n_hasstate := n.(F.n_hasstate);
             L.n_in := List.map tr_decl n.(F.n_in);
             L.n_out := List.map tr_decl n.(F.n_out);
             L.n_vars := List.map tr_decl n.(F.n_vars);
             L.n_eqs := List.map tr_equation n.(F.n_eqs);
             L.n_ingt0 := _;
             L.n_outgt0 := _;
             L.n_defd := _;
             L.n_nodup := _;
             L.n_good := _
          |}).
  admit (* TODO: Check that there is at least one input. *).
  admit (* TODO: Check that there is at least one output. *).
  admit (* TODO: Check declarations against definitions. *).
  admit (* TODO: Check for duplicate declarations. *).
  admit (* TODO: Check for reserved words. *).
Defined.

Definition tr_global (p : F.global) : L.global :=
  List.map tr_node p.

(* TODO: Add decision procedures and lemmas for well_typed. *)
(* TODO: Add decision procedures and lemmas for well_clocked. *)


