From Coq Require Import BinPos BinNat Extraction List.
Import ListNotations.

From Coq Require Import ExtrOcamlBasic.
From Coq Require Import ExtrOcamlString.

From Cpo Require Import Cpo_def Cpo_streams_type Systems.
Require Import Cpo_ext SDfuns Denot.

(* Discard useless function arguments in extracted OCaml code *)
Extraction Implicit fcontit [1 2].
Extraction Implicit Fcontit [1 2].
Extraction Implicit fcont_lub [1].
Extraction Implicit fcont_cpo [1].
Extraction Implicit fmon_comp [1 2 3].
Extraction Implicit fcont_comp [1 2 3].
Extraction Implicit le_compat2_mon [1 2 3].
Extraction Implicit mseq_lift_left [1].
Extraction Implicit Dmapi [1 2 3].
Extraction Implicit DMAPi [1 2 3].
Extraction Implicit fmon_cte [1 2].
Extraction Implicit ford_fcont_shift [1 2 3].
Extraction Implicit fcont_Comp [1 2 3].
Extraction Implicit continuous2_cont_app [1 2 3].
Extraction Implicit continuous2_cont [1 2 3].
Extraction Implicit fcont_COMP [1 2 3].
Extraction Implicit ford_app [1 2 3].
Extraction Implicit ford_shift [1 2 3].
Extraction Implicit fmon_app [1 2 3].
Extraction Implicit fmon_shift [1 2 3].
Extraction Implicit fmon_comp2 [1 2 3 4].
Extraction Implicit lub_fun [1].
Extraction Implicit mon0 [1].
Extraction Implicit fmon_cpo [1].
Extraction Implicit fcont_ord [1 2].
Extraction Implicit fcont0 [1].
Extraction Implicit fcontit [1 2].
Extraction Implicit fcont2_COMP [1 2 3 4].
Extraction Implicit fcont2_comp [1 2 3 4].
Extraction Implicit fcont_comp2 [1 2 3 4].
Extraction Implicit fcont_comp3 [1 2 3 4 5].
Extraction Implicit fcont_comp4 [1 2 3 4 5 6].
Extraction Implicit fconti [1 2].
Extraction Implicit fconti_fun [1 2].
Extraction Implicit fmon [1 2].
Extraction Implicit Id [1].
Extraction Implicit ID [1].
Extraction Implicit AP [1 2].
Extraction Implicit Oprod [1 2].
Extraction Implicit Fst [1 2].
Extraction Implicit Snd [1 2].
Extraction Implicit FST [1 2].
Extraction Implicit SND [1 2].
Extraction Implicit Pairr [1 2].
Extraction Implicit Pair [1 2].
Extraction Implicit PAIR [1 2].
Extraction Implicit curry [1 2 3].
Extraction Implicit uncurry [1 2 3].
Extraction Implicit remf [1 2].
Extraction Implicit Oprodi [1 2].
Extraction Implicit Proj [1 2].
Extraction Implicit PROJ [1 2].
Extraction Implicit DS_fam [1 2].
Extraction Implicit fcont_sub [1 2 3 4].
Extraction Implicit CTE [1 2].
(* Extraction Implicit assoc_ident_cons_or [4 5]. *)

Extraction Inline fconti_fun.
Extraction Inline fmon.
Extraction Inline fcontit.
Extraction Inline fcont_ord.
Extraction Inline Fcontit.
Extraction Inline fmonot.
Extraction Inline continuous2_cont continuous2_cont_app.
Extraction Inline fmon_comp fcont_comp.
Extraction Inline fmon_comp2 fcont_comp2.
Extraction Inline cons Cons CONS.

(* Datatypes *)
Extract Inlined Constant Datatypes.fst => "fst".
Extract Inlined Constant Datatypes.snd => "snd".

(* Très ad hoc, en attendant la résolution : *)
(* https://github.com/coq/coq/issues/15713 *)
Extract Constant DS_bot => "let rec _bot = Eps (lazy (_bot)) in Obj.magic _bot".

(** OCaml printing functions *)
(* TODO: foutre tout ça dans un fichier ml, comme Camlcoq ? *)
Parameter print_Z_list : list (option Z) -> unit.
Extract Constant print_Z_list =>
"fun l -> Stdlib.List.iter (fun x ->
      match x with
      | None -> print_string ""- ""
      | Some x -> Printf.printf ""%d "" (Camlcoq.Z.to_int x)
    ) l;
  print_newline()".

Parameter print_sampl_Z_list : list (option (sampl Z)) -> unit.
Extract Constant print_sampl_Z_list =>
"fun l -> Stdlib.List.iter (fun x ->
      match x with
      | None -> print_string ""- ""
      | Some Coq_absent -> Printf.printf ""‹› ""
      | Some (Coq_present x) -> Printf.printf ""%d "" (Camlcoq.Z.to_int x)
    ) l;
  print_newline()".

(* Idée d'amélioration : utiliser l'outil de mémoïsation proposé par la
   bibliothèque Fix. En pratique sur les nœuds on perd en performance,
   je ne comprends pas exactement pourquoi. *)
(*
Extract Constant iter =>
"fun d f ->
  let module NAT = struct type t = Datatypes.nat end in
  let module M = Fix.Memoize.ForType(NAT) in
  Obj.magic M.fix (fun iter2 n ->
      match n with
      | O -> d.coq_D0
      | S n -> Obj.magic f (iter2 n)
    )".
*)



From Velus Require Import Common.
From compcert Require Import Ctypes.

From Velus Require Import Instantiator.
From Velus Require Import Lustre.Denot.Denot.

(* ****** copié de extraction/Extraction.v *)
Extraction Blacklist Int String List.
Extract Constant Ident.str_to_pos => "(fun str -> Camlcoq.(str |> camlstring_of_coqstring |> intern_string))".
Extract Constant Ident.pos_to_str => "(fun pos -> Camlcoq.(pos |> extern_atom |> coqstring_of_camlstring))".
Extract Constant Ident.Ids.prefix => "Veluscommon.prefix".
Extract Constant Ident.Ids.gensym => "Veluscommon.gensym".
(* **************************************** *)

Module Denot := LDenotFun Ident.Ids Interface.Op Interface.OpAux Interface.Cks L.Senv L.Syn L.Ord Interface.CStr.

Import L.Syn Interface.Op Interface.Cks.


(* TODO: copier ça au début du fichier Extraction.v *)
(*
open Values
open Format
open Camlcoq
let print_typed_value p v ty =
  match v, ty with
  | Vint n, Ctypes.Tint(I32, Unsigned, _) ->
      fprintf p "%luU" (camlint_of_coqint n)
  | Vint n, _ ->
      fprintf p "%ld" (camlint_of_coqint n)
  | Vfloat f, _ ->
      fprintf p "%.15F" (camlfloat_of_coqfloat f)
  | Vsingle f, _ ->
      fprintf p "%.15Ff" (camlfloat_of_coqfloat32 f)
  | Vlong n, Ctypes.Tlong(Unsigned, _) ->
      fprintf p "%LuLLU" (camlint64_of_coqint n)
  | Vlong n, _ ->
      fprintf p "%LdLL" (camlint64_of_coqint n)
  | Vundef, _ ->
      fprintf p "<undef>"
let print_value p v = print_typed_value p v Tvoid
 *)

Parameter print_sampl_list : list (option (sampl value)) -> unit.
Extract Constant print_sampl_list =>
"fun l -> Stdlib.List.iter (fun x ->
      match x with
      | None -> print_string ""- ""
      | Some Coq_abs -> Printf.printf ""‹› ""
      | Some (Coq_pres (Interface.Op.Vscalar x)) -> Printf.printf ""%s "" (print_value Format.str_formatter x; Format.flush_str_formatter ())
      | Some (Coq_err Coq_error_Ty) -> Printf.printf ""TY ""
      | Some (Coq_err Coq_error_Cl) -> Printf.printf ""CL ""
      | Some (Coq_err Coq_error_Op) -> Printf.printf ""OP ""
    ) l;
  print_newline()".


(* Variables defined in the program *)
(* Definition _a : ident := 15%positive. *)
(* Definition _b : ident := 16%positive. *)
(* Definition _c : ident := 17%positive. *)
(* Definition _counter : ident := 12%positive. *)
Definition _i : ident := 13%positive.
Definition _p : ident := 14%positive.
Definition _q : ident := 15%positive.

(* Definition of node [counter] *)
Definition tbool : type := Tprimitive (Tint IBool Unsigned).

Definition ins : list (ident * (type * clock)) :=
  [(_i, (tbool, Cbase))].
Definition outs : list (ident * (type * clock)) :=
  [(_p, (tbool, Cbase));(_q, (tbool, Cbase))].
Definition vars : list (ident * (type * clock)) :=
  [].

(* 0 fby not p *)
Definition zfbynotp : exp :=
  Efby [Econst (Cint Integers.Int.zero IBool Unsigned)]
    [Eunop (UnaryOp Cop.Onotbool) (Evar _p (tbool,Cbase)) (tbool, Cbase)]
    [(tbool,Cbase)].

Definition eq1 : equation :=
  ([_p], [ zfbynotp]).

Import Cpo_def.
(* Definition res0 := (Denot.denot_exp (ins++outs++vars) zfbynotp 0 bk). *)
(* Definition res0 := sfby (DS_const ( (Vscalar (Integers.Int.zero IBool Unsigned))) 0. *)
(* Definition res0 := sfby (DS_const (pres (Vscalar (Values.Vint Integers.Int.zero)))) 0. *)


(* Definition output_stream0 := print_sampl_list (take_list 10 res0). *)

(* Definition bk : DS bool := DS_const true. *)

(* Definition res0 := (Denot.denot_equation (ins++outs++vars) eq1 0 bk). *)
(* Definition res1 := (Denot.denot_equation (ins++outs++vars) eq1 res0 bk). *)
(* Definition res2 := (Denot.denot_equation (ins++outs++vars) eq1 res1 bk). *)
(* Definition res3 := (Denot.denot_equation (ins++outs++vars) eq1 res2 bk). *)
(* Definition test_stream0 := res0 _p. *)
(* Definition test_stream1 := res1 _p. *)
(* Definition test_stream2 := res2 _p. *)
(* Definition test_stream3 := res3 _p. *)

(* Definition output_stream0 := print_sampl_list (take_list 10 test_stream0). *)
(* Definition output_stream1 := print_sampl_list (take_list 10 test_stream1). *)
(* Definition output_stream2 := print_sampl_list (take_list 10 test_stream2). *)
(* Definition output_stream3 := print_sampl_list (take_list 10 test_stream3). *)


Definition bk : DS bool := DS_const true.
Definition res := FIXP _ (Denot.denot_equation eq1 <___> bk).
Definition test_stream := res _p.
Definition output_stream := print_sampl_list (take_list 20 test_stream).


Require Import Infty.
Import Denot.

Module TEST1.
  (* Equation simple sans fby  *)

Definition all_infinite vars (env : DS_prod SI) : Prop :=
  forall i, In i vars -> infinite (PROJ _ i env).

Definition _q : ident := 15%positive.
(* not 0 *)
Definition not0 : exp :=
  Eunop (UnaryOp Cop.Onotbool) (Econst (Cint Integers.Int.zero IBool Unsigned)) (tbool,Cbase).
(* 1 *)
Definition e1 : exp :=
  Econst (Cint Integers.Int.one IBool Unsigned).
(* not p *)
Definition notp : exp :=
  Eunop (UnaryOp Cop.Onotbool) (Evar _p (tbool,Cbase)) (tbool, Cbase).

Definition eq2 : equation :=
  ([_q], [ not0]).
Definition eq3 : equation :=
  ([_p;_q], [e1; notp]).

Lemma test_infinite1 :
  forall bs,
    infinite bs ->
    let env := FIXP _ (denot_equation eq3 <___> bs) in
    all_infinite (fst eq3) env.
Proof.
  (* TODO: move after denot_equation_eq *)
  Opaque denot_equation.
  intros ??.
  unfold eq3; simpl.
  intros i Hin.
  assert (infinite (PROJ (DS_fam SI) _p (FIXP (DS_prod SI) (denot_equation ([_p; _q], [e1; notp]) <___> bs)))) as Hp.
  {
    rewrite FIXP_eq.
    rewrite fcont_app2_simpl, PROJ_simpl.
    rewrite denot_equation_eq.
    simpl.
    rewrite (denot_exps_eq e1 [notp]).
    autorewrite with cpodb using simpl.
    now apply infinite_map.
  }
  assert (infinite (PROJ (DS_fam SI) _q (FIXP (DS_prod SI) (denot_equation ([_p; _q], [e1; notp]) <___> bs)))) as Hq.
  {
    rewrite FIXP_eq.
    rewrite fcont_app2_simpl, PROJ_simpl.
    rewrite denot_equation_eq; simpl.
    rewrite ID_simpl, Id_simpl.
    remember ((FIXP (DS_prod SI) (denot_equation ([_p; _q], [e1; notp]) <___> bs))) as env.
    (* TODO: problème de reflexivité dans les arguments *)
    rewrite (denot_exps_eq e1 [notp] env bs); simpl.
    rewrite SND_PAIR_simpl.
    rewrite (denot_exps_eq notp [] env bs), CTE_eq.
    rewrite denot_exp_eq; simpl.
    setoid_rewrite (denot_exp_eq (Evar _p (tbool, Cbase)) env bs).
    now apply infinite_map.
  }
  inversion Hin as [|[|[]]]; subst; auto.
Qed.

End TEST1.


Module TEST2.
  (* équation avec [fby] utilisant les propriétés de producivité *)

  Definition _p : ident := 9%positive.
  Definition _q : ident := 15%positive.

  (* 0 fby not p *)
  Definition zfbynotp : exp :=
    Efby [Econst (Cint Integers.Int.zero IBool Unsigned)]
      [Eunop (UnaryOp Cop.Onotbool) (Evar _p (tbool,Cbase)) (tbool, Cbase)]
      [(tbool,Cbase)].

  Definition eq1 : equation :=
    ([_p;_q], [Evar _q (tbool,Cbase); zfbynotp]).

  (* TODO: move *)
  (* TODO: le P est utile mais un peu artificiel... *)
  Lemma nrem_inf_gen :
    forall {A} I (P : I -> Prop) (H : I -> DS A),
      (forall n i, P i -> is_cons (nrem n (H i))) ->
      forall i, P i -> infinite (H i).
  Proof.
    intros A I P.
    cofix Cof.
    intros H Hc i Pi.
    constructor.
    - apply (Hc O i Pi).
    - apply Cof with (H := fun i => rem (H i)); auto.
      intros n j.
      apply (Hc (S n) j).
  Qed.

  (* TODO: move *)
  Lemma inf_nrem :
    forall  {A} (s : DS A), infinite s -> forall n, is_cons (nrem n s).
  Proof.
    intros * Hf n.
    revert dependent s.
    induction n; intros; inv Hf; simpl; auto.
  Qed.

  Definition all_infinite (vars : list ident) (env : DS_prod SI) : Prop :=
    forall i, In i vars -> infinite (env i).

  Lemma test_infinite2 :
  forall bs,
    infinite bs ->
    let env := FIXP _ (denot_equation eq1 <___> bs) in
    all_infinite (fst eq1) env.
  Proof.
  Opaque denot_equation denot_exp.
  intros bs bsi.
  unfold eq1; simpl.

  (* TODO: tout ça pour appliquer [nrem_inf_gen], c'est moyen *)
  unfold all_infinite.
  apply nrem_inf_gen
    with (H := FIXP (DS_prod SI) (denot_equation ([_p; _q], [Evar _q (tbool, Cbase); zfbynotp]) <___> bs)).

  induction n; simpl; intros.
  - (* instant 0 *)
    assert (is_cons (FIXP (DS_prod SI) (denot_equation ([_p; _q], [Evar _q (tbool, Cbase); zfbynotp]) <___> bs) _q)) as Hq.
    { (* _q *)
    rewrite <- PROJ_simpl, FIXP_eq, PROJ_simpl.
    rewrite fcont_app2_simpl, denot_equation_eq; simpl.
    rewrite (denot_exps_eq (Evar _q (tbool, Cbase)) [zfbynotp]). (* pourquoi ?? *)
    autorewrite with cpodb using simpl.
    rewrite (denot_exps_eq zfbynotp []), denot_exp_eq.
    simpl. unfold eq_rect_r, eq_rect.
    autorewrite with cpodb using simpl.
    apply is_cons_fby.
    rewrite (denot_exps_eq (Econst (Cint Integers.Int.zero IBool Unsigned)) []), denot_exp_eq.
    autorewrite with cpodb using simpl.
    apply is_cons_map. now inv bsi.
    }
    destruct (ident_eq_dec i _q) as [|Hnq]; subst; auto.
    assert (is_cons (FIXP (DS_prod SI) (denot_equation ([_p; _q], [Evar _q (tbool, Cbase); zfbynotp]) <___> bs) _p)) as Hp.
    { (* _p *)
    rewrite <- PROJ_simpl, FIXP_eq, PROJ_simpl.
    rewrite fcont_app2_simpl, denot_equation_eq; simpl.
    rewrite (denot_exps_eq (Evar _q (tbool, Cbase)) [zfbynotp]), denot_exp_eq.
    autorewrite with cpodb using simpl; auto.
    }
    destruct (ident_eq_dec i _p) as [|Hnp]; subst; auto.
    { (* others *)
      exfalso. clear Hp Hq. firstorder.
    }
  - (* instant (S n) *)
    assert (is_cons
              (nrem n (rem (FIXP (DS_prod SI) (denot_equation ([_p; _q], [Evar _q (tbool, Cbase); zfbynotp]) <___> bs) _q)))) as Hq.
    { (* _q *)
    rewrite <- PROJ_simpl, FIXP_eq, PROJ_simpl.
    rewrite fcont_app2_simpl, denot_equation_eq; simpl.
    rewrite (denot_exps_eq (Evar _q (tbool, Cbase)) [zfbynotp]). (* pourquoi ?? *)
    autorewrite with cpodb using simpl.
    rewrite (denot_exps_eq zfbynotp []), denot_exp_eq.
    simpl. unfold eq_rect_r, eq_rect.
    autorewrite with cpodb using simpl.
    apply is_consn_S_fby.
    + rewrite (denot_exps_eq (Econst (Cint Integers.Int.zero IBool Unsigned)) []), denot_exp_eq.
      autorewrite with cpodb using simpl.
      apply is_consn_sconst with (n := (S n)); auto using inf_nrem.
    + rewrite (denot_exps_eq (Eunop (UnaryOp Cop.Onotbool) (Evar _p (tbool, Cbase)) (tbool, Cbase)) []), 2 denot_exp_eq.
      autorewrite with cpodb using simpl.
      apply is_consn_sunop.
      apply IHn; simpl; auto.
    }
    destruct (ident_eq_dec i _q) as [|Hnq]; subst; auto.
    assert (is_cons
              (nrem n (rem (FIXP (DS_prod SI) (denot_equation ([_p; _q], [Evar _q (tbool, Cbase); zfbynotp]) <___> bs) _p)))) as Hp.
    { (* _p *)
    rewrite <- PROJ_simpl, FIXP_eq, PROJ_simpl.
    rewrite fcont_app2_simpl, denot_equation_eq; simpl.
    rewrite (denot_exps_eq (Evar _q (tbool, Cbase)) [zfbynotp]), denot_exp_eq.
    autorewrite with cpodb using simpl; auto.
    }
    destruct (ident_eq_dec i _p) as [|Hnp]; subst; auto.
    { (* others *)
      exfalso. clear IHn Hp Hq. firstorder.
    }
  Qed.

(* Definition bk : DS bool := DS_const true. *)
(* Definition res := FIXP _ (Denot.denot_equation eq3 <___> bk). *)
(* Definition test_stream := res _q. *)
(* Definition output_stream := print_sampl_list (take_list 20 test_stream). *)

End TEST2.

(* Require Import LCausality. *)
(* Module Import Caus := LCausalityFun Ident.Ids Interface.Op Interface.OpAux Interface.Cks L.Senv L.Syn. *)

(* Check causal_ind. *)

(* (** on le retrouve dans  [extration-denot/Extraction.ml]  *) *)
Cd "extraction-denot".
Separate Extraction
         ZArith.BinIntDef
	 Floats.Float.of_bits Floats.Float.to_bits
	 Floats.Float32.of_bits Floats.Float32.to_bits
	 Floats.Float32.from_parsed Floats.Float.from_parsed
	 FMapPositive.PositiveMap.add FMapPositive.PositiveMap.empty
	 FMapPositive.PositiveMap.find
         output_stream
         (* TEST_infty.output_stream *)
         (* output_stream0 *)
         (* output_stream1 *)
         (* output_stream2 *)
         (* output_stream3 *)
.
Cd "..".

(* à compiler avec [ocamlbuild -use-ocamlfind -pkgs fix,str Extraction.native] *)


(* (** Petits exemples à extraire *) *)

(* Module Ex_1. *)

(* Definition six : DStr Z := const (Zpos 6). *)
(* Definition test_stream := FIXP _ (ite (const false) six *)
(*                                       @_ (fby six @_ (binop BinInt.Z.add (const (Zpos 1))))). *)
(* Definition output_stream := print_Z_list (take_list 48 test_stream). *)

(* End Ex_1. *)


(* Module Ex_const. *)

(* Definition _x := 2%positive. *)
(* Definition _y := 3%positive. *)
(* Definition _z := 4%positive. *)
(* Parameter MY_AXIOM : forall {A} (l : list (ident * A)), NoDupMembers l. *)
(* Definition df : decls := *)
(*   {| d_ins  := ncons _ (_x,lInt) (nsing _ (_y,lBool)); *)
(*      d_outs := nsing _ (_z, lInt); *)
(*      d_ins_nodup := MY_AXIOM _; *)
(*      d_outs_nodup := MY_AXIOM _; *)
(*   |}. *)
(* Definition gd : gdecls := *)
(*   fun f => match f with *)
(*         | 5%positive => Some df *)
(*         | _ => None *)
(*         end. *)

(* (* z = 47 *) *)
(* Definition eqf1 : @equation gd df (Lsingl lInt) := *)
(*   (@vars1 df _ _z eq_refl, (Econst _ (Cint (Zpos 47)))). *)
(* Definition nf : @node gd df := [ existT _ _ eqf1 ]. *)
(* Definition prog : global gd := *)
(*   fun i : ident => match i with *)
(*                 | 5%positive => nf *)
(*                 | _ => tt *)
(*                 end. *)

(* CoFixpoint DS_const_alt {A} (a : A) : DS (sampl A) := Con absent (Con (present a) (DS_const_alt a)). *)
(* Definition six : DStr (sampl Z) := DS_const_alt (Zpos 6). *)
(* Definition strue : DStr (sampl bool) := (* Con (present true) *) (DS_const_alt true). *)
(* Definition test_stream := SemSD.denot_global _ prog 5%positive (six,strue). *)
(* (* devrait être toujours présent... *) *)
(* Definition output_stream := print_sampl_Z_list (take_list 20 test_stream). *)

(* End Ex_const. *)

(* Module Ex_collines. *)

(* Definition _r := 2%positive. *)
(* Definition _n := 3%positive. *)
(* Definition _up := 4%positive. *)
(* Parameter MY_AXIOM : forall {A} (l : list (ident * A)), NoDupMembers l. *)
(* Definition df : decls := *)
(*   {| d_ins  := nsing _ (_r,lBool); *)
(*      d_outs := ncons _ (_n,lInt) (nsing _ (_up,lBool)); *)
(*      d_ins_nodup := MY_AXIOM _; *)
(*      d_outs_nodup := MY_AXIOM _; *)
(*   |}. *)
(* Definition gd : gdecls := *)
(*   fun f => match f with *)
(*         | 5%positive => Some df *)
(*         | _ => None *)
(*         end. *)


(* (* up = true fby ((up and n < 9) or (not up and n <= 1)); *) *)
(* Definition eqf1 : @equation gd df (Lsingl lBool) := *)
(*   (@vars1 df _ _up eq_refl, *)
(*     (Efby _ (Econst _ (Cbool true)) *)
(*           (Ebinop _ _ _ bOr *)
(*                   (Ebinop _ _ _ bAnd (@Evar _ df _ _up (right eq_refl)) *)
(*                           (Ebinop _ _ _ bLtI (@Evar _ df _ _n (right eq_refl)) (Econst _ (Cint (Zpos 3))))) *)
(*                   (Ebinop _ _ _ bAnd (Eunop _ _ uNot (@Evar _ df _ _up (right eq_refl))) *)
(*                           (Ebinop _ _ _ bLtI (@Evar _ df _ _n (right eq_refl)) (Econst _ (Cint (Zpos 2)))))))). *)

(* (* n = 0 fby (if up then n + 1 else n - 1); *) *)
(* Definition eqf2 : @equation gd df (Lsingl lInt) := *)
(*   (@vars1 df _ _n eq_refl, *)
(*     (Efby _ (Econst _ (Cint Z0)) *)
(*           (Eite _ (@Evar _ df _ _up (right eq_refl)) *)
(*                 (Ebinop _ _ _ bAddI (@Evar _ df _ _n (right eq_refl)) (Econst _ (Cint (Zpos 1)))) *)
(*                 (Ebinop _ _ _ bSubI (@Evar _ df _ _n (right eq_refl)) (Econst _ (Cint (Zpos 1)))) *)
(*     ))). *)

(* Definition nf : @node gd df := [ existT _ _ eqf1; existT _ _ eqf2 ]. *)
(* Definition prog : global gd := *)
(*   fun i : ident => match i with *)
(*                 | 5%positive => nf *)
(*                 | _ => tt *)
(*                 end. *)

(* Definition sfalse := DS_const false. *)
(* Definition test_stream := SemK.denot_global _ prog 5%positive sfalse. *)
(* (* devrait être toujours présent... *) *)
(* Definition output_stream := print_Z_list (take_list 7 (fst test_stream)). *)

(* End Ex_collines. *)

(* (** on le retrouve dans  [extration/Extraction.ml]  *) *)
(* Cd "extraction". *)
(* Separate Extraction BinPos BinInt BinNat Ex_collines.output_stream. *)
(* (* à compiler avec [ocamlbuild -use-ocamlfind -pkgs fix Extraction.native] *) *)
