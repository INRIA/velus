Require Import Coq.FSets.FMapPositive.
Require Import PArith.
Require Import Rustre.Nelist.
Require Import Rustre.Common.
Require Import Rustre.Minimp.Syntax.
Require Import Rustre.Dataflow.Syntax.
Require Import Rustre.Dataflow.Memories.

Import List.ListNotations.
Open Scope positive.
Open Scope list.
Require Import Nelist.


(** * Translation *)

(** ** Identification of node instances *)

(** 

Each node application in CoreDF turns into a method call in the
imperative setting. This means that, upon initializing a node, one
must declare a new instance for each its application.

Remark: it is necessary to distinguish different instantiations of the
same node (i.e., different objects of the same class). This is done in
Auger's thesis in the language LSNI, where node applications are
assigned unique identifiers. His context is richer, in particular,
because the result of a node application may be assigned to a
pattern-tuple containing multiple identifiers.

Here, we take advantage of the fact that the result of a node
application is assigned to a single variable. We use the name of that
variable to identify the instance.  *)

Module Type TRANSLATION
       (Import Op: OPERATORS)
       (Import SynDF : Rustre.Dataflow.Syntax.SYNTAX Op)
       (Import SynMP : Rustre.Minimp.Syntax.SYNTAX Op).

  Definition gather_eq (acc: list (ident * typ) * list obj_dec) (eq: equation) :=
    match eq with
    | EqDef _ _ _ => acc
    | EqApp x _ f _ => (fst acc, mk_obj_dec x f :: snd acc)
    | EqFby x _ _ le => ((x, SynDF.typeof le)::fst acc, snd acc)
    end.

  Definition gather_eqs (eqs: list equation) : (list (ident * typ) * list obj_dec) :=
    List.fold_left gather_eq eqs ([], []).

  (** ** Translation *)

  Section Translate.

    Variable memories : PS.t.

    (* =tovar= *)
    Definition tovar (xt: ident * typ) : exp :=
      let (x, ty) := xt in
      if PS.mem x memories then State x ty else Var x ty.
    (* =end= *)

    (* =control= *)
    Fixpoint Control (ck: clock) (s: stmt) : stmt :=
      match ck with
      | Cbase => s
      | Con ck x ty true  => Control ck (Ifte (tovar (x, ty)) s Skip)
      | Con ck x ty false => Control ck (Ifte (tovar (x, ty)) Skip s)
      end.
    (* =end= *)

    (* =translate_lexp= *)
    Fixpoint translate_lexp (e : lexp) : exp :=
      match e with
      | Econst c ty => Const c ty
      | Evar x ty => tovar (x, ty)
      | Ewhen e c x => translate_lexp e
                                     (* | Eop op es => Op op (Nelist.map translate_lexp es) *)
      | Eunop op e ty => Unop op (translate_lexp e) ty
      | Ebinop op e1 e2 ty => Binop op (translate_lexp e1) (translate_lexp e2) ty
      end.
    (* =end= *)

    (* =translate_cexp= *)
    Fixpoint translate_cexp (x: ident) (e: cexp) : stmt :=
      match e with
      | Emerge y ty t f => Ifte (tovar (y, ty)) (translate_cexp x t) (translate_cexp x f)
      | Eexp l => Assign x (translate_lexp l)
      end.
    (* =end= *)

    (* =translate_eqn= *)
    Definition translate_eqn (eqn: equation) : stmt :=
      match eqn with
      | EqDef x ck ce => Control ck (translate_cexp x ce)
      | EqApp x ck f les => Control ck (Step_ap x f x (map translate_lexp les))
      | EqFby x ck v le => Control ck (AssignSt x (translate_lexp le))
      end.
    (* =end= *)

    (** Remark: eqns ordered in reverse order of execution for coherence with
       [Is_well_sch]. *)

    (* =translate_eqns= *)
    Definition translate_eqns (eqns: list equation) : stmt :=
      List.fold_left (fun i eq => Comp (translate_eqn eq) i) eqns Skip.
    (* =end= *)

  End Translate.

  (* =translate_reset_eqn= *)
  Definition translate_reset_eqn (s: stmt) (eqn: equation) : stmt :=
    match eqn with
    | EqDef _ _ _ => s
    | EqFby x _ v0 _ => Comp (AssignSt x (Const v0 (typ_of_val v0))) s
    | EqApp x _ f _ => Comp (Reset_ap f x) s
    end.
  (* =end= *)

  (* =translate_reset_eqns= *)
  Definition translate_reset_eqns (eqns: list equation): stmt :=
    List.fold_left translate_reset_eqn eqns Skip.
  (* =end= *)

  Definition ps_from_list (l: list ident) : PS.t :=
    List.fold_left (fun s i=>PS.add i s) l PS.empty.

  (* =translate_node= *)
  Definition translate_node (n: node): class :=
    let names := gather_eqs n.(n_eqs) in
    let mems := ps_from_list (List.map (@fst ident typ) (fst names)) in
    mk_class n.(n_name)
             n.(n_input)
             n.(n_output)
             (fst names)
             (snd names)
             (translate_eqns mems n.(n_eqs))
             (translate_reset_eqns n.(n_eqs)).
  (* =end= *)

  (* =translate= *)
  Definition translate (G: global) : program :=
    List.map translate_node G.
  (* =end= *)


  (** ** Properties *)


  Axiom ps_from_list_pre_spec:
    forall x l S, (List.In x l \/ PS.In x S)
             <->
             PS.In x (List.fold_left (fun s i=>PS.add i s) l S).
  
  Axiom ps_from_list_spec:
    forall x l, List.In x l <-> PS.In x (ps_from_list l).

End TRANSLATION.

Module TranslationFun' (Import Op: OPERATORS)
       (Import SynDF : Rustre.Dataflow.Syntax.SYNTAX Op)
       (Import SynMP : Rustre.Minimp.Syntax.SYNTAX Op).

  Definition gather_eq (acc: list (ident * typ) * list obj_dec) (eq: equation) :=
    match eq with
    | EqDef _ _ _ => acc
    | EqApp x _ f _ => (fst acc, mk_obj_dec x f :: snd acc)
    | EqFby x _ _ le => ((x, SynDF.typeof le)::fst acc, snd acc)
    end.

  Definition gather_eqs (eqs: list equation) : (list (ident * typ) * list obj_dec) :=
    List.fold_left gather_eq eqs ([], []).

  (** ** Translation *)

  Section Translate.

    Variable memories : PS.t.

    (* =tovar= *)
    Definition tovar (xt: ident * typ) : exp :=
      let (x, ty) := xt in
      if PS.mem x memories then State x ty else Var x ty.
    (* =end= *)

    (* =control= *)
    Fixpoint Control (ck: clock) (s: stmt) : stmt :=
      match ck with
      | Cbase => s
      | Con ck x ty true  => Control ck (Ifte (tovar (x, ty)) s Skip)
      | Con ck x ty false => Control ck (Ifte (tovar (x, ty)) Skip s)
      end.
    (* =end= *)

    (* =translate_lexp= *)
    Fixpoint translate_lexp (e : lexp) : exp :=
      match e with
      | Econst c ty => Const c ty
      | Evar x ty => tovar (x, ty)
      | Ewhen e c x => translate_lexp e
                                     (* | Eop op es => Op op (Nelist.map translate_lexp es) *)
      | Eunop op e ty => Unop op (translate_lexp e) ty
      | Ebinop op e1 e2 ty => Binop op (translate_lexp e1) (translate_lexp e2) ty
      end.
    (* =end= *)

    (* =translate_cexp= *)
    Fixpoint translate_cexp (x: ident) (e: cexp) : stmt :=
      match e with
      | Emerge y ty t f => Ifte (tovar (y, ty)) (translate_cexp x t) (translate_cexp x f)
      | Eexp l => Assign x (translate_lexp l)
      end.
    (* =end= *)

    (* =translate_eqn= *)
    Definition translate_eqn (eqn: equation) : stmt :=
      match eqn with
      | EqDef x ck ce => Control ck (translate_cexp x ce)
      | EqApp x ck f les => Control ck (Step_ap x f x (map translate_lexp les))
      | EqFby x ck v le => Control ck (AssignSt x (translate_lexp le))
      end.
    (* =end= *)

    (** Remark: eqns ordered in reverse order of execution for coherence with
       [Is_well_sch]. *)

    (* =translate_eqns= *)
    Definition translate_eqns (eqns: list equation) : stmt :=
      List.fold_left (fun i eq => Comp (translate_eqn eq) i) eqns Skip.
    (* =end= *)

  End Translate.

  (* =translate_reset_eqn= *)
  Definition translate_reset_eqn (s: stmt) (eqn: equation) : stmt :=
    match eqn with
    | EqDef _ _ _ => s
    | EqFby x _ v0 _ => Comp (AssignSt x (Const v0 (typ_of_val v0))) s
    | EqApp x _ f _ => Comp (Reset_ap f x) s
    end.
  (* =end= *)

  (* =translate_reset_eqns= *)
  Definition translate_reset_eqns (eqns: list equation): stmt :=
    List.fold_left translate_reset_eqn eqns Skip.
  (* =end= *)

  Definition ps_from_list (l: list ident) : PS.t :=
    List.fold_left (fun s i=>PS.add i s) l PS.empty.

  (* =translate_node= *)
  Definition translate_node (n: node): class :=
    let names := gather_eqs n.(n_eqs) in
    let mems := ps_from_list (List.map (@fst ident typ) (fst names)) in
    mk_class n.(n_name)
             n.(n_input)
             n.(n_output)
             (fst names)
             (snd names)
             (translate_eqns mems n.(n_eqs))
             (translate_reset_eqns n.(n_eqs)).
  (* =end= *)

  (* =translate= *)
  Definition translate (G: global) : program :=
    List.map translate_node G.
  (* =end= *)


  (** ** Properties *)


  Lemma ps_from_list_pre_spec:
    forall x l S, (List.In x l \/ PS.In x S)
             <->
             PS.In x (List.fold_left (fun s i=>PS.add i s) l S).
  Proof.
    induction l as [|l ls IH].
    - firstorder.
    - split; intro HH.
      + firstorder.
      + apply IH in HH.
        destruct HH as [HH|HH]; try apply PS.add_spec in HH; firstorder.
  Qed.

  Lemma ps_from_list_spec:
    forall x l, List.In x l <-> PS.In x (ps_from_list l).
  Proof.
    unfold ps_from_list.
    intros.
    rewrite <- ps_from_list_pre_spec with (S:=PS.empty).
    split; try intros [H | H]; try tauto.
    apply not_In_empty in H; contradiction.
  Qed.

  
End TranslationFun'.
Module TranslationFun <: TRANSLATION := TranslationFun'.
