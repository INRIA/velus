(* *********************************************************************)
(*                                                                     *)
(*                 The Vélus verified Lustre compiler                  *)
(*                                                                     *)
(*             (c) 2019 Inria Paris (see the AUTHORS file)             *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.

From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import Stc.StcSyntax.

From Velus Require Import Obc.ObcSyntax.

From Coq Require Import List.
Import List.ListNotations.
From Coq Require Import Morphisms.

Open Scope list.

(** * Translation *)

Module Type TRANSLATION
       (Import Ids    : IDS)
       (Import Op     : OPERATORS)
       (Import OpAux  : OPERATORS_AUX Op)
       (Import CESyn  : CESYNTAX      Op)
       (Import SynStc : STCSYNTAX Ids Op       CESyn)
       (Import SynObc : OBCSYNTAX Ids Op OpAux).

  Section Translate.

    Variable memories : PS.t.
    Variable clkvars  : Env.t clock.

    Definition tovar (xt: ident * type) : exp :=
      let (x, ty) := xt in
      if PS.mem x memories then State x ty else Var x ty.

    Definition bool_var (x: ident) : exp := tovar (x, bool_type).

    Fixpoint Control (ck: clock) (s: stmt) : stmt :=
      match ck with
      | Cbase          => s
      | Con ck x true  => Control ck (Ifte (bool_var x) s Skip)
      | Con ck x false => Control ck (Ifte (bool_var x) Skip s)
      end.

    Fixpoint translate_exp (e: CESyn.exp) : exp :=
      match e with
      | Econst c           => Const c
      | Evar x ty          => tovar (x, ty)
      | Ewhen e c x        => translate_exp e
      | Eunop op e ty      => Unop op (translate_exp e) ty
      | Ebinop op e1 e2 ty => Binop op (translate_exp e1) (translate_exp e2) ty
      end.

    Fixpoint translate_cexp (x: ident) (e: cexp) : stmt :=
      match e with
      | Emerge y t f =>
        Ifte (bool_var y) (translate_cexp x t) (translate_cexp x f)
      | Eite b t f =>
        Ifte (translate_exp b) (translate_cexp x t) (translate_cexp x f)
      | Eexp l =>
        Assign x (translate_exp l)
      end.

    Definition var_on_base_clock (ck: clock) (x: ident) : bool :=
      negb (PS.mem x memories)
           && match Env.find x clkvars with
              | Some ck' => clock_eq ck ck'
              | None => false
              end.

    Definition translate_arg (ck: clock) (e : CESyn.exp) : exp :=
      match e with
      | Evar x ty =>
        if var_on_base_clock ck x
        then Valid x ty
        else translate_exp e
      | _ => translate_exp e
      end.

    Definition translate_tc (tc: trconstr) : stmt :=
      match tc with
      | TcDef x ck ce =>
        Control ck (translate_cexp x ce)
      | TcNext x ck le =>
        Control ck (AssignSt x (translate_exp le))
      | TcCall s xs ck rst f es =>
        Control ck (Call xs f s step (map (translate_arg ck) es))
      | TcReset s ck f =>
        Control ck (Call [] f s reset [])
      end.

  (*   (** Remark: tcs ordered in reverse order of execution for coherence with *)
  (*      [Is_well_sch]. *) *)

    Definition translate_tcs (tcs: list trconstr) : stmt :=
      fold_left (fun i tc => Comp (translate_tc tc) i) tcs Skip.

  End Translate.

  Lemma ValidIds_idty:
    forall A B (xs: list (ident * (A * B))),
    Forall ValidId xs ->
    Forall ValidId (idty xs).
  Proof.
    induction 1; constructor; auto.
  Qed.

  Program Definition step_method (s: system) : method :=
    let memids := map fst s.(s_inits) in
    let mems := ps_from_list memids in
    let clkvars := Env.adds_with snd s.(s_out)
                    (Env.adds_with snd s.(s_vars)
                      (Env.from_list_with snd s.(s_in)))
    in
    {| m_name := step;
       m_in   := idty s.(s_in);
       m_vars := idty s.(s_vars);
       m_out  := idty s.(s_out);
       m_body := translate_tcs mems clkvars s.(s_tcs)
    |}.
  Next Obligation.
    rewrite <-2 idty_app;
      apply NoDupMembers_idty, s_nodup_vars.
  Qed.
  Next Obligation.
    rewrite <-2 idty_app;
      apply ValidIds_idty, s_good.
  Qed.

  Definition reset_mems (mems: list (ident * (const * clock))) : stmt :=
    fold_left (fun s xc => Comp s (AssignSt (fst xc) (Const (fst (snd xc))))) mems Skip.

  Definition reset_insts (insts: list (ident * ident)) : stmt :=
    fold_left (fun s xf => Comp s (Call [] (snd xf) (fst xf) reset [])) insts Skip.

  Definition translate_reset (b: system) : stmt :=
    Comp (reset_mems b.(s_inits)) (reset_insts b.(s_subs)).

  Hint Constructors NoDupMembers.

  Program Definition reset_method (b: system) : method :=
    {| m_name := reset;
       m_in   := [];
       m_vars := [];
       m_out  := [];
       m_body := translate_reset b
    |}.

  Program Definition translate_system (b: system) : class :=
    {| c_name    := b.(s_name);
       c_mems    := map (fun xc => (fst xc, type_const (fst (snd xc)))) b.(s_inits);
       c_objs    := b.(s_subs);
       c_methods := [ step_method b; reset_method b ]
    |}.
  Next Obligation.
    rewrite map_map; simpl; apply s_nodup_inits_subs.
  Qed.
  Next Obligation.
    constructor; auto using NoDup.
    inversion_clear 1; auto.
    now apply reset_not_step.
  Qed.
  Next Obligation.
    pose proof b.(s_good) as (?&?& Subs &?).
    split; auto.
    clear - Subs.
    induction Subs as [|?? Valid]; constructor; auto.
    apply Valid.
  Qed.

  Definition translate (P: SynStc.program) : program :=
    map translate_system P.

  Lemma exists_step_method:
    forall s,
      find_method step (translate_system s).(c_methods) = Some (step_method s).
  Proof.
    intro; simpl; rewrite ident_eqb_refl; eauto.
  Qed.

  Lemma exists_reset_method:
    forall s,
      find_method reset (translate_system s).(c_methods)
      = Some (reset_method s).
  Proof.
    assert (ident_eqb step reset = false) as Hsr.
    { apply ident_eqb_neq.
      apply PositiveOrder.neq_sym; apply reset_not_step.
    }
    simpl; now rewrite Hsr, ident_eqb_refl.
  Qed.

  Lemma find_method_stepm_out:
    forall s stepm,
      find_method step (translate_system s).(c_methods) = Some stepm ->
      stepm.(m_out) = idty s.(s_out).
  Proof.
    intros ??; simpl.
    rewrite ident_eqb_refl.
    inversion 1; auto.
  Qed.

  Lemma find_method_stepm_in:
    forall s stepm,
      find_method step (translate_system s).(c_methods) = Some stepm ->
      stepm.(m_in) = idty s.(s_in).
  Proof.
    intros ??; simpl.
    rewrite ident_eqb_refl.
    inversion 1; auto.
  Qed.

  Lemma find_class_translate:
    forall f P cls P',
      find_class f (translate P) = Some (cls, P') ->
      exists s P',
        find_system f P = Some (s, P')
        /\ cls = translate_system s.
  Proof.
    induction P as [|s P]; [now inversion 1|].
    intros * Hfind; simpl in Hfind.
    destruct (equiv_dec s.(s_name) f) as [Heq|Hneq].
    - rewrite Heq, ident_eqb_refl in Hfind.
      inv Hfind.
      exists s, P. split; auto.
      simpl. now rewrite Heq, ident_eqb_refl.
    - apply ident_eqb_neq in Hneq. rewrite Hneq in Hfind.
      apply IHP in Hfind as (s' & P'' & Hfind & Hcls).
      exists s', P''. simpl. rewrite Hneq. auto.
  Qed.

  Lemma find_system_translate:
    forall f P s P',
      find_system f P = Some (s, P') ->
      exists cls prog',
        find_class f (translate P) = Some (cls, prog')
        /\ cls = translate_system s
        /\ prog' = translate P'.
  Proof.
    induction P as [|s' P]; [now inversion 1|].
    intros * Hfind; simpl in Hfind.
    destruct (equiv_dec s'.(s_name) f) as [Heq|Hneq].
    - rewrite Heq, ident_eqb_refl in Hfind.
      injection Hfind; intros; subst s P'.
      exists (translate_system s'), (translate P).
      split; [|split]; auto.
      simpl. now rewrite Heq, ident_eqb_refl.
    - apply ident_eqb_neq in Hneq. rewrite Hneq in Hfind.
      apply IHP in Hfind as (cls & prog' & Hfind & Hcls).
      exists cls, prog'. split; auto. simpl. now rewrite Hneq.
  Qed.

  Lemma typeof_correct:
    forall mems e,
      typeof (translate_exp mems e) = CESyn.typeof e.
  Proof.
    induction e; intros; simpl; auto; cases.
  Qed.

  Corollary typeof_arg_correct:
    forall mems clkvars ck e,
      typeof (translate_arg mems clkvars ck e) = CESyn.typeof e.
  Proof.
    unfold translate_arg; intros.
    cases; simpl; cases.
    apply typeof_correct.
  Qed.

End TRANSLATION.

Module TranslationFun
       (Import Ids    : IDS)
       (Import Op     : OPERATORS)
       (Import OpAux  : OPERATORS_AUX Op)
       (Import CESyn  : CESYNTAX      Op)
       (Import SynStc : STCSYNTAX Ids Op       CESyn)
       (Import SynObc : OBCSYNTAX Ids Op OpAux)
       <: TRANSLATION Ids Op OpAux CESyn SynStc SynObc.
  Include TRANSLATION Ids Op OpAux CESyn SynStc SynObc.
End TranslationFun.
