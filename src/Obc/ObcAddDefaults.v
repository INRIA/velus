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

From Coq Require Import FSets.FMapPositive.
From Coq Require Import PArith.
From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Obc.ObcSyntax.
From Velus Require Import Obc.ObcSemantics.
From Velus Require Import Obc.ObcInvariants.
From Velus Require Import Obc.ObcTyping.
From Velus Require Import Obc.Equiv.

From Velus Require Import VelusMemory.

From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Import Env.Notations.

From Coq Require Import Morphisms.

Module Type OBCADDDEFAULTS
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op)
       (Import SynObc: Velus.Obc.ObcSyntax.OBCSYNTAX         Ids Op OpAux)
       (Import SemObc: Velus.Obc.ObcSemantics.OBCSEMANTICS   Ids Op OpAux SynObc)
       (Import InvObc: Velus.Obc.ObcInvariants.OBCINVARIANTS Ids Op OpAux SynObc SemObc)
       (Import TypObc: Velus.Obc.ObcTyping.OBCTYPING         Ids Op OpAux SynObc SemObc)
       (Import Equ   : Velus.Obc.Equiv.EQUIV                 Ids Op OpAux SynObc SemObc TypObc).

  (** ** AddDefault functions *)

  Section AddDefaults.

    Variable type_of_var : ident -> option type.

    Definition add_write x s :=
      match type_of_var x with
      | None => s
      | Some ty => Comp (Assign x (Const (init_type ty))) s
      end.

    Definition add_writes W s := PS.fold add_write W s.

    Definition add_valid (e : exp) (esreq : list exp * PS.t) :=
      match e with
      | Var x ty => (Valid x ty :: fst esreq, PS.add x (snd esreq))
      | _ => (e :: fst esreq, snd esreq)
      end.

    (* [(s', required', sometimes, always) = add_defaults_stmt (s, required)]

       Transforms [s] into [s'] by
       - Adding [Valid]s around "naked variables" in function calls.
       - Adding initializing writes to satisfy [required].

       [required] is a set of variables that must be written or otherwise
       initialized by [s] or a statement executed before [s].

       The output sets are:
       - [required']: updated set of variables to write or initialize
       - [sometimes]: variables that may be written in s
       - [always]: variables always written in s

       with [PS.is_empty (PS.inter sometimes always)] and knowing that a
       variable is never written if it is neither in [sometimes] nor [always].

       This function is designed to optimize code produced by compiling and
       then "fusion-ing" NLustre code, but proofs of the invariant properties
       do not rely on this fact (since that would require precisely expressing
       and tracking the assumptions).
       Notably, for Ifte, it should always be the case that
       [sometimes1' = sometimes1] and [sometimes2' = sometimes2]. *)
    Fixpoint add_defaults_stmt (required: PS.t) (s: stmt) : stmt * PS.t * PS.t * PS.t :=
      match s with
      | Skip => (s, required, PS.empty, PS.empty)
      | Assign x e => (s, PS.remove x required, PS.empty, PS.singleton x)
      | AssignSt x e => (s, required, PS.empty, PS.empty)
      | Call xs f o m es =>
        let (es', required') := fold_right add_valid
                                           ([], ps_removes xs required) es
        in (Call xs f o m es', required', PS.empty, ps_adds xs PS.empty)
      | Comp s1 s2 =>
        let '(t2, required2, sometimes2, always2) := add_defaults_stmt required s2 in
        let '(t1, required1, sometimes1, always1) := add_defaults_stmt required2 s1 in
        (Comp t1 t2,
         required1,
         PS.union (PS.diff sometimes1 always2) (PS.diff sometimes2 always1),
         PS.union always1 always2)
      | Ifte e s1 s2 =>
        let '(t1, required1, sometimes1, always1) := add_defaults_stmt PS.empty s1 in
        let '(t2, required2, sometimes2, always2) := add_defaults_stmt PS.empty s2 in
        let always1_req := PS.inter always1 required in
        let always2_req := PS.inter always2 required in
        let w1 := PS.diff always2_req always1_req in
        let w2 := PS.diff always1_req always2_req in
        let w := PS.union (PS.diff (PS.inter sometimes1 required) w1)
                          (PS.diff (PS.inter sometimes2 required) w2) in
        let always1' := PS.union always1 w1 in
        let always2' := PS.union always2 w2 in
        let sometimes1' := PS.diff sometimes1 w1 in
        let sometimes2' := PS.diff sometimes2 w2 in
        (add_writes w (Ifte e (add_writes w1 t1) (add_writes w2 t2)),
         PS.diff (PS.union
                    (PS.union
                       ((PS.diff (PS.diff required always1_req) always2_req))
                       required1)
                    required2)
                 w,
         PS.diff (PS.union sometimes1'
                           (PS.union sometimes2'
                                     (PS.union
                                        (PS.diff always1' always2')
                                        (PS.diff always2' always1')))) w,
         PS.union (PS.inter always1' always2') w)
      end.

  End AddDefaults.

  Definition add_defaults_method (m: method): method :=
    match m with
      mk_method name ins vars outs body nodup good =>
      mk_method name ins vars outs
         (let tyenv := fun x => Env.find x
                (Env.adds' outs (Env.adds' vars (Env.from_list ins))) in
          let '(body', required, sometimes, always) :=
              add_defaults_stmt tyenv (ps_adds (map fst outs) PS.empty) body in
          add_writes tyenv (ps_removes (map fst ins) required) body')
         nodup good
    end.

  Lemma add_defaults_method_m_name:
    forall m,
      (add_defaults_method m).(m_name) = m.(m_name).
  Proof. now destruct m. Qed.

  Lemma add_defaults_method_m_in:
    forall m, (add_defaults_method m).(m_in) = m.(m_in).
  Proof. now destruct m. Qed.

  Lemma add_defaults_method_m_out:
    forall m, (add_defaults_method m).(m_out) = m.(m_out).
  Proof. now destruct m. Qed.

  Lemma add_defaults_method_m_vars:
    forall m, (add_defaults_method m).(m_vars) = m.(m_vars).
  Proof. now destruct m. Qed.

  Program Definition add_defaults_class (c: class): class :=
    match c with
      mk_class name mems objs methods nodup nodupm cgood =>
      mk_class name mems objs (map add_defaults_method methods) nodup _ cgood
    end.
  Next Obligation.
    rewrite map_map. now setoid_rewrite add_defaults_method_m_name.
  Qed.

  Definition add_defaults := map add_defaults_class.

  Lemma find_method_add_defaults_method:
    forall n ms m,
      find_method n ms = Some m ->
      find_method n (map add_defaults_method ms) = Some (add_defaults_method m).
  Proof.
    induction ms as [|m ms' IH]. discriminate.
    simpl. setoid_rewrite add_defaults_method_m_name.
    destruct (ident_eqb m.(m_name) n); auto.
    now inversion_clear 1.
  Qed.

  Lemma find_method_map_add_defaults_method':
    forall n ms fm,
      find_method n (map add_defaults_method ms) = Some fm
      -> exists fm',
        find_method n ms = Some fm' /\ fm = add_defaults_method fm'.
  Proof.
    induction ms as [|m ms' IH]. discriminate.
    simpl. setoid_rewrite add_defaults_method_m_name.
    destruct (ident_eqb m.(m_name) n); auto.
    inversion_clear 1; eauto.
  Qed.

  Lemma find_method_map_add_defaults_method:
    forall n c,
      find_method n (map add_defaults_method c.(c_methods))
      = find_method n (add_defaults_class c).(c_methods).
  Proof. now destruct c. Qed.

  Lemma add_defaults_class_c_name:
    forall c, (add_defaults_class c).(c_name) = c.(c_name).
  Proof. now destruct c. Qed.

  Lemma add_defaults_class_c_objs:
    forall c, (add_defaults_class c).(c_objs) = c.(c_objs).
  Proof. now destruct c. Qed.

  Lemma add_defaults_class_c_mems:
    forall c, (add_defaults_class c).(c_mems) = c.(c_mems).
  Proof. now destruct c. Qed.

  Lemma find_class_add_defaults_class:
    forall p n c p',
      find_class n p = Some (c, p') ->
      find_class n (add_defaults p)
      = Some (add_defaults_class c, add_defaults p').
  Proof.
    induction p as [|c p' IH]. discriminate.
    simpl in *. rewrite add_defaults_class_c_name.
    intros n c' p''.
    destruct (ident_eqb c.(c_name) n); auto.
    now inversion_clear 1.
  Qed.

  Lemma find_class_add_defaults_class_not_None:
    forall n p,
      find_class n p <> None ->
      find_class n (add_defaults p) <> None.
  Proof.
    intros n p Hfind.
    apply not_None_is_Some in Hfind as ((c & p') & Hfind).
    apply find_class_add_defaults_class in Hfind.
    now rewrite Hfind.
  Qed.

  Notation "x '∈' y" := (PS.In x y) (at level 10).
  Notation "x '∪' y" := (PS.union x y) (at level 11, right associativity).
  Notation "x '∩' y" := (PS.inter x y) (at level 11, right associativity).
  Notation "x '—' y" := (PS.diff x y) (at level 11).

  Ltac PS_split :=
    repeat match goal with
           | H: context [ PS.union _ _ ] |- _ => setoid_rewrite PS.union_spec in H
           | H: context [ ~(PS.inter _ _) ] |- _ => setoid_rewrite PS_not_inter in H
           | H: context [ PS.inter _ _ ] |- _ => setoid_rewrite PS.inter_spec in H
           | H: context [ PS.diff _ _ ] |- _ => setoid_rewrite PS.diff_spec in H
           | H: context [ ~(_ \/ _) ] |- _ => setoid_rewrite not_or' in H
           | H: context [ ~~PS.In _ _ ] |- _ => setoid_rewrite not_not_in in H
           | H:_ /\ _ |- _ => destruct H
           | |- context [ PS.union _ _ ] => setoid_rewrite PS.union_spec
           | |- context [ ~(PS.inter _ _) ] => setoid_rewrite PS_not_inter
           | |- context [ PS.inter _ _ ] => setoid_rewrite PS.inter_spec
           | |- context [ PS.diff _ _ ] => setoid_rewrite PS.diff_spec
           | |- context [ ~(_ \/ _) ] => setoid_rewrite not_or'
           | |- context [ ~~PS.In _ _ ] => setoid_rewrite not_not_in
           end.

  Ltac PS_negate :=
    repeat match goal with
           | H:~(_ /\ _) |- _ => apply Decidable.not_and in H; [|now intuition]
           | H:~~_ |- _ => apply Decidable.not_not in H; [|now intuition]
           | H: context [ ~~PS.In _ _ ] |- _ => setoid_rewrite not_not_in in H
           end.

  Lemma simplify_write_sets:
    forall w w1 w2 al1 al2 st1 st2 rq,
      w1 = (al2 ∩ rq) — (al1 ∩ rq) ->
      w2 = (al1 ∩ rq) — (al2 ∩ rq) ->
      w = ((st1 ∩ rq) — w1) ∪ ((st2 ∩ rq) — w2) ->
      PS.Equal ((((st1 — w1)
                    ∪ (st2 — w2)
                    ∪ ((al1 ∪ w1) — (al2 ∪ w2))
                    ∪ (al2 ∪ w2) — (al1 ∪ w1)) — w)
                  ∪ ((al1 ∪ w1) ∩ al2 ∪ w2) ∪ w)
               (w ∪ w1 ∪ w2 ∪ al1 ∪ al2 ∪ st1 ∪ st2).
  Proof.
    intros. intro x.
    rewrite (PSP.union_sym _ w), <-(PSP.union_assoc _ w), PS_union_diff_same.
    split; intro HH. now PS_split; tauto.
    destruct (PSP.In_dec x (al2 ∪ w2));
      destruct (PSP.In_dec x (al1 ∪ w1)).
    - PS_split; tauto.
    - PS_split; tauto.
    - PS_split; tauto.
    - PS_split; tauto.
  Qed.

  (** ** Basic lemmas around [add_defaults_class] and [add_defaults_method]. *)

  Lemma add_defaults_class_find_method:
    forall f c,
      find_method f (add_defaults_class c).(c_methods)
      = option_map (add_defaults_method) (find_method f c.(c_methods)).
  Proof.
    intros f c. destruct c. simpl.
    rewrite find_method_map; auto.
    now intro m; destruct m.
  Qed.

  Lemma In_snd_fold_right_add_valid:
    forall x s,
      PS.In x s ->
      forall es xs,
        PS.In x (snd (fold_right add_valid (xs, s) es)).
  Proof.
    intros x s Hin.
    induction es as [|e es IH]; auto.
    intro xs. simpl. unfold add_valid at 1.
    rewrite (surjective_pairing (fold_right _ _ _)).
    destruct e; simpl; auto. rewrite PS.add_spec.
    edestruct (equiv_dec x); [now left; eauto|auto].
  Qed.

  Definition add_valid' e := match e with Var x ty => Valid x ty | _ => e end.

  Lemma add_valid_add_valid':
    forall es S es',
      fst (fold_right add_valid (es', S) es) = map add_valid' es ++ es'.
  Proof.
    induction es as [|e es IH]; auto.
    simpl. intros S xs'.
    destruct e; simpl; rewrite IH; auto.
  Qed.

  Lemma Forall2_exp_eval_refines_with_valid:
    forall me ve1 ve2 es vos,
      ve2 ⊑ ve1 ->
      Forall (fun e => match e with Var x _ => Env.In x ve1 | _ => True end) es ->
      Forall2 (exp_eval me ve2) es vos ->
      exists vos',
        Forall2 (exp_eval me ve1) (map add_valid' es) vos'
        /\ Forall2 (fun vo vo' => forall v, vo = Some v -> vo' = Some v) vos vos'.
  Proof.
    intros me ve1 ve2 es vos Henv Hvar Hvos.
    induction Hvos as [|e vo es vos He Hfa IH].
    now setoid_rewrite Forall2_map_1; eauto.
    apply Forall_cons2 in Hvar as (Hvar & Hvars).
    apply exp_eval_refines' with (1:=Henv) in He as (vo' & Heval & Hvo').
    destruct IH as (vos' & Hevals & Hvos'); auto.
    destruct e; simpl; eauto using Forall2_cons.
    assert (exists v', vo' = Some v') as (v' & Hv')
        by now inv Heval; rewrite Env.In_find in Hvar.
    exists (vo'::vos'). subst vo'; split; auto.
    inv Heval; constructor; eauto using exp_eval.
    take (Env.find _ _ = _) and rewrite it; eauto using exp_eval.
  Qed.

  Lemma stmt_eval_add_writes_split:
    forall tyenv p s W me ve me'' ve'',
      stmt_eval p me ve (add_writes tyenv W s) (me'', ve'') <->
      (exists me' ve',
          stmt_eval p me ve (add_writes tyenv W Skip) (me', ve')
          /\ stmt_eval p me' ve' s (me'', ve'')).
  Proof.
    unfold add_writes.
    setoid_rewrite PSE.MP.fold_spec_right.
    intros until ve''.
    remember (rev (PS.elements W)) as ws.
    setoid_rewrite <-Heqws; clear Heqws W.
    revert s me ve me'' ve''.
    induction ws as [|w ws IH]; simpl; split; eauto using stmt_eval.
    - intros (me' & ve' & Heval1 & Heval2). now inv Heval1.
    - unfold add_write at 1 3. intro Heval.
      destruct (tyenv w).
      + inversion_clear Heval as [| | |? ? ? ? ? ? ? ? ? Heval1 Heval2| |].
        apply IH in Heval2 as (me' & ve' & Heval1' & Heval2'). eauto using stmt_eval.
      + apply IH in Heval as (me' & ve' & Heval1' & Heval2'). eauto.
    - unfold add_write at 1 3. intros (me' & ve' & Heval1 & Heval3).
      destruct (tyenv w).
      + inversion_clear Heval1 as [| | |? ? ? ? ? ? ? ? ? Heval1' Heval2| |].
        econstructor; [now eapply Heval1'|]. apply IH; eauto.
      + apply IH; eauto.
  Qed.

  Lemma No_Naked_Vars_add_writes:
    forall tyenv W s,
      No_Naked_Vars s <-> No_Naked_Vars (add_writes tyenv W s).
  Proof.
    unfold add_writes.
    setoid_rewrite PSE.MP.fold_spec_right.
    intros tyenv W s.
    remember (rev (PS.elements W)) as ws.
    setoid_rewrite <-Heqws; clear Heqws.
    induction ws as [|w ws IH]; simpl. reflexivity.
    unfold add_write.
    rewrite IH. destruct (tyenv w); split; intro HH; auto.
    inversion_clear HH; auto.
  Qed.

  Lemma stmt_eval_add_writes:
    forall p,
      (forall ome ome' clsid f vos rvos,
          Forall (fun vo => vo <> None) vos ->
          stmt_call_eval p ome clsid f vos ome' rvos ->
          Forall (fun x => x <> None) rvos) ->
      forall tyenv s W me ve me' ve',
        PS.For_all (fun x => tyenv x <> None) W ->
        No_Naked_Vars s ->
        stmt_eval p me ve (add_writes tyenv W s) (me', ve') ->
        (forall x, PS.In x W -> Env.In x ve').
  Proof.
    intros p Hcall tyenv s W.
    setoid_rewrite (No_Naked_Vars_add_writes tyenv W s). revert s W.
    unfold add_writes.
    setoid_rewrite PSE.MP.fold_spec_right.
    intros until ve'.
    remember (rev (PS.elements W)) as ws.
    assert (forall x, PS.In x W <-> In x ws) as HinW.
    { intro x; subst ws. rewrite <-in_rev, PSF.elements_iff.
      split; intro HH; auto. apply SetoidList.InA_alt in HH.
      destruct HH as (? & ? & ?); subst; eauto. }
    setoid_rewrite PS_For_all_Forall.
    setoid_rewrite (Permutation.Permutation_rev (PS.elements W)) at 1 4.
    setoid_rewrite <-Heqws.
    clear Heqws HinW W.
    revert s me ve me' ve'.
    induction ws as [|w ws IH]; eauto.
    simpl. intros * Hfa Hnnv Heval.
    inversion_clear Hfa as [|? ? Hnn Hws].
    unfold add_write in Heval, Hnnv.
    apply not_None_is_Some in Hnn; destruct Hnn as (wv & Hnn).
    rewrite Hnn in Heval, Hnnv.
    inversion_clear Heval as [| | |? ? ? ? ? ? ? Ha Hb Heval1 Heval2| |].
    inversion_clear Hnnv as [| | | |? ? Hnnv1 Hnnv2|].
    pose proof (stmt_eval_mono' _ Hcall _ _ _ _ _ Hnnv2 Heval2) as Henv1'.
    apply IH in Heval2; auto.
    constructor; auto.
    apply Henv1'. inv Heval1.
    apply Env.Props.P.F.add_in_iff; auto.
  Qed.

  Lemma stmt_eval_add_writes_Skip_other:
    forall p tyenv W me ve me' ve',
      stmt_eval p me ve (add_writes tyenv W Skip) (me', ve') ->
      forall x, ~PS.In x W ->
                Env.find x ve' = Env.find x ve.
  Proof.
    setoid_rewrite PSE.MP.fold_spec_right.
    intros until ve'.
    remember (rev (PS.elements W)) as ws.
    assert (forall x, PS.In x W <-> In x ws) as HinW.
    { intro x; subst ws. rewrite <-in_rev, PSF.elements_iff.
      split; intro HH; auto. apply SetoidList.InA_alt in HH.
      destruct HH as (? & ? & ?); subst; eauto. }
    setoid_rewrite HinW. setoid_rewrite <-Heqws.
    clear Heqws HinW W.
    revert me ve me' ve'.
    induction ws as [|w ws IH]. now inversion 1.
    simpl. intros * Heval x Hin.
    apply Decidable.not_or in Hin.
    destruct Hin as (Hnwx & Hnin).
    unfold add_write in Heval. destruct (tyenv w).
    - inversion_clear Heval as [| | |? ? ? ? ? ? ? ? ? Heval1 Heval2| |].
      apply IH with (x:=x) in Heval2; auto. rewrite Heval2.
      inv Heval1. rewrite Env.gso; auto.
    - apply IH with (x:=x) in Heval; auto.
  Qed.

  Lemma add_defaults_stmt_inv1:
    forall tyenv s t req req' stimes always,
      add_defaults_stmt tyenv req s = (t, req', stimes, always) ->
      PS.Empty (PS.inter stimes always)
      /\ (forall x, PS.In x req -> PS.In x always \/ PS.In x req')
      /\ (forall x, PS.In x (PS.union stimes always) -> Can_write_in x s)
      /\ (forall x, ~Can_write_in x s -> ~PS.In x (PS.union stimes always))
      /\ No_Naked_Vars t.
  Proof.
    induction s as [| | | |ys clsid o f es|]; intros t rq rq' st al Hadd; inv Hadd.
    - (* * Assign i e *)
      split; [now intuition|repeat split]; auto.
      + intros x Hin. edestruct (equiv_dec x) as [He|Hne]; eauto using PSF.remove_2.
        now rewrite He, PS.singleton_spec; auto.
      + setoid_rewrite PS.union_spec.
        intros x [Hin|Hin]; try not_In_empty.
        apply PSF.singleton_iff in Hin; subst; auto.
      + setoid_rewrite PS.union_spec.
        intros x Hnc [Hin|Hin]; try not_In_empty.
        apply PSF.singleton_iff in Hin; subst; auto.
    - (* * AssignSt i e *)
      setoid_rewrite PSF.empty_iff; intuition.
    - (* * Ifte e s1 s2 *)
      rename H0 into Hadd.
      set (defs1 := add_defaults_stmt tyenv PS.empty s1).
      assert (add_defaults_stmt tyenv PS.empty s1 = defs1) as Hdefs1
          by now subst defs1.
      rewrite Hdefs1 in Hadd.
      destruct defs1 as [[[t1 rq1] st1] al1].

      set (defs2 := add_defaults_stmt tyenv PS.empty s2).
      assert (add_defaults_stmt tyenv PS.empty s2 = defs2) as Hdefs2
          by now subst defs2.
      rewrite Hdefs2 in Hadd.
      destruct defs2 as [[[t2 rq2] st2] al2].

      remember ((al2 ∩ rq) — (al1 ∩ rq)) as w1.
      remember ((al1 ∩ rq) — (al2 ∩ rq)) as w2.
      remember (((st1 ∩ rq) — w1) ∪ ((st2 ∩ rq) — w2)) as w.
      assert (forall x, PS.In x w1 <-> PS.In x al2 /\ PS.In x rq /\ ~PS.In x al1) as Hw1
          by (subst w1; clear; PS_split; intuition).
      assert (forall x, PS.In x w2 <-> PS.In x al1 /\ PS.In x rq /\ ~PS.In x al2) as Hw2
          by (subst w2; clear; PS_split; intuition).

      injection Hadd; clear Hadd; intros; subst al st rq' t.
      apply IHs1 in Hdefs1 as (H1A & H1B & H1C & H1D & H1E); clear IHs1 H1B.
      apply IHs2 in Hdefs2 as (H2A & H2B & H2C & H2D & H2E); clear IHs2 H2B.

      repeat split.
      + (* PS.Empty (PS.inter st al) *)
        intros x HH. PS_split.
        match goal with H:_ \/ PS.In x w |- _ =>
                        destruct H as [[HH1 HH2]|HH]; [|contradiction] end.
        subst w. PS_split. PS_negate.
        repeat match goal with H: _ \/ _ |- _ =>
                               destruct H; PS_split; PS_negate;
                                 try contradiction;
                                 try (now eapply H1A; eapply PS.inter_spec; eauto);
                                 try (now eapply H2A; eapply PS.inter_spec; eauto)
               end.
      + (* forall x, x ∈ req -> x ∈ always \/ x ∈ req' *)
        intros x Hin.
        destruct (PSP.In_dec x (((al1 ∪ w1) ∩ al2 ∪ w2) ∪ w)) as [HH|HH]; auto.
        PS_split; PS_negate.
        repeat match goal with
                 H: _ \/ _ |- _ => destruct H
               | H:~(_ \/ _) |- _ => apply Decidable.not_or in H as (HH1 & HH2)
               end;
          match goal with
          | H:~(PS.In x w) |- _ => assert (Hnw := H);
                                     rewrite Heqw, PS_not_union in H;
                                     destruct H as (HnxA & HnxB);
                                     apply PS_not_diff in HnxA as [HnxA | HnxA];
                                     apply PS_not_diff in HnxB as [HnxB | HnxB];
                                     try (apply PS_not_inter in HnxA as [HnxA|];
                                          [|contradiction]);
                                     try (apply PS_not_inter in HnxB as [HnxB|];
                                          [|contradiction])
          end;
          repeat match goal with
                 | H:~PS.In x w1 |- _ =>
                   rewrite Hw1 in H; PS_negate; destruct H as [H|]; now tauto
                 | H:~PS.In x w2 |- _ =>
                   rewrite Hw2 in H; PS_negate; destruct H as [H|]; now tauto
                 | H:PS.In x (PS.inter (PS.inter _ _) _) |- _ =>
                   repeat rewrite PS.inter_spec in H;
                     destruct H as ((HB1 & HB2) & HB3)
                 end.
      + (* forall x, PS.In x (PS.union stimes always) -> Can_write_in x s *)
        intros x Hin.
        cut (PS.In x (PS.union (PS.union st1 al1) (PS.union st2 al2))).
        now rewrite PS.union_spec; destruct 1 as [HH|HH]; auto.
        PS_split; repeat match goal with H: _ \/ _ |- _ => destruct H
                                       | H: _ /\ _ |- _ => destruct H
                                       | H:PS.In _ w1 |- _ => apply Hw1 in H
                                       | H:PS.In _ w2 |- _ => apply Hw2 in H end;
        auto.
        subst w; PS_split; tauto.
      + (* forall x, ~Can_write_in x s -> ~PS.In x (PS.union stimes always) *)
        intros x Hncw.
        cut (~PS.In x (PS.union (PS.union st1 al1) (PS.union st2 al2))).
        * intros HH1 HH; apply HH1; clear HH1.
          PS_split; repeat match goal with H: _ \/ _ |- _ => destruct H
                                         | H: _ /\ _ |- _ => destruct H
                                         | H:PS.In _ w1 |- _ => apply Hw1 in H
                                         | H:PS.In _ w2 |- _ => apply Hw2 in H end;
          auto. subst w; PS_split; tauto.
        * setoid_rewrite PS.union_spec. intros [HH|HH]; auto.
      + (* No_Naked_Vars t *)
        apply No_Naked_Vars_add_writes.
        now constructor; apply No_Naked_Vars_add_writes.
    - (* * Comp s1 s2 *)
      rename H0 into Hadd.

      set (defs2 := add_defaults_stmt tyenv rq s2).
      assert (add_defaults_stmt tyenv rq s2 = defs2) as Hdefs2 by now subst defs2.
      rewrite Hdefs2 in Hadd.
      destruct defs2 as [[[t2 req2] stimes2] always2].

      set (defs1 := add_defaults_stmt tyenv req2 s1).
      assert (add_defaults_stmt tyenv req2 s1 = defs1) as Hdefs1 by now subst defs1.
      rewrite Hdefs1 in Hadd.
      destruct defs1 as [[[t1 req1] stimes1] always1].

      injection Hadd; clear Hadd; intros; subst al st rq' t.
      apply IHs1 in Hdefs1 as (H1A & H1B & H1C & H1D & H1E); clear IHs1.
      apply IHs2 in Hdefs2 as (H2A & H2B & H2C & H2D & H2E); clear IHs2.
      repeat split; auto.
      + intro x. PS_split.
        destruct 1 as [[[? ?]|[? ?]] [?|?]]; try contradiction.
        now eapply H1A, PS.inter_spec; eauto.
        now eapply H2A, PS.inter_spec; eauto.
      + intros x HH. apply H2B in HH as [HH|HH]; [now intuition|].
        apply H1B in HH. intuition.
      + repeat setoid_rewrite PS.union_spec. setoid_rewrite PS.diff_spec.
        intros x [[[Hin ?]|[Hin ?]]|[Hin|Hin]]; intuition.
      + repeat setoid_rewrite PS.union_spec. setoid_rewrite PS.diff_spec.
        intros x Hncw [[[Hin ?]|[Hin ?]]|[Hin|Hin]]; intuition.
    - (* * Call ys clsid o f es *)
      rename H0 into Hadd.
      rewrite (surjective_pairing (fold_right _ _ _)) in Hadd.
      inv Hadd. repeat split; auto.
      + intros x Hin.
        destruct (In_dec ident_eq_dec x ys) as [Hys|Hnys]; [left|right].
        * now apply ps_adds_spec; auto.
        * apply In_snd_fold_right_add_valid, ps_removes_spec; auto.
      + setoid_rewrite PS.union_spec.
        intros x [Hin|Hin]; try not_In_empty.
        apply ps_adds_spec in Hin as [Hin|Hin]; try not_In_empty; auto.
      + setoid_rewrite PS.union_spec.
        intros x Hncw [Hin|Hin]; try not_In_empty.
        apply ps_adds_spec in Hin as [Hin|Hin]; try not_In_empty; auto.
      + constructor. rewrite add_valid_add_valid', app_nil_r.
        rewrite Forall_map; auto. apply Forall_forall.
        intros e Hin y ty. destruct e; try discriminate.
    - (* * Skip *)
      setoid_rewrite PSF.empty_iff; intuition.
  Qed.

  Lemma Can_write_in_add_writes_mono:
    forall tyenv s W x,
      Can_write_in x s ->
      Can_write_in x (add_writes tyenv W s).
  Proof.
    intros tyenv s W x Hcan.
    setoid_rewrite PSE.MP.fold_spec_right.
    remember (rev (PS.elements W)) as ws.
    setoid_rewrite <-Heqws. clear Heqws W.
    induction ws as [|w ws IH]; auto.
    simpl. unfold add_write at 1.
    destruct (tyenv w); auto.
  Qed.

  Lemma Can_write_in_add_writes:
    forall tyenv s W x,
      Can_write_in x (add_writes tyenv W s) ->
      PS.In x W \/ Can_write_in x s.
  Proof.
    intros tyenv s W x.
    setoid_rewrite PSE.MP.fold_spec_right.
    remember (rev (PS.elements W)) as ws.
    assert (forall x, PS.In x W <-> In x ws) as HinW.
    { intro y; subst ws. rewrite <-in_rev, PSF.elements_iff.
      split; intro HH; auto. apply SetoidList.InA_alt in HH.
      destruct HH as (? & ? & ?); subst; eauto. }
    setoid_rewrite <-Heqws; rewrite HinW; clear Heqws HinW W.
    induction ws as [|w ws IH]; auto.
    simpl. unfold add_write at 1.
    destruct (tyenv w); [intro Hcw|now intuition].
    inversion_clear Hcw as [| | | | |? ? ? Hcw'|? ? ? Hcw'].
    now inversion_clear Hcw'; auto. intuition.
  Qed.

  Lemma Can_write_in_add_defaults_stmt:
    forall tyenv s req t req' st al,
      add_defaults_stmt tyenv req s = (t, req', st, al) ->
      (forall x, Can_write_in x s <-> Can_write_in x t).
  Proof.
    induction s.
    - (* Assign i e *)
      now inversion_clear 1.
    - (* AssignSt i e *)
      now inversion_clear 1.
    - (* Ifte e s1 s2 *)
      simpl; intros * Hadd x.
      set (defs1 := add_defaults_stmt tyenv PS.empty s1).
      assert (add_defaults_stmt tyenv PS.empty s1 = defs1) as Hdefs1
          by now subst defs1.
      rewrite Hdefs1 in Hadd.
      destruct defs1 as [[[t1 rq1] st1] al1].

      set (defs2 := add_defaults_stmt tyenv PS.empty s2).
      assert (add_defaults_stmt tyenv PS.empty s2 = defs2) as Hdefs2
          by now subst defs2.
      rewrite Hdefs2 in Hadd.
      destruct defs2 as [[[t2 rq2] st2] al2].

      remember ((al2 ∩ req) — (al1 ∩ req)) as w1.
      remember ((al1 ∩ req) — (al2 ∩ req)) as w2.
      remember (((st1 ∩ req) — w1) ∪ ((st2 ∩ req) — w2)) as w.
      inversion_clear Hadd.
      specialize (IHs1 _ _ _ _ _ Hdefs1).
      specialize (IHs2 _ _ _ _ _ Hdefs2).

      split; intro Hcan.
      + apply Can_write_in_add_writes_mono.
        inversion_clear Hcan.
        now apply CWIIfteTrue, Can_write_in_add_writes_mono, IHs1.
        now apply CWIIfteFalse, Can_write_in_add_writes_mono, IHs2.
      + apply add_defaults_stmt_inv1 in Hdefs1 as (? & ? & Hcw1).
        apply add_defaults_stmt_inv1 in Hdefs2 as (? & ? & Hcw2).
        apply Can_write_in_add_writes in Hcan as [Hcw|Hcw].
        now subst w; apply PS.union_spec in Hcw as [Hcw|Hcw]; PS_split; auto.
        inversion_clear Hcw as [| |? ? ? ? Hcw'|? ? ? ? Hcw'| | |].
        * apply Can_write_in_add_writes in Hcw' as [Hcw|Hcw].
          now subst w1; PS_split; auto. now apply CWIIfteTrue, IHs1.
        * apply Can_write_in_add_writes in Hcw' as [Hcw|Hcw].
          now subst w2; PS_split; auto. now apply CWIIfteFalse, IHs2.
    - (* * Comp s1 s2 *)
      simpl; intros * Hadd x.

      set (defs2 := add_defaults_stmt tyenv req s2).
      assert (add_defaults_stmt tyenv req s2 = defs2) as Hdefs2 by now subst defs2.
      rewrite Hdefs2 in Hadd.
      destruct defs2 as [[[t2 req2] stimes2] always2].

      set (defs1 := add_defaults_stmt tyenv req2 s1).
      assert (add_defaults_stmt tyenv req2 s1 = defs1) as Hdefs1 by now subst defs1.
      rewrite Hdefs1 in Hadd.
      destruct defs1 as [[[t1 req1] stimes1] always1].

      injection Hadd; clear Hadd; intros; subst al st req' t.
      specialize (IHs1 _ _ _ _ _ Hdefs1 x).
      specialize (IHs2 _ _ _ _ _ Hdefs2 x).
      split; inversion_clear 1.
      + rewrite IHs1 in *; auto.
      + rewrite IHs2 in *; auto.
      + rewrite <-IHs1 in *; auto.
      + rewrite <-IHs2 in *; auto.
    - (* * Call ys clsid o f es *)
      simpl; intros * Hadd x.
      rewrite (surjective_pairing (fold_right _ _ _)) in Hadd.
      inv Hadd. split; inversion_clear 1; auto.
    - (* * Skip *)
      now inversion_clear 1.
  Qed.

  Lemma add_defaults_stmt_no_write:
    forall p tyenv s t me me' ve ve' req req' stimes always,
      add_defaults_stmt tyenv req s = (t, req', stimes, always) ->
      stmt_eval p me ve s (me', ve') ->
      forall x, ~PS.In x (PS.union stimes always) ->
                Env.find x ve' = Env.find x ve.
  Proof.
    induction s as [| | | |ys clsid o f es|];
      intros t me me' ve ve' rq rq' st al Hadd Heval x Hnin.
    - (* * Assign i e *)
      inv Hadd. inv Heval. rewrite Env.gso; intuition.
    - (* * AssignSt i e *)
      inv Hadd. now inv Heval.
    - (* * Ifte e s1 s2 *)
      inversion Hadd as [Hadd']; clear Hadd.

      set (defs1 := add_defaults_stmt tyenv PS.empty s1).
      assert (add_defaults_stmt tyenv PS.empty s1 = defs1) as Hdefs1
          by now subst defs1.
      rewrite Hdefs1 in Hadd'.
      destruct defs1 as [[[t1 rq1] st1] al1].

      set (defs2 := add_defaults_stmt tyenv PS.empty s2).
      assert (add_defaults_stmt tyenv PS.empty s2 = defs2) as Hdefs2
          by now subst defs2.
      rewrite Hdefs2 in Hadd'.
      destruct defs2 as [[[t2 rq2] st2] al2].

      inv Hadd'. inv Heval. destruct b.
      + match goal with H:stmt_eval _ _ _ s1 _ |- _ =>
          apply IHs1 with (1:=Hdefs1) (x:=x) in H; auto end.
        PS_split; intuition.
      + match goal with H:stmt_eval _ _ _ s2 _ |- _ =>
          apply IHs2 with (1:=Hdefs2) (x:=x) in H; auto end.
        PS_split; intuition.
    - (* * Comp s1 s2 *)
      inversion Hadd as [Hadd']; clear Hadd.

      set (defs2 := add_defaults_stmt tyenv rq s2).
      assert (add_defaults_stmt tyenv rq s2 = defs2) as Hdefs2 by now subst defs2.
      rewrite Hdefs2 in Hadd'.
      destruct defs2 as [[[t2 rq2] st2] al2].

      set (defs1 := add_defaults_stmt tyenv rq2 s1).
      assert (add_defaults_stmt tyenv rq2 s1 = defs1) as Hdefs1 by now subst defs1.
      rewrite Hdefs1 in Hadd'.
      destruct defs1 as [[[t1 rq1] st1] al1].

      inv Hadd'. inv Heval.
      match goal with H:stmt_eval _ _ _ s2 _ |- _ =>
        apply IHs2 with (1:=Hdefs2) (x:=x) in H; [rewrite H|] end.
      match goal with H:stmt_eval _ _ _ s1 _ |- _ =>
        apply IHs1 with (1:=Hdefs1) (x:=x) in H; [now rewrite H|] end.
      + intro Hin; apply Hnin; clear Hnin.
        destruct (PSP.In_dec x al2). now intuition.
        apply PS.union_spec in Hin as [Hin|Hin]; intuition.
      + intro Hin; apply Hnin; clear Hnin.
        destruct (PSP.In_dec x al1). now intuition.
        apply PS.union_spec in Hin as [Hin|Hin]; intuition.
    - (* * Call ys clsid o f es *)
      simpl in Hadd.
      rewrite (surjective_pairing (fold_right _ _ _)) in Hadd.
      inv Hadd. inv Heval.
      apply Env.find_In_gsso_opt.
      intro Hin; apply Hnin. setoid_rewrite ps_adds_spec; auto.
    - (* * Skip *)
      now inv Heval.
  Qed.

  (* NB: The following lemma is not true in general:

            forall tyenv s req t req' st al,
              No_Overwrites s ->
              add_defaults_stmt tyenv req s = (t, req', st, al) ->
              No_Overwrites t

         Because adding defaults to an Ifte may well introduce overwriting:

            w1 = (al2 ∩ req) — (al1 ∩ req)
            w2 = (al1 ∩ req) — (al2 ∩ req)
            w = ((st1 ∩ req) — w1) ∪ (st2 ∩ req) — w2
            ============================
            No_Overwrites
              (add_writes tyenv w
                (Ifte e (add_writes tyenv w1 t1) (add_writes tyenv w2 t2)))

         The writes of w are variables that are sometimes written by t1 or t2.
         Nothing prevents t1 from sometimes writing variables in w1.
         Nothing prevents t2 from sometimes writing variables in w2. *)

  Lemma wt_method_add_defaults:
    forall p insts mem m,
      wt_method p insts mem m ->
      wt_method (add_defaults p) insts mem m.
  Proof.
    unfold wt_method, meth_vars. intros * WTm.
    destruct m as [n ins vars outs s nodup good]; simpl in *.
    induction s; inv WTm; eauto using wt_stmt.
    match goal with H:find_class _ _ = Some _ |- _ =>
                    apply find_class_add_defaults_class in H end.
    match goal with H:find_method _ _ = Some _ |- _ =>
                    apply find_method_add_defaults_method in H;
                      rewrite find_method_map_add_defaults_method in H end.
    econstructor; eauto.
    now rewrite add_defaults_method_m_out.
    now rewrite add_defaults_method_m_in.
  Qed.

  Section AddDefaultsStmt.

    Variables (p : list class)
              (insts : list (ident * ident))
              (mems  : list (ident * type))
              (vars  : list (ident * type))
              (tyenv : ident -> option type).

    Hypothesis wf_vars_tyenv:
      (forall x ty, In (x, ty) vars <-> tyenv x = Some ty).

    Lemma wf_vars_tyenv':
      forall x, InMembers x vars <-> tyenv x <> None.
    Proof.
      split; intro HH.
      - apply InMembers_In in HH as (ty, HH).
        apply wf_vars_tyenv in HH. rewrite HH. discriminate.
      - apply not_None_is_Some in HH as (ty, HH).
        apply wf_vars_tyenv in HH. eauto using In_InMembers.
    Qed.

    Lemma add_writes_wt':
      forall W s,
        wt_stmt p insts mems vars (add_writes tyenv W s) ->
        wt_stmt p insts mems vars s.
    Proof.
      intros W.
      unfold add_writes. setoid_rewrite PS.fold_spec.
      generalize (PS.elements W); clear W.
      intro ws. induction ws as [|w ws IH]; simpl; auto.
      intros s Hwws. apply IH in Hwws.
      unfold add_write in Hwws.
      destruct (tyenv w); auto. now inv Hwws.
    Qed.

    Lemma add_writes_wt:
      forall W s,
        PS.For_all (fun x => tyenv x <> None) W ->
        (wt_stmt p insts mems vars s <->
         wt_stmt p insts mems vars (add_writes tyenv W s)).
    Proof.
      intros W.
      unfold add_writes. setoid_rewrite PS.fold_spec.
      setoid_rewrite PS_For_all_Forall.
      generalize (PS.elements W); clear W.
      intro ws. induction ws as [|w ws IH]; simpl. reflexivity.
      intros s Hwws.
      inversion_clear Hwws as [|? ? Hw Hws].
      rewrite <-IH; auto.
      apply not_None_is_Some in Hw as (ty & Hw).
      unfold add_write. rewrite Hw.
      apply wf_vars_tyenv in Hw.
      split; intro HH.
      - constructor; eauto; constructor; simpl; auto using wt_exp.
        now rewrite type_init_type.
      - now inversion HH.
    Qed.

    Lemma add_defaults_stmt_wt:
      forall s t req req' stimes always,
        add_defaults_stmt tyenv req s = (t, req', stimes, always) ->
        wt_stmt p insts mems vars s ->
        wt_stmt p insts mems vars t
        /\ PS.For_all (fun x => InMembers x vars) stimes
        /\ PS.For_all (fun x => InMembers x vars) always
        /\ PS.For_all (fun x => PS.In x req \/ InMembers x vars) req'.
    Proof.
      induction s; intros * Hadd WTs;
        try (injection Hadd; intros; subst always stimes req' t).
      - (* * Assign i e *)
        repeat split; auto using PS_For_all_empty; intros x Hin.
        + apply PS.singleton_spec in Hin; subst.
          inv WTs. eauto using In_InMembers.
        + apply PS.remove_spec in Hin as (? & ?); auto.
      - (* * AssignSt i e *)
        repeat split; auto using PS_For_all_empty. intros x Hin; auto.
      - (* * Ifte e s1 s2 *)
        inversion_clear WTs as [| |? ? ? ? ? Hwt1 Hwt2| | |].
        simpl in Hadd.

        set (defs1 := add_defaults_stmt tyenv PS.empty s1).
        assert (add_defaults_stmt tyenv PS.empty s1 = defs1) as Hdefs1
            by now subst defs1.
        rewrite Hdefs1 in Hadd.
        destruct defs1 as [[[t1 rq1] st1] al1].

        set (defs2 := add_defaults_stmt tyenv PS.empty s2).
        assert (add_defaults_stmt tyenv PS.empty s2 = defs2) as Hdefs2
            by now subst defs2.
        rewrite Hdefs2 in Hadd.
        destruct defs2 as [[[t2 rq2] st2] al2].

        injection Hadd; intros; subst always stimes req' t; clear Hadd.

        apply IHs1 with (2:=Hwt1) in Hdefs1 as (WTt1 & Hst1 & Hal1 & Hrq1).
        apply IHs2 with (2:=Hwt2) in Hdefs2 as (WTt2 & Hst2 & Hal2 & Hrq2).

        repeat split.
        + setoid_rewrite wf_vars_tyenv' in Hst1.
          setoid_rewrite wf_vars_tyenv' in Hst2.
          setoid_rewrite wf_vars_tyenv' in Hal1.
          setoid_rewrite wf_vars_tyenv' in Hal2.
          rewrite <-add_writes_wt;
            auto using PS_For_all_union, PS_For_all_diff, PS_For_all_inter.
          constructor; try rewrite <-add_writes_wt;
            auto using PS_For_all_union, PS_For_all_diff, PS_For_all_inter.
        + intros x HH. PS_split.
          repeat match goal with H:_ \/ _ |- _ => destruct H; PS_split end;
            match goal with
            | Hi:PS.In ?x ?S, Hf:PS.For_all _ ?S |- InMembers ?x _ =>
              now apply PS_In_Forall with (1:=Hf); auto end.
        + intros x HH. PS_split.
          repeat match goal with H:_ \/ _ |- _ => destruct H; PS_split end;
            match goal with
            | Hi:PS.In ?x ?S, Hf:PS.For_all _ ?S |- InMembers ?x _ =>
              now apply PS_In_Forall with (1:=Hf); auto end.
        + intros x HH. PS_split.
          repeat match goal with
                 | H:_ \/ _ |- _ => destruct H; PS_split
                 | Hi:PS.In ?x ?S, Hf:PS.For_all _ ?S |- _ =>
                   apply PS_In_Forall with (1:=Hf) in Hi as [?|?]
                 | H:PS.In _ PS.empty |- _ =>
                   now apply not_In_empty in H
                 end; auto.
      - (* * Comp s1 s2 *)
        inversion_clear WTs as [| | |? ? Hwt1 Hwt2| |].
        simpl in Hadd.
        set (defs2 := add_defaults_stmt tyenv req s2).
        assert (add_defaults_stmt tyenv req s2 = defs2) as Hdefs2 by now subst defs2.
        rewrite Hdefs2 in Hadd.
        destruct defs2 as [[[t2 rq2] stimes2] always2].

        set (defs1 := add_defaults_stmt tyenv rq2 s1).
        assert (add_defaults_stmt tyenv rq2 s1 = defs1) as Hdefs1 by now subst defs1.
        rewrite Hdefs1 in Hadd.
        destruct defs1 as [[[t1 rq1] stimes1] always1].

        injection Hadd; clear Hadd; intros; subst always stimes req' t.
        apply IHs1 with (2:=Hwt1) in Hdefs1 as (IHt1 & Hst1 & Hal1 & Hrq1).
        apply IHs2 with (2:=Hwt2) in Hdefs2 as (IHt2 & Hst2 & Hal2 & Hrq2).
        repeat split; eauto using wt_stmt,
                      PS_For_all_union, PS_For_all_diff, PS_For_all_diff.
        intros x Hin.
        apply PS_In_Forall with (1:=Hrq1) in Hin as [Hin|Hin]; auto.
      - (* * Call ys clsid o f es *)
        simpl in Hadd.
        rewrite (surjective_pairing (fold_right _ _ _)) in Hadd.
        inv Hadd. repeat split; auto using PS_For_all_empty; inv WTs.
        + econstructor; eauto; rewrite add_valid_add_valid', app_nil_r.
          * apply Forall2_map_1.
            match goal with H:Forall2 _ _ _ |- _ =>
                            apply Forall2_impl_In with (2:=H) end.
            intros e (x, ty) Hin1 Hin2 Htye; rewrite <-Htye. now destruct e.
          * apply Forall_map.
            match goal with H:Forall _ _ |- _ =>
                            apply Forall_impl_In with (2:=H) end.
            intros e Hin WTe. destruct e; simpl; inv WTe; auto using wt_exp.
        + apply PS_For_all_ps_adds; split; auto using PS_For_all_empty.
          apply Forall_forall.
          intros x Hin.
          match goal with H:Forall2 _ _ _ |- _ =>
            apply Forall2_in_left with (1:=H) in Hin as (xty & Hin1 & Hin2) end.
          eauto using In_InMembers.
        + unfold PS.For_all.
          match goal with H:Forall (wt_exp _ _) ?xs |- _ =>
            revert H; clear; induction l0 as [|e es IH] end; simpl; intros WT x Hin.
          now apply ps_removes_spec in Hin as (? & ?); auto.
          apply Forall_cons2 in WT as (WTe & WTes).
          destruct e; auto. simpl in Hin.
          inversion_clear WTe.
          apply PS.add_spec in Hin as [Hin|Hin]; subst; eauto using In_InMembers.
      - (* * Skip *)
        repeat split; auto using PS_For_all_empty; intros x Hin; auto.
    Qed.

    (* Having [wt_stmt] ensures that the number of variables to the left of a
       function call matches the number of function outputs, and allows us to
       conclude that all those variables are written to. *)

    Lemma add_defaults_stmt_inv2:
      forall s t me me' ve ve' req req' stimes always,
        add_defaults_stmt tyenv req s = (t, req', stimes, always) ->
        stmt_eval p me ve t (me', ve') ->
        wt_stmt p insts mems vars s ->
        (forall x, PS.In x req' -> Env.In x ve) ->
        (forall ome ome' clsid f vos rvos,
            Forall (fun vo => vo <> None) vos ->
            stmt_call_eval p ome clsid f vos ome' rvos ->
            Forall (fun x => x <> None) rvos) ->
        (forall x, ~PS.In x (PS.union stimes always) -> Env.find x ve' = Env.find x ve)
        /\ (forall x, PS.In x always -> Env.In x ve').
    Proof.
      intros * Hadd Heval Hwt Hre1 Hcall.
      revert t me me' ve ve' Heval req req' stimes always Hadd Hre1.
      induction s as [| | | |ys clsid o f es|];
        intros t me me' ve ve' Heval rq rq' st al Hadd Hre1.

      - (* * Assign i e *)
        inv Hadd. inv Heval.
        repeat split; auto using PSP.empty_inter_1.
        + intros x Hnin. rewrite Env.gso; auto.
          intro; now apply Hnin, PSF.union_3, PS.singleton_spec.
        + intros x Hin. apply PSP.FM.singleton_1 in Hin.
          apply Env.Props.P.F.add_in_iff; auto.

      - (* * AssignSt i e *)
        inv Hadd. inv Heval.
        setoid_rewrite PSF.empty_iff; intuition.

      - (* * Ifte e s1 s2 *)
        (* unfold the two recursive calls to add_defaults_stmt *)
        inversion Hadd as [Hadd']; clear Hadd.

        set (defs1 := add_defaults_stmt tyenv PS.empty s1).
        assert (add_defaults_stmt tyenv PS.empty s1 = defs1) as Hdefs1
            by now subst defs1.
        rewrite Hdefs1 in Hadd'.
        destruct defs1 as [[[t1 rq1] st1] al1].

        set (defs2 := add_defaults_stmt tyenv PS.empty s2).
        assert (add_defaults_stmt tyenv PS.empty s2 = defs2) as Hdefs2
            by now subst defs2.
        rewrite Hdefs2 in Hadd'.
        destruct defs2 as [[[t2 rq2] st2] al2].

        injection Hadd'; clear Hadd'. intros. subst al st rq' t.

        (* use typing to deduce that added writes are in tyenv *)
        inversion_clear Hwt as [| |? ? ? ? ? Hwt1 Hwt2| | |].
        specialize (IHs1 Hwt1). specialize (IHs2 Hwt2).
        pose proof (add_defaults_stmt_wt _ _ _ _ _ _ Hdefs1 Hwt1)
          as (Ht1 & HTst1 & HTal1 & HTreq1).
        pose proof (add_defaults_stmt_wt _ _ _ _ _ _ Hdefs2 Hwt2)
          as (Ht2 & HTst2 & HTal2 & HTreq2).
        clear Ht1 Ht2 Hwt1 Hwt2.
        setoid_rewrite wf_vars_tyenv' in HTst1.
        setoid_rewrite wf_vars_tyenv' in HTal1.
        setoid_rewrite wf_vars_tyenv' in HTst2.
        setoid_rewrite wf_vars_tyenv' in HTal2.

        apply stmt_eval_add_writes_split in Heval.
        destruct Heval as (meW & veW & HevalW & Heval).

        (* massage the stmt_evals *)
        inversion_clear Heval as [| | | |? ? ? ? ? ? ? ? ? ? ? ? Heval'|].
        assert (exists meW' veW',
                   stmt_eval p meW veW
                             (if b then add_writes tyenv ((al2 ∩ rq) — (al1 ∩ rq)) Skip
                              else add_writes tyenv ((al1 ∩ rq) — (al2 ∩ rq)) Skip)
                             (meW', veW')
                   /\ stmt_eval p meW' veW' (if b then t1 else t2) (me', ve'))
          as Heval'' by (destruct b;
                         apply stmt_eval_add_writes_split in Heval';
                         destruct Heval' as (meW' & veW' & HevalW' & Heval');
                         eauto).
        clear Heval'. destruct Heval'' as (meW' & veW' & HevalW' & Heval).

        (* factor out obligations for inductive hypotheses *)
        assert (forall x, (PS.In x rq1 \/ PS.In x rq2) -> Env.In x veW') as Hreq'.
        { intros x Hrq1.
          apply stmt_eval_mono' with (x:=x) in HevalW'; auto; clear HevalW'.
          now destruct b; apply No_Naked_Vars_add_writes; auto.
          match goal with H:stmt_eval _ _ _ (add_writes _ ?W Skip) _ |- _ =>
                          destruct (PSP.In_dec x W) as [Hw|Hnw] end.
          - apply stmt_eval_add_writes with (x:=x) in HevalW; auto.
            apply PS_For_all_union;
              auto using PS_For_all_diff, PS_For_all_inter.
          - apply stmt_eval_mono' with (x:=x) in HevalW; auto.
            now destruct b; apply No_Naked_Vars_add_writes; auto. intuition. }
        assert (forall x, PS.In x rq1 -> Env.In x veW') as Hreq1 by auto.
        assert (forall x, PS.In x rq2 -> Env.In x veW') as Hreq2 by auto.
        clear Hreq'.

        (* Put some structure back into the sets *)
        remember ((al2 ∩ rq) — (al1 ∩ rq)) as w1.
        remember ((al1 ∩ rq) — (al2 ∩ rq)) as w2.
        remember (((st1 ∩ rq) — w1) ∪ ((st2 ∩ rq) — w2)) as w.
        setoid_rewrite (simplify_write_sets w w1 w2 _ _ _ _ _ Heqw1 Heqw2 Heqw).
        split.
        + (* forall x, ~x ∈ (st ∪ al) -> Env.find x env' = Env.find x env *)
          intros x HH.
          repeat rewrite PS_not_union in HH.
          destruct HH as (Hnw & Hnw1 & Hnw2 & Hnal1 & Hnal2 & Hnst1 & Hnst2).
          destruct b.
          * clear IHs2; specialize (IHs1 _ _ _ _ _ Heval _ _ _ _ Hdefs1 Hreq1).
            destruct IHs1 as (IH1 & IH2).
            rewrite IH1; [|now apply PS_not_union; auto].
            rewrite stmt_eval_add_writes_Skip_other with (1:=HevalW'); auto.
            rewrite stmt_eval_add_writes_Skip_other with (1:=HevalW); auto.
          * clear IHs1; specialize (IHs2 _ _ _ _ _ Heval _ _ _ _ Hdefs2 Hreq2).
            destruct IHs2 as (IH1 & IH2).
            rewrite IH1; [|now apply PS_not_union; auto].
            rewrite stmt_eval_add_writes_Skip_other with (1:=HevalW'); auto.
            rewrite stmt_eval_add_writes_Skip_other with (1:=HevalW); auto.
        + (* forall x, x ∈ al -> Env.In x env' *)
          setoid_rewrite PS.union_spec.
          setoid_rewrite PS.inter_spec.
          setoid_rewrite PS.union_spec.
          pose proof (add_defaults_stmt_inv1 _ _ _ _ _ _ _ Hdefs1) as (H1A & H1B & H1C & H1D & H1E).
          pose proof (add_defaults_stmt_inv1 _ _ _ _ _ _ _ Hdefs2) as (H2A & H2B & H2C & H2D & H2E).
          intros x [[[Hal1|Hiw1] [Hal2|Hiw2]]|Hiw].
          * destruct b.
            now apply IHs1 with (2:=Hdefs1) (3:=Hreq1) in Heval as (? & ?); auto.
            now apply IHs2 with (2:=Hdefs2) (3:=Hreq2) in Heval as (? & ?); auto.
          * destruct b.
            now apply IHs1 with (2:=Hdefs1) (3:=Hreq1) in Heval as (? & ?); auto.
            apply stmt_eval_mono' with (x:=x) in Heval; auto.
            apply stmt_eval_add_writes with (x:=x) in HevalW'; auto.
            subst; auto using PS_For_all_diff, PS_For_all_inter.
          * destruct b.
            2:now apply IHs2 with (2:=Hdefs2) (3:=Hreq2) in Heval as (? & ?); auto.
            apply stmt_eval_mono' with (x:=x) in Heval; auto.
            apply stmt_eval_add_writes with (x:=x) in HevalW'; auto.
            subst; auto using PS_For_all_diff, PS_For_all_inter.
          * apply stmt_eval_mono' with (x:=x) in Heval; destruct b; auto;
              apply stmt_eval_add_writes with (x:=x) in HevalW';
              subst; auto using PS_For_all_diff, PS_For_all_inter.
          * apply stmt_eval_mono' with (x:=x) in Heval; [| |destruct b|]; auto.
            apply stmt_eval_mono' with (x:=x) in HevalW'; auto.
            now destruct b; apply No_Naked_Vars_add_writes; auto.
            apply stmt_eval_add_writes with (x:=x) in HevalW; auto.
            subst; apply PS_For_all_union;
              auto using PS_For_all_diff, PS_For_all_inter.

      - (* * Comp s1 s2 *)
        pose proof (add_defaults_stmt_inv1 _ _ _ _ _ _ _ Hadd) as (HIc & HId).

        inversion_clear Hwt as [| | |? ? Hwt1 Hwt2| |].
        specialize (IHs1 Hwt1). specialize (IHs2 Hwt2).
        clear Hwt1 Hwt2. inversion Hadd as [Hadd']; clear Hadd.

        (* unfold the two recursive calls to add_defaults_stmt *)
        set (defs2 := add_defaults_stmt tyenv rq s2).
        assert (add_defaults_stmt tyenv rq s2 = defs2) as Hdefs2 by now subst defs2.
        rewrite Hdefs2 in Hadd'.
        destruct defs2 as [[[t2 rq2] st2] al2].
        pose proof (add_defaults_stmt_inv1 _ _ _ _ _ _ _ Hdefs2)
          as (HI2c & HI2d & HI2e & HI2f & HI2g).

        set (defs1 := add_defaults_stmt tyenv rq2 s1).
        assert (add_defaults_stmt tyenv rq2 s1 = defs1) as Hdefs1 by now subst defs1.
        rewrite Hdefs1 in Hadd'.
        destruct defs1 as [[[t1 rq1] st1] al1].
        pose proof (add_defaults_stmt_inv1 _ _ _ _ _ _ _ Hdefs1)
          as (HI1c & HI1d & HI1e & HI1f & HI1g).

        injection Hadd'; clear Hadd'; intros; subst al st rq' t.

        (* massage the stmt_evals *)
        inv Heval.
        match goal with H1:stmt_eval _ _ _ t1 _, H2:stmt_eval _ _ _ t2 _ |- _ =>
                        specialize (IHs1 _ _ _ _ _ H1 _ _ _ _ Hdefs1 Hre1);
                          rename H1 into Heval1; clear Hdefs1 end.
        destruct IHs1 as (HI1a & HI1b).

        (* factor out obligations for inductive hypotheses *)
        assert (forall x, PS.In x rq2 -> Env.In x ve1) as Hre2.
        { intros x Hin. apply HI1d in Hin.
          destruct Hin as [|Hin]; eauto using stmt_eval_mono'. }
        match goal with H1:stmt_eval _ _ _ t1 _, H2:stmt_eval _ _ _ t2 _ |- _ =>
                        specialize (IHs2 _ _ _ _ _ H2 _ _ _ _ Hdefs2 Hre2);
                          rename H2 into Heval2; clear Hdefs2 end.
        destruct IHs2 as (HI2a & HI2b).

        split.
        + (* forall x, ~x ∈ (st ∪ al) -> Env.find x env' = Env.find x env *)
          intros x Hnin.
          cut (~PS.In x (PS.union (PS.union st1 al1) (PS.union st2 al2))).
          * intros Hnin'. repeat rewrite PS_not_union in Hnin'.
            destruct Hnin' as [[HH1 HH2] [HH3 HH4]].
            rewrite HI2a, HI1a; try rewrite PS_not_union; auto.
          * repeat rewrite PS_not_union in Hnin.
            destruct Hnin as [[HH1 HH2] [HH3 HH4]].
            rewrite PS.diff_spec in HH1, HH2.
            repeat setoid_rewrite PS.union_spec.
            destruct 1 as [[HH|HH]|[HH|HH]]; auto.
        + (* forall x, x ∈ al -> Env.In x env' *)
          intros x HH. apply PS.union_spec in HH.
          destruct HH; eauto using stmt_eval_mono'.

      - (* * Call ys clsid o f es *)
        simpl in Hadd.
        rewrite (surjective_pairing (fold_right _ _ _)) in Hadd.
        inv Hadd. inv Heval. split.
        + (* forall x, ~x ∈ (st ∪ al) -> Env.find x env' = Env.find x env *)
          intros x Hnin.
          apply Env.find_In_gsso_opt.
          rewrite PSP.empty_union_1, ps_adds_spec in Hnin; auto.
        + (* forall x, x ∈ al -> Env.In x env' *)
          assert (length ys = length rvos) as Hlys.
          { inv Hwt.
            match goal with Hfa:Forall2 _ ys _,
                                He:stmt_call_eval _ _ _ _ _ _ _ |- _ =>
                            apply Forall2_length in Hfa; rename Hfa into Hlen1;
                              inversion_clear He as [? ? ? ? ? ? ? ? ? ? ? ? ? ? ? Hlen2] end.
            rewrite Forall2_map_1 in Hlen2. apply Forall2_length in Hlen2.
            match goal with H1:find_class ?c ?p = Some _,
                               H2:find_class ?c ?p = Some _,
                                  H3:find_method _ _ = Some _,
                                     H4:find_method _ _ = Some _ |- _ =>
                            rename H1 into Hf1; rename H2 into Hf2;
                              rename H3 into Hm1; rename H4 into Hm2 end.
            rewrite Hf1 in Hf2; inv Hf2.
            rewrite Hm1 in Hm2; inv Hm2.
            now rewrite Hlen1, Hlen2. }

          assert (Forall2 (fun _ _ => True) ys rvos) as Hlys' by (apply Forall2_forall; auto).
          match goal with H:stmt_call_eval _ _ _ _ _ _ _ |- _ =>
                          apply Hcall in H; rename H into Hnn end.
          *{ intros x Hinadds.
             apply ps_adds_In in Hinadds; auto using not_In_empty.
             revert Hnn Hinadds Hlys'; clear; intros Hnn Hinadds Hlys'.
             induction Hlys'; inv Hinadds.
             - inversion_clear Hnn as [|? ? Hrvo Hrvos].
               apply not_None_is_Some in Hrvo. destruct Hrvo as (rv & Hrvo).
               rewrite Hrvo; simpl. apply Env.Props.P.F.add_in_iff; auto.
             - inversion_clear Hnn as [|? ? Hrvo Hrvos].
               apply not_None_is_Some in Hrvo. destruct Hrvo as (rv & Hrvo).
               rewrite Hrvo.
               rewrite Env.adds_opt_cons_cons.
               rewrite Env.Props.P.F.add_in_iff; auto using IHHlys'.
           }
          * match goal with H:Forall2 (exp_eval _ _) (fst _) vos |- _ =>
              rewrite add_valid_add_valid', app_nil_r in H; rename H into Hvos end.
            rewrite Forall2_map_1 in Hvos.
            apply Forall_forall. intros vo Hin.
            apply Forall2_in_right with (2:=Hin) in Hvos as (e & Hein & He).
            destruct e; simpl; inv He; discriminate.
      - (* * Skip *)
        inv Hadd. inv Heval.
        setoid_rewrite PSF.empty_iff; intuition.
    Qed.

    Definition in1_notin2 xs1 xs2 (ve1 ve2 : Env.t val) :=
      (forall x, PS.In x xs1 -> Env.In x ve1)
      /\ (forall x, PS.In x xs2 -> ~Env.In x ve2).

    Import Basics.

    Instance in1_notin2_Proper1:
      Proper (PS.Equal ==> PS.Equal ==> Env.refines eq ==> Env.refines eq --> impl)
             in1_notin2.
    Proof.
      intros S1 S2 HS12 T1 T2 HT12 ve0 ve0' Henv0 ve1 ve1' Henv1'.
      intros (HH1 & HH2); split.
      - intros x HS2. rewrite <-HS12 in HS2.
        setoid_rewrite Henv0 in HH1; auto.
      - intros x HT2. rewrite <-HT12 in HT2.
        setoid_rewrite Henv1' in HH2; auto.
    Qed.

    Instance in1_notin2_Proper2:
      Proper (PS.Equal ==> PS.Equal ==> eq ==> eq ==> iff) in1_notin2.
    Proof.
      intros S1 S2 HS12 T1 T2 HT12 ve0 ve0' Henv0 ve1 ve1' Henv1'; subst.
      split; intros (HH1 & HH2); split.
      - intros x HS2. rewrite <-HS12 in HS2; auto.
      - intros x HT2. rewrite <-HT12 in HT2; auto.
      - intros x HS1. rewrite HS12 in HS1; auto.
      - intros x HT1. rewrite HT12 in HT1; auto.
    Qed.

    Lemma in1_notin2_add1:
      forall ve1 ve2 x S1 S2,
        in1_notin2 (PS.add x S1) S2 ve1 ve2 ->
        in1_notin2 S1 S2 ve1 ve2 /\ Env.In x ve1.
    Proof.
      destruct 1 as (Hin1 & Hout2).
      repeat split; auto.
      now intros y Hin; apply Hin1, PS.add_spec; auto.
      now apply Hin1, PS.add_spec; auto.
    Qed.

    Lemma in1_notin2_Var_In:
      forall ve' ve es acc S,
        in1_notin2 (snd (fold_right add_valid acc es)) S ve' ve ->
        Forall (fun e => match e with Var x _ => Env.In x ve' | _ => True end) es.
    Proof.
      induction es as [|e es IH]; auto.
      intros acc S HH.
      destruct e; simpl in *; try (now apply IH in HH; auto).
      apply in1_notin2_add1 in HH as (HH & Hin).
      apply IH in HH; auto.
    Qed.

    Lemma in1_notin2_Var_Not_In:
      forall ys s1 s2 ve' ve,
        in1_notin2 s1 (ps_adds ys s2) ve' ve ->
        Forall (fun x => ~ Env.In x ve) ys.
    Proof.
      intros * (?& Hnin).
      apply Forall_forall; intros * Hin.
      apply Hnin, ps_adds_spec; auto.
    Qed.

    Lemma in1_notin2_infer:
      forall ve1 ve2 S1 S2 Z1 Z2,
        in1_notin2 S1 S2 ve1 ve2 ->
        (forall x, PS.In x Z1 -> PS.In x S1) ->
        (forall x, PS.In x Z2 -> PS.In x S2) ->
        in1_notin2 Z1 Z2 ve1 ve2.
    Proof.
      intros * (?, ?) ? ?; split; auto.
    Qed.

    Lemma stmt_eval_add_writes_Skip:
      forall me w ve0' ve0,
        ve0 ⊑ ve0' ->
        PS.For_all (fun x => ~Env.In x ve0) w ->
        PS.For_all (fun x => InMembers x vars) w ->
        exists ve1',
          ve0 ⊑ ve1'
          /\ stmt_eval p me ve0' (add_writes tyenv w Skip) (me, ve1')
          /\ (forall x, Env.In x ve0' -> Env.In x ve1')
          /\ PS.For_all (fun x => Env.In x ve1') w.
    Proof.
      intros me w.
      unfold add_writes.
      setoid_rewrite PSP.fold_spec_right.
      setoid_rewrite PS_For_all_Forall.
      setoid_rewrite (Permutation.Permutation_rev (PS.elements w)) at -3.
      remember (rev (PS.elements w)) as ws.
      setoid_rewrite <-Heqws; clear Heqws w.
      induction ws as [|w ws IH]; eauto using stmt_eval.
      intros ve0' ve0 Henv Hni Hm.
      inversion_clear Hni as [|? ? Hniw Hniws].
      inversion_clear Hm as [|? ? Hmw Hmws].
      apply wf_vars_tyenv', not_None_is_Some in Hmw as (wty & Hwty).
      simpl. unfold add_write at 1. rewrite Hwty.
      apply (Env.refines_add_right _ _ _ w (sem_const (init_type wty)))
        with (2:=Hniw) in Henv.
      apply IH with (1:=Henv) (2:=Hniws) in Hmws
        as (ve1' & Henv'' & Heval' & Hinin' & Hfa').
      exists ve1'. repeat (try apply Forall_cons2; split; eauto using stmt_eval);
                      intros; apply Hinin', Env.Props.P.F.add_in_iff; auto.
    Qed.

    Definition all_in1 (xs : list (ident * type)) (ve1 ve2 : Env.t val) :=
      (forall x, InMembers x xs <-> Env.In x ve1)
      /\ (forall x, Env.In x ve2 -> InMembers x xs).

    Lemma add_defaults_stmt_correct:
      forall p' s req t req' st al,
        program_refines (fun _ _ => all_in1) p p' ->
        (forall ome ome' clsid f vos rvos,
            Forall (fun vo => vo <> None) vos ->
            stmt_call_eval p ome clsid f vos ome' rvos ->
            Forall (fun x => x <> None) rvos) ->
        No_Overwrites s ->
        wt_stmt p insts mems vars s ->
        add_defaults_stmt tyenv req s = (t, req', st, al) ->
        stmt_refines p p' (in1_notin2 req' (PS.union st al)) t s.
    Proof.
      intros p' s rq t rq' st al Hpr Hcall Hno Hwt Hadd
             me ve1 ve2 me' ve2' Hpre Henv Heval.
      revert t rq rq' st al Hadd ve1 Henv Hpre.
      remember (me', ve2') as rr.
      assert (me' = fst rr /\ ve2' = snd rr) as (HR1 & HR2) by (subst; auto).
      rewrite HR1, HR2; clear Heqrr HR1 HR2 me' ve2'.
      induction Heval; simpl.
      - (* Assign x e *)
        intros t rq rq' st al Hadd ve1 Henv Hpre; inv Hadd.
        exists (Env.add x v ve1).
        eauto using Env.refines_add_both, exp_eval_refines, stmt_eval.
      - (* AssignSt x e *)
        intros t rq rq' st al Hadd ve1 Henv Hpre; inv Hadd.
        eauto using exp_eval_refines, stmt_eval.

      - (* Call ys clsid o f es *)
        intros t rq rq' st al Hadd ve1 Henv Hpre.
        rewrite (surjective_pairing (fold_right _ _ _)),
                 add_valid_add_valid', app_nil_r in Hadd.
        inv Hadd.
        match goal with H:Forall2 (exp_eval _ _) _ _ |- _ =>
          apply Forall2_exp_eval_refines_with_valid with (1:=Henv)
                          in H as (vos' & Heval1 & Hvos)
        end; eauto using in1_notin2_Var_In.
        match goal with H:stmt_call_eval _ _ _ _ _ _ _ |- _ =>
          apply program_refines_stmt_call_eval with (1:=Hpr) (4:=Hvos) in H
                          as (rvos' & Hcall' & Hrvos') end.
        { inv Hwt.
          exists (Env.adds_opt ys rvos' ve1); split; eauto using stmt_eval.
          apply env_refines_adds_opt; auto.
          simpl in *.
          eapply in1_notin2_Var_Not_In; eauto.
        }

        assert (Forall (fun vo => vo <> None) vos') as Hsome.
        { apply Forall_forall. intros x Hin.
          apply Forall2_in_right with (1:=Heval1) in Hin as (e & Hin & Heval).
          apply in_map_iff in Hin as (e' & Hvalid & Hin).
          destruct e'; inv Heval;
            match goal with H:_ = add_valid' _ |- _ => inv H end; discriminate. }

        intros * Hfindc Hfindm Hlvos Hlvos'; split.
        + setoid_rewrite fst_InMembers.
          rewrite <-(map_length fst m.(m_in)) in Hlvos'.
          revert Hsome Hlvos'; clear; revert vos'.
          induction (map fst m.(m_in)) as [|x xs IH]; simpl.
          * unfold Env.adds_opt, vempty; simpl; split; intro; try contradiction.
            eapply Env.Props.P.F.empty_in_iff; eauto.
          * intros vos' Hsome Hlen.
            destruct vos'. discriminate.
            apply Forall_cons2 in Hsome as (Hvo & Hsome).
            apply not_None_is_Some in Hvo as (v & Hv); subst.
            inversion Hlen as [Hlen'].
            setoid_rewrite (IH _ Hsome Hlen').
            setoid_rewrite Env.Props.P.F.in_find_iff.
            intro y; split.
            intros [Hin|Hin]; subst.
            now rewrite Env.find_gsss_opt; discriminate.
            destruct (ident_eq_dec y x); subst.
            now rewrite Env.find_gsss_opt; discriminate.
            now rewrite Env.find_gsso_opt; auto.
            intros Hfind.
            destruct (ident_eq_dec y x); subst; auto.
            rewrite Env.find_gsso_opt in Hfind; auto.
        + intros; eapply fst_InMembers, Env.In_adds_opt_In; eauto.

      - (* Comp s1 s2 *)
        rename a1 into s1, a2 into s2, ve into ve0.
        intros t rq rq' st al Hadd ve0' Henv0 Hpre.

        inversion_clear Hwt as [| | |? ? Hwt1 Hwt2| |].

        set (defs2 := add_defaults_stmt tyenv rq s2).
        assert (add_defaults_stmt tyenv rq s2 = defs2) as Hdefs2 by now subst defs2.
        rewrite Hdefs2 in Hadd.
        destruct defs2 as [[[t2 rq2] stimes2] always2].

        set (defs1 := add_defaults_stmt tyenv rq2 s1).
        assert (add_defaults_stmt tyenv rq2 s1 = defs1) as Hdefs1 by now subst defs1.
        rewrite Hdefs1 in Hadd.
        destruct defs1 as [[[t1 rq1] stimes1] always1].
        inv Hadd.
        assert (in1_notin2 rq' (stimes1 ∪ always1) ve0' ve0) as Hpre'.
        { apply in1_notin2_infer with (1:=Hpre); auto.
          now intros x ?; PS_split; destruct (PSP.In_dec x always2); intuition. }
        inversion_clear Hno as [| | | |? ? Hwnw1 Hwnw2 Hno1 Hno2|].
        specialize (IHHeval1 Hpr Hno1 Hwt1 _ _ _ _ _ Hdefs1 _ Henv0 Hpre').
        destruct IHHeval1 as (ve1' & Henv1' & Heval1').

        assert (in1_notin2 rq2 (stimes2 ∪ always2) ve1' ve1) as Hpre''.
        { pose proof (add_defaults_stmt_inv1 _ _ _ _ _ _ _ Hdefs1) as (HI1 & HI2 & HI3 & HI4 & HI5).
          pose proof (add_defaults_stmt_inv2 _ _ _ _ _ _ _ _ _ _ Hdefs1 Heval1') as (HI6 & HI8); auto.
          now intros y Hyin; apply Hpre in Hyin.
          assert (H:=Hpre); apply in1_notin2_infer
            with (Z1:=PS.diff rq2 always1) (Z2:=PS.union stimes2 always2)
            in H as (Hpre3 & Hpre4); [split| |].
          - intros x Hin.
            apply HI2 in Hin as [Hin|Hin]; auto. apply Hpre in Hin.
            apply stmt_eval_mono' with (3:=Heval1'); auto.
          - intros x Hin.
            pose proof (add_defaults_stmt_inv1 _ _ _ _ _ _ _ Hdefs2) as (H2A & H2B & H2C & H2D & H2E).
            specialize (H2C _ Hin); apply Hwnw2, HI4 in H2C.
            apply Hpre4 in Hin.
            apply add_defaults_stmt_no_write with (1:=Hdefs1) (3:=H2C) in Heval1.
            now rewrite Env.Props.P.F.in_find_iff, Heval1, <-Env.Props.P.F.in_find_iff.
          - intros x Hin. apply PS.diff_spec in Hin as (Hin & Hnin).
            apply HI2 in Hin as [Hin|Hin]; auto. contradiction.
          - intros x Hin. destruct (PSP.In_dec x always1). now intuition.
            PS_split; intuition. }

        specialize (IHHeval2 Hpr Hno2 Hwt2 _ _ _ _ _ Hdefs2 _ Henv1' Hpre'').
        destruct IHHeval2 as (ve2' & Henv2' & Heval2'); eauto using stmt_eval.

      - (* Ifte c et ef *)
        rename ve into ve0, ve' into ve3, ifTrue into s1, ifFalse into s2.
        intros t rq rq' st al Hadd ve0' Henv0' Hpre.

        inversion_clear Hwt as [| |? ? ? ? ? Hwt1 Hwt2| | |].

        set (defs1 := add_defaults_stmt tyenv PS.empty s1).
        assert (add_defaults_stmt tyenv PS.empty s1 = defs1) as Hdefs1
            by now subst defs1.
        rewrite Hdefs1 in Hadd.
        destruct defs1 as [[[t1 rq1] st1] al1].

        set (defs2 := add_defaults_stmt tyenv PS.empty s2).
        assert (add_defaults_stmt tyenv PS.empty s2 = defs2) as Hdefs2
            by now subst defs2.
        rewrite Hdefs2 in Hadd.
        destruct defs2 as [[[t2 rq2] st2] al2].

        pose proof (add_defaults_stmt_wt _ _ _ _ _ _ Hdefs1 Hwt1)
          as (Hwt1' & Hvst1 & Hval1 & Hreq1).
        pose proof (add_defaults_stmt_wt _ _ _ _ _ _ Hdefs2 Hwt2)
          as (Hwt2' & Hvst2 & Hval2 & Hreq2).

        inversion Hadd as [Hadd']; subst; clear Hadd.
        remember ((al2 ∩ rq) — (al1 ∩ rq)) as w1.
        remember ((al1 ∩ rq) — (al2 ∩ rq)) as w2.
        remember (((st1 ∩ rq) — w1) ∪ ((st2 ∩ rq) — w2)) as w.
        setoid_rewrite (simplify_write_sets w w1 w2 _ _ _ _ _ Heqw1 Heqw2 Heqw) in Hpre.

        inversion_clear Hno as [| |? ? ? Hno1 Hno2| | |].

        assert (PS.For_all (fun x => ~Env.In x ve0) w) as Hwenv0
            by (intros x Hin; apply Hpre; intuition).
        assert (PS.For_all (fun x => InMembers x vars) w) as Hwim
            by (now subst w; apply PS_For_all_union;
                apply PS_For_all_diff, PS_For_all_inter).
        destruct (stmt_eval_add_writes_Skip me w _ _ Henv0' Hwenv0 Hwim)
          as (ve1' & Henv1' & Heval1' & Hmono1 & Hin1').

        assert (PS.For_all (fun x => ~Env.In x ve0) (if b then w1 else w2)) as Hwenv1
            by (destruct b; intros x Hin; apply Hpre; intuition).
        assert (PS.For_all (fun x => InMembers x vars) (if b then w1 else w2)) as Hwim1
            by (now subst w1 w2; destruct b; apply PS_For_all_diff, PS_For_all_inter).
        destruct (stmt_eval_add_writes_Skip me (if b then w1 else w2)
                                            _ _ Henv1' Hwenv1 Hwim1)
          as (ve2' & Henv2' & Heval2' & Hmono2 & Hin2').

        assert (exists ve3',
          ve3 ⊑ ve3'
          /\ stmt_eval p me ve2' (if b then t1 else t2) (me', ve3'))
          as (ve3' & Henv3' & Heval3').
        { destruct b.
          - apply (IHHeval Hpr Hno1 Hwt1 _ _ _ _ _ Hdefs1 _ Henv2').
            destruct Hpre as (Hpre1 & Hpre2); split.
            + intros x Hrq1.
              destruct (PSP.In_dec x w1) as [Hw1|Hnw1].
              now apply PS_In_Forall with (1:=Hin2') (2:=Hw1).
              apply (Hmono2 x).
              destruct (PSP.In_dec x w) as [Hw|Hnw].
              now apply PS_In_Forall with (1:=Hin1') (2:=Hw).
              apply (Hmono1 x). apply Hpre1. intuition.
            + intros x Hin. apply Hpre2. PS_split; tauto.
          - apply (IHHeval Hpr Hno2 Hwt2 _ _ _ _ _ Hdefs2 _ Henv2').
            destruct Hpre as (Hpre1 & Hpre2); split.
            + intros x Hrq2.
              destruct (PSP.In_dec x w2) as [Hw2|Hnw2].
              now apply PS_In_Forall with (1:=Hin2') (2:=Hw2).
              apply (Hmono2 x).
              destruct (PSP.In_dec x w) as [Hw|Hnw].
              now apply PS_In_Forall with (1:=Hin1') (2:=Hw).
              apply (Hmono1 x). apply Hpre1. intuition.
            + intros x Hin. apply Hpre2. PS_split; tauto. }

        exists ve3'; split; auto.
        apply stmt_eval_add_writes_split.
        exists me, ve1'; split; auto.
        econstructor; eauto using exp_eval_refines.
        destruct b; apply stmt_eval_add_writes_split; eauto.

      - (* skip *)
        inversion_clear 1; eauto using stmt_eval.
    Qed.

  End AddDefaultsStmt.


  Lemma output_or_local_in_typing_env:
    forall {A} (min mvars mout : list (ident * A)) S,
      NoDupMembers (min ++ mvars ++ mout) ->
      PS.For_all
        (fun x => PS.In x (ps_adds (map fst mout) PS.empty) \/
                  InMembers x (min ++ mvars ++ mout)) S ->
      PS.For_all (fun x => Env.find x (Env.from_list (min ++ mvars ++ mout)) <> None)
                 (ps_removes (map fst min) S).
  Proof.
    intros A min mvars mout S Hmndup HS x Hin.
    apply ps_removes_spec in Hin as (Hnin & Hin).
    apply PS_In_Forall with (1:=HS) in Hin as [Hin|Hin].
    - apply ps_adds_spec in Hin as [Hin|Hin]; try not_In_empty.
      apply in_map_iff in Hin as ((y & yty) & Heq & Hin).
      do 2 (eapply or_intror, in_app in Hin).
      eapply Env.In_find_adds' in Hin; eauto.
      subst. apply not_None_is_Some; eauto.
    - apply InMembers_In in Hin as (xty & Hin).
      eapply Env.In_find_adds' in Hin; eauto.
      apply not_None_is_Some; eauto.
  Qed.

  Lemma stmt_call_eval_add_defaults_class_not_None:
    forall p,
      wt_program p ->
      forall ome ome' clsid f vos rvos,
        Forall (fun vo => vo <> None) vos ->
        stmt_call_eval (add_defaults p) ome clsid f vos ome' rvos ->
        Forall (fun x => x <> None) rvos.
  Proof.
    induction p as [|c p' IH]; simpl. now inversion 3.
    intros WTp ome ome'' clsid f vos rvos Hvos Heval.
    inversion_clear WTp as [|? ? WTc WTp' Hpnd].
    specialize (IH WTp').
    destruct (ident_eq_dec c.(c_name) clsid) as [He|Hne].
    - destruct c as (name, mems, objs, methods, Hnodup, Hnodupm, Hgood).
      simpl in *.
      inversion_clear Heval as [? ? ? ? ? ? ? ? ve'' ? ? Hfindc Hfindm Hlvos Heval' Hrvos].
      subst name. simpl in Hfindc. rewrite ident_eqb_refl in Hfindc.
      inv Hfindc. simpl in Hfindm.
      apply find_method_map_add_defaults_method' in Hfindm as (fm' & Hfindm' & Hfm').
      subst fm.
      inversion_clear WTc as [Hfao WTms]. clear Hfao; simpl in WTms.
      induction methods as [|m methods' IHm]. discriminate.
      apply Forall_cons2 in WTms as (WTm & WTms).
      apply NoDup_cons' in Hnodupm as (Hnodupm1 & Hnodupm2).
      simpl in Hfindm'.
      destruct (ident_eqb m.(m_name) f); [clear IHm|apply IHm; auto].
      clear Hnodupm1 Hnodupm2. inv Hfindm'.
      destruct fm' as (mname, min, mvars, mout, mbody, Hmndup, Hmgood).
      simpl in *.

      assert (Env.adds' mout (Env.adds' mvars (Env.from_list min))
              = Env.from_list (min ++ mvars ++ mout)) as Hpmeq
          by (now unfold Env.from_list; repeat rewrite Env.adds'_app).
      rewrite Hpmeq in Heval'; clear Hpmeq.

      remember (add_defaults_stmt
                  (fun x => Env.find x (Env.from_list (min ++ mvars ++ mout)))
                  (ps_adds (map fst mout) PS.empty) mbody) as defs.
      symmetry in Heqdefs.
      setoid_rewrite Heqdefs in Heval'.
      destruct defs as [[[t req'] stimes] always].

      apply stmt_eval_add_writes_split in Heval' as (ome' & ve' & Heval & Heval').

      pose proof (add_defaults_stmt_inv1 _ _ _ _ _ _ _ Heqdefs)
        as (HH1 & Halreq' & HH2 & HH3 & HH4); clear HH1 HH2 HH3.

      assert (forall x ty,
                 In (x, ty) (min ++ mvars ++ mout) <->
                 Env.find x (Env.from_list (min ++ mvars ++ mout)) = Some ty) as Hinf
        by (split; [apply Env.In_find_adds'|apply Env.from_list_find_In]; auto).
      apply wt_method_add_defaults in WTm.
      unfold wt_method, meth_vars in WTm; simpl in WTm.

      pose proof (add_defaults_stmt_wt _ _ _ _ _ Hinf _ _ _ _ _ _ Heqdefs WTm)
          as (WTt & WTst & WTal & Hreq').

      assert (forall x, PS.In x (ps_removes (map fst min) req') -> Env.In x ve')
        as Hreq'in
          by (intros x Hin; apply stmt_eval_add_writes with (x:=x) in Heval;
              auto using output_or_local_in_typing_env).

      eapply add_defaults_stmt_inv2 in Heqdefs as (Hstal & Hal); eauto.
      + apply Forall_forall; intros x Hin.
        apply Forall2_in_right with (1:=Hrvos) in Hin as (xo & Hin & Hfind).
        assert (~In xo (map fst min)) as Hnmin.
        { intros Hin'. apply fst_InMembers in Hin'.
          apply fst_InMembers in Hin.
          apply NoDupMembers_app_InMembers with (1:=Hmndup) in Hin'.
          apply Hin', InMembers_app; auto. }
        eapply or_introl, ps_adds_spec, Halreq' in Hin as [Hin|Hin].
        * apply Hal, Env.Props.P.F.in_find_iff in Hin. now rewrite Hfind in Hin.
        * apply (conj Hnmin), ps_removes_spec, Hreq'in in Hin.
          apply stmt_eval_mono' with (3:=Heval') in Hin; auto.
          now apply Env.Props.P.F.in_find_iff in Hin; rewrite Hfind in Hin.
      + intros x Hin.
        destruct (In_dec ident_eq_dec x (map fst min)) as [Him|Hnim].
        * cut (Env.In x (Env.adds_opt (map fst min) vos vempty)).
          intro Hii; apply stmt_eval_mono' with (3:=Heval) in Hii; auto.
          now apply No_Naked_Vars_add_writes; auto.
          revert Him Hvos Hlvos; clear.
          rewrite <-(map_length fst). revert vos.
          induction (map fst min) as [|y ys IH].
          now intros vos Him; apply in_nil in Him.
          intros vos Him Hvos Hlvos.
          destruct vos as [|vo vos]. discriminate.
          apply Forall_cons2 in Hvos as (Hvo & Hvos).
          apply not_None_is_Some in Hvo as (v & Hvo); subst.
          apply Env.Props.P.F.in_find_iff.
          inv Him. now rewrite Env.find_gsss_opt. inv Hlvos.
          destruct (ident_eq_dec x y). now subst; rewrite Env.find_gsss_opt.
          rewrite Env.find_gsso_opt; simpl; auto.
          apply Env.Props.P.F.in_find_iff; auto.
        * now apply (conj Hnim), ps_removes_spec, Hreq'in in Hin.
    - assert ((add_defaults_class c).(c_name) <> clsid) as Hne'
          by (destruct c; auto).
      rewrite stmt_call_eval_cons in Heval; eauto.
  Qed.

  Lemma wt_add_defaults_method:
    forall p objs mems m,
      wt_method p objs mems m ->
      wt_method p objs mems (add_defaults_method m).
  Proof.
    unfold wt_method, meth_vars.
    intros p objs mems m WTm.
    rewrite add_defaults_method_m_in,
            add_defaults_method_m_out,
            add_defaults_method_m_vars.
    destruct m as [n min mvars mout s Hnodup Hgood]; simpl in *.

    assert (Env.adds' mout (Env.adds' mvars (Env.from_list min))
            = Env.from_list (min ++ mvars ++ mout)) as Hpmeq
        by (now unfold Env.from_list; repeat rewrite Env.adds'_app).
    rewrite Hpmeq; clear Hpmeq.

    remember (add_defaults_stmt
                (fun x => Env.find x (Env.from_list (min ++ mvars ++ mout)))
                (ps_adds (map fst mout) PS.empty) s) as defs.
    symmetry in Heqdefs.
    setoid_rewrite Heqdefs.
    destruct defs as [[[t req'] stimes] always].

    assert (forall x ty,
               In (x, ty) (min ++ mvars ++ mout) <->
               Env.find x (Env.from_list (min ++ mvars ++ mout)) = Some ty) as Hinf
        by (split; [apply Env.In_find_adds'|apply Env.from_list_find_In]; auto).

    apply add_defaults_stmt_wt with (1:=Hinf) (2:=Heqdefs) in WTm.
    destruct WTm as (WTt & HH1 & HH2 & Hreq'); clear HH1 HH2.

    apply add_writes_wt; auto.
    apply output_or_local_in_typing_env; auto.
  Qed.

  Lemma wt_mem_add_defaults:
    forall p c me,
      wt_mem me p c ->
      wt_mem me (add_defaults p) (add_defaults_class c).
  Proof.
    induction 1 as [???? WTmem_inst IH| |] using wt_mem_ind_mult
      with (Pinst := fun me P oc WT_mem_inst => wt_mem_inst me (add_defaults P) oc).
    - constructor.
      + destruct cl; auto.
      + assert (c_objs (add_defaults_class cl) = c_objs cl) as E
            by (destruct cl; auto).
        rewrite E; clear E.
        induction (c_objs cl) as [|(o, c)]; inv WTmem_inst; auto.
        inversion_clear IH as [|?? (?&?)].
        constructor; eauto.
    - constructor; auto.
    - eright; eauto.
      apply find_class_add_defaults_class; auto.
  Qed.

  Lemma wt_add_defaults_class:
    forall p,
      wt_program p ->
      wt_program (add_defaults p).
  Proof.
    induction p as [|c p' IH]; auto.
    inversion_clear 1 as [|? ? WTc WTp Hpnd].
    specialize (IH WTp).
    inversion_clear WTc as [Hfobs WTms].
    simpl. constructor; auto.
    - constructor.
      + rewrite add_defaults_class_c_objs.
        apply Forall_impl_In with (2:=Hfobs).
        intros. now apply find_class_add_defaults_class_not_None.
      + rewrite add_defaults_class_c_mems, add_defaults_class_c_objs.
        destruct c as (name, mems, objs, methods, Hnodup, Hnodupm, Hgood); simpl in *.
        apply Forall_map, Forall_impl_In with (2:=WTms).
        intros m Him WTm. apply wt_method_add_defaults.
        now apply wt_add_defaults_method.
    - unfold add_defaults.
      apply Forall_map.
      now setoid_rewrite add_defaults_class_c_name.
  Qed.

  Lemma add_defaults_stmt_refines:
    forall p1 p2 insts mems m,
      program_refines (fun _ _ => all_in1) p1 p2 ->
      wt_method p2 insts mems m ->
      No_Overwrites m.(m_body) ->
      Forall (fun x => ~Can_write_in x m.(m_body)) (map fst m.(m_in)) ->
      (forall ome ome' clsid f vos rvos,
          Forall (fun vo => vo <> None) vos ->
          stmt_call_eval p1 ome clsid f vos ome' rvos ->
          Forall (fun x => x <> None) rvos) ->
      stmt_refines p1 p2
                   (in1_notin2 (PSP.of_list (map fst m.(m_in)))
                               (PSP.of_list (map fst (m.(m_out) ++ m.(m_vars)))))
                   (add_defaults_method m).(m_body) m.(m_body).
  Proof.
    unfold wt_method, meth_vars; intros p1 p2 insts mems m Hpr WT;
      destruct m as [n ins vars outs s nodup good]; simpl in *.
    unfold Env.from_list; repeat rewrite Env.adds'_app;
      fold (@Env.from_list type (outs ++ vars ++ ins)).
    match goal with |- context [ add_defaults_stmt ?tyenv ?W s ] =>
      set (defs := add_defaults_stmt tyenv W s);
        assert (add_defaults_stmt tyenv W s = defs) as Hdefs by now subst defs
    end.
    destruct defs as [[[t rq'] st] al].
    intros Hnoo Hncwin Hcall me ve1' ve1 me' ve2 Hpre Henv Heval.
    apply wt_stmt_program_refines with (1:=Hpr) in WT.

    assert (forall x ty,
      In (x, ty) (ins ++ vars ++ outs) <->
      Env.find x (Env.adds' (ins ++ vars ++ outs) (Env.empty _)) = Some ty)
      as Htyenv.
    { split; intro HH.
      now apply Env.In_find_adds'.
      now apply Env.from_list_find_In in HH. }

    assert (WT':=WT); eapply add_defaults_stmt_wt with (1:=Htyenv) (2:=Hdefs) in WT'
      as (WTt & Hvst & Hval & Hrq').

    assert (PS.For_all (fun x => InMembers x (ins ++ vars ++ outs))
                       (ps_removes (map fst ins) rq')) as Hrq''.
    { intros x Hin.
      apply ps_removes_spec in Hin as (Hnin & Hin).
      apply PS_In_Forall with (1:=Hrq') in Hin as [Hin|Hin]; auto.
      do 2 (apply InMembers_app; right). apply fst_InMembers.
      apply ps_adds_spec in Hin as [Hin|Hin]; try not_In_empty; auto. }

    destruct Hpre as (Hpre1 & Hpre2).
    assert (PS.For_all (fun x => ~Env.In x ve1) (ps_removes (map fst ins) rq')).
    { intros x Hin.
      apply PS_In_Forall with (2:=Hin) in Hrq''.
      apply Hpre2. rewrite <-ps_adds_of_list.
      apply ps_adds_spec; left; apply fst_InMembers.
      setoid_rewrite (Permutation.Permutation_app_comm outs vars).
      apply InMembers_app in Hrq'' as [Hrq''|Hrq'']; auto.
      apply ps_removes_spec in Hin as (Hnin & Hin).
      apply fst_InMembers in Hrq''; contradiction. }

    eapply stmt_eval_add_writes_Skip with (1:=Htyenv) (p:=p1) (me:=me)
                                          (w:=ps_removes (map fst ins) rq')
      in Henv as (ve2' & Henv2' & Heval2' & Hmono2 & Hin2'); eauto.

    assert (Hsr:=Hdefs); eapply add_defaults_stmt_correct in Hsr; eauto.

    pose proof (add_defaults_stmt_inv1 _ _ _ _ _ _ _ Hdefs)
      as (HI1 & HI2 & HI3 & HI4).

    assert (in1_notin2 rq' (st ∪ al) ve2' ve1) as Hinout.
    { split.
      - intros x Hin.
        destruct (In_dec ident_eq_dec x (map fst ins)) as [Hiin|].
        + apply Hmono2, Hpre1, PSP.of_list_1, SetoidList.InA_alt; eauto.
        + assert (PS.In x (ps_removes (map fst ins) rq')) as Hinrq'
              by (apply ps_removes_spec; auto).
          now apply PS_In_Forall with (1:=Hin2') in Hinrq'.
      - intros x Hin.
        apply Hpre2, PSP.of_list_1, Env.ME.MO.ListIn_In, fst_InMembers.
        specialize (HI3 _ Hin).
        setoid_rewrite (Permutation.Permutation_app_comm outs vars).
        apply PS.union_spec in Hin as [Hin|Hin].
        + apply PS_In_Forall with (1:=Hvst) in Hin.
          apply InMembers_app in Hin.
          destruct Hin as [Hin|]; auto.
          apply InMembers_Forall with (1:=Hncwin) in Hin.
          contradiction.
        + apply PS_In_Forall with (1:=Hval) in Hin.
          apply InMembers_app in Hin.
          destruct Hin as [Hin|]; auto.
          apply InMembers_Forall with (1:=Hncwin) in Hin.
          contradiction. }

    eapply Hsr in Heval as (ve3' & Henv3' & Heval3'); eauto.

    exists ve3'; split; auto.
    apply stmt_eval_add_writes_split; eauto.
  Qed.

  Lemma No_Naked_Vars_add_defaults_method:
    forall m, No_Naked_Vars (add_defaults_method m).(m_body).
  Proof.
    destruct m as [n ins vars outs s nodup good]; simpl.
    match goal with |- context [ add_defaults_stmt ?tyenv ?W s ] =>
      set (defs := add_defaults_stmt tyenv W s);
        assert (add_defaults_stmt tyenv W s = defs) as Hdefs by now subst defs
    end.
    destruct defs as [[[t rq'] st] al].
    pose proof (add_defaults_stmt_inv1 _ _ _ _ _ _ _ Hdefs)
      as (HI1 & HI2 & HI3 & HI4 & HI5).
    now apply No_Naked_Vars_add_writes.
  Qed.

  Lemma add_defaults_method_refines:
    forall p1 p2 insts mems m,
      program_refines (fun _ _ => all_in1) p1 p2 ->
      wt_method p2 insts mems m ->
      No_Overwrites m.(m_body) ->
      Forall (fun x => ~ Can_write_in x m.(m_body)) (map fst m.(m_in)) ->
      (forall ome ome' clsid f vos rvos,
          Forall (fun vo => vo <> None) vos ->
          stmt_call_eval p1 ome clsid f vos ome' rvos ->
          Forall (fun x => x <> None) rvos) ->
      method_refines p1 p2 all_in1 (add_defaults_method m) m.
  Proof.
    intros * Hpr WTm Hnoo Hncwi Hcall.
    unfold method_refines.
    rewrite add_defaults_method_m_in, add_defaults_method_m_out.
    repeat split; auto.
    eapply add_defaults_stmt_refines
      with (2:=WTm) (3:=Hnoo) (4:=Hncwi) (5:=Hcall) in Hpr.
    apply stmt_refines_strengthen with (1:=Hpr).
    intros ve1 ve2 (Hpre1 & Hpre2).
    split; setoid_rewrite In_of_list_InMembers.
    now apply Hpre1.
    intros x Hin.
    rewrite Permutation.Permutation_app_comm in Hin.
    apply NoDupMembers_app_InMembers with (ws:=m.(m_in)) in Hin; auto.
    rewrite Permutation.Permutation_app_comm. apply m_nodupvars.
  Qed.

  Lemma add_defaults_class_refines:
    forall p1 p2 c,
      program_refines (fun _ _ => all_in1) p1 p2 ->
      wt_class p2 c ->
      Forall (fun m => No_Overwrites m.(m_body)) c.(c_methods) ->
      Forall (fun m => Forall (fun x => ~ Can_write_in x m.(m_body))
                              (map fst m.(m_in))) c.(c_methods) ->
      (forall ome ome' clsid f vos rvos,
          Forall (fun vo => vo <> None) vos ->
          stmt_call_eval p1 ome clsid f vos ome' rvos ->
          Forall (fun x => x <> None) rvos) ->
      class_refines p1 p2 (fun _ => all_in1) (add_defaults_class c) c.
  Proof.
    intros p1 p2 c Hpr WTc Hnoo Hncwm Hcall f fm Hfind.
    apply wt_class_find_method with (2:=Hfind) in WTc.
    rewrite add_defaults_class_find_method, Hfind; simpl.
    pose proof (find_method_In _ _ _ Hfind) as Hin.
    exists (add_defaults_method fm). split; auto.
    apply Forall_forall with (2:=Hin) in Hnoo.
    apply Forall_forall with (2:=Hin) in Hncwm.
    eapply add_defaults_method_refines; eauto.
  Qed.

  Lemma add_defaults_program_refines:
    forall p,
      wt_program p ->
      Forall_methods (fun m => No_Overwrites m.(m_body)) p ->
      Forall_methods (fun m => Forall (fun x => ~ Can_write_in x m.(m_body))
                                      (map fst m.(m_in))) p ->
      program_refines (fun _ _ => all_in1) (add_defaults p) p.
  Proof.
    intros p WTp Hnoo Hncw.
    cut (Forall2 (fun c1 c2 => c1 = add_defaults_class c2)
                 (add_defaults p) p).
    2:now apply Forall2_map_1, Forall2_same, Forall_forall.
    apply program_refines_by_class' with (1:=WTp).
    apply all_In_Forall2.
    now unfold add_defaults; rewrite map_length.
    intros c1 c2 Hin p1' p2' WTp' WTc Hpr Hadc Hx; subst.
    rewrite add_defaults_class_c_name; split; auto.
    apply in_combine_r in Hin.
    apply Forall_forall with (2:=Hin) in Hnoo.
    apply Forall_forall with (2:=Hin) in Hncw.
    apply add_defaults_class_refines with (1:=Hpr); auto.
    assert (p1' = add_defaults p2') as Hp1'
        by (now clear Hpr WTp' WTc; induction Hadc; auto; subst; simpl).
    subst. now apply stmt_call_eval_add_defaults_class_not_None.
  Qed.

  Lemma No_Naked_Vars_add_defaults_class:
    forall p,
      Forall_methods (fun m => No_Naked_Vars m.(m_body)) (add_defaults p).
  Proof.
    intros p.
    apply Forall_forall; intros c' Hcin.
    unfold add_defaults in *; apply in_map_iff in Hcin as (c & Hc' & Hcin); subst.
    apply Forall_forall; intros m' Hmin.
    destruct c as (name, mems, objs, methods, Hnodup, Hnodupm, Hgood); simpl in *.
    apply in_map_iff in Hmin as (m & Hm & Hmin); subst.
    apply No_Naked_Vars_add_defaults_method.
  Qed.

  Theorem stmt_call_eval_add_defaults:
    forall p me f m vs me' rvs,
      wt_program p ->
      Forall_methods (fun m => No_Overwrites m.(m_body)) p ->
      Forall_methods (fun m => Forall (fun x => ~ Can_write_in x m.(m_body))
                                      (map fst m.(m_in))) p ->
      stmt_call_eval p me f m (map Some vs) me' (map Some rvs) ->
      stmt_call_eval (add_defaults p) me f m (map Some vs) me' (map Some rvs).
  Proof.
    intros * WTp NOO NCW Call.
    eapply program_refines_stmt_call_eval in Call as (rvos &?& Spec);
      eauto using add_defaults_program_refines.
    - assert (rvos = map Some rvs) as ->; eauto.
      rewrite Forall2_map_2 in Spec.
      clear - Spec; induction Spec; simpl; auto; f_equal; auto.
    - split;
        rewrite Env.adds_opt_is_adds; try apply fst_NoDupMembers, m_nodupin; intro;
          rewrite Env.In_adds_spec, fst_InMembers, Env.Props.P.F.empty_in_iff; intuition;
            now rewrite map_length in *.
    - apply Forall2_same, Forall_forall; auto.
  Qed.

  Corollary loop_call_add_defaults:
    forall f c ins outs p me,
      wt_program p ->
      Forall_methods (fun m => No_Overwrites m.(m_body)) p ->
      Forall_methods (fun m => Forall (fun x => ~ Can_write_in x m.(m_body))
                                      (map fst m.(m_in))) p ->
      loop_call p c f (fun n => map Some (ins n)) (fun n => map Some (outs n)) 0 me ->
      loop_call (add_defaults p) c f (fun n => map Some (ins n)) (fun n => map Some (outs n)) 0 me.
  Proof.
    intros ?????; generalize 0%nat.
    cofix COINDHYP.
    intros n me WTp NOO NCW Hdo.
    destruct Hdo.
    econstructor; eauto using stmt_call_eval_add_defaults.
  Qed.

End OBCADDDEFAULTS.

Module ObcAddDefaultsFun
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op)
       (Import SynObc: Velus.Obc.ObcSyntax.OBCSYNTAX         Ids Op OpAux)
       (Import SemObc: Velus.Obc.ObcSemantics.OBCSEMANTICS   Ids Op OpAux SynObc)
       (Import InvObc: Velus.Obc.ObcInvariants.OBCINVARIANTS Ids Op OpAux SynObc SemObc)
       (Import TypObc: Velus.Obc.ObcTyping.OBCTYPING         Ids Op OpAux SynObc SemObc)
       (Import Equ   : Velus.Obc.Equiv.EQUIV                 Ids Op OpAux SynObc SemObc TypObc)
       <: OBCADDDEFAULTS Ids Op OpAux SynObc SemObc InvObc TypObc Equ.

  Include OBCADDDEFAULTS Ids Op OpAux SynObc SemObc InvObc TypObc Equ.

End ObcAddDefaultsFun.
