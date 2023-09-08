From Coq Require Import PArith.
From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Velus Require Import Common.
From Velus Require Import CommonProgram.
From Velus Require Import CommonTyping.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import StaticEnv.
From Velus Require Import Lustre.LSyntax.

(** * Ordering of Lustre nodes *)

(**

The compilation of a whole program is only correct if that program satisfies
the [Ordered_nodes] predicate, which states that a node may only call nodes
that were defined earlier.

 *)

Module Type LORDERED
       (Ids         : IDS)
       (Op          : OPERATORS)
       (OpAux       : OPERATORS_AUX Ids Op)
       (Cks         : CLOCKS Ids Op OpAux)
       (Senv        : STATICENV Ids Op OpAux Cks)
       (Import Syn  : LSYNTAX Ids Op OpAux Cks Senv).

  Inductive Is_node_in_exp : ident -> exp -> Prop :=
  | INEunop: forall f op e a,
      Is_node_in_exp f e -> Is_node_in_exp f (Eunop op e a)
  | INEbinop: forall f op e1 e2 a,
      Is_node_in_exp f e1 \/ Is_node_in_exp f e2 ->
      Is_node_in_exp f (Ebinop op e1 e2 a)
  | INEextcall: forall f g es a,
      Exists (Is_node_in_exp f) es ->
      Is_node_in_exp f (Eextcall g es a)
  | INEfby: forall f le1 le2 la,
      Exists (Is_node_in_exp f) le1 \/ Exists (Is_node_in_exp f) le2 ->
      Is_node_in_exp f (Efby le1 le2 la)
  | INEarrow: forall f le1 le2 la,
      Exists (Is_node_in_exp f) le1 \/ Exists (Is_node_in_exp f) le2 ->
      Is_node_in_exp f (Earrow le1 le2 la)
  | INEwhen: forall f le x b la,
      Exists (Is_node_in_exp f) le ->
      Is_node_in_exp f (Ewhen le x b la)
  | INEmerge: forall f x es la,
      Exists (fun es => Exists (Is_node_in_exp f) (snd es)) es ->
      Is_node_in_exp f (Emerge x es la)
  | INEcase: forall f e es d la,
      Is_node_in_exp f e
      \/ Exists (fun es => Exists (Is_node_in_exp f) (snd es)) es
      \/ (exists d0, d = Some d0 /\ Exists (Is_node_in_exp f) d0) ->
      Is_node_in_exp f (Ecase e es d la)
  | INEapp1: forall f g le ler a,
      Exists (Is_node_in_exp f) le \/
      Exists (Is_node_in_exp f) ler ->
      Is_node_in_exp f (Eapp g le ler a)
  | INEapp2: forall f le ler a, Is_node_in_exp f (Eapp f le ler a).

  Definition Is_node_in_eq (f: ident) (eq: equation) : Prop :=
    List.Exists (Is_node_in_exp f) (snd eq).

  Inductive Is_node_in_scope {A} (P_in : A -> Prop) (f : ident) : scope A -> Prop :=
  | INScope : forall locs blks,
      P_in blks ->
      Is_node_in_scope P_in f (Scope locs blks).

  Inductive Is_node_in_branch {A} (P_in : A -> Prop) : branch A -> Prop :=
  | INBranch : forall caus blks,
      P_in blks ->
      Is_node_in_branch P_in (Branch caus blks).

  Inductive Is_node_in_block (f: ident) : block -> Prop :=
  | INBeq: forall eq,
      Is_node_in_eq f eq ->
      Is_node_in_block f (Beq eq)
  | INBlast: forall x e,
      Is_node_in_exp f e ->
      Is_node_in_block f (Blast x e)
  | INBreset : forall blocks er,
      Exists (Is_node_in_block f) blocks \/ Is_node_in_exp f er ->
      Is_node_in_block f (Breset blocks er)
  | INBswitch : forall ec branches,
      Is_node_in_exp f ec
      \/ Exists (fun blks => Is_node_in_branch (Exists (Is_node_in_block f)) (snd blks)) branches ->
      Is_node_in_block f (Bswitch ec branches)
  | INBauto : forall type ini oth states ck,
      Exists (fun '(e, _) => Is_node_in_exp f e) ini
      \/ Exists (fun blks =>
                  Is_node_in_branch
                    (fun blks => Exists (fun '(e, _) => Is_node_in_exp f e) (fst blks)
                              \/ Is_node_in_scope
                                  (fun blks => Exists (Is_node_in_block f) (fst blks)
                                            \/ Exists (fun '(e, _) => Is_node_in_exp f e) (snd blks)) f (snd blks))
                    (snd blks)) states ->
      Is_node_in_block f (Bauto ck type (ini, oth) states)
  | INBlocal : forall scope,
      Is_node_in_scope (Exists (Is_node_in_block f)) f scope ->
      Is_node_in_block f (Blocal scope).

  Definition Is_node_in {PSyn prefs} (f: ident) (nd : @node PSyn prefs) :=
    Is_node_in_block f nd.(n_block).

  Definition Ordered_nodes {PSyn prefs} : @global PSyn prefs -> Prop :=
    Ordered_program Is_node_in.

  (** ** Properties of [Ordered_nodes] *)

  Section Ordered_nodes_Properties.

    Lemma Ordered_nodes_append {PSyn prefs}:
      forall (G G': @global PSyn prefs),
        suffix G G'
        -> Ordered_nodes G'
        -> Ordered_nodes G.
    Proof.
      intros * Hsuff Hord. inv Hsuff.
      eapply Ordered_program_append; eauto.
      eapply program_equiv_rel_Symmetric; eauto.
    Qed.

    Lemma find_node_later_not_Is_node_in {PSyn prefs}:
      forall f types externs (nd: @node PSyn prefs) nds nd',
        Ordered_nodes (Global types externs (nd::nds))
        -> find_node f (Global types externs nds) = Some nd'
        -> ~Is_node_in nd.(n_name) nd'.
    Proof.
      intros * Hord Hfind Hini.
      eapply option_map_inv in Hfind as ((?&?)&(Hfind&?)); subst.
      eapply find_unit_later_not_Is_called_in with (us:=[nd]) in Hfind; eauto.
      apply Forall_singl in Hfind. apply Hfind; auto.
    Qed.

    Lemma find_node_not_Is_node_in {PSyn prefs}:
      forall f (nd: @node PSyn prefs) G,
        Ordered_nodes G
        -> find_node f G = Some nd
        -> ~Is_node_in nd.(n_name) nd.
    Proof.
      intros f nd G Hord Hfind.
      apply option_map_inv in Hfind as ((?&?)&(?&?)); subst.
      assert (name n = f) by (eapply find_unit_In; eauto); subst.
      eapply not_Is_called_in_self in H; simpl; eauto.
    Qed.

    Lemma ordered_nodes_NoDup {PSyn prefs} :
      forall (G : @global PSyn prefs) ,
        Ordered_nodes G ->
        NoDup (List.map n_name (nodes G)).
    Proof.
      unfold Ordered_nodes, Ordered_program, units.
      simpl; intros * Hord.
      induction (nodes G); simpl; inv Hord; constructor; auto.
      rewrite in_map_iff.
      intros (x & Heq & Hin).
      destruct_conjs.
      rewrite Forall_forall in *.
      unfold not in *.
      eauto.
    Qed.

    Lemma find_node_uncons {PSyn prefs} :
      forall f tys (nd ndf : @node PSyn prefs) nds exts,
        Ordered_nodes (Global tys exts (nd :: nds)) ->
        find_node f (Global tys exts nds) = Some ndf ->
        find_node f (Global tys exts (nd :: nds)) = Some ndf.
    Proof.
      intros * Hord%ordered_nodes_NoDup Hfind.
      destruct (ident_eq_dec (n_name nd) f); subst.
      - apply find_node_name in Hfind.
        inv Hord; contradiction.
      - rewrite find_node_other; auto.
    Qed.

    Lemma Ordered_nodes_nin {PSyn prefs} :
      forall tys exts nds (n nd : @node PSyn prefs),
        Ordered_nodes (Global tys exts (nd :: nds)) ->
        In n nds ->
        ~ Is_node_in_block (n_name nd) (n_block n).
    Proof.
      intros * Ord In.
      apply ordered_nodes_NoDup in Ord as Nd.
      apply find_node_In with _ n in Nd as Hfind; simpl; auto.
      setoid_rewrite find_node_other in Hfind.
      2:{ simpl in Nd. apply in_map with (f := n_name) in In.
          inv Nd. intro Heq. rewrite Heq in H1. contradiction. }
      eapply find_node_later_not_Is_node_in; eauto.
    Qed.

    (* FIXME: Ordered_node is so complicated that it is easier to
       use this lemma than to apply an [inversion] on the hypothesis *)
    Lemma Ordered_nodes_cons {PSyn prefs} :
      forall tys (nd : @node PSyn prefs) nds exts,
        Ordered_nodes (Global tys exts (nd :: nds)) ->
        Ordered_nodes (Global tys exts nds).
    Proof.
      inversion 1; auto.
    Qed.

  End Ordered_nodes_Properties.

  (** Actually, any wt or wc program is also ordered :)
      We can use the wl predicates + hypothesis that there is no duplication in the node names *)

  Lemma wl_exp_Is_node_in_exp {PSyn prefs} : forall (G: @global PSyn prefs) e f,
      wl_exp G e ->
      Is_node_in_exp f e ->
      In f (map n_name (nodes G)).
  Proof.
    intros * Hwl Hisin.
    induction e using exp_ind2; inv Hwl; inv Hisin;
      repeat match goal with
             | H: _ \/ _ |- _ => destruct H
             | H: forall x, Some _ = Some x -> _ |- _ => specialize (H _ eq_refl)
             | _ => simpl_Exists; simpl_Forall; subst
             end; auto.
    - (* app2 *)
      assert (find_node f0 G <> None) as Hfind.
      { intro contra. congruence. }
      apply find_node_Exists, Exists_exists in Hfind as (?&?&?).
      solve_In.
  Qed.

  Lemma wl_equation_Is_node_in_eq {PSyn prefs} : forall (G: @global PSyn prefs) eq f,
      wl_equation G eq ->
      Is_node_in_eq f eq ->
      In f (map n_name (nodes G)).
  Proof.
    intros ? [xs es] * Hwl Hisin.
    destruct Hwl as [Hwl _].
    unfold Is_node_in_eq in Hisin.
    simpl_Exists; simpl_Forall; eauto using wl_exp_Is_node_in_exp.
  Qed.

  Lemma wl_block_Is_node_in_block {PSyn prefs} : forall (G: @global PSyn prefs) d f,
      wl_block G d ->
      Is_node_in_block f d ->
      In f (map n_name (nodes G)).
  Proof.
    induction d using block_ind2; intros * Hwl Hin; inv Hwl; inv Hin;
      repeat match goal with
        | H: _ \/ _ |- _ => destruct H
        | Hin: Is_node_in_scope _ _ _ |- _ => inv Hin
        | Hwl: wl_scope _ _ _ |- _ => inv Hwl
        | Hin: Is_node_in_branch _ _ |- _ => inv Hin
        | Hwl: wl_branch _ _ |- _ => inv Hwl
        | o: option _ |- _ => destruct o; destruct_conjs; simpl in *
        | H: False |- _ => now inv H
        | H:Scope _ _ = Scope _ _ |- _ => inv H
        | _ => simpl_Exists; simpl_Forall
        end; eauto using wl_exp_Is_node_in_exp, wl_equation_Is_node_in_eq.
  Qed.

  Lemma wl_node_Is_node_in {PSyn prefs} : forall (G: @global PSyn prefs) n f,
      wl_node G n ->
      Is_node_in f n ->
      In f (map n_name (nodes G)).
  Proof.
    intros * Hwl Hisin. inv Hwl.
    eapply wl_block_Is_node_in_block; eauto.
  Qed.

  Lemma wl_global_Ordered_nodes {PSyn prefs} : forall (G: @global PSyn prefs),
      wl_global G ->
      Ordered_nodes G.
  Proof.
    intros * Wl.
    eapply wt_program_Ordered_program; eauto.
    intros * Wl' IsNodeIn.
    eapply wl_node_Is_node_in, in_map_iff in IsNodeIn as (?&Name&Hin); eauto.
    rewrite find_unit_Exists.
    solve_Exists.
  Qed.

  Lemma Ordered_nodes_change_types {PSyn prefs} :
    forall (nds : list (@node PSyn prefs)) enms1 enms2 externs1 externs2,
      Ordered_nodes (Global enms1 externs1 nds) ->
      Ordered_nodes (Global enms2 externs2 nds).
  Proof.
    induction nds; intros * Hord; inv Hord; constructor; simpl in *.
    - destruct H1 as (Hnin&Hnames).
      split; auto. intros * Hinblk. specialize (Hnin _ Hinblk) as (?&?&?&?).
      split; auto.
      destruct (find_unit f {| types := enms2; nodes := nds |}) as [(?&?)|] eqn:Hnone; eauto. exfalso.
      apply find_unit_None in Hnone. simpl in *.
      apply find_unit_spec in H0 as (Hname&?&Hsome&_); simpl in *; subst.
      apply Forall_elt in Hnone. congruence.
    - eapply IHnds, H2.
  Qed.

  (** Induction based on order of nodes *)

  Section ordered_nodes_ind.
    Context {PSyn prefs} (G: @global PSyn prefs).

    Variable P_node : ident -> Prop.

    Hypothesis Hnode : forall f n,
        find_node f G = Some n ->
        (forall f', Is_node_in f' n -> P_node f') ->
        P_node f.

    Lemma ordered_nodes_ind :
      Ordered_nodes G ->
      (forall f n, find_node f G = Some n -> P_node f).
    Proof.
      destruct G. induction nodes0; intros * Hord * Hfind; inv Hord; destruct_conjs; simpl in *.
      now inv Hfind.
      assert (forall f n0,
                 find_node f {| types := types0; externs := externs0; nodes := nodes0 |} = Some n0 ->
                 P_node f) as Hind.
      { intros. eapply IHnodes0; eauto.
        intros * Hsome Hord. eapply Hnode; eauto.
        rewrite find_node_other; auto.
        edestruct (find_node_Exists f1 {| types := types0; externs := externs0; nodes := nodes0 |}) as (Hex&_).
        eapply Exists_exists in Hex as (?&?&?); subst; try congruence.
        simpl_Forall; auto.
      } clear IHnodes0.
      destruct (ident_eq_dec f (n_name a)); subst.
      - rewrite find_node_now in Hfind; auto; inv Hfind.
        eapply Hnode; eauto using find_node_now.
        intros ? Hblk.
        eapply H in Hblk as (_&?&?&Hfind).
        eapply Hind; eauto.
        unfold find_node. now rewrite Hfind.
      - rewrite find_node_other in Hfind; auto.
        eapply Hind; eauto.
    Qed.

  End ordered_nodes_ind.

End LORDERED.

Module LOrderedFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks   : CLOCKS Ids Op OpAux)
       (Senv  : STATICENV Ids Op OpAux Cks)
       (Syn   : LSYNTAX Ids Op OpAux Cks Senv)
       <: LORDERED Ids Op OpAux Cks Senv Syn.
  Include LORDERED Ids Op OpAux Cks Senv Syn.
End LOrderedFun.
