From Coq Require Import PArith.
From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Velus Require Import Common.
From Velus Require Import CommonProgram.
From Velus Require Import CommonTyping.
From Velus Require Import Operators.
From Velus Require Import Clocks.
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
       (Import Syn  : LSYNTAX Ids Op OpAux Cks).

  Inductive Is_node_in_exp : ident -> exp -> Prop :=
  | INEunop: forall f op e a,
      Is_node_in_exp f e -> Is_node_in_exp f (Eunop op e a)
  | INEbinop: forall f op e1 e2 a,
      Is_node_in_exp f e1 \/ Is_node_in_exp f e2 ->
      Is_node_in_exp f (Ebinop op e1 e2 a)
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

  Inductive Is_node_in_block (f: ident) : block -> Prop :=
  | INBeq: forall eq,
      Is_node_in_eq f eq ->
      Is_node_in_block f (Beq eq)
  | INBreset : forall blocks er,
      Exists (Is_node_in_block f) blocks \/ Is_node_in_exp f er ->
      Is_node_in_block f (Breset blocks er)
  | INBlocal : forall locs blocks,
      Exists (Is_node_in_block f) blocks ->
      Is_node_in_block f (Blocal locs blocks).

  Definition Ordered_nodes {PSyn prefs} : @global PSyn prefs -> Prop :=
    Ordered_program (fun f nd => Is_node_in_block f nd.(n_block)).

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
      forall f enums (nd: @node PSyn prefs) nds nd',
        Ordered_nodes (Global enums (nd::nds))
        -> find_node f (Global enums nds) = Some nd'
        -> ~Is_node_in_block nd.(n_name) nd'.(n_block).
    Proof.
      intros * Hord Hfind Hini.
      eapply option_map_inv in Hfind as ((?&?)&(Hfind&?)); subst.
      eapply find_unit_later_not_Is_called_in with (us:=[nd]) in Hfind; eauto.
      apply Forall_singl in Hfind; auto.
    Qed.

    Lemma find_node_not_Is_node_in {PSyn prefs}:
      forall f (nd: @node PSyn prefs) G,
        Ordered_nodes G
        -> find_node f G = Some nd
        -> ~Is_node_in_block nd.(n_name) nd.(n_block).
    Proof.
      intros f nd G Hord Hfind.
      apply option_map_inv in Hfind as ((?&?)&(?&?)); subst.
      assert (name n = f) by (eapply find_unit_In; eauto); subst.
      eapply not_Is_called_in_self in H; simpl; eauto.
      assumption.
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
    Local Ltac Forall_Exists :=
      match goal with
      | Hex : Exists _ ?es, Hwl : Forall (wl_exp ?G) ?Es, H: Forall (fun _ => _) ?es |- _ =>
        eapply Forall_Forall in H; [|eapply Hwl]; clear Hwl;
        eapply Forall_Exists, Exists_exists in H as [? [_ [[? ?] ?]]]; eauto
      end.
    induction e using exp_ind2; inv Hwl; inv Hisin.
    - (* unop *) auto.
    - (* binop *) destruct H1; auto.
    - (* fby *) destruct H3 as [?|?]; Forall_Exists.
    - (* arrow *) destruct H3 as [?|?]; Forall_Exists.
    - (* when *) Forall_Exists.
    - (* merge *)
      eapply Forall_Forall in H; [|eapply H5]; clear H5.
      eapply Forall_Exists, Exists_exists in H2 as (?&?&He&?); eauto; simpl in *.
      destruct He. Forall_Exists.
    - (* case *)
      destruct H3 as [Hex|[Hex|(?&?&Hex)]]; subst; simpl in *; auto.
      + eapply Forall_Forall in H; [|eapply H9]; clear H9.
        eapply Forall_Exists, Exists_exists in Hex as (?&?&He&?); eauto; simpl in *.
        destruct He. Forall_Exists.
      + specialize (H11 _ eq_refl). Forall_Exists.
    - (* app1 *) clear H8. destruct H3; Forall_Exists.
    - (* app2 *) assert (find_node f0 G <> None) as Hfind.
      { intro contra. congruence. }
      apply find_node_Exists, Exists_exists in Hfind as [? [Hin Hname]].
      rewrite in_map_iff; eauto.
  Qed.

  Lemma wl_equation_Is_node_in_eq {PSyn prefs} : forall (G: @global PSyn prefs) eq f,
      wl_equation G eq ->
      Is_node_in_eq f eq ->
      In f (map n_name (nodes G)).
  Proof.
    intros ? [xs es] * Hwl Hisin.
    destruct Hwl as [Hwl _].
    unfold Is_node_in_eq in Hisin.
    eapply Forall_Exists in Hisin; eauto.
    eapply Exists_exists in Hisin as [? [_ [? ?]]].
    eapply wl_exp_Is_node_in_exp; eauto.
  Qed.

  Lemma wl_equation_Is_node_in_block {PSyn prefs} : forall (G: @global PSyn prefs) d f,
      wl_block G d ->
      Is_node_in_block f d ->
      In f (map n_name (nodes G)).
  Proof.
    induction d using block_ind2; intros * Hwl Hin.
    - inv Hwl; inv Hin.
      eapply wl_equation_Is_node_in_eq; eauto.
    - inv Hwl. inv Hin.
      destruct H1 as [Hisin|Hisin].
      + eapply Forall_Forall in H; eauto.
        eapply Forall_Exists in Hisin; eauto.
        eapply Exists_exists in Hisin as (?&_&(?&?)&?); eauto.
      + eapply wl_exp_Is_node_in_exp; eauto.
    - inv Hwl. inv Hin.
      eapply Forall_Forall in H; eauto.
      eapply Forall_Exists in H; eauto.
      eapply Exists_exists in H as (?&_&(?&?)&?); eauto.
  Qed.

  Lemma wl_node_Is_node_in {PSyn prefs} : forall (G: @global PSyn prefs) n f,
      wl_node G n ->
      Is_node_in_block f (n_block n) ->
      In f (map n_name (nodes G)).
  Proof.
    intros * Hwl Hisin.
    unfold wl_node in Hwl.
    eapply wl_equation_Is_node_in_block; eauto.
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
    eapply Exists_exists; eauto.
  Qed.

End LORDERED.

Module LOrderedFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks   : CLOCKS Ids Op OpAux)
       (Syn   : LSYNTAX Ids Op OpAux Cks)
       <: LORDERED Ids Op OpAux Cks Syn.
  Include LORDERED Ids Op OpAux Cks Syn.
End LOrderedFun.
