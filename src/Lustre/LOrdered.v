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
  | INEfby: forall f le1 le2 ler la,
      Exists (Is_node_in_exp f) le1 \/ Exists (Is_node_in_exp f) le2 \/
      Exists (Is_node_in_exp f) ler ->
      Is_node_in_exp f (Efby le1 le2 ler la)
  | INEarrow: forall f le1 le2 ler la,
      Exists (Is_node_in_exp f) le1 \/ Exists (Is_node_in_exp f) le2 \/
      Exists (Is_node_in_exp f) ler ->
      Is_node_in_exp f (Earrow le1 le2 ler la)
  | INEwhen: forall f le x b la,
      Exists (Is_node_in_exp f) le ->
      Is_node_in_exp f (Ewhen le x b la)
  | INEmerge: forall f x es la,
      Exists (Exists (Is_node_in_exp f)) es ->
      Is_node_in_exp f (Emerge x es la)
  | INEite: forall f e es la,
      Is_node_in_exp f e
      \/ Exists (Exists (Is_node_in_exp f)) es ->
      Is_node_in_exp f (Ecase e es la)
  | INEapp1: forall f g le ler a,
      Exists (Is_node_in_exp f) le \/
      Exists (Is_node_in_exp f) ler ->
      Is_node_in_exp f (Eapp g le ler a)
  | INEapp2: forall f le ler a, Is_node_in_exp f (Eapp f le ler a).

  Definition Is_node_in_eq (f: ident) (eq: equation) : Prop :=
    List.Exists (Is_node_in_exp f) (snd eq).

  (* definition is needed in signature *)
  Definition Is_node_in (f: ident) (eqs: list equation) : Prop :=
    List.Exists (Is_node_in_eq f) eqs.

  Definition Ordered_nodes {prefs }: @global prefs -> Prop :=
    Ordered_program (fun f nd => Is_node_in f nd.(n_eqs)).

  (** ** Properties of [Is_node_in] *)

  Section Is_node_Properties.

    Lemma not_Is_node_in_cons:
      forall n eq eqs,
        ~ Is_node_in n (eq::eqs) <-> ~Is_node_in_eq n eq /\ ~Is_node_in n eqs.
    Proof.
      intros n eq eqs.
      split; intro HH.
      - split; intro; apply HH; unfold Is_node_in; intuition.
      - destruct HH; inversion_clear 1; intuition.
    Qed.

    Lemma Is_node_in_Exists: forall n eqs,
        Is_node_in n eqs <-> List.Exists (Is_node_in_eq n) eqs.
    Proof.
      intros.
      induction eqs as [|eq eqs IH].
      - split; intro Hisin; inv Hisin.
      - split; intro Hisin.
        + inv Hisin.
          * constructor; auto.
          * apply Exists_cons_tl; auto.
        + inv Hisin.
          * constructor; auto.
          * apply Exists_cons_tl; auto.
    Qed.

    Lemma Is_node_in_Forall:
      forall n eqs,
        ~Is_node_in n eqs <-> List.Forall (fun eq=>~Is_node_in_eq n eq) eqs.
    Proof.
      intros n eqs.
      rewrite Is_node_in_Exists. symmetry. apply Forall_Exists_neg.
    Qed.

    Lemma Is_node_in_app: forall n eqs1 eqs2,
        Is_node_in n (eqs1++eqs2) <-> (Is_node_in n eqs1 \/ Is_node_in n eqs2).
    Proof.
      intros n eqs1 eqs2.
      unfold Is_node_in.
      apply Exists_app'.
    Qed.

  End Is_node_Properties.

  (** ** Properties of [Ordered_nodes] *)

  Section Ordered_nodes_Properties.

    Lemma Ordered_nodes_append {prefs}:
      forall (G G': @global prefs),
        suffix G G'
        -> Ordered_nodes G'
        -> Ordered_nodes G.
    Proof.
      intros * Hsuff Hord. inv Hsuff.
      eapply Ordered_program_append; eauto.
      eapply program_equiv_rel_Symmetric; eauto.
    Qed.

    Lemma find_node_later_not_Is_node_in {prefs}:
      forall f enums (nd: @node prefs) nds nd',
        Ordered_nodes (Global enums (nd::nds))
        -> find_node f (Global enums nds) = Some nd'
        -> ~Is_node_in nd.(n_name) nd'.(n_eqs).
    Proof.
      intros * Hord Hfind Hini.
      eapply option_map_inv in Hfind as ((?&?)&(Hfind&?)); subst.
      eapply find_unit_later_not_Is_called_in with (us:=[nd]) in Hfind; eauto.
      apply Forall_singl in Hfind; auto.
    Qed.

    Lemma find_node_not_Is_node_in {prefs}:
      forall f (nd: @node prefs) G,
        Ordered_nodes G
        -> find_node f G = Some nd
        -> ~Is_node_in nd.(n_name) nd.(n_eqs).
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

  Lemma wl_exp_Is_node_in_exp {prefs} : forall (G: @global prefs) e f,
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
    - (* fby *) clear H12. destruct H4 as [?|[?|?]]; Forall_Exists.
    - (* arrow *) clear H12. destruct H4 as [?|[?|?]]; Forall_Exists.
    - (* when *) Forall_Exists.
    - (* merge *)
      eapply Forall_Forall in H; [|eapply H5]; clear H5.
      eapply Forall_Exists, Exists_exists in H2 as (?&?&He&?); eauto; simpl in *.
      destruct He. Forall_Exists.
    - (* case *)
      destruct H2 as [Hex|Hex]; auto.
      eapply Forall_Forall in H; [|eapply H7]; clear H7.
      eapply Forall_Exists, Exists_exists in H as (?&?&He&?); eauto; simpl in *.
      destruct He. Forall_Exists.
    - (* app1 *) clear H8. destruct H3; Forall_Exists.
    - (* app2 *) assert (find_node f0 G <> None) as Hfind.
      { intro contra. congruence. }
      apply find_node_Exists, Exists_exists in Hfind as [? [Hin Hname]].
      rewrite in_map_iff; eauto.
  Qed.

  Lemma wl_equation_Is_node_in_eq {prefs} : forall (G: @global prefs) eq f,
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

  Lemma wl_node_Is_node_in {prefs} : forall (G: @global prefs) n f,
      wl_node G n ->
      Is_node_in f (n_eqs n) ->
      In f (map n_name (nodes G)).
  Proof.
    intros * Hwl Hisin.
    unfold wl_node in Hwl.
    unfold Is_node_in in Hisin.
    eapply Forall_Exists in Hisin; eauto.
    eapply Exists_exists in Hisin as [? [_ [? ?]]].
    eapply wl_equation_Is_node_in_eq; eauto.
  Qed.

  Lemma wl_global_Ordered_nodes {prefs} : forall (G: @global prefs),
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
