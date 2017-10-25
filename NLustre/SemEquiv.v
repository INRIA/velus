Require Import List.
Import List.ListNotations.
Open Scope list_scope.
Require Import Coq.Sorting.Permutation.

Require Import Coq.FSets.FMapPositive.
Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.Clocks.
Require Import Velus.NLustre.NLSyntax.
Require Import Velus.NLustre.NLSemanticsCommon.
Require Import Velus.NLustre.Ordered.
Require Import Streams.

Require Import Velus.NLustre.NLSemanticsCoIndWire.
Require Import Velus.NLustre.NLSemanticsCoIndRec.

Module Type SEMEQUIV
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op)
       (Import Clks  : CLOCKS    Ids)
       (Import Syn   : NLSYNTAX  Ids Op Clks)
       (Import Comm  : NLSEMANTICSCOMMON Ids Op OpAux Clks Syn)
       (Import Ord   : ORDERED   Ids Op Clks Syn)
       (Wire  : NLSEMANTICSCOINDWIRE Ids Op OpAux Clks Syn Comm Ord)
       (Rec   : NLSEMANTICSCOINDREC  Ids Op OpAux Clks Syn Comm Ord).

  CoFixpoint false_s : Stream bool := false ::: false_s.

  Lemma unfold_false_s : false_s = false ::: false_s.
  Proof.
    rewrite unfold_Stream at 1; auto.
  Qed.

  Section Global.

    Variable G: global.

    Lemma fby1_equiv:
      forall c v xs ys,
        Wire.fby1 false_s v (sem_const c) xs ys <->
        Rec.fby1 v (sem_const c) xs ys.
    Proof.
      split; revert c v xs ys; cofix CoFby1; intros ** Fby1.
      - rewrite unfold_false_s in Fby1.
        inversion Fby1; constructor; auto.
      - rewrite unfold_false_s.
        inversion Fby1; constructor; auto.
    Qed.

    Lemma fby_equiv:
      forall c xs ys,
        Wire.fby false_s (sem_const c) xs ys <->
        Rec.fby (sem_const c) xs ys.
    Proof.
      split; revert xs ys; cofix CoFby; intros ** Fby.
      - rewrite unfold_false_s in Fby.
        inversion_clear Fby; constructor; auto.
        now apply fby1_equiv.
      - rewrite unfold_false_s.
        inversion_clear Fby; constructor; auto.
        now apply fby1_equiv.
    Qed.

    (* CoInductive synchronised: Stream value -> Stream value -> Prop := *)
    (* | A_synchro: *)
    (*     forall xs ys, *)
    (*       synchronised xs ys -> *)
    (*       synchronised (absent ::: xs) (absent ::: ys) *)
    (* | P_synchro: *)
    (*     forall xs ys x y, *)
    (*       synchronised xs ys -> *)
    (*       synchronised (present x ::: xs) (present y ::: ys). *)

    (* Ltac prove_synchro := *)
    (*   match goal with *)
    (*     |- forall s, synchronised s ?s' => *)
    (*     let COFIX := fresh "COFIX" in *)
    (*     let s := fresh s in *)
    (*     let v := fresh "v" in *)
    (*     cofix COFIX; intro s; *)
    (*     rewrite unfold_Stream; *)
    (*     destruct s as [v]; destruct v; simpl; constructor; auto *)
    (*   end. *)

    (* Lemma true_s'_synchronised: *)
    (*   forall s, synchronised s (Rec.true_s' s). *)
    (* Proof. prove_synchro. Qed. *)

    (* Lemma once'_synchronised: *)
    (*   forall s, synchronised s (Rec.once' s). *)
    (* Proof. *)
    (*   prove_synchro. *)
    (*   destruct (c ==b true_val); auto. *)
    (*   apply true_s'_synchronised. *)
    (* Qed. *)

    (* Lemma when_witness: *)
    (*   forall k xs ys, *)
    (*     synchronised xs ys -> *)
    (*     exists rs, when k xs ys rs. *)
    (* Proof. *)
    (*   eexists. *)
    (*   revert k xs ys H. *)
    (*   cofix. *)
    (*   intros. *)
    (*   inv H. *)
    (*   - constructor. *)
    (* Admitted. *)

    Lemma WireRec_node_reset:
      forall rs f ess oss,
        Wire.sem_node G (Wire.merge_reset false_s (reset_of rs)) f ess oss ->
        Rec.sem_node G f ess oss ->
        Rec.sem_reset G f (reset_of rs) ess oss.
    Proof.
      intros ** Reset Node.
      destruct Reset.

      (* assert (exists xss', Forall2 (fun xs xs' => when true xs (Rec.once' (Rec.reset_of rs)) xs') xss xss') *)
      (*   as (xss' & When_xss). *)
      (* { clear; induction xss. *)
      (*   - eexists; eauto. *)
      (*   - edestruct IHxss. *)
      (*     edestruct (when_witness true a (Rec.once' (Rec.reset_of rs))). *)
      (*     admit. *)
      (*     eexists. *)
      (*     constructor; eauto. *)
      (* } *)

      (* assert (exists rs', when true (Rec.reset_of rs) (Rec.once' (Rec.reset_of rs)) rs') *)
      (*   as (rs' & When_rs) by apply when_witness, once'_synchronised. *)

       econstructor; eauto.
      - econstructor. clear; induction xss.
        + eexists; eauto.

    Admitted.

    Lemma WireRec_equation_node:
      (forall H b r e,
          Wire.sem_equation G H b r e ->
          (* r = false_s -> *)
          Rec.sem_equation G H b e)
      /\
      (forall r f xss oss,
          Wire.sem_node G r f xss oss ->
          Rec.sem_node G f xss oss).
    Proof.
      Check Wire.sem_equation_node_ind.
      apply Wire.sem_equation_node_ind; intros.
      - econstructor; eauto.
      - econstructor; eauto.
      - econstructor; eauto.
        eapply WireRec_node_reset; eauto.
      - econstructor; eauto.
        subst; now apply fby_equiv.
      - econstructor; eauto.
        apply Forall_impl with (2:=H4).
        auto.
    Qed.

    Theorem WireRec:
      forall G f xss yss,
        Wire.sem_node G false_s f xss yss
        <-> Rec.sem_node G f xss yss.
    Proof.
      split; intro Sem; inv Sem; econstructor; eauto; eapply Forall_impl;
        [ now apply WireRec_equation | auto
          | now apply WireRec_equation | auto ].
    Qed.

    SearchAbout Forall.

  End SEMEQUIV.
