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
Require Import Velus.NLustre.NLSemanticsCoInd.

Require Import Setoid.
Module Type SEMEQUIV
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op)
       (Import Clks  : CLOCKS    Ids)
       (Import Syn   : NLSYNTAX  Ids Op Clks)
       (Import Comm  : NLSEMANTICSCOMMON Ids Op OpAux Clks Syn)
       (Import Ord   : ORDERED   Ids Op Clks Syn)
       (Wire         : NLSEMANTICSCOINDWIRE Ids Op OpAux Clks Syn Comm Ord)
       (Rec          : NLSEMANTICSCOIND Ids Op OpAux Clks Syn Comm Ord).

   Ltac unfold_Stv xs :=
    rewrite (unfold_Stream xs);
    destruct xs as [[|]];
    simpl.

  Ltac unfold_St xs :=
    rewrite (unfold_Stream xs);
    destruct xs;
    simpl.

  Add Parametric Relation A : (Stream A) (@EqSt A)
      reflexivity proved by (@EqSt_reflex A)
      symmetry proved by (@sym_EqSt A)
      transitivity proved by (@trans_EqSt A)
        as EqStrel.

  Add Parametric Morphism A : (@Cons A)
      with signature eq ==> @EqSt A ==> @EqSt A
        as Cons_EqSt.
  Proof.
    cofix Cofix.
    intros x xs xs' Exs.
    constructor; simpl; auto.
  Qed.

  Add Parametric Morphism A : (@hd A)
      with signature @EqSt A ==> eq
        as hd_EqSt.
  Proof.
    intros xs xs' Exs.
    destruct xs, xs'; inv Exs; simpl; auto.
  Qed.

  Add Parametric Morphism A : (@tl A)
      with signature @EqSt A ==> @EqSt A
        as tl_EqSt.
  Proof.
    intros xs xs' Exs.
    destruct xs, xs'; inv Exs; simpl; auto.
  Qed.

  Section EqSts.
    Variable A: Type.

    Definition EqSts (xss yss: list (Stream A)) :=
      Forall2 (@EqSt A) xss yss.

    Theorem EqSts_reflex: forall xss, EqSts xss xss.
    Proof.
      induction xss; constructor; auto.
      reflexivity.
    Qed.

    Theorem EqSts_sym: forall xss yss, EqSts xss yss -> EqSts yss xss.
    Proof.
      induction xss, yss; intros ** H; auto; try inv H.
      constructor.
      - now symmetry.
      - now apply IHxss.
    Qed.

    Theorem EqSts_trans: forall xss yss zss, EqSts xss yss -> EqSts yss zss -> EqSts xss zss.
    Proof.
      induction xss, yss, zss; intros ** Hx Hy; auto; try inv Hx; try inv Hy.
      constructor.
      - now transitivity s.
      - eapply IHxss; eauto.
    Qed.

  End EqSts.

  Add Parametric Relation A : (list (Stream A)) (@EqSts A)
      reflexivity proved by (@EqSts_reflex A)
      symmetry proved by (@EqSts_sym A)
      transitivity proved by (@EqSts_trans A)
        as EqStsrel.

  Add Parametric Morphism A : (@cons (Stream A))
      with signature @EqSt A ==> @EqSts A ==> @EqSts A
        as cons_EqSt.
  Proof. constructor; auto. Qed.

  Add Parametric Morphism
      A B (P: A -> Stream B -> Prop) xs
      (P_compat: forall (x: A) (y y': Stream B), y ≡ y' -> (P x y <-> P x y'))
    : (@Forall2 A (Stream B) P xs)
      with signature @EqSts B ==> Basics.impl
        as Forall2_EqSt.
  Proof.
    intros ys ys' Eys.
    revert xs ys ys' Eys;
      induction xs, ys; intros ** H; inv H; inv Eys; auto.
    constructor; eauto.  eapply P_compat; eauto.
    - now symmetry.
    - eapply IHxs; eauto.
  Qed.

  Add Parametric Morphism H x : (sem_var H x)
      with signature @EqSt value ==> Basics.impl
        as sem_var_EqSt.
  Proof.
    intros xs xs' E.
    intros Sem.
  Admitted.

  Add Parametric Morphism : merge
      with signature @EqSt value ==> @EqSt value ==> @EqSt value ==> @EqSt value ==> Basics.impl
        as merge_EqSt.
  Proof.
    cofix Cofix.
    intros cs cs' Ecs xs xs' Exs ys ys' Eys zs zs' Ezs H.
    destruct cs' as [[]], xs' as [[]], ys' as [[]], zs' as [[]];
      inv H; inv Ecs; inv Exs; inv Eys; inv Ezs; simpl in *;
        try discriminate.
      + constructor; eapply Cofix; eauto.
      + rewrite <-H, <-H4, <-H6.
        constructor; eapply Cofix; eauto.
      + rewrite <-H, <-H2, <-H6.
        constructor; eapply Cofix; eauto.
  Qed.

  Add Parametric Morphism : ite
      with signature @EqSt value ==> @EqSt value ==> @EqSt value ==> @EqSt value ==> Basics.impl
        as ite_EqSt.
  Proof.
    cofix Cofix.
    intros es es' Ees ts ts' Ets fs fs' Efs zs zs' Ezs H.
    destruct es' as [[]], ts' as [[]], fs' as [[]], zs' as [[]];
      inv H; inv Ees; inv Ets; inv Efs; inv Ezs; simpl in *;
        try discriminate.
      + constructor; eapply Cofix; eauto.
      + rewrite <-H, <-H2, <-H6.
        constructor; eapply Cofix; eauto.
      + rewrite <-H, <-H4, <-H6.
        constructor; eapply Cofix; eauto.
  Qed.

  Add Parametric Morphism k : (when k)
      with signature @EqSt value ==> @EqSt value ==> @EqSt value ==> Basics.impl
        as when_EqSt.
  Proof.
    cofix Cofix.
    intros cs cs' Ecs xs xs' Exs ys ys' Eys H.
    destruct cs' as [[]], xs' as [[]], ys' as [[]];
      inv H; inv Ecs; inv Exs; inv Eys; simpl in *;
        try discriminate.
      + constructor; eapply Cofix; eauto.
      + constructor.
        * eapply Cofix; eauto.
        * now inv H3.
      + rewrite <-H, <-H5.
        constructor.
        * eapply Cofix; eauto.
        * now inv H3.
  Qed.

  Add Parametric Morphism op t : (lift1 op t)
      with signature @EqSt value ==> @EqSt value ==> Basics.impl
        as lift1_EqSt.
  Proof.
    cofix Cofix.
    intros es es' Ees ys ys' Eys Lift.
    destruct es' as [[]], ys' as [[]];
      inv Lift; inv Eys; inv Ees; simpl in *; try discriminate.
    - constructor; eapply Cofix; eauto.
    - constructor.
      + now inv H1; inv H3.
      + eapply Cofix; eauto.
  Qed.

  Add Parametric Morphism op t1 t2 : (lift2 op t1 t2)
      with signature @EqSt value ==> @EqSt value ==> @EqSt value ==> Basics.impl
        as lift2_EqSt.
  Proof.
    cofix Cofix.
    intros e1s e1s' Ee1s e2s e2s' Ee2s ys ys' Eys Lift.
    destruct e1s' as [[]], e2s' as [[]], ys' as [[]];
      inv Lift; inv Eys; inv Ee1s; inv Ee2s; simpl in *; try discriminate.
    - constructor; eapply Cofix; eauto.
    - constructor.
      + now inv H1; inv H3; inv H5.
      + eapply Cofix; eauto.
  Qed.

  Add Parametric Morphism H : (sem_lexp H)
      with signature @EqSt bool ==> eq ==> @EqSt value ==> Basics.impl
        as sem_lexp_morph.
  Proof.
    intros ** b b' Eb e xs xs' Exs Sem.
    revert b' xs' Eb Exs; induction Sem.
    - intros. admit.
    - econstructor; eauto.
      eapply sem_var_EqSt; eauto.
    - econstructor; eauto.
      apply IHSem; auto; try reflexivity.
      now rewrite <-Exs.
    - econstructor.
      + apply IHSem; auto; reflexivity.
      + now rewrite <-Exs.
    - econstructor.
      + apply IHSem1; auto; reflexivity.
      + apply IHSem2; auto; reflexivity.
      + now rewrite <-Exs.
  Qed.

  Add Parametric Morphism H : (sem_cexp H)
      with signature @EqSt bool ==> eq ==> @EqSt value ==> Basics.impl
        as sem_cexp_morph.
  Proof.
    intros ** b b' Eb e xs xs' Exs Sem.
    revert b' xs' Eb Exs; induction Sem.
    - econstructor; eauto.
      + apply IHSem1; auto; reflexivity.
      + apply IHSem2; auto; reflexivity.
      + now rewrite <-Exs.
    - econstructor; eauto.
      + rewrite <-Eb; eauto.
      + apply IHSem1; auto; reflexivity.
      + apply IHSem2; auto; reflexivity.
      + now rewrite <-Exs.
    - constructor.
      now rewrite <-Eb, <-Exs.
  Qed.

  Add Parametric Morphism : Wire.merge_reset
      with signature @EqSt bool ==> @EqSt bool ==> @EqSt bool
        as merge_reset_EqSt.
  Proof.
    cofix Cofix.
    intros r1 r1' Er1 r2 r2' Er2.
    unfold_St r1; unfold_St r1'; unfold_St r2; unfold_St r2'.
    constructor; inv Er1; inv Er2; simpl in *; auto.
    now subst.
  Qed.

  CoFixpoint wire_fby1_EqSt_fix (v c: val)
           (rs rs': Stream bool) (Ers: rs ≡ rs')
           (xs xs': Stream value) (Exs: xs ≡ xs') :
    Wire.fby1 rs v c xs ≡ Wire.fby1 rs' v c xs'
  with wire_fby_EqSt_fix (c: val)
                     (rs rs': Stream bool) (Ers: rs ≡ rs')
                     (xs xs': Stream value) (Exs: xs ≡ xs') :
         Wire.fby rs c xs ≡ Wire.fby rs' c xs'.
  Proof.
    - unfold_Stv rs; unfold_Stv rs'; unfold_Stv xs; unfold_Stv xs';
        constructor; inv Exs; inv Ers; simpl in *; try discriminate; auto.
      + inv H; apply wire_fby1_EqSt_fix; auto.
      + inv H; apply wire_fby1_EqSt_fix; auto.
    - unfold_Stv xs; unfold_Stv xs'; unfold_St rs; unfold_St rs';
        constructor; inv Exs; inv Ers; simpl in *; try discriminate; auto.
      inv H; apply wire_fby1_EqSt_fix; auto.
  Qed.

  Add Parametric Morphism : Wire.fby
      with signature @EqSt bool ==> eq ==> @EqSt value ==> @EqSt value
        as wire_fby_EqSt.
  Proof. intros; apply wire_fby_EqSt_fix; auto. Qed.

  Add Parametric Morphism : clocks_of
      with signature @EqSts value ==> @EqSt bool
        as clocks_of_EqSt.
  Proof.
    cofix Cofix.
    intros xs xs' Exs.
    constructor; simpl.
    - clear Cofix.
      revert dependent xs'.
      induction xs; intros; try inv Exs; simpl; auto.
      f_equal; auto.
      now rewrite H1.
    - apply Cofix.
      clear Cofix.
      revert dependent xs'.
      induction xs; intros; try inv Exs; simpl; constructor.
      + now rewrite H1.
      + now apply IHxs.
  Qed.

  Fixpoint wire_sem_equation_morph_fix
           (G: global) (H: history)
           (b b': Stream bool) (Eb: b ≡ b')
           (r r': Stream bool) (Er: r ≡ r')
           (e: equation)
           (Sem: Wire.sem_equation G H b r e) {struct Sem} :
    Wire.sem_equation G H b' r' e
  with wire_sem_node_morph_fix
         (G: global)
         (r r': Stream bool) (Er: r ≡ r')
         (f: ident)
         (xss xss': list (Stream value)) (Exss: EqSts value xss xss')
         (yss yss': list (Stream value)) (Eyss: EqSts value yss yss')
         (Sem: Wire.sem_node G r f xss yss) {struct Sem} :
    Wire.sem_node G r' f xss' yss'.
  Proof.
    - induction Sem.
      + econstructor; eauto.
        now rewrite <-Eb.
      + econstructor; eauto.
        * apply Forall2_impl_In with (P:=sem_lexp H b); eauto.
          intros; now rewrite <-Eb.
        * eapply wire_sem_node_morph_fix; eauto; reflexivity.
      + econstructor; eauto.
        * apply Forall2_impl_In with (P:=sem_lexp H b); eauto.
          intros; now rewrite <-Eb.
        * eapply wire_sem_node_morph_fix; eauto; try reflexivity.
          rewrite <-Er; reflexivity.
      + econstructor; eauto.
        * rewrite <-Eb; eauto.
        * subst.
          eapply sem_var_EqSt; eauto.
          now rewrite <-Er.
    - induction Sem.
      econstructor; eauto.
      + instantiate (1:=H).
        eapply Forall2_EqSt; eauto.
        intros; split; apply sem_var_EqSt; auto.
        now symmetry.
      + eapply Forall2_EqSt; eauto.
        intros; split; apply sem_var_EqSt; auto.
        now symmetry.
      + apply Forall_impl with (P:=Wire.sem_equation G H (clocks_of xss) r); auto.
        apply wire_sem_equation_morph_fix; auto.
        now rewrite Exss.
  Admitted.

  Add Parametric Morphism G H : (Wire.sem_equation G H)
      with signature @EqSt bool ==> @EqSt bool ==> eq ==> Basics.impl
        as wire_sem_equation_morph.
  Proof.
    unfold Basics.impl; apply wire_sem_equation_morph_fix.
  Qed.

  Add Parametric Morphism G : (Wire.sem_node G)
      with signature @EqSt bool ==> eq ==> @EqSts value ==> @EqSts value ==> Basics.impl
        as wire_sem_node_morph.
  Proof.
    unfold Basics.impl; apply wire_sem_node_morph_fix.
  Qed.

  CoFixpoint false_s : Stream bool := false ::: false_s.

  Lemma unfold_false_s : false_s = false ::: false_s.
  Proof.
    rewrite unfold_Stream at 1; auto.
  Qed.

  Section Global.

    Variable G: global.

    Remark fby1_equiv:
      forall c v xs,
        Wire.fby1 false_s v (sem_const c) xs ≡ Rec.fby1 v (sem_const c) xs.
    Proof.
      cofix; intros.
      unfold_Stv xs; constructor; simpl; auto.
    Qed.

    Corollary fby_equiv:
      forall c xs,
        Wire.fby false_s (sem_const c) xs ≡ Rec.fby (sem_const c) xs.
    Proof.
      cofix; intros.
      unfold_Stv xs; constructor; simpl; auto.
      apply fby1_equiv.
    Qed.

    Remark merge_reset_with_false:
      forall r, Wire.merge_reset false_s r ≡ r.
    Proof.
      cofix; intro.
      rewrite unfold_false_s.
      destruct r.
      constructor; simpl; auto.
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

    (* Lemma flatten_masks_n_spec: *)
    (*   forall rs xs n, *)
    (*     Rec.flatten_masks rs (Rec.masks_from n rs xs) ≡ xs. *)
    (* Proof. *)
    (*   cofix; intros. *)
    (*   unfold_Stv rs; unfold_St xs. *)
    (*   - constructor; simpl; auto. *)
    (*     simpl. *)

    Lemma flatten_masks_spec:
      forall rs xs,
        Rec.flatten_masks rs (Rec.masks rs xs) ≡ xs.
    Proof.
      cofix; intros.
      unfold_Stv rs; unfold_St xs.
      - constructor; simpl; auto.
        admit.
      - constructor; simpl; auto.
        admit.
    Admitted.

    Definition map_history: (Stream value -> Stream value) -> history -> history.
    Admitted.

    Fact map_history_spec:
      forall H x xs f,
        sem_var H x xs ->
        sem_var (map_history f H) x (f xs).
    Admitted.

    Definition mask_history (n: nat) (rs: Stream bool) (H: history) : history :=
      map_history (Rec.mask n rs) H.

    Corollary mask_history_spec:
      forall n rs H x xs,
        sem_var H x xs ->
        sem_var (mask_history n rs H) x (Rec.mask n rs xs).
    Proof.
      intros; apply map_history_spec; auto.
    Qed.

    Lemma WireRec_node_reset:
      forall rs f ess oss,
        Wire.sem_node G (Wire.merge_reset false_s (reset_of rs)) f ess oss ->
        (* Rec.sem_node G f ess oss -> *)
        Rec.sem_reset G f (reset_of rs) ess oss.
    Proof.
      intros ** Reset (* Node *).
      rewrite merge_reset_with_false in Reset.
      constructor.
      inversion_clear Reset as [? ? ? ? ? ? ? In Out Sem].
      intro i.
      econstructor; eauto.
      instantiate (1:=mask_history i (reset_of rs) H).
      - admit.
      - admit.
      - induction (n_eqs n) as [|e]; auto.
        inversion_clear Sem as [|? ? Sem_e].
        constructor; auto.
        remember (clocks_of ess) as b.
        remember (reset_of rs) as r.
        induction Sem_e.
        + apply (mask_history_spec i r)in H3.
          econstructor; eauto.
      - econstructor; eauto.
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
