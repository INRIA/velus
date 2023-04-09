From Coq Require Import String.
From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Velus Require Import Common.
From Velus Require Import CommonList.
From Velus Require Import FunctionalEnvironment.
From Velus Require Import Operators.
From Velus Require Import CoindStreams.
From Velus Require Import Clocks.
From Velus Require Import Lustre.StaticEnv.
From Velus Require Import Lustre.LSyntax Lustre.LTyping Lustre.LCausality Lustre.LOrdered Lustre.LSemantics.

(** ** Proof of the determinism of the coinductive semantics
    We can proove that the semantics of a causal program are deterministic:
    That is, a node always return the same output for a given input.
 *)
Module Type LSEMDETERMINISM
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks   : CLOCKS        Ids Op OpAux)
       (Import Senv  : STATICENV     Ids Op OpAux Cks)
       (Import Syn   : LSYNTAX Ids Op OpAux Cks Senv)
       (Import Typ   : LTYPING Ids Op OpAux Cks Senv Syn)
       (Import LCA   : LCAUSALITY Ids Op OpAux Cks Senv Syn)
       (Import Lord  : LORDERED Ids Op OpAux Cks Senv Syn)
       (Import CStr  : COINDSTREAMS Ids Op OpAux Cks)
       (Import Sem   : LSEMANTICS Ids Op OpAux Cks Senv Syn Lord CStr).

  Import List.

  (** Induction hypothesis over the program *)
  Definition det_nodes {PSyn prefs} (G : @global PSyn prefs) := forall f n ins1 ins2 outs1 outs2,
      Forall2 (EqStN n) ins1 ins2 ->
      sem_node G f ins1 outs1 ->
      sem_node G f ins2 outs2 ->
      Forall2 (EqStN n) outs1 outs2.

  Lemma det_nodes_ins {PSyn prefs} : forall (G : @global PSyn prefs) f ins outs1 outs2,
      det_nodes G ->
      sem_node G f ins outs1 ->
      sem_node G f ins outs2 ->
      EqSts outs1 outs2.
  Proof.
    intros * Hdet Hsem1 Hsem2.
    eapply EqStN_EqSts; intros.
    eapply Hdet. 2,3:eauto.
    eapply Forall2_same, Forall_forall; intros. reflexivity.
  Qed.

  Lemma EqStN_mask {A} (absent : A) : forall n rs1 rs2 xs1 xs2,
      EqStN n rs1 rs2 ->
      EqStN n xs1 xs2 ->
      forall k, EqStN n (mask absent k rs1 xs1) (mask absent k rs2 xs2).
  Proof.
    intros * Heqr Heqx ?.
    apply EqStN_spec. intros. rewrite 2 mask_nth.
    assert ((count rs1) # k0 = (count rs2) # k0) as Hcount.
    { eapply EqStN_spec; eauto using count_EqStN. }
    rewrite Hcount; clear Hcount.
    destruct (_ =? _); auto.
    eapply EqStN_spec; eauto.
  Qed.

  Corollary EqStNs_mask {A} (absent : A) : forall n rs1 rs2 xs1 xs2,
      EqStN n rs1 rs2 ->
      Forall2 (EqStN n) xs1 xs2 ->
      forall k, Forall2 (EqStN n) (List.map (mask absent k rs1) xs1) (List.map (mask absent k rs2) xs2).
  Proof.
    intros * Heq1 Heq2 ?.
    rewrite Forall2_map_1, Forall2_map_2.
    eapply Forall2_impl_In; [|eauto]; intros.
    eapply EqStN_mask; eauto.
  Qed.

  Global Hint Resolve EqStN_mask EqStNs_mask : coindstreams.

  Lemma EqStN_unmask {A} (absent : A) : forall n rs1 rs2 xs1 xs2,
      EqStN n rs1 rs2 ->
      (forall k, EqStN n (mask absent k rs1 xs1) (mask absent k rs2 xs2)) ->
      EqStN n xs1 xs2.
  Proof.
    intros * Heq1 Heq2.
    apply EqStN_spec; intros.
    assert ((count rs1) # k = (count rs2) # k) as Hcount.
    { eapply EqStN_spec; eauto using count_EqStN. }
    specialize (Heq2 ((count rs1) # k)). eapply EqStN_spec in Heq2; [|eauto].
    rewrite 2 mask_nth, Hcount, Nat.eqb_refl in Heq2. auto.
  Qed.

  Corollary EqStNs_unmask {A} (absent : A) : forall n rs1 rs2 xs1 xs2,
      EqStN n rs1 rs2 ->
      (forall k, Forall2 (EqStN n) (List.map (mask absent k rs1) xs1) (List.map (mask absent k rs2) xs2)) ->
      Forall2 (EqStN n) xs1 xs2.
  Proof.
    intros * Heq1 Heq2.
    setoid_rewrite Forall2_map_1 in Heq2. setoid_rewrite Forall2_map_2 in Heq2.
    eapply Forall2_forall2; split; intros.
    - specialize (Heq2 0). now eapply Forall2_length in Heq2.
    - eapply EqStN_unmask; eauto.
      intros k. specialize (Heq2 k).
      eapply Forall2_forall2 in Heq2 as (_&Heq2); eauto.
  Qed.

  Global Hint Resolve EqStN_unmask EqStNs_unmask : coindstreams.

  Section sem_equation_det.
    Context {PSyn : list decl -> block -> Prop}.
    Context {prefs : PS.t}.
    Variable (G : @global PSyn prefs).

    Hypothesis HdetG : det_nodes G.

    Variable Γ : static_env.

    Definition det_var n (Hi1 Hi2 : history) x :=
      forall vs1 vs2,
        sem_var Hi1 x vs1 ->
        sem_var Hi2 x vs2 ->
        EqStN n vs1 vs2.

    Definition det_var_inv n (Hi1 Hi2 : history) : ident -> Prop :=
      fun cx => (forall x, HasCaus Γ x cx -> det_var n Hi1 Hi2 (Var x))
             /\ (forall x, HasLastCaus Γ x cx -> det_var n Hi1 Hi2 (Last x)).

    Definition def_stream := Streams.const (@absent value).

    Definition det_exp_inv n H1 H2 bs1 bs2 : exp -> nat -> Prop :=
      fun e k => forall ss1 ss2,
          wt_exp G Γ e ->
          sem_exp G H1 bs1 e ss1 ->
          sem_exp G H2 bs2 e ss2 ->
          EqStN n (nth k ss1 def_stream) (nth k ss2 def_stream).

    Lemma P_exps_det_exp_inv : forall n H1 H2 bs1 bs2 es k ss1 ss2,
        Forall (wt_exp G Γ) es ->
        P_exps (det_exp_inv n H1 H2 bs1 bs2) es k ->
        Forall2 (sem_exp G H1 bs1) es ss1 ->
        Forall2 (sem_exp G H2 bs2) es ss2 ->
        EqStN n (nth k (concat ss1) def_stream) (nth k (concat ss2) def_stream).
    Proof.
      induction es; intros * Hwt Hp Hsem1 Hsem2;
        inv Hwt; inv Hsem1; inv Hsem2; simpl. inv Hp.
      assert (length y = numstreams a) as Hlen1 by (eapply sem_exp_numstreams; eauto with ltyping).
      assert (length y0 = numstreams a) as Hlen2 by (eapply sem_exp_numstreams; eauto with ltyping).
      inv Hp.
      - (* now *)
        rewrite 2 app_nth1; try congruence.
        eapply H11; eauto.
      - (* later *)
        rewrite 2 app_nth2; try congruence.
        rewrite Hlen2, Hlen1.
        eapply IHes; eauto.
    Qed.

    Lemma Forall2Brs_det_exp_inv : forall n H1 H2 bs1 bs2 es k ss1 ss2,
        k < length ss1 ->
        Forall (fun es => Forall (wt_exp G Γ) (snd es)) es ->
        Forall (fun es => P_exps (det_exp_inv n H1 H2 bs1 bs2) (snd es) k) es ->
        Forall2Brs (sem_exp G H1 bs1) es ss1 ->
        Forall2Brs (sem_exp G H2 bs2) es ss2 ->
        Forall2 (fun xs1 xs2 => EqStN n (snd xs1) (snd xs2)) (nth k ss1 []) (nth k ss2 []).
    Proof.
      induction es; intros * Hlen Hwt Hp Hsem1 Hsem2;
        inv Hwt; inv Hsem1; inv Hsem2; simpl; inv Hp.
      { eapply Forall_forall in H; [|eapply nth_In]. rewrite H. 2:auto.
        destruct (Compare_dec.dec_lt k (length ss2)).
        eapply Forall_forall in H0; [|eapply nth_In]. rewrite H0. 2:auto. constructor.
        erewrite nth_overflow; auto. lia.
      }
      eapply P_exps_det_exp_inv in H9 as Heq1. 3:eauto. 2,3:eauto.
      eapply IHes in H11 as Heq2. 3-5:eauto.
      2:{ eapply Forall3_length in H8 as (?&?). congruence. }
      assert (length (concat vs1) = length (concat vs0)) as Hlen0.
      { eapply sem_exps_numstreams in H5; eauto with ltyping.
        eapply sem_exps_numstreams in H9; eauto with ltyping. congruence. }
      clear - Hlen Hlen0 H8 H12 Heq1 Heq2.
      eapply Forall3_forall3 in H8 as (?&?&?).
      eapply Forall3_forall3 in H12 as (?&?&?).
      erewrite H1 at 1; try reflexivity.
      erewrite H4; try reflexivity.
      constructor; eauto.
      1,2:congruence.
    Qed.

    Lemma P_exps_det_exp_inv_all : forall n H1 H2 bs1 bs2 es ss1 ss2,
        Forall (wt_exp G Γ) es ->
        (forall k, k < length (annots es) -> P_exps (det_exp_inv n H1 H2 bs1 bs2) es k) ->
        Forall2 (sem_exp G H1 bs1) es ss1 ->
        Forall2 (sem_exp G H2 bs2) es ss2 ->
        Forall2 (EqStN n) (concat ss1) (concat ss2).
    Proof.
      intros * Hwt Hk Hsem1 Hsem2.
      assert (length (concat ss1) = length (annots es)) as Hlen1.
      { eapply sem_exps_numstreams; eauto with ltyping. }
      assert (length (concat ss2) = length (annots es)) as Hlen2.
      { eapply sem_exps_numstreams; eauto with ltyping. }
      eapply Forall2_forall2; split. congruence.
      intros * Hn ? ?; subst.
      erewrite nth_indep with (d:=a) (d':=def_stream); auto.
      erewrite nth_indep with (d:=b) (d':=def_stream); try congruence.
      eapply P_exps_det_exp_inv; eauto.
      eapply Hk. congruence.
    Qed.

    (** We first establish the determinism of all the coinductive operators,
        as well as the expression semantics.
        We show that they are deterministic "up-to-n" : that is they preserve
        the equality "up-to-n".
        Proving this for any n is stronger than just proving that they output the
        same stream for the same input, as we can use `EqStN_EqSt` to rewrite
        the conclusion and hypotheses.
    *)

    Hint Constructors EqStN : core.

    Lemma const_detn : forall n bs1 bs2 c,
        EqStN n bs1 bs2 ->
        EqStN n (const bs1 c) (const bs2 c).
    Proof.
      induction n; intros * Hbs; auto.
      inv Hbs. do 2 rewrite const_Cons.
      constructor; eauto.
    Qed.

    Lemma enum_detn : forall n bs1 bs2 c,
        EqStN n bs1 bs2 ->
        EqStN n (enum bs1 c) (enum bs2 c).
    Proof.
      induction n; intros * Hbs; auto.
      inv Hbs. rewrite (unfold_Stream (enum (_ ⋅ xs1) _)), (unfold_Stream (enum (_ ⋅ xs2) _)).
      constructor; eauto.
    Qed.

    Lemma lift1_detn : forall n op ty xs1 xs2 ys1 ys2,
        EqStN n xs1 xs2 ->
        lift1 op ty xs1 ys1 ->
        lift1 op ty xs2 ys2 ->
        EqStN n ys1 ys2.
    Proof.
      induction n; intros * Heq Hl1 Hl2; auto.
      inv Heq; inv Hl1; inv Hl2; constructor; eauto.
      rewrite H2 in H3. now inv H3.
    Qed.

    Lemma lift2_detn : forall n op ty1 ty2 xs11 xs12 xs21 xs22 ys1 ys2,
        EqStN n xs11 xs21 ->
        EqStN n xs12 xs22 ->
        lift2 op ty1 ty2 xs11 xs12 ys1 ->
        lift2 op ty1 ty2 xs21 xs22 ys2 ->
        EqStN n ys1 ys2.
    Proof.
      induction n; intros * Heq1 Heq2 Hl1 Hl2; auto.
      inv Heq1; inv Heq2; inv Hl1; inv Hl2; constructor; eauto.
      rewrite H6 in H8. now inv H8.
    Qed.

    Lemma liftn_detn : forall n f tyins tyout xss1 xss2 ys1 ys2,
        xss1 <> [] ->
        Forall2 (EqStN n) xss1 xss2 ->
        liftn (fun vs v => sem_extern f tyins vs tyout v) xss1 ys1 ->
        liftn (fun vs v => sem_extern f tyins vs tyout v) xss2 ys2 ->
        EqStN n ys1 ys2.
    Proof.
      intros * Hnnil Heqsts Hl1 Hl2.
      apply EqStN_spec; intros * Hlt.
      apply liftn_spec with (n:=k) in Hl1. apply liftn_spec with (n:=k) in Hl2.
      destruct Hl1 as [(?&?)|(?&?&?&?&?)], Hl2 as [(?&?)|(?&?&?&?&?)]; try congruence.
      - exfalso. eapply Forall2_ignore2 in H1.
        inv Heqsts; try congruence; simpl_Forall.
        take (EqStN _ x1 y) and eapply EqStN_spec in it; rename it into contra; eauto.
        take (_ = absent) and setoid_rewrite it in contra.
        take (_ = present _) and setoid_rewrite it in contra. congruence.
      - exfalso. eapply Forall2_ignore2 in H.
        inv Heqsts; try congruence; simpl_Forall.
        take (EqStN _ x1 y) and eapply EqStN_spec in it; rename it into contra; eauto.
        take (_ = absent) and setoid_rewrite it in contra.
        take (_ = present _) and setoid_rewrite it in contra. congruence.
      - take (ys1 # k = _) and rewrite it.
        take (ys2 # k = _) and rewrite it.
        repeat f_equal.
        eapply sem_extern_det; eauto. replace x with x1; auto.
        clear - Hlt Heqsts H H2.
        apply Forall2_swap_args in H. eapply Forall2_trans_ex in Heqsts; [|eauto].
        eapply Forall2_trans_ex in H2; [|eauto].
        clear - Hlt H2. induction H2; destruct_conjs; f_equal; auto.
        eapply EqStN_spec in H4; eauto.
        setoid_rewrite H3 in H4. setoid_rewrite H1 in H4. now inv H4.
    Qed.

    Corollary fby_detn {A} : forall n (xs1 xs2 ys1 ys2 zs1 zs2 : Stream (synchronous A)),
        EqStN n xs1 xs2 ->
        EqStN n ys1 ys2 ->
        fby xs1 ys1 zs1 ->
        fby xs2 ys2 zs2 ->
        EqStN n zs1 zs2.
    Proof.
      induction n; intros * Heq1 Heq2 Hfby1 Hfby2; inv Heq1; inv Heq2;
        inv Hfby1; inv Hfby2; constructor; auto. eauto.
      clear IHn. revert y xs0 xs1 xs3 xs2 rs rs0 H1 H2 H6 H7.
      induction n; intros * Heq1 Heq2 Hfby1 Hfby2; inv Heq1; inv Heq2;
        inv Hfby1; inv Hfby2; constructor; eauto.
    Qed.

    Lemma arrow_detn : forall n xs1 xs2 ys1 ys2 zs1 zs2,
        EqStN n xs1 xs2 ->
        EqStN n ys1 ys2 ->
        arrow xs1 ys1 zs1 ->
        arrow xs2 ys2 zs2 ->
        EqStN n zs1 zs2.
    Proof.
      induction n; intros * Heq1 Heq2 Hfby1 Hfby2; inv Heq1; inv Heq2;
        inv Hfby1; inv Hfby2; constructor; auto. eauto.
      clear IHn. revert xs0 xs1 xs3 xs2 rs rs0 H1 H2 H6 H7.
      induction n; intros * Heq1 Heq2 Hfby1 Hfby2; inv Heq1; inv Heq2;
        inv Hfby1; inv Hfby2; constructor; eauto.
    Qed.

    Lemma when_detn : forall n k xs1 xs2 ys1 ys2 zs1 zs2,
        EqStN n xs1 xs2 ->
        EqStN n ys1 ys2 ->
        when k xs1 ys1 zs1 ->
        when k xs2 ys2 zs2 ->
        EqStN n zs1 zs2.
    Proof.
      induction n; intros * Heq1 Heq2 Hwhen1 Hwhen2; inv Heq1; inv Heq2; auto.
      inv Hwhen1; inv Hwhen2; constructor; eauto.
      1,2:congruence.
    Qed.

    Lemma merge_detn : forall n cs1 cs2 xss1 xss2 ys1 ys2,
        map fst xss1 = map fst xss2 ->
        NoDupMembers xss1 ->
        EqStN n cs1 cs2 ->
        Forall2 (fun xs1 xs2 => EqStN n (snd xs1) (snd xs2)) xss1 xss2 ->
        merge cs1 xss1 ys1 ->
        merge cs2 xss2 ys2 ->
        EqStN n ys1 ys2.
    Proof.
      induction n; intros * Hfst Hnd Heq1 Heq2 Hmerge1 Hmerge2; inv Heq1; auto.
      inv Hmerge1; inv Hmerge2; constructor; eauto.
      1,3:eapply IHn. 5,6,11,12:eauto. 1-8:eauto.
      1,4:erewrite 2 map_map, map_ext with (l:=xss1), map_ext with (l:=xss2); eauto; intros (?&?); auto.
      1,3:apply NoDupMembers_map; auto.
      1,2:simpl_Forall; take (EqStN (S _) _ _) and inv it; auto.
      clear - Hfst Hnd Heq2 H3 H5. unfold EqSts in *.
      induction Heq2; inv H3; inv H5; inv Hnd; simpl in *; inv Hfst; auto.
      - destruct y, H1, H2; subst; simpl in *.
        rewrite <-H1, <-H3. inv H; auto.
      - exfalso. destruct y, H1; subst; simpl in *.
        eapply H4. rewrite fst_InMembers, H6, <-fst_InMembers.
        simpl_Exists; subst; eauto using In_InMembers.
      - exfalso. destruct y, H2; subst; simpl in *.
        eapply H4. rewrite fst_InMembers, <-fst_InMembers.
        simpl_Exists; subst; eauto using In_InMembers.
    Qed.

    Lemma case_detn : forall n cs1 cs2 xss1 xss2 ys1 ys2 ds1 ds2,
        map fst xss1 = map fst xss2 ->
        NoDupMembers xss1 ->
        EqStN n cs1 cs2 ->
        Forall2 (fun xs1 xs2 => EqStN n (snd xs1) (snd xs2)) xss1 xss2 ->
        (forall d1 d2, ds1 = Some d1 -> ds2 = Some d2 -> EqStN n d1 d2) ->
        case cs1 xss1 ds1 ys1 ->
        case cs2 xss2 ds2 ys2 ->
        EqStN n ys1 ys2.
    Proof.
      induction n; intros * Hfst Hnd Heq1 Heq2 Heq3 Hcase1 Hcase2; inv Heq1; auto.
      inv Hcase1; inv Hcase2.
      - econstructor; eauto.
        eapply IHn. 6,7:eauto. 1-5:intros; eauto.
        erewrite 2 map_map, map_ext with (l:=xss1), map_ext with (l:=xss2); eauto; intros (?&?); auto.
        apply NoDupMembers_map; auto.
        simpl_Forall; take (EqStN (S _) _ _) and inv it; auto.
        inv_equalities.
        specialize (Heq3 _ _ eq_refl eq_refl). inv Heq3; auto.
      - econstructor; eauto.
        + clear - Hfst Hnd Heq2 H8 H12. unfold EqSts in *.
          induction Heq2; inv H8; inv H12; inv Hnd; simpl in *; inv Hfst; auto.
          * destruct y, H1, H2; subst; simpl in *.
            rewrite <-H1, <-H3. inv H; auto.
          * exfalso. destruct y, H1; subst; simpl in *.
            eapply H4. rewrite fst_InMembers, H6, <-fst_InMembers.
            simpl_Exists; subst; eauto using In_InMembers.
          * exfalso. destruct y, H2; subst; simpl in *.
            eapply H4. rewrite fst_InMembers, <-fst_InMembers.
            simpl_Exists; subst; eauto using In_InMembers.
        + eapply IHn. 6,7:eauto. 1-5:intros; eauto.
          erewrite 2 map_map, map_ext with (l:=xss1), map_ext with (l:=xss2); eauto; intros (?&?); auto.
          apply NoDupMembers_map; auto.
          simpl_Forall; take (EqStN (S _) _ _) and inv it; auto.
          inv_equalities.
          specialize (Heq3 _ _ eq_refl eq_refl). inv Heq3; auto.
      - exfalso. simpl_Exists.
        eapply In_InMembers, fst_InMembers in Hin. setoid_rewrite Hfst in Hin.
        eapply fst_InMembers, InMembers_In in Hin as (?&Hin).
        unshelve simpl_Forall; eauto.
      - exfalso. simpl_Exists.
        eapply In_InMembers, fst_InMembers in Hin. setoid_rewrite <-Hfst in Hin.
        eapply fst_InMembers, InMembers_In in Hin as (?&Hin).
        unshelve simpl_Forall; eauto.
      - econstructor; eauto.
        + specialize (Heq3 _ _ eq_refl eq_refl). inv Heq3; auto.
        + eapply IHn. 6,7:eauto. 1-5:intros; eauto.
          erewrite 2 map_map, map_ext with (l:=xss1), map_ext with (l:=xss2); eauto; intros (?&?); auto.
          erewrite fst_NoDupMembers, map_map, map_ext, <-fst_NoDupMembers; eauto; intros (?&?); auto.
          simpl_Forall. take (EqStN (S n) _ _) and inv it; auto.
          repeat (take (Some _ = Some _) and inv it).
          specialize (Heq3 _ _ eq_refl eq_refl). inv Heq3; eauto.
    Qed.

    Lemma bools_of_detn : forall n xs1 xs2 bs1 bs2,
        EqStN n xs1 xs2 ->
        bools_of xs1 bs1 ->
        bools_of xs2 bs2 ->
        EqStN n bs1 bs2.
    Proof.
      induction n; intros * Heq Hbools1 Hbools2;
        inv Heq; inv Hbools1; inv Hbools2; eauto.
    Qed.

    Lemma disj_str_detn : forall n xss1 xss2 bs1 bs2,
        Forall2 (EqStN n) xss1 xss2 ->
        bs1 ≡ disj_str xss1 ->
        bs2 ≡ disj_str xss2 ->
        EqStN n bs1 bs2.
    Proof.
      intros * Heq Hdisj1 Hdisj2.
      eapply EqStN_spec. intros * Hlt.
      eapply eqst_ntheq in Hdisj1. eapply eqst_ntheq in Hdisj2.
      rewrite Hdisj1, Hdisj2.
      repeat rewrite disj_str_spec.
      clear - Heq Hlt.
      induction Heq; simpl; auto.
      rewrite IHHeq. f_equal; auto.
      eapply EqStN_spec; eauto.
    Qed.

    Corollary bools_ofs_detn : forall n xss1 xss2 bs1 bs2,
        Forall2 (EqStN n) xss1 xss2 ->
        bools_ofs xss1 bs1 ->
        bools_ofs xss2 bs2 ->
        EqStN n bs1 bs2.
    Proof.
      intros * Heq (?&Hb1&Hdisj1) (?&Hb2&Hdisj2).
      eapply disj_str_detn. 2,3:eauto.
      clear - Heq Hb1 Hb2.
      revert x x0 Hb1 Hb2.
      induction Heq; intros; inv Hb1; inv Hb2; constructor; eauto.
      eapply bools_of_detn; eauto.
    Qed.

    Fact det_exps_n' : forall n Hi1 Hi2 bs1 bs2 es ss1 ss2,
        Forall (fun e => forall ss1 ss2,
                    wt_exp G Γ e ->
                    sem_exp G Hi1 bs1 e ss1 ->
                    sem_exp G Hi2 bs2 e ss2 ->
                    Forall2 (EqStN n) ss1 ss2) es ->
        Forall (wt_exp G Γ) es->
        Forall2 (sem_exp G Hi1 bs1) es ss1 ->
        Forall2 (sem_exp G Hi2 bs2) es ss2 ->
        Forall2 (EqStN n) (concat ss1) (concat ss2).
    Proof.
      intros * Hf. revert ss1 ss2.
      induction Hf; intros * Hwt Hsem1 Hsem2;
        inv Hwt; inv Hsem1; inv Hsem2; simpl; auto.
      apply Forall2_app; eauto.
    Qed.

    Lemma Forall2Brs_det_exp_n' : forall n H1 H2 bs1 bs2 es ss1 ss2,
        Forall
          (fun es =>
             Forall
               (fun e =>
                  forall ss1 ss2,
                    wt_exp G Γ e ->
                    sem_exp G H1 bs1 e ss1 -> sem_exp G H2 bs2 e ss2 -> Forall2 (EqStN n) ss1 ss2)
               (snd es)) es ->
        length ss1 = length ss2 ->
        Forall (fun es => Forall (wt_exp G Γ) (snd es)) es ->
        Forall2Brs (sem_exp G H1 bs1) es ss1 ->
        Forall2Brs (sem_exp G H2 bs2) es ss2 ->
        Forall2 (Forall2 (fun xs1 xs2 => EqStN n (snd xs1) (snd xs2))) ss1 ss2.
    Proof.
      induction es; intros * Hf Hlen Hwt Hsem1 Hsem2;
        inv Hf; inv Hwt; inv Hsem1; inv Hsem2; simpl.
      - revert ss2 Hlen H0.
        induction H; intros * Hl Hf2; destruct ss2; simpl in *; try congruence; inv Hf2.
        1,2:constructor; eauto.
      - eapply IHes in H4. 3-5:eauto. clear IHes.
        2:{ eapply Forall3_length in H10 as (?&?). eapply Forall3_length in H14 as (?&?).
            congruence.
        }
        eapply det_exps_n' in H3; eauto.
        clear - H3 H4 H10 H14. revert vs2 vs3 H10 H14 H3 H4.
        generalize (concat vs0) (concat vs1); clear vs0 vs1.
        intros * Hf1. revert l ss2 vs3.
        induction Hf1; intros * Hf2 Heq1 Heq2; inv Heq1; inv Heq2; inv Hf2; constructor; eauto.
    Qed.

    (** The clocking hypothesis could be replaced with a typing one.
        The important point is that all the variables appearing in the expression
        are in `env`.
        I chose a clocking hypothesis because this lemma is used in the
        clocked-semantics proof. *)
    Lemma det_exp_n : forall n Hi1 Hi2 bs1 bs2 e ss1 ss2,
        (forall x cx, HasCaus Γ x cx \/ HasLastCaus Γ x cx -> det_var_inv n Hi1 Hi2 cx) ->
        EqStN n bs1 bs2 ->
        wt_exp G Γ e ->
        sem_exp G Hi1 bs1 e ss1 ->
        sem_exp G Hi2 bs2 e ss2 ->
        Forall2 (EqStN n) ss1 ss2.
    Proof.
      intros * Hn Hbs. revert ss1 ss2.
      induction e using exp_ind2; intros * Hwt Hs1 Hs2; inv Hwt.
      - (* const *)
        inv Hs1. inv Hs2.
        constructor; auto.
        rewrite H3, H4. eapply const_detn; eauto.
      - (* enum *)
        inv Hs1. inv Hs2.
        constructor; auto.
        rewrite H7, H8. eapply enum_detn; eauto.
      - (* var *)
        inv Hs1. inv Hs2.
        constructor; auto. inv H1. simpl_In.
        edestruct Hn as (Hn1&_). left; econstructor; solve_In; eauto.
        eapply Hn1; eauto. econstructor; solve_In; eauto.
      - (* last *)
        inv Hs1. inv Hs2.
        constructor; auto. inv H2. simpl_In.
        destruct (causl_last e) eqn:Hcaus; try congruence.
        edestruct Hn as (_&Hn2). right; econstructor; solve_In; eauto.
        eapply Hn2; eauto. econstructor; solve_In; eauto.
      - (* unop *)
        inversion_clear Hs1 as [| | | |???????? Hse1 Hty1 Hl1| | | | | | | | |].
        inversion_clear Hs2 as [| | | |???????? Hse2 Hty2 Hl2| | | | | | | | |].
        rewrite Hty2 in Hty1; inv Hty1.
        eapply IHe in Hse1; eauto. inv Hse1.
        constructor; auto.
        eapply lift1_detn; eauto.
      - (* binop *)
        inversion_clear Hs1 as [| | | | |??????????? Hse11 Hse12 Hty11 Hty12 Hl1| | | | | | | |].
        inversion_clear Hs2 as [| | | | |??????????? Hse21 Hse22 Hty21 Hty22 Hl2| | | | | | | |].
        rewrite Hty21 in Hty11; inv Hty11. rewrite Hty22 in Hty12; inv Hty12.
        eapply IHe1 in Hse21; eauto. eapply IHe2 in Hse22; eauto.
        inv Hse21. inv Hse22.
        constructor; auto.
        eapply lift2_detn. 3,4:eauto. 1,2:eauto.
      - (* extcall *)
        inversion_clear Hs1 as [| | | | | |????????? Hty1 Hse1 Hl1| | | | | | |].
        inversion_clear Hs2 as [| | | | | |????????? Hty2 Hse2 Hl2| | | | | | |].
        constructor; auto.
        assert (tyins1 = tyins0); subst.
        { apply Forall2_eq. eapply Forall2_trans_ex in Hty1. 2:eapply Forall2_swap_args, Hty2.
          simpl_Forall. congruence. }
        eapply liftn_detn. 3,4:eauto.
        + eapply sem_exps_numstreams in Hse1; [|eauto with ltyping].
          rewrite typesof_annots in H5.
          destruct (annots es), (concat ss); simpl in *; try congruence.
        + eapply det_exps_n'; eauto.
      - (* fby *)
        inversion_clear Hs1 as [| | | | | | |???????? Hse11 Hse12 Hfby1| | | | | |].
        inversion_clear Hs2 as [| | | | | | |???????? Hse21 Hse22 Hfby2| | | | | |].
        eapply det_exps_n' in H; eauto.
        eapply det_exps_n' in H0; eauto.
        clear - H H0 Hfby1 Hfby2.
        rewrite_Forall_forall.
        1:{ setoid_rewrite <-H4. setoid_rewrite <-H7. auto. }
        eapply fby_detn.
        + eapply H2 with (a:=def_stream) (b:=def_stream) (n:=n0); eauto.
          setoid_rewrite H7; auto.
        + eapply H1 with (a:=def_stream) (b:=def_stream) (n:=n0); eauto.
          setoid_rewrite <-H6. setoid_rewrite H7. auto.
        + eapply H8; eauto. setoid_rewrite H7; auto.
        + eapply H5; eauto. setoid_rewrite <-H. setoid_rewrite H7. auto.
      - (* arrow *)
        inversion_clear Hs1 as [| | | | | | | |???????? Hse11 Hse12 Harrow1| | | | |].
        inversion_clear Hs2 as [| | | | | | | |???????? Hse21 Hse22 Harrow2| | | | |].
        eapply det_exps_n' in H; eauto.
        eapply det_exps_n' in H0; eauto.
        clear - H H0 Harrow1 Harrow2.
        rewrite_Forall_forall. congruence.
        eapply arrow_detn.
        + eapply H2 with (a:=def_stream) (b:=def_stream) (n:=n0); eauto. congruence.
        + eapply H1 with (a:=def_stream) (b:=def_stream) (n:=n0); eauto. congruence.
        + eapply H8; eauto; congruence.
        + eapply H5; eauto; congruence.
      - (* when *)
        repeat simpl_In.
        inversion_clear Hs1 as [| | | | | | | | |?????????? Hse1 Hsv1 Hwhen1| | | |].
        inversion_clear Hs2 as [| | | | | | | | |?????????? Hse2 Hsv2 Hwhen2| | | |].
        eapply det_exps_n' in H; eauto.
        take (HasType _ _ _) and inv it; simpl_In.
        edestruct Hn as (Hn1&_). left; econstructor; solve_In; eauto.
        eapply Hn1 in Hsv1; eauto. 2:econstructor; solve_In; eauto.
        clear - H Hsv1 Hwhen1 Hwhen2.
        rewrite_Forall_forall. congruence.
        eapply when_detn. 2:eauto.
        + eapply e1 with (a:=def_stream) (b:=def_stream) (n:=n0); eauto. congruence.
        + eapply w0; eauto; congruence.
        + eapply w; eauto; congruence.
      - (* merge *)
        repeat simpl_In.
        inversion_clear Hs1 as [| | | | | | | | | |????????? Hsv1 Hse1 Hmerge1| | |].
        inversion_clear Hs2 as [| | | | | | | | | |????????? Hsv2 Hse2 Hmerge2| | |].
        inv H3; simpl_In.
        edestruct Hn as (Hn1&_). left; econstructor; solve_In; eauto.
        eapply Hn1 in Hsv1; eauto. specialize (Hsv1 Hsv2). 2:econstructor; solve_In; eauto.
        eapply Forall2Brs_det_exp_n' in H. 3-5:eauto.
        2:{ eapply Forall2Brs_length1 in Hse1. eapply Forall2Brs_length1 in Hse2.
            2,3:do 2 (eapply Forall_forall; intros); eapply sem_exp_numstreams; eauto.
            2,3:do 2 (eapply Forall_forall in H7; eauto with ltyping).
            inv Hse1; inv Hse2; try congruence. exfalso; auto.
        }
        eapply Forall2Brs_fst in Hse1. eapply Forall2Brs_fst in Hse2.
        clear - Hmerge1 Hmerge2 Hsv1 H H5 Hse1 Hse2. revert vs0 ss2 Hsv1 Hmerge2 H Hse1 Hse2.
        induction Hmerge1; intros * Hsv1 Hmerge2 Heq Hse1 Hse2;
          inv Heq; inv Hmerge2; inv Hse1; inv Hse2;
            constructor; eauto.
        eapply merge_detn. 5,6:eauto. 1-4:eauto.
        congruence.
        rewrite fst_NoDupMembers, H6, H5. apply seq_NoDup.
      - (* case *)
        inversion_clear Hs1 as [| | | | | | | | | | |????????? Hsv1 Hse1 Hcase1| |].
        inversion_clear Hs2 as [| | | | | | | | | | |????????? Hsv2 Hse2 Hcase2| |].
        eapply IHe in Hsv2; eauto. apply Forall2_singl in Hsv2.
        eapply Forall2Brs_det_exp_n' in H. 3-5:eauto.
        2:{ eapply Forall2Brs_length1 in Hse1. eapply Forall2Brs_length1 in Hse2.
            2,3:do 2 (eapply Forall_forall; intros); eapply sem_exp_numstreams; eauto.
            2,3:do 2 (eapply Forall_forall in H10; eauto with ltyping).
            inv Hse1; inv Hse2; try congruence. exfalso; auto.
        }
        eapply Forall2Brs_fst in Hse1. eapply Forall2Brs_fst in Hse2.
        clear - Hcase1 Hcase2 Hsv2 H H8 Hse1 Hse2. revert vs0 ss2 Hsv2 Hcase2 H Hse1 Hse2.
        induction Hcase1; intros * Hsv2 Hcase2 Heq Hse1 Hse2;
          inv Heq; inv Hcase2; inv Hse1; inv Hse2;
            constructor; eauto.
        eapply case_detn. 6,7:eauto. 1-5:eauto.
        congruence.
        rewrite fst_NoDupMembers, H5, H8. apply seq_NoDup.
        intros. congruence.
      - (* case (default) *)
        inversion_clear Hs1 as [| | | | | | | | | | | |?????????? Hsv1 _ Hse1 Hd1 Hcase1|].
        inversion_clear Hs2 as [| | | | | | | | | | | |?????????? Hsv2 _ Hse2 Hd2 Hcase2|].
        eapply IHe in Hsv2; eauto. apply Forall2_singl in Hsv2.
        eapply Forall2Brs_det_exp_n' in H. 3-5:eauto.
        2:{ eapply Forall2Brs_length1 in Hse1. eapply Forall2Brs_length1 in Hse2.
            2,3:do 2 (eapply Forall_forall; intros); eapply sem_exp_numstreams; eauto.
            2,3:do 2 (eapply Forall_forall in H11; eauto with ltyping).
            inv Hse1; inv Hse2; try congruence. exfalso; auto.
        }
        eapply det_exps_n' in Hd2; eauto.
        eapply Forall2Brs_fst in Hse1. eapply Forall2Brs_fst in Hse2.
        rewrite Forall3_map_2 in Hcase1. rewrite Forall3_map_2 in Hcase2.
        clear - Hcase1 Hcase2 Hsv2 H H9 Hse1 Hse2 Hd2. revert Hcase1 Hsv2 Hcase2 H Hse1 Hse2 Hd2.
        generalize (concat vd). generalize (concat vd0). intros * Hcase1. revert vs0 l ss2.
        induction Hcase1; intros * Hsv2 Hcase2 Heq Hse1 Hse2 Hd2;
          inv Heq; inv Hcase2; inv Hse1; inv Hse2; inv Hd2;
            constructor; eauto.
        eapply case_detn. 6,7:eauto. 1-5:eauto.
        congruence.
        rewrite fst_NoDupMembers, H5, <-fst_NoDupMembers; auto.
        intros ?? Heq1 Heq2. inv Heq1. inv Heq2. assumption.
      - (* app *)
        inversion_clear Hs1 as [| | | | | | | | | | | | |?????????? Hes1 Her1 Hbools1 Hn1].
        inversion_clear Hs2 as [| | | | | | | | | | | | |?????????? Hes2 Her2 Hbools2 Hn2].
        eapply det_exps_n' in H; eauto.
        rewrite <-Forall2_map_2 in Her1, Her2.
        eapply det_exps_n' in H0; eauto. repeat rewrite concat_map_singl1 in H0.
        eapply bools_ofs_detn in Hbools2; eauto.
        eapply EqStNs_unmask; [eapply Hbools2|]; intros. clear H0.
        eapply HdetG. 2,3:eauto.
        eapply EqStNs_mask; eauto.
    Qed.

    Corollary det_exps_n : forall n Hi1 Hi2 bs1 bs2 es ss1 ss2,
        (forall x cx, HasCaus Γ x cx \/ HasLastCaus Γ x cx -> det_var_inv n Hi1 Hi2 cx) ->
        EqStN n bs1 bs2 ->
        Forall (wt_exp G Γ) es ->
        Forall2 (sem_exp G Hi1 bs1) es ss1 ->
        Forall2 (sem_exp G Hi2 bs2) es ss2 ->
        Forall2 (EqStN n) (concat ss1) (concat ss2).
    Proof.
      intros * Hin Hbs Hwt Hsem1 Hsem2.
      eapply Forall2_concat.
      eapply Forall2_trans_ex in Hsem2; [|eapply Forall2_swap_args, Hsem1].
      eapply Forall2_impl_In; [|eauto]; intros ?? _ _ (?&Hin'&(Hs1&Hs2)).
      rewrite Forall_forall in *.
      eapply det_exp_n; eauto.
    Qed.

    Corollary det_exp : forall Hi bs e ss1 ss2,
        wt_exp G Γ e ->
        sem_exp G Hi bs e ss1 ->
        sem_exp G Hi bs e ss2 ->
        EqSts ss1 ss2.
    Proof.
      intros * Hwt Hs1 Hs2.
      eapply EqStN_EqSts. intros n.
      eapply det_exp_n; eauto.
      + intros * _.
        split; intros ??????; eapply EqStN_EqSt, sem_var_det; eauto.
      + reflexivity.
    Qed.

    Corollary det_exps : forall Hi bs es ss1 ss2,
        Forall (wt_exp G Γ) es ->
        Forall2 (sem_exp G Hi bs) es ss1 ->
        Forall2 (sem_exp G Hi bs) es ss2 ->
        EqSts (concat ss1) (concat ss2).
    Proof.
      intros * Hwt Hs1 Hs2.
      eapply EqStN_EqSts. intros n.
      eapply det_exps_n; eauto.
      + intros * _.
        split; intros ??????; eapply EqStN_EqSt, sem_var_det; eauto.
      + reflexivity.
    Qed.

    (** We reason inductively on the length of streams.
        Given that all the streams in the environnement are equal "up-to",
        we need to proove that they are equal "up-to" n+1.
        This can be established using causality, by following the causal order of the variables.
        The interesting case is the fby operator, where the causality hypothesis doesn't tell us
        anything about the expression on the right.
        Fortunately, the following lemma indicates that we only need to know about equality "up-to" n
        for the right-side stream of a fby, as the output only depends on its previous value.
     *)

    Lemma fby_det_Sn {A} : forall n (xs1 xs2 ys1 ys2 zs1 zs2 : Stream (synchronous A)),
        EqStN (S n) xs1 xs2 ->
        EqStN n ys1 ys2 ->
        fby xs1 ys1 zs1 ->
        fby xs2 ys2 zs2 ->
        EqStN (S n) zs1 zs2.
    Proof.
      induction n; intros * Heq1 Heq2 Hfby1 Hfby2; inv Heq1; inv Heq2;
        inv Hfby1; inv Hfby2; constructor; auto. eauto.
      clear IHn. revert y xs0 xs1 xs3 xs2 rs rs0 H1 H2 H6 H7.
      induction n; intros * Heq1 Heq2 Hfby1 Hfby2; inv Heq1; inv Heq2;
        inv Hfby1; inv Hfby2; constructor; eauto.
    Qed.

    Lemma det_exp_S : forall n Hi1 Hi2 bs1 bs2 e k,
        (forall x cx, HasCaus Γ x cx \/ HasLastCaus Γ x cx -> det_var_inv n Hi1 Hi2 cx) ->
        wt_exp G Γ e ->
        k < numstreams e ->
        EqStN (S n) bs1 bs2 ->
        (forall x, Is_used_inst Γ x k e -> det_var_inv (S n) Hi1 Hi2 x) ->
        det_exp_inv (S n) Hi1 Hi2 bs1 bs2 e k.
    Proof.
      intros * Hn Hwt Hnum Hbs HSn.
      eapply exp_causal_ind
        with (P_exp:=det_exp_inv (S n) Hi1 Hi2 bs1 bs2); eauto with ltyping.
      1-13:clear Hwt HSn.
      - (* const *)
        intros ??? Hwt Hs1 Hs2. inv Hs1. inv Hs2. simpl.
        rewrite H3, H4. eapply const_detn; eauto.
      - (* enum *)
        intros ???? Hwt Hs1 Hs2. inv Hs1. inv Hs2. simpl.
        rewrite H5, H6. eapply enum_detn; eauto.
      - (* var *)
        intros ???? Hvar ?? Hwt Hs1 Hs2. inv Hwt. inv Hs1. inv Hs2. simpl.
        edestruct Hvar as (Hv&_). eapply Hv; eauto.
      - (* last *)
        intros ???? Hvar ?? Hwt Hs1 Hs2. inv Hwt. inv Hs1. inv Hs2. simpl.
        edestruct Hvar as (_&Hv). eapply Hv; eauto.
      - (* unop *)
        intros ??? He1 ?? Hwt Hs1 Hs2. inv Hwt.
        inversion_clear Hs1 as [| | | |???????? Hse1 Hty1 Hl1| | | | | | | | |].
        inversion_clear Hs2 as [| | | |???????? Hse2 Hty2 Hl2| | | | | | | | |].
        rewrite Hty2 in Hty1; inv Hty1.
        eapply He1 in Hse2; eauto. simpl in *.
        eapply lift1_detn; eauto.
      - (* binop *)
        intros ???? He1 He2 ?? Hwt Hs1 Hs2. inv Hwt.
        inversion_clear Hs1 as [| | | | |??????????? Hse11 Hse12 Hty11 Hty12 Hl1| | | | | | | |].
        inversion_clear Hs2 as [| | | | |??????????? Hse21 Hse22 Hty21 Hty22 Hl2| | | | | | | |].
        rewrite Hty21 in Hty11; inv Hty11. rewrite Hty22 in Hty12; inv Hty12.
        eapply He1 in Hse21; eauto. eapply He2 in Hse22; eauto. simpl in *.
        eapply lift2_detn. 3,4:eauto. 1,2:eauto.
      - (* extcall *)
        intros * Hes ?? Hwt Hs1 Hs2. inv Hwt.
        inversion_clear Hs1 as [| | | | | |????????? Hty1 Hse1 Hl1| | | | | | |].
        inversion_clear Hs2 as [| | | | | |????????? Hty2 Hse2 Hl2| | | | | | |].
        simpl.
        assert (tyins1 = tyins0); subst.
        { apply Forall2_eq. eapply Forall2_trans_ex in Hty1. 2:eapply Forall2_swap_args, Hty2.
          simpl_Forall. congruence. }
        eapply liftn_detn. 3,4:eauto.
        + eapply sem_exps_numstreams in Hse1; [|eauto with ltyping].
          rewrite typesof_annots in H4.
          destruct (annots es), (concat ss); simpl in *; try congruence.
        + eapply P_exps_det_exp_inv_all in Hes; eauto.
      - (* fby *)
        intros ???? Hk He0s ?? Hwt Hs1 Hs2. inv Hwt.
        inversion_clear Hs1 as [| | | | | | |???????? Hse11 Hse12 Hfby1| | | | | |].
        inversion_clear Hs2 as [| | | | | | |???????? Hse21 Hse22 Hfby2| | | | | |].
        eapply P_exps_det_exp_inv in He0s; eauto.
        eapply det_exps_n in Hse22; eauto using EqStN_weaken.
        assert (length (concat s0ss) = length ann0) as Hlen1.
        { eapply sem_exps_numstreams in Hse11; eauto with ltyping.
          rewrite <-length_typesof_annots, H5, map_length in Hse11.
          assumption. }
        assert (length (concat s0ss0) = length ann0) as Hlen2.
        { eapply sem_exps_numstreams in Hse21; eauto with ltyping.
          rewrite <-length_typesof_annots, H5, map_length in Hse21.
          assumption. }
        eapply fby_det_Sn; eauto.
        + eapply Forall2_forall2 in Hse22 as (_&Heq). eapply Heq; eauto.
          eapply Forall3_length in Hfby1 as (Hl1&Hl2).
          setoid_rewrite <-Hl1. setoid_rewrite Hlen1; eauto.
        + eapply Forall3_forall3 in Hfby1 as (_&_&Hfby1).
          eapply Hfby1 with (b:=def_stream); eauto. setoid_rewrite Hlen1. auto.
        + eapply Forall3_forall3 in Hfby2 as (_&_&Hfby2).
          eapply Hfby2 with (b:=def_stream); eauto. setoid_rewrite Hlen2. auto.
      - (* arrow *)
        intros ???? Hk He0s He1s ?? Hwt Hs1 Hs2. inv Hwt.
        inversion_clear Hs1 as [| | | | | | | |???????? Hse11 Hse12 Harrow1| | | | |].
        inversion_clear Hs2 as [| | | | | | | |???????? Hse21 Hse22 Harrow2| | | | |].
        eapply P_exps_det_exp_inv in He0s; eauto.
        eapply P_exps_det_exp_inv in He1s; eauto.
        assert (length (concat s0ss) = length ann0) as Hlen1.
        { eapply sem_exps_numstreams in Hse11; eauto with ltyping.
          rewrite <-length_typesof_annots, H5, map_length in Hse11.
          assumption. }
        assert (length (concat s0ss0) = length ann0) as Hlen2.
        { eapply sem_exps_numstreams in Hse21; eauto with ltyping.
          rewrite <-length_typesof_annots, H5, map_length in Hse21.
          assumption. }
        eapply arrow_detn. eapply He0s. eapply He1s.
        + eapply Forall3_forall3 in Harrow1 as (_&_&Harrow1). eapply Harrow1; eauto.
          congruence.
        + eapply Forall3_forall3 in Harrow2 as (_&_&Harrow2). eapply Harrow2; eauto.
          congruence.
      - (* when *)
        intros ??????? Hk Hes Hin Hvar ?? Hwt Hs1 Hs2. inv Hwt. simpl in *.
        inversion_clear Hs1 as [| | | | | | | | |?????????? Hse1 Hsv1 Hwhen1| | | |].
        inversion_clear Hs2 as [| | | | | | | | |?????????? Hse2 Hsv2 Hwhen2| | | |].
        eapply Hvar in Hsv2; eauto.
        eapply P_exps_det_exp_inv in Hes; eauto.
        assert (length (concat ss) = length (typesof es)) as Hlen1.
        { eapply sem_exps_numstreams in Hse1; eauto with ltyping.
          now rewrite <-length_typesof_annots in Hse1. }
        assert (length (concat ss0) = length (typesof es)) as Hlen2.
        { eapply sem_exps_numstreams in Hse2; eauto with ltyping.
          now rewrite <-length_typesof_annots in Hse2. }
        clear - Hk Hlen1 Hlen2 Hsv2 Hes Hwhen1 Hwhen2.
        rewrite_Forall_forall.
        eapply when_detn.
        + eapply Hes.
        + eapply Hsv2.
        + eapply H2; eauto. congruence.
        + eapply H0; eauto. congruence.
      - (* merge *)
        intros ?????? Hk Hin Hvar Hes ?? Hwt Hs1 Hs2. assert (Hwt':=Hwt). inv Hwt'. simpl in *.
        assert (length ss1 = length tys) as Hlen1.
        { eapply sem_exp_numstreams in Hs1; eauto with ltyping. }
        assert (length ss2 = length tys) as Hlen2.
        { eapply sem_exp_numstreams in Hs2; eauto with ltyping. }
        inversion_clear Hs1 as [| | | | | | | | | |????????? Hsv1 Hse1 Hmerge1| | |].
        inversion_clear Hs2 as [| | | | | | | | | |????????? Hsv2 Hse2 Hmerge2| | |].
        eapply Hvar in Hsv1; eauto using In_InMembers.
        assert (Forall2 (fun xs1 xs2 => EqStN (S n) (snd xs1) (snd xs2)) (nth k0 vs []) (nth k0 vs0 [])) as Heq.
        { eapply Forall2Brs_det_exp_inv; eauto. eapply Forall2_length in Hmerge1. congruence. }
        eapply Forall2Brs_fst in Hse1. eapply Forall2Brs_fst in Hse2.
        eapply Forall2_forall2 in Hmerge1 as (?&Hmerge1).
        eapply Forall2_forall2 in Hmerge2 as (?&Hmerge2).
        eapply merge_detn. 5:eapply Hmerge1; eauto. 6:eapply Hmerge2; eauto. 3,4:eauto.
        3,4:congruence.
        + eapply Forall_forall in Hse1; [|eapply nth_In]. eapply Forall_forall in Hse2; [|eapply nth_In].
          rewrite Hse1, Hse2; auto. 1,2:congruence.
        + eapply Forall_forall in Hse1; [|eapply nth_In].
          rewrite fst_NoDupMembers, Hse1, H5. apply seq_NoDup. congruence.
      - (* case *)
        intros ????? Hk Hse Hvar Hes ?? Hwt Hs1 Hs2. assert (Hwt':=Hwt). inv Hwt'; simpl in *.
        + (* total *)
          assert (length ss1 = length tys) as Hlen1.
          { eapply sem_exp_numstreams in Hs1; eauto with ltyping. }
          assert (length ss2 = length tys) as Hlen2.
          { eapply sem_exp_numstreams in Hs2; eauto with ltyping. }
          inversion_clear Hs1 as [| | | | | | | | | | |????????? Hsv1 Hse1 Hcase1| |].
          inversion_clear Hs2 as [| | | | | | | | | | |????????? Hsv2 Hse2 Hcase2| |].
          eapply Hse in Hsv1; eauto using In_InMembers. specialize (Hsv1 Hsv2). simpl in Hsv1.
          assert (Forall2 (fun xs1 xs2 => EqStN (S n) (snd xs1) (snd xs2)) (nth k0 vs []) (nth k0 vs0 [])) as Heq.
          { eapply Forall2Brs_det_exp_inv; eauto. eapply Forall2_length in Hcase1 as ?. congruence. }
          eapply Forall2Brs_fst in Hse1. eapply Forall2Brs_fst in Hse2.
          eapply Forall2_forall2 in Hcase1 as (?&Hcase1).
          eapply Forall2_forall2 in Hcase2 as (?&Hcase2).
          eapply case_detn. 6:eapply Hcase1; eauto. 7:eapply Hcase2; eauto. 1-5:eauto.
          4,5:congruence.
          * eapply Forall_forall in Hse1; [|eapply nth_In]. eapply Forall_forall in Hse2; [|eapply nth_In].
            rewrite Hse1, Hse2; auto. 1,2:congruence.
          * eapply Forall_forall in Hse1; [|eapply nth_In].
            rewrite fst_NoDupMembers, Hse1, H6. apply seq_NoDup. congruence.
          * intros. congruence.
        + (* default *)
          assert (length ss1 = length (typesof d0)) as Hlen1.
          { eapply sem_exp_numstreams in Hs1; eauto with ltyping. }
          assert (length ss2 = length (typesof d0)) as Hlen2.
          { eapply sem_exp_numstreams in Hs2; eauto with ltyping. }
          inversion_clear Hs1 as [| | | | | | | | | | | |?????????? Hsv1 _ Hse1 Hd1 Hcase1|].
          inversion_clear Hs2 as [| | | | | | | | | | | |?????????? Hsv2 _ Hse2 Hd2 Hcase2|].
          eapply Hse in Hsv1; eauto using In_InMembers. specialize (Hsv1 Hsv2). simpl in Hsv1.
          assert (Forall2 (fun xs1 xs2 => EqStN (S n) (snd xs1) (snd xs2)) (nth k0 vs []) (nth k0 vs0 [])) as Heq.
          { eapply Forall2Brs_det_exp_inv; eauto. eapply Forall3_length in Hcase1 as (?&?). congruence. }
          eapply P_exps_det_exp_inv in Hes; eauto.
          eapply Forall2Brs_fst in Hse1. eapply Forall2Brs_fst in Hse2.
          eapply Forall3_forall3 in Hcase1 as (?&?&Hcase1).
          eapply Forall3_forall3 in Hcase2 as (?&?&Hcase2).
          eapply case_detn. 6:eapply Hcase1; eauto. 7:eapply Hcase2; eauto. 1-5:eauto.
          4,5:congruence.
          * eapply Forall_forall in Hse1; [|eapply nth_In]. eapply Forall_forall in Hse2; [|eapply nth_In].
            rewrite Hse1, Hse2; auto. 1,2:congruence.
          * eapply Forall_forall in Hse1; [|eapply nth_In].
            rewrite fst_NoDupMembers, Hse1, <-fst_NoDupMembers; auto. congruence.
          * intros ??. instantiate (1:=None). instantiate (1:=None). intros Hnth1 Hnth2.
            erewrite map_nth' with (d':=def_stream) in Hnth1, Hnth2. inv Hnth1. inv Hnth2. auto.
            1,2:rewrite map_length in H, H1; try setoid_rewrite <-H; try setoid_rewrite <-H1; congruence.
      - (* app *)
        intros ????? Hlen Hes Her ?? Hwt Hsem1 Hsem2. inv Hwt.
        inversion_clear Hsem1 as [| | | | | | | | | | | | |?????????? Hes1 Her1 Hbools1 Hn1].
        inversion_clear Hsem2 as [| | | | | | | | | | | | |?????????? Hes2 Her2 Hbools2 Hn2].
        eapply P_exps_det_exp_inv_all in Hes; eauto.
        rewrite <-Forall2_map_2 in Her1, Her2. eapply P_exps_det_exp_inv_all in Her; eauto.
        do 2 rewrite concat_map_singl1 in Her.
        eapply bools_ofs_detn in Hbools2; eauto.
        assert (Forall2 (EqStN (S n)) ss1 ss2) as Heq.
        2:{ eapply Forall2_forall2 in Heq as (_&Heq).
            eapply Heq; eauto.
            specialize (Hn1 0). inv Hn1. rewrite H5 in H0. inv H0.
            unfold idents in H2. rewrite Forall2_map_1, Forall2_map_2 in H2. eapply Forall2_length in H2.
            eapply Forall2_length in H7.
            rewrite <-H2, <-H7; auto.
        }
        eapply EqStNs_unmask; eauto. intros.
        eapply HdetG. 2,3:eauto.
        eapply EqStNs_mask; eauto.
    Qed.

    Hypothesis Hnd : NoDup (map snd (idcaus_of_senv Γ)).

    Lemma det_equation_S : forall n Hi1 Hi2 bs1 bs2 xs es k cx,
        wt_equation G Γ (xs, es) ->
        Sem.sem_equation G Hi1 bs1 (xs, es) ->
        Sem.sem_equation G Hi2 bs2 (xs, es) ->
        k < length xs ->
        P_exps (det_exp_inv (S n) Hi1 Hi2 bs1 bs2) es k ->
        HasCaus Γ (nth k xs xH) cx ->
        det_var_inv (S n) Hi1 Hi2 cx.
    Proof.
      intros * (* Hn  *)(Hwt1&Hwt2) Hsem1 Hsem2 Hnum HSn Hin.
      inv Hsem1. inv Hsem2.
      eapply P_exps_det_exp_inv in HSn; eauto.
      split; intros ??? Hin' Hv1 Hv2.
      - eapply Forall2_forall2 in H5 as (Hl1&Heq1).
        eapply Forall2_forall2 in H7 as (Hl2&Heq2).
        eapply HasCaus_snd_det in Hin; eauto; subst.
        eapply EqStN_morph. 3:eauto.
        1,2:eapply sem_var_det; eauto.
      - exfalso. eapply NoDup_HasCaus_HasLastCaus; eauto.
    Qed.

  End sem_equation_det.

  Lemma sem_clock_detN n Γ : forall ck bs1 bs2 Hi1 Hi2 bs1' bs2',
      EqStN n bs1 bs2 ->
      wx_clock Γ ck ->
      (forall x cx, Is_free_in_clock x ck -> HasCaus Γ x cx -> det_var_inv Γ n Hi1 Hi2 cx) ->
      sem_clock (var_history Hi1) bs1 ck bs1' ->
      sem_clock (var_history Hi2) bs2 ck bs2' ->
      EqStN n bs1' bs2'.
  Proof.
    induction ck; intros * Hbs Hwx Hck Hsem1 Hsem2; inv Hwx; inv Hsem1; inv Hsem2.
    - now rewrite <-H0, <-H1.
    - inv H3. apply fst_InMembers in H; simpl_In.
      repeat (take (sem_var (var_history _) _ _) and apply sem_var_history in it).
      eapply Hck in it; eauto using Is_free_in_clock with senv.
      eapply enums_of_detn; eauto.
  Qed.

  Lemma det_var_inv_mask : forall Γ n rs1 rs2 Hi1 Hi2 x,
      EqStN n rs1 rs2 ->
      det_var_inv Γ n Hi1 Hi2 x ->
      forall k, det_var_inv Γ n (mask_hist k rs1 Hi1) (mask_hist k rs2 Hi2) x.
  Proof.
    intros * Heq Hdet ?.
    split; intros ??? Hin Hv1 Hv2.
    1,2:(eapply sem_var_mask_inv in Hv1 as (?&Hv1&Heq1);
         eapply sem_var_mask_inv in Hv2 as (?&Hv2&Heq2);
         rewrite Heq1, Heq2;
         eapply EqStN_mask; eauto;
         eapply Hdet in Hv2; eauto).
  Qed.

  Lemma det_var_unmask : forall n rs1 rs2 Hi1 Hi2 x,
      EqStN n rs1 rs2 ->
      (forall k, det_var n (mask_hist k rs1 Hi1) (mask_hist k rs2 Hi2) x) ->
      det_var n Hi1 Hi2 x.
  Proof.
    intros * Heq Hdet ?? V1 V2.
    eapply EqStN_unmask; eauto.
    intros k. eapply Hdet; unfold mask_hist; eauto using sem_var_mask.
  Qed.

  Corollary det_var_inv_unmask : forall Γ n rs1 rs2 Hi1 Hi2 x,
      EqStN n rs1 rs2 ->
      (forall k, det_var_inv Γ n (mask_hist k rs1 Hi1) (mask_hist k rs2 Hi2) x) ->
      det_var_inv Γ n Hi1 Hi2 x.
  Proof.
    intros * Heq Hdet.
    split; intros; eapply det_var_unmask; eauto.
    1,2:intros ?; eapply Hdet; eauto.
  Qed.

  Lemma EqStN_fwhen {A} (absent : A) : forall n sc1 sc2 xs1 xs2,
      EqStN n sc1 sc2 ->
      EqStN n xs1 xs2 ->
      forall c, EqStN n (fwhen absent c xs1 sc1) (fwhen absent c xs2 sc2).
  Proof.
    induction n; intros * Heq1 Heq2 k; auto with coindstreams.
    inv Heq1; inv Heq2; repeat rewrite fwhen_Cons.
    destruct k as [|[|]], x2; try (solve [constructor; auto]).
  Qed.

  Lemma EqStN_unwhen : forall n tx tn sc1 sc2 xs1 xs2,
      0 < length tn ->
      wt_stream sc1 (Tenum tx tn) ->
      wt_stream sc2 (Tenum tx tn) ->
      EqStN n sc1 sc2 ->
      (forall sel, In sel (seq 0 (length tn)) ->
              exists xs1' xs2',
                when sel xs1 sc1 xs1'
                /\ when sel xs2 sc2 xs2'
                /\ EqStN n xs1' xs2') ->
      EqStN n xs1 xs2.
  Proof.
    intros * Htn Hwt1 Hwt2 Heq1 Heq2.
    eapply EqStN_spec. intros ? Hlt.
    eapply EqStN_spec in Heq1; [|eauto].
    eapply SForall_forall in Hwt1; instantiate (1:=k) in Hwt1.
    eapply SForall_forall in Hwt2; instantiate (1:=k) in Hwt2.
    destruct (sc2 # k) eqn:Heq3; simpl in *.
    1,2:rewrite Heq1 in *; inv Hwt1; inv Hwt2.
    - edestruct Heq2 as (?&?&Hf1&Hf2&Heq). apply in_seq. auto.
      eapply when_spec with (n:=k) in Hf1 as [|[|]]; destruct_conjs; try congruence.
      eapply when_spec with (n:=k) in Hf2 as [|[|]]; destruct_conjs; try congruence.
    - assert (In v0 (seq 0 (length tn))) as Hin by (apply in_seq; lia).
      specialize (Heq2 _ Hin) as (?&?&Hf1&Hf2&Heq).
      eapply when_spec with (n:=k) in Hf1 as [|[|]]; destruct_conjs; try congruence.
      eapply when_spec with (n:=k) in Hf2 as [|[|]]; destruct_conjs; try congruence.
      rewrite EqStN_spec in Heq.
      rewrite H, H4, <-H3, Heq; auto.
  Qed.

  Lemma det_var_inv_when : forall Γ n sc1 sc2 Hi1 Hi2 Hi1' Hi2' x,
      EqStN n sc1 sc2 ->
      det_var_inv Γ n Hi1 Hi2 x ->
      forall c, when_hist c Hi1 sc1 Hi1' ->
           when_hist c Hi2 sc2 Hi2' ->
           det_var_inv Γ n Hi1' Hi2' x.
  Proof.
    intros * Heq Hdet * Hf1 Hf2.
    split; intros ??? Hin Hv1 Hv2.
    - eapply sem_var_when_inv in Hv1 as (?&Hv1&Heq1); eauto.
      eapply sem_var_when_inv in Hv2 as (?&Hv2&Heq2); eauto.
      apply when_fwhen in Heq1. apply when_fwhen in Heq2. rewrite Heq1, Heq2.
      eapply EqStN_fwhen; eauto.
      eapply Hdet in Hv2; eauto.
    - eapply sem_var_when_inv in Hv1 as (?&Hv1&Heq1); eauto.
      eapply sem_var_when_inv in Hv2 as (?&Hv2&Heq2); eauto.
      apply when_fwhen in Heq1. apply when_fwhen in Heq2. rewrite Heq1, Heq2.
      eapply EqStN_fwhen; eauto.
      eapply Hdet in Hv2; eauto.
  Qed.

  Lemma det_var_unwhen : forall tx tn n sc1 sc2 Hi1 Hi2 x,
      0 < length tn ->
      wt_stream sc1 (Tenum tx tn) ->
      wt_stream sc2 (Tenum tx tn) ->
      EqStN n sc1 sc2 ->
      (forall c, In c (seq 0 (length tn)) ->
            exists Hi1' Hi2',
              (FEnv.In (Var x) Hi1' /\ FEnv.In (Var x) Hi2')
              /\ when_hist c Hi1 sc1 Hi1'
              /\ when_hist c Hi2 sc2 Hi2'
              /\ det_var n Hi1' Hi2' (Var x)) ->
      det_var n Hi1 Hi2 (Var x).
  Proof.
    intros * Hn Hwt1 Hwt2 Heq Hdet.
    intros ?? Hv1 Hv2.
    eapply EqStN_unwhen. 4:eauto. 1-3:eauto.
    intros k Hin'. edestruct Hdet as (Hi1'&Hi2'&(Hin1&Hin2)&Hf1&Hf2&Hdet'); eauto.
    assert (exists vs1', sem_var Hi1' (Var x) vs1') as (?&Hvar1) by (inv Hin1; do 2 econstructor; try reflexivity; eauto).
    assert (exists vs1', sem_var Hi2' (Var x) vs1') as (?&Hvar2) by (inv Hin2; do 2 econstructor; try reflexivity; eauto).
    assert (Hvar1':=Hvar1). eapply sem_var_when_inv in Hvar1' as (?&?&Hv1'); eauto.
    assert (Hvar2':=Hvar2). eapply sem_var_when_inv in Hvar2' as (?&?&Hv2'); eauto.
    eapply sem_var_det in Hv1; eauto. eapply sem_var_det in Hv2; eauto.
    do 2 esplit; eauto. rewrite Hv1, Hv2 in *. repeat split; eauto.
  Qed.

  Fact det_var_inv_weaken Γ n : forall Hi1 Hi2 x,
      det_var_inv Γ (S n) Hi1 Hi2 x ->
      det_var_inv Γ n Hi1 Hi2 x.
  Proof.
    intros * Hdet.
    split; intros ??????; [edestruct Hdet as (Hdet1&_)|edestruct Hdet as (_&Hdet1)].
    1,2:eapply EqStN_weaken; [|eapply Hdet1; eauto]; auto.
  Qed.

  Lemma EqStN_fselect {A} (absent : A) : forall n sc1 sc2 xs1 xs2,
      EqStN n sc1 sc2 ->
      EqStN n xs1 xs2 ->
      forall c k, EqStN n (fselect absent c k sc1 xs1) (fselect absent c k sc2 xs2).
  Proof.
    intros.
    apply EqStN_mask. 1,2:apply EqStN_fwhen; auto.
    1-3:apply map_EqStN; auto.
  Qed.

  Lemma EqStN_unselect : forall n tn sc1 sc2 xs1 xs2,
      0 < tn ->
      EqStN n sc1 sc2 ->
      SForall (fun v => match v with present (e, _) => e < tn | _ => True end) sc1 ->
      SForall (fun v => match v with present (e, _) => e < tn | _ => True end) sc2 ->
      (forall sel k, In sel (seq 0 tn) ->
                exists xs1' xs2',
                  select sel k sc1 xs1 xs1'
                  /\ select sel k sc2 xs2 xs2'
                  /\ EqStN n xs1' xs2') ->
      EqStN n xs1 xs2.
  Proof.
    intros * Htn Heq1 Hwt1 Hwt2 Heq2.
    eapply EqStN_spec. intros ? Hlt.
    eapply EqStN_spec in Heq1 as Heq1'; [|eauto].
    eapply SForall_forall in Hwt1; instantiate (1:=k) in Hwt1.
    eapply SForall_forall in Hwt2; instantiate (1:=k) in Hwt2.
    destruct (sc2 # k) as [|(?&?)] eqn:Heq3; simpl in *.
    1,2:rewrite Heq1' in *.
    - edestruct Heq2 with (k:=0) as (?&?&Hf1&Hf2&Heq). apply in_seq. auto.
      apply select_mask_when in Hf1 as (?&Hfil1&Hmask1).
      apply select_mask_when in Hf2 as (?&Hfil2&Hmask2).
      eapply when_spec with (n:=k) in Hfil1 as [|[|]]; destruct_conjs.
      all:take ((stres_st _) # _ = _) and setoid_rewrite Str_nth_map in it; setoid_rewrite Heq1' in it; try congruence.
      eapply when_spec with (n:=k) in Hfil2 as [|[|]]; destruct_conjs; try congruence.
      all:take ((stres_st _) # _ = _) and setoid_rewrite Str_nth_map in it; setoid_rewrite Heq3 in it; try congruence.
    - assert (In n0 (seq 0 tn)) as Hin by (apply in_seq; lia).
      specialize (Heq2 _ ((count (fwhenb n0 (stres_res sc1) (stres_st sc1))) # k) Hin) as (?&?&Hf1&Hf2&Heq).
      apply select_mask_when in Hf1 as (?&Hfil1&Hmask1).
      apply select_mask_when in Hf2 as (?&Hfil2&Hmask2).
      eapply when_spec with (n:=k) in Hfil1 as [|[|]]; destruct_conjs.
      all:take ((stres_st _) # _ = _) and setoid_rewrite Str_nth_map in it; setoid_rewrite Heq1' in it; try congruence.
      eapply when_spec with (n:=k) in Hfil2 as [|[|]]; destruct_conjs.
      all:take ((stres_st _) # _ = _) and setoid_rewrite Str_nth_map in it; setoid_rewrite Heq3 in it; try congruence.
      rewrite H, H0, <-H1, <-H3.
      rewrite EqStN_spec in Heq. specialize (Heq _ Hlt).
      apply eqst_ntheq with (n:=k) in Hmask1. rewrite maskv_nth, Nat.eqb_refl in Hmask1.
      apply eqst_ntheq with (n:=k) in Hmask2. erewrite maskv_nth in Hmask2.
      replace ((count (fwhenb n0 (stres_res sc2) (stres_st sc2))) # k)
        with ((count (fwhenb n0 (stres_res sc1) (stres_st sc1))) # k) in Hmask2.
      2:{ eapply EqStN_spec; eauto.
          apply count_EqStN, EqStN_fwhen; eauto using map_EqStN. }
      rewrite Nat.eqb_refl in Hmask2.
      congruence.
  Qed.

  Lemma EqStN_unfselect {A} : forall n tn sc1 sc2 xs1 xs2,
      0 < tn ->
      EqStN n sc1 sc2 ->
      SForall (fun v => match v with present (e, _) => e < tn | _ => True end) sc1 ->
      SForall (fun v => match v with present (e, _) => e < tn | _ => True end) sc2 ->
      slower xs1 (abstract_clock sc1) ->
      slower xs2 (abstract_clock sc2) ->
      (forall sel k, In sel (seq 0 tn) ->
                EqStN n (fselect (@absent A) sel k sc1 xs1) (fselect (@absent A) sel k sc2 xs2)) ->
      EqStN n xs1 xs2.
  Proof.
    intros * Htn Heq1 Hwt1 Hwt2 Hslow1 Hslow2 Heq2.
    eapply EqStN_spec. intros ? Hlt.
    eapply EqStN_spec in Heq1 as Heq1'; [|eauto].
    eapply SForall_forall in Hwt1; instantiate (1:=k) in Hwt1.
    eapply SForall_forall in Hwt2; instantiate (1:=k) in Hwt2.
    destruct (sc2 # k) as [|(?&?)] eqn:Heq3; simpl in *.
    1,2:rewrite Heq1' in *.
    - apply slower_nth with (n:=k) in Hslow1. 2:rewrite ac_nth, Heq1'; auto.
      apply slower_nth with (n:=k) in Hslow2. 2:rewrite ac_nth, Heq3; auto.
      congruence.
    - assert (In n0 (seq 0 tn)) as Hin by (apply in_seq; lia).
      specialize (Heq2 _ ((count (fwhenb n0 (stres_res sc1) (stres_st sc1))) # k) Hin) as Heq.
      rewrite EqStN_spec in Heq. specialize (Heq _ Hlt).
      unfold fselect in Heq. rewrite 2 mask_nth, Nat.eqb_refl in Heq.
      replace ((count (fwhenb n0 (stres_res sc2) (stres_st sc2))) # k)
        with ((count (fwhenb n0 (stres_res sc1) (stres_st sc1))) # k) in Heq.
      2:{ eapply EqStN_spec; eauto.
          apply count_EqStN, EqStN_fwhen; eauto using map_EqStN. }
      rewrite Nat.eqb_refl, 2 fwhen_nth in Heq. repeat setoid_rewrite Str_nth_map in Heq.
      setoid_rewrite Heq1' in Heq. setoid_rewrite Heq3 in Heq.
      rewrite equiv_decb_refl in Heq. auto.
  Qed.

  Lemma det_var_inv_select : forall Γ n sc1 sc2 Hi1 Hi2 Hi1' Hi2' x,
      EqStN n sc1 sc2 ->
      det_var_inv Γ n Hi1 Hi2 x ->
      forall c k, select_hist c k sc1 Hi1 Hi1' ->
             select_hist c k sc2 Hi2 Hi2' ->
             det_var_inv Γ n Hi1' Hi2' x.
  Proof.
    intros * Heq Hdet * Hf1 Hf2.
    split; intros ??? Hin Hv1 Hv2.
    - eapply sem_var_select_inv in Hv1 as (?&Hv1&Heq1); eauto.
      eapply sem_var_select_inv in Hv2 as (?&Hv2&Heq2); eauto.
      apply select_fselect in Heq1. apply select_fselect in Heq2. rewrite Heq1, Heq2.
      eapply EqStN_mask. 1,2:eapply EqStN_fwhen; eauto.
      4:eapply Hdet in Hv2; eauto.
      1-3:apply map_EqStN; auto.
    - eapply sem_var_select_inv in Hv1 as (?&Hv1&Heq1); eauto.
      eapply sem_var_select_inv in Hv2 as (?&Hv2&Heq2); eauto.
      apply select_fselect in Heq1. apply select_fselect in Heq2. rewrite Heq1, Heq2.
      eapply EqStN_mask. 1,2:eapply EqStN_fwhen; eauto.
      4:eapply Hdet in Hv2; eauto.
      1-3:apply map_EqStN; auto.
  Qed.

  Lemma det_var_unselect : forall tn n sc1 sc2 Hi1 Hi2 x,
      0 < tn ->
      EqStN n sc1 sc2 ->
      SForall (fun v => match v with present (e, _) => e < tn | _ => True end) sc1 ->
      SForall (fun v => match v with present (e, _) => e < tn | _ => True end) sc2 ->
      (forall c k, In c (seq 0 tn) ->
              exists Hi1' Hi2',
                (FEnv.In (Var x) Hi1' /\ FEnv.In (Var x) Hi2')
                /\ select_hist c k sc1 Hi1 Hi1'
                /\ select_hist c k sc2 Hi2 Hi2'
                /\ det_var n Hi1' Hi2' (Var x)) ->
      det_var n Hi1 Hi2 (Var x).
  Proof.
    intros * Hn Heq Hwt1 Hwt2 Hdet ?? Hv1 Hv2.
    eapply EqStN_unselect; eauto.
    intros * Hin'. edestruct Hdet as (Hi1'&Hi2'&(Hin1&Hin2)&Hf1&Hf2&Hdet'); eauto.
    assert (exists vs1', sem_var Hi1' (Var x) vs1') as (?&Hvar1) by (inv Hin1; do 2 econstructor; try reflexivity; eauto).
    assert (exists vs1', sem_var Hi2' (Var x) vs1') as (?&Hvar2) by (inv Hin2; do 2 econstructor; try reflexivity; eauto).
    assert (Hvar1':=Hvar1). eapply sem_var_select_inv in Hvar1' as (?&?&Hv1'); eauto.
    assert (Hvar2':=Hvar2). eapply sem_var_select_inv in Hvar2' as (?&?&Hv2'); eauto.
    eapply sem_var_det in Hv1; eauto. eapply sem_var_det in Hv2; eauto.
    do 2 esplit; eauto. rewrite Hv1, Hv2 in *. repeat split; eauto.
  Qed.

  Lemma const_stres_detn {A} n : forall (x : A) bs1 bs2,
      EqStN n bs1 bs2 ->
      EqStN n (const_stres bs1 x) (const_stres bs2 x).
  Proof.
    intros * Heq.
    apply EqStN_spec; intros * Hlt.
    eapply EqStN_spec in Heq; eauto.
    setoid_rewrite Str_nth_map. now rewrite Heq.
  Qed.

  Lemma choose_first_detn {A} n : forall xs1 xs2 ys1 ys2,
      EqStN n xs1 xs2 ->
      EqStN n ys1 ys2 ->
      EqStN n (@choose_first A xs1 ys1) (choose_first xs2 ys2).
  Proof.
    intros * Heq1 Heq2.
    apply EqStN_spec; intros * Hlt.
    eapply EqStN_spec in Heq1; eauto. eapply EqStN_spec in Heq2; eauto.
    rewrite 2 choose_first_nth, Heq1, Heq2; auto.
  Qed.

  Lemma sem_transitions_detn {PSyn prefs} (G: @global PSyn prefs) Γ n :
    forall Hi1 Hi2 bs1 bs2 trans def stres1 stres2,
      det_nodes G ->
      Forall (fun '(e, (t, _)) => wt_exp G Γ e) trans ->
      (forall x cx, HasCaus Γ x cx \/ HasLastCaus Γ x cx -> det_var_inv Γ n Hi1 Hi2 cx) ->
      EqStN n bs1 bs2 ->
      sem_transitions G Hi1 bs1 trans def stres1 ->
      sem_transitions G Hi2 bs2 trans def stres2 ->
      EqStN n stres1 stres2.
  Proof.
    induction trans; intros * HdetG Hwt Hsc Hbs Htr1 Htr2; inv Hwt; inv Htr1; inv Htr2.
    - rewrite H0, H1. apply const_stres_detn; auto.
    - rewrite H11, H17.
      apply choose_first_detn; eauto. apply const_stres_detn.
      eapply bools_of_detn; eauto. eapply det_exp_n in H12; eauto.
      simpl_Forall; auto.
  Qed.

  Lemma sem_transitions_detS {PSyn prefs} (G: @global PSyn prefs) Γ n :
    forall Hi1 Hi2 bs1 bs2 trans def stres1 stres2,
      det_nodes G ->
      Forall (fun '(e, (t, _)) => wt_exp G Γ e /\ typeof e = [bool_velus_type]) trans ->
      (forall x cx, HasCaus Γ x cx \/ HasLastCaus Γ x cx -> det_var_inv Γ n Hi1 Hi2 cx) ->
      (forall x cx, HasCaus Γ x cx \/ HasLastCaus Γ x cx -> Exists (fun '(e, _) => Is_used_inst Γ cx 0 e) trans -> det_var_inv Γ (S n) Hi1 Hi2 cx) ->
      EqStN (S n) bs1 bs2 ->
      sem_transitions G Hi1 bs1 trans def stres1 ->
      sem_transitions G Hi2 bs2 trans def stres2 ->
      EqStN (S n) stres1 stres2.
  Proof.
    induction trans; intros * HdetG Hwt Hsc1 Hsc2 Hbs Htr1 Htr2; inv Hwt; inv Htr1; inv Htr2.
    - rewrite H0, H1. apply const_stres_detn; auto.
    - destruct_conjs. rewrite H11, H17.
      apply choose_first_detn; eauto. apply const_stres_detn.
      eapply bools_of_detn; eauto.
      eapply det_exp_S with (k:=0) in H4; eauto. specialize (H4 H12); eauto.
      + rewrite <-length_typeof_numstreams, H0; auto.
      + intros * Hfree. split; intros ??; [edestruct Hsc2 as (Hsc&_)|edestruct Hsc2 as (_&Hsc)]; eauto.
  Qed.

  Fact det_var_inv_local :
    forall Γ (locs : list decl) Hi1 Hi2 Hi1' Hi2' n cx,
      (forall x : ident, InMembers x locs -> ~ In x (map fst Γ)) ->
      dom Hi1' (senv_of_decls locs) ->
      dom Hi2' (senv_of_decls locs) ->
      det_var_inv Γ n Hi1 Hi2 cx ->
      det_var_inv (senv_of_decls locs) n Hi1' Hi2' cx ->
      det_var_inv (Γ ++ senv_of_decls locs) n (Hi1 + Hi1') (Hi2 + Hi2') cx.
  Proof.
    intros * Hnd (* Hdoml1 Hdoml2  *)Hdom1 Hdom2 (* Hrefl1 Hrefl2  *)Hsc1 Hsc2.
    split; intros ? Hin ?? Hv1 Hv2; inv Hin; rewrite in_app_iff in H; destruct H as [Hin|Hin]; simpl_In.
    - edestruct Hsc1 as (Hinv&_). eapply Hinv; eauto using sem_var_local_inv1 with senv.
    - edestruct Hsc2 as (Hinv&_). eapply Hinv; eauto.
      econstructor; solve_In; auto.
      1,2:eapply sem_var_local_inv2; eauto; solve_In.

    - assert (IsLast Γ x) as L by (econstructor; eauto; congruence).
      edestruct Hsc1 as (_&Hinv). eapply Hinv; eauto using sem_last_local_inv1 with senv.
    - edestruct Hsc2 as (_&Hinv). eapply Hinv; eauto using sem_last_local_inv2.
      econstructor; solve_In; auto.
  Qed.

  Fact det_var_inv_branch :
    forall Γ caus Hi1 Hi2 n cx,
      (forall x, HasCaus Γ x cx \/ HasLastCaus Γ x cx -> det_var_inv Γ n Hi1 Hi2 cx) ->
      (forall x vs1 vs2, In (x, cx) caus -> sem_var Hi1 (Var x) vs1 -> sem_var Hi2 (Var x) vs2 -> EqStN n vs1 vs2) ->
      det_var_inv (replace_idcaus caus Γ) n Hi1 Hi2 cx.
  Proof.
    intros * Hsc1 Hsc2.
    split; intros ? Hin ?? Hv1 Hv2; inv Hin; simpl_In.
    - destruct (assoc_ident x caus) eqn:Hassoc; simpl in *.
      + apply assoc_ident_In in Hassoc.
        eapply Hsc2; eauto.
      + edestruct Hsc1 as (Hinv&_); [|eapply Hinv]; eauto with senv.
    - rewrite ann_with_caus_causl_last in H0.
      edestruct Hsc1 as (_&Hinv); [|eapply Hinv]; eauto with senv.
  Qed.

  Section sem_block_det.
    Context {prefs : PS.t}.
    Variable (G: @global complete prefs).

    Section sem_scope.

      Context {A : Type}.

      Variable sem_block : history -> history -> A -> Prop.

      Inductive sem_scope_det (n : nat) (envS : list ident) : history -> history -> Stream bool -> Stream bool -> scope A -> Prop :=
      | Sscope : forall Hi1 Hi2 Hi1' Hi2' bs1 bs2 locs blks,
          dom Hi1' (senv_of_decls locs) ->
          dom Hi2' (senv_of_decls locs) ->

          sem_block (Hi1 + Hi1') (Hi2 + Hi2') blks ->

          (forall cx, det_var_inv (senv_of_decls locs) n Hi1' Hi2' cx) ->
          (forall cx, In cx envS -> det_var_inv (senv_of_decls locs) (S n) Hi1' Hi2' cx) ->
          sem_scope_det n envS Hi1 Hi2 bs1 bs2 (Scope locs blks).
    End sem_scope.

    Section sem_branch.

      Context {A : Type}.

      Variable sem_block : A -> Prop.

      Variable must_def : ident -> Prop.
      Variable is_def : ident -> A -> Prop.

      Inductive sem_branch_det (n : nat) (envS : list ident) : history -> history -> branch A -> Prop :=
      | Sbranch : forall Hi1 Hi2 caus blks,
          sem_block blks ->
          (forall x, must_def x -> ~is_def x blks -> exists vs, sem_var Hi1 (Last x) vs /\ sem_var Hi1 (Var x) vs) ->
          (forall x, must_def x -> ~is_def x blks -> exists vs, sem_var Hi2 (Last x) vs /\ sem_var Hi2 (Var x) vs) ->

          Forall (fun '(x, _) => det_var n Hi1 Hi2 (Var x)) caus ->
          Forall (fun '(x, cx) => In cx envS -> det_var (S n) Hi1 Hi2 (Var x)) caus ->
          sem_branch_det n envS Hi1 Hi2 (Branch caus blks).

      (* Use for strong transitions *)
      Inductive sem_branch_det' : history -> history -> branch A -> Prop :=
      | Sbranch' : forall Hi1 Hi2 caus blks,
          sem_block blks ->
          (forall x, must_def x -> ~is_def x blks -> exists vs, sem_var Hi1 (Last x) vs /\ sem_var Hi1 (Var x) vs) ->
          (forall x, must_def x -> ~is_def x blks -> exists vs, sem_var Hi2 (Last x) vs /\ sem_var Hi2 (Var x) vs) ->
          sem_branch_det' Hi1 Hi2 (Branch caus blks).
    End sem_branch.

    Inductive sem_block_det (n : nat) (envS : list ident) : history -> history -> Stream bool -> Stream bool -> block -> Prop :=
    | Sdetbeq : forall Hi1 Hi2 bs1 bs2 eq,
        sem_equation G Hi1 bs1 eq ->
        sem_equation G Hi2 bs2 eq ->
        sem_block_det n envS Hi1 Hi2 bs1 bs2 (Beq eq)

    | Sdetlast : forall Hi1 Hi2 bs1 bs2 x e vs01 vs02 vs11 vs12 vs1 vs2,
        sem_exp G Hi1 bs1 e [vs01] -> sem_var Hi1 (Var x) vs11 -> fby vs01 vs11 vs1 -> sem_var Hi1 (Last x) vs1 ->
        sem_exp G Hi2 bs2 e [vs02] -> sem_var Hi2 (Var x) vs12 -> fby vs02 vs12 vs2 -> sem_var Hi2 (Last x) vs2 ->
        sem_block_det n envS Hi1 Hi2 bs1 bs2 (Blast x e)

    | Sdetreset : forall Hi1 Hi2 bs1 bs2 blocks er sr1 sr2 r1 r2,
        sem_exp G Hi1 bs1 er [sr1] ->
        sem_exp G Hi2 bs2 er [sr2] ->
        bools_of sr1 r1 ->
        bools_of sr2 r2 ->
        (forall k, Forall (sem_block_det n envS (mask_hist k r1 Hi1) (mask_hist k r2 Hi2) (maskb k r1 bs1) (maskb k r2 bs2)) blocks) ->
        sem_block_det n envS Hi1 Hi2 bs1 bs2 (Breset blocks er)

    | Sdetswitch : forall Hi1 Hi2 bs1 bs2 branches ec sc1 sc2,
        sem_exp G Hi1 bs1 ec [sc1] ->
        sem_exp G Hi2 bs2 ec [sc2] ->
        wt_streams [sc1] (typeof ec) ->
        wt_streams [sc2] (typeof ec) ->
        Forall (fun blks => exists Hi1' Hi2',
                    when_hist (fst blks) Hi1 sc1 Hi1'
                    /\ when_hist (fst blks) Hi2 sc2 Hi2'
                    /\ let bi1 := fwhenb (fst blks) bs1 sc1 in
                      let bi2 := fwhenb (fst blks) bs2 sc2 in
                      sem_branch_det (Forall (sem_block_det n envS Hi1' Hi2' bi1 bi2))
                        (fun x => Syn.Is_defined_in (Var x) (Bswitch ec branches))
                        (fun x => List.Exists (Syn.Is_defined_in (Var x)))
                        n envS Hi1' Hi2' (snd blks)) branches ->
        sem_block_det n envS Hi1 Hi2 bs1 bs2 (Bswitch ec branches)

    | SdetautoWeak:
      forall Hi1 Hi2 bs1 bs2 ini oth states ck bs'1 bs'2 stres01 stres11 stres1 stres02 stres12 stres2,
        sem_clock (var_history Hi1) bs1 ck bs'1 ->
        sem_clock (var_history Hi2) bs2 ck bs'2 ->
        sem_transitions G Hi1 bs'1 (List.map (fun '(e, t) => (e, (t, false))) ini) (oth, false) stres01 ->
        sem_transitions G Hi2 bs'2 (List.map (fun '(e, t) => (e, (t, false))) ini) (oth, false) stres02 ->
        fby stres01 stres11 stres1 ->
        fby stres02 stres12 stres2 ->
        EqStN n stres11 stres12 ->
        Forall (fun state =>
                  let tag := fst (fst state) in
                  forall k, exists Hik1 Hik2,
                    select_hist tag k stres1 Hi1 Hik1
                    /\ select_hist tag k stres2 Hi2 Hik2
                    /\ let bik1 := fselectb tag k stres1 bs1 in
                      let bik2 := fselectb tag k stres2 bs2 in
                      sem_branch_det
                        (fun blks =>
                           sem_scope_det (fun Hi1 Hi2 blks =>
                                            Forall (sem_block_det n envS Hi1 Hi2 bik1 bik2) (fst blks)
                                            /\ sem_transitions G Hi1 bik1 (snd blks) (tag, false) (fselect absent tag k stres1 stres11)
                                            /\ sem_transitions G Hi2 bik2 (snd blks) (tag, false) (fselect absent tag k stres2 stres12))
                             n envS Hik1 Hik2 bik1 bik2 (snd blks))
                        (fun x => Syn.Is_defined_in (Var x) (Bauto Weak ck (ini, oth) states))
                        (fun x '(_, s) => Syn.Is_defined_in_scope (fun '(blks, _) => List.Exists (Syn.Is_defined_in (Var x)) blks) (Var x) s)
                        n envS Hik1 Hik2 (snd state)) states ->
        sem_block_det n envS Hi1 Hi2 bs1 bs2 (Bauto Weak ck (ini, oth) states)

    | SdetautoStrong:
      forall Hi1 Hi2 bs1 bs2 ini states ck bs'1 bs'2 stres11 stres1 stres12 stres2,
        sem_clock (var_history Hi1) bs1 ck bs'1 ->
        sem_clock (var_history Hi2) bs2 ck bs'2 ->
        fby (const_stres bs'1 (ini, false)) stres11 stres1 ->
        fby (const_stres bs'2 (ini, false)) stres12 stres2 ->
        Forall (fun state =>
                  let tag := fst (fst state) in
                  forall k, exists Hik1 Hik2,
                    select_hist tag k stres1 Hi1 Hik1
                    /\ select_hist tag k stres2 Hi2 Hik2
                    /\ let bik1 := fselectb tag k stres1 bs1 in
                      let bik2 := fselectb tag k stres2 bs2 in
                      sem_branch_det'
                        (fun blks =>
                           sem_transitions G Hik1 bik1 (fst blks) (tag, false) (fselect absent (tag) k stres1 stres11)
                           /\ sem_transitions G Hik2 bik2 (fst blks) (tag, false) (fselect absent (tag) k stres2 stres12))
                        (fun x => Syn.Is_defined_in (Var x) (Bauto Strong ck ([], ini) states))
                        (fun x '(_, s) => Syn.Is_defined_in_scope (fun '(blks, _) => List.Exists (Syn.Is_defined_in (Var x)) blks) (Var x) s)
                        Hik1 Hik2 (snd state)) states ->
        EqStN n stres11 stres12 ->
        Forall (fun state =>
                  let tag := fst (fst state) in
                  forall k, exists Hik1 Hik2,
                    select_hist tag k stres11 Hi1 Hik1
                    /\ select_hist tag k stres12 Hi2 Hik2
                    /\ let bik1 := fselectb tag k stres11 bs1 in
                      let bik2 := fselectb tag k stres12 bs2 in
                      sem_branch_det
                        (fun blks =>
                           sem_scope_det (fun Hi1 Hi2 blks => Forall (sem_block_det n envS Hi1 Hi2 bik1 bik2) (fst blks))
                             n envS Hik1 Hik2 bik1 bik2 (snd blks))
                        (fun x => Syn.Is_defined_in (Var x) (Bauto Strong ck ([], ini) states))
                        (fun x '(_, s) => Syn.Is_defined_in_scope (fun '(blks, _) => List.Exists (Syn.Is_defined_in (Var x)) blks) (Var x) s)
                        n envS Hik1 Hik2 (snd state)) states ->
        sem_block_det n envS Hi1 Hi2 bs1 bs2 (Bauto Strong ck ([], ini) states)

    | Sdetlocal : forall Hi1 Hi2 bs1 bs2 s,
        sem_scope_det (fun Hi1 Hi2 => Forall (sem_block_det n envS Hi1 Hi2 bs1 bs2)) n envS Hi1 Hi2 bs1 bs2 s ->
        sem_block_det n envS Hi1 Hi2 bs1 bs2 (Blocal s).

    Ltac inv_branch :=
      match goal with
      | H:sem_branch_det _ _ _ _ _ _ _ _ |- _ => inv H; destruct_conjs; subst
      | H:sem_branch_det' _ _ _ _ _ _ |- _ => inv H; destruct_conjs; subst
      | _ => (Syn.inv_branch || Typ.inv_branch || Sem.inv_branch)
      end.

    Ltac inv_scope :=
      match goal with
      | H:sem_scope_det _ _ _ _ _ _ _ _ |- _ => inv H; destruct_conjs; subst
      | _ => (Syn.inv_scope || Typ.inv_scope || Sem.inv_scope)
      end.

    Ltac inv_block :=
      match goal with
      | H:sem_block_det _ _ _ _ _ _ _ |- _ => inv H
      | _ => (Syn.inv_block || Typ.inv_block || Sem.inv_block)
      end.

    Lemma sem_scope_det_0 {A} P_blk1 P_blk2 (P_blk3: _ -> _ -> _ -> Prop) :
      forall locs (blks: A) Hi1 Hi2 bs1 bs2,
        sem_scope P_blk1 Hi1 bs1 (Scope locs blks) ->
        sem_scope P_blk2 Hi2 bs2 (Scope locs blks) ->
        (forall Hi1 Hi2, P_blk1 Hi1 blks -> P_blk2 Hi2 blks -> P_blk3 Hi1 Hi2 blks) ->
        sem_scope_det P_blk3 0 [] Hi1 Hi2 bs1 bs2 (Scope locs blks).
    Proof.
      intros * Hsem1 Hsem2 Hblk.
      inv Hsem1. inv Hsem2.
      econstructor. 3:eauto. all:simpl_Forall; eauto using EqSt0.
      - split; intros ???; eauto using EqSt0.
      - intros * [].
    Qed.

    Lemma sem_branch_det_0 {A} must_def is_def P_blk1 P_blk2 (P_blk3: _ -> Prop) :
      forall caus (blks: A) Hi1 Hi2,
        sem_branch P_blk1 must_def is_def Hi1 (Branch caus blks) ->
        sem_branch P_blk2 must_def is_def Hi2 (Branch caus blks) ->
        (P_blk1 blks -> P_blk2 blks -> P_blk3 blks) ->
        sem_branch_det P_blk3 must_def is_def 0 [] Hi1 Hi2 (Branch caus blks).
    Proof.
      intros * Hsem1 Hsem2 Hblk. repeat inv_branch.
      econstructor; eauto. all:simpl_Forall.
      - intros ???; eauto using EqSt0.
      - intros [].
    Qed.

    (* Initialize with two "simple" sems *)
    Lemma sem_block_det_0 : forall blk Hi1 Hi2 bs1 bs2,
        sem_block G Hi1 bs1 blk ->
        sem_block G Hi2 bs2 blk ->
        sem_block_det 0 [] Hi1 Hi2 bs1 bs2 blk.
    Proof.
      induction blk using block_ind2; intros * Hsem1 Hsem2;
        inv Hsem1; inv Hsem2.
      - (* equation *)
        constructor; auto.
      - (* last *)
        econstructor; eauto.
      - (* reset *)
        econstructor; eauto.
        intros k. specialize (H7 k). specialize (H10 k).
        rewrite Forall_forall in *; eauto.
      - (* switch *)
        econstructor; eauto. simpl_Forall. destruct b.
        do 2 esplit. split; [|split]; eauto.
        eapply sem_branch_det_0; eauto.
        intros; simpl_Forall; eauto.
      - (* automaton (weak) *)
        econstructor; eauto. apply EqSt0.
        simpl_Forall. specialize (H10 k). specialize (H14 k). destruct b; destruct_conjs.
        do 2 esplit. split; [|split]; eauto.
        eapply sem_branch_det_0; eauto; intros; destruct s; destruct_conjs.
        eapply sem_scope_det_0; eauto.
        intros; destruct_conjs. split; [|split]; eauto.
        simpl_Forall; eauto.
      - (* automaton (strong) *)
        econstructor; eauto using EqSt0. 1,2:simpl_Forall.
        + specialize (H12 k). specialize (H9 k). destruct b; destruct_conjs.
          do 2 esplit. split; [|split]; eauto.
          repeat inv_branch. econstructor; eauto.
        + specialize (H13 k). specialize (H10 k). destruct b; destruct_conjs.
          do 2 esplit. split; [|split]; eauto.
          eapply sem_branch_det_0; eauto. intros; destruct_conjs.
          destruct s; destruct_conjs. eapply sem_scope_det_0; eauto.
          intros; simpl_Forall; eauto.
      - (* locals *)
        econstructor; eauto.
        eapply sem_scope_det_0; eauto.
        intros; simpl_Forall; eauto.
    Qed.

    (* Go from n to n + 1 :) *)
    Lemma det_scope_S {A} P_nd P_wt f_idcaus P_blk1 (P_blk2: _ -> _ -> _ -> Prop) :
      forall Γ n envS locs (blks: A) Hi1 Hi2 bs1 bs2,
        det_nodes G ->
        NoDupScope P_nd (map fst Γ) (Scope locs blks) ->
        wt_scope P_wt G Γ (Scope locs blks) ->
        EqStN (S n) bs1 bs2 ->
        (forall cx, det_var_inv Γ (S n) Hi1 Hi2 cx) ->
        incl (map snd (idcaus_of_scope f_idcaus (Scope locs blks))) envS ->
        sem_scope_det P_blk1 n envS Hi1 Hi2 bs1 bs2 (Scope locs blks) ->
        (forall Γ Hi1 Hi2,
            P_nd (map fst Γ) blks ->
            P_wt Γ blks ->
            (forall cx, det_var_inv Γ (S n) Hi1 Hi2 cx) ->
            incl (map snd (f_idcaus blks)) envS ->
            P_blk1 Hi1 Hi2 blks ->
            P_blk2 Hi1 Hi2 blks) ->
        sem_scope_det P_blk2 (S n) [] Hi1 Hi2 bs1 bs2 (Scope locs blks).
    Proof.
      intros * Hdet Hndl Hwt Hbs (* Hdoml1 Hdoml2  *)Hsc Hincl Hsem Hind; repeat inv_scope; subst Γ'; simpl in *.
      eapply Sscope with (Hi1':=Hi1') (Hi2':=Hi2'); eauto.
      - eapply Hind; eauto.
        + rewrite map_app, map_fst_senv_of_decls; auto.
        + intros. eapply det_var_inv_local with (Hi1':=Hi1'); eauto.
          split; intros. 1,2:eapply H9; eauto; eapply Hincl.
            1,2:repeat rewrite map_app, in_app_iff; left.
            1,2:clear - H; solve_In; try eapply idcaus_of_senv_In; eauto; auto.
        + etransitivity. 2:eapply Hincl.
          intros ??. rewrite map_app, in_app_iff; auto.
      - simpl_Forall. split; intros. 1,2:eapply H9; eauto; eapply Hincl.
        1,2:repeat rewrite map_app, in_app_iff; left.
        1,2:clear - H; solve_In; try eapply idcaus_of_senv_In; eauto; auto.
      - simpl_Forall. intros * [].
    Qed.

    Lemma det_branch_S {A} P_nd P_wt f_idcaus P_blk1 (P_blk2: _ -> Prop) must_def is_def :
      forall Γ n envS locs (blks: A) Hi1 Hi2,
        det_nodes G ->
        NoDupBranch P_nd (Branch locs blks) ->
        wt_branch P_wt (Branch locs blks) ->
        (forall cx, det_var_inv Γ (S n) Hi1 Hi2 cx) ->
        incl (map snd (idcaus_of_branch f_idcaus (Branch locs blks))) envS ->
        sem_branch_det P_blk1 must_def is_def n envS Hi1 Hi2 (Branch locs blks) ->
        (P_nd blks ->
         P_wt blks ->
         (forall cx, det_var_inv Γ (S n) Hi1 Hi2 cx) ->
         incl (map snd (f_idcaus blks)) envS ->
         P_blk1 blks ->
         P_blk2 blks) ->
        sem_branch_det P_blk2 must_def is_def (S n) [] Hi1 Hi2 (Branch locs blks).
    Proof.
      intros * Hdet Hndl Hwt (* Hdoml1 Hdoml2  *)Hsc Hincl Hsem Hind; repeat inv_branch; simpl in *.
      econstructor; eauto.
      - eapply Hind; eauto.
        + etransitivity. 2:eapply Hincl.
          intros ??. rewrite map_app, in_app_iff; auto.
      - simpl_Forall. eapply H7, Hincl; eauto.
        repeat rewrite map_app, in_app_iff in *. left; solve_In.
      - simpl_Forall. intros. now exfalso.
    Qed.

    Lemma det_block_S : forall n envS blk Γ Hi1 Hi2 bs1 bs2,
        det_nodes G ->
        NoDupLocals (map fst Γ) blk ->
        wt_block G Γ blk ->
        EqStN (S n) bs1 bs2 ->
        (forall cx, det_var_inv Γ (S n) Hi1 Hi2 cx) ->
        incl (map snd (idcaus_of_locals blk)) envS ->
        sem_block_det n envS Hi1 Hi2 bs1 bs2 blk ->
        sem_block_det (S n) [] Hi1 Hi2 bs1 bs2 blk.
    Proof.
      induction blk using block_ind2; intros * HdetG Hndl Hwt Hbs (* Hdoml1 Hdoml2  *)Hsc Hincl Hsem;
        inv Hndl; inv Hwt; inv Hsem; simpl in *.
      - (* equation *)
        constructor; eauto.

      - (* last *)
        econstructor; eauto.

      - (* reset *)
        econstructor; eauto.
        intros k. specialize (H14 k).
        rewrite Forall_forall in *; intros; eauto.
        eapply det_exp_n in H7; eauto. simpl_Forall.
        eapply bools_of_detn in H13; eauto.
        eapply H; eauto.
        + apply EqStN_mask; eauto.
        + intros. eapply det_var_inv_mask; eauto.
        + etransitivity. 2:eapply Hincl.
          intros ??. solve_In.

      - (* switch *)
        econstructor; eauto. simpl_Forall.
        do 2 esplit. split; [|split]; eauto.
        eapply det_exp_n in H10; eauto. simpl_Forall.
        destruct b. eapply det_branch_S; eauto.
        + intros. eapply det_var_inv_when; eauto.
        + etransitivity. 2:eapply Hincl.
          intros ??. simpl_In. solve_In.
        + intros; simpl in *. simpl_Forall; eauto.
          eapply H; eauto using EqStN_fwhen.
          etransitivity; [|eauto]. intros ??; solve_In.

      - (* automaton (weak) *)
        take (sem_clock _ _ _ _) and eapply sem_clock_detN in it as Hbs'; eauto with ltyping.
        assert (EqStN (S n) stres1 stres2) as Hstates.
        { take (fby _ _ stres2) and eapply fby_det_Sn in it; eauto.
          eapply sem_transitions_detS in H15; eauto using det_var_inv_weaken.
          simpl_Forall; eauto. }
        assert (EqStN (S n) stres11 stres12) as Hstates1.
        { eapply EqStN_unfselect with (tn:=length states); eauto.
          + destruct states; simpl in *; lia.
          + eapply sem_automaton_wt_state1 with (states:=states) in H14; eauto.
            1,3,4:simpl_Forall; try destruct s; destruct_conjs; eauto.
            * repeat inv_branch. repeat inv_scope. simpl_Forall; auto.
            * repeat inv_branch. repeat inv_scope.
              intros. specialize (H23 k); destruct_conjs.
              repeat inv_branch. repeat inv_scope. simpl_Forall; eauto.
            * rewrite <-H9. now apply fst_InMembers.
          + eapply sem_automaton_wt_state1 with (states:=states) in H15; eauto.
            1,3,4:simpl_Forall; try destruct s; destruct_conjs; eauto.
            * repeat inv_branch. repeat inv_scope. simpl_Forall; auto.
            * repeat inv_branch. repeat inv_scope.
              intros. specialize (H23 k); destruct_conjs.
              repeat inv_branch. repeat inv_scope. simpl_Forall; eauto.
            * rewrite <-H9. now apply fst_InMembers.
          + take (fby _ _ stres1) and (apply ac_fby2 in it; rewrite <-it). apply ac_slower.
          + take (fby _ _ stres2) and (apply ac_fby2 in it; rewrite <-it). apply ac_slower.
          + intros * Hsel.
            assert (exists c blks, In ((sel, c), blks) states) as (?&blks&Hinstates).
            { rewrite <-H9 in Hsel. simpl_In; eauto. }
            simpl_Forall. repeat inv_branch. repeat inv_scope.
            specialize (H23 k); destruct_conjs.
            repeat inv_branch. repeat inv_scope.
            eapply sem_transitions_detn in H25; eauto using det_var_inv_select, det_var_inv_weaken.
            * simpl_Forall; eauto.
            * intros.
              eapply det_var_inv_local. 4:intros; eapply det_var_inv_select; eauto. all:eauto.
              split; intros ? Ca.
              1,2:take (forall cx, In _ envS -> det_var_inv _ _ _ _ _) and eapply it; eauto.
              1,2:eapply Hincl; clear - Hinstates Ca; solve_In.
              2,4:rewrite 2 in_app_iff; right; left; eapply idcaus_of_senv_In; eauto. 1,2:auto.
            * apply EqStN_mask. 1,2:apply EqStN_fwhen; eauto using EqStN_weaken.
              1-3:apply map_EqStN; eauto using EqStN_weaken.
        }
        econstructor; eauto.
        simpl_Forall. specialize (H23 k); destruct_conjs.
        do 2 esplit. repeat (split; eauto).
        destruct b as [?(?&[?(?&?)])]; destruct_conjs.
        eapply det_branch_S; eauto. 3:intros; destruct_conjs; eapply det_scope_S; eauto.
        + intros. eapply det_var_inv_select. 2-4:eauto. eauto.
        + etransitivity. 2:eapply Hincl.
          intros ??. simpl_In. solve_In.
        + apply EqStN_mask. 1,2:apply EqStN_fwhen; auto.
          1-3:apply map_EqStN; auto.
        + instantiate (1:=fun '(blks, _) => flat_map idcaus_of_locals blks).
          etransitivity. 2:eapply Hincl. eapply incl_map.
          intros ??. eapply in_flat_map'. solve_Exists; auto with datatypes.
        + intros; simpl in *. destruct_conjs.
          split; [|split]; eauto. simpl_Forall.
          eapply H; eauto.
          * apply EqStN_mask. 1,2:apply EqStN_fwhen; auto.
            1-3:apply map_EqStN; auto.
          * etransitivity; [|eauto]. intros ??; solve_In.

      - (* automaton (strong) *)
        take (sem_clock _ _ _ _) and eapply sem_clock_detN in it as Hbs'; eauto with ltyping.
        assert (EqStN (S n) stres1 stres2) as Hstates.
        { take (fby _ _ stres2) and eapply fby_det_Sn in it; eauto using const_stres_detn. }
        assert (EqStN (S n) stres11 stres12) as Hstates1.
        { eapply EqStN_unfselect with (tn:=length states); eauto.
          + destruct states; simpl in *; lia.
          + eapply sem_automaton_wt_state2 with (states:=states) in H12; eauto.
            2,3:simpl_Forall; try destruct s; destruct_conjs; eauto.
            * rewrite <-H8. now apply fst_InMembers.
            * repeat inv_branch. repeat inv_scope. simpl_Forall; auto.
            * repeat inv_branch. repeat inv_scope.
              intros. specialize (H18 k); destruct_conjs.
              repeat inv_branch. simpl_Forall; eauto.
          + eapply sem_automaton_wt_state2 with (states:=states) in H13; eauto.
            2,3:simpl_Forall; try destruct s; destruct_conjs; eauto.
            * rewrite <-H8. now apply fst_InMembers.
            * repeat inv_branch. repeat inv_scope. simpl_Forall; auto.
            * repeat inv_branch. repeat inv_scope.
              intros. specialize (H18 k); destruct_conjs.
              repeat inv_branch. simpl_Forall; eauto.
          + take (fby _ _ stres1) and (apply ac_fby2 in it; rewrite <-it). apply ac_slower.
          + take (fby _ _ stres2) and (apply ac_fby2 in it; rewrite <-it). apply ac_slower.
          + intros * Hsel.
            assert (exists c blks, In ((sel, c), blks) states) as (?&blks&Hinstates).
            { rewrite <-H8 in Hsel. simpl_In; eauto. }
            simpl_Forall.
            specialize (H18 k); destruct_conjs; repeat inv_branch.
            eapply sem_transitions_detn in H7; eauto using det_var_inv_select, det_var_inv_weaken.
            * repeat inv_branch. repeat inv_scope. simpl_Forall; eauto.
            * apply EqStN_mask. 1,2:apply EqStN_fwhen; eauto using EqStN_weaken.
              1-3:apply map_EqStN; eauto using EqStN_weaken.
        }
        econstructor; eauto; simpl_Forall.
        + specialize (H20 k); destruct_conjs.
          do 2 esplit. repeat (split; eauto).
          destruct b as [?(?&[?(?&?)])]; destruct_conjs.
          eapply det_branch_S; eauto. 3:intros; destruct_conjs; eapply det_scope_S; eauto.
          * intros. eapply det_var_inv_select. 2-4:eauto. eauto.
          * etransitivity. 2:eapply Hincl.
            intros ??. simpl_In. solve_In.
          * apply EqStN_mask. 1,2:apply EqStN_fwhen; auto.
            1-3:apply map_EqStN; auto.
          * instantiate (1:=fun '(blks, _) => flat_map idcaus_of_locals blks).
            etransitivity. 2:eapply Hincl. eapply incl_map.
            intros ??. eapply in_flat_map'. solve_Exists; auto with datatypes.
          * intros; simpl in *. destruct_conjs.
            simpl_Forall.
            eapply H; eauto.
            -- apply EqStN_mask. 1,2:apply EqStN_fwhen; auto.
               1-3:apply map_EqStN; auto.
            -- etransitivity; [|eauto]. intros ??; solve_In.

      - (* locals *)
        econstructor; eauto.
        eapply det_scope_S; eauto.
        intros; simpl_Forall. eapply H; eauto.
        etransitivity; [|eauto]. intros ??; solve_In.
    Qed.

    Fact sem_block_det_sem_block1 : forall n envS blk Hi1 Hi2 bs1 bs2,
        sem_block_det n envS Hi1 Hi2 bs1 bs2 blk ->
        sem_block G Hi1 bs1 blk.
    Proof.
      induction blk using block_ind2; intros * Hsem; inv Hsem.
      - (* equation *)
        constructor; auto.
      - (* last *)
        econstructor; eauto.
      - (* reset *)
        econstructor; eauto.
        intros k. specialize (H10 k). simpl_Forall; eauto.
      - (* switch *)
        econstructor; eauto.
        simpl_Forall. do 2 esplit; eauto.
        repeat inv_branch.
        econstructor; eauto. simpl_Forall; eauto.
      - (* automaton (weak) *)
        econstructor; eauto.
        simpl_Forall. specialize (H15 k); destruct_conjs.
        repeat inv_branch. repeat inv_scope.
        esplit. repeat (split; eauto).
        eapply Sem.Sscope with (Hi':=Hi1'); eauto.
        split; simpl_Forall; eauto.
      - (* automaton (strong) *)
        econstructor; eauto.
        + simpl_Forall. specialize (H12 k); destruct_conjs.
          repeat inv_branch. repeat inv_scope.
          esplit; eauto. split; [|econstructor]; eauto.
        + simpl_Forall. specialize (H14 k); destruct_conjs.
          repeat inv_branch. repeat inv_scope.
          esplit. repeat (split; eauto).
          eapply Sem.Sscope with (Hi':=Hi1'); eauto.
          simpl_Forall; eauto.
      - (* locals *)
        constructor. inv H5.
        eapply Sem.Sscope with (Hi':=Hi1'); eauto. simpl_Forall; eauto.
    Qed.

    Fact sem_block_det_sem_block2 : forall n envS blk Hi1 Hi2 bs1 bs2,
        sem_block_det n envS Hi1 Hi2 bs1 bs2 blk ->
        sem_block G Hi2 bs2 blk.
    Proof.
      induction blk using block_ind2; intros * Hsem; inv Hsem.
      - (* equation *)
        constructor; auto.
      - (* last *)
        econstructor; eauto.
      - (* reset *)
        econstructor; eauto.
        intros k. specialize (H10 k). simpl_Forall; eauto.
      - (* switch *)
        econstructor; eauto.
        simpl_Forall. do 2 esplit; eauto.
        repeat inv_branch.
        econstructor; eauto. simpl_Forall; eauto.
      - (* automaton (weak) *)
        econstructor; eauto.
        simpl_Forall. specialize (H15 k); destruct_conjs.
        repeat inv_branch. repeat inv_scope.
        esplit. repeat (split; eauto).
        econstructor; eauto.
        split; simpl_Forall; eauto.
      - (* automaton (strong) *)
        econstructor; eauto.
        + simpl_Forall. specialize (H12 k); destruct_conjs. repeat inv_branch.
          esplit; eauto. split; [|econstructor]; eauto.
        + simpl_Forall. specialize (H14 k); destruct_conjs.
          repeat inv_branch. repeat inv_scope.
          esplit. repeat (split; eauto).
          econstructor; eauto.
          simpl_Forall; eauto.
      - (* locals *)
        constructor. inv H5. econstructor; eauto. simpl_Forall; eauto.
    Qed.

    (* Hint Resolve sem_block_det_sem_block1 sem_block_det_sem_block2 : ldet. *)

    Lemma det_var_inv_incl : forall Γ Γ' n Hi1 Hi2 x,
        incl Γ Γ' ->
        det_var_inv Γ' n Hi1 Hi2 x ->
        det_var_inv Γ n Hi1 Hi2 x.
    Proof.
      intros * Hincl1 Hdet.
      split; intros ??? Hin Hv1 Hv2; eauto.
      1,2:eapply Hdet in Hv2; eauto with senv.
    Qed.

    Import Permutation.

    Lemma sem_block_det_Perm : forall n xs ys blk Hi1 Hi2 bs1 bs2,
        Permutation xs ys ->
        sem_block_det n xs Hi1 Hi2 bs1 bs2 blk ->
        sem_block_det n ys Hi1 Hi2 bs1 bs2 blk.
    Proof.
      induction blk using block_ind2; intros * Hperm Hsem;
        inv Hsem.
      - (* equation *)
        constructor; auto.
      - (* last *)
        econstructor; eauto.
      - (* reset *)
        econstructor; eauto.
        intros k. specialize (H10 k). simpl_Forall; eauto.
      - (* switch *)
        econstructor; eauto. simpl_Forall.
        do 2 esplit. split; [|split]; eauto.
        repeat inv_branch. econstructor; eauto.
        1-2:simpl_Forall; eauto.
        + rewrite <-Hperm; auto.
      - (* automaton (weak) *)
        econstructor; eauto. simpl_Forall. specialize (H15 k); destruct_conjs.
        do 2 esplit. repeat (split; eauto).
        repeat inv_branch. repeat inv_scope. econstructor. econstructor. 3,4:eauto.
        all:simpl_Forall; eauto.
        + repeat split; simpl_Forall; eauto.
        + intros. take (In _ ys) and rewrite <-Hperm in it; auto.
        + intros. take (In _ ys) and rewrite <-Hperm in it; auto.
      - (* automaton (strong) *)
        econstructor; eauto.
        + simpl_Forall. specialize (H14 k); destruct_conjs.
          do 2 esplit. repeat (split; eauto).
          repeat inv_branch. repeat inv_scope. constructor. econstructor. 3,4:eauto.
          all:simpl_Forall; eauto; intros.
          1,2:take (In _ ys) and rewrite <-Hperm in it; auto.
      - (* local *)
        econstructor; eauto.
        repeat inv_scope. econstructor. 3,4:eauto.
        all:simpl_Forall; eauto.
        intros. take (In _ ys) and rewrite <-Hperm in it; auto.
    Qed.

    Lemma det_scope_cons {A} f_idcaus P_nd P_wt (P_blk1 P_blk2 : _ -> _ -> _ -> Prop) P_vd P_ld P_def P_dep :
      forall n envS locs (blks: A) Γ xs ls Hi1 Hi2 bs1 bs2 cy,
        det_nodes G ->
        NoDupMembers Γ ->
        NoDup (map snd (idcaus_of_senv Γ ++ idcaus_of_scope f_idcaus (Scope locs blks))) ->
        NoDupScope P_nd (map fst Γ) (Scope locs blks) ->
        VarsDefinedCompScope P_vd (Scope locs blks) xs ->
        incl xs (map fst Γ) ->
        LastsDefinedScope P_ld (Scope locs blks) ls ->
        incl ls (map fst Γ) ->
        (forall cx, det_var_inv Γ n Hi1 Hi2 cx) ->
        wt_scope P_wt G Γ (Scope locs blks) ->
        sem_scope_det P_blk1 n envS Hi1 Hi2 bs1 bs2 (Scope locs blks) ->
        EqStN n bs1 bs2 ->
        (Is_defined_in_scope P_def Γ cy (Scope locs blks) -> EqStN (S n) bs1 bs2) ->
        (forall cx, depends_on_scope P_dep Γ cy cx (Scope locs blks) -> det_var_inv Γ (S n) Hi1 Hi2 cx) ->
        (forall cx, In cx (map snd (idcaus_of_scope f_idcaus (Scope locs blks))) ->
               depends_on_scope P_dep Γ cy cx (Scope locs blks) -> In cx envS) ->
        (forall Γ xs ls Hi1 Hi2,
            NoDupMembers Γ ->
            NoDup (map snd (idcaus_of_senv Γ ++ f_idcaus blks)) ->
            P_nd (map fst Γ) blks ->
            P_vd blks xs ->
            incl xs (map fst Γ) ->
            P_ld blks ls ->
            incl ls (map fst Γ) ->
            (forall cx, det_var_inv Γ n Hi1 Hi2 cx) ->
            P_wt Γ blks ->
            P_blk1 Hi1 Hi2 blks ->
            (P_def Γ blks -> EqStN (S n) bs1 bs2) ->
            (forall cx, P_dep Γ cy cx blks -> det_var_inv Γ (S n) Hi1 Hi2 cx) ->
            (forall cx, In cx (map snd (f_idcaus blks)) ->
                   P_dep Γ cy cx blks -> In cx envS) ->
            (forall y, In y xs -> HasCaus Γ y cy -> det_var (S n) Hi1 Hi2 (Var y))
            /\ (forall y, In y ls -> HasLastCaus Γ y cy -> det_var (S n) Hi1 Hi2 (Last y))
            /\ P_blk2 Hi1 Hi2 blks) ->
        (forall y, In y xs -> HasCaus Γ y cy -> det_var (S n) Hi1 Hi2 (Var y))
        /\ (forall y, In y ls -> HasLastCaus Γ y cy -> det_var (S n) Hi1 Hi2 (Last y))
        /\ sem_scope_det P_blk2 n (cy::envS) Hi1 Hi2 bs1 bs2 (Scope locs blks).
    Proof.
      intros * HdetG Hnd1 Hnd Hnd2 Hvd Hivd Hld Hild Hn Hwt Hsem Hbs HSbs HSn HenvS Hind;
        inv Hnd2; inv Hvd; inv Hld; inv Hwt; inv Hsem; subst Γ'; simpl in *.
      take (forall x, InMembers x locs -> ~ _) and rename it into Hnd2.
      edestruct Hind with (Γ:=Γ ++ senv_of_decls locs) (xs:=xs ++ map fst locs) as (Hdetv&Hdetl&Hcons); eauto using in_or_app.
      1:{ apply NoDupScope_NoDupMembers; auto. }
      1:{ rewrite idcaus_of_senv_app, <-app_assoc.
          eapply Permutation_NoDup; [|eauto].
          solve_Permutation_app. }
      1:{ now rewrite map_app, map_fst_senv_of_decls. }
      1:{ rewrite map_app, map_fst_senv_of_decls.
          eapply incl_appl'; auto. }
      1:{ rewrite map_app, map_fst_senv_of_decls.
          eapply incl_app; [apply incl_appl|apply incl_appr]; auto.
          unfold lasts_of_decls. intros ? In. clear -In. solve_In. }
      1:{ intros. eapply det_var_inv_local; eauto. }
      1:{ intros; eauto with lcaus. }
      1:{ intros * Hdep. eapply det_var_inv_local; eauto.
          + intros. eapply HSn; eauto.
            econstructor; eauto.
          + split; intros * In; eapply H17; eauto.
            1,2:eapply HenvS; [|econstructor; eauto].
            1,2:eapply in_map_iff; do 2 esplit; [|apply in_app_iff; left; eapply idcaus_of_senv_In; eauto].
            1,2:auto.
      }
      1:{ intros * Hin Hdep. apply HenvS.
          + repeat rewrite map_app, in_app_iff. auto.
          + econstructor; eauto. }
      split; [|split].
      - intros * Hxs Hin ?? V1 V2.
        eapply Hdetv; eauto using in_or_app. apply HasCaus_app; auto.
        1,2:eapply sem_var_union2; eauto; intros contra.
        + apply H7, IsVar_senv_of_decls in contra.
          eapply Hnd2; eauto.
        + apply H10, IsVar_senv_of_decls in contra.
          eapply Hnd2; eauto.
      - intros * Hxs Hin ?? V1 V2.
        eapply Hdetl; eauto using in_or_app. apply HasLastCaus_app; auto.
        1,2:eapply sem_var_union2; eauto; intros contra.
        + apply H7, IsLast_senv_of_decls in contra.
          eapply Hnd2; eauto.
        + apply H10, IsLast_senv_of_decls in contra.
          eapply Hnd2; eauto.
      - econstructor. 3,4:eauto. all:eauto.
        intros ? [|HinS]; subst; auto.
        split; intros * Hc ?? Hv1 Hv2.
        + eapply Hdetv; eauto using sem_var_union3'.
          * apply in_or_app. right. clear - Hc. inv Hc. solve_In.
          * apply HasCaus_app; auto.
        + eapply Hdetl; eauto using sem_var_union3'.
          * apply in_or_app. right. clear - Hc. inv Hc. unfold lasts_of_decls. solve_In.
          * apply HasLastCaus_app; auto.
    Qed.

    Lemma det_branch_cons {A} f_idcaus P_nd P_vd P_ld P_wt (P_blk1 P_blk2 : _ -> Prop) P_dep must_def is_def :
      forall n envS caus (blks: A) Γ xs Hi1 Hi2 cy,
        det_nodes G ->
        NoDupMembers Γ ->
        NoDup (map snd (idcaus_of_senv Γ ++ idcaus_of_branch f_idcaus (Branch caus blks))) ->
        NoDupBranch P_nd (Branch caus blks) ->
        VarsDefinedCompBranch P_vd (Branch caus blks) xs ->
        incl xs (map fst Γ) ->
        LastsDefinedBranch P_ld (Branch caus blks) ->
        (forall cx, det_var_inv Γ n Hi1 Hi2 cx) ->
        wt_branch P_wt (Branch caus blks) ->
        sem_branch_det P_blk1 must_def is_def n envS Hi1 Hi2 (Branch caus blks) ->
        (forall cx, depends_on_branch P_dep Γ cy cx (Branch caus blks) -> det_var_inv Γ (S n) Hi1 Hi2 cx) ->
        (forall cx, In cx (map snd (idcaus_of_branch f_idcaus (Branch caus blks))) ->
               depends_on_branch P_dep Γ cy cx (Branch caus blks) -> In cx envS) ->
        (let Γ := replace_idcaus caus Γ in
         NoDupMembers Γ ->
         NoDup (map snd (idcaus_of_senv Γ ++ f_idcaus blks)) ->
         P_nd blks ->
         P_vd blks xs ->
         incl xs (map fst Γ) ->
         P_ld blks ->
         (forall cx, det_var_inv Γ n Hi1 Hi2 cx) ->
         P_wt blks ->
         P_blk1 blks ->
         (forall cx, P_dep Γ cy cx blks -> det_var_inv Γ (S n) Hi1 Hi2 cx) ->
         (forall cx, In cx (map snd (f_idcaus blks)) ->
                P_dep Γ cy cx blks -> In cx envS) ->
         (forall y, In y xs -> HasCaus Γ y cy -> det_var (S n) Hi1 Hi2 (Var y))
         /\ P_blk2 blks) ->
        (forall y, In y xs -> HasCaus Γ y cy -> det_var (S n) Hi1 Hi2 (Var y))
        /\ sem_branch_det P_blk2 must_def is_def n (cy::envS) Hi1 Hi2 (Branch caus blks).
    Proof.
      intros * HdetG Hnd1 Hnd Hnd2 Hvd Hincl Hld Hn Hwt Hsem HSn HenvS Hind;
        inv Hnd2; inv Hvd; inv Hld; inv Hwt; inv Hsem; simpl in *.
      edestruct Hind as (Hdet&Hcons); eauto using in_or_app.
      1:{ apply NoDupMembers_map; auto. }
      1:{ apply replace_idcaus_NoDup; auto. }
      1:{ now rewrite map_fst_replace_idcaus. }
      1:{ intros *. eapply det_var_inv_branch; eauto.
          - intros * Hin. simpl_Forall. eauto. }
      1:{ intros * Hdep. eapply det_var_inv_branch; eauto.
          + intros. eapply HSn; eauto.
            econstructor; eauto.
          + intros * Hin. simpl_Forall. eapply H13, HenvS.
            * rewrite map_app, in_app_iff. left. solve_In.
            * econstructor; eauto. }
      1:{ intros * Hin Hdep. apply HenvS.
          + repeat rewrite map_app, in_app_iff. auto.
          + econstructor; eauto. }
      split.
      - intros * Hxs Hinenv.
        destruct (in_dec ident_eq_dec y (map fst caus)); simpl_In.
        + simpl_Forall.
          eapply H13; eauto. apply HenvS; eauto with lcaus.
          repeat rewrite map_app, in_app_iff. left; solve_In.
        + eapply Hdet; eauto. eapply replace_idcaus_HasCaus2; eauto.
          now rewrite fst_InMembers.
      - econstructor; eauto.
        simpl_Forall. intros [|HinS]; subst; eauto.
        assert (In i xs) as Hinxs by (take (incl _ xs) and apply it; solve_In).
        assert (HasCaus (replace_idcaus caus Γ) i i0) as Hca.
        { apply Hincl in Hinxs. simpl_In.
          eapply replace_idcaus_HasCaus1; eauto with senv. }
        intros. eauto.
    Qed.

    Lemma det_block_cons : forall n envS blk Γ xs ls Hi1 Hi2 bs1 bs2 cy,
        det_nodes G ->
        NoDupMembers Γ ->
        NoDup (map snd (idcaus_of_senv Γ ++ idcaus_of_locals blk)) ->
        NoDupLocals (map fst Γ) blk ->
        VarsDefinedComp blk xs ->
        incl xs (map fst Γ) ->
        LastsDefined blk ls ->
        incl ls (map fst Γ) ->
        (forall cx, det_var_inv Γ n Hi1 Hi2 cx) ->
        wt_block G Γ blk ->
        sem_block_det n envS Hi1 Hi2 bs1 bs2 blk ->
        EqStN n bs1 bs2 ->
        (Is_defined_in Γ cy blk -> EqStN (S n) bs1 bs2) ->
        (forall cx, depends_on Γ cy cx blk -> det_var_inv Γ (S n) Hi1 Hi2 cx) ->
        (forall cx, In cx (map snd (idcaus_of_locals blk)) ->
               depends_on Γ cy cx blk -> In cx envS) ->
        (forall y, In y xs -> HasCaus Γ y cy -> det_var (S n) Hi1 Hi2 (Var y))
        /\ (forall y, In y ls -> HasLastCaus Γ y cy -> det_var (S n) Hi1 Hi2 (Last y))
        /\ sem_block_det n (cy::envS) Hi1 Hi2 bs1 bs2 blk.
    Proof.
      induction blk as [(xs&es)| | | | |] using block_ind2;
        intros * HdetG Hnd1 Hnd Hnd2 Hvd Hvdi Hld Hldi Hn Hwt Hsem Hbs HSbs HSn HenvS;
        assert (Hsem':=Hsem); inv Hnd2; inv Hvd; inv Hld; inv Hwt; inv Hsem; simpl in *.

      - (* equation *)
        split; [|split]; [|intros * []|constructor; auto].
        intros * Hinxs Hca; subst.
        eapply In_nth in Hinxs as (?&Hlen&Hnth); subst. instantiate (1:=xH) in Hnth.
        rewrite app_nil_r in Hnd.
        eapply det_equation_S; eauto.
        + eapply Pexp_Pexps.
          * simpl_Forall.
            eapply det_exp_S; eauto.
            eapply HSbs. econstructor; eauto. rewrite <-Hnth. now apply nth_In.
          * intros ? IsF. assert (IsF':=IsF). eapply Is_used_inst_list_In_snd in IsF as (?&?).
            eapply HSn; eauto.
            rewrite <-Hnth in *. econstructor; eauto using nth_error_nth'.
          * destruct H1 as (_&Hf2). apply Forall2_length in Hf2.
            rewrite <-length_typesof_annots. congruence.
        + now rewrite Hnth.

      - (* last *)
        split; [|split]; [intros * []| |econstructor; eauto].
        intros * [|[]] Hca ?? L1 L2; subst.
        eapply sem_var_det in H8; [|eauto]; rewrite H8.
        eapply sem_var_det in H16; [|eauto]; rewrite H16.
        eapply fby_det_Sn; eauto.
        + eapply det_exp_S with (k:=0) in H3; eauto.
          specialize (H3 H9). simpl in *; auto.
          * rewrite <-length_typeof_numstreams, H5. auto.
          * eapply HSbs. constructor. auto.
          * intros * USed. eapply HSn. econstructor; eauto.
        + assert (exists cy', HasCaus Γ y cy') as (?&Hca').
          { inv Hca. do 2 econstructor; eauto. }
          eapply Hn in Hca'; eauto.

      - (* reset *)
        assert (EqStN n r1 r2) as Hr.
        { eapply bools_of_detn; eauto.
          eapply det_exp_n, Forall2_singl in H9; eauto using EqStN_weaken. }
        assert (Is_defined_in Γ cy (Breset blocks er) -> EqStN (S n) r1 r2) as HSr.
        { intros * Hdef.
          eapply bools_of_detn. 2,3:eauto.
          eapply det_exp_S with (k:=0) (n:=n) in H6; eauto.
          - eapply H6 in H9; simpl in H9; eauto.
          - rewrite <-length_typeof_numstreams, H8; simpl. lia.
          - intros ? IsF. assert (IsF':=IsF). eapply Is_used_inst_In_snd in IsF as (?&?).
            eapply HSn, DepOnReset2; eauto.
        }
        assert (forall k, Forall (fun blks => (forall y xs, VarsDefinedComp blks xs -> In y xs -> HasCaus Γ y cy ->
                                               det_var (S n) (mask_hist k r1 Hi1) (mask_hist k r2 Hi2) (Var y))
                                      /\ (forall y xs, LastsDefined blks xs -> In y xs -> HasLastCaus Γ y cy ->
                                                 det_var (S n) (mask_hist k r1 Hi1) (mask_hist k r2 Hi2) (Last y))
                                      /\ sem_block_det n (cy::envS) (mask_hist k r1 Hi1) (mask_hist k r2 Hi2) (maskb k r1 bs1) (maskb k r2 bs2) blks) blocks) as Hf.
        { intros *. specialize (H16 k). simpl_Forall. inv_VarsDefined.
          edestruct H with (xs:=xs2) (ls:=xs1) as (Hdetv&Hdetl&Hsem). 11:eauto. all:eauto.
          - eapply NoDup_locals_inv; eauto.
          - etransitivity; eauto using incl_concat.
          - etransitivity; eauto using incl_concat.
          - intros. eapply det_var_inv_mask; eauto.
          - eapply EqStN_mask; eauto.
          - intros Hdef'. eapply EqStN_mask; eauto.
            + eapply HSr. econstructor. solve_Exists.
            + eapply HSbs. econstructor. solve_Exists.
          - intros * Hdep. eapply det_var_inv_mask; eauto.
            + eapply HSr, depends_on_def. econstructor; solve_Exists.
            + eapply HSn; eauto. constructor. solve_Exists.
          - intros * Hin' Hdep. eapply HenvS; eauto.
            2:constructor; solve_Exists. solve_In.
          - split; [|split]; eauto.
            + intros * Hdef' Hin' Hca. eapply Hdetv; eauto.
              eapply VarsDefinedComp_det in Hdef0; eauto. now rewrite <-Hdef0.
            + intros * Hdef' Hin' Hca. eapply Hdetl; eauto.
              eapply LastsDefined_det in Hdef; eauto. now rewrite <-Hdef.
        } clear H.
        split; [|split].
        + intros * Hinxs Hca.
          apply in_concat in Hinxs as (?&Hin1&Hin2). inv_VarsDefined. simpl_Forall.
          eapply det_var_unmask; intros.
          * eapply HSr; eauto. eapply Is_defined_in_Is_defined_in; eauto.
            constructor; solve_Exists. eapply VarsDefinedComp_Is_defined; eauto.
            eapply NoDupLocals_incl; [|eauto]. etransitivity; eauto using incl_concat.
          * specialize (Hf k). simpl_Forall; eauto.
        + intros * Hinxs Hca.
          apply in_concat in Hinxs as (?&Hin1&Hin2). inv_VarsDefined. simpl_Forall.
          eapply det_var_unmask; intros.
          * eapply HSr; eauto. eapply Is_defined_in_last_Is_defined_in; eauto.
            constructor; solve_Exists. eapply LastsDefined_Is_defined; eauto.
            eapply NoDupLocals_incl; [|eauto]. etransitivity; eauto using incl_concat.
          * specialize (Hf k). simpl_Forall; eauto.

        + econstructor; eauto.
          intros k. specialize (Hf k). simpl_Forall; eauto.

      - (* switch *)
        assert (EqStN n sc1 sc2) as Hsc.
        { eapply det_exp_n, Forall2_singl in H14; eauto. }
        assert (Is_defined_in Γ cy (Bswitch ec branches) -> EqStN (S n) sc1 sc2) as HSsc.
        { intros * Hdef.
          eapply det_exp_S with (k:=0) (n:=n) in H11; eauto.
          - eapply H11 in H14; simpl in H14; eauto.
          - rewrite <-length_typeof_numstreams, H8; simpl. lia.
          - intros ? IsF. assert (IsF':=IsF). eapply Is_used_inst_In_snd in IsF as (?&?).
            eapply HSn, DepOnSwitch2; eauto.
        }
        assert (Forall (fun '(k, s) => exists Hi1' Hi2',
                            when_hist k Hi1 sc1 Hi1' /\ when_hist k Hi2 sc2 Hi2'
                            /\ (forall y, In y xs -> HasCaus Γ y cy -> det_var (S n) Hi1' Hi2' (Var y))
                            /\ sem_branch_det
                                (Forall (sem_block_det n (cy::envS) Hi1' Hi2' (fwhenb k bs1 sc1) (fwhenb k bs2 sc2)))
                                (fun x : ident => Syn.Is_defined_in (Var x) (Bswitch ec branches))
                                (fun x : ident => Exists (Syn.Is_defined_in (Var x)))
                                n (cy :: envS) Hi1' Hi2' s)
                       branches) as Hf.
        { simpl_Forall. destruct b. do 2 esplit; eauto. split; [|split]; eauto.
          eapply det_branch_cons; eauto.
          - eapply NoDup_locals_inv2; eauto.
          - intros *. eapply det_var_inv_when; eauto using EqStN_weaken.
          - intros * Hdep. eapply det_var_inv_when; eauto.
            + eapply HSsc, depends_on_def. econstructor; solve_Exists; eauto.
            + eapply HSn; eauto. constructor. solve_Exists.
          - intros * Hin' Hdep. eapply HenvS; eauto.
            2:constructor; solve_Exists. solve_In.
          - intros; simpl in *. destruct_conjs.
            assert (Forall (fun blks => (forall y xs, VarsDefinedComp blks xs -> In y xs -> HasCaus Γ0 y cy ->
                                              det_var (S n) x x0 (Var y))
                                     /\ sem_block_det n (cy::envS) x x0 (fwhenb e bs1 sc1) (fwhenb e bs2 sc2) blks) l0) as Hf.
            { simpl_Forall. inv_VarsDefined.
              edestruct H with (Γ:=Γ0) as (Detv&_&Sem). 9:eauto. all:eauto.
              - eapply NoDup_locals_inv; eauto.
              - eapply NoDupLocals_incl; eauto. subst Γ0. now rewrite map_fst_replace_idcaus.
              - etransitivity; eauto using incl_concat.
                take (Permutation _ _) and now rewrite it.
              - apply incl_nil'.
              - subst Γ0. eapply wt_block_incl. 3:eauto. 1,2:intros; (rewrite replace_idcaus_HasType||rewrite replace_idcaus_IsLast); auto.
              - eapply EqStN_fwhen; eauto.
              - intros Hdef'. eapply EqStN_fwhen; eauto.
                eapply HSsc. 2:eapply HSbs. 1,2:do 2 (econstructor; solve_Exists).
              - intros * Hdep. eapply H28; eauto. solve_Exists.
              - intros * Hin' Hdep. eapply H29; eauto.
                2:solve_Exists. solve_In.
              - split; eauto.
                intros * Hdef' Hin' Hca. eapply Detv; eauto.
                eapply VarsDefinedComp_det in Hdef; eauto. now rewrite <-Hdef.
            }
            split; simpl_Forall; eauto.
            intros * Hin Hca. rewrite <-H30 in Hin. apply in_concat in Hin as (?&?&?).
            inv_VarsDefined; simpl_Forall; eauto.
        } clear H H21.
        split; [|split].
        + repeat (take (wt_streams [_] (typeof ec)) and rewrite H8 in it; apply Forall2_singl in it).
          intros * Hinxs Hca.
          eapply det_var_unwhen with (sc1:=sc1); eauto.
          * destruct tn; simpl in *; try lia.
            apply Permutation_sym, Permutation_nil, map_eq_nil in H10; congruence.
          * eapply HSsc; eauto. eapply Is_defined_in_Is_defined_in; eauto.
            eapply VarsDefinedComp_Is_defined; eauto. econstructor; eauto.
            eapply NoDupLocals_incl; [|econstructor; eauto]. eauto.
          * intros * Hseq.
            assert (exists blks, In (c, blks) branches) as (blks&Hinbrs).
            { rewrite <-H10 in Hseq. simpl_In; eauto. }
            simpl_Forall. do 2 esplit. split; [|split; [|split]]; eauto.
            destruct blks. split; eapply sem_branch_defined1; eauto.
            1,2:inv H15; econstructor; eauto; simpl_Forall; eauto using sem_block_det_sem_block1, sem_block_det_sem_block2.
        + intros * [].
        + econstructor; eauto.
          simpl_Forall. eauto.

      - (* automaton (weak) *)
        assert (EqStN n bs'1 bs'2) as Hbs' by (eapply sem_clock_detN; eauto with ltyping).
        assert (Is_defined_in Γ cy (Bauto Weak ck (ini0, oth) states) -> EqStN (S n) bs'1 bs'2) as HSbs'.
        { intros. eapply sem_clock_detN; eauto with ltyping.
          intros. eapply HSn; eauto with lcaus. }
        assert (EqStN n stres1 stres2) as Hstres.
        { eapply fby_detn. 2-4:eauto.
          take (sem_transitions _ Hi2 _ _ _ _) and eapply sem_transitions_detn in it; eauto.
          simpl_Forall; eauto. }
        assert (Is_defined_in Γ cy (Bauto Weak ck (ini0, oth) states) -> EqStN (S n) stres1 stres2) as HSstres.
        { intros. eapply fby_det_Sn. 3-4:eauto. 2:auto.
          take (sem_transitions _ Hi2 _ _ _ _) and eapply sem_transitions_detS in it; eauto.
          - simpl_Forall; eauto.
          - intros. eapply HSn; eauto.
            eapply DepOnAuto3; eauto. solve_Exists.
        }
        assert (Forall (fun '((e, _), br) => forall k, exists Hi1' Hi2',
                            select_hist e k stres1 Hi1 Hi1' /\ select_hist e k stres2 Hi2 Hi2'
                            /\ (forall y, In y xs -> HasCaus Γ y cy -> det_var (S n) Hi1' Hi2' (Var y)) /\
                              sem_branch_det
                                (fun s =>
                                   sem_scope_det
                                     (fun Hi1 Hi2 blks => Forall (sem_block_det n (cy::envS) Hi1 Hi2 (fselectb e k stres1 bs1) (fselectb e k stres2 bs2)) (fst blks)
                                                       /\ sem_transitions G Hi1 (fselectb e k stres1 bs1) (snd blks) (e, false) (fselect absent e k stres1 stres11)
                                                       /\ sem_transitions G Hi2 (fselectb e k stres2 bs2) (snd blks) (e, false) (fselect absent e k stres2 stres12))
                                     n (cy :: envS) Hi1' Hi2' (fselectb e k stres1 bs1) (fselectb e k stres2 bs2) (snd s))
                                (fun x => Syn.Is_defined_in (Var x) (Bauto Weak ck (ini0, oth) states))
                                (fun x '(_, s) => Syn.Is_defined_in_scope (fun '(blks, _) => List.Exists (Syn.Is_defined_in (Var x)) blks) (Var x) s)
                                n (cy :: envS) Hi1' Hi2' br)
                       states) as Hf.
        { simpl_Forall. intros. take (forall (k : nat), _) and specialize (it k); destruct_conjs. destruct b as [?(?&[?(?&?)])].
          do 2 esplit; eauto. split; [|split]; eauto.
          eapply det_branch_cons; eauto.
          - eapply NoDup_locals_inv2; eauto.
          - intros *. eapply det_var_inv_select; eauto.
          - intros * Hdep. eapply det_var_inv_select; eauto.
            + eapply HSstres, depends_on_def. econstructor; solve_Exists; eauto.
            + eapply HSn; eauto. constructor. solve_Exists.
          - intros * Hin' Hdep. eapply HenvS; eauto.
            2:constructor; solve_Exists. solve_In.
          - intros; simpl in *; destruct_conjs.
            subst Γ0. eapply det_scope_cons in H31 as (?&?&?); eauto.
            + instantiate (1:=fun '(blks, _) => flat_map idcaus_of_locals blks). eauto.
            + rewrite map_fst_replace_idcaus; eauto.
            + apply incl_nil'.
            + eapply wt_scope_incl. 4:eauto.
              3:intros; destruct_conjs; split; simpl_Forall; eauto using wt_exp_incl, wt_block_incl.
              1,2:intros; (rewrite replace_idcaus_HasType||rewrite replace_idcaus_IsLast); auto.
            + eapply EqStN_fselect; eauto.
            + intros Hdef'. eapply EqStN_fselect; eauto.
              * eapply HSstres. econstructor; solve_Exists; econstructor; eauto.
              * eapply HSbs. econstructor; solve_Exists; econstructor; eauto.
            + intros * Hin' Hdep. eapply HenvS; eauto.
              2:constructor; solve_Exists; econstructor; eauto. solve_In.
              2:eauto with datatypes. auto.
            + intros; simpl in *. destruct_conjs.
              rewrite <-and_assoc.
              assert (Forall (fun blks =>
                                (forall y xs, VarsDefinedComp blks xs -> In y xs -> HasCaus Γ0 y cy -> det_var (S n) Hi0 Hi3 (Var y))
                                /\ (forall y xs, LastsDefined blks xs -> In y xs -> HasLastCaus Γ0 y cy -> det_var (S n) Hi0 Hi3 (Last y))
                                /\ sem_block_det n (cy::envS) Hi0 Hi3 (fselectb e k stres1 bs1) (fselectb e k stres2 bs2) blks) l2) as Hf.
              { simpl_Forall. inv_VarsDefined.
                edestruct H as (DetV&DetL&Sem). 9:eauto. all:eauto.
                - eapply NoDup_locals_inv; eauto.
                - etransitivity; eauto using incl_concat.
                  take (Permutation _ xs0) and now rewrite it.
                - etransitivity; eauto using incl_concat.
                  take (Permutation _ ls) and now rewrite it.
                - eapply EqStN_fselect; eauto.
                - intros Hdef'. eapply H45; eauto. solve_Exists.
                - intros * Hdep. eapply H46; eauto. solve_Exists.
                - intros * Hin' Hdep. eapply H47; eauto.
                  2:solve_Exists. solve_In.
                - split; [|split]; eauto.
                  + intros * Hdef' Hin' Hca. eapply DetV; eauto.
                    eapply VarsDefinedComp_det in Hdef0; eauto. now rewrite <-Hdef0.
                  + intros * Hdef' Hin' Hca. eapply DetL; eauto.
                    eapply LastsDefined_det in Hdef; eauto. now rewrite <-Hdef.
              }
              split; [|split]; auto; [|simpl_Forall; eauto].
              split.
              * intros * Hin Hca. take (Permutation _ xs0) and rewrite <-it in Hin. apply in_concat in Hin as (?&?&?).
                inv_VarsDefined; simpl_Forall; eauto.
              * intros * Hin Hca. take (Permutation _ ls) and rewrite <-it in Hin. apply in_concat in Hin as (?&?&?).
                inv_VarsDefined; simpl_Forall; eauto.
        } clear H H27.
        split; [|split].
        + intros * Hinxs Hca.
          eapply det_var_unselect with (tn:=length states) (sc1:=stres1); eauto.
          * destruct states; simpl in *; try congruence. lia.
          * eapply HSstres; eauto. eapply Is_defined_in_Is_defined_in; eauto.
            eapply VarsDefinedComp_Is_defined; eauto. econstructor; eauto.
            eapply NoDupLocals_incl; [|econstructor; eauto]. eauto.
          * take (sem_transitions _ Hi1 _ _ _ _) and eapply sem_automaton_wt_state1 in it; eauto. 1,3:simpl_Forall; eauto.
            -- repeat inv_branch. repeat inv_scope. simpl_Forall; auto.
            -- now take (Permutation _ _) and rewrite <-it, <-fst_InMembers.
            -- simpl_Forall. repeat inv_branch. repeat inv_scope. intros. specialize (Hf k); destruct_conjs.
               repeat inv_branch. repeat inv_scope. eauto.
          * take (sem_transitions _ Hi2 _ _ _ _) and eapply sem_automaton_wt_state1 in it; eauto. 1,3:simpl_Forall; eauto.
            -- repeat inv_branch. repeat inv_scope. simpl_Forall; auto.
            -- now take (Permutation _ _) and rewrite <-it, <-fst_InMembers.
            -- simpl_Forall. repeat inv_branch. repeat inv_scope. intros. specialize (Hf k); destruct_conjs.
               repeat inv_branch. repeat inv_scope. eauto.
          * intros * Hseq.
            assert (exists constr blks, In ((c, constr), blks) states) as (?&?&Hinbrs); destruct_conjs.
            { take (Permutation _ _) and rewrite <-it in Hseq. simpl_In; eauto. }
            simpl_Forall. specialize (Hf k); destruct_conjs.
            do 2 esplit. split; [|split; [|split]]; eauto.
            destruct x0 as [?(?&[?(?&?)])].
            split; eapply sem_branch_defined2 with (must_def:=fun x => Syn.Is_defined_in (Var x) _) (is_def:=fun x _ => Syn.Is_defined_in_scope _ (Var x) _); eauto.
            1,2:repeat inv_branch; repeat inv_scope; econstructor; eauto.
            1,2:econstructor; [|simpl_Forall; eauto using sem_block_det_sem_block1, sem_block_det_sem_block2]; eauto.
        + intros * [].
        + econstructor; eauto.
          simpl_Forall. specialize (Hf k); destruct_conjs. eauto.

      - (* automaton (strong) *)
        assert (EqStN n bs'1 bs'2) as Hbs' by (eapply sem_clock_detN; eauto with ltyping).
        assert (Is_defined_in Γ cy (Bauto Strong ck ([], oth) states) -> EqStN (S n) bs'1 bs'2) as HSbs'.
        { intros. eapply sem_clock_detN; eauto with ltyping.
          intros. eapply HSn; eauto with lcaus. }
        assert (EqStN n stres1 stres2) as Hstres.
        { eapply fby_detn. 2-4:eauto. eauto using const_stres_detn. }
        assert (Is_defined_in Γ cy (Bauto Strong ck ([], oth) states) -> EqStN (S n) stres1 stres2) as HSstres.
        { intros. eapply fby_det_Sn. 3-4:eauto. 2:auto.
          eauto using const_stres_detn. }
        assert (Is_defined_in Γ cy (Bauto Strong ck ([], oth) states) -> EqStN (S n) stres11 stres12) as HSstres1.
        { intros. eapply EqStN_unfselect with (tn:=length states); eauto.
          - destruct states; simpl in *; lia.
          - take (fby _ _ stres1) and eapply sem_automaton_wt_state2 with (states:=states) in it; eauto.
            + take (Permutation _ _) and rewrite <-it. now apply fst_InMembers.
            + simpl_Forall. repeat inv_branch. simpl_Forall; auto.
            + simpl_Forall. repeat inv_branch. intros. specialize (H22 k); destruct_conjs. repeat inv_branch. eauto.
          - take (fby _ _ stres2) and eapply sem_automaton_wt_state2 with (states:=states) in it; eauto.
            + take (Permutation _ _) and rewrite <-it. now apply fst_InMembers.
            + simpl_Forall. repeat inv_branch. simpl_Forall; auto.
            + simpl_Forall. repeat inv_branch. intros. specialize (H22 k); destruct_conjs. repeat inv_branch. eauto.
          - take (fby _ _ stres1) and (apply ac_fby2 in it; rewrite <-it). apply ac_slower.
          - take (fby _ _ stres2) and (apply ac_fby2 in it; rewrite <-it). apply ac_slower.
          - intros * Hsel. rewrite <-H12 in Hsel. simpl_In.
            simpl_Forall.
            specialize (H22 k); destruct_conjs. repeat inv_branch.
            take (sem_transitions _ x0 _ _ _ _) and eapply sem_transitions_detS in it; eauto using det_var_inv_select, det_var_inv_weaken.
            + simpl_Forall; eauto.
            + intros. eapply det_var_inv_select; eauto. eapply HSn; eauto.
              eapply DepOnAuto4; eauto. repeat solve_Exists.
            + apply EqStN_mask. 1,2:apply EqStN_fwhen; eauto using EqStN_weaken.
              1-3:apply map_EqStN; eauto using EqStN_weaken.
        }

        assert (Forall (fun '((e, _), br) => forall k, exists Hi1' Hi2',
                            select_hist e k stres11 Hi1 Hi1' /\ select_hist e k stres12 Hi2 Hi2'
                            /\ (forall y, In y xs -> HasCaus Γ y cy -> det_var (S n) Hi1' Hi2' (Var y))
                            /\ sem_branch_det
                                (fun s =>
                                   sem_scope_det
                                     (fun Hi1 Hi2 blks => Forall (sem_block_det n (cy::envS) Hi1 Hi2 (fselectb e k stres11 bs1) (fselectb e k stres12 bs2)) (fst blks))
                                     n (cy :: envS) Hi1' Hi2' (fselectb e k stres11 bs1) (fselectb e k stres12 bs2) (snd s))
                                (fun x => Syn.Is_defined_in (Var x) (Bauto Strong ck ([], oth) states))
                                (fun x '(_, s) => Syn.Is_defined_in_scope (fun '(blks, _) => List.Exists (Syn.Is_defined_in (Var x)) blks) (Var x) s)
                                n (cy :: envS) Hi1' Hi2' br)
                       states) as Hf.
        { simpl_Forall. intros. specialize (H24 k); destruct_conjs. destruct b as [?(?&[?(?&?)])].
          do 2 esplit; eauto. split; [|split]; eauto.
          eapply det_branch_cons; eauto.
          - eapply NoDup_locals_inv2; eauto.
          - intros *. eapply det_var_inv_select with (sc1:=stres11); eauto.
          - intros * Hdep. eapply det_var_inv_select; eauto.
            + eapply HSstres1, depends_on_def. econstructor; solve_Exists; eauto.
            + eapply HSn; eauto. constructor. solve_Exists.
          - intros * Hin' Hdep. eapply HenvS; eauto.
            2:constructor; solve_Exists. solve_In.
          - intros; simpl in *. destruct_conjs.
            subst Γ0. eapply det_scope_cons in H29 as (DetV&DetL&Sem); eauto.
            + instantiate (1:=fun '(blks, _) => flat_map idcaus_of_locals blks). eauto.
            + rewrite map_fst_replace_idcaus; eauto.
            + apply incl_nil'.
            + eapply wt_scope_incl. 4:eauto.
              3:intros; destruct_conjs; split; simpl_Forall; eauto using wt_exp_incl, wt_block_incl.
              1,2:intros; (rewrite replace_idcaus_HasType||rewrite replace_idcaus_IsLast); auto.
            + eapply EqStN_fselect; eauto.
            + intros Hdef'. eapply EqStN_fselect; eauto.
              * eapply HSstres1. econstructor; solve_Exists; econstructor; eauto.
              * eapply HSbs. econstructor; solve_Exists; econstructor; eauto.
            + intros * Hin' Hdep. eapply HenvS; eauto.
              2:constructor; solve_Exists; econstructor; eauto. solve_In.
              2:eauto with datatypes. auto.
            + intros; simpl in *; destruct_conjs.
              assert (Forall (fun blks =>
                                (forall y xs, VarsDefinedComp blks xs -> In y xs -> HasCaus Γ0 y cy -> det_var (S n) Hi0 Hi3 (Var y))
                                /\ (forall y xs, LastsDefined blks xs -> In y xs -> HasLastCaus Γ0 y cy -> det_var (S n) Hi0 Hi3 (Last y))
                                /\ sem_block_det n (cy::envS) Hi0 Hi3 (fselectb e k stres11 bs1) (fselectb e k stres12 bs2) blks) l2) as Hf.
              { simpl_Forall. inv_VarsDefined.
                edestruct H as (DetV&DetL&Sem). 9:eauto. all:eauto.
                - eapply NoDup_locals_inv; eauto.
                - etransitivity; eauto using incl_concat.
                  take (Permutation _ xs0) and now rewrite it.
                - etransitivity; eauto using incl_concat.
                  take (Permutation _ ls) and now rewrite it.
                - eapply EqStN_fselect; eauto.
                - intros Hdef'. eapply H43; eauto. solve_Exists.
                - intros * Hdep. eapply H44; eauto. solve_Exists.
                - intros * Hin' Hdep. eapply H45; eauto.
                  2:solve_Exists. solve_In.
                - split; [|split]; eauto.
                  + intros * Hdef' Hin' Hca. eapply DetV; eauto.
                    eapply VarsDefinedComp_det in Hdef0; eauto. now rewrite <-Hdef0.
                  + intros * Hdef' Hin' Hca. eapply DetL; eauto.
                    eapply LastsDefined_det in Hdef; eauto. now rewrite <-Hdef.
              }
              split; [|split]; simpl_Forall; eauto.
              * intros * Hin Hca. take (Permutation _ xs0) and rewrite <-it in Hin. apply in_concat in Hin as (?&?&?).
                inv_VarsDefined; simpl_Forall; eauto.
              * intros * Hin Hca. take (Permutation _ ls) and rewrite <-it in Hin. apply in_concat in Hin as (?&?&?).
                inv_VarsDefined; simpl_Forall; eauto.
        } clear H H24.
        assert ((forall y, In y xs -> HasCaus Γ y cy -> det_var (S n) Hi1 Hi2 (Var y))) as Hdet.
        { intros * Hinxs Hca.
          eapply det_var_unselect with (tn:=length states) (sc1:=stres11); eauto.
          - destruct states; simpl in *; try congruence. lia.
          - eapply HSstres1; eauto. eapply Is_defined_in_Is_defined_in; eauto.
            eapply VarsDefinedComp_Is_defined; eauto. econstructor; eauto.
            eapply NoDupLocals_incl; [|econstructor; eauto]. eauto.
          - take (fby _ _ stres1) and eapply sem_automaton_wt_state3 in it; eauto. 2,3:simpl_Forall; eauto.
            + now take (Permutation _ _) and rewrite <-it, <-fst_InMembers.
            + repeat inv_branch. simpl_Forall; eauto.
            + simpl_Forall. repeat inv_branch. repeat inv_scope. intros. specialize (H22 k); destruct_conjs.
              repeat inv_branch. repeat inv_scope. eauto.
          - take (fby _ _ stres2) and eapply sem_automaton_wt_state3 in it; eauto. 2,3:simpl_Forall; eauto.
            + now take (Permutation _ _) and rewrite <-it, <-fst_InMembers.
            + repeat inv_branch. simpl_Forall; eauto.
            + simpl_Forall. repeat inv_branch. repeat inv_scope. intros. specialize (H22 k); destruct_conjs.
              repeat inv_branch. repeat inv_scope. eauto.
          - intros * Hseq. take (Permutation _ _) and rewrite <-it in Hseq. simpl_In.
            simpl_Forall. specialize (Hf k); destruct_conjs.
            do 2 esplit. split; [|split; [|split]]; eauto.
            destruct b as [?(?&[?(?&?)])].
            split; eapply sem_branch_defined2 with (must_def:=fun x => Syn.Is_defined_in (Var x) _) (is_def:=fun x _ => Syn.Is_defined_in_scope _ (Var x) _); eauto.
            1,2:repeat inv_branch; repeat inv_scope; econstructor; eauto.
            1,2:econstructor; [|simpl_Forall; eauto using sem_block_det_sem_block1, sem_block_det_sem_block2]; eauto.
        }
        split; [|split]; auto.
        + intros * [].
        + econstructor; eauto; simpl_Forall.
          specialize (Hf k); destruct_conjs; eauto.

      - (* locals *)
        eapply det_scope_cons in H9 as (DetV&DetL&Sem); eauto.
        + split; [|split]; eauto. econstructor; eauto.
        + intros; eauto with lcaus.
        + intros. eapply HSn; eauto. econstructor; eauto.
        + intros. eapply HenvS; eauto. econstructor; eauto.
        + intros; simpl in *.
          assert (Forall (fun blks =>
                            (forall y xs, VarsDefinedComp blks xs -> In y xs -> HasCaus Γ0 y cy -> det_var (S n) Hi0 Hi3 (Var y))
                            /\ (forall y xs, LastsDefined blks xs -> In y xs -> HasLastCaus Γ0 y cy -> det_var (S n) Hi0 Hi3 (Last y))
                            /\ sem_block_det n (cy::envS) Hi0 Hi3 bs1 bs2 blks) blocks) as Hf.
            { simpl_Forall. inv_VarsDefined.
              edestruct H with (xs:=xs2) (ls:=xs1) as (DetV&DetL&Sem). 11:eauto. all:eauto.
              - eapply NoDup_locals_inv; eauto.
              - etransitivity; eauto using incl_concat.
                take (Permutation (concat x1) _) and now rewrite it.
              - etransitivity; eauto using incl_concat.
                take (Permutation (concat x0) _) and now rewrite it.
              - intros Hdef'. eapply H15; eauto. solve_Exists.
              - intros * Hdep. eapply H16; eauto. solve_Exists.
              - intros * Hin' Hdep. eapply H17; eauto.
                2:solve_Exists. solve_In.
              - split; [|split]; eauto.
                + intros * Hdef' Hin' Hca. eapply DetV; eauto.
                  eapply VarsDefinedComp_det in Hdef0; eauto. now rewrite <-Hdef0.
                + intros * Hdef' Hin' Hca. eapply DetL; eauto.
                  eapply LastsDefined_det in Hdef; eauto. now rewrite <-Hdef.
            }
            split; [|split]; simpl_Forall; eauto.
            * intros * Hin Hca. destruct_conjs. take (Permutation _ xs0) and rewrite <-it in Hin. apply in_concat in Hin as (?&?&?).
              inv_VarsDefined; simpl_Forall; eauto.
            * intros * Hin Hca. destruct_conjs. take (Permutation _ ls0) and rewrite <-it in Hin. apply in_concat in Hin as (?&?&?).
              inv_VarsDefined; simpl_Forall; eauto.
    Qed.

    Lemma det_vars_n : forall nd n Hi1 Hi2 bs1 bs2,
        det_nodes G ->
        wt_node G nd ->
        node_causal nd ->
        let Γ := senv_of_ins (n_in nd) ++ senv_of_decls (n_out nd) in
        let caus := idcaus (n_in nd) ++ idcaus_of_decls (n_out nd) in
        Forall (fun x => det_var (S n) Hi1 Hi2 (Var x)) (map fst (n_in nd)) ->
        EqStN (S n) bs1 bs2 ->
        (forall x, det_var_inv Γ n Hi1 Hi2 x) ->
        sem_block_det n [] Hi1 Hi2 bs1 bs2 (n_block nd) ->
        Forall (fun x => det_var_inv Γ (S n) Hi1 Hi2 x) (map snd (caus ++ idcaus_of_locals (n_block nd)))
        /\ sem_block_det n (map snd (caus ++ idcaus_of_locals (n_block nd))) Hi1 Hi2 bs1 bs2 (n_block nd).
    Proof.
      intros * HdetG Hwtn Hcaus Γ caus Hins Hbs Hn Hblk; subst Γ caus; rewrite <-app_assoc in *.

      eapply node_causal_ind; eauto.
      - intros ?? Hperm (Hblk'&Hvars'). split.
        + rewrite <-Hperm; auto.
        + eapply sem_block_det_Perm; eauto.
      - intros * Hin (HSn&Hblk') Hdep.
        pose proof (n_syn nd) as Syn. inversion_clear Syn as [??? Hdef Hperm].
        pose proof (n_lastd nd) as (?&Hlast&Hperml).
        destruct Hcaus as (Hnd&_).
        eapply det_block_cons in Hblk' as (Hdet&Hdetl&Hsem);
          eauto using EqStN_weaken, node_NoDupLocals, node_NoDupMembers.
        2:now rewrite idcaus_of_senv_app, idcaus_of_senv_ins, <-app_assoc.
        2:{ rewrite Hperm, map_app, map_fst_senv_of_decls. solve_incl_app. }
        2:{ rewrite Hperml, map_app, map_fst_senv_of_decls.
            eauto using incl_appr, lasts_of_decls_incl. }
        2:now inv Hwtn.
        2:{ intros * Dep.
            eapply Forall_forall in HSn; eauto.
            eapply Hdep. constructor; eauto. }
        2:{ intros. eapply Hdep. econstructor; eauto. }
        split; eauto. constructor; auto.
        split; intros * Hc; rewrite ?HasCaus_app, ?HasLastCaus_app in Hc; destruct Hc as [Hc|Hc].
        + inv Hc. eapply Forall_forall in Hins; eauto. solve_In.
        + eapply Hdet; eauto. 2:apply HasCaus_app; eauto.
          rewrite Hperm. inv Hc. solve_In.
        + inv Hc. simpl_In. congruence.
        + eapply Hdetl; eauto. 2:apply HasLastCaus_app; auto.
          rewrite Hperml. inv Hc. unfold lasts_of_decls. solve_In.
    Qed.

    Lemma det_vars :
      forall nd n Hi1 Hi2 bs1 bs2,
        det_nodes G ->
        wt_node G nd ->
        node_causal nd ->
        EqStN n bs1 bs2 ->
        sem_block G Hi1 bs1 (n_block nd) ->
        sem_block G Hi2 bs2 (n_block nd) ->
        Forall (fun x => det_var n Hi1 Hi2 (Var x)) (map fst (n_in nd)) ->
        Forall (det_var_inv (senv_of_ins (n_in nd) ++ senv_of_decls (n_out nd)) n Hi1 Hi2) (map snd (idcaus (n_in nd) ++ idcaus_of_decls (n_out nd))).
    Proof.
      intros * HdetG Hwtn Hcaus Hbs Hsem1 Hsem2 Hins.

      assert (Forall (fun x => det_var_inv (senv_of_ins (n_in nd) ++ senv_of_decls (n_out nd)) n Hi1 Hi2 x)
                     (map snd (idcaus (n_in nd) ++ idcaus_of_decls (n_out nd) ++ idcaus_of_locals (n_block nd)))
              /\ sem_block_det n [] Hi1 Hi2 bs1 bs2 (n_block nd)) as (Hvars&_).
      2:{ eapply Forall_impl_In; [|eapply Forall_incl; [eapply Hvars|]]; eauto.
          repeat rewrite idcaus_app. solve_incl_app. }

      induction n.
      - (* everyone is equal up to 0 anyway *)
        split.
        + eapply Forall_forall. intros. split; intros; constructor.
        + eapply sem_block_det_0; eauto.

      - (* use the causal induction to step once *)
        clear Hsem1 Hsem2.
        destruct IHn as (Hvars&Hblk); eauto using EqStN_weaken.
        { simpl_Forall. intros ????. eapply EqStN_weaken; eauto. }
        eapply det_vars_n in Hblk as (Hvars'&Hblk'); eauto. rewrite <-app_assoc in *.
        split; auto.
        + inv Hwtn. subst Γ.
          pose proof (n_nodup nd) as (_&Hnd2).
          eapply det_block_S; eauto.
          * apply node_NoDupLocals.
          * intros *.
            split; intros * Hca.
            1,2:eapply Forall_forall in Hvars'; try eapply Hvars'; eauto.
            1,2:rewrite app_assoc, map_app, in_app_iff; left.
            1,2:unfold idcaus_of_decls; rewrite <-idcaus_of_senv_ins, <-idcaus_of_senv_app.
            1,2:eapply in_map_iff; do 2 esplit; [|eapply idcaus_of_senv_In]; eauto; auto.
          * solve_incl_app.
        + intros *.
          split; intros * Hca.
          1,2:eapply Forall_forall in Hvars; try eapply Hvars; eauto.
          1,2:rewrite app_assoc, map_app, in_app_iff; left.
          1,2:unfold idcaus_of_decls; rewrite <-idcaus_of_senv_ins, <-idcaus_of_senv_app.
          1,2:eapply in_map_iff; do 2 esplit; [|eapply idcaus_of_senv_In]; eauto; auto.
    Qed.

  End sem_block_det.


  Lemma det_global_n {prefs} : forall (G : @global complete prefs),
      wt_global G ->
      Forall node_causal (nodes G) ->
      det_nodes G.
  Proof.
    intros [].
    induction nodes0 as [|nd nds]; intros Hwt Hcaus ?????? Heqins Hs1 Hs2;
      inv Hcaus. now inv Hs1.
    inversion_clear Hs1 as [????? Hfind1 Hins1 Houts1 bs1 Hblk1].
    inversion_clear Hs2 as [????? Hfind2 Hins2 Houts2 bs2 Hblk2].
    rewrite Hfind1 in Hfind2. inv Hfind2.
    destruct (ident_eq_dec (n_name nd) f); subst.
    - assert (Hfind2:=Hfind1). rewrite find_node_now in Hfind2; auto; inv Hfind2.
      assert (~ Is_node_in (n_name n1) n1) as Hnin.
      { eapply find_node_not_Is_node_in; eauto using wl_global_Ordered_nodes with ltyping. }
      eapply sem_block_cons1 in Hblk1; eauto using wl_global_Ordered_nodes with ltyping.
      eapply sem_block_cons1 in Hblk2; eauto using wl_global_Ordered_nodes with ltyping.

      assert (Forall (fun x => det_var n H H0 (Var x)) (map fst (n_in n1))) as Hins.
      { eapply node_causal_NoDup in H1 as Hnd.
        clear - Heqins Hins1 Hins2 Hnd.
        simpl_Forall. simpl_In. intros ?? Hv1 Hv2.
        eapply Forall2_trans_ex in Heqins; [|eauto]. simpl_Forall.
        eapply Forall2_ignore2 in Heqins. simpl_Forall.
        eapply sem_var_det in Hv1; [|eauto]. eapply sem_var_det in Hv2; [|eauto]. now rewrite <-Hv1, <-Hv2.
      }
      eapply det_vars in Hins; eauto.
      + eapply Forall2_trans_ex in Houts2; [|eapply Forall2_swap_args, Houts1].
        eapply Forall2_impl_In; [|eauto]; intros ?? _ _ (?&Hin&Hv1&Hv2). simpl_In.
        unfold idcaus in Hins. simpl_Forall. repeat apply Forall_app in Hins as (?&Hins).
        unfold senv_of_decls in H4. simpl_Forall. eapply H4 in Hv2; eauto; simpl in *.
        apply HasCaus_app, or_intror. econstructor. solve_In. auto.
      + inv Hwt; inv H4. eapply IHnds; eauto. split; eauto.
      + inv Hwt; inv H4. destruct H7; auto.
      + eapply clocks_of_EqStN; eauto.
    - rewrite find_node_other in Hfind1; auto.
      assert (~ Is_node_in (n_name nd) n1) as Hnin.
      { eapply find_node_later_not_Is_node_in; eauto using wl_global_Ordered_nodes with ltyping. }
      eapply sem_block_cons1 in Hblk1; eauto using wl_global_Ordered_nodes with ltyping.
      eapply sem_block_cons1 in Hblk2; eauto using wl_global_Ordered_nodes with ltyping.
      eapply IHnds; eauto. inv Hwt; inv H4; split; auto.
      1,2:econstructor; eauto.
  Qed.

  Theorem det_global {prefs} : forall (G: @global complete prefs) f ins outs1 outs2,
      wt_global G ->
      Forall node_causal (nodes G) ->
      sem_node G f ins outs1 ->
      sem_node G f ins outs2 ->
      EqSts outs1 outs2.
  Proof.
    intros * Hwt Hcaus Hsem1 Hsem2.
    eapply det_nodes_ins; eauto.
    eapply det_global_n; eauto.
  Qed.

End LSEMDETERMINISM.

Module LSemDeterminismFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks   : CLOCKS        Ids Op OpAux)
       (Senv  : STATICENV     Ids Op OpAux Cks)
       (Syn   : LSYNTAX Ids Op OpAux Cks Senv)
       (Typ   : LTYPING Ids Op OpAux Cks Senv Syn)
       (LCA   : LCAUSALITY Ids Op OpAux Cks Senv Syn)
       (Lord  : LORDERED Ids Op OpAux Cks Senv Syn)
       (CStr  : COINDSTREAMS Ids Op OpAux Cks)
       (Sem   : LSEMANTICS Ids Op OpAux Cks Senv Syn Lord CStr)
<: LSEMDETERMINISM Ids Op OpAux Cks Senv Syn Typ LCA Lord CStr Sem.
  Include LSEMDETERMINISM Ids Op OpAux Cks Senv Syn Typ LCA Lord CStr Sem.
End LSemDeterminismFun.
