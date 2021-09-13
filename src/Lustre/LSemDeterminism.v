From Coq Require Import String.
From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Velus Require Import Common.
From Velus Require Import CommonList.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import CoindStreams.
From Velus Require Import Clocks.
From Velus Require Import Lustre.LSyntax Lustre.LCausality Lustre.LOrdered Lustre.LSemantics.

(** ** Proof of the determinism of the coinductive semantics
    We can proove that the semantics of a causal program are deterministic:
    That is, a node always return the same output for a given input.
 *)
Module Type LSEMDETERMINISM
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks   : CLOCKS        Ids Op OpAux)
       (Import Syn   : LSYNTAX Ids Op OpAux Cks)
       (Import LCA   : LCAUSALITY Ids Op OpAux Cks Syn)
       (Import Lord  : LORDERED Ids Op OpAux Cks Syn)
       (Import CStr  : COINDSTREAMS Ids Op OpAux Cks)
       (Import Sem   : LSEMANTICS Ids Op OpAux Cks Syn Lord CStr).

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

  Section sem_equation_det.
    Context {PSyn : block -> Prop}.
    Context {prefs : PS.t}.
    Variable (G : @global PSyn prefs).

    Hypothesis HdetG : det_nodes G.

    Variable env : list (ident * ident).

    Definition det_var_inv n (H1 H2 : history) : ident -> Prop :=
      fun cx => forall x vs1 vs2,
          In (x, cx) env ->
          sem_var H1 x vs1 ->
          sem_var H2 x vs2 ->
          EqStN n vs1 vs2.

    Definition def_stream := Streams.const absent.

    Definition det_exp_inv n H1 H2 bs1 bs2 : exp -> nat -> Prop :=
      fun e k => forall ss1 ss2,
          wl_exp G e ->
          wx_exp (map fst env) e ->
          sem_exp G H1 bs1 e ss1 ->
          sem_exp G H2 bs2 e ss2 ->
          EqStN n (nth k ss1 def_stream) (nth k ss2 def_stream).

    Lemma P_exps_det_exp_inv : forall n H1 H2 bs1 bs2 es k ss1 ss2,
        Forall (wl_exp G) es ->
        Forall (wx_exp (map fst env)) es ->
        P_exps (det_exp_inv n H1 H2 bs1 bs2) es k ->
        Forall2 (sem_exp G H1 bs1) es ss1 ->
        Forall2 (sem_exp G H2 bs2) es ss2 ->
        EqStN n (nth k (concat ss1) def_stream) (nth k (concat ss2) def_stream).
    Proof.
      induction es; intros * Hwl Hwx Hp Hsem1 Hsem2;
        inv Hwl; inv Hwx; inv Hsem1; inv Hsem2; simpl. inv Hp.
      assert (length y = numstreams a) as Hlen1 by (eapply sem_exp_numstreams; eauto).
      assert (length y0 = numstreams a) as Hlen2 by (eapply sem_exp_numstreams; eauto).
      inv Hp.
      - (* now *)
        rewrite 2 app_nth1; try congruence.
        eapply H13; eauto.
      - (* later *)
        rewrite 2 app_nth2; try congruence.
        rewrite Hlen2, Hlen1.
        eapply IHes; eauto.
    Qed.

    Lemma P_exps_det_exp_inv_all : forall n H1 H2 bs1 bs2 es ss1 ss2,
        Forall (wl_exp G) es ->
        Forall (wx_exp (map fst env)) es ->
        (forall k, k < length (annots es) -> P_exps (det_exp_inv n H1 H2 bs1 bs2) es k) ->
        Forall2 (sem_exp G H1 bs1) es ss1 ->
        Forall2 (sem_exp G H2 bs2) es ss2 ->
        Forall2 (EqStN n) (concat ss1) (concat ss2).
    Proof.
      intros * Hwl Hwx Hk Hsem1 Hsem2.
      assert (length (concat ss1) = length (annots es)) as Hlen1.
      { eapply sem_exps_numstreams; eauto. }
      assert (length (concat ss2) = length (annots es)) as Hlen2.
      { eapply sem_exps_numstreams; eauto. }
      eapply Forall2_forall2; split. congruence.
      intros * Hn ? ?; subst.
      erewrite nth_indep with (d:=a) (d':=def_stream); auto.
      erewrite nth_indep with (d:=b) (d':=def_stream); try congruence.
      eapply P_exps_det_exp_inv; eauto.
      eapply Hk. congruence.
    Qed.

    Lemma EqSts_mask : forall k r ss1 ss2,
        EqSts ss1 ss2 ->
        EqSts (map (maskv k r) ss1) (map (maskv k r) ss2).
    Proof.
      unfold EqSts.
      intros * Heq.
      rewrite Forall2_map_1, Forall2_map_2.
      eapply Forall2_impl_In; [|eauto]; intros ?? _ _ Hab.
      now rewrite Hab.
    Qed.

    Lemma EqSts_unmask : forall r ss1 ss2,
        (forall k, EqSts (map (maskv k r) ss1) (map (maskv k r) ss2)) ->
        EqSts ss1 ss2.
    Proof.
      intros * Heq.
      assert (length ss1 = length ss2) as Hlen.
      { specialize (Heq 0). eapply Forall2_length in Heq.
        now repeat rewrite map_length in Heq. }
      eapply Forall2_forall2. split; auto; intros ????? Hl ??; subst.
      eapply EqSt_unmask. intros.
      specialize (Heq k). eapply Forall2_forall2 in Heq as (_&Heq).
      eapply Heq; eauto.
      rewrite map_length; eauto.
      1,2:rewrite map_nth; reflexivity.
    Qed.

    (** We first establish the determinism of all the coinductive operators,
        as well as the expression semantics.
        We show that they are deterministic "up-to-n" : that is they preserve
        the equality "up-to-n".
        Proving this for any n is stronger than just proving that they output the
        same stream for the same input, as we can use `EqStN_EqSt` to rewrite
        the conclusion and hypotheses.
    *)

    Hint Constructors EqStN.

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

    Corollary fby_detn : forall n xs1 xs2 ys1 ys2 zs1 zs2,
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
        EqStN n cs1 cs2 ->
        Forall2 (EqStN n) xss1 xss2 ->
        merge cs1 xss1 ys1 ->
        merge cs2 xss2 ys2 ->
        EqStN n ys1 ys2.
    Proof.
      induction n; intros * Heq1 Heq2 Hmerge1 Hmerge2; inv Heq1; auto.
      inv Hmerge1; inv Hmerge2; constructor; eauto.
      1,3:eapply IHn; [eauto| |eauto|eauto].
      1,2:(rewrite Forall2_map_1, Forall2_map_2; eapply Forall2_impl_In; [|eauto];
           intros ?? _ _ Heq; inv Heq; auto).
      clear - Heq2 H3 H5 H6. unfold EqSts in *.
      eapply Forall2_trans_ex in Heq2; [|eapply Forall2_swap_args, H3].
      eapply Forall2_swap_args in Heq2. eapply Forall2_trans_ex in Heq2; [|eapply Forall2_swap_args, H5].
      eapply Forall2_app_split in Heq2 as (_&Heq2); eauto.
      inv Heq2. destruct H2 as (?&_&Heq1&?&_&Heq2&Heqn).
      rewrite Heq1, Heq2 in Heqn. inv Heqn; auto.
    Qed.

    Lemma case_detn : forall n cs1 cs2 xss1 xss2 ys1 ys2,
        EqStN n cs1 cs2 ->
        Forall2 (EqStN n) xss1 xss2 ->
        case cs1 xss1 ys1 ->
        case cs2 xss2 ys2 ->
        EqStN n ys1 ys2.
    Proof.
      induction n; intros * Heq1 Heq2 Hmerge1 Hmerge2; inv Heq1; auto.
      inv Hmerge1; inv Hmerge2; constructor; eauto.
      1,3:eapply IHn; [eauto| |eauto|eauto].
      1,2:(rewrite Forall2_map_1, Forall2_map_2; eapply Forall2_impl_In; [|eauto];
           intros ?? _ _ Heq; inv Heq; auto).
      clear - Heq2 H6 H9. inv H6. inv H9.
      repeat rewrite_Forall_forall.
      assert (c < length xss1) as Hlen.
      { eapply nth_error_Some; eauto. congruence. }
      specialize (H4 def_stream def_stream _ _ _ Hlen eq_refl eq_refl).
      eapply eq_sym, nth_error_nth in H. eapply eq_sym, nth_error_nth in H0.
      rewrite H, H0, H1, H3 in H4. now inv H4.
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
                    wl_exp G e ->
                    wx_exp (map fst env) e ->
                    sem_exp G Hi1 bs1 e ss1 ->
                    sem_exp G Hi2 bs2 e ss2 ->
                    Forall2 (EqStN n) ss1 ss2) es ->
        Forall (wl_exp G) es ->
        Forall (wx_exp (map fst env)) es ->
        Forall2 (sem_exp G Hi1 bs1) es ss1 ->
        Forall2 (sem_exp G Hi2 bs2) es ss2 ->
        Forall2 (EqStN n) (concat ss1) (concat ss2).
    Proof.
      intros * Hf. revert ss1 ss2.
      induction Hf; intros * Hwl Hwx Hsem1 Hsem2;
        inv Hwl; inv Hwx; inv Hsem1; inv Hsem2; simpl; auto.
      apply Forall2_app; eauto.
    Qed.

    (** The clocking hypothesis could be replaced with a typing one.
        The important point is that all the variables appearing in the expression
        are in `env`.
        I chose a clocking hypothesis because this lemma is used in the
        clocked-semantics proof. *)
    Lemma det_exp_n : forall n Hi1 Hi2 bs1 bs2 e ss1 ss2,
        (forall x, In x (map snd env) -> det_var_inv n Hi1 Hi2 x) ->
        EqStN n bs1 bs2 ->
        wl_exp G e ->
        wx_exp (map fst env) e ->
        sem_exp G Hi1 bs1 e ss1 ->
        sem_exp G Hi2 bs2 e ss2 ->
        Forall2 (EqStN n) ss1 ss2.
    Proof.
      intros * Hn Hbs. revert ss1 ss2.
      induction e using exp_ind2; intros * Hwl Hwx Hs1 Hs2.
      - (* const *)
        inv Hs1. inv Hs2.
        constructor; auto.
        rewrite H3, H4. eapply const_detn; eauto.
      - (* enum *)
        inv Hs1. inv Hs2.
        constructor; auto.
        rewrite H5, H6. eapply enum_detn; eauto.
      - (* var *)
        inv Hs1. inv Hs2.
        constructor; auto.
        inv Hwx; eauto. eapply in_map_iff in H0 as ((id&cx)&?&?); subst.
        eapply Hn; eauto. eapply in_map_iff. exists (id, cx); eauto.
      - (* unop *)
        inv Hwl. inv Hwx.
        inversion_clear Hs1 as [| | |???????? Hse1 Hty1 Hl1| | | | | | |].
        inversion_clear Hs2 as [| | |???????? Hse2 Hty2 Hl2| | | | | | |].
        rewrite Hty2 in Hty1; inv Hty1.
        eapply IHe in Hse1; eauto. inv Hse1.
        constructor; auto.
        eapply lift1_detn; eauto.
      - (* binop *)
        inv Hwl. inv Hwx.
        inversion_clear Hs1 as [| | | |??????????? Hse11 Hse12 Hty11 Hty12 Hl1| | | | | |].
        inversion_clear Hs2 as [| | | |??????????? Hse21 Hse22 Hty21 Hty22 Hl2| | | | | |].
        rewrite Hty21 in Hty11; inv Hty11. rewrite Hty22 in Hty12; inv Hty12.
        eapply IHe1 in Hse21; eauto. eapply IHe2 in Hse22; eauto.
        inv Hse21. inv Hse22.
        constructor; auto.
        eapply lift2_detn. 3,4:eauto. 1,2:eauto.
      - (* fby *)
        inv Hwl. inv Hwx.
        inversion_clear Hs1 as [| | | | |???????? Hse11 Hse12 Hfby1| | | | |].
        inversion_clear Hs2 as [| | | | |???????? Hse21 Hse22 Hfby2| | | | |].
        eapply det_exps_n' in H; eauto.
        eapply det_exps_n' in H0; eauto.
        clear - H H0 Hfby1 Hfby2.
        repeat rewrite_Forall_forall. congruence.
        eapply fby_detn.
        + eapply H2 with (a:=def_stream) (b:=def_stream) (n0:=n0); eauto. congruence.
        + eapply H1 with (a:=def_stream) (b:=def_stream) (n0:=n0); eauto. congruence.
        + eapply H8; eauto; congruence.
        + eapply H5; eauto; congruence.
      - (* arrow *)
        inv Hwl. inv Hwx.
        inversion_clear Hs1 as [| | | | | |???????? Hse11 Hse12 Harrow1| | | |].
        inversion_clear Hs2 as [| | | | | |???????? Hse21 Hse22 Harrow2| | | |].
        eapply det_exps_n' in H; eauto.
        eapply det_exps_n' in H0; eauto.
        clear - H H0 Harrow1 Harrow2.
        repeat rewrite_Forall_forall. congruence.
        eapply arrow_detn.
        + eapply H2 with (a:=def_stream) (b:=def_stream) (n0:=n0); eauto. congruence.
        + eapply H1 with (a:=def_stream) (b:=def_stream) (n0:=n0); eauto. congruence.
        + eapply H8; eauto; congruence.
        + eapply H5; eauto; congruence.
      - (* when *)
        inv Hwl. inv Hwx. eapply in_map_iff in H2 as ((id&cx)&?&?); subst.
        inversion_clear Hs1 as [| | | | | | |????????? Hse1 Hsv1 Hwhen1| | |].
        inversion_clear Hs2 as [| | | | | | |????????? Hse2 Hsv2 Hwhen2| | |].
        eapply det_exps_n' in H; eauto.
        eapply Hn in Hsv1; eauto using In_InMembers. 2:eapply in_map_iff; exists (id, cx); eauto.
        specialize (Hsv1 Hsv2).
        clear - H Hsv1 Hwhen1 Hwhen2.
        repeat rewrite_Forall_forall. congruence.
        eapply when_detn. 2:eauto.
        + eapply H0 with (a:=def_stream) (b:=def_stream) (n0:=n0); eauto. congruence.
        + eapply H4; eauto; congruence.
        + eapply H2; eauto; congruence.
      - (* merge *)
        inv Hwl. inv Hwx. eapply in_map_iff in H2 as ((id&cx)&?&?); subst.
        inversion_clear Hs1 as [| | | | | | | |????????? Hsv1 Hse1 Hmerge1| |].
        inversion_clear Hs2 as [| | | | | | | |????????? Hsv2 Hse2 Hmerge2| |].
        eapply Hn in Hsv1; eauto using In_InMembers. 2:eapply in_map_iff; exists (id, cx); eauto.
        specialize (Hsv1 Hsv2).
        assert (Forall2 (Forall2 (EqStN n)) (map (@concat _) vs) (map (@concat _) vs0)) as Heq.
        { clear - H H5 H8 Hse1 Hse2.
          revert vs vs0 Hse1 Hse2.
          induction H; intros * Hse1 Hse2; inv H5; inv H8; inv Hse1; inv Hse2; constructor; eauto.
          eapply det_exps_n' in H; eauto.
        }
        assert ((map (@concat _) vs) <> []) as Hnnil.
        { inv Hse1; simpl; congruence. }
        clear - Hsv1 Heq Hmerge1 Hmerge2 Hnnil.
        revert Hnnil Hmerge1 Hmerge2 Heq.
        generalize (map (@concat _) vs0). generalize (map (@concat _) vs). clear vs vs0.
        intros vs1 vs2 Hnnil Hmerge1. revert vs2 ss2.
        induction Hmerge1; intros * Hmerge2 Heq.
        + inv H; try congruence. inv Heq; try congruence. inv H2.
          inv Hmerge2; auto. inv H; simpl in *; congruence.
        + inv Hmerge2.
          { exfalso. clear IHHmerge1 Hmerge1. inv H; try congruence.
            inv Heq. inv H1. inv H5. simpl in *; congruence. }
          econstructor.
          * eapply merge_detn. 3,4:eauto. 1,2:eauto.
            clear - H H1 Heq.
            revert hd1 hd0 H H1.
            induction Heq; intros * H1 H2; inv H1; inv H2; constructor; auto.
            inv H; simpl in *; inv H4; inv H3; auto.
          * eapply IHHmerge1; eauto.
            destruct l1; simpl in *; congruence.
            clear - Heq.
            induction Heq; simpl; constructor; eauto. inv H; simpl; auto.
      - (* case *)
        inv Hwl. inv Hwx.
        inversion_clear Hs1 as [| | | | | | | | |?????????? Hsv1 Hsome1 Hnone1 Hd1 Hcase1|].
        inversion_clear Hs2 as [| | | | | | | | |?????????? Hsv2 Hsome2 Hnone2 Hd2 Hcase2|].
        eapply IHe in Hsv2; eauto. apply Forall2_singl in Hsv2.
        assert (Forall2 (Forall2 (EqStN n)) (map (@concat _) vs) (map (@concat _) vs0)) as Heq.
        { clear - H H0 H9 H14 H11 H15 Hsome1 Hsome2 Hnone1 Hnone2 Hd1 Hd2.
          revert vs vs0 Hsome1 Hsome2 Hnone1 Hnone2.
          induction H; intros * Hsome1 Hsome2 Hnone1 Hnone2;
            inv Hsome1; inv Hsome2; inv Hnone1; inv Hnone2; constructor; eauto.
          - destruct x; simpl in *.
            + eapply det_exps_n' in H; eauto.
            + eapply det_exps_n' in H0; eauto.
              * clear - H10 Hd1.
                eapply Forall2_swap_args, Forall2_trans_ex, Forall2_swap_args in Hd1; [|eauto].
                eapply Forall2_impl_In; [|eauto]; intros ?? _ _ (?&?&Heq&?).
                rewrite Heq; auto.
              * clear - H12 Hd2.
                eapply Forall2_swap_args, Forall2_trans_ex, Forall2_swap_args in Hd2; [|eauto].
                eapply Forall2_impl_In; [|eauto]; intros ?? _ _ (?&?&Heq&?).
                rewrite Heq; auto.
          - eapply IHForall; eauto with datatypes.
        }
        assert ((map (@concat _) vs) <> []) as Hnnil.
        { inv Hsome1; simpl; congruence. }
        clear - Hsv2 Heq Hcase1 Hcase2 Hnnil.
        revert Hnnil Hcase1 Hcase2 Heq.
        generalize (map (@concat _) vs0). generalize (map (@concat _) vs). clear vs vs0.
        intros vs1 vs2 Hnnil Hcase1. revert vs2 ss2.
        induction Hcase1; intros * Hcase2 Heq.
        + inv H; try congruence. inv Heq; try congruence. inv H2.
          inv Hcase2; auto. inv H; simpl in *; congruence.
        + inv Hcase2.
          { exfalso. clear IHHcase1 Hcase1. inv H; try congruence.
            inv Heq. inv H1. inv H5. simpl in *; congruence. }
          econstructor.
          * eapply case_detn. 3,4:eauto. 1,2:eauto.
            clear - H H1 Heq.
            revert hd1 hd0 H H1.
            induction Heq; intros * H1 H2; inv H1; inv H2; constructor; auto.
            inv H; simpl in *; inv H4; inv H3; auto.
          * eapply IHHcase1; eauto.
            destruct l1; simpl in *; congruence.
            clear - Heq.
            induction Heq; simpl; constructor; eauto. inv H; simpl; auto.
      - (* app *)
        inv Hwl. inv Hwx.
        inversion_clear Hs1 as [| | | | | | | | | |?????????? Hes1 Her1 Hbools1 Hn1].
        inversion_clear Hs2 as [| | | | | | | | | |?????????? Hes2 Her2 Hbools2 Hn2].
        eapply det_exps_n' in H; eauto.
        rewrite <-Forall2_map_2 in Her1, Her2.
        eapply det_exps_n' in H0; eauto. repeat rewrite concat_map_singl1 in H0.
        eapply bools_ofs_detn in Hbools2; eauto.
        eapply EqStNs_unmask; [eapply Hbools2|]; intros. clear H0.
        eapply HdetG. 2,3:eauto.
        eapply EqStNs_mask; eauto.
    Qed.

    Corollary det_exps_n : forall n Hi1 Hi2 bs1 bs2 es ss1 ss2,
        (forall x, In x (map snd env) -> det_var_inv n Hi1 Hi2 x) ->
        EqStN n bs1 bs2 ->
        Forall (wl_exp G) es ->
        Forall (wx_exp (map fst env)) es ->
        Forall2 (sem_exp G Hi1 bs1) es ss1 ->
        Forall2 (sem_exp G Hi2 bs2) es ss2 ->
        Forall2 (EqStN n) (concat ss1) (concat ss2).
    Proof.
      intros * Hin Hbs Hwl Hwx Hsem1 Hsem2.
      eapply Forall2_concat.
      eapply Forall2_trans_ex in Hsem2; [|eapply Forall2_swap_args, Hsem1].
      eapply Forall2_impl_In; [|eauto]; intros ?? _ _ (?&Hin'&(Hs1&Hs2)).
      rewrite Forall_forall in *.
      eapply det_exp_n; eauto.
    Qed.

    Corollary det_exp : forall Hi bs e ss1 ss2,
        wl_exp G e ->
        wx_exp (map fst env) e ->
        sem_exp G Hi bs e ss1 ->
        sem_exp G Hi bs e ss2 ->
        EqSts ss1 ss2.
    Proof.
      intros * Hwl Hwx Hs1 Hs2.
      eapply EqStN_EqSts. intros n.
      eapply det_exp_n; eauto.
      + intros * _ ???? Hv1 Hv2.
        eapply EqStN_EqSt, sem_var_det; eauto.
      + reflexivity.
    Qed.

    Corollary det_exps : forall Hi bs es ss1 ss2,
        Forall (wl_exp G) es ->
        Forall (wx_exp (map fst env)) es ->
        Forall2 (sem_exp G Hi bs) es ss1 ->
        Forall2 (sem_exp G Hi bs) es ss2 ->
        EqSts (concat ss1) (concat ss2).
    Proof.
      intros * Hwl Hwx Hs1 Hs2.
      eapply EqStN_EqSts. intros n.
      eapply det_exps_n; eauto.
      + intros * _ ???? Hv1 Hv2.
        eapply EqStN_EqSt, sem_var_det; eauto.
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

    Lemma fby_det_Sn : forall n xs1 xs2 ys1 ys2 zs1 zs2,
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
        (forall x, In x (map snd env) -> det_var_inv n Hi1 Hi2 x) ->
        wl_exp G e ->
        wx_exp (map fst env) e ->
        k < numstreams e ->
        EqStN (S n) bs1 bs2 ->
        (forall x, Is_free_left env x k e -> det_var_inv (S n) Hi1 Hi2 x) ->
        det_exp_inv (S n) Hi1 Hi2 bs1 bs2 e k.
    Proof.
      intros * Hn Hwl Hwx Hnum Hbs HSn.
      eapply exp_causal_ind
        with (P_exp:=det_exp_inv (S n) Hi1 Hi2 bs1 bs2); eauto; clear Hwl Hwx HSn.
      - (* const *)
        intros ??? Hwl Hwx Hs1 Hs2. inv Hs1. inv Hs2. simpl.
        rewrite H3, H4. eapply const_detn; eauto.
      - (* enum *)
        intros ???? Hwl Hwx Hs1 Hs2. inv Hs1. inv Hs2. simpl.
        rewrite H5, H6. eapply enum_detn; eauto.
      - (* var *)
        intros ???? Hvar ?? Hwl Hwx Hs1 Hs2. inv Hwx. inv Hs1. inv Hs2. simpl.
        eapply Hvar; eauto.
      - (* unop *)
        intros ??? He1 ?? Hwl Hwx Hs1 Hs2. inv Hwl. inv Hwx.
        inversion_clear Hs1 as [| | |???????? Hse1 Hty1 Hl1| | | | | | |].
        inversion_clear Hs2 as [| | |???????? Hse2 Hty2 Hl2| | | | | | |].
        rewrite Hty2 in Hty1; inv Hty1.
        eapply He1 in Hse2; eauto. simpl in *.
        eapply lift1_detn; eauto.
      - (* binop *)
        intros ???? He1 He2 ?? Hwl Hwx Hs1 Hs2. inv Hwl. inv Hwx.
        inversion_clear Hs1 as [| | | |??????????? Hse11 Hse12 Hty11 Hty12 Hl1| | | | | |].
        inversion_clear Hs2 as [| | | |??????????? Hse21 Hse22 Hty21 Hty22 Hl2| | | | | |].
        rewrite Hty21 in Hty11; inv Hty11. rewrite Hty22 in Hty12; inv Hty12.
        eapply He1 in Hse21; eauto. eapply He2 in Hse22; eauto. simpl in *.
        eapply lift2_detn. 3,4:eauto. 1,2:eauto.
      - (* fby *)
        intros ???? Hk He0s ?? Hwl Hwx Hs1 Hs2. inv Hwl. inv Hwx.
        inversion_clear Hs1 as [| | | | |???????? Hse11 Hse12 Hfby1| | | | |].
        inversion_clear Hs2 as [| | | | |???????? Hse21 Hse22 Hfby2| | | | |].
        eapply P_exps_det_exp_inv in He0s; eauto.
        eapply det_exps_n in Hse22; eauto using EqStN_weaken.
        assert (length (concat s0ss) = length ann0) as Hlen1.
        { eapply sem_exps_numstreams in Hse11; eauto.
          congruence. }
        assert (length (concat s0ss0) = length ann0) as Hlen2.
        { eapply sem_exps_numstreams in Hse21; eauto.
          congruence. }
        eapply fby_det_Sn; eauto.
        + eapply Forall2_forall2 in Hse22 as (_&Heq). eapply Heq; eauto.
          eapply Forall3_length in Hfby1 as (Hl1&Hl2). rewrite <-Hl1, Hlen1; eauto.
        + eapply Forall3_forall3 in Hfby1 as (_&_&Hfby1).
          eapply Hfby1 with (b:=def_stream); eauto. congruence.
        + eapply Forall3_forall3 in Hfby2 as (_&_&Hfby2).
          eapply Hfby2 with (b:=def_stream); eauto. congruence.
      - (* arrow *)
        intros ???? Hk He0s He1s ?? Hwl Hwx Hs1 Hs2. inv Hwl. inv Hwx.
        inversion_clear Hs1 as [| | | | | |???????? Hse11 Hse12 Harrow1| | | |].
        inversion_clear Hs2 as [| | | | | |???????? Hse21 Hse22 Harrow2| | | |].
        eapply P_exps_det_exp_inv in He0s; eauto.
        eapply P_exps_det_exp_inv in He1s; eauto.
        assert (length (concat s0ss) = length ann0) as Hlen1.
        { eapply sem_exps_numstreams in Hse11; eauto.
          congruence. }
        assert (length (concat s0ss0) = length ann0) as Hlen2.
        { eapply sem_exps_numstreams in Hse21; eauto.
          congruence. }
        eapply arrow_detn. eapply He0s. eapply He1s.
        + eapply Forall3_forall3 in Harrow1 as (_&_&Harrow1). eapply Harrow1; eauto.
          congruence.
        + eapply Forall3_forall3 in Harrow2 as (_&_&Harrow2). eapply Harrow2; eauto.
          congruence.
      - (* when *)
        intros ?????? Hk Hes Hin Hvar ?? Hwl Hwx Hs1 Hs2. inv Hwl. inv Hwx. simpl in *.
        inversion_clear Hs1 as [| | | | | | |????????? Hse1 Hsv1 Hwhen1| | |].
        inversion_clear Hs2 as [| | | | | | |????????? Hse2 Hsv2 Hwhen2| | |].
        eapply Hvar in Hsv2; eauto.
        eapply P_exps_det_exp_inv in Hes; eauto.
        assert (length (concat ss) = length tys) as Hlen1.
        { eapply sem_exps_numstreams in Hse1; eauto.
          congruence. }
        assert (length (concat ss0) = length tys) as Hlen2.
        { eapply sem_exps_numstreams in Hse2; eauto.
          congruence. }
        clear - Hk Hlen1 Hlen2 Hsv2 Hes Hwhen1 Hwhen2.
        repeat rewrite_Forall_forall.
        eapply when_detn.
        + eapply Hes.
        + eapply Hsv2.
        + eapply H2; eauto. congruence.
        + eapply H0; eauto. congruence.
      - (* merge *)
        intros ?????? Hk Hin Hvar Hes ?? Hwl Hwx Hs1 Hs2. assert (Hwl':=Hwl). inv Hwl'. inv Hwx. simpl in *.
        assert (length ss1 = length tys) as Hlen1.
        { eapply sem_exp_numstreams in Hs1; eauto. }
        assert (length ss2 = length tys) as Hlen2.
        { eapply sem_exp_numstreams in Hs2; eauto. }
        inversion_clear Hs1 as [| | | | | | | |????????? Hsv1 Hse1 Hmerge1| |].
        inversion_clear Hs2 as [| | | | | | | |????????? Hsv2 Hse2 Hmerge2| |].
        eapply Hvar in Hsv1; eauto using In_InMembers. specialize (Hsv1 Hsv2).
        assert (Forall2 (fun vs1 vs2 => EqStN (S n) (nth k0 vs1 def_stream) (nth k0 vs2 def_stream))
                        (map (@concat _) vs) (map (@concat _) vs0)) as Heq.
        { clear - Hes H4 H8 Hse1 Hse2.
          revert vs vs0 Hse1 Hse2.
          induction Hes; intros * Hse1 Hse2; inv H4; inv H8; inv Hse1; inv Hse2; constructor; eauto.
          eapply P_exps_det_exp_inv in H; eauto.
        }
        clear - Hk Hsv1 Heq Hmerge1 Hmerge2 Hlen1 Hlen2.
        revert Hmerge1 Hmerge2 Heq.
        generalize (map (@concat _) vs0). generalize (map (@concat _) vs). clear vs vs0.
        intros vs1 vs2 Hmerge1 Hmerge2 Heq.
        eapply merge_detn. eauto.
        + eapply Forall2_map_1, Forall2_map_2. eapply Heq.
        + eapply Forall2Transpose_nth in Hmerge1; eauto.
          congruence.
        + eapply Forall2Transpose_nth in Hmerge2; eauto.
          congruence.
      - (* case *)
        intros ????? Hk He Hes ?? Hwl Hwx Hs1 Hs2. assert (Hwl':=Hwl). inv Hwl'. inv Hwx. simpl in *.
        assert (length ss1 = length tys) as Hlen1.
        { eapply sem_exp_numstreams in Hs1; eauto. }
        assert (length ss2 = length tys) as Hlen2.
        { eapply sem_exp_numstreams in Hs2; eauto. }
        inversion_clear Hs1 as [| | | | | | | | |?????????? Hsv1 Hsome1 Hnone1 Hd1 Hcase1|].
        inversion_clear Hs2 as [| | | | | | | | |?????????? Hsv2 Hsome2 Hnone2 Hd2 Hcase2|].
        eapply He in Hsv2; eauto; simpl in Hsv2.
        assert (Forall2 (fun vs1 vs2 => EqStN (S n) (nth k0 vs1 def_stream) (nth k0 vs2 def_stream))
                        (map (@concat _) vs) (map (@concat _) vs0)) as Heq.
        { clear - Hes H7 H9 H12 H13 Hsome1 Hsome2 Hnone1 Hnone2 Hd1 Hd2.
          revert vs vs0 Hsome1 Hsome2 Hnone1 Hnone2.
          induction Hes; intros * Hsome1 Hsome2 Hnone1 Hnone2;
            inv Hsome1; inv Hsome2; inv Hnone1; inv Hnone2; constructor; eauto.
          - destruct x; simpl in *.
            + eapply P_exps_det_exp_inv in H; eauto.
            + eapply P_exps_det_exp_inv in H; eauto.
              * clear - H8 Hd1.
                eapply Forall2_swap_args, Forall2_trans_ex, Forall2_swap_args in Hd1; [|eauto].
                eapply Forall2_impl_In; [|eauto]; intros ?? _ _ (?&?&Heq&?).
                rewrite Heq; auto.
              * clear - H10 Hd2.
                eapply Forall2_swap_args, Forall2_trans_ex, Forall2_swap_args in Hd2; [|eauto].
                eapply Forall2_impl_In; [|eauto]; intros ?? _ _ (?&?&Heq&?).
                rewrite Heq; auto.
          - eapply IHHes; eauto with datatypes.
        }
        clear - Hk Hsv2 Heq Hcase1 Hcase2 Hlen1 Hlen2.
        revert Hcase1 Hcase2 Heq.
        generalize (map (@concat _) vs0). generalize (map (@concat _) vs). clear vs vs0.
        intros vs1 vs2 Hcase1 Hcase2 Heq.
        eapply case_detn. eauto.
        + eapply Forall2_map_1, Forall2_map_2. eapply Heq.
        + eapply Forall2Transpose_nth in Hcase1; eauto.
          congruence.
        + eapply Forall2Transpose_nth in Hcase2; eauto.
          congruence.
      - (* app *)
        intros ????? Hlen Hes Her ?? Hwl Hwx Hsem1 Hsem2. inv Hwl. inv Hwx.
        inversion_clear Hsem1 as [| | | | | | | | | |?????????? Hes1 Her1 Hbools1 Hn1].
        inversion_clear Hsem2 as [| | | | | | | | | |?????????? Hes2 Her2 Hbools2 Hn2].
        eapply P_exps_det_exp_inv_all in Hes; eauto.
        rewrite <-Forall2_map_2 in Her1, Her2. eapply P_exps_det_exp_inv_all in Her; eauto.
        do 2 rewrite concat_map_singl1 in Her.
        eapply bools_ofs_detn in Hbools2; eauto.
        assert (Forall2 (EqStN (S n)) ss1 ss2) as Heq.
        2:{ eapply Forall2_forall2 in Heq as (_&Heq).
            eapply Heq; eauto.
            specialize (Hn1 0). inv Hn1. rewrite H7 in H0. inv H0.
            unfold idents in H5. rewrite Forall2_map_1, Forall2_map_2 in H5. eapply Forall2_length in H5.
            congruence.
        }
        eapply EqStNs_unmask; eauto. intros.
        eapply HdetG. 2,3:eauto.
        eapply EqStNs_mask; eauto.
    Qed.

    Hypothesis Hnd : NoDup (map snd env).

    Lemma det_equation_S : forall n Hi1 Hi2 bs1 bs2 xs es k cx,
        wl_equation G (xs, es) ->
        wx_equation (map fst env) (xs, es) ->
        Sem.sem_equation G Hi1 bs1 (xs, es) ->
        Sem.sem_equation G Hi2 bs2 (xs, es) ->
        k < length xs ->
        P_exps (det_exp_inv (S n) Hi1 Hi2 bs1 bs2) es k ->
        In (nth k xs xH, cx) env ->
        det_var_inv (S n) Hi1 Hi2 cx.
    Proof.
      intros * (* Hn  *)(Hwl1&Hwl2) (Hwx1&Hwx2) Hsem1 Hsem2 Hnum HSn Hin.
      inv Hsem1. inv Hsem2.
      eapply P_exps_det_exp_inv in HSn; eauto.
      intros ???? Hv1 Hv2.
      eapply Forall2_forall2 in H5 as (Hl1&Heq1).
      eapply Forall2_forall2 in H7 as (Hl2&Heq2).
      eapply NoDup_snd_det in Hin; eauto; subst.
      eapply EqStN_morph. 3:eauto.
      1,2:eapply sem_var_det; eauto.
    Qed.

  End sem_equation_det.

  Lemma det_var_inv_mask : forall env n rs1 rs2 Hi1 Hi2 x,
      EqStN n rs1 rs2 ->
      det_var_inv env n Hi1 Hi2 x ->
      forall k, det_var_inv env n (mask_hist k rs1 Hi1) (mask_hist k rs2 Hi2) x.
  Proof.
    intros * Heq Hdet ????? Hv1 Hv2.
    eapply sem_var_mask_inv in Hv1 as (?&Hv1&Heq1).
    eapply sem_var_mask_inv in Hv2 as (?&Hv2&Heq2).
    rewrite Heq1, Heq2.
    eapply EqStN_mask; eauto.
  Qed.

  Lemma det_var_inv_unmask : forall env n rs1 rs2 Hi1 Hi2 x,
      EqStN n rs1 rs2 ->
      (forall k, det_var_inv env n (mask_hist k rs1 Hi1) (mask_hist k rs2 Hi2) x) ->
      det_var_inv env n Hi1 Hi2 x.
  Proof.
    intros * Heq Hdet ???? Hv1 Hv2.
    eapply EqStN_unmask; eauto.
    intros k. eapply Hdet; eauto using sem_var_mask.
  Qed.

  Fact in_app_map_flat_map {A B C} : forall (f : C -> B) (g : A -> list C) x xs y ys,
      In y ys ->
      In x (xs ++ map f (g y)) ->
      In x (xs ++ map f (flat_map g ys)).
  Proof.
    intros * Hin1 Hin2.
    rewrite in_app_iff in *.
    destruct Hin2 as [Hin2|Hin2]; auto.
    right.
    eapply incl_map; [|eauto]. intros ??.
    eapply in_flat_map; eauto.
  Qed.

  Fact nodup_app_map_flat_map {A B C} : forall (f : C -> B) (g : A -> list C) xs y ys,
      In y ys ->
      NoDup (xs ++ map f (flat_map g ys)) ->
      NoDup (xs ++ map f (g y)).
  Proof.
    intros * Hin Hnd.
    apply NoDup_app'.
    - apply NoDup_app_l in Hnd; auto.
    - apply NoDup_app_r in Hnd.
      induction ys; inv Hin; simpl in *; rewrite map_app in *.
      + apply NoDup_app_l in Hnd; auto.
      + apply NoDup_app_r in Hnd; auto.
    - eapply Forall_forall; intros * Hin1 Hin2.
      eapply NoDup_app_In in Hnd; eauto. eapply Hnd.
      eapply incl_map; [|eauto]. intros ??.
      eapply in_flat_map; eauto.
  Qed.

  Section sem_block_det.
    Context {PSyn : block -> Prop}.
    Context {prefs : PS.t}.
    Variable (G: @global PSyn prefs).

    Inductive sem_block_det (n : nat) (envS : list ident) : history -> history -> Stream bool -> Stream bool -> block -> Prop :=
    | Sdetbeq : forall Hi1 Hi2 bs1 bs2 eq,
        sem_equation G Hi1 bs1 eq ->
        sem_equation G Hi2 bs2 eq ->
        sem_block_det n envS Hi1 Hi2 bs1 bs2 (Beq eq)
    | Sdetreset : forall Hi1 Hi2 bs1 bs2 blocks er sr1 sr2 r1 r2,
        sem_exp G Hi1 bs1 er [sr1] ->
        sem_exp G Hi2 bs2 er [sr2] ->
        bools_of sr1 r1 ->
        bools_of sr2 r2 ->
        (forall k, Forall (sem_block_det n envS (mask_hist k r1 Hi1) (mask_hist k r2 Hi2) (maskb k r1 bs1) (maskb k r2 bs2)) blocks) ->
        sem_block_det n envS Hi1 Hi2 bs1 bs2 (Breset blocks er)
    | Sdetlocal : forall Hi1 Hi2 bs1 bs2 locs blocks Hl1 Hl2,
        (forall x vs, sem_var Hl1 x vs -> ~(InMembers x locs) -> sem_var Hi1 x vs) ->
        (forall x vs, sem_var Hl2 x vs -> ~(InMembers x locs) -> sem_var Hi2 x vs) ->
        Forall (sem_block_det n envS Hl1 Hl2 bs1 bs2) blocks ->
        Forall (det_var_inv (idcaus locs) (pred n) Hl1 Hl2) (map snd (idcaus locs)) ->
        Forall (fun x => In x envS -> det_var_inv (idcaus locs) n Hl1 Hl2 x) (map snd (idcaus locs)) ->
        sem_block_det n envS Hi1 Hi2 bs1 bs2 (Blocal locs blocks).

    (* Initialize with two "simple" sems *)
    Lemma sem_block_det_0 : forall envS blk Hi1 Hi2 bs1 bs2,
        sem_block G Hi1 bs1 blk ->
        sem_block G Hi2 bs2 blk ->
        sem_block_det 0 envS Hi1 Hi2 bs1 bs2 blk.
    Proof.
      induction blk using block_ind2; intros * Hsem1 Hsem2;
        inv Hsem1; inv Hsem2.
      - (* equation *)
        constructor; auto.
      - (* reset *)
        econstructor; eauto.
        intros k. specialize (H7 k). specialize (H10 k).
        rewrite Forall_forall in *; eauto.
      - (* locals *)
        econstructor; eauto.
        + rewrite Forall_forall in *; eauto.
        + eapply Forall_forall; intros * _ ??????; auto.
        + eapply Forall_forall; intros * _ ??????; auto.
    Qed.

    (* Go from n to n + 1 :) *)
    Lemma sem_block_det_S : forall n envS blk Hi1 Hi2 bs1 bs2,
        incl (map snd (idcaus (locals blk))) envS ->
        sem_block_det n envS Hi1 Hi2 bs1 bs2 blk ->
        sem_block_det (S n) [] Hi1 Hi2 bs1 bs2 blk.
    Proof.
      induction blk using block_ind2; intros * Hincl Hsem; inv Hsem; simpl in *.
      - (* equation *)
        constructor; eauto.
      - (* reset *)
        econstructor; eauto.
        intros k. specialize (H10 k).
        rewrite Forall_forall in *; intros; eauto.
        eapply H; eauto. etransitivity; eauto.
        apply incl_map, incl_map; intros ??; apply in_flat_map; eauto.
      - (* locals *)
        econstructor; eauto.
        + rewrite Forall_forall in *; intros; eauto.
          eapply H; eauto. etransitivity; eauto.
          apply incl_map, incl_map, incl_appr; intros ??; apply in_flat_map; eauto.
        + eapply Forall_impl_In; [|eapply H10]; intros ? Hin Hdet.
          eapply Hdet, Hincl; eauto. rewrite idcaus_app, map_app, in_app_iff; auto.
        + eapply Forall_forall; intros * _ Hnil. inv Hnil.
    Qed.

    Fact sem_block_det_sem_block1 : forall n envS blk Hi1 Hi2 bs1 bs2,
        sem_block_det n envS Hi1 Hi2 bs1 bs2 blk ->
        sem_block G Hi1 bs1 blk.
    Proof.
      induction blk using block_ind2; intros * Hsem; inv Hsem.
      - (* equation *)
        constructor; auto.
      - (* reset *)
        econstructor; eauto.
        intros k. specialize (H10 k).
        rewrite Forall_forall in *; eauto.
      - (* locals *)
        econstructor; eauto.
        rewrite Forall_forall in *; eauto.
    Qed.

    Fact sem_block_det_sem_block2 : forall n envS blk Hi1 Hi2 bs1 bs2,
        sem_block_det n envS Hi1 Hi2 bs1 bs2 blk ->
        sem_block G Hi2 bs2 blk.
    Proof.
      induction blk using block_ind2; intros * Hsem; inv Hsem.
      - (* equation *)
        constructor; auto.
      - (* reset *)
        econstructor; eauto.
        intros k. specialize (H10 k).
        rewrite Forall_forall in *; eauto.
      - (* locals *)
        econstructor; eauto.
        rewrite Forall_forall in *; eauto.
    Qed.

    Hint Resolve sem_block_det_sem_block1 sem_block_det_sem_block2.

    Lemma det_var_inv_incl : forall env env' n Hi1 Hi2 x,
        incl env env' ->
        det_var_inv env' n Hi1 Hi2 x ->
        det_var_inv env n Hi1 Hi2 x.
    Proof.
      intros * Hincl Hdet ??? Hin Hv1 Hv2; eauto.
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
      - (* reset *)
        econstructor; eauto.
        intros k. specialize (H10 k).
        rewrite Forall_forall in *; eauto.
      - (* local *)
        econstructor; eauto.
        1-2:rewrite Forall_forall in *; intros * Hin; eauto.
        rewrite <-Hperm; auto.
    Qed.

    Lemma sem_var_refines_inv : forall env Hi1 Hi2 x vs,
        In x env ->
        Env.dom_lb Hi1 env ->
        (forall vs, sem_var Hi1 x vs -> sem_var Hi2 x vs) ->
        sem_var Hi2 x vs ->
        sem_var Hi1 x vs.
    Proof.
      intros * Hin Hdom Href Hvar.
      eapply Env.dom_lb_use in Hdom as (vs'&Hfind); eauto.
      assert (sem_var Hi1 x vs') as Hvar' by (econstructor; eauto; reflexivity).
      specialize (Href _ Hvar').
      eapply sem_var_det in Href; eauto.
      now rewrite Href.
    Qed.

    Lemma sem_var_refines' : forall env Hi1 Hi2 x vs,
        In x env ->
        Env.dom_lb Hi1 env ->
        Env.refines (@EqSt _) Hi1 Hi2 ->
        sem_var Hi2 x vs ->
        sem_var Hi1 x vs.
    Proof.
      intros * Hin Hdom Href Hvar.
      eapply sem_var_refines_inv in Hvar; eauto.
      intros. eapply sem_var_refines; eauto.
    Qed.

    Lemma det_block_S : forall n envS blk env xs Hi1 Hi2 bs1 bs2 y cy,
        det_nodes G ->
        NoDup (map snd (env ++ idcaus (locals blk))) ->
        NoDupLocals (map fst env) blk ->
        VarsDefined blk xs ->
        incl xs (map fst env) ->
        (forall x, In x (map snd env) -> det_var_inv env n Hi1 Hi2 x) ->
        wl_block G blk ->
        wx_block (map fst env) blk ->
        sem_block_det (S n) envS Hi1 Hi2 bs1 bs2 blk ->
        EqStN (S n) bs1 bs2 ->
        In y xs ->
        In (y, cy) env ->
        (forall cx, In cx (map snd env) -> depends_on env cy cx blk -> det_var_inv env (S n) Hi1 Hi2 cx) ->
        (forall cx, In cx (map snd (idcaus (locals blk))) -> depends_on env cy cx blk -> In cx envS) ->
        det_var_inv env (S n) Hi1 Hi2 cy.
    Proof.
      induction blk as [(xs&es)| |] using block_ind2;
        intros * HdetG Hnd Hnd2 Hvars Hincl Hn Hwl Hwx Hsem Hbs Hinxs Hinenv HSn HenvS;
        inv Hnd2; inv Hvars; inv Hwl; inv Hwx; inv Hsem; simpl in *.
      - (* equation *)
        eapply In_nth in Hinxs as (?&Hlen&Hnth).
        rewrite app_nil_r in Hnd.
        eapply det_equation_S; eauto.
        + eapply Pexp_Pexps.
          * eapply Forall_forall; intros.
            inv H0. inv H2. eapply det_exp_S; eauto.
            1,2:eapply Forall_forall; eauto.
          * intros ? Hfree. eapply HSn; eauto using Is_free_left_list_In_snd.
            constructor. repeat esplit; eauto.
            rewrite <-Hnth. eapply nth_error_nth'; eauto.
          * inv H0. simpl in *. congruence.
        + now rewrite Hnth.
      - (* reset *)
        eapply in_concat in Hinxs as (?&Hin1&Hin2).
        eapply Forall2_ignore1, Forall_forall in H4 as (?&Hinblk&Hvars); eauto.
        eapply Forall_forall in H; eauto.
        assert (EqStN (S n) r1 r2) as Hrs.
        { eapply bools_of_detn. 2,3:eauto.
          eapply det_exp_S with (k:=0) (n0:=n) in H7; eauto; try lia.
          - eapply H7 in H10; eauto.
          - intros ? Hfree. eapply HSn; eauto using Is_free_left_In_snd.
            eapply DepOnReset2; eauto.
            eapply Exists_exists; do 2 esplit; eauto.
            eapply In_Is_defined_in with (cenv:=env0); eauto using incl_refl.
            1,2:eapply in_or_app; eauto.
            etransitivity; eauto using incl_concat.
        }
        eapply det_var_inv_unmask; eauto.
        intros k. specialize (H17 k).
        eapply H with (bs1:=maskb k r1 bs1) (bs2:=maskb k r2 bs2); eauto.
        2,5-7:rewrite Forall_forall in *; try rewrite map_app, map_fst_idcaus; eauto.
        + clear - Hinblk Hnd.
          unfold idcaus in *. rewrite map_app, map_map in *.
          eapply nodup_app_map_flat_map; eauto.
        + etransitivity; eauto using incl_concat.
        + intros. eapply det_var_inv_mask; eauto using EqStN_weaken.
        + eapply EqStN_mask; eauto.
        + intros ? Hin Hdep. eapply det_var_inv_mask; eauto.
          eapply HSn; eauto. constructor; eapply Exists_exists; eauto.
        + intros ? Hin Hdep. eapply HenvS; eauto.
          2:constructor; eapply Exists_exists; eauto.
          eapply incl_map; eauto. apply incl_map. intros ??; apply in_flat_map; eauto.
      - (* locals *)
        assert (In y (concat xs0)) as Hinxs0 by (rewrite <-H7; auto with datatypes).
        eapply in_concat in Hinxs0 as (?&Hin1&Hin2).
        eapply Forall2_ignore1, Forall_forall in H3 as (?&Hinblk&Hvars); eauto.
        eapply Forall_forall in H; eauto.
        assert (det_var_inv (env0 ++ idcaus locs) (S n) Hl1 Hl2 cy) as Hdet'.
        { eapply H; eauto.
          2,5-7:rewrite Forall_forall in *; try rewrite map_app, map_fst_idcaus; eauto.
          - clear - Hinblk Hnd. rewrite idcaus_app, app_assoc in Hnd.
            unfold idcaus in *. rewrite map_app, map_map in *.
            eapply nodup_app_map_flat_map; eauto.
          - rewrite map_app, map_fst_idcaus.
            etransitivity; eauto using incl_concat.
            rewrite <-H7, Permutation_app_comm.
            apply incl_app; [apply incl_appl|apply incl_appr]; eauto using incl_refl.
          - intros * Hin.
            rewrite map_app in Hin.
            apply in_app_iff in Hin as [Hin|Hin].
            + assert (Hdet:=Hin). eapply Hn in Hdet.
              intros ??? Hin3 Hv1 Hv2.
              assert (In (x2, x1) env0) as Hin4.
              { eapply in_app_iff in Hin3 as [Hin3|Hin3]; eauto. exfalso.
                rewrite map_app in Hnd. eapply NoDup_app_In in Hnd; eauto.
                eapply Hnd. rewrite idcaus_app, map_app. apply in_or_app; auto.
                left; eapply in_map_iff; do 2 esplit; eauto. auto.
              }
              assert (~InMembers x2 locs); eauto.
              intro contra. eapply H5; eauto.
              eapply in_map_iff. now do 2 esplit; eauto.
            + eapply Forall_forall in H16; eauto.
              intros ??? Hin3 Hv1 Hv2.
              eapply H16; eauto.
              eapply in_app_iff in Hin3 as [Hin3|Hin3]; auto. exfalso.
              rewrite map_app in Hnd. eapply NoDup_app_In in Hnd. 2:eapply in_map_iff; eauto.
              eapply Hnd. rewrite idcaus_app, map_app. apply in_or_app; auto.
          - apply in_app_iff; auto.
          - intros ? _ Hdep ??? Hin Hv1 Hv2.
            apply in_app_iff in Hin as [Hin|Hin].
            + assert (~InMembers x1 locs) as Hnin.
              { intro contra. eapply H5; eauto.
                eapply in_map_iff. now do 2 esplit; eauto. }
              eapply HSn; eauto. eapply in_map_iff; do 2 esplit; eauto; auto.
              constructor; simpl. eapply Exists_exists; do 2 esplit; eauto.
            + eapply Forall_forall in H17. 2:(eapply in_map_iff; do 2 esplit; eauto).
              eapply H17; eauto. eapply HenvS; eauto.
              eapply in_map_iff. do 2 esplit; eauto. rewrite idcaus_app, in_app_iff; auto.
              constructor; simpl. eapply Exists_exists; do 2 esplit; eauto.
          - intros * Hin Hdep. apply HenvS.
            eapply incl_map; eauto. apply incl_map, incl_appr. intros ??; apply in_flat_map; eauto.
            constructor. eapply Exists_exists; do 2 esplit; eauto.
        }
        intros ??? Hin3 Hv1 Hv2.
        assert (x1 = y); subst.
        { eapply NoDup_snd_det; eauto. 1,2:repeat rewrite in_app_iff; eauto. }
        assert (~InMembers y locs) as Hnin.
        { intro contra. eapply H5; eauto. }
        assert (NoDupLocals x x0).
        { rewrite Forall_forall in *. eapply NoDupLocals_incl; eauto.
          intros x' ?; eapply in_concat' with (x1:=x') in Hin2; eauto.
          rewrite <-H7 in Hin2. repeat rewrite in_app_iff in *. destruct Hin2; auto.
        }
        eapply Hdet'; eauto using in_or_app.
        1,2:(eapply sem_var_refines_inv; [| | |eauto]; intros; eauto).
        1,2:rewrite Forall_forall in *; eapply sem_block_dom_lb; eauto.
    Qed.

    Lemma sem_block_det_cons_nIn : forall n envS x blk Hi1 Hi2 bs1 bs2,
        ~In x (map snd (idcaus (locals blk))) ->
        sem_block_det n envS Hi1 Hi2 bs1 bs2 blk ->
        sem_block_det n (x::envS) Hi1 Hi2 bs1 bs2 blk.
    Proof.
      induction blk using block_ind2; intros * Hnin Hsem;
        simpl in *; inv Hsem.
      - (* equation *)
        constructor; auto.
      - (* reset *)
        econstructor; eauto.
        intros k. specialize (H10 k).
        rewrite Forall_forall in *; intros. eapply H; eauto.
        contradict Hnin. eapply incl_map; eauto. apply incl_map.
        intros ??. apply in_flat_map; eauto.
      - (* locals *)
        econstructor; eauto.
        + rewrite Forall_forall in *; intros. eapply H; eauto.
          contradict Hnin. eapply incl_map; eauto. apply incl_map, incl_appr.
          intros ??. apply in_flat_map; eauto.
        + eapply Forall_impl_In; [|eapply H10]; intros * Hin1 Hloc Hin2.
          inv Hin2; eauto.
          exfalso. eapply Hnin. rewrite idcaus_app, map_app, in_app_iff; auto.
    Qed.

    Lemma sem_block_det_cons_In : forall n envS blk env xs Hi1 Hi2 bs1 bs2 y cy,
        det_nodes G ->
        NoDup (map snd (env ++ idcaus (locals blk))) ->
        NoDupLocals (map fst env) blk ->
        VarsDefined blk xs ->
        incl xs (map fst env) ->
        (forall x, In x (map snd env) -> det_var_inv env n Hi1 Hi2 x) ->
        wl_block G blk ->
        wx_block (map fst env) blk ->
        sem_block_det (S n) envS Hi1 Hi2 bs1 bs2 blk ->
        EqStN (S n) bs1 bs2 ->
        In (y, cy) (idcaus (locals blk)) ->
        (forall cx, In cx (map snd env) -> depends_on env cy cx blk -> det_var_inv env (S n) Hi1 Hi2 cx) ->
        (forall cx, In cx (map snd (idcaus (locals blk))) -> depends_on env cy cx blk -> In cx envS) ->
        sem_block_det (S n) (cy::envS) Hi1 Hi2 bs1 bs2 blk.
    Proof.
      induction blk as [(xs&es)| |] using block_ind2;
        intros * HdetG Hnd Hnd2 Hvars Hincl Hn Hwl Hwx Hsem Hbs Hinenv HSn HenvS;
        inv Hnd2; inv Hvars; inv Hwl; inv Hwx; inv Hsem; simpl in *.
      - (* equation *)
        inv Hinenv.
      - (* reset *)
        econstructor; eauto. intros k. specialize (H17 k).
        eapply Forall2_ignore2 in H4.
        rewrite Forall_forall in *; intros * Hinblk.
        destruct (in_dec ident_eq_dec cy (map snd (idcaus (locals x)))).
        2:eapply sem_block_det_cons_nIn; eauto.
        eapply in_map_iff in i as ((?&?)&?&?); subst.
        edestruct H4 as (?&Hinvars&Hvars'); eauto.
        assert (EqStN (S n) r1 r2) as Hrs.
        { eapply bools_of_detn. 2,3:eauto.
          eapply det_exp_S with (k0:=0) (n0:=n) in H7; eauto; try lia.
          - eapply H7 in H10; eauto.
          - intros ? Hfree. eapply HSn; eauto using Is_free_left_In_snd.
            eapply DepOnReset2; eauto.
            eapply Exists_exists; do 2 esplit; eauto.
            eapply In_Is_defined_in with (cenv:=env0); eauto using incl_refl.
            1,2:eapply in_or_app; eauto.
            + right. rewrite <-map_fst_idcaus. eapply in_map_iff. now do 2 esplit; eauto.
            + etransitivity; eauto using incl_concat.
        }
        { eapply H with (env:=env0); eauto.
          - clear - Hinblk Hnd.
            unfold idcaus in *. rewrite map_app, map_map in *.
            eapply nodup_app_map_flat_map; eauto.
          - etransitivity; eauto using incl_concat.
          - intros * Hin.
            eapply det_var_inv_mask; eauto using EqStN_weaken.
          - eapply EqStN_mask; eauto.
          - intros ? Hin' Hdep.
            eapply det_var_inv_mask; eauto. eapply HSn; eauto.
            constructor; simpl. eapply Exists_exists; do 2 esplit; eauto.
          - intros * Hin Hdep. apply HenvS.
            eapply incl_map; eauto. apply incl_map. intros ??; apply in_flat_map; eauto.
            constructor. eapply Exists_exists; do 2 esplit; eauto.
        }
      - (* locals *)
        rewrite idcaus_app, in_app_iff in Hinenv. destruct Hinenv as [Hinenv|Hinenv].
        + (* current locs *)
          econstructor; eauto.
          * rewrite Forall_forall in *; intros.
            eapply sem_block_det_cons_nIn; eauto.
            rewrite idcaus_app, 2 map_app in Hnd. eapply NoDup_app_r in Hnd.
            eapply NoDup_app_In in Hnd; eauto. 2:eapply in_map_iff; now do 2 esplit; eauto.
            contradict Hnd. eapply incl_map; eauto. apply incl_map.
            intros ??. apply in_flat_map; eauto.
          * eapply Forall_impl_In; [|eapply H17]; intros ? Hin Hdet Hin'.
            inv Hin'; eauto.
            assert (In y (concat xs0)) as Hinvars.
            { rewrite <-H7. apply in_or_app; left. rewrite <-map_fst_idcaus.
              eapply in_map_iff. now do 2 esplit; eauto. }
            eapply in_concat in Hinvars as (xs'&?&Hinvars).
            eapply Forall2_ignore1, Forall_forall in H3 as (?&Hinblk&Hvars'); eauto.
            eapply det_var_inv_incl with (env':=env0 ++ idcaus locs). solve_incl_app.
            { eapply det_block_S with (envS:=envS); eauto.
              - clear - Hinblk Hnd. rewrite idcaus_app, app_assoc in Hnd.
                unfold idcaus in *. rewrite map_app, map_map in *.
                eapply nodup_app_map_flat_map; eauto.
              - rewrite Forall_forall in *. eapply NoDupLocals_incl; [|eauto].
                rewrite map_app, map_fst_idcaus. solve_incl_app.
              - rewrite map_app, map_fst_idcaus.
                etransitivity; eauto using incl_concat.
                rewrite <-H7, Permutation_app_comm.
                apply incl_app; [apply incl_appl|apply incl_appr]; eauto using incl_refl.
              - intros * Hin'.
                rewrite map_app in Hin'.
                apply in_app_iff in Hin' as [Hin'|Hin'].
                + assert (Hdet':=Hin'). eapply Hn in Hdet'.
                  intros ??? Hin3 Hv1 Hv2.
                  assert (In (x1, x0) env0) as Hin4.
                  { eapply in_app_iff in Hin3 as [Hin3|Hin3]; eauto. exfalso.
                    rewrite map_app in Hnd. eapply NoDup_app_In in Hnd; eauto.
                    eapply Hnd. rewrite idcaus_app, map_app. apply in_or_app; auto.
                    left; eapply in_map_iff; do 2 esplit; eauto. auto.
                  }
                  assert (~InMembers x1 locs) as Hnin.
                  { intro contra. eapply H5; eauto.
                    eapply in_map_iff. now do 2 esplit; eauto. }
                  eapply Hdet'; eauto.
                + eapply Forall_forall in H16; eauto.
                  intros ??? Hin3 Hv1 Hv2.
                  eapply H16; eauto.
                  eapply in_app_iff in Hin3 as [Hin3|Hin3]; auto. exfalso.
                  rewrite map_app in Hnd. eapply NoDup_app_In in Hnd. 2:eapply in_map_iff; eauto.
                  eapply Hnd. rewrite idcaus_app, map_app. apply in_or_app; auto.
              - eapply Forall_forall in H1; eauto.
              - rewrite map_app, map_fst_idcaus.
                rewrite Forall_forall in *; eauto.
              - rewrite Forall_forall in *; eauto.
              - apply in_app_iff; auto.
              - intros ? _ Hdep ??? Hin' Hv1 Hv2.
                apply in_app_iff in Hin' as [Hin'|Hin'].
                + assert (~InMembers x0 locs) as Hnin.
                  { intro contra. eapply H5; eauto.
                    eapply in_map_iff. now do 2 esplit; eauto. }
                  eapply HSn; eauto. eapply in_map_iff; do 2 esplit; eauto; auto.
                  constructor; simpl. eapply Exists_exists; do 2 esplit; eauto.
                + eapply Forall_forall in H17. 2:(eapply in_map_iff; do 2 esplit; eauto).
                  eapply H17; eauto. eapply HenvS; eauto.
                  eapply in_map_iff. do 2 esplit; eauto. rewrite idcaus_app, in_app_iff; auto.
                  constructor; simpl. eapply Exists_exists; do 2 esplit; eauto.
              - intros * Hin' Hdep. eapply HenvS; eauto.
                2:constructor; eapply Exists_exists; eauto.
                rewrite idcaus_app, map_app, in_app_iff. right.
                eapply incl_map; eauto. apply incl_map. intros ??. apply in_flat_map; eauto.
            }
        + (* deeper *)
          eapply Forall2_ignore2 in H3; eauto.
          econstructor; eauto.
          * rewrite Forall_forall in *; intros * Hinblk.
            destruct (in_dec ident_eq_dec cy (map snd (idcaus (locals x)))).
            2:eapply sem_block_det_cons_nIn; eauto.
            { edestruct H3 as (?&Hinvars&Hvars'); eauto.
              eapply in_map_iff in i as ((?&?)&?&?); subst.
              eapply H with (env:=env0++idcaus locs); eauto.
              2,3,5:rewrite map_app, map_fst_idcaus; eauto.
              - clear - Hinblk Hnd. rewrite idcaus_app, app_assoc in Hnd.
                unfold idcaus in *. rewrite map_app, map_map in *.
                eapply nodup_app_map_flat_map; eauto.
              - etransitivity; eauto using incl_concat.
                rewrite <-H7, Permutation_app_comm.
                apply incl_app; [apply incl_appl|apply incl_appr]; eauto using incl_refl.
              - intros * Hin.
                rewrite map_app in Hin.
                apply in_app_iff in Hin as [Hin|Hin].
                + assert (Hdet:=Hin). eapply Hn in Hdet.
                  intros ??? Hin3 Hv1 Hv2.
                  assert (In (x2, x1) env0) as Hin4.
                  { eapply in_app_iff in Hin3 as [Hin3|Hin3]; eauto. exfalso.
                    rewrite map_app in Hnd. eapply NoDup_app_In in Hnd; eauto.
                    eapply Hnd. rewrite idcaus_app, map_app. apply in_or_app; auto.
                    left; eapply in_map_iff; do 2 esplit; eauto. auto.
                  }
                  assert (~InMembers x2 locs) as Hnin.
                  { intro contra. eapply H5; eauto.
                    eapply in_map_iff. now do 2 esplit; eauto. }
                  eapply Hdet; eauto.
                + intros ??? Hin3 Hv1 Hv2.
                  eapply H16; eauto.
                  eapply in_app_iff in Hin3 as [Hin3|Hin3]; auto. exfalso.
                  rewrite map_app in Hnd. eapply NoDup_app_In in Hnd. 2:eapply in_map_iff; eauto.
                  eapply Hnd. rewrite idcaus_app, map_app. apply in_or_app; auto.
              - intros ? _ Hdep ??? Hin Hv1 Hv2.
                apply in_app_iff in Hin as [Hin|Hin].
                + assert (~InMembers x1 locs) as Hnin.
                  { intro contra. eapply H5; eauto.
                    eapply in_map_iff. now do 2 esplit; eauto. }
                  eapply HSn; eauto. eapply in_map_iff; do 2 esplit; eauto; auto.
                  constructor; simpl. eapply Exists_exists; do 2 esplit; eauto.
                + eapply H17; eauto. eapply in_map_iff; now do 2 esplit; eauto.
                  eapply HenvS; eauto. rewrite idcaus_app, map_app, in_app_iff; left.
                  eapply in_map_iff. now do 2 esplit; eauto.
                  constructor; simpl. eapply Exists_exists; do 2 esplit; eauto.
              - intros * Hin Hdep. apply HenvS.
                eapply incl_map; eauto. apply incl_map, incl_appr. intros ??; apply in_flat_map; eauto.
                constructor. eapply Exists_exists; do 2 esplit; eauto.
            }
          * eapply Forall_impl_In; [|eapply H17]; intros ? Hin Hdet Hin'.
            inv Hin'; eauto. exfalso. clear - Hnd Hinenv Hin.
            rewrite idcaus_app, 2 map_app in Hnd.
            eapply NoDup_app_r, NoDup_app_In in Hnd; eauto.
            eapply Hnd, in_map_iff. now do 2 esplit; eauto.
    Qed.

    Lemma det_vars_n :
      forall nd n Hi1 Hi2 bs1 bs2,
        det_nodes G ->
        wl_node G nd ->
        wx_node nd ->
        node_causal nd ->
        EqStN n bs1 bs2 ->
        sem_block G Hi1 bs1 (n_block nd) ->
        sem_block G Hi2 bs2 (n_block nd) ->
        Forall (det_var_inv (idcaus (n_in nd ++ n_out nd)) n Hi1 Hi2) (map snd (idcaus (n_in nd))) ->
        Forall (det_var_inv (idcaus (n_in nd ++ n_out nd)) n Hi1 Hi2) (map snd (idcaus (n_in nd ++ n_out nd))).
    Proof.
      intros * HdetG Hwl Hwxn Hcaus Hbs Hsem1 Hsem2 Hins.

      assert (sem_block_det n (map snd (idcaus (n_in nd ++ n_out nd ++ locals (n_block nd)))) Hi1 Hi2 bs1 bs2 (n_block nd) /\
              Forall (fun x => In x (map snd (idcaus (n_in nd ++ n_out nd))) ->
                            det_var_inv (idcaus (n_in nd ++ n_out nd)) n Hi1 Hi2 x)
                     (map snd (idcaus (n_in nd ++ n_out nd ++ locals (n_block nd))))) as (_&Hvars).
      2:{ eapply Forall_impl_In; [|eapply Forall_incl; [eapply Hvars|]]; eauto.
          repeat rewrite idcaus_app. solve_incl_app. }

      induction n.
      - (* everyone is equal up to 0 anyway *)
        split.
        + eapply sem_block_det_0; eauto.
        + eapply Forall_forall. intros ??????. constructor.
      - (* use the causal induction to step once *)
        clear Hsem1 Hsem2.
        destruct IHn as (Hblk&Hvars); eauto using EqStN_weaken.
        { eapply Forall_impl; [|eapply Hins]; intros ??? ?????.
          eapply EqStN_weaken; eauto. }

        eapply node_causal_ind2; eauto.
        + intros ?? Hperm (Hblk'&Hvars'). split.
          * eapply sem_block_det_Perm; eauto.
          * rewrite <-Hperm; auto.
        + split; auto.
          eapply sem_block_det_S; [|eauto].
          repeat rewrite idcaus_app. solve_incl_app.
        + intros ?? Hin (Hblk'&Hvars') Hdep.
          repeat rewrite idcaus_app, map_app, in_app_iff in Hin.
          destruct Hcaus as (Hnd&_). rewrite app_assoc, idcaus_app, map_app in Hnd.
          destruct Hin as [Hin|[Hin|Hin]]; (split; [|constructor; auto; intros Hin']).
          * eapply sem_block_det_cons_nIn; eauto.
            eapply NoDup_app_In in Hnd; eauto. rewrite idcaus_app, map_app, in_app_iff; auto.
          * eapply Forall_forall in Hins; eauto.
          * eapply sem_block_det_cons_nIn; eauto.
            eapply NoDup_app_In in Hnd; eauto. rewrite idcaus_app, map_app, in_app_iff; auto.
          * pose proof (n_defd nd) as (?&Hdef&Hperm).
            eapply in_map_iff in Hin as ((?&?)&?&Hin); subst.
            eapply det_block_S; eauto.
            5:rewrite map_fst_idcaus; auto.
            -- rewrite map_app; auto.
            -- rewrite map_fst_idcaus. eapply node_NoDupLocals.
            -- rewrite Hperm, map_fst_idcaus. solve_incl_app.
            -- intros ??.
               eapply Forall_forall in Hvars; eauto.
               rewrite app_assoc, idcaus_app, map_app, in_app_iff; auto.
            -- rewrite Hperm, <-map_fst_idcaus.
               eapply in_map_iff; do 2 esplit; eauto.
            -- rewrite idcaus_app, in_app_iff; auto.
            -- intros ???.
               eapply Forall_forall in Hvars'; eauto.
          * pose proof (n_defd nd) as (?&Hdef&Hperm).
            eapply in_map_iff in Hin as ((?&?)&?&?); subst.
            eapply sem_block_det_cons_In; eauto.
            5:rewrite map_fst_idcaus; auto.
            -- rewrite map_app; auto.
            -- rewrite map_fst_idcaus. eapply node_NoDupLocals.
            -- rewrite Hperm, map_fst_idcaus. solve_incl_app.
            -- intros ? Hin'. eapply Forall_forall in Hvars; eauto.
               rewrite app_assoc, idcaus_app, map_app, in_app_iff; auto.
            -- intros ? Hin' Hdep'.
               eapply Forall_forall in Hvars'; eauto.
          * exfalso. eapply NoDup_app_In in Hnd; eauto.
    Qed.

  End sem_block_det.

  Lemma det_global_n {PSyn prefs} : forall (G : @global PSyn prefs),
      wl_global G ->
      wx_global G ->
      Forall node_causal (nodes G) ->
      det_nodes G.
  Proof.
    intros (enms&nds).
    induction nds as [|nd nds]; intros Hwl Hwx Hcaus ?????? Heqins Hs1 Hs2;
      inv Hcaus. now inv Hs1.
    inversion_clear Hs1 as [?????? Hfind1 Hins1 Houts1 Hbcks1 Hbk1].
    inversion_clear Hs2 as [?????? Hfind2 Hins2 Houts2 Hbcks2 Hbk2].
    rewrite Hfind1 in Hfind2. inv Hfind2.
    destruct (ident_eq_dec (n_name nd) f); subst.
    - assert (Hfind2:=Hfind1). rewrite find_node_now in Hfind2; auto; inv Hfind2.
      assert (~ Is_node_in_block (n_name n1) (n_block n1)) as Hnin.
      { eapply find_node_not_Is_node_in; eauto using wl_global_Ordered_nodes. }
      eapply sem_block_cons in Hbcks1; eauto using wl_global_Ordered_nodes.
      eapply sem_block_cons in Hbcks2; eauto using wl_global_Ordered_nodes.

      assert (Forall (det_var_inv (idcaus (n_in n1 ++ n_out n1)) n H H0) (map snd (idcaus (n_in n1)))) as Hins.
      { eapply node_causal_NoDup in H1 as Hnd.
        clear - Heqins Hins1 Hins2 Hnd.
        assert (incl (idcaus (n_in n1)) (idcaus (n_in n1 ++ n_out n1))) as Hincl.
        { rewrite idcaus_app. solve_incl_app. }
        revert ins1 ins2 Hins1 Hins2 Heqins Hnd Hincl.
        generalize (idcaus (n_in n1 ++ n_out n1)) as cenv.
        induction (n_in n1) as [|(?&(?&?)&?)]; intros * Hins1 Hins2 Heqins;
          inv Hins1; inv Hins2; inv Heqins; constructor; eauto; simpl in *.
        - intros ???? Hv1 Hv2.
          specialize (Hincl _ (in_eq _ _)).
          eapply NoDup_snd_det in Hincl; eauto; subst.
          eapply sem_var_det in H3; eauto. eapply sem_var_det in H4; eauto.
          now rewrite H3, H4.
        - eapply IHl; eauto. eapply incl_cons'; eauto. }
      eapply det_vars_n in Hins; eauto.
      + eapply Forall2_trans_ex in Houts2; [|eapply Forall2_swap_args, Houts1].
        eapply Forall2_impl_In; [|eauto]; intros ?? _ _ (?&Hin&Hv1&Hv2).
        eapply in_map_iff in Hin as ((?&(?&?)&?)&?&Hin); subst.
        unfold idcaus in Hins. rewrite Forall_map, Forall_map in Hins.
        eapply Forall_forall in Hins; [|eauto using in_or_app].
        eapply Hins; eauto; simpl in *.
        eapply in_map_iff; do 2 esplit; eauto using in_or_app. reflexivity.
      + inv Hwl; inv Hwx; auto.
      + inv Hwl; destruct H5; auto.
      + inv Hwx; auto.
      + eapply clocks_of_EqStN; eauto.
    - rewrite find_node_other in Hfind1; auto.
      eapply IHnds; eauto. inv Hwl; auto. inv Hwx; auto.
      1,2:econstructor; eauto.
      1,2:eapply sem_block_cons; eauto using wl_global_Ordered_nodes.
      1,2:eapply find_node_later_not_Is_node_in; eauto using wl_global_Ordered_nodes.
  Qed.

  Theorem det_global {PSyn prefs} : forall (G: @global PSyn prefs) f ins outs1 outs2,
      wl_global G ->
      wx_global G ->
      Forall node_causal (nodes G) ->
      sem_node G f ins outs1 ->
      sem_node G f ins outs2 ->
      EqSts outs1 outs2.
  Proof.
    intros * Hwl Hwx Hcaus Hsem1 Hsem2.
    eapply det_nodes_ins; eauto.
    eapply det_global_n; eauto.
  Qed.

End LSEMDETERMINISM.

Module LSemDeterminismFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks   : CLOCKS        Ids Op OpAux)
       (Syn   : LSYNTAX Ids Op OpAux Cks)
       (LCA   : LCAUSALITY Ids Op OpAux Cks Syn)
       (Lord  : LORDERED Ids Op OpAux Cks Syn)
       (CStr  : COINDSTREAMS Ids Op OpAux Cks)
       (Sem   : LSEMANTICS Ids Op OpAux Cks Syn Lord CStr)
<: LSEMDETERMINISM Ids Op OpAux Cks Syn LCA Lord CStr Sem.
  Include LSEMDETERMINISM Ids Op OpAux Cks Syn LCA Lord CStr Sem.
End LSemDeterminismFun.
