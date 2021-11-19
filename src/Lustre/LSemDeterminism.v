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
       (Import Syn   : LSYNTAX Ids Op OpAux Cks)
       (Import Typ   : LTYPING Ids Op OpAux Cks Syn)
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

    Variable env : list (ident * (type * clock * ident)).

    Definition det_var_inv n (H1 H2 : history) : ident -> Prop :=
      fun cx => forall x vs1 vs2,
          In (x, cx) (idcaus env) ->
          sem_var H1 x vs1 ->
          sem_var H2 x vs2 ->
          EqStN n vs1 vs2.

    Definition def_stream := Streams.const absent.

    Definition det_exp_inv n H1 H2 bs1 bs2 : exp -> nat -> Prop :=
      fun e k => forall ss1 ss2,
          wt_exp G (idty (idty env)) e ->
          sem_exp G H1 bs1 e ss1 ->
          sem_exp G H2 bs2 e ss2 ->
          EqStN n (nth k ss1 def_stream) (nth k ss2 def_stream).

    Lemma P_exps_det_exp_inv : forall n H1 H2 bs1 bs2 es k ss1 ss2,
        Forall (wt_exp G (idty (idty env))) es ->
        P_exps (det_exp_inv n H1 H2 bs1 bs2) es k ->
        Forall2 (sem_exp G H1 bs1) es ss1 ->
        Forall2 (sem_exp G H2 bs2) es ss2 ->
        EqStN n (nth k (concat ss1) def_stream) (nth k (concat ss2) def_stream).
    Proof.
      induction es; intros * Hwt Hp Hsem1 Hsem2;
        inv Hwt; inv Hsem1; inv Hsem2; simpl. inv Hp.
      assert (length y = numstreams a) as Hlen1 by (eapply sem_exp_numstreams; eauto).
      assert (length y0 = numstreams a) as Hlen2 by (eapply sem_exp_numstreams; eauto).
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
        Forall (fun es => Forall (wt_exp G (idty (idty env))) (snd es)) es ->
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
      { eapply sem_exps_numstreams in H5; eauto.
        eapply sem_exps_numstreams in H9; eauto. congruence. }
      clear - Hlen Hlen0 H8 H12 Heq1 Heq2.
      eapply Forall3_forall3 in H8 as (?&?&?).
      eapply Forall3_forall3 in H12 as (?&?&?).
      erewrite H1 at 1; try reflexivity.
      erewrite H4; try reflexivity.
      constructor; eauto.
      1,2:congruence.
    Qed.

    Lemma P_exps_det_exp_inv_all : forall n H1 H2 bs1 bs2 es ss1 ss2,
        Forall (wt_exp G (idty (idty env))) es ->
        (forall k, k < length (annots es) -> P_exps (det_exp_inv n H1 H2 bs1 bs2) es k) ->
        Forall2 (sem_exp G H1 bs1) es ss1 ->
        Forall2 (sem_exp G H2 bs2) es ss2 ->
        Forall2 (EqStN n) (concat ss1) (concat ss2).
    Proof.
      intros * Hwt Hk Hsem1 Hsem2.
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
      1,3:erewrite fst_NoDupMembers, map_map, map_ext, <-fst_NoDupMembers; eauto; intros (?&?); auto.
      1,2:(rewrite Forall2_map_1, Forall2_map_2; eapply Forall2_impl_In; [|eauto];
           intros (?&?) (?&?) _ _ Heq; inv Heq; simpl in *; subst; auto).
      clear - Hfst Hnd Heq2 H3 H5. unfold EqSts in *.
      induction Heq2; inv H3; inv H5; inv Hnd; simpl in *; inv Hfst; auto.
      - destruct y, H1, H2; subst; simpl in *.
        rewrite <-H1, <-H3. inv H; auto.
      - exfalso. destruct y, H1; subst; simpl in *.
        eapply H4. rewrite fst_InMembers, H6, <-fst_InMembers.
        eapply Exists_exists in H2 as ((?&?)&?&?&?); subst; eauto using In_InMembers.
      - exfalso. destruct y, H2; subst; simpl in *.
        eapply H4. rewrite fst_InMembers, <-fst_InMembers.
        eapply Exists_exists in H1 as ((?&?)&?&?&?); subst; eauto using In_InMembers.
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
        erewrite fst_NoDupMembers, map_map, map_ext, <-fst_NoDupMembers; eauto; intros (?&?); auto.
        (rewrite Forall2_map_1, Forall2_map_2; eapply Forall2_impl_In; [|eauto];
           intros (?&?) (?&?) _ _ Heq; inv Heq; simpl in *; subst; auto).
        eapply option_map_inv in H as (?&?&?); subst.
        eapply option_map_inv in H6 as (?&?&?); subst.
        specialize (Heq3 _ _ eq_refl eq_refl). inv Heq3; auto.
      - econstructor; eauto.
        + clear - Hfst Hnd Heq2 H8 H12. unfold EqSts in *.
          induction Heq2; inv H8; inv H12; inv Hnd; simpl in *; inv Hfst; auto.
          * destruct y, H1, H2; subst; simpl in *.
            rewrite <-H1, <-H3. inv H; auto.
          * exfalso. destruct y, H1; subst; simpl in *.
            eapply H4. rewrite fst_InMembers, H6, <-fst_InMembers.
            eapply Exists_exists in H2 as ((?&?)&?&?&?); subst; eauto using In_InMembers.
          * exfalso. destruct y, H2; subst; simpl in *.
            eapply H4. rewrite fst_InMembers, <-fst_InMembers.
            eapply Exists_exists in H1 as ((?&?)&?&?&?); subst; eauto using In_InMembers.
        + eapply IHn. 6,7:eauto. 1-5:intros; eauto.
          erewrite 2 map_map, map_ext with (l:=xss1), map_ext with (l:=xss2); eauto; intros (?&?); auto.
          erewrite fst_NoDupMembers, map_map, map_ext, <-fst_NoDupMembers; eauto; intros (?&?); auto.
          (rewrite Forall2_map_1, Forall2_map_2; eapply Forall2_impl_In; [|eauto];
           intros (?&?) (?&?) _ _ Heq; inv Heq; simpl in *; subst; auto).
          eapply option_map_inv in H as (?&?&?); subst.
          eapply option_map_inv in H0 as (?&?&?); subst.
          specialize (Heq3 _ _ eq_refl eq_refl). inv Heq3; auto.
      - exfalso.
        eapply Exists_exists in H8 as ((?&?)&Hin&?&?); subst.
        eapply In_InMembers, fst_InMembers in Hin. rewrite Hfst in Hin.
        eapply fst_InMembers, InMembers_In in Hin as (?&Hin).
        eapply Forall_forall in H11; eauto; simpl in *. congruence.
      - exfalso.
        eapply Exists_exists in H11 as ((?&?)&Hin&?&?); subst.
        eapply In_InMembers, fst_InMembers in Hin. rewrite <-Hfst in Hin.
        eapply fst_InMembers, InMembers_In in Hin as (?&Hin).
        eapply Forall_forall in H7; eauto; simpl in *. congruence.
      - econstructor; eauto.
        + specialize (Heq3 _ _ eq_refl eq_refl). inv Heq3; auto.
        + eapply IHn. 6,7:eauto. 1-5:intros; eauto.
          erewrite 2 map_map, map_ext with (l:=xss1), map_ext with (l:=xss2); eauto; intros (?&?); auto.
          erewrite fst_NoDupMembers, map_map, map_ext, <-fst_NoDupMembers; eauto; intros (?&?); auto.
          (rewrite Forall2_map_1, Forall2_map_2; eapply Forall2_impl_In; [|eauto];
           intros (?&?) (?&?) _ _ Heq; inv Heq; simpl in *; subst; auto).
          inv H. inv H0.
          specialize (Heq3 _ _ eq_refl eq_refl). inv Heq3; auto.
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
                    wt_exp G (idty (idty env)) e ->
                    sem_exp G Hi1 bs1 e ss1 ->
                    sem_exp G Hi2 bs2 e ss2 ->
                    Forall2 (EqStN n) ss1 ss2) es ->
        Forall (wt_exp G (idty (idty env))) es->
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
                    wt_exp G (idty (idty env)) e ->
                    sem_exp G H1 bs1 e ss1 -> sem_exp G H2 bs2 e ss2 -> Forall2 (EqStN n) ss1 ss2)
               (snd es)) es ->
        length ss1 = length ss2 ->
        Forall (fun es => Forall (wt_exp G (idty (idty env))) (snd es)) es ->
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
        (forall x, In x (map snd (idcaus env)) -> det_var_inv n Hi1 Hi2 x) ->
        EqStN n bs1 bs2 ->
        wt_exp G (idty (idty env)) e ->
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
        constructor; auto.
        eapply in_map_iff in H1 as ((id&(?&?))&Heq&Hin); inv Heq.
        eapply in_map_iff in Hin as ((id&(?&?))&Heq&Hin); inv Heq.
        eapply Hn; eauto. eapply in_map_iff; repeat esplit; eauto.
        1,2:eapply in_map_iff; eauto. exists (x, (ty, c, i)); auto.
      - (* unop *)
        inversion_clear Hs1 as [| | |???????? Hse1 Hty1 Hl1| | | | | | | |].
        inversion_clear Hs2 as [| | |???????? Hse2 Hty2 Hl2| | | | | | | |].
        rewrite Hty2 in Hty1; inv Hty1.
        eapply IHe in Hse1; eauto. inv Hse1.
        constructor; auto.
        eapply lift1_detn; eauto.
      - (* binop *)
        inversion_clear Hs1 as [| | | |??????????? Hse11 Hse12 Hty11 Hty12 Hl1| | | | | | |].
        inversion_clear Hs2 as [| | | |??????????? Hse21 Hse22 Hty21 Hty22 Hl2| | | | | | |].
        rewrite Hty21 in Hty11; inv Hty11. rewrite Hty22 in Hty12; inv Hty12.
        eapply IHe1 in Hse21; eauto. eapply IHe2 in Hse22; eauto.
        inv Hse21. inv Hse22.
        constructor; auto.
        eapply lift2_detn. 3,4:eauto. 1,2:eauto.
      - (* fby *)
        inversion_clear Hs1 as [| | | | |???????? Hse11 Hse12 Hfby1| | | | | |].
        inversion_clear Hs2 as [| | | | |???????? Hse21 Hse22 Hfby2| | | | | |].
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
        inversion_clear Hs1 as [| | | | | |???????? Hse11 Hse12 Harrow1| | | | |].
        inversion_clear Hs2 as [| | | | | |???????? Hse21 Hse22 Harrow2| | | | |].
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
        eapply in_map_iff in H4 as ((id&(ty&cx))&Heq&Hin); inv Heq.
        eapply in_map_iff in Hin as ((?&?&?)&Heq&Hin); inv Heq.
        inversion_clear Hs1 as [| | | | | | |????????? Hse1 Hsv1 Hwhen1| | | |].
        inversion_clear Hs2 as [| | | | | | |????????? Hse2 Hsv2 Hwhen2| | | |].
        eapply det_exps_n' in H; eauto.
        eapply Hn in Hsv1; eauto using In_InMembers. 2:eapply in_map_iff; do 2 esplit; eauto.
        2,3:eapply in_map_iff; do 2 esplit; eauto; simpl; auto.
        specialize (Hsv1 Hsv2).
        clear - H Hsv1 Hwhen1 Hwhen2.
        repeat rewrite_Forall_forall. congruence.
        eapply when_detn. 2:eauto.
        + eapply H0 with (a:=def_stream) (b:=def_stream) (n0:=n0); eauto. congruence.
        + eapply H4; eauto; congruence.
        + eapply H2; eauto; congruence.
      - (* merge *)
        eapply in_map_iff in H3 as ((id&(ty&cx))&Heq&Hin); inv Heq.
        eapply in_map_iff in Hin as ((?&?&?)&Heq&Hin); inv Heq.
        inversion_clear Hs1 as [| | | | | | | |????????? Hsv1 Hse1 Hmerge1| | |].
        inversion_clear Hs2 as [| | | | | | | |????????? Hsv2 Hse2 Hmerge2| | |].
        eapply Hn in Hsv1; eauto using In_InMembers. 2:eapply in_map_iff; do 2 esplit; eauto.
        2,3:eapply in_map_iff; do 2 esplit; eauto; auto.
        specialize (Hsv1 Hsv2).
        eapply Forall2Brs_det_exp_n' in H. 3-5:eauto.
        2:{ eapply Forall2Brs_length1 in Hse1. eapply Forall2Brs_length1 in Hse2.
            2,3:do 2 (eapply Forall_forall; intros); eapply sem_exp_numstreams; eauto.
            2,3:do 2 (eapply Forall_forall in H7; eauto).
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
        inversion_clear Hs1 as [| | | | | | | | |????????? Hsv1 Hse1 Hcase1| |].
        inversion_clear Hs2 as [| | | | | | | | |????????? Hsv2 Hse2 Hcase2| |].
        eapply IHe in Hsv2; eauto. apply Forall2_singl in Hsv2.
        eapply Forall2Brs_det_exp_n' in H. 3-5:eauto.
        2:{ eapply Forall2Brs_length1 in Hse1. eapply Forall2Brs_length1 in Hse2.
            2,3:do 2 (eapply Forall_forall; intros); eapply sem_exp_numstreams; eauto.
            2,3:do 2 (eapply Forall_forall in H10; eauto).
            inv Hse1; inv Hse2; try congruence. exfalso; auto.
        }
        eapply Forall2Brs_fst in Hse1. eapply Forall2Brs_fst in Hse2.
        rewrite Forall3_map_2 in Hcase1. rewrite Forall3_map_2 in Hcase2.
        clear - Hcase1 Hcase2 Hsv2 H H8 Hse1 Hse2. revert vs0 ss2 Hsv2 Hcase2 H Hse1 Hse2.
        induction Hcase1; intros * Hsv2 Hcase2 Heq Hse1 Hse2;
          inv Heq; inv Hcase2; inv Hse1; inv Hse2;
            constructor; eauto.
        eapply case_detn. 6,7:eauto. 1-5:eauto.
        congruence.
        rewrite fst_NoDupMembers, H3, H8. apply seq_NoDup.
        intros. congruence.
      - (* case (default) *)
        inversion_clear Hs1 as [| | | | | | | | | |?????????? Hsv1 _ Hse1 Hd1 Hcase1|].
        inversion_clear Hs2 as [| | | | | | | | | |?????????? Hsv2 _ Hse2 Hd2 Hcase2|].
        eapply IHe in Hsv2; eauto. apply Forall2_singl in Hsv2.
        eapply Forall2Brs_det_exp_n' in H. 3-5:eauto.
        2:{ eapply Forall2Brs_length1 in Hse1. eapply Forall2Brs_length1 in Hse2.
            2,3:do 2 (eapply Forall_forall; intros); eapply sem_exp_numstreams; eauto.
            2,3:do 2 (eapply Forall_forall in H11; eauto).
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
        inversion_clear Hs1 as [| | | | | | | | | | |?????????? Hes1 Her1 Hbools1 Hn1].
        inversion_clear Hs2 as [| | | | | | | | | | |?????????? Hes2 Her2 Hbools2 Hn2].
        eapply det_exps_n' in H; eauto.
        rewrite <-Forall2_map_2 in Her1, Her2.
        eapply det_exps_n' in H0; eauto. repeat rewrite concat_map_singl1 in H0.
        eapply bools_ofs_detn in Hbools2; eauto.
        eapply EqStNs_unmask; [eapply Hbools2|]; intros. clear H0.
        eapply HdetG. 2,3:eauto.
        eapply EqStNs_mask; eauto.
    Qed.

    Corollary det_exps_n : forall n Hi1 Hi2 bs1 bs2 es ss1 ss2,
        (forall x, In x (map snd (idcaus env)) -> det_var_inv n Hi1 Hi2 x) ->
        EqStN n bs1 bs2 ->
        Forall (wt_exp G (idty (idty env))) es ->
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
        wt_exp G (idty (idty env)) e ->
        sem_exp G Hi bs e ss1 ->
        sem_exp G Hi bs e ss2 ->
        EqSts ss1 ss2.
    Proof.
      intros * Hwt Hs1 Hs2.
      eapply EqStN_EqSts. intros n.
      eapply det_exp_n; eauto.
      + intros * _ ???? Hv1 Hv2.
        eapply EqStN_EqSt, sem_var_det; eauto.
      + reflexivity.
    Qed.

    Corollary det_exps : forall Hi bs es ss1 ss2,
        Forall (wt_exp G (idty (idty env))) es ->
        Forall2 (sem_exp G Hi bs) es ss1 ->
        Forall2 (sem_exp G Hi bs) es ss2 ->
        EqSts (concat ss1) (concat ss2).
    Proof.
      intros * Hwt Hs1 Hs2.
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
        (forall x, In x (map snd (idcaus env)) -> det_var_inv n Hi1 Hi2 x) ->
        wt_exp G (idty (idty env)) e ->
        k < numstreams e ->
        EqStN (S n) bs1 bs2 ->
        (forall x, Is_free_left (idcaus env) x k e -> det_var_inv (S n) Hi1 Hi2 x) ->
        det_exp_inv (S n) Hi1 Hi2 bs1 bs2 e k.
    Proof.
      intros * Hn Hwt Hnum Hbs HSn.
      eapply exp_causal_ind
        with (P_exp:=det_exp_inv (S n) Hi1 Hi2 bs1 bs2); eauto.
      1-11:clear Hwt HSn.
      - (* const *)
        intros ??? Hwt Hs1 Hs2. inv Hs1. inv Hs2. simpl.
        rewrite H3, H4. eapply const_detn; eauto.
      - (* enum *)
        intros ???? Hwt Hs1 Hs2. inv Hs1. inv Hs2. simpl.
        rewrite H5, H6. eapply enum_detn; eauto.
      - (* var *)
        intros ???? Hvar ?? Hwt Hs1 Hs2. inv Hwt. inv Hs1. inv Hs2. simpl.
        eapply Hvar; eauto.
      - (* unop *)
        intros ??? He1 ?? Hwt Hs1 Hs2. inv Hwt.
        inversion_clear Hs1 as [| | |???????? Hse1 Hty1 Hl1| | | | | | | |].
        inversion_clear Hs2 as [| | |???????? Hse2 Hty2 Hl2| | | | | | | |].
        rewrite Hty2 in Hty1; inv Hty1.
        eapply He1 in Hse2; eauto. simpl in *.
        eapply lift1_detn; eauto.
      - (* binop *)
        intros ???? He1 He2 ?? Hwt Hs1 Hs2. inv Hwt.
        inversion_clear Hs1 as [| | | |??????????? Hse11 Hse12 Hty11 Hty12 Hl1| | | | | | |].
        inversion_clear Hs2 as [| | | |??????????? Hse21 Hse22 Hty21 Hty22 Hl2| | | | | | |].
        rewrite Hty21 in Hty11; inv Hty11. rewrite Hty22 in Hty12; inv Hty12.
        eapply He1 in Hse21; eauto. eapply He2 in Hse22; eauto. simpl in *.
        eapply lift2_detn. 3,4:eauto. 1,2:eauto.
      - (* fby *)
        intros ???? Hk He0s ?? Hwt Hs1 Hs2. inv Hwt.
        inversion_clear Hs1 as [| | | | |???????? Hse11 Hse12 Hfby1| | | | | |].
        inversion_clear Hs2 as [| | | | |???????? Hse21 Hse22 Hfby2| | | | | |].
        eapply P_exps_det_exp_inv in He0s; eauto.
        eapply det_exps_n in Hse22; eauto using EqStN_weaken.
        assert (length (concat s0ss) = length ann0) as Hlen1.
        { eapply sem_exps_numstreams in Hse11; eauto.
          rewrite <-length_typesof_annots, H5, map_length in Hse11.
          assumption. }
        assert (length (concat s0ss0) = length ann0) as Hlen2.
        { eapply sem_exps_numstreams in Hse21; eauto.
          rewrite <-length_typesof_annots, H5, map_length in Hse21.
          assumption. }
        eapply fby_det_Sn; eauto.
        + eapply Forall2_forall2 in Hse22 as (_&Heq). eapply Heq; eauto.
          eapply Forall3_length in Hfby1 as (Hl1&Hl2). rewrite <-Hl1, Hlen1; eauto.
        + eapply Forall3_forall3 in Hfby1 as (_&_&Hfby1).
          eapply Hfby1 with (b:=def_stream); eauto. congruence.
        + eapply Forall3_forall3 in Hfby2 as (_&_&Hfby2).
          eapply Hfby2 with (b:=def_stream); eauto. congruence.
      - (* arrow *)
        intros ???? Hk He0s He1s ?? Hwt Hs1 Hs2. inv Hwt.
        inversion_clear Hs1 as [| | | | | |???????? Hse11 Hse12 Harrow1| | | | |].
        inversion_clear Hs2 as [| | | | | |???????? Hse21 Hse22 Harrow2| | | | |].
        eapply P_exps_det_exp_inv in He0s; eauto.
        eapply P_exps_det_exp_inv in He1s; eauto.
        assert (length (concat s0ss) = length ann0) as Hlen1.
        { eapply sem_exps_numstreams in Hse11; eauto.
          rewrite <-length_typesof_annots, H5, map_length in Hse11.
          assumption. }
        assert (length (concat s0ss0) = length ann0) as Hlen2.
        { eapply sem_exps_numstreams in Hse21; eauto.
          rewrite <-length_typesof_annots, H5, map_length in Hse21.
          assumption. }
        eapply arrow_detn. eapply He0s. eapply He1s.
        + eapply Forall3_forall3 in Harrow1 as (_&_&Harrow1). eapply Harrow1; eauto.
          congruence.
        + eapply Forall3_forall3 in Harrow2 as (_&_&Harrow2). eapply Harrow2; eauto.
          congruence.
      - (* when *)
        intros ?????? Hk Hes Hin Hvar ?? Hwt Hs1 Hs2. inv Hwt. simpl in *.
        inversion_clear Hs1 as [| | | | | | |????????? Hse1 Hsv1 Hwhen1| | | |].
        inversion_clear Hs2 as [| | | | | | |????????? Hse2 Hsv2 Hwhen2| | | |].
        eapply Hvar in Hsv2; eauto.
        eapply P_exps_det_exp_inv in Hes; eauto.
        assert (length (concat ss) = length (typesof es)) as Hlen1.
        { eapply sem_exps_numstreams in Hse1; eauto.
          now rewrite <-length_typesof_annots in Hse1. }
        assert (length (concat ss0) = length (typesof es)) as Hlen2.
        { eapply sem_exps_numstreams in Hse2; eauto.
          now rewrite <-length_typesof_annots in Hse2. }
        clear - Hk Hlen1 Hlen2 Hsv2 Hes Hwhen1 Hwhen2.
        repeat rewrite_Forall_forall.
        eapply when_detn.
        + eapply Hes.
        + eapply Hsv2.
        + eapply H2; eauto. congruence.
        + eapply H0; eauto. congruence.
      - (* merge *)
        intros ?????? Hk Hin Hvar Hes ?? Hwt Hs1 Hs2. assert (Hwt':=Hwt). inv Hwt'. simpl in *.
        assert (length ss1 = length tys) as Hlen1.
        { eapply sem_exp_numstreams in Hs1; eauto. }
        assert (length ss2 = length tys) as Hlen2.
        { eapply sem_exp_numstreams in Hs2; eauto. }
        inversion_clear Hs1 as [| | | | | | | |????????? Hsv1 Hse1 Hmerge1| | |].
        inversion_clear Hs2 as [| | | | | | | |????????? Hsv2 Hse2 Hmerge2| | |].
        eapply Hvar in Hsv1; eauto using In_InMembers. specialize (Hsv1 Hsv2).
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
          { eapply sem_exp_numstreams in Hs1; eauto. }
          assert (length ss2 = length tys) as Hlen2.
          { eapply sem_exp_numstreams in Hs2; eauto. }
          inversion_clear Hs1 as [| | | | | | | | |????????? Hsv1 Hse1 Hcase1| |].
          inversion_clear Hs2 as [| | | | | | | | |????????? Hsv2 Hse2 Hcase2| |].
          eapply Hse in Hsv1; eauto using In_InMembers. specialize (Hsv1 Hsv2). simpl in Hsv1.
          assert (Forall2 (fun xs1 xs2 => EqStN (S n) (snd xs1) (snd xs2)) (nth k0 vs []) (nth k0 vs0 [])) as Heq.
          { eapply Forall2Brs_det_exp_inv; eauto. eapply Forall3_length in Hcase1 as (?&?). congruence. }
          eapply Forall2Brs_fst in Hse1. eapply Forall2Brs_fst in Hse2.
          eapply Forall3_forall3 in Hcase1 as (?&?&Hcase1).
          eapply Forall3_forall3 in Hcase2 as (?&?&Hcase2).
          eapply case_detn. 6:eapply Hcase1; eauto. 7:eapply Hcase2; eauto. 1-5:eauto.
          4,5:congruence.
          * eapply Forall_forall in Hse1; [|eapply nth_In]. eapply Forall_forall in Hse2; [|eapply nth_In].
            rewrite Hse1, Hse2; auto. 1,2:congruence.
          * eapply Forall_forall in Hse1; [|eapply nth_In].
            rewrite fst_NoDupMembers, Hse1, H6. apply seq_NoDup. congruence.
          * intros ??. instantiate (1:=None). instantiate (1:=None). intros Hnth1 Hnth2.
            erewrite map_nth with (d:=bool_velus_type) in Hnth1. inv Hnth1.
        + (* default *)
          assert (length ss1 = length (typesof d0)) as Hlen1.
          { eapply sem_exp_numstreams in Hs1; eauto. }
          assert (length ss2 = length (typesof d0)) as Hlen2.
          { eapply sem_exp_numstreams in Hs2; eauto. }
          inversion_clear Hs1 as [| | | | | | | | | |?????????? Hsv1 _ Hse1 Hd1 Hcase1|].
          inversion_clear Hs2 as [| | | | | | | | | |?????????? Hsv2 _ Hse2 Hd2 Hcase2|].
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
            1,2:rewrite map_length in H, H1; congruence.
      - (* app *)
        intros ????? Hlen Hes Her ?? Hwt Hsem1 Hsem2. inv Hwt.
        inversion_clear Hsem1 as [| | | | | | | | | | |?????????? Hes1 Her1 Hbools1 Hn1].
        inversion_clear Hsem2 as [| | | | | | | | | | |?????????? Hes2 Her2 Hbools2 Hn2].
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
      - rewrite map_fst_idcaus, <-2 map_fst_idty; eauto.
    Qed.

    Hypothesis Hnd : NoDup (map snd (idcaus env)).

    Lemma det_equation_S : forall n Hi1 Hi2 bs1 bs2 xs es k cx,
        wt_equation G (idty (idty env)) (xs, es) ->
        Sem.sem_equation G Hi1 bs1 (xs, es) ->
        Sem.sem_equation G Hi2 bs2 (xs, es) ->
        k < length xs ->
        P_exps (det_exp_inv (S n) Hi1 Hi2 bs1 bs2) es k ->
        In (nth k xs xH, cx) (idcaus env) ->
        det_var_inv (S n) Hi1 Hi2 cx.
    Proof.
      intros * (* Hn  *)(Hwt1&Hwt2) Hsem1 Hsem2 Hnum HSn Hin.
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

  Lemma det_var_inv_filter : forall env n sc1 sc2 Hi1 Hi2 x,
      EqStN n sc1 sc2 ->
      det_var_inv env n Hi1 Hi2 x ->
      forall c, det_var_inv env n (filter_hist c sc1 Hi1) (filter_hist c sc2 Hi2) x.
  Proof.
    intros * Heq Hdet ????? Hv1 Hv2.
    eapply sem_var_filter_inv in Hv1 as (?&Hv1&Heq1).
    eapply sem_var_filter_inv in Hv2 as (?&Hv2&Heq2).
    rewrite Heq1, Heq2.
    eapply EqStN_filter; eauto.
  Qed.

  Lemma det_var_inv_unfilter dom : forall env tn n sc1 sc2 Hi1 Hi2 x,
      wt_stream sc1 (Tenum tn) ->
      wt_stream sc2 (Tenum tn) ->
      EqStN n sc1 sc2 ->
      (forall c, In c (seq 0 (snd tn)) -> det_var_inv env n (filter_hist c sc1 Hi1) (filter_hist c sc2 Hi2) x) ->
      slower_subhist dom Hi1 (abstract_clock sc1) ->
      slower_subhist dom Hi2 (abstract_clock sc2) ->
      (forall y, In (y, x) (idcaus env) -> dom y) ->
      det_var_inv env n Hi1 Hi2 x.
  Proof.
    intros * Hwt1 Hwt2 Heq Hdet Hsl1 Hsl2 Hdom ???? Hv1 Hv2.
    eapply EqStN_unfilter. 3:eauto. 1,2:eauto.
    intros k Hin. eapply Hdet; eauto using sem_var_filter.
    - inv Hv1. rewrite H2. eapply Hsl1; eauto.
    - inv Hv2. rewrite H2. eapply Hsl2; eauto.
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
    | Sdetswitch : forall Hi1 Hi2 bs1 bs2 branches ec sc1 sc2,
        sem_exp G Hi1 bs1 ec [sc1] ->
        sem_exp G Hi2 bs2 ec [sc2] ->
        wt_streams [sc1] (typeof ec) ->
        wt_streams [sc2] (typeof ec) ->
        Forall (fun blks => Forall (sem_block_det n envS
                                               (filter_hist (fst blks) sc1 Hi1) (filter_hist (fst blks) sc2 Hi2)
                                               (filterb (fst blks) sc1 bs1) (filterb (fst blks) sc2 bs2)) (snd blks)) branches ->
        slower_subhist (fun x => Syn.Is_defined_in x (Bswitch ec branches)) Hi1 (abstract_clock sc1) ->
        slower_subhist (fun x => Syn.Is_defined_in x (Bswitch ec branches)) Hi2 (abstract_clock sc2) ->
        sem_block_det n envS Hi1 Hi2 bs1 bs2 (Bswitch ec branches)
    | Sdetlocal : forall Hi1 Hi2 bs1 bs2 locs blocks Hl1 Hl2,
        (forall x vs, sem_var Hl1 x vs -> ~(InMembers x locs) -> sem_var Hi1 x vs) ->
        (forall x vs, sem_var Hl2 x vs -> ~(InMembers x locs) -> sem_var Hi2 x vs) ->
        Forall (sem_block_det n envS Hl1 Hl2 bs1 bs2) blocks ->
        Forall (det_var_inv locs (pred n) Hl1 Hl2) (map snd (idcaus locs)) ->
        Forall (fun x => In x envS -> det_var_inv locs n Hl1 Hl2 x) (map snd (idcaus locs)) ->
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
      - (* switch *)
        econstructor; eauto.
        do 2 (eapply Forall_forall; intros).
        repeat (take (Forall _ _) and eapply Forall_forall in it; eauto).
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
      - (* switch *)
        econstructor; eauto.
        do 2 (eapply Forall_forall; intros).
        repeat (take (Forall _ _) and eapply Forall_forall in it; eauto).
        eapply it; eauto.
        etransitivity; [|eauto].
        apply incl_map, incl_map.
        intros ??; do 2 (apply in_flat_map; repeat esplit; eauto).
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
      - (* switch *)
        econstructor; eauto.
        do 2 (eapply Forall_forall; intros).
        repeat (take (Forall _ _) and eapply Forall_forall in it; eauto).
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
      - (* switch *)
        econstructor; eauto.
        do 2 (eapply Forall_forall; intros).
        repeat (take (Forall _ _) and eapply Forall_forall in it; eauto).
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
      eapply Hdet; eauto. eapply incl_map; eauto.
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
      - (* switch *)
        econstructor; eauto.
        do 2 (eapply Forall_forall; intros).
        repeat (take (Forall _ _) and eapply Forall_forall in it; eauto).
      - (* local *)
        econstructor; eauto.
        1-2:rewrite Forall_forall in *; intros * Hin; eauto.
        rewrite <-Hperm; auto.
    Qed.

    Lemma det_block_S : forall n envS blk env xs Hi1 Hi2 bs1 bs2 y cy,
        det_nodes G ->
        NoDup (map snd (idcaus env ++ idcaus (locals blk))) ->
        NoDupLocals (map fst env) blk ->
        VarsDefined blk xs ->
        incl xs (map fst env) ->
        (forall x, In x (map snd (idcaus env)) -> det_var_inv env n Hi1 Hi2 x) ->
        wt_block G (idty (idty env)) blk ->
        sem_block_det (S n) envS Hi1 Hi2 bs1 bs2 blk ->
        EqStN (S n) bs1 bs2 ->
        In y xs ->
        In (y, cy) (idcaus env) ->
        (forall cx, In cx (map snd (idcaus env)) -> depends_on (idcaus env) cy cx blk -> det_var_inv env (S n) Hi1 Hi2 cx) ->
        (forall cx, In cx (map snd (idcaus (locals blk))) -> depends_on (idcaus env) cy cx blk -> In cx envS) ->
        det_var_inv env (S n) Hi1 Hi2 cy.
    Proof.
      induction blk as [(xs&es)| | |] using block_ind2;
        intros * HdetG Hnd Hnd2 Hvars Hincl Hn Hwt Hsem Hbs Hinxs Hinenv HSn HenvS;
        inv Hnd2; inv Hvars; inv Hwt; inv Hsem; simpl in *.
      - (* equation *)
        eapply In_nth in Hinxs as (?&Hlen&Hnth).
        rewrite app_nil_r in Hnd.
        eapply det_equation_S; eauto.
        + eapply Pexp_Pexps.
          * eapply Forall_forall; intros.
            inv H1. eapply det_exp_S; eauto.
            1,2:eapply Forall_forall; eauto.
          * intros ? Hfree. eapply HSn; eauto using Is_free_left_list_In_snd.
            constructor. repeat esplit; eauto.
            rewrite <-Hnth. eapply nth_error_nth'; eauto.
          * inv H1. apply Forall2_length in H2.
            rewrite <-length_typesof_annots. congruence.
        + now rewrite Hnth.
      - (* reset *)
        eapply in_concat in Hinxs as (?&Hin1&Hin2).
        eapply Forall2_ignore1, Forall_forall in H4 as (?&Hinblk&Hvars); eauto.
        eapply Forall_forall in H; eauto.
        assert (EqStN (S n) r1 r2) as Hrs.
        { eapply bools_of_detn. 2,3:eauto.
          eapply det_exp_S with (k:=0) (n0:=n) in H5; eauto.
          - eapply H5 in H8; simpl in H8; eauto.
          - rewrite <-length_typeof_numstreams, H7; simpl. lia.
          - intros ? Hfree. eapply HSn; eauto using Is_free_left_In_snd.
            eapply DepOnReset2; eauto.
            eapply Exists_exists; do 2 esplit; eauto.
            eapply In_Is_defined_in with (cenv:=idcaus env0); eauto using incl_refl.
            1,2:eapply in_or_app; eauto. rewrite map_fst_idcaus.
            etransitivity; eauto using incl_concat.
        }
        eapply det_var_inv_unmask; eauto.
        intros k. specialize (H15 k).
        eapply H with (bs1:=maskb k r1 bs1) (bs2:=maskb k r2 bs2); eauto.
        2,5-6:rewrite Forall_forall in *; try rewrite map_app, map_fst_idcaus; eauto.
        + clear - Hinblk Hnd.
          unfold idcaus in *. rewrite map_app, 2 map_map in *.
          eapply nodup_app_map_flat_map; eauto.
        + etransitivity; eauto using incl_concat.
        + intros. eapply det_var_inv_mask; eauto using EqStN_weaken.
        + eapply EqStN_mask; eauto.
        + intros ? Hin Hdep. eapply det_var_inv_mask; eauto.
          eapply HSn; eauto. constructor; eapply Exists_exists; eauto.
        + intros ? Hin Hdep. eapply HenvS; eauto.
          2:constructor; eapply Exists_exists; eauto.
          eapply incl_map; eauto. apply incl_map. intros ??; apply in_flat_map; eauto.
      - (* switch *)
        eapply det_exp_S with (k:=0) (n0:=n) in H9; eauto. specialize (H9 H12); simpl in H9.
        2:{ rewrite <-length_typeof_numstreams, H6; auto. }
        2:{ intros ? Isf. eapply HSn; eauto using Is_free_left_In_snd.
            eapply DepOnSwitch2; eauto.
            inv H5; try congruence. destruct H0 as (?&Hvars&Hperm).
            rewrite <-Hperm in Hinxs. apply in_concat in Hinxs as (?&Hin1&Hin2).
            eapply Forall2_ignore1, Forall_forall in Hvars as (?&?&?); eauto.
            left. eapply Exists_exists; do 2 esplit; eauto.
            eapply In_Is_defined_in with (cenv:=idcaus env0); eauto using incl_refl, in_or_app.
            rewrite map_fst_idcaus. etransitivity; eauto using incl_concat.
            now rewrite Hperm. }
        repeat (take (wt_streams [_] (typeof ec)) and rewrite H6 in it; apply Forall2_singl in it).
        eapply det_var_inv_unfilter. 3:eauto. 1-6:eauto.
        2:{ intros ? Hinenv'; simpl.
            eapply NoDup_snd_det in Hinenv; eauto; subst. 2:solve_NoDup_app.
            eapply VarsDefined_Is_defined; eauto. 2:constructor; auto.
            constructor.
            eapply Forall_impl; [|eapply H2]; intros (?&?) ?.
            eapply Forall_impl; [|eauto]; intros. eapply NoDupLocals_incl; eauto.
        }
        intros ? Hseq.
        assert (exists blks, In (c, blks) branches) as (blks&Hinbrs).
        { rewrite <-H8 in Hseq. eapply in_map_iff in Hseq as ((?&?)&?&Hin); subst; eauto. }
        repeat (take (Forall _ branches) and eapply Forall_forall in it; eauto).
        destruct it4 as (?&Hvars&Hperm).
        rewrite <-Hperm in Hinxs. apply in_concat in Hinxs as (?&Hin1&Hin2).
        eapply Forall2_ignore1, Forall_forall in Hvars as (?&Hinblk&?); eauto; simpl in *.
        repeat (take (Forall _ blks) and eapply Forall_forall in it; eauto).
        eapply it4; eauto.
        + clear - Hinbrs Hinblk Hnd.
          unfold idcaus in *. rewrite map_app, 2 map_map in *.
          do 2 (eapply nodup_app_map_flat_map; eauto).
          eapply in_map_iff with (f:=snd); eauto. exists (c, blks); eauto.
          repeat rewrite flat_map_concat_map in *. rewrite map_map; auto.
        + etransitivity; [|eauto]. rewrite <-Hperm. eapply incl_concat; eauto.
        + intros ? Hin. eapply det_var_inv_filter; eauto using EqStN_weaken.
        + eapply EqStN_filter; eauto.
        + intros ? Hin Hdep. eapply det_var_inv_filter; eauto.
          eapply HSn; eauto.
          constructor. do 2 (eapply Exists_exists; do 2 esplit; eauto).
        + intros ? Hin Hdep. eapply HenvS; eauto.
          * eapply incl_map; [|eauto]. apply incl_map.
            intros ??. do 2 (apply in_flat_map; repeat esplit; eauto).
          * constructor. do 2 (eapply Exists_exists; do 2 esplit; eauto).
      - (* locals *)
        assert (In y (concat xs0)) as Hinxs0 by (rewrite <-H7; auto with datatypes).
        eapply in_concat in Hinxs0 as (?&Hin1&Hin2).
        eapply Forall2_ignore1, Forall_forall in H3 as (?&Hinblk&Hvars); eauto.
        eapply Forall_forall in H; eauto.
        assert (det_var_inv (env0 ++ locs) (S n) Hl1 Hl2 cy) as Hdet'.
        { eapply H; eauto.
          2,5-6:rewrite Forall_forall in *; try rewrite map_app; eauto.
          - clear - Hinblk Hnd. rewrite idcaus_app, app_assoc in Hnd. rewrite idcaus_app.
            unfold idcaus in *. rewrite map_app, map_map in *.
            eapply nodup_app_map_flat_map; eauto.
          - repeat rewrite idty_app; eauto.
          - etransitivity; eauto using incl_concat.
            rewrite <-H7, Permutation_app_comm, map_app.
            apply incl_app; [apply incl_appl|apply incl_appr]; eauto using incl_refl.
          - intros * Hin.
            rewrite idcaus_app, map_app in Hin.
            apply in_app_iff in Hin as [Hin|Hin].
            + assert (Hdet:=Hin). eapply Hn in Hdet.
              intros ??? Hin3 Hv1 Hv2. rewrite idcaus_app in Hin3.
              assert (In (x2, x1) (idcaus env0)) as Hin4.
              { eapply in_app_iff in Hin3 as [Hin3|Hin3]; eauto. exfalso.
                rewrite map_app in Hnd. eapply NoDup_app_In in Hnd; eauto.
                eapply Hnd. rewrite idcaus_app, map_app. apply in_or_app; auto.
                left; eapply in_map_iff; do 2 esplit; eauto. auto.
              }
              assert (~InMembers x2 locs); eauto.
              intro contra. eapply H5; eauto.
              eapply in_map_iff in Hin4 as ((?&(?&?)&?)&Heq&?); inv Heq.
              eapply in_map_iff. do 2 esplit; eauto; auto.
            + eapply Forall_forall in H17; eauto.
              intros ??? Hin3 Hv1 Hv2. rewrite idcaus_app in Hin3.
              eapply H17; eauto.
              eapply in_app_iff in Hin3 as [Hin3|Hin3]; auto. exfalso.
              rewrite map_app in Hnd. eapply NoDup_app_In in Hnd. 2:eapply in_map_iff; eauto.
              eapply Hnd. rewrite idcaus_app, map_app. apply in_or_app; auto.
          - rewrite idcaus_app. apply in_app_iff; auto.
          - intros ? _ Hdep ??? Hin Hv1 Hv2. rewrite idcaus_app in Hin.
            apply in_app_iff in Hin as [Hin|Hin].
            + assert (~InMembers x1 locs) as Hnin.
              { intro contra. eapply H5; eauto. eapply in_map_iff in Hin as ((?&(?&?)&?)&Heq&?); inv Heq.
                eapply in_map_iff. do 2 esplit; eauto; auto. }
              eapply HSn; eauto. eapply in_map_iff; do 2 esplit; eauto; auto.
              constructor; simpl. eapply Exists_exists; do 2 esplit; eauto.
              rewrite idcaus_app in Hdep; auto.
            + eapply Forall_forall in H18. 2:(eapply in_map_iff; do 2 esplit; eauto).
              eapply H18; eauto. eapply HenvS; eauto.
              eapply in_map_iff. do 2 esplit; eauto. rewrite idcaus_app, in_app_iff; auto.
              constructor; simpl. eapply Exists_exists; do 2 esplit; eauto.
              rewrite idcaus_app in Hdep; auto.
          - intros * Hin Hdep. apply HenvS.
            eapply incl_map; eauto. apply incl_map, incl_appr. intros ??; apply in_flat_map; eauto.
            constructor. eapply Exists_exists; do 2 esplit; eauto.
            rewrite idcaus_app in Hdep; auto.
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
        rewrite idcaus_app; eauto using in_or_app.
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
      - (* switch *)
        econstructor; eauto.
        do 2 (eapply Forall_forall; intros).
        repeat (take (Forall _ _) and eapply Forall_forall in it; eauto).
        eapply it; eauto.
        contradict Hnin.
        eapply incl_map; [|eauto]. apply incl_map.
        intros ??. do 2 (apply in_flat_map; repeat esplit; eauto).
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
        NoDup (map snd (idcaus env ++ idcaus (locals blk))) ->
        NoDupLocals (map fst env) blk ->
        VarsDefined blk xs ->
        incl xs (map fst env) ->
        (forall x, In x (map snd (idcaus env)) -> det_var_inv env n Hi1 Hi2 x) ->
        wt_block G (idty (idty env)) blk ->
        sem_block_det (S n) envS Hi1 Hi2 bs1 bs2 blk ->
        EqStN (S n) bs1 bs2 ->
        In (y, cy) (idcaus (locals blk)) ->
        (forall cx, In cx (map snd (idcaus env)) -> depends_on (idcaus env) cy cx blk -> det_var_inv env (S n) Hi1 Hi2 cx) ->
        (forall cx, In cx (map snd (idcaus (locals blk))) -> depends_on (idcaus env) cy cx blk -> In cx envS) ->
        sem_block_det (S n) (cy::envS) Hi1 Hi2 bs1 bs2 blk.
    Proof.
      induction blk as [(xs&es)| | |] using block_ind2;
        intros * HdetG Hnd Hnd2 Hvars Hincl Hn Hwt Hsem Hbs Hinenv HSn HenvS;
        inv Hnd2; inv Hvars; inv Hwt; inv Hsem; simpl in *.
      - (* equation *)
        inv Hinenv.
      - (* reset *)
        econstructor; eauto. intros k. specialize (H15 k).
        eapply Forall2_ignore2 in H4.
        rewrite Forall_forall in *; intros * Hinblk.
        destruct (in_dec ident_eq_dec cy (map snd (idcaus (locals x)))).
        2:eapply sem_block_det_cons_nIn; eauto.
        eapply in_map_iff in i as ((?&?)&?&?); subst.
        edestruct H4 as (?&Hinvars&Hvars'); eauto.
        assert (EqStN (S n) r1 r2) as Hrs.
        { eapply bools_of_detn. 2,3:eauto.
          eapply det_exp_S with (k0:=0) (n0:=n) in H5; eauto.
          - eapply H5 in H8; eauto.
          - rewrite <-length_typeof_numstreams, H7; simpl; lia.
          - intros ? Hfree. eapply HSn; eauto using Is_free_left_In_snd.
            eapply DepOnReset2; eauto.
            eapply Exists_exists; do 2 esplit; eauto.
            eapply In_Is_defined_in with (cenv:=idcaus env0); eauto using incl_refl, in_or_app.
            + eapply in_or_app; eauto. right. rewrite <-map_fst_idcaus.
              eapply in_map_iff. now do 2 esplit; eauto.
            + rewrite map_fst_idcaus. etransitivity; eauto using incl_concat.
        }
        { eapply H with (env:=env0); eauto.
          - clear - Hinblk Hnd.
            unfold idcaus in *. rewrite map_app, 2 map_map in *.
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
      - (* switch *)
        econstructor; eauto.
        do 2 (eapply Forall_forall; intros).
        repeat (take (Forall _ _) and eapply Forall_forall in it; eauto).
        destruct it2 as (?&Hinvar&Hperm).
        eapply Forall2_ignore2, Forall_forall in Hinvar as (?&?&?); eauto.
        destruct (in_dec ident_eq_dec cy (map snd (idcaus (locals x0)))).
        2:eapply sem_block_det_cons_nIn; eauto.
        eapply in_map_iff in i as ((?&?)&?&?); subst.
        eapply det_exp_S with (k:=0) (n0:=n) in H9; eauto. specialize (H9 H12); simpl in H9.
        2:{ rewrite <-length_typeof_numstreams, H6; auto. }
        2:{ intros ? Isf. eapply HSn; eauto using Is_free_left_In_snd.
            eapply DepOnSwitch2; eauto.
            do 2 (eapply Exists_exists; do 2 esplit; eauto).
            eapply In_Is_defined_in with (cenv:=idcaus env0); eauto using incl_refl, in_or_app.
            + eapply in_or_app; eauto. right. rewrite <-map_fst_idcaus.
              eapply in_map_iff. now do 2 esplit; eauto.
            + rewrite map_fst_idcaus. etransitivity; eauto using incl_concat.
              now rewrite Hperm. }
        repeat (take (wt_streams [_] (typeof ec)) and rewrite H6 in it; apply Forall2_singl in it).
        eapply it2; eauto.
        + clear - H0 H1 Hnd.
          unfold idcaus in *. rewrite map_app, 2 map_map in *.
          do 2 (eapply nodup_app_map_flat_map; eauto).
          eapply in_map_iff with (f:=snd); eauto.
          repeat rewrite flat_map_concat_map in *. rewrite map_map; auto.
        + etransitivity; [|eauto]. rewrite <-Hperm. eapply incl_concat; eauto.
        + intros ? Hin. eapply det_var_inv_filter; eauto using EqStN_weaken.
        + eapply EqStN_filter; eauto.
        + intros ? Hin Hdep. eapply det_var_inv_filter; eauto.
          eapply HSn; eauto.
          constructor. do 2 (eapply Exists_exists; do 2 esplit; eauto).
        + intros ? Hin Hdep. eapply HenvS; eauto.
          * eapply incl_map; [|eauto]. apply incl_map.
            intros ??. do 2 (apply in_flat_map; repeat esplit; eauto).
          * constructor. do 2 (eapply Exists_exists; do 2 esplit; eauto).
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
          * eapply Forall_impl_In; [|eapply H18]; intros ? Hin Hdet Hin'.
            inv Hin'; eauto.
            assert (In y (concat xs0)) as Hinvars.
            { rewrite <-H7. apply in_or_app; left. rewrite <-map_fst_idcaus.
              eapply in_map_iff. now do 2 esplit; eauto. }
            eapply in_concat in Hinvars as (xs'&?&Hinvars).
            eapply Forall2_ignore1, Forall_forall in H3 as (?&Hinblk&Hvars'); eauto.
            eapply det_var_inv_incl with (env':=env0 ++ locs). solve_incl_app.
            { eapply det_block_S with (envS:=envS); eauto.
              - clear - Hinblk Hnd. rewrite idcaus_app, app_assoc in Hnd. rewrite idcaus_app.
                unfold idcaus in *. rewrite map_app, map_map in *.
                eapply nodup_app_map_flat_map; eauto.
              - rewrite Forall_forall in *. eapply NoDupLocals_incl; [|eauto].
                rewrite map_app. reflexivity.
              - rewrite map_app.
                etransitivity; eauto using incl_concat.
                rewrite <-H7, Permutation_app_comm.
                apply incl_app; [apply incl_appl|apply incl_appr]; eauto using incl_refl.
              - intros * Hin'.
                rewrite idcaus_app, map_app in Hin'.
                apply in_app_iff in Hin' as [Hin'|Hin'].
                + assert (Hdet':=Hin'). eapply Hn in Hdet'.
                  intros ??? Hin3 Hv1 Hv2. rewrite idcaus_app in Hin3.
                  assert (In (x1, x0) (idcaus env0)) as Hin4.
                  { eapply in_app_iff in Hin3 as [Hin3|Hin3]; eauto. exfalso.
                    rewrite map_app in Hnd. eapply NoDup_app_In in Hnd; eauto.
                    eapply Hnd. rewrite idcaus_app, map_app. apply in_or_app; auto.
                    left; eapply in_map_iff; do 2 esplit; eauto. auto.
                  }
                  assert (~InMembers x1 locs) as Hnin.
                  { intro contra. eapply H5; eauto. eapply in_map_iff in Hin4 as ((?&(?&?)&?)&Heq&?); inv Heq.
                    eapply in_map_iff. do 2 esplit; eauto; auto. }
                  eapply Hdet'; eauto.
                + eapply Forall_forall in H17; eauto.
                  intros ??? Hin3 Hv1 Hv2. rewrite idcaus_app in Hin3.
                  eapply H17; eauto.
                  eapply in_app_iff in Hin3 as [Hin3|Hin3]; auto. exfalso.
                  rewrite map_app in Hnd. eapply NoDup_app_In in Hnd. 2:eapply in_map_iff; eauto.
                  eapply Hnd. rewrite idcaus_app, map_app. apply in_or_app; auto.
              - eapply Forall_forall in H6; eauto.
                repeat rewrite idty_app; auto.
              - rewrite Forall_forall in *; eauto.
              - rewrite idcaus_app. apply in_app_iff; auto.
              - intros ? _ Hdep ??? Hin' Hv1 Hv2. rewrite idcaus_app in Hin'.
                apply in_app_iff in Hin' as [Hin'|Hin'].
                + assert (~InMembers x0 locs) as Hnin.
                  { intro contra. eapply H5; eauto. eapply in_map_iff in Hin' as ((?&(?&?)&?)&Heq&?); inv Heq.
                    eapply in_map_iff. do 2 esplit; eauto; auto. }
                  eapply HSn; eauto. eapply in_map_iff; do 2 esplit; eauto; auto.
                  constructor; simpl. eapply Exists_exists; do 2 esplit; eauto.
                  rewrite idcaus_app in Hdep; auto.
                + eapply Forall_forall in H18. 2:(eapply in_map_iff; do 2 esplit; eauto).
                  eapply H18; eauto. eapply HenvS; eauto.
                  eapply in_map_iff. do 2 esplit; eauto. rewrite idcaus_app, in_app_iff; auto.
                  constructor; simpl. eapply Exists_exists; do 2 esplit; eauto.
                  rewrite idcaus_app in Hdep; auto.
              - intros * Hin' Hdep. eapply HenvS; eauto.
                2:constructor; eapply Exists_exists; eauto.
                rewrite idcaus_app, map_app, in_app_iff. right.
                eapply incl_map; eauto. apply incl_map. intros ??. apply in_flat_map; eauto.
                rewrite idcaus_app in Hdep; eauto.
            }
        + (* deeper *)
          eapply Forall2_ignore2 in H3; eauto.
          econstructor; eauto.
          * rewrite Forall_forall in *; intros * Hinblk.
            destruct (in_dec ident_eq_dec cy (map snd (idcaus (locals x)))).
            2:eapply sem_block_det_cons_nIn; eauto.
            { edestruct H3 as (?&Hinvars&Hvars'); eauto.
              eapply in_map_iff in i as ((?&?)&?&?); subst.
              eapply H with (env:=env0++locs); eauto.
              2,3:rewrite map_app; eauto.
              - clear - Hinblk Hnd. rewrite idcaus_app, app_assoc in Hnd. rewrite idcaus_app.
                unfold idcaus in *. rewrite map_app, map_map in *.
                eapply nodup_app_map_flat_map; eauto.
              - etransitivity; eauto using incl_concat.
                rewrite <-H7, Permutation_app_comm.
                apply incl_app; [apply incl_appl|apply incl_appr]; eauto using incl_refl.
              - intros * Hin.
                rewrite idcaus_app, map_app in Hin.
                apply in_app_iff in Hin as [Hin|Hin].
                + assert (Hdet:=Hin). eapply Hn in Hdet.
                  intros ??? Hin3 Hv1 Hv2. rewrite idcaus_app in Hin3.
                  assert (In (x2, x1) (idcaus env0)) as Hin4.
                  { eapply in_app_iff in Hin3 as [Hin3|Hin3]; eauto. exfalso.
                    rewrite map_app in Hnd. eapply NoDup_app_In in Hnd; eauto.
                    eapply Hnd. rewrite idcaus_app, map_app. apply in_or_app; auto.
                    left; eapply in_map_iff; do 2 esplit; eauto. auto.
                  }
                  assert (~InMembers x2 locs) as Hnin.
                  { intro contra. eapply H5; eauto. eapply in_map_iff in Hin4 as ((?&(?&?)&?)&Heq&?); inv Heq.
                    eapply in_map_iff. do 2 esplit; eauto; auto. }
                  eapply Hdet; eauto.
                + intros ??? Hin3 Hv1 Hv2. rewrite idcaus_app in Hin3.
                  eapply H17; eauto.
                  eapply in_app_iff in Hin3 as [Hin3|Hin3]; auto. exfalso.
                  rewrite map_app in Hnd. eapply NoDup_app_In in Hnd. 2:eapply in_map_iff; eauto.
                  eapply Hnd. rewrite idcaus_app, map_app. apply in_or_app; auto.
              - rewrite 2 idty_app; eauto.
              - intros ? _ Hdep ??? Hin Hv1 Hv2. rewrite idcaus_app in Hin.
                apply in_app_iff in Hin as [Hin|Hin].
                + assert (~InMembers x1 locs) as Hnin.
                  { intro contra. eapply H5; eauto. eapply in_map_iff in Hin as ((?&(?&?)&?)&Heq&?); inv Heq.
                    eapply in_map_iff. do 2 esplit; eauto; auto. }
                  eapply HSn; eauto. eapply in_map_iff; do 2 esplit; eauto; auto.
                  constructor; simpl. eapply Exists_exists; do 2 esplit; eauto.
                  rewrite idcaus_app in Hdep; auto.
                + eapply H18; eauto. eapply in_map_iff; now do 2 esplit; eauto.
                  eapply HenvS; eauto. rewrite idcaus_app, map_app, in_app_iff; left.
                  eapply in_map_iff. now do 2 esplit; eauto.
                  constructor; simpl. eapply Exists_exists; do 2 esplit; eauto.
                  rewrite idcaus_app in Hdep; auto.
              - intros * Hin Hdep. apply HenvS.
                eapply incl_map; eauto. apply incl_map, incl_appr. intros ??; apply in_flat_map; eauto.
                constructor. eapply Exists_exists; do 2 esplit; eauto.
                rewrite idcaus_app in Hdep; auto.
            }
          * eapply Forall_impl_In; [|eapply H18]; intros ? Hin Hdet Hin'.
            inv Hin'; eauto. exfalso. clear - Hnd Hinenv Hin.
            rewrite idcaus_app, 2 map_app in Hnd.
            eapply NoDup_app_r, NoDup_app_In in Hnd; eauto.
            eapply Hnd, in_map_iff. now do 2 esplit; eauto.
    Qed.

    Lemma det_vars_n :
      forall nd n Hi1 Hi2 bs1 bs2,
        det_nodes G ->
        wt_node G nd ->
        node_causal nd ->
        EqStN n bs1 bs2 ->
        sem_block G Hi1 bs1 (n_block nd) ->
        sem_block G Hi2 bs2 (n_block nd) ->
        Forall (det_var_inv (n_in nd ++ n_out nd) n Hi1 Hi2) (map snd (idcaus (n_in nd))) ->
        Forall (det_var_inv (n_in nd ++ n_out nd) n Hi1 Hi2) (map snd (idcaus (n_in nd ++ n_out nd))).
    Proof.
      intros * HdetG Hwtn Hcaus Hbs Hsem1 Hsem2 Hins.

      assert (sem_block_det n (map snd (idcaus (n_in nd ++ n_out nd ++ locals (n_block nd)))) Hi1 Hi2 bs1 bs2 (n_block nd) /\
              Forall (fun x => In x (map snd (idcaus (n_in nd ++ n_out nd))) ->
                            det_var_inv (n_in nd ++ n_out nd) n Hi1 Hi2 x)
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

        eapply node_causal_ind; eauto.
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
            apply in_map_iff in Hin as ((?&(?&?)&?)&Heq&?); inv Heq; eauto.
            eapply det_block_S; eauto.
            -- rewrite map_app; auto.
            -- eapply node_NoDupLocals.
            -- rewrite Hperm. solve_incl_app.
            -- intros ??.
               eapply Forall_forall in Hvars; eauto.
               rewrite app_assoc, idcaus_app, map_app, in_app_iff; auto.
            -- destruct Hwtn as (?&?&?&?); auto.
            -- rewrite Hperm.
               eapply in_map_iff; do 2 esplit; eauto.
            -- rewrite idcaus_app, in_app_iff; auto.
               right. eapply in_map_iff; do 2 esplit; eauto; auto.
            -- intros ???.
               eapply Forall_forall in Hvars'; eauto.
          * pose proof (n_defd nd) as (?&Hdef&Hperm).
            eapply in_map_iff in Hin as ((?&?)&?&?); subst.
            eapply sem_block_det_cons_In; eauto.
            -- rewrite map_app; auto.
            -- eapply node_NoDupLocals.
            -- rewrite Hperm. solve_incl_app.
            -- intros ? Hin'. eapply Forall_forall in Hvars; eauto.
               rewrite app_assoc, idcaus_app, map_app, in_app_iff; auto.
            -- destruct Hwtn as (?&?&?&?); auto.
            -- intros ? Hin' Hdep'.
               eapply Forall_forall in Hvars'; eauto.
          * exfalso. eapply NoDup_app_In in Hnd; eauto.
    Qed.

  End sem_block_det.

  Lemma det_global_n {PSyn prefs} : forall (G : @global PSyn prefs),
      wt_global G ->
      Forall node_causal (nodes G) ->
      det_nodes G.
  Proof.
    intros (enms&nds).
    induction nds as [|nd nds]; intros Hwt Hcaus ?????? Heqins Hs1 Hs2;
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

      assert (Forall (det_var_inv (n_in n1 ++ n_out n1) n H H0) (map snd (idcaus (n_in n1)))) as Hins.
      { eapply node_causal_NoDup in H1 as Hnd.
        clear - Heqins Hins1 Hins2 Hnd.
        assert (incl (idcaus (n_in n1)) (idcaus (n_in n1 ++ n_out n1))) as Hincl.
        { rewrite idcaus_app. solve_incl_app. }
        revert ins1 ins2 Hins1 Hins2 Heqins Hnd Hincl.
        generalize (n_in n1 ++ n_out n1) as cenv.
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
      + inv Hwt; inv H4. eapply IHnds; eauto. split; eauto.
      + inv Hwt; inv H4. destruct H7; auto.
      + eapply clocks_of_EqStN; eauto.
    - rewrite find_node_other in Hfind1; auto.
      eapply IHnds; eauto. inv Hwt; inv H4; split; auto.
      1,2:econstructor; eauto.
      1,2:eapply sem_block_cons; eauto using wl_global_Ordered_nodes.
      1,2:eapply find_node_later_not_Is_node_in; eauto using wl_global_Ordered_nodes.
  Qed.

  Theorem det_global {PSyn prefs} : forall (G: @global PSyn prefs) f ins outs1 outs2,
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
       (Syn   : LSYNTAX Ids Op OpAux Cks)
       (Typ   : LTYPING Ids Op OpAux Cks Syn)
       (LCA   : LCAUSALITY Ids Op OpAux Cks Syn)
       (Lord  : LORDERED Ids Op OpAux Cks Syn)
       (CStr  : COINDSTREAMS Ids Op OpAux Cks)
       (Sem   : LSEMANTICS Ids Op OpAux Cks Syn Lord CStr)
<: LSEMDETERMINISM Ids Op OpAux Cks Syn Typ LCA Lord CStr Sem.
  Include LSEMDETERMINISM Ids Op OpAux Cks Syn Typ LCA Lord CStr Sem.
End LSemDeterminismFun.
