From Coq Require Import String Morphisms.
From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Velus Require Import Common.
From Velus Require Import CommonList.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import CoindStreams.
From Velus Require Import Clocks.
From Velus Require Import Lustre.StaticEnv.
From Velus Require Import Lustre.LSyntax Lustre.LTyping Lustre.LCausality Lustre.LOrdered Lustre.LSemantics.

From Cpo Require Import Cpo_streams_type Systems.
Require Import SDfuns.
Require Import Denot.
Require Import Infty.
Require Import Cpo_ext.

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
       (* (Import Sem   : LSEMANTICS Ids Op OpAux Cks Senv Syn Lord CStr) *)
       (Import Den   : LDENOT     Ids Op OpAux Cks Senv Syn Lord CStr).


  Import List.

  (* (** Induction hypothesis over the program *) *)
  (* Definition det_nodes {PSyn prefs} (G : @global PSyn prefs) := forall f n ins1 ins2 outs1 outs2, *)
  (*     Forall2 (EqStN n) ins1 ins2 -> *)
  (*     sem_node G f ins1 outs1 -> *)
  (*     sem_node G f ins2 outs2 -> *)
  (*     Forall2 (EqStN n) outs1 outs2. *)

  (* Lemma det_nodes_ins {PSyn prefs} : forall (G : @global PSyn prefs) f ins outs1 outs2, *)
  (*     det_nodes G -> *)
  (*     sem_node G f ins outs1 -> *)
  (*     sem_node G f ins outs2 -> *)
  (*     EqSts outs1 outs2. *)
  (* Proof. *)
  (*   intros * Hdet Hsem1 Hsem2. *)
  (*   eapply EqStN_EqSts; intros. *)
  (*   eapply Hdet. 2,3:eauto. *)
  (*   eapply Forall2_same, Forall_forall; intros. reflexivity. *)
  (* Qed. *)

  Section sem_equation_det.
    Context {PSyn : block -> Prop}.
    Context {prefs : PS.t}.
    Variable (G : @global PSyn prefs).

    (* Hypothesis HdetG : det_nodes G. *)

    Variable Γ : static_env.

    Definition inf_var_inv n (env : DS_prod SI) : ident -> Prop :=
      fun cx => forall x,
          (HasCaus Γ x cx ->
           is_cons (nrem n (env x))).

    Definition inf_exp_inv n env bs : exp -> nat -> Prop :=
      fun e k =>
        wt_exp G Γ e ->
        is_cons (nrem n (get_nth (denot_exp e env bs) k)).

    Lemma P_exps_inf_exp_inv : forall n env bs es k,
        Forall (wt_exp G Γ) es ->
        P_exps (inf_exp_inv n env bs) es k ->
        is_cons (nrem n (get_nth (denot_exps es env bs) k)).
    Proof.
      induction es as [| e es]; intros * Hwt Hp; inv Hwt; simpl. inv Hp.
      inv Hp.
      - (* now *)
        setoid_rewrite denot_exps_eq.
        rewrite nprod_app_nth1; auto.
      - (* later *)
        setoid_rewrite denot_exps_eq.
        rewrite nprod_app_nth2; auto.
    Qed.

    (* Lemma Forall2Brs_det_exp_inv : forall n H1 H2 bs1 bs2 es k ss1 ss2, *)
    (*     k < length ss1 -> *)
    (*     Forall (fun es => Forall (wt_exp G Γ) (snd es)) es -> *)
    (*     Forall (fun es => P_exps (det_exp_inv n H1 H2 bs1 bs2) (snd es) k) es -> *)
    (*     Forall2Brs (sem_exp G H1 bs1) es ss1 -> *)
    (*     Forall2Brs (sem_exp G H2 bs2) es ss2 -> *)
    (*     Forall2 (fun xs1 xs2 => EqStN n (snd xs1) (snd xs2)) (nth k ss1 []) (nth k ss2 []). *)
    (* Proof. *)
    (*   induction es; intros * Hlen Hwt Hp Hsem1 Hsem2; *)
    (*     inv Hwt; inv Hsem1; inv Hsem2; simpl; inv Hp. *)
    (*   { eapply Forall_forall in H; [|eapply nth_In]. rewrite H. 2:auto. *)
    (*     destruct (Compare_dec.dec_lt k (length ss2)). *)
    (*     eapply Forall_forall in H0; [|eapply nth_In]. rewrite H0. 2:auto. constructor. *)
    (*     erewrite nth_overflow; auto. lia. *)
    (*   } *)
    (*   eapply P_exps_det_exp_inv in H9 as Heq1. 3:eauto. 2,3:eauto. *)
    (*   eapply IHes in H11 as Heq2. 3-5:eauto. *)
    (*   2:{ eapply Forall3_length in H8 as (?&?). congruence. } *)
    (*   assert (length (concat vs1) = length (concat vs0)) as Hlen0. *)
    (*   { eapply sem_exps_numstreams in H5; eauto with ltyping. *)
    (*     eapply sem_exps_numstreams in H9; eauto with ltyping. congruence. } *)
    (*   clear - Hlen Hlen0 H8 H12 Heq1 Heq2. *)
    (*   eapply Forall3_forall3 in H8 as (?&?&?). *)
    (*   eapply Forall3_forall3 in H12 as (?&?&?). *)
    (*   erewrite H1 at 1; try reflexivity. *)
    (*   erewrite H4; try reflexivity. *)
    (*   constructor; eauto. *)
    (*   1,2:congruence. *)
    (* Qed. *)

    Section Forall_Nprod.

      Variable P : DS (sampl value) -> Prop.

      Definition forall_nprod {n} (np : nprod n) : Prop.
        induction n as [|[]]; simpl in *.
        - exact True.
        - exact (P np).
        - exact (P (fst np) /\ IHn (snd np)).
      Defined.

      Lemma forall_nprod_skip :
        forall {n} (np : nprod (S n)),
          forall_nprod np ->
          forall_nprod (nprod_skip np).
      Proof.
        intros * Hnp.
        destruct n.
        - now simpl.
        - destruct Hnp. auto.
      Qed.

      Lemma forall_nprod_k :
        forall {n} (np : nprod n),
          (forall k, k < n -> P (get_nth np k)) ->
          forall_nprod np.
      Proof.
        induction n as [|[]]; intros * Hk.
        - constructor.
        - apply (Hk O); auto.
        - split.
          + apply (Hk O); auto with arith.
          + apply IHn; intros.
            change (snd np) with (nprod_skip np).
            rewrite get_nth_skip; auto with arith.
      Qed.

      Lemma forall_nprod_k' :
        forall {n} (np : nprod n),
          forall_nprod np ->
          (forall k, k < n -> P (get_nth np k)).
      Proof.
        induction n as [|[]]; intros * Hk.
        - lia.
        - intros.
          assert (k = O) by lia; subst.
          now simpl in Hk.
        - intros.
          specialize (IHn (nprod_skip np)).
          setoid_rewrite get_nth_skip in IHn.
          destruct k. { destruct Hk; auto. }
          apply IHn; auto using forall_nprod_skip with arith.
      Qed.

      (* Lemma forall_nprod_Oeq_compat : *)
      (*   forall {n} (np np' : nprod n), *)
      (*     np == np' -> *)
      (*     forall_nprod np <-> forall_nprod np'. *)
      (* Proof. *)
      (*   intros * Heq. *)
      (*   split; intro Hf. *)
      (*   - apply forall_nprod_k; intros. *)
      (*     rewrite <- Heq. *)
      (*     auto using forall_nprod_k'. *)
      (*   - apply forall_nprod_k; intros. *)
      (*     rewrite Heq. *)
      (*     auto using forall_nprod_k'. *)
      (* Qed. *)

      (* Add Parametric Morphism {n} : forall_nprod *)
      (*     with signature (@Oeq (nprod n)) ==> iff as forall_nprod_compat_morph. *)
      (* Proof. *)
      (*   exact (forall_nprod_Oeq_compat). *)
      (* Qed. *)

      Lemma forall_nprod_app :
        forall {n m} (np : nprod n) (mp : nprod m),
          forall_nprod np ->
          forall_nprod mp ->
          forall_nprod (nprod_app np mp).
      Proof.
        intros * Hnp Hmp.
        apply forall_nprod_k.
        intros * Hk.
        destruct (Nat.lt_ge_cases k n).
        - rewrite nprod_app_nth1; auto using forall_nprod_k'.
        - rewrite nprod_app_nth2; auto.
          apply forall_nprod_k'; auto; lia.
      Qed.

    End Forall_Nprod.

    Lemma numstreams_annots :
      forall es, list_sum (map numstreams es) = length (annots es).
    Proof.
      induction es; simpl; auto.
      rewrite app_length; f_equal; auto.
      rewrite <- length_typeof_numstreams, typeof_annot.
      now rewrite map_length.
    Qed.

    Lemma P_exps_inf_exp_inv_all : forall n env bs es,
        Forall (wt_exp G Γ) es ->
        (forall k, k < length (annots es) -> P_exps (inf_exp_inv n env bs) es k) ->
        forall_nprod (fun s => is_cons (nrem n s)) (denot_exps es env bs).
    Proof.
      intros * Hwt Hks.
      rewrite <- numstreams_annots in Hks.
      induction es; simpl; auto.
      apply forall_nprod_k.
      intros.
      eapply P_exps_inf_exp_inv in Hks; eauto.
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
      { specialize (Heq O). eapply Forall2_length in Heq.
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

    (* Lemma lift2_detn : forall n op ty1 ty2 xs11 xs12 xs21 xs22 ys1 ys2, *)
    (*     EqStN n xs11 xs21 -> *)
    (*     EqStN n xs12 xs22 -> *)
    (*     lift2 op ty1 ty2 xs11 xs12 ys1 -> *)
    (*     lift2 op ty1 ty2 xs21 xs22 ys2 -> *)
    (*     EqStN n ys1 ys2. *)
    (* Proof. *)
    (*   induction n; intros * Heq1 Heq2 Hl1 Hl2; auto. *)
    (*   inv Heq1; inv Heq2; inv Hl1; inv Hl2; constructor; eauto. *)
    (*   rewrite H6 in H8. now inv H8. *)
    (* Qed. *)

    (* Corollary fby_detn : forall n xs1 xs2 ys1 ys2 zs1 zs2, *)
    (*     EqStN n xs1 xs2 -> *)
    (*     EqStN n ys1 ys2 -> *)
    (*     fby xs1 ys1 zs1 -> *)
    (*     fby xs2 ys2 zs2 -> *)
    (*     EqStN n zs1 zs2. *)
    (* Proof. *)
    (*   induction n; intros * Heq1 Heq2 Hfby1 Hfby2; inv Heq1; inv Heq2; *)
    (*     inv Hfby1; inv Hfby2; constructor; auto. eauto. *)
    (*   clear IHn. revert y xs0 xs1 xs3 xs2 rs rs0 H1 H2 H6 H7. *)
    (*   induction n; intros * Heq1 Heq2 Hfby1 Hfby2; inv Heq1; inv Heq2; *)
    (*     inv Hfby1; inv Hfby2; constructor; eauto. *)
    (* Qed. *)

    (* Lemma arrow_detn : forall n xs1 xs2 ys1 ys2 zs1 zs2, *)
    (*     EqStN n xs1 xs2 -> *)
    (*     EqStN n ys1 ys2 -> *)
    (*     arrow xs1 ys1 zs1 -> *)
    (*     arrow xs2 ys2 zs2 -> *)
    (*     EqStN n zs1 zs2. *)
    (* Proof. *)
    (*   induction n; intros * Heq1 Heq2 Hfby1 Hfby2; inv Heq1; inv Heq2; *)
    (*     inv Hfby1; inv Hfby2; constructor; auto. eauto. *)
    (*   clear IHn. revert xs0 xs1 xs3 xs2 rs rs0 H1 H2 H6 H7. *)
    (*   induction n; intros * Heq1 Heq2 Hfby1 Hfby2; inv Heq1; inv Heq2; *)
    (*     inv Hfby1; inv Hfby2; constructor; eauto. *)
    (* Qed. *)

    (* Lemma when_detn : forall n k xs1 xs2 ys1 ys2 zs1 zs2, *)
    (*     EqStN n xs1 xs2 -> *)
    (*     EqStN n ys1 ys2 -> *)
    (*     when k xs1 ys1 zs1 -> *)
    (*     when k xs2 ys2 zs2 -> *)
    (*     EqStN n zs1 zs2. *)
    (* Proof. *)
    (*   induction n; intros * Heq1 Heq2 Hwhen1 Hwhen2; inv Heq1; inv Heq2; auto. *)
    (*   inv Hwhen1; inv Hwhen2; constructor; eauto. *)
    (*   1,2:congruence. *)
    (* Qed. *)

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
            simpl_Exists; subst; eauto using In_InMembers.
          * exfalso. destruct y, H2; subst; simpl in *.
            eapply H4. rewrite fst_InMembers, <-fst_InMembers.
            simpl_Exists; subst; eauto using In_InMembers.
        + eapply IHn. 6,7:eauto. 1-5:intros; eauto.
          erewrite 2 map_map, map_ext with (l:=xss1), map_ext with (l:=xss2); eauto; intros (?&?); auto.
          erewrite fst_NoDupMembers, map_map, map_ext, <-fst_NoDupMembers; eauto; intros (?&?); auto.
          (rewrite Forall2_map_1, Forall2_map_2; eapply Forall2_impl_In; [|eauto];
           intros (?&?) (?&?) _ _ Heq; inv Heq; simpl in *; subst; auto).
          eapply option_map_inv in H as (?&?&?); subst.
          eapply option_map_inv in H0 as (?&?&?); subst.
          specialize (Heq3 _ _ eq_refl eq_refl). inv Heq3; auto.
      - exfalso. simpl_Exists.
        eapply In_InMembers, fst_InMembers in Hin. rewrite Hfst in Hin.
        eapply fst_InMembers, InMembers_In in Hin as (?&Hin).
        unshelve simpl_Forall; eauto.
      - exfalso. simpl_Exists.
        eapply In_InMembers, fst_InMembers in Hin. rewrite <-Hfst in Hin.
        eapply fst_InMembers, InMembers_In in Hin as (?&Hin).
        unshelve simpl_Forall; eauto.
      - econstructor; eauto.
        + specialize (Heq3 _ _ eq_refl eq_refl). inv Heq3; auto.
        + eapply IHn. 6,7:eauto. 1-5:intros; eauto.
          erewrite 2 map_map, map_ext with (l:=xss1), map_ext with (l:=xss2); eauto; intros (?&?); auto.
          erewrite fst_NoDupMembers, map_map, map_ext, <-fst_NoDupMembers; eauto; intros (?&?); auto.
          (rewrite Forall2_map_1, Forall2_map_2; eapply Forall2_impl_In; [|eauto];
           intros (?&?) (?&?) _ _ Heq; inv Heq; simpl in *; subst; auto).
          inv H. inv H0.
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

    (* Fact det_exps_n' : forall n Hi1 Hi2 bs1 bs2 es ss1 ss2, *)
    (*     Forall (fun e => forall ss1 ss2, *)
    (*                 wt_exp G Γ e -> *)
    (*                 sem_exp G Hi1 bs1 e ss1 -> *)
    (*                 sem_exp G Hi2 bs2 e ss2 -> *)
    (*                 Forall2 (EqStN n) ss1 ss2) es -> *)
    (*     Forall (wt_exp G Γ) es-> *)
    (*     Forall2 (sem_exp G Hi1 bs1) es ss1 -> *)
    (*     Forall2 (sem_exp G Hi2 bs2) es ss2 -> *)
    (*     Forall2 (EqStN n) (concat ss1) (concat ss2). *)
    (* Proof. *)
    (*   intros * Hf. revert ss1 ss2. *)
    (*   induction Hf; intros * Hwt Hsem1 Hsem2; *)
    (*     inv Hwt; inv Hsem1; inv Hsem2; simpl; auto. *)
    (*   apply Forall2_app; eauto. *)
    (* Qed. *)

    (* Lemma Forall2Brs_det_exp_n' : forall n H1 H2 bs1 bs2 es ss1 ss2, *)
    (*     Forall *)
    (*       (fun es => *)
    (*          Forall *)
    (*            (fun e => *)
    (*               forall ss1 ss2, *)
    (*                 wt_exp G Γ e -> *)
    (*                 sem_exp G H1 bs1 e ss1 -> sem_exp G H2 bs2 e ss2 -> Forall2 (EqStN n) ss1 ss2) *)
    (*            (snd es)) es -> *)
    (*     length ss1 = length ss2 -> *)
    (*     Forall (fun es => Forall (wt_exp G Γ) (snd es)) es -> *)
    (*     Forall2Brs (sem_exp G H1 bs1) es ss1 -> *)
    (*     Forall2Brs (sem_exp G H2 bs2) es ss2 -> *)
    (*     Forall2 (Forall2 (fun xs1 xs2 => EqStN n (snd xs1) (snd xs2))) ss1 ss2. *)
    (* Proof. *)
    (*   induction es; intros * Hf Hlen Hwt Hsem1 Hsem2; *)
    (*     inv Hf; inv Hwt; inv Hsem1; inv Hsem2; simpl. *)
    (*   - revert ss2 Hlen H0. *)
    (*     induction H; intros * Hl Hf2; destruct ss2; simpl in *; try congruence; inv Hf2. *)
    (*     1,2:constructor; eauto. *)
    (*   - eapply IHes in H4. 3-5:eauto. clear IHes. *)
    (*     2:{ eapply Forall3_length in H10 as (?&?). eapply Forall3_length in H14 as (?&?). *)
    (*         congruence. *)
    (*     } *)
    (*     eapply det_exps_n' in H3; eauto. *)
    (*     clear - H3 H4 H10 H14. revert vs2 vs3 H10 H14 H3 H4. *)
    (*     generalize (concat vs0) (concat vs1); clear vs0 vs1. *)
    (*     intros * Hf1. revert l ss2 vs3. *)
    (*     induction Hf1; intros * Hf2 Heq1 Heq2; inv Heq1; inv Heq2; inv Hf2; constructor; eauto. *)
    (* Qed. *)

    (** The clocking hypothesis could be replaced with a typing one.
        The important point is that all the variables appearing in the expression
        are in `env`.
        I chose a clocking hypothesis because this lemma is used in the
        clocked-semantics proof. *)
    Lemma inf_exp_n : forall n env bs e,
        (forall x cx, HasCaus Γ x cx \/ HasLastCaus Γ x cx -> inf_var_inv n env cx) ->
        wt_exp G Γ e ->
        restr_exp e ->
        is_cons (nrem n bs) ->
        forall_nprod (fun s => is_cons (nrem n s)) (denot_exp e env bs).
    Proof.
      (* intros * Hn Hbs. revert ss1 ss2. *)
      induction e using exp_ind2; intros * Hn Hwt Hr Hb; inv Hr; inv Hwt.
      - (* const *)
        rewrite denot_exp_eq.
        apply is_consn_sconst; auto.
      - (* var *)
        rewrite denot_exp_eq.
        inv H1.
        eapply Hn; eauto. left.
        all: econstructor; solve_In; eauto.
      - (* unop *)
        rewrite denot_exp_eq; simpl.
        cases; try congruence; inv H4. (* typeof *)
        assert (forall_nprod (fun s => is_cons (nrem n s)) (denot_exp e env0 bs)) as He by auto.
        revert He.
        generalize (denot_exp e env0 bs).
        generalize (numstreams e).
        intros ns t Ht.
        cases; auto using is_consn_DS_const. (* numstreams *)
        apply is_consn_sunop; auto.
      - (* fby *)
        rewrite denot_exp_eq; simpl.
        unfold eq_rect_r, eq_rect.
        cases.
        2,3: apply forall_nprod_k; intros; rewrite get_nth_const; auto using is_consn_DS_const.
    (* TODO: un lemme pour ça : *)
        assert (forall_nprod (fun s => is_cons (nrem n s)) (denot_exps e0s env0 bs)) as He0s.
        { clear dependent es. clear H9.
          induction e0s; simpl in *; auto; simpl_Forall.
          setoid_rewrite denot_exps_eq; auto using forall_nprod_app.
        }
        assert (forall_nprod (fun s => is_cons (nrem n s)) (denot_exps es env0 bs)) as Hes.
        { clear dependent e0s. clear H8.
          induction es; simpl in *; auto; simpl_Forall.
          setoid_rewrite denot_exps_eq; auto using forall_nprod_app.
        }
        clear - He0s Hes e.
        revert He0s Hes.
        generalize ((denot_exps e0s env0 bs)), ((denot_exps es env0 bs)).
        rewrite e.
        generalize (list_sum (map numstreams es)).
        intro i.
        induction i as [|[]]; auto; intros s0s ss Hs0s Hss.
        + simpl in *. auto using is_consn_fby.
        + destruct s0s, ss, Hs0s, Hss.
          setoid_rewrite lift2_simpl.
          split.
          simpl; auto using is_consn_fby.
          now apply IHi.
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
      + intros * _ ???.
        split; intros; eapply EqStN_EqSt, sem_var_det; eauto.
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
      + intros * _ ???.
        split; intros; eapply EqStN_EqSt, sem_var_det; eauto.
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
        (forall x cx, HasCaus Γ x cx \/ HasLastCaus Γ x cx -> det_var_inv n Hi1 Hi2 cx) ->
        wt_exp G Γ e ->
        k < numstreams e ->
        EqStN (S n) bs1 bs2 ->
        (forall x, Is_free_left Γ x k e -> det_var_inv (S n) Hi1 Hi2 x) ->
        det_exp_inv (S n) Hi1 Hi2 bs1 bs2 e k.
    Proof.
      intros * Hn Hwt Hnum Hbs HSn.
      eapply exp_causal_ind
        with (P_exp:=det_exp_inv (S n) Hi1 Hi2 bs1 bs2); eauto with ltyping.
      1-12:clear Hwt HSn.
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
        inversion_clear Hs1 as [| | | |???????? Hse1 Hty1 Hl1| | | | | | | |].
        inversion_clear Hs2 as [| | | |???????? Hse2 Hty2 Hl2| | | | | | | |].
        rewrite Hty2 in Hty1; inv Hty1.
        eapply He1 in Hse2; eauto. simpl in *.
        eapply lift1_detn; eauto.
      - (* binop *)
        intros ???? He1 He2 ?? Hwt Hs1 Hs2. inv Hwt.
        inversion_clear Hs1 as [| | | | |??????????? Hse11 Hse12 Hty11 Hty12 Hl1| | | | | | |].
        inversion_clear Hs2 as [| | | | |??????????? Hse21 Hse22 Hty21 Hty22 Hl2| | | | | | |].
        rewrite Hty21 in Hty11; inv Hty11. rewrite Hty22 in Hty12; inv Hty12.
        eapply He1 in Hse21; eauto. eapply He2 in Hse22; eauto. simpl in *.
        eapply lift2_detn. 3,4:eauto. 1,2:eauto.
      - (* fby *)
        intros ???? Hk He0s ?? Hwt Hs1 Hs2. inv Hwt.
        inversion_clear Hs1 as [| | | | | |???????? Hse11 Hse12 Hfby1| | | | | |].
        inversion_clear Hs2 as [| | | | | |???????? Hse21 Hse22 Hfby2| | | | | |].
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
          eapply Forall3_length in Hfby1 as (Hl1&Hl2). rewrite <-Hl1, Hlen1; eauto.
        + eapply Forall3_forall3 in Hfby1 as (_&_&Hfby1).
          eapply Hfby1 with (b:=def_stream); eauto. congruence.
        + eapply Forall3_forall3 in Hfby2 as (_&_&Hfby2).
          eapply Hfby2 with (b:=def_stream); eauto. congruence.
      - (* arrow *)
        intros ???? Hk He0s He1s ?? Hwt Hs1 Hs2. inv Hwt.
        inversion_clear Hs1 as [| | | | | | |???????? Hse11 Hse12 Harrow1| | | | |].
        inversion_clear Hs2 as [| | | | | | |???????? Hse21 Hse22 Harrow2| | | | |].
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
        intros ?????? Hk Hes Hin Hvar ?? Hwt Hs1 Hs2. inv Hwt. simpl in *.
        inversion_clear Hs1 as [| | | | | | | |????????? Hse1 Hsv1 Hwhen1| | | |].
        inversion_clear Hs2 as [| | | | | | | |????????? Hse2 Hsv2 Hwhen2| | | |].
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
        inversion_clear Hs1 as [| | | | | | | | |????????? Hsv1 Hse1 Hmerge1| | |].
        inversion_clear Hs2 as [| | | | | | | | |????????? Hsv2 Hse2 Hmerge2| | |].
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
          inversion_clear Hs1 as [| | | | | | | | | |????????? Hsv1 Hse1 Hcase1| |].
          inversion_clear Hs2 as [| | | | | | | | | |????????? Hsv2 Hse2 Hcase2| |].
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
          { eapply sem_exp_numstreams in Hs1; eauto with ltyping. }
          assert (length ss2 = length (typesof d0)) as Hlen2.
          { eapply sem_exp_numstreams in Hs2; eauto with ltyping. }
          inversion_clear Hs1 as [| | | | | | | | | | |?????????? Hsv1 _ Hse1 Hd1 Hcase1|].
          inversion_clear Hs2 as [| | | | | | | | | | |?????????? Hsv2 _ Hse2 Hd2 Hcase2|].
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
        inversion_clear Hsem1 as [| | | | | | | | | | | |?????????? Hes1 Her1 Hbools1 Hn1].
        inversion_clear Hsem2 as [| | | | | | | | | | | |?????????? Hes2 Her2 Hbools2 Hn2].
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
      intros ???. split; intros Hin' Hv1 Hv2.
      - eapply Forall2_forall2 in H5 as (Hl1&Heq1).
        eapply Forall2_forall2 in H7 as (Hl2&Heq2).
        eapply HasCaus_snd_det in Hin; eauto; subst.
        eapply EqStN_morph. 3:eauto.
        1,2:eapply sem_var_det; eauto.
      - exfalso. eapply NoDup_HasCaus_HasLastCaus; eauto.
    Qed.

  End sem_equation_det.

  Lemma det_var_inv_mask : forall Γ n rs1 rs2 Hi1 Hi2 x,
      EqStN n rs1 rs2 ->
      det_var_inv Γ n Hi1 Hi2 x ->
      forall k, det_var_inv Γ n (mask_hist k rs1 Hi1) (mask_hist k rs2 Hi2) x.
  Proof.
    intros * Heq Hdet ????.
    split; intros Hin Hv1 Hv2.
    1,2:(eapply sem_var_mask_inv in Hv1 as (?&Hv1&Heq1);
         eapply sem_var_mask_inv in Hv2 as (?&Hv2&Heq2);
         rewrite Heq1, Heq2;
         eapply EqStN_mask; eauto;
         eapply Hdet in Hv2; eauto).
  Qed.

  Lemma det_var_inv_unmask : forall Γ n rs1 rs2 Hi1 Hi2 x,
      EqStN n rs1 rs2 ->
      (forall k, det_var_inv Γ n (mask_hist k rs1 Hi1) (mask_hist k rs2 Hi2) x) ->
      det_var_inv Γ n Hi1 Hi2 x.
  Proof.
    intros * Heq Hdet ???.
    split; intros Hin Hv1 Hv2; eapply EqStN_unmask; eauto;
      intros k; [edestruct Hdet as (Hd&_)|edestruct Hdet as (_&Hd)];
      eapply Hd; unfold mask_hist; eauto using sem_var_mask.
  Qed.

  Lemma det_var_inv_filter : forall Γ n sc1 sc2 Hi1 Hi2 Hi1' Hi2' x,
      EqStN n sc1 sc2 ->
      det_var_inv Γ n Hi1 Hi2 x ->
      forall c, filter_hist c sc1 Hi1 Hi1' ->
           filter_hist c sc2 Hi2 Hi2' ->
           det_var_inv Γ n Hi1' Hi2' x.
  Proof.
    intros * Heq Hdet * (Hf11&Hf12) (Hf21&Hf22).
    split; intros Hin Hv1 Hv2.
    - eapply sem_var_filter_inv in Hv1 as (?&Hv1&Heq1); eauto.
      eapply sem_var_filter_inv in Hv2 as (?&Hv2&Heq2); eauto.
      apply filter_ffilter in Heq1. apply filter_ffilter in Heq2. rewrite Heq1, Heq2.
      eapply EqStN_ffilter; eauto.
      eapply Hdet in Hv2; eauto.
    - rewrite Hf12 in Hv1. rewrite Hf22 in Hv2.
      apply sem_var_ffilter_inv in Hv1 as (?&Hv1&Heq1).
      apply sem_var_ffilter_inv in Hv2 as (?&Hv2&Heq2).
      rewrite Heq1, Heq2.
      eapply EqStN_ffilter; eauto.
      eapply Hdet in Hv2; eauto.
  Qed.

  Lemma det_var_inv_unfilter : forall Γ tn n sc1 sc2 Hi1 Hi2 x,
      snd tn > 0 ->
      wt_stream sc1 (Tenum tn) ->
      wt_stream sc2 (Tenum tn) ->
      EqStN n sc1 sc2 ->
      (forall c, In c (seq 0 (snd tn)) ->
            exists Hi1' Hi2',
              (forall y, HasCaus Γ y x -> Env.In y (fst Hi1') /\ Env.In y (fst Hi2'))
              /\ filter_hist c sc1 Hi1 Hi1'
              /\ filter_hist c sc2 Hi2 Hi2'
              /\ det_var_inv Γ n Hi1' Hi2' x) ->
      (forall y, ~HasLastCaus Γ y x) ->
      det_var_inv Γ n Hi1 Hi2 x.
  Proof.
    intros * Hn Hwt1 Hwt2 Heq Hdet Hnin ???.
    split; intros Hin Hv1 Hv2.
    - eapply EqStN_unfilter. 4:eauto. 1-3:eauto.
      intros k Hin'. edestruct Hdet as (Hi1'&Hi2'&(Hin1&Hin2)&(Hf1&_)&(Hf2&_)&Hdet'); eauto.
      assert (exists vs1', sem_var (fst Hi1') x0 vs1') as (?&Hvar1) by (inv Hin1; do 2 econstructor; try reflexivity; eauto).
      assert (exists vs1', sem_var (fst Hi2') x0 vs1') as (?&Hvar2) by (inv Hin2; do 2 econstructor; try reflexivity; eauto).
      assert (Hvar1':=Hvar1). eapply sem_var_filter_inv in Hvar1' as (?&?&Hv1'); eauto.
      assert (Hvar2':=Hvar2). eapply sem_var_filter_inv in Hvar2' as (?&?&Hv2'); eauto.
      eapply sem_var_det in Hv1; eauto. eapply sem_var_det in Hv2; eauto.
      do 2 esplit; eauto. rewrite Hv1, Hv2 in *. repeat split; eauto.
      apply filter_ffilter in Hv1'. apply filter_ffilter in Hv2'.
      edestruct Hdet' as (Hdet1&_). eapply Hdet1; eauto.
    - exfalso. eapply Hnin; eauto.
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
        Forall (fun blks => exists Hi1' Hi2',
                    filter_hist (fst blks) sc1 Hi1 Hi1'
                    /\ filter_hist (fst blks) sc2 Hi2 Hi2'
                    /\ Forall (sem_block_det n envS
                                            Hi1' Hi2'
                                            (ffilterb (fst blks) sc1 bs1) (ffilterb (fst blks) sc2 bs2)) (snd blks)) branches ->
        sem_block_det n envS Hi1 Hi2 bs1 bs2 (Bswitch ec branches)
    | Sdetlocal : forall Hi1 Hi2 Hl1 Hl2 bs1 bs2 locs blocks Hi1' Hi2' Hl1' Hl2',
        (forall x vs, sem_var Hi1' x vs -> ~InMembers x locs -> sem_var Hi1 x vs) ->
        (forall x vs, sem_var Hi2' x vs -> ~InMembers x locs -> sem_var Hi2 x vs) ->

        Env.refines (@EqSt _) Hl1 Hl1' ->
        Env.refines (@EqSt _) Hl2 Hl2' ->

        (forall x ty ck cx e0 clx,
              In (x, (ty, ck, cx, Some (e0, clx))) locs ->
              exists vs0 vs1 vs,
                sem_exp G (Hi1', Hl1') bs1 e0 [vs0] /\ sem_var Hi1' x vs1 /\ fby vs0 vs1 vs /\ sem_var Hl1' x vs) ->
        (forall x ty ck cx e0 clx,
              In (x, (ty, ck, cx, Some (e0, clx))) locs ->
              exists vs0 vs1 vs,
                sem_exp G (Hi2', Hl2') bs2 e0 [vs0] /\ sem_var Hi2' x vs1 /\ fby vs0 vs1 vs /\ sem_var Hl2' x vs) ->

        Forall (sem_block_det n envS (Hi1', Hl1') (Hi2', Hl2') bs1 bs2) blocks ->

        Forall (det_var_inv (senv_of_locs locs)
                            (pred n) (Hi1', Hl1') (Hi2', Hl2')) (map snd (idcaus_of_senv (senv_of_locs locs))) ->
        Forall (fun x => In x envS -> det_var_inv (senv_of_locs locs) n (Hi1', Hl1') (Hi2', Hl2') x)
               (map snd (idcaus_of_senv (senv_of_locs locs))) ->
        sem_block_det n envS (Hi1, Hl1) (Hi2, Hl2) bs1 bs2 (Blocal locs blocks).

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
        econstructor; eauto. simpl_Forall.
        do 2 esplit. split; [|split]; eauto.
        simpl_Forall; eauto.
      - (* locals *)
        econstructor; eauto.
        + rewrite Forall_forall in *; eauto.
        + simpl_Forall. intros ???. split; intros; auto with coindstreams.
        + simpl_Forall. intros ???. split; intros; auto with coindstreams.
    Qed.

    (* Go from n to n + 1 :) *)
    Lemma sem_block_det_S : forall n envS blk Hi1 Hi2 bs1 bs2,
        incl (map snd (idcaus_of_locals blk)) envS ->
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
        eapply H; eauto. etransitivity. 2:eapply Hincl.
        intros ??. solve_In.
      - (* switch *)
        econstructor; eauto. simpl_Forall.
        do 2 esplit. split; [|split]; eauto.
        simpl_Forall. eapply H; eauto.
        etransitivity. 2:eapply Hincl.
        intros ??. simpl_In. solve_In.
      - (* locals *)
        econstructor; eauto. 1-3:simpl_Forall.
        + eapply H; eauto.
          etransitivity. 2:eapply Hincl.
          intros ??; simpl_In. eapply idcaus_of_locals_In_local1 in Hin; eauto. solve_In.
        + eapply H14, Hincl.
          eapply idcaus_of_locals_In_local2 in H0; eauto. solve_In.
        + now exfalso.
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
        intros k. specialize (H10 k). simpl_Forall; eauto.
      - (* switch *)
        econstructor; eauto.
        simpl_Forall. do 2 esplit; eauto. simpl_Forall; eauto.
      - (* locals *)
        econstructor; eauto. simpl_Forall; eauto.
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
        intros k. specialize (H10 k). simpl_Forall; eauto.
      - (* switch *)
        econstructor; eauto.
        simpl_Forall. do 2 esplit; eauto. simpl_Forall; eauto.
      - (* locals *)
        econstructor; eauto. simpl_Forall; eauto.
    Qed.

    Hint Resolve sem_block_det_sem_block1 sem_block_det_sem_block2 : ldet.

    Lemma det_var_inv_incl : forall Γ Γ' n Hi1 Hi2 x,
        incl Γ Γ' ->
        det_var_inv Γ' n Hi1 Hi2 x ->
        det_var_inv Γ n Hi1 Hi2 x.
    Proof.
      intros * Hincl1 Hdet ???.
      split; intros Hin Hv1 Hv2; eauto.
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
      - (* reset *)
        econstructor; eauto.
        intros k. specialize (H10 k). simpl_Forall; eauto.
      - (* switch *)
        econstructor; eauto. simpl_Forall.
        do 2 esplit. split; [|split]; eauto.
        simpl_Forall; eauto.
      - (* local *)
        econstructor; eauto.
        1:simpl_Forall; eauto.
        setoid_rewrite <-Hperm; auto.
    Qed.

    Fact det_var_inv_local :
      forall Γ (locs : list (ident * (type * clock * ident * option (exp * ident)))) Hi1 Hi2 Hl1 Hl2 Hi1' Hi2' Hl1' Hl2' n cx,
        (forall x : ident, InMembers x locs -> ~ In x (map fst Γ)) ->
        (forall x, IsLast Γ x -> Env.In x Hl1) ->
        (forall x, IsLast Γ x -> Env.In x Hl2) ->
        (forall x vs, sem_var Hi1' x vs -> ~ InMembers x locs -> sem_var Hi1 x vs) ->
        (forall x vs, sem_var Hi2' x vs -> ~ InMembers x locs -> sem_var Hi2 x vs) ->
        Env.refines (@EqSt _) Hl1 Hl1' ->
        Env.refines (@EqSt _) Hl2 Hl2' ->
        (forall x, HasCaus Γ x cx \/ HasLastCaus Γ x cx -> det_var_inv Γ n (Hi1, Hl1) (Hi2, Hl2) cx) ->
        (forall x, HasCaus (senv_of_locs locs) x cx \/ HasLastCaus (senv_of_locs locs) x cx ->
              det_var_inv (senv_of_locs locs) n (Hi1', Hl1') (Hi2', Hl2') cx) ->
        det_var_inv (Γ ++ senv_of_locs locs) n (Hi1', Hl1') (Hi2', Hl2') cx.
    Proof.
      intros * Hnd Hdoml1 Hdoml2 Href1 Href2 Hrefl1 Hrefl2 Hsc1 Hsc2.
      split; intros Hin Hv1 Hv2; inv Hin; rewrite in_app_iff in H; destruct H as [Hin|Hin]; simpl in *.
      - edestruct Hsc1 as (Hinv&_); [|eapply Hinv]; eauto with senv.
        + eapply Href1; eauto. intros Hnin.
          eapply Hnd; eauto. solve_In.
        + eapply Href2; eauto. intros Hnin.
          eapply Hnd; eauto. solve_In.
      - edestruct Hsc2 as (Hinv&_); [|eapply Hinv]; eauto with senv.
      - edestruct Hsc1 as (_&Hinv); [|eapply Hinv]; eauto with senv.
        1,2:eapply sem_var_refines'; eauto with senv.
        + eapply Hdoml1. econstructor; eauto. congruence.
        + eapply Hdoml2. econstructor; eauto. congruence.
      - edestruct Hsc2 as (_&Hinv); [|eapply Hinv]; eauto with senv.
    Qed.

    Lemma det_block_S : forall n envS blk Γ xs Hi1 Hi2 bs1 bs2 y cy,
        det_nodes G ->
        NoDup (map snd (idcaus_of_senv Γ ++ idcaus_of_locals blk)) ->
        NoDupLocals (map fst Γ) blk ->
        VarsDefined blk xs ->
        incl xs (map fst Γ) ->
        (forall x, IsLast Γ x -> Env.In x (snd Hi1)) ->
        (forall x, IsLast Γ x -> Env.In x (snd Hi2)) ->
        (forall x cx, HasCaus Γ x cx \/ HasLastCaus Γ x cx -> det_var_inv Γ n Hi1 Hi2 cx) ->
        wt_block G Γ blk ->
        sem_block_det (S n) envS Hi1 Hi2 bs1 bs2 blk ->
        EqStN (S n) bs1 bs2 ->
        In y xs ->
        HasCaus Γ y cy ->
        (forall x cx, HasCaus Γ x cx \/ HasLastCaus Γ x cx ->
                 depends_on Γ cy cx blk -> det_var_inv Γ (S n) Hi1 Hi2 cx) ->
        (forall cx, In cx (map snd (idcaus_of_locals blk)) ->
               depends_on Γ cy cx blk -> In cx envS) ->
        det_var_inv Γ (S n) Hi1 Hi2 cy.
    Proof.
      induction blk as [(xs&es)| | |] using block_ind2;
        intros * HdetG Hnd Hnd2 Hvars Hincl Hdom1 Hdom2 Hn Hwt Hsem Hbs Hinxs Hinenv HSn HenvS;
        inv Hnd2; inv Hvars; inv Hwt; inv Hsem; simpl in *.
      - (* equation *)
        eapply In_nth in Hinxs as (?&Hlen&Hnth). instantiate (1:=xH) in Hnth.
        rewrite app_nil_r in Hnd.
        eapply det_equation_S; eauto.
        + eapply Pexp_Pexps.
          * simpl_Forall.
            eapply det_exp_S; eauto.
          * intros ? IsF. assert (IsF':=IsF). eapply Is_free_left_list_In_snd in IsF as (?&?).
            eapply HSn; eauto.
            rewrite <-Hnth in *. econstructor; eauto using nth_error_nth'.
          * destruct H1 as (_&Hf2). apply Forall2_length in Hf2.
            rewrite <-length_typesof_annots. congruence.
        + now rewrite Hnth.

      - (* reset *)
        eapply in_concat in Hinxs as (?&Hin1&Hin2). inv_VarsDefined. simpl_Forall.
        assert (EqStN (S n) r1 r2) as Hrs.
        { eapply bools_of_detn. 2,3:eauto.
          eapply det_exp_S with (k:=0) (n:=n) in H5; eauto.
          - eapply H5 in H8; simpl in H8; eauto.
          - rewrite <-length_typeof_numstreams, H7; simpl. lia.
          - intros ? IsF. assert (IsF':=IsF). eapply Is_free_left_In_snd in IsF as (?&?).
            eapply HSn, DepOnReset2; eauto. solve_Exists.
            left. eapply In_Is_defined_in with (Γ:=Γ); eauto using in_or_app.
            etransitivity; eauto using incl_concat.
        }
        eapply det_var_inv_unmask; eauto.
        intros k. specialize (H15 k). simpl_Forall.
        eapply H with (bs1:=maskb k r1 bs1) (bs2:=maskb k r2 bs2); eauto.
        + clear - Hinblks Hnd.
          eapply NoDup_locals_inv; eauto.
        + etransitivity; eauto using incl_concat.
        + setoid_rewrite Env.Props.P.F.map_in_iff; eauto.
        + setoid_rewrite Env.Props.P.F.map_in_iff; eauto.
        + intros. eapply det_var_inv_mask; eauto using EqStN_weaken.
        + eapply EqStN_mask; eauto.
        + intros * Hin' Hdep. eapply det_var_inv_mask; eauto.
          eapply HSn; eauto. constructor. solve_Exists.
        + intros * Hin' Hdep. eapply HenvS; eauto.
          2:constructor; solve_Exists. solve_In.

      - (* switch *)
        assert (Is_defined_in Γ cy (Bswitch ec branches)) as Hdef.
        { eapply In_Is_defined_in with (Γ:=Γ); eauto using incl_refl, in_or_app.
          econstructor; eauto. }
        eapply det_exp_S with (k:=0) (n:=n) in H9; eauto. specialize (H9 H12); simpl in H9.
        2:{ rewrite <-length_typeof_numstreams, H6; auto. }
        2:{ intros ? IsF. assert (IsF':=IsF). eapply Is_free_left_In_snd in IsF as (?&?).
            eapply HSn, DepOnSwitch2; eauto.
            inv Hdef. solve_Exists. }
        repeat (take (wt_streams [_] (typeof ec)) and rewrite H6 in it; apply Forall2_singl in it).
        eapply det_var_inv_unfilter. 4:eauto. all:eauto.
        1:{ destruct tn as (?&[]); simpl in *; try lia.
            apply Permutation_sym, Permutation_nil, map_eq_nil in H8; congruence. }
        2:{ intros * Hnin. eapply NoDup_HasCaus_HasLastCaus; eauto. solve_NoDup_app. }
        intros ? Hseq.
        assert (exists blks, In (c, blks) branches) as (blks&Hinbrs).
        { rewrite <-H8 in Hseq. simpl_In; eauto. }
        repeat (take (Forall _ branches) and eapply Forall_forall in it; eauto).
        destruct it4 as (?&Hvars&Hperm).
        rewrite <-Hperm in Hinxs. apply in_concat in Hinxs as (?&Hin1&Hin2).
        eapply Forall2_ignore1, Forall_forall in Hvars as (?&Hinblk&?); eauto; simpl in *.
        simpl_Forall. do 2 esplit. split; [|split; [|split]]; eauto.
        1:{ intros ? Hcaus.
            eapply HasCaus_snd_det in Hinenv; eauto; subst. 2:simpl_app; eauto using NoDup_app_l.
            split; eapply sem_block_defined; eauto using sem_block_det_sem_block1, sem_block_det_sem_block2.
            1,2:(eapply VarsDefined_Is_defined in H; eauto;
                 eapply NoDupLocals_incl; [|eauto]; etransitivity; eauto;
                 rewrite <-Hperm; eauto using incl_concat).
        }
        eapply it; eauto.
        + clear - Hinbrs Hinblk Hnd.
          eapply NoDup_locals_inv, NoDup_locals_inv2; eauto. auto.
        + etransitivity; [|eauto]. rewrite <-Hperm. eapply incl_concat; eauto.
        + destruct H0 as (?&Heq). setoid_rewrite Heq. setoid_rewrite Env.Props.P.F.map_in_iff; eauto.
        + destruct H1 as (?&Heq). setoid_rewrite Heq. setoid_rewrite Env.Props.P.F.map_in_iff; eauto.
        + intros * Hin. eapply det_var_inv_filter; eauto using EqStN_weaken.
        + eapply EqStN_ffilter; eauto.
        + intros * Hin Hdep. eapply det_var_inv_filter; eauto.
          eapply HSn; eauto.
          constructor. solve_Exists.
        + intros * Hin Hdep. eapply HenvS; eauto.
          * solve_In.
          * constructor. solve_Exists.

      - (* locals *)
        assert (In y (concat xs0)) as Hinxs0 by (rewrite <-H7; auto with datatypes).
        eapply in_concat in Hinxs0 as (?&Hin1&Hin2).
        eapply Forall2_ignore1, Forall_forall in H3 as (?&Hinblk&Hvars); eauto.
        eapply Forall_forall in H; eauto.
        assert (det_var_inv (Γ ++ senv_of_locs locs)
                            (S n) (Hi1', Hl1') (Hi2', Hl2') cy) as Hdet'.
        { eapply H; eauto.
          - clear - Hinblk Hnd.
            eapply NoDup_locals_inv; eauto. rewrite idcaus_of_senv_app.
            simpl_app. auto.
          - simpl_Forall. now rewrite map_app, map_fst_senv_of_locs.
          - rewrite map_app, map_fst_senv_of_locs.
            etransitivity; eauto using incl_concat.
            rewrite <-H7, Permutation_app_comm.
            apply incl_app; [apply incl_appl|apply incl_appr]; eauto using incl_refl.
          - intros * Hin. inv Hin.
            apply in_app_iff in H0 as [|]; simpl_In; subst.
            + eapply Env.In_refines; eauto with senv.
            + destruct o as [(?&?)|]; simpl in *; try congruence.
              edestruct H15 as (?&?&?&?&?&?&?); eauto using sem_var_In.
          - intros * Hin. inv Hin.
            apply in_app_iff in H0 as [|]; simpl_In; subst.
            + eapply Env.In_refines; eauto with senv.
            + destruct o as [(?&?)|]; simpl in *; try congruence.
              edestruct H16 as (?&?&?&?&?&?&?); eauto using sem_var_In.
          - intros * _. eapply det_var_inv_local with (Hl1:=Hl1); eauto.
            intros ? Hin. eapply Forall_forall in H22; eauto.
            apply idcaus_of_senv_In in Hin. solve_In.
          - simpl_Forall; auto.
          - simpl_Forall; auto.
          - apply HasCaus_app; auto.
          - intros * _ Hdep. eapply det_var_inv_local with (Hl1:=Hl1); eauto.
            + intros. eapply HSn; eauto.
              econstructor; eauto. solve_Exists.
            + intros * Hin.
              assert (In cx (map snd (idcaus_of_senv (senv_of_locs locs)))) as Hin'.
              { apply idcaus_of_senv_In in Hin. solve_In. }
              eapply Forall_forall in H23; eauto. eapply H23.
              eapply HenvS.
              * simpl_In. eapply idcaus_of_locals_In_local2 in Hin0; eauto. solve_In.
              * econstructor; eauto. solve_Exists.
          - intros * Hin Hdep. apply HenvS.
            + simpl_In. eapply idcaus_of_locals_In_local1 in Hin0; eauto. solve_In.
            + econstructor; eauto. solve_Exists.
        }
        intros ???. split; intros Hin3 Hv1 Hv2.
        + eapply HasCaus_snd_det in Hinenv; eauto; subst. 2:solve_NoDup_app.
          assert (~InMembers y locs) as Hnin.
          { intros ?. eapply H5; eauto. }
          assert (NoDupLocals x x0).
          { rewrite Forall_forall in *. eapply NoDupLocals_incl; eauto.
            etransitivity; eauto using incl_concat.
            rewrite <-H7, Permutation_app_comm.
            apply incl_app; [apply incl_appl; auto|apply incl_appr, incl_refl].
          }
          edestruct Hdet' as (Hd1&_). eapply Hd1; [eapply HasCaus_app| |]; eauto.
          1,2:(eapply sem_var_refines_inv; [| | |eauto]; intros; eauto).
          1,2:rewrite Forall_forall in *; eapply sem_block_dom_lb; eauto with ldet.
        + exfalso. eapply NoDup_HasCaus_HasLastCaus; eauto. solve_NoDup_app.
    Qed.

    Lemma sem_block_det_cons_nIn : forall n envS x blk Hi1 Hi2 bs1 bs2,
        ~In x (map snd (idcaus_of_locals blk)) ->
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
        contradict Hnin. solve_In.
      - (* switch *)
        econstructor; eauto. simpl_Forall.
        do 2 esplit; split; [|split]; eauto. simpl_Forall.
        eapply H; eauto.
        contradict Hnin. solve_In.
      - (* locals *)
        econstructor; eauto.
        + rewrite Forall_forall in *; intros. eapply H; eauto.
          contradict Hnin.
          simpl_In. eapply idcaus_of_locals_In_local1 in Hin; eauto. solve_In.
        + eapply Forall_impl_In; [|eapply H14]; intros * Hin1 Hloc Hin2.
          inv Hin2; eauto.
          exfalso. eapply Hnin. simpl_In. eapply idcaus_of_locals_In_local2 in Hin; eauto. solve_In.
    Qed.

    Lemma sem_block_det_cons_In : forall n envS blk Γ xs Hi1 Hi2 bs1 bs2 y cy,
        det_nodes G ->
        NoDup (map snd (idcaus_of_senv Γ ++ idcaus_of_locals blk)) ->
        NoDupLocals (map fst Γ) blk ->
        VarsDefined blk xs ->
        incl xs (map fst Γ) ->
        (forall x, IsLast Γ x -> Env.In x (snd Hi1)) ->
        (forall x, IsLast Γ x -> Env.In x (snd Hi2)) ->
        (forall x cx, HasCaus Γ x cx \/ HasLastCaus Γ x cx -> det_var_inv Γ n Hi1 Hi2 cx) ->
        wt_block G Γ blk ->
        sem_block_det (S n) envS Hi1 Hi2 bs1 bs2 blk ->
        EqStN (S n) bs1 bs2 ->
        In (y, cy) (idcaus_of_locals blk) ->
        (forall x cx, HasCaus Γ x cx \/ HasLastCaus Γ x cx ->
                 depends_on Γ cy cx blk -> det_var_inv Γ (S n) Hi1 Hi2 cx) ->
        (forall cx, In cx (map snd (idcaus_of_locals blk)) ->
               depends_on Γ cy cx blk -> In cx envS) ->
        sem_block_det (S n) (cy::envS) Hi1 Hi2 bs1 bs2 blk.
    Proof.
      induction blk as [(xs&es)| | |] using block_ind2;
        intros * HdetG Hnd Hnd2 Hvars Hincl Hdom1 Hdom2 Hn Hwt Hsem Hbs Hinenv HSn HenvS;
        inv Hnd2; inv Hvars; inv Hwt; inv Hsem; simpl in *.
      - (* equation *)
        inv Hinenv.

      - (* reset *)
        econstructor; eauto. intros k. specialize (H15 k).
        eapply Forall2_ignore2 in H4.
        rewrite Forall_forall in *; intros * Hinblk.
        destruct (in_dec ident_eq_dec cy (map snd (idcaus_of_locals x))).
        2:eapply sem_block_det_cons_nIn; eauto.
        edestruct H4 as (?&Hinvars&Hvars'); eauto.
        assert (EqStN (S n) r1 r2) as Hrs.
        { eapply bools_of_detn. 2,3:eauto.
          eapply det_exp_S with (k:=0) (n:=n) in H5; eauto.
          - eapply H5 in H8; eauto.
          - rewrite <-length_typeof_numstreams, H7; simpl; lia.
          - intros ? IsF. assert (IsF':=IsF). eapply Is_free_left_In_snd in IsF as (?&?).
            eapply HSn, DepOnReset2; eauto. solve_Exists.
            eapply idcaus_of_locals_def_last; eauto.
            eapply NoDupLocals_incl; eauto. etransitivity; eauto using incl_concat.
        }
        { simpl_In.
          eapply H with (Γ:=Γ); eauto; try solve_In.
          - clear - Hinblk Hnd.
            eapply NoDup_locals_inv; eauto.
          - etransitivity; eauto using incl_concat.
          - setoid_rewrite Env.Props.P.F.map_in_iff; eauto.
          - setoid_rewrite Env.Props.P.F.map_in_iff; eauto.
          - intros * ?.
            eapply det_var_inv_mask; eauto using EqStN_weaken.
          - eapply EqStN_mask; eauto.
          - intros * Hin' Hdep.
            eapply det_var_inv_mask; eauto. eapply HSn; eauto.
            constructor. solve_Exists.
          - intros * Hin' Hdep. eapply HenvS; eauto. solve_In.
            constructor; solve_Exists.
        }

      - (* switch *)
        econstructor; eauto. simpl_Forall.
        do 2 esplit. split; [|split]; eauto.
        simpl_Forall. inv_VarsDefined.
        destruct (in_dec ident_eq_dec cy (map snd (idcaus_of_locals x0))).
        2:eapply sem_block_det_cons_nIn; eauto. simpl_In.
        eapply det_exp_S with (k:=0) (n:=n) in H9; eauto. specialize (H9 H12); simpl in H9.
        2:{ rewrite <-length_typeof_numstreams, H6; auto. }
        2:{ intros ? IsF. assert (IsF':=IsF). eapply Is_free_left_In_snd in IsF as (?&?).
            eapply HSn, DepOnSwitch2; eauto. solve_Exists.
            eapply idcaus_of_locals_def_last; eauto. 2:solve_In.
            eapply NoDupLocals_incl; eauto. etransitivity; eauto.
            take (Permutation _ _) and rewrite <-it; eauto using incl_concat.
        }
        repeat (take (wt_streams [_] (typeof ec)) and rewrite H6 in it; apply Forall2_singl in it).
        eapply H; eauto.
        + clear - H0 H17 Hnd.
          eapply NoDup_locals_inv, NoDup_locals_inv2; eauto. auto.
        + etransitivity; [|eauto]. take (Permutation _ _) and rewrite <-it. eapply incl_concat; eauto.
        + destruct H1 as (?&Heq). setoid_rewrite Heq. setoid_rewrite Env.Props.P.F.map_in_iff; eauto.
        + destruct H14 as (?&Heq). setoid_rewrite Heq. setoid_rewrite Env.Props.P.F.map_in_iff; eauto.
        + intros * ??. eapply det_var_inv_filter; eauto using EqStN_weaken.
        + eapply EqStN_ffilter; eauto.
        + intros * ? Hdep. eapply det_var_inv_filter; eauto.
          eapply HSn; eauto.
          constructor. solve_Exists.
        + intros ? Hin' Hdep. eapply HenvS; eauto. solve_In.
          constructor. solve_Exists.

      - (* locals *)
        unfold idcaus_of_locals, idcaus_of_senv in Hinenv; simpl in *. rewrite 2 in_app_iff in Hinenv.
        destruct Hinenv as [[Hinenv|Hinenv]|Hinenv].
        + (* current locs *)
          econstructor; eauto.
          * rewrite Forall_forall in *; intros.
            eapply sem_block_det_cons_nIn; eauto.
            { intro Hin. clear - H0 Hinenv Hin Hnd. unfold idcaus_of_senv in Hnd.
              simpl_app.
              eapply NoDup_app_r, NoDup_app_r, NoDup_app_In with (x:=cy) in Hnd.
              2:solve_In. clear Hinenv.
              eapply Hnd. repeat rewrite in_app_iff in *. right. solve_In. }
          * eapply Forall_impl_In; [|eauto]; intros ? Hin Hdet Hin'.
            inv Hin'; eauto.
            assert (In y (concat xs0)) as Hinvars.
            { rewrite <-H7. apply in_or_app; left.
              clear - Hinenv. solve_In. }
            eapply in_concat in Hinvars as (xs'&?&Hinvars). inv_VarsDefined.
            eapply det_var_inv_incl with (Γ':=Γ ++ senv_of_locs locs).
            1:solve_incl_app.
            { eapply det_block_S with (envS:=envS); eauto.
              - clear - Hinblks Hnd.
                eapply NoDup_locals_inv; eauto. rewrite idcaus_of_senv_app. simpl_app. auto.
              - simpl_Forall. now rewrite map_app, map_fst_senv_of_locs.
              - rewrite map_app, map_fst_senv_of_locs.
                etransitivity; eauto using incl_concat.
                rewrite <-H7, Permutation_app_comm.
                apply incl_app; [apply incl_appl|apply incl_appr]; eauto using incl_refl.
              - intros * Hin'. inv Hin'.
                apply in_app_iff in H1 as [|]; simpl_In; subst.
                + eapply Env.In_refines; eauto with senv.
                + destruct o as [(?&?)|]; simpl in *; try congruence.
                  edestruct H15 as (?&?&?&?&?&?&?); eauto using sem_var_In.
              - intros * Hin'. inv Hin'.
                apply in_app_iff in H1 as [|]; simpl_In; subst.
                + eapply Env.In_refines; eauto with senv.
                + destruct o as [(?&?)|]; simpl in *; try congruence.
                  edestruct H16 as (?&?&?&?&?&?&?); eauto using sem_var_In.
              - intros * _. eapply det_var_inv_local with (Hl1:=Hl1); eauto.
                intros * Hin'. eapply Forall_forall in H22; eauto.
                clear - Hin'. unfold idcaus_of_senv. simpl_app. rewrite in_app_iff; auto.
                destruct Hin' as [Hin'|Hin']; inv Hin'; simpl_In; [left|right]; solve_In. auto.
              - simpl_Forall; auto.
              - simpl_Forall; auto.
              - simpl_In. econstructor. apply in_or_app; right; solve_In. auto.
              - intros * _ Hdep. eapply det_var_inv_local with (Hl1:=Hl1); eauto.
                + intros. eapply HSn; eauto.
                  econstructor; eauto. solve_Exists.
                + intros * Hin'.
                  assert (In cx (map snd (idcaus_of_senv (senv_of_locs locs)))) as Hin2.
                  { apply idcaus_of_senv_In in Hin'. solve_In. }
                  eapply Forall_forall with (x:=cx) in H23; eauto. eapply H23.
                  eapply HenvS.
                  * simpl_In. eapply idcaus_of_locals_In_local2 in Hin0; eauto. solve_In.
                  * econstructor; eauto. solve_Exists.
              - intros * Hin' Hdep. apply HenvS.
                + simpl_In. eapply idcaus_of_locals_In_local1 in Hin0; eauto. solve_In.
                + econstructor; eauto. solve_Exists.
            }

        + (* lasts *)
          simpl_In; subst.
          econstructor; eauto.
          * rewrite Forall_forall in *; intros.
            eapply sem_block_det_cons_nIn; eauto.
            { intro Hin. clear - H0 Hin0 Hin Hnd. unfold idcaus_of_senv in Hnd.
              simpl_app.
              eapply NoDup_app_r, NoDup_app_r, NoDup_app_r, NoDup_app_In with (x:=i0) in Hnd.
              2:solve_In; auto. clear Hin0.
              eapply Hnd. repeat rewrite in_app_iff in *. solve_In. }
          * apply Forall_forall; intros * Hin HinenvS. destruct HinenvS; subst; [|simpl_Forall; eauto].
            simpl_In. unfold idcaus_of_senv, senv_of_locs in Hin1. apply in_app_iff in Hin1 as [|]; simpl_In; subst.
            1:{ exfalso. clear - Hnd Hin1 Hin0. unfold idcaus_of_senv in Hnd. simpl_app.
                eapply NoDup_app_r, NoDup_app_r, NoDup_app_In in Hnd. 2:solve_In.
                eapply Hnd. repeat rewrite in_app_iff. left. clear Hin1. solve_In. auto.
            }
            edestruct H15 as (?&?&?&He1&Hv1&Hfby1&Hv'1); eauto.
            edestruct H16 as (?&?&?&He2&Hv2&Hfby2&Hv'2); eauto.
            split; intros * Hin' Hv Hv'.
            1:{ exfalso. clear - Hnd Hin1 Hin'. inv Hin'. simpl_In.
                unfold idcaus_of_senv in Hnd. simpl_app.
                eapply NoDup_app_r, NoDup_app_r, NoDup_app_In in Hnd. 2:solve_In.
                eapply Hnd. repeat rewrite in_app_iff. left. clear Hin. solve_In. auto.
            } simpl in *.
            assert (x5 = i2); subst.
            { clear - Hin1 Hin' Hnd. inv Hin'. simpl_In; subst.
              unfold idcaus_of_senv in Hnd. simpl_app.
              apply NoDup_app_r, NoDup_app_r, NoDup_app_r, NoDup_app_l in Hnd.
              eapply NoDup_snd_det; eauto. solve_In; simpl; eauto. clear Hin. solve_In; simpl; auto.
            } clear Hin'.
            eapply sem_var_det in Hv'1; eauto. eapply sem_var_det in Hv'2; eauto. rewrite Hv'1, Hv'2.
            { eapply fby_det_Sn; eauto.
              - simpl_Forall.
                eapply det_exp_S with (k:=0) in He1; eauto. specialize (He1 He2). simpl in *; eauto.
                + intros. eapply det_var_inv_local with (Hl1:=Hl1); eauto.
                  intros * Hin'. apply idcaus_of_senv_In in Hin'.
                  eapply Forall_forall in H22; eauto. eauto.
                + rewrite <-length_typeof_numstreams, H1; auto.
                + intros * IsF. eapply det_var_inv_local with (Hl1:=Hl1); eauto.
                  * intros. eapply HSn; eauto.
                    eapply DepOnLocal2; eauto. solve_Exists; split; auto.
                  * intros * Hin'. apply idcaus_of_senv_In in Hin'.
                    eapply Forall_forall in H23; eauto. eapply H23.
                    eapply HenvS; simpl.
                    { eapply idcaus_of_locals_In_local2 in Hin'; eauto. solve_In. }
                    eapply DepOnLocal2; eauto. solve_Exists; split; auto.
              - eapply Forall_forall in H22. 2:unfold idcaus_of_senv; simpl_app; apply in_app_iff, or_introl; solve_In.
                simpl in *.
                edestruct H22 as (Hinv&_). eapply Hinv; eauto. econstructor; solve_In. auto.
            }

        + (* deeper *)
          econstructor; eauto.
          * apply Forall_forall; intros * Hinblk.
            destruct (in_dec ident_eq_dec cy (map snd (idcaus_of_locals x))). unfold idcaus_of_locals in i; simpl in i.
            2:simpl_Forall; eapply sem_block_det_cons_nIn; eauto.
            simpl_In.
            inv_VarsDefined. rewrite Forall_forall in H.
            { eapply H with (Γ:=Γ ++ senv_of_locs locs); eauto.
              - clear - Hinblk Hnd.
                eapply NoDup_locals_inv; eauto. rewrite idcaus_of_senv_app.
                simpl_app; auto.
              - simpl_Forall. now rewrite map_app, map_fst_senv_of_locs.
              - rewrite map_app, map_fst_senv_of_locs.
                etransitivity; eauto using incl_concat.
                rewrite <-H7, Permutation_app_comm.
                apply incl_app; [apply incl_appl|apply incl_appr]; eauto using incl_refl.
              - intros * Hin'. inv Hin'.
                apply in_app_iff in H0 as [|]; simpl_In; subst.
                + eapply Env.In_refines; eauto with senv.
                + destruct o as [(?&?)|]; simpl in *; try congruence.
                  edestruct H15 as (?&?&?&?&?&?&?); eauto using sem_var_In.
              - intros * Hin'. inv Hin'.
                apply in_app_iff in H0 as [|]; simpl_In; subst.
                + eapply Env.In_refines; eauto with senv.
                + destruct o as [(?&?)|]; simpl in *; try congruence.
                  edestruct H16 as (?&?&?&?&?&?&?); eauto using sem_var_In.
              - intros * _. eapply det_var_inv_local with (Hl1:=Hl1); eauto.
                intros * Hin'. eapply Forall_forall in H22; eauto.
                clear - Hin'. unfold idcaus_of_senv. simpl_app. rewrite in_app_iff; auto.
                destruct Hin' as [Hin'|Hin']; inv Hin'; simpl_In; [left|right]; solve_In. auto.
              - simpl_Forall; auto.
              - simpl_Forall; auto.
              - intros * _ Hdep. eapply det_var_inv_local with (Hl1:=Hl1); eauto.
                + intros. eapply HSn; eauto.
                  econstructor; eauto. solve_Exists.
                + intros * Hin'.
                  assert (In cx (map snd (idcaus_of_senv (senv_of_locs locs)))) as Hin2.
                  { apply idcaus_of_senv_In in Hin'. solve_In. }
                  eapply Forall_forall with (x:=cx) in H23; eauto. eapply H23.
                  eapply HenvS.
                  * clear - Hin2. simpl_In. eapply idcaus_of_locals_In_local2 in Hin; solve_In.
                  * econstructor; eauto. solve_Exists.
              - intros * Hin' Hdep. apply HenvS.
                + simpl_app. apply in_or_app, or_intror. solve_In.
                + econstructor; eauto. solve_Exists.
            }
          * simpl_Forall. destruct H1; subst; eauto.
            exfalso. clear - Hinenv H0 Hnd.
            unfold idcaus_of_senv in *. simpl_app.
            repeat rewrite map_map in Hnd. apply NoDup_app_r, NoDup_app_r in Hnd.
            rewrite app_assoc in Hnd. eapply NoDup_app_In in Hnd.
            eapply Hnd. solve_In. simpl.
            rewrite in_app_iff in *. destruct H0 as [|]; [left|right]; solve_In. auto.
    Qed.

    Lemma det_vars_n :
      forall nd n Hi1 Hi2 bs1 bs2,
        det_nodes G ->
        wt_node G nd ->
        node_causal nd ->
        EqStN n bs1 bs2 ->
        sem_block G Hi1 bs1 (n_block nd) ->
        sem_block G Hi2 bs2 (n_block nd) ->
        Forall (det_var_inv (senv_of_inout (n_in nd ++ n_out nd)) n Hi1 Hi2) (map snd (idcaus (n_in nd))) ->
        Forall (det_var_inv (senv_of_inout (n_in nd ++ n_out nd)) n Hi1 Hi2) (map snd (idcaus (n_in nd ++ n_out nd))).
    Proof.
      intros * HdetG Hwtn Hcaus Hbs Hsem1 Hsem2 Hins.

      assert (sem_block_det n (map snd (idcaus (n_in nd ++ n_out nd) ++ idcaus_of_locals (n_block nd)))
                            Hi1 Hi2 bs1 bs2 (n_block nd) /\
              Forall (fun x => In x (map snd (idcaus (n_in nd ++ n_out nd))) ->
                            det_var_inv (senv_of_inout (n_in nd ++ n_out nd)) n Hi1 Hi2 x)
                     (map snd (idcaus (n_in nd ++ n_out nd) ++ idcaus_of_locals (n_block nd)))) as (_&Hvars).
      2:{ eapply Forall_impl_In; [|eapply Forall_incl; [eapply Hvars|]]; eauto.
          repeat rewrite idcaus_app. solve_incl_app. }

      induction n.
      - (* everyone is equal up to 0 anyway *)
        split.
        + eapply sem_block_det_0; eauto.
        + eapply Forall_forall. intros ??????. split; intros; constructor.
      - (* use the causal induction to step once *)
        clear Hsem1 Hsem2.
        destruct IHn as (Hblk&Hvars); eauto using EqStN_weaken.
        { eapply Forall_impl; [|eapply Hins]; intros ?????.
          split; intros Hin Hv1 Hv2; eapply EqStN_weaken; eauto.
          1,2:eapply H in Hv1; eauto.
        }

        eapply node_causal_ind; eauto.
        + intros ?? Hperm (Hblk'&Hvars'). split.
          * eapply sem_block_det_Perm; eauto.
          * rewrite <-Hperm; auto.
        + split; auto.
          eapply sem_block_det_S; [|eauto]. solve_incl_app.
        + intros * Hin (Hblk'&Hvars') Hdep.
          repeat rewrite idcaus_app, map_app, in_app_iff in Hin.
          destruct Hcaus as (Hnd&_).
          destruct Hin as [[Hin|Hin]|Hin]; (split; [|constructor; auto; intros Hin']).
          * eapply sem_block_det_cons_nIn; eauto.
            intros Hin'. clear - Hin Hin' Hnd. simpl_app.
            eapply NoDup_app_In in Hnd; eauto. eapply Hnd.
            repeat rewrite in_app_iff in *. auto.
          * eapply Forall_forall in Hins; eauto.
          * eapply sem_block_det_cons_nIn; eauto.
            intros Hin'. clear - Hin Hin' Hnd. simpl_app.
            eapply NoDup_app_r, NoDup_app_In in Hnd; eauto.
          * pose proof (n_defd nd) as (?&Hdef&Hperm). simpl_In.
            eapply det_block_S; eauto.
            -- clear - Hnd. now rewrite idcaus_of_senv_inout.
            -- rewrite map_fst_senv_of_inout. apply node_NoDupLocals.
            -- rewrite map_fst_senv_of_inout, Hperm. solve_incl_app.
            -- intros * Has. inv Has. simpl_In. congruence.
            -- intros * Has. inv Has. simpl_In. congruence.
            -- intros * [Hin'|Hin']; inv Hin'; simpl_In; try congruence.
               eapply Forall_forall in Hvars; eauto. eapply Hvars. solve_In.
               rewrite map_app. apply in_app_iff, or_introl. solve_In.
            -- destruct Hwtn as (?&?&?&?); auto.
            -- rewrite Hperm. solve_In.
            -- clear - Hin0. econstructor. solve_In; eauto using in_or_app.
               1,2:simpl; auto.
            -- intros * [Hin'|Hin'] ?; inv Hin'; simpl_In; try congruence.
               eapply Forall_forall in Hvars'; eauto. eapply Hvars'. solve_In.
          * pose proof (n_defd nd) as (?&Hdef&Hperm).
            simpl_In.
            eapply sem_block_det_cons_In; eauto.
            -- clear - Hnd. now rewrite idcaus_of_senv_inout.
            -- rewrite map_fst_senv_of_inout. apply node_NoDupLocals.
            -- rewrite map_fst_senv_of_inout, Hperm. solve_incl_app.
            -- intros * Has. inv Has. simpl_In. congruence.
            -- intros * Has. inv Has. simpl_In. congruence.
            -- intros * [Hin'|Hin']; inv Hin'; simpl_In; try congruence.
               eapply Forall_forall in Hvars; eauto. eapply Hvars. solve_In.
               rewrite map_app. apply in_app_iff, or_introl. solve_In.
            -- destruct Hwtn as (?&?&?&?); auto.
            -- intros * [Hin'|Hin'] ?; inv Hin'; simpl_In; try congruence.
               eapply Forall_forall in Hvars'; eauto. eapply Hvars'. solve_In.
          * exfalso. rewrite map_app in Hnd.
            eapply NoDup_app_In in Hnd; eauto.
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
      { eapply find_node_not_Is_node_in; eauto using wl_global_Ordered_nodes with ltyping. }
      eapply sem_block_cons in Hbcks1; eauto using wl_global_Ordered_nodes with ltyping.
      eapply sem_block_cons in Hbcks2; eauto using wl_global_Ordered_nodes with ltyping.

      assert (Forall (det_var_inv (senv_of_inout (n_in n1 ++ n_out n1)) n (H, @Env.empty _) (H0, @Env.empty _)) (map snd (idcaus (n_in n1)))) as Hins.
      { eapply node_causal_NoDup in H1 as Hnd.
        clear - Heqins Hins1 Hins2 Hnd.
        assert (incl (idcaus (n_in n1)) (idcaus (n_in n1 ++ n_out n1))) as Hincl.
        { rewrite idcaus_app. solve_incl_app. }
        revert ins1 ins2 Hins1 Hins2 Heqins Hnd Hincl.
        generalize (n_in n1 ++ n_out n1) as cenv.
        induction (n_in n1) as [|(?&(?&?)&?)]; intros * Hins1 Hins2 Heqins;
          inv Hins1; inv Hins2; inv Heqins; constructor; eauto; simpl in *.
        - intros ???. split; intros Hin Hv1 Hv2; inv Hin; simpl_In; try congruence.
          specialize (Hincl _ (in_eq _ _)).
          eapply NoDup_snd_det in Hincl; [|eauto|solve_In]; subst.
          eapply sem_var_det in H3; eauto. eapply sem_var_det in H4; eauto.
          now rewrite H3, H4.
        - eapply IHl; eauto. eapply incl_cons'; eauto. }
      eapply det_vars_n in Hins; eauto.
      + eapply Forall2_trans_ex in Houts2; [|eapply Forall2_swap_args, Houts1].
        eapply Forall2_impl_In; [|eauto]; intros ?? _ _ (?&Hin&Hv1&Hv2). simpl_In.
        unfold idcaus in Hins. rewrite Forall_map, Forall_map in Hins.
        eapply Forall_forall in Hins; [|eauto using in_or_app].
        eapply Hins in Hv2; eauto; simpl in *.
        econstructor. solve_In; eauto using in_or_app. 1,2:reflexivity.
      + inv Hwt; inv H4. eapply IHnds; eauto. split; eauto.
      + inv Hwt; inv H4. destruct H7; auto.
      + eapply clocks_of_EqStN; eauto.
    - rewrite find_node_other in Hfind1; auto.
      eapply IHnds; eauto. inv Hwt; inv H4; split; auto.
      1,2:econstructor; eauto.
      1,2:eapply sem_block_cons; eauto using wl_global_Ordered_nodes with ltyping.
      1,2:eapply find_node_later_not_Is_node_in; eauto using wl_global_Ordered_nodes with ltyping.
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
