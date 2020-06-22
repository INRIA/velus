From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Lustre.LSyntax.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import Transcription.Transcription.

From Velus Require Import Lustre.LTyping.
From Velus Require Import Lustre.LClocking.
From Velus Require Import Lustre.LOrdered.
From Velus Require Import Lustre.LCausality.
From Velus Require Import Lustre.LSemantics.
From Velus Require Import NLustre.NLOrdered.
From Velus Require Import NLustre.NLCoindSemantics.

From Velus Require Import CoindStreams.

From Coq Require Import String.

From Coq Require Import List.
Import List.ListNotations.
From Coq Require Import Permutation.
From Coq Require Import Omega.
From Coq Require Import Setoid.
From Coq Require Import Morphisms.

Open Scope list.

From compcert Require Import common.Errors.
Open Scope error_monad_scope.

From Coq Require Import Classes.EquivDec.

(** * Semantics Preservation Proof for Transcription *)

Module Type CORRECTNESS
       (Import Ids  : IDS)
       (Import Op   : OPERATORS)
       (Import OpAux: OPERATORS_AUX        Op)
       (L           : LSYNTAX          Ids Op)
       (Import CE   : CESYNTAX             Op)
       (NL          : NLSYNTAX         Ids Op              CE)
       (Import TR   : TRANSCRIPTION    Ids Op OpAux L      CE NL)
       (LT          : LTYPING          Ids Op       L)
       (LC          : LCLOCKING        Ids Op       L)
       (LCA         : LCAUSALITY       Ids Op       L)
       (Ord         : NLORDERED        Ids Op              CE NL)
       (Lord        : LORDERED         Ids Op       L)
       (Import Str  : COINDSTREAMS         Op OpAux)
       (LS          : LSEMANTICS       Ids Op OpAux L Lord       Str)
       (NLSC        : NLCOINDSEMANTICS Ids Op OpAux        CE NL Str Ord).

  Lemma const_inv1 :
    forall c b s,
      const b c ≡ absent ⋅ s ->
      exists b', s ≡ const b' c /\ b ≡ false ⋅ b'.
  Proof.
    intros * H.
    unfold_Stv b; inv H; simpl in *; inv H0.
    exists b. split; symmetry; auto. reflexivity.
  Qed.

  Lemma const_inv2 :
    forall c c' b s,
      const b c ≡ present c' ⋅ s ->
      exists b', s ≡ const b' c
            /\ b ≡ true ⋅ b'
            /\ c' = sem_const c.
  Proof.
    intros * H.
    unfold_Stv b; inv H; simpl in *; inv H0.
    exists b. split. symmetry. assumption. split; reflexivity.
  Qed.

  Lemma const_tl :
    forall c b v tl,
      const b c ≡ v ⋅ tl ->
      const (Streams.tl b) c ≡ tl.
  Proof.
    intros * H.
    unfold_Stv b; inv H; simpl in *; inv H0; assumption.
  Qed.

  Lemma sem_var_var :
    forall H x s,
      LS.sem_var H x s <-> NLSC.sem_var H x s.
  Proof.
    split; intros * Hsem; inv Hsem;
    econstructor; eauto.
  Qed.

  Lemma env_maps_tl :
    forall i v s H,
      Env.MapsTo i (v ⋅ s) H -> Env.MapsTo i s (NLSC.History_tl H).
  Proof.
    intros * Hmap.
    unfold NLSC.History_tl.
    assert (s = Streams.tl (v ⋅ s)) as Hs by auto.
    rewrite Hs. eapply Env.map_1. assumption.
  Qed.

  Lemma sem_var_step :
    forall H x v s,
      LS.sem_var H x (v ⋅ s) -> LS.sem_var (NLSC.History_tl H) x s.
  Proof.
    intros * Hsem.
    inv Hsem.
    destruct xs'.
    econstructor.
    eapply env_maps_tl; eauto. now inv H2.
  Qed.

  Lemma sem_var_step_nl :
    forall H x v s,
      NLSC.sem_var H x (v ⋅ s) -> NLSC.sem_var (NLSC.History_tl H) x s.
  Proof.
    intros * Hsem.
    inv Hsem.
    destruct xs'.
    econstructor.
    eapply env_maps_tl; eauto. now inv H2.
  Qed.

  Lemma sc_step :
    forall H b ck s ss,
      NLSC.sem_clock H b ck (s ⋅ ss) ->
      NLSC.sem_clock (NLSC.History_tl H) (Streams.tl b) ck ss.
  Proof.
    intros * Hsem.
    inv Hsem; auto. econstructor. rewrite H1. simpl. reflexivity.
  Qed.

  Lemma sem_const_step :
    forall G H b e e' v s,
      to_constant e = OK e' ->
      LS.sem_exp G H b e [v ⋅ s] ->
      LS.sem_exp G (NLSC.History_tl H) (Streams.tl b) e [s].
  Proof.
    einduction e using L.exp_ind2; intros * Htr Hsem; inv Htr.
    - inv Hsem. symmetry in H5.
      destruct v;
        [ apply const_inv1 in H5; destruct H5 as [ b' [ Hs Hb ] ]
        | apply const_inv2 in H5; destruct H5 as (b' & Hs & Hb & Hc) ];
        rewrite Hs; rewrite Hb; simpl; econstructor; reflexivity.
    - destruct es; inv H2.
      destruct es; inv H3.
      inv H0. inv H5. inv Hsem. inv H12. inv H10. inv H9. inv H6. inv H0.
      rewrite app_nil_r in H3. inv H3.
      destruct x0. destruct s0.
      econstructor. econstructor; eauto.
      eapply sem_var_step; eauto. econstructor; eauto.
      now inv H5.
  Qed.

  Lemma sem_lexp_step :
    forall G H b e e' v s,
      to_lexp e = OK e' ->
      LS.sem_exp G H b e [v ⋅ s] ->
      LS.sem_exp G (NLSC.History_tl H) (Streams.tl b) e [s].
  Proof.
    einduction e using L.exp_ind2; intros * Htr Hsem; inv Htr.
    - inv Hsem. symmetry in H5.
      destruct v;
        [ apply const_inv1 in H5; destruct H5 as [ b' [ Hs Hb ] ]
        | apply const_inv2 in H5; destruct H5 as (b' & Hs & Hb & Hc) ];
      rewrite Hs; rewrite Hb; simpl; econstructor; reflexivity.
    - inv Hsem. inv H5.  destruct xs'.
      econstructor. econstructor.
      eapply env_maps_tl; eauto. inv H3; simpl in *. assumption.
    - inv Hsem. destruct a. monadInv H1. destruct s0.
      econstructor; eauto. inv H10; auto.
    - inv Hsem. destruct a. monadInv H1. destruct s1, s2.
      econstructor; eauto. inv H13; auto.
    - destruct es; inv H2.
      destruct es; inv H3.
      inv H0.
      destruct a. destruct l; inv H2.
      destruct l; try now inv H1. monadInv H1.
      clear H5.
      inv Hsem. inv H11. inv H5. destruct s0, x1.
      inv H9. inv H7. simpl in H0. rewrite app_nil_r in H0. subst.
      econstructor.
      + econstructor; eauto.
      + eapply sem_var_step. eassumption.
      + econstructor; eauto. inv H3; eauto.
  Qed.

  Lemma sem_cexp_step :
    forall G H b e e' v s,
      to_cexp e = OK e' ->
      LS.sem_exp G H b e [v ⋅ s] ->
      LS.sem_exp G (NLSC.History_tl H) (Streams.tl b) e [s].
  Proof.
    einduction e using L.exp_ind2; intros * Htr Hsem;
      (now inv Htr) || (unfold to_cexp in Htr;
                       try (monadInv Htr; eapply sem_lexp_step; eauto));
      cases; monadInv Htr; fold to_cexp in *;

        inv Hsem; inv H11; inv H6; inv H12; inv H7; inv H13; inv H10;
          rewrite app_nil_r in H3, H2; subst;
            inv H0; inv H1; clear H10 H7; destruct x2, y1.
    - inv H8;
        (econstructor; eauto;
         [ eapply sem_var_step; eauto | econstructor; eauto; econstructor ]).
    - inv H8;
        (econstructor; eauto; eapply sem_lexp_step in EQ; eauto;
         econstructor; eauto; constructor).
  Qed.

  Lemma ty_lexp :
    forall G env e e',
      LT.wt_exp G env e ->
      to_lexp e = OK e' ->
      L.typeof e = [CE.typeof e'].
  Proof.
    induction e using L.exp_ind2; intros * Hwt Htr; inv Htr.
    - now simpl.
    - destruct a. inv H0. now simpl.
    - destruct a. simpl. monadInv H0. now simpl.
    - destruct a. monadInv H0. now simpl.
    - cases. inv H. simpl. inv Hwt. inv H8. inv H6. monadInv H1.
      unfold L.typesof. unfold flat_map. simpl. rewrite app_nil_r.
      now apply H3.
  Qed.

  Lemma sem_exp_lexp :
    forall G G' env H b e e' s,
      LT.wt_exp G' env e ->
      to_lexp e = OK e' ->
      LS.sem_exp G H b e [s] ->
      NLSC.sem_exp H b e' s.
  Proof.
    induction e using L.exp_ind2; intros * Hwt Htr Hsem; inv Htr.
    - inv Hsem. now econstructor.
    - destruct a. inv Hsem. inv H1. econstructor. now apply sem_var_var.
    - destruct a. inv Hsem. monadInv H1. inv Hwt. econstructor; eauto.
      eapply ty_lexp in EQ; eauto. rewrite H9 in EQ. now inv EQ.
    - destruct a. inv Hsem. monadInv H1. inv Hwt. econstructor; eauto.
      eapply ty_lexp in EQ; eauto. eapply ty_lexp in EQ1; eauto.
      rewrite H11 in EQ. inv EQ. rewrite H12 in EQ1. now inv EQ1.
    - cases. monadInv H2. inv Hsem. inv H0. clear H4. inv Hwt.
      inv H9. inv H5. inv H11. inv H6. rewrite app_nil_r in H0. inv H0. inv H14.
      econstructor; eauto. now apply sem_var_var.
  Qed.

  Lemma sem_lexp_single :
    forall e e' G H b ss,
      to_lexp e = OK e' ->
      LS.sem_exp G H b e ss ->
      exists s, ss = [s].
  Proof.
    induction e using L.exp_ind2; intros * Htr Hsem; inv Htr;
      try (inv Hsem; eexists; now eauto).
    cases_eqn H2. subst. monadInv H2. inv Hsem. inv H9. inv H5. inv H. inv H5.
    eapply H4 in EQ; [|eauto]. inv EQ. simpl in H11. inv H11. inv H6.
    eauto.
  Qed.

  Lemma sem_exps_lexps :
    forall G H b tenv es les ss,
      mmap to_lexp es = OK les ->
      Forall (LT.wt_exp G tenv) es ->
      Forall2 (LS.sem_exp G H b) es ss ->
      Forall2 (NLSC.sem_exp H b) les (concat ss).
  Proof.
    intros * Hmmap Hwt Hsem. revert dependent les.
    induction Hsem; intros. inv Hmmap. simpl. auto.
    apply mmap_cons in Hmmap.
    destruct Hmmap as [ x' [le' [Hle [Htolexp  Hmmap]]]]. inv Hwt.
    apply IHHsem in Hmmap; eauto.
    assert (Htolexp' := Htolexp).
    eapply sem_lexp_single in Htolexp'; eauto. inv Htolexp'.
    eapply sem_exp_lexp in Htolexp; eauto. now constructor.
  Qed.

  Lemma sem_exp_cexp :
    forall G G' env H b e e' s,
      LT.wt_exp G' env e ->
      to_cexp e = OK e' ->
      LS.sem_exp G H b e [s] ->
      NLSC.sem_cexp H b e' s.
  Proof.
    induction e using L.exp_ind2; intros * Hwt Htr Hsem;
      (now inv Htr) || (unfold to_cexp in Htr;
                       try (monadInv Htr; econstructor;
                            eapply sem_exp_lexp; eauto));
      cases; monadInv Htr; fold to_cexp in *;
                 inv Hsem; inv H11; inv H6; inv H12; inv H7; inv H13; inv H10;
                   rewrite app_nil_r in H3, H2; subst;
                     inv H0; inv H1; clear H10 H7; destruct x2, y1.
    - inv Hwt; inv H11; inv H12. inv H8;
        (econstructor; eauto;
         [ eapply sem_var_var; eauto
         | econstructor; eauto; eapply merge_id; eauto ]).
    - inv Hwt. inv H12. inv H13.
      inv H8; econstructor; eauto;
        eapply sem_exp_lexp in EQ; eauto;
          econstructor; eauto.
  Qed.

  CoFixpoint abstract_clock (xs: Stream value) : Stream bool:=
    match xs with
    | absent ⋅ xs => false ⋅ abstract_clock xs
    | present _ ⋅ xs => true ⋅ abstract_clock xs
    end.

  Add Parametric Morphism : (abstract_clock)
      with signature @EqSt value ==> @EqSt bool
        as ac_EqSt.
  Proof.
    cofix Cofix; intros b b' Eb.
    unfold_Stv b; unfold_Stv b';
      constructor; inv Eb; simpl in *; try discriminate; auto.
  Qed.

  Lemma ac_tl :
    forall s, abstract_clock (Streams.tl s) ≡ Streams.tl (abstract_clock s).
  Proof.
    intros. unfold_Stv s; reflexivity.
  Qed.

  Lemma length_typeof :
    forall G H b env e os,
      LT.wt_exp G env e ->
      LS.sem_exp G H b e os ->
      length (L.typeof e) = length os.
  Proof.
    intros * Hwt Hsem.
    eapply LS.sem_exp_numstreams in Hsem; eauto.
    rewrite L.length_typeof_numstreams; auto.
  Qed.

  Lemma length_clockof :
    forall G H b env e os,
      LC.wc_exp G env e ->
      LS.sem_exp G H b e os ->
      length (L.clockof e) = length os.
  Proof.
    intros * Hwc Hsem.
    eapply LS.sem_exp_numstreams in Hsem; eauto.
    rewrite L.length_clockof_numstreams; auto.
  Qed.

  Lemma ac_when :
    forall k cs xs rs,
      when k cs xs rs -> abstract_clock cs ≡ abstract_clock xs.
  Proof.
    cofix Cofix.
    intros * Hwhen. inv Hwhen; econstructor; simpl; eauto.
  Qed.

  Lemma ac_const:
    forall c b cs,
      const b c ≡ cs -> b ≡ abstract_clock cs.
  Proof.
    cofix Cofix.
    intros * Hconst.
    unfold_Stv b;
      inv Hconst; simpl in *;
      unfold_Stv cs; constructor; simpl; eauto; inv H.
  Qed.

  Lemma ac_fby1 :
    forall xs ys rs,
      LS.fby xs ys rs -> abstract_clock xs ≡ abstract_clock rs.
  Proof.
    cofix Cofix.
    intros * Hfby.
    unfold_Stv xs; inv Hfby; econstructor; simpl; eauto.
    clear - H3. revert H3. revert y xs ys0 rs0.
    cofix Cofix.
    intros * Hfby1.
    unfold_Stv xs; inv Hfby1; econstructor; simpl; eauto.
  Qed.

  Lemma ac_fby2 :
    forall xs ys rs,
      LS.fby xs ys rs -> abstract_clock ys ≡ abstract_clock rs.
  Proof.
    cofix Cofix. intros * Hfby.
    unfold_Stv ys; inv Hfby; econstructor; simpl; eauto.
    clear - H3. revert H3. revert v ys xs0 rs0.
    cofix Cofix. intros * Hfby1.
    unfold_Stv ys; inv Hfby1; econstructor; simpl; eauto.
  Qed.

  Lemma ac_ite :
    forall s  ts fs rs,
      ite s ts fs rs -> abstract_clock ts ≡ abstract_clock rs.
  Proof.
    cofix Cofix.
    intros * Hite.
    unfold_Stv ts; inv Hite; econstructor; simpl; eauto.
  Qed.

  Lemma ac_lift1 :
    forall op ty s o,
      lift1 op ty s o -> abstract_clock s ≡ abstract_clock o.
  Proof.
    cofix Cofix.
    intros * Hlift.
    unfold_Stv s; inv Hlift; econstructor; simpl; eauto.
  Qed.

  Lemma ac_lift2 :
    forall op ty1 ty2 s1 s2 o,
      lift2 op ty1 ty2 s1 s2 o -> abstract_clock s1 ≡ abstract_clock o.
  Proof.
    cofix Cofix.
    intros * Hlift.
    unfold_Stv s1; inv Hlift; econstructor; simpl; eauto.
  Qed.

  Lemma ac_synchronized :
    forall s, NLSC.synchronized s (abstract_clock s).
  Proof.
    cofix Cofix. intro.
    unfold_Stv s; rewrite unfold_Stream; simpl; constructor; auto.
  Qed.

  Lemma free_left_env :
    forall G x env eq,
      LC.wc_equation G env eq ->
      Exists (fun e : L.exp => LCA.Is_free_left x e) (snd eq) ->
      InMembers x env.
  Proof.
    intros ??? [xs es] (Hwc & _ & _) Hfr.
    induction es as [| e]. inv Hfr. simpl in *.
    inversion_clear Hwc as [|?? HWc].
    inversion_clear Hfr as [?? Hf | ]; auto.
    clear - Hf HWc.
    induction e using L.exp_ind2; inv Hf; inv HWc; eauto using In_InMembers.
    - tauto.
    - take (Exists _ _) and apply Exists_exists in it as (?& Hin &?).
      eapply Forall_forall in H; eauto. apply H; auto.
      eapply Forall_forall in Hin; eauto.
    - intuition; subst; eauto using In_InMembers.
      take (Exists _ _) and apply Exists_exists in it as (?& Hin &?).
      eapply Forall_forall in H; eauto. apply H; auto.
      eapply Forall_forall in Hin; eauto.
    - intuition; subst; eauto using In_InMembers.
      take (Exists _ _) and apply Exists_exists in it as (?& Hin &?).
      eapply Forall_forall in H; eauto. apply H; auto.
      eapply Forall_forall in Hin; eauto.
      take (Exists _ _) and apply Exists_exists in it as (?& Hin &?).
      eapply Forall_forall in H0; eauto. apply H0; auto.
      eapply Forall_forall in Hin; eauto.
    - intuition; subst; eauto using In_InMembers.
      take (Exists _ _) and apply Exists_exists in it as (?& Hin &?).
      eapply Forall_forall in H; eauto. apply H; auto.
      eapply Forall_forall in Hin; eauto.
      take (Exists _ _) and apply Exists_exists in it as (?& Hin &?).
      eapply Forall_forall in H0; eauto. apply H0; auto.
      eapply Forall_forall in Hin; eauto.
    - take (Exists _ _) and apply Exists_exists in it as (?& Hin &?).
      eapply Forall_forall in H0; eauto. apply H0; auto.
      eapply Forall_forall in Hin; eauto.
    - take (Exists _ _) and apply Exists_exists in it as (?& Hin &?).
      destruct Hin as [| Hin]. subst. auto.
      eapply Forall_forall in H0; eauto. apply H0; auto.
      eapply Forall_forall in Hin; eauto.
  Qed.

  Lemma Forall2_const_map :
    forall (A B C : Type) (P : A -> B -> Prop) (e : A) (l : list C) (l' : list B),
      Forall (fun y => P e y) l' ->
      length l = length l' ->
      Forall2 (fun x y => P x y) (map (fun _ => e) l) l'.
  Proof.
    intros * Hf Hlen.
    apply Forall2_forall; split; [| now rewrite map_length].
    intros * Hin. revert dependent l'.
    induction l; intros. inv Hin.
    destruct l'; inv Hlen. simpl in Hin.
    destruct Hin; inv Hf; try inv H; eauto.
  Qed.

  Definition var_inv (D : positive -> Prop) (env : list (ident * clock))
                     (H : LS.history) (b : Stream bool) : Prop :=
    forall x, D x ->
         (forall ck xs,
             In (x, ck) env ->
             LS.sem_var H x xs ->
             NLSC.sem_clock H b ck (abstract_clock xs)).

  Lemma var_inv_weaken:
    forall (D1 D2 : positive -> Prop) (env : list (ident * clock))
      (H : LS.history) (b : Stream bool),
      var_inv D1 env H b  ->
      (forall x, D2 x -> D1 x) ->
      var_inv D2 env H b.
  Proof.
    intros D1 D2 env H b I1 H12 x D2x.
    now apply H12, I1 in D2x.
  Qed.

  Lemma sc_when :
    forall H x b k ck xs ys rs,
      LS.sem_var H x xs ->
      NLSC.sem_clock H b ck (abstract_clock ys) ->
      when k ys xs rs ->
      NLSC.sem_clock H b (Con ck x k) (abstract_clock rs).
  Proof.
    cofix Cofix. intros * Hsemv Hsemc Hwhen.
    unfold_Stv rs; inv Hwhen; rewrite unfold_Stream; simpl;
      rewrite unfold_Stream in Hsemc; simpl in Hsemc.
    - rewrite sem_var_var in Hsemv. econstructor; eauto.
      rewrite <- sem_var_var in Hsemv.
      apply sem_var_step in Hsemv. apply sc_step in Hsemc.
      eapply Cofix; eauto; reflexivity.
    - assert (k = negb (negb k)) as Hk by apply Bool.negb_involutive_reverse.
      rewrite Hk. rewrite sem_var_var in Hsemv. eapply NLSC.Son_abs2 with (c:=c); eauto.
      rewrite <- Hk. rewrite <- sem_var_var in Hsemv.
      apply sem_var_step in Hsemv. apply sc_step in Hsemc.
      eapply Cofix; eauto; reflexivity.
    - rewrite sem_var_var in Hsemv. econstructor; eauto.
      rewrite <- sem_var_var in Hsemv.
      apply sem_var_step in Hsemv. apply sc_step in Hsemc.
      eapply Cofix; eauto; reflexivity.
  Qed.

  Ltac discriminate_var :=
    repeat match goal with
           | H: LS.sem_var _ _ _ |- _ => apply sem_var_var in H
           end;
    match goal with
    | H1: NLSC.sem_var ?H ?x (present _ ⋅ _),
          H2 : NLSC.sem_var ?H ?x (absent ⋅ _)
      |- _ => eapply NLSC.sem_var_det with (2 := H2) in H1;
            inv H1; simpl in *; discriminate
    end.

  Lemma sc_merge :
    forall H b ck x xs ts fs ss,
      LS.sem_var H x xs ->
      NLSC.sem_clock H b (Con ck x true) (abstract_clock ts) ->
      NLSC.sem_clock H b (Con ck x false)(abstract_clock fs) ->
      merge xs ts fs ss ->
      NLSC.sem_clock H b ck (abstract_clock ss).
  Proof.
    destruct ck; intros ???????? Hmerge.
    - econstructor. revert dependent H. revert Hmerge. revert b x xs ts fs ss.
      cofix Cofix; intros * Hmerge H Hsemv Hsct Hscf.
      unfold_Stv ss; inv Hmerge; rewrite unfold_Stream;
        rewrite unfold_Stream in Hsct, Hscf; simpl in *.
      + inv Hscf; try discriminate_var.
        inv H8. apply sem_var_step in Hsemv.
        apply sc_step in Hsct. eapply Cofix in Hsemv; eauto. inv H1.
        econstructor; simpl in *; auto.
      + inv Hsct; [| rewrite Bool.negb_true_iff in H3; subst; now simpl in H5].
        apply sem_var_step in Hsemv. apply sc_step in Hscf.
        eapply Cofix in Hsemv; eauto.
        inv H8. inv H1. econstructor; simpl in *; auto.
      + inv Hscf; [| now rewrite H3 in H5].
        inv H8. apply sem_var_step in Hsemv.
        apply sc_step in Hsct. eapply Cofix in Hsemv; eauto. inv H1.
        econstructor; simpl in *; auto.
    - revert dependent H. revert Hmerge. revert b ck i b0 x xs ts fs ss.
      cofix Cofix; intros * Hmerge H Hsemv Hsct Hscf.
      unfold_Stv ss; inv Hmerge; rewrite unfold_Stream;
        rewrite unfold_Stream in Hsct, Hscf; simpl in *.
      + inv Hscf; inv H8; try discriminate_var;
          apply sem_var_step in Hsemv;
          apply sc_step in Hsct; now econstructor; eauto.
      + inv Hsct; [| rewrite Bool.negb_true_iff in H3; subst; now simpl in H5].
        inv H8. econstructor; eauto.
        apply sem_var_step in Hsemv. apply sc_step in Hscf.
        eapply Cofix; eauto.
      + inv Hscf; [| now rewrite H3 in H5 ].
        inv H8. econstructor; eauto.
        apply sem_var_step in Hsemv. apply sc_step in Hsct.
        eapply Cofix; eauto.
  Qed.

  (* TODO: move to Streams.v *)
  Add Parametric Morphism
      A B (P: A -> Stream B -> Prop) xs
      (P_compat: Proper (eq ==> @EqSt B ==>  Basics.flip Basics.impl) P)
    : (@Forall2 A (Stream B) P xs)
      with signature @EqSts B ==> Basics.flip Basics.impl
        as Forall2_EqSt_flip.
  Proof.
    intros ys ys' Eys.
    revert xs ys ys' Eys.
      induction xs, ys; intros ** H; inv H; inv Eys; auto.
    constructor; eauto.
    - eapply P_compat; eauto.
    - eapply IHxs; eauto.
  Qed.

  Lemma sem_var_switch_env:
    forall H H' x v,
      orel (@EqSt value) (Env.find x H) (Env.find x H') ->
      NLSC.sem_var H x v <-> NLSC.sem_var H' x v.
  Proof.
    intros * Hfind; split; intro Hsem; inversion_clear Hsem as [???? Hr];
      rewrite Hr in Hfind; inv Hfind; econstructor; eauto.
    transitivity xs'; auto. now rewrite H1, H3.
  Qed.

  Lemma env_find_tl : forall x x' H H',
      orel (@EqSt value) (Env.find x H) (Env.find x' H') ->
      orel (@EqSt value)
           (Env.find x (NLSC.History_tl H))
           (Env.find x' (NLSC.History_tl H')).
  Proof.
    intros * Hfind. unfold NLSC.History_tl.
    do 2 rewrite Env.Props.P.F.map_o.
    inversion Hfind as [|?? Hs]; eauto; econstructor; now rewrite Hs.
  Qed.

  Lemma sc_switch_env:
    forall b H H' ck v,
      (forall x, Is_free_in_clock x ck ->
            orel (@EqSt value) (Env.find x H) (Env.find x H')) ->
      NLSC.sem_clock H b ck v <-> NLSC.sem_clock H' b ck v.
  Proof.
    intros * Hf. revert Hf. revert b H H' v.
    induction ck.
    - (* Cbase *)
      split; inversion_clear 1; eauto using NLSC.sem_clock.
    - (* Con *)
      split; revert Hf; revert b v H H' b0; cofix Cofix; intros * Hf Hsem;
        inversion_clear Hsem.
      + econstructor; eauto. apply (IHck b0 H H'); eauto.
        intros. apply Hf. now econstructor.
        rewrite <- sem_var_switch_env; eauto. apply Hf. econstructor.
        eauto. eapply Cofix; [| eassumption]. intros. apply env_find_tl.
        eapply Hf. inv H0; now econstructor.
      + econstructor; eauto. apply (IHck b0 H H'); eauto.
        intros. apply Hf. now econstructor.
        rewrite <- sem_var_switch_env; eauto. apply Hf. econstructor.
        eauto. eapply Cofix; [| eassumption]. intros. apply env_find_tl.
        eapply Hf. inv H0; now econstructor.
      +  eapply NLSC.Son_abs2; eauto. apply (IHck b0 H H'); eauto.
        intros. apply Hf. now econstructor.
        rewrite <- sem_var_switch_env; eauto. apply Hf. econstructor.
        eauto. eapply Cofix; [| eassumption]. intros. apply env_find_tl.
        eapply Hf. inv H0; now econstructor.
      + econstructor; eauto. apply (IHck b0 H H') in H1; eauto.
        intros. apply Hf. now econstructor.
        eapply sem_var_switch_env; try apply Hf. econstructor.
        eauto. eapply Cofix; [| eassumption]. intros. apply env_find_tl.
        eauto.
      + econstructor; eauto. apply (IHck b0 H H') in H1; eauto.
        intros. apply Hf. now econstructor.
        eapply sem_var_switch_env; try apply Hf. econstructor.
        eauto. eapply Cofix; [| eassumption]. intros. apply env_find_tl.
        eauto.
      + eapply NLSC.Son_abs2; eauto. apply (IHck b0 H H') in H1; eauto.
        intros. apply Hf. now econstructor.
        eapply sem_var_switch_env; try apply Hf. econstructor.
        eauto. eapply Cofix; [| eassumption]. intros. apply env_find_tl.
        eapply Hf. inv H0; now econstructor.
  Qed.

  Ltac discriminate_stream :=
    let H := fresh in
    match goal with
    | H1: ?b ≡ true ⋅ _, H2 : ?b ≡ false ⋅ _ |- _ =>
      rewrite H1 in H2; inversion H2 as [? H]; simpl in H; discriminate
    end.

  (* TODO: move to NLSC *)
  Lemma sem_clock_det :
    forall (ck : clock) (H : NLSC.History)
      (b xs xs' : Stream bool),
      NLSC.sem_clock H b ck xs ->
      NLSC.sem_clock H b ck xs' ->
      xs ≡ xs'.
  Proof.
    cofix Cofix. intros * Hsc Hsc'.
    unfold_Stv xs; unfold_Stv xs'.
    - inv Hsc; inv Hsc'.
      rewrite H1 in H2. inv H2. constructor; auto.
      constructor; simpl; auto. eapply Cofix; eauto.
    - inv Hsc; inv Hsc'; try discriminate_stream;
        try discriminate_var.
      take (NLSC.sem_var _ x (present c ⋅ _)) and
           eapply NLSC.sem_var_det in it; eauto.
      inversion it as [Hit]. simpl in Hit. inv Hit.
      destruct k0; simpl in *; congruence.
    - inv Hsc; inv Hsc'; try discriminate_stream;
        try discriminate_var.
      take (NLSC.sem_var _ x (present c ⋅ _)) and
           eapply NLSC.sem_var_det in it; eauto.
      inversion it as [Hit]. simpl in Hit. inv Hit.
      destruct k; simpl in *; congruence.
    - inv Hsc; inv Hsc'; constructor; simpl; auto;
        try (now eapply Cofix; eauto).
      rewrite H1 in H2. inv H2. now simpl in H3.
      rewrite H6 in H14. eapply Cofix; eauto.
  Qed.

  Ltac discriminate_clock :=
    let HH := fresh in
    match goal with
    | H1: NLSC.sem_clock ?H ?b ?ck (true ⋅ _),
          H2 : NLSC.sem_clock ?H ?b ?ck (false ⋅ _) |- _ =>
      eapply sem_clock_det with (2 := H2) in H1; eauto;
      inversion H1 as [HH ?]; simpl in HH; discriminate
    end.

  Lemma sc_inst:
    forall H H' b b' ck ck' bck sub cks,
      instck bck sub ck = Some ck' ->
      NLSC.sem_clock H b ck cks ->
      NLSC.sem_clock H' b' bck b ->
      (forall x x',
          Is_free_in_clock x ck ->
          sub x = Some x' ->
          orel (@EqSt value) (Env.find x H) (Env.find x' H')) ->
      NLSC.sem_clock H' b' ck' cks.
  Proof.
    intros * Hinst Hck Hbck Henv.
    revert dependent H'. revert Hinst Hck. revert H b b' ck' bck cks sub.
    induction ck; intros.
    - inv Hinst. inversion_clear Hck as [??? Hb| | |]. now rewrite <- Hb.
    - revert dependent H'. revert dependent cks.
      revert Hinst. revert b' i b0 ck' b H. cofix Cofix; intros.
      inversion Hinst as [Hcase]. cases_eqn Hcase. inv Hcase.
      unfold_Stv cks; assert (Hck' := Hck); inv Hck.
      + econstructor; eauto. eapply IHck in Hcase0; eauto.
        intros. eapply Henv; eauto. now constructor.
        specialize (Henv i i0 (FreeCon1 i ck b) Hcase1).
        inversion_clear H8 as [???? Hf]. rewrite Hf in Henv. inv Henv.
        rewrite H3 in H1. econstructor; eauto. destruct b0.
        eapply Cofix; eauto using sc_step. intros * Hfree ?.
        apply Henv with (x':= x') in Hfree; auto. now apply env_find_tl.
      + econstructor; eauto. eapply IHck in Hcase0; eauto.
        intros. eapply Henv; eauto. now constructor.
        specialize (Henv i i0 (FreeCon1 i ck b) Hcase1).
        inversion_clear H8 as [???? Hf]. rewrite Hf in Henv. inv Henv.
        rewrite H3 in H1. econstructor; eauto. destruct b0.
        eapply Cofix; eauto using sc_step. intros * Hfree ?.
        apply Henv with (x':= x') in Hfree; auto. now apply env_find_tl.
      + eapply NLSC.Son_abs2; eauto. eapply IHck in Hcase0; eauto.
        intros. eapply Henv; eauto. now constructor.
        specialize (Henv i i0 (FreeCon1 i ck (negb k)) Hcase1).
        inversion_clear H8 as [???? Hf]. rewrite Hf in Henv. inv Henv.
        rewrite H3 in H1. econstructor; eauto. destruct b0.
        eapply Cofix; eauto using sc_step. intros * Hfree ?.
        apply Henv with (x':= x') in Hfree; auto. now apply env_find_tl.
  Qed.

  Lemma sc_inst':
      forall H' H b b' ck ck' bck sub cks,
      instck bck sub ck = Some ck' ->
      NLSC.sem_clock H' b' ck' cks ->
      NLSC.sem_clock H' b' bck b ->
      (forall x x',
          Is_free_in_clock x ck ->
          sub x = Some x' ->
          orel (@EqSt value) (Env.find x H) (Env.find x' H')) ->
      NLSC.sem_clock H b ck cks.
  Proof.
    intros * Hinst Hck Hbck Henv.
    revert dependent H. revert Hinst Hck Hbck. revert H' b b' ck' bck cks sub.
    induction ck; intros.
    - inv Hinst. constructor. eauto using sem_clock_det.
    - revert dependent H'. revert dependent cks.
      revert Hinst. revert b' i b0 ck' b H. cofix Cofix; intros.
      inversion Hinst as [Hcase]. cases_eqn Hcase. inv Hcase.
      unfold_Stv cks; assert (Hck' := Hck); inv Hck.
      + econstructor; eauto. eapply IHck in Hcase0; eauto.
        intros. eapply Henv; eauto. now constructor.
        specialize (Henv i i0 (FreeCon1 i ck b) Hcase1).
        inversion_clear H8 as [???? Hf]. rewrite Hf in Henv. inv Henv.
        rewrite <- H3 in H1. econstructor; eauto. destruct b0.
        eapply Cofix; eauto using sc_step. intros * Hfree ?.
        apply Henv with (x':= x') in Hfree; auto. now apply env_find_tl.
      + econstructor; eauto. eapply IHck in Hcase0; eauto.
        intros. eapply Henv; eauto. now constructor.
        specialize (Henv i i0 (FreeCon1 i ck b) Hcase1).
        inversion_clear H8 as [???? Hf]. rewrite Hf in Henv. inv Henv.
        rewrite <- H3 in H1. econstructor; eauto. destruct b0.
        eapply Cofix; eauto using sc_step. intros * Hfree ?.
        apply Henv with (x':= x') in Hfree; auto. now apply env_find_tl.
      + eapply NLSC.Son_abs2; eauto. eapply IHck in Hcase0; eauto.
        intros. eapply Henv; eauto. now constructor.
        specialize (Henv i i0 (FreeCon1 i ck (negb k)) Hcase1).
        inversion_clear H8 as [???? Hf]. rewrite Hf in Henv. inv Henv.
        rewrite <- H3 in H1. econstructor; eauto. destruct b0.
        eapply Cofix; eauto using sc_step. intros * Hfree ?.
        apply Henv with (x':= x') in Hfree; auto. now apply env_find_tl.
  Qed.

  CoInductive sub_clock : relation (Stream bool) :=
  | SubP1 : forall s s',
      sub_clock s s' -> sub_clock (true ⋅ s) (true ⋅ s')
  | SubP2 : forall s s',
      sub_clock s s' -> sub_clock (true ⋅ s) (false ⋅ s')
  | SubA : forall s s',
      sub_clock s s' -> sub_clock (false ⋅ s) (false ⋅ s').

  Global Instance sub_clock_trans : Transitive sub_clock.
  Proof.
    cofix Cofix. intros x y z XY YZ.
    unfold_Stv x; unfold_Stv z; inv XY; inv YZ; constructor;
      eapply Cofix; eauto.
  Qed.

  Global Instance sub_clock_refl : Reflexive sub_clock.
  Proof.
    cofix Cofix. intro x.
    unfold_Stv x; constructor; auto.
  Qed.

  Add Parametric Morphism : (sub_clock)
      with signature @EqSt bool ==> @EqSt bool ==> Basics.impl
        as sub_clock_EqSt.
  Proof.
    cofix Cofix. intros b b' Eb c c' Ec Hsub.
    unfold_Stv b'; unfold_Stv c'; try constructor; inv Eb; inv Ec; inv Hsub;
      simpl in *; try discriminate; eapply Cofix; eauto.
  Qed.

  Lemma sub_clock_step :
    forall b b', sub_clock b b' -> sub_clock (Streams.tl b) (Streams.tl b').
  Proof.
    intros * Hs. unfold_Stv b; unfold_Stv b'; inv Hs; eauto.
  Qed.

  Lemma sub_clock_Con :
    forall H b ck x b0 s s',
      NLSC.sem_clock H b ck s ->
      NLSC.sem_clock H b (Con ck x b0) s' ->
      sub_clock s s'.
  Proof.
    intros * Hsc Hsc'.
    - destruct ck.
      + inv Hsc. revert Hsc' H1. revert H b x b0 s s'. cofix Cofix; intros.
        unfold_Stv s'; unfold_Stv s.
        constructor. inv Hsc'. inv H1. eapply Cofix; eauto.
        inversion_clear Hsc' as [|????????? Hb'| |]. inv Hb'.
        discriminate_stream.
        constructor. inv Hsc'; inv H1; eapply Cofix; eauto.
        constructor. inv Hsc'; inv H1; eapply Cofix; eauto.
      + revert Hsc Hsc'. revert H b ck i b1 s s' x b0.
        cofix Cofix; intros.
        unfold_Stv s'; unfold_Stv s.
        constructor. apply sc_step in Hsc.
        apply sc_step in Hsc'.
        eapply Cofix; eauto.
        inv Hsc'. discriminate_clock.
        inv Hsc'. discriminate_clock.
        constructor. apply sc_step in Hsc. eapply Cofix; eauto.
        constructor. apply sc_step in Hsc.
        apply sc_step in Hsc'. eapply Cofix; eauto.
  Qed.

  Lemma sub_clock_parent :
    forall H b ck ck' s s',
      NLSC.sem_clock H b ck s ->
      NLSC.sem_clock H b ck' s' ->
      clock_parent ck ck' ->
      sub_clock s s'.
  Proof.
    intros * Hsc Hsc' Hparent.
    revert dependent s'. induction Hparent; intros.
    - eapply sub_clock_Con; eauto.
    - inversion Hsc' as [|????????? Hck'|???????? Hck' |????????? Hck'];
        subst; pose proof (sub_clock_Con _ _ _ _ _ _ _ Hck' Hsc');
          apply IHHparent in Hck'; etransitivity; eauto.
  Qed.

  Lemma sub_clock_sclocksof :
    forall s ss,
      In s ss ->
      Forall (fun s' => sub_clock (abstract_clock s) (abstract_clock s')) ss ->
      clocks_of ss ≡ abstract_clock s.
  Proof.
    intros * Hin Hsub.
    remember (abstract_clock s) as acs eqn: Hacs. apply eq_EqSt in Hacs.
    revert Hin Hacs Hsub. revert s ss acs.
    cofix Cofix. intros.
    rewrite (unfold_Stream s) in *; destruct s as [[|]]; simpl in *;
    rewrite unfold_Stream in Hacs; simpl in Hacs; inversion Hacs as [Hac ?].
    - constructor; simpl in *. rewrite Hac.
      apply existsb_Forall, forallb_Forall, Forall_forall; intros * Hin'.
      pose proof Hin' as Hs; eapply Forall_forall in Hs; eauto; simpl in Hs.
      rewrite Hacs in Hs. inversion Hs as [| |??? HH Hx ]. unfold_Stv x; auto.
      rewrite unfold_Stream in Hx. simpl in Hx. discriminate.
      eapply in_map in Hin. eapply Cofix; eauto. rewrite Forall_map.
      eapply Forall_impl; eauto. intros * HH. simpl in HH.
      rewrite ac_tl. now apply sub_clock_step.
    - constructor; simpl in *. rewrite Hac. rewrite existsb_exists; eauto.
      eapply in_map in Hin. eapply Cofix; eauto. rewrite Forall_map.
      eapply Forall_impl; eauto. intros * HH. simpl in HH.
      rewrite ac_tl. now apply sub_clock_step.
  Qed.

  Lemma sc_parent :
    forall H b ck lck ss,
      Forall2 (NLSC.sem_clock H b) lck (map abstract_clock ss) ->
      In ck lck ->
      Forall (fun ck' => ck' = ck \/ clock_parent ck ck') lck ->
      NLSC.sem_clock H b ck (clocks_of ss).
  Proof.
    intros * Hsc Hin Hparent.
    pose proof (Forall2_in_left _ _ _ _ Hsc Hin) as [s (Hins & Hsc0)].
    rewrite Forall2_map_2 in Hsc. apply in_map_iff in Hins as [?(?&?)]. subst.
    assert (
        Forall (fun s' => sub_clock (abstract_clock x) (abstract_clock s')) ss
      ) as Hf. {
      apply Forall_forall; intros * Hx0.
      pose proof (Forall2_in_right _ _ _ _ Hsc Hx0) as [? (Hx1&Hsc1)].
      eapply Forall_forall in Hx1; eauto. destruct Hx1.
      subst.
      apply sem_clock_det with (2 := Hsc1) in Hsc0. now rewrite Hsc0.
      eapply sub_clock_parent; eauto.
    }
    apply sub_clock_sclocksof in Hf; auto. now rewrite Hf.
  Qed.

  Lemma wc_env_free_in_clock :
    forall x i ck vars,
      wc_env vars ->
      In (x, ck) vars ->
      Is_free_in_clock i ck ->
      exists ick, In (i, ick) vars.
  Proof.
    intros * WC Ix Hfree.
    revert x Ix. induction ck; inv Hfree;
    intros; eapply Forall_forall in WC; eauto; inv WC; eauto.
  Qed.

  Lemma idck_idents :
    forall l, LS.idents l = map fst (idck l).
  Proof.
    unfold LS.idents, idck. induction l; simpl; auto.
    f_equal. auto.
  Qed.

  Ltac inv_NoDup_fresh_ins H :=
    unfold L.anon_ins, L.fresh_ins in H; simpl in H;
    repeat rewrite idck_app.

  Lemma app_length_impl :
    forall {A: Type} (l1 l1' l2 l2' : list A),
      l1 ++ l2 = l1' ++ l2' ->
      length l1 = length l1' ->
      l2 = l2'.
  Proof.
    intros * Happ Hlen.
    apply f_equal with (f := skipn (length l1)) in Happ.
    rewrite Hlen, skipn_app, skipn_app in Happ; auto.
  Qed.

  Lemma app_length_impl' :
    forall {A: Type} (l1 l1' l2 l2' : list A),
      l1 ++ l2 = l1' ++ l2' ->
      length l1 = length l1' ->
      l1 = l1'.
  Proof.
    intros * Happ Hlen.
    apply f_equal with (f := firstn (length l1)) in Happ.
    rewrite Hlen in Happ at 2.
    do 2 rewrite CommonList.firstn_app in Happ; auto.
  Qed.

  (* TODO: move elsewhere *)
  Lemma Ino_Forall:
    forall (A : Type) (x : A) (xs : list (option A)) (P : option A -> Prop),
      Forall P xs -> Ino x xs -> P (Some x).
  Proof.
    intros * Hforall Hin.
    induction xs as [|a]; inversion Hin; inversion Hforall; subst; auto.
    destruct a; simpl in *; subst; tauto.
  Qed.

  Lemma In_clockof :
    forall ck e es,
      In ck (L.clockof e) ->
      In e es ->
      In ck (L.clocksof es).
  Proof.
    intros. unfold L.clocksof.
    rewrite in_flat_map. eauto.
  Qed.

  Lemma In_nclockof :
    forall ck e es,
      In ck (L.nclockof e) ->
      In e es ->
      In ck (L.nclocksof es).
  Proof.
    intros. unfold L.nclocksof.
    rewrite in_flat_map. eauto.
  Qed.

  Fact InMembers_fresh_in : forall x e es,
      In e es ->
      InMembers x (L.fresh_in e) ->
      InMembers x (L.fresh_ins es).
  Proof.
    intros * Hin Hinm.
    eapply LC.fresh_in_incl, incl_map with (f:=fst) in Hin.
    rewrite fst_InMembers in *. eauto.
  Qed.

  Fact InMembers_anon_in : forall x e es,
      In e es ->
      InMembers x (L.anon_in e) ->
      InMembers x (L.anon_ins es).
  Proof.
    intros * Hin Hinm.
    eapply LC.anon_in_incl, incl_map with (f:=fst) in Hin.
    rewrite fst_InMembers in *. eauto.
  Qed.

  Fact InMembers_anon_in_eq : forall x e es,
      In e es ->
      InMembers x (L.anon_in_eq e) ->
      InMembers x (L.anon_in_eqs es).
  Proof.
    intros * Hin Hinm.
    eapply LC.anon_in_eq_incl, incl_map with (f:=fst) in Hin.
    rewrite fst_InMembers in *. eauto.
  Qed.

  Fact Ino_In_anon_streams : forall x anns,
      Ino x (map (fun x => snd (snd x)) anns) ->
      InMembers x (L.anon_streams anns).
  Proof.
    intros x anns H.
    rewrite Ino_In, in_map_iff in H; destruct H as [[? [? ?]] [? ?]]; simpl in *; subst.
    rewrite fst_InMembers, in_map_iff.
    exists (x, (t, c)); split; auto.
    eapply map_filter_In; eauto.
  Qed.

  Lemma var_clock_defined:
    forall G vars e x,
      LC.wc_exp G vars e ->
      LC.wc_global G ->
      wc_env vars ->
      (Ino x (map snd (L.nclockof e))
       \/ Exists (Is_free_in_clock x) (L.clockof e)) ->
      InMembers x vars \/ InMembers x (L.fresh_in e).
  Proof.
    induction e using L.exp_ind2; intros * Hwc Hwcg Henv Hfree; simpl in Hfree.
    - inv Hwc. inversion_clear Hfree as [| Hfree']; try tauto.
      inversion_clear Hfree' as [?? Hf|?? Hf]; inv Hf.
    - inv Hwc.
      + inversion_clear Hfree as [[]| Hf]; intuition; simpl in *. subst.
        eauto using In_InMembers.
        unfold L.clock_of_nclock, stripname in Hf. simpl in Hf.
        eapply wc_env_free_in_clock in Henv as []; eauto using In_InMembers.
        now inv Hf.
      + inversion_clear Hfree as [[]| Hf]; intuition; simpl in *. subst.
        eauto using In_InMembers.
        unfold L.clock_of_nclock, stripname in Hf. simpl in Hf.
        eapply wc_env_free_in_clock in Henv as []; eauto using In_InMembers.
        now inv Hf.
    - (* Eunop *)
      inv Hwc. simpl in *. inversion_clear Hfree as [[|]|Hfree']; intuition.
      inversion_clear Hfree' as [?? Hf|?? Hf]; try now inv Hf.
      unfold L.clock_of_nclock, stripname in Hf. simpl in Hf.
      eapply IHe in Henv; eauto.
      right. rewrite H3. constructor; auto.
    - (* Ebinop *)
      inv Hwc. simpl in *. inversion_clear Hfree as [[|]|Hfree']; intuition.
      inversion_clear Hfree' as [?? Hf|?? Hf]; try now inv Hf.
      unfold L.clock_of_nclock, stripname in Hf. simpl in Hf.
      eapply IHe1 in Henv; eauto.
      2:{ take (L.clockof e1 = _) and rewrite it; eauto. }
      destruct Henv; auto. right. rewrite InMembers_app; auto.
    - (* Efby *)
      inv Hwc. take (Forall2 eq _ _) and apply Forall2_eq in it as Heq.
      rewrite Heq, Exists_exists in Hfree. destruct Hfree as [Hino|(?&Hin &?)].
      apply Ino_In in Hino. apply in_map_iff in Hino as ((?&?)&?&Hino).
      apply in_map_iff in Hino as ((?&?)&?&Hino).
      eapply Forall_forall in Hino; eauto. simpl in *. subst. inv Hino.
      unfold L.clocksof in Hin. apply in_flat_map in Hin as (?&?&?).
      eapply Forall_forall in H0; eauto.
      eapply H0 in Henv; auto; [|eapply Forall_forall|right; eapply Exists_exists];
        eauto.
      destruct Henv; auto. right.
      simpl. rewrite InMembers_app; right.
      eapply InMembers_fresh_in; eauto.
    - (* Ewhen *)
      inv Hwc. simpl in Hfree. destruct Hfree as [Hf|Hf].
      { clear - Hf. exfalso. induction tys; simpl in *; intuition. }
      rewrite CommonList.Exists_map in Hf. unfold L.clock_of_nclock, stripname in Hf.
      simpl in Hf. apply Exists_exists in Hf as (?&?&Hf).
      inv Hf; eauto using In_InMembers.
      destruct (L.clocksof es) eqn:Heql; simpl in *.
      take (length tys = 0) and apply length_zero_iff_nil in it. subst. contradiction.
      apply flat_map_ExistsIn in Heql as (?&?&?&Hckof).
      eapply Forall_forall in H; eauto. take (Forall (eq _) _) and inv it.
      eapply H in Henv; eauto. 2:{ eapply Forall_forall; eauto. }
      2:{ right. rewrite Hckof. eauto. } destruct Henv; auto. right.
      eapply InMembers_fresh_in; eauto.
    - (* Emerge *)
      inv Hwc. simpl in Hfree. destruct Hfree as [Hf|Hf].
      { clear - Hf. exfalso. induction tys; simpl in *; intuition. }
      rewrite CommonList.Exists_map in Hf. unfold L.clock_of_nclock, stripname in Hf.
      simpl in Hf. apply Exists_exists in Hf as (?&?&Hf).
      destruct (L.clocksof ets) eqn:Heql; simpl in *.
      take (length tys = 0) and apply length_zero_iff_nil in it. subst. contradiction.
      apply flat_map_ExistsIn in Heql as (?&?&?&Hckof).
      eapply Forall_forall in H; eauto. take (Forall (eq _) (_::_)) and inv it.
      eapply H with (x := x0) in Henv; eauto.
      2:{ eapply Forall_forall; [|eauto]. auto. }
      2:{ right. rewrite Hckof. left. now constructor. }
      destruct Henv; auto. right. rewrite InMembers_app; left.
      eapply InMembers_fresh_in; eauto.
    - (* Eite *)
      inv Hwc. simpl in Hfree. destruct Hfree as [Hf|Hf].
      { clear - Hf. exfalso. induction tys; simpl in *; intuition. }
      rewrite CommonList.Exists_map in Hf. unfold L.clock_of_nclock, stripname in Hf.
      simpl in Hf. apply Exists_exists in Hf as (?&?&Hf).
      eapply IHe in Henv; eauto.
      2:{ right. take (L.clockof e = _) and rewrite it. eauto. }
      destruct Henv; auto. right.
      simpl; rewrite InMembers_app; left; auto.
    - (* Eapp and Ereset *)
      inv Hwc; simpl.
      + destruct Hfree as [Hino| Hfree'].
        * right. rewrite InMembers_app; right.
          rewrite map_map in Hino.
          eapply Ino_In_anon_streams; eauto.
        * apply Exists_exists in Hfree' as (?&Hin&?).
          assert (Hwio := H8). assert (Hwcg' := Hwcg).
          apply in_map_iff in Hin as ((?&?)&?&?). rewrite Forall2_map_2 in Hwio.
          eapply Forall2_in_right in Hwio as ((?&ck)&?&(?&Hinst)); eauto.
          eapply LC.wc_find_node in Hwcg as (?&(?& WCio&?)); eauto.
          unfold L.clock_of_nclock, stripname in *. simpl in *. subst.
          eapply instck_inv in Hinst as [Hbck|(?&Heq&?)]; eauto.
          -- (* la variable est dans bck, donc dans une entrée *)
            destruct (L.nclocksof es) as [|(?&?)] eqn:Heql.
            { inversion H7 as [Hlen|].
              apply (f_equal (@length (ident * clock))) in Hlen; simpl in Hlen.
              unfold idck in Hlen. rewrite map_length in Hlen.
              pose proof (L.n_ingt0 n). omega. }
            inversion_clear H7 as [|???? (?&?)].
            eapply instck_free_bck in Hbck; eauto.
            apply flat_map_ExistsIn in Heql as (?&?&?&Hnc).
            eapply Forall_forall in H0; eauto. eapply H0 in Hwcg'; eauto.
            2:{ eapply Forall_forall in H5; eauto. }
            2:{ rewrite L.clockof_nclockof. rewrite Hnc. simpl in *. eauto. }
            destruct Hwcg'; auto. right.
            rewrite InMembers_app; left.
            eapply InMembers_fresh_in; eauto.
          -- eapply wc_env_free_in_clock with (ck := ck) in WCio as (?&Hin); eauto.
             2:{ rewrite idck_app, in_app. eauto. }
             rewrite idck_app, in_app in Hin. destruct Hin as [Hini | Hino].
             (* Hini, Hypothèse d'induction *)
             eapply Forall2_in_left in H7 as (?&Hin&(Heq'&?)); eauto. simpl in *.
             eapply L.In_nclocksof in Hin as (?&?&?). eapply Forall_forall in H0; eauto.
             eapply H0 in Hwcg' as HH; eauto.
             2:{ eapply Forall_forall; eauto. }
             2:{ left. instantiate (1 := x).
                 rewrite Ino_In, <- Heq, Heq', in_map_iff; eauto. }
             ++ destruct HH; auto. right.
                rewrite InMembers_app; left.
                eapply InMembers_fresh_in; eauto.
             ++ (* Hino *)
               right. rewrite InMembers_app; right.
               eapply Forall2_in_left in H8 as (nc &?&(Heq'&?)); eauto.
               simpl in *. eapply Ino_In_anon_streams.
               rewrite Heq in Heq'.
               rewrite in_map_iff in H8; destruct H8 as [[? ?] [? ?]]; simpl in *; subst.
               rewrite Ino_In, in_map_iff. unfold L.stream_name.
               exists (t0, nc). split; auto.
      + destruct Hfree as [Hino| Hfree'].
        * right. repeat (rewrite InMembers_app; right).
          rewrite map_map in Hino.
          eapply Ino_In_anon_streams; eauto.
        * apply Exists_exists in Hfree' as (?&Hin&?).
          assert (Hwio := H8). assert (Hwcg' := Hwcg).
          apply in_map_iff in Hin as ((?&?)&?&?). rewrite Forall2_map_2 in Hwio.
          eapply Forall2_in_right in Hwio as ((?&ck)&?&(?&Hinst)); eauto.
          eapply LC.wc_find_node in Hwcg as (?&(?& WCio&?)); eauto.
          unfold L.clock_of_nclock, stripname in *. simpl in *. subst.
          eapply instck_inv in Hinst as [Hbck|(?&Heq&?)]; eauto.
          -- (* la variable est dans bck, donc dans une entrée *)
            destruct (L.nclocksof es) as [|(?&?)] eqn:Heql.
            { inversion H7 as [Hlen|].
              apply (f_equal (@length (ident * clock))) in Hlen; simpl in Hlen.
              unfold idck in Hlen. rewrite map_length in Hlen.
              pose proof (L.n_ingt0 n). omega. }
            inversion_clear H7 as [|???? (?&?)].
            eapply instck_free_bck in Hbck; eauto.
            apply flat_map_ExistsIn in Heql as (?&?&?&Hnc).
            eapply Forall_forall in H0; eauto. eapply H0 in Hwcg'; eauto.
            2:{ eapply Forall_forall in H5; eauto. }
            2:{ rewrite L.clockof_nclockof. rewrite Hnc. simpl in *. eauto. }
            destruct Hwcg'; auto. right.
            rewrite InMembers_app; left.
            eapply InMembers_fresh_in; eauto.
          -- eapply wc_env_free_in_clock with (ck := ck) in WCio as (?&Hin); eauto.
             2:{ rewrite idck_app, in_app. eauto. }
             rewrite idck_app, in_app in Hin. destruct Hin as [Hini | Hino].
             (* Hini, Hypothèse d'induction *)
             eapply Forall2_in_left in H7 as (?&Hin&(Heq'&?)); eauto. simpl in *.
             eapply L.In_nclocksof in Hin as (?&?&?). eapply Forall_forall in H0; eauto.
             eapply H0 in Hwcg' as HH; eauto.
             2:{ eapply Forall_forall; eauto. }
             2:{ left. instantiate (1 := x).
                 rewrite Ino_In, <- Heq, Heq', in_map_iff; eauto. }
             ++ destruct HH; auto. right.
                rewrite InMembers_app; left.
                eapply InMembers_fresh_in; eauto.
             ++ (* Hino *)
               right. repeat (rewrite InMembers_app; right).
               eapply Forall2_in_left in H8 as (nc &?&(Heq'&?)); eauto.
               simpl in *. eapply Ino_In_anon_streams.
               rewrite Heq in Heq'.
               rewrite in_map_iff in H8; destruct H8 as [[? ?] [? ?]]; simpl in *; subst.
               rewrite Ino_In, in_map_iff. unfold L.stream_name.
               exists (t0, nc). split; auto.
  Qed.

  Corollary free_clock_defined :
    forall G vars e x,
      LC.wc_exp G vars e ->
      LC.wc_global G ->
      wc_env vars ->
      Exists (Is_free_in_clock x) (L.clockof e) ->
      InMembers x vars \/ InMembers x (L.fresh_in e).
  Proof.
    eauto using var_clock_defined.
  Qed.

  Corollary snd_nclocks_defined :
    forall G vars e x,
      LC.wc_exp G vars e ->
      LC.wc_global G ->
      wc_env vars ->
      Ino x (map snd (L.nclockof e)) ->
      InMembers x vars \/ InMembers x (L.fresh_in e).
  Proof.
    eauto using var_clock_defined.
  Qed.

  Corollary snd_nclocks_fresh :
    forall G vars e x,
      LC.wc_exp G vars e ->
      LC.wc_global G ->
      wc_env vars ->
      Ino x (map snd (L.nclockof e)) ->
      ~ InMembers x vars ->
      InMembers x (L.fresh_in e).
  Proof.
    intros * ??? Hino ?. eapply snd_nclocks_defined in Hino as []; eauto.
    contradiction.
  Qed.

  Lemma wc_app_reset:
    forall G vars f es r anns,
      LC.wc_exp G vars (L.Eapp f es r anns) ->
      exists n bck sub,
        (Forall (LC.wc_exp G vars) es
        /\ L.find_node f G = Some n
        /\ Forall2 (LC.WellInstantiated bck sub) (idck (L.n_in n)) (L.nclocksof es)
        /\ Forall2 (LC.WellInstantiated bck sub) (idck (L.n_out n)) (map snd anns)).
  Proof.
    intros * Hwc.
    inv Hwc; eauto 7.
  Qed.

  Ltac simpl_Foralls :=
    repeat
      match goal with
      | H: Forall _ [] |- _ => inv H
      | H: Forall _ [_] |- _ => inv H
      | H: Forall _ (_ :: _) |- _ => inv H
      | H: Forall2 _ [_] _ |- _ => inv H
      | H: Forall2 _ [] _ |- _ => inv H
      | H: Forall2 _ _ [_] |- _ => inv H
      | H: Forall2 _ _ [] |- _ => inv H
      end.

  Fact NoDupMembers_fresh_in : forall e es,
      In e es ->
      NoDupMembers (L.fresh_ins es) ->
      NoDupMembers (L.fresh_in e).
  Proof.
    intros * Hin Hndup.
    unfold L.fresh_ins in *.
    induction es; inv Hin; simpl in Hndup.
    - apply NoDupMembers_app_l in Hndup; auto.
    - apply NoDupMembers_app_r in Hndup; auto.
  Qed.

  Corollary NoDupMembers_fresh_in' : forall vars e es,
      In e es ->
      NoDupMembers (vars ++ L.fresh_ins es) ->
      NoDupMembers (vars ++ L.fresh_in e).
  Proof.
    intros * Hin Hndup.
    apply NoDupMembers_app.
    - apply NoDupMembers_app_l in Hndup; auto.
    - apply NoDupMembers_app_r in Hndup; auto.
      eapply NoDupMembers_fresh_in; eauto.
    - intros x HIn contra.
      eapply NoDupMembers_app_InMembers in Hndup; eauto.
      eapply InMembers_fresh_in in contra; eauto.
  Qed.

  Fact NoDupMembers_anon_in_eq : forall eq eqs,
      In eq eqs ->
      NoDupMembers (L.anon_in_eqs eqs) ->
      NoDupMembers (L.anon_in_eq eq).
  Proof.
    intros * Hin Hndup.
    unfold L.fresh_ins in *.
    induction eqs; inv Hin; simpl in Hndup.
    - apply NoDupMembers_app_l in Hndup; auto.
    - apply NoDupMembers_app_r in Hndup; auto.
  Qed.

  Corollary NoDupMembers_anon_in_eq' : forall vars eq eqs,
      In eq eqs ->
      NoDupMembers (vars ++ L.anon_in_eqs eqs) ->
      NoDupMembers (vars ++ L.anon_in_eq eq).
  Proof.
    intros * Hin Hndup.
    apply NoDupMembers_app.
    - apply NoDupMembers_app_l in Hndup; auto.
    - apply NoDupMembers_app_r in Hndup; auto.
      eapply NoDupMembers_anon_in_eq; eauto.
    - intros x HIn contra.
      eapply NoDupMembers_app_InMembers in Hndup; eauto.
      eapply InMembers_anon_in_eq in contra; eauto.
  Qed.

  Fact NoDupMembers_idck : forall (xs : list (ident * (type * clock))),
      NoDupMembers (idck xs) <-> NoDupMembers xs.
  Proof.
    intros. repeat rewrite fst_NoDupMembers.
    rewrite <- idck_idents. reflexivity.
  Qed.

  (* TODO: move somewhere *)
  Definition adds_opt' {A : Type} (xos: list (option positive))
             (vs : list A) (e : Env.t A) : Env.t A :=
    fold_right (fun (xov: option positive * A) env =>
                  match xov with
                  | (Some x, v) => Env.add x v env
                  | _ => env end) e (combine xos vs).

  Lemma find_adds_opt'_spec_Some:
    forall {A} xs vs x (a : A) m,
      length xs = length vs ->
      Env.find x (adds_opt' xs vs m) = Some a ->
      List.In (Some x, a) (combine xs vs)
      \/ Env.find x m = Some a.
  Proof.
    unfold adds_opt'.
    induction xs as [|x'], vs as [|v']; simpl; auto; try discriminate.
    intros * Length Find; inv Length.
    destruct x'.
    - destruct (Pos.eq_dec x p) as [|].
      + subst; rewrite Env.gss in Find; inv Find; auto.
      + rewrite Env.gso in Find; auto.
        apply IHxs in Find as [|()]; auto.
    - apply IHxs in Find as [|]; auto.
  Qed.

  Lemma find_gsso_opt':
    forall {A}x x' xs (vs: list A) S,
      Some x <> x' ->
      Env.find x (adds_opt' (x' :: xs) vs S) =
      Env.find x (adds_opt' xs (tl vs) S).
  Proof.
    intros * Hneq.
    unfold adds_opt'.
    destruct vs. now destruct xs; auto.
    destruct x'; simpl; auto.
    rewrite Env.gso; auto. intro. apply Hneq. congruence.
  Qed.

  Lemma find_gsss_opt':
    forall {A} x v xs (vs: list A) S,
      Env.find x (adds_opt' (Some x :: xs) (v :: vs) S) = Some v.
  Proof.
    intros. unfold adds_opt'. apply Env.gss.
  Qed.

  Lemma find_In_gsso_opt':
    forall {A} x ys (vs: list A) env,
      ~ Ino x ys ->
      Env.find x (adds_opt' ys vs env) = Env.find x env.
  Proof.
    intros ? x ys vs env Hin.
    revert vs; induction ys; intro vs; simpl; auto.
    rewrite find_gsso_opt'.
    - apply IHys. rewrite Ino_In in *. intuition.
    - intro. apply Hin. rewrite Ino_In. now left.
  Qed.

  (* TODO: move *)
  Lemma adds_opt'_cons_Some:
    forall {A} xs x (v: A) vs e,
      adds_opt' (Some x :: xs) (v :: vs) e =
      Env.add x v (adds_opt' xs vs e).
  Proof.
    induction xs as [|x']; intros; simpl; auto.
  Qed.

  Lemma adds_opt'_cons_None:
    forall {A} xs (v : A) vs e,
      adds_opt' (None :: xs) (v :: vs) e = adds_opt' xs vs e.
  Proof. auto. Qed.

  Lemma adds_opt'_app :
    forall {A} xs (vs : list A) xs' vs' m,
      length xs = length vs ->
      adds_opt' (xs ++ xs') (vs ++ vs') m
      = adds_opt' xs vs (adds_opt' xs' vs' m).
  Proof.
    induction xs as [|x xs IH]; simpl; intros * Hlen.
    - symmetry in Hlen. apply length_zero_iff_nil in Hlen. subst. auto.
    - destruct vs as [| v vs]; simpl in Hlen; inv Hlen.
      destruct x; simpl.
      + do 2 rewrite adds_opt'_cons_Some.
        rewrite IH; auto.
      + do 2 rewrite adds_opt'_cons_None.
        rewrite IH; auto.
  Qed.

  Lemma adds_opt'_nil:
    forall {A} vs (e : Env.t A),
      adds_opt' [] vs e = e.
  Proof. auto. Qed.

  Lemma adds_opt'_nil':
    forall {A} xs (e : Env.t A),
      adds_opt' xs [] e = e.
  Proof.
    unfold adds_opt'.
    setoid_rewrite combine_nil_r. simpl. auto.
  Qed.

  Lemma adds_opt'_None:
    forall {A B} xs vs (e : Env.t A),
      adds_opt' (map (fun _ : B => None) xs) vs e = e.
  Proof.
    induction xs; simpl. now setoid_rewrite adds_opt'_nil.
    destruct vs. now setoid_rewrite adds_opt'_nil'.
    setoid_rewrite adds_opt'_cons_None. auto.
  Qed.

  Lemma sc_switch_adds :
    forall H b ck cks xs ss,
      NLSC.sem_clock (adds_opt' xs ss H) b ck cks ->
      (forall x, Is_free_in_clock x ck -> ~Ino x xs) ->
      NLSC.sem_clock H b ck cks.
  Proof.
    intros * Hsc Hino. eapply sc_switch_env; eauto.
    intros * Hfree. apply Hino in Hfree.
    rewrite find_In_gsso_opt'; auto.
  Qed.

  Lemma sc_switch_adds' :
    forall H b ck cks xs ss,
      NLSC.sem_clock H b ck cks ->
      (forall x, Is_free_in_clock x ck -> ~Ino x xs) ->
      NLSC.sem_clock (adds_opt' xs ss H) b ck cks.
  Proof.
    intros * Hsc Hino. eapply sc_switch_env; eauto.
    intros * Hfree. apply Hino in Hfree.
    rewrite find_In_gsso_opt'; auto.
  Qed.

  Lemma in_app_weak :
    forall {A} (x : A) l l',
      In x l -> In x (l ++ l').
  Proof.
    intros. apply in_app; auto.
  Qed.

  (* permute quantifiers to ease instantiation *)
  Lemma Forall2_in_right':
    forall {A B} P (xs: list A) (ys: list B),
      Forall2 P xs ys ->
      forall y,
        In y ys ->
        exists x, In x xs /\ P x y.
  Proof.
    eauto using Forall2_in_right.
  Qed.

  (* induction hypothesis over the program *)
  Definition sc_nodes (G : L.global) : Prop :=
    forall H f n xs (* vs *) os,
      LS.sem_node G f xs os ->
      L.find_node f G = Some n ->
      Forall2 (LS.sem_var H) (LS.idents (L.n_in n)) xs ->
      (* Forall2 (LS.sem_var H) (LS.idents (L.n_vars n)) vs -> *)
      Forall2 (LS.sem_var H) (LS.idents (L.n_out n)) os ->
      Forall2 (fun xc => NLSC.sem_clock H (clocks_of xs) (snd xc))
              (idck (L.n_in n)) (map abstract_clock xs) ->
      (* Forall2 (fun xc => NLSC.sem_clock H (clocks_of xs) (snd xc)) *)
      (*         (idck (L.n_vars n)) (map abstract_clock vs) /\ *)
      Forall2 (fun xc => NLSC.sem_clock H (clocks_of xs) (snd xc))
              (idck (L.n_out n)) (map abstract_clock os).
  Hint Unfold sc_nodes.

  Definition filter_anons (env : list (ident * clock)) (ncs : list nclock) :
    list (option ident) :=
    map (fun nc => match snd nc with
                | None => None
                | Some x => if mem_assoc_ident x env
                           then None
                           else Some x
                end) ncs.

  Lemma filter_anons_spec :
    forall env ncs x,
      Ino x (filter_anons env ncs) ->
      Ino x (map snd ncs) /\ ~ InMembers x env.
  Proof.
    unfold filter_anons.
    intros * Hino. rewrite Ino_In, in_map_iff in Hino.
    destruct Hino as [(c & o) (H & ?)]. simpl in H.
    destruct o; cases_eqn H; inv H. split.
    rewrite Ino_In, in_map_iff. esplit; split; eauto; simpl; eauto.
    apply NotIn_NotInMembers; intros. now apply mem_assoc_ident_false.
  Qed.

  Lemma filter_anons_ino :
    forall env ncs x,
    Ino x (filter_anons env ncs) ->
    ~ InMembers x env.
  Proof.
    intros. eapply filter_anons_spec; eauto.
  Qed.

  Lemma filter_anons_app :
    forall env l l',
      filter_anons env (l ++ l') = filter_anons env l ++ filter_anons env l'.
  Proof.
    unfold filter_anons. now setoid_rewrite map_app.
  Qed.

  Lemma filter_anons_filter :
    forall env x xs,
      Ino x (filter_anons env xs) ->
      Ino x (map snd xs).
  Proof.
    intros * Hin. induction xs; inv Hin; [| right; auto].
    destruct a as [? []]; simpl in *; cases; tauto.
  Qed.

  Lemma filter_anons_filter' :
    forall env x xs,
      Ino x (map snd xs) ->
      ~ Ino x (filter_anons env xs) ->
      InMembers x env.
  Proof.
    intros * Hin Hnin. induction xs. inv Hin.
    rewrite Ino_In in Hin, Hnin, IHxs, IHxs. simpl in *.
    apply not_or' in Hnin as [Ha Hnin]. destruct Hin as [Heq | Hin].
    + destruct (snd a); inv Heq. destruct (mem_assoc_ident x env) eqn:Hm.
      apply mem_assoc_ident_true in Hm as []. eauto using In_InMembers.
      congruence.
    + apply IHxs in Hin; auto.
  Qed.

  Fact filter_anons_In : forall x vars anns,
      Ino x (filter_anons vars (map snd anns)) ->
      InMembers x (L.anon_streams anns).
  Proof.
    intros * Hino.
    induction anns; simpl in *; auto.
    destruct a as [? [? [?|]]]; simpl in *.
    - destruct Hino; auto.
      left. destruct mem_assoc_ident; simpl in H; inv H; auto.
    - destruct Hino; [inv H|]; auto.
  Qed.

  Fact filter_anons_NoDupMembers : forall vars anns,
      NoDupMembers (L.anon_streams anns) ->
      NoDupo (filter_anons vars (map snd anns)).
  Proof.
    intros * H.
    induction anns; simpl in *; [constructor|].
    destruct a as [? [? [?|]]].
    - inv H; simpl.
      destruct mem_assoc_ident; constructor; auto.
      intro contra; apply H2.
      eapply filter_anons_In; eauto.
    - constructor; auto.
  Qed.

  Lemma nodupo_filter_anons :
    forall G env e,
      LC.wc_exp G env e ->
      NoDupMembers (L.fresh_in e) ->
      NoDupo (filter_anons env (L.nclockof e)).
  Proof.
    destruct e; intros Hwc Hdf; inv Hwc; simpl.
    1,3,4,5:repeat constructor.
    - destruct (mem_assoc_ident i env); repeat constructor; auto.
    - clear - H6. induction l1; simpl in *. constructor.
      inv H6. unfold L.unnamed_stream in *. destruct a as (?&?&?).
      simpl in *. subst. constructor. auto.
    - clear - tys. induction tys; simpl; constructor. auto.
    - clear - tys. induction tys; simpl; constructor. auto.
    - clear - tys. induction tys; simpl; constructor. auto.
    - simpl in Hdf.
      apply NoDupMembers_app_r in Hdf.
      eapply filter_anons_NoDupMembers in Hdf; eauto.
    - simpl in Hdf.
      repeat apply NoDupMembers_app_r in Hdf.
      eapply filter_anons_NoDupMembers in Hdf; eauto.
  Qed.

  (* TODO: move *)
  Lemma LiftO_impl:
    forall {A} d (P P' : A -> Prop) (x : option A),
      (forall a, P a -> P' a) ->
      LiftO d P x ->
      LiftO d P' x.
  Proof.
    intros. destruct x; simpl in *; auto.
  Qed.

  (* TODO: move *)
  Lemma ino_dec:
    forall {A} (x : A) xos,
      (forall x y : A, {x = y} + {x <> y}) ->
      Ino x xos \/ ~Ino x xos.
  Proof.
    intros * H; rewrite Ino_In. eapply ListDec.In_decidable.
    intros y z. destruct y as [a|], z as [b|]; try (right; congruence).
    destruct (H a b); [left|right]; congruence.
    now left.
  Qed.

  (* TODO: move *)
  Lemma find_adds_opt'_disj:
    forall {A} (x : ident) xs xs' vs vs' (e : Env.t A),
      (forall x, Ino x xs -> ~ Ino x xs') ->
      Ino x xs ->
      Env.find x (adds_opt' xs vs e)
      = Env.find x (adds_opt' xs vs (adds_opt' xs' vs' e)).
  Proof.
    intros * Hino Hin.
    revert dependent x. revert vs. induction xs; intros; inv Hin.
    destruct a as [p|]; take (LiftO _ _ _) and inv it. destruct vs.
    do 2 rewrite adds_opt'_nil'.
    specialize (Hino p). simpl in Hino.
    specialize (Hino (or_introl (eq_refl p))).
    now rewrite find_In_gsso_opt'.
    now rewrite 2 find_gsss_opt'.
    destruct a as [p|], vs.
    + eapply IHxs with (vs := []) in H; eauto.
      2: intros; apply Hino; now right.
      now rewrite 2 adds_opt'_nil' in *.
    + destruct (decidable_eq_ident x p). subst.
      now rewrite 2 find_gsss_opt'.
      rewrite 2 find_gsso_opt'; simpl. 2-3: intro Heq; inv Heq; auto.
      apply IHxs; auto. intros. apply Hino. now right.
    + eapply IHxs with (vs := []) in H; eauto.
      2: intros; apply Hino; now right.
      now rewrite 2 adds_opt'_nil' in *.
    + rewrite 2 adds_opt'_cons_None; auto.
      apply IHxs; auto. intros. apply Hino. now right.
  Qed.

  Lemma find_permute_adds_opt':
    forall {A} (x : ident) xs xs' vs vs' (e : Env.t A),
      (forall x, Ino x xs -> ~ Ino x xs') ->
      Env.find x (adds_opt' xs vs (adds_opt' xs' vs' e))
      = Env.find x (adds_opt' xs' vs' (adds_opt' xs vs e)).
  Proof.
    intros * Hino.
    destruct (ino_dec x xs (ident_eq_dec)) as [Hin|Hin].
    - erewrite <- find_adds_opt'_disj; eauto.
      apply Hino in Hin. setoid_rewrite find_In_gsso_opt' at 2; auto.
    - rewrite find_In_gsso_opt'; auto.
      destruct (ino_dec x xs' (ident_eq_dec)) as [Hin'|Hin'].
      erewrite <- find_adds_opt'_disj; eauto. intros ?? HH.
      now apply Hino in HH.
      rewrite 3 find_In_gsso_opt'; auto.
  Qed.

  Lemma sc_permute_adds :
    forall H b ck cks xs vs xs' vs',
      NLSC.sem_clock (adds_opt' xs vs (adds_opt' xs' vs' H)) b ck cks ->
      (forall x, Ino x xs -> ~ Ino x xs') ->
      NLSC.sem_clock (adds_opt' xs' vs' (adds_opt' xs vs H)) b ck cks.
  Proof.
    intros * Hsc Hino. eapply sc_switch_env; eauto.
    intros * Hfree.
    rewrite <- find_permute_adds_opt'; auto.
  Qed.

  Lemma sc_permute_adds_nest :
    forall H b ck cks xs vs xs' vs' xs'' vs'',
      NLSC.sem_clock (adds_opt' xs vs (adds_opt' xs' vs' (adds_opt' xs'' vs'' H))) b ck cks ->
      (forall x, Ino x xs -> ~ Ino x xs') ->
      (forall x, Ino x xs -> ~ Ino x xs'') ->
      length xs' = length vs' ->
      NLSC.sem_clock (adds_opt' xs' vs' (adds_opt' xs'' vs'' (adds_opt' xs vs H))) b ck cks.
  Proof.
    intros * Hsc Hino Hino' Hlen. eapply sc_switch_env; eauto.
    intros * Hfree.
    rewrite <- adds_opt'_app; auto. setoid_rewrite <- adds_opt'_app at 3; auto.
    rewrite find_permute_adds_opt'; auto.
    intros ? HH ?. apply ino_app_iff in HH as [Hin|Hin]; eauto.
    apply Hino in Hin; auto. apply Hino' in Hin; auto.
  Qed.

  (* TODO: move *)
  Lemma find_adds_opt'_ino:
    forall {A} (x : ident) xs vs (e : Env.t A),
      length xs = length vs ->
      Ino x xs ->
      Env.find x (adds_opt' xs vs e)
      = Env.find x (adds_opt' xs vs (Env.empty A)).
  Proof.
    induction xs. inversion 2. intros * Hlen Hino.
    destruct vs. inv Hlen. apply Ino_In in Hino. inv Hino.
    - now rewrite 2 find_gsss_opt'.
    - destruct a as [p|]. destruct (ident_eq_dec x p).
      subst. now rewrite 2 find_gsss_opt'.
      rewrite 2 find_gsso_opt'; try (intro HH; inv HH; auto).
      simpl. apply IHxs; auto. now apply Ino_In.
      rewrite 2 adds_opt'_cons_None. apply IHxs; auto. now apply Ino_In.
  Qed.

  (* TODO: move *)
  Lemma in_combine_nodup :
    forall {A B} xs ys (x : A) (y : B) y',
      NoDup xs ->
      In (x, y) (combine xs ys) ->
      In (x, y') (combine xs ys) ->
      y = y'.
  Proof.
    induction xs. inversion 2. intros * Hdup Hin Hin'.
    destruct ys. inv Hin. inv Hin; inv Hin'; try congruence.
    - inv H. inv Hdup. now take (In _ _) and apply in_combine_l in it.
    - inv H0. inv Hdup. now take (In _ _) and apply in_combine_l in it.
    - inv Hdup. eauto.
  Qed.

  Lemma In_find_adds_opt':
    forall {A} x (v : A) xs vs m,
      NoDupo xs ->
      In (Some x, v) (combine xs vs) ->
      Env.find x (adds_opt' xs vs m) = Some v.
  Proof.
    induction xs. inversion 2.
    intros * Hdupo Hino. destruct vs. rewrite combine_nil_r in Hino.
    inv Hino. inv Hino. inv H. now rewrite find_gsss_opt'.
    destruct a as [p|]; inv Hdupo; try rewrite adds_opt'.
    destruct (Pos.eq_dec x p). subst.
    + now apply in_combine_l, Ino_In in H.
    + rewrite find_gsso_opt'; auto. congruence.
    + rewrite adds_opt'_cons_None; eauto.
  Qed.

  Lemma NoDupo_app':
    forall (A : Type) (xs ws : list (option A)),
      NoDupo xs ->
      NoDupo ws ->
      (forall x : A, Ino x xs -> ~ Ino x ws) ->
      NoDupo (xs ++ ws).
  Proof.
    induction xs as [|[]]; intros * D1 D2 Hino; simpl; auto.
    - constructor. inv D1. rewrite Ino_In in *. rewrite in_app.
      intros []; auto. specialize (Hino a).
      apply Hino; simpl; rewrite Ino_In in *; auto.
      inv D1. apply IHxs; auto. intros. apply Hino. now right.
    - inv D1. constructor. apply IHxs; auto. intros. apply Hino. now right.
  Qed.

  (* TODO: move to Lsyntax *)
  Lemma In_snd_nclocksof:
    forall n es,
      In n (map snd (L.nclocksof es)) ->
      exists e, In e es /\ In n (map snd (L.nclockof e)).
  Proof.
    intros * Hin. apply in_map_iff in Hin as (?&?&Hin).
    apply L.In_nclocksof in Hin as (e&?&?).
    exists e. split; auto. apply in_map_iff; eauto.
  Qed.

  Lemma filter_nclock_eq :
    forall G env e,
      LC.wc_exp G env e ->
      filter_anons env (L.nclockof (e)) =
      match e with
      | L.Eapp _ _ _ anns => filter_anons env (map snd anns)
      | _ => map (fun _ => None) (L.nclockof (e))
      end.
  Proof.
    destruct e; intros Hwc; inv Hwc; simpl; auto.
    - take (In _ _) and cases_eqn it. eapply mem_assoc_ident_false in it; tauto.
    - eapply map_ext_in; eauto. intros (?&?) Hin.
      apply in_map_iff in Hin as ((?&?)&?&?).
      take (_ L.unnamed_stream _) and eapply Forall_forall in it as un; eauto.
      unfold  L.unnamed_stream in un. now repeat (simpl in *; subst).
    - eapply map_ext_in; eauto. intros (?&?) Hin.
      apply in_map_iff in Hin as (?&HH&?). inv HH. now simpl.
    - eapply map_ext_in; eauto. intros (?&?) Hin.
      apply in_map_iff in Hin as (?&HH&?). inv HH. now simpl.
    - eapply map_ext_in; eauto. intros (?&?) Hin.
      apply in_map_iff in Hin as (?&HH&?). inv HH. now simpl.
  Qed.

  Lemma clockof_defined:
    forall G env e,
      LT.wt_exp G (idty env) e ->
      LC.wc_exp G (idck env) e ->
      forall ck x,
      In ck (L.clockof e) ->
      Is_free_in_clock x ck ->
      match e with
      | L.Eapp _ _ _ anns => True
      | _ => InMembers x env
      end.
  Proof.
    destruct e; intros * Hwt Hwc * Hin Hfr; simpl in *; auto.
    - inv Hin; inv Hfr; tauto.
    - inv Hin; intuition; inv Hwt; inv Hwc;
        eapply LT.wt_nclock_Is_free_in in H2; eauto;
          eapply InMembers_idty; eauto.
    - inv Hin; intuition; inv Hwt; inv Hwc.
      eapply LT.wt_nclock_Is_free_in in H5; eauto.
      eapply InMembers_idty; eauto.
    - inv Hin; intuition; inv Hwt; inv Hwc.
      eapply LT.wt_nclock_Is_free_in in H8; eauto.
      eapply InMembers_idty; eauto.
    - inv Hwt; inv Hwc.
      eapply LT.wt_clock_Is_free_in with (env:=idty env) in Hfr; eauto. eapply InMembers_idty; eauto.
      rewrite Forall_map, Forall_forall in H6. unfold L.clock_of_nclock, stripname in *.
      apply in_map_iff in Hin as [[? ?] [? Hin]].
      apply H6 in Hin; simpl in *; subst; inv Hin; auto.
    - inv Hwt; inv Hwc.
      eapply LT.wt_clock_Is_free_in with (env:=idty env) in Hfr; eauto. eapply InMembers_idty; eauto.
      unfold L.clock_of_nclock, stripname in *.
      simpl in Hin. apply in_map_iff in Hin as [? [? _]]; subst. inv H6; auto.
    - inv Hwt; inv Hwc.
      eapply LT.wt_clock_Is_free_in with (env:=idty env) in Hfr; eauto. eapply InMembers_idty; eauto.
      unfold L.clock_of_nclock, stripname in *.
      simpl in Hin. apply in_map_iff in Hin as [? [? _]]; subst. inv H8; auto.
    - inv Hwt; inv Hwc.
      eapply LT.wt_clock_Is_free_in with (env:=idty env) in Hfr; eauto. eapply InMembers_idty; eauto.
      unfold L.clock_of_nclock, stripname in *.
      simpl in Hin. apply in_map_iff in Hin as [? [? _]]; subst. inv H9; auto.
  Qed.

  (* Given a [sem_clock] hypothesis over local expressions [es],
     build a global environment (disjoint union of the respective
     environments) which could be used for the whole [L.clocksof es]
   *)
  Lemma sc_union_envs :
    forall G es env H b ss0,
      Forall (LT.wt_exp G (idty env)) es ->
      Forall (LC.wc_exp G (idck env)) es ->
      Forall2 (LS.sem_exp G H b) es ss0 ->
      LC.wc_global G ->
      wc_env (idck env) ->
      NoDupMembers (env++L.fresh_ins es) ->
      Forall2
        (fun (e : L.exp) (ss : list (Stream value)) =>
           match e with
           | L.Eapp _ _ _ anns =>
             exists ncs nss,
             Datatypes.length ncs = Datatypes.length nss /\
             Forall (LiftO True (fun x : ident => InMembers x (L.fresh_in e))) ncs /\
             (let H := adds_opt' ncs nss H in
              let H0 := adds_opt' (filter_anons (idck env)(map snd anns)) ss H in
              Forall2 (NLSC.sem_clock H0 b) (L.clockof e) (map abstract_clock ss))
           | _ => Forall2 (NLSC.sem_clock H b) (L.clockof e) (map abstract_clock ss)
           end) es ss0
      ->
      exists ncs nss,
        Datatypes.length ncs = Datatypes.length nss /\
        Forall (LiftO True (fun x : ident => Exists (fun e => InMembers x (L.fresh_in e)) es)) ncs /\
        (let H0 := adds_opt' ncs nss H in
         let H1 := adds_opt' (filter_anons (idck env)(L.nclocksof es)) (concat ss0) H0 in
         Forall2 (NLSC.sem_clock H1 b) (L.clocksof es)
                 (map abstract_clock (concat ss0))).
  Proof.
    intros * Hwt Hwc Hse Hwcg Henv Hndup Hes.
    revert dependent ss0.
    induction es; intros; inv Hes. exists [], []. now simpl.
    assert (Hwc' := Hwc). inv Hse. inv Hwt. inv Hwc'.
    inv_NoDup_fresh_ins Hndup.
    take (Forall (LC.wc_exp _ _) _) and eapply IHes in it
      as (ncs & nss & Hlen & Hfresh & Hscl); eauto.
    Local Ltac solve_length :=
      rewrite map_length, L.nclockof_length; eapply length_clockof; eauto.
    Local Ltac solve_NoDupMembers H :=
      eapply NoDupMembers_app_InMembers in H; eauto;
      eapply H, InMembers_app, or_intror, InMembers_fresh_in; eauto.
    simpl in *. destruct a.
    1-8: exists ncs,nss; split; auto; split;
                 [ apply Forall_impl with (2 := Hfresh); auto; intros;
                   eapply LiftO_impl; eauto; intros; now right |].
    (* all cases except Eapp are identical... *)
    (* { *)
    (*   (* clear - Henv Hwc H2 H10 H5 Hfresh H13 Hscl. *) *)
    (*   inv Hwc. rewrite map_app. apply Forall2_app. *)
    (*   - take (_ _ (L.clockof _) (map abstract_clock _)) and *)
    (*          eapply Forall2_impl_In in it; eauto. intros ck ? Hinck ??. *)
    (*     erewrite filter_anons_app, filter_nclock_eq, *)
    (*     adds_opt'_app, adds_opt'_None; eauto. 2: solve_length. *)
    (*     apply sc_switch_adds'; simpl; eauto. *)
    (*     2:{ intros x Hfr Hfil. eapply clockof_defined in Hfr; eauto. simpl in Hfr. *)
    (*         apply filter_anons_ino in Hfil. eapply InMembers_idck in Hfr; eauto. } *)
    (*     apply sc_switch_adds'; simpl; eauto. *)
    (*     intros x Hfree Hncs. eapply clockof_defined in Hfree; eauto. simpl in Hfree. *)
    (*     eapply Ino_Forall in Hncs; eauto. simpl in Hncs. *)
    (*     apply Exists_exists in Hncs as (?&?& Hfr). *)
    (*     solve_NoDupMembers Hndup. *)
    (*   - eapply Forall2_impl_In; eauto; intros. *)
    (*     erewrite filter_anons_app, filter_nclock_eq, *)
    (*     adds_opt'_app, adds_opt'_None; eauto. solve_length. *)
    (* } *)

    1-8:(inv Hwc; rewrite map_app; apply Forall2_app;
         [ (take (_ _ (L.clockof _) (map abstract_clock _)) and eapply Forall2_impl_In in it); eauto;
           intros ck ? Hinck ??; auto;
           erewrite filter_anons_app, filter_nclock_eq, adds_opt'_app, adds_opt'_None; eauto; [| solve_length];
           apply sc_switch_adds'; simpl; eauto;
           [ apply sc_switch_adds'; simpl; eauto;
             intros x Hfree Hncs; eapply clockof_defined in Hfree; eauto; simpl in Hfree;
             eapply Ino_Forall in Hncs; eauto; simpl in Hncs;
             apply Exists_exists in Hncs as (?&?& Hfr); solve_NoDupMembers Hndup
           | intros x Hfr Hfil; eapply clockof_defined in Hfr; eauto; simpl in Hfr;
             apply filter_anons_ino in Hfil; apply InMembers_idck in Hfr; eauto ]
         | eapply Forall2_impl_In; eauto; intros;
           erewrite filter_anons_app, filter_nclock_eq, adds_opt'_app, adds_opt'_None; eauto; solve_length ]).

    (* Eapp *)
    Local Ltac solve_NoDupMembers2 H :=
      eapply NoDupMembers_app_r, NoDupMembers_app_InMembers in H; eauto;
      eapply H, InMembers_fresh_in; eauto.

    take (exists _,_) and destruct it as (ncs'& nss'& Hlen' & Hncs' & Hsc).
    exists (ncs ++ ncs'),(nss ++ nss'). split. rewrite 2 app_length. omega. split.
    apply Forall_app. split.
    apply Forall_impl with (2 := Hfresh); auto; intros;
      eapply LiftO_impl; eauto; intros; now right.
    apply Forall_impl with (2 := Hncs'); auto; intros;
      eapply LiftO_impl; eauto; intros; now left.
    rewrite map_app. apply Forall2_app.

    3:{ rewrite Permutation_swap in Hndup. apply NoDupMembers_app_r in Hndup; auto. }

    - take (_ _ (L.clockof _) (map abstract_clock _)) and
           eapply Forall2_impl_In in it; eauto.
      intros c ? Hin ? Hsc. simpl in *.
      rewrite adds_opt'_app; auto.
      unfold filter_anons. rewrite map_app, adds_opt'_app.
      2:{ apply Forall2_length in it. now rewrite 2 map_length in *. }
      apply sc_permute_adds.
      2:{
        intros x Hinnc Hinl0.
        apply filter_anons_spec in Hinnc as (Hino &?).
        apply filter_anons_spec in Hinl0 as (Hino' &?).
        rewrite Ino_In in Hino.
        eapply In_snd_nclocksof in Hino as (?&?& Hsnd).
        inv Hwc. rewrite <- Ino_In in Hsnd.
        eapply snd_nclocks_defined with (vars := idck env) in Hsnd as []; eauto.
        2:{ eapply Forall_forall; eauto. }
        eapply snd_nclocks_fresh in H12; eauto; simpl in H12.
        solve_NoDupMembers2 Hndup.
      }
      eapply sc_switch_adds'.
      2:{
        intros x Hinnc Hinl0.
        apply filter_anons_spec in Hinl0 as (Hino &?).
        take (LC.wc_exp _ _ _) and eapply free_clock_defined in it as []; eauto.
        2:{ simpl. unfold L.clock_of_nclock, stripname. apply Exists_exists.
            esplit. split; eauto. }
        eapply Ino_In, In_snd_nclocksof in Hino as (?&?& Hsnd).
        inv Hwc. rewrite <- Ino_In in Hsnd.
        eapply snd_nclocks_defined with (vars := idck env) in Hsnd as []; eauto.
        2:{ eapply Forall_forall; eauto. }
        solve_NoDupMembers2 Hndup.
      }
      apply sc_permute_adds.
      2:{
        intros x Hinc Hinl0.
        eapply Ino_In, Forall_forall in Hinc; eauto. simpl in Hinc.
        apply filter_anons_spec in Hinl0 as (Hino &?).
        eapply snd_nclocks_fresh in H8; eauto; simpl in H8.
        rewrite Exists_exists in Hinc; destruct Hinc as [? [? ?]].
        solve_NoDupMembers2 Hndup.
      }
      apply sc_switch_adds'.
      2:{
        intros x Hfr Hinc.
        eapply Ino_In, Forall_forall in Hinc; eauto; simpl in Hinc.
        take (LC.wc_exp _ _ _) and eapply free_clock_defined in it as []; eauto.
        3:{ simpl. unfold L.clock_of_nclock, stripname. apply Exists_exists.
            esplit. split; eauto. }
        1,2:eapply Exists_exists in Hinc as (e&?&Hfr'); inv Hwc.
        2: solve_NoDupMembers2 Hndup.
        eapply InMembers_idck in H1. solve_NoDupMembers Hndup.
      }
      assumption.
    - eapply Forall2_impl_In in Hscl; eauto; intros c ? Hin ? Hsc'. simpl in *.
      unfold filter_anons. rewrite map_app.
      rewrite 2 adds_opt'_app; auto.
      2:{ apply Forall2_length in Hsc. now rewrite 2 map_length in *. }
      apply sc_switch_adds'.
      2:{
        intros x Hinnc Hinl0.
        apply filter_anons_spec in Hinl0 as (Hino &?).
        take (LC.wc_exp _ _ _) and eapply snd_nclocks_fresh in it; simpl in it; eauto.
        apply L.In_clocksof in Hin as (e&?&?). inv Hwc.
        eapply free_clock_defined with (e := e) (x := x) in Henv as []; eauto.
        + solve_NoDupMembers2 Hndup.
        + inv H11; eapply Forall_forall in H2; eauto.
        + apply Exists_exists; eauto.
      }
      apply sc_permute_adds_nest.
      2:{
        intros x Hinnc Hinl0. apply Ino_In in Hinnc.
        apply filter_anons_spec in Hinl0 as (Hino & Hmem).
        eapply Forall_forall in Hinnc; eauto.
        rewrite Ino_In in Hino.
        apply In_snd_nclocksof in Hino as (e&?&?). inv Hwc.
        eapply snd_nclocks_fresh with (e := e) in Hmem; eauto.
        + solve_NoDupMembers2 Hndup.
        + inv H11; eapply Forall_forall in H1; eauto.
        + now apply Ino_In.
      }
      2:{
        intros x Hinnc' Hinnc. rewrite Ino_In in Hinnc, Hinnc'.
        eapply Forall_forall in Hinnc; eauto.
        eapply Forall_forall in Hinnc'; eauto. simpl in *.
        apply Exists_exists in Hinnc as [? [? ?]].
        solve_NoDupMembers2 Hndup.
      }
      2:{ apply Forall2_length in Hscl.
          now rewrite L.clocksof_nclocksof, 2 map_length in *. }
      apply sc_switch_adds'; auto.
      1:{
        intros x Hfree Hinnc. rewrite Ino_In in Hinnc.
        eapply Forall_forall in Hinnc; eauto. simpl in *.
        apply L.In_clocksof in Hin as (e&?&?). inv Hwc.
        eapply free_clock_defined with (e := e) (x := x) in Henv as []; eauto.
        + eapply NoDupMembers_app_InMembers in Hndup; eauto.
          eapply Hndup, InMembers_app; eauto. eapply InMembers_idck in H9; eauto.
        + solve_NoDupMembers2 Hndup.
        + eapply Forall_forall; eauto.
        + apply Exists_exists; eauto.
      }
  Qed.

  Lemma inst_in_eqst:
    forall G env H Hi b n es ss0 i ck bck sub,
      In (i, ck) (idck (L.n_in n)) ->
      LC.wc_global G ->
      wc_env (idck env) ->
      wc_env (idck (L.n_in n)) ->
      Forall (LT.wt_exp G (idty env)) es ->
      Forall (LC.wc_exp G (idck env)) es ->
      NoDupMembers (env++L.fresh_ins es) ->
      Forall2 (LC.WellInstantiated bck sub) (idck (L.n_in n)) (L.nclocksof es) ->
      Forall2 (LS.sem_exp G H b) es ss0 ->
      Forall2 (LS.sem_var Hi) (LS.idents (L.n_in n)) (concat ss0) ->
      forall i' ncs nss,
        sub i = Some i' ->
        Forall (LiftO True (fun x : ident => Exists (fun e => InMembers x (L.fresh_in e)) es)) ncs ->
        orel (@EqSt value) (Env.find i Hi)
             (Env.find i' (adds_opt' (filter_anons (idck env) (L.nclocksof es))
                                     (concat ss0) (adds_opt' ncs nss H))).
  Proof.
    intros * Hin Hwcg Henv WCin Hwt Hwc Hndup WIi Hse Hsv i' ncs nss Sub Hncs.
    (* i is a node variable, i' its image *)
    destruct (ino_dec i' ((filter_anons (idck env) (L.nclocksof es)))
                      (ident_eq_dec)) as [Hino|Hnino].
    + (* i' is an anonymous variable manually added to H *)
      rewrite idck_idents, Forall2_map_1 in Hsv.
      pose proof (Forall2_in_left_combine  _ _ _ _ Hsv Hin) as (?&Hcomb&Hvar).
      inv Hvar. take (Env.MapsTo _ _ _) and apply Env.find_1 in it as Heq.
      simpl in *. erewrite In_find_adds_opt'. rewrite Heq; eauto.
      now take (_ ≡ _) and rewrite <- it.
      { (* nodupo *)
        clear - Hwcg Henv Hwc Hwt Hndup. induction es; simpl. constructor.
        unfold filter_anons. rewrite map_app.
        inv Hwt. inv Hwc.
        inv_NoDup_fresh_ins Hndup. rewrite Permutation_swap in Hndup.
        assert (Hndup':=Hndup). apply NoDupMembers_app' in Hndup' as [Hndup1 ?].
        apply NoDupo_app'; auto. eapply nodupo_filter_anons; eauto.
        intros ? Hino Hino'. assert (Henv' := Henv).
        apply filter_anons_spec in Hino as (Hnd&?).
        eapply var_clock_defined in Henv as []; eauto.
        apply filter_anons_spec in Hino' as (Hnd'&?).
        apply Ino_In, In_snd_nclocksof in Hnd' as (e&?&Hnd').
        apply Ino_In in Hnd'.
        eapply var_clock_defined with (e := e) in Henv' as []; eauto.
        2: eapply Forall_forall; eauto.
        eapply NoDupMembers_app_InMembers in Hndup; eauto.
        eapply Hndup, InMembers_app, or_intror, InMembers_fresh_in; eauto.
      }
      apply Forall2_swap_args in WIi.
      pose proof (Forall2_trans_ex _ _ _ _ _ WIi Hsv) as Hesss0.
      apply Forall2_swap_args in WIi.
      pose proof (Forall2_chain_In' _ _ _ _ _ _ _ WIi Hesss0 Hcomb)
        as ((?&?)&(Sub'&?)&?&?& Hok).
      simpl in *. rewrite Sub in Sub'.
      eapply in_combine_nodup in Hcomb; eauto. subst.
      2:{ apply NoDupMembers_NoDup. apply NoDupMembers_idck.
          exact (NoDupMembers_app_l _ _ (L.n_nodup n)). }
      unfold filter_anons. rewrite combine_map_fst, in_map_iff.
      esplit. split; eauto. simpl.
      eapply filter_anons_spec in Hino as (?&Hinm).
      destruct (mem_assoc_ident i' _) eqn:Hb; auto.
      apply mem_assoc_ident_true in Hb as (?&IM).
      apply In_InMembers in IM; congruence.
    + (* i' was not added, it necessarily comes from the environment *)
      rewrite find_In_gsso_opt'; auto.
      apply filter_anons_filter' in Hnino; auto.
      2:{ eapply Forall2_in_left in WIi as (?&?&Heq&?); eauto. simpl in *.
          rewrite Ino_In, in_map_iff. rewrite Heq in Sub. eauto. }
      rewrite find_In_gsso_opt'.
      2:{ intro Hino. rewrite Ino_In in Hino. eapply Forall_forall in Hncs; eauto.
          simpl in Hncs. eapply Exists_exists in Hncs as (?&?&Hfr).
          eapply NoDupMembers_app_InMembers in Hndup; eauto.
          eapply Hndup, InMembers_fresh_in; eauto. eapply InMembers_idck in Hnino; eauto. }
      clear - Hwc Hse Hsv Hin Sub WIi Hnino Hndup.
      rewrite idck_idents in *.
      remember (idck (L.n_in n)) as ids. clear Heqids.
      revert dependent ids. revert dependent ss0.
      induction es as [|e]; intros. inv WIi. inv Hin.
      simpl in *. apply Forall2_app_inv_r in WIi as (l&?&Hf&Hc&?).
      subst. inv_NoDup_fresh_ins Hndup. inv Hse.
      inversion_clear Hwc as [| ?? Hwce].
      simpl in Hsv. rewrite map_app in Hsv.
      eapply Forall2_app_split in Hsv as (?&?); eauto.
      2:{ eapply length_clockof in Hwce; eauto. apply Forall2_length in Hf.
          rewrite L.clockof_nclockof, map_length in *. etransitivity; eauto. }
      apply in_app_or in Hin as [Hin|Hin]; eauto.
      clear Hc IHes. eapply Forall2_in_left in Hf as ((?&?)& Hck & Sub'&?); eauto.
      simpl in *. rewrite Sub in Sub'.
      { destruct e; inv Hwce; simpl in Hck.
        - inv Hck; try tauto. congruence.
        - (* variable *)
          destruct Hck as [Hck|]; try tauto. inv Hck.
          take (LS.sem_exp _ _ _ _ _) and inv it.
          take (Forall2 _ _ [_]) and inv it.
          take (Forall2 _ _ []) and inv it.
          destruct l. inv Hin. simpl in *.
          destruct l; take ([_] = _) and inv it. inv Hin; intuition.
          simpl in *. do 2 take (LS.sem_var _ _ _) and inv it.
          do 2 (erewrite Env.find_1; eauto). constructor.
          etransitivity; eauto. now symmetry.
        - inv Hck; try tauto. congruence.
        - inv Hck; try tauto. congruence.
        - inv Hck; try tauto. congruence.
        - eapply in_map_iff in Hck as ((?&?&?)&?&HH). simpl in *.
          eapply Forall_forall in HH; eauto. inv H6. inv HH.
        - clear - Hck. induction tys; simpl; inv Hck; auto. congruence.
        - clear - Hck. induction tys; simpl; inv Hck; auto. congruence.
        - clear - Hck. induction tys; simpl; inv Hck; auto. congruence.
        - eapply in_map with (f := snd) in Hck.
          simpl in *. rewrite map_map in Hck.
          exfalso. apply InMembers_idck in Hnino. eapply NoDupMembers_app_InMembers in Hndup; eauto.
          eapply Hndup, InMembers_app, or_introl, InMembers_app, or_intror, Ino_In_anon_streams.
          rewrite Ino_In; auto.
        - eapply in_map with (f := snd) in Hck.
          simpl in *. rewrite map_map in Hck.
          exfalso. apply InMembers_idck in Hnino. eapply NoDupMembers_app_InMembers in Hndup; eauto.
          eapply Hndup, InMembers_app, or_introl.
          repeat eapply InMembers_app, or_intror. eapply Ino_In_anon_streams.
          rewrite Ino_In; auto.
      }
      eapply IHes; eauto.
      rewrite Permutation_swap in Hndup.
      apply NoDupMembers_app_r in Hndup; auto.
  Qed.

  (* When function call parameters are well instantiated and have
     the [sem_clock] property, we obtain the same property inside
     the node (Hi = "H inside").
   *)
  Lemma sc_inside :
    forall G H Hi b env es ss0 bck sub n,
      Forall (LT.wt_exp G (idty env)) es ->
      Forall (LC.wc_exp G (idck env)) es ->
      Forall2 (LS.sem_exp G H b) es ss0 ->
      LC.wc_global G ->
      wc_env (idck env) ->
      wc_env (idck (L.n_in n)) ->
      NoDupMembers (env ++ L.fresh_ins es) ->
      Forall2
        (fun e ss =>
           match e with
           | L.Eapp f _ _ anns =>
             exists ncs nss,
             length ncs = length nss /\
             Forall (LiftO True (fun x => InMembers x (L.fresh_in e))) ncs /\
             let H := adds_opt' ncs nss H in
             let H := adds_opt' (filter_anons (idck env)(map snd anns)) ss H in
             Forall2 (NLSC.sem_clock H b) (L.clockof e) (map abstract_clock ss)
           | _ =>
             Forall2 (NLSC.sem_clock H b) (L.clockof e) (map abstract_clock ss)
           end) es ss0 ->
      Forall2 (LC.WellInstantiated bck sub) (idck (L.n_in n)) (L.nclocksof es) ->
      Forall2 (LS.sem_var Hi) (LS.idents (L.n_in n)) (concat ss0) ->
      Forall2 (fun xc => NLSC.sem_clock Hi (clocks_of (concat ss0)) (snd xc))
              (idck (L.n_in n)) (map abstract_clock (concat ss0)).
  Proof.
    intros * Hwt Hwc Hse Hwcg Henv WCin Hndup Hes WIi Hsv. assert (Hse' := Hse).
    eapply sc_union_envs in Hse' as (ncs & nss & Hlen & Hncs & Hscin); eauto.

    rewrite L.clocksof_nclocksof, Forall2_map_1 in Hscin.
    apply Forall2_trans_ex with (1 := WIi) in Hscin as H1.
    eapply Forall2_impl_In; eauto.
    intros (x & ck) xs  Hxin ? ((yck & ny) & Hyin & (Hsub & Hinst) & Hsc).
    simpl in *. unfold LC.WellInstantiated in WIi.
    eapply sc_inst'; eauto.
    - pose proof (LC.wc_env_has_Cbase _ WCin) as [i Hin];
        [ unfold idck; rewrite map_length; exact (L.n_ingt0 n) |].
      apply LC.WellInstantiated_parent in WIi as Hp.
      change (Forall (fun ck => (fun x => x = bck \/ clock_parent bck x) (fst ck))
                     (L.nclocksof es)) in Hp.
      rewrite <- Forall_map in Hp.
      eapply sc_parent; eauto.
      now rewrite Forall2_map_1.
      pose proof (Forall2_in_left _ _ _ _ WIi Hin) as [?(?&?& H14)].
      simpl in H14. inv H14. now apply in_map.
    - intros i i' Free Sub.
      pose proof (wc_env_free_in_clock _ _ _ _ WCin Hxin Free) as [].
      eapply inst_in_eqst; eauto.
  Qed.


  (* In the Eapp case, we must extend the [sem_clock] environment
     with a map for anonymous variables introduced by the application.
     The resulting environment contains the fresh (anonymous) outputs of
     the current call plus the fresh variables from sub-expressions (ncs).
   *)
  Lemma sc_exp :
    forall G H b env e ss,
      LS.sem_exp G H b e ss ->
      LT.wt_exp G (idty env) e ->
      LC.wc_exp G (idck env) e ->
      wc_env (idck env) ->
      NoDupMembers (env ++ L.fresh_in e) ->
      LC.wc_global G ->
      sc_nodes G ->
      var_inv (fun x => LCA.Is_free_left x e) (idck env) H b ->
      match e with
      | L.Eapp f es _ anns =>
        exists ncs nss,
        length ncs = length nss /\
        Forall (LiftO True (fun x => InMembers x (L.fresh_in e))) ncs /\
        let H := adds_opt' ncs nss H in
        (* no need for disjointedness with ncs here *)
        let H := adds_opt' (filter_anons (idck env) (map snd anns)) ss H in
        Forall2 (NLSC.sem_clock H b) (L.clockof e) (map abstract_clock ss)
      | _ =>
        Forall2 (NLSC.sem_clock H b) (L.clockof e) (map abstract_clock ss)
      end.
  Proof.
    induction e using L.exp_ind2;
      intros * Hsem Hwt Hwc Henv Hndup Hwcg Hnode Hvar;
      specialize (clockof_defined G env _ Hwt Hwc) as Hmem; simpl in *.
     - inv Hsem. constructor; eauto. constructor. symmetry in H4.
       destruct cs. eapply ac_const; eauto.
     - inv Hsem.
       inv Hwc; constructor; auto; unfold L.clock_of_nclock, stripname;
         simpl; eapply Hvar; eauto; constructor.
     - inv Hsem. constructor; eauto. inv Hwt. inv Hwc.
       unfold L.clock_of_nclock, stripname. simpl.
       take (L.clockof e = _) and rewrite it in IHe.
       take (LS.sem_exp _ _ _ e _) and apply IHe in it as He; auto. simpl in He.
       2:{ eapply var_inv_weaken; eauto. simpl. intros. now constructor. }
       destruct e; inv He;
         take (lift1 _ _ _ _) and apply ac_lift1 in it; rewrite <- it; auto.
       take (exists _, _) and destruct it as (?&?&?&HH).
       inversion_clear HH as [|???? Hsc].
       eapply sc_switch_adds in Hsc; eauto.
       2:{ intros ? Hfree Hino. apply filter_anons_spec in Hino as []. rewrite InMembers_idck in H10.
           eapply Hmem in Hfree; tauto. }
       eapply sc_switch_adds in Hsc; eauto.
       intros ? Hfree Hino. eapply Ino_Forall in Hino; eauto. simpl in Hino.
       eapply LT.wt_nclock_Is_free_in in Hfree; eauto.
       eapply NoDupMembers_app_InMembers in Hndup; eauto.
       apply InMembers_idty; auto.
     - inv Hsem. constructor; eauto. inv Hwt. inv Hwc.
       unfold L.clock_of_nclock, stripname. simpl.
       take (L.clockof e1 = _) and rewrite it in IHe1. simpl in IHe1.
       take (LS.sem_exp _ _ _ e1 _) and apply IHe1 in it as He; auto.
       simpl in He.
       2:{ rewrite app_assoc in Hndup. apply NoDupMembers_app_l in Hndup; auto. }
       2:{ eapply var_inv_weaken; eauto. simpl. intros. constructor. auto. }
       destruct e1; inv He; take (lift2 _ _ _ _ _ _) and apply ac_lift2 in it;
         rewrite <- it; auto.
       take (exists _, _) and destruct it as (?&?&?&HH).
       inversion_clear HH as [|???? Hsc].
       eapply sc_switch_adds in Hsc; eauto.
       2:{ intros ? Hfree Hino. apply filter_anons_spec in Hino as [].
           rewrite InMembers_idck in H5. eapply Hmem in Hfree; tauto. }
       eapply sc_switch_adds in Hsc; eauto.
       intros ? Hfree Hino. eapply Ino_Forall in Hino; eauto. simpl in Hino.
       eapply LT.wt_nclock_Is_free_in in Hfree; eauto.
       { rewrite app_assoc in Hndup. eapply NoDupMembers_app_l, NoDupMembers_app_InMembers in Hndup; eauto.
         apply InMembers_idty; auto. }
     - (* Efby *)
       inv Hwc. inv Hsem.
       assert (EqSts (map abstract_clock ss)
                     (map abstract_clock (concat s0ss))) as Hmap.
       clear - H16.
       revert dependent s0ss. revert sss.
       induction ss; intros. inv H16. simpl. constructor.
       inv H16. rewrite 2 map_cons.
       constructor. symmetry. eapply ac_fby1; eauto.
       assert (l0 = concat [l0]) as Hl0 by (simpl; rewrite app_nil_r; auto).
       assert (l1 = concat [l1]) as Hl1 by (simpl; rewrite app_nil_r; auto).
       rewrite Hl0. rewrite Hl1 in H4.
       eapply IHss; eauto. simpl. rewrite app_nil_r. eauto.
       setoid_rewrite Hmap.

       pose proof (Forall2_in_right' _ _ _ H7) as Heq.
       rewrite Forall2_eq in H7. rewrite H7.
       take (Forall2 (LS.sem_exp _ _ _) e0s _) and rename it into Hsem.
       take (Forall (LC.wc_exp _ _) e0s) and rename it into Hwc.
       inv Hwt. rename H5 into Hwt.
       clear - Hndup H0 Hsem Henv Hwcg Hnode Hvar Hwt Hwc Heq Hmem.
       revert dependent s0ss.
       induction e0s as [|e]; intros. inv Hsem. now simpl.
       inv Hsem. inv Hwc; inv Hwt.
       simpl. rewrite map_app. apply Forall2_app.
       + simpl in Hndup; repeat rewrite <- app_assoc, idck_app in Hndup;
           rewrite app_assoc in Hndup; apply NoDupMembers_app_l in Hndup; auto.
         inversion_clear H0 as [|?? He Hg]. clear Hg IHe0s.
         take (LS.sem_exp _ _ _ e _) and apply He in it as ?; auto.
         2:{ rewrite app_assoc in Hndup. apply NoDupMembers_app_l in Hndup; auto. }
         2:{ eapply var_inv_weaken; eauto. simpl. intros. constructor. auto. }
         destruct e; auto. simpl in *.
         take (exists _, _) and destruct it as (?&?&?&?&HF2).
         eapply Forall2_impl_In in HF2; eauto. intros * Hin ? Hsc.
         eapply in_app_weak in Hin. apply Heq in Hin as (?&Hin&?). subst.
         unfold L.clock_of_nclock, stripname in Hin.
         apply in_map_iff in Hin as ((?&?&?)&?&?). simpl in *. subst.
         eapply sc_switch_adds in Hsc; eauto.
         2:{ intros ? Hfree Hino. apply filter_anons_spec in Hino as []. rewrite InMembers_idck in H10.
             eapply Hmem in Hfree; eauto. apply in_map_iff.
             esplit; split; eauto; simpl; eauto. }
         eapply sc_switch_adds in Hsc; eauto.
         intros ? Hfree Hino. eapply Ino_Forall in Hino; eauto. simpl in Hino.
         apply Hmem in Hfree. 2:apply in_map_iff; esplit; split; eauto; simpl; eauto.
         eapply NoDupMembers_app_InMembers in Hndup; eauto.
         apply Hndup, InMembers_app; eauto.
       + inv H0.
         eapply IHe0s; eauto; try constructor; eauto.
         { simpl in Hndup; repeat rewrite <- app_assoc in Hndup.
           rewrite Permutation_swap in Hndup; apply NoDupMembers_app_r in Hndup; auto. }
         { eapply var_inv_weaken; eauto. simpl. intros * Hf. constructor.
           inv Hf. now right. }
         { intros. apply Heq. simpl. apply in_or_app. now right. }
     - (* Ewhen *)
       clear Hwt. inv Hwc. unfold L.clock_of_nclock, stripname. simpl. clear Hmem.
       revert dependent tys. revert dependent ss.
       induction es; intros; inv Hsem; inv H13.
       inv H15. apply length_zero_iff_nil in H8. subst. simpl. constructor.
       rename a into e0. simpl in H15. inv H0.
       apply Forall2_app_inv_l in H15. destruct H15 as (?&?&?&?&?). subst.
       unfold L.clocksof, flat_map in H8. simpl in H8.
       apply length_app in H8. destruct H8 as (?&?&?&?&?). subst.
       rewrite map_app. rewrite map_app. apply Forall2_app.
       + clear H10 IHes. apply Forall2_forall; split; intros.
         2:{ rewrite map_length. rewrite map_length.
             apply Forall2_length in H0. rewrite <- H0. rewrite H8.
             inv H5. eapply length_clockof; eauto. }
         assert (Hin := H2).
         apply in_combine_l in H2. apply in_combine_r in Hin.
         clear - H0 Hin H2 Hvar H6 H14. induction x2. inv H2.
         inv H2; [| apply IHx2; auto].
         2:{ eapply var_inv_weaken; eauto. simpl. intros.
             inv H2. now constructor. }
         rewrite in_map_iff in Hin. destruct Hin as (?&?&?). subst.
         eapply Forall2_in_right in H2; eauto. destruct H2 as (?&?&?).
         eapply sc_when; eauto. apply ac_when in H2. rewrite H2.
         eapply Hvar; eauto. constructor. now left.
       + unfold L.clocksof, flat_map in H7. simpl in H7.
         apply Forall_app in H7. destruct H7.
         inv H5.
         eapply IHes in H10; eauto; try econstructor; eauto.
         { simpl in Hndup. rewrite Permutation_swap in Hndup.
           apply NoDupMembers_app_r in Hndup; auto. }
         eapply var_inv_weaken; eauto. simpl. intros * Hf.
         inv Hf. constructor. intuition.
     - (* EMerge *)
       assert (Hlen := Hwc). eapply length_clockof in Hlen; eauto.
       inv Hwt. inv Hwc. inv Hsem. unfold L.clock_of_nclock, stripname. simpl.
       simpl in Hlen. rewrite map_length in Hlen.
       apply Forall2_const_map; [| now rewrite map_length].
       apply Forall_forall; intros * Hin.
       rewrite in_map_iff in Hin. destruct Hin as (s0 & Hac & Hin).
       apply Forall3_in_right with (z := s0) in H25; auto.
       destruct H25 as (st & sf & Hints & Hinfs & Hmerge).
       rewrite <- Hac.
       apply in_concat in Hints. destruct Hints as (lts & Hints & Hinlst).
       eapply Forall2_in_right in H23; eauto. destruct H23 as (e1 & Hine1 & Hseme1).
       eapply Forall_forall in H6; eauto. eapply Forall_forall in H12; eauto.
       eapply Forall_forall in H0; eauto.
       apply H0 in Hseme1; eauto.
       2:{ rewrite app_assoc in Hndup; apply NoDupMembers_app_l in Hndup.
           eapply NoDupMembers_fresh_in'; eauto. }
       2:{ eapply var_inv_weaken; eauto. simpl. intros. constructor.
           right. left. apply Exists_exists. now exists e1. }

       apply in_concat in Hinfs. destruct Hinfs as (lfs & Hinfs & Hinlsf).
       eapply Forall2_in_right in H24; eauto. destruct H24 as (e2 & Hine2 & Hseme2).
       eapply Forall_forall in H7; eauto. eapply Forall_forall in H13; eauto.
       eapply Forall_forall in H1; eauto.
       apply H1 in Hseme2; auto.
       2:{ rewrite Permutation_swap in Hndup; apply NoDupMembers_app_r in Hndup.
           eapply NoDupMembers_fresh_in'; eauto. }
       2:{ eapply var_inv_weaken; eauto. simpl. intros. constructor.
           right. right. apply Exists_exists. now exists e2. }
       eapply sc_merge; eauto.
       + apply in_map with (f := abstract_clock) in Hints.
         destruct e1; try (destruct Hseme1 as (?&?&?&?&Hseme1));
           eapply Forall2_in_right in Hseme1; eauto;
           destruct Hseme1 as (ck1 & Hinck1 & Hsc1);
           assert (In ck1 (L.clocksof ets)) by (apply in_flat_map; eauto);
           eapply Forall_forall in H15; eauto; subst; auto.
         (* Eapp case *)
         eapply sc_switch_adds in Hsc1; eauto.
         2:{ intros ? Hfree Hino. apply filter_anons_spec in Hino as []. rewrite InMembers_idck in H9.
             inv Hfree; eauto. eapply In_InMembers, InMembers_idck in H14; eauto.
             eapply LT.wt_nclock_Is_free_in in H11; eauto. rewrite InMembers_idty in H11; eauto. }
         eapply sc_switch_adds in Hsc1; eauto.
         intros ? Hfree Hino. eapply Ino_Forall in Hino; eauto. simpl in Hino.
         rewrite app_assoc in Hndup; eapply NoDupMembers_app_l, NoDupMembers_app_InMembers in Hndup; eauto.
         eapply Hndup, InMembers_fresh_in; eauto.
         eapply LT.wt_clock_Is_free_in with (env:= idty env), InMembers_idty in Hfree; eauto.
         inv H11; constructor; auto.
       + apply in_map with (f := abstract_clock) in Hinfs.
         destruct e2; try (destruct Hseme2 as (?&?&?&?&Hseme2));
           eapply Forall2_in_right in Hseme2; eauto;
         destruct Hseme2 as (ck2 & Hinck2 & Hsc2);
         assert (In ck2 (L.clocksof efs)) by (apply in_flat_map; eauto);
         eapply Forall_forall in H16; eauto; subst; auto.
         (* Eapp case *)
         eapply sc_switch_adds in Hsc2; eauto.
         2:{ intros ? Hfree Hino. apply filter_anons_spec in Hino as []. rewrite InMembers_idck in H9.
             inv Hfree; eauto. eapply In_InMembers, InMembers_idck in H14; eauto.
             eapply LT.wt_nclock_Is_free_in in H11; eauto. rewrite InMembers_idty in H11; eauto. }
         eapply sc_switch_adds in Hsc2; eauto.
         intros ? Hfree Hino. eapply Ino_Forall in Hino; eauto. simpl in Hino.
         rewrite Permutation_swap in Hndup; eapply NoDupMembers_app_r, NoDupMembers_app_InMembers in Hndup; eauto.
         eapply Hndup, InMembers_fresh_in; eauto.
         eapply LT.wt_clock_Is_free_in with (env:= idty env), InMembers_idty in Hfree; eauto.
         inv H11; constructor; auto.
     - (* Eite *)
       inv Hwc. inv Hsem. simpl. take (Forall3 _ _ _ _) and rename it into Hite.
       assert (EqSts (map abstract_clock ss)
                     (map abstract_clock (concat ts))) as Hmap.
       1:{
         clear - Hite.
         revert dependent ts. revert fs.
         induction ss; intros. inv Hite. simpl. constructor.
         inv Hite. rewrite 2 map_cons.
         constructor. symmetry. eapply ac_ite; eauto.
         assert (l0 = concat [l0]) as Hl0 by (simpl; rewrite app_nil_r; auto).
         assert (l1 = concat [l1]) as Hl1 by (simpl; rewrite app_nil_r; auto).
         rewrite Hl0. rewrite Hl1 in *.
         eapply IHss; eauto. simpl. rewrite app_nil_r. eauto. }
       setoid_rewrite Hmap. unfold L.clock_of_nclock, stripname. simpl.
       assert (Forall (LT.wt_exp G (idty env)) ets) as Hwt1 by (inv Hwt; eauto).
       clear Hmap Hwt Hite H13 H14. revert dependent ts. revert dependent tys.
       induction ets; intros.
       take (Forall2 _ [] _) and inv it. take (length _ = _) and inv it.
       take (length tys = 0) and apply length_zero_iff_nil in it. subst. simpl. auto.
       take (Forall2 _ (_::_) _) and inv it. simpl in *.
       take (Forall _ (_++_)) and apply  Forall_app in it as (?&?).
       take (length _ = _) and apply length_app in it as (?&?&?&?&?). subst.
       rewrite map_app. rewrite map_app.
       apply Forall2_app;
         take (Forall (LC.wc_exp _ _) (_::_)) and inversion_clear it as [|?? Hwc];
         inversion_clear H0 as [|?? Ha].
       + assert (map (fun _ : type => ck) x = L.clockof a) as Hmap.
         { clear - H2 H10. revert dependent x.
           induction (L.clockof a); intros lty Hlen.
           inversion Hlen as [Hnil]. apply length_zero_iff_nil in Hnil. now subst.
           destruct lty; inv Hlen. simpl. inv H2. f_equal. now apply IHl. }
         rewrite Hmap.
         assert (NoDupMembers (env ++ L.fresh_in a)) as Hndup'.
         { clear - Hndup. rewrite Permutation_swap in Hndup. apply NoDupMembers_app_r in Hndup.
           repeat rewrite app_assoc in Hndup. repeat (apply NoDupMembers_app_l in Hndup; auto). }
         inv Hwt1.
         destruct a; eapply Ha in Hwc as Hsc; eauto;
           try (eapply var_inv_weaken; eauto; simpl; constructor; intuition).
         (* Eapp case *)
         destruct Hsc as (?&?&?&?&HF2).
         eapply Forall2_impl_In in HF2; eauto. intros * Hin ? Hsc.
         eapply sc_switch_adds in Hsc; eauto.
         2:{ intros ? Hfree Hino.
             apply filter_anons_spec in Hino as []. rewrite InMembers_idck in H20.
             eapply Hmem in Hfree; eauto.
             rewrite <- Hmap, in_map_iff in Hin. destruct Hin as (?&?&?). subst.
             apply in_map_iff. esplit; split; eauto. eauto using in_or_app.
         }
         eapply sc_switch_adds in Hsc; eauto.
         intros ? Hfree Hino. eapply Ino_Forall in Hino; eauto. simpl in Hino.
         eapply NoDupMembers_app_InMembers in Hndup'; eauto.
         eapply Hmem in Hfree; eauto.
         rewrite <- Hmap, in_map_iff in Hin. destruct Hin as (?&?&?). subst.
         apply in_map_iff. esplit; split; eauto. eauto using in_or_app.
       + inv Hwt1. apply IHets; try constructor; auto.
         { clear - Hndup. repeat rewrite idck_app.
           rewrite <- app_assoc in Hndup. rewrite app_assoc, Permutation_swap, <- app_assoc in Hndup.
           apply NoDupMembers_app_r in Hndup; auto. }
         intros. eapply Hmem; eauto. rewrite map_app, in_app_iff; eauto.
         eapply var_inv_weaken; eauto. simpl. intros * Hf.
         constructor. inv Hf. intuition.
     - destruct ro. all: swap 1 2.
       + (* Eapp *)
         assert (Hndup':=Hndup).
         eapply NoDupMembers_app_r in Hndup'.
         pose proof (nodupo_filter_anons _ _ _ Hwc Hndup') as Hnodupo.
         inversion_clear Hwc as
             [| | | | | | | | |???? bck sub Hwce Hfind WIi WIo|].
         inversion_clear Hsem as [| | | | | | | |??????? Hse Hsemn |].
         inversion Hsemn as [ ???? Hi ?? Hvin Hvout ? Hsck]. subst.
         match goal with
         | H1: L.find_node f G = Some _, H2: L.find_node f G = Some _ |- _
           => rewrite H2 in H1; inv H1
         end.
         rewrite app_assoc in Hndup.
         assert (Hndup'':=Hndup). apply NoDupMembers_app_l in Hndup''; auto.
         unfold sc_nodes in Hnode. eapply Hnode in Hsemn; eauto.
         { (* output *)
           inv Hwt. assert (Hse' := Hse).
           eapply sc_union_envs in Hse' as (ncs & nss & Hlen & Hncs & Hscin); eauto.
           2:{
             eapply Forall2_impl_In; eauto. intros e? Hin ??.
             pose proof Hin as He; eapply Forall_forall with (1:=H1) in He; eauto.
             apply He; auto; try (now eapply Forall_forall; eauto).
             { eapply NoDupMembers_fresh_in'; eauto. }
             eapply var_inv_weaken; eauto. simpl. intros. constructor.
             eapply Exists_exists. eauto.
           }
           exists ((filter_anons (idck env) (L.nclocksof es)) ++ ncs), ((concat ss0) ++ nss).
           split.
           { unfold filter_anons. apply Forall2_length in Hscin.
             now rewrite L.clocksof_nclocksof, 2 app_length, 2 map_length,
             Hlen, <- Hscin in *. }
           split.
           { apply Forall_app. split.
             apply Forall_forall. intros [x|] Hin; simpl; auto. apply Ino_In in Hin.
             apply filter_anons_spec in Hin as [Hin].
             apply Ino_In, In_snd_nclocksof in Hin as (?&?&Hin).
             eapply Ino_In, snd_nclocks_fresh in Hin; eauto.
             - apply InMembers_app, or_introl. eapply InMembers_fresh_in; eauto.
             - rewrite Forall_forall in Hwce; eauto.
             - eapply Forall_impl_In in Hncs; eauto. intros [] ??; auto; simpl in *.
               apply Exists_exists in H5 as [? [Hin Hinm]].
               apply InMembers_app, or_introl. eapply InMembers_fresh_in; eauto.
           }
           unfold LC.WellInstantiated in WIo. unfold L.clock_of_nclock, stripname.
           rewrite Forall2_map_1. rewrite Forall2_map_2 in WIo.
           apply Forall2_swap_args in WIo.
           apply Forall2_trans_ex with (1 := WIo) in Hsemn.
           eapply Forall2_impl_In; eauto.
           intros [aty (ack & anm)] so ??((x&ck)& Hxin & (Hsub & Hinst) & Hsc).
           simpl in *.
           pose proof (LC.wc_find_node G f n Hwcg) as [?(WCin&(WCio&?))]; eauto.
           unfold LC.WellInstantiated in WIi.
           eapply sc_inst; eauto.
           - pose proof (LC.wc_env_has_Cbase _ WCin) as [i Hin];
               [ unfold idck; rewrite map_length; exact (L.n_ingt0 n) |].
             apply LC.WellInstantiated_parent in WIi as Hp.
             change (Forall (fun ck => (fun x => x = bck \/ clock_parent bck x) (fst ck))
                            (L.nclocksof es)) in Hp.
             rewrite <- Forall_map in Hp.
             eapply sc_parent; eauto.
             2:{ pose proof (Forall2_in_left _ _ _ _ WIi Hin) as [?(?&?& H14)].
                 simpl in H14. inv H14. now apply in_map. }
             rewrite L.clocksof_nclocksof in Hscin.
             eapply Forall2_impl_In in Hscin; eauto. simpl. intros ?? Hinnc ??.
             rewrite adds_opt'_app.
             2:{ unfold filter_anons. apply Forall2_length in Hscin.
                 now rewrite 2 map_length in *. }
             eapply sc_switch_adds'; eauto.
             intros ? Hfr Hino. apply filter_anons_spec in Hino as [Hino].
             rewrite map_map in Hino.
             rewrite <- L.clocksof_nclocksof in Hinnc. apply L.In_clocksof in Hinnc as (e&?&?).
             eapply free_clock_defined with (x := x1) (e := e) (vars := idck env)
               in Henv as []; auto; try (now eapply Forall_forall; eauto); auto.
             2:apply Exists_exists; eauto.
             eapply NoDupMembers_app_InMembers in Hndup'. 2:eapply InMembers_fresh_in; eauto.
             apply Hndup', Ino_In_anon_streams; auto.
           - intros i i' Hfree Hisub.
             eapply wc_env_free_in_clock in WCio as [ick Hin]; eauto.
             2:{ unfold idck. rewrite map_app. apply in_or_app. right. eauto. }
             rewrite idck_app in Hin. apply in_app_or in Hin as [Hin | Hin].
             + (* i ∈ idck(n_in n) *)
               rewrite adds_opt'_app.
               2: unfold filter_anons; apply Forall2_length in Hscin;
                 now rewrite L.clocksof_nclocksof, 2 map_length in *.
               rewrite find_In_gsso_opt'.
               2:{
                 intro Hino. apply filter_anons_spec in Hino as [Hino].
                 unfold L.stream_name in Hino; rewrite map_map in Hino.
                 apply Forall2_in_left with (2 := Hin) in WIi as (?& Hnc & Sub &?).
                 simpl in Sub. rewrite Hisub in Sub.
                 apply in_map with (f := snd), In_snd_nclocksof in Hnc as (?&?& Hsnd).
                 rewrite <- Sub, <- Ino_In in Hsnd.
                 eapply snd_nclocks_fresh with (vars := idck env) in Hsnd; eauto.
                 2: eapply Forall_forall; eauto.
                 eapply NoDupMembers_app_InMembers in Hndup'. 2:eapply InMembers_fresh_in; eauto.
                 apply Hndup', Ino_In_anon_streams; auto. }
               eapply inst_in_eqst; eauto.
             + (* i ∈ idck(n_out n) *)
               rewrite idck_idents, Forall2_map_1 in Hvout.
               pose proof (Forall2_in_left_combine  _ _ _ _ Hvout Hin) as (?&Hcomb&Hv).
               inv Hv. take (Env.MapsTo _ _ _) and apply Env.find_1 in it as Heq.
               simpl in *. erewrite In_find_adds_opt'; auto. rewrite Heq; eauto.
               now take (_ ≡ _) and rewrite <- it.
               rewrite Forall2_swap_args in WIo. rewrite Forall2_map_2 in Hsemn.
               pose proof (Forall2_chain_In' _ _ _ _ _ _ _ WIo Hsemn Hcomb)
                 as ((?&?)&(Sub'&?)&?&?& Hok). simpl in *.
               unfold filter_anons. rewrite 2 combine_map_fst, in_map_iff.
               esplit; split.
               2:{ rewrite in_map_iff. esplit; split; eauto. }
               simpl. f_equal. rewrite <- Sub', Hisub. cases_eqn Hm. exfalso.
               apply mem_assoc_ident_true in Hm as (?&Hm); apply In_InMembers in Hm.
               eapply in_combine_l,in_map with (f := snd),in_map with (f := snd) in Hok.
               rewrite map_map in Hok. simpl in *.
               rewrite <- app_assoc, Permutation_swap in Hndup. rewrite InMembers_idck in Hm.
               eapply NoDupMembers_app_r, NoDupMembers_app_InMembers in Hndup; eauto.
               eapply Hndup, Ino_In_anon_streams; auto.
               rewrite <- Sub', Hisub, <- Ino_In in Hok; auto.
         }
         { (* input *)
           take (L.find_node _ _ = _) and eapply LC.wc_find_node in it
             as (?&(?&?)); eauto.
           inv Hwt. eapply sc_inside; eauto.
           eapply Forall2_impl_In; eauto. intros ? Hin ???.
           eapply Forall_forall in H1; eauto.
           apply H1; auto. 3:{ eapply NoDupMembers_fresh_in'; eauto. }
           1,2:eapply Forall_forall; eauto.
           eapply var_inv_weaken; eauto. simpl. intros. constructor.
           eapply Exists_exists. eauto.
         }
       + (* EAppReset *)
  Admitted.

  Lemma extract_sc:
    forall H b env cenv x xs ys ss e ck,
      Forall2 (LS.sem_var H) xs ys ->
      Forall2 (NLSC.sem_clock H b) (L.clockof e) (map abstract_clock ys) ->
      Forall2 (fun x ck => In (x, ck) cenv) xs (L.clockof e) ->
      envs_eq env cenv ->
      In x xs ->
      find_clock env x = OK ck ->
      LS.sem_var H x ss ->
      NLSC.sem_clock H b ck (abstract_clock ss).
  Proof.
    intros * Hl1 Hse HFin1 Henvs Hin Hfind Hsemv.
    revert dependent ys. revert HFin1.
    generalize (L.clockof e).
    induction xs; intros; inv Hin.
    + inv Hl1. simpl in *. inv Hse. inv HFin1.
      assert (Hin := H9).
      eapply envs_eq_find in Henvs; eauto. rewrite Henvs in Hfind. inv Hfind.
      rewrite sem_var_var in Hsemv, H2.
      eapply NLSC.sem_var_det in Hsemv; eauto.
      now rewrite <- Hsemv.
    + inv Hl1. simpl in *. inv Hse. inv HFin1. eapply IHxs; eauto.
  Qed.

  Lemma sc_equation :
    forall G H b x cenv env ck eq ss,
      LT.wt_equation G (idty cenv) eq ->
      LC.wc_equation G (idck cenv) eq ->
      LS.sem_equation G H b eq ->
      LC.wc_global G ->
      wc_env (idck cenv) ->
      envs_eq env (idck cenv) ->
      In x (fst eq) ->
      NoDupMembers (cenv ++ L.anon_in_eq eq) ->
      var_inv (fun x => Exists (fun e => LCA.Is_free_left x e) (snd eq)) (idck cenv) H b ->
      LS.sem_var H x ss ->
      find_clock env x = OK ck ->
      sc_nodes G ->
      NLSC.sem_clock H b ck (abstract_clock ss).
  Proof.
    intros * Hwt Hwc Hsemeq Hwcg Henv Henvs Hin Hndup Hinv Hsemv Hfind Hnode.
    destruct eq as [xs es]. simpl in Hin.
    destruct Hwc as (Hwceq & Hlifto & HFin).
    destruct Hwt as (Hwt & _).

    inv Hsemeq. revert dependent ss0. revert dependent xs.
    induction es as [| e]; intros. inv H5. inv H6. now inv Hin.
    inversion H5 as [| ? ys ba yss Hse Hf2]. subst. simpl in *.
    apply Forall2_app_inv_r in H6. destruct H6 as (l1 & l2 & Hl1 & Hl2 & Hxs).
    subst.
    inversion_clear Hwceq as [| ?? Hwc].
    apply Forall2_app_split in HFin.
    2:{ apply Forall2_length in Hl1. rewrite Hl1.
        symmetry. eapply length_clockof; eauto. }
    apply Forall2_app_split in Hlifto.
    2:{ apply Forall2_length in Hl1. rewrite Hl1.
        symmetry. rewrite L.nclockof_length. eapply length_clockof; eauto. }
    destruct HFin as [HFin1 HFin2]. destruct Hlifto as [Hlifto1 Hlifto2].
    apply in_app_iff in Hin. destruct Hin as [Hin|].
    - unfold L.anon_in_eq, L.anon_ins in Hndup; simpl in Hndup.
      rewrite app_assoc in Hndup; apply NoDupMembers_app_l in Hndup.
      clear dependent l2. clear IHes. rename l1 into xs. inv Hwt.
      destruct e.
      1-8:(eapply sc_exp in Hse; eauto using extract_sc;
           eapply var_inv_weaken; eauto; intros; simpl; left; eauto).
      (* Eapp case, we can't use sc_exp directly because
         we don't have DisjointFresh at top-level *)
      eapply extract_sc; eauto.
      inv Hse.
      + take (LS.sem_node _ _ _ _) and inversion it; subst.
        inversion_clear Hwc as [| | | | | | | | |???? bck sub Wce ? WIi WIo|].
        match goal with
        | H1: L.find_node _ G = Some _, H2: L.find_node _ G = Some _ |- _
          => rewrite H2 in H1; inv H1
        end. simpl in *.
        unfold sc_nodes in Hnode.
        take (LS.sem_node _ _ _ _) and eapply Hnode in it as Hsco; eauto.
        { (* output *)
          rename es into es'. rename l into es. clear Hin. rename i into f.
          assert (Hndup' := Hndup). inv H3.
          eapply sc_union_envs in Hndup' as (ncs & nss & Hlen & Hncs & Hscin); eauto.
          2:{ eapply Forall2_impl_In; eauto. intros ???? Hse.
              eapply sc_exp in Hse; eauto;
                try (now eapply Forall_forall; eauto).
              { eapply NoDupMembers_fresh_in'; eauto. }
              eapply var_inv_weaken; eauto. intros. simpl. constructor.
              constructor. apply Exists_exists; eauto. }

          unfold LC.WellInstantiated in WIo. unfold L.clock_of_nclock, stripname.
          rewrite Forall2_map_1. rewrite Forall2_map_2 in WIo.
          apply Forall2_swap_args in WIo.
          apply Forall2_trans_ex with (1 := WIo) in Hsco.
          eapply Forall2_impl_In; eauto.
          intros [aty (ack & anm)] so Hl0 ?((x'&ck')& Hxin & (Hsub & Hinst) & Hsc).
          simpl in *.
          pose proof (LC.wc_find_node G f n Hwcg) as [?(WCin&(WCio&?))]; eauto.
          eapply sc_inst; eauto.
          - pose proof (LC.wc_env_has_Cbase _ WCin) as [i Hin];
              [ unfold idck; rewrite map_length; exact (L.n_ingt0 n) |].
            apply LC.WellInstantiated_parent in WIi as Hp.
            change (Forall (fun ck => (fun x => x = bck \/ clock_parent bck x) (fst ck))
                           (L.nclocksof es)) in Hp.
            rewrite <- Forall_map in Hp. eapply sc_parent in Hp.
            2: rewrite <- L.clocksof_nclocksof; eauto.
            2:{ pose proof (Forall2_in_left _ _ _ _ WIi Hin) as [?(?&?& H42)].
                simpl in H42. inv H42. now apply in_map. }
            assert (forall x, Is_free_in_clock x bck -> InMembers x cenv). {
              intros ? Hfree. eapply instck_free_bck in Hfree; eauto.
              rewrite Forall2_map_2 in HFin1.
              eapply Forall2_in_right with (2 := Hl0) in HFin1 as (?&?&HH).
              unfold L.clock_of_nclock, stripname in HH. simpl in HH.
              eapply wc_env_free_in_clock in HH as []; eauto. eapply In_InMembers, InMembers_idck in H11; eauto.
            }
            apply sc_switch_adds in Hp.
            2: { intros ?? Hino; apply filter_anons_spec in Hino as []; eauto.
                 rewrite InMembers_idck in H19; eauto. }
            apply sc_switch_adds in Hp.
            2:{ intros ?? Hino.
                eapply Ino_Forall in Hino; eauto. simpl in Hino.
                apply Exists_exists in Hino as (?&?&Hf).
                eapply H10 in H11.
                eapply NoDupMembers_app_InMembers in Hndup; eauto.
                eapply InMembers_fresh_in in Hf; eauto.
            }
            assumption.
          - intros i i' Hfree Hisub.
            assert (InMembers i' cenv) as Hinm. {
              pose proof (Forall2_in_right _ _ _ _ WIo Hxin)
                as ((?&?)& Hin&?& Inst). simpl in *.
              pose proof (instck_free_sub _ _ _ _ _ _ Inst Hfree Hisub).
              rewrite Forall2_map_2 in HFin1.
              eapply Forall2_in_right with (2 := Hin) in HFin1 as (?&?&HH).
              unfold L.clock_of_nclock, stripname in HH. simpl in HH.
              eapply wc_env_free_in_clock in HH as []; eauto. eapply In_InMembers, InMembers_idck in H19; eauto.
            }
            eapply wc_env_free_in_clock in WCio as [ick Hin]; eauto.
            2:{ unfold idck. rewrite map_app. apply in_or_app. right. eauto. }
            rewrite idck_app in Hin. apply in_app_or in Hin as [Hin | Hin].
            + (* i ∈ idck(n_in n) *)
              eapply inst_in_eqst with (env := cenv) (nss := nss) in Hin; eauto.
              rewrite find_In_gsso_opt' in Hin.
              2: { intro HH; apply filter_anons_spec in HH as []; eauto.
                   rewrite InMembers_idck in H11; eauto. }
              rewrite find_In_gsso_opt' in Hin.
              2:{ intro Hino.
                  eapply Ino_Forall in Hino; eauto. simpl in Hino.
                  apply Exists_exists in Hino as (?&?&Hf).
                  eapply NoDupMembers_app_InMembers in Hndup; eauto.
                  eapply InMembers_fresh_in in Hf; eauto. }
              assumption.
            + (* i ∈ idck(n_out n) *)
              rename H7 into Hvout.
              rewrite idck_idents, Forall2_map_1 in Hvout.
              apply Forall2_swap_args in Hl1.
              eapply Forall2_trans_ex with (1 := Hvout) in Hl1.
              eapply Forall2_trans_ex with (1 := Hl1) in Hlifto1.
              rewrite Forall2_map_2 in Hlifto1.
              apply Forall2_swap_args in WIo.
              pose proof (Forall2_in_left_combine  _ _ _ _ WIo Hin)
                as (?& Comb & Sub &?).
              eapply Forall2_In with (1 := Comb) in Hlifto1
                as (?&?&(s &?&?&?)& Heq).
              simpl in *. rewrite <- Sub, Hisub in Heq. simpl in Heq. subst.
              do 2 take (LS.sem_var _ _ _) and inv it.
                 do 2 take (Env.MapsTo _ _ _) and apply Env.find_1 in it as ->.
                    constructor. transitivity s; auto. now symmetry.
        }
        { (* input *)
          take (L.find_node _ _ = _) and pose proof
               (LC.wc_find_node _ _ _ Hwcg it) as (?&(?&?)); eauto.
          inv H3. eapply sc_inside with (es := l) (env := cenv); eauto.
          eapply Forall2_impl_In; eauto. intros ???? Hsem.
          eapply sc_exp in Hsem; eauto;
            try now (eapply Forall_forall; eauto).
          { eapply NoDupMembers_fresh_in'; eauto. }
          eapply var_inv_weaken; eauto. simpl. intros. constructor.
          constructor. apply Exists_exists; eauto.
        }
      + admit. (* reset *)
    - inv Hwt. eapply IHes; eauto.
      { unfold L.anon_in_eq, L.anon_ins in *; simpl in *.
        rewrite Permutation_swap in Hndup. apply NoDupMembers_app_r in Hndup; auto. }
      eapply var_inv_weaken; eauto. intros. simpl. right. auto.
  Admitted.

  Lemma wc_free_clock :
    forall x ck vars,
      wc_clock vars ck ->
      Is_free_in_clock x ck ->
      In x (map fst vars).
  Proof.
    intros * Hwc Hfree. induction ck; inv Hfree; inv Hwc; auto.
    now apply in_map with (f := fst) in H3.
  Qed.

  (* Extract the [var_inv] invariant for defined variables (out + vars)
     from the causality of the node and the sem_clock of inputs. *)
  Lemma causal_variables :
    forall G n H xs H0,
      sc_nodes G ->
      Lord.Ordered_nodes G ->
      LT.wt_global G ->
      LC.wc_global G ->
      Forall2 (fun xc : ident * clock => NLSC.sem_clock H (clocks_of xs) (snd xc))
              (idck (L.n_in n)) (map abstract_clock xs) ->
      Forall2 (LS.sem_var H) (LS.idents (L.n_in n)) xs ->
      Forall2 (LS.sem_var H0) (LS.idents (L.n_in n)) xs ->
      wc_env (idck (L.n_in n)) ->
      wc_env (idck (L.n_in n ++ L.n_out n ++ L.n_vars n)) ->
      LCA.node_causal n ->
      Forall (LS.sem_equation G H0 (clocks_of xs)) (L.n_eqs n) ->
      Forall (LT.wt_equation G (idty (L.n_in n ++ L.n_vars n ++ L.n_out n))) (L.n_eqs n) ->
      Forall (LC.wc_equation G (idck (L.n_in n ++ L.n_vars n ++ L.n_out n))) (L.n_eqs n) ->
      forall env : Env.t (type * clock),
        envs_eq env (idck (L.n_in n ++ L.n_vars n ++ L.n_out n)) ->
        Forall
          (fun x : ident => forall (ss : Stream value) (ck : clock),
               LS.sem_var H0 x ss ->
               find_clock env x = OK ck ->
               NLSC.sem_clock H0 (clocks_of xs) ck (abstract_clock ss))
          (L.vars_defined (L.n_eqs n)).
  Proof.
    intros * Hscn Hord Hwcg Hwtg Hscin Hinv Hins Hwcin Hwcenv Hcaus Heqs Hwteq Hwceq.
    destruct Hcaus as [eqs (Hperm & Hcausal)].
    rewrite Hperm in Heqs, Hwteq, Hwceq.
    assert (Forall (fun e => NoDupMembers (L.n_in n ++ L.n_vars n ++ L.n_out n ++ L.anon_in_eq e)) eqs) as Hndup'.
    { rewrite Forall_forall. intros e Hin.
      assert (Hndup':=(L.n_nodup n)).
      unfold L.anon_in_eqs in Hndup'; rewrite Hperm in Hndup'.
      repeat rewrite app_assoc. eapply NoDupMembers_anon_in_eq'; eauto.
      repeat rewrite <- app_assoc; eauto. }
    unfold L.vars_defined. setoid_rewrite Hperm. clear Hperm.

    induction eqs as [| e]; inv Hwteq; inv Hwceq; inv Heqs;
      inversion_clear Hcausal as [| ?? Hcaus Hor]; simpl; auto.
    intros * Henvs.
    apply Forall_app; split; auto. eapply Forall_forall.
    intros z Hin zs ck Hsemz Hfind. eapply sc_equation; eauto.
    eapply wc_env_Proper; try eassumption. unfold idck. rewrite 4 map_app.
    now apply Permutation_app_head, Permutation_app_comm.
    { inv Hndup'. repeat rewrite <- app_assoc; auto. }
    2: { inv Hndup'; eauto. }
    intros y Hfree cky ys Iny Semy.
    pose proof (Hor y Hfree) as [Hydef | Hyin].
    - eapply IHeqs in Hcaus; eauto. eapply Forall_forall in Hcaus; eauto.
      apply Hcaus; eauto using envs_eq_find.
      inv Hndup'; auto.
    - unfold LS.idents, idck in Hscin, Hins, Hinv.
      rewrite Forall2_map_1 in Hins, Hinv.
      rewrite Forall2_map_1, Forall2_map_2 in Hscin.
      apply in_map_iff in Hyin
        as ((y' & (yt & yc)) & (Hyy' & Hyin)). simpl in Hyy'. inv Hyy'.
      eapply Forall2_Forall2 with (2 := Hins) in Hscin as Hscsv.
      eapply Forall2_in_left in Hscsv as (ys'&?&?&?); eauto. simpl in *.
      rewrite sem_var_var in *. eapply NLSC.sem_var_det in Semy; eauto.
      rewrite <- Semy. assert (Hyck := Hyin).
      apply in_app_weak with (l' := L.n_vars n) in Hyin.
      apply in_app_weak with (l' := L.n_out n) in Hyin.
      rewrite <- app_assoc in Hyin. unfold idck in Iny.
      apply in_map_iff in Iny as ((?&?)& HP & Hcky).
      destruct p. simpl in *. inv HP.
      eapply NoDupMembers_det in Hcky; eauto using (L.n_nodup n). inv Hcky.
      eapply sc_switch_env; eauto. intros x0 Hf.
      apply in_map with (f := fun xtc => (fst xtc, snd (snd xtc))) in Hyck.
      simpl in *. apply wc_env_var in Hyck; auto.
      eapply wc_free_clock in Hyck; eauto.
      apply Forall2_Forall2 with (1 := Hinv) in Hins.
      rewrite map_map in Hyck. apply in_map_iff in Hyck as ((?&?)&Heq&?).
      simpl in *. inv Heq.
      eapply Forall2_in_left in Hins as (?&?& V1 & V2); eauto.
      inversion_clear V1 as [???? a w]. inversion_clear V2 as [???? a' w'].
      now rewrite a, a', <- w, <- w'.
      specialize (L.n_nodup n) as Hndup.
      repeat rewrite app_assoc in *. apply NoDupMembers_app_l in Hndup; auto.
  Qed.

  Theorem l_sem_node_clock :
    forall G,
      Forall LCA.node_causal G ->
      Lord.Ordered_nodes G ->
      LT.wt_global G ->
      LC.wc_global G ->
      sc_nodes G.
  Proof.
    unfold sc_nodes.
    induction G as [|node]. now inversion 5.
    intros Hcaus Hord Hwt Hwc ????? Hsem Hfind Hinv Houtv Hscin. assert (Hsem' := Hsem).
    pose proof (Lord.find_node_not_Is_node_in _ _ _ Hord Hfind) as Hnini.
    inversion_clear Hsem' as [? ? ? ? ? ? Hfind' Hins Houts Heqs Hbk].
    simpl in Hfind. destruct (ident_eqb (L.n_name node) f) eqn:Hnf.
    - inv Hfind. simpl in Hfind'. rewrite Hnf in Hfind'. inv Hfind'.
      eapply LS.Forall_sem_equation_global_tl in Heqs; eauto.
      inversion_clear Hord as [|? ? Hord'' Hnneqs Hnn].
      inversion_clear Hwc as [|?? Hwcg Hwcn]. destruct Hwcn as (Hwcin & Hwcio &?& Hwceq).
      inversion_clear Hwt as [|?? Hwtg Hwtn]. destruct Hwtn as (Hwtin & Hwtio &?& Hwteq).

      assert (Houts' := Houts). unfold LS.idents in Houts. unfold idck.
      rewrite Forall2_map_1 in Houts. rewrite Forall2_map_1, Forall2_map_2.
      eapply Forall2_impl_In; eauto. intros (y & ?) ys Hiny ? Hsvy.
      simpl in *.

      inv Hcaus.
      pose proof (envs_eq_node n0) as Hsc.
      eapply causal_variables in Hsc; eauto.

      unfold L.vars_defined in Hsc.
      eapply (Forall_forall) in Hsc; eauto.
      2:{ rewrite (L.n_defd n0). rewrite map_app, in_app. right.
          rewrite in_map_iff. exists (y,p). eauto. }

      destruct p as [ty ck]. simpl.
      specialize (Hsc ys ck Hsvy (find_clock_out n0 y ty ck Hiny)).
      eapply sc_switch_env; eauto. intros x0 Hf.
      eapply in_app_weak in Hiny as Hx0. apply in_app_comm in Hx0.
      apply in_map with (f := fun xtc => (fst xtc, snd (snd xtc))) in Hx0.
      simpl in *. apply wc_env_var in Hx0; eauto.
      eapply wc_free_clock in Hx0; eauto.
      apply Forall2_Forall2 with (1 := Hinv) in Hins.
      apply Forall2_Forall2 with (1 := Houtv) in Houts'.
      unfold LS.idents in Hins, Houts'. rewrite Forall2_map_1 in Hins, Houts'.
      rewrite map_map in Hx0. apply in_map_iff in Hx0 as ((?&?)&Heq& Hx0).
      simpl in *. inv Heq.
      apply in_app_iff in Hx0 as [Hin|Hin];
        [ eapply Forall2_in_left in Hins as (?&?& V1 & V2)
        | eapply Forall2_in_left in Houts' as (?&?& V1 & V2)]; eauto;
          inversion_clear V1 as [???? t u]; inversion_clear V2 as [???? v w];
            inversion t as [Eq1]; inversion v as [Eq2];
            now rewrite Eq1, Eq2, <- u, <- w.
    - apply ident_eqb_neq in Hnf.
      eapply LS.sem_node_cons in Hsem; auto.
      rewrite cons_is_app in Hord.
      apply Lord.Ordered_nodes_append in Hord.
      inv Hwt. inv Hwc. inv Hcaus. eapply IHG; eauto.
  Qed.

  Lemma sem_lexp_step2: forall H b e v s,
      NLSC.sem_exp H b e (v ⋅ s) ->
      NLSC.sem_exp (NLSC.History_tl H) (Streams.tl b) e s.
  Proof.
    induction e; intros * Hsem; inv Hsem.
    - econstructor; eauto. unfold_St b. inv H4. simpl in *. eauto.
    - econstructor; eauto using sem_var_step_nl.
    - inv H9; econstructor; eauto using sem_var_step_nl.
    - inv H8; econstructor; eauto using sem_var_step_nl.
    - inv H10; econstructor; eauto using sem_var_step_nl.
  Qed.

  Lemma sem_cexp_step2: forall H b e v s,
      NLSC.sem_cexp H b e (v ⋅ s) ->
      NLSC.sem_cexp (NLSC.History_tl H) (Streams.tl b) e s.
  Proof.
    induction e; intros * Hsem; inv Hsem.
    - inv H10; econstructor; eauto using sem_var_step_nl.
    - inv H10; econstructor; eauto using sem_lexp_step2.
    - econstructor; eauto using sem_lexp_step2.
  Qed.

  Lemma fby_const:
    forall b c xs ys rs,
      LS.fby xs ys rs ->
      xs ≡ const b c ->
      b  ≡ abstract_clock rs ->
      rs ≡ NLSC.fby (sem_const c) ys.
  Proof.
    cofix Cofix; intros * Hfby Hconst Hac.
    unfold_Stv ys; inv Hfby; rewrite unfold_Stream in Hac;
      simpl in Hac; rewrite unfold_Stream; simpl; symmetry in Hconst.
    - apply const_inv1 in Hconst.
      destruct Hconst as (?& Hc & Hb). rewrite Hb in Hac.
      inv Hac; simpl in *. econstructor; simpl; eauto.
    - apply const_inv2 in Hconst.
      destruct Hconst as (?& Hc & Hb & Hx). rewrite Hb in Hac.
      inv Hac; simpl in *. econstructor; simpl; eauto.
      clear H Cofix. revert H0 H3 Hb Hc. revert rs0 x0 ys xs0 v c b.
      cofix Cofix; intros * Hac Hfby1 Hb Hconst.
      unfold_Stv ys; inv Hfby1; rewrite unfold_Stream in Hac;
        simpl in Hac; rewrite unfold_Stream; simpl; symmetry in Hconst.
      + apply const_inv1 in Hconst.
        destruct Hconst as (?& Hc & Hbb). rewrite Hbb in Hac.
        inv Hac; simpl in *. econstructor; simpl; eauto.
        eapply Cofix; eauto. reflexivity.
      + apply const_inv2 in Hconst.
        destruct Hconst as (?& Hc & Hbb & Hx). rewrite Hbb in Hac.
        inv Hac; simpl in *. econstructor; simpl; eauto.
  Qed.

  Lemma sem_const_exp:
    forall G H b e c c' xs,
      to_constant e = OK c ->
      LS.sem_exp G H b e [present c' ⋅ xs] ->
      c' = sem_const c.
  Proof.
    induction e using L.exp_ind2; intros * Htoc Hsem;
      inv Htoc; inv Hsem.
    - symmetry in H5. apply const_inv2 in H5. inv H5. tauto.
    - cases. inv H0. inv H5.
      inv H10. inv H6. inv H12. inv H7. rewrite app_nil_r in H0.
      subst. inv H6.
      eapply H4; eauto.
  Qed.

  Lemma fby_const_when :
    forall G H bk x i ck e b c s cs css xs ys,
      LS.sem_var H x xs ->
      NLSC.sem_clock H bk (Con ck i b) (abstract_clock xs) ->
      LS.fby css ys xs ->
      to_constant e = OK c ->
      LS.sem_exp G H bk e [cs] ->
      when b cs s css ->
      xs ≡ NLSC.fby (sem_const c) ys.
  Proof.
    cofix Cofix; intros * Hsemv Hsc Hfby Htoc Hse Hwhen.
    unfold_Stv xs; inv Hfby; rewrite unfold_Stream; simpl;
      rewrite unfold_Stream in Hsc; simpl in Hsc.
    - econstructor; simpl; eauto. destruct cs.
      eapply sem_var_step in Hsemv; eauto.
      assert (Htoc' := Htoc).
      eapply sem_const_step in Htoc; eauto.
      eapply sc_step in Hsc.
      inv Hwhen; eapply Cofix; eauto.
    - econstructor; simpl; eauto. inv Hwhen. f_equal.
      eapply sem_const_exp; eauto. clear Cofix.
      eapply sc_step in Hsc.
      eapply sem_var_step in Hsemv.
      assert (Htoc' := Htoc).
      inv Hwhen. eapply sem_const_step in Htoc'; eauto. clear Hse.
      revert dependent H. revert H3 H5 H6. revert bk xs xs0 xs1 xs0 cs0 ys0 y.
      cofix Cofix; intros.
      unfold_Stv xs; inv H3; rewrite unfold_Stream; simpl;
        rewrite unfold_Stream in Hsc; simpl in Hsc;
          eapply sc_step in Hsc;
          eapply sem_var_step in Hsemv;
          econstructor; simpl; eauto;
            inv H5; eapply Cofix; eauto using sem_const_step.
  Qed.

  Lemma var_fby_const :
    forall G H b c a env cenv ck ckx x e0 e1 cs xs ys,
      LS.sem_exp G H b e0 [cs] ->
      LS.sem_var H x xs ->
      LS.fby cs ys xs ->
      find_clock env x = OK ck ->
      LC.wc_exp G cenv (L.Efby [e0] [e1] a) ->
      [ckx] = map L.clock_of_nclock a ->
      In (x, ckx) cenv ->
      envs_eq env cenv ->
      to_constant e0 = OK c ->
      NLSC.sem_clock H b ck (abstract_clock xs) ->
      NLSC.sem_var H x (NLSC.fby (sem_const c) ys).
  Proof.
    destruct ck; intros * Hse Hxs Hfby Hfind Hwc Hckx Hin Henv Htoc Hsc.
    - (* ck = Base. Show that e0 is not EWhen *)
      inv Hsc. destruct e0; inv Htoc.
      + inv Hse. eapply fby_const in Hfby; eauto.
        now rewrite <- Hfby, <- sem_var_var.
      + cases. inv Hwc. inv H5. inv H4. rewrite <- Hckx in H7.
        inv H7. inv H11. destruct tys; inv H4.
        unfold L.clock_of_nclock, stripname in Hin. simpl in Hin.
        eapply envs_eq_find with (x := x) in Henv; eauto.
        rewrite Henv in Hfind. discriminate.
    - destruct e0; inv Htoc.
      + inv Hse. eapply fby_const in Hfby; eauto.
        now rewrite <- Hfby, <- sem_var_var.
        apply ac_fby1 in Hfby. symmetry in H5. apply ac_const in H5.
        now rewrite H5, Hfby.
      + cases. eapply envs_eq_find with (x := x) in Henv; eauto.
        rewrite Henv in Hfind. inv Hfind. destruct a; inv Hckx.
        destruct a0; inv H3.
        inv Hwc. inv H5. inv H4. simpl in *.
        rewrite app_nil_r in H7. destruct tys; inv H7.
        destruct tys; inv H16. rewrite <- H2 in H5.
        unfold L.clock_of_nclock, stripname in H5. simpl in H5. inv H5.
        (* now (i,b0) = (i0,b1) *)
        inv Hse. inv H18. inv H7. simpl in H20. rewrite app_nil_r in H20.
        inv H20. inv H11.
        assert (Hxs' := Hxs).
        eapply fby_const_when in Hxs; eauto.
        now rewrite <- Hxs, <- sem_var_var.
  Qed.

  Lemma sem_exp_caexp :
    forall G H b env e e' s ck,
      LT.wt_exp G env e ->
      to_cexp e = OK e' ->
      LS.sem_exp G H b e [s] ->
      NLSC.sem_clock H b ck (abstract_clock s) ->
      NLSC.sem_caexp H b ck e' s.
  Proof.
    cofix Cofix. intros * Hwt Hto Hsem Hsc.
    pose proof (sem_exp_cexp _ _ _ _ _ _ _ _ Hwt Hto Hsem).
    unfold_Stv s; rewrite unfold_Stream in Hsc; simpl in Hsc;
      econstructor; eauto; eapply Cofix;
        eauto using sc_step, sem_cexp_step.
  Qed.

  Lemma sem_lexp_laexp :
    forall H b e s ck,
      NLSC.sem_exp H b e s ->
      NLSC.sem_clock H b ck (abstract_clock s) ->
      NLSC.sem_aexp H b ck e s.
  Proof.
    cofix Cofix. intros * Hsem Hsc.
    unfold_Stv s; rewrite unfold_Stream in Hsc; simpl in Hsc;
      econstructor; eauto; eapply Cofix;
        eauto using sc_step, sem_lexp_step2.
  Qed.

  Definition sem_clock_inputs (G : L.global) (f : ident) (xs : list (Stream value)): Prop :=
    exists H n,
      L.find_node f G = Some n /\
      Forall2 (LS.sem_var H) (LS.idents (L.n_in n)) xs /\
      Forall2 (fun xc => NLSC.sem_clock H (clocks_of xs) (snd xc))
              (idck (L.n_in n)) (map abstract_clock xs).

  Lemma sem_toeq :
    forall cenv G H P env envo eq eq' b,
      LT.wt_equation G (idty cenv) eq ->
      LC.wc_equation G (idck cenv) eq ->
      LC.wc_global G ->
      sc_nodes G ->
      NoDupMembers (cenv ++ L.anon_in_eq eq) ->
      wc_env (idck cenv) ->
      envs_eq env (idck cenv) ->
      (forall f xs ys,
          LS.sem_node G f xs ys ->
          sem_clock_inputs G f xs ->
          NLSC.sem_node P f xs ys) ->
      var_inv (fun x => Exists (fun e => LCA.Is_free_left x e) (snd eq)) (idck cenv) H b ->
      to_equation env envo eq = OK eq' ->
      LS.sem_equation G H b eq ->
      NLSC.sem_equation P H b eq'.
  Proof.
    intros ?????? [xs [|e []]] eq' b Hwt Hwc Hwcg Hscg
           Hnodup Henv Henvs Hsemnode Hvar Htoeq Hsem; try now (inv Htoeq; cases).
    destruct e.
    - unfold to_equation in Htoeq. cases. monadInv Htoeq.
      inversion Hsem; subst. simpl_Foralls.
      eapply sc_equation in Hwc; simpl; eauto.
      econstructor; try (eapply sem_var_var; eauto).
      inv Hwt. simpl_Foralls. eapply sem_exp_caexp; eauto.
      simpl in *. rewrite app_nil_r in *. now subst.
    - unfold to_equation in Htoeq. cases. monadInv Htoeq.
      inversion Hsem. subst. simpl_Foralls.
      eapply sc_equation in Hwc; simpl; eauto.
      econstructor; try (eapply sem_var_var; eauto).
      inv Hwt. simpl_Foralls. eapply sem_exp_caexp; eauto.
      simpl in *. rewrite app_nil_r in *. now subst.
    - unfold to_equation in Htoeq. cases. monadInv Htoeq.
      inversion Hsem. subst. simpl_Foralls.
      eapply sc_equation in Hwc; simpl; eauto.
      econstructor; try (eapply sem_var_var; eauto).
      inv Hwt. simpl_Foralls. eapply sem_exp_caexp; eauto.
      simpl in *. rewrite app_nil_r in *. now subst.
    - unfold to_equation in Htoeq. cases. monadInv Htoeq.
      inversion Hsem. subst. simpl_Foralls.
      eapply sc_equation in Hwc; simpl; eauto.
      econstructor; try (eapply sem_var_var; eauto).
      inv Hwt. simpl_Foralls. eapply sem_exp_caexp; eauto.
      simpl in *. rewrite app_nil_r in *. now subst.
    - (* EFby *)
      inversion Htoeq as [Heq']. cases; monadInv Heq'. rename x1 into ck.
      assert (Hsem' := Hsem).
      inversion_clear Hsem as [ ????? Hseme Hsemv].
      inversion Hseme as [| ???? Hsef Hse]. inv Hse. simpl in Hsemv.
      rewrite app_nil_r in Hsemv.
      inversion Hsemv as [|???? Hsvar Hf2]. inv Hf2.
      assert (Hsc := Hwc). eapply sc_equation in Hsc; simpl; eauto.
      inversion_clear Hwc as [Hwce ?]. inv Hwce.
      inversion_clear Hwt as [Hwte ?]. inversion Hwte as [|?? Hwt].
      inversion Hwt as [| | | | ? ? ? ? Hwte1 | | | | |]. inv Hwte1.
      inversion Hsef as [| | | |???????? Hse0 Hse1 Hwfby | | | | |].
      inversion Hse1 as [|????? Hf2]. inv Hf2.
      inversion Hwfby as [|?????? Hlsf Hf Hcat]. inv Hf. rewrite app_nil_r in *.
      subst. eapply sem_exp_lexp in EQ2; eauto.
      econstructor; eauto. instantiate (1 := y1).
      apply ac_fby2 in Hlsf. rewrite <- Hlsf in Hsc.
      eapply sem_lexp_laexp; eauto.
      (* we show how to erase Whens in constants using var_fby_const *)
      inversion Hse0 as [| ????? Hf2]. inv Hf2.
      inversion Hcat as [Hx1]. rewrite app_nil_r in Hx1. subst.
      destruct H0 as (HliftO & HFin).
      inversion HFin as [|?????  Hf2 Huseless Hnil].
      inv Hf2. rewrite app_nil_r in Hnil.
      eapply var_fby_const; eauto.
    - unfold to_equation in Htoeq. cases. monadInv Htoeq.
      inversion Hsem. subst. simpl_Foralls.
      eapply sc_equation in Hwc; simpl; eauto.
      econstructor; try (eapply sem_var_var; eauto).
      inv Hwt. simpl_Foralls. eapply sem_exp_caexp; eauto.
      simpl in *. rewrite app_nil_r in *. now subst.
    - unfold to_equation in Htoeq. cases. monadInv Htoeq.
      inversion Hsem. subst. simpl_Foralls.
      eapply sc_equation in Hwc; simpl; eauto.
      econstructor; try (eapply sem_var_var; eauto).
      inv Hwt. simpl_Foralls. eapply sem_exp_caexp; eauto.
      simpl in *. rewrite app_nil_r in *. now subst.
    - unfold to_equation in Htoeq. cases. monadInv Htoeq.
      inversion Hsem. subst. simpl_Foralls.
      eapply sc_equation in Hwc; simpl; eauto.
      econstructor; try (eapply sem_var_var; eauto).
      inv Hwt. simpl_Foralls. eapply sem_exp_caexp; eauto.
      simpl in *. rewrite app_nil_r in *. now subst.
    - (* Eapp *)
      simpl in Htoeq.
      cases; monadInv Htoeq. admit. (* reset *)
      unfold L.anon_in_eq, L.anon_ins in Hnodup; simpl in Hnodup; rewrite app_nil_r in Hnodup.
      inversion Hsem. subst. inv Hwt. simpl_Foralls. simpl in *. rewrite app_nil_r in *.
      take (LS.sem_exp _ _ _ _ _) and inv it.
      (* 2: cases; monadInv Htoeq. *)
      take (LT.wt_exp _ _ _) and inv it.
      econstructor; eauto using sem_exps_lexps.
      2:{ eapply Hsemnode; eauto. take (LS.sem_node _ _ _ _) and inv it.
          unfold sem_clock_inputs. esplit; esplit; split; eauto. split; eauto.
          (* now we use sc_inside *)
          destruct Hwc as (Hwc & ?& Hinxs). simpl_Foralls.
          take (LC.wc_exp _ _ _) and inv it.
          match goal with
          | H1: L.find_node _ G = Some _, H2: L.find_node _ G = Some _ |- _
            => rewrite H2 in H1; inv H1
          end.
          take (L.find_node _ _ = _) and eapply LC.wc_find_node in it
            as (?&?&?); eauto.
          eapply sc_inside with (es := l); eauto.
          eapply Forall2_impl_In; eauto. intros.
          eapply sc_exp; eauto; try (now eapply Forall_forall; eauto).
          { eapply NoDupMembers_fresh_in'; eauto. }
          eapply var_inv_weaken; eauto. intros. simpl. constructor.
          constructor. eapply Exists_exists; eauto.
      }
      2: eapply Forall2_impl_In; [intros | eassumption ]; now apply sem_var_var.

      destruct Hwc as (Hwc & ?& Hinxs). simpl_Foralls.
      take (LC.wc_exp _ _ _) and inversion_clear it
        as [| | | | | | | | |???? bck sub Wce ? WIi WIo|].
      take (Forall2 (LS.sem_exp _ _ _) _ _) and eapply sc_union_envs
        in it as (?&?&?&?& Hsc); eauto.
      2:{
        eapply Forall2_impl_In; eauto. intros ???? Hse.
        eapply sc_exp in Hse; eauto; try (now eapply Forall_forall; eauto).
        { eapply NoDupMembers_fresh_in'; eauto. }
        eapply var_inv_weaken; eauto. simpl. intros. constructor.
        constructor. apply Exists_exists; eauto.
      }
      simpl in *.
      take (L.find_node _ _ = Some n0) and
           pose proof (LC.wc_find_node _ _ n0 Hwcg it) as (?& (Wcin &?)).
      assert (find_base_clock (L.clocksof l) = bck) as ->.
      {
        apply find_base_clock_bck.
        + rewrite L.clocksof_nclocksof. eapply LC.WellInstantiated_bck; eauto.
          unfold idck. rewrite map_length. exact (L.n_ingt0 n0).
        + apply LC.WellInstantiated_parent in WIi.
          rewrite L.clocksof_nclocksof, Forall_map.
          eapply Forall_impl; eauto. now simpl.
      }
      eapply sc_parent with (ck := bck) in Hsc.
      2:{ rewrite L.clocksof_nclocksof. eapply LC.WellInstantiated_bck; eauto.
          unfold idck. rewrite map_length. exact (L.n_ingt0 n0). }
      2:{ apply LC.WellInstantiated_parent in WIi.
          rewrite L.clocksof_nclocksof, Forall_map.
          eapply Forall_impl; eauto. now simpl. }
      assert (forall x, Is_free_in_clock x bck -> InMembers x cenv). {
        intros ? Hfr.
          destruct l0 as [| a].
          { inv WIo. take ([] = _) and symmetry in it.
            apply map_eq_nil, length_zero_iff_nil in it.
            pose (L.n_outgt0 n0). omega. }
          simpl in WIo. inv WIo. take (LC.WellInstantiated _ _ _ _) and inv it.
          eapply instck_free_bck in Hfr; eauto.
          inv Hinxs. unfold L.clock_of_nclock, stripname in *.
          eapply wc_env_free_in_clock with (vars := idck cenv) in Hfr as (?&?); eauto.
          eapply In_InMembers, InMembers_idck in H15; eauto.
      }
      eapply sc_switch_adds in Hsc; eauto.
      2:{ intros ? Hfr Hino. apply filter_anons_spec in Hino as [Hino]; eauto.
          rewrite InMembers_idck in H13; eauto. }
      eapply sc_switch_adds in Hsc; eauto.
      { intros ? Hfr Hino. eapply Ino_Forall in Hino; eauto. simpl in Hino.
        apply Exists_exists in Hino as (?&?& Hf).
        apply H12 in Hfr.
        eapply NoDupMembers_app_InMembers in Hnodup; eauto.
        eapply Hnodup, InMembers_fresh_in; eauto.
      }
  Admitted.

  Lemma sem_var_env_eq :
    forall H H' xs ss,
      Forall2 (LS.sem_var H) xs ss ->
      Forall2 (LS.sem_var H') xs ss ->
      Forall (fun x => orel (EqSt (A:=value)) (Env.find x H) (Env.find x H')) xs.
  Proof.
    induction 1; auto. intros Hf. inv Hf. constructor; auto.
    do 2 take (LS.sem_var _ _ _) and inv it.
    do 2 take (Env.MapsTo _ _ _) and apply Env.find_1 in it as ->.
    now rewrite <- H4, <- H5.
  Qed.

  Lemma sem_toeqs :
    forall G n H P env envo eqs' ins,
      Forall (LT.wt_equation G (idty (L.n_in n ++ L.n_vars n ++ L.n_out n))) (L.n_eqs n) ->
      Forall (LC.wc_equation G (idck (L.n_in n ++ L.n_vars n ++ L.n_out n))) (L.n_eqs n) ->
      LCA.node_causal n ->
      Lord.Ordered_nodes G ->
      LT.wt_global G ->
      LC.wc_global G ->
      sc_nodes G ->
      wc_env (idck (L.n_in n ++ L.n_vars n ++ L.n_out n)) ->
      envs_eq env (idck (L.n_in n ++ L.n_vars n ++ L.n_out n)) ->
      (forall f xs ys,
          LS.sem_node G f xs ys ->
          sem_clock_inputs G f xs ->
          NLSC.sem_node P f xs ys) ->
      LC.wc_node G n ->
      Forall2 (LS.sem_var H) (LS.idents (L.n_in n)) ins ->
      sem_clock_inputs (n :: G) (L.n_name n) ins ->
      mmap (to_equation env envo) (L.n_eqs n) = OK eqs' ->
      Forall (LS.sem_equation G H (clocks_of ins)) (L.n_eqs n) ->
      Forall (NLSC.sem_equation P H (clocks_of ins)) eqs'.
  Proof.
    intros * Hwt Hwc Hcaus Hord Hwcg Hwtg Hscn (* Henv *) Hcenv Henvs Hnode Hwcn
                 Hins Hscin Hmmap Hsem.

    destruct Hscin as (H0 & n0 & Hfind & Hins' & Hscin).
    simpl in Hfind. rewrite ident_eqb_refl in Hfind. inv Hfind.
    destruct Hwcn as (Wcin &?&?& Hwceqs).
    pose proof (envs_eq_node n0) as Heq.
    eapply causal_variables with (H0 := H) in Heq as Hvar; eauto.

    assert (Forall (fun e => NoDupMembers (L.n_in n0 ++ L.n_vars n0 ++ L.n_out n0 ++ L.anon_in_eq e)) (L.n_eqs n0)) as Hndup'.
    { rewrite Forall_forall. intros e Hin.
      assert (Hndup:=(L.n_nodup n0)).
      unfold L.anon_in_eqs in Hndup.
      repeat rewrite app_assoc. eapply NoDupMembers_anon_in_eq'; eauto.
      repeat rewrite <- app_assoc; eauto. }

    assert (Hvar2 := Hvar). rewrite L.n_defd in Hvar2.
    revert dependent eqs'.
    induction Hsem; intros. now inv Hmmap. apply mmap_cons in Hmmap.
    destruct Hmmap as (eq' & leq' & Heqs' & Htoeq & Hmmap). subst.
    inv Hwt. inv Hwc.
    simpl in Hvar. apply Forall_app in Hvar as [Hvar Hvar'].
    constructor. 2: take (Forall _ (_::_)) and inv it; eapply IHHsem; eauto.
    eapply sem_toeq in Htoeq; eauto.
    { inv Hndup'. repeat rewrite <- app_assoc; auto. }
    intros y Hfr ck ys Hin Hy.

    inv Hwceqs. eapply free_left_env in Hfr; eauto.
    unfold idck in Hfr.
    rewrite map_app, InMembers_app in Hfr.
    destruct Hfr as [Hini| Hinov].
    - (* input *)
      pose proof (L.n_nodup n0) as Hdup.
      apply InMembers_In in Hini as (?&?).
      unfold idck in Hin. rewrite map_app, in_app in Hin.
      destruct Hin as [Hin|Hin]. 2:{
        exfalso.
        eapply NoDupMembers_app_InMembers with (x1 := y) in Hdup.
        2: apply InMembers_idck; eapply In_InMembers; eauto.
        apply In_InMembers,InMembers_idck in Hin.
        apply Hdup. rewrite app_assoc, InMembers_app; auto.
      }
      pose proof (sem_var_env_eq _ _ _ _ Hins Hins') as Horel.

      rewrite idck_idents, Forall2_map_1 in Hins.
      rewrite Forall2_map_2 in Hscin.
      pose proof (Forall2_Forall2 _ _ _ _ Hins Hscin) as Hf2.
      pose proof (Forall2_in_left _ _ _ _ Hf2 Hin) as (?&?& Hv&?).
      simpl in *. rewrite sem_var_var in *.
      eapply NLSC.sem_var_det in Hy; eauto. rewrite <- Hy.
      eapply sc_switch_env; eauto.
      intros * Hfr.
      eapply Forall_forall in Horel; eauto.
      unfold LS.idents.
      eapply wc_env_free_in_clock with (ck := ck) in Wcin as (?&?); eauto.
      rewrite <- fst_InMembers, <- InMembers_idck. eauto using In_InMembers.
    - (* defined variable *)
      rewrite fst_InMembers, map_map in Hinov. simpl in Hinov.
      pose proof Hinov as Hsc; eapply Forall_forall in Hsc; eauto.
      simpl in Hsc.
      apply Hsc; auto. subst. eapply envs_eq_find; eauto.
  Qed.

  Lemma inin_l_nl :
    forall f n n',
      to_node n = OK n' ->
      Ord.Is_node_in f (NL.n_eqs n') ->
      Lord.Is_node_in f (L.n_eqs n).
  Proof.
    intros * Htr Hord.
    destruct n'. simpl in Hord.
    tonodeInv Htr.
    clear - Hord Hmmap. revert dependent n_eqs.
    induction (L.n_eqs n); intros. inv Hmmap. inv Hord.
    apply mmap_cons in Hmmap.
    destruct Hmmap as (eq' & l' & Hneqs & Hteq & Hmmap); subst.
    inversion_clear Hord as [ ? ? Hord' |].
    - econstructor.
      destruct eq' as [| i ck x le |]; inv Hord'.
      destruct a as [ xs [|]]. inv Hteq. cases.
      destruct l0; [ idtac | inv Hteq; cases ].
      destruct e; inv Hteq; cases; monadInv H0;
        econstructor; apply Lord.INEapp2.
    - apply Exists_cons_tl. eapply IHl; eauto.
  Qed.

  Lemma ninin_l_nl :
    forall f n n',
      to_node n = OK n' ->
      ~ Lord.Is_node_in f (L.n_eqs n) ->
      ~ Ord.Is_node_in f (NL.n_eqs n').
  Proof.
    intros. intro. destruct H0. eapply inin_l_nl; eauto.
  Qed.

  Lemma ord_l_nl :
    forall G P,
      to_global G = OK P ->
      Lord.Ordered_nodes G ->
      Ord.Ordered_nodes P.
  Proof.
    intros * Htr Hord.
    revert dependent P.
    induction Hord; intros. inv Htr. constructor.
    apply mmap_cons in Htr.
    destruct Htr as (n' & P' & HP & Hton & Hmmap). subst.
    constructor; auto.
    - intros f Hin.
      assert (Lord.Is_node_in f (L.n_eqs nd)) as Hfin.
      eapply inin_l_nl; eauto.
      apply H in Hfin. destruct Hfin as [ Hf Hnds ].
      split.
      apply to_node_name in Hton. now rewrite <- Hton.
      clear - Hnds Hmmap. revert dependent P'.
      induction nds; intros; inv Hnds;
        apply mmap_cons in Hmmap;
        destruct Hmmap as (n'' & P'' & HP & Hton' & Hmmap); subst.
      constructor. now apply to_node_name.
      apply Exists_cons_tl. apply IHnds; auto.
    - apply to_node_name in Hton. rewrite <- Hton.
      monadInv Hmmap. clear - H0 H1.
      induction H1; eauto. inv H0.
      constructor. apply to_node_name in H. now rewrite <- H.
      now apply IHlist_forall2.
  Qed.

  Lemma sem_clock_inputs_cons :
    forall G f n ins,
      sem_clock_inputs (n :: G) f ins ->
      L.n_name n <> f ->
      sem_clock_inputs G f ins.
  Proof.
    intros * Hscin Hname.
    destruct Hscin as (H & n' & Hfind &?&?).
    apply L.find_node_other in Hfind; auto.
    exists H, n'; auto.
  Qed.

  Lemma inputs_clocked_vars :
    forall n G H f ins,
      sem_clock_inputs (n :: G) f ins ->
      L.n_name n = f ->
      wc_env (idck (L.n_in n)) ->
      Forall2 (LS.sem_var H) (LS.idents (L.n_in n)) ins ->
      NLSC.sem_clocked_vars H (clocks_of ins) (idck (L.n_in n)).
  Proof.
    intros * (H'&n'& Hfind & Hv & Hscin) Hnf Wcin Hins.
    simpl in Hfind. rewrite <- Hnf, ident_eqb_refl in Hfind. inv Hfind.
    pose proof (sem_var_env_eq _ _ _ _ Hins Hv) as Horel.
    unfold NLSC.sem_clocked_vars, NLSC.sem_clocked_var.
    rewrite idck_idents in *. rewrite Forall2_map_1 in Hv, Hins.
    apply Forall_forall. intros (?&ck) Hin. split; intros ? Hvar.
    - rewrite Forall2_map_2 in Hscin.
      pose proof (Forall2_Forall2 _ _ _ _ Hins Hscin) as Hf2.
      pose proof (Forall2_in_left _ _ _ _ Hf2 Hin) as (s&?& Hv'&?).
      exists (abstract_clock s). split.
      eapply sc_switch_env; eauto. intros * Hfr.
      eapply Forall_forall in Horel; eauto.
      eapply wc_env_free_in_clock in Wcin as (?& Hmem); eauto.
      rewrite <- fst_InMembers. now apply In_InMembers in Hmem.
      simpl in *. rewrite sem_var_var in *.
      eapply NLSC.sem_var_det in Hvar; eauto. rewrite <- Hvar.
      apply ac_synchronized.
    - pose proof (Forall2_in_left _ _ _ _ Hins Hin) as (?&?&?).
      setoid_rewrite <- sem_var_var. eauto.
  Qed.

  Theorem sem_l_nl :
    forall G P f ins outs,
      Lord.Ordered_nodes G ->
      Forall LCA.node_causal G ->
      LT.wt_global G ->
      LC.wc_global G ->
      to_global G = OK P ->
      LS.sem_node G f ins outs ->
      sem_clock_inputs G f ins ->
      NLSC.sem_node P f ins outs.
  Proof.
    induction G as [|node]. now inversion 6.
    intros * Hord Hcaus Hwt Hwc Htr Hsem Hscin.
    assert (Hsem' := Hsem).
    inversion_clear Hsem' as [? ? ? ? ? ? Hfind Hins Houts Heqs Hbk].
    pose proof (Lord.find_node_not_Is_node_in _ _ _ Hord Hfind) as Hnini.
    inv Hwt. inv Hwc. inv Hcaus.
    simpl in Hfind. destruct (ident_eqb (L.n_name node) f) eqn:Hnf.
    - assert (Hord':=Hord).
      inversion_clear Hord as [|? ? Hord'' Hnneqs Hnn].
      injection Hfind; intro HR; rewrite HR in *; clear HR; simpl in *.
      eapply LS.Forall_sem_equation_global_tl in Heqs; eauto.
      assert (Htr' := Htr). apply mmap_cons in Htr'.
      destruct Htr' as (n' & P' & Hp & Htrn & Hmmap). subst.
      assert (forall f ins outs,
                 LS.sem_node G f ins outs ->
                 sem_clock_inputs G f ins ->
                 NLSC.sem_node P' f ins outs) as IHG'
          by auto.
      apply ident_eqb_eq in Hnf. rewrite <- Hnf.
      take (LT.wt_node _ _) and inversion it as (Hwt1 & Hwt2 & Hwt3 & Hwt4).
      take (LC.wc_node _ _) and inversion it as (Hwc1 & Hwc2 & Hwc3 & Hwc4).
      econstructor; simpl.
      + tonodeInv Htrn. rewrite ident_eqb_refl; eauto.
      + tonodeInv Htrn. simpl.
        eapply Forall2_impl_In in Hins; eauto.
        intros * Hina Hinb0 Hsemv.
        eapply sem_var_var. eauto.
      + tonodeInv Htrn. simpl. eapply Forall2_impl_In in Houts; eauto.
        intros * Hina Hinb0 Hsemv. eapply sem_var_var. eauto.
      + erewrite <- to_node_in; eauto.
        eapply inputs_clocked_vars; eauto.
      + apply NLSC.sem_equation_cons2; auto.
        * eapply ord_l_nl; eauto.
        * assert (Hton := Htrn). tonodeInv Htrn. simpl in *.
          eapply sem_toeqs; eauto using l_sem_node_clock.
          eapply wc_env_Proper; try eassumption. unfold idck. rewrite 4 map_app.
          now apply Permutation_app_head, Permutation_app_comm.
          apply envs_eq_node.
        * assert (Htrn' := Htrn).
          apply to_node_name in Htrn. rewrite <- Htrn.
          eapply ninin_l_nl; eauto.
    - apply ident_eqb_neq in Hnf.
      eapply LS.sem_node_cons in Hsem; auto.
      eapply sem_clock_inputs_cons in Hscin; auto.
      assert (Htr' := Htr).
      apply mmap_cons in Htr.
      destruct Htr as (n' & P' & Hp & Htn & Hmmap). subst.
      rewrite cons_is_app in Hord.
      apply Lord.Ordered_nodes_append in Hord.
      eapply NLSC.sem_node_cons2; eauto.
      + eapply ord_l_nl; eauto.
      + apply to_node_name in Htn. rewrite <- Htn.
        monadInv Hmmap. clear - H0 H7.
        induction H0; eauto. inv H7.
        constructor. apply to_node_name in H. now rewrite <- H.
        now apply IHlist_forall2.
  Qed.

End CORRECTNESS.

Module CorrectnessFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX        Op)
       (L     : LSYNTAX          Ids Op)
       (CE    : CESYNTAX             Op)
       (NL    : NLSYNTAX         Ids Op              CE)
       (TR    : TRANSCRIPTION    Ids Op OpAux L      CE NL)
       (LT    : LTYPING          Ids Op       L)
       (LC    : LCLOCKING        Ids Op       L)
       (LCA   : LCAUSALITY       Ids Op       L)
       (Ord   : NLORDERED        Ids Op              CE NL)
       (Lord  : LORDERED         Ids Op       L)
       (Str   : COINDSTREAMS         Op OpAux)
       (LS    : LSEMANTICS       Ids Op OpAux L Lord       Str)
       (NLSC  : NLCOINDSEMANTICS Ids Op OpAux        CE NL Str Ord)
<: CORRECTNESS Ids Op OpAux L CE NL TR LT LC LCA Ord Lord Str LS NLSC.
  Include CORRECTNESS Ids Op OpAux L CE NL TR LT LC LCA Ord Lord Str LS NLSC.
End CorrectnessFun.
