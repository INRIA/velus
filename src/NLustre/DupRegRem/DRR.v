From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Coq Require Import Recdef.
From Velus Require Import Common.
From Velus Require Import CommonProgram.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Environment.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import NLustre.NLSyntax.

(** Remove duplicate registers in an NLustre program *)

Module Type DRR
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX   Ids Op)
       (Import Cks   : CLOCKS      Ids Op OpAux)
       (Import CESyn : CESYNTAX    Ids Op OpAux Cks)
       (Import Syn   : NLSYNTAX    Ids Op OpAux Cks CESyn).

  Definition const_dec : forall (c1 c2 : const),
    { c1 = c2 } + { c1 <> c2 }.
  Proof.
    decide equality.
    1-2:auto using cconst_dec, Nat.eq_dec.
  Defined.

  Definition exp_dec : forall (e1 e2 : exp),
    { e1 = e2 } + { e1 <> e2 }.
  Proof.
    decide equality.
    1-11:auto using cconst_dec, Nat.eq_dec, Pos.eq_dec.
    1-3,5:apply EqDec_instance_5.
    apply EqDec_instance_3.
    apply EqDec_instance_4.
  Defined.

  Global Instance: EqDec const eq := { equiv_dec := const_dec }.
  Global Instance: EqDec exp eq := { equiv_dec := exp_dec }.

  Definition find_duplicates (eqs : list equation) : Env.t ident :=
    snd (fold_left
           (fun '(regs, sub) eq =>
              match eq with
              | EqFby x ck c0 e xr =>
                let xr := PSP.of_list (List.map fst xr) in
                match List.find
                        (fun '(x, ck', c0', e', xr') =>
                           (ck' ==b ck) && (c0' ==b c0) && (e' ==b e) && PS.equal xr' xr) regs
                with
                | Some (x', _, _, _ , _) => (regs, Env.add x x' sub)
                | None => ((x, ck, c0, e, xr)::regs, sub)
                end
              | _ => (regs, sub)
              end) eqs ([], Env.empty _)).

  Section rename.
    Variable (sub : Env.t ident).

    Definition rename_in_var (x : ident) :=
      match Env.find x sub with
      | Some x' => x'
      | None => x
      end.

    Fixpoint rename_in_clock (ck : clock) :=
      match ck with
      | Cbase => Cbase
      | Con ck' x t => Con (rename_in_clock ck') (rename_in_var x) t
      end.

    Fixpoint rename_in_exp (e : exp) :=
      match e with
      | Econst _ | Eenum _ _ => e
      | Evar x ty => Evar (rename_in_var x) ty
      | Ewhen e x t => Ewhen (rename_in_exp e) (rename_in_var x) t
      | Eunop op e1 ty => Eunop op (rename_in_exp e1) ty
      | Ebinop op e1 e2 ty => Ebinop op (rename_in_exp e1) (rename_in_exp e2) ty
      end.

    Fixpoint rename_in_cexp (e : cexp) :=
      match e with
      | Emerge (x, te) ces ty =>
        Emerge (rename_in_var x, te) (List.map rename_in_cexp ces) ty
      | Ecase e ces d =>
        Ecase (rename_in_exp e) (map (option_map rename_in_cexp) ces) (rename_in_cexp d)
      | Eexp e => Eexp (rename_in_exp e)
      end.

    Definition rename_in_reset :=
      map (fun '(xr, ckr) => (rename_in_var xr, rename_in_clock ckr)).

    Definition rename_in_equation (equ : equation) :=
      match equ with
      | EqDef x ck ce => EqDef x (rename_in_clock ck) (rename_in_cexp ce)
      | EqApp xs ck f es xr =>
        EqApp xs (rename_in_clock ck) f (map rename_in_exp es) (rename_in_reset xr)
      | EqFby x ck c0 e xr =>
        EqFby x (rename_in_clock ck) c0 (rename_in_exp e) (rename_in_reset xr)
      end.

    Definition subst_and_filter_vars (vars : list (ident * (type * clock))) :=
      let vars' := List.filter (fun '(x, _) => negb (Env.mem x sub)) vars in
      List.map (fun '(x, (ty, ck)) => (x, (ty, rename_in_clock ck))) vars'.

    Definition subst_and_filter_equations (eqs : list equation) :=
      let eqs' := List.filter (fun eq => match eq with
                                      | EqFby x _ _ _ _ => negb (Env.mem x sub)
                                      | _ => true
                                      end) eqs in
      List.map rename_in_equation eqs'.

  End rename.

  Definition remove_dup_regs_eqs_once (vars : list (ident * (type * clock))) (eqs : list equation) :=
    let sub' := find_duplicates eqs in
    (subst_and_filter_vars sub' vars, subst_and_filter_equations sub' eqs).

  Function remove_dup_regs_eqs (vars : list (ident * (type * clock))) (eqs : list equation) {measure length eqs} :=
    let (vars', eqs') := remove_dup_regs_eqs_once vars eqs in
    if (length eqs') <? (length eqs)
    then remove_dup_regs_eqs vars' eqs'
    else (vars, eqs).
  Proof.
    intros ????? Hlen.
    apply Nat.ltb_lt in Hlen; auto.
  Defined.

  (** ** Properties *)

  Lemma rename_in_exp_typeof : forall sub e,
      typeof (rename_in_exp sub e) = typeof e.
  Proof.
    induction e; intros; simpl; auto.
  Qed.

  Lemma rename_in_cexp_typeofc : forall sub e,
      typeofc (rename_in_cexp sub e) = typeofc e.
  Proof.
    induction e; intros; simpl; auto using rename_in_exp_typeof.
    destruct p; auto.
  Qed.

  Lemma subst_and_filter_vars_InMembers : forall x sub vars,
      InMembers x (subst_and_filter_vars sub vars) ->
      InMembers x vars.
  Proof.
    induction vars as [|(?&?&?)]; intros Hin; simpl in *; auto.
    unfold subst_and_filter_vars in Hin; simpl in Hin.
    destruct (negb _); simpl; auto.
    inv Hin; auto.
  Qed.

  Lemma subst_and_filter_vars_NoDupMembers : forall sub vars,
      NoDupMembers vars ->
      NoDupMembers (subst_and_filter_vars sub vars).
  Proof.
    induction vars as [|(?&?&?)]; intros Hnd; inv Hnd; simpl in *; auto.
    - constructor.
    - unfold subst_and_filter_vars; simpl.
      destruct (negb _); simpl; auto.
      constructor; auto.
      contradict H1; eauto using subst_and_filter_vars_InMembers.
  Qed.

  Lemma remove_dup_regs_eqs_fby_incl : forall sub eqs,
      incl (vars_defined (filter is_fby (snd (remove_dup_regs_eqs sub eqs))))
           (vars_defined (filter is_fby eqs)).
  Proof.
    intros.
    functional induction (remove_dup_regs_eqs sub eqs).
    - etransitivity; eauto.
      clear - e. inv e.
      generalize (find_duplicates eqs) as sub'; intros.
      induction eqs as [|[| |] ?]; simpl; auto using List.incl_refl.
      unfold subst_and_filter_equations in *; simpl.
      destruct (Env.mem i sub'); simpl; auto using incl_tl, incl_tl'.
    - reflexivity.
  Qed.

  Lemma find_duplicates_spec : forall x y eqs,
      Env.find x (find_duplicates eqs) = Some y ->
      exists ck c e xr1 xr2,
        In (EqFby x ck c e xr1) eqs /\
        In (EqFby y ck c e xr2) eqs /\
        PS.Equal (PSP.of_list (map fst xr1)) (PSP.of_list (map fst xr2)).
  Proof.
    unfold find_duplicates.
    intros *.
    setoid_rewrite (in_rev eqs).
    rewrite <-fold_left_rev_right.
    generalize (rev eqs); clear eqs; intros eqs.
    remember (fold_right _ _ _) as find_duplicates.
    assert ((forall x ck c0 e xr, In (x, ck, c0, e, xr) (fst find_duplicates) ->
                          exists xr', In (EqFby x ck c0 e xr') eqs /\ PS.Equal (PSP.of_list (map fst xr')) xr) /\
            (Env.find x (snd find_duplicates) = Some y ->
             exists (ck : clock) (c : const) (e : exp) (xr1 xr2 : list (ident * clock)),
               In (EqFby x ck c e xr1) eqs /\
               In (EqFby y ck c e xr2) eqs /\ PS.Equal (PSP.of_list (map fst xr1)) (PSP.of_list (map fst xr2)))
           ) as (?&?); auto.
    subst.
    induction eqs as [|[| |]]; intros *; (split; [intros * Hin|intros * Hfind]); simpl in *;
      try destruct IHeqs as (IHeqs1&IHeqs2).
    - inv Hin.
    - rewrite Env.gempty in Hfind; congruence.
    - destruct (fold_right _ _) eqn:Hfold.
      eapply IHeqs1 in Hin as (?&?&?); eauto.
    - destruct (fold_right _ _) eqn:Hfold.
      eapply IHeqs2 in Hfind as (?&?&?&?&?&?&?&?); eauto 11.
    - destruct (fold_right _ _) eqn:Hfold.
      eapply IHeqs1 in Hin as (?&?&?); eauto.
    - destruct (fold_right _ _) eqn:Hfold.
      eapply IHeqs2 in Hfind as (?&?&?&?&?&?&?&?); eauto 11.
    - destruct (fold_right _ _) eqn:Hfold.
      destruct (find _ _) as [((((?&?)&?)&?)&?)|]; simpl in *.
      2:destruct Hin as [Hin|Hin].
      1,3:eapply IHeqs1 in Hin as (?&?&?); eauto.
      inv Hin. do 1 eexists. split; eauto. reflexivity.
    - destruct (fold_right _ _) eqn:Hfold.
      destruct (find _ _) as [((((?&?)&?)&?)&?)|] eqn:Hfind'; simpl in *.
      destruct (ident_eq_dec x i); subst.
      2:rewrite Env.gso in Hfind; auto.
      2,3:(eapply IHeqs2 in Hfind as (?&?&?&?&?&?&?&?); eauto 11).
      rewrite Env.gss in Hfind; inv Hfind.
      eapply find_some in Hfind' as (Hin&?).
      eapply IHeqs1 in Hin as (?&Hin&Heq).
      repeat rewrite Bool.andb_true_iff in H. destruct H as (((Heq1&Heq2)&Heq3)&Heq4).
      rewrite equiv_decb_equiv in Heq1; inv Heq1.
      rewrite equiv_decb_equiv in Heq2; inv Heq2.
      rewrite equiv_decb_equiv in Heq3; inv Heq3.
      apply PSF.equal_2 in Heq4.
      do 7 (eexists; eauto).
      symmetry. etransitivity; eauto.
  Qed.

  Corollary find_duplicates_In : forall x eqs,
      Env.In x (find_duplicates eqs) ->
      In x (vars_defined eqs).
  Proof.
    intros * Hin.
    eapply Env.In_find in Hin as (?&Hfind).
    eapply find_duplicates_spec in Hfind as (?&?&?&?&?&?&_).
    eapply in_flat_map. do 2 (eexists; eauto). simpl; auto.
  Qed.

  Import Permutation.

  Lemma find_duplicates_irrefl: forall x y eqs,
      NoDup (vars_defined eqs) ->
      Env.find x (find_duplicates eqs) = Some y ->
      ~Env.In y (find_duplicates eqs).
  Proof.
    unfold find_duplicates.
    intros * Hnd.
    assert (NoDup (vars_defined (rev eqs))) as Hnd'.
    { eapply Permutation_NoDup; [|eauto].
      eapply Permutation_flat_map_Proper, Permutation_rev. }
    clear Hnd. revert Hnd' y.
    rewrite <-fold_left_rev_right.
    generalize (rev eqs); clear eqs; intros eqs Hnd.
    remember (fold_right _ _ _) as find_duplicates.
    assert ((forall x ck c0 e xr, In (x, ck, c0, e, xr) (fst find_duplicates) -> ~Env.In x (snd find_duplicates) /\ In x (vars_defined eqs)) /\
            (forall y, Env.find x (snd find_duplicates) = Some y ->
                  ~ Env.In y (snd find_duplicates) /\
                  In x (vars_defined eqs) /\ In y (vars_defined eqs))) as (_&?).
    2:intros; apply H; auto.
    revert x Hnd; subst.
    induction eqs as [|[| |]]; intros x Hnd; (split; [intros * Hin|intros * Hfind]); simpl in *.
    - inv Hin.
    - rewrite Env.gempty in Hfind; congruence.
    - inv Hnd. destruct (fold_right _ _) eqn:Hfold.
      eapply IHeqs in Hin as (?&?); eauto.
    - inv Hnd. destruct (fold_right _ _) eqn:Hfold.
      apply IHeqs in Hfind as (?&?&?); auto.
    - apply NoDup_app_r in Hnd.
      destruct (fold_right _ _) eqn:Hfold.
      rewrite in_app_iff.
      eapply IHeqs in Hin as (?&?); eauto.
    - apply NoDup_app_r in Hnd.
      destruct (fold_right _ _) eqn:Hfold.
      repeat rewrite in_app_iff.
      apply IHeqs in Hfind as (?&?&?); auto.
    - inv Hnd. destruct (fold_right _ _) eqn:Hfold.
      destruct (find _ _) as [((((?&?)&?)&?)&?)|] eqn:Hfind'; simpl in *.
      rewrite Env.Props.P.F.add_in_iff, not_or'; split.
      3:destruct Hin as [?|Hin]. 3:inv H; split; auto.
      1,2,4:eapply IHeqs in Hin as (?&?); eauto.
      + split; auto.
        intro contra; subst. congruence.
      + intro contra. eapply Env.In_find in contra as (?&contra).
        unfold Env.MapsTo in contra.
        eapply IHeqs in contra as (?&?&?); eauto.
    - inv Hnd. destruct (fold_right _ _) eqn:Hfold.
      destruct (find _ _) as [((((?&?)&?)&?)&?)|] eqn:Hfind'; simpl in *.
      destruct (ident_eq_dec x i); subst.
      3:apply IHeqs in Hfind as (?&?&?); auto.
      1,2:rewrite Env.Props.P.F.add_in_iff, not_or'.
      + rewrite Env.gss in Hfind; inv Hfind.
        eapply find_some in Hfind' as (Hin&_).
        eapply IHeqs in Hin as (?&?); eauto. repeat split; auto.
        intro contra; subst. congruence.
      + rewrite Env.gso in Hfind; auto.
        eapply IHeqs in Hfind as (?&?&?); eauto.
        repeat split; auto.
        intro; subst. congruence.
  Qed.

  Lemma subst_and_filter_equations_incl : forall sub eqs,
      incl (vars_defined (subst_and_filter_equations sub eqs))
           (vars_defined eqs).
  Proof.
    induction eqs as [|[| |]]; intros ? Hin; simpl in *; auto.
    - inv Hin; auto.
    - rewrite in_app_iff in *. inv Hin; auto.
    - unfold subst_and_filter_equations in Hin; simpl in Hin.
      destruct (negb _); simpl in *; auto. inv Hin; auto.
  Qed.

  Lemma subst_and_filter_equations_NoDup : forall sub eqs,
      NoDup (vars_defined eqs) ->
      NoDup (vars_defined (subst_and_filter_equations sub eqs)).
  Proof.
    induction eqs as [|[| |]]; intros Hnd; simpl in *; auto.
    - inv Hnd. constructor; auto.
      contradict H1. apply subst_and_filter_equations_incl in H1; auto.
    - rewrite NoDup_app'_iff in *. destruct Hnd as (?&?&?).
      repeat split; auto.
      eapply Forall_impl; eauto. intros.
      contradict H2.
      apply subst_and_filter_equations_incl in H2; auto.
    - inv Hnd.
      unfold subst_and_filter_equations; simpl.
      destruct (negb _); simpl; auto.
      constructor; auto.
      contradict H1.
      apply subst_and_filter_equations_incl in H1; auto.
  Qed.

  (** *** vars_defined *)

  Lemma find_duplicates_is_fby : forall x eqs,
      NoDup (vars_defined eqs) ->
      Env.In x (find_duplicates eqs) ->
      forall eq, In eq eqs ->
            In x (var_defined eq) ->
            is_fby eq = true.
  Proof.
    unfold find_duplicates. intros * Hnd Henvin.
    rewrite <-fold_left_rev_right in Henvin.
    assert (NoDup (vars_defined (rev eqs))) as Hnd'.
    { unfold vars_defined. rewrite <-Permutation_rev; auto. }
    setoid_rewrite (in_rev eqs).
    clear Hnd. revert Hnd' Henvin. generalize (rev eqs) as eqs'. clear eqs.
    intros eqs.
    induction eqs as [|[| |]]; intros * Hnd Hinsub ? Hineq Hin; simpl in *.
    - exfalso. apply Env.Props.P.F.empty_in_iff in Hinsub; auto.
    - destruct (fold_right _ _ _) eqn:Hfold.
      inv Hnd. destruct Hineq; subst; simpl in *; auto.
      destruct Hin; auto; subst.
      exfalso. eapply H1.
      { clear - Hfold Hinsub.
        revert l t Hinsub Hfold.
        induction eqs as [|[| |]]; intros; simpl in *.
        - inv Hfold. apply Env.Props.P.F.empty_in_iff in Hinsub; auto.
        - destruct (fold_right _ _ _) eqn:Hfold'; inv Hfold; eauto.
        - destruct (fold_right _ _ _) eqn:Hfold'; inv Hfold; eauto.
          apply in_or_app; eauto.
        - destruct (fold_right _ _ _) eqn:Hfold'.
          destruct (find _ _) as [((((?&?)&?)&?)&?)|]; inv Hfold; simpl in *; eauto.
          apply Env.Props.P.F.add_in_iff in Hinsub as [?|Hinsub]; eauto.
      }
    - destruct (fold_right _ _ _) eqn:Hfold.
      destruct Hineq; subst; simpl in *; eauto using NoDup_app_r.
      eapply NoDup_app_In in Hnd; eauto.
      exfalso. eapply Hnd.
      { clear - Hfold Hinsub.
        revert l2 t Hinsub Hfold.
        induction eqs as [|[| |]]; intros; simpl in *.
        - inv Hfold. apply Env.Props.P.F.empty_in_iff in Hinsub; auto.
        - destruct (fold_right _ _ _) eqn:Hfold'; inv Hfold; eauto.
        - destruct (fold_right _ _ _) eqn:Hfold'; inv Hfold; eauto.
          apply in_or_app; eauto.
        - destruct (fold_right _ _ _) eqn:Hfold'.
          destruct (find _ _) as [((((?&?)&?)&?)&?)|]; inv Hfold; simpl in *; eauto.
          apply Env.Props.P.F.add_in_iff in Hinsub as [?|Hinsub]; eauto.
      }
    - inv Hnd.
      destruct (fold_right _ _ _) eqn:Hfold.
      destruct (find _ _) as [((((?&?)&?)&?)&?)|]; simpl in *.
      + apply Env.Props.P.F.add_in_iff in Hinsub as [?|Hinsub]; subst.
        * destruct Hineq; subst; simpl in Hin; auto.
          exfalso. apply H1.
          unfold vars_defined. apply in_flat_map; eauto.
        * destruct Hineq; subst; simpl in Hin; auto.
      + destruct Hineq; subst; auto.
  Qed.

  Corollary find_duplicates_Forall_is_fby : forall eqs,
      NoDup (vars_defined eqs) ->
      Forall (fun eq => forall x, Env.In x (find_duplicates eqs) -> In x (var_defined eq) -> is_fby eq = true) eqs.
  Proof.
    intros.
    eapply Forall_forall; intros.
    eapply find_duplicates_is_fby; eauto.
  Qed.

  Lemma subst_and_filter_equations_vars_defined : forall sub eqs,
      Forall (fun eq => forall x, Env.In x sub -> In x (var_defined eq) -> is_fby eq = true) eqs ->
      vars_defined (subst_and_filter_equations sub eqs) =
      filter (fun k => negb (Env.mem k sub)) (vars_defined eqs).
  Proof.
    induction eqs as [|[| |]]; intros Hf; inv Hf; simpl; auto.
    2:rewrite <-filter_app.
    1-3:rewrite <-IHeqs; eauto.
    - destruct (Env.mem _ _) eqn:Hmem; simpl; auto.
      exfalso. apply Env.mem_2, H1 in Hmem; simpl; auto.
      inv Hmem.
    - replace (filter (fun k => negb (Env.mem k sub)) l) with l; auto.
      assert (Forall (fun x => ~Env.In x sub) l) as Hnin.
      { clear - H1. apply Forall_forall; intros ?? contra.
        apply H1 in contra; simpl in *; try congruence. }
      clear -Hnin.
      induction Hnin; simpl; auto.
      apply Env.Props.P.F.not_mem_in_iff in H. rewrite H, <-IHHnin; auto.
    - unfold subst_and_filter_equations; simpl.
      destruct (negb _); simpl; auto.
  Qed.

  Lemma subst_and_filter_equations_Perm : forall sub eqs outs vars,
      Forall (fun x => ~Env.In x sub) outs ->
      Forall (fun eq => forall x, Env.In x sub -> In x (var_defined eq) -> is_fby eq = true) eqs ->
      Permutation (vars_defined eqs) (map fst vars ++ outs) ->
      Permutation (vars_defined (subst_and_filter_equations sub eqs))
                  (map fst (subst_and_filter_vars sub vars) ++ outs).
  Proof.
    intros * Hnouts Hisfby.
    unfold subst_and_filter_vars.
    rewrite map_map; simpl. rewrite map_ext with (g:=fst) (l:=filter _ _).
    2:(intros (?&?&?); auto).
    replace (map fst (filter (fun '(k, _) => negb (Env.mem k sub)) vars))
            with (filter (fun k => negb (Env.mem k sub)) (map fst vars)).
    2:{ clear - vars. induction vars as [|(?&?)]; simpl; auto.
        destruct (negb _); simpl; auto. }
    generalize (map fst vars); clear vars; intros vars.
    replace (filter (fun k => negb (Env.mem k sub)) vars ++ outs)
      with (filter (fun k => negb (Env.mem k sub)) (vars ++ outs)).
    2:{ rewrite <-filter_app. f_equal; auto.
        induction Hnouts; simpl; auto.
        apply Env.Props.P.F.not_mem_in_iff in H. rewrite H; simpl.
        f_equal; auto. }
    generalize (vars ++ outs); clear vars outs Hnouts.
    intros. rewrite subst_and_filter_equations_vars_defined; auto.
    rewrite H; auto.
  Qed.

  Lemma remove_dup_regs_eqs_Perm : forall vars eqs outs,
      NoDup (vars_defined eqs) ->
      Forall (fun x => ~In x (vars_defined (filter is_fby eqs))) outs ->
      Permutation (vars_defined eqs) (map fst vars ++ outs) ->
      Permutation (vars_defined (snd (remove_dup_regs_eqs vars eqs)))
                  (map fst (fst (remove_dup_regs_eqs vars eqs)) ++ outs).
  Proof.
    intros *.
    functional induction (remove_dup_regs_eqs vars eqs); simpl; intros * Hnd Houts Hperm; auto.
    apply IHp; auto.
    - inv e.
      rewrite subst_and_filter_equations_vars_defined; auto using nodup_filter.
      eapply find_duplicates_Forall_is_fby; eauto.
    - eapply Forall_impl; eauto.
      intros ??; simpl in *.
      contradict H. clear - H e. inv e.
      revert H. generalize (find_duplicates eqs). intros.
      induction eqs as [|[| |]]; simpl in *; auto.
      unfold subst_and_filter_equations in H; simpl in H.
      destruct (Env.mem _ _); simpl in *; auto.
      destruct H; auto.
    - clear - Hnd Houts Hperm e. inv e.
      apply subst_and_filter_equations_Perm; auto.
      + eapply Forall_impl; eauto; intros; simpl in *.
        intro contra.
        assert (Hin:=contra). eapply find_duplicates_In in Hin.
        eapply in_flat_map in Hin as (?&?&?).
        eapply find_duplicates_is_fby in contra; eauto.
        eapply H, in_flat_map. repeat esplit; eauto.
        eapply filter_In; eauto.
      + eapply find_duplicates_Forall_is_fby; eauto.
  Qed.

  Lemma remove_dup_regs_eqs_vars_InMembers : forall x vars eqs,
      InMembers x (fst (remove_dup_regs_eqs vars eqs)) ->
      InMembers x vars.
  Proof.
    intros *.
    functional induction (remove_dup_regs_eqs vars eqs); intros; auto.
    apply IHp in H; auto.
    inv e. clear -H.
    induction vars as [|(?&?&?)]; simpl in *; auto.
    unfold subst_and_filter_vars in *; simpl in *.
    destruct (negb _); auto.
    inv H; simpl; auto.
  Qed.

  Lemma remove_dup_regs_eqs_vars_NoDupMembers : forall vars eqs,
      NoDupMembers vars ->
      NoDupMembers (fst (remove_dup_regs_eqs vars eqs)).
  Proof.
    intros *.
    functional induction (remove_dup_regs_eqs vars eqs); intros; auto.
    apply IHp.
    inv e. clear -H.
    induction vars as [|(?&?&?)]; inv H; simpl; try constructor.
    unfold subst_and_filter_vars; simpl.
    destruct (negb _); auto.
    constructor; auto.
    contradict H2. clear - H2.
    induction vars as [|(?&?&?)]; simpl in *. inv H2.
    destruct (negb _); auto.
    inv H2; auto.
  Qed.

  (** ** Transformation of the node and global *)

  Definition remove_dup_regs_eqs' vars eqs:
    { res | remove_dup_regs_eqs vars eqs = res }.
  Proof.
    econstructor. reflexivity.
  Defined.

  Program Definition remove_dup_regs_node (n : node) : node :=
    let res := remove_dup_regs_eqs' n.(n_vars) n.(n_eqs) in
    {| n_name := n.(n_name);
       n_in := n.(n_in);
       n_out := n.(n_out);
       n_vars := fst (proj1_sig res);
       n_eqs := snd (proj1_sig res)
    |}.
  Next Obligation. exact n.(n_ingt0). Qed.
  Next Obligation. exact n.(n_outgt0). Qed.
  Next Obligation.
    specialize (n_defd n) as Hdef.
    specialize (n_vout n) as Hnout.
    specialize (n_nodup n) as Hndup.
    rewrite map_app.
    apply remove_dup_regs_eqs_Perm; auto.
    + apply NoDup_var_defined_n_eqs.
    + apply Forall_forall; intros; eauto.
    + rewrite <-map_app; auto.
  Qed.
  Next Obligation.
    intro contra.
    eapply n_vout; eauto.
    eapply remove_dup_regs_eqs_fby_incl; eauto.
  Qed.
  Next Obligation.
    specialize (n_nodup n) as Hnd.
    repeat apply NoDupMembers_app.
    - apply NoDupMembers_app_l in Hnd; auto.
    - apply remove_dup_regs_eqs_vars_NoDupMembers; auto.
      apply NoDupMembers_app_r, NoDupMembers_app_l in Hnd; auto.
    - apply NoDupMembers_app_r, NoDupMembers_app_r in Hnd; auto.
    - intros ? Hin.
      intros Hout.
      eapply NoDupMembers_app_r, NoDupMembers_app_InMembers in Hnd; eauto.
      apply remove_dup_regs_eqs_vars_InMembers in Hin; auto.
    - intros ? Hin.
      eapply NoDupMembers_app_InMembers in Hnd; eauto.
      rewrite InMembers_app in *.
      contradict Hnd. destruct Hnd; auto.
      left. apply remove_dup_regs_eqs_vars_InMembers in H; auto.
  Qed.
  Next Obligation.
    specialize (n_good n) as Hgood.
    repeat rewrite map_app, Forall_app in *.
    destruct Hgood as ((Hin&Hvar&Hout)&Hname).
    repeat (split; auto).
    clear - Hvar.
    eapply Forall_forall; intros.
    apply fst_InMembers, remove_dup_regs_eqs_vars_InMembers, fst_InMembers in H.
    eapply Forall_forall in Hvar; eauto.
  Qed.

  Local Program Instance remove_dup_regs_node_transform_unit: TransformUnit node node :=
    { transform_unit := remove_dup_regs_node }.

  Local Program Instance remove_dup_regs_without_units: TransformProgramWithoutUnits global global :=
    { transform_program_without_units := fun g => Global g.(enums) [] }.

  Definition remove_dup_regs : global -> global := transform_units.

  (** *** Some properties *)

  Lemma find_node_remove_dup_regs_forward : forall G f n,
      find_node f G = Some n ->
      find_node f (remove_dup_regs G) = Some (remove_dup_regs_node n).
  Proof.
    unfold remove_dup_regs, find_node.
    intros * Hfind.
    apply option_map_inv in Hfind as ((?&?)&Hfind&?); subst.
    apply find_unit_transform_units_forward in Hfind.
    rewrite Hfind; auto.
  Qed.

  Lemma find_node_remove_dup_regs_backward : forall G f n,
      find_node f (remove_dup_regs G) = Some n ->
      exists n0, find_node f G = Some n0 /\ n = remove_dup_regs_node n0.
  Proof.
    unfold remove_dup_regs, find_node.
    intros * Hfind.
    apply option_map_inv in Hfind as ((?&?)&Hfind&?); subst.
    apply find_unit_transform_units_backward in Hfind as (?&?&Hfind&?&?); subst.
    exists x. repeat split; auto.
    rewrite Hfind; auto.
  Qed.

  Lemma remove_dup_regs_iface_eq : forall G,
      global_iface_eq G (remove_dup_regs G).
  Proof.
    intros. split; intros; auto.
    destruct (find_node _ _) eqn:Hfind.
    - erewrite find_node_remove_dup_regs_forward; eauto.
      constructor; simpl.
      repeat (split; auto).
    - destruct (find_node f (remove_dup_regs _)) eqn:Hfind'; try constructor.
      exfalso.
      apply find_node_remove_dup_regs_backward in Hfind' as (?&?&_); congruence.
  Qed.

End DRR.

Module DRRFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX   Ids Op)
       (Cks   : CLOCKS      Ids Op OpAux)
       (CESyn : CESYNTAX    Ids Op OpAux Cks)
       (Syn   : NLSYNTAX    Ids Op OpAux Cks CESyn)
<: DRR Ids Op OpAux Cks CESyn Syn.
  Include DRR Ids Op OpAux Cks CESyn Syn.
End DRRFun.
