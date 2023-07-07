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
(** TODO this whole pass could be rewritten to integrate the transformation of fbys into last

    Schema:
    x = c0 fby e; becomes

    last lx = c0;
    x = last lx;
    nx = e;

    Introduce only one lx for several registers with the same fby form.
    No more renaming anywhere ! Just a lot of useless copies (can x then be inlined ?)
 *)

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
    repeat decide equality.
    apply cconst_dec.
  Defined.

  Definition exp_dec : forall (e1 e2 : exp),
    { e1 = e2 } + { e1 <> e2 }.
  Proof.
    repeat decide equality.
    all:auto using ctype_dec, cconst_dec, unop_dec, binop_dec, Nat.eq_dec, Pos.eq_dec.
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
      | Elast x ty => Elast x ty
      | Ewhen e (x, tx) t => Ewhen (rename_in_exp e) (rename_in_var x, tx) t
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

    Definition rename_in_rhs (e : rhs) :=
      match e with
      | Eextcall f es ty => Eextcall f (map rename_in_exp es) ty
      | Ecexp e => Ecexp (rename_in_cexp e)
      end.

    Definition rename_in_reset :=
      map (fun '(xr, ckr) => (rename_in_var xr, rename_in_clock ckr)).

    Definition rename_in_equation (equ : equation) :=
      match equ with
      | EqDef x ck ce => EqDef x (rename_in_clock ck) (rename_in_rhs ce)
      | EqLast x ty ck c0 xr =>
        EqLast x ty (rename_in_clock ck) c0 (rename_in_reset xr)
      | EqApp xs ck f es xr =>
        EqApp xs (rename_in_clock ck) f (map rename_in_exp es) (rename_in_reset xr)
      | EqFby x ck c0 e xr =>
        EqFby x (rename_in_clock ck) c0 (rename_in_exp e) (rename_in_reset xr)
      end.

    Definition subst_and_filter_vars (vars : list (ident * (type * clock * bool))) :=
      let vars' := List.filter (fun '(x, _) => negb (Env.mem x sub)) vars in
      List.map (fun '(x, (ty, ck, islast)) => (x, (ty, rename_in_clock ck, islast))) vars'.

    Definition subst_and_filter_equations (eqs : list equation) :=
      let eqs' := List.filter (fun eq => match eq with
                                      | EqFby x _ _ _ _ => negb (Env.mem x sub)
                                      | _ => true
                                      end) eqs in
      List.map rename_in_equation eqs'.

  End rename.

  Definition remove_dup_regs_eqs_once (vars : list (ident * (type * clock * bool))) (eqs : list equation) :=
    let sub' := find_duplicates eqs in
    (subst_and_filter_vars sub' vars, subst_and_filter_equations sub' eqs).

  Function remove_dup_regs_eqs (vars : list (ident * (type * clock * bool))) (eqs : list equation) {measure length eqs} :=
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
    induction e; destruct_conjs; intros; simpl; auto.
  Qed.

  Lemma rename_in_cexp_typeofc : forall sub e,
      typeofc (rename_in_cexp sub e) = typeofc e.
  Proof.
    induction e; intros; simpl; auto using rename_in_exp_typeof.
    destruct p; auto.
  Qed.

  Lemma rename_in_rhs_typeofr : forall sub e,
      typeofr (rename_in_rhs sub e) = typeofr e.
  Proof.
    intros ? []; simpl; auto using rename_in_cexp_typeofc.
  Qed.

  Lemma subst_and_filter_vars_InMembers : forall x sub vars,
      InMembers x (subst_and_filter_vars sub vars) ->
      InMembers x vars.
  Proof.
    induction vars as [|(?&?&?)]; intros Hin; simpl in *; auto.
    unfold subst_and_filter_vars in Hin; simpl in Hin.
    simpl_In.
    destruct (negb _); simpl; auto. 2:right; solve_In.
    inv Hin; [inv H; left|right]; auto. solve_In.
  Qed.

  Lemma subst_and_filter_vars_NoDupMembers : forall sub vars,
      NoDupMembers vars ->
      NoDupMembers (subst_and_filter_vars sub vars).
  Proof.
    induction vars as [|(?&(?&?)&?)]; intros Hnd; inv Hnd; simpl in *; auto.
    - constructor.
    - unfold subst_and_filter_vars; simpl.
      destruct (negb _); simpl; auto.
      constructor; auto.
      contradict H1; eauto using subst_and_filter_vars_InMembers.
  Qed.

  Lemma remove_dup_regs_eqs_once_fby_incl : forall vars eqs,
      incl (vars_defined (filter is_fby (snd (remove_dup_regs_eqs_once vars eqs))))
           (vars_defined (filter is_fby eqs)).
  Proof.
    intros. simpl.
    generalize (find_duplicates eqs) as vars'; intros.
    induction eqs as [|[| | |] ?]; simpl; auto using List.incl_refl.
    unfold subst_and_filter_equations in *; simpl.
    destruct (Env.mem i vars'); simpl; auto using incl_tl, incl_tl'.
  Qed.

  Lemma remove_dup_regs_eqs_fby_incl : forall vars eqs,
      incl (vars_defined (filter is_fby (snd (remove_dup_regs_eqs vars eqs))))
           (vars_defined (filter is_fby eqs)).
  Proof.
    intros.
    functional induction (remove_dup_regs_eqs vars eqs).
    - etransitivity; eauto.
      clear - e. inv e.
      eapply remove_dup_regs_eqs_once_fby_incl with (vars:=vars).
    - reflexivity.
  Qed.

  Lemma remove_dup_regs_eqs_once_def_cexp : forall vars eqs,
      vars_defined (filter is_def_cexp (snd (remove_dup_regs_eqs_once vars eqs)))
      = vars_defined (filter is_def_cexp eqs).
  Proof.
    intros. simpl.
    generalize (find_duplicates eqs) as vars'; intros.
    unfold subst_and_filter_equations in *; simpl.
    induction eqs as [|[| | |] ?]; simpl; auto.
    - destruct r; simpl; auto.
    - cases; auto.
  Qed.

  Lemma remove_dup_regs_eqs_def_cexp : forall vars eqs,
      vars_defined (filter is_def_cexp (snd (remove_dup_regs_eqs vars eqs)))
      = vars_defined (filter is_def_cexp eqs).
  Proof.
    intros.
    functional induction (remove_dup_regs_eqs vars eqs).
    - rewrite IHp.
      clear - e. inv e.
      apply remove_dup_regs_eqs_once_def_cexp with (vars:=vars).
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
    induction eqs as [|[| | |]]; intros *; (split; [intros * Hin|intros * Hfind]); simpl in *;
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
      In x (vars_defined (filter is_fby eqs)).
  Proof.
    intros * Hin.
    eapply Env.In_find in Hin as (?&Hfind).
    eapply find_duplicates_spec in Hfind as (?&?&?&?&?&?&_).
    unfold vars_defined. solve_In. simpl; auto.
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
    induction eqs as [|[| | |]]; intros x Hnd; (split; [intros * Hin|intros * Hfind]); simpl in *.
    - inv Hin.
    - rewrite Env.gempty in Hfind; congruence.
    - inv Hnd. destruct (fold_right _ _) eqn:Hfold.
      eapply IHeqs in Hin as (?&?); eauto.
    - inv Hnd. destruct (fold_right _ _) eqn:Hfold.
      apply IHeqs in Hfind as (?&?&?); auto.
    - destruct (fold_right _ _) eqn:Hfold.
      eapply IHeqs in Hin as (?&?); eauto.
    - destruct (fold_right _ _) eqn:Hfold.
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
    induction eqs as [|[| | |]]; intros ? Hin; simpl in *; auto.
    - inv Hin; auto.
    - rewrite in_app_iff in *. inv Hin; auto.
    - unfold subst_and_filter_equations in Hin; simpl in Hin.
      destruct (negb _); simpl in *; auto. inv Hin; auto.
  Qed.

  Lemma subst_and_filter_equations_NoDup : forall sub eqs,
      NoDup (vars_defined eqs) ->
      NoDup (vars_defined (subst_and_filter_equations sub eqs)).
  Proof.
    induction eqs as [|[| | |]]; intros Hnd; simpl in *; auto.
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
    induction eqs as [|]; intros * Hnd Hinsub ? Hineq Hin; simpl in *.
    - now exfalso.
    - destruct (fold_right _ _ _) eqn:Hfold.
      assert (forall x, Env.In x t -> In x (vars_defined eqs)) as In'.
      { clear - Hfold.
        revert l t Hfold.
        induction eqs as [|[| | |]]; intros; simpl in *.
        - inv Hfold. apply Env.Props.P.F.empty_in_iff in H; auto.
        - destruct (fold_right _ _ _) eqn:Hfold'; inv Hfold; eauto.
        - destruct (fold_right _ _ _) eqn:Hfold'; inv Hfold; eauto.
        - destruct (fold_right _ _ _) eqn:Hfold'; inv Hfold; eauto.
          apply in_or_app; eauto.
        - destruct (fold_right _ _ _) eqn:Hfold'.
          destruct (find _ _) as [((((?&?)&?)&?)&?)|]; inv Hfold; simpl in *; eauto.
          apply Env.Props.P.F.add_in_iff in H as [?|Hinsub]; eauto.
      }
      destruct Hineq; subst; simpl in *; auto.
      2:{ eapply IHeqs; eauto using NoDup_app_r.
          destruct a; simpl in *; auto.
          cases.
          apply Env.Props.P.F.add_in_iff in Hinsub as [|]; subst; auto.
          exfalso. inv Hnd.
          eapply H2. unfold vars_defined. solve_In. }
      clear IHeqs.
      destruct eq; simpl in *; auto; exfalso.
      + destruct Hin; auto. subst.
        inv Hnd. eauto.
      + eapply NoDup_app_In in Hnd; eauto.
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
    induction eqs as [|[| | |]]; intros Hf; inv Hf; simpl; auto.
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
    rewrite map_map, map_ext with (g:=fst) (l:=filter _ _); [|intros; destruct_conjs; auto].
    replace (map fst (filter (fun '(k, _) => negb (Env.mem k sub)) vars))
            with (filter (fun k => negb (Env.mem k sub)) (map fst vars)).
    2:{ clear - vars. induction vars as [|(?&?)]; simpl; auto.
        destruct (negb _); simpl; auto with datatypes. }
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
      induction eqs as [|[| | |]]; simpl in *; auto.
      unfold subst_and_filter_equations in H; simpl in H.
      destruct (Env.mem _ _); simpl in *; auto.
      destruct H; auto.
    - clear - Hnd Houts Hperm e. inv e.
      apply subst_and_filter_equations_Perm; auto.
      + eapply Forall_impl; eauto; intros; simpl in *.
        intro contra.
        eapply find_duplicates_In in contra.
        contradiction.
      + eapply find_duplicates_Forall_is_fby; eauto.
  Qed.

  Lemma remove_dup_regs_eqs_lasts_defined : forall vars eqs,
      lasts_defined (snd (remove_dup_regs_eqs vars eqs)) = lasts_defined eqs.
  Proof.
    intros *.
    functional induction (remove_dup_regs_eqs vars eqs); simpl; auto.
    rewrite IHp.
    inv e. unfold subst_and_filter_equations, lasts_defined.
    generalize (find_duplicates eqs) as dups; intros.
    clear - eqs. induction eqs as [|[| | |]]; simpl; auto.
    cases; simpl; auto.
  Qed.

  Lemma remove_dup_regs_eqs_lasts_Perm : forall vars eqs,
      Forall (fun '(x, (_, _, islast)) => islast = true -> ~In x (vars_defined (filter is_fby eqs))) vars ->
      Permutation (map fst (filter (fun '(_, (_, _, islast)) => islast) vars))
        (map fst (filter (fun '(_, (_, _, islast)) => islast) (fst (remove_dup_regs_eqs vars eqs)))).
  Proof.
    intros * LastsNFby.
    functional induction (remove_dup_regs_eqs vars eqs); simpl; auto.
    inv e. rewrite <-IHp; eauto using subst_and_filter_equations_NoDup.
    2:{ unfold subst_and_filter_vars. simpl_Forall. simpl_In. simpl_Forall.
        intros L In. eapply LastsNFby; eauto.
        eapply remove_dup_regs_eqs_once_fby_incl with (vars:=vars); eauto.
    }
    assert (Forall (fun '(x, (_, _, islast)) => islast = true -> ~Env.In x (find_duplicates eqs)) vars).
    { simpl_Forall. intros ? In.
      eapply LastsNFby; eauto using find_duplicates_In. }
    clear - H. unfold subst_and_filter_vars.
    induction H; destruct_conjs; simpl; auto.
    destruct b; cases_eqn Eq; auto.
    exfalso.
    eapply H; eauto using Env.mem_2.
  Qed.

  Lemma remove_dup_regs_eqs_vars_In : forall x ty ck islast vars eqs,
      In (x, (ty, ck, islast)) (fst (remove_dup_regs_eqs vars eqs)) ->
      exists ck', In (x, (ty, ck', islast)) vars.
  Proof.
    intros *.
    functional induction (remove_dup_regs_eqs vars eqs); intros; eauto.
    apply IHp in H as (?&In); eauto.
    inv e. clear -In.
    simpl_In. eauto.
  Qed.

  Lemma remove_dup_regs_eqs_vars_InMembers : forall x vars eqs,
      InMembers x (fst (remove_dup_regs_eqs vars eqs)) ->
      InMembers x vars.
  Proof.
    intros *.
    functional induction (remove_dup_regs_eqs vars eqs); intros; auto.
    apply IHp in H; auto.
    inv e. clear -H.
    simpl_In. solve_In.
  Qed.

  Lemma remove_dup_regs_eqs_vars_NoDupMembers : forall vars eqs,
      NoDupMembers vars ->
      NoDupMembers (fst (remove_dup_regs_eqs vars eqs)).
  Proof.
    intros *.
    functional induction (remove_dup_regs_eqs vars eqs); intros; auto.
    apply IHp.
    inv e. clear -H.
    induction vars as [|(?&(?&?)&?)]; inv H; simpl; try constructor.
    unfold subst_and_filter_vars; simpl.
    destruct (negb _); auto.
    constructor; auto.
    contradict H2. clear - H2.
    solve_In.
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
    apply remove_dup_regs_eqs_Perm; auto.
    + apply NoDup_var_defined_n_eqs.
    + apply Forall_forall; intros; eauto.
  Qed.
  Next Obligation.
    rewrite remove_dup_regs_eqs_lasts_defined, n_lastd1.
    apply remove_dup_regs_eqs_lasts_Perm.
    simpl_Forall. intros Eq; subst.
    eapply n_lastfby.
    rewrite n_lastd1. solve_In.
  Qed.
  Next Obligation.
    rewrite remove_dup_regs_eqs_def_cexp. simpl in *.
    eapply remove_dup_regs_eqs_vars_In in H as (?&In).
    eapply n_lastd2; eauto.
  Qed.
  Next Obligation.
    intro contra.
    eapply n_vout; eauto.
    eapply remove_dup_regs_eqs_fby_incl; eauto.
  Qed.
  Next Obligation.
    specialize (n_nodup n) as Hnd.
    repeat apply NoDup_app'; eauto using NoDup_app_l, NoDup_app_r.
    - apply fst_NoDupMembers, remove_dup_regs_eqs_vars_NoDupMembers, fst_NoDupMembers;
        eauto using NoDup_app_l, NoDup_app_r.
    - simpl_Forall.
      eapply NoDup_app_r, NoDup_app_In in Hnd; eauto.
      eapply fst_InMembers, remove_dup_regs_eqs_vars_InMembers; eauto using In_InMembers.
    - simpl_Forall.
      eapply NoDup_app_In in Hnd. 2:solve_In.
      contradict Hnd. rewrite in_app_iff, <-fst_InMembers in *. destruct Hnd; auto.
      left. eapply remove_dup_regs_eqs_vars_InMembers; eauto.
  Qed.
  Next Obligation.
    specialize (n_good n) as Hgood.
    repeat rewrite Forall_app in *.
    destruct Hgood as ((Hin&Hvar&Hout)&Hname).
    repeat (split; auto).
    clear - Hvar.
    simpl_Forall.
    apply In_InMembers, remove_dup_regs_eqs_vars_InMembers, fst_InMembers in H.
    simpl_In. simpl_Forall. auto.
  Qed.

  Local Program Instance remove_dup_regs_node_transform_unit: TransformUnit node node :=
    { transform_unit := remove_dup_regs_node }.

  Local Program Instance remove_dup_regs_without_units: TransformProgramWithoutUnits global global :=
    { transform_program_without_units := fun g => Global g.(types) g.(externs) [] }.

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
    intros. repeat split; intros; auto.
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
