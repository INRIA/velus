From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.
From Coq Require Import Permutation.
From Coq Require Import Decidable.
From Coq Require Import Omega.
From Coq Require Import Setoid Morphisms.

From compcert Require Import common.Errors.

From Velus Require Import Common Ident Clocks.
From Velus Require Import CheckGraph.
From Velus Require Import Operators Environment.
From Velus Require Import Lustre.LSyntax Lustre.LClocking Lustre.LCausality.
From Velus Require Import Lustre.Normalization.Fresh Lustre.Normalization.Normalization.

(** * Conservation of causality through normalization *)

Local Set Warnings "-masking-absolute-name".
Module Type NCAUSALITY
       (Import Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Import Syn : LSYNTAX Ids Op)
       (Import Cau : LCAUSALITY Ids Op Syn)
       (Import Clo : LCLOCKING Ids Op Syn)
       (Import Norm : NORMALIZATION Ids Op OpAux Syn Cau).

  Import Fresh Tactics.

  (** Some auxiliary stuff *)

  Fact in_vars_defined_concat : forall x eqs eqs',
      In eqs eqs' ->
      In x (vars_defined eqs) ->
      In x (vars_defined (concat eqs')).
  Proof.
    intros * Hin1 Hin2.
    unfold vars_defined in *. rewrite flat_map_concat_map in *.
    apply in_concat in Hin2 as [xs [Hin2 Hin3]].
    apply in_map_iff in Hin3 as [[xs' es] [? Hin3]]; simpl in *; subst.
    eapply incl_concat_map with (x0:=(xs, es)); simpl; auto.
    eapply in_concat'; eauto.
  Qed.

  Fact vars_defined_combine : forall xs es,
      length xs = length es ->
      vars_defined (combine xs es) = concat xs.
  Proof.
    intros * Hlen.
    unfold vars_defined. rewrite flat_map_concat_map, combine_map_fst'; auto.
  Qed.

  (** If an expression is wc with regards to an environment, all it's
      left-free vars appear in the environment *)

  Fact wc_exp_Is_free_left : forall G env e x k,
      wc_exp G env e ->
      Is_free_left x k e ->
      InMembers x env.
  Proof.
    Local Hint Resolve In_InMembers.
    Local Ltac solve_forall_exists H1 H2 H3 :=
      try eapply Is_free_left_list_Exists in H3; try destruct H3 as (?&H3);
      eapply Forall_Forall in H1; [|eapply H2];
      eapply Forall_Exists in H1; [|eapply H3];
      eapply Exists_exists in H1 as (?&?&(?&?)&?); eauto.
    induction e using exp_ind2; intros * Hwc Hfree;
      inv Hwc; inv Hfree; eauto.
    - (* binop *) destruct H1; eauto.
    - (* fby *) solve_forall_exists H H4 H3.
    - (* arrow *)
      destruct H3 as [Hex|Hex]. solve_forall_exists H H4 Hex. solve_forall_exists H0 H5 Hex.
    - (* when *)
      destruct H2 as [[? Hex]|Hex]; subst; eauto.
      solve_forall_exists H H4 Hex.
    - (* merge *)
      destruct H3 as [[? Hex]|[Hex|Hex]]; subst; eauto.
      solve_forall_exists H H5 Hex. solve_forall_exists H0 H6 Hex.
    - (* ite *)
      destruct H3 as [[? Hex]|[Hex|Hex]]; eauto.
      solve_forall_exists H H6 Hex. solve_forall_exists H0 H7 Hex.
    - (* app *) solve_forall_exists H0 H5 H10.
    - (* app (reset) *)
      destruct H13 as [Hex|Hex]; eauto. solve_forall_exists H0 H5 Hex.
  Qed.

  Definition depends_on_ck (eqs : list equation) (x : ident) (ck : clock) (y : ident) :=
    depends_on eqs x y \/ Is_free_in_clock y ck.

  Definition Is_causal_ck (eqs : list equation) (xs : list (ident * clock)) :=
    ForallTail (fun '(x, ck) xs => forall y, depends_on_ck eqs x ck y -> InMembers y xs) xs.
  Hint Unfold Is_causal_ck.
  Hint Constructors ForallTail.

  Lemma Is_causal_ck_Is_causal : forall eqs xs,
      Is_causal_ck eqs xs ->
      Is_causal eqs (map fst xs).
  Proof.
    intros * Hcaus. induction Hcaus as [|(?&?) ?]; constructor; eauto.
    intros y Hdep. setoid_rewrite <- fst_InMembers. apply H; auto.
    unfold depends_on_ck in *; auto.
  Qed.

  Lemma Is_causal_Is_causal_ck : forall eqs xs,
      Is_causal eqs (map fst xs) ->
      exists xs', Permutation xs xs' /\ Is_causal_ck eqs xs'.
  Proof.
  (* This is hard to proove, because only some of the orders accept by Is_causal will be accepted by Is_causal_ck.
     For instance, with f (x :: .) returns (c :: .; y :: . on c) consider:

     node g(x1 :: .) returns (c1 :: .; y1 : . on c1)
     let (c1, y1) = f(x1);
     tel

     We have Is_causal [c1;y1;x1] and Is_causal [y1;c1;x1]
     but only Is_causal_ck [y1;c1;x1]
   *)
  Admitted.

  (** ** Additional properties of Is_causal_ck *)

  Hint Constructors ForallTail.

  Lemma Is_causal_ck_add_eq : forall eqs eq eqs' xs,
      Is_causal_ck eqs xs ->
      Add eq eqs eqs' ->
      Forall (fun x => ~InMembers x xs) (fst eq) ->
      Is_causal_ck eqs' xs.
  Proof.
    induction xs; intros * Hcaus Hadd Heq; auto.
    destruct a as (x&ck). inv Hcaus; constructor.
    - intros y Hdep.
      unfold depends_on_ck in *. destruct Hdep as [Hdep|Hdep]; auto.
      unfold depends_on in Hdep.
      apply Exists_exists in Hdep as ((xs'&es')&Hin&Hk).
      eapply Add_in in Hin; eauto. inv Hin.
      + exfalso. destruct Hk as (k&Hlen&Hnth&_); subst.
        eapply nth_In with (d:=xH) in Hlen.
        eapply Forall_forall in Heq; [|eauto].
        apply Heq. left; auto.
      + apply H1. left. eapply Exists_exists; eauto.
    - apply IHxs; auto.
      eapply Forall_impl; [|eauto]. intros ? Hin contra.
      apply Hin. right; auto.
  Qed.

  Instance causal_ck_Proper:
    Proper (@Permutation equation ==> @eq (list _) ==> @Basics.impl)
           Is_causal_ck.
  Proof.
    intros eqs eqs' Hp ? xs ? Hcaus; subst.
    induction xs as [|(?&?) ?]; auto.
    inv Hcaus. constructor. 2:eapply IHxs; eauto.
    intros ? Hdep. apply H1.
    destruct Hdep.
    + left. unfold depends_on in *. rewrite Hp; auto.
    + right; auto.
  Qed.

  Hint Constructors Is_free_in_clock.

  Lemma Is_free_in_clock_dec : forall x ck,
      {Is_free_in_clock x ck} + {~Is_free_in_clock x ck}.
  Proof.
    induction ck.
    - right. intro contra; inv contra.
    - destruct IHck; auto.
      destruct (ident_eqb x i) eqn:Heqb.
      * rewrite ident_eqb_eq in Heqb; subst; auto.
      * rewrite ident_eqb_neq in Heqb.
        right. intro contra. inv contra; auto.
  Qed.

  Fact Is_causal_ck_Is_free_in_clock : forall eqs xs x ck,
      Is_causal_ck eqs ((x, ck)::xs) ->
      (forall y, Is_free_in_clock y ck -> InMembers y xs).
  Proof.
    intros * Hcaus y Hfree.
    inv Hcaus.
    specialize (H1 y). apply H1.
    right; auto.
  Qed.

  Corollary Is_causal_ck_Is_free_in_clock' : forall eqs xs,
      Is_causal_ck eqs xs ->
      Forall (fun '(_, ck) => forall y, Is_free_in_clock y ck -> InMembers y xs) xs.
  Proof.
    induction xs; intros * Hcaus; auto.
    destruct a as (x&ck). constructor.
    - intros. eapply Is_causal_ck_Is_free_in_clock in Hcaus; eauto.
      right; auto.
    - inv Hcaus. eapply IHxs in H2.
      eapply Forall_impl; [|eauto]. intros (?&?) ???.
      right; auto.
  Qed.

  Fact Is_causal_ck_nIs_free_in_clock : forall eqs xs x ck,
      NoDupMembers ((x, ck)::xs) ->
      Is_causal_ck eqs ((x, ck)::xs) ->
      Forall (fun '(x', ck') => ~Is_free_in_clock x ck') xs.
  Proof.
    intros * Hnd Hcaus.
    inv Hcaus. eapply Is_causal_ck_Is_free_in_clock' in H2.
    eapply Forall_impl; [|eauto]. intros (?&?) ? contra.
    eapply H in contra. inv Hnd; auto.
  Qed.

  Lemma causal_insert_early : forall eqs x xs ck,
      NoDupMembers xs ->
      wc_clock xs ck ->
      Is_causal_ck eqs xs ->
      (* x only depends on the variables of its clock (this is the case for the init equations) *)
      (forall y, depends_on_ck eqs x ck y -> Is_free_in_clock y ck) ->
      exists xs1 xs2,
          xs = xs1 ++ xs2 /\
          (* Its possible to insert x ... *)
          Is_causal_ck eqs (xs1 ++ (x, ck) :: xs2) /\
          (* So that every variable with the same clock is after it *)
          Forall (fun '(y, ck') => ck = ck' -> ~InMembers y xs2) xs.
  Proof.
    induction xs; intros * Hnd Hwc Hcaus Hdep.
    - exists []. exists []. repeat split; simpl; auto.
      constructor; auto. intros y ?.
      eapply wc_clock_is_free_in in Hwc; eauto.
    - destruct a as (x0&ck0).
      destruct (Is_free_in_clock_dec x0 ck).
      + exists []. exists ((x0, ck0)::xs). repeat split; simpl; auto.
        * constructor; auto.
          intros y Hdepon. eapply Hdep in Hdepon.
          eapply wc_clock_is_free_in; eauto.
        * constructor.
          -- intros; subst.
             eapply wc_nfree_in_clock in Hwc; eauto. left; auto.
          -- eapply Is_causal_ck_nIs_free_in_clock in Hcaus; eauto.
             eapply Forall_impl; [|eauto]. intros (?&?) ? ?; subst; auto.
      + apply wc_clock_nfreein_remove' in Hwc; eauto.
        inv Hcaus. inv Hnd.
        eapply IHxs in Hwc as (xs1&xs2&?&Hcaus'&Hfree); eauto; subst.
        exists ((x0, ck0)::xs1). exists xs2. repeat split; auto.
        * constructor; auto. intros y Hdep'.
          apply H1 in Hdep'.
          rewrite InMembers_app in *. destruct Hdep'; auto. right; right; auto.
        * constructor.
          -- intros; subst. intro contra.
             apply H3. apply InMembers_app; auto.
          -- eapply Forall_impl_In; [|eauto]. intros (?&?) ???; auto.
  Qed.

  (** ** Causality of the second phase of normalization *)

  (** *** Recover info about the init equations in the state *)

  Definition st_inits (st : fresh_st (Op.type * clock * bool)) :=
    idck (idty (filter (fun '(_, (ty, _, b)) => b && (ty ==b Op.bool_type)) (st_anns st))).

  Fact st_follows_inits_incl : forall st st',
      st_follows st st' ->
      incl (st_inits st) (st_inits st').
  Proof.
    intros * Hfollows.
    eapply st_follows_incl in Hfollows.
    unfold st_inits, idck, idty.
    apply incl_map, incl_map, incl_filter; auto.
  Qed.

  Fact st_inits_find_Some : forall st x (ck : nclock) p,
      find (fun '(_, (ty, ck', isinit)) => isinit && (ck' ==b fst ck) && (ty ==b Op.bool_type)) (st_anns st) = Some (x, p) ->
      In (x, (fst ck)) (st_inits st).
  Proof.
    intros * Hfind.
    apply find_some in Hfind as [Hin Hf].
    destruct p as [[ty ck'] isinit].
    repeat rewrite Bool.andb_true_iff in Hf. destruct Hf as [[Hty Hck] ?]; auto.
    unfold st_inits.
    rewrite In_idck_exists. exists ty.
    rewrite In_idty_exists. exists isinit.
    rewrite filter_In; split; auto.
    - rewrite clock_eqb_eq in Hck; subst. assumption.
    - rewrite Hty, H; auto.
  Qed.

  Fact st_inits_find_None : forall st (ck : nclock),
      find (fun '(_, (ty, ck', isinit)) => isinit && (ck' ==b fst ck) && (ty ==b Op.bool_type)) (st_anns st) = None ->
      ~In (fst ck) (map snd (st_inits st)).
  Proof.
    intros * Hfind.
    intro contra. unfold st_inits in contra. repeat simpl_In.
    apply filter_In in H0 as [Hin Heq].
    eapply find_none in Hfind; eauto. simpl in *.
    apply Bool.andb_true_iff in Heq as [Hb Hty]; subst; simpl in Hfind.
    rewrite Hty, equiv_decb_refl in Hfind; simpl in Hfind. congruence.
  Qed.

  Fact fresh_ident_false_st_inits : forall (st st' : fresh_st (Op.type * clock * bool)) a id,
      fresh_ident (a, false) st = (id, st') ->
      st_inits st' = st_inits st.
  Proof.
    intros * Hfresh.
    unfold st_inits. destruct a as [ty ck].
    apply fresh_ident_anns in Hfresh. rewrite Hfresh.
    simpl; auto.
  Qed.

  Fact fresh_ident_true_st_inits : forall st st' ck id,
      fresh_ident ((Op.bool_type, ck), true) st = (id, st') ->
      st_inits st' = (id, ck)::st_inits st.
  Proof.
    intros * Hfresh.
    unfold st_inits.
    apply fresh_ident_anns in Hfresh. rewrite Hfresh.
    simpl. rewrite equiv_decb_refl; auto.
  Qed.

  Fact init_var_for_clock_In_st_inits : forall ck x eqs' st st',
      init_var_for_clock ck st = (x, eqs', st') ->
      In (x, ck) (st_inits st').
  Proof.
    intros * Hinit.
    eapply init_var_for_clock_In in Hinit.
    unfold st_inits.
    simpl_In. exists Op.bool_type. simpl_In. exists true.
    rewrite filter_In. split; auto.
    rewrite equiv_decb_refl; auto.
  Qed.

  Fact add_whens_Is_free_left : forall ck ty c,
      forall x, Is_free_left x 0 (add_whens (Econst c) ty ck) ->
           Is_free_in_clock x ck.
  Proof.
    induction ck; intros * Hfree; inv Hfree; simpl in *.
    destruct H1 as [[_ ?]|?]; subst; auto.
    - inv H; eauto.
      rewrite add_whens_numstreams in H3; auto. inv H3.
  Qed.

  (** *** Small properties on the clocking of generated equations *)

  Fact init_var_for_clock_clocksof : forall ck id eqs' st st',
      init_var_for_clock ck st = (id, eqs', st') ->
      Forall (fun eq => clocksof (snd eq) = [ck]) eqs'.
  Proof.
    intros * Hinit.
    unfold init_var_for_clock in Hinit.
    destruct (find _ _); repeat inv_bind.
    - destruct p; inv Hinit; auto.
    - destruct (fresh_ident _ _); inv Hinit; auto.
  Qed.

  Fact fby_iteexp_clocksof : forall e0 e ty ck name e' eqs' st st',
      fby_iteexp e0 e (ty, (ck, name)) st = (e', eqs', st') ->
      Forall (fun eq => clocksof (snd eq) = [ck]) eqs'.
  Proof.
    intros * Hfby; simpl in *.
    repeat inv_bind; constructor; auto.
    eapply init_var_for_clock_clocksof; eauto.
  Qed.

  (** *** Causality invariant *)
  (* We have to talk about the causality over the whole set of variables
     (since we will be inserting init variables early).
     The inveriant contains several part:
     * Two general no-duplication hypothesis, respectively about the vars
       defined by equations and about the st_inits
       This is reinforced by the st_valid_after property on the state
     * A strengthened causality hypothesis : the set of variables is causal (wrt the equations generated),
       and the init variables appear before any variables on the same clock as them
   *)

  Definition st_clocks (st : fresh_st (Op.type * clock * bool)) :=
    idck (idty (st_anns st)).

  Fact st_clocks_st_ids : forall st,
      map fst (st_clocks st) = st_ids st.
  Proof.
    intros *.
    unfold st_clocks, st_ids, idty, idck.
    repeat rewrite map_map. apply map_ext.
    intros (?&(?&?)&?); auto.
  Qed.

  Fact st_inits_incl_st_clocks : forall st,
      incl (st_inits st) (st_clocks st).
  Proof.
    intros st. intros ? Hin.
    unfold st_inits, st_clocks in *.
    repeat simpl_In. exists x. simpl_In. exists x0.
    eapply in_filter; eauto.
  Qed.

  Definition causal_inv vars eqs (st : fresh_st (Op.type * clock * bool)) :=
    NoDupMembers vars /\
    NoDup (map snd (st_inits st)) /\
    st_valid_after st (PSP.of_list (map fst vars)) /\
    incl (vars_defined eqs) (map fst vars ++ st_ids st) /\
    exists xs, Permutation xs (vars ++ st_clocks st) /\
      Is_causal_ck eqs xs /\
      ForallTail (fun '(x, ck) xs => forall y, In (y, ck) (st_inits st) -> In (y, ck) ((x, ck)::xs)) xs.

  Instance causal_inv_Proper:
    Proper (@Permutation (ident * clock) ==> @Permutation equation ==> @eq (fresh_st (Op.type * clock * bool)) ==> @Basics.impl)
           causal_inv.
  Proof.
    intros ? ? Hp1 ? ? Hp2 ? ? Heq (?&?&?&?&xs&?&?&?); subst.
    repeat (split; try exists xs); auto.
    - rewrite <- Hp1; auto.
    - rewrite <- ps_from_list_ps_of_list, <- Hp1, ps_from_list_ps_of_list; auto.
    - rewrite <- Hp1, <- Hp2; auto.
    - rewrite <- Hp1; auto.
    - rewrite <- Hp2; auto.
  Qed.

  Fact Is_causal_ck_causal_inv : forall vars eqs id0,
      NoDupMembers vars ->
      Forall (fun id => (id < id0)%positive) (map fst vars) ->
      incl (vars_defined eqs) (map fst vars) ->
      (exists xs, Permutation xs vars /\ Is_causal_ck eqs xs) ->
      causal_inv vars eqs (init_st id0).
  Proof.
    intros * Hndup Hlt Hincl (xs&Hp&Hcaus).
    repeat (split; try exists xs); auto.
    1,5: unfold st_inits; rewrite init_st_anns; simpl.
    - constructor.
    - eapply ForallTail_impl; [|eauto].
      intros (?&?) ? ? ? contra. inv contra.
    - apply init_st_valid.
      rewrite <- ps_from_list_ps_of_list, PS_For_all_Forall'; auto.
    - unfold st_ids; rewrite init_st_anns, app_nil_r; auto.
    - unfold st_clocks; rewrite init_st_anns, app_nil_r; auto.
  Qed.

  Fact vars_defined_In : forall x xs es eqs,
      In (xs, es) eqs ->
      In x xs ->
      In x (vars_defined eqs).
  Proof.
    intros * Hin Hin'.
    unfold vars_defined. rewrite in_flat_map.
    exists (xs, es); auto.
  Qed.

  Fact causal_inv_insert_early : forall vars eqs x ck e st st',
      causal_inv vars eqs st ->
      wc_clock (vars++st_clocks st) ck ->
      (forall x, Is_free_left x 0 e -> Is_free_in_clock x ck) ->
      ~In ck (map snd (st_inits st)) ->
      fresh_ident (Op.bool_type, ck, true) st = (x, st') ->
      causal_inv vars (([x], [e])::eqs) st'.
  Proof.
    intros * Hcaus Hwc Hfree Hnin Hfresh.
    destruct Hcaus as (Hnd&Hnd'&Hvalid&Hincl&xs&Hperm&Hcaus&Hinits).

    assert (st_inits st' = (x, ck)::st_inits st) as Hstinit.
    { apply fresh_ident_true_st_inits; auto. }
    assert (NoDupMembers (vars ++ st_clocks st)) as Hnd''.
    { eapply Facts.st_valid_after_NoDupMembers in Hvalid; eauto.
      rewrite fst_NoDupMembers, map_app, st_clocks_st_ids; auto. }
    assert (~ InMembers x (vars ++ st_clocks st)) as Hnin'.
    { rewrite NotInMembers_app. split.
      + eapply Facts.fresh_ident_nIn in Hfresh; eauto.
        rewrite fst_InMembers, st_clocks_st_ids; auto.
      + eapply Facts.fresh_ident_nIn' in Hfresh; eauto.
        rewrite In_of_list_InMembers in Hfresh; eauto.
    }

    (* Add the equation *)
    eapply Is_causal_ck_add_eq with (eq:=(([x], [e]))) in Hcaus; eauto. 2:apply Add_head.
    2:{ simpl; constructor; auto. rewrite Hperm; auto. }

    (* Add the variable *)
    eapply causal_insert_early with (x:=x) (ck:=ck) in Hcaus as (xs1&xs2&?&Hcaus'&Hinits'); subst.
    2,3:rewrite Hperm; auto.
    - repeat constructor; eauto.
      3: exists (xs1 ++ (x, ck) :: xs2); repeat split; eauto.
      + rewrite Hstinit; constructor; auto.
      + simpl; rewrite <- Facts.fresh_ident_vars_perm, <- Permutation_middle; eauto.
        apply Coqlib.incl_same_head; auto.
      + unfold st_clocks in *.
        erewrite fresh_ident_anns; eauto; simpl.
        rewrite <- Permutation_middle, <- Permutation_middle.
        apply perm_skip; auto.
      + clear Hperm.
        induction xs1; simpl in *.
        * constructor.
          -- intros y ?. rewrite Hstinit in H. inv H; auto.
             exfalso. apply in_map with (f:=snd) in H0; auto.
          -- eapply ForallTail_impl_In; [|eauto].
             intros (?&?) ? Hin Hy ? Hin'.
             rewrite Hstinit in Hin'. inv Hin'; auto.
             exfalso. inv H.
             eapply Forall_forall in Hinits'; [|eauto]; auto.
             specialize (Hinits' eq_refl). eauto using In_InMembers.
        * inv Hinits. inv Hinits'. inv Hcaus'.
          destruct a.
          constructor; eauto. clear IHxs1 H2 H4 H6.
          intros y Hin.
          rewrite Hstinit in Hin. inv Hin.
          -- inv H. right.
             rewrite in_app, Coqlib.in_cns in *; auto.
          -- apply H1 in H as [?|?]; auto.
             right. rewrite in_app, Coqlib.in_cns in *.
             destruct H; auto.
    - intros ? Hdep.
      destruct Hdep as [Hdep|?]; auto.
      inv Hdep. destruct H0 as (k&Hk&?&?).
      + simpl in H. rewrite Nat.lt_1_r in Hk; subst.
        inv H0; auto. inv H5.
      + exfalso. (* x ∈ vars_defined eqs ≡ (vars ++ st_clocks st), impossible *)
        eapply Exists_exists in H0 as ((?&?)&?&?&Hk&?&?); subst.
        eapply nth_In with (d:=xH) in Hk.
        eapply Hnin'. rewrite fst_InMembers, map_app, st_clocks_st_ids.
        eapply Hincl, vars_defined_In; eauto.
  Qed.

  Fact init_var_for_clock_causal_inv :
    forall vars eqs ck x eqs' st st',
      wc_clock vars ck ->
      causal_inv vars eqs st ->
      init_var_for_clock ck st = (x, eqs', st') ->
      causal_inv vars (eqs++eqs') st'.
  Proof.
    intros * Hwc Hinv Hinit.
    unfold init_var_for_clock in Hinit.
    destruct (find _ _) eqn:Hfind.
    - destruct p; inv Hinit; rewrite app_nil_r; auto.
    - destruct (fresh_ident _ _) eqn:Hfresh. inv Hinit.
      rewrite Permutation_app_comm; simpl.
      eapply causal_inv_insert_early. 1,5:eauto.
      + eapply wc_clock_incl; eauto. eapply incl_appl; reflexivity.
      + intros ? Hfree. inv Hfree.
        inv H1. 2:inv H4.
        eapply add_whens_Is_free_left; eauto.
      + eapply st_inits_find_None with (ck:=(ck, None)) in Hfind; eauto.
  Qed.

  Lemma causal_inv_replace_eq : forall vars st x ck e e' eqs,
      In (x, ck) (vars ++ st_clocks st) ->
      numstreams e = 1 ->
      causal_inv vars (([x], [e]) :: eqs) st ->
      (forall y, Is_free_left y 0 e' -> (Is_free_left y 0 e \/ (y <> x /\ In (y, ck) (st_inits st)))) ->
      causal_inv vars (([x], [e']) :: eqs) st.
  Proof.
    intros * Hck Hnum (?&?&?&?&xs&?&Hcaus&?) Hfree.
    repeat split; auto. exists xs; repeat split; auto.
    assert (Hcaus':=Hcaus).
    eapply ForallTail_ForallTail in Hcaus; [|eapply H4]. clear H4.
    eapply ForallTail_impl_In; [|eapply Hcaus]. clear Hcaus.
    intros [? ?] ? Hin [Hst Hinm] ? Hdep.
    (* x <> y ? *)
    destruct Hdep; auto. 2:apply Hinm; right; auto.
    inv H4. 2:apply Hinm; left; right; auto.
    destruct H6 as (k&Hlen&Hnth&Hfree'); subst.
    rewrite Nat.lt_1_r in Hlen; simpl in *; subst.
    inv Hfree'. 2:inv H8.
    apply Hfree in H8 as [Hfree'|[Hneq Hinit]]; clear Hfree.
    + eapply Hinm. left. left.
      exists 0. repeat split; auto.
      left; auto. rewrite Hnum; auto.
    + clear Hinm.
      assert (c = ck); subst.
      { rewrite H3 in Hin.
        eapply Facts.st_valid_after_NoDupMembers in H1; eauto.
        rewrite <- st_clocks_st_ids, <- map_app, <- fst_NoDupMembers in H1.
        eapply NoDupMembers_det in Hck; eauto. }
      eapply Hst in Hinit as [Heq|?].
      * inv Heq. contradiction.
      * eapply In_InMembers; eauto.
  Qed.

  (** Insert x right before y in l *)
  Fixpoint insert_before (x y : positive) (ck : clock) xs :=
    match xs with
    | [] => [(x, ck)]
    | hd::tl => if ident_eqb (fst hd) y then hd::(x, ck)::tl
              else hd::(insert_before x y ck tl)
    end.

  Lemma insert_before_Perm : forall x y ck xs,
      Permutation (insert_before x y ck xs) ((x, ck)::xs).
  Proof.
    induction xs; intros; simpl; auto.
    destruct ident_eqb; rewrite perm_swap; auto.
  Qed.

  Lemma insert_before_spec : forall x y ck xs,
      NoDupMembers xs ->
      In (y, ck) xs ->
      exists xs1 xs2,
        xs = xs1 ++ (y, ck) :: xs2 /\
        insert_before x y ck xs = xs1 ++ (y, ck) :: (x, ck) :: xs2.
  Proof.
    induction xs as [|[y' ck'] ?]; intros * Hndup Hin; inv Hin.
    - clear IHxs. inv H.
      exists []. exists xs. split; simpl; auto.
      rewrite ident_eqb_refl; auto.
    - assert (Hndup':=Hndup). inv Hndup'.
      specialize (IHxs H4 H) as (xs1&xs2&?&?); simpl.
      destruct ident_eqb eqn:Heq.
      + rewrite ident_eqb_eq in Heq; subst.
        eapply NoDupMembers_det in Hndup. 2:left; eauto.
        2:right; rewrite in_app_iff; right; left; eauto.
        subst.
        exists []. exists (xs1 ++ (y, ck) :: xs2). split; simpl; f_equal; auto.
      + eexists ((y', ck')::xs1). exists xs2. split; simpl; f_equal; auto.
  Qed.

  Fact depends_on_vars_defined : forall eqs x y,
      depends_on eqs x y ->
      In x (vars_defined eqs).
  Proof.
    intros * Hdep.
    unfold depends_on in Hdep.
    apply Exists_exists in Hdep as ((?&?)&?&?&Hl&Hnth&_).
    eapply vars_defined_In; eauto.
    rewrite <- Hnth. apply nth_In; auto.
  Qed.

  Lemma causal_inv_insert_eq :
    forall vars st st' x x' ty ck e e1 e2 eqs,
      In (x, ck) (vars ++ st_clocks st) ->
      ~In (x, ck) (st_inits st) ->
      numstreams e = 1 ->
      fresh_ident (ty, ck, false) st = (x', st') ->
      causal_inv vars (([x], [e]) :: eqs) st ->
      (forall y, Is_free_left y 0 e1 -> (y = x' \/ Is_free_left y 0 e \/ (y <> x /\ In (y, ck) (st_inits st)))) ->
      (forall y, Is_free_left y 0 e2 -> (Is_free_left y 0 e \/ Is_free_in_clock y ck)) ->
      causal_inv vars (([x], [e1]) :: ([x'], [e2]) :: eqs) st'.
  Proof.
    intros * Hck Hnin Hnum Hfresh (?&?&?&?&xs&?&Hcaus&?) Hf1 Hf2.
    repeat split; auto.
    - eapply fresh_ident_false_st_inits in Hfresh. rewrite Hfresh; auto.
    - eapply fresh_ident_st_valid in Hfresh; eauto.
    - simpl. rewrite <- Facts.fresh_ident_vars_perm; eauto.
      rewrite perm_swap, <- Permutation_middle. apply incl_tl'; auto.
    - assert (In (x, ck) xs) as Hck' by (rewrite H3; auto).
      assert (NoDupMembers xs) as Hnd.
      { rewrite H3. apply Facts.st_valid_after_NoDupMembers in H1; auto.
        rewrite <- st_clocks_st_ids, <- map_app, <- fst_NoDupMembers in H1; auto. }
      exists (insert_before x' x ck xs).
      specialize (insert_before_spec x' _ _ _ Hnd Hck') as (xs1&xs2&?&Hins); subst.
      assert (ForallTail
                (fun '(x0, ck0) xs => forall y : ident, In (y, ck0) (st_inits st') -> In (y, ck0) ((x0, ck0) :: xs))
                (xs1 ++ (x, ck) :: (x', ck) :: xs2)) as Hft.
      { eapply fresh_ident_false_st_inits in Hfresh. rewrite Hfresh.
        rewrite <- app_last_app. eapply ForallTail_insert with (x0:=(x', ck)).
        * rewrite app_last_app; auto.
        * eapply ForallTail_middle in H4. intros ? Hin.
          specialize (H4 _ Hin). rewrite Coqlib.in_cns in *. destruct H4 as [Hin'|Hin']; auto.
          inv Hin'. contradiction.
        * eapply Forall_forall. intros (?&?) _ ? Hy ? Hin.
          apply Hy in Hin.
          rewrite Coqlib.in_cns, in_app, Coqlib.in_cns in *.
          destruct Hin as [?|[?|?]]; auto. }
      repeat split.
      + rewrite insert_before_Perm.
        unfold st_clocks in *.
        erewrite fresh_ident_anns; [|eauto]; simpl.
        rewrite <- (Permutation_middle _ _ (x', _)). apply perm_skip; auto.
      + rewrite Hins. clear Hins.
        assert (ForallTail (fun '(x0, ck0) xs0 =>
                              forall y, depends_on_ck (([x], [e1]) :: ([x'], [e2]) :: eqs) x0 ck0 y ->
                                   InMembers y xs0 \/ y = x') (xs1 ++ (x, ck) :: xs2)) as Hcaus'.
        { eapply ForallTail_ForallTail in Hcaus; [|eapply H4].
          eapply ForallTail_impl_In; [|eapply Hcaus]. clear Hcaus H4.
          intros (?&?) ? Hin (Hinit&Hy) ? Hdep.
          assert (i <> x') as Hnx'.
          { intro contra; subst. rewrite H3 in Hin.
            eapply Facts.fresh_ident_nIn'' in Hfresh; eauto.
            apply in_map with (f:=fst) in Hin; auto.
            rewrite map_app, st_clocks_st_ids in Hin; auto. }
          unfold depends_on_ck, depends_on in Hdep. repeat rewrite Exists_cons in Hdep.
          destruct Hdep as [[(?&Hl&Hnth&Hf)|[(?&Hl&Hnth&Hf)|Hdep]]|Hdep]; simpl in *.
          - rewrite Nat.lt_1_r in Hl; subst.
            inv Hf. 2:inv H8.
            assert (c = ck); subst.
            { eapply NoDupMembers_det in Hnd; eauto. }
            apply Hf1 in H8 as [?|[?|(?&?)]]; subst.
            + right; auto.
            + left. eapply Hy. left; left.
              exists 0. repeat split; auto. left; auto. rewrite Hnum; auto.
            + specialize (Hinit _ H5) as [Hinit|Hinit]. inv Hinit; congruence.
              apply In_InMembers in Hinit; auto.
          - exfalso. rewrite Nat.lt_1_r in Hl; subst.
            congruence.
          - left. apply Hy. left; right; auto.
          - left. eapply Hy. right; eauto.
        }
        assert (forall x0 ck0, In (x0, ck0) xs2 -> x0 <> x /\ x0 <> x') as Hxs2.
        { intros x0 ck0 Hin. split; intro; subst.
          - apply NoDupMembers_app_r in Hnd. inv Hnd.
            apply In_InMembers in Hin; auto.
          - eapply Permutation_in in H3.
            2:rewrite in_app; right; right; eauto.
            eapply Facts.fresh_ident_nIn'' in Hfresh; eauto.
                apply in_map with (f:=fst) in H3; auto.
                rewrite map_app, st_clocks_st_ids in H3; auto.
        }
        clear H3 Hck' Hnd Hft.
        induction xs1; simpl in *; inv Hcaus; inv Hcaus'.
        * constructor; [|constructor]; eauto.
          -- intros y Hdep. eapply H8 in Hdep as [Hdep|Hdep]; [right|left]; auto.
          -- intros y Hdep.
             unfold depends_on_ck, depends_on in Hdep. repeat rewrite Exists_cons in Hdep.
             destruct Hdep as [[(?&Hl&Hnth&Hf)|[(?&Hl&Hnth&Hf)|Hdep]]|Hdep]; simpl in *.
             ++ exfalso. apply Nat.lt_1_r in Hl; subst.
                eapply Facts.fresh_ident_nIn'' in Hfresh; eauto.
                apply in_map with (f:=fst) in Hck; auto.
                rewrite map_app, st_clocks_st_ids in Hck; auto.
             ++ apply H6.
                apply Nat.lt_1_r in Hl; subst.
                inv Hf. 2:inv H12.
                apply Hf2 in H12 as [Hf|Hf]. 2:right; auto.
                left. left. exists 0. repeat split; auto.
                left; auto. rewrite Hnum; auto.
             ++ exfalso. apply depends_on_vars_defined in Hdep.
                apply incl_cons' in H2 as (_&Hincl). apply Hincl in Hdep.
                eapply Facts.fresh_ident_nIn'' in Hfresh; eauto.
             ++ apply H6. right; auto.
          -- clear H8 H9.
             eapply ForallTail_impl_In; [|eapply H7].
             intros (?&?) ? Hin Hy ? Hdep.
             apply Hxs2 in Hin as (Hneq1&Hneq2).
             unfold depends_on_ck, depends_on in Hdep. repeat rewrite Exists_cons in Hdep.
             destruct Hdep as [[(?&Hl&Hnth&Hf)|[(?&Hl&Hnth&Hf)|Hdep]]|Hdep]; simpl in *.
             ++ apply Nat.lt_1_r in Hl; subst. congruence.
             ++ apply Nat.lt_1_r in Hl; subst. congruence.
             ++ apply Hy. left; right; auto.
             ++ apply Hy. right; auto.
        * inv H4. destruct a.
          econstructor. 2:eapply IHxs1; eauto. clear IHxs1 H7 H9.
          intros y Hdep.
          apply H8 in Hdep.
          rewrite InMembers_app in *. destruct Hdep as [[Hdep|Hdep]|Hdep]; auto; subst.
          -- right. inv Hdep. left; auto. right; right; auto.
          -- right; right; left; auto.
      + rewrite Hins; auto.
  Qed.

  Fact fby_equation_causal : forall G vars to_cut eq eqs eqs' st st',
      Forall unnested_equation (eq::eqs) ->
      wc_env vars ->
      wc_equation G vars eq ->
      causal_inv vars (eq::eqs) st ->
      fby_equation to_cut eq st = (eqs', st') ->
      causal_inv vars (eqs++eqs') st'.
  Proof.
    intros * Hunt Hwenv Hwc Hinv Hfby.
    inv_fby_equation Hfby to_cut eq; try destruct x2 as (ty&ck&name).
    - destruct PS.mem; repeat inv_bind.
      1,2:rewrite Permutation_app_comm; simpl; auto.
      eapply causal_inv_insert_eq; eauto. 3:simpl; auto.
      + destruct Hwc as (_&_&Hwc). apply Forall2_singl in Hwc; auto.
        apply in_or_app; auto.
      + destruct Hinv as (Hndup&_&Hvalid&_).
        destruct Hwc as (_&_&Hin). apply Forall2_singl in Hin.
        apply Facts.st_valid_after_NoDupMembers in Hvalid; auto.
        intro contra. apply st_inits_incl_st_clocks in contra.
        rewrite <- st_clocks_st_ids, <- map_app in Hvalid.
        apply In_InMembers in Hin. apply In_InMembers in contra.
        rewrite <- fst_NoDupMembers in Hvalid. eapply NoDupMembers_app_InMembers in Hvalid; eauto.
      + intros ? Hfree. inv Hfree. left; auto.
    - repeat inv_bind.
      assert (Hinit:=H). eapply init_var_for_clock_causal_inv in H; eauto.
      2:{ destruct Hwc as (_&_&Hwc). apply Forall2_singl in Hwc.
          eapply wc_env_var; eauto. }
      simpl in *. rewrite <- Permutation_middle, <- (Permutation_middle eqs).
      assert (In (x, ck) vars) as Hin.
      { destruct Hwc as (_&_&Hwc). apply Forall2_singl in Hwc; auto. }
      eapply causal_inv_insert_eq; eauto. 3:auto.
      + apply in_or_app; auto.
      + destruct H as (Hndup&_&Hvalid&_).
        destruct Hwc as (_&_&Hin'). apply Forall2_singl in Hin'.
        apply Facts.st_valid_after_NoDupMembers in Hvalid; auto.
        intro contra. apply st_inits_incl_st_clocks in contra.
        rewrite <- st_clocks_st_ids, <- map_app in Hvalid.
        apply In_InMembers in Hin'. apply In_InMembers in contra.
        rewrite <- fst_NoDupMembers in Hvalid. eapply NoDupMembers_app_InMembers in Hvalid; eauto.
      + intros ? Hf. inv Hf.
        destruct H3 as [(_&Hf)|[Hf|Hf]]; auto 10.
        * inv Hf. right. right. split; auto.
          -- intro contra; subst.
             eapply init_var_for_clock_In in Hinit.
             destruct H as (_&_&Hvalid&_). eapply st_valid_NoDup in Hvalid.
             eapply NoDup_app_In in Hvalid. 2:rewrite <- Facts.st_anns_ids_In; eauto.
             apply Hvalid. rewrite ps_of_list_ps_to_list; auto.
             apply In_InMembers, fst_InMembers in Hin; auto.
          -- eapply init_var_for_clock_In_st_inits in Hinit; eauto.
        * inv Hf; inv H5; auto.
      + intros ? Hf.
        right. inv Hf.
        inv H3. 2:inv H6.
        apply add_whens_Is_free_left in H6; auto.
    - repeat inv_bind.
      assert (Hinit:=H). eapply init_var_for_clock_causal_inv in H; eauto.
      2:{ destruct Hwc as (_&_&Hwc). apply Forall2_singl in Hwc.
          eapply wc_env_var; eauto. }
      simpl in *. rewrite <- Permutation_middle.
      assert (In (x, ck) vars) as Hin.
      { destruct Hwc as (_&_&Hwc). apply Forall2_singl in Hwc; auto. }
      eapply causal_inv_replace_eq; eauto. 2:auto.
      + apply in_or_app; eauto.
      + intros y Hfree.
        inv Hfree. destruct H2 as [(_&?)|[Hfree|Hfree]].
        2,3:left; constructor; auto.
        right.
        inv H0. split.
        * intro contra; subst.
          eapply init_var_for_clock_In in Hinit.
          destruct H as (_&_&Hvalid&_). eapply st_valid_NoDup in Hvalid.
          eapply NoDup_app_In in Hvalid. 2:rewrite <- Facts.st_anns_ids_In; eauto.
          apply Hvalid. rewrite ps_of_list_ps_to_list; auto.
          apply In_InMembers, fst_InMembers in Hin; auto.
        * eapply init_var_for_clock_In_st_inits in Hinit; eauto.
    - rewrite Permutation_app_comm; auto.
  Qed.

  Fact fby_equations_causal' :
    forall G vars to_cut eqs ceqs eqs' st st',
      wc_env vars ->
      Forall unnested_equation (ceqs++eqs) ->
      Forall (wc_equation G vars) eqs ->
      causal_inv vars (ceqs++eqs) st ->
      fby_equations to_cut eqs st = (eqs', st') ->
      causal_inv vars (ceqs++eqs') st'.
  Proof.
    induction eqs; intros * Henv Hunt Hwc Hinv Hfby;
      unfold fby_equations in Hfby; simpl in *; repeat inv_bind; simpl; auto.
    inv Hwc.
    rewrite <- Permutation_middle in Hinv.
    eapply fby_equation_causal in H as Hcaus'. 2,3,4,5:eauto.
    2:rewrite Permutation_middle; eauto.
    rewrite <- app_assoc, (Permutation_app_comm eqs), app_assoc in Hcaus'.
    eapply IHeqs in Hcaus'; eauto.
    - rewrite <- app_assoc in Hcaus'; eauto.
    - apply Forall_app in Hunt as [Hunt1 Hunt2]. inv Hunt2.
      repeat rewrite Forall_app. repeat split; auto.
      eapply fby_equation_unnested_eq; eauto.
    - unfold fby_equations; repeat inv_bind; repeat eexists; eauto; inv_bind; auto.
  Qed.

  Corollary fby_equations_causal :
    forall G vars to_cut eqs eqs' st st',
      wc_env vars ->
      Forall unnested_equation eqs ->
      Forall (wc_equation G vars) eqs ->
      causal_inv vars eqs st ->
      fby_equations to_cut eqs st = (eqs', st') ->
      causal_inv vars eqs' st'.
  Proof.
    intros * Hwenv Hunt Hwl Hcaus Hfby.
    eapply fby_equations_causal' with (ceqs:=[]) in Hfby; simpl; eauto.
  Qed.

  Fact Permutation_map_fst {B} : forall (xs : list (ident * B)) ys,
      Permutation (map fst xs) ys ->
      exists zs, Permutation xs zs /\ ys = map fst zs.
  Proof.
    induction xs; intros * Hperm.
    - apply Permutation_nil in Hperm; subst.
      exists []; auto.
    - destruct a as [id b].
      specialize (in_split id ys) as (ys1&ys2&?); subst.
      { rewrite <- Hperm. left; auto. }
      apply Permutation_cons_app_inv in Hperm.
      apply IHxs in Hperm as (?&?&?).
      symmetry in H0. apply map_app' in H0 as (xs1&xs2&?&?&?); subst.
      exists (xs1 ++ (id, b) :: xs2); simpl; split.
      + rewrite <- Permutation_middle. apply perm_skip; auto.
      + rewrite map_app; simpl. reflexivity.
  Qed.

  Lemma normfby_node_causal : forall G n to_cut Hunt,
      wc_global G ->
      wc_node G n ->
      node_causal n ->
      node_causal (normfby_node to_cut n Hunt).
  Proof.
    intros * HwcG Hwc Hcaus.
    unfold node_causal in *; simpl.
    remember (fby_equations _ _ _) as res. symmetry in Heqres. destruct res as [eqs' st'].
    eapply fby_equations_causal in Heqres; eauto. 3:destruct Hwc as (_&_&_&?); eauto.
    - destruct Heqres as (?&?&?&?&xs'&Hperm'&Hcaus'&_).
      exists (map fst xs'); simpl; split; auto.
      2:apply Is_causal_ck_Is_causal; auto.
      rewrite <- map_fst_idck.
      apply Permutation_map. rewrite Hperm'.
      repeat rewrite idck_app. unfold st_clocks.
      repeat rewrite <- app_assoc. apply Permutation_app_head, Permutation_app_head.
      rewrite Permutation_app_comm. apply Permutation_app_tail.
      reflexivity.
    - destruct Hwc as (_&_&?&_).
      rewrite (Permutation_app_comm (n_vars _)); eauto.
    - eapply Is_causal_ck_causal_inv; eauto.
      + rewrite NoDupMembers_idck, fst_NoDupMembers.
        apply node_NoDup.
      + eapply Forall_incl. eapply first_unused_ident_gt; eauto.
        rewrite map_fst_idck.
        apply incl_tl, incl_tl, incl_map, incl_appr', incl_appr', incl_appl, incl_refl.
      + rewrite n_defd, map_fst_idck.
        apply incl_map, incl_appr, incl_refl.
      + destruct Hcaus as (xs&Hperm1&Hcaus).
        symmetry in Hperm1. rewrite <- map_fst_idck in Hperm1. apply Permutation_map_fst in Hperm1 as (xs'&Hperm1&?); subst.
        apply Is_causal_Is_causal_ck in Hcaus as (xs''&Hperm2&Hcaus).
        exists xs''. split; auto.
        rewrite <- Hperm2, <- Hperm1; eauto.
  Qed.

  Lemma normfby_global_causal : forall G Hunt,
      wc_global G ->
      Forall node_causal G ->
      Forall node_causal (normfby_global G Hunt).
  Proof.
    induction G; intros * Hwc Hcaus; auto.
    inv Hwc. inv Hcaus.
    constructor; eauto.
    eapply normfby_node_causal; eauto.
  Qed.

End NCAUSALITY.

Module NCausalityFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Syn : LSYNTAX Ids Op)
       (Cau : LCAUSALITY Ids Op Syn)
       (Clo : LCLOCKING Ids Op Syn)
       (Norm : NORMALIZATION Ids Op OpAux Syn Cau)
       <: NCAUSALITY Ids Op OpAux Syn Cau Clo Norm.
  Include NCAUSALITY Ids Op OpAux Syn Cau Clo Norm.
End NCausalityFun.
