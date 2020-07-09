From Coq Require Import List Sorting.Permutation.
Import List.ListNotations.
Open Scope list_scope.
Require Import Omega.

From Velus Require Import Common Ident Environment.
From Velus Require Import Operators.
From Velus Require Import Lustre.LSyntax.
From Velus Require Lustre.Normalization.Fresh.
From Velus Require Import Lustre.Normalization.Untuple.

(** * Putting FBYs into normalized form *)

Local Set Warnings "-masking-absolute-name".
Module Type NORMFBY
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Import Syn : LSYNTAX Ids Op)
       (Import Unt : UNTUPLE Ids Op OpAux Syn).

  Import Fresh Fresh.Fresh Fresh.Notations Facts Tactics.
  Local Open Scope fresh_monad_scope.

  (** Fresh ident generation keeping type annotations;
      also retaining if the var is an init var or not *)
  Definition FreshAnn A := Fresh A ((type * clock) * bool).

  (** Add some whens on top of an expression *)
  Fixpoint add_whens (e : exp) (ty : type) (cl : clock) :=
    match cl with
    | Cbase => e
    | Con cl' clid b => Ewhen [(add_whens e ty cl')] clid b ([ty], (cl, None))
    end.

  (** Generate an init equation for a given clock `cl`; if the init equation for `cl` already exists,
      just return the variable *)
  Definition init_var_for_clock (cl : clock) : FreshAnn (ident * list equation) :=
    fun st => match (find (fun '(_, ((ty, cl'), isinit)) => isinit && (cl' ==b cl) && (ty ==b Op.bool_type)) (st_anns st)) with
           | Some (x, _) => ((x, []), st)
           | None => let (x, st') := fresh_ident ((bool_type, cl), true) st in
                    ((x, [([x], [Efby [add_whens (Econst true_const) bool_type cl]
                                      [add_whens (Econst false_const) bool_type cl]
                                      [(bool_type, (cl, None))]])]), st')
           end.

  Fixpoint is_constant (e : exp) : bool :=
    match e with
    | Econst _ => true
    | Ewhen [e] _ _ ([ty], _) => is_constant e
    | _ => false
    end.

  (** Generate a if-then-else equation for (0 fby e), and return an expression using it *)
  Definition fby_iteexp (e0 : exp) (e : exp) (ann : ann) : FreshAnn (exp * list equation) :=
    let '(ty, cl) := ann in
    if (is_constant e0)
    then ret (Efby [e0] [e] [ann], [])
    else do (initid, eqs) <- init_var_for_clock (fst cl);
         do px <- fresh_ident ((ty, fst cl), false);
         ret (Eite (Evar initid (bool_type, (fst cl, Some initid))) [e0]
                   [Evar px (ty, (fst cl, Some px))] ([ty], cl),
              ([px], [Efby [add_whens (Econst (init_type ty)) ty (fst cl)] [e] [ann]])::eqs).

  Definition fby_equation (to_cut : PS.t) (eq : equation) : FreshAnn (list equation) :=
    match eq with
    | ([x], [Efby [e0] [e] [ann]]) =>
      let '(ty, (ck, _)) := ann in
      do (fby, eqs) <- fby_iteexp e0 e ann;
      if PS.mem x to_cut
      then do x' <- fresh_ident ((ty, ck), false);
           ret (([x], [Evar x' ann])::([x'], [fby])::eqs)
      else ret (([x], [fby])::eqs)
    | _ => ret [eq]
    end.

  Definition fby_equations (to_cut : PS.t) (eqs : list equation) : FreshAnn (list equation) :=
    do eqs' <- map_bind (fby_equation to_cut) eqs;
    ret (concat eqs').

  (** Some initial properties *)

  Local Ltac destruct_to_singl l :=
    destruct l; [|destruct l]; auto.

  Fact fby_equation_spec : forall to_cut xs es,
      (exists x, exists e0, exists e, exists ann,
                xs = [x] /\
                es = [Efby [e0] [e] [ann]] /\
                fby_equation to_cut (xs, es) =
                (let '(ty, (ck, _)) := ann in
                 do (fby, eqs) <- fby_iteexp e0 e ann;
                 if PS.mem x to_cut
                 then do x' <- fresh_ident ((ty, ck), false);
                      ret (([x], [Evar x' ann])::([x'], [fby])::eqs)
                 else ret (([x], [fby])::eqs)))
      \/ fby_equation to_cut (xs, es) = (ret [(xs, es)]).
  Proof.
    intros *.
    destruct_to_singl xs. destruct_to_singl es.
    2: { right; simpl. destruct e; auto.
         destruct_to_singl l. destruct_to_singl l0. destruct_to_singl l1. }
    destruct e; auto.
    destruct_to_singl l. destruct_to_singl l0. destruct_to_singl l1.
    left. repeat eexists; eauto.
  Qed.

  (** *** Preservation of st_valid *)

  Fact init_var_for_clock_st_valid : forall cl res st st' aft,
      init_var_for_clock cl st = (res, st') ->
      st_valid_after st aft ->
      st_valid_after st' aft.
  Proof.
    intros * Hinit Hvalid.
    unfold init_var_for_clock in Hinit.
    repeat inv_bind.
    destruct (find _ _).
    - destruct p. inv Hinit. assumption.
    - destruct (fresh_ident _ _) eqn:Hfresh. inv Hinit.
      eapply fresh_ident_st_valid in Hfresh; eauto.
  Qed.
  Hint Resolve init_var_for_clock_st_valid.

  Fact fby_iteexp_st_valid : forall e0 e a e' eqs' st st' aft,
      fby_iteexp e0 e a st = (e', eqs', st') ->
      st_valid_after st aft ->
      st_valid_after st' aft.
  Proof with eauto.
    intros e0 e [ty cl] e' eqs' st st' aft Hfby Hvalid.
    unfold fby_iteexp in Hfby.
    destruct (is_constant e0); repeat inv_bind...
  Qed.
  Hint Resolve fby_iteexp_st_valid.

  Fact fby_equation_st_valid : forall to_cut eq eqs' st st' aft,
      fby_equation to_cut eq st = (eqs', st') ->
      st_valid_after st aft ->
      st_valid_after st' aft.
  Proof.
    intros to_cut [xs es] ? ? ? ? Hfby Hvalid.
    specialize (fby_equation_spec to_cut xs es) as [[? [? [? [? [? [? Hspec]]]]]]|Hspec]; subst;
      rewrite Hspec in Hfby; clear Hspec; [|repeat inv_bind; auto].
    destruct x2 as [ty [ck name]]; repeat inv_bind.
    destruct (PS.mem _ _); repeat inv_bind; auto.
    - eapply fresh_ident_st_valid; eauto.
      eapply fby_iteexp_st_valid with (a:=(ty, (ck, name))); unfold fby_iteexp; eauto.
    - eapply fby_iteexp_st_valid with (a:=(ty, (ck, name))); unfold fby_iteexp; eauto.
  Qed.

  Fact fby_equations_st_valid : forall to_cut eqs eqs' st st' aft,
      fby_equations to_cut eqs st = (eqs', st') ->
      st_valid_after st aft ->
      st_valid_after st' aft.
  Proof.
    intros * Hfby Hst.
    unfold fby_equations in Hfby; repeat inv_bind.
    eapply map_bind_st_valid in Hst; eauto.
    solve_forall. eapply fby_equation_st_valid; eauto.
  Qed.

  (** *** Preservation of st_follows *)

  Fact init_var_for_clock_st_follows : forall cl res st st',
      init_var_for_clock cl st = (res, st') ->
      st_follows st st'.
  Proof.
    intros cl res st st' Hinit.
    unfold init_var_for_clock in Hinit.
    repeat inv_bind.
    destruct (find _ _).
    - destruct p. inv Hinit. reflexivity.
    - destruct (fresh_ident _ _) eqn:Hfresh. inv Hinit.
      apply fresh_ident_st_follows in Hfresh. auto.
  Qed.
  Hint Resolve init_var_for_clock_st_follows.

  Fact fby_iteexp_st_follows : forall e0 e ann res st st',
      fby_iteexp e0 e ann st = (res, st') ->
      st_follows st st'.
  Proof.
    intros e0 e [ty cl] res st st' Hfby.
    unfold fby_iteexp in Hfby.
    destruct (is_constant e0); repeat inv_bind.
    - reflexivity.
    - etransitivity; eauto.
  Qed.
  Hint Resolve fby_iteexp_st_follows.

  (** *** The variables generated are a permutation of the ones contained in the state *)

  Fact init_var_for_clock_vars_perm : forall cl id eqs st st',
      init_var_for_clock cl st = ((id, eqs), st') ->
      Permutation ((vars_defined eqs)++(st_ids st)) (st_ids st').
  Proof.
    intros cl id eqs st st' Hinit.
    unfold init_var_for_clock in Hinit. repeat inv_bind.
    destruct (find _ _).
    - destruct p. inv Hinit. reflexivity.
    - destruct (fresh_ident _ _) eqn:Hfresh. inv Hinit.
      apply fresh_ident_vars_perm in Hfresh.
      simpl. assumption.
  Qed.

  Fact fby_iteexp_vars_perm : forall e0 e ann e' eqs' st st',
      fby_iteexp e0 e ann st = (e', eqs', st') ->
      Permutation ((vars_defined eqs')++(st_ids st)) (st_ids st').
  Proof.
    intros ? ? [ty [ck name]] ? ? ? ? Hfby.
    unfold fby_iteexp in Hfby. repeat inv_bind.
    destruct (is_constant _); repeat inv_bind; simpl; eauto.
    eapply init_var_for_clock_vars_perm in H; eauto.
    eapply fresh_ident_vars_perm in H0.
    rewrite <- H0, H; auto.
  Qed.

  Fact fby_equation_vars_perm : forall to_cut eq eqs' st st',
      fby_equation to_cut eq st = (eqs', st') ->
      Permutation ((vars_defined eqs')++(st_ids st)) ((vars_defined [eq])++(st_ids st')).
  Proof.
    intros to_cut [xs es] eqs' st st' Hfby.
    specialize (fby_equation_spec to_cut xs es) as [[? [? [? [? [? [? Hspec]]]]]]|Hspec];
      subst; rewrite Hspec in Hfby; clear Hspec.
    - destruct x2 as [ty [ck name]]; repeat inv_bind.
      eapply fby_iteexp_vars_perm with (ann:=(ty, (ck, name))) in H.
      destruct (PS.mem _ _); repeat inv_bind; simpl.
      + apply fresh_ident_vars_perm in H0.
        rewrite H, <- H0; auto.
      + rewrite H; auto.
    - repeat inv_bind; simpl; auto.
  Qed.

  Fact fby_equations_vars_perm : forall to_cut eqs eqs' st st',
      fby_equations to_cut eqs st = (eqs', st') ->
      Permutation ((vars_defined eqs')++(st_ids st)) ((vars_defined eqs)++(st_ids st')).
  Proof.
    induction eqs; intros * Hnorm; unfold fby_equations in Hnorm; repeat inv_bind.
    - reflexivity.
    - assert (fby_equations to_cut eqs x1 = (concat x2, st')) as Hnorm'.
      { unfold fby_equations. repeat inv_bind. repeat eexists; eauto.
        inv_bind; eauto. } eapply IHeqs in Hnorm'; eauto.
      eapply fby_equation_vars_perm in H; eauto; simpl in *.
      repeat simpl_list.
      rewrite Permutation_swap, H, Permutation_swap.
      apply Permutation_app_head. assumption.
  Qed.

  (** *** Preservation of annotations *)

  Fact fby_iteexp_annot : forall e0 e ann es' eqs' st st',
      fby_iteexp e0 e ann st = (es', eqs', st') ->
      annot es' = [ann].
  Proof.
    intros e0 e [ty [cl n]] es' eqs' st st' Hfby.
    unfold fby_iteexp in Hfby.
    destruct (is_constant e0); repeat inv_bind; reflexivity.
  Qed.

  (** *** Additional props *)

  Fact init_var_for_clock_In : forall cl id eqs' st st',
      init_var_for_clock cl st = (id, eqs', st') ->
      In (id, (Op.bool_type, cl, true)) (st_anns st').
  Proof.
    intros cl id eqs' st st' Hinit.
    unfold init_var_for_clock in Hinit.
    destruct (find _ _) eqn:Hfind.
    - destruct p; inv Hinit.
      eapply find_some in Hfind. destruct Hfind as [Hin H].
      destruct p as [[? ?] ?].
      repeat rewrite Bool.andb_true_iff in H. destruct H as [[Hb Hcl] Hty].
      rewrite OpAux.type_eqb_eq in Hty. rewrite Clocks.clock_eqb_eq in Hcl. subst. eauto.
    - destruct (fresh_ident _ _) eqn:Hfresh. inv Hinit.
      eapply fresh_ident_In in Hfresh; eauto.
  Qed.

  (** ** Specification of a normalized node *)

  Inductive normalized_constant : exp -> Prop :=
  | constant_Econst : forall c,
      normalized_constant (Econst c)
  | constant_Ewhen : forall e x b ty cl,
      normalized_constant e ->
      normalized_constant (Ewhen [e] x b ([ty], cl)).

  Inductive normalized_equation : PS.t -> equation -> Prop :=
  | normalized_eq_Eapp : forall out xs f es lann,
      Forall normalized_lexp es ->
      normalized_equation out (xs, [Eapp f es None lann])
  | normalized_eq_Eapp_reset : forall out xs f es x ty cl lann,
      Forall normalized_lexp es ->
      normalized_equation out (xs, [Eapp f es (Some (Evar x (ty, cl))) lann])
  | normalized_eq_Efby : forall out x e0 e ann,
      ~PS.In x out ->
      normalized_constant e0 ->
      normalized_lexp e ->
      normalized_equation out ([x], [Efby [e0] [e] [ann]])
  | normalized_eq_cexp : forall out x e,
      normalized_cexp e ->
      normalized_equation out ([x], [e]).

  Definition normalized_node (n : node) :=
    Forall (normalized_equation (ps_from_list (List.map fst (n_out n)))) (n_eqs n).

  Definition normalized_global (G : global) := Forall normalized_node G.

  Hint Constructors normalized_constant normalized_equation.

  (** *** Propagation of the weak_valid_after property *)

  Fact init_var_for_clock_weak_valid : forall nck id st st' out,
      init_var_for_clock nck st = (id, st') ->
      weak_valid_after st out ->
      weak_valid_after st' out.
  Proof.
    intros nck id st st' out Hinit Hval;
      unfold init_var_for_clock in Hinit.
    destruct find in Hinit.
    - destruct p; inv Hinit; auto.
    - destruct fresh_ident eqn:Hfresh.
      inv Hinit; eauto.
  Qed.
  Local Hint Resolve init_var_for_clock_weak_valid.

  Fact fby_iteexp_weak_valid : forall e0 e a e' eqs' st st' out,
      fby_iteexp e0 e a st = (e', eqs', st') ->
      weak_valid_after st out ->
      weak_valid_after st' out.
  Proof.
    intros e0 e [ty cl] e' eqs' st st' out Hfby Hval;
      unfold fby_iteexp in Hfby.
    destruct (is_constant e0); repeat inv_bind; eauto.
  Qed.
  Local Hint Resolve fby_iteexp_weak_valid.

  Fact fby_equation_weak_valid : forall eq eqs' st st' to_cut out,
      fby_equation to_cut eq st = (eqs', st') ->
      weak_valid_after st out ->
      weak_valid_after st' out.
  Proof.
    intros * Hfby Hweak. destruct eq as [xs es].
    specialize (fby_equation_spec to_cut xs es) as [[? [? [? [? [? [? Hspec]]]]]]|Hspec]; subst;
      rewrite Hspec in Hfby; clear Hspec.
    - destruct x2 as [ty [ck name]]; repeat inv_bind.
      eapply fby_iteexp_weak_valid with (a:=(ty, (ck, name))) in H; eauto.
      destruct (PS.mem _ _); repeat inv_bind; eauto.
    - repeat inv_bind; auto.
  Qed.

  Fact fby_equations_weak_valid : forall eqs eqs' st st' to_cut out,
      fby_equations to_cut eqs st = (eqs', st') ->
      weak_valid_after st out ->
      weak_valid_after st' out.
  Proof.
    intros * Hfby Hweak.
    unfold fby_equations in Hfby; repeat inv_bind.
    eapply map_bind_weak_valid in H; eauto.
    solve_forall. eapply fby_equation_weak_valid; eauto.
  Qed.

  (** *** normalized_node implies untupled_node *)

  Fact constant_normalized_lexp : forall e,
      normalized_constant e ->
      normalized_lexp e.
  Proof.
    intros e Hconst.
    induction Hconst; auto.
  Qed.

  Fact normalized_eq_untupled_eq : forall to_cut eq,
      normalized_equation to_cut eq ->
      untupled_equation eq.
  Proof.
    intros * Hnormed. inv Hnormed; auto using constant_normalized_lexp.
  Qed.

  (** ** After normalization, equations and expressions are normalized *)

  Fact add_whens_is_constant : forall ty cl e,
      normalized_constant e ->
      normalized_constant (add_whens e ty cl).
  Proof.
    induction cl; intros e Hcons; simpl.
    - assumption.
    - constructor. eauto.
  Qed.

  Fact add_whens_normalized_lexp : forall ty cl e,
      normalized_lexp e ->
      normalized_lexp (add_whens e ty cl).
  Proof.
    induction cl; intros e Hadd; simpl in Hadd.
    - assumption.
    - constructor. eauto.
  Qed.

  Fact is_constant_normalized_constant : forall e,
      is_constant e = true <->
      normalized_constant e.
  Proof with eauto.
    intros e. split; intros Hconst.
    - induction e using exp_ind2; simpl in Hconst; try congruence.
      + constructor.
      + repeat (destruct es; try congruence).
        inv H; inv H3.
        destruct a.
        repeat (destruct l; try congruence).
        constructor...
    - induction Hconst...
  Qed.

  Fact init_var_for_clock_normalized_eq : forall cl id eqs' out st st',
      weak_valid_after st out ->
      init_var_for_clock cl st = (id, eqs', st') ->
      Forall (normalized_equation out) eqs'.
  Proof.
    intros cl id eqs' out st st' Hvalid Hinit.
    unfold init_var_for_clock in Hinit.
    destruct (find _ _).
    - destruct p. inv Hinit. constructor.
    - destruct (fresh_ident _ _) eqn:Hfresh. inv Hinit.
      repeat constructor.
      + eapply fresh_ident_weak_valid_nIn in Hfresh; eauto.
      + apply add_whens_is_constant. auto.
      + apply add_whens_normalized_lexp. auto.
  Qed.

  Fact fby_iteexp_normalized_eq : forall e0 e a e' eqs' out st st',
      weak_valid_after st out ->
      normalized_lexp e ->
      fby_iteexp e0 e a st = (e', eqs', st') ->
      Forall (normalized_equation out) eqs'.
  Proof.
    intros e0 e [ty cl] e' eqs' out st st' Hvalid He Hfby.
    unfold fby_iteexp in Hfby.
    destruct (is_constant e0); repeat inv_bind; constructor.
    - assert (weak_valid_after x1 out) as Hvalid' by eauto.
      constructor; auto.
      + eapply fresh_ident_weak_valid_nIn in H0; eauto.
      + eapply add_whens_is_constant; eauto.
    - eapply init_var_for_clock_normalized_eq in H; eauto.
  Qed.

  Fact fby_equation_normalized_eq : forall out to_cut eq eqs' st st',
      weak_valid_after st out ->
      untupled_equation eq ->
      PS.Subset out to_cut ->
      fby_equation to_cut eq st = (eqs', st') ->
      Forall (normalized_equation out) eqs'.
  Proof.
    intros out to_cut [xs es] eqs' st st' Hvalid Hunt Hsub Hfby.
    inv Hunt; simpl in *.
    - destruct_to_singl xs; repeat inv_bind; auto.
    - destruct_to_singl xs; repeat inv_bind; auto.
    - destruct ann0 as [ty [ck name]]; repeat inv_bind.
      destruct (PS.mem _ _) eqn:Hmem; repeat inv_bind; constructor. 2:constructor.
      3,5:eapply fby_iteexp_normalized_eq with (a:=(ty, (ck, name))); eauto.
      2,3:destruct (is_constant e0) eqn:Hconst; repeat inv_bind.
      1-5:repeat (constructor; eauto).
      2,4:rewrite is_constant_normalized_constant in Hconst; eauto.
      + eapply fresh_ident_weak_valid_nIn in H0; eauto.
      + apply PSE.mem_4 in Hmem; auto.
    - inv H0; repeat inv_bind; auto.
      inv H; repeat inv_bind; auto.
  Qed.

  Fact fby_equations_normalized_eq : forall out to_cut eqs eqs' st st',
      weak_valid_after st out ->
      Forall untupled_equation eqs ->
      PS.Subset out to_cut ->
      fby_equations to_cut eqs st = (eqs', st') ->
      Forall (normalized_equation out) eqs'.
  Proof.
    induction eqs; intros * Hvalid Hunt Hsub Hfby;
      unfold fby_equations in Hfby; repeat inv_bind; simpl; auto.
    inv Hunt.
    eapply Forall_app; split.
    - eapply fby_equation_normalized_eq in H; eauto.
    - eapply IHeqs with (st:=x1) (st':=st'); eauto. 1:eapply fby_equation_weak_valid; eauto.
      unfold fby_equations; repeat inv_bind.
      repeat eexists; eauto. inv_bind; eauto.
  Qed.

  (** ** No anonymous names in a normalized node *)

  Fact is_constant_no_fresh : forall e,
      normalized_constant e ->
      fresh_in e = [].
  Proof with eauto.
    intros e Hconst.
    induction Hconst; simpl...
    rewrite IHHconst...
  Qed.

  Lemma fby_equations_no_fresh : forall out to_cut eqs eqs' st st',
      weak_valid_after st out ->
      Forall untupled_equation eqs ->
      PS.Subset out to_cut ->
      fby_equations to_cut eqs st = (eqs', st') ->
      anon_in_eqs eqs' = [].
  Proof.
    intros * Hweak Hunt Hsub Hfby.
    eapply fby_equations_normalized_eq in Hfby; eauto.
    eapply untupled_equations_no_anon.
    solve_forall. eapply normalized_eq_untupled_eq; eauto.
  Qed.

  (** ** Normalization of a full node *)

  Program Definition normfby_node (to_cut : PS.t) (n : node) (Hunt : untupled_node n) : node :=
    let anon := anon_in_eqs (n_eqs n) in
    let id0 := first_unused_ident (reserved++List.map fst (n_in n++n_vars n++n_out n++anon)) in
    let eqs := fby_equations (PS.union to_cut (ps_from_list (map fst (n_out n)))) (n_eqs n) (init_st id0) in
    let nvars := idty (st_anns (snd eqs)) in
    {| n_name := n_name n;
       n_hasstate := n_hasstate n;
       n_in := n_in n;
       n_out := n_out n;
       n_vars := (n_vars n)++nvars;
       n_eqs := fst eqs;
       n_ingt0 := n_ingt0 n;
       n_outgt0 := n_outgt0 n;
    |}.
  Next Obligation.
    remember (first_unused_ident _) as id0.
    remember (init_st _) as st.
    remember (fby_equations _ _ _) as eqs. destruct eqs as [eqs st']. symmetry in Heqeqs.
    specialize (n_defd n) as Hperm.
    apply fby_equations_vars_perm in Heqeqs; simpl.
    rewrite Permutation_app_comm, app_assoc, map_app, (Permutation_app_comm (n_out n)), <- Hperm, map_fst_idty.
    rewrite <- Heqeqs, Heqst. unfold st_ids. rewrite init_st_anns, app_nil_r; auto.
  Qed.
  Next Obligation.
    remember (first_unused_ident _) as id0.
    remember (init_st _) as st.
    remember (fby_equations _ _ _) as eqs. destruct eqs as [eqs st']. symmetry in Heqeqs.
    assert (NoDup (map fst (n_in n ++ n_vars n ++ n_out n))) as Hndup.
    { specialize (n_nodup n) as Hndup.
      rewrite <- fst_NoDupMembers. repeat rewrite app_assoc in *. apply NoDupMembers_app_l in Hndup; auto. }
    assert (st_valid_after st (PSP.of_list (map fst (n_in n ++ n_vars n ++ n_out n)))) as Hvalid.
    { rewrite Heqst. eapply init_st_valid. symmetry in Heqid0. eapply first_unused_ident_gt in Heqid0.
      rewrite PS_For_all_Forall.
      eapply Forall_incl; eauto.
      apply incl_tl, incl_tl.
      rewrite ps_of_list_ps_to_list_Perm; eauto.
      apply incl_map, incl_appr', incl_appr', incl_appl, incl_refl. }
    assert (weak_valid_after st (PSP.of_list (map fst (n_out n)))) as Hweak.
    { rewrite Heqst. eapply st_valid_weak_valid, init_st_valid. symmetry in Heqid0. eapply first_unused_ident_gt in Heqid0.
      rewrite PS_For_all_Forall.
      eapply Forall_incl; eauto.
      apply incl_tl, incl_tl. intros ? Hin.
      rewrite ps_of_list_ps_to_list in Hin. repeat simpl_In.
      exists (i, (t, c)); split; auto. repeat rewrite in_app_iff in *; auto. }
    simpl. erewrite fby_equations_no_fresh, app_nil_r. 2,3,5:eauto.
    2:rewrite ps_from_list_ps_of_list; eapply PSP.union_subset_2.
    eapply fby_equations_st_valid, st_valid_NoDup in Heqeqs; eauto.
    rewrite ps_of_list_ps_to_list_Perm in Heqeqs; auto.
    rewrite <- app_assoc, fst_NoDupMembers. repeat rewrite map_app in *.
    unfold st_ids in Heqeqs. rewrite map_fst_idty, (app_assoc (map _ (n_vars _))), (Permutation_app_comm (map _ (n_vars _))),
                             <- app_assoc, app_assoc, (Permutation_app_comm (map _ (n_in _))), <- app_assoc; auto.
  Qed.
  Admit Obligations.

  Fixpoint normfby_global (G : global) (Hunt: Forall untupled_node G) : global.
  Proof.
    destruct G as [|hd tl].
    - exact [].
    - refine ((normfby_node PS.empty hd _)::(normfby_global tl _)).
      + inv Hunt; eauto.
      + inv Hunt; eauto.
  Defined.

  (** *** After normalization, a global is normalized *)

  Fact normfby_node_normalized_node : forall n to_cut Hunt,
      normalized_node (normfby_node to_cut n Hunt).
  Proof.
    intros *.
    unfold normfby_node, normalized_node; simpl.
    remember (first_unused_ident _) as id0.
    remember (init_st _) as st.
    remember (fby_equations _ _ _) as eqs. symmetry in Heqeqs. destruct eqs as [eqs st'].
    eapply fby_equations_normalized_eq in Heqeqs; eauto.
    2:rewrite ps_from_list_ps_of_list; eapply PSP.union_subset_2.
    { rewrite Heqst. eapply st_valid_weak_valid, init_st_valid. symmetry in Heqid0. eapply first_unused_ident_gt in Heqid0.
      rewrite PS_For_all_Forall.
      eapply Forall_incl; eauto.
      apply incl_tl, incl_tl. intros ? Hin.
      rewrite ps_from_list_ps_of_list, ps_of_list_ps_to_list in Hin. repeat simpl_In.
      exists (i, (t, c)); split; auto. repeat rewrite in_app_iff in *; auto. }
  Qed.

  Fact normfby_global_normalized_global : forall G Hunt,
      normalized_global (normfby_global G Hunt).
  Proof.
    induction G; intros; simpl; constructor.
    - eapply normfby_node_normalized_node.
    - eapply IHG.
  Qed.

  (** *** normfby_global produces an equivalent global *)

  Fact normfby_global_eq : forall G Hunt,
      global_iface_eq G (normfby_global G Hunt).
  Proof.
    induction G; intros Hunt.
    - reflexivity.
    - simpl. apply global_iface_eq_cons; auto.
  Qed.

  Fact normfby_global_names : forall a G Hunt,
      Forall (fun n => (n_name a <> n_name n)%type) G ->
      Forall (fun n => (n_name a <> n_name n)%type) (normfby_global G Hunt).
  Proof.
    induction G; intros Hunt Hnames; simpl.
    - constructor.
    - inv Hnames.
      constructor; eauto.
  Qed.
End NORMFBY.

Module NormFbyFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Syn : LSYNTAX Ids Op)
       (Unt : UNTUPLE Ids Op OpAux Syn)
       <: NORMFBY Ids Op OpAux Syn Unt.
  Include NORMFBY Ids Op OpAux Syn Unt.
End NormFbyFun.
