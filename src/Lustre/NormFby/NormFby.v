From Coq Require Import List Sorting.Permutation.
Import List.ListNotations.
Open Scope list_scope.

From Velus Require Import Common Environment.
From Velus Require Import CommonTyping.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Lustre.StaticEnv.
From Velus Require Import Lustre.LSyntax.
From Velus Require Fresh.
From Velus Require Import Lustre.SubClock.SubClock.

(** * Putting FBYs into normalized form *)

Module Type NORMFBY
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks : CLOCKS Ids Op OpAux)
       (Import Senv : STATICENV Ids Op OpAux Cks)
       (Import Syn : LSYNTAX Ids Op OpAux Cks Senv).

  Module Fresh := Fresh.Fresh(Ids).
  Import Fresh Fresh.Notations Facts Tactics.
  Local Open Scope fresh_monad_scope.

  Module Import SC := SubClockFun Ids Op OpAux Cks Senv Syn.

  Open Scope bool_scope.

  Lemma fby_not_in_last_prefs :
    ~PS.In fby_id last_prefs.
  Proof.
    unfold last_prefs, norm1_prefs, local_prefs, switch_prefs, auto_prefs, last_prefs, elab_prefs.
    rewrite ? PSF.add_iff, PSF.singleton_iff.
    pose proof gensym_prefs_NoDup as Hnd. unfold gensym_prefs in Hnd.
    repeat rewrite NoDup_cons_iff in Hnd. destruct_conjs.
    intros Eq. repeat take (_ \/ _) and destruct it as [Eq|Eq]; eauto 8 with datatypes.
  Qed.

  Definition FreshAnn A := Fresh fby_id A (type * clock).

  (** Generate an init equation for a given clock `cl`; if the init equation for `cl` already exists,
      just return the variable *)
  Definition init_var_for_clock (ck : clock) : FreshAnn (ident * list equation) :=
    fun st => let (x, st') := fresh_ident None ((OpAux.bool_velus_type, ck)) st in
           ((x, [([x], [Efby [add_whens (Eenum 1 bool_velus_type) bool_velus_type ck]
                             [add_whens (Eenum 0 bool_velus_type) bool_velus_type ck]
                             [(bool_velus_type, ck)]])]), st').

  Fixpoint is_constant (e : exp) : bool :=
    match e with
    | Econst _ | Eenum _ _ => true
    | Ewhen [e] _ _ ([ty], _) => is_constant e
    | _ => false
    end.

  Definition init_type (ty : type) :=
    match ty with
    | Tprimitive cty => Econst (init_ctype cty)
    | Tenum _ _ => Eenum 0 ty
    end.

  (** Generate a if-then-else equation for (0 fby e), and return an expression using it *)
  Definition fby_iteexp (e0 : exp) (e : exp) (ann : ann) : FreshAnn (exp * list equation) :=
    let '(ty, ck) := ann in
    do (initid, eqs) <- init_var_for_clock ck;
    do px <- fresh_ident None (ty, ck);
    ret (Ecase (Evar initid (bool_velus_type, ck))
               [(1, [e0]); (0, [Evar px (ty, ck)])] None ([ty], ck),
         ([px], [Efby [add_whens (init_type ty) ty ck] [e] [ann]])::eqs).

  Definition arrow_iteexp (e0 : exp) (e : exp) (ann : ann) : FreshAnn (exp * list equation) :=
    let '(ty, ck) := ann in
    do (initid, eqs) <- init_var_for_clock ck;
    ret (Ecase (Evar initid (bool_velus_type, ck)) [(1, [e0]); (0, [e])] None
              ([ty], ck), eqs).

  Definition normfby_equation (to_cut : PS.t) (eq : equation) : FreshAnn (list equation) :=
    match eq with
    | ([x], [Efby [e0] [e] [ann]]) =>
      let '(ty, ck) := ann in
      if is_constant e0 then
        if PS.mem x to_cut then
          do x' <- fresh_ident None (ty, ck);
          ret [([x], [Evar x' ann]); ([x'], [Efby [e0] [e] [ann]])]
        else ret [eq]
      else
        do (fby, eqs) <- fby_iteexp e0 e ann; ret (([x], [fby])::eqs)
    | ([x], [Earrow [e0] [e] [ann]]) =>
      do (ite, eqs) <- arrow_iteexp e0 e ann;
      ret (([x], [ite])::eqs)
    | _ => ret [eq]
    end.

  Fixpoint normfby_block (to_cut : PS.t) (d : block) : FreshAnn (list block) :=
    match d with
    | Beq eq =>
      do eq' <- normfby_equation to_cut eq;
      ret (map Beq eq')
    | Breset [d] (Evar x (ty, ckr)) =>
      do blocks' <- normfby_block to_cut d;
      ret (map (fun d => Breset [d] (Evar x (ty, ckr))) blocks')
    | _ => ret [d]
    end.

  Definition normfby_blocks (to_cut : PS.t) (blocks : list block) : FreshAnn (list block) :=
    do blocks' <- mmap (normfby_block to_cut) blocks;
    ret (concat blocks').

  (** Some initial properties *)

  Local Ltac destruct_to_singl l :=
    destruct l; [|destruct l]; auto.

  Fact normfby_equation_spec : forall to_cut xs es,
      (exists x e0 e ann,
          xs = [x] /\
          es = [Efby [e0] [e] [ann]] /\
          is_constant e0 = true /\
          normfby_equation to_cut (xs, es) =
          (let '(ty, ck) := ann in
           if PS.mem x to_cut then
             do x' <- fresh_ident None (ty, ck);
             ret [([x], [Evar x' ann]); ([x'], es)]
           else ret [(xs, es)]))
      \/ (exists x e0 e ann,
          xs = [x] /\
          es = [Efby [e0] [e] [ann]] /\
          is_constant e0 = false /\
          normfby_equation to_cut (xs, es) =
          (do (fby, eqs) <- fby_iteexp e0 e ann;
           ret (([x], [fby])::eqs)))
      \/ (exists x e0 e ann,
            xs = [x] /\
            es = [Earrow [e0] [e] [ann]] /\
            normfby_equation to_cut (xs, es) =
            (do (ite, eqs) <- arrow_iteexp e0 e ann;
             ret (([x], [ite])::eqs)))
      \/ normfby_equation to_cut (xs, es) = (ret [(xs, es)]).
  Proof.
    intros *.
    destruct_to_singl xs. destruct_to_singl es.
    2: { repeat right; simpl. destruct e; auto.
         1,2:(destruct_to_singl l; destruct_to_singl l0; destruct_to_singl l1).
    }
    destruct e; auto.
    1,2:destruct_to_singl l; destruct_to_singl l0; destruct_to_singl l1; simpl.
    - (* fby *)
      destruct a as [ty ck].
      destruct (is_constant e) eqn:Hconst; simpl.
      + left. repeat eexists; eauto.
      + right; left. repeat eexists; eauto.
    - (* arrow *)
      destruct a as [ty ck]. right; right; left.
      repeat eexists; eauto.
  Qed.

  Ltac inv_normfby_equation Hfby to_cut eq :=
    let Hspec := fresh "Hspec" in
    let Hconst := fresh "Hconst" in
    let Hr := fresh "Hr" in
    destruct eq as [xs es];
    specialize (normfby_equation_spec to_cut xs es) as
        [(?&?&?&?&?&?&Hconst&Hspec)|[(?&?&?&?&?&?&Hconst&Hspec)|[(?&?&?&?&?&?&Hspec)|Hspec]]];
    subst; rewrite Hspec in Hfby; clear Hspec; repeat inv_bind; auto.

  (** *** Preservation of st_follows *)

  Fact init_var_for_clock_st_follows : forall ck res st st',
      init_var_for_clock ck st = (res, st') ->
      st_follows st st'.
  Proof.
    intros * Hinit.
    unfold init_var_for_clock in Hinit.
    repeat inv_bind.
    destruct (fresh_ident _ _) eqn:Hfresh. inv Hinit.
    apply fresh_ident_st_follows in Hfresh. auto.
  Qed.
  Global Hint Resolve init_var_for_clock_st_follows : norm.

  Fact fby_iteexp_st_follows : forall e0 e ann res st st',
      fby_iteexp e0 e ann st = (res, st') ->
      st_follows st st'.
  Proof.
    intros e0 e [ty ck] res st st' Hfby.
    unfold fby_iteexp in Hfby; repeat inv_bind.
    etransitivity; eauto with fresh norm.
  Qed.
  Global Hint Resolve fby_iteexp_st_follows : norm.

  Fact arrow_iteexp_st_follows : forall e0 e ann res st st',
      arrow_iteexp e0 e ann st = (res, st') ->
      st_follows st st'.
  Proof.
    intros e0 e [ty ck] res st st' Hfby.
    unfold arrow_iteexp in Hfby.
    repeat inv_bind; eauto with norm.
  Qed.
  Global Hint Resolve arrow_iteexp_st_follows : norm.

  Fact normfby_equation_st_follows : forall to_cut eq eqs' st st',
      normfby_equation to_cut eq st = (eqs', st') ->
      st_follows st st'.
  Proof.
    intros * Hfby.
    inv_normfby_equation Hfby to_cut eq.
    - destruct x2 as [ty ck].
      destruct (PS.mem _ _); repeat inv_bind.
      + eauto using fresh_ident_st_follows.
      + reflexivity.
    - eapply fby_iteexp_st_follows; eauto.
    - eapply arrow_iteexp_st_follows; eauto.
    - reflexivity.
  Qed.
  Global Hint Resolve normfby_equation_st_follows : norm.

  Fact normfby_block_st_follows : forall to_cut d blocks' st st',
      normfby_block to_cut d st = (blocks', st') ->
      st_follows st st'.
  Proof.
    induction d using block_ind2; intros * Hfby; simpl in Hfby; repeat inv_bind; try reflexivity.
    - eapply normfby_equation_st_follows; eauto.
    - cases; repeat inv_bind; try reflexivity.
      inv H; eauto.
  Qed.
  Global Hint Resolve normfby_block_st_follows : norm.

  (** *** The variables generated are a permutation of the ones contained in the state *)

  Fact init_var_for_clock_vars_perm : forall ck id eqs st st',
      init_var_for_clock ck st = ((id, eqs), st') ->
      Permutation (flat_map fst eqs++st_ids st) (st_ids st').
  Proof.
    intros * Hinit.
    unfold init_var_for_clock in Hinit. repeat inv_bind.
    destruct (fresh_ident _ _) eqn:Hfresh. inv Hinit.
    apply fresh_ident_vars_perm in Hfresh.
    simpl. assumption.
  Qed.

  Fact fby_iteexp_vars_perm : forall e0 e ann e' eqs' st st',
      fby_iteexp e0 e ann st = (e', eqs', st') ->
      Permutation (flat_map fst eqs'++st_ids st) (st_ids st').
  Proof.
    intros ? ? [ty ck] ? ? ? ? Hfby.
    unfold fby_iteexp in Hfby. repeat inv_bind.
    eapply init_var_for_clock_vars_perm in H; eauto.
    eapply fresh_ident_vars_perm in H0.
    simpl.
    rewrite <- H0. apply perm_skip; auto.
  Qed.

  Fact arrow_iteexp_vars_perm : forall e0 e ann e' eqs' st st',
      arrow_iteexp e0 e ann st = (e', eqs', st') ->
      Permutation (flat_map fst eqs'++st_ids st) (st_ids st').
  Proof.
    intros ? ? [ty ck] ? ? ? ? Hfby.
    unfold arrow_iteexp in Hfby. repeat inv_bind.
    eapply init_var_for_clock_vars_perm in H; eauto.
  Qed.

  Fact normfby_equation_vars_perm : forall to_cut eq eqs' st st',
      normfby_equation to_cut eq st = (eqs', st') ->
      Permutation (flat_map fst eqs'++st_ids st) (fst eq++st_ids st').
  Proof.
    intros * Hfby.
    inv_normfby_equation Hfby to_cut eq.
    destruct x2 as [ty ck]; repeat inv_bind.
    - destruct PS.mem; repeat inv_bind; simpl; auto.
      eapply fresh_ident_vars_perm in H.
      apply perm_skip; auto.
    - simpl. apply perm_skip.
      eapply fby_iteexp_vars_perm in H; eauto.
    - eapply arrow_iteexp_vars_perm in H; simpl; auto.
    - simpl; rewrite app_nil_r; auto.
  Qed.

  Lemma normfby_block_vars_perm : forall G blk blks' xs st st',
      VarsDefinedComp blk xs ->
      normfby_block G blk st = (blks', st') ->
      exists ys, Forall2 VarsDefinedComp blks' ys /\ Permutation (concat ys ++ st_ids st) (xs ++ st_ids st').
  Proof.
    induction blk using block_ind2; intros * Hvars Hun; inv Hvars; repeat inv_bind.
    - exists (map fst x). split.
      + simpl_Forall. constructor.
      + eapply normfby_equation_vars_perm in H. now rewrite flat_map_concat_map in H.
    - exists [[]]. repeat constructor; auto.
    - simpl in Hun. cases; repeat inv_bind.
      1-3,5-15:(exists [(concat xs0)]; simpl; rewrite app_nil_r; split; auto; repeat constructor; auto).
      inv H; inv H5. inv H3; inv H6.
      eapply H4 in H0 as (ys1&Hvars1&Hperm1); eauto.
      exists ys1. simpl; rewrite app_nil_r. split; auto.
      rewrite Forall2_map_1.
      eapply Forall2_impl_In; [|eauto]; intros.
      replace b0 with (concat [b0]) by (simpl; now rewrite app_nil_r).
      repeat constructor; auto.
    - exists [xs]. split; try constructor; auto.
      + econstructor; eauto.
      + simpl; rewrite app_nil_r; auto.
    - exists [xs]. split; try constructor; auto.
      + econstructor; eauto.
      + simpl; rewrite app_nil_r; auto.
    - exists [xs]. split; try constructor; auto.
      + econstructor; eauto.
      + simpl; rewrite app_nil_r; auto.
  Qed.

  Fact mmap_vars_perm {A} pref : forall (f : block -> Fresh pref (list block) A) blks blks' xs st st',
      Forall
        (fun blk => forall blks' xs st st',
             VarsDefinedComp blk xs -> f blk st = (blks', st') ->
             exists ys, Forall2 VarsDefinedComp blks' ys /\ Permutation (concat ys ++ st_ids st) (xs ++ st_ids st')) blks ->
      Forall2 VarsDefinedComp blks xs ->
      mmap f blks st = (blks', st') ->
      exists ys, Forall2 VarsDefinedComp (concat blks') ys /\ Permutation (concat ys ++ st_ids st) (concat xs ++ st_ids st').
  Proof.
    induction blks; intros * Hf Hvars Hnorm; inv Hf; inv Hvars; repeat inv_bind; simpl.
    - exists []. split; auto.
    - eapply H1 in H as (ys1&Hvars1&Hperm1); eauto.
      eapply IHblks in H2 as (ys2&Hvars2&Hperm2); eauto. clear IHblks.
      exists (ys1 ++ ys2). split.
      + apply Forall2_app; auto.
      + rewrite <-app_assoc, <-Hperm2, Permutation_swap, <-Hperm1, Permutation_swap.
        now rewrite concat_app, <-app_assoc.
  Qed.

  Corollary normfby_blocks_vars_perm : forall G blks blks' xs st st',
      Forall2 VarsDefinedComp blks xs ->
      normfby_blocks G blks st = (blks', st') ->
      exists ys, Forall2 VarsDefinedComp blks' ys /\ Permutation (concat ys ++ st_ids st) (concat xs ++ st_ids st').
  Proof.
    intros * Hvars Hun. unfold normfby_blocks in Hun. repeat inv_bind.
    eapply mmap_vars_perm; [|eauto|eauto].
    simpl_Forall. eapply normfby_block_vars_perm; eauto.
  Qed.

  (** *** LastsDefined *)

  Lemma normfby_block_lasts_perm : forall G blk blks' xs st st',
      LastsDefined blk xs ->
      normfby_block G blk st = (blks', st') ->
      exists ys, Forall2 LastsDefined blks' ys /\ Permutation (concat ys) xs.
  Proof.
    induction blk using block_ind2; intros * Hvars Hun; inv Hvars; repeat inv_bind.
    - exists (map (fun _ => []) x). split.
      + simpl_Forall. constructor.
      + rewrite concat_map_nil. auto.
    - exists [[x]]. repeat constructor; auto.
    - simpl in Hun. cases; repeat inv_bind.
      all:simpl_Forall; try now do 2 esplit; [repeat (constructor; eauto)|simpl; try rewrite app_nil_r; auto].
      rewrite app_nil_r.
      eapply H4 in H0 as (?&Last&Perm); eauto.
      do 2 esplit.
      + simpl_Forall. erewrite Forall2_map_2. instantiate (1:=x0). simpl_Forall.
        repeat constructor; eauto.
      + simpl. setoid_rewrite app_nil_r. now rewrite map_id.
    - exists [[]]. repeat constructor; auto.
    - exists [[]]. repeat constructor; auto.
    - exists [xs]. repeat (constructor; auto).
      simpl; rewrite app_nil_r; auto.
  Qed.

  Fact mmap_lasts_perm {A} pref : forall (f : block -> Fresh pref (list block) A) blks blks' xs st st',
      Forall
        (fun blk => forall blks' xs st st',
             LastsDefined blk xs -> f blk st = (blks', st') ->
             exists ys, Forall2 LastsDefined blks' ys /\ Permutation (concat ys) xs) blks ->
      Forall2 LastsDefined blks xs ->
      mmap f blks st = (blks', st') ->
      exists ys, Forall2 LastsDefined (concat blks') ys /\ Permutation (concat ys) (concat xs).
  Proof.
    induction blks; intros * Hf Hvars Hnorm; inv Hf; inv Hvars; repeat inv_bind; simpl.
    - exists []. split; auto.
    - eapply H1 in H as (ys1&Hvars1&Hperm1); eauto.
      eapply IHblks in H2 as (ys2&Hvars2&Hperm2); eauto. clear IHblks.
      exists (ys1 ++ ys2). split.
      + apply Forall2_app; auto.
      + rewrite concat_app, Hperm1, Hperm2; auto.
  Qed.

  Corollary normfby_blocks_lasts_perm : forall G blks blks' xs st st',
      Forall2 LastsDefined blks xs ->
      normfby_blocks G blks st = (blks', st') ->
      exists ys, Forall2 LastsDefined blks' ys /\ Permutation (concat ys) (concat xs).
  Proof.
    intros * Hvars Hun. unfold normfby_blocks in Hun. repeat inv_bind.
    eapply mmap_lasts_perm; [|eauto|eauto].
    simpl_Forall. eapply normfby_block_lasts_perm; eauto.
  Qed.

  (** *** Additional props *)

  Fact init_var_for_clock_In : forall ck id eqs' st st',
      init_var_for_clock ck st = (id, eqs', st') ->
      In (id, (bool_velus_type, ck)) (st_anns st').
  Proof.
    intros * Hinit.
    unfold init_var_for_clock in Hinit.
    destruct (fresh_ident _ _) eqn:Hfresh. inv Hinit.
    eapply fresh_ident_In in Hfresh; eauto.
  Qed.

  (** ** equations and blocks are normalized *)

  Fact add_whens_is_constant : forall ty ck e,
      normalized_constant e ->
      normalized_constant (add_whens e ty ck).
  Proof.
    induction ck; intros e Hcons; simpl.
    - assumption.
    - destruct p. constructor. eauto.
  Qed.

  Fact add_whens_normalized_lexp : forall ty ck e,
      normalized_lexp e ->
      normalized_lexp (add_whens e ty ck).
  Proof.
    induction ck; intros e Hadd; simpl in Hadd.
    - assumption.
    - destruct p. constructor. eauto.
  Qed.

  Fact is_constant_normalized_constant : forall e,
      is_constant e = true <->
      normalized_constant e.
  Proof with eauto.
    intros e. split; intros Hconst.
    - induction e using exp_ind2; simpl in Hconst; try congruence.
      + constructor.
      + constructor.
      + repeat (destruct es; try congruence).
        inv H; inv H3.
        destruct a.
        repeat (destruct l; try congruence).
        constructor...
    - induction Hconst...
  Qed.

  Fact init_var_for_clock_normalized_eq : forall ck id eqs' out lasts st st',
      Forall (AtomOrGensym last_prefs) out ->
      Forall (AtomOrGensym last_prefs) lasts ->
      init_var_for_clock ck st = (id, eqs', st') ->
      Forall (normalized_equation out lasts) eqs'.
  Proof.
    intros * Hat1 Hat2 Hinit.
    unfold init_var_for_clock in Hinit.
    destruct (fresh_ident _ _) eqn:Hfresh. inv Hinit.
    repeat constructor.
    - apply add_whens_is_constant; auto with norm.
    - apply add_whens_normalized_lexp; auto with norm.
    - eapply fresh_ident_nIn' with (aft:=out0) in Hfresh; eauto using fby_not_in_last_prefs.
    - eapply fresh_ident_nIn' with (aft:=lasts) in Hfresh; eauto using fby_not_in_last_prefs.
  Qed.

  Fact normfby_equation_normalized_eq : forall lasts out to_cut eq eqs' st st',
      Forall (AtomOrGensym last_prefs) out ->
      Forall (AtomOrGensym last_prefs) lasts ->
      unnested_equation lasts eq ->
      (forall x, In x out -> PS.In x to_cut) ->
      normfby_equation to_cut eq st = (eqs', st') ->
      Forall (normalized_equation out lasts) eqs'.
  Proof with eauto with norm.
    intros * Hat1 Hat2 Hunt Hsub Hfby.
    inv Hunt; simpl in *; repeat inv_bind; eauto.
    1:destruct_to_singl xs; repeat inv_bind...
    - (* fby *)
      (destruct ann0 as (?&?); destruct (is_constant e0) eqn:Hconst;
       [apply is_constant_normalized_constant in Hconst;
        destruct PS.mem eqn:Hmem; [|apply PSE.mem_4 in Hmem]|]; repeat inv_bind).
      1-3:repeat constructor...
      3,4:repeat esplit...
      + eapply fresh_ident_nIn' in H2; eauto using fby_not_in_last_prefs.
      + eapply fresh_ident_nIn' in H2; eauto using fby_not_in_last_prefs.
      + intros * ?. congruence.
      + apply add_whens_is_constant; destruct t; simpl...
      + eapply fresh_ident_nIn' in H3; eauto using fby_not_in_last_prefs.
      + eapply fresh_ident_nIn' in H3; eauto using fby_not_in_last_prefs.
      + eapply init_var_for_clock_normalized_eq; eauto.
    - (* arrow *)
      destruct ann0 as (?&?) eqn:Vars; repeat inv_bind.
      repeat constructor; eauto.
      1-2:repeat esplit; eauto...
      intros ??; congruence.
      eapply init_var_for_clock_normalized_eq; eauto.
    - (* extapp *)
      repeat econstructor; eauto.
    - (* cexp *)
      inv H; repeat inv_bind; auto...
      inv H0; repeat inv_bind; auto...
  Qed.

  Fact normfby_block_normalized_block : forall out lasts to_cut d blocks' st st',
      Forall (AtomOrGensym last_prefs) out ->
      Forall (AtomOrGensym last_prefs) lasts ->
      normlast_block lasts d ->
      (forall x, In x out -> PS.In x to_cut) ->
      normfby_block to_cut d st = (blocks', st') ->
      Forall (normalized_block out lasts) blocks'.
  Proof.
    induction d using block_ind2; intros * Hat1 Hat2 Hun Hsub Hfby; inv Hun;
      simpl in Hfby; try destruct ann0; repeat inv_bind.
    - eapply normfby_equation_normalized_eq with (out:=out0) in H; eauto.
      simpl_Forall; eauto with norm.
    - repeat constructor; auto.
    - apply Forall_singl in H.
      apply H in H0; auto.
      simpl_Forall; eauto with norm.
  Qed.

  Corollary normfby_blocks_normalized_block : forall out lasts to_cut blocks blocks' st st',
      Forall (AtomOrGensym last_prefs) out ->
      Forall (AtomOrGensym last_prefs) lasts ->
      Forall (normlast_block lasts) blocks ->
      (forall x, In x out -> PS.In x to_cut) ->
      normfby_blocks to_cut blocks st = (blocks', st') ->
      Forall (normalized_block out lasts) blocks'.
  Proof.
    induction blocks; intros * Hat1 Hat2 Hunt Hsub Hfby;
      unfold normfby_blocks in Hfby; repeat inv_bind; simpl; auto.
    inv Hunt.
    eapply Forall_app; split.
    - eapply normfby_block_normalized_block in H; eauto.
    - eapply IHblocks with (st:=x1) (st':=st'); eauto.
      unfold normfby_blocks; repeat inv_bind; eauto.
  Qed.

  (** *** GoodLocals *)

  Lemma normfby_block_GoodLocals to_cut : forall prefs blk blk' st st',
      GoodLocals prefs blk ->
      normfby_block to_cut blk st = (blk', st') ->
      Forall (GoodLocals prefs) blk'.
  Proof.
    induction blk using block_ind2; intros * Hgood Hun; inv Hgood; repeat inv_bind.
    - (* equation *)
      simpl_Forall. constructor.
    - (* last *)
      repeat constructor.
    - (* reset *)
      simpl in Hun. cases; repeat inv_bind; repeat (constructor; auto).
      apply Forall_singl in H. apply Forall_singl in H1.
      rewrite Forall_map. eapply Forall_impl; [|eauto]. intros ??. constructor; auto.
    - do 2 (constructor; auto).
    - do 2 (constructor; auto).
    - do 2 (constructor; auto).
  Qed.

  Corollary normfby_blocks_GoodLocals to_cut : forall prefs blks blks' st st',
      Forall (GoodLocals prefs) blks ->
      normfby_blocks to_cut blks st = (blks', st') ->
      Forall (GoodLocals prefs) blks'.
  Proof.
    intros * Hgood Hun.
    unfold normfby_blocks in Hun. repeat inv_bind.
    eapply mmap_values, Forall2_ignore1 in H.
    eapply Forall_concat. rewrite Forall_forall in *; intros.
    specialize (H _ H0) as (?&Hinblk&?&?&Hun); eauto.
    eapply normfby_block_GoodLocals; eauto.
  Qed.

  Lemma normfby_block_NoDupLocals G env : forall blk blks' st st',
      NoDupLocals env blk ->
      normfby_block G blk st = (blks', st') ->
      Forall (NoDupLocals env) blks'.
  Proof.
    induction blk using block_ind2; intros * Hnd Hun; repeat inv_bind; auto.
    - (* equation *)
      inv Hnd.
      simpl_Forall. constructor.
    - (* reset *)
      unfold normfby_block in Hun.
      cases; repeat inv_bind; auto.
      inv Hnd. apply Forall_singl in H3. apply Forall_singl in H.
      rewrite Forall_map. eapply H in H0; eauto.
      simpl_Forall. constructor; auto.
  Qed.

  Fact mmap_NoDupLocals {pref A} (f : block -> Fresh pref (list block) A) env : forall blks blks' st st',
      Forall (fun blk => forall blks' st st',
                  NoDupLocals env blk ->
                  f blk st = (blks', st') -> Forall (NoDupLocals env) blks') blks ->
      Forall (NoDupLocals env) blks ->
      mmap f blks st = (blks', st') ->
      Forall (NoDupLocals env) (concat blks').
  Proof.
    induction blks; intros * Hf Hnd Hmap; inv Hf; inv Hnd;
      repeat inv_bind; simpl; auto.
    apply Forall_app; split; eauto.
  Qed.

  Corollary normfby_blocks_NoDupLocals G env : forall blks blks' st st',
      Forall (NoDupLocals env) blks ->
      normfby_blocks G blks st = (blks', st') ->
      Forall (NoDupLocals env) blks'.
  Proof.
    intros * Hnd Hun. unfold normfby_blocks in Hun; repeat inv_bind.
    eapply mmap_NoDupLocals in H; eauto.
    eapply Forall_forall; intros.
    eapply normfby_block_NoDupLocals; eauto.
  Qed.

  (** ** Normalization of a full node *)

  Program Definition normfby_node (n : @node normlast last_prefs) : @node normalized fby_prefs :=
    {| n_name := n_name n;
       n_hasstate := n_hasstate n;
       n_in := n_in n;
       n_out := n_out n;
       n_block := match (n_block n) with
                  | Blocal (Scope vars blks) =>
                    let res := normfby_blocks (ps_from_list (map fst (n_out n))) blks init_st in
                    let nvars := st_anns (snd res) in
                    Blocal (Scope (vars++map (fun xtc => (fst xtc, ((fst (snd xtc)), snd (snd xtc), xH, None))) nvars) (fst res))
                  | blk => blk
                  end;
       n_ingt0 := n_ingt0 n;
       n_outgt0 := n_outgt0 n;
    |}.
  Next Obligation.
    pose proof (n_good n) as (Hgood1&Hgood&_).
    pose proof (n_syn n) as Syn. inversion Syn as [??? Syn1 Syn2 (?&Hvars&Hperm)]; rewrite <-H0 in *; subst; clear Syn.
    inv Hvars. repeat inv_scope.
    destruct (normfby_blocks _ _) as (blks'&st') eqn:Heqs.
    do 2 esplit; [|eauto].
    eapply noswitch_VarsDefinedComp_VarsDefined.
    1:{ constructor.
        eapply normfby_blocks_normalized_block with (out:=[]) (lasts:=lasts_of_decls _) in Heqs; eauto.
        + simpl_Forall; eauto using normalized_normlast, normlast_unnested, unnested_nolocal, nolocal_noswitch.
        + inv Hgood. inv_scope.
          unfold lasts_of_decls. simpl_Forall. simpl_In. simpl_Forall. auto.
        + intros * []. }
    eapply normfby_blocks_vars_perm in Heqs as (ys&Hvars&Hperm'); eauto.
    constructor. econstructor; eauto using incl_nil'.
    unfold st_ids in *. rewrite init_st_anns, app_nil_r in Hperm'. simpl.
    do 2 esplit; eauto. rewrite Hperm', H1, Hperm, map_app, <-app_assoc, map_fst_senv_of_decls.
    apply Permutation_app_head, Permutation_app_head.
    rewrite map_map; reflexivity.
  Qed.
  Next Obligation.
    pose proof (n_lastd n) as (?&Last&Perm).
    pose proof (n_syn n) as Syn. inversion Syn as [??? _ Syn2 _]; rewrite <-H0 in *; clear Syn.
    inv Last. inv_scope.
    destruct (normfby_blocks _ _) as (blks'&st') eqn:Heqs.
    do 2 esplit; [|eauto].
    repeat constructor.
    eapply normfby_blocks_lasts_perm in Heqs as (?&Last'&Perm'); eauto.
    do 2 esplit; eauto.
    rewrite Perm', H1.
    unfold lasts_of_decls. rewrite map_filter_app, map_filter_nil with (xs:=map _ _), app_nil_r; auto.
    simpl_Forall; auto.
  Qed.
  Next Obligation.
    pose proof (n_good n) as (Hgood1&Hgood&_).
    pose proof (n_nodup n) as (Hndup&Hndl).
    destruct (n_block n) as [| | | | |[locs blks]] eqn:Hblk; eauto.
    destruct (normfby_blocks _ blks init_st) as (blks'&st') eqn:Hunn.
    repeat rewrite app_nil_r. split; simpl in *; auto.
    inv Hndl. inv H1.
    do 2 constructor; simpl.
    - eapply normfby_blocks_NoDupLocals; [|eauto].
      inv Hgood. inv H0. simpl_Forall.
      eapply NoDupLocals_incl' with (npref:=fby_id). 1,2,4:eauto using fby_not_in_last_prefs.
      assert (Forall (fun id => exists x hint, id = gensym fby_id hint x) (st_ids st')) as Hids.
      { eapply st_valid_prefixed; eauto. }
      intros ? Hin. repeat rewrite map_app in *. repeat rewrite in_app_iff in *. destruct Hin as [[?|Hin]|[Hin|Hin]]; auto.
      rewrite map_map in Hin. eapply Forall_forall in Hids; eauto.
    - apply NoDupMembers_app; auto.
      + specialize (st_valid_NoDup st') as Hvalid. unfold st_ids in Hvalid.
        erewrite fst_NoDupMembers, map_map, map_ext; eauto.
      + intros * Hinm1 Hinm2. rewrite fst_InMembers in Hinm1, Hinm2. simpl_In.
        inv Hgood. take (GoodLocalsScope _ _ _) and inv it. simpl_Forall; subst.
        eapply st_valid_AtomOrGensym_nIn; eauto using fby_not_in_last_prefs.
        unfold st_ids. solve_In.
    - setoid_rewrite InMembers_app. intros * [Hinm|Hinm] Hin'.
      + eapply H5; eauto using in_or_app.
      + simpl_Forall. rewrite fst_InMembers in Hinm. simpl_In.
        eapply st_valid_AtomOrGensym_nIn; eauto using fby_not_in_last_prefs.
        unfold st_ids. solve_In.
  Qed.
  Next Obligation.
    specialize (n_good n) as (Hgood1&Hgood2&Hname). repeat split; eauto using Forall_AtomOrGensym_add.
    destruct (n_block n) as [| | | | |[locs blks]] eqn:Hblk; eauto using GoodLocals_add.
    destruct (normfby_blocks _ blks init_st) as (blks'&st') eqn:Heqres.
    inv Hgood2. inv H0.
    do 2 constructor.
    + repeat rewrite map_app. repeat rewrite Forall_app. repeat split; eauto using Forall_AtomOrGensym_add.
      specialize (st_valid_prefixed st') as Hvalid.
      unfold st_ids in Hvalid. simpl_Forall; subst.
      right. do 2 esplit; eauto. now apply PSF.add_1.
    + eapply normfby_blocks_GoodLocals in H3; eauto.
      simpl_Forall; eauto using GoodLocals_add.
  Qed.
  Next Obligation.
    specialize (n_good n) as (Hgood1&Hgood2&_).
    pose proof (n_syn n) as Hsyn. inversion Hsyn as [??? Syn1 Syn2 (?&Hvars&Hperm)]; rewrite <-H0 in *; subst; clear Hsyn.
    inv Hvars. inv_scope.
    repeat constructor; auto.
    - eapply normfby_blocks_normalized_block. 5:eauto using surjective_pairing.
      + apply Forall_app in Hgood1 as (?&?); auto.
      + unfold lasts_of_decls. rewrite map_filter_app, map_filter_nil with (xs:=map _ _).
        2:simpl_Forall; auto.
        inv Hgood2. inv_scope. simpl_Forall. simpl_In. simpl_Forall. auto.
      + simpl_Forall.
        unfold lasts_of_decls. rewrite map_filter_app, map_filter_nil with (xs:=map _ _), app_nil_r; auto.
        simpl_Forall; auto.
      + intros * In. apply ps_from_list_In; auto.
    - do 2 esplit; eauto.
      destruct (normfby_blocks _ _) as (blks'&st') eqn:Heqs.
      eapply normfby_blocks_vars_perm in Heqs as (ys&Hvars'&Hperm'); eauto.
      constructor. econstructor; eauto using incl_nil'.
      unfold st_ids in *. rewrite init_st_anns, app_nil_r in Hperm'. simpl.
      do 2 esplit; eauto. rewrite Hperm', H1, map_app, <-app_assoc.
      apply Permutation_app_head, Permutation_app_head.
      rewrite map_map; reflexivity.
  Qed.

  Global Program Instance normfby_node_transform_unit: TransformUnit node node :=
    { transform_unit := normfby_node }.

  Global Program Instance normfby_global_without_units : TransformProgramWithoutUnits (@global normlast last_prefs) (@global normalized fby_prefs) :=
    { transform_program_without_units := fun g => Global g.(types) g.(externs) [] }.

  Definition normfby_global : @global normlast last_prefs -> @global normalized fby_prefs := transform_units.

  (** *** normfby_global produces an equivalent global *)

  Fact normfby_global_eq : forall G,
      global_iface_eq G (normfby_global G).
  Proof.
    repeat split; auto.
    intros f. unfold find_node.
    destruct (find_unit f G) as [(?&?)|] eqn:Hfind; simpl.
    - setoid_rewrite find_unit_transform_units_forward; eauto.
      simpl. repeat constructor.
    - destruct (find_unit f (normfby_global G)) as [(?&?)|] eqn:Hfind'; simpl; try constructor.
      eapply find_unit_transform_units_backward in Hfind' as (?&?&?&?); congruence.
  Qed.

  Fact normfby_nodes_names {PSyn prefs} : forall (a : @node PSyn prefs) nds,
      Forall (fun n => (n_name a <> n_name n)%type) nds ->
      Forall (fun n => (n_name a <> n_name n)%type) (map normfby_node nds).
  Proof.
    induction nds; intros * Hnames; simpl.
    - constructor.
    - inv Hnames.
      constructor; eauto.
  Qed.

  (** *** Preservation of normal_args *)

  Fact init_var_for_clock_normal_args {PSyn prefs} : forall (G : @global PSyn prefs) ck id eqs' st st',
      init_var_for_clock ck st = (id, eqs', st') ->
      Forall (normal_args_eq G) eqs'.
  Proof.
    intros * Hinit.
    unfold init_var_for_clock in Hinit.
    destruct (fresh_ident _ _) eqn:Hfresh. inv Hinit.
    repeat constructor.
  Qed.

  Fact normfby_equation_normal_args {PSyn prefs} : forall (G : @global PSyn prefs) lasts to_cut eq eqs' st st',
      unnested_equation lasts eq ->
      normal_args_eq G eq ->
      normfby_equation to_cut eq st = (eqs', st') ->
      Forall (normal_args_eq G) eqs'.
  Proof with eauto with norm.
    intros * Hun Hnorm Hfby.
    inv Hnorm; simpl in *; repeat inv_bind; eauto.
    - (* app *)
      cases; repeat inv_bind; repeat econstructor; eauto.
    - (* fby *)
      (destruct ann0 as (?&?); destruct (is_constant e0) eqn:Hconst;
       [apply is_constant_normalized_constant in Hconst;
        destruct PS.mem eqn:Hmem; [|apply PSE.mem_4 in Hmem]|]; repeat inv_bind).
      1-3:repeat constructor...
      1,2:repeat esplit...
      + inv Hun; auto with norm. inv H2. inv H1.
      + intros * ?. congruence.
      + eapply init_var_for_clock_normal_args; eauto.
    - (* arrow *)
      destruct ann0 as (?&?) eqn:Vars; repeat inv_bind.
      repeat constructor; eauto.
      1-2:repeat esplit; eauto...
      1,2:inv Hun; auto with norm; inv H1; inv H0.
      + intros ??; congruence.
      + eapply init_var_for_clock_normal_args; eauto.
    - (* extapp *)
      repeat econstructor; eauto.
    - (* cexp *)
      inv H; repeat inv_bind; auto...
      1,2:repeat constructor; auto with norm.
      inv H0; repeat inv_bind; auto...
      all:repeat constructor; auto with norm.
  Qed.

  Fact normfby_block_normal_args {PSyn prefs} : forall (G : @global PSyn prefs) lasts to_cut blk blocks' st st',
      normlast_block lasts blk ->
      normal_args_blk G blk ->
      normfby_block to_cut blk st = (blocks', st') ->
      Forall (normal_args_blk G) blocks'.
  Proof.
    induction blk using block_ind2; intros * Hun Hnorm Hfby; inv Hun; inv Hnorm;
      simpl in Hfby; try destruct ann0; repeat inv_bind.
    - eapply normfby_equation_normal_args in H; eauto.
      simpl_Forall. constructor; eauto with norm.
    - repeat constructor; auto.
    - apply Forall_singl in H. apply Forall_singl in H2.
      apply H in H0; auto.
      simpl_Forall; constructor; auto.
  Qed.

  Corollary normfby_blocks_normal_args {PSyn prefs} : forall (G : @global PSyn prefs) lasts to_cut blocks blocks' st st',
      Forall (normlast_block lasts) blocks ->
      Forall (normal_args_blk G) blocks ->
      normfby_blocks to_cut blocks st = (blocks', st') ->
      Forall (normal_args_blk G) blocks'.
  Proof.
    induction blocks; intros * Hun Hnorm Hfby;
      unfold normfby_blocks in Hfby; repeat inv_bind; simpl; auto.
    inv Hun. inv Hnorm.
    eapply Forall_app; split.
    - eapply normfby_block_normal_args in H; eauto.
    - eapply IHblocks with (st:=x1) (st':=st'); eauto.
      unfold normfby_blocks; repeat inv_bind; eauto.
  Qed.

  Fact normfby_node_normal_args : forall G n,
      normal_args_node G n ->
      normal_args_node (normfby_global G) (normfby_node n).
  Proof.
    intros * Hnorm.
    unfold normal_args_node, normfby_node in *. simpl.
    pose proof (n_syn n) as Syn. inversion Syn as [??? _ Syn2 _].
    inv Hnorm.
    constructor.
    eapply normfby_blocks_normal_args; eauto using surjective_pairing.
    simpl_Forall. eapply iface_eq_normal_args_blk; eauto using normfby_global_eq.
  Qed.

  Fact normfby_global_normal_args : forall G,
      normal_args G ->
      normal_args (normfby_global G).
  Proof.
    unfold normfby_global. destruct G.
    induction nodes0; intros * Hwl; constructor; auto.
    - simpl. inv Hwl. destruct_conjs.
      eapply normfby_node_normal_args in H1; eauto.
    - inv Hwl. apply IHnodes0; auto.
  Qed.

  Definition st_senv {pref} (st: fresh_st pref _) := senv_of_tyck (st_anns st).
  Global Hint Unfold st_senv senv_of_tyck : list.

  Lemma st_senv_senv_of_decls {pref} : forall (st : fresh_st pref _),
      st_senv st = senv_of_decls (map (fun xtc => (fst xtc, ((fst (snd xtc)), snd (snd xtc), xH, None))) (st_anns st)).
  Proof.
    intros.
    unfold st_senv, senv_of_decls, senv_of_tyck.
    repeat rewrite map_map. eapply map_ext. intros; destruct_conjs; auto.
  Qed.

  Ltac solve_st_follows :=
    match goal with
    | |- st_follows ?st ?st =>
      reflexivity
    | H : st_follows ?st1 ?st2 |- st_follows ?st1 _ =>
      etransitivity; [eapply H |]
    | H : fresh_ident _ _ ?st = _ |- st_follows ?st _ =>
      etransitivity; [ eapply fresh_ident_st_follows in H; eauto with norm | ]
    | H: mmap _ _ ?st = _ |- st_follows ?st _ =>
      etransitivity; [ eapply mmap_st_follows in H; eauto; simpl_Forall; eauto with norm |]
    | H : mmap2 _ _ ?st = _ |- st_follows ?st _ =>
      etransitivity; [ eapply mmap2_st_follows in H; eauto with norm; simpl_Forall; eauto with norm | ]
    end.

End NORMFBY.

Module NormFbyFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks : CLOCKS Ids Op OpAux)
       (Senv : STATICENV Ids Op OpAux Cks)
       (Syn : LSYNTAX Ids Op OpAux Cks Senv)
       <: NORMFBY Ids Op OpAux Cks Senv Syn.
  Include NORMFBY Ids Op OpAux Cks Senv Syn.
End NormFbyFun.
