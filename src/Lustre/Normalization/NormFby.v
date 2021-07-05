From Coq Require Import List Sorting.Permutation.
Import List.ListNotations.
Open Scope list_scope.
Require Import Omega.

From Velus Require Import Common Environment.
From Velus Require Import CommonTyping.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Lustre.LSyntax.
From Velus Require Lustre.Normalization.Fresh.
From Velus Require Import Lustre.Normalization.Unnesting.

(** * Putting FBYs into normalized form *)

Module Type NORMFBY
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks : CLOCKS Ids Op OpAux)
       (Import Syn : LSYNTAX Ids Op OpAux Cks)
       (Import Unt : UNNESTING Ids Op OpAux Cks Syn).

  Import Fresh Fresh.Notations Facts Tactics.
  Local Open Scope fresh_monad_scope.

  (** Add some whens on top of an expression *)
  Fixpoint add_whens (e : exp) (ty : type) (cl : clock) :=
    match cl with
    | Cbase => e
    | Con cl' ckid (_, b) => Ewhen [(add_whens e ty cl')] ckid b ([ty], (cl, None))
    end.

  Open Scope bool_scope.

  (** Generate an init equation for a given clock `cl`; if the init equation for `cl` already exists,
      just return the variable *)
  Definition init_var_for_clock (ck : clock) : FreshAnn (ident * list equation) :=
    fun st => let (x, st') := fresh_ident norm2 ((OpAux.bool_velus_type, ck)) st in
           ((x, [([x], [Efby [add_whens (Eenum 1 bool_velus_type) bool_velus_type ck]
                             [add_whens (Eenum 0 bool_velus_type) bool_velus_type ck]
                             [(bool_velus_type, (ck, None))]])]), st').

  Fixpoint is_constant (e : exp) : bool :=
    match e with
    | Econst _ | Eenum _ _ => true
    | Ewhen [e] _ _ ([ty], _) => is_constant e
    | _ => false
    end.

  Definition init_type (ty : type) :=
    match ty with
    | Tprimitive cty => Econst (init_ctype cty)
    | Tenum _ => Eenum 0 ty
    end.

  (** Generate a if-then-else equation for (0 fby e), and return an expression using it *)
  Definition fby_iteexp (e0 : exp) (e : exp) (ann : ann) : FreshAnn (exp * list equation) :=
    let '(ty, (ck, name)) := ann in
    do (initid, eqs) <- init_var_for_clock ck;
    do px <- fresh_ident norm2 (ty, ck);
    ret (Ecase (Evar initid (bool_velus_type, (ck, Some initid)))
               [Some [Evar px (ty, (ck, Some px))]; None] [e0] ([ty], (ck, name)),
         ([px], [Efby [add_whens (init_type ty) ty ck] [e] [ann]])::eqs).

  Definition arrow_iteexp (e0 : exp) (e : exp) (ann : ann) : FreshAnn (exp * list equation) :=
    let '(ty, (ck, name)) := ann in
    do (initid, eqs) <- init_var_for_clock ck;
    ret (Ecase (Evar initid (bool_velus_type, (ck, Some initid))) [Some [e]; None] [e0]
              ([ty], (ck, name)), eqs).

  Definition normfby_equation (to_cut : PS.t) (eq : equation) : FreshAnn (list equation) :=
    match eq with
    | ([x], [Efby [e0] [e] [ann]]) =>
      let '(ty, (ck, _)) := ann in
      if is_constant e0 then
        if PS.mem x to_cut then
          do x' <- fresh_ident norm2 (ty, ck);
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
    | _ => ret [d] (* Should not happen *)
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
          (let '(ty, (ck, _)) := ann in
           if PS.mem x to_cut then
             do x' <- fresh_ident norm2 (ty, ck);
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
         1,2,3:(destruct_to_singl l; destruct_to_singl l0; destruct_to_singl l1).
    }
    destruct e; auto.
    1,2:destruct_to_singl l; destruct_to_singl l0; destruct_to_singl l1; simpl.
    - (* fby *)
      destruct a as [ty [ck name]].
      destruct (is_constant e) eqn:Hconst; simpl.
      + left. repeat eexists; eauto.
      + right; left. repeat eexists; eauto.
    - (* arrow *)
      destruct a as [ty [ck name]]. right; right; left.
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

  (** *** Preservation of st_valid *)

  Definition st_valid_after {B} st aft := @st_valid_after B st norm2 aft.
  Hint Unfold st_valid_after.

  Fact init_var_for_clock_st_valid : forall ck res st st' aft,
      init_var_for_clock ck st = (res, st') ->
      st_valid_after st aft ->
      st_valid_after st' aft.
  Proof.
    intros * Hinit Hvalid.
    unfold init_var_for_clock in Hinit.
    repeat inv_bind.
    destruct (fresh_ident _ _) eqn:Hfresh. inv Hinit.
    eapply fresh_ident_st_valid in Hfresh; eauto.
  Qed.
  Hint Resolve init_var_for_clock_st_valid.

  Fact fby_iteexp_st_valid : forall e0 e a e' eqs' st st' aft,
      fby_iteexp e0 e a st = (e', eqs', st') ->
      st_valid_after st aft ->
      st_valid_after st' aft.
  Proof with eauto.
    intros e0 e [ty [ck name]] e' eqs' st st' aft Hfby Hvalid.
    unfold fby_iteexp in Hfby.
    repeat inv_bind;
      eapply fresh_ident_st_valid, init_var_for_clock_st_valid; eauto.
  Qed.
  Hint Resolve fby_iteexp_st_valid.

  Fact arrow_iteexp_st_valid : forall e0 e a e' eqs' st st' aft,
      arrow_iteexp e0 e a st = (e', eqs', st') ->
      st_valid_after st aft ->
      st_valid_after st' aft.
  Proof with eauto.
    intros e0 e [ty [ck name]] e' eqs' st st' aft Hfby Hvalid.
    unfold arrow_iteexp in Hfby.
    repeat inv_bind...
  Qed.
  Hint Resolve arrow_iteexp_st_valid.

  Fact normfby_equation_st_valid : forall to_cut eq eqs' st st' aft,
      normfby_equation to_cut eq st = (eqs', st') ->
      st_valid_after st aft ->
      st_valid_after st' aft.
  Proof.
    intros * Hfby Hvalid.
    inv_normfby_equation Hfby to_cut eq.
    - destruct x2 as [ty [ck name]]; repeat inv_bind.
      destruct (PS.mem _ _); repeat inv_bind; auto.
      eapply fresh_ident_st_valid; eauto.
    - eapply fby_iteexp_st_valid; eauto.
    - eapply arrow_iteexp_st_valid; eauto.
  Qed.

  Fact normfby_block_st_valid : forall to_cut d blocks' st st' aft,
      normfby_block to_cut d st = (blocks', st') ->
      st_valid_after st aft ->
      st_valid_after st' aft.
  Proof.
    induction d using block_ind2; intros * Hfby Hst;
      simpl in Hfby; repeat inv_bind.
    - eapply normfby_equation_st_valid; eauto.
    - cases; repeat inv_bind; auto.
      apply Forall_singl in H; eauto.
  Qed.

  Corollary normfby_blocks_st_valid : forall to_cut blocks blocks' st st' aft,
      normfby_blocks to_cut blocks st = (blocks', st') ->
      st_valid_after st aft ->
      st_valid_after st' aft.
  Proof.
    intros * Hfby Hst.
    unfold normfby_blocks in Hfby; repeat inv_bind.
    eapply mmap_st_valid in Hst; eauto.
    solve_forall. eapply normfby_block_st_valid; eauto.
  Qed.

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
  Hint Resolve init_var_for_clock_st_follows.

  Fact fby_iteexp_st_follows : forall e0 e ann res st st',
      fby_iteexp e0 e ann st = (res, st') ->
      st_follows st st'.
  Proof.
    intros e0 e [ty [ck name]] res st st' Hfby.
    unfold fby_iteexp in Hfby; repeat inv_bind.
    etransitivity; eauto.
  Qed.
  Hint Resolve fby_iteexp_st_follows.

  Fact arrow_iteexp_st_follows : forall e0 e ann res st st',
      arrow_iteexp e0 e ann st = (res, st') ->
      st_follows st st'.
  Proof.
    intros e0 e [ty [ck name]] res st st' Hfby.
    unfold arrow_iteexp in Hfby.
    repeat inv_bind; eauto.
  Qed.
  Hint Resolve arrow_iteexp_st_follows.

  Fact normfby_equation_st_follows : forall to_cut eq eqs' st st',
      normfby_equation to_cut eq st = (eqs', st') ->
      st_follows st st'.
  Proof.
    intros * Hfby.
    inv_normfby_equation Hfby to_cut eq.
    - destruct x2 as [ty [ck name]].
      destruct (PS.mem _ _); repeat inv_bind.
      1,2:repeat solve_st_follows.
    - eapply fby_iteexp_st_follows; eauto.
    - eapply arrow_iteexp_st_follows; eauto.
    - reflexivity.
  Qed.
  Hint Resolve normfby_equation_st_follows.

  Fact normfby_block_st_follows : forall to_cut d blocks' st st',
      normfby_block to_cut d st = (blocks', st') ->
      st_follows st st'.
  Proof.
    induction d using block_ind2; intros * Hfby; simpl in Hfby; repeat inv_bind.
    - eapply normfby_equation_st_follows; eauto.
    - cases; repeat inv_bind; try reflexivity.
      inv H; eauto.
  Qed.
  Hint Resolve normfby_block_st_follows.

  Corollary normfby_equations_st_follows : forall to_cut blocks blocks' st st',
      normfby_blocks to_cut blocks st = (blocks', st') ->
      st_follows st st'.
  Proof.
    intros * Hfby. unfold normfby_blocks in *; repeat inv_bind.
    eapply mmap_st_follows; eauto.
    solve_forall.
  Qed.

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
    intros ? ? [ty [ck name]] ? ? ? ? Hfby.
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
    intros ? ? [ty [ck name]] ? ? ? ? Hfby.
    unfold arrow_iteexp in Hfby. repeat inv_bind.
    eapply init_var_for_clock_vars_perm in H; eauto.
  Qed.

  Fact normfby_equation_vars_perm : forall to_cut eq eqs' st st',
      normfby_equation to_cut eq st = (eqs', st') ->
      Permutation (flat_map fst eqs'++st_ids st) (fst eq++st_ids st').
  Proof.
    intros * Hfby.
    inv_normfby_equation Hfby to_cut eq.
    destruct x2 as [ty [ck name]]; repeat inv_bind.
    - destruct PS.mem; repeat inv_bind; simpl; auto.
      eapply fresh_ident_vars_perm in H.
      apply perm_skip; auto.
    - simpl. apply perm_skip.
      eapply fby_iteexp_vars_perm in H; eauto.
    - eapply arrow_iteexp_vars_perm in H; simpl; auto.
    - simpl; rewrite app_nil_r; auto.
  Qed.

  Fact normfby_block_vars_perm : forall to_cut d blocks' st st',
      normfby_block to_cut d st = (blocks', st') ->
      Permutation (flat_map vars_defined blocks'++st_ids st) (vars_defined d++st_ids st').
  Proof.
    induction d using block_ind2; intros * Hfby; simpl in Hfby; repeat inv_bind.
    - eapply normfby_equation_vars_perm in H. rewrite <-H.
      apply Permutation_app_tail.
      clear - x. induction x; simpl; auto using Permutation_app_head.
    - cases; repeat inv_bind; simpl; repeat rewrite app_nil_r; try reflexivity.
      apply Forall_singl in H.
      apply H in H0.
      rewrite <-H0.
      clear - x.
      induction x; simpl; auto.
      rewrite app_nil_r, <-2 app_assoc.
      apply Permutation_app_head; auto.
  Qed.

  Corollary normfby_blocks_vars_perm : forall to_cut blocks blocks' st st',
      normfby_blocks to_cut blocks st = (blocks', st') ->
      Permutation (flat_map vars_defined blocks'++(st_ids st)) (flat_map vars_defined blocks++st_ids st').
  Proof.
    induction blocks; intros * Hnorm; unfold normfby_blocks in Hnorm; repeat inv_bind.
    - reflexivity.
    - assert (normfby_blocks to_cut blocks x1 = (concat x2, st')) as Hnorm'.
      { unfold normfby_blocks. repeat inv_bind; eauto. }
      eapply IHblocks in Hnorm'; eauto.
      eapply normfby_block_vars_perm in H; eauto; simpl in *.
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
    repeat inv_bind; reflexivity.
  Qed.

  Fact arrow_iteexp_annot : forall e0 e ann es' eqs' st st',
      arrow_iteexp e0 e ann st = (es', eqs', st') ->
      annot es' = [ann].
  Proof.
    intros e0 e [ty [cl n]] es' eqs' st st' Hfby.
    unfold arrow_iteexp in Hfby.
    repeat inv_bind; reflexivity.
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

  (** ** Specification of a normalized node *)

  Inductive normalized_constant : exp -> Prop :=
  | constant_Econst : forall c,
      normalized_constant (Econst c)
  | constant_Eenum : forall k ty,
      normalized_constant (Eenum k ty)
  | constant_Ewhen : forall e x b ty cl,
      normalized_constant e ->
      normalized_constant (Ewhen [e] x b ([ty], cl)).

  Inductive normalized_equation {prefs} (G : @global prefs) : PS.t -> equation -> Prop :=
  | normalized_eq_Eapp : forall out xs f n es er lann,
      Forall normalized_lexp es ->
      find_node f G = Some n ->
      Forall2 noops_exp (map (fun '(_, (_, ck)) => ck) n.(n_in)) es ->
      Forall (fun e => exists x ann, e = Evar x ann) er ->
      normalized_equation G out (xs, [Eapp f es er lann])
  | normalized_eq_Efby : forall out x e0 e ann,
      ~PS.In x out ->
      normalized_constant e0 ->
      normalized_lexp e ->
      normalized_equation G out ([x], [Efby [e0] [e] [ann]])
  | normalized_eq_cexp : forall out x e,
      normalized_cexp e ->
      normalized_equation G out ([x], [e]).

  Inductive normalized_block {prefs} (G : @global prefs) : PS.t -> block -> Prop :=
  | normalized_Beq : forall out eq,
      normalized_equation G out eq ->
      normalized_block G out (Beq eq)
  | normalized_Breset : forall out block x ann,
      normalized_block G out block ->
      normalized_block G out (Breset [block] (Evar x ann)).

  Definition normalized_node {prefs1 prefs2} (G : @global prefs1) (n : @node prefs2) :=
    Forall (normalized_block G (ps_from_list (List.map fst (n_out n)))) (n_blocks n).

  Definition normalized_global {prefs} : @global prefs -> Prop :=
    wt_program normalized_node.

  Hint Constructors normalized_constant normalized_equation normalized_block.

  (** *** normalized_node implies unnested_node *)

  Fact constant_normalized_lexp : forall e,
      normalized_constant e ->
      normalized_lexp e.
  Proof.
    intros e Hconst.
    induction Hconst; auto.
  Qed.

  Fact normalized_eq_unnested_eq {prefs} : forall (G : @global prefs) to_cut eq,
      normalized_equation G to_cut eq ->
      unnested_equation G eq.
  Proof.
    intros * Hnormed. inv Hnormed; eauto using constant_normalized_lexp.
  Qed.

  Fact normalized_block_unnested_block {prefs} : forall (G : @global prefs) to_cut block,
      normalized_block G to_cut block ->
      unnested_block G block.
  Proof.
    intros * Hnormed.
    induction Hnormed; constructor; auto.
    eapply normalized_eq_unnested_eq; eauto.
  Qed.

  Fact normalized_node_unnested_node {prefs1 prefs2} : forall (G : @global prefs1) (n : @node prefs2),
      normalized_node G n ->
      unnested_node G n.
  Proof.
    intros * Hnormed.
    unfold normalized_node, unnested_node in *.
    solve_forall.
    eapply normalized_block_unnested_block; eauto.
  Qed.

  Fact normalized_global_unnested_global {prefs} : forall (G : @global prefs),
      normalized_global G ->
      unnested_global G.
  Proof.
    unfold normalized_global, unnested_global.
    destruct G as (enums&nds).
    induction nds; intros Hnormed; inv Hnormed; constructor.
    - destruct H1. split; eauto.
      eapply normalized_node_unnested_node; eauto.
    - eapply IHnds; eauto.
  Qed.

  (** *** Preservation of wl property *)

  Fact add_whens_numstreams : forall ty ck e,
      numstreams e = 1 ->
      numstreams (add_whens e ty ck) = 1.
  Proof.
    induction ck; intros *; try destruct p; simpl; auto.
  Qed.

  Fact add_whens_wl {prefs} : forall (G : @global prefs) ty ck e,
      numstreams e = 1 ->
      wl_exp G e ->
      wl_exp G (add_whens e ty ck).
  Proof.
    induction ck; intros * Hlen Hwl; simpl; auto.
    destruct p; constructor; simpl; auto.
    rewrite app_nil_r, length_annot_numstreams.
    apply add_whens_numstreams; auto.
  Qed.

  Hint Constructors wl_exp.

  Fact init_var_for_clock_wl {prefs} : forall (G : @global prefs) ck id eqs' st st',
      init_var_for_clock ck st = (id, eqs', st') ->
      Forall (wl_equation G) eqs'.
  Proof.
    intros * Hinit.
    unfold init_var_for_clock in Hinit.
    destruct (fresh_ident _ _). inv Hinit.
    repeat constructor; simpl.
    1,2:apply add_whens_wl; auto.
    1,2:simpl; rewrite app_nil_r, length_annot_numstreams; apply add_whens_numstreams; auto.
  Qed.

  Fact fby_iteexp_numstreams : forall e0 e a e' eqs' st st',
      fby_iteexp e0 e a st = (e', eqs', st') ->
      numstreams e' = 1.
  Proof.
    intros * Hfby. destruct a as [ty [ck name]].
    unfold fby_iteexp in Hfby.
    repeat inv_bind; simpl; auto.
  Qed.

  Fact fby_iteexp_wl_exp {prefs} : forall (G : @global prefs) e0 e a e' eqs' st st',
      wl_exp G e0 ->
      wl_exp G e ->
      numstreams e0 = 1 ->
      numstreams e = 1 ->
      fby_iteexp e0 e a st = (e', eqs', st') ->
      wl_exp G e'.
  Proof.
    intros * Hwl1 Hwl2 Hn1 Hn2 Hfby.
    destruct a as [ty [ck name]].
    unfold fby_iteexp in Hfby.
    repeat inv_bind.
    constructor; auto; simpl.
    - congruence.
    - repeat constructor; simpl.
      intros ? [Heq|[Heq|Heq]]; inv Heq; auto.
    - intros ? [Heq|[Heq|Heq]]; inv Heq; auto.
    - rewrite app_nil_r, length_annot_numstreams; auto.
  Qed.

  Fact fby_iteexp_wl_eq {prefs} : forall (G : @global prefs) e0 e a e' eqs' st st',
      wl_exp G e0 ->
      wl_exp G e ->
      numstreams e0 = 1 ->
      numstreams e = 1 ->
      fby_iteexp e0 e a st = (e', eqs', st') ->
      Forall (wl_equation G) eqs'.
  Proof.
    intros * Hwl1 Hwl2 Hn1 Hn2 Hfby.
    destruct a as [ty [ck name]].
    unfold fby_iteexp in Hfby.
    repeat inv_bind; auto.
    repeat constructor; simpl; auto.
    - apply add_whens_wl; auto.
      1,2:destruct ty; simpl; auto.
    - rewrite app_nil_r, length_annot_numstreams. apply add_whens_numstreams; auto.
      destruct ty; simpl; auto.
    - rewrite app_nil_r, length_annot_numstreams; auto.
    - eapply init_var_for_clock_wl; eauto.
  Qed.

  Fact arrow_iteexp_numstreams : forall e0 e a e' eqs' st st',
      arrow_iteexp e0 e a st = (e', eqs', st') ->
      numstreams e' = 1.
  Proof.
    intros * Hfby. destruct a as [ty [ck name]].
    unfold arrow_iteexp in Hfby.
    repeat inv_bind. reflexivity.
  Qed.

  Fact arrow_iteexp_wl_exp {prefs} : forall (G : @global prefs) e0 e a e' eqs' st st',
      wl_exp G e0 ->
      wl_exp G e ->
      numstreams e0 = 1 ->
      numstreams e = 1 ->
      arrow_iteexp e0 e a st = (e', eqs', st') ->
      wl_exp G e'.
  Proof.
    intros * Hwl1 Hwl2 Hn1 Hn2 Hfby. destruct a as [ty [ck name]].
    unfold arrow_iteexp in Hfby; repeat inv_bind.
    repeat constructor; auto; simpl.
    congruence.
    1,2:intros ? [Heq|[Heq|Heq]]; inv Heq; simpl; auto.
    1,2:rewrite app_nil_r, length_annot_numstreams; auto.
  Qed.

  Fact arrow_iteexp_wl_eq {prefs} : forall (G : @global prefs) e0 e a e' eqs' st st',
      wl_exp G e0 ->
      wl_exp G e ->
      numstreams e0 = 1 ->
      numstreams e = 1 ->
      arrow_iteexp e0 e a st = (e', eqs', st') ->
      Forall (wl_equation G) eqs'.
  Proof.
    intros * Hwl1 Hwl2 Hn1 Hn2 Hfby.
    destruct a as [ty [ck name]].
    unfold arrow_iteexp in Hfby; repeat inv_bind.
    eapply init_var_for_clock_wl in H; eauto.
  Qed.

  Fact normfby_equation_wl {prefs} : forall (G : @global prefs) to_cut eq eqs' st st',
      wl_equation G eq ->
      normfby_equation to_cut eq st = (eqs', st') ->
      Forall (wl_equation G) eqs'.
  Proof.
    intros * Hwl Hfby.
    inv_normfby_equation Hfby to_cut eq.
    - destruct x2 as [ty [ck name]].
      destruct PS.mem; repeat inv_bind; auto.
      destruct Hwl as [Hwl _]; inv Hwl; repeat (constructor; auto).
    - destruct Hwl as [Hwl _]. apply Forall_singl in Hwl.
      inv Hwl.
      apply Forall_singl in H3. apply Forall_singl in H5.
      simpl in *. rewrite app_nil_r, length_annot_numstreams in *.
      repeat constructor; simpl; try rewrite app_nil_r.
      + eapply fby_iteexp_wl_exp in H; eauto.
      + eapply fby_iteexp_annot in H; eauto.
        rewrite H; auto.
      + eapply fby_iteexp_wl_eq in H; eauto.
    - destruct Hwl as [Hwl _]. apply Forall_singl in Hwl.
      inv Hwl.
      apply Forall_singl in H3. apply Forall_singl in H5.
      simpl in *. rewrite app_nil_r, length_annot_numstreams in *.
      repeat constructor; simpl; try rewrite app_nil_r.
      + eapply arrow_iteexp_wl_exp in H; eauto.
      + eapply arrow_iteexp_annot in H; eauto.
        rewrite H; auto.
      + eapply arrow_iteexp_wl_eq in H; eauto.
  Qed.

  (** ** After normalization, equations and expressions are normalized *)

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

  Fact init_var_for_clock_unnested_eq {prefs} : forall (G : @global prefs) ck id eqs' st st',
      init_var_for_clock ck st = (id, eqs', st') ->
      Forall (unnested_equation G) eqs'.
  Proof.
    intros * Hinit.
    unfold init_var_for_clock in Hinit.
    destruct (fresh_ident _ _) eqn:Hfresh. inv Hinit.
    repeat constructor.
    1-2:eapply add_whens_normalized_lexp; eauto.
  Qed.

  Fact init_var_for_clock_normalized_eq {prefs} : forall (G : @global prefs) ck id eqs' out st st',
      st_valid_after st out ->
      init_var_for_clock ck st = (id, eqs', st') ->
      Forall (normalized_equation G out) eqs'.
  Proof.
    intros * Hvalid Hinit.
    unfold init_var_for_clock in Hinit.
    destruct (fresh_ident _ _) eqn:Hfresh. inv Hinit.
    repeat constructor.
    + eapply fresh_ident_nIn' in Hfresh; eauto.
    + apply add_whens_is_constant; auto.
    + apply add_whens_normalized_lexp; auto.
  Qed.

  Fact fby_iteexp_unnested_eq {prefs} : forall (G : @global prefs) e0 e a e' eqs' st st',
      normalized_lexp e0 ->
      normalized_lexp e ->
      fby_iteexp e0 e a st = (e', eqs', st') ->
      Forall (unnested_equation G) eqs'.
  Proof.
    intros * Hnormed1 Hnormed2 Hfby. destruct a as [ty [ck name]].
    unfold fby_iteexp in Hfby.
    repeat inv_bind; auto.
    repeat constructor; auto.
    - apply add_whens_normalized_lexp; destruct ty; simpl; auto.
    - eapply init_var_for_clock_unnested_eq in H; eauto.
  Qed.

  Fact fby_iteexp_normalized_eq {prefs} : forall (G : @global prefs) e0 e a e' eqs' out st st',
      st_valid_after st out ->
      normalized_lexp e ->
      fby_iteexp e0 e a st = (e', eqs', st') ->
      Forall (normalized_equation G out) eqs'.
  Proof.
    intros G e0 e [ty [ck name]] * Hvalid He Hfby.
    unfold fby_iteexp in Hfby.
    repeat inv_bind; constructor.
    - assert (st_valid_after x1 out0) as Hvalid' by eauto.
      constructor; auto.
      + eapply fresh_ident_nIn' in H0; eauto.
      + eapply add_whens_is_constant; destruct ty; simpl; eauto.
    - eapply init_var_for_clock_normalized_eq in H; eauto.
  Qed.

  Fact normfby_equation_unnested_eq {prefs} : forall (G : @global prefs) to_cut eq eqs' st st',
      unnested_equation G eq ->
      normfby_equation to_cut eq st = (eqs', st') ->
      Forall (unnested_equation G) eqs'.
  Proof.
    intros * Hunt Hfby.
    inv_normfby_equation Hfby to_cut eq;
      try destruct x2 as [ty [ck name]].
    - destruct PS.mem; repeat inv_bind; auto.
      inv Hunt; constructor; auto.
    - assert (H':=H). eapply fby_iteexp_unnested_eq in H'.
      constructor; eauto.
      repeat inv_bind. repeat constructor; eauto.
      1,2:intros ? Heq; inv Heq. eexists; split; eauto.
      1-3:(clear - Hunt; inv Hunt; eauto; inv H0; inv H).
    - repeat inv_bind. repeat constructor; auto.
      1,2:intros ? Heq; inv Heq. exists x1; split; auto.
      3:eapply init_var_for_clock_unnested_eq in H; eauto.
      1-2:(clear - Hunt; inv Hunt; eauto; inv H0; inv H).
  Qed.

  Fact normfby_block_unnested_block {prefs} : forall (G : @global prefs) to_cut bck bcks' st st',
      unnested_block G bck ->
      normfby_block to_cut bck st = (bcks', st') ->
      Forall (unnested_block G) bcks'.
  Proof.
    induction bck using block_ind2; intros * Hunt Hfby;
      inv Hunt; simpl in *; cases; repeat inv_bind.
    - eapply normfby_equation_unnested_eq in H; eauto.
      rewrite Forall_map. eapply Forall_impl; [|eauto]; intros.
      constructor; auto.
    - apply Forall_singl in H.
      eapply H in H0; eauto.
      rewrite Forall_map. eapply Forall_impl; [|eauto]; intros.
      constructor; auto.
  Qed.

  Fact normfby_equation_normalized_eq {prefs} : forall (G : @global prefs) out to_cut eq eqs' st st',
      st_valid_after st out ->
      unnested_equation G eq ->
      PS.Subset out to_cut ->
      normfby_equation to_cut eq st = (eqs', st') ->
      Forall (normalized_equation G out) eqs'.
  Proof.
    intros * Hvalid Hunt Hsub Hfby.
    inv Hunt; simpl in *; repeat inv_bind; eauto.
    1:destruct_to_singl xs; repeat inv_bind; eauto.
    - (* fby *)
      (destruct ann0 as (?&?&?); destruct (is_constant e0) eqn:Hconst;
       [apply is_constant_normalized_constant in Hconst;
        destruct PS.mem eqn:Hmem; [|apply PSE.mem_4 in Hmem]|]; repeat inv_bind).
      1-3:repeat constructor; eauto.
      2,3:intros ? Heq; inv Heq.
      + eapply fresh_ident_nIn'; eauto.
      + eexists; split; eauto.
      + eapply fresh_ident_nIn' in H2; eauto.
        eapply init_var_for_clock_st_valid; eauto.
      + apply add_whens_is_constant; destruct t; simpl; auto.
      + eapply init_var_for_clock_normalized_eq; eauto.
    - (* arrow *)
      destruct ann0 as (?&?&?) eqn:Vars; repeat inv_bind.
      repeat constructor; eauto.
      1-2:intros ? Heq; inv Heq. exists e; auto.
      eapply init_var_for_clock_normalized_eq; eauto.
    - (* cexp *)
      inv H; repeat inv_bind; auto.
      inv H0; repeat inv_bind; auto.
  Qed.

  Fact normfby_block_normalized_block {prefs} : forall (G : @global prefs) out to_cut d blocks' st st',
      st_valid_after st out ->
      unnested_block G d ->
      PS.Subset out to_cut ->
      normfby_block to_cut d st = (blocks', st') ->
      Forall (normalized_block G out) blocks'.
  Proof.
    induction d using block_ind2; intros * Hvalid Hun Hsub Hfby; inv Hun;
      simpl in Hfby; try destruct ann0; repeat inv_bind.
    - eapply normfby_equation_normalized_eq in H; eauto.
      rewrite Forall_map. eapply Forall_impl; [|eauto]; eauto.
    - apply Forall_singl in H.
      apply H in H0; auto.
      rewrite Forall_map. eapply Forall_impl; [|eauto]; eauto.
  Qed.

  Corollary normfby_blocks_normalized_block {prefs} : forall (G : @global prefs) out to_cut blocks blocks' st st',
      st_valid_after st out ->
      Forall (unnested_block G) blocks ->
      PS.Subset out to_cut ->
      normfby_blocks to_cut blocks st = (blocks', st') ->
      Forall (normalized_block G out) blocks'.
  Proof.
    induction blocks; intros * Hvalid Hunt Hsub Hfby;
      unfold normfby_blocks in Hfby; repeat inv_bind; simpl; auto.
    inv Hunt.
    eapply Forall_app; split.
    - eapply normfby_block_normalized_block in H; eauto.
    - eapply IHblocks with (st:=x1) (st':=st'); eauto. 1:eapply normfby_block_st_valid; eauto.
      unfold normfby_blocks; repeat inv_bind; eauto.
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

  Lemma add_whens_no_fresh : forall e ty ck,
      fresh_in (add_whens e ty ck) = fresh_in e.
  Proof.
    induction ck as [|??? (?&?)]; simpl; auto.
    rewrite app_nil_r; auto.
  Qed.

  Lemma init_var_for_clock_no_anon : forall ck xinit eqs' st st' ,
      init_var_for_clock ck st = (xinit, eqs', st') ->
      flat_map anon_in_eq eqs' = [].
  Proof.
    unfold init_var_for_clock. intros * Hinit.
    destruct fresh_ident; repeat inv_bind; simpl.
    unfold anon_in_eq; simpl.
    repeat rewrite app_nil_r.
    repeat rewrite add_whens_no_fresh; simpl.
    reflexivity.
  Qed.

  Lemma normfby_equation_anon : forall to_cut equ eqs' st st' ,
      normfby_equation to_cut equ st = (eqs', st') ->
      Permutation (flat_map anon_in_eq eqs') (anon_in_eq equ).
  Proof.
    unfold normfby_equation, fby_iteexp, arrow_iteexp.
    intros ? (?&?) * Hfby.
    cases; repeat inv_bind; simpl; repeat rewrite app_nil_r; try reflexivity.
    - unfold anon_in_eq; simpl; repeat rewrite app_nil_r.
      apply Permutation_app_head.
      rewrite add_whens_no_fresh.
      replace (fresh_in (init_type t)) with (@nil (ident * (type * clock))) by (destruct t; simpl; auto).
      erewrite init_var_for_clock_no_anon, app_nil_r; eauto.
    - unfold anon_in_eq; simpl; repeat rewrite app_nil_r.
      erewrite init_var_for_clock_no_anon, app_nil_r; eauto using Permutation_app_comm.
  Qed.

  Lemma normfby_block_anon : forall to_cut d blocks' st st' ,
      normfby_block to_cut d st = (blocks', st') ->
      Permutation (flat_map anon_in_block blocks') (anon_in_block d).
  Proof.
    induction d using block_ind2; intros * Hfby; simpl in Hfby;
      cases; repeat inv_bind; simpl; repeat rewrite app_nil_r; try reflexivity.
    - erewrite <-normfby_equation_anon; eauto.
      clear - x. induction x; simpl; auto using Permutation_app_head.
    - apply Forall_singl in H. erewrite <-H; [|eauto].
      clear - x. induction x; simpl; auto.
      repeat rewrite app_nil_r. apply Permutation_app_head; auto.
  Qed.

  Corollary normfby_blocks_anon : forall to_cut blocks blocks' st st',
      normfby_blocks to_cut blocks st = (blocks', st') ->
      Permutation (flat_map anon_in_block blocks') (flat_map anon_in_block blocks).
  Proof.
    unfold normfby_blocks.
    induction blocks; intros * Hfby; repeat inv_bind; simpl in *; auto.
    eapply normfby_block_anon in H.
    rewrite <-flat_map_app, H, IHblocks; auto.
    repeat inv_bind; eauto.
  Qed.

  Lemma normfby_blocks_no_anon {prefs} : forall (G : @global prefs) out to_cut blocks blocks' st st',
      st_valid_after st out ->
      Forall (unnested_block G) blocks ->
      PS.Subset out to_cut ->
      normfby_blocks to_cut blocks st = (blocks', st') ->
      flat_map anon_in_block blocks' = [].
  Proof.
    intros * Hweak Hunt Hsub Hfby.
    eapply normfby_blocks_normalized_block in Hfby; eauto.
    eapply unnested_blocks_no_anon.
    solve_forall. eapply normalized_block_unnested_block; eauto.
  Qed.

  (** ** Normalization of a full node *)

  Lemma norm2_not_in_norm1_prefs :
    ~PS.In norm2 norm1_prefs.
  Proof.
    unfold norm1_prefs, elab_prefs.
    rewrite PSF.add_iff, PSF.singleton_iff.
    intro contra.
    pose proof gensym_prefs_NoDup as Hnd. unfold gensym_prefs in Hnd.
    repeat rewrite NoDup_cons_iff in Hnd. destruct Hnd as (Hnin1&Hnin2&_).
    destruct contra as [contra|contra].
    1,2:rewrite contra in *.
    + apply Hnin2; left; auto.
    + apply Hnin1; right; left; auto.
  Qed.

  Program Definition normfby_node (* (to_cut : PS.t) *) (n : @node norm1_prefs) : @node norm2_prefs :=
    let blocks := normfby_blocks (ps_from_list (map fst (n_out n))) (n_blocks n) init_st in
    let nvars := st_anns (snd blocks) in
    {| n_name := n_name n;
       n_hasstate := n_hasstate n;
       n_in := n_in n;
       n_out := n_out n;
       n_vars := (n_vars n)++nvars;
       n_blocks := fst blocks;
       n_ingt0 := n_ingt0 n;
       n_outgt0 := n_outgt0 n;
    |}.
  Next Obligation.
    remember (normfby_blocks _ _ _) as blocks. destruct blocks as [blocks st']. symmetry in Heqblocks.
    specialize (n_defd n) as Hperm.
    apply normfby_blocks_vars_perm in Heqblocks; simpl.
    rewrite Permutation_app_comm, app_assoc, map_app, (Permutation_app_comm (n_out n)), <- Hperm.
    rewrite <- Heqblocks. unfold st_ids. rewrite init_st_anns, app_nil_r; auto.
  Qed.
  Next Obligation.
    destruct (normfby_blocks _ _ _) as (blocks, st') eqn:Heqblocks.
    pose proof (node_NoDup n) as Hndup.
    pose proof (n_good n) as (Good&_).
    simpl. erewrite normfby_blocks_anon; eauto.
    eapply normfby_blocks_st_valid, st_valid_NoDup in Heqblocks; eauto.
    2:{ eapply init_st_valid.
        - eapply norm2_not_in_norm1_prefs.
        - rewrite PS_For_all_Forall.
          eapply Forall_incl; eauto.
          intros ? Hin.
          rewrite ps_of_list_ps_to_list in Hin; eauto. }
    rewrite ps_of_list_ps_to_list_Perm in Heqblocks; auto. 2:rewrite <-fst_NoDupMembers; apply n_nodup.
    rewrite <- app_assoc, fst_NoDupMembers. repeat rewrite map_app in *.
    unfold st_ids in Heqblocks.
    rewrite (app_assoc (map _ (n_vars _))), (Permutation_app_comm (map _ (n_vars _))),
    <- app_assoc, app_assoc, (Permutation_app_comm (map _ (n_in _))), <- app_assoc; auto.
  Qed.
  Next Obligation.
    specialize (n_good n) as (Hgood&Hname). split; auto.
    repeat rewrite map_app, Forall_app in Hgood. destruct Hgood as (?&?&?&?).
    destruct (normfby_blocks _ _ _) as (blocks, st') eqn:Heqblocks.
    pose proof (node_NoDup n) as Hndup.
    pose proof (n_good n) as (Good&_).
    assert (st_valid_after st' (PSP.of_list (map fst (n_in n ++ n_vars n ++ n_out n)))) as Hvalid.
    { eapply normfby_blocks_st_valid, init_st_valid; eauto.
      - eapply norm2_not_in_norm1_prefs.
      - rewrite PS_For_all_Forall.
        eapply Forall_incl; eauto.
        intros ? Hin.
        rewrite ps_of_list_ps_to_list in Hin.
        eapply incl_map; eauto.
        apply incl_appr', incl_appr', incl_appl, incl_refl. }
    erewrite normfby_blocks_anon; eauto.
    simpl.
    repeat rewrite map_app, Forall_app in *. destruct Good as (?&?&?&_).
    unfold norm2_prefs.
    repeat split; auto using AtomOrGensym_add.
    eapply st_valid_prefixed in Hvalid.
    eapply Forall_impl; [|eauto]. intros ? (?&?); subst.
    right. exists norm2. eauto using PSF.add_1.
  Qed.

  Program Instance normfby_node_transform_unit: TransformUnit node node :=
    { transform_unit := normfby_node }.

  Program Instance normfby_global_without_units : TransformProgramWithoutUnits (@global norm1_prefs) (@global norm2_prefs) :=
    { transform_program_without_units := fun g => Global g.(enums) [] }.

  Definition normfby_global : @global norm1_prefs -> @global norm2_prefs := transform_units.

  (** *** normfby_global produces an equivalent global *)

  Fact normfby_global_eq : forall G,
      global_iface_eq G (normfby_global G).
  Proof.
    split; auto.
    intros f. unfold find_node.
    destruct (find_unit f G) as [(?&?)|] eqn:Hfind; simpl.
    - setoid_rewrite find_unit_transform_units_forward; eauto.
      simpl. repeat constructor.
    - destruct (find_unit f (normfby_global G)) as [(?&?)|] eqn:Hfind'; simpl; try constructor.
      eapply find_unit_transform_units_backward in Hfind' as (?&?&?&?); congruence.
  Qed.

  Fact normfby_nodes_names {prefs} : forall (a : @node prefs) nds,
      Forall (fun n => (n_name a <> n_name n)%type) nds ->
      Forall (fun n => (n_name a <> n_name n)%type) (map normfby_node nds).
  Proof.
    induction nds; intros * Hnames; simpl.
    - constructor.
    - inv Hnames.
      constructor; eauto.
  Qed.

  (** *** After normalization, a global is normalized *)

  Lemma iface_eq_normalized_equation {prefs1 prefs2} : forall (G : @global prefs1) (G' : @global prefs2) to_cut eq,
      global_iface_eq G G' ->
      normalized_equation G to_cut eq ->
      normalized_equation G' to_cut eq.
  Proof.
    intros * Heq Hunt.
    inv Hunt; try constructor; eauto.
    destruct Heq as (_&Heq). specialize (Heq f).
    rewrite H0 in Heq. inv Heq. destruct H5 as (_&_&?&_).
    econstructor; eauto. congruence.
  Qed.

  Lemma iface_eq_normalized_block {prefs1 prefs2} : forall (G : @global prefs1) (G' : @global prefs2) to_cut d,
      global_iface_eq G G' ->
      normalized_block G to_cut d ->
      normalized_block G' to_cut d.
  Proof.
    induction d using block_ind2; intros * Heq Hnormed; inv Hnormed; constructor.
    - eapply iface_eq_normalized_equation; eauto.
    - apply Forall_singl in H; eauto.
  Qed.

  Corollary iface_eq_normalized_node {p1 p2 p3} : forall (G : @global p1) (G' : @global p2) (n : @node p3),
      global_iface_eq G G' ->
      normalized_node G n ->
      normalized_node G' n.
  Proof.
    intros * Hglob Hunt.
    unfold normalized_node in *.
    eapply Forall_impl; [|eauto]. intros.
    eapply iface_eq_normalized_block; eauto.
  Qed.

  Fact normfby_node_normalized_node {prefs} : forall (G : @global prefs) n,
      unnested_node G n ->
      normalized_node G (normfby_node n).
  Proof.
    intros * Hunt.
    unfold normfby_node, normalized_node; simpl.
    pose proof (n_good n) as (Good&_).
    remember (normfby_blocks _ _ _) as eqs. symmetry in Heqeqs. destruct eqs as [eqs st'].
    eapply normfby_blocks_normalized_block in Heqeqs; eauto.
    2:rewrite ps_from_list_ps_of_list; reflexivity.
    { eapply init_st_valid.
      - apply norm2_not_in_norm1_prefs.
      - rewrite PS_For_all_Forall.
        eapply Forall_incl; eauto.
        intros ? Hin.
        rewrite ps_from_list_ps_of_list, ps_of_list_ps_to_list in Hin. repeat simpl_In.
        exists (i, (t, c)); split; auto. repeat rewrite in_app_iff in *; auto. }
  Qed.

  Fact normfby_global_normalized_global : forall G,
      unnested_global G ->
      normalized_global (normfby_global G).
  Proof.
    unfold normfby_global. destruct G as (enums&nds).
    intros * Hunt.
    eapply transform_units_wt_program; eauto.
    intros ?? Huntn.
    eapply normfby_node_normalized_node; eauto.
    eapply iface_eq_unnested_node; eauto.
    eapply normfby_global_eq.
  Qed.
End NORMFBY.

Module NormFbyFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks : CLOCKS Ids Op OpAux)
       (Syn : LSYNTAX Ids Op OpAux Cks)
       (Unt : UNNESTING Ids Op OpAux Cks Syn)
       <: NORMFBY Ids Op OpAux Cks Syn Unt.
  Include NORMFBY Ids Op OpAux Cks Syn Unt.
End NormFbyFun.
