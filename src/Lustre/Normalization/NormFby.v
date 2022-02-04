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
From Velus Require Import Lustre.Normalization.Unnesting.

(** * Putting FBYs into normalized form *)

Module Type NORMFBY
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks : CLOCKS Ids Op OpAux)
       (Import Senv : STATICENV Ids Op OpAux Cks)
       (Import Syn : LSYNTAX Ids Op OpAux Cks Senv)
       (Import Unt : UNNESTING Ids Op OpAux Cks Senv Syn).

  Import Fresh Fresh.Notations Facts Tactics.
  Local Open Scope fresh_monad_scope.

  (** Add some whens on top of an expression *)
  Fixpoint add_whens (e : exp) (ty : type) (cl : clock) :=
    match cl with
    | Cbase => e
    | Con cl' ckid (_, b) => Ewhen [(add_whens e ty cl')] ckid b ([ty], cl)
    end.

  Open Scope bool_scope.

  (** Generate an init equation for a given clock `cl`; if the init equation for `cl` already exists,
      just return the variable *)
  Definition init_var_for_clock (ck : clock) : FreshAnn (ident * list equation) :=
    fun st => let (x, st') := fresh_ident norm2 None ((OpAux.bool_velus_type, ck)) st in
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
    | Tenum _ => Eenum 0 ty
    end.

  (** Generate a if-then-else equation for (0 fby e), and return an expression using it *)
  Definition fby_iteexp (e0 : exp) (e : exp) (ann : ann) : FreshAnn (exp * list equation) :=
    let '(ty, ck) := ann in
    do (initid, eqs) <- init_var_for_clock ck;
    do px <- fresh_ident norm2 None (ty, ck);
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
          do x' <- fresh_ident norm2 None (ty, ck);
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
          (let '(ty, ck) := ann in
           if PS.mem x to_cut then
             do x' <- fresh_ident norm2 None (ty, ck);
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

  (** *** Preservation of st_valid *)

  Definition st_valid_after {B} st aft := @st_valid_after B st norm2 aft.
  Global Hint Unfold st_valid_after : norm.

  Fact init_var_for_clock_st_valid : forall ck res st st' aft,
      init_var_for_clock ck st = (res, st') ->
      st_valid_after st aft ->
      st_valid_after st' aft.
  Proof.
    intros * Hinit Hvalid.
    unfold init_var_for_clock in Hinit.
    repeat inv_bind.
    destruct (fresh_ident _ _ _) eqn:Hfresh. inv Hinit.
    eapply fresh_ident_st_valid in Hfresh; eauto.
  Qed.
  Global Hint Resolve init_var_for_clock_st_valid : norm.

  Fact fby_iteexp_st_valid : forall e0 e a e' eqs' st st' aft,
      fby_iteexp e0 e a st = (e', eqs', st') ->
      st_valid_after st aft ->
      st_valid_after st' aft.
  Proof with eauto.
    intros e0 e [ty ck] e' eqs' st st' aft Hfby Hvalid.
    unfold fby_iteexp in Hfby.
    repeat inv_bind;
      eapply fresh_ident_st_valid, init_var_for_clock_st_valid; eauto.
  Qed.
  Global Hint Resolve fby_iteexp_st_valid : norm.

  Fact arrow_iteexp_st_valid : forall e0 e a e' eqs' st st' aft,
      arrow_iteexp e0 e a st = (e', eqs', st') ->
      st_valid_after st aft ->
      st_valid_after st' aft.
  Proof with eauto with norm.
    intros e0 e [ty ck] e' eqs' st st' aft Hfby Hvalid.
    unfold arrow_iteexp in Hfby.
    repeat inv_bind...
  Qed.
  Global Hint Resolve arrow_iteexp_st_valid : norm.

  Fact normfby_equation_st_valid : forall to_cut eq eqs' st st' aft,
      normfby_equation to_cut eq st = (eqs', st') ->
      st_valid_after st aft ->
      st_valid_after st' aft.
  Proof.
    intros * Hfby Hvalid.
    inv_normfby_equation Hfby to_cut eq.
    - destruct x2 as [ty ck]; repeat inv_bind.
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
      simpl in Hfby; repeat inv_bind; auto.
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
      1,2:repeat solve_st_follows.
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
      VarsDefined blk xs ->
      normfby_block G blk st = (blks', st') ->
      exists ys, Forall2 VarsDefined blks' ys /\ Permutation (concat ys ++ st_ids st) (xs ++ st_ids st').
  Proof.
    induction blk using block_ind2; intros * Hvars Hun; inv Hvars; repeat inv_bind.
    - exists (map fst x). split.
      + rewrite Forall2_map_1, Forall2_map_2. apply Forall2_same.
        eapply Forall_forall; intros. constructor.
      + eapply normfby_equation_vars_perm in H. now rewrite flat_map_concat_map in H.
    - simpl in Hun. cases; repeat inv_bind.
      1-3,5-14:(exists [(concat xs0)]; simpl; rewrite app_nil_r; split; auto; repeat constructor; auto).
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
  Qed.

  Corollary normfby_blocks_vars_perm : forall G blks blks' xs st st',
      Forall2 VarsDefined blks xs ->
      normfby_blocks G blks st = (blks', st') ->
      exists ys, Forall2 VarsDefined blks' ys /\ Permutation (concat ys ++ st_ids st) (concat xs ++ st_ids st').
  Proof.
    intros * Hvars Hun. unfold normfby_blocks in Hun. repeat inv_bind.
    eapply mmap_vars_perm; [|eauto|eauto].
    solve_forall. eapply normfby_block_vars_perm; eauto.
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

  Inductive normalized_equation {PSyn prefs} (G : @global PSyn prefs) : PS.t -> equation -> Prop :=
  | normalized_eq_Eapp : forall out xs f n es er lann,
      Forall normalized_lexp es ->
      find_node f G = Some n ->
      Forall2 noops_exp (map (fun '(_, (_, ck, _)) => ck) n.(n_in)) es ->
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

  Inductive normalized_block {PSyn prefs} (G : @global PSyn prefs) : PS.t -> block -> Prop :=
  | normalized_Beq : forall out eq,
      normalized_equation G out eq ->
      normalized_block G out (Beq eq)
  | normalized_Breset : forall out block x ann,
      normalized_block G out block ->
      normalized_block G out (Breset [block] (Evar x ann)).

  Inductive normalized_node {PSyn1 PSyn2 prefs1 prefs2} (G : @global PSyn1 prefs1) : (@node PSyn2 prefs2) -> Prop :=
  | normalized_Node : forall n locs blks,
      n_block n = Blocal locs blks ->
      Forall (fun '(_, (_, _, _, o)) => o = None) locs ->
      Forall (normalized_block G (ps_from_list (List.map fst (n_out n)))) blks ->
      normalized_node G n.

  Definition normalized_global {PSyn prefs} : @global PSyn prefs -> Prop :=
    wt_program normalized_node.

  Global Hint Constructors normalized_constant normalized_equation normalized_block : norm.

  (** *** normalized_node implies unnested_node *)

  Fact constant_normalized_lexp : forall e,
      normalized_constant e ->
      normalized_lexp e.
  Proof.
    intros e Hconst.
    induction Hconst; auto with norm.
  Qed.

  Fact normalized_eq_unnested_eq {PSyn prefs} : forall (G : @global PSyn prefs) to_cut eq,
      normalized_equation G to_cut eq ->
      unnested_equation G eq.
  Proof.
    intros * Hnormed. inv Hnormed; eauto using constant_normalized_lexp with norm.
  Qed.

  Fact normalized_block_unnested_block {PSyn prefs} : forall (G : @global PSyn prefs) to_cut block,
      normalized_block G to_cut block ->
      unnested_block G block.
  Proof.
    intros * Hnormed.
    induction Hnormed; constructor; auto.
    eapply normalized_eq_unnested_eq; eauto.
  Qed.

  Fact normalized_node_unnested_node {PSyn1 PSyn2 prefs1 prefs2} : forall (G : @global PSyn1 prefs1) (n : @node PSyn2 prefs2),
      normalized_node G n ->
      unnested_node G n.
  Proof.
    intros * Hnormed.
    inv Hnormed. econstructor; eauto.
    solve_forall.
    eapply normalized_block_unnested_block; eauto.
  Qed.

  Fact normalized_global_unnested_global {PSyn prefs} : forall (G : @global PSyn prefs),
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

  Fact init_var_for_clock_normalized_eq {PSyn prefs} : forall (G : @global PSyn prefs) ck id eqs' out st st',
      st_valid_after st out ->
      init_var_for_clock ck st = (id, eqs', st') ->
      Forall (normalized_equation G out) eqs'.
  Proof.
    intros * Hvalid Hinit.
    unfold init_var_for_clock in Hinit.
    destruct (fresh_ident _ _) eqn:Hfresh. inv Hinit.
    repeat constructor.
    + eapply fresh_ident_nIn' in Hfresh; eauto.
    + apply add_whens_is_constant; auto with norm.
    + apply add_whens_normalized_lexp; auto with norm.
  Qed.

  Fact normfby_equation_normalized_eq {PSyn prefs} : forall (G : @global PSyn prefs) out to_cut eq eqs' st st',
      st_valid_after st out ->
      unnested_equation G eq ->
      PS.Subset out to_cut ->
      normfby_equation to_cut eq st = (eqs', st') ->
      Forall (normalized_equation G out) eqs'.
  Proof with eauto with norm.
    intros * Hvalid Hunt Hsub Hfby.
    inv Hunt; simpl in *; repeat inv_bind; eauto.
    1:destruct_to_singl xs; repeat inv_bind...
    - (* fby *)
      (destruct ann0 as (?&?); destruct (is_constant e0) eqn:Hconst;
       [apply is_constant_normalized_constant in Hconst;
        destruct PS.mem eqn:Hmem; [|apply PSE.mem_4 in Hmem]|]; repeat inv_bind).
      1-3:repeat constructor...
      2,3:repeat esplit...
      + eapply fresh_ident_nIn'...
      + intros ??; congruence.
      + eapply fresh_ident_nIn' in H2; eauto.
        eapply init_var_for_clock_st_valid; eauto.
      + apply add_whens_is_constant; destruct t; simpl...
      + eapply init_var_for_clock_normalized_eq; eauto.
    - (* arrow *)
      destruct ann0 as (?&?) eqn:Vars; repeat inv_bind.
      repeat constructor; eauto.
      1-2:repeat esplit; eauto...
      intros ??; congruence.
      eapply init_var_for_clock_normalized_eq; eauto.
    - (* cexp *)
      inv H; repeat inv_bind; auto...
      inv H0; repeat inv_bind; auto...
  Qed.

  Fact normfby_block_normalized_block {PSyn prefs} : forall (G : @global PSyn prefs) out to_cut d blocks' st st',
      st_valid_after st out ->
      unnested_block G d ->
      PS.Subset out to_cut ->
      normfby_block to_cut d st = (blocks', st') ->
      Forall (normalized_block G out) blocks'.
  Proof.
    induction d using block_ind2; intros * Hvalid Hun Hsub Hfby; inv Hun;
      simpl in Hfby; try destruct ann0; repeat inv_bind.
    - eapply normfby_equation_normalized_eq in H; eauto.
      rewrite Forall_map. eapply Forall_impl; [|eauto]; eauto with norm.
    - apply Forall_singl in H.
      apply H in H0; auto.
      rewrite Forall_map. eapply Forall_impl; [|eauto]; eauto with norm.
  Qed.

  Corollary normfby_blocks_normalized_block {PSyn prefs} : forall (G : @global PSyn prefs) out to_cut blocks blocks' st st',
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

  Lemma normfby_block_GoodLocals to_cut : forall prefs blk blk' st st',
      GoodLocals prefs blk ->
      normfby_block to_cut blk st = (blk', st') ->
      Forall (GoodLocals prefs) blk'.
  Proof.
    induction blk using block_ind2; intros * Hgood Hun; inv Hgood; repeat inv_bind.
    - (* equation *)
      eapply Forall_map, Forall_forall; intros * Hin. constructor.
    - (* reset *)
      simpl in Hun. cases; repeat inv_bind; repeat (constructor; auto).
      apply Forall_singl in H. apply Forall_singl in H1.
      rewrite Forall_map. eapply Forall_impl; [|eauto]. intros ??. constructor; auto.
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
      rewrite Forall_map. eapply Forall_forall; intros. constructor.
    - (* reset *)
      unfold normfby_block in Hun.
      cases; repeat inv_bind; auto.
      inv Hnd. apply Forall_singl in H3. apply Forall_singl in H.
      rewrite Forall_map. eapply H in H0; eauto.
      solve_forall. constructor; auto.
  Qed.

  Corollary normfby_blocks_NoDupLocals G env : forall blks blks' st st',
      Forall (NoDupLocals env) blks ->
      normfby_blocks G blks st = (blks', st') ->
      Forall (NoDupLocals env) blks'.
  Proof.
    intros * Hnd Hun. unfold normfby_blocks in Hun; repeat inv_bind.
    eapply mmap_NoDupLocals in H; eauto.
    solve_forall. eapply normfby_block_NoDupLocals; eauto.
  Qed.

  (** *** nolocal *)

  Lemma normfby_block_nolocal : forall to_cut blk blks' st st',
      nolocal_block blk ->
      normfby_block to_cut blk st = (blks', st') ->
      Forall nolocal_block blks'.
  Proof.
    induction blk using block_ind2; intros * Hnl Hun; inv Hnl; repeat inv_bind.
    - (* equation *)
      rewrite Forall_map, Forall_forall. intros. constructor.
    - (* reset *)
      unfold normfby_block in *. cases; repeat inv_bind; repeat (constructor; auto).
      apply Forall_singl in H. apply Forall_singl in H1.
      eapply H in H0; eauto.
      rewrite Forall_map. eapply Forall_impl; [|eauto]; intros.
      repeat constructor; auto.
  Qed.

  Corollary normfby_blocks_nolocal : forall to_cut blks blks' st st',
      Forall nolocal_block blks ->
      normfby_blocks to_cut blks st = (blks', st') ->
      Forall nolocal_block blks'.
  Proof.
    unfold normfby_blocks.
    intros * Hf Hun; repeat inv_bind.
    eapply mmap_values, Forall2_ignore1 in H.
    eapply Forall_concat, Forall_impl; [|eauto]; intros ? (?&?&?&?&?).
    eapply Forall_forall in Hf; eauto.
    eapply normfby_block_nolocal; eauto.
  Qed.

  (** ** Normalization of a full node *)

  Lemma norm2_not_in_norm1_prefs :
    ~PS.In norm2 norm1_prefs.
  Proof.
    unfold norm1_prefs, local_prefs, switch_prefs, last_prefs, elab_prefs.
    rewrite 4 PSF.add_iff, PSF.singleton_iff.
    pose proof gensym_prefs_NoDup as Hnd. unfold gensym_prefs in Hnd.
    repeat rewrite NoDup_cons_iff in Hnd. destruct_conjs.
    intros [contra|[contra|[contra|[contra|contra]]]]; rewrite contra in *; eauto 10 with datatypes.
  Qed.

  Lemma normfby_node_init_st_valid {A} : forall (n: @node nolocal_top_block norm1_prefs) locs blks,
      n_block n = Blocal locs blks ->
      st_valid_after (@init_st A) (PSP.of_list (map fst (n_in n ++ n_out n ++ Common.idty locs))).
  Proof.
    intros * Hn.
    specialize (n_nodup n) as (Hndup&Hndl).
    rewrite Hn in *.
    rewrite fst_NoDupMembers in Hndup; simpl in Hndup.
    inv Hndl. simpl in *.
    eapply init_st_valid.
    - apply norm2_not_in_norm1_prefs.
    - rewrite <- ps_from_list_ps_of_list, PS_For_all_Forall'.
      pose proof (n_good n) as (Good1&Good2&_); eauto. rewrite Hn in Good2. inv Good2.
      rewrite app_assoc, map_app, Forall_app, map_fst_idty.
      split; auto.
  Qed.

  Program Definition normfby_node (* (to_cut : PS.t) *) (n : @node nolocal_top_block norm1_prefs) : @node nolocal_top_block norm2_prefs :=
    {| n_name := n_name n;
       n_hasstate := n_hasstate n;
       n_in := n_in n;
       n_out := n_out n;
       n_block := match (n_block n) with
                  | Blocal vars blks =>
                    let res := normfby_blocks (ps_from_list (map fst (n_out n))) blks init_st in
                    let nvars := st_anns (snd res) in
                    Blocal (vars++map (fun xtc => (fst xtc, ((fst (snd xtc)), snd (snd xtc), xH, None))) nvars) (fst res)
                  | blk => blk
                  end;
       n_ingt0 := n_ingt0 n;
       n_outgt0 := n_outgt0 n;
    |}.
  Next Obligation.
    specialize (n_defd n) as (?&Hvars&Hperm).
    destruct (n_block n) eqn:Hn; eauto. inv Hvars.
    destruct (normfby_blocks _ _ _) as (blks'&st') eqn:Hblks.
    do 2 esplit; [|eauto].
    eapply normfby_blocks_vars_perm in Hblks as (ys&Hvars&Hperm'); eauto.
    econstructor; eauto.
    unfold st_ids in *. rewrite init_st_anns, app_nil_r in Hperm'.
    rewrite Hperm', <-H3, map_app, <-2 app_assoc.
    apply Permutation_app_head. rewrite Permutation_app_comm. apply Permutation_app_head.
    rewrite map_map; simpl. reflexivity.
  Qed.
  Next Obligation.
    pose proof (n_good n) as (Hgood1&Hgood&_).
    pose proof (n_nodup n) as (Hndup&Hndl).
    destruct (n_block n) as [| | |locs blks] eqn:Hblk; eauto.
    destruct (normfby_blocks _ blks init_st) as (blks'&st') eqn:Hunn.
    repeat rewrite app_nil_r. split; simpl in *; auto.
    inv Hndl. rewrite fst_NoDupMembers in H3.
    assert (st_valid_after st' (PSP.of_list (map fst (n_in n ++ n_out n ++ Common.idty locs)))) as Hvalid.
    { eapply normfby_blocks_st_valid; eauto.
      eapply normfby_node_init_st_valid; eauto.
    }
    assert (Hvalid':=Hvalid). eapply st_valid_after_NoDupMembers in Hvalid.
    2:{ rewrite app_assoc. apply NoDupMembers_app; auto.
        - rewrite NoDupMembers_idty, fst_NoDupMembers; auto.
        - intros * Hinm Hinl. rewrite fst_InMembers in Hinm. rewrite InMembers_idty in Hinl.
          eapply H4; eauto using in_or_app.
    }
    constructor; simpl.
    - eapply normfby_blocks_NoDupLocals; [|eauto].
      inv Hgood.
      eapply Forall_impl_In; [|eapply H1]; intros.
      eapply NoDupLocals_incl' with (npref:=norm2). 1,2,4:eauto using norm2_not_in_norm1_prefs.
      eapply Forall_forall in H5; eauto.
      assert (Forall (fun id => exists x hint, id = gensym norm2 hint x) (st_ids st')) as Hids.
      { eapply st_valid_prefixed; eauto. }
      intros ? Hin. repeat rewrite map_app in *. repeat rewrite in_app_iff in *. destruct Hin as [[?|Hin]|[Hin|Hin]]; auto.
      rewrite map_map in Hin. eapply Forall_forall in Hids; eauto.
    - rewrite 2 map_app, map_fst_idty in Hvalid.
      rewrite fst_NoDupMembers, map_app, map_map.
      solve_NoDup_app.
    - rewrite app_assoc, map_app, <-app_assoc in Hvalid.
      setoid_rewrite InMembers_app. intros * [Hinm|Hinm] Hin'; eauto.
      + eapply H4; eauto.
      + rewrite fst_InMembers, map_map in Hinm.
        eapply st_valid_prefixed, Forall_forall in Hvalid' as (?&?&?); eauto; subst.
        eapply Forall_forall in Hgood1; eauto.
        inv Hgood1.
        * apply gensym_not_atom in H; auto.
        * destruct H as (?&Hin&?&?&Hgen). apply gensym_injective in Hgen as (?&?); subst.
          eapply norm2_not_in_norm1_prefs in Hin; eauto.
  Qed.
  Next Obligation.
    specialize (n_good n) as (Hgood1&Hgood2&Hname). repeat split; eauto using AtomOrGensym_add.
    destruct (n_block n) as [| | |locs blks] eqn:Hblk; eauto using GoodLocals_add.
    destruct (normfby_blocks _ blks init_st) as (blks'&st') eqn:Heqres.
    assert (st_valid_after st' (PSP.of_list (map fst (n_in n ++ n_out n ++ Common.idty locs)))) as Hvalid.
    { specialize (n_nodup n) as (Hndup&Hndl).
      rewrite Hblk in Hndl; simpl in Hndl. inv Hndl. rewrite fst_NoDupMembers in H3.
      eapply normfby_blocks_st_valid; eauto.
      eapply normfby_node_init_st_valid; eauto.
    }
    inv Hgood2.
    constructor.
    + repeat rewrite map_app. repeat rewrite Forall_app. repeat split; eauto using AtomOrGensym_add.
      eapply st_valid_prefixed in Hvalid; auto; simpl.
      erewrite map_map, map_ext with (g:=fst); [eauto|]. 2:intros (?&?&?); auto.
      eapply Forall_impl; [|eauto]. intros ? (?&?); subst. right.
      do 2 esplit; eauto. now apply PSF.add_1.
    + eapply normfby_blocks_GoodLocals in H2; eauto.
      rewrite Forall_forall in *; eauto using GoodLocals_add.
  Qed.
  Next Obligation.
    pose proof (n_syn n) as Hsyn. inv Hsyn.
    constructor.
    - apply Forall_app; split; auto.
      simpl_Forall; auto.
    - eapply normfby_blocks_nolocal; eauto using surjective_pairing.
  Qed.

  Global Program Instance normfby_node_transform_unit: TransformUnit node node :=
    { transform_unit := normfby_node }.

  Global Program Instance normfby_global_without_units : TransformProgramWithoutUnits (@global nolocal_top_block norm1_prefs) (@global nolocal_top_block norm2_prefs) :=
    { transform_program_without_units := fun g => Global g.(enums) [] }.

  Definition normfby_global : @global nolocal_top_block norm1_prefs -> @global nolocal_top_block norm2_prefs := transform_units.

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

  Fact normfby_nodes_names {PSyn prefs} : forall (a : @node PSyn prefs) nds,
      Forall (fun n => (n_name a <> n_name n)%type) nds ->
      Forall (fun n => (n_name a <> n_name n)%type) (map normfby_node nds).
  Proof.
    induction nds; intros * Hnames; simpl.
    - constructor.
    - inv Hnames.
      constructor; eauto.
  Qed.

  (** *** After normalization, a global is normalized *)

  Fact normfby_node_normalized_node {PSyn prefs} : forall (G : @global PSyn prefs) n,
      unnested_node G n ->
      normalized_node G (normfby_node n).
  Proof.
    intros * Hunt. inversion_clear Hunt as [??? Hblk Hblks].
    econstructor; simpl. rewrite Hblk; eauto.
    - apply Forall_app; split; auto. simpl_Forall; auto.
    - pose proof (n_good n) as (Good&_).
      destruct (normfby_blocks _ _ _) as (blks'&st') eqn:Hnorm.
      eapply normfby_blocks_normalized_block in Hnorm; eauto.
      2:rewrite ps_from_list_ps_of_list; reflexivity.
      { eapply init_st_valid.
        - apply norm2_not_in_norm1_prefs.
        - rewrite PS_For_all_Forall.
          eapply Forall_incl; eauto.
          intros ? Hin.
          rewrite ps_from_list_ps_of_list, ps_of_list_ps_to_list in Hin.
          rewrite map_app, in_app_iff; auto. }
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
       (Senv : STATICENV Ids Op OpAux Cks)
       (Syn : LSYNTAX Ids Op OpAux Cks Senv)
       (Unt : UNNESTING Ids Op OpAux Cks Senv Syn)
       <: NORMFBY Ids Op OpAux Cks Senv Syn Unt.
  Include NORMFBY Ids Op OpAux Cks Senv Syn Unt.
End NormFbyFun.
