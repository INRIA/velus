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
  Definition init_var_for_clock (ck : clock) xr : FreshAnn (ident * list equation) :=
    fun st => let (x, st') := fresh_ident norm2 (OpAux.bool_velus_type, ck) st in
           ((x, [([x], [Efby [add_whens (Eenum 1 bool_velus_type) bool_velus_type ck]
                             [add_whens (Eenum 0 bool_velus_type) bool_velus_type ck]
                             (map (fun '(x, ck) => Evar x (bool_velus_type, ck)) xr)
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
  Definition fby_iteexp (e0 : exp) (e : exp) (xr : list (ident * nclock)) (ann : ann) : FreshAnn (exp * list equation) :=
    let '(ty, (ck, name)) := ann in
    do (initid, eqs) <- init_var_for_clock ck xr;
    do px <- fresh_ident norm2 (ty, ck);
    ret (Ecase (Evar initid (bool_velus_type, (ck, Some initid)))
               [None; Some [e0]] [Evar px (ty, (ck, Some px))] ([ty], (ck, name)),
         ([px], [Efby [add_whens (init_type ty) ty ck] [e] [] [ann]])::eqs).

  Definition arrow_iteexp (e0 : exp) (e : exp) (xr : list (ident * nclock)) (ann : ann) : FreshAnn (exp * list equation) :=
    let '(ty, (ck, name)) := ann in
    do (initid, eqs) <- init_var_for_clock ck xr;
    ret (Ecase (Evar initid (bool_velus_type, (ck, Some initid))) [None; Some [e0]] [e]
              ([ty], (ck, name)), eqs).

  Definition vars_of (es : list exp) :=
    omap (fun e => match e with
                | Evar x (_, ck) => Some (x, ck)
                | _ => None
                end) es.

  Definition fby_equation (to_cut : PS.t) (eq : equation) : FreshAnn (list equation) :=
    match eq with
    | ([x], [Efby [e0] [e] er [ann]]) =>
      let '(ty, (ck, _)) := ann in
      if is_constant e0 then
        if PS.mem x to_cut then
          do x' <- fresh_ident norm2 (ty, ck);
          ret [([x], [Evar x' ann]); ([x'], [Efby [e0] [e] er [ann]])]
        else ret [eq]
      else
        match (vars_of er) with
        | Some xr =>
          do (fby, eqs) <- fby_iteexp e0 e xr ann; ret (([x], [fby])::eqs)
        | _ => ret [eq] (* Should not happen *)
        end
    | ([x], [Earrow [e0] [e] er [ann]]) =>
      match (vars_of er) with
      | Some xr =>
        do (ite, eqs) <- arrow_iteexp e0 e xr ann;
        ret (([x], [ite])::eqs)
      | _ => ret [eq] (* Should not happen *)
      end
    | _ => ret [eq]
    end.

  Definition fby_equations (to_cut : PS.t) (eqs : list equation) : FreshAnn (list equation) :=
    do eqs' <- mmap (fby_equation to_cut) eqs;
    ret (concat eqs').

  (** Some initial properties *)

  Local Ltac destruct_to_singl l :=
    destruct l; [|destruct l]; auto.

  Fact vars_of_spec: forall es xr,
      vars_of es = Some xr <->
      Forall2 (fun e '(x, ck) => exists ty, e = Evar x (ty, ck)) es xr.
  Proof.
    induction es; intros *; simpl in *; split; intros H.
    - inv H; auto.
    - inv H; auto.
    - destruct a; inv H.
      destruct a. destruct (vars_of es) eqn:Vars; inv H1.
      constructor; eauto. eapply IHes; eauto.
    - inv H. destruct y, H2 as (?&?); subst.
      eapply IHes in H4. rewrite H4; auto.
  Qed.

  Lemma vars_of_Some: forall es,
      Forall (fun e : exp => exists (x : ident) (ann : ann), e = Evar x ann) es ->
      exists xr, vars_of es = Some xr.
  Proof.
    induction es; intros F; inv F.
    - exists []; auto.
    - eapply IHes in H2 as (xr&?).
      destruct H1 as (?&(?&?)&?); subst.
      simpl. setoid_rewrite H. eauto.
  Qed.

  Fact fby_equation_spec : forall to_cut xs es,
      (exists x e0 e er ann,
          xs = [x] /\
          es = [Efby [e0] [e] er [ann]] /\
          is_constant e0 = true /\
          fby_equation to_cut (xs, es) =
          (let '(ty, (ck, _)) := ann in
           if PS.mem x to_cut then
             do x' <- fresh_ident norm2 (ty, ck);
             ret [([x], [Evar x' ann]); ([x'], es)]
           else ret [(xs, es)]))
      \/ (exists x e0 e er ann xr,
          xs = [x] /\
          es = [Efby [e0] [e] er [ann]] /\
          is_constant e0 = false /\
          Forall2 (fun er '(x, ck) => exists ty, er = Evar x (ty, ck)) er xr /\
          fby_equation to_cut (xs, es) =
          (do (fby, eqs) <- fby_iteexp e0 e xr ann;
           ret (([x], [fby])::eqs)))
      \/ (exists x e0 e er ann xr,
            xs = [x] /\
            es = [Earrow [e0] [e] er [ann]] /\
            Forall2 (fun er '(x, ck) => exists ty, er = Evar x (ty, ck)) er xr /\
            fby_equation to_cut (xs, es) =
            (do (ite, eqs) <- arrow_iteexp e0 e xr ann;
             ret (([x], [ite])::eqs)))
      \/ fby_equation to_cut (xs, es) = (ret [(xs, es)]).
  Proof.
    intros *.
    destruct_to_singl xs. destruct_to_singl es.
    2: { repeat right; simpl. destruct e; auto.
         1,2,3:(destruct_to_singl l; destruct_to_singl l0; destruct_to_singl l2).
    }
    destruct e; auto.
    1,2:destruct_to_singl l; destruct_to_singl l0; destruct_to_singl l2; simpl.
    - (* fby *)
      destruct a as [ty [ck name]].
      destruct (is_constant e) eqn:Hconst; simpl.
      + left. repeat eexists; eauto.
      + right.
        destruct (vars_of l1) eqn:Vars; simpl; [left|repeat right]; auto.
        repeat eexists; eauto. eapply vars_of_spec; eauto.
    - (* arrow *)
      destruct a as [ty [ck name]]. right. right.
      destruct (vars_of l1) eqn:Vars; simpl; [left|right]; auto.
      repeat eexists; eauto. eapply vars_of_spec; eauto.
  Qed.

  Ltac inv_fby_equation Hfby to_cut eq :=
    let Hspec := fresh "Hspec" in
    let Hconst := fresh "Hconst" in
    let Hr := fresh "Hr" in
    destruct eq as [xs es];
    specialize (fby_equation_spec to_cut xs es) as
        [(?&?&?&?&?&?&?&Hconst&Hspec)|[(?&?&?&?&?&?&?&?&Hconst&Hr&Hspec)|[(?&?&?&?&?&?&?&?&Hr&Hspec)|Hspec]]];
    subst; rewrite Hspec in Hfby; clear Hspec; repeat inv_bind; auto.

  (** *** Preservation of st_valid *)

  Definition st_valid_after {B} st aft := @st_valid_after B st norm2 aft.
  Hint Unfold st_valid_after.

  Fact init_var_for_clock_st_valid : forall ck er res st st' aft,
      init_var_for_clock ck er st = (res, st') ->
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

  Fact fby_iteexp_st_valid : forall e0 e er a e' eqs' st st' aft,
      fby_iteexp e0 e er a st = (e', eqs', st') ->
      st_valid_after st aft ->
      st_valid_after st' aft.
  Proof with eauto.
    intros e0 e er [ty [ck name]] e' eqs' st st' aft Hfby Hvalid.
    unfold fby_iteexp in Hfby.
    destruct (is_constant e0); repeat inv_bind;
      eapply fresh_ident_st_valid, init_var_for_clock_st_valid; eauto.
  Qed.
  Hint Resolve fby_iteexp_st_valid.

  Fact arrow_iteexp_st_valid : forall e0 e er a e' eqs' st st' aft,
      arrow_iteexp e0 e er a st = (e', eqs', st') ->
      st_valid_after st aft ->
      st_valid_after st' aft.
  Proof with eauto.
    intros e0 e er [ty [ck name]] e' eqs' st st' aft Hfby Hvalid.
    unfold arrow_iteexp in Hfby.
    repeat inv_bind...
  Qed.
  Hint Resolve arrow_iteexp_st_valid.

  Fact fby_equation_st_valid : forall to_cut eq eqs' st st' aft,
      fby_equation to_cut eq st = (eqs', st') ->
      st_valid_after st aft ->
      st_valid_after st' aft.
  Proof.
    intros * Hfby Hvalid.
    inv_fby_equation Hfby to_cut eq.
    - destruct x3 as [ty [ck name]]; repeat inv_bind.
      destruct (PS.mem _ _); repeat inv_bind; auto.
      eapply fresh_ident_st_valid; eauto.
    - eapply fby_iteexp_st_valid; eauto.
    - eapply arrow_iteexp_st_valid; eauto.
  Qed.

  Fact fby_equations_st_valid : forall to_cut eqs eqs' st st' aft,
      fby_equations to_cut eqs st = (eqs', st') ->
      st_valid_after st aft ->
      st_valid_after st' aft.
  Proof.
    intros * Hfby Hst.
    unfold fby_equations in Hfby; repeat inv_bind.
    eapply mmap_st_valid in Hst; eauto.
    solve_forall. eapply fby_equation_st_valid; eauto.
  Qed.

  (** *** Preservation of st_follows *)

  Fact init_var_for_clock_st_follows : forall ck er res st st',
      init_var_for_clock ck er st = (res, st') ->
      st_follows st st'.
  Proof.
    intros * Hinit.
    unfold init_var_for_clock in Hinit.
    repeat inv_bind.
    destruct (fresh_ident _ _) eqn:Hfresh. inv Hinit.
    apply fresh_ident_st_follows in Hfresh. auto.
  Qed.
  Hint Resolve init_var_for_clock_st_follows.

  Fact fby_iteexp_st_follows : forall e0 e er ann res st st',
      fby_iteexp e0 e er ann st = (res, st') ->
      st_follows st st'.
  Proof.
    intros e0 e er [ty [ck name]] res st st' Hfby.
    unfold fby_iteexp in Hfby; repeat inv_bind.
    etransitivity; eauto.
  Qed.
  Hint Resolve fby_iteexp_st_follows.

  Fact arrow_iteexp_st_follows : forall e0 e er ann res st st',
      arrow_iteexp e0 e er ann st = (res, st') ->
      st_follows st st'.
  Proof.
    intros e0 e er [ty [ck name]] res st st' Hfby.
    unfold arrow_iteexp in Hfby.
    repeat inv_bind; eauto.
  Qed.
  Hint Resolve arrow_iteexp_st_follows.

  Fact fby_equation_st_follows : forall to_cut eq eqs' st st',
      fby_equation to_cut eq st = (eqs', st') ->
      st_follows st st'.
  Proof.
    intros * Hfby.
    inv_fby_equation Hfby to_cut eq.
    - destruct x3 as [ty [ck name]].
      destruct (PS.mem _ _); repeat inv_bind.
      1,2:repeat solve_st_follows.
    - eapply fby_iteexp_st_follows; eauto.
    - eapply arrow_iteexp_st_follows; eauto.
    - reflexivity.
  Qed.
  Hint Resolve fby_equation_st_follows.

  Fact fby_equations_st_follows : forall to_cut eqs eqs' st st',
      fby_equations to_cut eqs st = (eqs', st') ->
      st_follows st st'.
  Proof.
    intros * Hfby. unfold fby_equations in *; repeat inv_bind.
    eapply mmap_st_follows; eauto.
    solve_forall.
  Qed.

  (** *** The variables generated are a permutation of the ones contained in the state *)

  Fact init_var_for_clock_vars_perm : forall ck r id eqs st st',
      init_var_for_clock ck r st = ((id, eqs), st') ->
      Permutation ((vars_defined eqs)++(st_ids st)) (st_ids st').
  Proof.
    intros * Hinit.
    unfold init_var_for_clock in Hinit. repeat inv_bind.
    destruct (fresh_ident _ _) eqn:Hfresh. inv Hinit.
    apply fresh_ident_vars_perm in Hfresh.
    simpl. assumption.
  Qed.

  Fact fby_iteexp_vars_perm : forall e0 e er ann e' eqs' st st',
      fby_iteexp e0 e er ann st = (e', eqs', st') ->
      Permutation ((vars_defined eqs')++(st_ids st)) (st_ids st').
  Proof.
    intros ? ? ? [ty [ck name]] ? ? ? ? Hfby.
    unfold fby_iteexp in Hfby. repeat inv_bind.
    eapply init_var_for_clock_vars_perm in H; eauto.
    eapply fresh_ident_vars_perm in H0.
    simpl.
    rewrite <- H0. apply perm_skip; auto.
  Qed.

  Fact arrow_iteexp_vars_perm : forall e0 e er ann e' eqs' st st',
      arrow_iteexp e0 e er ann st = (e', eqs', st') ->
      Permutation ((vars_defined eqs')++(st_ids st)) (st_ids st').
  Proof.
    intros ? ? ? [ty [ck name]] ? ? ? ? Hfby.
    unfold arrow_iteexp in Hfby. repeat inv_bind.
    eapply init_var_for_clock_vars_perm in H; eauto.
  Qed.

  Fact fby_equation_vars_perm : forall to_cut eq eqs' st st',
      fby_equation to_cut eq st = (eqs', st') ->
      Permutation ((vars_defined eqs')++(st_ids st)) ((vars_defined [eq])++(st_ids st')).
  Proof.
    intros * Hfby.
    inv_fby_equation Hfby to_cut eq.
    destruct x3 as [ty [ck name]]; repeat inv_bind.
    - destruct PS.mem; repeat inv_bind; simpl; auto.
      eapply fresh_ident_vars_perm in H.
      apply perm_skip; auto.
    - simpl. apply perm_skip.
      eapply fby_iteexp_vars_perm in H; eauto.
    - eapply arrow_iteexp_vars_perm in H; simpl; auto.
  Qed.

  Fact fby_equations_vars_perm : forall to_cut eqs eqs' st st',
      fby_equations to_cut eqs st = (eqs', st') ->
      Permutation ((vars_defined eqs')++(st_ids st)) ((vars_defined eqs)++(st_ids st')).
  Proof.
    induction eqs; intros * Hnorm; unfold fby_equations in Hnorm; repeat inv_bind.
    - reflexivity.
    - assert (fby_equations to_cut eqs x1 = (concat x2, st')) as Hnorm'.
      { unfold fby_equations. repeat inv_bind; eauto. }
      eapply IHeqs in Hnorm'; eauto.
      eapply fby_equation_vars_perm in H; eauto; simpl in *.
      repeat simpl_list.
      rewrite Permutation_swap, H, Permutation_swap.
      apply Permutation_app_head. assumption.
  Qed.

  (** *** Preservation of annotations *)

  Fact fby_iteexp_annot : forall e0 e er ann es' eqs' st st',
      fby_iteexp e0 e er ann st = (es', eqs', st') ->
      annot es' = [ann].
  Proof.
    intros e0 e er [ty [cl n]] es' eqs' st st' Hfby.
    unfold fby_iteexp in Hfby.
    repeat inv_bind; reflexivity.
  Qed.

  Fact arrow_iteexp_annot : forall e0 e er ann es' eqs' st st',
      arrow_iteexp e0 e er ann st = (es', eqs', st') ->
      annot es' = [ann].
  Proof.
    intros e0 e er [ty [cl n]] es' eqs' st st' Hfby.
    unfold arrow_iteexp in Hfby.
    repeat inv_bind; reflexivity.
  Qed.

  (** *** Additional props *)

  Fact init_var_for_clock_In : forall ck xr id eqs' st st',
      init_var_for_clock ck xr st = (id, eqs', st') ->
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
  | normalized_eq_Efby : forall out x e0 e er ann,
      ~PS.In x out ->
      normalized_constant e0 ->
      normalized_lexp e ->
      Forall (fun e => exists x ann, e = Evar x ann) er ->
      normalized_equation G out ([x], [Efby [e0] [e] er [ann]])
  | normalized_eq_cexp : forall out x e,
      normalized_cexp e ->
      normalized_equation G out ([x], [e]).

  Definition normalized_node {prefs1 prefs2} (G : @global prefs1) (n : @node prefs2) :=
    Forall (normalized_equation G (ps_from_list (List.map fst (n_out n)))) (n_eqs n).

  Definition normalized_global {prefs} : @global prefs -> Prop
    := wt_program normalized_node.

  Hint Constructors normalized_constant normalized_equation.

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

  Fact normalized_node_unnested_node {prefs1 prefs2} : forall (G : @global prefs1) (n : @node prefs2),
      normalized_node G n ->
      unnested_node G n.
  Proof.
    intros * Hnormed.
    unfold normalized_node, unnested_node in *.
    solve_forall.
    eapply normalized_eq_unnested_eq; eauto.
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

  Fact init_var_for_clock_wl {prefs} : forall (G : @global prefs) ck xr id eqs' st st',
      init_var_for_clock ck xr st = (id, eqs', st') ->
      Forall (wl_equation G) eqs'.
  Proof.
    intros * Hinit.
    unfold init_var_for_clock in Hinit.
    destruct (fresh_ident _ _). inv Hinit.
    repeat constructor; simpl.
    1,2:apply add_whens_wl; auto.
    2,3:simpl; rewrite app_nil_r, length_annot_numstreams; apply add_whens_numstreams; auto.
    1,2:rewrite Forall_map; eapply Forall_forall; intros (?&?) ?; eauto.
  Qed.

  Fact fby_iteexp_numstreams : forall e0 e er a e' eqs' st st',
      fby_iteexp e0 e er a st = (e', eqs', st') ->
      numstreams e' = 1.
  Proof.
    intros * Hfby. destruct a as [ty [ck name]].
    unfold fby_iteexp in Hfby.
    repeat inv_bind; simpl; auto.
  Qed.

  Fact fby_iteexp_wl_exp {prefs} : forall (G : @global prefs) e0 e xr a e' eqs' st st',
      wl_exp G e0 ->
      wl_exp G e ->
      numstreams e0 = 1 ->
      numstreams e = 1 ->
      fby_iteexp e0 e xr a st = (e', eqs', st') ->
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
    - intros ? [Heq|[Heq|Heq]]; inv Heq; simpl.
      rewrite app_nil_r, length_annot_numstreams; auto.
  Qed.

  Fact fby_iteexp_wl_eq {prefs} : forall (G : @global prefs) e0 e xr a e' eqs' st st',
      wl_exp G e0 ->
      wl_exp G e ->
      numstreams e0 = 1 ->
      numstreams e = 1 ->
      fby_iteexp e0 e xr a st = (e', eqs', st') ->
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

  Fact arrow_iteexp_numstreams : forall e0 e er a e' eqs' st st',
      arrow_iteexp e0 e er a st = (e', eqs', st') ->
      numstreams e' = 1.
  Proof.
    intros * Hfby. destruct a as [ty [ck name]].
    unfold arrow_iteexp in Hfby.
    repeat inv_bind. reflexivity.
  Qed.

  Fact arrow_iteexp_wl_exp {prefs} : forall (G : @global prefs) e0 e er a e' eqs' st st',
      wl_exp G e0 ->
      wl_exp G e ->
      numstreams e0 = 1 ->
      numstreams e = 1 ->
      arrow_iteexp e0 e er a st = (e', eqs', st') ->
      wl_exp G e'.
  Proof.
    intros * Hwl1 Hwl2 Hn1 Hn2 Hfby. destruct a as [ty [ck name]].
    unfold arrow_iteexp in Hfby; repeat inv_bind.
    repeat constructor; auto; simpl.
    congruence.
    1,2:intros ? [Heq|[Heq|Heq]]; inv Heq; simpl; auto.
    1,2:rewrite app_nil_r, length_annot_numstreams; auto.
  Qed.

  Fact arrow_iteexp_wl_eq {prefs} : forall (G : @global prefs) e0 e xr a e' eqs' st st',
      wl_exp G e0 ->
      wl_exp G e ->
      numstreams e0 = 1 ->
      numstreams e = 1 ->
      arrow_iteexp e0 e xr a st = (e', eqs', st') ->
      Forall (wl_equation G) eqs'.
  Proof.
    intros * Hwl1 Hwl2 Hn1 Hn2 Hfby.
    destruct a as [ty [ck name]].
    unfold arrow_iteexp in Hfby; repeat inv_bind.
    eapply init_var_for_clock_wl in H; eauto.
  Qed.

  Fact fby_equation_wl {prefs} : forall (G : @global prefs) to_cut eq eqs' st st',
      wl_equation G eq ->
      fby_equation to_cut eq st = (eqs', st') ->
      Forall (wl_equation G) eqs'.
  Proof.
    intros * Hwl Hfby.
    inv_fby_equation Hfby to_cut eq.
    - destruct x3 as [ty [ck name]].
      destruct PS.mem; repeat inv_bind; auto.
      destruct Hwl as [Hwl _]; inv Hwl; repeat (constructor; auto).
    - destruct Hwl as [Hwl _]. apply Forall_singl in Hwl.
      inv Hwl.
      apply Forall_singl in H4. apply Forall_singl in H5.
      simpl in *. rewrite app_nil_r, length_annot_numstreams in *.
      repeat constructor; simpl; try rewrite app_nil_r.
      + eapply fby_iteexp_wl_exp in H; eauto.
      + eapply fby_iteexp_annot in H; eauto.
        rewrite H; auto.
      + eapply fby_iteexp_wl_eq in H; eauto.
    - destruct Hwl as [Hwl _]. apply Forall_singl in Hwl.
      inv Hwl.
      apply Forall_singl in H4. apply Forall_singl in H5.
      simpl in *. rewrite app_nil_r, length_annot_numstreams in *.
      repeat constructor; simpl; try rewrite app_nil_r.
      + eapply arrow_iteexp_wl_exp in H; eauto.
      + eapply arrow_iteexp_annot in H; eauto.
        rewrite H; auto.
      + eapply arrow_iteexp_wl_eq in H; eauto.
  Qed.

  (** ** After normalization, equations and expressions are normalized *)

  Fact add_whens_is_constant : forall ty cl e,
      normalized_constant e ->
      normalized_constant (add_whens e ty cl).
  Proof.
    induction cl; intros e Hcons; simpl.
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

  Fact init_var_for_clock_unnested_eq {prefs} : forall (G : @global prefs) ck xr id eqs' st st',
      init_var_for_clock ck xr st = (id, eqs', st') ->
      Forall (unnested_equation G) eqs'.
  Proof.
    intros * Hinit.
    unfold init_var_for_clock in Hinit.
    destruct (fresh_ident _ _) eqn:Hfresh. inv Hinit.
    repeat constructor.
    1-2:eapply add_whens_normalized_lexp; eauto.
    rewrite Forall_map. apply Forall_forall. intros (?&?) ?; eauto.
  Qed.

  Fact init_var_for_clock_normalized_eq {prefs} : forall (G : @global prefs) ck xr id eqs' out st st',
      st_valid_after st out ->
      init_var_for_clock ck xr st = (id, eqs', st') ->
      Forall (normalized_equation G out) eqs'.
  Proof.
    intros * Hvalid Hinit.
    unfold init_var_for_clock in Hinit.
    destruct (fresh_ident _ _) eqn:Hfresh. inv Hinit.
    repeat constructor.
    + eapply fresh_ident_nIn' in Hfresh; eauto.
    + apply add_whens_is_constant; auto.
    + apply add_whens_normalized_lexp; auto.
    + rewrite Forall_map. apply Forall_forall. intros (?&?) ?; eauto.
  Qed.

  Fact fby_iteexp_unnested_eq {prefs} : forall (G : @global prefs) e0 e xr a e' eqs' st st',
      normalized_lexp e0 ->
      normalized_lexp e ->
      fby_iteexp e0 e xr a st = (e', eqs', st') ->
      Forall (unnested_equation G) eqs'.
  Proof.
    intros * Hnormed1 Hnormed2 Hfby. destruct a as [ty [ck name]].
    unfold fby_iteexp in Hfby.
    repeat inv_bind; auto.
    repeat constructor; auto.
    - apply add_whens_normalized_lexp; destruct ty; simpl; auto.
    - eapply init_var_for_clock_unnested_eq in H; eauto.
  Qed.

  Fact fby_iteexp_normalized_eq {prefs} : forall (G : @global prefs) e0 e xr a e' eqs' out st st',
      st_valid_after st out ->
      normalized_lexp e ->
      fby_iteexp e0 e xr a st = (e', eqs', st') ->
      Forall (normalized_equation G out) eqs'.
  Proof.
    intros G e0 e xr [ty [ck name]] * Hvalid He Hfby.
    unfold fby_iteexp in Hfby.
    repeat inv_bind; constructor.
    - assert (st_valid_after x1 out0) as Hvalid' by eauto.
      constructor; auto.
      + eapply fresh_ident_nIn' in H0; eauto.
      + eapply add_whens_is_constant; destruct ty; simpl; eauto.
    - eapply init_var_for_clock_normalized_eq in H; eauto.
  Qed.

  Fact fby_equation_unnested_eq {prefs} : forall (G : @global prefs) to_cut eq eqs' st st',
      unnested_equation G eq ->
      fby_equation to_cut eq st = (eqs', st') ->
      Forall (unnested_equation G) eqs'.
  Proof.
    intros * Hunt Hfby.
    inv_fby_equation Hfby to_cut eq;
      try destruct x3 as [ty [ck name]].
    - destruct PS.mem; repeat inv_bind; auto.
      inv Hunt; constructor; auto.
    - assert (H':=H). eapply fby_iteexp_unnested_eq in H'.
      constructor; eauto.
      repeat inv_bind. repeat constructor; eauto.
      1,2:intros ? Heq; inv Heq. exists x0; split; auto.
      1-3:(clear - Hunt; inv Hunt; eauto; inv H0; inv H).
    - repeat inv_bind. repeat constructor; auto.
      1,2:intros ? Heq; inv Heq. exists x0; split; auto.
      3:eapply init_var_for_clock_unnested_eq in H; eauto.
      1-2:(clear - Hunt; inv Hunt; eauto; inv H0; inv H).
  Qed.

  Fact fby_equation_normalized_eq {prefs} : forall (G : @global prefs) out to_cut eq eqs' st st',
      st_valid_after st out ->
      unnested_equation G eq ->
      PS.Subset out to_cut ->
      fby_equation to_cut eq st = (eqs', st') ->
      Forall (normalized_equation G out) eqs'.
  Proof.
    intros * Hvalid Hunt Hsub Hfby.
    inv Hunt; simpl in *; repeat inv_bind; eauto.
    1:destruct_to_singl xs; repeat inv_bind; eauto.
    - (* fby *)
      (destruct ann0 as (?&?&?); destruct (is_constant e0) eqn:Hconst;
       [apply is_constant_normalized_constant in Hconst;
        destruct PS.mem eqn:Hmem; [|apply PSE.mem_4 in Hmem]|]; repeat inv_bind).
      3:destruct (vars_of _) eqn:Vars; repeat inv_bind.
      1-3:repeat constructor; eauto.
      2,3:intros ? Heq; inv Heq.
      + eapply fresh_ident_nIn'; eauto.
      + exists e0; auto.
      + eapply fresh_ident_nIn' in H3; eauto.
        eapply init_var_for_clock_st_valid; eauto.
      + apply add_whens_is_constant; destruct t; simpl; auto.
      + eapply init_var_for_clock_normalized_eq; eauto.
      + apply vars_of_Some in H1 as (?&?). congruence.
    - (* arrow *)
      destruct ann0 as (?&?&?), (vars_of er) eqn:Vars; repeat inv_bind.
      + repeat constructor; eauto.
        1-2:intros ? Heq; inv Heq. exists e0; auto.
        eapply init_var_for_clock_normalized_eq; eauto.
      + apply vars_of_Some in H1 as (?&?). congruence.
    - (* cexp *)
      inv H; repeat inv_bind; auto.
      inv H0; repeat inv_bind; auto.
  Qed.

  Fact fby_equations_normalized_eq {prefs} : forall (G : @global prefs) out to_cut eqs eqs' st st',
      st_valid_after st out ->
      Forall (unnested_equation G) eqs ->
      PS.Subset out to_cut ->
      fby_equations to_cut eqs st = (eqs', st') ->
      Forall (normalized_equation G out) eqs'.
  Proof.
    induction eqs; intros * Hvalid Hunt Hsub Hfby;
      unfold fby_equations in Hfby; repeat inv_bind; simpl; auto.
    inv Hunt.
    eapply Forall_app; split.
    - eapply fby_equation_normalized_eq in H; eauto.
    - eapply IHeqs with (st:=x1) (st':=st'); eauto. 1:eapply fby_equation_st_valid; eauto.
      unfold fby_equations; repeat inv_bind; eauto.
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

  Lemma vars_of_no_fresh : forall es xs,
      vars_of es = Some xs ->
      fresh_ins es = [].
  Proof.
    induction es; simpl in *; intros * Hvars; auto.
    destruct a; simpl; try solve [inv Hvars].
    destruct a, vars_of eqn:Hvars'; inv Hvars.
    eauto.
  Qed.

  Lemma add_whens_no_fresh : forall e ty ck,
      fresh_in (add_whens e ty ck) = fresh_in e.
  Proof.
    induction ck as [|??? (?&?)]; simpl; auto.
    rewrite app_nil_r; auto.
  Qed.

  Lemma init_var_for_clock_no_anon : forall ck xr xinit eqs' st st',
      init_var_for_clock ck xr st = (xinit, eqs', st') ->
      anon_in_eqs eqs' = [].
  Proof.
    unfold init_var_for_clock. intros * Hinit.
    destruct fresh_ident; repeat inv_bind; simpl.
    unfold anon_in_eq; simpl.
    repeat rewrite app_nil_r.
    repeat rewrite add_whens_no_fresh; simpl.
    induction xr as [|(?&?)]; simpl; auto.
  Qed.

  Lemma fby_equation_anon : forall to_cut equ eqs' st st',
      fby_equation to_cut equ st = (eqs', st') ->
      Permutation (anon_in_eqs eqs') (anon_in_eq equ).
  Proof.
    unfold fby_equation.
    intros ? (?&?) * Hfby.
    destruct_to_singl l; repeat inv_bind; simpl; repeat rewrite app_nil_r; try reflexivity.
    destruct_to_singl l0; repeat inv_bind; simpl; try reflexivity.
    - destruct e; repeat inv_bind; simpl; repeat rewrite app_nil_r; try reflexivity.
      1,2:destruct_to_singl l; destruct_to_singl l0; destruct_to_singl l2;
        repeat inv_bind; simpl; repeat rewrite app_nil_r; try reflexivity.
      + destruct a as (?&?&?).
        destruct (is_constant e); [destruct (PS.mem i to_cut)|destruct (vars_of l1) eqn:Hvars];
          repeat inv_bind; simpl; repeat rewrite app_nil_r; try reflexivity.
        unfold anon_in_eq; simpl; repeat rewrite app_nil_r.
        apply Permutation_app_head.
        rewrite add_whens_no_fresh.
        replace (fresh_in (init_type t)) with (@nil (ident * (type * clock))) by (destruct t; simpl; auto).
        simpl. apply Permutation_app_head.
        eapply vars_of_no_fresh in Hvars; setoid_rewrite Hvars.
        erewrite init_var_for_clock_no_anon; eauto.
      + destruct (vars_of l1) eqn:Hvars; repeat inv_bind; simpl; repeat rewrite app_nil_r; try reflexivity.
        destruct a as (?&?&?); repeat inv_bind.
        unfold anon_in_eq; simpl; repeat rewrite app_nil_r; rewrite app_assoc.
        apply Permutation_app_head.
        eapply vars_of_no_fresh in Hvars; setoid_rewrite Hvars.
        erewrite init_var_for_clock_no_anon; eauto.
    - destruct e; repeat inv_bind; simpl; repeat rewrite app_nil_r; try reflexivity.
      1,2:destruct_to_singl l; destruct_to_singl l1; destruct_to_singl l3;
        repeat inv_bind; simpl; repeat rewrite app_nil_r; reflexivity.
  Qed.

  Corollary fby_equations_anon : forall to_cut eqs eqs' st st',
      fby_equations to_cut eqs st = (eqs', st') ->
      Permutation (anon_in_eqs eqs') (anon_in_eqs eqs).
  Proof.
    unfold fby_equations.
    induction eqs; intros * Hfby; repeat inv_bind; simpl in *; auto.
    eapply fby_equation_anon in H.
    unfold anon_in_eqs. rewrite <-flat_map_app.
    rewrite H, IHeqs; auto.
    repeat inv_bind; eauto.
  Qed.

  Lemma fby_equations_no_anon {prefs} : forall (G : @global prefs) out to_cut eqs eqs' st st',
      st_valid_after st out ->
      Forall (unnested_equation G) eqs ->
      PS.Subset out to_cut ->
      fby_equations to_cut eqs st = (eqs', st') ->
      anon_in_eqs eqs' = [].
  Proof.
    intros * Hweak Hunt Hsub Hfby.
    eapply fby_equations_normalized_eq in Hfby; eauto.
    eapply unnested_equations_no_anon.
    solve_forall. eapply normalized_eq_unnested_eq; eauto.
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
    let eqs := fby_equations (ps_from_list (map fst (n_out n))) (n_eqs n) init_st in
    let nvars := st_anns (snd eqs) in
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
    remember (fby_equations _ _ _) as eqs. destruct eqs as [eqs st']. symmetry in Heqeqs.
    specialize (n_defd n) as Hperm.
    apply fby_equations_vars_perm in Heqeqs; simpl.
    rewrite Permutation_app_comm, app_assoc, map_app, (Permutation_app_comm (n_out n)), <- Hperm.
    rewrite <- Heqeqs. unfold st_ids. rewrite init_st_anns, app_nil_r; auto.
  Qed.
  Next Obligation.
    destruct (fby_equations _ _ _) as (eqs, st') eqn:Heqeqs.
    pose proof (node_NoDup n) as Hndup.
    pose proof (n_good n) as (Good&_).
    simpl. erewrite fby_equations_anon; eauto.
    eapply fby_equations_st_valid, st_valid_NoDup in Heqeqs; eauto.
    2:{ eapply init_st_valid.
        - eapply norm2_not_in_norm1_prefs.
        - rewrite PS_For_all_Forall.
          eapply Forall_incl; eauto.
          intros ? Hin.
          rewrite ps_of_list_ps_to_list in Hin; eauto. }
    rewrite ps_of_list_ps_to_list_Perm in Heqeqs; auto. 2:rewrite <-fst_NoDupMembers; apply n_nodup.
    rewrite <- app_assoc, fst_NoDupMembers. repeat rewrite map_app in *.
    unfold st_ids in Heqeqs. rewrite (app_assoc (map _ (n_vars _))), (Permutation_app_comm (map _ (n_vars _))),
                             <- app_assoc, app_assoc, (Permutation_app_comm (map _ (n_in _))), <- app_assoc; auto.
  Qed.
  Next Obligation.
    specialize (n_good n) as (Hgood&Hname). split; auto.
    repeat rewrite map_app, Forall_app in Hgood. destruct Hgood as (?&?&?&?).
    destruct (fby_equations _ _ _) as (eqs, st') eqn:Heqeqs.
    pose proof (node_NoDup n) as Hndup.
    pose proof (n_good n) as (Good&_).
    assert (st_valid_after st' (PSP.of_list (map fst (n_in n ++ n_vars n ++ n_out n)))) as Hvalid.
    { eapply fby_equations_st_valid, init_st_valid; eauto.
      - eapply norm2_not_in_norm1_prefs.
      - rewrite PS_For_all_Forall.
        eapply Forall_incl; eauto.
        intros ? Hin.
        rewrite ps_of_list_ps_to_list in Hin.
        eapply incl_map; eauto.
        apply incl_appr', incl_appr', incl_appl, incl_refl. }
    erewrite fby_equations_anon; eauto.
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

  Corollary iface_eq_normalized_node {p1 p2 p3} : forall (G : @global p1) (G' : @global p2) (n : @node p3),
      global_iface_eq G G' ->
      normalized_node G n ->
      normalized_node G' n.
  Proof.
    intros * Hglob Hunt.
    unfold normalized_node in *.
    eapply Forall_impl; [|eauto]. intros.
    eapply iface_eq_normalized_equation; eauto.
  Qed.

  Fact normfby_node_normalized_node {prefs} : forall (G : @global prefs) n,
      unnested_node G n ->
      normalized_node G (normfby_node n).
  Proof.
    intros * Hunt.
    unfold normfby_node, normalized_node; simpl.
    pose proof (n_good n) as (Good&_).
    remember (fby_equations _ _ _) as eqs. symmetry in Heqeqs. destruct eqs as [eqs st'].
    eapply fby_equations_normalized_eq in Heqeqs; eauto.
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
