From Coq Require Import List Sorting.Permutation.
Import List.ListNotations.
Open Scope list_scope.
Require Import Omega.

From Velus Require Import Common Environment.
From Velus Require Import Operators.
From Velus Require Import Lustre.LSyntax.
From Velus Require Lustre.Normalization.Fresh.
From Velus Require Import Lustre.Normalization.Unnesting.

(** * Putting FBYs into normalized form *)

Local Set Warnings "-masking-absolute-name".
Module Type NORMFBY
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Import Syn : LSYNTAX Ids Op)
       (Import Unt : UNNESTING Ids Op OpAux Syn).

  Import Fresh Fresh.Notations Facts Tactics.
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

  Open Scope bool_scope.

  (** Generate an init equation for a given clock `cl`; if the init equation for `cl` already exists,
      just return the variable *)
  Definition init_var_for_clock (cl : clock) : FreshAnn (ident * list equation) :=
    fun st => match (find (fun '(_, ((ty, cl'), isinit)) => isinit && (cl' ==b cl) && (ty ==b Op.bool_type)) (st_anns st)) with
           | Some (x, _) => ((x, []), st)
           | None => let (x, st') := fresh_ident norm2 ((bool_type, cl), true) st in
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
    let '(ty, (ck, name)) := ann in
    do (initid, eqs) <- init_var_for_clock ck;
    do px <- fresh_ident norm2 ((ty, ck), false);
    ret (Eite (Evar initid (bool_type, (ck, Some initid))) [e0]
              [Evar px (ty, (ck, Some px))] ([ty], (ck, name)),
         ([px], [Efby [add_whens (Econst (init_type ty)) ty ck] [e] [ann]])::eqs).

  Definition arrow_iteexp (e0 : exp) (e : exp) (ann : ann) : FreshAnn (exp * list equation) :=
    let '(ty, (ck, name)) := ann in
    do (initid, eqs) <- init_var_for_clock ck;
    ret (Eite (Evar initid (bool_type, (ck, Some initid))) [e0] [e]
              ([ty], (ck, name)), eqs).

  Definition fby_equation (to_cut : PS.t) (eq : equation) : FreshAnn (list equation) :=
    match eq with
    | ([x], [Efby [e0] [e] [ann]]) =>
      let '(ty, (ck, _)) := ann in
      if is_constant e0 then
        if PS.mem x to_cut then
          do x' <- fresh_ident norm2 ((ty, ck), false);
          ret [([x], [Evar x' ann]); ([x'], [Efby [e0] [e] [ann]])]
        else ret [eq]
      else
        do (fby, eqs) <- fby_iteexp e0 e ann;
        ret (([x], [fby])::eqs)
    | ([x], [Earrow [e0] [e] [ann]]) =>
      do (ite, eqs) <- arrow_iteexp e0 e ann;
      ret (([x], [ite])::eqs)
    | _ => ret [eq]
    end.

  Definition fby_equations (to_cut : PS.t) (eqs : list equation) : FreshAnn (list equation) :=
    do eqs' <- map_bind (fby_equation to_cut) eqs;
    ret (concat eqs').

  (** Some initial properties *)

  Local Ltac destruct_to_singl l :=
    destruct l; [|destruct l]; auto.

  Fact fby_equation_spec : forall to_cut xs es,
      (exists x e0 e ann,
          xs = [x] /\
          es = [Efby [e0] [e] [ann]] /\
          is_constant e0 = true /\
          fby_equation to_cut (xs, es) =
          (let '(ty, (ck, _)) := ann in
           if PS.mem x to_cut then
             do x' <- fresh_ident norm2 ((ty, ck), false);
             ret [([x], [Evar x' ann]); ([x'], es)]
           else ret [(xs, es)]))
      \/ (exists x e0 e ann ,
          xs = [x] /\
          es = [Efby [e0] [e] [ann]] /\
          is_constant e0 = false /\
          fby_equation to_cut (xs, es) =
          (do (fby, eqs) <- fby_iteexp e0 e ann;
           ret (([x], [fby])::eqs)))
      \/ (exists x e0 e ann,
            xs = [x] /\
            es = [Earrow [e0] [e] [ann]] /\
            fby_equation to_cut (xs, es) =
            (do (ite, eqs) <- arrow_iteexp e0 e ann;
             ret (([x], [ite])::eqs)))
      \/ fby_equation to_cut (xs, es) = (ret [(xs, es)]).
  Proof.
    intros *.
    destruct_to_singl xs. destruct_to_singl es.
    2: { repeat right; simpl. destruct e; auto.
         1,2:(destruct_to_singl l; destruct_to_singl l0; destruct_to_singl l1).
    }
    destruct e; auto.
    1,2:destruct_to_singl l; destruct_to_singl l0; destruct_to_singl l1.

    (* left. 2:right;left. *)
    (* 1,2:repeat eexists; eauto. *)
    (* 1,2:destruct_to_singl l; destruct_to_singl l0; destruct_to_singl l1; simpl. *)
    (* 2,4:(repeat right; destruct o; auto; destruct e1; auto; *)
    (*      try destruct a as (?&?&?); try destruct a1 as (?&?&?); auto). *)
    - (* fby *)
      destruct a as [ty [ck name]].
      destruct (is_constant e) eqn:Hconst; simpl.
      + left. rewrite Hconst. repeat eexists; eauto.
      + right. left. rewrite Hconst. repeat eexists; eauto.
    - (* arrow *)
      destruct a as [ty [ck name]]. right. right. left.
      repeat eexists; eauto.
  Qed.

  Ltac inv_fby_equation Hfby to_cut eq :=
    let Hspec := fresh "Hspec" in
    let Hconst := fresh "Hconst" in
    let Hr := fresh "Hr" in
    destruct eq as [xs es];
    specialize (fby_equation_spec to_cut xs es) as
        [(?&?&?&?&?&?&Hconst&Hspec)|[(?&?&?&?&?&?&Hconst&Hspec)|[(?&?&?&?&?&?&Hspec)|Hspec]]];
    subst; rewrite Hspec in Hfby; clear Hspec; repeat inv_bind; auto.

  (** *** Preservation of st_valid *)

  Definition st_valid_after {B} st aft := @st_valid_after B st norm2 aft.
  Hint Unfold st_valid_after.

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
    intros e0 e [ty [ck name]] e' eqs' st st' aft Hfby Hvalid.
    unfold fby_iteexp in Hfby.
    destruct (is_constant e0); repeat inv_bind;
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

  Fact fby_equation_st_valid : forall to_cut eq eqs' st st' aft,
      fby_equation to_cut eq st = (eqs', st') ->
      st_valid_after st aft ->
      st_valid_after st' aft.
  Proof.
    intros * Hfby Hvalid.
    inv_fby_equation Hfby to_cut eq.
    - destruct x2 as (?&?&?).
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

  Fact fby_equation_st_follows : forall to_cut eq eqs' st st',
      fby_equation to_cut eq st = (eqs', st') ->
      st_follows st st'.
  Proof.
    intros * Hfby.
    inv_fby_equation Hfby to_cut eq; eauto.
    - destruct x2 as (?&?&?).
      destruct PS.mem; repeat inv_bind; eauto.
      reflexivity.
    - reflexivity.
  Qed.
  Hint Resolve fby_equation_st_follows.

  Fact fby_equations_st_follows : forall to_cut eqs eqs' st st',
      fby_equations to_cut eqs st = (eqs', st') ->
      st_follows st st'.
  Proof.
    intros * Hfby. unfold fby_equations in *; repeat inv_bind.
    eapply map_bind_st_follows; eauto.
    solve_forall.
  Qed.

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
    eapply init_var_for_clock_vars_perm in H; eauto.
    eapply fresh_ident_vars_perm in H0.
    simpl.
    rewrite <- H0. apply perm_skip; auto.
  Qed.

  Fact arrow_iteexp_vars_perm : forall e0 e ann e' eqs' st st',
      arrow_iteexp e0 e ann st = (e', eqs', st') ->
      Permutation ((vars_defined eqs')++(st_ids st)) (st_ids st').
  Proof.
    intros ? ? [ty [ck name]] ? ? ? ? Hfby.
    unfold arrow_iteexp in Hfby. repeat inv_bind.
    eapply init_var_for_clock_vars_perm in H; eauto.
  Qed.

  Fact fby_equation_vars_perm : forall to_cut eq eqs' st st',
      fby_equation to_cut eq st = (eqs', st') ->
      Permutation ((vars_defined eqs')++(st_ids st)) ((vars_defined [eq])++(st_ids st')).
  Proof.
    intros * Hfby.
    inv_fby_equation Hfby to_cut eq.
    - destruct x2 as (?&?&?).
      destruct PS.mem; repeat inv_bind; eauto.
      eapply perm_skip, fresh_ident_vars_perm; eauto.
    - eapply perm_skip. eapply fby_iteexp_vars_perm in H; eauto.
    - eapply perm_skip. eapply arrow_iteexp_vars_perm in H; eauto.
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

  (** *** normalized_node implies unnested_node *)

  Fact constant_normalized_lexp : forall e,
      normalized_constant e ->
      normalized_lexp e.
  Proof.
    intros e Hconst.
    induction Hconst; auto.
  Qed.

  Fact normalized_eq_unnested_eq : forall to_cut eq,
      normalized_equation to_cut eq ->
      unnested_equation eq.
  Proof.
    intros * Hnormed. inv Hnormed; auto using constant_normalized_lexp.
  Qed.

  (** *** Preservation of wl property *)

  Fact add_whens_numstreams : forall ty ck e,
      numstreams e = 1 ->
      numstreams (add_whens e ty ck) = 1.
  Proof.
    induction ck; intros *; simpl; auto.
  Qed.


  Fact add_whens_wl : forall G ty ck e,
      numstreams e = 1 ->
      wl_exp G e ->
      wl_exp G (add_whens e ty ck).
  Proof.
    induction ck; intros * Hlen Hwl; simpl; auto.
    constructor; simpl; auto.
    rewrite app_nil_r, length_annot_numstreams.
    apply add_whens_numstreams; auto.
  Qed.

  Hint Constructors wl_exp.

  Fact init_var_for_clock_wl : forall G ck id eqs' st st',
      init_var_for_clock ck st = (id, eqs', st') ->
      Forall (wl_equation G) eqs'.
  Proof.
    intros * Hinit.
    unfold init_var_for_clock in Hinit.
    destruct (find _ _).
    - destruct p; inv Hinit; auto.
    - destruct (fresh_ident _ _). inv Hinit.
      repeat constructor; simpl.
      1,2:apply add_whens_wl; auto.
      1,2:rewrite app_nil_r, length_annot_numstreams; apply add_whens_numstreams; auto.
  Qed.

  Fact fby_iteexp_numstreams : forall e0 e a e' eqs' st st',
      fby_iteexp e0 e a st = (e', eqs', st') ->
      numstreams e' = 1.
  Proof.
    intros * Hfby. destruct a as [ty [ck name]].
    unfold fby_iteexp in Hfby.
    repeat inv_bind; simpl; auto.
  Qed.

  Fact fby_iteexp_wl_exp : forall G e0 e a e' eqs' st st',
      wl_exp G e0 ->
      wl_exp G e ->
      numstreams e0 = 1 ->
      numstreams e = 1 ->
      fby_iteexp e0 e a st = (e', eqs', st') ->
      wl_exp G e'.
  Proof.
    intros * Hwl1 Hwl2 Hn1 Hn2 Hfby. destruct a as [ty [ck name]].
    unfold fby_iteexp in Hfby.
    repeat inv_bind.
    constructor; auto; simpl.
    rewrite app_nil_r, length_annot_numstreams; auto.
  Qed.

  Fact fby_iteexp_wl_eq : forall G e0 e a e' eqs' st st',
      wl_exp G e0 ->
      wl_exp G e ->
      numstreams e0 = 1 ->
      numstreams e = 1 ->
      fby_iteexp e0 e a st = (e', eqs', st') ->
      Forall (wl_equation G) eqs'.
  Proof.
    intros * Hwl1 Hwl2 Hn1 Hn2 Hfby. destruct a as [ty [ck name]].
    unfold fby_iteexp in Hfby.
    repeat inv_bind; auto.
    repeat constructor; simpl; auto.
    - apply add_whens_wl; auto.
    - rewrite app_nil_r, length_annot_numstreams. apply add_whens_numstreams; auto.
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

  Fact arrow_iteexp_wl_exp : forall G e0 e a e' eqs' st st',
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
    1,2:rewrite app_nil_r, length_annot_numstreams; auto.
  Qed.

  Fact arrow_iteexp_wl_eq : forall G e0 e a e' eqs' st st',
      wl_exp G e0 ->
      wl_exp G e ->
      numstreams e0 = 1 ->
      numstreams e = 1 ->
      arrow_iteexp e0 e a st = (e', eqs', st') ->
      Forall (wl_equation G) eqs'.
  Proof.
    intros * Hwl1 Hwl2 Hn1 Hn2 Hfby. destruct a as [ty [ck name]].
    unfold arrow_iteexp in Hfby; repeat inv_bind.
    eapply init_var_for_clock_wl in H; eauto.
  Qed.

  Fact fby_equation_wl : forall G to_cut eq eqs' st st',
      wl_equation G eq ->
      fby_equation to_cut eq st = (eqs', st') ->
      Forall (wl_equation G) eqs'.
  Proof.
    intros * Hwl Hfby.
    inv_fby_equation Hfby to_cut eq.
    - destruct x2 as (?&?&?).
      destruct PS.mem; repeat inv_bind; auto.
      destruct Hwl as [Hwl _]; inv Hwl; auto.
      repeat (constructor; eauto).
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

  Fact init_var_for_clock_unnested_eq : forall ck id eqs' st st',
      init_var_for_clock ck st = (id, eqs', st') ->
      Forall unnested_equation eqs'.
  Proof.
    intros * Hinit.
    unfold init_var_for_clock in Hinit.
    destruct (find _ _).
    - destruct p. inv Hinit. constructor.
    - destruct (fresh_ident _ _) eqn:Hfresh. inv Hinit.
      repeat constructor.
      1,2:eapply add_whens_normalized_lexp; eauto.
  Qed.

  Fact init_var_for_clock_normalized_eq : forall cl id eqs' out st st',
      st_valid_after st out ->
      init_var_for_clock cl st = (id, eqs', st') ->
      Forall (normalized_equation out) eqs'.
  Proof.
    intros cl id eqs' out st st' Hvalid Hinit.
    unfold init_var_for_clock in Hinit.
    destruct (find _ _).
    - destruct p. inv Hinit. constructor.
    - destruct (fresh_ident _ _) eqn:Hfresh. inv Hinit.
      repeat constructor.
      + eapply fresh_ident_nIn' in Hfresh; eauto.
      + apply add_whens_is_constant. auto.
      + apply add_whens_normalized_lexp. auto.
  Qed.

  Fact fby_iteexp_unnested_eq : forall e0 e a e' eqs' st st',
      normalized_lexp e0 ->
      normalized_lexp e ->
      fby_iteexp e0 e a st = (e', eqs', st') ->
      Forall unnested_equation eqs'.
  Proof.
    intros * Hnormed1 Hnormed2 Hfby. destruct a as [ty [ck name]].
    unfold fby_iteexp in Hfby.
    repeat inv_bind; auto.
    repeat constructor; auto.
    - apply add_whens_normalized_lexp; auto.
    - eapply init_var_for_clock_unnested_eq in H; auto.
  Qed.

  Fact fby_iteexp_normalized_eq : forall e0 e a e' eqs' out st st',
      st_valid_after st out ->
      normalized_lexp e ->
      fby_iteexp e0 e a st = (e', eqs', st') ->
      Forall (normalized_equation out) eqs'.
  Proof.
    intros e0 e [ty [ck name]] e' eqs' out st st' Hvalid He Hfby.
    unfold fby_iteexp in Hfby.
    repeat inv_bind; constructor.
    - assert (st_valid_after x1 out) as Hvalid' by eauto.
      constructor; auto.
      + eapply fresh_ident_nIn' in H0; eauto.
      + eapply add_whens_is_constant; eauto.
    - eapply init_var_for_clock_normalized_eq in H; eauto.
  Qed.

  Fact fby_equation_unnested_eq : forall to_cut eq eqs' st st',
      unnested_equation eq ->
      fby_equation to_cut eq st = (eqs', st') ->
      Forall unnested_equation eqs'.
  Proof.
    intros * Hunt Hfby.
    inv_fby_equation Hfby to_cut eq.
    - destruct x2 as (?&?&?).
      destruct PS.mem; repeat inv_bind; auto.
      constructor; constructor; auto.
      inv Hunt; constructor; auto. 1,2:inv H1; inv H0.
    - inv Hunt. 2:inv H1; inv H0.
      assert (H':=H). eapply fby_iteexp_unnested_eq in H'; eauto.
      constructor; auto.
      destruct x2 as (?&?&?). repeat inv_bind.
      repeat constructor; auto.
    - destruct x2 as (?&?&?). repeat inv_bind.
      repeat constructor; auto.
      3:eapply init_var_for_clock_unnested_eq in H; eauto.
      1-2:(clear - Hunt; inv Hunt; auto; inv H0; inv H).
  Qed.

  Fact fby_equation_normalized_eq : forall out to_cut eq eqs' st st',
      st_valid_after st out ->
      unnested_equation eq ->
      PS.Subset out to_cut ->
      fby_equation to_cut eq st = (eqs', st') ->
      Forall (normalized_equation out) eqs'.
  Proof.
    intros * Hvalid Hunt Hsub Hfby.
    inv Hunt; simpl in *; repeat inv_bind; auto.
    1,2:destruct_to_singl xs; repeat inv_bind; auto.
    - (* fby *)
      destruct ann0 as (?&?&?); destruct (is_constant e0) eqn:Hconst;
        [apply is_constant_normalized_constant in Hconst;
         destruct PS.mem eqn:Hmem; [|apply PSE.mem_4 in Hmem]|]; repeat inv_bind.
      1-3:repeat constructor; auto.
      3:apply add_whens_is_constant; auto.
      3:eapply init_var_for_clock_normalized_eq; eauto.
      eapply fresh_ident_nIn'; eauto.
      eapply fresh_ident_nIn' in H2; eauto.
      eapply init_var_for_clock_st_valid; eauto.
    - (* arrow *)
      destruct ann0 as (?&?&?); repeat inv_bind.
      repeat constructor; auto.
      eapply init_var_for_clock_normalized_eq; eauto.
    - inv H; repeat inv_bind; auto.
      inv H0; repeat inv_bind; auto.
  Qed.

  Fact fby_equations_normalized_eq : forall out to_cut eqs eqs' st st',
      st_valid_after st out ->
      Forall unnested_equation eqs ->
      PS.Subset out to_cut ->
      fby_equations to_cut eqs st = (eqs', st') ->
      Forall (normalized_equation out) eqs'.
  Proof.
    induction eqs; intros * Hvalid Hunt Hsub Hfby;
      unfold fby_equations in Hfby; repeat inv_bind; simpl; auto.
    inv Hunt.
    eapply Forall_app; split.
    - eapply fby_equation_normalized_eq in H; eauto.
    - eapply IHeqs with (st:=x1) (st':=st'); eauto. 1:eapply fby_equation_st_valid; eauto.
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

  Lemma fby_equations_no_anon : forall out to_cut eqs eqs' st st',
      st_valid_after st out ->
      Forall unnested_equation eqs ->
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

  Definition norm1_prefs := PS.add norm1 elab_prefs.

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

  Program Definition normfby_node (to_cut : PS.t) (n : node)
          (Hunt : unnested_node n)
          (Hpref : n_prefixes n = norm1_prefs) : node :=
    let anon := anon_in_eqs (n_eqs n) in
    let eqs := fby_equations (PS.union to_cut (ps_from_list (map fst (n_out n)))) (n_eqs n) init_st in
    let nvars := idty (st_anns (snd eqs)) in
    {| n_name := n_name n;
       n_hasstate := n_hasstate n;
       n_in := n_in n;
       n_out := n_out n;
       n_vars := (n_vars n)++nvars;
       n_prefixes := PS.add norm2 (n_prefixes n);
       n_eqs := fst eqs;
       n_ingt0 := n_ingt0 n;
       n_outgt0 := n_outgt0 n;
    |}.
  Next Obligation.
    remember (fby_equations _ _ _) as eqs. destruct eqs as [eqs st']. symmetry in Heqeqs.
    specialize (n_defd n) as Hperm.
    apply fby_equations_vars_perm in Heqeqs; simpl.
    rewrite Permutation_app_comm, app_assoc, map_app, (Permutation_app_comm (n_out n)), <- Hperm, map_fst_idty.
    rewrite <- Heqeqs. unfold st_ids. rewrite init_st_anns, app_nil_r; auto.
  Qed.
  Next Obligation.
    destruct (fby_equations _ _ _) as (eqs, st') eqn:Heqeqs.
    pose proof (node_NoDup n) as Hndup.
    pose proof (n_good n) as (Good&_). rewrite Hpref in Good.
    simpl. erewrite fby_equations_no_anon, app_nil_r. 2,3,5:eauto.
    3:rewrite ps_from_list_ps_of_list; eapply PSP.union_subset_2.
    - eapply fby_equations_st_valid, st_valid_NoDup in Heqeqs; eauto.
      2:{ eapply init_st_valid.
          - eapply norm2_not_in_norm1_prefs.
          - rewrite PS_For_all_Forall.
            eapply Forall_incl; eauto.
            intros ? Hin.
            rewrite ps_of_list_ps_to_list in Hin.
            eapply incl_map; eauto.
            apply incl_appr', incl_appr', incl_appl, incl_refl. }
      rewrite ps_of_list_ps_to_list_Perm in Heqeqs; auto.
      rewrite <- app_assoc, fst_NoDupMembers. repeat rewrite map_app in *.
      unfold st_ids in Heqeqs. rewrite map_fst_idty, (app_assoc (map _ (n_vars _))), (Permutation_app_comm (map _ (n_vars _))),
                               <- app_assoc, app_assoc, (Permutation_app_comm (map _ (n_in _))), <- app_assoc; auto.
    - eapply init_st_valid.
      + apply norm2_not_in_norm1_prefs.
      + rewrite PS_For_all_Forall.
        eapply Forall_incl; eauto.
        intros ? Hin.
        rewrite ps_of_list_ps_to_list in Hin. repeat simpl_In.
        exists (i, (t, c)); split; auto. repeat rewrite in_app_iff in *; auto.
  Qed.
  Next Obligation.
    specialize (n_good n) as (Hgood&Hname). split; auto.
    repeat rewrite map_app, Forall_app in Hgood. destruct Hgood as (?&?&?&?).
    destruct (fby_equations _ _ _) as (eqs, st') eqn:Heqeqs.
    pose proof (node_NoDup n) as Hndup.
    pose proof (n_good n) as (Good&_). rewrite Hpref in Good.
    assert (st_valid_after st' (PSP.of_list (map fst (n_in n ++ n_vars n ++ n_out n)))) as Hvalid.
    { eapply fby_equations_st_valid, init_st_valid; eauto.
      - eapply norm2_not_in_norm1_prefs.
      - rewrite PS_For_all_Forall.
        eapply Forall_incl; eauto.
        intros ? Hin.
        rewrite ps_of_list_ps_to_list in Hin.
        eapply incl_map; eauto.
        apply incl_appr', incl_appr', incl_appl, incl_refl. }
    erewrite fby_equations_no_anon. 3,5:eauto. 3:rewrite ps_from_list_ps_of_list; eapply PSP.union_subset_2.
    2:{ eapply init_st_valid.
        - apply norm2_not_in_norm1_prefs.
        - rewrite PS_For_all_Forall.
          eapply Forall_incl; eauto.
          intros ? Hin.
          rewrite ps_of_list_ps_to_list in Hin. repeat simpl_In.
          exists (i, (t, c)); split; auto. repeat rewrite in_app_iff in *; auto. }
    simpl. rewrite app_nil_r.
    repeat rewrite map_app, Forall_app in *. destruct Good as (?&?&?&_).
    repeat split; auto using AtomOrGensym_add.
    eapply st_valid_prefixed in Hvalid.
    rewrite Hpref, map_fst_idty. auto.
    eapply Forall_impl; [|eauto]. intros ? (?&?); subst.
    right. exists norm2. eauto using PSF.add_1.
  Qed.

  Fixpoint normfby_global (G : global) :
    Forall unnested_node G ->
    Forall (fun n => n_prefixes n = norm1_prefs) G ->
    global.
  Proof.
    destruct G as [|hd tl]; intros Hunt Hprefs.
    - exact [].
    - refine ((normfby_node PS.empty hd _ _)::(normfby_global tl _ _)).
      + inv Hunt; auto.
      + inv Hprefs; auto.
      + inv Hunt; auto.
      + inv Hprefs; auto.
  Defined.

  (** *** After normalization, a global is normalized *)

  Fact normfby_node_normalized_node : forall n to_cut Hunt Hpref,
      normalized_node (normfby_node to_cut n Hunt Hpref).
  Proof.
    intros *.
    unfold normfby_node, normalized_node; simpl.
    pose proof (n_good n) as (Good&_). rewrite Hpref in Good.
    remember (fby_equations _ _ _) as eqs. symmetry in Heqeqs. destruct eqs as [eqs st'].
    eapply fby_equations_normalized_eq in Heqeqs; eauto.
    2:rewrite ps_from_list_ps_of_list; eapply PSP.union_subset_2.
    { eapply init_st_valid.
      - apply norm2_not_in_norm1_prefs.
      - rewrite PS_For_all_Forall.
        eapply Forall_incl; eauto.
        intros ? Hin.
        rewrite ps_from_list_ps_of_list, ps_of_list_ps_to_list in Hin. repeat simpl_In.
        exists (i, (t, c)); split; auto. repeat rewrite in_app_iff in *; auto. }
  Qed.

  Fact normfby_global_normalized_global : forall G Hunt Hprefs,
      normalized_global (normfby_global G Hunt Hprefs).
  Proof.
    induction G; intros; simpl; constructor.
    - eapply normfby_node_normalized_node.
    - eapply IHG.
  Qed.

  (** *** normfby_global produces a global with the correct prefixes *)

  Lemma normfby_global_prefixes : forall G G' Hunt Hprefs,
      normfby_global G Hunt Hprefs = G' ->
      Forall (fun n => n_prefixes n = PS.add norm2 norm1_prefs) G'.
  Proof.
    induction G; intros * Hnorm; simpl in *; inv Hnorm; constructor; simpl; eauto.
    inv Hprefs. congruence.
  Qed.

  (** *** normfby_global produces an equivalent global *)

  Fact normfby_global_eq : forall G Hunt Hprefs,
      global_iface_eq G (normfby_global G Hunt Hprefs).
  Proof.
    induction G; intros Hunt Hprefs.
    - reflexivity.
    - simpl. apply global_iface_eq_cons; auto.
  Qed.

  Fact normfby_global_names : forall a G Hunt Hprefs,
      Forall (fun n => (n_name a <> n_name n)%type) G ->
      Forall (fun n => (n_name a <> n_name n)%type) (normfby_global G Hunt Hprefs).
  Proof.
    induction G; intros * Hnames; simpl.
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
       (Unt : UNNESTING Ids Op OpAux Syn)
       <: NORMFBY Ids Op OpAux Syn Unt.
  Include NORMFBY Ids Op OpAux Syn Unt.
End NormFbyFun.
