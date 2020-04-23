From Coq Require Import List Sorting.Permutation.
Import List.ListNotations.
Open Scope list_scope.
Require Import Omega.

From Velus Require Import Common Ident.
From Velus Require Import Operators.
From Velus Require Import Lustre.LSyntax.
From Velus Require Lustre.Normalization.Fresh.

(** * Normalization procedure *)

Local Set Warnings "-masking-absolute-name".
Module Type NORMALIZATION
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Import Syn : LSYNTAX Ids Op).

  (** All the indents currently used in the node *)
  Definition used_idents (n : node) : list ident :=
    reserved ++ map fst (n_in n ++ n_vars n ++ n_out n).

  Definition first_unused_ident (n : node) : ident :=
    ((fold_left Pos.max (used_idents n) xH) + 100)%positive.

  (** Some facts about getting the first unused ident *)

  Fact first_unused_ident_gt : forall n id,
      first_unused_ident n = id ->
      Forall (fun id' => (id' < id)%positive) (used_idents n).
  Proof.
    intros n id Hfirst.
    subst. unfold first_unused_ident.
    rewrite Forall_forall; intros x Hin.
    eapply Pos.le_lt_trans. 2: apply Pos.lt_add_r.
    apply max_fold_in; auto.
  Qed.

  Import Fresh Fresh.Fresh Notations Facts Tactics.

  (** Fresh ident generation keeping type annotations;
      also retaining if the var is an init var or not *)
  Definition FreshAnn A := Fresh A ((type * clock) * bool).

  Local Open Scope fresh_monad_scope.

  Definition hd_default (l : list exp) : exp :=
    hd (Econst (init_type bool_type)) l.

  Fixpoint idents_for_anns (anns : list ann) : FreshAnn (list (ident * ann)) :=
    match anns with
    | [] => ret []
    | (ty, (cl, _))::tl => do x <- fresh_ident ((ty, cl), false);
              do xs <- idents_for_anns tl;
              ret ((x, (ty, (cl, Some x)))::xs)
    end.

  Fact idents_for_anns_values : forall anns idents st st',
      idents_for_anns anns st = (idents, st') ->
      Forall2 (fun '(ty, (cl, _)) '(x, (ty', (cl', k))) =>
                 ty' = ty /\ cl' = cl /\ k = Some x) anns idents.
  Proof.
    induction anns; intros idents st st' Hanns; simpl in *; repeat inv_bind.
    - constructor.
    - destruct a as [ty [cl ?]]. repeat inv_bind.
      specialize (IHanns _ _ _ H0).
      constructor; eauto.
  Qed.

  Corollary idents_for_anns_length : forall anns idents st st',
      idents_for_anns anns st = (idents, st') ->
      length idents = length anns.
  Proof.
    intros.
    apply idents_for_anns_values in H.
    rewrite Forall2_forall2 in H; destruct H; auto.
  Qed.

  (** Add some whens on top of an expression *)
  Fixpoint add_whens (e : exp) (ty : type) (cl : clock) :=
    match cl with
    | Cbase => e
    | Con cl' clid b => Ewhen [(add_whens e ty cl')] clid b ([ty], (cl, None))
    end.

  (** Generate an init equation for a given clock `cl`; if the init equation for `cl` already exists,
      just return the variable *)
  Definition init_var_for_clock (cl : nclock) : FreshAnn (ident * list equation) :=
    fun st => match (find (fun '(_, ((ty, cl'), isinit)) => isinit && (cl' ==b (fst cl)) && (ty ==b Op.bool_type)) (st_anns st)) with
           | Some (x, _) => ((x, []), st)
           | None => let (x, st') := fresh_ident ((bool_type, (fst cl)), true) st in
                    ((x, [([x], [Efby [add_whens (Econst true_const) bool_type (fst cl)]
                                      [add_whens (Econst false_const) bool_type (fst cl)]
                                      [(bool_type, cl)]])]), st')
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
    else do (initid, eqs) <- init_var_for_clock cl;
         do px <- fresh_ident ((ty, fst cl), false);
         ret (Eite (Evar initid (bool_type, (fst cl, Some initid))) [e0]
                   [Evar px (ty, (fst cl, Some px))] ([ty], (fst cl, None)),
              ([px], [Efby [Econst (init_type ty)] [e] [ann]])::eqs).

  (** Normalize a `fby inits es anns` expression, with inits and es already normalized *)
  Definition normalize_fby (inits : list exp) (es : list exp) (anns : list ann) : FreshAnn (list exp * list equation) :=
    do (es, eqs) <- map_bind2 (fun '((init, e), ann) => fby_iteexp init e ann) (combine (combine inits es) anns);
    ret (es, concat eqs).

  Definition normalize_reset (e : exp) : FreshAnn (exp * list equation) :=
    match e with
    | Evar v ann => ret (Evar v ann, [])
    | e => let '(ty, (cl, _)) := hd (bool_type, (Cbase, None)) (annot e) in
          do x <- fresh_ident ((ty, cl), false);
          ret (Evar x (ty, (cl, Some x)), ([x], [e])::[])
    end.

  Lemma normalize_reset_spec : forall e,
      (exists v, exists ann, e = Evar v ann /\ normalize_reset e = ret (Evar v ann, []))
      \/ normalize_reset e = let '(ty, (cl, _)) := hd (bool_type, (Cbase, None)) (annot e) in
                            do x <- fresh_ident ((ty, cl), false);
                            ret (Evar x (ty, (cl, Some x)), ([x], [e])::[]).
  Proof. destruct e; eauto. Qed.

  Fixpoint normalize_exp (is_control : bool) (e : exp) {struct e} : FreshAnn (list exp * list equation) :=
    let normalize_exps := fun es => do (es, eqs) <- map_bind2 (normalize_exp false) es; ret (concat es, concat eqs) in
    let normalize_controls := fun es => do (es, eqs) <- map_bind2 (normalize_exp true) es; ret (concat es, concat eqs) in
    match e with
    | Econst c => ret ([Econst c], [])
    | Evar v ann => ret ([Evar v ann], [])
    | Eunop op e1 ann =>
      do (e1', eqs) <- normalize_exp false e1;
      ret ([Eunop op (hd_default e1') ann], eqs)
    | Ebinop op e1 e2 ann =>
      do (e1', eqs1) <- normalize_exp false e1;
      do (e2', eqs2) <- normalize_exp false e2;
      ret ([Ebinop op (hd_default e1') (hd_default e2') ann], eqs1++eqs2)
    | Ewhen es clid b (tys, cl) =>
      do (es', eqs) <- normalize_exps es;
      ret (map (fun '(e, ty) => Ewhen [e] clid b ([ty], cl)) (combine es' tys), eqs)
    | Emerge clid es1 es2 (tys, cl) =>
      do (es1', eqs1) <- normalize_controls es1;
      do (es2', eqs2) <- normalize_controls es2;
      let merges := map (fun '((e1, e2), ty) => Emerge clid [e1] [e2] ([ty], cl)) (combine (combine es1' es2') tys) in
      if is_control then
        ret (merges, eqs1++eqs2)
      else
        do xs <- idents_for_anns (List.map (fun ty => (ty, cl)) tys);
        ret (List.map (fun '(id, ann) => Evar id ann) xs,
             (combine (List.map (fun '(id, _) => [id]) xs) (List.map (fun e => [e]) merges))++eqs1++eqs2)
    | Eite e es1 es2 (tys, cl) =>
      do (e', eqs0) <- normalize_exp false e;
      do (es1', eqs1) <- normalize_controls es1;
      do (es2', eqs2) <- normalize_controls es2;
      let ites := map (fun '((e1, e2), ty) => Eite (hd_default e') [e1] [e2] ([ty], cl)) (combine (combine es1' es2') tys) in
      if is_control then
        ret (ites, eqs0++eqs1++eqs2)
      else
        do xs <- idents_for_anns (List.map (fun ty => (ty, cl)) tys);
        ret (List.map (fun '(id, ann) => Evar id ann) xs,
             (combine (List.map (fun '(id, _) => [id]) xs) (List.map (fun e => [e]) ites))++eqs0++eqs1++eqs2)
    | Efby inits es anns =>
      do (inits', eqs1) <- normalize_exps inits;
      do (es', eqs2) <- normalize_exps es;
      do (fbys, eqs3) <- normalize_fby inits' es' anns;
      do xs <- idents_for_anns anns;
      ret (List.map (fun '(x, ann) => Evar x ann) xs,
           (List.map (fun '((x, _), fby) => ([x], [fby])) (combine xs fbys))++eqs1++eqs2++eqs3)
    | Eapp f es r anns =>
      do (r', eqs1) <- match r with
                      | Some er => do (er, eqs1) <- normalize_exp false er;
                                  do (er', eqs2) <- normalize_reset (hd_default er);
                                  ret (Some er', eqs1++eqs2)
                      | None => ret (None, [])
                      end;
      do (es', eqs2) <- normalize_exps es;
      do xs <- idents_for_anns anns;
      ret (List.map (fun '(id, ann) => Evar id ann) xs,
           (List.map fst xs, [Eapp f es' r' anns])::eqs1++eqs2)
    end.

  Definition normalize_exps (es : list exp) :=
    do (es, eqs) <- map_bind2 (normalize_exp false) es;
      ret (concat es, concat eqs).

  Definition normalize_rhs (keep_fby : bool) (e : exp) : FreshAnn (list exp * list equation) :=
    match e with
    | Eapp f es r anns =>
      do (r', eqs1) <- match r with
                      | Some er => do (er, eqs1) <- normalize_exp false er;
                                  do (er', eqs2) <- normalize_reset (hd_default er);
                                  ret (Some er', eqs1++eqs2)
                      | None => ret (None, [])
                      end;
      do (es', eqs2) <- normalize_exps es;
      ret ([Eapp f es' r' anns], eqs1++eqs2)
    | Efby inits es anns =>
      if keep_fby then
        do (inits', eqs1) <- normalize_exps inits;
        do (es', eqs2) <- normalize_exps es;
        do (fbys, eqs3) <- normalize_fby inits' es' anns;
        ret (fbys, eqs1++eqs2++eqs3)
      else normalize_exp true e
    | _ => normalize_exp true e
    end.
  Definition normalize_rhss (keep_fby : bool) (es : list exp) :=
    do (es, eqs) <- map_bind2 (normalize_rhs keep_fby) es; ret (concat es, concat eqs).

  Fixpoint combine_for_numstreams {B} (es : list exp) (vs : list B) :=
    match es with
    | [] => []
    | hd::tl => let n := numstreams hd in
                (hd, (firstn n vs))::(combine_for_numstreams tl (skipn n vs))
    end.

  Definition split_equation (eq : equation) : list equation :=
    let (xs, es) := eq in
    List.map (fun '(e, xs) => (xs, [e])) (combine_for_numstreams es xs).

  Definition normalize_equation (to_cut : PS.t) (e : equation) : FreshAnn (list equation) :=
    let '(xs, es) := e in
    do (es', eqs) <- normalize_rhss (negb (existsb (fun x => PS.mem x to_cut) xs)) es;
    ret ((split_equation (xs, es'))++eqs).

  Fixpoint normalize_equations (to_cut : PS.t) (eqs : list equation) : FreshAnn (list equation) :=
    match eqs with
    | [] => ret []
    | hd::tl => do eqs1 <- normalize_equation to_cut hd;
                do eqs2 <- normalize_equations to_cut tl;
                ret (eqs1++eqs2)
    end.

  (** ** Some additional tactics *)

  Definition default_ann : ann := (Op.bool_type, (Cbase, None)).

  Ltac solve_forall :=
    match goal with
    | H: Forall _ ?l |- Forall _ ?l =>
      eapply Forall_impl; [ | eapply H]; intros; simpl in *; eauto
    | |- Forall _ _ =>
      rewrite Forall_forall; intros; eauto
    | _ => idtac
    end.

  Ltac simpl_In :=
    match goal with
    | x : ?t1 * ?t2 |- _ =>
      destruct x
    | H : In (?x1, ?x2) (combine ?l1 ?l2) |- _ =>
      specialize (in_combine_l _ _ _ _ H) as ?; apply in_combine_r in H
    | H : In ?x (map ?f ?l) |- _ =>
      rewrite in_map_iff in H; destruct H as [? [? ?]]; subst
    | |- In ?x (map ?f ?l) =>
      rewrite in_map_iff
    end.

  (** ** Some additional facts *)

  Fact combine_for_numstreams_In {B} : forall es (xs : list B) e x,
      In (e, x) (combine_for_numstreams es xs) ->
      In e es.
  Proof.
    induction es; intros xs e x Hin; simpl in Hin.
    - inv Hin.
    - destruct Hin.
      + inv H. constructor; auto.
      + right. eauto.
  Qed.

  (** ** Propagation of the st_valid property *)

  Fact idents_for_anns_st_valid : forall anns res st st',
      idents_for_anns anns st = (res, st') ->
      fresh_st_valid st ->
      fresh_st_valid st'.
  Proof.
    induction anns; intros res st st' Hidforanns Hvalid;
      simpl in *; repeat inv_bind.
    - assumption.
    - destruct a as [ty [cl _]]. repeat inv_bind.
      eapply IHanns; eauto.
  Qed.
  Hint Resolve idents_for_anns_st_valid.

  Fact init_var_for_clock_st_valid : forall cl res st st',
      init_var_for_clock cl st = (res, st') ->
      fresh_st_valid st ->
      fresh_st_valid st'.
  Proof.
    intros cl res st st' Hinit Hvalid.
    unfold init_var_for_clock in Hinit.
    repeat inv_bind.
    destruct (find _ _).
    - destruct p. inv Hinit. assumption.
    - destruct (fresh_ident _ _) eqn:Hfresh. inv Hinit.
      apply fresh_ident_st_valid in Hfresh; assumption.
  Qed.
  Hint Resolve init_var_for_clock_st_valid.

  Fact fby_iteexp_st_valid : forall e0 e a e' eqs' st st',
      fby_iteexp e0 e a st = (e', eqs', st') ->
      fresh_st_valid st ->
      fresh_st_valid st'.
  Proof with eauto.
    intros e0 e [ty cl] e' eqs' st st' Hfby Hvalid.
    unfold fby_iteexp in Hfby.
    destruct (is_constant e0); repeat inv_bind...
  Qed.
  Hint Resolve fby_iteexp_st_valid.

  Fact normalize_fby_st_valid : forall inits es anns res st st',
      normalize_fby inits es anns st = (res, st') ->
      fresh_st_valid st ->
      fresh_st_valid st'.
  Proof with eauto.
    intros inits es anns res st st' Hnorm Hfresh.
    unfold normalize_fby in Hnorm.
    repeat inv_bind.
    eapply map_bind2_st_valid; eauto.
    apply Forall_forall.
    intros [[i e] [ty cl]] HIn e' eq' st1 st1' Hfby Hst1.
    eapply fby_iteexp_st_valid...
  Qed.
  Hint Resolve normalize_fby_st_valid.

  Fact normalize_reset_st_valid : forall e res st st',
      normalize_reset e st = (res, st') ->
      fresh_st_valid st ->
      fresh_st_valid st'.
  Proof.
    intros e res st st' Hnorm Hvalid.
    destruct (normalize_reset_spec e) as [[v [ann [He Hnorm']]]|Hnorm']; subst;
      rewrite Hnorm' in Hnorm; clear Hnorm';
        try (destruct (hd _ _) as [ty [cl _]]);
        simpl in *; repeat inv_bind; eauto.
  Qed.
  Hint Resolve normalize_reset_st_valid.

  Local Ltac solve_st_valid :=
    match goal with
    | H : map_bind2 _ _ _ = (_, _, ?st) |- fresh_st_valid ?st =>
      eapply map_bind2_st_valid; eauto; solve_forall
    | H : normalize_fby _ _ _ _ = (_, _, ?st) |- fresh_st_valid ?st =>
      eapply normalize_fby_st_valid; eauto
    | H : idents_for_anns _ _ = (_, ?st) |- fresh_st_valid ?st =>
      eapply idents_for_anns_st_valid; eauto
    end.

  Fact normalize_exp_st_valid : forall e is_control res st st',
      normalize_exp is_control e st = (res, st') ->
      fresh_st_valid st ->
      fresh_st_valid st'.
  Proof with eauto.
    induction e using exp_ind2; intros is_control res st st' Hnorm Hvalid;
      simpl in Hnorm.
    - (* const *)
      repeat inv_bind...
    - (* var *)
      repeat inv_bind...
    - (* unop *)
      repeat inv_bind...
    - (* binop *)
      repeat inv_bind...
    - (* fby *)
      repeat inv_bind; repeat solve_st_valid.
    - (* when *)
      destruct a.
      repeat inv_bind; repeat solve_st_valid.
    - (* merge *)
      destruct a.
      destruct is_control; repeat inv_bind; repeat solve_st_valid.
    - (* ite *)
      destruct a.
      destruct is_control; repeat inv_bind; repeat solve_st_valid.
    - (* app *)
      repeat inv_bind; repeat solve_st_valid;
        destruct ro; repeat inv_bind...
  Qed.
  Hint Resolve normalize_exp_st_valid.

  Fact normalize_rhs_st_valid : forall e keep_fby res st st',
      normalize_rhs keep_fby e st = (res, st') ->
      fresh_st_valid st ->
      fresh_st_valid st'.
  Proof.
    intros e keep_fby res st st' Hnorm Hfresh.
    destruct e; try (solve [eapply normalize_exp_st_valid; eauto]);
      simpl in Hnorm; unfold normalize_exps in *.
    - (* fby *)
      destruct keep_fby; repeat inv_bind;
        repeat solve_st_valid;
        eapply Forall_forall; intros; eauto.
    - (* app *)
      repeat inv_bind.
      repeat solve_st_valid.
      destruct o; repeat inv_bind; eauto.
  Qed.
  Hint Resolve normalize_rhs_st_valid.

  Fact normalize_equation_st_valid : forall e to_cut res st st',
      normalize_equation to_cut e st = (res, st') ->
      fresh_st_valid st ->
      fresh_st_valid st'.
  Proof.
    intros [xs es] to_cut res st st' Hnorm Hvalid.
    simpl in *; unfold normalize_rhss in *; repeat inv_bind.
    eapply map_bind2_st_valid; eauto.
    apply Forall_forall. intros; eauto.
  Qed.
  Hint Resolve normalize_equation_st_valid.

  Fact normalize_equations_st_valid : forall eqs to_cut res st st',
      normalize_equations to_cut eqs st = (res, st') ->
      fresh_st_valid st ->
      fresh_st_valid st'.
  Proof.
    induction eqs; intros to_cut res st st' Hnorm Hvalid;
      simpl in *; repeat inv_bind.
    - assumption.
    - eapply IHeqs; eauto.
  Qed.

  (** ** Propagation of the st_follows property *)

  Fact idents_for_anns_st_follows : forall anns res st st',
      idents_for_anns anns st = (res, st') ->
      fresh_st_follows st st'.
  Proof.
    induction anns; intros res st st' Hidforanns;
      simpl in *; repeat inv_bind.
    - reflexivity.
    - destruct a as [ty [cl _]]. repeat inv_bind.
      etransitivity; eauto.
  Qed.
  Hint Resolve idents_for_anns_st_follows.

  Corollary idents_for_anns_incl : forall anns ids st st',
      idents_for_anns anns st = (ids, st') ->
      incl (List.map (fun '(id, (ty, (cl, _))) => (id, (ty, cl))) ids) (idty (st_anns st')).
  Proof.
    induction anns; intros ids st st' Hids; simpl in Hids; repeat inv_bind;
      unfold incl; intros ? Hin; simpl in *; try destruct Hin.
    destruct a as [ty [cl _]]. repeat inv_bind.
    repeat simpl_In. inv H1. inv H2.
    - inv H1.
      apply fresh_ident_In in H.
      apply idents_for_anns_st_follows in H0.
      apply st_follows_incl in H0.
      apply H0 in H.
      unfold idty. simpl_In.
      exists (i, ((t, c), false)); auto.
    - apply IHanns in H0.
      apply H0. repeat simpl_In.
      exists (i, (t, (c, o))); auto.
  Qed.

  Corollary idents_for_anns_incl_ids : forall anns ids st st',
      idents_for_anns anns st = (ids, st') ->
      incl (List.map fst ids) (st_ids st').
  Proof.
    induction anns; intros ids st st' Hids; simpl in Hids; repeat inv_bind;
      unfold incl; intros ? Hin; simpl in *; try destruct Hin.
    destruct a as [ty [cl _]]. repeat inv_bind.
    repeat simpl_In; simpl. inv H2.
    - inv H1.
      apply fresh_ident_In in H.
      unfold st_ids.
      apply idents_for_anns_st_follows in H0.
      apply st_follows_incl in H0.
      apply H0 in H.
      repeat simpl_In. exists (i, ((ty, cl), false)); auto.
    - apply IHanns in H0.
      apply H0. repeat simpl_In.
      exists (i, a); auto.
  Qed.

  Fact init_var_for_clock_st_follows : forall cl res st st',
      init_var_for_clock cl st = (res, st') ->
      fresh_st_follows st st'.
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
      fresh_st_follows st st'.
  Proof.
    intros e0 e [ty cl] res st st' Hfby.
    unfold fby_iteexp in Hfby.
    destruct (is_constant e0); repeat inv_bind.
    - reflexivity.
    - etransitivity; eauto.
  Qed.
  Hint Resolve fby_iteexp_st_follows.

  Fact normalize_fby_st_follows : forall inits es anns res st st',
      normalize_fby inits es anns st = (res, st') ->
      fresh_st_follows st st'.
  Proof.
    intros inits es anns res st st' Hnorm.
    unfold normalize_fby in Hnorm; repeat inv_bind.
    eapply map_bind2_st_follows; eauto.
    rewrite Forall_forall.
    intros [[i e] [ty cl]] HIn e' eq' st1 st1' Hfby. eauto.
  Qed.
  Hint Resolve normalize_fby_st_follows.

  Fact normalize_reset_st_follows : forall e res st st',
      normalize_reset e st = (res, st') ->
      fresh_st_follows st st'.
  Proof.
    intros e res st st' Hnorm.
    destruct (normalize_reset_spec e) as [[v [ann [He Hnorm']]]|Hnorm']; subst;
      simpl in *; repeat inv_bind.
    - reflexivity.
    - rewrite Hnorm' in Hnorm; clear Hnorm'.
      destruct (hd _ _) as [ty [cl _]].
      repeat inv_bind. eauto.
  Qed.
  Hint Resolve normalize_reset_st_follows.

  Local Ltac solve_st_follows' :=
    match goal with
    | |- fresh_st_follows ?st ?st =>
      reflexivity
    | H : fresh_st_follows ?st1 ?st2 |- fresh_st_follows ?st1 _ =>
      etransitivity; [eapply H |]
    | H : fresh_ident _ ?st = _ |- fresh_st_follows ?st _ =>
      etransitivity; [ eapply fresh_ident_st_follows in H; eauto | ]
    | H : idents_for_anns _ ?st = _ |- fresh_st_follows ?st _ =>
      etransitivity; [ eapply idents_for_anns_st_follows in H; eauto | ]
    | H : init_var_for_clock _ ?st = _ |- fresh_st_follows ?st _ =>
      etransitivity; [ eapply init_var_for_clock_st_follows in H; eauto | ]
    | H : fby_iteexp _ _ _ ?st = _ |- fresh_st_follows ?st _ =>
      etransitivity; [ eapply fby_iteexp_st_follows in H; eauto | ]
    | H : normalize_fby _ _ _ ?st = _ |- fresh_st_follows ?st _ =>
      etransitivity; [ eapply normalize_fby_st_follows in H; eauto | ]
    | H : normalize_reset _ ?st = _ |- fresh_st_follows ?st _ =>
      etransitivity; [ eapply normalize_reset_st_follows in H; eauto | ]
    | H : map_bind2 _ _ ?st = _ |- fresh_st_follows ?st _ =>
      etransitivity; [ eapply map_bind2_st_follows in H; eauto; solve_forall | ]
    end.

  Fact normalize_exp_st_follows : forall e is_control res st st',
      normalize_exp is_control e st = (res, st') ->
      fresh_st_follows st st'.
  Proof with eauto.
    induction e using exp_ind2; intros is_control res st st' Hnorm;
      simpl in Hnorm.
    - (* const *)
      repeat inv_bind; reflexivity.
    - (* var *)
      repeat inv_bind; reflexivity.
    - (* unop *)
      repeat inv_bind...
    - (* binop *)
      repeat inv_bind; etransitivity...
    - (* fby *)
      repeat inv_bind; repeat solve_st_follows'.
    - (* when *)
      destruct a.
      repeat inv_bind; repeat solve_st_follows'.
    - (* merge *)
      destruct a.
      destruct is_control; repeat inv_bind; repeat solve_st_follows'.
    - (* ite *)
      destruct a.
      destruct is_control; repeat inv_bind;
        (etransitivity; [ eapply IHe; eauto | repeat solve_st_follows' ]).
    - (* app *)
      destruct ro; repeat inv_bind; repeat solve_st_follows';
        (etransitivity; [ eapply H; eauto | repeat solve_st_follows' ]).
  Qed.
  Hint Resolve normalize_exp_st_follows.

  Corollary normalize_exps_st_follows : forall es res st st',
      normalize_exps es st = (res, st') ->
      fresh_st_follows st st'.
  Proof.
    intros es res st st' Hnorm.
    unfold normalize_exps in Hnorm. repeat inv_bind.
    eapply map_bind2_st_follows; eauto.
    rewrite Forall_forall; intros; eauto.
  Qed.

  Fact normalize_rhs_st_follows : forall e keep_fby res st st',
      normalize_rhs keep_fby e st = (res, st') ->
      fresh_st_follows st st'.
  Proof.
    intros e keep_fby res st st' Hnorm.
    destruct e; try (solve [eapply normalize_exp_st_follows; eauto]);
      simpl in Hnorm; unfold normalize_exps in *.
    - (* fby *)
      destruct keep_fby; repeat inv_bind;
        repeat solve_st_follows';
        eapply Forall_forall; intros; eauto.
    - (* app *)
      destruct o; repeat inv_bind.
      + etransitivity. eapply normalize_exp_st_follows; eauto. repeat solve_st_follows'.
      + repeat solve_st_follows'.
  Qed.
  Hint Resolve normalize_rhs_st_follows.

  Fact normalize_equation_st_follows : forall e to_cut res st st',
      normalize_equation to_cut e st = (res, st') ->
      fresh_st_follows st st'.
  Proof.
    intros [xs es] to_cut res st st' Hnorm.
    simpl in *; unfold normalize_rhss in *; repeat inv_bind.
    eapply map_bind2_st_follows; eauto.
    apply Forall_forall. intros; eauto.
  Qed.
  Hint Resolve normalize_equation_st_follows.

  Fact normalize_equations_st_follows : forall eqs to_cut res st st',
      normalize_equations to_cut eqs st = (res, st') ->
      fresh_st_follows st st'.
  Proof.
    induction eqs; intros to_cut res st st' Hnorm;
      simpl in *; repeat inv_bind.
    - reflexivity.
    - etransitivity; eauto.
  Qed.

  Ltac solve_st_follows :=
    match goal with
    | H : normalize_exp _ _ ?st = _ |- fresh_st_follows ?st _ =>
      etransitivity; [ eapply normalize_exp_st_follows in H; eauto |]
    | H : normalize_exps _ ?st = _ |- fresh_st_follows ?st _ =>
      etransitivity; [ eapply normalize_exps_st_follows in H; eauto |]
    | H : normalize_rhs _ _ ?st = _ |- fresh_st_follows ?st _ =>
      etransitivity; [ eapply normalize_rhs_st_follows in H; eauto |]
    | H : normalize_equation _ _ ?st = _ |- fresh_st_follows ?st _ =>
      etransitivity; [ eapply normalize_equation_st_follows in H; eauto |]
    | H : normalize_equations _ _ ?st = _ |- fresh_st_follows ?st _ =>
      etransitivity; [ eapply normalize_equations_st_follows in H; eauto |]
    | _ => solve_st_follows'
    end.

  (** ** Property on the length of annotations *)

  Inductive wl_exp : exp -> Prop :=
  | wl_Const : forall c,
      wl_exp (Econst c)
  | wl_Evar : forall x a,
      wl_exp (Evar x a)
  | wl_Eunop : forall op e a,
      wl_exp e ->
      numstreams e = 1 ->
      wl_exp (Eunop op e a)
  | wl_Ebinop : forall op e1 e2 a,
      wl_exp e1 ->
      wl_exp e2 ->
      numstreams e1 = 1 ->
      numstreams e2 = 1 ->
      wl_exp (Ebinop op e1 e2 a)
  | wl_Efby : forall e0s es anns,
      Forall wl_exp e0s ->
      Forall wl_exp es ->
      length (annots e0s) = length anns ->
      length (annots es) = length anns ->
      wl_exp (Efby e0s es anns)
  | wl_Ewhen : forall es x b tys nck,
      Forall wl_exp es ->
      length (annots es) = length tys ->
      wl_exp (Ewhen es x b (tys, nck))
  | wl_Emerge : forall x ets efs tys nck,
      Forall wl_exp ets ->
      Forall wl_exp efs ->
      length (annots ets) = length tys ->
      length (annots efs) = length tys ->
      wl_exp (Emerge x ets efs (tys, nck))
  | wl_Eifte : forall e ets efs tys nck,
      wl_exp e ->
      Forall wl_exp ets ->
      Forall wl_exp efs ->
      numstreams e = 1 ->
      length (annots ets) = length tys ->
      length (annots efs) = length tys ->
      wl_exp (Eite e ets efs (tys, nck))
  | wl_Eapp : forall f es anns,
      Forall wl_exp es ->
      wl_exp (Eapp f es None anns)
  | wl_EappReset : forall f es r anns,
      wl_exp r ->
      Forall wl_exp es ->
      numstreams r = 1 ->
      wl_exp (Eapp f es (Some r) anns).

  Definition wl_equation (eq : equation) :=
    let (xs, es) := eq in
    Forall wl_exp es /\ length xs = length (annots es).

  Definition wl_node (n : node) :=
    Forall wl_equation (n_eqs n).

  Definition wl_global (G : global) :=
    Forall wl_node G.

  (** ** Length of normalized expression *)

  Ltac idents_for_anns_length :=
    match goal with
    | H : idents_for_anns ?anns _ = (?ids, _) |- length ?ids = length ?anns =>
      apply idents_for_anns_values in H;
      rewrite Forall2_forall2 in H; destruct H;
      auto
    | H : idents_for_anns (List.map _ ?anns) _ = (?ids, _) |- length ?ids = length ?anns =>
      apply idents_for_anns_values in H;
      rewrite Forall2_forall2 in H; destruct H;
      rewrite map_length in *; auto
    end.

  Ltac rewrite_Forall_forall :=
    match goal with
    | H : Forall _ _ |- _ =>
      rewrite Forall_forall in H
    | H : Forall2 _ _ _ |- _ =>
      rewrite Forall2_forall2 in H; destruct H
    | H : Forall3 _ _ _ _ |- _ =>
      rewrite Forall3_forall3 in H; destruct H as [? [? ?]]
    | |- Forall _ _ =>
      rewrite Forall_forall; intros; subst
    | |- Forall2 _ _ _ =>
      rewrite Forall2_forall2; repeat split; auto; intros; subst
    | |- Forall3 _ _ _ _ =>
      rewrite Forall3_forall3; repeat split; auto; intros; subst
    end.

  Ltac subst_length :=
    match goal with
    | H: length ?x1 = length ?x2 |- context l [length ?x1] =>
      setoid_rewrite H
    | H: length ?x1 = length ?x2, H1: context l [length ?x1] |- _ =>
      setoid_rewrite H in H1
    | H: ?x1 = ?x2 |- context l [length ?x1] =>
      setoid_rewrite H
    | H: ?x1 = ?x2, H1: context l [length ?x1] |- _ =>
      setoid_rewrite H in H1
    end.

  Ltac simpl_length :=
    repeat subst_length;
    (match goal with
     | H : context c [typesof _] |- _ =>
       rewrite typesof_annots in H
     | H : context c [clocksof _] |- _ =>
       rewrite clocksof_annots in H
     | H : _ < Nat.min _ _ |- _ =>
       setoid_rewrite Nat.min_glb_lt_iff in H; destruct H
     | H : context c [Nat.min ?x1 ?x1] |- _ =>
       repeat setoid_rewrite PeanoNat.Nat.min_id in H
     | H : context c [length (combine _ _)] |- _ =>
       setoid_rewrite combine_length in H
     | H : context c [length (map ?l1 ?l2)] |- _ =>
       setoid_rewrite map_length in H
     | |- _ < Nat.min _ _ =>
       apply Nat.min_glb_lt
     | |- context c [Nat.min ?x1 ?x1] =>
       setoid_rewrite PeanoNat.Nat.min_id
     | |- context c [length (combine _ _)] =>
       setoid_rewrite combine_length
     | |- context c [length (map _ _)] =>
       setoid_rewrite map_length
     | |- context c [typesof _] =>
       rewrite typesof_annots
     | |- context c [clocksof _] =>
       rewrite clocksof_annots
     | _ => idtac
    end).

  Ltac solve_length :=
    repeat simpl_length; auto; try congruence.

  Ltac simpl_nth :=
    match goal with
    | H : In ?x _ |- _ =>
      apply In_nth with (d:=x) in H; destruct H as [? [? ?]]
    | H : context c [nth _ (combine _ _) (?x1, ?x2)] |- _ =>
      rewrite (combine_nth _ _ _ x1 x2) in H; [inv H|clear H;try solve_length]
    | H : context c [nth _ (map _ _) _] |- _ =>
      erewrite map_nth' in H; [|clear H; try solve_length]
    | |- context c [nth _ (map _ _) _] =>
      erewrite map_nth'; [| try solve_length]
    end.

  Fact map_bind2_length : forall is_control es es' eqs' st st',
      Forall2 (fun e es' => forall eqs' st st',
                   normalize_exp is_control e st = (es', eqs', st') ->
                   length es' = numstreams e) es es' ->
    map_bind2 (normalize_exp is_control) es st = (es', eqs', st') ->
    length (concat es') = length (annots es).
  Proof.
    intros is_control es es' eqs' st st' Hf Hmap.
    apply map_bind2_values in Hmap.
    unfold annots. rewrite flat_map_concat_map.
    apply concat_length_eq.
    repeat rewrite_Forall_forall.
    + rewrite map_length; auto.
    + replace (length es') in *.
      specialize (H3 (hd_default []) a [] _ _ _ _ H4 eq_refl eq_refl eq_refl) as [? [? H3]].
      erewrite (map_nth' _ _ _ (hd_default [])); eauto.
      rewrite length_annot_numstreams.
      eapply H0; eauto.
  Qed.

  Local Hint Resolve nth_In.
  Fact normalize_exp_length : forall e is_control es' eqs' st st',
      wl_exp e ->
      normalize_exp is_control e st = (es', eqs', st') ->
      length es' = numstreams e.
  Proof with eauto.
    induction e using exp_ind2; intros is_control es' eqs' st st' Hwl Hnorm;
      simpl in *; inv Hwl; repeat inv_bind; auto.
    - (* fby *)
      simpl in *. rewrite map_length.
      apply idents_for_anns_length in H8...
    - (* when *)
      rewrite map_length.
      eapply map_bind2_length in H0.
      + solve_length.
      + eapply map_bind2_values in H0.
        repeat rewrite_Forall_forall...
    - (* merge *)
      destruct is_control; repeat inv_bind.
      + apply map_bind2_length in H1; [| eapply map_bind2_values in H1; repeat rewrite_Forall_forall; eauto].
        apply map_bind2_length in H2; [| eapply map_bind2_values in H2; repeat rewrite_Forall_forall; eauto].
        repeat rewrite typesof_annots. solve_length.
      + apply idents_for_anns_length in H3.
        rewrite map_length in *.
        assumption.
    - (* ite *)
      destruct is_control; repeat inv_bind.
      + apply map_bind2_length in H2; [| eapply map_bind2_values in H2; repeat rewrite_Forall_forall; eauto].
        apply map_bind2_length in H3; [| eapply map_bind2_values in H3; repeat rewrite_Forall_forall; eauto].
        repeat rewrite typesof_annots. solve_length.
      + apply idents_for_anns_length in H4.
        rewrite map_length in *.
        assumption.
    - (* app *)
      apply idents_for_anns_length in H3.
      rewrite map_length. congruence.
    - (* app (reset) *)
      apply idents_for_anns_length in H3.
      rewrite map_length. congruence.
  Qed.

  Corollary map_bind2_normalize_exp_length : forall is_control es es' eqs' st st',
      Forall wl_exp es ->
      map_bind2 (normalize_exp is_control) es st = (es', eqs', st') ->
      length (concat es') = length (annots es).
  Proof.
    intros is_control es es' eqs' st st' Hf Hmap.
    eapply map_bind2_length; eauto.
    eapply map_bind2_values in Hmap.
    repeat rewrite_Forall_forall.
    eapply normalize_exp_length; eauto.
  Qed.

  Corollary normalize_exps_length : forall es es' eqs' st st',
      Forall wl_exp es ->
      normalize_exps es st = (es', eqs', st') ->
      length es' = length (annots es).
  Proof.
    intros es es' eqs' st st' Hwt Hnorm.
    unfold normalize_exps in Hnorm.
    repeat inv_bind.
    eapply map_bind2_normalize_exp_length; eauto.
  Qed.

  Fact normalize_fby_length : forall inits es anns es' eqs' st st',
      length inits = length anns ->
      length es = length anns ->
      normalize_fby inits es anns st = (es', eqs', st') ->
      length es' = length anns.
  Proof.
    intros inits es anns es' eqs' st st' Hlen1 Hlen2 Hnorm.
    unfold normalize_fby in Hnorm.
    repeat inv_bind.
    apply map_bind2_values in H.
    rewrite_Forall_forall; clear H0 H1.
    repeat rewrite combine_length in H.
    replace (length inits) in *.
    replace (length es) in *.
    repeat rewrite PeanoNat.Nat.min_id in H.
    auto.
  Qed.

  Fact normalize_rhs_length : forall e keep_fby es' eqs' st st',
      wl_exp e ->
      normalize_rhs keep_fby e st = (es', eqs', st') ->
      (length es' = 1 \/ length es' = numstreams e).
  Proof.
    intros e keep_fby es' eqs' st st' Hwt Hnorm;
      destruct e; unfold normalize_rhs in Hnorm;
        try (solve [right; eapply normalize_exp_length; eauto]);
        try (destruct o); destruct keep_fby; repeat inv_bind; auto.
    - (* keep_fby = true *)
      right. inv Hwt.
      eapply normalize_fby_length; eauto.
      + eapply normalize_exps_length in H; eauto. congruence.
      + eapply normalize_exps_length in H0; eauto. congruence.
    - (* keep_fby = false *)
      eapply normalize_exp_length in Hnorm; eauto.
  Qed.

  (** ** Preservation of annotations : useful for the rest of the proofs :p *)

  Definition without_names (anns: list ann) : list (type * clock) :=
    List.map (fun '(ty, (cl, _)) => (ty, cl)) anns.

  Fact typeof_without_names : forall e,
      typeof e = map fst (without_names (annot e)).
  Proof.
    intros e.
    unfold without_names.
    rewrite map_map; simpl. rewrite typeof_annot.
    induction (annot e); simpl; f_equal; auto.
    destruct a as [ty [cl ?]]; auto.
  Qed.

  Fact typesof_without_names : forall e,
      typesof e = map fst (without_names (annots e)).
  Proof.
    intros e.
    unfold without_names.
    rewrite map_map; simpl. rewrite typesof_annots.
    induction (annots e); simpl; f_equal; auto.
    destruct a as [ty [cl ?]]; auto.
  Qed.

  Fact clockof_without_names : forall e,
      clockof e = map snd (without_names (annot e)).
  Proof.
    intros e.
    unfold without_names.
    rewrite map_map; simpl. rewrite clockof_annot.
    induction (annot e); simpl; f_equal; auto.
    destruct a as [ty [cl ?]]; auto.
  Qed.

  Fact clocksof_without_names : forall e,
      clocksof e = map snd (without_names (annots e)).
  Proof.
    intros e.
    unfold without_names.
    rewrite map_map; simpl. rewrite clocksof_annots.
    induction (annots e); simpl; f_equal; auto.
    destruct a as [ty [cl ?]]; auto.
  Qed.

  Fact normalize_exp_annot : forall e is_control es' eqs' st st',
      wl_exp e ->
      normalize_exp is_control e st = (es', eqs', st')  ->
      without_names (annots es') = without_names (annot e).
  Proof.
    induction e; intros is_control es' eqs' st st' Hwt Hnorm;
      specialize (normalize_exp_length _ _ es' eqs' st st' Hwt Hnorm) as Hlength;
      simpl in *; repeat inv_bind; auto.
    - (* fby *)
      apply idents_for_anns_values in H2.
      clear H1 Hwt; (induction H2; [ auto | destruct y; subst; simpl; f_equal; auto ]).
      destruct p as [ty [cl ?]]. destruct x as [ty' [cl' ?]].
      destruct H1 as [? [? _]]. f_equal; auto.
    - (* when *)
      destruct l0. repeat inv_bind.
      rewrite map_length in Hlength.
      assert (Forall2 (fun '(e, ty) ty' => typeof (Ewhen [e] i b ([ty], n)) = [ty']) (combine (concat x0) l0) l0) as Hf.
      { rewrite_Forall_forall.
        destruct nth eqn:Hnth; simpl; f_equal.
        destruct a.
        specialize (combine_length_r _ _ Hlength) as Hlen'.
        specialize (combine_nth_r _ _ n0 e0 t0 Hlen') as [d Hnth'].
        rewrite Hnth' in Hnth; inv Hnth.
        apply nth_indep; rewrite <- Hlength; auto.
      } clear Hwt.
      induction Hf; simpl; auto.
      destruct x; simpl in *. inv H0. f_equal; auto.
    - (* merge *)
      clear Hwt.
      destruct l1.
      destruct is_control; repeat inv_bind; rewrite map_length in *.
      + (* control *)
        assert (Forall2 (fun '(e1, e2, ty) ty' => typeof (Emerge i [e1] [e2] ([ty], n)) = [ty'])
                        (combine (combine (concat x2) (concat x4)) l1) l1) as Hf.
        { rewrite_Forall_forall.
          destruct (nth n0 _ a) eqn:Hnth. destruct p; simpl; f_equal.
          destruct a as [[d1 d2] d3].
          specialize (combine_length_r _ _ Hlength) as Hlen'.
          specialize (combine_nth_r _ _ n0 (d1, d2) d3 Hlen') as [d Hnth'].
          rewrite Hnth' in Hnth; inv Hnth.
          apply nth_indep; rewrite <- Hlength; auto.
        }
        induction Hf; simpl; auto.
        destruct x as [[e1 e2] a]. inv Hlength. simpl in *.
        inv H1. f_equal; auto.
      + (* exp *)
        clear Hlength.
        apply idents_for_anns_values in H1.
        rewrite Forall2_map_1 in H1.
        induction H1; simpl; auto.
        destruct y; simpl in *. f_equal; auto.
        destruct p as [ty [cl ?]]. destruct n as [cl' ?].
        destruct H1 as [? [? _]]. f_equal; auto.
    - (* ite *)
      clear Hwt.
      destruct l1.
      destruct is_control; repeat inv_bind; rewrite map_length in *.
      + (* control *)
        assert (Forall2 (fun '(e1, e2, ty) ty' => typeof (Eite (hd_default x) [e1] [e2] ([ty], n)) = [ty'])
                        (combine (combine (concat x5) (concat x7)) l1) l1) as Hf.
        { rewrite_Forall_forall.
          destruct (nth n0 _ a) eqn:Hnth. destruct p; simpl; f_equal.
          destruct a as [[d1 d2] d3].
          specialize (combine_length_r _ _ Hlength) as Hlen'.
          specialize (combine_nth_r _ _ n0 (d1, d2) d3 Hlen') as [d Hnth'].
          rewrite Hnth' in Hnth; inv Hnth.
          apply nth_indep; rewrite <- Hlength; auto.
        }
        induction Hf; simpl; auto.
        destruct x2 as [[e1 e2] a]. inv Hlength. simpl in *.
        inv H2. f_equal; auto.
      + (* exp *)
        clear Hlength.
        apply idents_for_anns_values in H2.
        rewrite Forall2_map_1 in H2.
        induction H2; simpl; auto.
        destruct y; simpl in *. f_equal; auto.
        destruct p as [ty [cl ?]]. destruct n as [cl' ?].
        destruct H2 as [? [? _]]. f_equal; auto.
    - (* app *)
      clear Hwt.
      repeat inv_bind.
      apply idents_for_anns_values in H1.
      induction H1; simpl in *; auto.
      destruct y; subst; simpl. inv Hlength. f_equal; auto.
      destruct p as [ty [cl ?]]. destruct x2 as [ty' [cl' ?]].
      destruct H1 as [? [? _]]. f_equal; auto.
  Qed.

  Corollary map_bind2_normalize_exp_annots' :
    forall is_control es es' eqs' st st',
      Forall wl_exp es ->
      map_bind2 (normalize_exp is_control) es st = (es', eqs', st') ->
      Forall2 (fun es' e => without_names (annots es') = without_names (annot e)) es' es.
  Proof.
    intros is_control es es' eqs' st st' Hf Hmap.
    apply map_bind2_values in Hmap.
    induction Hmap.
    - constructor.
    - destruct H as [? [? Hnorm]]. inv Hf.
      constructor; eauto.
      eapply normalize_exp_annot; eauto.
  Qed.

  Corollary map_bind2_normalize_exp_annots :
    forall is_control es es' eqs' st st',
      Forall wl_exp es ->
      map_bind2 (normalize_exp is_control) es st = (es', eqs', st') ->
      without_names (annots (concat es')) = without_names (annots es).
  Proof.
    intros is_control es es' a2s st st' Hwt Hmap.
    eapply map_bind2_normalize_exp_annots' in Hmap; eauto.
    induction Hmap; simpl.
    - reflexivity.
    - inv Hwt.
      unfold annots in *; rewrite flat_map_concat_map in *.
      unfold without_names in *; rewrite map_app; rewrite concat_app; repeat rewrite map_app.
      f_equal; auto.
  Qed.

  Corollary normalize_exps_annots : forall es es' eqs' st st',
      Forall wl_exp es ->
      normalize_exps es st = (es', eqs', st') ->
      without_names (annots es') = without_names (annots es).
  Proof.
    intros es es' eqs' st st' Hwt Hnorm.
    unfold normalize_exps in Hnorm; repeat inv_bind.
    eapply map_bind2_normalize_exp_annots in H; eauto.
  Qed.

  Fact fby_iteexp_annot : forall e0 e ann es' eqs' st st',
      fby_iteexp e0 e ann st = (es', eqs', st') ->
      without_names (annot es') = without_names [ann].
  Proof.
    intros e0 e [ty [cl n]] es' eqs' st st' Hfby.
    unfold fby_iteexp in Hfby.
    destruct (is_constant e0); repeat inv_bind; reflexivity.
  Qed.

  Fact normalize_fby_annot : forall inits es anns es' eqs' st st',
      length inits = length anns ->
      length es = length anns ->
      normalize_fby inits es anns st = (es', eqs', st') ->
      without_names (annots es') = without_names anns.
  Proof.
    intros inits es anns es' eqs' st st' Hlen1 Hlen2 Hnorm.
    specialize (normalize_fby_length _ _ _ _ _ _ _ Hlen1 Hlen2 Hnorm) as Hlen.
    unfold normalize_fby in Hnorm.
    repeat inv_bind.
    apply map_bind2_values in H.
    assert (Forall2 (fun e a => without_names (annot e) = without_names [a]) es' anns) as Hf.
    { repeat rewrite_Forall_forall.
      rewrite <- H in H2.
      specialize (H1 (a, a, b) a [] _ _ _ _ H2 eq_refl eq_refl eq_refl); destruct H1 as [? [? ?]].
      destruct nth eqn:Hnth in H1. destruct p.
      apply fby_iteexp_annot in H1.
      rewrite combine_nth in Hnth; auto.
      + inv Hnth. assumption.
      + rewrite combine_length.
        replace (length inits). replace (length es).
        apply PeanoNat.Nat.min_id.
    } clear H Hlen Hlen1 Hlen2.
    induction Hf; simpl; auto.
    unfold without_names in *. rewrite map_app.
    destruct y as [? [? ?]].
    setoid_rewrite H. setoid_rewrite IHHf. auto.
  Qed.

  Fact normalize_rhs_annot : forall e keep_fby es' eqs' st st',
      wl_exp e ->
      normalize_rhs keep_fby e st = (es', eqs', st') ->
      without_names (annots es') = without_names (annot e).
  Proof.
    intros e keep_fby es' eqs' st st' Hwt Hnorm.
    destruct e; unfold normalize_rhs in Hnorm;
      try (solve [eapply normalize_exp_annot in Hnorm; eauto]).
    - (* fby *)
      destruct keep_fby.
      + repeat inv_bind. inv Hwt.
        erewrite normalize_fby_annot; eauto.
        * eapply normalize_exps_length in H; eauto. congruence.
        * eapply normalize_exps_length in H0; eauto. congruence.
      + eapply normalize_exp_annot in Hnorm; eauto.
    - (* app *)
      destruct o; repeat inv_bind; simpl; rewrite app_nil_r; reflexivity.
  Qed.

  Corollary normalize_rhss_annots : forall es keep_fby es' eqs' st st',
      Forall wl_exp es ->
      normalize_rhss keep_fby es st = (es', eqs', st') ->
      without_names (annots es') = without_names (annots es).
  Proof.
    intros es keep_fby es' eqs' st st' Hf Hnorm.
    unfold normalize_rhss in Hnorm. repeat inv_bind.
    apply map_bind2_values in H.
    induction H; simpl in *.
    - reflexivity.
    - inv Hf.
      destruct H as [? [? H]]. eapply normalize_rhs_annot in H; eauto.
      unfold annots in *. rewrite flat_map_concat_map in *.
      unfold without_names in *. rewrite map_app. rewrite concat_app. repeat rewrite map_app.
      f_equal; auto.
  Qed.

  Fact normalize_exp_numstreams : forall e is_control es' eqs' st st',
      normalize_exp is_control e st = (es', eqs', st') ->
      Forall (fun e => numstreams e = 1) es'.
  Proof.
    intros e is_control es' eqs' st st' Hnorm.
    induction e; simpl in Hnorm; repeat inv_bind; repeat constructor.
    2: destruct l0.
    3,4: destruct l1.
    3,4: destruct is_control.
    1,2,3,4,5,6,7:(repeat inv_bind; rewrite Forall_forall; intros ? Hin;
                   repeat simpl_In; reflexivity).
  Qed.

  Corollary map_bind2_normalize_exp_numstreams : forall es is_control es' eqs' st st',
      map_bind2 (normalize_exp is_control) es st = (es', eqs', st') ->
      Forall (fun e => numstreams e = 1) (concat es').
  Proof.
    intros es is_control es' eqs' st st' Hmap.
    apply map_bind2_values in Hmap.
    induction Hmap; simpl.
    - constructor.
    - apply Forall_app; split; auto.
      destruct H as [? [? H]].
      eapply normalize_exp_numstreams; eauto.
  Qed.

  Corollary normalize_exps_numstreams : forall es es' eqs' st st',
      normalize_exps es st = (es', eqs', st') ->
      Forall (fun e => numstreams e = 1) es'.
  Proof.
    intros es es' eqs' st st' Hnorm.
    unfold normalize_exps in Hnorm. repeat inv_bind.
    eapply map_bind2_normalize_exp_numstreams. eauto.
  Qed.

  Fact normalize_fby_numstreams : forall e0s es anns es' eqs' st st',
      normalize_fby e0s es anns st = (es', eqs', st') ->
      Forall (fun e => numstreams e = 1) es'.
  Proof.
    intros e0s es anns es' eqs' st st' Hnorm.
    unfold normalize_fby in Hnorm. repeat inv_bind.
    apply map_bind2_values in H.
    repeat rewrite_Forall_forall.
    eapply In_nth with (d:=x) in H2; destruct H2 as [n [? ?]].
    repeat simpl_length.
    specialize (H1 (x, x, (Op.bool_type, (Cbase, None))) x [] _ _ _ _ H2 eq_refl eq_refl eq_refl).
    destruct H1 as [st'' [st''' H1]]. destruct (nth _ _ _) as [[e0 e] [ty cl]]. rewrite <- H3.
    unfold fby_iteexp in H1.
    destruct (is_constant e0); repeat inv_bind; reflexivity.
  Qed.

  (** ** Propagation of the variable permutation property *)

  Fact idents_for_anns_vars_perm : forall anns ids st st',
      idents_for_anns anns st = (ids, st') ->
      Permutation ((map fst ids)++(st_ids st)) (st_ids st').
  Proof.
    induction anns; intros ids st st' Hidents; simpl in Hidents; repeat inv_bind.
    - reflexivity.
    - destruct a as [ty [cl _]]. repeat inv_bind.
      apply fresh_ident_vars_perm in H.
      apply IHanns in H0.
      etransitivity. 2: eapply H0.
      etransitivity. eapply Permutation_middle.
      apply Permutation_app_head. assumption.
  Qed.

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

  Fact map_bind2_vars_perm {A B} : forall (k : A -> FreshAnn (B * list equation)) es es' eqs' st st',
      map_bind2 k es st = (es', eqs', st') ->
      Forall (fun e => forall es' eqs' st st',
                  k e st = (es', eqs', st') ->
                  Permutation ((vars_defined eqs')++(st_ids st)) (st_ids st')) es ->
      Permutation ((vars_defined (concat eqs'))++(st_ids st)) (st_ids st').
  Proof.
    induction es; intros es' eqs' st st' Hmap Hf;
      simpl in *; repeat inv_bind.
    - reflexivity.
    - inv Hf.
      specialize (IHes _ _ _ _ H0 H4).
      specialize (H3 _ _ _ _ H).
      etransitivity. 2: apply IHes.
      unfold vars_defined in *. simpl in *. rewrite <- flat_map_app.
      rewrite <- app_assoc. rewrite Permutation_swap.
      apply Permutation_app_head. assumption.
  Qed.

  Fact normalize_fby_vars_perm : forall inits es anns es' eqs' st st',
      normalize_fby inits es anns st = ((es', eqs'), st') ->
      Permutation ((vars_defined eqs')++(st_ids st)) (st_ids st').
  Proof.
    intros inits es anns es' eqs' st st' Hnorm.
    unfold normalize_fby in Hnorm; repeat inv_bind.
    eapply map_bind2_vars_perm. eapply H.
    apply Forall_forall; intros [[e0 e] [ty cl]] Hin; intros.
    unfold fby_iteexp in H0.
    destruct (is_constant e0); repeat inv_bind.
    - reflexivity.
    - apply fresh_ident_vars_perm in H1.
      etransitivity. 2 : apply H1.
      apply perm_skip.
      eapply init_var_for_clock_vars_perm; eauto.
  Qed.

  Fact normalize_reset_vars_perm : forall e e' eqs' st st',
      normalize_reset e st = ((e', eqs'), st') ->
      Permutation ((vars_defined eqs')++(st_ids st)) (st_ids st').
  Proof.
    intros e e' eqs' st st' Hnorm.
    destruct (normalize_reset_spec e) as [[v [ann [Hv Hspec]]]| Hspec];
      subst; rewrite Hspec in Hnorm; clear Hspec.
    - repeat inv_bind. reflexivity.
    - destruct (hd _ _) as [ty [cl _]]; simpl in *. repeat inv_bind.
      eapply fresh_ident_vars_perm; eauto.
  Qed.

  Fact normalize_exp_vars_perm : forall e is_control es' eqs' st st',
      wl_exp e ->
      normalize_exp is_control e st = ((es', eqs'), st') ->
      Permutation ((vars_defined eqs')++(st_ids st)) (st_ids st').
  Proof with eauto.
    induction e using exp_ind2; intros is_control e' eqs' st st' Hwt Hnorm;
      simpl in Hnorm; inv Hwt.
    - (* const *)
      repeat inv_bind...
    - (* var *)
      repeat inv_bind...
    - (* unop *)
      repeat inv_bind...
    - (* binop *)
      repeat inv_bind.
      unfold vars_defined in *; rewrite <- flat_map_app; rewrite <- app_assoc.
      apply IHe1 in H...
      apply IHe2 in H0...
      etransitivity. 2: eauto.
      rewrite Permutation_swap.
      apply Permutation_app_head...
    - (* fby *)
      repeat inv_bind.
      assert (length x5 = length x8) as Hlen58.
      { apply map_bind2_normalize_exp_length in H1...
        apply map_bind2_normalize_exp_length in H2...
        apply idents_for_anns_length in H8...
        apply normalize_fby_length in H3; solve_length.
      }
      apply map_bind2_vars_perm in H1. 2: (rewrite Forall_forall in *; eauto).
      apply map_bind2_vars_perm in H2. 2: (rewrite Forall_forall in *; eauto).
      apply normalize_fby_vars_perm in H3.
      apply idents_for_anns_vars_perm in H8.
      unfold vars_defined in *. rewrite flat_map_concat_map in *.
      etransitivity. 2 : apply H8. clear H8.
      repeat rewrite map_app. rewrite map_map; simpl.
      replace (map (fun x => fst (let '(x0, _, fby) := x in ([x0], [fby]))) (combine x8 x5)) with (map (fun x => [fst x]) x8).
      2: { refine (list_ind2 (fun l1 l2 => _) _ _ x5 x8 Hlen58); simpl.
           + reflexivity.
           + intros. destruct b; simpl.
             f_equal. assumption. }
      repeat rewrite concat_app.
      replace (concat (map (fun x => [fst x]) x8)) with (map fst x8).
      2: { clear Hlen58. induction x8; simpl; f_equal; auto. }
      repeat rewrite <- app_assoc. apply Permutation_app_head.
      etransitivity. 2: eauto.
      rewrite app_assoc. rewrite Permutation_swap. apply Permutation_app_head.
      etransitivity. 2: eauto.
      rewrite <- app_assoc. rewrite Permutation_swap. apply Permutation_app_head.
      assumption.
    - (* when *)
      repeat inv_bind.
      eapply map_bind2_vars_perm...
      rewrite Forall_forall in *. intros...
    - (* merge *)
      destruct is_control; repeat inv_bind.
      + apply map_bind2_vars_perm in H1. 2: (rewrite Forall_forall in *; eauto).
        apply map_bind2_vars_perm in H2. 2: (rewrite Forall_forall in *; eauto).
        etransitivity. 2: apply H2.
        unfold vars_defined in *; rewrite <- flat_map_app; repeat rewrite <- app_assoc.
        rewrite Permutation_swap. apply Permutation_app_head.
        assumption.
      + unfold vars_defined; rewrite flat_map_concat_map.
        repeat rewrite map_app. repeat rewrite concat_app.
        rewrite combine_map_fst'.
        2: {
          repeat rewrite map_length. repeat rewrite combine_length.
          repeat rewrite typesof_annots in *.
          assert (length (concat x3) = length (annots ets)) as Hlen3 by (eapply map_bind2_normalize_exp_length; eauto).
          assert (length (concat x7) = length (annots efs)) as Hlen7 by (eapply map_bind2_normalize_exp_length; eauto).
          apply idents_for_anns_length in H3.
          solve_length. }
        apply map_bind2_vars_perm in H1. 2: (repeat rewrite_Forall_forall; eauto).
        apply map_bind2_vars_perm in H2. 2: (repeat rewrite_Forall_forall; eauto).
        apply idents_for_anns_vars_perm in H3.
        etransitivity. 2: eauto.
        replace (concat (map (fun '(id, _) => [id]) x6)) with (map fst x6).
        2: { clear H3. induction x6; try destruct a; simpl; f_equal; auto. }
        repeat rewrite <- app_assoc. apply Permutation_app_head.
        etransitivity. 2: eauto.
        unfold vars_defined in *; rewrite flat_map_concat_map in *.
        rewrite Permutation_swap. apply Permutation_app_head.
        assumption.
    - (* ite *)
      destruct is_control; repeat inv_bind.
      + apply map_bind2_vars_perm in H2. 2: (rewrite Forall_forall in *; eauto).
        apply map_bind2_vars_perm in H3. 2: (rewrite Forall_forall in *; eauto).
        apply IHe in H1; eauto.
        etransitivity. 2: eauto.
        unfold vars_defined in *; repeat rewrite <- flat_map_app.
        rewrite <- app_assoc. rewrite Permutation_swap.
        rewrite <- app_assoc. rewrite Permutation_swap. apply Permutation_app_head.
        etransitivity. 2: eauto.
        apply Permutation_app_head.
        assumption.
      + unfold vars_defined; rewrite flat_map_concat_map.
        repeat rewrite map_app. repeat rewrite concat_app.
        rewrite combine_map_fst'.
        2: {
          repeat rewrite map_length. repeat rewrite combine_length.
          repeat rewrite typesof_annots in *.
          assert (length (concat x5) = length (annots ets)) as Hlen3 by (eapply map_bind2_normalize_exp_length; eauto).
          assert (length (concat x9) = length (annots efs)) as Hlen7 by (eapply map_bind2_normalize_exp_length; eauto).
          apply idents_for_anns_length in H4.
          solve_length. }
        apply map_bind2_vars_perm in H2. 2: (repeat rewrite_Forall_forall; eauto).
        apply map_bind2_vars_perm in H3. 2: (repeat rewrite_Forall_forall; eauto).
        apply idents_for_anns_vars_perm in H4.
        apply IHe in H1; eauto.
        etransitivity. 2: eauto.
        replace (concat (map (fun '(id, _) => [id]) x8)) with (map fst x8).
        2: { clear H4. induction x8; try destruct a; simpl; f_equal; auto. }
        repeat rewrite <- app_assoc. apply Permutation_app_head.
        etransitivity. 2: eauto.
        unfold vars_defined in *; rewrite flat_map_concat_map in *.
        rewrite app_assoc. rewrite Permutation_swap. apply Permutation_app_head.
        etransitivity. 2: eauto.
        rewrite <- app_assoc. rewrite Permutation_swap. apply Permutation_app_head.
        assumption.
    - (* app *)
      repeat inv_bind.
      apply idents_for_anns_vars_perm in H3.
      apply map_bind2_vars_perm in H1. 2: (repeat rewrite_Forall_forall; eauto).
      etransitivity. 2: apply H3.
      rewrite <- app_assoc. apply Permutation_app_head.
      assumption.
    - (* app (reset) *)
      repeat inv_bind.
      apply idents_for_anns_vars_perm in H3.
      apply map_bind2_vars_perm in H2. 2: (repeat rewrite_Forall_forall; eauto).
      apply normalize_reset_vars_perm in H5.
      apply H in H1; eauto.
      etransitivity. 2: eauto.
      repeat rewrite <- app_assoc. apply Permutation_app_head.
      etransitivity. 2: eauto.
      unfold vars_defined in *. repeat rewrite flat_map_concat_map in *.
      repeat rewrite map_app in *. repeat rewrite concat_app in *.
      rewrite <- app_assoc. rewrite Permutation_swap.
      rewrite <- app_assoc. rewrite Permutation_swap. apply Permutation_app_head.
      etransitivity. 2: eauto.
      apply Permutation_app_head.
      assumption.
  Qed.

  Corollary normalize_exps_vars_perm : forall es es' eqs' st st',
      Forall wl_exp es ->
      normalize_exps es st = ((es', eqs'), st') ->
      Permutation ((vars_defined eqs')++(st_ids st)) (st_ids st').
  Proof with eauto.
    intros es es' eqs' st st' Hf Hnorm.
    unfold normalize_exps in Hnorm.
    repeat inv_bind.
    eapply map_bind2_vars_perm...
    repeat rewrite_Forall_forall.
    eapply normalize_exp_vars_perm...
  Qed.

  Fact normalize_rhs_vars_perm : forall e keep_fby es' eqs' st st',
      wl_exp e ->
      normalize_rhs keep_fby e st = ((es', eqs'), st') ->
      Permutation ((vars_defined eqs')++(st_ids st)) (st_ids st').
  Proof with eauto.
    intros e keep_fby es' eqs' st st' Hwt Hnorm.
    destruct e; unfold normalize_rhs in Hnorm;
      try (solve [eapply normalize_exp_vars_perm; eauto]); inv Hwt; repeat inv_bind.
    - (* fby *)
      destruct keep_fby.
      + repeat inv_bind.
        eapply normalize_exps_vars_perm in H...
        eapply normalize_exps_vars_perm in H0...
        eapply normalize_fby_vars_perm in H1.
        etransitivity. 2: eauto.
        unfold vars_defined in *. repeat rewrite flat_map_concat_map in *.
        repeat rewrite map_app. repeat rewrite concat_app.
        repeat (rewrite <- app_assoc; rewrite Permutation_swap).
        apply Permutation_app_head.
        etransitivity. 2: eauto.
        apply Permutation_app_head.
        assumption.
      + eapply normalize_exp_vars_perm; eauto.
        econstructor; eauto.
    - (* app *)
      eapply normalize_exps_vars_perm in H; eauto.
    - (* app (reset) *)
      eapply normalize_exp_vars_perm in H; eauto.
      eapply normalize_exps_vars_perm in H0; eauto.
      eapply normalize_reset_vars_perm in H1.
      etransitivity. 2: eauto.
      unfold vars_defined in *. repeat rewrite flat_map_concat_map in *.
      repeat rewrite map_app. repeat rewrite concat_app.
      repeat (rewrite <- app_assoc; rewrite Permutation_swap).
      rewrite Permutation_swap. apply Permutation_app_head.
      etransitivity. 2: eauto.
      rewrite Permutation_swap. apply Permutation_app_head.
      assumption.
  Qed.

  Corollary normalize_rhss_vars_perm : forall es keep_fby es' eqs' st st',
      Forall wl_exp es ->
      normalize_rhss keep_fby es st = ((es', eqs'), st') ->
      Permutation ((vars_defined eqs')++(st_ids st)) (st_ids st').
  Proof.
    intros es keep_fby es' eqs' st st' Hf Hnorm.
    unfold normalize_rhss in Hnorm.
    repeat inv_bind.
    eapply map_bind2_vars_perm in H; eauto.
    repeat rewrite_Forall_forall.
    eapply normalize_rhs_vars_perm; eauto.
  Qed.

  Fact split_equation_vars_defined : forall xs es,
      length xs = length (annots es) ->
      vars_defined (split_equation (xs, es)) = vars_defined [(xs, es)].
  Proof.
    intros xs es; revert xs.
    induction es; intros xs Hwt; inv Hwt; simpl in *.
    - destruct xs; simpl in *; congruence.
    - specialize (IHes (skipn (numstreams a) xs)).
      rewrite IHes.
      + repeat rewrite app_nil_r. apply firstn_skipn.
      + rewrite app_length in H0.
        rewrite length_annot_numstreams in H0.
        rewrite skipn_length. omega.
  Qed.

  Corollary split_equations_vars_defined : forall eqs,
      Forall (fun '(xs, es) => length xs = length (annots es)) eqs ->
      vars_defined (flat_map split_equation eqs) = vars_defined eqs.
  Proof.
    induction eqs; intro Hf; simpl in *; inv Hf.
    - reflexivity.
    - destruct a as [xs es]; simpl in H1.
      specialize (split_equation_vars_defined _ _ H1) as Heq.
      unfold vars_defined in *; repeat rewrite flat_map_concat_map in *.
      rewrite map_app. rewrite concat_app.
      f_equal; simpl in *; auto.
      rewrite app_nil_r in Heq. assumption.
  Qed.

  Fact normalize_equation_vars_perm : forall eq to_cut eqs' st st',
      wl_equation eq ->
      normalize_equation to_cut eq st = (eqs', st') ->
      Permutation ((vars_defined eqs')++(st_ids st)) ((vars_defined [eq])++(st_ids st')).
  Proof.
    intros eq to_cut eqs' st st' Hwt Hnorm.
    destruct eq; simpl in *.
    repeat inv_bind. destruct Hwt as [Hwt Hl].
    specialize (normalize_rhss_vars_perm _ _ _ _ _ _ Hwt H) as Hperm1.
    rewrite app_nil_r.
    assert (vars_defined (flat_map split_equation [(l, x)]) = vars_defined [(l, x)]) as Hxl.
    { apply split_equations_vars_defined.
      repeat constructor.
      eapply normalize_rhss_annots in H; eauto.
      unfold without_names in H. rewrite Hl.
      erewrite <- map_length. setoid_rewrite <- H. apply map_length. }
    unfold vars_defined in *; repeat rewrite flat_map_concat_map in *.
    repeat rewrite map_app; repeat rewrite concat_app.
    repeat rewrite <- app_assoc.
    simpl in Hxl. repeat rewrite app_nil_r in Hxl.
    apply Permutation_app; auto.
    rewrite <- Hxl at 2. reflexivity.
  Qed.

  Corollary normalize_equations_vars_perm : forall eqs to_cut eqs' st st',
      Forall wl_equation eqs ->
      normalize_equations to_cut eqs st = (eqs', st') ->
      Permutation ((vars_defined eqs')++(st_ids st)) ((vars_defined eqs)++(st_ids st')).
  Proof.
    induction eqs; intros to_cut eqs' st st' Hf Hnorm; simpl in *; repeat inv_bind.
    - reflexivity.
    - inv Hf. eapply IHeqs in H0; eauto.
      eapply normalize_equation_vars_perm in H; eauto; simpl in *.
      unfold vars_defined in *; rewrite flat_map_concat_map in *.
      rewrite app_nil_r in *.
      repeat rewrite map_app in *. repeat rewrite concat_app in *.
      rewrite Permutation_app_comm. rewrite Permutation_swap.
      etransitivity.
      + rewrite app_assoc. eapply Permutation_app; eauto.
      + repeat rewrite <- app_assoc. apply Permutation_app_head.
        rewrite Permutation_app_comm. assumption.
  Qed.

  (** Additional properties *)

  Fact init_var_for_clock_In : forall cl id eqs' st st',
      init_var_for_clock cl st = (id, eqs', st') ->
      In (id, (Op.bool_type, (fst cl), true)) (st_anns st').
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

  (** Normalization of a full node *)

  Definition normalize_equations' (to_cut : PS.t) (eq : list equation) (st : fresh_st ((type * clock) * bool)) :
    { res | normalize_equations to_cut eq st = res }.
  Proof.
    remember (normalize_equations to_cut eq st) as eqs'.
    econstructor; eauto.
  Defined.

  Program Definition normalize_node (to_cut : PS.t) (n : node) (Hwl : wl_node n) : node :=
    let id0 := first_unused_ident n in
    let eqs := normalize_equations' (PS.union to_cut (ps_from_list (map fst (n_out n)))) (n_eqs n) (init_st id0) in
    let nvars := (idty (st_anns (snd (proj1_sig eqs)))) in
    {| n_name := (n_name n);
       n_hasstate := (n_hasstate n);
       n_in := (n_in n);
       n_out := (n_out n);
       n_vars := (n_vars n)++nvars;
       n_eqs := fst (proj1_sig eqs);
       n_ingt0 := (n_ingt0 n);
       n_outgt0 := (n_outgt0 n);
    |}.
  Next Obligation.
    eapply normalize_equations_vars_perm with (st:=init_st (first_unused_ident n)) in Hwl. 2: eapply surjective_pairing.
    specialize (n_defd n) as Hperm'.
    unfold idty in *; repeat rewrite map_app in *; rewrite map_map; simpl in *.
    unfold st_ids in Hwl. rewrite init_st_anns in Hwl. rewrite app_nil_r in Hwl.
    etransitivity. apply Hwl.
    rewrite Permutation_app_comm. symmetry.
    rewrite <- app_assoc. rewrite Permutation_swap.
    eapply Permutation_app_head. symmetry. assumption.
  Qed.
  Next Obligation.
    remember (normalize_equations _ (n_eqs n) (init_st (first_unused_ident n))) as res.
    assert (fresh_st_follows (init_st (first_unused_ident n)) (snd res)) as Hfollows.
    { subst. eapply normalize_equations_st_follows. eapply surjective_pairing. }
    assert (fresh_st_valid (snd res)) as Hvalid.
    { subst. eapply normalize_equations_st_valid.
      eapply surjective_pairing.
      eapply init_st_valid. }
    destruct res as [eqs st']. simpl in *.
    apply init_st_follows in Hfollows.
    apply st_valid_NoDupMembers in Hvalid.
    specialize (n_nodup n) as Hndup.
    specialize (first_unused_ident_gt n _ eq_refl) as Hfirst; unfold used_idents in *.
    rewrite Forall_forall in Hfirst. repeat rewrite map_app in Hfirst.
    rewrite fst_NoDupMembers in *.
    unfold idty in *; repeat rewrite map_app in *; rewrite map_map; simpl.
    rewrite NoDup_swap. rewrite <- app_assoc. rewrite NoDup_swap.
    apply NoDup_app'; auto.
    - rewrite <- fst_NoDupMembers. assumption.
    - rewrite NoDup_swap. assumption.
    - rewrite Forall_forall. intros x Hin.
      intro contra.
      assert (Pos.lt x (first_unused_ident n)).
      + eapply Hfirst.
        repeat (apply in_app_or in contra; destruct contra as [?|contra]);
          repeat (apply in_or_app; auto; try (left; assumption); right).
      + clear Hfirst.
        rewrite Forall_forall in Hfollows. specialize (Hfollows x Hin).
        apply (Pos.lt_irrefl x).
        eapply Pos.lt_le_trans; eauto.
  Qed.
  Admit Obligations.

  Fixpoint normalize_global (G : global) (Hwl: wl_global G) : global.
  Proof.
    destruct G as [|hd tl].
    - exact [].
    - refine ((normalize_node PS.empty hd _)::(normalize_global tl _)).
      + inv Hwl; auto.
      + inv Hwl; auto.
  Defined.
End NORMALIZATION.

Module NormalizationFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Syn : LSYNTAX Ids Op)
       <: NORMALIZATION Ids Op OpAux Syn.
  Include NORMALIZATION Ids Op OpAux Syn.
End NormalizationFun.
