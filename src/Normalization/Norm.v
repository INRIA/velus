From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Velus Require Import Common Operators Ident.
From Velus Require Import Lustre.LSyntax Lustre.LTyping.
From Velus Require Import Normalization.Fresh.

(** * Normalization procedure *)

Module Type NORM
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (Import Syn : LSYNTAX Ids Op).

  (** All the indents currently used in the node *)
  Definition used_idents (n : node) : list ident :=
    reserved ++ map fst (n_in n ++ n_vars n ++ n_out n).

  Definition first_unused_ident (n : node) : ident :=
    Pos.succ (fold_left Pos.max (used_idents n) xH).

  (** Some facts about getting the first unused ident *)

  Fact first_unused_ident_gt : forall n id,
      first_unused_ident n = id ->
      Forall (fun id' => (id' < id)%positive) (used_idents n).
  Proof.
    intros n id Hfirst.
    subst. unfold first_unused_ident.
    rewrite Forall_forall; intros x Hin.
    rewrite Pos.lt_succ_r.
    apply max_fold_in; auto.
  Qed.

  (** Fresh ident generation keeping type annotations;
      also retaining if the var is an init var or not *)
  Definition FreshAnn A := Fresh A (ann * bool).

  Local Open Scope fresh_monad_scope.

  Definition hd_default (l : list exp) : exp :=
    hd (Econst (init_type bool_type)) l.

  Fixpoint idents_for_anns (anns : list ann) : FreshAnn (list (ident * ann)) :=
    match anns with
    | [] => ret []
    | hd::tl => do x <- fresh_ident (hd, false);
              do xs <- idents_for_anns tl;
              ret ((x, hd)::xs)
    end.

  Fact idents_for_anns_st_valid : forall anns res st st',
      idents_for_anns anns st = (res, st') ->
      fresh_st_valid st ->
      fresh_st_valid st'.
  Proof.
    induction anns; intros res st st' Hidforanns Hvalid;
      simpl in *; repeat inv_bind.
    - assumption.
    - eapply IHanns; eauto.
      eapply fresh_ident_st_valid; eauto.
  Qed.

  Fact idents_for_anns_st_follows : forall anns res st st',
      idents_for_anns anns st = (res, st') ->
      fresh_st_follows st st'.
  Proof.
    induction anns; intros res st st' Hidforanns;
      simpl in *; repeat inv_bind.
    - reflexivity.
    - etransitivity.
      + eapply fresh_ident_st_follows; eauto.
      + eauto.
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
    fun '(n, l) => match (find (fun '(_, ((_, cl'), isinit)) => isinit && (cl ==b cl'))) l with
                | Some (x, _) => ((x, []), (n, l))
                | None => ((n, [([n], [Efby [add_whens (Econst true_const) bool_type (fst cl)]
                                           [add_whens (Econst false_const) bool_type (fst cl)] [(bool_type, cl)]])]),
                          (Pos.succ n, (n, ((bool_type, cl), true))::l))
                end.

  Fact init_var_for_clock_st_valid : forall cl res st st',
      init_var_for_clock cl st = (res, st') ->
      fresh_st_valid st ->
      fresh_st_valid st'.
  Proof.
    intros cl res [n l] st' Hinit Hvalid.
    unfold init_var_for_clock in Hinit.
    destruct (find (fun '(_, (_, cl', isinit)) => isinit && (cl ==b cl')) l).
    - destruct p. inv Hinit. assumption.
    - inv Hinit. destruct Hvalid as [Hlt Hndup].
      constructor.
      + constructor.
        * apply Pos.lt_succ_diag_r.
        * eapply Forall_impl; eauto.
          intros [x _] Hlt'. apply Pos.lt_lt_succ; auto.
      + constructor; auto.
        intro contra.
        induction l; inv Hlt; inv Hndup; simpl in *; auto.
        destruct contra; subst; auto.
        apply Pos.lt_irrefl in H1; auto.
  Qed.

  Fact init_var_for_clock_st_follows : forall cl res st st',
      init_var_for_clock cl st = (res, st') ->
      fresh_st_follows st st'.
  Proof.
    intros cl res [n l] [n' l'] Hinit.
    unfold init_var_for_clock in Hinit.
    destruct (find (fun '(_, (_, cl', isinit)) => isinit && (cl ==b cl')) l).
    - destruct p. inv Hinit. reflexivity.
    - inv Hinit.
      unfold fresh_st_follows, smallest_ident in *; simpl in *.
      induction l as [|[a ?]]; simpl in *.
      + rewrite Pos.min_glb_iff.
        split.
        * reflexivity.
        * apply Pos.lt_le_incl.
          apply Pos.lt_succ_diag_r.
      + rewrite Pos.min_glb_iff in *.
        destruct IHl as [IHl1 IHl2].
        split.
        * etransitivity; eauto.
          eapply Pos.le_min_r.
        * eapply Pos.min_le_compat_l; eauto.
  Qed.

  (** Generate a if-then-else equation for (0 fby e), and return an expression using it *)
  Definition fby_iteexp (e0 : exp) (e : exp) (ann : ann) : FreshAnn (exp * list equation) :=
    let '(ty, cl) := ann in
    match e0 with
    | Econst c => ret (Efby [e0] [e] [ann], [])
    | _ => do (initid, eqs) <- init_var_for_clock cl;
          do px <- fresh_ident (ann, false);
          ret (Eite (Evar initid (bool_type, cl)) [e0] [Evar px ann] ([ty], cl),
               ([px], [Efby [Econst (init_type ty)] [e] [ann]])::eqs)
    end.

  Lemma fby_iteexp_spec : forall e0 e ty cl,
      (exists c, e0 = Econst c /\ fby_iteexp e0 e (ty, cl) = ret (Efby [e0] [e] [(ty, cl)], []))
      \/ fby_iteexp e0 e (ty, cl) = do (initid, eqs) <- init_var_for_clock cl;
                                   do px <- fresh_ident ((ty, cl), false);
                                   ret (Eite (Evar initid (bool_type, cl)) [e0] [Evar px (ty, cl)] ([ty], cl),
                                        ([px], [Efby [Econst (init_type ty)] [e] [(ty, cl)]])::eqs).
  Proof. destruct e0; eauto. Qed.

  (** Normalize a `fby inits es anns` expression, with inits and es already normalized *)
  Definition normalize_fby (inits : list exp) (es : list exp) (anns : list ann) : FreshAnn (list exp * list equation) :=
    do (es, eqs) <- map_bind2 (fun '((init, e), ann) => fby_iteexp init e ann) (combine (combine inits es) anns);
    ret (es, concat eqs).

  Fact normalize_fby_st_valid : forall inits es anns res st st',
      normalize_fby inits es anns st = (res, st') ->
      fresh_st_valid st ->
      fresh_st_valid st'.
  Proof.
    intros inits es anns res st st' Hnorm Hfresh.
    unfold normalize_fby in Hnorm.
    repeat inv_bind.
    eapply map_bind2_st_valid; eauto.
    apply Forall_forall.
    intros [[i e] [ty cl]] HIn e' eq' st1 st1' Hfby Hst1.
    destruct (fby_iteexp_spec i e ty cl) as [[c [Hite1 Hite2]]|Hite]; subst.
    - rewrite Hite2 in Hfby; clear Hite2.
      inv Hfby. auto.
    - rewrite Hite in Hfby; clear Hite.
      repeat inv_bind.
      apply init_var_for_clock_st_valid in H0; auto.
      apply fresh_ident_st_valid in H1; auto.
  Qed.

  Fact normalize_fby_st_follows : forall inits es anns res st st',
      normalize_fby inits es anns st = (res, st') ->
      fresh_st_follows st st'.
  Proof.
    intros inits es anns res st st' Hnorm.
    unfold normalize_fby in Hnorm; repeat inv_bind.
    eapply map_bind2_st_follows; eauto.
    apply Forall_forall.
    intros [[i e] [ty cl]] HIn e' eq' st1 st1' Hfby.
    destruct (fby_iteexp_spec i e ty cl) as [[c [Hite1 Hite2]]|Hite]; subst.
    - rewrite Hite2 in Hfby; clear Hite2.
      inv Hfby. reflexivity.
    - rewrite Hite in Hfby; clear Hite.
      repeat inv_bind.
      apply init_var_for_clock_st_follows in H0; auto.
      apply fresh_ident_st_follows in H1; auto.
      etransitivity; eauto.
  Qed.

  Definition normalize_reset (e : exp) : FreshAnn (exp * list equation) :=
    match e with
    | Evar v ann => ret (Evar v ann, [])
    | e => let ann := hd (bool_type, (Cbase, None)) (annot e) in
          do x <- fresh_ident (ann, false);
          ret (Evar x ann, ([x], [e])::[])
    end.

  Lemma normalize_reset_spec : forall e,
      (exists v, exists ann, e = Evar v ann /\ normalize_reset e = ret (Evar v ann, []))
      \/ normalize_reset e = let ann := hd (bool_type, (Cbase, None)) (annot e) in
                            do x <- fresh_ident (ann, false);
                            ret (Evar x ann, ([x], [e])::[]).
  Proof. destruct e; eauto. Qed.

  Fact normalize_reset_st_valid : forall e res st st',
      normalize_reset e st = (res, st') ->
      fresh_st_valid st ->
      fresh_st_valid st'.
  Proof.
    intros e res st st' Hnorm Hvalid.
    destruct (normalize_reset_spec e) as [[v [ann [He Hnorm']]]|Hnorm']; subst;
      rewrite Hnorm' in Hnorm; clear Hnorm';
        simpl in *; repeat inv_bind.
    - assumption.
    - eapply fresh_ident_st_valid; eauto.
  Qed.

  Fact normalize_reset_st_follows : forall e res st st',
      normalize_reset e st = (res, st') ->
      fresh_st_follows st st'.
  Proof.
    intros e res st st' Hnorm.
    destruct (normalize_reset_spec e) as [[v [ann [He Hnorm']]]|Hnorm']; subst;
      simpl in *; repeat inv_bind.
    - reflexivity.
    - rewrite Hnorm' in Hnorm; clear Hnorm'.
      repeat inv_bind. eapply fresh_ident_st_follows; eauto.
  Qed.

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

  Local Ltac solve_forall :=
    match goal with
    | H: Forall ?P1 ?l |- Forall ?P2 ?l =>
      eapply Forall_impl; eauto; intros; eauto
    | _ => idtac
    end.

  Local Ltac solve_st_valid :=
    match goal with
    | H : map_bind2 _ _ _ = (_, _, ?st) |- fresh_st_valid ?st =>
      eapply map_bind2_st_valid; eauto; solve_forall
    | H : normalize_fby _ _ _ _ = (_, _, ?st) |- fresh_st_valid ?st =>
      eapply normalize_fby_st_valid; eauto
    | H : idents_for_anns _ _ = (_, ?st) |- fresh_st_valid ?st =>
      eapply idents_for_anns_st_valid; eauto
    end.

  Fact normalize_st_valid : forall e is_control res st st',
      normalize_exp is_control e st = (res, st') ->
      fresh_st_valid st ->
      fresh_st_valid st'.
  Proof.
    induction e using exp_ind2; intros is_control res st st' Hnorm Hvalid;
      simpl in Hnorm.
    - (* const *)
      inv_bind; auto.
    - (* var *)
      inv_bind; auto.
    - (* unop *)
      repeat inv_bind; eauto.
    - (* binop *)
      repeat inv_bind; destruct x1; eauto.
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
        destruct ro; repeat inv_bind; eauto;
          eapply normalize_reset_st_valid; eauto.
  Qed.

  Local Ltac solve_st_follows :=
    match goal with
    | H : map_bind2 _ _ ?st = _ |- fresh_st_follows ?st _ =>
      etransitivity; [ eapply map_bind2_st_follows; eauto; solve_forall | ]
    | H : normalize_fby _ _ _ ?st = _ |- fresh_st_follows ?st _ =>
      etransitivity; [ eapply normalize_fby_st_follows; eauto | ]
    | H : normalize_reset _ ?st = _ |- fresh_st_follows ?st _ =>
      etransitivity; [ eapply normalize_reset_st_follows; eauto | ]
    | H : idents_for_anns _ ?st = _ |- fresh_st_follows ?st _ =>
      etransitivity; [ eapply idents_for_anns_st_follows; eauto | ]
    | |- fresh_st_follows ?st ?st =>
      reflexivity
    end.

  Fact normalize_st_follows: forall e is_control res st st',
      normalize_exp is_control e st = (res, st') ->
      fresh_st_follows st st'.
  Proof.
    intros e.
    induction e using exp_ind2; intros is_control res st st' Hnorm;
      simpl in Hnorm.
    - (* const *)
      inv_bind; reflexivity.
    - (* var *)
      inv_bind; reflexivity.
    - (* unop *)
      repeat inv_bind; eauto.
    - (* binop *)
      repeat inv_bind; etransitivity; eauto.
    - (* fby *)
      repeat inv_bind; repeat solve_st_follows.
    - (* when *)
      destruct a.
      repeat inv_bind; repeat solve_st_follows.
    - (* merge *)
      destruct a.
      destruct is_control; repeat inv_bind; repeat solve_st_follows.
    - (* ite *)
      destruct a.
      destruct is_control; repeat inv_bind;
        (etransitivity; [ eapply IHe; eauto | repeat solve_st_follows ]).
    - (* app *)
      destruct ro; repeat inv_bind; repeat solve_st_follows;
        (etransitivity; [ eapply H; eauto | repeat solve_st_follows ]).
  Qed.

  Definition normalize_top (e : exp) : FreshAnn (list exp * list equation) :=
    match e with
    | Efby inits es anns =>
      do (inits', eqs1) <- normalize_exps inits;
      do (es', eqs2) <- normalize_exps es;
      do (fbys, eqs3) <- normalize_fby inits' es' anns;
      ret (fbys, eqs1++eqs2++eqs3)
    | Eapp f es r anns =>
      do (r', eqs1) <- match r with
                      | Some er => do (er, eqs1) <- normalize_exp false er;
                                  do (er', eqs2) <- normalize_reset (hd_default er);
                                  ret (Some er', eqs1++eqs2)
                      | None => ret (None, [])
                      end;
      do (es', eqs2) <- normalize_exps es;
      ret ([Eapp f es' r' anns], eqs1++eqs2)
    | _ => normalize_exp true e
    end.
  Definition normalize_tops (es : list exp) :=
    do (es, eqs) <- map_bind2 normalize_top es; ret (concat es, concat eqs).

  Fact normalize_top_st_valid : forall e res st st',
      normalize_top e st = (res, st') ->
      fresh_st_valid st ->
      fresh_st_valid st'.
  Proof.
    intros e res st st' Hnorm Hfresh.
    destruct e; try (solve [eapply normalize_st_valid; eauto]);
      simpl in Hnorm; unfold normalize_exps in *; repeat inv_bind.
    - (* fby *)
      repeat solve_st_valid;
        eapply Forall_forall; intros; eapply normalize_st_valid; eauto.
    - (* app *)
      repeat solve_st_valid.
      + eapply Forall_forall; intros; eapply normalize_st_valid; eauto.
      + destruct o; repeat inv_bind; eauto.
        eapply normalize_reset_st_valid; eauto.
        eapply normalize_st_valid; eauto.
  Qed.

  Fact normalize_top_st_follows : forall e res st st',
      normalize_top e st = (res, st') ->
      fresh_st_follows st st'.
  Proof.
    intros e res st st' Hnorm.
    destruct e; try (solve [eapply normalize_st_follows; eauto]);
      simpl in Hnorm; unfold normalize_exps in *; repeat inv_bind.
    - (* fby *)
      repeat solve_st_follows;
        eapply Forall_forall; intros; eapply normalize_st_follows; eauto.
    - (* app *)
      destruct o; repeat inv_bind.
      + etransitivity. eapply normalize_st_follows; eauto. repeat solve_st_follows.
        eapply Forall_forall; intros; eapply normalize_st_follows; eauto.
      + repeat solve_st_follows.
        eapply Forall_forall; intros; eapply normalize_st_follows; eauto.
  Qed.

  Definition split_equation (eq : equation) : list equation :=
    let (xs, es) := eq in
    match es with
    | [e] => [eq]
    | es => map (fun '(x, e) => ([x], [e])) (combine xs es)
    end.

  Definition normalize_equation (e : equation) : FreshAnn (list equation) :=
    let '(xs, es) := e in
    do (es', eqs) <- normalize_tops es;
    ret (flat_map split_equation ((xs, es')::eqs)).

  Fact normalize_equation_st_valid : forall e res st st',
      normalize_equation e st = (res, st') ->
      fresh_st_valid st ->
      fresh_st_valid st'.
  Proof.
    intros [xs es] res st st' Hnorm Hvalid.
    simpl in *; unfold normalize_tops in *; repeat inv_bind.
    eapply map_bind2_st_valid; eauto.
    apply Forall_forall. intros.
    eapply normalize_top_st_valid; eauto.
  Qed.

  Fact normalize_equation_st_follows : forall e res st st',
      normalize_equation e st = (res, st') ->
      fresh_st_follows st st'.
  Proof.
    intros [xs es] res st st' Hnorm.
    simpl in *; unfold normalize_tops in *; repeat inv_bind.
    eapply map_bind2_st_follows; eauto.
    apply Forall_forall. intros.
    eapply normalize_top_st_follows; eauto.
  Qed.

  Fixpoint normalize_equations (eqs : list equation) : FreshAnn (list equation) :=
    match eqs with
    | [] => ret []
    | hd::tl => do eqs1 <- normalize_equation hd;
              do eqs2 <- normalize_equations tl;
              ret (eqs1++eqs2)
    end.

  Fact normalize_equations_st_valid : forall eqs res st st',
      normalize_equations eqs st = (res, st') ->
      fresh_st_valid st ->
      fresh_st_valid st'.
  Proof.
    induction eqs; intros res st st' Hnorm Hvalid;
      simpl in *; repeat inv_bind.
    - assumption.
    - eapply IHeqs; eauto.
      eapply normalize_equation_st_valid; eauto.
  Qed.

  Fact normalize_equations_st_follows : forall eqs res st st',
      normalize_equations eqs st = (res, st') ->
      fresh_st_follows st st'.
  Proof.
    induction eqs; intros res st st' Hnorm;
      simpl in *; repeat inv_bind.
    - reflexivity.
    - etransitivity.
      + eapply normalize_equation_st_follows; eauto.
      + eauto.
  Qed.

  (** Normalization of a full node *)
  Program Definition normalize_node (n : node) : node :=
    let id0 := first_unused_ident n in
    let '(eqs, (_, nvars)) := (normalize_equations (n_eqs n)) (id0, nil) in
    let nvars := (List.map (fun var => (fst var, (fst (fst (snd var)), (fst (snd (fst (snd var))))))) nvars) in
    {| n_name := (n_name n);
       n_hasstate := (n_hasstate n);
       n_in := (n_in n);
       n_out := (n_out n);
       n_vars := (n_vars n)++nvars;
       n_eqs := eqs;
       n_ingt0 := (n_ingt0 n);
       n_outgt0 := (n_outgt0 n);
    |}.
  Next Obligation.
  Admitted.
  Next Obligation.
    symmetry in Heq_anonymous.
    specialize (normalize_equations_st_valid _ _ _ _ Heq_anonymous) as Hvalid.
    specialize (normalize_equations_st_follows _ _ _ _ Heq_anonymous) as Hfollows.
    clear Heq_anonymous.
    unfold fresh_st_follows in Hfollows; simpl in *.
    assert (fresh_st_valid (wildcard', nvars0)) as Hvalid' by (apply Hvalid; repeat constructor); clear Hvalid.
    destruct Hvalid' as [Hvalid1 Hvalid2].
    specialize (n_nodup n) as Hndup.
    specialize (first_unused_ident_gt n _ eq_refl) as Hfirst; unfold used_idents in *.
    rewrite Forall_forall in Hfirst. repeat rewrite map_app in Hfirst.
    repeat apply NoDupMembers_app.
    - eapply NoDupMembers_app_l. eapply NoDupMembers_app_l.
      rewrite <- app_assoc. eassumption.
    - eapply NoDupMembers_app_l. eapply NoDupMembers_app_r.
      eassumption.
    - clear Hfollows Hvalid1.
      rewrite fst_NoDupMembers in *. rewrite map_map.
      induction Hvalid2; simpl in *; constructor; auto.
      rewrite fst_InMembers in H. assumption.
    - clear Hvalid1 Hvalid2 Hndup.
      intros x Hin. specialize (Hfirst x); repeat rewrite in_app_iff in Hfirst.
      rewrite fst_InMembers in *; rewrite map_map; simpl in *.
      assert (Pos.lt x (first_unused_ident n)) as Hfirst' by auto; clear Hfirst.
      intro contra.
      apply (min_fold_in _ _ wildcard') in contra.
      refine (Pos.lt_irrefl x _).
      eapply Pos.lt_le_trans; eauto. etransitivity; eauto.
    - eapply NoDupMembers_app_r. eapply NoDupMembers_app_r.
      eassumption.
    - clear Hvalid1 Hvalid2.
      intros x Hin. specialize (Hfirst x).
      rewrite fst_InMembers in *; rewrite map_app in *; repeat rewrite in_app_iff in *.
      rewrite map_map in *; simpl in *.
      intro contra.
      assert (Pos.lt x (first_unused_ident n)) as Hfirst' by auto; clear Hfirst.
      destruct Hin.
      + rewrite fst_NoDupMembers in Hndup.
        repeat rewrite map_app in Hndup; rewrite app_assoc in Hndup.
        refine (NoDup_app_In _ _ _ _ _ contra); eauto.
        apply in_or_app; auto.
      + apply (min_fold_in _ _ wildcard') in H.
        refine (Pos.lt_irrefl x _).
        eapply Pos.lt_le_trans; eauto. etransitivity; eauto.
    - clear Hvalid1 Hvalid2.
      intros x Hin. specialize (Hfirst x).
      rewrite fst_InMembers in *; repeat rewrite map_app in *. repeat rewrite in_app_iff in *.
      rewrite map_map in *; simpl in *.
      intro contra.
      assert (Pos.lt x (first_unused_ident n)) as Hfirst' by auto; clear Hfirst.
      repeat destruct contra as [contra|contra].
      + rewrite fst_NoDupMembers in Hndup.
        repeat rewrite map_app in Hndup.
        refine (NoDup_app_In _ _ _ _ _ _); eauto.
        apply in_or_app; auto.
      + apply (min_fold_in _ _ wildcard') in contra.
        refine (Pos.lt_irrefl x _).
        eapply Pos.lt_le_trans; eauto. etransitivity; eauto.
      + rewrite fst_NoDupMembers in Hndup.
        repeat rewrite map_app in Hndup.
        refine (NoDup_app_In _ _ _ _ _ _); eauto.
        apply in_or_app; auto.
  Qed.
  Next Obligation.
  Admitted.

  Definition normalize_global (G : global) : global :=
    List.map normalize_node G.
End NORM.

Module NormFun
       (Ids : IDS)
       (Op : OPERATORS)
       (Syn : LSYNTAX Ids Op) <: NORM Ids Op Syn.
  Include NORM Ids Op Syn.
End NormFun.
