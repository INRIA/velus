From Coq Require Import List Sorting.Permutation.
Import List.ListNotations.
Open Scope list_scope.
Require Import Omega.

From Velus Require Import Common Ident Environment.
From Velus Require Import Operators.
From Velus Require Import Lustre.LSyntax.
From Velus Require Lustre.Normalization.Fresh.

(** * Normalization procedure *)

Local Set Warnings "-masking-absolute-name".
Module Type UNTUPLE
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Import Syn : LSYNTAX Ids Op).

  Import Fresh Fresh.Fresh Notations Facts Tactics.
  Local Open Scope fresh_monad_scope.

  (** Fresh ident generation keeping type annotations *)
  Definition FreshAnn A := Fresh A (type * clock).

  Definition hd_default (l : list exp) : exp :=
    hd (Econst (init_type bool_type)) l.

  Fixpoint idents_for_anns (anns : list ann) : FreshAnn (list (ident * ann)) :=
    match anns with
    | [] => ret []
    | (ty, (cl, name))::tl => do x <- fresh_ident (ty, cl);
                            do xs <- idents_for_anns tl;
                            ret ((x, (ty, (cl, name)))::xs)
    end.

  Fact idents_for_anns_values: forall anns ids st st',
      idents_for_anns anns st = (ids, st') ->
      map snd ids = anns.
  Proof.
    induction anns; intros idents st st' Hanns; repeat inv_bind; auto.
    destruct a as [ty [cl ?]]. repeat inv_bind.
    specialize (IHanns _ _ _ H0); simpl.
    f_equal; auto.
  Qed.

  Corollary idents_for_anns_length : forall anns idents st st',
      idents_for_anns anns st = (idents, st') ->
      length idents = length anns.
  Proof.
    intros.
    apply idents_for_anns_values in H.
    rewrite <- H. rewrite map_length; auto.
  Qed.
  Hint Resolve idents_for_anns_length.

  (** Returns the identifiers for a list of annotations,
      while applying clock substitutions *)
  Fixpoint idents_for_anns' (anns : list ann) :=
    match anns with
    | [] => ret []
    | (ty, (ck, None))::tl => do x <- fresh_ident (ty, ck);
                            do xs <- idents_for_anns' tl;
                            ret ((x, (ty, (ck, None)))::xs)
    | (ty, (ck, Some x))::tl => do _ <- reuse_ident x (ty, ck);
                              do xs <- idents_for_anns' tl;
                              ret ((x, (ty, (ck, Some x)))::xs)
    end.

  Fact idents_for_anns'_values: forall anns idents st st',
      idents_for_anns' anns st = (idents, st') ->
      map snd idents = anns.
  Proof.
    induction anns; intros idents st st' Hanns; repeat inv_bind; simpl; auto.
    destruct a as [ty [cl [name|]]]; repeat inv_bind; simpl;
      specialize (IHanns _ _ _ H0);
      f_equal; eauto.
  Qed.

  Corollary idents_for_anns'_length : forall anns ids st st',
      idents_for_anns' anns st = (ids, st') ->
      length ids = length anns.
  Proof.
    intros.
    apply idents_for_anns'_values in H.
    rewrite <- H. rewrite map_length; auto.
  Qed.
  Hint Resolve idents_for_anns'_length.

  Definition normalize_fby (e0s : list exp) (es : list exp) (anns : list ann) :=
    map (fun '((e0, e), a) => Efby [e0] [e] [a]) (combine (combine e0s es) anns).

  Definition normalize_when ckid b es tys ck :=
    map (fun '(e, ty) => Ewhen [e] ckid b ([ty], ck)) (combine es tys).

  Definition normalize_merge ckid ets efs tys ck :=
    map (fun '((e1, e2), ty) => Emerge ckid [e1] [e2] ([ty], ck)) (combine (combine ets efs) tys).

  Definition normalize_ite e ets efs tys ck :=
    map (fun '((et, ef), ty) => Eite e [et] [ef] ([ty], ck)) (combine (combine ets efs) tys).

  Hint Unfold normalize_when normalize_merge normalize_ite.

  Definition normalize_reset (e : exp) : FreshAnn (exp * list equation) :=
    match e with
    | Evar v ann => ret (Evar v ann, [])
    | e => let '(ty, (cl, _)) := hd (bool_type, (Cbase, None)) (annot e) in
          do x <- fresh_ident (ty, cl);
          ret (Evar x (ty, (cl, Some x)), ([x], [e])::[])
    end.

  Lemma normalize_reset_spec : forall e,
      (exists v, exists ann, e = Evar v ann /\ normalize_reset e = ret (Evar v ann, []))
      \/ normalize_reset e = let '(ty, (cl, _)) := hd (bool_type, (Cbase, None)) (annot e) in
                            do x <- fresh_ident (ty, cl);
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
    | Ewhen es ckid b (tys, ck) =>
      do (es', eqs) <- normalize_exps es;
      ret (normalize_when ckid b es' tys ck, eqs)
    | Emerge ckid es1 es2 (tys, cl) =>
      do (es1', eqs1) <- normalize_controls es1;
      do (es2', eqs2) <- normalize_controls es2;
      let merges := normalize_merge ckid es1' es2' tys cl in
      if is_control then
        ret (merges, eqs1++eqs2)
      else
        do xs <- idents_for_anns (List.map (fun ty => (ty, cl)) tys);
        ret (List.map (fun '(id, ann) => Evar id ann) xs,
             (combine (List.map (fun '(id, _) => [id]) xs) (List.map (fun e => [e]) merges))++eqs1++eqs2)
    | Eite e es1 es2 (tys, ck) =>
      do (e', eqs0) <- normalize_exp false e;
      do (es1', eqs1) <- normalize_controls es1;
      do (es2', eqs2) <- normalize_controls es2;
      let ites :=  normalize_ite (hd_default e') es1' es2' tys ck in
      if is_control then
        ret (ites, eqs0++eqs1++eqs2)
      else
        do xs <- idents_for_anns (List.map (fun ty => (ty, ck)) tys);
        ret (List.map (fun '(id, ann) => Evar id ann) xs,
             (combine (List.map (fun '(id, _) => [id]) xs) (List.map (fun e => [e]) ites))++eqs0++eqs1++eqs2)
    | Efby e0s es anns =>
      do (e0s', eqs1) <- normalize_exps e0s;
      do (es', eqs2) <- normalize_exps es;
      let fbys := normalize_fby e0s' es' anns in
      do xs <- idents_for_anns anns;
      ret (List.map (fun '(x, ann) => Evar x ann) xs,
           (List.map (fun '((x, _), fby) => ([x], [fby])) (combine xs fbys))++eqs1++eqs2)
    | Eapp f es r anns =>
      do (es', eqs1) <- normalize_exps es;
      do (r', eqs2) <- match r with
                      | Some er => do (er, eqs1) <- normalize_exp false er;
                                  do (er', eqs2) <- normalize_reset (hd_default er);
                                  ret (Some er', eqs1++eqs2)
                      | None => ret (None, [])
                      end;
      do xs <- idents_for_anns' anns;
      ret (List.map (fun '(id, ann) => Evar id ann) xs,
           (List.map fst xs, [Eapp f es' r' (List.map snd xs)])::eqs1++eqs2)
    end.

  Definition normalize_exps (es : list exp) :=
    do (es, eqs) <- map_bind2 (normalize_exp false) es;
    ret (concat es, concat eqs).

  Definition normalize_rhs (e : exp) : FreshAnn (list exp * list equation) :=
    match e with
    | Eapp f es r anns =>
      do (es', eqs1) <- normalize_exps es;
      do (r', eqs2) <- match r with
                      | Some er => do (er, eqs1) <- normalize_exp false er;
                                  do (er', eqs2) <- normalize_reset (hd_default er);
                                  ret (Some er', eqs1++eqs2)
                      | None => ret (None, [])
                      end;
      ret ([Eapp f es' r' anns], eqs1++eqs2)
    | Efby e0s es anns =>
      do (e0s', eqs1) <- normalize_exps e0s;
      do (es', eqs2) <- normalize_exps es;
      let fbys := normalize_fby e0s' es' anns in
      ret (fbys, eqs1++eqs2)
    | _ => normalize_exp true e
    end.

  Definition normalize_rhss (es : list exp) :=
    do (es, eqs) <- map_bind2 normalize_rhs es; ret (concat es, concat eqs).

  Fixpoint combine_for_numstreams {B} (es : list exp) (vs : list B) :=
    match es with
    | [] => []
    | hd::tl => let n := numstreams hd in
                (hd, (firstn n vs))::(combine_for_numstreams tl (skipn n vs))
    end.

  Definition split_equation (eq : equation) : list equation :=
    let (xs, es) := eq in
    List.map (fun '(e, xs) => (xs, [e])) (combine_for_numstreams es xs).

  Definition untuple_equation (e : equation) : FreshAnn (list equation) :=
    let '(xs, es) := e in
    do (es', eqs) <- normalize_rhss es;
    ret ((split_equation (xs, es'))++eqs).

  Definition untuple_equations (eqs : list equation) : FreshAnn (list equation) :=
    do eqs <- map_bind untuple_equation eqs;
    ret (concat eqs).

  (** ** Some additional tactics *)

  Definition default_ann : ann := (Op.bool_type, (Cbase, None)).

  Ltac simpl_forall :=
    repeat
      match goal with
      (* same *)
      | |- Forall2 _ ?l1 ?l1 => apply Forall2_same
      (* Get rid of maps *)
      | H : Forall _ (map _ _) |- _ => rewrite Forall_map in H
      | H : Forall2 _ (map _ _) _ |- _ => rewrite Forall2_map_1 in H
      | H : Forall2 _ _ (map _ _) |- _ => rewrite Forall2_map_2 in H
      | |- Forall _ (map _ _) => rewrite Forall_map
      | |- Forall2 _ (map _ _) _ => rewrite Forall2_map_1
      | |- Forall2 _ _ (map _ _) => rewrite Forall2_map_2
      (* Get rid of combines *)
      | |- Forall _ (combine _ _) => eapply Forall2_combine'
      | |- Forall2 _ (combine _ _) _ => eapply Forall3_combine'1
      (* Assemble Foralls *)
      | H1 : Forall _ ?l, H2 : Forall _ ?l |- _ =>
        eapply Forall_Forall in H1; [|eapply H2]; clear H2
      | H1 : Forall2 _ ?l1 ?l2, H2 : Forall2 _ ?l1 ?l2 |- _ =>
        eapply Forall2_Forall2 in H1; [|eapply H2]; clear H2
      | H1 : Forall3 _ ?l1 ?l2 ?l3, H2 : Forall3 _ ?l1 ?l2 ?l3 |- _ =>
        eapply Forall3_Forall3 in H1; [|eapply H2]; clear H2
      (* Try to hyp Foralls in the same form as conclusion *)
      | H : Forall _ ?l1 |- Forall2 _ ?l1 ?l2 =>
        eapply Forall2_ignore2' with (ys:=l2) in H; try congruence
      | H : Forall _ ?l2 |- Forall2 _ ?l1 ?l2 =>
        eapply Forall2_ignore1' with (xs:=l1) in H; try congruence
      | H : Forall2 _ ?l2 ?l3 |- Forall3 _ ?l1 ?l2 ?l3 =>
        eapply Forall3_ignore1' with (xs:=l1) in H; try congruence
      | H : Forall2 _ ?l1 ?l3 |- Forall3 _ ?l1 ?l2 ?l3 =>
        eapply Forall3_ignore2' with (ys:=l2) in H; try congruence
      | H : Forall2 _ ?l1 ?l2 |- Forall3 _ ?l1 ?l2 ?l3 =>
        eapply Forall3_ignore3' with (zs:=l3) in H; try congruence
      | H : Forall _ ?l1 |- Forall3 _ ?l1 ?l2 ?l3 =>
        eapply Forall2_ignore2' with (ys:=l2) in H; try congruence
      | H : Forall _ ?l2 |- Forall3 _ ?l1 ?l2 ?l3 =>
        eapply Forall2_ignore1' with (xs:=l1) in H; try congruence
      | H : Forall _ ?l3 |- Forall3 _ ?l1 ?l2 ?l3 =>
        eapply Forall2_ignore1' with (xs:=l1) in H; try congruence
      end; simpl in *; auto.

  Ltac destruct_conjs :=
    repeat
      match goal with
      | H: _ /\ _ |- _ => destruct H
      | x: _ * _ |- _ => destruct x
      end.

  Ltac solve_forall :=
    simpl_forall;
    match goal with
    | H: Forall _ ?l |- Forall _ ?l =>
      eapply Forall_impl_In; [|eapply H]; clear H; intros; simpl in *
    | H: Forall2 _ ?l1 ?l2 |- Forall2 _ ?l1 ?l2 =>
      eapply Forall2_impl_In; [|eapply H]; clear H; intros; simpl in *
    | H: Forall3 _ ?l1 ?l2 ?l3 |- Forall3 _ ?l1 ?l2 ?l3 =>
      eapply Forall3_impl_In; [|eapply H]; clear H; intros; simpl in *
    | |- Forall _ _ =>
      eapply Forall_forall; intros
    | _ => idtac
    end; destruct_conjs; eauto.

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

  (** ** Propagation of the st_valid_after property *)

  Fact idents_for_anns_st_valid_after : forall anns res st st' aft,
      idents_for_anns anns st = (res, st') ->
      st_valid_after st aft ->
      st_valid_after st' aft.
  Proof.
    induction anns; intros res st st' aft Hidforanns Hvalid;
      repeat inv_bind.
    - assumption.
    - destruct a as [ty [cl name]]. repeat inv_bind.
      eapply IHanns; eauto.
  Qed.
  Hint Resolve idents_for_anns_st_valid_after.

  (** ** Propagation of the st_valid_reuse property *)

  Fact idents_for_anns_st_valid_reuse : forall anns res st st' aft reusable,
      idents_for_anns anns st = (res, st') ->
      st_valid_reuse st aft reusable ->
      st_valid_reuse st' aft reusable.
  Proof.
    induction anns; intros res st st' aft reuse Hidforanns Hvalid;
      repeat inv_bind.
    - assumption.
    - destruct a as [ty [cl name]]. repeat inv_bind.
      eapply IHanns; eauto.
  Qed.
  Hint Resolve idents_for_anns_st_valid_reuse.

  Fact idents_for_anns'_st_valid : forall anns res st st' aft reusable,
      NoDup (map fst (anon_streams anns)++PS.elements reusable) -> (* OK because of the n_dup property *)
      idents_for_anns' anns st = (res, st') ->
      st_valid_reuse st aft (ps_adds (map fst (anon_streams anns)) reusable) ->
      st_valid_reuse st' aft reusable.
  Proof with eauto.
    induction anns; intros res st st' aft reusable HND Hidforanns Hvalid;
      repeat inv_bind.
    - assumption.
    - destruct a as [ty [cl [name|]]]; repeat inv_bind; simpl in *;
        eapply IHanns; eauto.
      + inv HND; eauto.
      + inv HND. destruct x.
        eapply reuse_ident_st_valid_reuse in H; eauto.
        * intro contra; apply H3.
          rewrite <- In_PS_elements in contra.
          rewrite Permutation_PS_elements_ps_adds' in contra...
        * rewrite ps_add_adds_eq...
  Qed.
  Hint Resolve idents_for_anns'_st_valid.

  Fact normalize_reset_st_valid : forall e res st st' aft reusable,
      normalize_reset e st = (res, st') ->
      st_valid_reuse st aft reusable ->
      st_valid_reuse st' aft reusable.
  Proof.
    intros e res st st' aft reusable Hnorm Hvalid.
    destruct (normalize_reset_spec e) as [[v [ann [He Hnorm']]]|Hnorm']; subst;
      rewrite Hnorm' in Hnorm; clear Hnorm';
        try (destruct (hd _ _) as [ty [cl _]]);
        repeat inv_bind; eauto.
  Qed.
  Hint Resolve normalize_reset_st_valid.

  Ltac ndup_simpl :=
    repeat rewrite map_app, <- app_assoc in *.
  Ltac ndup_l H :=
    ndup_simpl;
    rewrite Permutation_swap in H;
    apply NoDup_app_r in H; auto.
  Ltac ndup_r H :=
    ndup_simpl;
    apply NoDup_app_r in H; auto.

  Fact map_bind2_st_valid_reuse' {B} :
    forall (k : exp -> list (ident * B)) (f : exp -> FreshAnn (list exp * list equation)) es es' eqs' st st' aft reusable,
      Forall (fun e =>
                forall es' eqs' st st' aft reusable,
                  NoDup (map fst (k e)++PS.elements reusable) ->
                  f e st = (es', eqs', st') ->
                  st_valid_reuse st aft (ps_adds (map fst (k e)) reusable) ->
                  st_valid_reuse st' aft reusable) es ->
      NoDup (map fst (concat (map k es))++PS.elements reusable) ->
      map_bind2 f es st = (es', eqs', st') ->
      st_valid_reuse st aft (ps_adds (map fst (concat (map k es))) reusable) ->
      st_valid_reuse st' aft reusable.
  Proof.
    induction es; intros es' eqs' st st' aft reusable Hf Hnd Hmap Hvalid;
      repeat inv_bind; auto.
    inv Hf.
    ndup_simpl.
    assert (NoDup (map fst (k a)++PS.elements reusable)) by ndup_l Hnd.
    assert (NoDup (map fst (concat (map k es))++PS.elements reusable)) by ndup_r Hnd.
    rewrite ps_adds_app in Hvalid; eauto.
    eapply IHes in H4; eauto. eapply H3; eauto.
    rewrite Permutation_PS_elements_ps_adds'; eauto.
  Qed.

  Local Ltac solve_st_valid :=
    match goal with
    | H : map_bind2 _ _ _ = (_, _, ?st) |- st_valid_reuse ?st _ _ =>
      eapply map_bind2_st_valid_reuse' in H; eauto; solve_forall
    | H : normalize_reset _ _ = (_, _, ?st) |- st_valid_reuse ?st _ _ =>
      eapply normalize_reset_st_valid; eauto
    | H : idents_for_anns _ _ = (_, ?st) |- st_valid_reuse ?st _ _ =>
      eapply idents_for_anns_st_valid_reuse; eauto
    | H : idents_for_anns' _ _ = (_, ?st) |- st_valid_reuse ?st _ _ =>
      eapply idents_for_anns'_st_valid; eauto
    end.

  Fact normalize_exp_st_valid : forall e is_control res st st' aft reusable,
      NoDup (map fst (fresh_in e)++PS.elements reusable) ->
      normalize_exp is_control e st = (res, st') ->
      st_valid_reuse st aft (ps_adds (map fst (fresh_in e)) reusable) ->
      st_valid_reuse st' aft reusable.
  Proof with eauto.
    induction e using exp_ind2; intros is_control res st st' aft reusable Hnd Hnorm Hvalid;
      simpl in *.
    - (* const *)
      repeat inv_bind...
    - (* var *)
      repeat inv_bind...
    - (* unop *)
      repeat inv_bind...
    - (* binop *)
      repeat inv_bind. ndup_simpl.
      assert (NoDup (map fst (fresh_in e1)++PS.elements reusable)) by ndup_l Hnd.
      assert (NoDup (map fst (fresh_in e2)++PS.elements reusable)) by ndup_r Hnd.
      rewrite ps_adds_app in *...
      eapply IHe2... eapply IHe1...
      rewrite Permutation_PS_elements_ps_adds'...
    - (* fby *)
      repeat inv_bind. ndup_simpl.
      assert (NoDup (map fst (fresh_ins e0s)++PS.elements reusable)) by ndup_l Hnd.
      assert (NoDup (map fst (fresh_ins es)++PS.elements reusable)) by ndup_r Hnd.
      rewrite ps_adds_app in Hvalid... repeat solve_st_valid.
      rewrite Permutation_PS_elements_ps_adds'; eauto.
    - (* when *)
      destruct a.
      repeat inv_bind; repeat solve_st_valid.
    - (* merge *)
      destruct a. ndup_simpl.
      assert (NoDup (map fst (fresh_ins ets)++PS.elements reusable)) by ndup_l Hnd.
      assert (NoDup (map fst (fresh_ins efs)++PS.elements reusable)) by ndup_r Hnd.
      destruct is_control; repeat inv_bind;
        try rewrite ps_adds_app in *; repeat solve_st_valid;
          rewrite Permutation_PS_elements_ps_adds'; eauto.
    - (* ite *)
      destruct a. ndup_simpl.
      assert (NoDup (map fst (fresh_in e)++PS.elements reusable)) by (repeat ndup_l Hnd).
      assert (NoDup (map fst (fresh_ins ets)++PS.elements reusable)) by (ndup_r Hnd; ndup_l Hnd).
      assert (NoDup (map fst (fresh_ins efs)++PS.elements reusable)) by (repeat ndup_r Hnd).
      assert (NoDup (map fst (fresh_ins ets)++map fst (fresh_ins efs)++PS.elements reusable)) by ndup_r Hnd.
      destruct is_control; repeat inv_bind;
        repeat rewrite ps_adds_app in Hvalid; repeat solve_st_valid.
      2,4:eapply IHe; eauto.
      1,2,3,4: repeat rewrite Permutation_PS_elements_ps_adds'; eauto.
    - (* app *)
      repeat inv_bind;
        destruct ro; ndup_simpl;
        repeat rewrite ps_adds_app in Hvalid; repeat inv_bind; repeat solve_st_valid...
      2: (eapply H; eauto; repeat solve_st_valid).
      2,3,5: repeat rewrite Permutation_PS_elements_ps_adds'; eauto.
      1,2,3,4,5,6,7,8:repeat ndup_r Hnd.
  Qed.
  Hint Resolve normalize_exp_st_valid.

  Fact normalize_rhs_st_valid : forall e res st st' aft reusable,
      NoDup (map fst (anon_in e)++PS.elements reusable) ->
      normalize_rhs e st = (res, st') ->
      st_valid_reuse st aft (ps_adds (map fst (anon_in e)) reusable) ->
      st_valid_reuse st' aft reusable.
  Proof.
    intros * Hnd Hnorm Hvalid.
    destruct e; try (solve [eapply normalize_exp_st_valid in Hnorm; eauto]);
      simpl in *; unfold normalize_exps in *.
    - (* fby *)
      ndup_simpl.
      repeat inv_bind.
      repeat rewrite ps_adds_app in Hvalid;
        repeat solve_st_valid.
      2: rewrite Permutation_PS_elements_ps_adds'; eauto.
      1,2: ndup_r Hnd.
    - (* app *)
      repeat inv_bind.
      destruct o; repeat inv_bind; ndup_simpl;
        try rewrite ps_adds_app in Hvalid;
        repeat solve_st_valid.
      eapply normalize_exp_st_valid in H0; eauto. 2:solve_st_valid.
      2:rewrite Permutation_PS_elements_ps_adds'; eauto.
      1,2:ndup_r Hnd.
  Qed.
  Hint Resolve normalize_rhs_st_valid.

  Fact untuple_equation_st_valid : forall e res st st' aft reusable,
      NoDup (map fst (anon_in_eq e)++PS.elements reusable) ->
      untuple_equation e st = (res, st') ->
      st_valid_reuse st aft (ps_adds (map fst (anon_in_eq e)) reusable) ->
      st_valid_reuse st' aft reusable.
  Proof.
    intros [xs es] * Hnd Hnorm Hvalid.
    unfold anon_in_eq in Hnd.
    simpl in *; unfold normalize_rhss in *; repeat inv_bind.
    eapply map_bind2_st_valid_reuse' in H; eauto.
    apply Forall_forall. intros; eauto.
  Qed.
  Hint Resolve untuple_equation_st_valid.

  Fact untuple_equations_st_valid : forall eqs res st st' aft reusable,
      NoDup (map fst (anon_in_eqs eqs)++PS.elements reusable) ->
      untuple_equations eqs st = (res, st') ->
      st_valid_reuse st aft (ps_adds (map fst (anon_in_eqs eqs)) reusable) ->
      st_valid_reuse st' aft reusable.
  Proof.
    induction eqs; intros * Hndup Hnorm Hvalid;
      unfold untuple_equations in Hnorm; repeat inv_bind; auto.
    - unfold anon_in_eqs in *; simpl in *.
      ndup_simpl.
      rewrite ps_adds_app in Hvalid.
      eapply IHeqs; eauto. 1:ndup_r Hndup.
      unfold untuple_equations; repeat inv_bind; repeat eexists; eauto; inv_bind; eauto.
      eapply untuple_equation_st_valid; eauto.
      rewrite Permutation_PS_elements_ps_adds'; auto. ndup_r Hndup.
  Qed.

  (** ** Propagation of the st_follows property *)

  Fact idents_for_anns_st_follows : forall anns res st st',
      idents_for_anns anns st = (res, st') ->
      st_follows st st'.
  Proof.
    induction anns; intros res st st' Hidforanns;
      repeat inv_bind.
    - reflexivity.
    - destruct a as [ty [cl name]]. repeat inv_bind.
      etransitivity; eauto.
  Qed.
  Hint Resolve idents_for_anns_st_follows.

  Corollary idents_for_anns_incl : forall anns ids st st',
      idents_for_anns anns st = (ids, st') ->
      incl (List.map (fun '(id, (ty, (cl, _))) => (id, (ty, cl))) ids) (st_anns st').
  Proof.
    induction anns; intros ids st st' Hids; simpl in Hids; repeat inv_bind;
      unfold incl; intros ? Hin; simpl in *; try destruct Hin.
    destruct a as [ty [cl name]]. repeat inv_bind.
    repeat simpl_In. inv H1. inv H2.
    - inv H1.
      apply fresh_ident_In in H.
      apply idents_for_anns_st_follows in H0.
      apply st_follows_incl in H0; auto.
    - apply IHanns in H0.
      apply H0. repeat simpl_In.
      exists (i, (t, (c, o))); auto.
  Qed.

  Corollary idents_for_anns_incl_ids : forall anns ids st st',
      idents_for_anns anns st = (ids, st') ->
      incl (List.map fst ids) (st_ids st').
  Proof.
    intros.
    eapply idents_for_anns_incl in H.
    unfold st_ids, idty in *.
    eapply incl_map with (f:=fst) in H.
    repeat rewrite map_map in H; simpl in H.
    replace (map (fun x => fst (let '(id, (ty, (cl, _))) := x in (id, (ty, cl)))) ids) with (map fst ids) in H.
    2: { eapply map_ext. intros [? [? [? ?]]]; auto. }
    assumption.
  Qed.

  Fact idents_for_anns'_st_follows : forall anns res st st',
      idents_for_anns' anns st = (res, st') ->
      st_follows st st'.
  Proof.
    induction anns; intros res st st' Hidforanns;
      repeat inv_bind.
    - reflexivity.
    - destruct a as [ty [cl [name|]]]; repeat inv_bind;
        [destruct x|]; etransitivity; eauto.
  Qed.
  Hint Resolve idents_for_anns'_st_follows.

  Corollary idents_for_anns'_incl : forall anns ids st st',
      idents_for_anns' anns st = (ids, st') ->
      incl (List.map (fun '(id, (ty, (cl, _))) => (id, (ty, cl))) ids) (st_anns st').
  Proof.
    induction anns; intros ids st st' Hids; simpl in Hids; repeat inv_bind;
      unfold incl; intros ? Hin; simpl in *; try destruct Hin.
    destruct a as [ty [cl [name|]]]; repeat inv_bind; repeat simpl_In; inv H1; inv H2.
    - inv H1. destruct x.
      apply reuse_ident_In in H.
      apply idents_for_anns'_st_follows in H0.
      apply st_follows_incl in H0; auto.
    - apply IHanns in H0.
      apply H0. repeat simpl_In.
      exists (i, (t, (c, o))); auto.
    - inv H1.
      apply fresh_ident_In in H.
      apply idents_for_anns'_st_follows in H0.
      apply st_follows_incl in H0; auto.
    - apply IHanns in H0.
      apply H0. repeat simpl_In.
      exists (i, (t, (c, o))); auto.
  Qed.

  Corollary idents_for_anns'_incl_ids : forall anns ids st st',
      idents_for_anns' anns st = (ids, st') ->
      incl (List.map fst ids) (st_ids st').
  Proof.
    intros.
    eapply idents_for_anns'_incl in H.
    unfold st_ids, idty in *.
    eapply incl_map with (f:=fst) in H.
    repeat rewrite map_map in H; simpl in H.
    replace (map (fun x => fst (let '(id, (ty, (cl, _))) := x in (id, (ty, cl)))) ids) with (map fst ids) in H.
    2: { eapply map_ext. intros [? [? [? ?]]]; auto. }
    assumption.
  Qed.

  Fact normalize_reset_st_follows : forall e res st st',
      normalize_reset e st = (res, st') ->
      st_follows st st'.
  Proof.
    intros e res st st' Hnorm.
    destruct (normalize_reset_spec e) as [[v [ann [He Hnorm']]]|Hnorm']; subst;
      repeat inv_bind.
    - reflexivity.
    - rewrite Hnorm' in Hnorm; clear Hnorm'.
      destruct (hd _ _) as [ty [cl _]].
      repeat inv_bind. eauto.
  Qed.
  Hint Resolve normalize_reset_st_follows.

  Local Ltac solve_st_follows' :=
    match goal with
    | |- st_follows ?st ?st =>
      reflexivity
    | H : st_follows ?st1 ?st2 |- st_follows ?st1 _ =>
      etransitivity; [eapply H |]
    | H : fresh_ident _ ?st = _ |- st_follows ?st _ =>
      etransitivity; [ eapply fresh_ident_st_follows in H; eauto | ]
    | H : reuse_ident _ _ ?st = _ |- st_follows ?st _ =>
      etransitivity; [ eapply reuse_ident_st_follows in H; eauto | ]
    | H : idents_for_anns _ ?st = _ |- st_follows ?st _ =>
      etransitivity; [ eapply idents_for_anns_st_follows in H; eauto | ]
    | H : idents_for_anns' _ ?st = _ |- st_follows ?st _ =>
      etransitivity; [ eapply idents_for_anns'_st_follows in H; eauto | ]
    | H : normalize_reset _ ?st = _ |- st_follows ?st _ =>
      etransitivity; [ eapply normalize_reset_st_follows in H; eauto | ]
    | H : map_bind2 _ _ ?st = _ |- st_follows ?st _ =>
      etransitivity; [ eapply map_bind2_st_follows in H; eauto; solve_forall | ]
    end.

  Fact normalize_exp_st_follows : forall e is_control res st st',
      normalize_exp is_control e st = (res, st') ->
      st_follows st st'.
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
      destruct ro; repeat inv_bind; [eapply H in H2|]; repeat solve_st_follows'.
  Qed.
  Hint Resolve normalize_exp_st_follows.

  Corollary normalize_exps_st_follows : forall es res st st',
      normalize_exps es st = (res, st') ->
      st_follows st st'.
  Proof.
    intros es res st st' Hnorm.
    unfold normalize_exps in Hnorm. repeat inv_bind.
    eapply map_bind2_st_follows; eauto.
    rewrite Forall_forall; intros; eauto.
  Qed.

  Fact normalize_rhs_st_follows : forall e res st st',
      normalize_rhs e st = (res, st') ->
      st_follows st st'.
  Proof.
    intros * Hnorm.
    destruct e; try (solve [eapply normalize_exp_st_follows; eauto]);
      simpl in Hnorm; unfold normalize_exps in *.
    - (* fby *)
      repeat inv_bind;
        repeat solve_st_follows';
        eapply Forall_forall; intros; eauto.
    - (* app *)
      destruct o; repeat inv_bind; [eapply normalize_exp_st_follows in H0|]; repeat solve_st_follows'.
  Qed.
  Hint Resolve normalize_rhs_st_follows.

  Corollary normalize_rhss_st_follows : forall es res st st',
      normalize_rhss es st = (res, st') ->
      st_follows st st'.
  Proof.
    intros * Hnorm.
    unfold normalize_rhss in Hnorm; repeat inv_bind.
    repeat solve_st_follows'.
  Qed.
  Hint Resolve normalize_rhss_st_follows.

  Fact untuple_equation_st_follows : forall e res st st',
      untuple_equation e st = (res, st') ->
      st_follows st st'.
  Proof.
    intros [xs es] * Hnorm.
    simpl in *; repeat inv_bind; eauto.
  Qed.
  Hint Resolve untuple_equation_st_follows.

  Fact untuple_equations_st_follows : forall eqs res st st',
      untuple_equations eqs st = (res, st') ->
      st_follows st st'.
  Proof.
    intros * Hnorm.
    unfold untuple_equations in Hnorm; repeat inv_bind.
    eapply map_bind_st_follows; eauto.
    solve_forall.
  Qed.

  Ltac solve_st_follows :=
    match goal with
    | |- st_follows ?st ?st => reflexivity
    | H : normalize_exp _ _ ?st = _ |- st_follows ?st _ =>
      etransitivity; [ eapply normalize_exp_st_follows in H; eauto |]
    | H : normalize_exps _ ?st = _ |- st_follows ?st _ =>
      etransitivity; [ eapply normalize_exps_st_follows in H; eauto |]
    | H : normalize_rhs _ _ ?st = _ |- st_follows ?st _ =>
      etransitivity; [ eapply normalize_rhs_st_follows in H; eauto |]
    | H : normalize_rhss _ _ ?st = _ |- st_follows ?st _ =>
      etransitivity; [ eapply normalize_rhss_st_follows in H; eauto |]
    | H : untuple_equation _ ?st = _ |- st_follows ?st _ =>
      etransitivity; [ eapply untuple_equation_st_follows in H; eauto |]
    | H: map_bind _ _ ?st = _ |- st_follows ?st _ =>
      etransitivity; [ eapply map_bind_st_follows in H; eauto; solve_forall |]
    | H : untuple_equations _ ?st = _ |- st_follows ?st _ =>
      etransitivity; [ eapply untuple_equations_st_follows in H; eauto |]
    | _ => solve_st_follows'
    end.

  (** ** Some helpful tactics *)

  (** Simplify an expression with maps and other stuff... *)
  Ltac simpl_list :=
    unfold normalize_when, normalize_merge, normalize_ite in *;
    simpl in *;
    match goal with
    (* annots, clocksof and typesof are just plurals *)
    | H : context c [annots ?es] |- _ => unfold annots in H
    | |- context c [annots ?es] => unfold annots
    | H : context c [typesof ?es] |- _ => unfold typesof in H
    | |- context c [typesof ?es] => unfold typesof
    | H : context c [clocksof ?es] |- _ => unfold clocksof in H
    | |- context c [clocksof ?es] => unfold clocksof
    | H : context c [vars_defined ?es] |- _ => unfold vars_defined in H
    | |- context c [vars_defined ?es] => unfold vars_defined
    (* flat_map, map_map, map_app, concat_app *)
    | H: context c [flat_map ?f ?l] |- _ => rewrite flat_map_concat_map in H
    | |- context c [flat_map ?f ?l] => rewrite flat_map_concat_map
    | H: context c [map ?f (map ?g ?l)] |- _ => rewrite map_map in H
    | |- context c [map ?f (map ?g ?l)] => rewrite map_map
    | H: context c [map ?f (app ?l1 ?l2)] |- _ => rewrite map_app in H
    | |- context c [map ?f (app ?l1 ?l2)] => rewrite map_app
    | H: context c [concat (app ?l1 ?l2)] |- _ => rewrite concat_app in H
    | |- context c [concat (app ?l1 ?l2)] => rewrite concat_app
    (* idck_app, idty_app *)
    | H: context c [idty (?l1 ++ ?l2)] |- _ => rewrite idty_app in H
    | H: context c [idck (?l1 ++ ?l2)] |- _ => rewrite idck_app in H
    (* app_nil_r *)
    | H: context c [app ?l nil] |- _ => rewrite app_nil_r in H
    | |- context c [app ?l nil] => rewrite app_nil_r
    (* app_assoc *)
    | H: context c [app (app ?l1 ?l2) ?l3] |- _ => rewrite <- app_assoc in H
    | |- context c [app (app ?l1 ?l2) ?l3] => rewrite <- app_assoc
    end.

  (** ** Length of normalized expression *)

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
    repeat simpl_list.
    apply concat_length_eq.
    rewrite Forall2_map_2, Forall2_swap_args.
    eapply Forall3_ignore3, Forall2_Forall2 in Hmap; [| eapply Hf]. clear Hf.
    eapply Forall2_impl_In; eauto.
    intros ? ? _ _ [H1 [? [? [? H2]]]]. rewrite length_annot_numstreams; eauto.
  Qed.

  Local Hint Resolve nth_In.
  Fact normalize_exp_length : forall G e is_control es' eqs' st st',
      wl_exp G e ->
      normalize_exp is_control e st = (es', eqs', st') ->
      length es' = numstreams e.
  Proof with eauto.
    induction e using exp_ind2; intros is_control es' eqs' st st' Hwl Hnorm;
      simpl in *; inv Hwl; repeat inv_bind; auto.
    - (* fby *)
      simpl in *. rewrite map_length.
      apply idents_for_anns_length in H3...
    - (* when *)
      unfold normalize_when. rewrite map_length.
      eapply map_bind2_length in H0.
      + solve_length.
      + eapply map_bind2_values in H0.
        repeat rewrite_Forall_forall...
    - (* merge *)
      destruct is_control; repeat inv_bind; unfold normalize_merge.
      + apply map_bind2_length in H1; [| eapply map_bind2_values in H1; repeat rewrite_Forall_forall; eauto].
        apply map_bind2_length in H2; [| eapply map_bind2_values in H2; repeat rewrite_Forall_forall; eauto].
        solve_length.
      + apply idents_for_anns_length in H3. solve_length.
    - (* ite *)
      destruct is_control; repeat inv_bind; unfold normalize_ite.
      + apply map_bind2_length in H2; [| eapply map_bind2_values in H2; repeat rewrite_Forall_forall; eauto].
        apply map_bind2_length in H3; [| eapply map_bind2_values in H3; repeat rewrite_Forall_forall; eauto].
        solve_length.
      + apply idents_for_anns_length in H4. solve_length.
    - (* app *)
      apply idents_for_anns'_length in H2.
      solve_length.
    - (* app (reset) *)
      apply idents_for_anns'_length in H3.
      solve_length.
  Qed.
  Hint Resolve normalize_exp_length.

  Corollary map_bind2_normalize_exp_length : forall G is_control es es' eqs' st st',
      Forall (wl_exp G) es ->
      map_bind2 (normalize_exp is_control) es st = (es', eqs', st') ->
      length (concat es') = length (annots es).
  Proof.
    intros G is_control es es' eqs' st st' Hf Hmap.
    eapply map_bind2_length; eauto.
    eapply map_bind2_values in Hmap.
    repeat rewrite_Forall_forall.
    eapply normalize_exp_length; eauto.
  Qed.
  Hint Resolve map_bind2_normalize_exp_length.

  Corollary normalize_exps_length : forall G es es' eqs' st st',
      Forall (wl_exp G) es ->
      normalize_exps es st = (es', eqs', st') ->
      length es' = length (annots es).
  Proof.
    intros G es es' eqs' st st' Hwt Hnorm.
    unfold normalize_exps in Hnorm.
    repeat inv_bind.
    eapply map_bind2_normalize_exp_length; eauto.
  Qed.
  Hint Resolve normalize_exps_length.

  Fact normalize_fby_length : forall e0s es anns,
      length e0s = length anns ->
      length es = length anns ->
      length (normalize_fby e0s es anns) = length anns.
  Proof.
    intros * Hl1 Hl2.
    unfold normalize_fby. solve_length.
  Qed.

  Fact normalize_merge_length : forall ckid ets efs tys nck,
    length ets = length tys ->
    length efs = length tys ->
    length (normalize_merge ckid ets efs tys nck) = length tys.
  Proof.
    intros * Hl1 Hl2.
    unfold normalize_merge. solve_length.
  Qed.

  Fact normalize_ite_length : forall e ets efs tys nck,
    length ets = length tys ->
    length efs = length tys ->
    length (normalize_ite e ets efs tys nck) = length tys.
  Proof.
    intros * Hl1 Hl2.
    unfold normalize_ite. solve_length.
  Qed.

  Fact normalize_rhs_length : forall G e es' eqs' st st',
      wl_exp G e ->
      normalize_rhs e st = (es', eqs', st') ->
      (length es' = 1 \/ length es' = numstreams e).
  Proof.
    intros * Hwt Hnorm;
      destruct e; unfold normalize_rhs in Hnorm;
        try (solve [right; eapply normalize_exp_length; eauto]);
        try (destruct o); repeat inv_bind; auto.
    (* keep_fby = true *)
    right. inv Hwt.
    eapply normalize_fby_length; eauto.
    - eapply normalize_exps_length in H; eauto. congruence.
    - eapply normalize_exps_length in H0; eauto. congruence.
  Qed.
  Hint Resolve normalize_rhs_length.

  Fact normalize_exp_numstreams : forall e is_control es' eqs' st st',
      normalize_exp is_control e st = (es', eqs', st') ->
      Forall (fun e => numstreams e = 1) es'.
  Proof.
    intros e is_control es' eqs' st st' Hnorm.
    induction e; simpl in Hnorm; repeat inv_bind; repeat constructor.
    2: destruct l0.
    3,4: destruct l1.
    3,4: destruct is_control.
    1,2,3,4,5,6,7:(repeat inv_bind; unfold normalize_when, normalize_merge, normalize_ite;
                   rewrite Forall_forall; intros ? Hin;
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

  (** ** Preservation of annotations *)

  Definition without_names (vars : list ann) : list (Op.type * clock) :=
    List.map (fun '(ty, (cl, _)) => (ty, cl)) vars.

  Fact without_names_length : forall anns,
      length (without_names anns) = length anns.
  Proof.
    intros. unfold without_names. apply map_length.
  Qed.

  Fact idents_for_anns_annots : forall anns ids st st',
      idents_for_anns anns st = (ids, st') ->
      annots (map (fun '(x, a) => Evar x a) ids) = anns.
  Proof.
    intros.
    eapply idents_for_anns_values in H; subst.
    induction ids; simpl; auto.
    destruct a; simpl. f_equal; auto.
  Qed.

  Fact idents_for_anns'_annots : forall anns ids st st',
      idents_for_anns' anns st = (ids, st') ->
      annots (map (fun '(x, a) => Evar x a) ids) = anns.
  Proof.
    intros.
    eapply idents_for_anns'_values in H; subst.
    induction ids; simpl; auto.
    destruct a; simpl. f_equal; auto.
  Qed.

  Fact normalize_merge_annot : forall ckid ets efs tys ck,
      length ets = length tys ->
      length efs = length tys ->
      Forall2 (fun ty e => annot e = [(ty, ck)]) tys (normalize_merge ckid ets efs tys ck).
  Proof.
    intros * Hlen1 Hlen2. unfold normalize_merge. rewrite Forall2_map_2.
    revert ets efs Hlen1 Hlen2.
    induction tys; intros; destruct ets, efs; simpl in *; try congruence;
      constructor; auto.
  Qed.

  Fact normalize_ite_annot : forall e ets efs tys ck,
      length ets = length tys ->
      length efs = length tys ->
      Forall2 (fun ty e => annot e = [(ty, ck)]) tys (normalize_ite e ets efs tys ck).
  Proof.
    intros * Hlen1 Hlen2. unfold normalize_ite. rewrite Forall2_map_2.
    revert ets efs Hlen1 Hlen2.
    induction tys; intros; destruct ets, efs; simpl in *; try congruence;
      constructor; auto.
  Qed.

  Fact normalize_exp_annot : forall G e is_control es' eqs' st st',
      wl_exp G e ->
      normalize_exp is_control e st = (es', eqs', st')  ->
      annots es' = annot e.
  Proof with eauto.
    destruct e; intros is_control es' eqs' st st' Hwl Hnorm;
      (* specialize (normalize_exp_length _ _ _ es' eqs' st st' Hwl Hnorm) as Hlength; *)
        inv Hwl; repeat inv_bind...
    - (* fby *) apply idents_for_anns_annots in H1...
    - (* when *)
      assert (length (concat x0) = length (annots l)) as Hlen by eauto.
      repeat simpl_list.
      rewrite H5 in Hlen.
      remember (concat x0) as l0.
      clear x0 H H2 H5 Heql0. revert l0 Hlen.
      induction tys; intros l0 Hlen; destruct l0; simpl in *; try congruence.
      destruct nck. f_equal; auto.
    - (* merge *)
      destruct is_control; repeat inv_bind.
      + assert (length (concat x2) = length (annots l)) as Hlen1 by eauto; rewrite H6 in Hlen1.
        assert (length (concat x5) = length (annots l0)) as Hlen2 by eauto; rewrite H7 in Hlen2.
        repeat simpl_list.
        remember (concat x2) as l1. remember (concat x5) as l2.
        clear x2 x5 H H0 H4 H5 H6 H7 Heql1 Heql2. revert l1 l2 Hlen1 Hlen2.
        induction tys; intros l1 l2 Hlen1 Hlen2; destruct l1; destruct l2; simpl in *; try congruence.
        destruct nck. f_equal; auto.
      + apply idents_for_anns_annots in H1...
    - (* ite *)
      destruct is_control; repeat inv_bind.
      + assert (length (concat x5) = length (annots l)) as Hlen1 by eauto; rewrite H8 in Hlen1.
        assert (length (concat x8) = length (annots l0)) as Hlen2 by eauto; rewrite H9 in Hlen2.
        repeat simpl_list.
        remember (concat x5) as l1. remember (concat x8) as l2.
        clear x5 x8 H0 H1 H8 H9 Heql1 Heql2. revert l1 l2 Hlen1 Hlen2.
        induction tys; intros l1 l2 Hlen1 Hlen2; destruct l1; destruct l2; simpl in *; try congruence.
        destruct nck. f_equal; auto.
      + apply idents_for_anns_annots in H2...
    - (* app *) apply idents_for_anns'_annots in H0...
    - (* app (reset) *) apply idents_for_anns'_annots in H1...
  Qed.

  Corollary normalize_exp_annot_length : forall G e is_control es' eqs' st st',
      wl_exp G e ->
      normalize_exp is_control e st = (es', eqs', st')  ->
      length (annots es') = length (annot e).
  Proof with eauto.
    intros.
    eapply normalize_exp_annot in H0; eauto.
    congruence.
  Qed.

  Fact map_bind2_normalize_exp_annots': forall G is_control es es' eqs' st st',
      Forall (wl_exp G) es ->
      map_bind2 (normalize_exp is_control) es st = (es', eqs', st') ->
      Forall2 (fun es' e => annots es' = annot e) es' es.
  Proof.
    intros G is_control es es' eqs' st st' Hf Hmap.
    apply map_bind2_values in Hmap.
    induction Hmap.
    - constructor.
    - destruct H as [? [? Hnorm]]. inv Hf.
      constructor; eauto.
      eapply normalize_exp_annot; eauto.
  Qed.

  Corollary map_bind2_normalize_exp_annots'' : forall G is_control es es' eqs' st st',
      Forall (wl_exp G) es ->
      map_bind2 (normalize_exp is_control) es st = (es', eqs', st') ->
      Forall2 (fun e ann => annot e = [ann]) (concat es') (annots es).
  Proof.
    intros * Hwl Hmap.
    assert (Forall (fun e => numstreams e = 1) (concat es')) as Hnumstreams.
    { eapply map_bind2_normalize_exp_numstreams in Hmap; eauto. }
    eapply map_bind2_normalize_exp_annots' in Hmap; eauto.
    unfold annots; rewrite flat_map_concat_map.
    apply Forall2_concat. rewrite Forall2_map_2.
    eapply Forall2_impl_In; eauto. clear Hmap. intros; simpl in *.
    rewrite <- H1, <- (concat_map_singl1 a) at 1.
    unfold annots; rewrite flat_map_concat_map.
    apply Forall2_concat. rewrite Forall2_map_1, Forall2_map_2.
    apply Forall2_same, Forall_forall. intros.
    assert (In x (concat es')) as HIn by eauto using in_concat'.
    eapply Forall_forall in HIn; eauto; simpl in HIn.
    rewrite <- length_annot_numstreams in HIn. singleton_length.
    repeat constructor; auto.
  Qed.

  Corollary map_bind2_normalize_exp_annots_length' :
    forall G is_control es es' eqs' st st',
      Forall (wl_exp G) es ->
      map_bind2 (normalize_exp is_control) es st = (es', eqs', st') ->
      Forall2 (fun es' e => length (annots es') = length (annot e)) es' es.
  Proof.
    intros G is_control es es' eqs' st st' Hf Hmap.
    eapply map_bind2_normalize_exp_annots' in Hmap; eauto.
    induction Hmap; inv Hf; constructor; eauto.
    congruence.
  Qed.

  Fact map_bind2_normalize_exp_annots :
    forall G is_control es es' eqs' st st',
      Forall (wl_exp G) es ->
      map_bind2 (normalize_exp is_control) es st = (es', eqs', st') ->
      annots (concat es') = annots es.
  Proof.
    intros G is_control es es' a2s st st' Hwl Hmap.
    eapply map_bind2_normalize_exp_annots' in Hmap; eauto.
    induction Hmap; simpl; auto.
    inv Hwl.
    repeat simpl_list.
    f_equal; auto.
  Qed.

  Fact map_bind2_normalize_exp_annots_length :
    forall G is_control es es' eqs' st st',
      Forall (wl_exp G) es ->
      map_bind2 (normalize_exp is_control) es st = (es', eqs', st') ->
      length (annots (concat es')) = length (annots es).
  Proof.
    intros G is_control es es' a2s st st' Hwl Hmap.
    eapply map_bind2_normalize_exp_annots in Hmap; eauto.
    congruence.
  Qed.

  Fact normalize_exps_annots : forall G es es' eqs' st st',
      Forall (wl_exp G) es ->
      normalize_exps es st = (es', eqs', st') ->
      annots es' = annots es.
  Proof.
    intros G es es' eqs' st st' Hwt Hnorm.
    unfold normalize_exps in Hnorm; repeat inv_bind.
    eapply map_bind2_normalize_exp_annots in H; eauto.
  Qed.

  Corollary normalize_exps_annots_length : forall G es es' eqs' st st',
      Forall (wl_exp G) es ->
      normalize_exps es st = (es', eqs', st') ->
      length (annots es') = length (annots es).
  Proof.
    intros G es es' eqs' st st' Hwt Hnorm.
    eapply normalize_exps_annots in Hnorm; eauto.
    congruence.
  Qed.

  Fact normalize_fby_annot : forall anns e0s es,
      length e0s = length anns ->
      length es = length anns ->
      annots (normalize_fby e0s es anns) = anns.
  Proof.
    induction anns; intros * Hl1 Hl2;
      destruct e0s; destruct es; simpl in *; try congruence; auto.
    f_equal. eauto.
  Qed.

  Fact normalize_fby_annot' : forall anns e0s es,
      length e0s = length anns ->
      length es = length anns ->
      Forall2 (fun e a => annot e = [a]) (normalize_fby e0s es anns) anns.
  Proof.
    induction anns; intros * Hl1 Hl2;
      destruct e0s; destruct es; simpl in *; try congruence; auto.
    - constructor.
    - simpl. constructor; eauto.
  Qed.

  Fact normalize_rhs_annot : forall G e es' eqs' st st',
      wl_exp G e ->
      normalize_rhs e st = (es', eqs', st') ->
      annots es' = annot e.
  Proof.
    intros * Hwt Hnorm.
    destruct e; unfold normalize_rhs in Hnorm;
      try (solve [eapply normalize_exp_annot in Hnorm; eauto]).
    - (* fby *)
      repeat inv_bind. inv Hwt.
      eapply normalize_fby_annot; eauto.
      + eapply normalize_exps_length in H; eauto. congruence.
      + eapply normalize_exps_length in H0; eauto. congruence.
    - (* app *)
      destruct o; repeat inv_bind; simpl; rewrite app_nil_r; reflexivity.
  Qed.

  Corollary normalize_rhs_annot_length : forall G e es' eqs' st st',
      wl_exp G e ->
      normalize_rhs e st = (es', eqs', st') ->
      length (annots es') = length (annot e).
  Proof.
    intros * Hwt Hnorm.
    eapply normalize_rhs_annot in Hnorm; eauto.
    congruence.
  Qed.

  Fact normalize_rhss_annots : forall G es es' eqs' st st',
      Forall (wl_exp G) es ->
      normalize_rhss es st = (es', eqs', st') ->
      annots es' = annots es.
  Proof.
    intros * Hf Hnorm.
    unfold normalize_rhss in Hnorm. repeat inv_bind.
    apply map_bind2_values in H.
    induction H; simpl in *.
    - reflexivity.
    - inv Hf.
      destruct H as [? [? H]]. eapply normalize_rhs_annot in H; eauto.
      repeat simpl_list.
      f_equal; auto.
  Qed.

  Corollary normalize_rhss_annots_length : forall G es es' eqs' st st',
      Forall (wl_exp G) es ->
      normalize_rhss es st = (es', eqs', st') ->
      length (annots es') = length (annots es).
  Proof.
    intros G es es' eqs' st st' Hf Hnorm.
    eapply normalize_rhss_annots in Hnorm; eauto.
    congruence.
  Qed.

  (** ** Propagation of the variable permutation property *)

  Fact idents_for_anns_vars_perm : forall anns ids st st',
      idents_for_anns anns st = (ids, st') ->
      Permutation ((map fst ids)++(st_ids st)) (st_ids st').
  Proof.
    induction anns; intros ids st st' Hidents; simpl in Hidents; repeat inv_bind.
    - reflexivity.
    - destruct a as [ty [cl name]]. repeat inv_bind.
      apply fresh_ident_vars_perm in H.
      apply IHanns in H0.
      etransitivity. 2: eapply H0.
      etransitivity. eapply Permutation_middle.
      apply Permutation_app_head. assumption.
  Qed.

  Fact idents_for_anns'_vars_perm : forall anns ids st st',
      idents_for_anns' anns st = (ids, st') ->
      Permutation ((map fst ids)++(st_ids st)) (st_ids st').
  Proof.
    induction anns; intros ids st st' Hidents; simpl in Hidents; repeat inv_bind.
    - reflexivity.
    - destruct a as [ty [cl [name|]]]; repeat inv_bind.
      1: (destruct x; apply reuse_ident_vars_perm in H).
      2: apply fresh_ident_vars_perm in H.
      1,2: (apply IHanns in H0;
            etransitivity; [| eapply H0];
            etransitivity; [eapply Permutation_middle|];
            apply Permutation_app_head; auto).
  Qed.

  Fact map_bind2_vars_perm {A B} : forall (k : A -> FreshAnn (B * list equation)) es es' eqs' st st',
      map_bind2 k es st = (es', eqs', st') ->
      Forall (fun e => forall es' eqs' st st',
                  k e st = (es', eqs', st') ->
                  Permutation ((vars_defined eqs')++(st_ids st)) (st_ids st')) es ->
      Permutation ((vars_defined (concat eqs'))++(st_ids st)) (st_ids st').
  Proof.
    induction es; intros es' eqs' st st' Hmap Hf;
      repeat inv_bind.
    - reflexivity.
    - inv Hf.
      specialize (IHes _ _ _ _ H0 H4).
      specialize (H3 _ _ _ _ H).
      etransitivity. 2: apply IHes.
      repeat simpl_list.
      rewrite Permutation_swap.
      apply Permutation_app_head. assumption.
  Qed.

  Fact normalize_reset_vars_perm : forall e e' eqs' st st',
      normalize_reset e st = ((e', eqs'), st') ->
      Permutation ((vars_defined eqs')++(st_ids st)) (st_ids st').
  Proof.
    intros e e' eqs' st st' Hnorm.
    destruct (normalize_reset_spec e) as [[v [ann [Hv Hspec]]]| Hspec];
      subst; rewrite Hspec in Hnorm; clear Hspec.
    - repeat inv_bind. reflexivity.
    - destruct (hd _ _) as [ty [cl _]]. repeat inv_bind.
      eapply fresh_ident_vars_perm; eauto.
  Qed.

  Fact normalize_exp_vars_perm : forall G e is_control es' eqs' st st',
      wl_exp G e ->
      normalize_exp is_control e st = ((es', eqs'), st') ->
      Permutation ((vars_defined eqs')++(st_ids st)) (st_ids st')(* ++(fresh_in e) *).
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
      repeat simpl_list.
      apply IHe1 in H...
      apply IHe2 in H0...
      etransitivity. 2: eauto. repeat simpl_list.
      rewrite Permutation_swap.
      apply Permutation_app_head...
    - (* fby *)
      repeat inv_bind.
      remember (normalize_fby _ _ _) as fby.
      assert (length x5 = length fby) as Hlen.
      { eapply map_bind2_normalize_exp_length in H1...
        eapply map_bind2_normalize_exp_length in H2...
        apply idents_for_anns_length in H3...
        rewrite Heqfby, normalize_fby_length; solve_length.
      }
      apply map_bind2_vars_perm in H1. 2:solve_forall.
      apply map_bind2_vars_perm in H2. 2:solve_forall.
      apply idents_for_anns_vars_perm in H3.
      repeat simpl_list.
      etransitivity. 2:apply H3.
      replace (map (fun x => fst (let '(x0, _, fby) := x in ([x0], [fby]))) (combine x5 _)) with (map (fun x => [fst x]) x5).
      2: { clear - Hlen. revert fby Hlen.
           induction x5; intros; destruct fby; simpl in *; try congruence.
           destruct a. f_equal; eauto. }
      repeat rewrite concat_app.
      replace (concat (map (fun x => [fst x]) x5)) with (map fst x5).
      2: { clear. induction x5; simpl; f_equal; auto. }
      repeat rewrite <- app_assoc. apply Permutation_app_head.
      etransitivity. 2: eauto.
      rewrite Permutation_swap. apply Permutation_app_head; auto.
    - (* when *)
      repeat inv_bind.
      eapply map_bind2_vars_perm...
      rewrite Forall_forall in *. intros...
    - (* merge *)
      destruct is_control; repeat inv_bind.
      + apply map_bind2_vars_perm in H1. 2: (rewrite Forall_forall in *; eauto).
        apply map_bind2_vars_perm in H2. 2: (rewrite Forall_forall in *; eauto).
        etransitivity. 2: apply H2.
        repeat simpl_list.
        rewrite Permutation_swap. apply Permutation_app_head.
        assumption.
      + repeat simpl_list.
        rewrite combine_map_fst'.
        2: {
          repeat rewrite map_length. repeat rewrite combine_length.
          repeat rewrite typesof_annots in *.
          assert (length (concat x3) = length (annots ets)) as Hlen3 by eauto.
          assert (length (concat x7) = length (annots efs)) as Hlen7 by eauto.
          apply idents_for_anns_length in H3.
          repeat simpl_list. solve_length. }
        apply map_bind2_vars_perm in H1. 2: (repeat rewrite_Forall_forall; eauto).
        apply map_bind2_vars_perm in H2. 2: (repeat rewrite_Forall_forall; eauto).
        apply idents_for_anns_vars_perm in H3.
        etransitivity. 2: eauto.
        replace (concat (map (fun '(id, _) => [id]) x6)) with (map fst x6).
        2: { clear H3. induction x6; try destruct a; simpl; f_equal; auto. }
        repeat rewrite <- app_assoc. apply Permutation_app_head.
        etransitivity. 2: eauto.
        repeat simpl_list.
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
      + repeat simpl_list.
        rewrite combine_map_fst'.
        2: {
          repeat rewrite map_length. repeat rewrite combine_length.
          repeat rewrite typesof_annots in *.
          assert (length (concat x5) = length (annots ets)) as Hlen3 by eauto.
          assert (length (concat x9) = length (annots efs)) as Hlen7 by eauto.
          apply idents_for_anns_length in H4.
          repeat simpl_list. solve_length. }
        apply map_bind2_vars_perm in H2. 2: (repeat rewrite_Forall_forall; eauto).
        apply map_bind2_vars_perm in H3. 2: (repeat rewrite_Forall_forall; eauto).
        apply idents_for_anns_vars_perm in H4.
        apply IHe in H1; eauto.
        etransitivity. 2: eauto.
        replace (concat (map (fun '(id, _) => [id]) x8)) with (map fst x8).
        2: { clear H4. induction x8; try destruct a; simpl; f_equal; auto. }
        repeat rewrite <- app_assoc. apply Permutation_app_head.
        etransitivity. 2: eauto.
        repeat simpl_list.
        rewrite app_assoc. rewrite Permutation_swap. apply Permutation_app_head.
        etransitivity. 2: eauto.
        rewrite <- app_assoc. rewrite Permutation_swap. apply Permutation_app_head.
        assumption.
    - (* app *)
      repeat inv_bind.
      assert (length x1 = length a) as Hlen by eauto.
      apply idents_for_anns'_vars_perm in H2.
      apply map_bind2_vars_perm in H1. 2: (repeat rewrite_Forall_forall; eauto).
      etransitivity. 2: apply H2.
      rewrite <- app_assoc.
      apply Permutation_app_head. rewrite app_nil_r. assumption.
    - (* app (reset) *)
      repeat inv_bind.
      assert (length x5 = length a) as Hlen by eauto.
      apply idents_for_anns'_vars_perm in H3.
      apply map_bind2_vars_perm in H1. 2: (repeat rewrite_Forall_forall; eauto).
      apply normalize_reset_vars_perm in H4.
      apply H in H2; eauto.
      etransitivity. 2: eauto.
      repeat rewrite <- app_assoc.
      apply Permutation_app_head.
      repeat simpl_list.
      etransitivity; [| eauto].
      rewrite Permutation_app_comm, Permutation_swap, <- app_assoc.
      apply Permutation_app_head.
      etransitivity; [| eauto].
      repeat simpl_list. apply Permutation_app_head.
      rewrite Permutation_app_comm. assumption.
  Qed.

  Corollary normalize_exps_vars_perm : forall G es es' eqs' st st',
      Forall (wl_exp G) es ->
      normalize_exps es st = ((es', eqs'), st') ->
      Permutation ((vars_defined eqs')++(st_ids st)) (st_ids st').
  Proof with eauto.
    intros G es es' eqs' st st' Hf Hnorm.
    unfold normalize_exps in Hnorm.
    repeat inv_bind.
    eapply map_bind2_vars_perm...
    repeat rewrite_Forall_forall.
    eapply normalize_exp_vars_perm...
  Qed.

  Fact normalize_rhs_vars_perm : forall G e es' eqs' st st',
      wl_exp G e ->
      normalize_rhs e st = ((es', eqs'), st') ->
      Permutation ((vars_defined eqs')++(st_ids st)) (st_ids st').
  Proof with eauto.
    intros * Hwt Hnorm.
    destruct e; unfold normalize_rhs in Hnorm;
      try (solve [eapply normalize_exp_vars_perm; eauto]); inv Hwt; repeat inv_bind.
    - (* fby *)
      repeat inv_bind.
      eapply normalize_exps_vars_perm in H...
      eapply normalize_exps_vars_perm in H0...
      etransitivity. 2: eauto.
      repeat simpl_list.
      rewrite Permutation_swap. apply Permutation_app_head; auto.
    - (* app *)
      eapply normalize_exps_vars_perm in H; eauto.
      rewrite app_nil_r; eauto.
    - (* app (reset) *)
      eapply normalize_exps_vars_perm in H; eauto.
      eapply normalize_exp_vars_perm in H0; eauto.
      eapply normalize_reset_vars_perm in H1.
      etransitivity. 2: eauto.
      repeat simpl_list.
      rewrite Permutation_app_comm, Permutation_swap, <- app_assoc, <- app_assoc.
      apply Permutation_app_head.
      etransitivity. 2: eauto.
      apply Permutation_app_head.
      rewrite Permutation_app_comm.
      assumption.
  Qed.

  Corollary normalize_rhss_vars_perm : forall G es es' eqs' st st',
      Forall (wl_exp G) es ->
      normalize_rhss es st = ((es', eqs'), st') ->
      Permutation ((vars_defined eqs')++(st_ids st)) (st_ids st').
  Proof.
    intros * Hf Hnorm.
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
      repeat simpl_list.
      f_equal; simpl in *; auto.
  Qed.

  Fact untuple_equation_vars_perm : forall G eq eqs' st st',
      wl_equation G eq ->
      untuple_equation eq st = (eqs', st') ->
      Permutation ((vars_defined eqs')++(st_ids st)) ((vars_defined [eq])++(st_ids st')).
  Proof.
    intros * Hwt Hnorm.
    destruct eq; simpl in *.
    repeat inv_bind. destruct Hwt as [Hwt Hl].
    specialize (normalize_rhss_vars_perm _ _ _ _ _ _ Hwt H) as Hperm1.
    rewrite app_nil_r.
    assert (vars_defined (flat_map split_equation [(l, x)]) = vars_defined [(l, x)]) as Hxl.
    { apply split_equations_vars_defined.
      repeat constructor.
      eapply normalize_rhss_annots_length in H; eauto. congruence. }
    repeat simpl_list.
    apply Permutation_app; auto.
    rewrite <- Hxl at 2. reflexivity.
  Qed.

  Corollary untuple_equations_vars_perm : forall G eqs eqs' st st',
      Forall (wl_equation G) eqs ->
      untuple_equations eqs st = (eqs', st') ->
      Permutation ((vars_defined eqs')++(st_ids st)) ((vars_defined eqs)++(st_ids st')).
  Proof.
    induction eqs; intros * Hf Hnorm; unfold untuple_equations in Hnorm; repeat inv_bind.
    - reflexivity.
    - inv Hf.
      assert (untuple_equations eqs x1 = (concat x2, st')) as Hnorm'.
      { unfold untuple_equations. repeat inv_bind. repeat eexists; eauto.
        inv_bind; eauto. } eapply IHeqs in Hnorm'; eauto.
      eapply untuple_equation_vars_perm in H; eauto; simpl in *.
      repeat simpl_list.
      rewrite Permutation_swap, H, Permutation_swap.
      apply Permutation_app_head. assumption.
  Qed.

  (** ** Specification of an (almost) normalized node *)

  Inductive normalized_lexp : exp -> Prop :=
  | normalized_Econst : forall c, normalized_lexp (Econst c)
  | normalized_Evar : forall x ty cl, normalized_lexp (Evar x (ty, cl))
  | normalized_Eunop : forall op e1 ty cl,
      normalized_lexp e1 ->
      normalized_lexp (Eunop op e1 (ty, cl))
  | normalized_Ebinop : forall op e1 e2 ty cl,
      normalized_lexp e1 ->
      normalized_lexp e2 ->
      normalized_lexp (Ebinop op e1 e2 (ty, cl))
  | normalized_Ewhen : forall e x b ty cl,
      normalized_lexp e ->
      normalized_lexp (Ewhen [e] x b ([ty], cl)).

  Inductive normalized_cexp : exp -> Prop :=
  | normalized_Emerge : forall x et ef ty cl,
      normalized_cexp et ->
      normalized_cexp ef ->
      normalized_cexp (Emerge x [et] [ef] ([ty], cl))
  | normalized_Eite : forall e et ef ty cl,
      normalized_lexp e ->
      normalized_cexp et ->
      normalized_cexp ef ->
      normalized_cexp (Eite e [et] [ef] ([ty], cl))
  | normalized_lexp_cexp : forall e,
      normalized_lexp e ->
      normalized_cexp e.

  Inductive untupled_equation : equation -> Prop :=
  | untupled_eq_Eapp : forall xs f es lann,
      Forall normalized_lexp es ->
      untupled_equation (xs, [Eapp f es None lann])
  | untupled_eq_Eapp_reset : forall xs f es x ty cl lann,
      Forall normalized_lexp es ->
      untupled_equation (xs, [Eapp f es (Some (Evar x (ty, cl))) lann])
  | untupled_eq_Efby : forall x e0 e ann,
      normalized_lexp e0 ->
      normalized_lexp e ->
      untupled_equation ([x], [Efby [e0] [e] [ann]])
  | untupled_eq_cexp : forall x e,
      normalized_cexp e ->
      untupled_equation ([x], [e]).

  Definition untupled_node (n : node) :=
    Forall untupled_equation (n_eqs n).

  Definition untupled_global (G : global) := Forall untupled_node G.

  Hint Constructors normalized_lexp normalized_cexp untupled_equation.

  (** A few initial properties *)

  Fact normalized_lexp_numstreams : forall e,
      normalized_lexp e ->
      numstreams e = 1.
  Proof.
    induction e; intros Hnorm; inv Hnorm; reflexivity.
  Qed.

  Fact normalized_cexp_numstreams : forall e,
      normalized_cexp e ->
      numstreams e = 1.
  Proof.
    induction e; intros Hnorm; inv Hnorm;
      try apply normalized_lexp_numstreams in H; auto.
  Qed.

  (** ** After normalization, equations and expressions are normalized *)

  Fact normalized_lexp_hd_default : forall es,
      Forall normalized_lexp es ->
      normalized_lexp (hd_default es).
  Proof.
    intros es Hf.
    destruct es; simpl.
    - constructor.
    - inv Hf; auto.
  Qed.

  Fact map_bind2_normalized_lexp' {A A2} :
    forall (k : A -> FreshAnn ((list exp) * A2)) a es' a2s st st',
      map_bind2 k a st = (es', a2s, st') ->
      Forall (fun a => forall es' a2s st st',
                  k a st = (es', a2s, st') ->
                  Forall normalized_lexp es') a ->
      Forall normalized_lexp (concat es').
  Proof.
    intros k a eqs' a2s st st' Hmap Hf.
    apply map_bind2_values in Hmap.
    induction Hmap; simpl in *.
    - constructor.
    - destruct H as [? [? H]]. inv Hf.
      rewrite Forall_app.
      split; eauto.
  Qed.

  Fact map_bind2_normalized_cexp' {A A2} :
    forall (k : A -> FreshAnn ((list exp) * A2)) a es' a2s st st',
      map_bind2 k a st = (es', a2s, st') ->
      Forall (fun a => forall es' a2s st st',
                  k a st = (es', a2s, st') ->
                  Forall normalized_cexp es') a ->
      Forall normalized_cexp (concat es').
  Proof.
    intros k a eqs' a2s st st' Hmap Hf.
    apply map_bind2_values in Hmap.
    induction Hmap; simpl in *.
    - constructor.
    - destruct H as [? [? H]]. inv Hf.
      rewrite Forall_app.
      split; eauto.
  Qed.

  Hint Resolve in_combine_l in_combine_r.
  Hint Resolve normalized_lexp_hd_default.

  Lemma normalize_exp_normalized_lexp : forall e es' eqs' st st',
      normalize_exp false e st = (es', eqs', st') ->
      Forall normalized_lexp es'.
  Proof with eauto.
    induction e using exp_ind2; intros es' eqs' st st' Hnorm;
      repeat inv_bind; repeat constructor.
    - (* var *)
      destruct a...
    - (* unop *)
      destruct a...
    - (* binop *)
      destruct a. constructor...
    - (* fby *)
      simpl_forall.
      repeat rewrite_Forall_forall.
      repeat simpl_In. destruct a0...
    - (* when *)
      destruct a. repeat inv_bind. unfold normalize_when.
      apply map_bind2_normalized_lexp' in H0...
      repeat rewrite_Forall_forall.
      repeat simpl_In...
    - (* merge *)
      destruct a. repeat inv_bind. unfold normalize_merge.
      repeat rewrite_Forall_forall.
      repeat simpl_In. destruct a...
    - (* ite *)
      destruct a. repeat inv_bind. unfold normalize_ite.
      repeat rewrite_Forall_forall.
      repeat simpl_In. destruct a...
    - (* app *)
      repeat rewrite_Forall_forall.
      repeat simpl_In. destruct a0...
  Qed.
  Hint Resolve normalize_exp_normalized_lexp.

  Corollary map_bind2_normalized_lexp : forall es es' eqs' st st',
      map_bind2 (normalize_exp false) es st = (es', eqs', st') ->
      Forall normalized_lexp (concat es').
  Proof.
    intros es es' eqs' st st' Hnorm.
    eapply map_bind2_normalized_lexp' in Hnorm; auto.
    solve_forall.
  Qed.
  Hint Resolve map_bind2_normalized_lexp.

  Corollary normalize_exps_normalized_lexp: forall es es' eqs' st st',
      normalize_exps es st = (es', eqs', st') ->
      Forall normalized_lexp es'.
  Proof.
    intros es es' eqs' st st' Hnorm.
    unfold normalize_exps in Hnorm. repeat inv_bind.
    apply map_bind2_normalized_lexp in H; auto.
  Qed.
  Hint Resolve normalize_exps_normalized_lexp.

  Fact normalize_reset_normalized_lexp : forall e e' eqs' st st',
      normalize_reset e st = (e', eqs', st') ->
      normalized_lexp e'.
  Proof.
    intros * Hnorm.
    specialize (normalize_reset_spec e) as [[? [? [? Hspec]]]|Hspec]; subst;
      rewrite Hspec in Hnorm; clear Hspec; repeat inv_bind.
    - destruct x0. constructor.
    - destruct hd as [? [? ?]] in Hnorm; repeat inv_bind.
      constructor.
  Qed.

  Fact normalize_merge_normalized_cexp : forall x ets efs tys ck,
      Forall normalized_cexp ets ->
      Forall normalized_cexp efs ->
      Forall normalized_cexp (normalize_merge x ets efs tys ck).
  Proof.
    intros. unfold normalize_merge.
    repeat rewrite_Forall_forall. repeat simpl_In.
    econstructor; eauto.
  Qed.

  Fact normalize_ite_normalized_cexp : forall e ets efs tys ck,
      normalized_lexp e ->
      Forall normalized_cexp ets ->
      Forall normalized_cexp efs ->
      Forall normalized_cexp (normalize_ite e ets efs tys ck).
  Proof.
    intros. unfold normalize_ite.
    repeat rewrite_Forall_forall. repeat simpl_In.
    econstructor; eauto.
  Qed.

  Lemma normalize_exp_normalized_cexp : forall e es' eqs' st st',
      normalize_exp true e st = (es', eqs', st') ->
      Forall normalized_cexp es'.
  Proof with eauto.
    induction e using exp_ind2; intros es' eqs' st st' Hnorm;
      repeat inv_bind; repeat constructor.
    - (* var *)
      destruct a...
    - (* unop *)
      destruct a...
    - (* binop *)
      destruct a. constructor...
    - (* fby *)
      solve_forall.
      repeat simpl_In. destruct a0...
    - (* when *)
      destruct a. repeat inv_bind. unfold normalize_when.
      apply map_bind2_normalized_lexp in H0.
      repeat rewrite_Forall_forall.
      repeat simpl_In...
    - (* merge *)
      destruct a. repeat inv_bind.
      eapply normalize_merge_normalized_cexp...
      apply map_bind2_normalized_cexp' in H1; [|solve_forall]...
      apply map_bind2_normalized_cexp' in H2; [|solve_forall]...
    - (* ite *)
      destruct a. repeat inv_bind.
      eapply normalize_ite_normalized_cexp...
      apply map_bind2_normalized_cexp' in H2; [|solve_forall]...
      apply map_bind2_normalized_cexp' in H3; [|solve_forall]...
    - (* app *)
      solve_forall.
      repeat simpl_In. destruct a0...
  Qed.

  Corollary map_bind2_normalized_cexp : forall es es' eqs' st st',
      map_bind2 (normalize_exp true) es st = (es', eqs', st') ->
      Forall normalized_cexp (concat es').
  Proof.
    intros. apply map_bind2_normalized_cexp' in H; auto.
    solve_forall. apply normalize_exp_normalized_cexp in H1; auto.
  Qed.

  Fact map_bind2_untupled_eq {A A1} :
    forall (k : A -> FreshAnn (A1 * (list equation))) a a1s eqs' st st',
      map_bind2 k a st = (a1s, eqs', st') ->
      Forall (fun a => forall a1s eqs' st st',
                  k a st = (a1s, eqs', st') ->
                  Forall untupled_equation eqs') a ->
      Forall untupled_equation (concat eqs').
  Proof.
    induction a; intros * Hmap Hf;
      repeat inv_bind.
    - constructor.
    - inv Hf. simpl.
      rewrite Forall_app; eauto.
  Qed.

  Lemma normalize_exp_untupled_eq : forall e is_control es' eqs' st st',
      normalize_exp is_control e st = (es', eqs', st') ->
      Forall untupled_equation eqs'.
  Proof with eauto.
    induction e using exp_ind2; intros * Hnorm;
      repeat inv_bind; repeat constructor; eauto.
    - (* binop *)
      apply Forall_app. split...
    - (* fby *)
      repeat rewrite Forall_app. repeat split.
      + eapply map_bind2_normalized_lexp in H1.
        eapply map_bind2_normalized_lexp in H2.
        eapply Forall_forall; intros ? Hin.
        unfold normalize_fby in Hin. repeat simpl_In.
        constructor.
        * eapply Forall_forall in H7...
        * eapply Forall_forall in H5...
      + eapply map_bind2_untupled_eq in H1... solve_forall.
      + eapply map_bind2_untupled_eq in H2...
        eapply map_bind2_st_follows in H1; solve_forall.
    - (* when *)
      destruct a. repeat inv_bind.
      eapply map_bind2_untupled_eq in H0; eauto. solve_forall.
    - (* merge *)
      destruct a; destruct is_control; repeat inv_bind; unfold normalize_merge;
        repeat rewrite Forall_app; repeat split.
      1,2,4,5: (eapply map_bind2_untupled_eq; eauto; solve_forall).
      rewrite Forall_forall; intros [? ?] Hin. rewrite map_map in Hin; simpl in Hin.
      repeat simpl_In.
      do 2 constructor.
      + eapply map_bind2_normalized_cexp in H1.
        rewrite Forall_forall in H1...
      + eapply map_bind2_normalized_cexp in H2.
        rewrite Forall_forall in H2...
    - (* ite *)
      destruct a; destruct is_control; repeat inv_bind; unfold normalize_ite;
        repeat rewrite Forall_app; repeat split.
      1,5: (eapply IHe; eauto).
      1,2,4,5: (eapply map_bind2_untupled_eq; eauto; solve_forall).
      rewrite Forall_forall; intros [? ?] Hin. rewrite map_map in Hin; simpl in Hin.
      repeat simpl_In.
      constructor. constructor.
      + eapply normalized_lexp_hd_default.
        eapply normalize_exp_normalized_lexp...
      + eapply map_bind2_normalized_cexp in H2.
        rewrite Forall_forall in H2...
      + eapply map_bind2_normalized_cexp in H3.
        rewrite Forall_forall in H3...
    - (* app *)
      eapply map_bind2_normalized_lexp in H1...
      destruct ro; repeat inv_bind.
      + specialize (normalize_reset_spec (hd_default x)) as [[? [? [? Hspec]]]|Hspec]; subst;
          rewrite Hspec in H4; clear Hspec; repeat inv_bind.
        * destruct x3...
        * destruct (hd _) as [? [? ?]]; repeat inv_bind...
      + constructor...
    - (* app (auxiliary equations) *)
      rewrite Forall_app. split.
      + destruct ro; repeat inv_bind;
        eapply map_bind2_untupled_eq in H1; eauto; solve_forall.
      + destruct ro; repeat inv_bind; try constructor;
        eapply Forall_app. split.
        * eapply H in H2...
        * specialize (normalize_reset_spec (hd_default x)) as [[? [? [? Hspec]]]|Hspec]; subst;
          rewrite Hspec in H4; clear Hspec; repeat inv_bind...
          destruct (hd _) as [? [? ?]]; repeat inv_bind.
          repeat constructor. apply normalized_lexp_hd_default...
  Qed.
  Local Hint Resolve normalize_exp_untupled_eq.

  Corollary normalize_exps_untupled_eq : forall es es' eqs' st st',
      normalize_exps es st = (es', eqs', st') ->
      Forall untupled_equation eqs'.
  Proof.
    intros * Hnorm.
    unfold normalize_exps in Hnorm. repeat inv_bind.
    eapply map_bind2_untupled_eq in H; eauto.
    solve_forall.
  Qed.
  Local Hint Resolve normalize_exps_untupled_eq.

  (* Intermediary predicate for normalized rhs *)
  Inductive untupled_rhs : exp -> Prop :=
  | untupled_rhs_Eapp : forall f es lann,
      Forall normalized_lexp es ->
      untupled_rhs (Eapp f es None lann)
  | untupled_rhs_Eapp_reset : forall f es x ty cl lann,
      Forall normalized_lexp es ->
      untupled_rhs (Eapp f es (Some (Evar x (ty, cl))) lann)
  | untupled_rhs_Efby : forall e0 e ann,
      normalized_lexp e0 ->
      normalized_lexp e ->
      untupled_rhs (Efby [e0] [e] [ann])
  | untupled_rhs_cexp : forall e,
      normalized_cexp e ->
      untupled_rhs e.
  Hint Constructors untupled_rhs.

  Fact untupled_equation_untupled_rhs : forall xs es,
      untupled_equation (xs, es) ->
      Forall untupled_rhs es.
  Proof with eauto.
    intros * Hnormed.
    inv Hnormed...
  Qed.

  Fact normalize_rhs_untupled_rhs : forall e es' eqs' st st',
      normalize_rhs e st = (es', eqs', st') ->
      Forall untupled_rhs es'.
  Proof with eauto.
    intros * Hnorm.
    destruct e; unfold normalize_rhs in Hnorm;
      try (apply normalize_exp_normalized_cexp in Hnorm; solve_forall; auto).
    - (* fby *)
      repeat inv_bind.
      apply normalize_exps_normalized_lexp in H.
      apply normalize_exps_normalized_lexp in H0.
      unfold normalize_fby.
      apply Forall_forall; intros * Hin.
      repeat simpl_In.
      constructor.
      + eapply Forall_forall in H3; eauto.
      + eapply Forall_forall in H1; eauto.
    - (* app *)
      destruct o; repeat inv_bind...
      specialize (normalize_reset_spec (hd_default x4)) as [[? [[? ?] [? Hspec]]]|Hspec]; subst;
        rewrite Hspec in H1; clear Hspec; repeat inv_bind...
      destruct (hd _) as [? [ty cl]]; repeat inv_bind...
  Qed.

  Corollary normalize_rhss_untupled_rhs : forall es es' eqs' st st',
      normalize_rhss es st = (es', eqs', st') ->
      Forall untupled_rhs es'.
  Proof with eauto.
    intros * Hnorm.
    unfold normalize_rhss in Hnorm. repeat inv_bind.
    eapply map_bind2_values in H.
    induction H; simpl; try constructor.
    apply Forall_app. split; auto.
    destruct H as [? [? H]].
    eapply normalize_rhs_untupled_rhs; eauto.
  Qed.

  Fact normalize_rhs_untupled_eq : forall e es' eqs' st st',
      normalize_rhs e st = (es', eqs', st') ->
      Forall untupled_equation eqs'.
  Proof with eauto.
    intros * Hnorm.
    destruct e; unfold normalize_rhs in Hnorm;
      try (eapply normalize_exp_untupled_eq in Hnorm; eauto).
    - (* fby *)
      repeat inv_bind.
      repeat rewrite Forall_app. repeat split...
    - (* app *)
      repeat inv_bind...
      destruct o; repeat inv_bind; repeat rewrite Forall_app; repeat split...
      specialize (normalize_reset_spec (hd_default x4)) as [[? [? [? Hspec]]]|Hspec]; subst;
        rewrite Hspec in H1; clear Hspec; repeat inv_bind; eauto.
      + destruct (hd _ _) as [? [? ?]]; simpl in H1.
        repeat inv_bind. repeat constructor.
        apply normalized_lexp_hd_default...
  Qed.
  Hint Resolve normalize_rhs_untupled_eq.

  Corollary normalize_rhss_untupled_eq : forall es es' eqs' st st',
      normalize_rhss es st = (es', eqs', st') ->
      Forall untupled_equation eqs'.
  Proof.
    intros * Hnorm.
    unfold normalize_rhss in Hnorm; repeat inv_bind.
    eapply map_bind2_untupled_eq in H; eauto.
    rewrite Forall_forall; intros; eauto.
  Qed.
  Hint Resolve normalize_rhss_untupled_eq.

  Lemma untuple_equation_untupled_eq : forall G eq eqs' st st',
      wl_equation G eq ->
      untuple_equation eq st = (eqs', st') ->
      Forall untupled_equation eqs'.
  Proof with eauto.
    intros G [xs es] * Hwl Hnorm.
    unfold untuple_equation in Hnorm.
    repeat inv_bind.
    rewrite Forall_app. split.
    - assert (length xs = length (annots x)) as Hlen.
      { destruct Hwl as [Hwl1 Hwl2].
        eapply normalize_rhss_annots_length in H...
        congruence. } clear Hwl.
      eapply normalize_rhss_untupled_rhs in H; eauto.
      revert xs Hlen.
      induction H; intros xs Hlen; constructor.
      + inv H...
        * destruct xs; simpl in *; try omega.
          constructor...
        * simpl in Hlen. rewrite app_length in Hlen.
          rewrite length_annot_numstreams in Hlen.
          specialize (normalized_cexp_numstreams _ H1) as Hlen'.
          rewrite Hlen' in *. simpl.
          destruct xs... simpl in Hlen. omega.
      + eapply IHForall.
        rewrite skipn_length.
        rewrite Hlen. simpl. rewrite app_length.
        rewrite length_annot_numstreams. omega.
    - eapply normalize_rhss_untupled_eq in H; eauto.
  Qed.

  Corollary untuple_equations_untupled_eq : forall G eqs eqs' st st',
      Forall (wl_equation G) eqs ->
      untuple_equations eqs st = (eqs', st') ->
      Forall untupled_equation eqs'.
  Proof.
    induction eqs; intros * Hwl Hnorm;
      unfold untuple_equations in Hnorm; repeat inv_bind; simpl; auto.
    inv Hwl. apply Forall_app; split.
    - eapply untuple_equation_untupled_eq; eauto.
    - eapply IHeqs; eauto.
      unfold untuple_equations; repeat inv_bind; repeat eexists; eauto.
      inv_bind; eauto.
  Qed.

  (** ** No anonymous names in a normalized node *)

  Fact normalized_lexp_no_fresh : forall e,
      normalized_lexp e ->
      fresh_in e = [].
  Proof with eauto.
    intros e Hnormed.
    induction Hnormed; simpl...
    - (* binop *)
      rewrite IHHnormed1. rewrite IHHnormed2. reflexivity.
    - (* when *)
      rewrite IHHnormed. reflexivity.
  Qed.

  Corollary normalized_lexps_no_fresh : forall es,
      Forall normalized_lexp es ->
      fresh_ins es = [].
  Proof.
    induction es; intros; auto.
    unfold fresh_ins in *; simpl.
    inv H. rewrite IHes, app_nil_r; auto using normalized_lexp_no_fresh.
  Qed.

  Fact normalized_cexp_no_fresh : forall e,
      normalized_cexp e ->
      fresh_in e = [].
  Proof with eauto.
    intros e Hnormed.
    induction Hnormed; simpl...
    - (* merge *)
      rewrite IHHnormed1. rewrite IHHnormed2. reflexivity.
    - (* ite *)
      rewrite IHHnormed1. rewrite IHHnormed2.
      rewrite normalized_lexp_no_fresh...
    - (* lexp *)
      eapply normalized_lexp_no_fresh...
  Qed.

  Corollary normalized_cexps_no_fresh : forall es,
      Forall normalized_cexp es ->
      fresh_ins es = [].
  Proof.
    induction es; intros; auto.
    unfold fresh_ins in *; simpl.
    inv H. rewrite IHes, app_nil_r; auto using normalized_cexp_no_fresh.
  Qed.

  Corollary normalize_exp_no_fresh : forall e is_control es' eqs' st st',
      normalize_exp is_control e st = (es', eqs', st') ->
      fresh_ins es' = [].
  Proof.
    intros e is_control es' eqs' st st' Hnorm.
    unfold fresh_ins. rewrite concat_eq_nil, Forall_map.
    destruct is_control.
    - apply normalize_exp_normalized_cexp in Hnorm.
      eapply Forall_impl; eauto. intros. apply normalized_cexp_no_fresh; auto.
    - apply normalize_exp_normalized_lexp in Hnorm.
      eapply Forall_impl; eauto. intros. apply normalized_lexp_no_fresh; auto.
  Qed.

  Corollary normalize_reset_no_fresh : forall e e' eqs' st st',
      normalize_reset e st = (e', eqs', st') ->
      fresh_in e' = [].
  Proof.
    intros * Hnorm.
    apply normalize_reset_normalized_lexp, normalized_lexp_no_fresh in Hnorm; auto.
  Qed.

  Corollary normalize_exps_no_fresh : forall es es' eqs' st st',
      normalize_exps es st = (es', eqs', st') ->
      fresh_ins es' = [].
  Proof.
    induction es; intros es' eqs' st st' Hnorm;
      unfold fresh_ins;
      unfold normalize_exps in Hnorm; repeat inv_bind; auto.
    simpl. rewrite map_app, concat_app.
    eapply normalize_exp_no_fresh in H.
    unfold fresh_ins in H, IHes; rewrite H; simpl.
    eapply IHes.
    unfold normalize_exps; inv_bind.
    repeat eexists; eauto. inv_bind; eauto.
  Qed.

  Fact untupled_equation_no_anon_in_eq : forall e,
      untupled_equation e ->
      anon_in_eq e = [].
  Proof with eauto.
    intros * Hnormed.
    induction Hnormed; unfold anon_in_eq, anon_ins; simpl; repeat rewrite app_nil_r.
    - (* app *)
      unfold fresh_ins. rewrite concat_eq_nil, Forall_map.
      solve_forall. eapply normalized_lexp_no_fresh...
    - (* app (reset) *)
      unfold fresh_ins. rewrite concat_eq_nil, Forall_map.
      solve_forall. eapply normalized_lexp_no_fresh...
    - (* fby *)
      rewrite normalized_lexp_no_fresh...
      rewrite normalized_lexp_no_fresh...
    - (* cexp *)
      specialize (anon_in_fresh_in e) as Hincl.
      rewrite normalized_cexp_no_fresh in Hincl...
      apply incl_nil...
  Qed.

  Lemma untupled_equations_no_anon : forall eqs,
      Forall untupled_equation eqs ->
      anon_in_eqs eqs = [].
  Proof.
    intros * Hnormed.
    unfold anon_in_eqs.
    rewrite concat_eq_nil, Forall_map.
    solve_forall. eapply untupled_equation_no_anon_in_eq; eauto.
  Qed.

  Corollary untuple_equations_no_anon : forall G eqs eqs' st st',
      Forall (wl_equation G) eqs ->
      untuple_equations eqs st = (eqs', st') ->
      anon_in_eqs eqs' = [].
  Proof.
    intros * Hwl Hnorm.
    eapply untupled_equations_no_anon.
    eapply untuple_equations_untupled_eq; eauto.
  Qed.

  (** ** Normalization of a full node *)

  Import Fresh Fresh.Fresh Facts Tactics.

  Definition untuple_equations' (eq : list equation) (st : fresh_st (type * clock)) :
    { res | untuple_equations eq st = res }.
  Proof.
    remember (untuple_equations eq st) as eqs'.
    econstructor; eauto.
  Defined.

  Definition first_unused_ident (vs : list ident) : ident :=
    ((fold_left Pos.max vs xH) + 100)%positive.

  Fact first_unused_ident_gt : forall vs id,
      first_unused_ident vs = id ->
      Forall (fun id' => (id' < id)%positive) vs.
  Proof.
    intros n id Hfirst.
    subst. unfold first_unused_ident.
    rewrite Forall_forall; intros x Hin.
    eapply Pos.le_lt_trans. 2: apply Pos.lt_add_r.
    apply max_fold_in; auto.
  Qed.

  Program Definition untuple_node (n : node) (G : { G | wl_node G n}) : node :=
    let anon := anon_in_eqs (n_eqs n) in
    let id0 := first_unused_ident (reserved++List.map fst (n_in n++n_vars n++n_out n++anon)) in
    let eqs := untuple_equations' (n_eqs n) (init_st id0) in
    let nvars := (st_anns (snd (proj1_sig eqs))) in
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
    remember (first_unused_ident _) as id0.
    eapply untuple_equations_vars_perm with (st:=init_st id0) in H. 2: eapply surjective_pairing.
    specialize (n_defd n) as Hperm'.
    unfold st_ids, idty in *. rewrite init_st_anns in H. rewrite app_nil_r in H.
    etransitivity. apply H.
    rewrite Permutation_app_comm. symmetry.
    rewrite <- app_assoc. rewrite Permutation_swap.
    repeat rewrite map_app in *.
    rewrite Hperm'. reflexivity.
  Qed.
  Next Obligation.
    remember (first_unused_ident _) as id0.
    specialize (first_unused_ident_gt _ id0 (eq_sym Heqid0)) as Hident.
    remember (untuple_equations (n_eqs n) (init_st id0)) as res.
    assert (st_valid_reuse (snd res) (PSP.of_list (map fst (n_in n ++ n_vars n ++ n_out n)))
                           PS.empty) as Hvalid.
    { specialize (n_nodup n) as Hndup. rewrite fst_NoDupMembers in Hndup.
      repeat rewrite map_app in Hndup.
      subst. eapply untuple_equations_st_valid.
      2: eapply surjective_pairing.
      2: eapply init_st_valid_reuse.
      + rewrite PSP.elements_empty, app_nil_r.
        repeat ndup_r Hndup.
      + replace (ps_adds _ PS.empty) with (ps_from_list (map fst (anon_in_eqs (n_eqs n)))); auto.
        rewrite ps_from_list_ps_of_list.
        repeat rewrite ps_of_list_ps_to_list_Perm; repeat rewrite map_app; repeat rewrite <- app_assoc in *; auto.
        repeat ndup_r Hndup.
        repeat rewrite app_assoc in Hndup. apply NoDup_app_l in Hndup.
        repeat rewrite <- app_assoc in Hndup; auto.
      + rewrite <- ps_from_list_ps_of_list. rewrite PS_For_all_Forall'.
        eapply Forall_incl; eauto.
        repeat rewrite map_app.
        repeat apply incl_tl.
        repeat rewrite app_assoc. apply incl_appl. reflexivity.
      + replace (ps_adds _ PS.empty) with (ps_from_list (map fst (anon_in_eqs (n_eqs n)))); auto.
        rewrite PS_For_all_Forall'.
        eapply Forall_incl; eauto.
        repeat rewrite map_app.
        repeat apply incl_tl.
        repeat apply incl_appr. reflexivity. }
    destruct res as [eqs st']. simpl in *.
    apply st_valid_reuse_st_valid in Hvalid. apply st_valid_NoDup in Hvalid.
    specialize (n_nodup n) as Hndup.
    rewrite ps_of_list_ps_to_list_Perm in Hvalid.
    - rewrite fst_NoDupMembers.
      repeat rewrite map_app in *.
      unfold idty, st_ids in *; simpl.
      rewrite <- app_assoc, app_assoc, Permutation_swap, <- app_assoc.
      assert (anon_in_eqs eqs = []).
      { symmetry in Heqres. eapply untuple_equations_no_anon in Heqres; eauto. }
      rewrite H0; simpl. rewrite app_nil_r. assumption.
    - rewrite <- fst_NoDupMembers.
      repeat rewrite app_assoc in *.
      apply NoDupMembers_app_l in Hndup; auto.
  Qed.
  Admit Obligations.

  Fixpoint untuple_global (G : global) (Hwl: wl_global G) : global.
  Proof.
    destruct G as [|hd tl].
    - exact [].
    - refine ((untuple_node hd _)::(untuple_global tl _)).
      + econstructor. inv Hwl; eauto.
      + inv Hwl; eauto.
  Defined.

  (** *** After normalization, a global is normalized *)

  Lemma untuple_node_untupled_node : forall n Hwl,
      untupled_node (untuple_node n Hwl).
  Proof.
    intros n [G Hwl].
    unfold untuple_node.
    unfold untupled_node; simpl.
    eapply untuple_equations_untupled_eq; eauto.
    apply surjective_pairing.
  Qed.

  Lemma untuple_global_untupled_global : forall G Hwl,
      untupled_global (untuple_global G Hwl).
  Proof.
    induction G; intros Hwl; simpl; constructor.
    - apply untuple_node_untupled_node.
    - apply IHG.
  Qed.

  (** *** untuple_global produces an equivalent global *)

  Fact untuple_global_eq : forall G Hwt,
      global_iface_eq G (untuple_global G Hwt).
  Proof.
    induction G; intros Hwt.
    - reflexivity.
    - simpl. apply global_iface_eq_cons; auto.
  Qed.

  Fact untuple_global_names : forall a G Hwt,
      Forall (fun n => (n_name a <> n_name n)%type) G ->
      Forall (fun n => (n_name a <> n_name n)%type) (untuple_global G Hwt).
  Proof.
    induction G; intros Hwt Hnames; simpl.
    - constructor.
    - inv Hnames.
      constructor; eauto.
  Qed.

  (** ** Additional properties *)

  Fact idents_for_anns'_anon_streams : forall anns ids st st',
      idents_for_anns' anns st = (ids, st') ->
      incl (anon_streams anns) (anon_streams (map snd ids)).
  Proof.
    induction anns; intros ids st st' Hids;
      repeat inv_bind; simpl; auto.
    - reflexivity.
    - destruct a as [ty [cl [name|]]]; repeat inv_bind; simpl in *.
      + apply incl_tl'; eauto.
      + eauto.
  Qed.

  Definition without_names' (vars : list (ident * ann)) : list (ident * (Op.type * clock)) :=
    List.map (fun '(id, (ty, (cl, _))) => (id, (ty, cl))) vars.

  Fact idents_for_anns'_anon_streams_incl : forall anns ids st st',
      idents_for_anns' anns st = (ids, st') ->
      incl (anon_streams anns) (without_names' ids).
  Proof.
    induction anns; intros ids st st' Hids;
      repeat inv_bind; simpl; try reflexivity.
    destruct a as [ty [cl [name|]]]; repeat inv_bind; simpl.
    - eapply incl_tl'; eauto.
    - eapply incl_tl; eauto.
  Qed.

  Fact untupled_equation_not_nil : forall G eq,
      untupled_equation eq ->
      wl_equation G eq ->
      fst eq <> [].
  Proof.
    intros * Hunt Hwl contra.
    inv Hunt; simpl in *; subst. 3,4:congruence.
    1,2:(destruct Hwl as [Hwl1 Hwl2]; rewrite app_nil_r in Hwl2; simpl in Hwl2;
         apply Forall_singl in Hwl1; inv Hwl1).
    - specialize (n_outgt0 n) as Hout.
      apply (Nat.lt_irrefl (length (n_out n))). rewrite <- H7 at 1. setoid_rewrite <- Hwl2; auto.
    - specialize (n_outgt0 n) as Hout.
      apply (Nat.lt_irrefl (length (n_out n))). rewrite <- H10 at 1. setoid_rewrite <- Hwl2; auto.
  Qed.

  (** ** fresh_ins appear in the state after normalisation *)

  Fact map_bind2_fresh_incl : forall is_control es es' eqs' st st',
      Forall (fun e => forall es' eqs' st st',
                normalize_exp is_control e st = (es', eqs', st') ->
                incl (fresh_in e) (st_anns st')) es ->
      map_bind2 (normalize_exp is_control) es st = (es', eqs', st') ->
      incl (fresh_ins es) (st_anns st').
  Proof with eauto.
    induction es; intros es' eqs' st st' Hf Hmap;
      repeat inv_bind; try apply incl_nil'.
    inv Hf.
    apply incl_app; eauto.
    etransitivity; eauto.
    apply st_follows_incl; repeat solve_st_follows.
  Qed.

  Fact idents_for_anns'_fresh_incl : forall anns ids st st',
      idents_for_anns' anns st = (ids, st') ->
      incl (anon_streams anns) (st_anns st').
  Proof.
    intros anns ids st st' Hids.
    etransitivity. eapply idents_for_anns'_anon_streams_incl; eauto.
    eapply idents_for_anns'_incl; eauto.
  Qed.

  Fact normalize_exp_fresh_incl : forall e is_control es' eqs' st st',
      normalize_exp is_control e st = (es', eqs', st') ->
      incl (fresh_in e) (st_anns st').
  Proof with eauto.
    induction e using exp_ind2; intros is_control es' eqs' st st' Hnorm;
      repeat inv_bind; eauto.
    - (* const *) apply incl_nil'.
    - (* var *) apply incl_nil'.
    - (* binop *)
      apply incl_app; eauto.
      etransitivity...
    - (* fby *)
      apply incl_app.
      + assert (st_follows x1 st') by repeat solve_st_follows.
        apply map_bind2_fresh_incl in H1. 2:solve_forall.
        etransitivity...
      + assert (st_follows x4 st') by repeat solve_st_follows.
        apply map_bind2_fresh_incl in H2. 2:solve_forall.
        etransitivity...
    - (* when *)
      destruct a; repeat inv_bind.
      apply map_bind2_fresh_incl in H0... solve_forall.
    - (* merge *)
      destruct a; repeat inv_bind.
      assert (st_follows x2 x5) by repeat solve_st_follows.
      apply map_bind2_fresh_incl in H1.
      apply map_bind2_fresh_incl in H2. 2,3:solve_forall.
      assert (st_follows x5 st').
      { destruct is_control; repeat inv_bind; repeat solve_st_follows. }
      eapply incl_app; etransitivity; eauto. etransitivity...
    - (* ite *)
      destruct a; repeat inv_bind.
      assert (st_follows x1 x4) by repeat solve_st_follows.
      assert (st_follows x4 x7) by repeat solve_st_follows.
      eapply IHe in H1.
      eapply map_bind2_fresh_incl in H2.
      eapply map_bind2_fresh_incl in H3. 2,3:solve_forall.
      assert (st_follows x7 st').
      { destruct is_control; repeat inv_bind; repeat solve_st_follows. }
      repeat eapply incl_app; repeat (etransitivity; eauto).
    - (* app *)
      apply map_bind2_fresh_incl in H1. 2:solve_forall.
      assert (st_follows x1 st').
      { destruct ro; repeat inv_bind; repeat solve_st_follows. }
      destruct ro; repeat inv_bind; repeat eapply incl_app.
      1,4:etransitivity; eauto; eapply incl_map; etransitivity; eauto; reflexivity.
      2,3:eapply idents_for_anns'_fresh_incl...
      assert (st_follows x8 st') by repeat solve_st_follows.
      etransitivity...
  Qed.

  Corollary map_bind2_normalize_exp_fresh_incl : forall es is_control es' eqs' st st',
      map_bind2 (normalize_exp is_control) es st = (es', eqs', st') ->
      incl (fresh_ins es) (st_anns st').
  Proof.
    intros es is_control es' eqs' st st' Hmap.
    apply map_bind2_fresh_incl in Hmap; auto.
    solve_forall. apply normalize_exp_fresh_incl in H0; auto.
  Qed.

  Corollary normalize_exps_fresh_incl : forall es es' eqs' st st',
      normalize_exps es st = (es', eqs', st') ->
      incl (fresh_ins es) (st_anns st').
  Proof.
    intros es es' eqs' st st' Hnorm.
    unfold normalize_exps in Hnorm; repeat inv_bind.
    apply map_bind2_normalize_exp_fresh_incl in H; auto.
  Qed.

  (** ** Preservation of clockof *)

  Fact normalize_exp_clockof : forall G e is_control es' eqs' st st',
      wl_exp G e ->
      normalize_exp is_control e st = (es', eqs', st')  ->
      clocksof es' = clockof e.
  Proof with eauto.
    intros vars e is_control es' eqs' st st' Hwl Hnorm.
    eapply normalize_exp_annot in Hnorm...
    rewrite clocksof_annots, Hnorm, <- clockof_annot...
  Qed.
  Hint Resolve normalize_exp_clockof.
End UNTUPLE.

Module UntupleFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Syn : LSYNTAX Ids Op)
       <: UNTUPLE Ids Op OpAux Syn.
  Include UNTUPLE Ids Op OpAux Syn.
End UntupleFun.
