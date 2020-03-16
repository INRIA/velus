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
       (Import Syn : LSYNTAX Ids Op)
       (Import Typ : LTYPING Ids Op Syn).

  (** All the indents currently used in the node *)
  Definition used_idents (n : node) : list ident :=
    reserved ++ map fst (n_in n ++ n_vars n ++ n_out n).

  Definition first_unused_ident (n : node) : ident :=
    Pos.succ (fold_left Pos.max (used_idents n) xH).

  (** Some facts about getting the first unused ident *)

  Fact max_fold_ge : forall l x0,
      (x0 <= (fold_left Pos.max l x0))%positive.
  Proof.
    induction l; intros x0; simpl in *.
    - apply Pos.le_refl.
    - eapply Pos.le_trans.
      2: apply IHl.
      apply Pos.le_max_l.
  Qed.

  Fact max_fold_in : forall x l x0,
      List.In x l ->
      (x <= (fold_left Pos.max l x0))%positive.
  Proof.
    intros x l.
    induction l; intros x0 Hin; simpl in Hin.
    - inversion Hin.
    - destruct Hin as [?|Hin]; subst; simpl.
      + eapply Pos.le_trans.
        2: eapply max_fold_ge.
        apply Pos.le_max_r.
      + apply IHl; eauto.
  Qed.

  Fact first_unused_ident_gt : forall n id,
      first_unused_ident n = id ->
      Forall (fun id' => (id > id')%positive) (used_idents n).
  Proof.
    intros n id Hfirst.
    subst. unfold first_unused_ident.
    rewrite Forall_forall; intros x Hin.
    rewrite Pos.gt_lt_iff.
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

  Fact idents_for_anns_values : forall anns idents st st',
      idents_for_anns anns st = (idents, st') ->
      Forall2 (fun a '(id, a') => a = a') anns idents.
  Proof.
    induction anns; intros idents st st' Hanns; simpl in *.
    - inv Hanns. constructor.
    - repeat inv_bind.
      specialize (IHanns _ _ _ H0).
      constructor; eauto.
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

  (** Normalize a `fby inits es anns` expression, with inits and es already normalized *)
  Definition normalize_fby (inits : list exp) (es : list exp) (anns : list ann) : FreshAnn (list exp * list equation) :=
    do (es, eqs) <- map_bind2 (fun '((init, e), ann) => fby_iteexp init e ann) (combine (combine inits es) anns);
    ret (es, concat eqs).

  Fixpoint normalize_exp (e : exp) {struct e} : FreshAnn (list exp * list equation) :=
    let normalize_exps := fun es => do (es, eqs) <- map_bind2 normalize_exp es; ret (concat es, concat eqs) in
    let normalize_controls := fun es => do (es, eqs) <- map_bind2 normalize_control es; ret (concat es, concat eqs) in
    match e with
    | Econst c => ret ([Econst c], [])
    | Evar v ann => ret ([Evar v ann], [])
    | Eunop op e1 ann =>
      do (e1', eqs) <- normalize_exp e1;
      ret ([Eunop op (hd_default e1') ann], eqs)
    | Ebinop op e1 e2 ann =>
      do (e1', eqs1) <- normalize_exp e1;
      do (e2', eqs2) <- normalize_exp e2;
      ret ([Ebinop op (hd_default e1') (hd_default e2') ann], eqs1++eqs2)
    | Ewhen es clid b (tys, cl) =>
      do (es', eqs) <- normalize_exps es;
      ret (map (fun '(e, ty) => Ewhen [e] clid b ([ty], cl)) (combine es' tys), eqs)
    | Emerge clid es1 es2 (tys, cl) =>
      do (es1', eqs1) <- normalize_controls es1;
      do (es2', eqs2) <- normalize_controls es2;
      let merges := map (fun '((e1, e2), ty) => Emerge clid [e1] [e2] ([ty], cl)) (combine (combine es1' es2') tys) in
      do xs <- idents_for_anns (List.map (fun ty => (ty, cl)) tys);
      ret (List.map (fun '(id, ann) => Evar id ann) xs,
           (combine (List.map (fun '(id, _) => [id]) xs) (List.map (fun e => [e]) merges))++eqs1++eqs2)
    | Eite e es1 es2 (tys, cl) =>
      do (e', eqs0) <- normalize_exp e;
      do (es1', eqs1) <- normalize_controls es1;
      do (es2', eqs2) <- normalize_controls es2;
      let ites := map (fun '((e1, e2), ty) => Eite (hd_default e') [e1] [e2] ([ty], cl)) (combine (combine es1' es2') tys) in
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
                      | Some er => do (er, eqs1) <- normalize_exp er;
                                  match (hd_default er) with
                                  | Evar v ann => ret (Some (Evar v ann), eqs1)
                                  | e => let ann := hd (bool_type, (Cbase, None)) (annot e) in
                                        do x <- fresh_ident (ann, false);
                                        ret (Some (Evar x ann), ([x], [e])::eqs1)
                                  end
                      | None => ret (None, [])
                      end;
      do (es', eqs2) <- normalize_exps es;
      do xs <- idents_for_anns anns;
      ret (List.map (fun '(id, ann) => Evar id ann) xs,
           (List.map fst xs, [Eapp f es' r' anns])::eqs1++eqs2)
    end

  with normalize_control (e : exp) : FreshAnn (list exp * list equation) :=
    let normalize_exps := fun es => do (es, eqs) <- map_bind2 normalize_exp es; ret (concat es, concat eqs) in
    let normalize_controls := fun es => do (es, eqs) <- map_bind2 normalize_control es; ret (concat es, concat eqs) in
    match e with
    | Econst c => ret ([Econst c], [])
    | Evar v ann => ret ([Evar v ann], [])
    | Eunop op e1 ann =>
      do (e1', eqs) <- normalize_exp e1;
      ret ([Eunop op (hd_default e1') ann], eqs)
    | Ebinop op e1 e2 ann =>
      do (e1', eqs1) <- normalize_exp e1;
      do (e2', eqs2) <- normalize_exp e2;
      ret ([Ebinop op (hd_default e1') (hd_default e2') ann], eqs1++eqs2)
    | Ewhen es clid b (tys, cl) =>
      do (es', eqs) <- normalize_exps es;
      ret (map (fun '(e, ty) => Ewhen [e] clid b ([ty], cl)) (combine es' tys), eqs)
    | Emerge clid es1 es2 (tys, cl) =>
      do (es1', eqs1) <- normalize_controls es1;
      do (es2', eqs2) <- normalize_controls es2;
      let merges := map (fun '((e1, e2), ty) => Emerge clid [e1] [e2] ([ty], cl)) (combine (combine es1' es2') tys) in
      ret (merges, eqs1++eqs2)
    | Eite e es1 es2 (tys, cl) =>
      do (e', eqs0) <- normalize_exp e;
      do (es1', eqs1) <- normalize_controls es1;
      do (es2', eqs2) <- normalize_controls es2;
      let ites := map (fun '((e1, e2), ty) => Eite (hd_default e') [e1] [e2] ([ty], cl)) (combine (combine es1' es2') tys) in
      ret (ites, eqs0++eqs1++eqs2)
    | Efby inits es anns =>
      do (inits', eqs1) <- normalize_exps inits;
      do (es', eqs2) <- normalize_exps es;
      do (fbys, eqs3) <- normalize_fby inits' es' anns;
      do xs <- idents_for_anns anns;
      ret (List.map (fun '(x, ann) => Evar x ann) xs,
           (List.map (fun '((x, _), fby) => ([x], [fby])) (combine xs fbys))++eqs1++eqs2++eqs3)
    | Eapp f es r anns =>
      do (r', eqs1) <- match r with
                      | Some er => do (er, eqs1) <- normalize_exp er;
                                  match (hd_default er) with
                                  | Evar v ann => ret (Some (Evar v ann), eqs1)
                                  | e => let ann := hd (bool_type, (Cbase, None)) (annot e) in
                                        do x <- fresh_ident (ann, false);
                                        ret (Some (Evar x ann), ([x], [e])::eqs1)
                                  end
                      | None => ret (None, [])
                      end;
      do (es', eqs2) <- normalize_exps es;
      do xs <- idents_for_anns anns;
      ret (List.map (fun '(id, ann) => Evar id ann) xs,
           (List.map fst xs, [Eapp f es' r' anns])::eqs1++eqs2)
    end.

  Definition normalize_exps (es : list exp) :=
    do (es, eqs) <- map_bind2 normalize_exp es; ret (concat es, concat eqs).
  Definition normalize_controls (es : list exp) :=
    do (es, eqs) <- map_bind2 normalize_control es; ret (concat es, concat eqs).

  Fact normalize_exp_length : forall G vars e st es' eqs' st',
      wt_exp G vars e ->
      normalize_exp e st = ((es', eqs'), st') ->
      length es' = numstreams e.
  Proof.
    intros G vars e.
    rewrite <- numstreams_length_typeof.
    induction e using exp_ind2; intros st es' eqs' st' Hwt Hnorm;
      simpl in *; inv Hwt; inv Hnorm; repeat inv_bind; simpl; auto.
    - (* fby *)
      repeat rewrite map_length.
      apply idents_for_anns_values in H9.
      rewrite Forall2_forall2 in H9; destruct H9; auto.
    - (* when *)
      rewrite map_length.
      apply map_bind2_values in H0.
      assert (Forall2 (fun e x => length x = length (typeof e)) es x1) as Hlen.
      { rewrite Forall_forall in *.
        rewrite Forall3_forall3 in H0; destruct H0 as [Hlen1 [Hlen2 H0]].
        rewrite Forall2_forall2; split; auto.
        intros ? ? ? ? ? Hlen Hnth1 Hnth2; subst.
        specialize (H0 a b0 [] _ _ _ _ Hlen eq_refl eq_refl eq_refl); destruct H0 as [st'' [st''' H0]].
        eapply nth_In in Hlen. eapply H; eauto.
      } clear H H0.
      assert (length (concat x1) = length (typesof es)) as Hlen'.
      { unfold typesof. rewrite flat_map_concat_map.
        induction Hlen; simpl; auto.
        inv H4. repeat rewrite app_length; auto. }
      rewrite combine_length. rewrite Hlen'.
      apply OrdersEx.Nat_as_DT.min_id.
    - (* ite *)
      apply idents_for_anns_values in H3.
      rewrite Forall2_forall2 in H3; destruct H3.
      rewrite map_length in *; auto.
    - (* merge *)
      apply idents_for_anns_values in H4.
      rewrite Forall2_forall2 in H4; destruct H4.
      rewrite map_length in *; auto.
    - (* app *)
      apply idents_for_anns_values in H2.
      rewrite Forall2_forall2 in H2; destruct H2.
      repeat rewrite map_length in *; auto.
    - (* app (reset) *)
      apply idents_for_anns_values in H3.
      rewrite Forall2_forall2 in H3; destruct H3.
      repeat rewrite map_length in *; auto.
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
                      | Some er => do (er, eqs1) <- normalize_exp er;
                                  match (hd_default er) with
                                  | Evar v ann => ret (Some (Evar v ann), eqs1)
                                  | e => let ann := hd (bool_type, (Cbase, None)) (annot e) in
                                        do x <- fresh_ident (ann, false);
                                        ret (Some (Evar x ann), ([x], [e])::eqs1)
                                  end
                      | None => ret (None, [])
                      end;
      do (es', eqs2) <- normalize_exps es;
      ret ([Eapp f es' r' anns], eqs1++eqs2)
    | _ => normalize_control e
    end.
  Definition normalize_tops (es : list exp) :=
    do (es, eqs) <- map_bind2 normalize_top es; ret (concat es, concat eqs).

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

  Definition normalize_equations (eqs : list equation) : FreshAnn (list equation) :=
    fold_left (fun eqs eq => do eqs <- eqs;
                          do eqs' <- (normalize_equation eq);
                          ret (eqs++eqs')) eqs (ret nil).

  (** Normalization of a full node *)
  Program Definition normalize_node (n : node) : node :=
    let id0 := first_unused_ident n in
    let '(eqs, (_, nvars)) := (normalize_equations (n_eqs n)) (id0, nil) in
    let nvars := (List.map (fun '(id, ann) => let '(ann, _) := ann in
                                           let '(ty, cl) := ann in
                                           let '(cl, _) := cl in (id, (ty, cl))) nvars) in
    {| n_name := (n_name n);
       n_hasstate := (n_hasstate n);
       n_in := (n_in n);
       n_out := (n_out n);
       n_vars := (n_vars n)++nvars;
       n_eqs := eqs;
       n_ingt0 := (n_ingt0 n);
       n_outgt0 := (n_outgt0 n);
    |}.
  Admit Obligations.

  Definition normalize_global (G : global) : global :=
    List.map normalize_node G.
End NORM.

Module NormFun
       (Ids : IDS)
       (Op : OPERATORS)
       (Syn : LSYNTAX Ids Op)
       (Typ : LTYPING Ids Op Syn) <: NORM Ids Op Syn Typ.
  Include NORM Ids Op Syn Typ.
End NormFun.
