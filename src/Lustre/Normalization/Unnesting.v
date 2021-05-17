From Coq Require Import List Sorting.Permutation.
Import List.ListNotations.
Open Scope list_scope.
Require Import Omega.

From Coq Require Import Setoid Morphisms.

From Velus Require Import Common Environment.
From Velus Require Import Operators.
From Velus Require Import Lustre.LSyntax.
From Velus Require Lustre.Normalization.Fresh.

(** * Normalization procedure *)

Module Type UNNESTING
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Import Syn : LSYNTAX Ids Op).

  Module Fresh := Fresh.Fresh(Ids).
  Export Fresh.
  Import Fresh Notations Facts Tactics.
  Local Open Scope fresh_monad_scope.

  (** ** Some additional tactics *)

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
    | H : In ?x (idty ?l) |- _ =>
      rewrite In_idty_exists in H; destruct H as (?&?); subst
    | H : In ?x (idck ?l) |- _ =>
      rewrite In_idck_exists in H; destruct H as (?&?); subst
    | |- In ?x (map ?f ?l) => rewrite in_map_iff
    | |- In ?x (idty ?l) => rewrite In_idty_exists
    | |- In ?x (idck ?l) => rewrite In_idck_exists
    end.

  (** Simplify an expression with maps and other stuff... *)
  Ltac simpl_list :=
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

  Ltac ndup_simpl :=
    repeat rewrite map_app, <- app_assoc in *.
  Ltac ndup_l H :=
    ndup_simpl;
    rewrite Permutation_swap in H;
    apply NoDup_app_r in H; auto.
  Ltac ndup_r H :=
    ndup_simpl;
    apply NoDup_app_r in H; auto.

  Definition default_ann : ann := (Op.bool_type, (Cbase, None)).

  (** Fresh ident generation keeping type annotations *)
  Definition FreshAnn A := Fresh A (type * clock).

  Definition hd_default (l : list exp) : exp :=
    hd (Econst (init_type bool_type)) l.

  Fixpoint idents_for_anns (anns : list ann) : FreshAnn (list (ident * ann)) :=
    match anns with
    | [] => ret []
    | (ty, (cl, name))::tl => do x <- fresh_ident norm1 (ty, cl);
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
    | (ty, (ck, None))::tl => do x <- fresh_ident norm1 (ty, ck);
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

  Definition unnest_reset k (e : exp) : FreshAnn (exp * list equation) :=
      do (e', eqs1) <- k e;
      match hd_default e' with
      | Evar v ann => ret (Evar v ann, eqs1)
      | e => let '(ty, (ck, _)) := hd (bool_type, (Cbase, None)) (annot e) in
            do x <- fresh_ident norm1 (ty, ck);
            ret (Evar x (ty, (ck, Some x)), ([x], [e])::eqs1)
      end.

  Lemma unnest_reset_spec : forall k e es' eqs' st st',
      k e st = ((es', eqs'), st') ->
      (exists v, exists ann, (hd_default es') = Evar v ann /\ unnest_reset k e st = ((Evar v ann, eqs'), st'))
      \/ exists ty ck o x st'', hd (bool_type, (Cbase, None)) (annot (hd_default es')) = (ty, (ck, o)) /\
                          fresh_ident norm1 (ty, ck) st' = (x, st'') /\
                          unnest_reset k e st = ((Evar x (ty, (ck, Some x)), ([x], [hd_default es'])::eqs'), st'').
  Proof.
    intros * Hk.
    unfold unnest_reset; simpl.
    destruct (hd_default es') eqn:Hes'.
    1,3-10:
      (right; destruct (hd _) as [ty [ck ?]] eqn:Hx; simpl;
       destruct (fresh_ident norm1 (ty, ck) st') as [x st''] eqn:Hfresh;
       repeat eexists; eauto; repeat inv_bind;
       repeat eexists; eauto;
       rewrite Hes'; try rewrite Hx;
       repeat inv_bind; repeat eexists; eauto;
       repeat inv_bind; eauto).
    - left. repeat eexists.
      inv_bind; repeat eexists; eauto. rewrite Hes'; inv_bind; eauto.
  Qed.

  Ltac unnest_reset_spec :=
    match goal with
    | H:unnest_reset ?k ?e ?st = (?res, ?st') |- _ =>
      let Hk := fresh "Hk" in let Hk' := fresh "Hk" in
                              let Hhd := fresh "Hhd" in
                              let Hfresh := fresh "Hfresh" in
                              let Hnorm' := fresh "Hnorm" in
                              destruct (k e st) as [[? ?] ?] eqn:Hk;
                              assert (Hk' := Hk);
                              eapply unnest_reset_spec in Hk as [[? [[? [? ?]] [? Hnorm']]]|[? [? [? [? [? [Hhd [Hfresh Hnorm']]]]]]]]; subst;
                              rewrite Hnorm' in H; clear Hnorm'; inv H
    end.

  Definition unnest_fby (e0s : list exp) (es : list exp) ro (anns : list ann) :=
    map (fun '((e0, e), a) => Efby [e0] [e] ro [a]) (combine (combine e0s es) anns).

  Definition unnest_arrow (e0s : list exp) (es : list exp) ro (anns : list ann) :=
    map (fun '((e0, e), a) => Earrow [e0] [e] ro [a]) (combine (combine e0s es) anns).

  Definition unnest_when ckid b es tys ck :=
    map (fun '(e, ty) => Ewhen [e] ckid b ([ty], ck)) (combine es tys).

  Definition unnest_merge ckid ets efs tys ck :=
    map (fun '((e1, e2), ty) => Emerge ckid [e1] [e2] ([ty], ck)) (combine (combine ets efs) tys).

  Definition unnest_ite e ets efs tys ck :=
    map (fun '((et, ef), ty) => Eite e [et] [ef] ([ty], ck)) (combine (combine ets efs) tys).

  Hint Unfold unnest_when unnest_merge unnest_ite.

  Fixpoint is_noops_exp (ck: clock) (e : exp) : bool :=
    match ck with
    | Cbase => true
    | Con ck' _ _ =>
      match e with
      | Econst _ | Evar _ _ => true
      | Ewhen [e'] _ _ _ => is_noops_exp ck' e'
      | _ => false
      end
    end.

  Definition find_node_incks G (f : ident) : list clock :=
    match find_node f G with
    | Some n => map (fun '(_, (_, ck)) => ck) (n_in n)
    | None => []
    end.

  Definition unnest_noops_exp (cki: clock) (e : exp) : FreshAnn (exp * list equation) :=
    let '(ty, (ck, o)) := hd (bool_type, (Cbase, None)) (annot e) in
    if is_noops_exp cki e then ret (e, [])
    else do x <- fresh_ident norm1 (ty, ck);
         ret (Evar x (ty, (ck, o)), [([x], [e])]).

  Definition unnest_noops_exps (ckis : list clock) (es : list exp) : FreshAnn (list exp * list equation) :=
    do (es', eqs') <- map_bind2 (fun '(cki, e) => unnest_noops_exp cki e) (combine ckis es);
    ret (es', concat eqs').

  Fixpoint unnest_exp G (is_control : bool) (e : exp) {struct e} : FreshAnn (list exp * list equation) :=
    let unnest_exps := fun es => do (es, eqs) <- map_bind2 (unnest_exp G false) es; ret (concat es, concat eqs) in
    let unnest_controls := fun es => do (es, eqs) <- map_bind2 (unnest_exp G true) es; ret (concat es, concat eqs) in
    let unnest_resets := fun es => do (es, eqs) <- map_bind2 (unnest_reset (unnest_exp G true)) es; ret (es, concat eqs) in
    match e with
    | Econst c => ret ([Econst c], [])
    | Evar v ann => ret ([Evar v ann], [])
    | Eunop op e1 ann =>
      do (e1', eqs) <- unnest_exp G false e1;
      ret ([Eunop op (hd_default e1') ann], eqs)
    | Ebinop op e1 e2 ann =>
      do (e1', eqs1) <- unnest_exp G false e1;
      do (e2', eqs2) <- unnest_exp G false e2;
      ret ([Ebinop op (hd_default e1') (hd_default e2') ann], eqs1++eqs2)
    | Efby e0s es er anns =>
      do (e0s', eqs1) <- unnest_exps e0s;
      do (es', eqs2) <- unnest_exps es;
      do (er', eqs3) <- unnest_resets er;
      let fbys := unnest_fby e0s' es' er' anns in
      do xs <- idents_for_anns anns;
      ret (List.map (fun '(x, ann) => Evar x ann) xs,
           (List.map (fun '((x, _), fby) => ([x], [fby])) (combine xs fbys))++eqs1++eqs2++eqs3)
    | Earrow e0s es er anns =>
      do (e0s', eqs1) <- unnest_exps e0s;
      do (es', eqs2) <- unnest_exps es;
      do (er', eqs3) <- unnest_resets er;
      let arrows := unnest_arrow e0s' es' er' anns in
      do xs <- idents_for_anns anns;
      ret (List.map (fun '(x, ann) => Evar x ann) xs,
           (List.map (fun '((x, _), arrow) => ([x], [arrow])) (combine xs arrows))++eqs1++eqs2++eqs3)
    | Ewhen es ckid b (tys, ck) =>
      do (es', eqs) <- unnest_exps es;
      ret (unnest_when ckid b es' tys ck, eqs)
    | Emerge ckid es1 es2 (tys, cl) =>
      do (es1', eqs1) <- unnest_controls es1;
      do (es2', eqs2) <- unnest_controls es2;
      let merges := unnest_merge ckid es1' es2' tys cl in
      if is_control then
        ret (merges, eqs1++eqs2)
      else
        do xs <- idents_for_anns (List.map (fun ty => (ty, cl)) tys);
        ret (List.map (fun '(id, ann) => Evar id ann) xs,
             (combine (List.map (fun '(id, _) => [id]) xs) (List.map (fun e => [e]) merges))++eqs1++eqs2)
    | Eite e es1 es2 (tys, ck) =>
      do (e', eqs0) <- unnest_exp G false e;
      do (es1', eqs1) <- unnest_controls es1;
      do (es2', eqs2) <- unnest_controls es2;
      let ites :=  unnest_ite (hd_default e') es1' es2' tys ck in
      if is_control then
        ret (ites, eqs0++eqs1++eqs2)
      else
        do xs <- idents_for_anns (List.map (fun ty => (ty, ck)) tys);
        ret (List.map (fun '(id, ann) => Evar id ann) xs,
             (combine (List.map (fun '(id, _) => [id]) xs) (List.map (fun e => [e]) ites))++eqs0++eqs1++eqs2)
    | Eapp f es er anns =>
      do (es', eqs1) <- unnest_exps es;
      do (es', eqs2) <- unnest_noops_exps (find_node_incks G f) es';
      do (er', eqs3) <- unnest_resets er;
      do xs <- idents_for_anns' anns;
      ret (List.map (fun '(id, ann) => Evar id ann) xs,
           (List.map fst xs, [Eapp f es' er' (List.map snd xs)])::eqs1++eqs2++eqs3)
    end.

  Definition unnest_exps G (es : list exp) :=
    do (es, eqs) <- map_bind2 (unnest_exp G false) es;
    ret (concat es, concat eqs).

  Definition unnest_rhs G (e : exp) : FreshAnn (list exp * list equation) :=
    let unnest_resets := fun es => do (es, eqs) <- map_bind2 (unnest_reset (unnest_exp G true)) es; ret (es, concat eqs) in
    match e with
    | Eapp f es er anns =>
      do (es', eqs1) <- unnest_exps G es;
      do (es', eqs2) <- unnest_noops_exps (find_node_incks G f) es';
      do (er', eqs3) <- unnest_resets er;
      ret ([Eapp f es' er' anns], eqs1++eqs2++eqs3)
    | Efby e0s es er anns =>
      do (e0s', eqs1) <- unnest_exps G e0s;
      do (es', eqs2) <- unnest_exps G es;
      do (er', eqs3) <- unnest_resets er;
      let fbys := unnest_fby e0s' es' er' anns in
      ret (fbys, eqs1++eqs2++eqs3)
    | Earrow e0s es er anns =>
      do (e0s', eqs1) <- unnest_exps G e0s;
      do (es', eqs2) <- unnest_exps G es;
      do (er', eqs3) <- unnest_resets er;
      let arrows := unnest_arrow e0s' es' er' anns in
      ret (arrows, eqs1++eqs2++eqs3)
    | _ => unnest_exp G true e
    end.

  Definition unnest_rhss G (es : list exp) :=
    do (es, eqs) <- map_bind2 (unnest_rhs G) es; ret (concat es, concat eqs).

  Fixpoint combine_for_numstreams {B} (es : list exp) (vs : list B) :=
    match es with
    | [] => []
    | hd::tl => let n := numstreams hd in
              (hd, (firstn n vs))::(combine_for_numstreams tl (skipn n vs))
    end.

  Definition split_equation (eq : equation) : list equation :=
    let (xs, es) := eq in
    List.map (fun '(e, xs) => (xs, [e])) (combine_for_numstreams es xs).

  Definition unnest_equation G (e : equation) : FreshAnn (list equation) :=
    let '(xs, es) := e in
    do (es', eqs) <- unnest_rhss G es;
    ret ((split_equation (xs, es'))++eqs).

  Definition unnest_equations G (eqs : list equation) : FreshAnn (list equation) :=
    do eqs <- map_bind (unnest_equation G) eqs;
    ret (concat eqs).

  Definition unnest_equations' G (eq : list equation) (st : fresh_st (type * clock)) :
    { res | unnest_equations G eq st = res }.
  Proof.
    remember (unnest_equations G eq st) as eqs'.
    econstructor; eauto.
  Defined.

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
      st_valid_after st norm1 aft ->
      st_valid_after st' norm1 aft.
  Proof.
    induction anns; intros * Hidforanns Hvalid;
      repeat inv_bind.
    - assumption.
    - destruct a as [ty [cl name]]. repeat inv_bind.
      eapply IHanns; eauto.
  Qed.
  Hint Resolve idents_for_anns_st_valid_after.

  (** ** Propagation of the st_valid_reuse property *)

  Definition elab_prefs := PS.singleton elab.
  Definition st_valid_reuse {B} st aft reusable := @st_valid_reuse B st norm1 aft elab_prefs reusable.
  Hint Unfold st_valid_reuse.

  Fact idents_for_anns_st_valid_reuse : forall anns res st st' aft reusable,
      idents_for_anns anns st = (res, st') ->
      st_valid_reuse st aft reusable ->
      st_valid_reuse st' aft reusable.
  Proof.
    induction anns; intros * Hidanns Hvalid;
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
    induction anns; intros * HND Hidforanns Hvalid;
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

  Fact unnest_reset_st_valid : forall k e e' eqs' st st' aft reu,
      (forall res st st',
        k e st = (res, st') ->
        st_valid_reuse st aft (ps_adds (map fst (fresh_in e)) reu) ->
        st_valid_reuse st' aft reu) ->
      unnest_reset k e st = (e', eqs', st') ->
      st_valid_reuse st aft (ps_adds (map fst (fresh_in e)) reu) ->
      st_valid_reuse st' aft reu.
  Proof.
    intros * Hkvalid Hnorm Hvalid.
    unnest_reset_spec; simpl in *; eauto.
    eapply fresh_ident_st_valid_reuse, Hkvalid; eauto.
  Qed.
  Hint Resolve unnest_reset_st_valid.

  Fact unnest_noops_exp_st_valid : forall e ck e' eqs' st st' aft reu,
      unnest_noops_exp ck e st = (e', eqs', st') ->
      st_valid_reuse st aft reu ->
      st_valid_reuse st' aft reu.
  Proof.
    intros * Hun Hval.
    unfold unnest_noops_exp in Hun.
    destruct (hd _ _) as (?&?&?), is_noops_exp; repeat inv_bind; eauto.
  Qed.

  Fact unnest_noops_exps_st_valid : forall es ckis es' eqs' st st' aft reu,
      unnest_noops_exps ckis es st = (es', eqs', st') ->
      st_valid_reuse st aft reu ->
      st_valid_reuse st' aft reu.
  Proof.
    unfold unnest_noops_exps.
    intros * Hun Hval.
    repeat inv_bind.
    eapply map_bind2_st_valid_reuse; eauto.
    eapply Forall_forall. intros (?&?) _ * Hun Hval'.
    eapply unnest_noops_exp_st_valid; eauto.
  Qed.

  Fact map_bind2_st_valid_reuse' {A B} :
    forall (k : exp -> list (ident * B)) (f : exp -> FreshAnn (A * list equation)) es es' eqs' st st' aft reusable,
      Forall (fun e =>
                forall es' eqs' st st' aft reusable,
                  NoDup (map fst (k e)++PS.elements reusable) ->
                  f e st = (es', eqs', st') ->
                  st_valid_reuse st aft (ps_adds (map fst (k e)) reusable) ->
                  st_valid_reuse st' aft reusable) es ->
      NoDup (map fst (flat_map k es)++PS.elements reusable) ->
      map_bind2 f es st = (es', eqs', st') ->
      st_valid_reuse st aft (ps_adds (map fst (flat_map k es)) reusable) ->
      st_valid_reuse st' aft reusable.
  Proof.
    induction es; intros es' eqs' st st' aft reusable Hf Hnd Hmap Hvalid;
      repeat inv_bind; auto.
    inv Hf.
    ndup_simpl.
    assert (NoDup (map fst (k a)++PS.elements reusable)) by ndup_l Hnd.
    assert (NoDup (map fst (flat_map k es)++PS.elements reusable)) by ndup_r Hnd.
    unfold st_valid_reuse in *.
    rewrite ps_adds_app in Hvalid; eauto.
    eapply IHes in H4; eauto. eapply H3; eauto.
    rewrite Permutation_PS_elements_ps_adds'; eauto.
  Qed.

  Local Ltac solve_st_valid :=
    match goal with
    | H : map_bind2 _ _ _ = (_, _, ?st) |- st_valid_reuse ?st _ _ =>
      eapply map_bind2_st_valid_reuse' in H; eauto; solve_forall
    | H : unnest_reset _ _ = (_, _, ?st) |- st_valid_reuse ?st _ _ =>
      eapply unnest_reset_st_valid; eauto
    | H : unnest_noops_exps _ _ _ = (_, _, ?st) |- st_valid_reuse ?st _ _ =>
      eapply unnest_noops_exps_st_valid; eauto
    | H : idents_for_anns _ _ = (_, ?st) |- st_valid_reuse ?st _ _ =>
      eapply idents_for_anns_st_valid_reuse; eauto
    | H : idents_for_anns' _ _ = (_, ?st) |- st_valid_reuse ?st _ _ =>
      eapply idents_for_anns'_st_valid; eauto
    end.

  Global Add Parametric Morphism {B} st aft : (@st_valid_reuse B st aft)
      with signature @PS.eq ==> Basics.impl
        as st_valid_reuse_PSeq_Proper.
  Proof.
    intros. intro Hv.
    eapply st_valid_reuse_PSeq; eauto.
  Qed.

  Fact unnest_exp_st_valid : forall G e is_control res st st' aft reusable,
      NoDup (map fst (fresh_in e)++PS.elements reusable) ->
      unnest_exp G is_control e st = (res, st') ->
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
      assert (NoDup (map fst (fresh_ins e0s)++PS.elements reusable)) by (repeat ndup_l Hnd).
      assert (NoDup (map fst (fresh_ins es)++PS.elements reusable)) by (rewrite Permutation_swap in Hnd; repeat ndup_l Hnd).
      repeat rewrite ps_adds_app in Hvalid.
      eapply map_bind2_st_valid_reuse' in H4; eauto.
      1:{ eapply Forall_impl; [|eapply H1]. intros.
          eapply unnest_reset_st_valid in H10; eauto. }
      repeat ndup_r Hnd.
      repeat solve_st_valid.
      2:rewrite Permutation_swap in Hnd.
      1,2:repeat rewrite Permutation_PS_elements_ps_adds'; auto.
      1,2:repeat ndup_r Hnd.
      1,3:rewrite Permutation_swap in Hnd; auto.
      1-3:repeat ndup_r Hnd.
    - (* fby *)
      repeat inv_bind. ndup_simpl.
      assert (NoDup (map fst (fresh_ins e0s)++PS.elements reusable)) by (repeat ndup_l Hnd).
      assert (NoDup (map fst (fresh_ins es)++PS.elements reusable)) by (rewrite Permutation_swap in Hnd; repeat ndup_l Hnd).
      repeat rewrite ps_adds_app in Hvalid.
      eapply map_bind2_st_valid_reuse' in H4; eauto.
      1:{ eapply Forall_impl; [|eapply H1]. intros.
          eapply unnest_reset_st_valid in H10; eauto. }
      repeat ndup_r Hnd.
      repeat solve_st_valid.
      2:rewrite Permutation_swap in Hnd.
      1,2:repeat rewrite Permutation_PS_elements_ps_adds'; auto.
      1,2:repeat ndup_r Hnd.
      1,3:rewrite Permutation_swap in Hnd; auto.
      1-3:repeat ndup_r Hnd.
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
      repeat inv_bind.
      eapply idents_for_anns'_st_valid; eauto. repeat ndup_r Hnd.
      eapply map_bind2_st_valid_reuse' in H3; eauto.
      1:{ eapply Forall_impl; [|eapply H0]. intros.
          eapply unnest_reset_st_valid in H7; eauto. }
      rewrite Permutation_PS_elements_ps_adds'. 1,2:repeat ndup_r Hnd.
      repeat solve_st_valid.
      2:repeat rewrite map_app, ps_adds_app in *; eauto.
      repeat rewrite Permutation_PS_elements_ps_adds'; eauto.
      1-4:try (solve [repeat ndup_r Hnd]).
      1:repeat rewrite map_app, <- app_assoc in *; auto.
  Qed.
  Hint Resolve unnest_exp_st_valid.

  Fact unnest_rhs_st_valid : forall G e res st st' aft reusable,
      NoDup (map fst (anon_in e)++PS.elements reusable) ->
      unnest_rhs G e st = (res, st') ->
      st_valid_reuse st aft (ps_adds (map fst (anon_in e)) reusable) ->
      st_valid_reuse st' aft reusable.
  Proof.
    intros * Hnd Hnorm Hvalid.
    destruct e; try (solve [eapply unnest_exp_st_valid in Hnorm; eauto]);
      simpl in *; unfold unnest_exps in *.
    - (* fby *)
      ndup_simpl.
      repeat inv_bind.
      eapply map_bind2_st_valid_reuse' in H1; eauto.
      1:{ eapply Forall_forall; intros.
          eapply unnest_reset_st_valid in H4; eauto. } repeat ndup_r Hnd.
      repeat rewrite ps_adds_app in Hvalid; repeat solve_st_valid.
      1,2:repeat rewrite Permutation_PS_elements_ps_adds'; eauto.
      1-7:repeat ndup_r Hnd.
    - (* arrow *)
      ndup_simpl.
      repeat inv_bind.
      eapply map_bind2_st_valid_reuse' in H1; eauto.
      1:{ eapply Forall_forall; intros.
          eapply unnest_reset_st_valid in H4; eauto. } repeat ndup_r Hnd.
      repeat rewrite ps_adds_app in Hvalid; repeat solve_st_valid.
      1,2:repeat rewrite Permutation_PS_elements_ps_adds'; eauto.
      1-7:repeat ndup_r Hnd.
    - (* app *)
      repeat inv_bind.
      eapply map_bind2_st_valid_reuse' in H1; eauto.
      1:{ eapply Forall_forall; intros.
          eapply unnest_reset_st_valid in H4; eauto. } repeat ndup_r Hnd.
      repeat solve_st_valid.
      2:rewrite <- ps_adds_app, <- map_app; auto.
      rewrite Permutation_PS_elements_ps_adds'.
      rewrite map_app, <- app_assoc in Hnd; auto.
      ndup_r Hnd.
  Qed.
  Hint Resolve unnest_rhs_st_valid.

  Fact unnest_equation_st_valid : forall G e res st st' aft reusable,
      NoDup (map fst (anon_in_eq e)++PS.elements reusable) ->
      unnest_equation G e st = (res, st') ->
      st_valid_reuse st aft (ps_adds (map fst (anon_in_eq e)) reusable) ->
      st_valid_reuse st' aft reusable.
  Proof.
    intros G [xs es] * Hnd Hnorm Hvalid.
    unfold anon_in_eq in Hnd.
    simpl in *; unfold unnest_rhss in *; repeat inv_bind.
    eapply map_bind2_st_valid_reuse' in H; eauto.
    apply Forall_forall. intros; eauto.
  Qed.
  Hint Resolve unnest_equation_st_valid.

  Fact unnest_equations_st_valid : forall G eqs res st st' aft reusable,
      NoDup (map fst (anon_in_eqs eqs)++PS.elements reusable) ->
      unnest_equations G eqs st = (res, st') ->
      st_valid_reuse st aft (ps_adds (map fst (anon_in_eqs eqs)) reusable) ->
      st_valid_reuse st' aft reusable.
  Proof.
    induction eqs; intros * Hndup Hnorm Hvalid;
      unfold unnest_equations in Hnorm; repeat inv_bind; auto.
    - unfold anon_in_eqs in *; simpl in *.
      ndup_simpl.
      rewrite ps_adds_app in Hvalid.
      eapply IHeqs; eauto. 1:ndup_r Hndup.
      unfold unnest_equations; repeat inv_bind; repeat eexists; eauto; inv_bind; eauto.
      eapply unnest_equation_st_valid; eauto.
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
    2: (eapply map_ext; intros [? [? [? ?]]]; auto).
    assumption.
  Qed.

  Fact unnest_reset_st_follows' : forall k e res st st',
      (forall res st st',
          k e st = (res, st') ->
          st_follows st st') ->
      unnest_reset k e st = (res, st') ->
      st_follows st st'.
  Proof.
    intros * Hkfollow Hnorm.
    unnest_reset_spec; eauto.
    etransitivity; eapply fresh_ident_st_follows in Hfresh; eauto.
  Qed.
  Hint Resolve unnest_reset_st_follows'.

  Lemma unnest_noops_exp_st_follows : forall e ck e' eqs' st st' ,
      unnest_noops_exp ck e st = (e', eqs', st') ->
      st_follows st st'.
  Proof.
    intros * Hun.
    unfold unnest_noops_exp in Hun.
    destruct (hd _ _) as (?&?&?).
    destruct (is_noops_exp _ _); repeat inv_bind; eauto.
    reflexivity.
  Qed.
  Hint Resolve unnest_noops_exp_st_follows.

  Lemma unnest_noops_exps_st_follows : forall es ckis es' eqs' st st' ,
      unnest_noops_exps ckis es st = (es', eqs', st') ->
      st_follows st st'.
  Proof.
    intros * Hun. unfold unnest_noops_exps in Hun.
    repeat inv_bind.
    eapply map_bind2_st_follows; eauto.
    eapply Forall_forall. intros (?&?) _ * Hun; eauto.
  Qed.
  Hint Resolve unnest_noops_exps_st_follows.

  Local Ltac solve_st_follows' :=
    match goal with
    | |- st_follows ?st ?st =>
      reflexivity
    | H : st_follows ?st1 ?st2 |- st_follows ?st1 _ =>
      etransitivity; [eapply H |]
    | H : fresh_ident _ _ ?st = _ |- st_follows ?st _ =>
      etransitivity; [ eapply fresh_ident_st_follows in H; eauto | ]
    | H : reuse_ident _ _ ?st = _ |- st_follows ?st _ =>
      etransitivity; [ eapply reuse_ident_st_follows in H; eauto | ]
    | H : idents_for_anns _ ?st = _ |- st_follows ?st _ =>
      etransitivity; [ eapply idents_for_anns_st_follows in H; eauto | ]
    | H : idents_for_anns' _ ?st = _ |- st_follows ?st _ =>
      etransitivity; [ eapply idents_for_anns'_st_follows in H; eauto | ]
    | H : unnest_reset _ _ ?st = _ |- st_follows ?st _ =>
      etransitivity; [ eapply unnest_reset_st_follows' in H; eauto | ]
    | H : unnest_noops_exps _ _ ?st = _ |- st_follows ?st _ =>
      etransitivity; [ eapply unnest_noops_exps_st_follows in H; eauto | ]
    | H : map_bind2 _ _ ?st = _ |- st_follows ?st _ =>
      etransitivity; [ eapply map_bind2_st_follows in H; eauto; solve_forall | ]
    end.

  Fact unnest_exp_st_follows : forall G e is_control res st st',
      unnest_exp G is_control e st = (res, st') ->
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
    - (* arrow *)
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
      repeat inv_bind.
      etransitivity; eauto. repeat solve_st_follows'.
  Qed.
  Hint Resolve unnest_exp_st_follows.

  Corollary unnest_exps_st_follows : forall G es res st st',
      unnest_exps G es st = (res, st') ->
      st_follows st st'.
  Proof.
    intros * Hnorm.
    unfold unnest_exps in Hnorm. repeat inv_bind.
    eapply map_bind2_st_follows; eauto.
    rewrite Forall_forall; intros; eauto.
  Qed.

  Fact unnest_rhs_st_follows : forall G e res st st',
      unnest_rhs G e st = (res, st') ->
      st_follows st st'.
  Proof.
    intros * Hnorm.
    destruct e; try (solve [eapply unnest_exp_st_follows; eauto]);
      simpl in Hnorm; unfold unnest_exps in *.
    1,2,3:
      repeat inv_bind;
      repeat solve_st_follows';
      destruct o; simpl; eauto.
  Qed.
  Hint Resolve unnest_rhs_st_follows.

  Corollary unnest_rhss_st_follows : forall G es res st st',
      unnest_rhss G es st = (res, st') ->
      st_follows st st'.
  Proof.
    intros * Hnorm.
    unfold unnest_rhss in Hnorm; repeat inv_bind.
    repeat solve_st_follows'.
  Qed.
  Hint Resolve unnest_rhss_st_follows.

  Fact unnest_equation_st_follows : forall G e res st st',
      unnest_equation G e st = (res, st') ->
      st_follows st st'.
  Proof.
    intros G [xs es] * Hnorm.
    simpl in *; repeat inv_bind; eauto.
  Qed.
  Hint Resolve unnest_equation_st_follows.

  Fact unnest_equations_st_follows : forall G eqs res st st',
      unnest_equations G eqs st = (res, st') ->
      st_follows st st'.
  Proof.
    intros * Hnorm.
    unfold unnest_equations in Hnorm; repeat inv_bind.
    eapply map_bind_st_follows; eauto.
    solve_forall.
  Qed.

  Fact unnest_reset_st_follows : forall G b e res st st',
      unnest_reset (unnest_exp G b) e st = (res, st') ->
      st_follows st st'.
  Proof.
    intros * Hunn.
    apply unnest_reset_st_follows' in Hunn; auto.
    intros. eapply unnest_exp_st_follows; eauto.
  Qed.

  (** ** Length of unnested expression *)

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

  Fact map_bind2_length : forall G is_control es es' eqs' st st',
      Forall2 (fun e es' => forall eqs' st st',
                   unnest_exp G is_control e st = (es', eqs', st') ->
                   length es' = numstreams e) es es' ->
      map_bind2 (unnest_exp G is_control) es st = (es', eqs', st') ->
      length (concat es') = length (annots es).
  Proof.
    intros * Hf Hmap.
    apply map_bind2_values in Hmap.
    repeat simpl_list.
    apply concat_length_eq.
    rewrite Forall2_map_2, Forall2_swap_args.
    eapply Forall3_ignore3, Forall2_Forall2 in Hmap; [| eapply Hf]. clear Hf.
    eapply Forall2_impl_In; eauto.
    intros ? ? _ _ [H1 [? [? [? H2]]]]. rewrite length_annot_numstreams; eauto.
  Qed.

  Local Hint Resolve nth_In.
  Fact unnest_exp_length : forall G e is_control es' eqs' st st',
      wl_exp G e ->
      unnest_exp G is_control e st = (es', eqs', st') ->
      length es' = numstreams e.
  Proof with eauto.
    induction e using exp_ind2; intros is_control es' eqs' st st' Hwl Hnorm;
      simpl in *; inv Hwl; repeat inv_bind; auto.
    - (* fby *)
      simpl in *. rewrite map_length.
      apply idents_for_anns_length in H5...
    - (* arrow *)
      simpl in *. rewrite map_length.
      apply idents_for_anns_length in H5...
    - (* when *)
      unfold unnest_when. rewrite map_length.
      eapply map_bind2_length in H0.
      + solve_length.
      + eapply map_bind2_values in H0.
        repeat rewrite_Forall_forall...
    - (* merge *)
      destruct is_control; repeat inv_bind; unfold unnest_merge.
      + apply map_bind2_length in H1; [| eapply map_bind2_values in H1; repeat rewrite_Forall_forall; eauto].
        apply map_bind2_length in H2; [| eapply map_bind2_values in H2; repeat rewrite_Forall_forall; eauto].
        solve_length.
      + apply idents_for_anns_length in H3. solve_length.
    - (* ite *)
      destruct is_control; repeat inv_bind; unfold unnest_ite.
      + apply map_bind2_length in H2; [| eapply map_bind2_values in H2; repeat rewrite_Forall_forall; eauto].
        apply map_bind2_length in H3; [| eapply map_bind2_values in H3; repeat rewrite_Forall_forall; eauto].
        solve_length.
      + apply idents_for_anns_length in H4. solve_length.
    - (* app (reset) *)
      apply idents_for_anns'_length in H4.
      solve_length.
  Qed.
  Hint Resolve unnest_exp_length.

  Corollary map_bind2_unnest_exp_length : forall G is_control es es' eqs' st st',
      Forall (wl_exp G) es ->
      map_bind2 (unnest_exp G is_control) es st = (es', eqs', st') ->
      length (concat es') = length (annots es).
  Proof.
    intros * Hf Hmap.
    eapply map_bind2_length; eauto.
    eapply map_bind2_values in Hmap.
    repeat rewrite_Forall_forall.
    eapply unnest_exp_length; eauto.
  Qed.
  Hint Resolve map_bind2_unnest_exp_length.

  Corollary unnest_exps_length : forall G es es' eqs' st st',
      Forall (wl_exp G) es ->
      unnest_exps G es st = (es', eqs', st') ->
      length es' = length (annots es).
  Proof.
    intros * Hwt Hnorm.
    unfold unnest_exps in Hnorm.
    repeat inv_bind.
    eapply map_bind2_unnest_exp_length; eauto.
  Qed.
  Hint Resolve unnest_exps_length.

  Fact unnest_fby_length : forall e0s es er anns,
      length e0s = length anns ->
      length es = length anns ->
      length (unnest_fby e0s es er anns) = length anns.
  Proof.
    intros * Hl1 Hl2.
    unfold unnest_fby. solve_length.
  Qed.

  Fact unnest_arrow_length : forall e0s es er anns,
      length e0s = length anns ->
      length es = length anns ->
      length (unnest_arrow e0s es er anns) = length anns.
  Proof.
    intros * Hl1 Hl2.
    unfold unnest_arrow. solve_length.
  Qed.

  (* Fact unnest_pre_length : forall es anns, *)
  (*     length es = length anns -> *)
  (*     length (unnest_pre es anns) = length anns. *)
  (* Proof. *)
  (*   intros * Hl1. *)
  (*   unfold unnest_pre. solve_length. *)
  (* Qed. *)

  Fact unnest_merge_length : forall ckid ets efs tys nck,
      length ets = length tys ->
      length efs = length tys ->
      length (unnest_merge ckid ets efs tys nck) = length tys.
  Proof.
    intros * Hl1 Hl2.
    unfold unnest_merge. solve_length.
  Qed.

  Fact unnest_ite_length : forall e ets efs tys nck,
      length ets = length tys ->
      length efs = length tys ->
      length (unnest_ite e ets efs tys nck) = length tys.
  Proof.
    intros * Hl1 Hl2.
    unfold unnest_ite. solve_length.
  Qed.

  Fact unnest_rhs_length : forall G e es' eqs' st st',
      wl_exp G e ->
      unnest_rhs G e st = (es', eqs', st') ->
      (length es' = 1 \/ length es' = numstreams e).
  Proof.
    intros * Hwt Hnorm;
      destruct e; unfold unnest_rhs in Hnorm;
        try (solve [right; eapply unnest_exp_length; eauto]);
        try (destruct o); repeat inv_bind; auto.
    1,2,3,4,5:right; inv Hwt;
      eapply unnest_exps_length in H; eauto.
    1,2,3,4:eapply unnest_exps_length in H0; eauto.
    eapply unnest_fby_length; eauto; congruence.
    eapply unnest_arrow_length; eauto; congruence.
  Qed.
  Hint Resolve unnest_rhs_length.

  Fact unnest_exp_numstreams : forall G e is_control es' eqs' st st',
      unnest_exp G is_control e st = (es', eqs', st') ->
      Forall (fun e => numstreams e = 1) es'.
  Proof.
    intros * Hnorm.
    induction e; simpl in Hnorm; repeat inv_bind; repeat constructor.
    3:destruct l0; repeat inv_bind.
    4,5: destruct l1, is_control; repeat inv_bind.
    1,2,5,7,8:rewrite Forall_map; eapply Forall_forall; intros [? ?] ?; auto.
    1,2,3:(unfold unnest_when, unnest_merge, unnest_ite;
           rewrite Forall_forall; intros ? Hin;
           repeat simpl_In; reflexivity).
  Qed.

  Corollary map_bind2_unnest_exp_numstreams : forall G es is_control es' eqs' st st',
      map_bind2 (unnest_exp G is_control) es st = (es', eqs', st') ->
      Forall (fun e => numstreams e = 1) (concat es').
  Proof.
    intros * Hmap.
    apply map_bind2_values in Hmap.
    induction Hmap; simpl.
    - constructor.
    - apply Forall_app; split; auto.
      destruct H as [? [? H]].
      eapply unnest_exp_numstreams; eauto.
  Qed.

  Corollary unnest_exps_numstreams : forall G es es' eqs' st st',
      unnest_exps G es st = (es', eqs', st') ->
      Forall (fun e => numstreams e = 1) es'.
  Proof.
    intros * Hnorm.
    unfold unnest_exps in Hnorm. repeat inv_bind.
    eapply map_bind2_unnest_exp_numstreams. eauto.
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

  Fact unnest_merge_annot : forall ckid ets efs tys ck,
      length ets = length tys ->
      length efs = length tys ->
      Forall2 (fun ty e => annot e = [(ty, ck)]) tys (unnest_merge ckid ets efs tys ck).
  Proof.
    intros * Hlen1 Hlen2. unfold unnest_merge. rewrite Forall2_map_2.
    revert ets efs Hlen1 Hlen2.
    induction tys; intros; destruct ets, efs; simpl in *; try congruence;
      constructor; auto.
  Qed.

  Fact unnest_ite_annot : forall e ets efs tys ck,
      length ets = length tys ->
      length efs = length tys ->
      Forall2 (fun ty e => annot e = [(ty, ck)]) tys (unnest_ite e ets efs tys ck).
  Proof.
    intros * Hlen1 Hlen2. unfold unnest_ite. rewrite Forall2_map_2.
    revert ets efs Hlen1 Hlen2.
    induction tys; intros; destruct ets, efs; simpl in *; try congruence;
      constructor; auto.
  Qed.

  Fact unnest_noops_exps_annots : forall cks es es' eqs' st st',
      length cks = length es ->
      Forall (fun e => numstreams e = 1) es ->
      unnest_noops_exps cks es st = (es', eqs', st') ->
      annots es' = annots es.
  Proof.
    unfold unnest_noops_exps.
    induction cks; intros * Hl Hnum Hunt; repeat inv_bind.
    - destruct es; simpl in *; congruence.
    - destruct es; simpl in *; inv Hl.
      inv Hnum.
      repeat inv_bind. simpl. f_equal.
      2:eapply IHcks; eauto; inv_bind; repeat eexists; eauto; inv_bind; eauto.
      clear H0 H1.
      unfold unnest_noops_exp in H.
      rewrite <-length_annot_numstreams in H3. singleton_length.
      destruct p as (?&?&?).
      destruct (is_noops_exp _); repeat inv_bind; eauto.
  Qed.

  Fact unnest_exp_annot : forall G e is_control es' eqs' st st',
      wl_exp G e ->
      unnest_exp G is_control e st = (es', eqs', st')  ->
      annots es' = annot e.
  Proof with eauto.
    destruct e; intros * Hwl Hnorm;
      (* specialize (unnest_exp_length _ _ _ es' eqs' st st' Hwl Hnorm) as Hlength; *)
      inv Hwl; repeat inv_bind...
    - (* fby *) apply idents_for_anns_annots in H2...
    - (* arrow *) apply idents_for_anns_annots in H2...
    - (* when *)
      assert (length (concat x0) = length (annots l)) as Hlen by eauto.
      unfold unnest_when; repeat simpl_list.
      rewrite H5 in Hlen.
      remember (concat x0) as l0.
      clear x0 H H2 H5 Heql0. revert l0 Hlen.
      induction tys; intros l0 Hlen; destruct l0; simpl in *; try congruence; auto.
      destruct nck. f_equal; auto.
    - (* merge *)
      destruct is_control; repeat inv_bind.
      + assert (length (concat x2) = length (annots l)) as Hlen1 by eauto; rewrite H6 in Hlen1.
        assert (length (concat x5) = length (annots l0)) as Hlen2 by eauto; rewrite H7 in Hlen2.
        unfold unnest_merge; repeat simpl_list.
        remember (concat x2) as l1. remember (concat x5) as l2.
        clear x2 x5 H H0 H4 H5 H6 H7 Heql1 Heql2. revert l1 l2 Hlen1 Hlen2.
        induction tys; intros l1 l2 Hlen1 Hlen2; destruct l1; destruct l2; simpl in *; try congruence; auto.
        destruct nck. f_equal; auto.
      + apply idents_for_anns_annots in H1...
    - (* ite *)
      destruct is_control; repeat inv_bind.
      + assert (length (concat x5) = length (annots l)) as Hlen1 by eauto; rewrite H8 in Hlen1.
        assert (length (concat x8) = length (annots l0)) as Hlen2 by eauto; rewrite H9 in Hlen2.
        unfold unnest_ite; repeat simpl_list.
        remember (concat x5) as l1. remember (concat x8) as l2.
        clear x5 x8 H0 H1 H8 H9 Heql1 Heql2. revert l1 l2 Hlen1 Hlen2.
        induction tys; intros l1 l2 Hlen1 Hlen2; destruct l1; destruct l2; simpl in *; try congruence; auto.
        destruct nck. f_equal; auto.
      + apply idents_for_anns_annots in H2...
    - (* app *) apply idents_for_anns'_annots in H2...
  Qed.

  Corollary unnest_exp_annot_length : forall G e is_control es' eqs' st st',
      wl_exp G e ->
      unnest_exp G is_control e st = (es', eqs', st')  ->
      length (annots es') = length (annot e).
  Proof with eauto.
    intros.
    eapply unnest_exp_annot in H0; eauto.
    congruence.
  Qed.

  Fact map_bind2_unnest_exp_annots': forall G is_control es es' eqs' st st',
      Forall (wl_exp G) es ->
      map_bind2 (unnest_exp G is_control) es st = (es', eqs', st') ->
      Forall2 (fun es' e => annots es' = annot e) es' es.
  Proof.
    intros * Hf Hmap.
    apply map_bind2_values in Hmap.
    induction Hmap.
    - constructor.
    - destruct H as [? [? Hnorm]]. inv Hf.
      constructor; eauto.
      eapply unnest_exp_annot; eauto.
  Qed.

  Corollary map_bind2_unnest_exp_annots'' : forall G is_control es es' eqs' st st',
      Forall (wl_exp G) es ->
      map_bind2 (unnest_exp G is_control) es st = (es', eqs', st') ->
      Forall2 (fun e ann => annot e = [ann]) (concat es') (annots es).
  Proof.
    intros * Hwl Hmap.
    assert (Forall (fun e => numstreams e = 1) (concat es')) as Hnumstreams.
    { eapply map_bind2_unnest_exp_numstreams in Hmap; eauto. }
    eapply map_bind2_unnest_exp_annots' in Hmap; eauto.
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

  Corollary map_bind2_unnest_exp_annots_length' :
    forall G is_control es es' eqs' st st',
      Forall (wl_exp G) es ->
      map_bind2 (unnest_exp G is_control) es st = (es', eqs', st') ->
      Forall2 (fun es' e => length (annots es') = length (annot e)) es' es.
  Proof.
    intros * Hf Hmap.
    eapply map_bind2_unnest_exp_annots' in Hmap; eauto.
    induction Hmap; inv Hf; constructor; eauto.
    congruence.
  Qed.

  Fact map_bind2_unnest_exp_annots :
    forall G is_control es es' eqs' st st',
      Forall (wl_exp G) es ->
      map_bind2 (unnest_exp G is_control) es st = (es', eqs', st') ->
      annots (concat es') = annots es.
  Proof.
    intros * Hwl Hmap.
    eapply map_bind2_unnest_exp_annots' in Hmap; eauto.
    induction Hmap; simpl; auto.
    inv Hwl.
    repeat simpl_list.
    f_equal; auto.
  Qed.

  Fact map_bind2_unnest_exp_annots_length :
    forall G is_control es es' eqs' st st',
      Forall (wl_exp G) es ->
      map_bind2 (unnest_exp G is_control) es st = (es', eqs', st') ->
      length (annots (concat es')) = length (annots es).
  Proof.
    intros * Hwl Hmap.
    eapply map_bind2_unnest_exp_annots in Hmap; eauto.
    congruence.
  Qed.

  Fact unnest_exps_annots : forall G es es' eqs' st st',
      Forall (wl_exp G) es ->
      unnest_exps G es st = (es', eqs', st') ->
      annots es' = annots es.
  Proof.
    intros * Hwt Hnorm.
    unfold unnest_exps in Hnorm; repeat inv_bind.
    eapply map_bind2_unnest_exp_annots in H; eauto.
  Qed.

  Corollary unnest_exps_annots_length : forall G es es' eqs' st st',
      Forall (wl_exp G) es ->
      unnest_exps G es st = (es', eqs', st') ->
      length (annots es') = length (annots es).
  Proof.
    intros * Hwt Hnorm.
    eapply unnest_exps_annots in Hnorm; eauto.
    congruence.
  Qed.

  Fact unnest_fby_annot : forall anns e0s es er,
      length e0s = length anns ->
      length es = length anns ->
      annots (unnest_fby e0s es er anns) = anns.
  Proof.
    induction anns; intros * Hl1 Hl2;
      destruct e0s; destruct es; simpl in *; try congruence; auto.
    f_equal. eauto.
  Qed.

  Fact unnest_arrow_annot : forall anns e0s es er,
      length e0s = length anns ->
      length es = length anns ->
      annots (unnest_arrow e0s es er anns) = anns.
  Proof.
    induction anns; intros * Hl1 Hl2;
      destruct e0s; destruct es; simpl in *; try congruence; auto.
    f_equal. eauto.
  Qed.

  (* Fact unnest_pre_annot : forall anns es, *)
  (*     length es = length anns -> *)
  (*     annots (unnest_pre es anns) = anns. *)
  (* Proof. *)
  (*   induction anns; intros * Hl1; *)
  (*     destruct es; simpl in *; try congruence; auto. *)
  (*   f_equal. eauto. *)
  (* Qed. *)

  Fact unnest_fby_annot' : forall anns e0s es er,
      length e0s = length anns ->
      length es = length anns ->
      Forall2 (fun e a => annot e = [a]) (unnest_fby e0s es er anns) anns.
  Proof.
    induction anns; intros * Hl1 Hl2;
      destruct e0s; destruct es; simpl in *; try congruence; auto.
    - constructor.
    - simpl. constructor; eauto.
      eapply IHanns; eauto.
  Qed.

  Fact unnest_arrow_annot' : forall anns e0s es er,
      length e0s = length anns ->
      length es = length anns ->
      Forall2 (fun e a => annot e = [a]) (unnest_arrow e0s es er anns) anns.
  Proof.
    induction anns; intros * Hl1 Hl2;
      destruct e0s; destruct es; simpl in *; try congruence; auto.
    - constructor.
    - simpl. constructor; eauto.
      eapply IHanns; eauto.
  Qed.

  (* Fact unnest_pre_annot' : forall anns es, *)
  (*     length es = length anns -> *)
  (*     Forall2 (fun e a => annot e = [a]) (unnest_pre es anns) anns. *)
  (* Proof. *)
  (*   induction anns; intros * Hl1; *)
  (*     destruct es; simpl in *; try congruence; auto. *)
  (*   - constructor. *)
  (*   - simpl. constructor; eauto. *)
  (* Qed. *)

  Fact unnest_rhs_annot : forall G e es' eqs' st st',
      wl_exp G e ->
      unnest_rhs G e st = (es', eqs', st') ->
      annots es' = annot e.
  Proof.
    intros * Hwt Hnorm.
    destruct e; unfold unnest_rhs in Hnorm;
      try (solve [eapply unnest_exp_annot in Hnorm; eauto]).
    - (* fby *)
      repeat inv_bind. inv Hwt.
      1,2:eapply unnest_fby_annot; eauto.
      1,3:eapply unnest_exps_length in H; eauto; congruence.
      1,2:eapply unnest_exps_length in H0; eauto; congruence.
    - (* arrow *)
      repeat inv_bind. inv Hwt.
      1,2:eapply unnest_arrow_annot; eauto.
      1,3:eapply unnest_exps_length in H; eauto; congruence.
      1,2:eapply unnest_exps_length in H0; eauto; congruence.
    - (* app *)
      repeat inv_bind; simpl; rewrite app_nil_r; reflexivity.
  Qed.

  Corollary unnest_rhs_annot_length : forall G e es' eqs' st st',
      wl_exp G e ->
      unnest_rhs G e st = (es', eqs', st') ->
      length (annots es') = length (annot e).
  Proof.
    intros * Hwt Hnorm.
    eapply unnest_rhs_annot in Hnorm; eauto.
    congruence.
  Qed.

  Fact unnest_rhss_annots : forall G es es' eqs' st st',
      Forall (wl_exp G) es ->
      unnest_rhss G es st = (es', eqs', st') ->
      annots es' = annots es.
  Proof.
    intros * Hf Hnorm.
    unfold unnest_rhss in Hnorm. repeat inv_bind.
    apply map_bind2_values in H.
    induction H; simpl in *.
    - reflexivity.
    - inv Hf.
      destruct H as [? [? H]]. eapply unnest_rhs_annot in H; eauto.
      repeat simpl_list.
      f_equal; auto.
  Qed.

  Corollary unnest_rhss_annots_length : forall G es es' eqs' st st',
      Forall (wl_exp G) es ->
      unnest_rhss G es st = (es', eqs', st') ->
      length (annots es') = length (annots es).
  Proof.
    intros * Hf Hnorm.
    eapply unnest_rhss_annots in Hnorm; eauto.
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

  Fact unnest_noops_exps_vars_perm : forall cks es es' eqs' st st',
      unnest_noops_exps cks es st = (es', eqs', st') ->
      Permutation (vars_defined eqs'++st_ids st) (st_ids st').
  Proof.
    intros * Hun.
    unfold unnest_noops_exps in Hun. repeat inv_bind.
    eapply map_bind2_vars_perm; eauto.
    eapply Forall_forall. intros (?&?) _ * Hun.
    unfold unnest_noops_exp in Hun.
    destruct (hd _ _) as (?&?&?). destruct is_noops_exp; repeat inv_bind; eauto.
    simpl. eapply fresh_ident_vars_perm; eauto.
  Qed.

  Fact unnest_reset_vars_perm : forall k e es' eqs' st st',
      (forall es' eqs' st st',
          k e st = ((es', eqs'), st') ->
          Permutation ((vars_defined eqs')++(st_ids st)) (st_ids st')) ->
      unnest_reset k e st = ((es', eqs'), st') ->
      Permutation ((vars_defined eqs')++(st_ids st)) (st_ids st').
  Proof.
    intros * Hkperm Hnorm.
    unnest_reset_spec; simpl; eauto.
    destruct (hd _ _) as [ty [ck o]]; repeat inv_bind.
    eapply Hkperm in Hk0.
    eapply fresh_ident_vars_perm in Hfresh; eauto.
    rewrite <- Hfresh, <- Hk0; auto.
  Qed.

  Fact unnest_exp_vars_perm : forall G e is_control es' eqs' st st',
      wl_exp G e ->
      unnest_exp G is_control e st = ((es', eqs'), st') ->
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
      apply map_bind2_vars_perm in H4.
      2:{ eapply Forall_impl_In; [|eapply H1]. intros; simpl in *.
          eapply unnest_reset_vars_perm in H14; intros; eauto.
          eapply Forall_forall in H9; eauto. }
      remember (unnest_fby _ _ _ _) as fby.
      assert (length x8 = length fby) as Hlen.
      { eapply map_bind2_unnest_exp_length in H2...
        eapply map_bind2_unnest_exp_length in H3...
        apply idents_for_anns_length in H5...
        rewrite Heqfby, unnest_fby_length; solve_length.
      }
      apply map_bind2_vars_perm in H2. 2:solve_forall.
      apply map_bind2_vars_perm in H3. 2:solve_forall.
      apply idents_for_anns_vars_perm in H5.
      rewrite <- H5, <- H4, <- H3, <- H2.
      repeat simpl_list.
      replace (map (fun x => fst (let '(x0, _, fby) := x in ([x0], [fby]))) (combine x8 _)) with (map (fun x => [fst x]) x8).
      2:{ clear - Hlen. revert fby Hlen.
          induction x8; intros; destruct fby; simpl in *; try congruence.
          destruct a. f_equal; eauto. }
      replace (concat (map (fun x => [fst x]) x8)) with (map fst x8).
      2: { clear. induction x8; simpl; f_equal; auto. }
      eapply Permutation_app_head.
      rewrite Permutation_swap. symmetry. rewrite Permutation_swap. apply Permutation_app_head.
      rewrite Permutation_swap; auto.
    - (* arrow *)
      repeat inv_bind.
      apply map_bind2_vars_perm in H4.
      2:{ eapply Forall_impl_In; [|eapply H1]. intros; simpl in *.
          eapply unnest_reset_vars_perm in H14; intros; eauto.
          eapply Forall_forall in H9; eauto. }
      repeat inv_bind.
      remember (unnest_arrow _ _ _ _) as fby.
      assert (length x8 = length fby) as Hlen.
      { eapply map_bind2_unnest_exp_length in H2...
        eapply map_bind2_unnest_exp_length in H3...
        apply idents_for_anns_length in H5...
        rewrite Heqfby, unnest_arrow_length; solve_length.
      }
      apply map_bind2_vars_perm in H2. 2:solve_forall.
      apply map_bind2_vars_perm in H3. 2:solve_forall.
      apply idents_for_anns_vars_perm in H5.
      rewrite <- H5, <- H4, <- H3, <- H2.
      repeat simpl_list.
      replace (map (fun x => fst (let '(x0, _, fby) := x in ([x0], [fby]))) (combine x8 _)) with (map (fun x => [fst x]) x8).
      2:{ clear - Hlen. revert fby Hlen.
          induction x8; intros; destruct fby; simpl in *; try congruence.
          destruct a. f_equal; eauto. }
      replace (concat (map (fun x => [fst x]) x8)) with (map fst x8).
      2: { clear. induction x8; simpl; f_equal; auto. }
      eapply Permutation_app_head.
      rewrite Permutation_swap. symmetry. rewrite Permutation_swap. apply Permutation_app_head.
      rewrite Permutation_swap; auto.
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
    - (* app (reset) *)
      repeat inv_bind.
      apply map_bind2_vars_perm in H3.
      2:{ eapply Forall_impl_In; [|eapply H0]. intros; simpl in *.
          eapply unnest_reset_vars_perm in H13; intros; eauto.
          eapply Forall_forall in H6; eauto. }
      unfold vars_defined in *; repeat rewrite <- flat_map_app; simpl.
      eapply idents_for_anns'_vars_perm in H4.
      simpl; repeat inv_bind.
      apply map_bind2_vars_perm in H1. 2: (repeat rewrite_Forall_forall; eauto).
      apply unnest_noops_exps_vars_perm in H2.
      rewrite <- H4, <- H3, <- H2, <- H1; simpl.
      repeat simpl_list.
      apply Permutation_app_head. rewrite Permutation_app_comm, Permutation_swap, <- app_assoc, <- app_assoc.
      apply Permutation_app_head, Permutation_app_head. apply Permutation_app_comm.
  Qed.

  Corollary unnest_exps_vars_perm : forall G es es' eqs' st st',
      Forall (wl_exp G) es ->
      unnest_exps G es st = ((es', eqs'), st') ->
      Permutation ((vars_defined eqs')++(st_ids st)) (st_ids st').
  Proof with eauto.
    intros * Hwl Hnorm.
    unfold unnest_exps in Hnorm.
    repeat inv_bind.
    eapply map_bind2_vars_perm...
    repeat rewrite_Forall_forall.
    eapply unnest_exp_vars_perm...
  Qed.

  Fact unnest_rhs_vars_perm : forall G e es' eqs' st st',
      wl_exp G e ->
      unnest_rhs G e st = ((es', eqs'), st') ->
      Permutation ((vars_defined eqs')++(st_ids st)) (st_ids st').
  Proof with eauto.
    intros * Hwt Hnorm.
    destruct e; unfold unnest_rhs in Hnorm;
      try (solve [eapply unnest_exp_vars_perm; eauto]); inv Hwt.
    - (* fby *)
      repeat inv_bind.
      apply map_bind2_vars_perm in H1.
      2:{ eapply Forall_forall. intros * ? * Res.
          eapply unnest_reset_vars_perm in Res; intros; eauto.
          eapply unnest_exp_vars_perm; eauto. eapply Forall_forall in H6; eauto. }
      repeat inv_bind.
      eapply unnest_exps_vars_perm in H...
      eapply unnest_exps_vars_perm in H0...
      rewrite <- H1, <- H0, <- H.
      repeat simpl_list.
      rewrite Permutation_swap, (Permutation_swap _ (concat (map fst x3))).
      apply Permutation_app_head; auto.
      rewrite Permutation_swap; auto.
    - (* arrow *)
      repeat inv_bind.
      apply map_bind2_vars_perm in H1.
      2:{ eapply Forall_forall. intros * ? * Res.
          eapply unnest_reset_vars_perm in Res; intros; eauto.
          eapply unnest_exp_vars_perm; eauto. eapply Forall_forall in H6; eauto. }
      repeat inv_bind.
      eapply unnest_exps_vars_perm in H...
      eapply unnest_exps_vars_perm in H0...
      rewrite <- H1, <- H0, <- H.
      repeat simpl_list.
      rewrite Permutation_swap, (Permutation_swap _ (concat (map fst x3))).
      apply Permutation_app_head; auto.
      rewrite Permutation_swap; auto.
    - (* app *)
      repeat inv_bind.
      apply map_bind2_vars_perm in H1.
      2:{ eapply Forall_forall. intros * ? * Res.
          eapply unnest_reset_vars_perm in Res; intros; eauto.
          eapply unnest_exp_vars_perm; eauto. eapply Forall_forall in H4; eauto. }
      unfold vars_defined. repeat rewrite <- flat_map_app; repeat rewrite <- app_assoc; simpl.
      eapply unnest_exps_vars_perm in H; eauto.
      eapply unnest_noops_exps_vars_perm in H0.
      rewrite <- H1, <- H0, <- H.
      rewrite Permutation_swap, <- (Permutation_swap (vars_defined x3)).
      apply Permutation_app_head.
      rewrite Permutation_swap. reflexivity.
  Qed.

  Corollary unnest_rhss_vars_perm : forall G es es' eqs' st st',
      Forall (wl_exp G) es ->
      unnest_rhss G es st = ((es', eqs'), st') ->
      Permutation ((vars_defined eqs')++(st_ids st)) (st_ids st').
  Proof.
    intros * Hf Hnorm.
    unfold unnest_rhss in Hnorm.
    repeat inv_bind.
    eapply map_bind2_vars_perm in H; eauto.
    repeat rewrite_Forall_forall.
    eapply unnest_rhs_vars_perm; eauto.
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

  Fact unnest_equation_vars_perm : forall G eq eqs' st st',
      wl_equation G eq ->
      unnest_equation G eq st = (eqs', st') ->
      Permutation ((vars_defined eqs')++(st_ids st)) ((vars_defined [eq])++(st_ids st')).
  Proof.
    intros * Hwt Hnorm.
    destruct eq; simpl in *.
    repeat inv_bind. destruct Hwt as [Hwt Hl].
    specialize (unnest_rhss_vars_perm _ _ _ _ _ _ Hwt H) as Hperm1.
    rewrite app_nil_r.
    assert (vars_defined (flat_map split_equation [(l, x)]) = vars_defined [(l, x)]) as Hxl.
    { apply split_equations_vars_defined.
      repeat constructor.
      eapply unnest_rhss_annots_length in H; eauto. congruence. }
    repeat simpl_list.
    apply Permutation_app; auto.
    rewrite <- Hxl at 2. reflexivity.
  Qed.

  Corollary unnest_equations_vars_perm : forall G eqs eqs' st st',
      Forall (wl_equation G) eqs ->
      unnest_equations G eqs st = (eqs', st') ->
      Permutation ((vars_defined eqs')++(st_ids st)) ((vars_defined eqs)++(st_ids st')).
  Proof.
    induction eqs; intros * Hf Hnorm; unfold unnest_equations in Hnorm; repeat inv_bind.
    - reflexivity.
    - inv Hf.
      assert (unnest_equations G eqs x1 = (concat x2, st')) as Hnorm'.
      { unfold unnest_equations. repeat inv_bind. repeat eexists; eauto.
        inv_bind; eauto. } eapply IHeqs in Hnorm'; eauto.
      eapply unnest_equation_vars_perm in H; eauto; simpl in *.
      repeat simpl_list.
      rewrite Permutation_swap, H, Permutation_swap.
      apply Permutation_app_head. assumption.
  Qed.

  (** ** Specification of an (almost) normalized node *)

  Inductive normalized_lexp : exp -> Prop :=
  | unnested_Econst : forall c, normalized_lexp (Econst c)
  | unnested_Evar : forall x ty cl, normalized_lexp (Evar x (ty, cl))
  | unnested_Eunop : forall op e1 ty cl,
      normalized_lexp e1 ->
      normalized_lexp (Eunop op e1 (ty, cl))
  | unnested_Ebinop : forall op e1 e2 ty cl,
      normalized_lexp e1 ->
      normalized_lexp e2 ->
      normalized_lexp (Ebinop op e1 e2 (ty, cl))
  | unnested_Ewhen : forall e x b ty cl,
      normalized_lexp e ->
      normalized_lexp (Ewhen [e] x b ([ty], cl)).

  Fixpoint noops_exp (ck: clock) (e : exp) : Prop :=
    match ck with
    | Cbase => True
    | Con ck' _ _ =>
      match e with
      | Econst _ | Evar _ _ => True
      | Ewhen [e'] _ _ _ => noops_exp ck' e'
      | _ => False
      end
    end.

  Inductive normalized_cexp : exp -> Prop :=
  | unnested_Emerge : forall x et ef ty cl,
      normalized_cexp et ->
      normalized_cexp ef ->
      normalized_cexp (Emerge x [et] [ef] ([ty], cl))
  | unnested_Eite : forall e et ef ty cl,
      normalized_lexp e ->
      normalized_cexp et ->
      normalized_cexp ef ->
      normalized_cexp (Eite e [et] [ef] ([ty], cl))
  | normalized_lexp_cexp : forall e,
      normalized_lexp e ->
      normalized_cexp e.

  Inductive unnested_equation G : equation -> Prop :=
  | unnested_eq_Eapp : forall xs f n es er lann,
      Forall normalized_lexp es ->
      find_node f G = Some n ->
      Forall2 noops_exp (map (fun '(_, (_, ck)) => ck) n.(n_in)) es ->
      Forall (fun e => exists x ann, e = Evar x ann) er ->
      unnested_equation G (xs, [Eapp f es er lann])
  | unnested_eq_Efby : forall x e0 e er ann,
      normalized_lexp e0 ->
      normalized_lexp e ->
      Forall (fun e => exists x ann, e = Evar x ann) er ->
      unnested_equation G ([x], [Efby [e0] [e] er [ann]])
  | unnested_eq_Earrow : forall x e0 e er ann,
      normalized_lexp e0 ->
      normalized_lexp e ->
      Forall (fun e => exists x ann, e = Evar x ann) er ->
      unnested_equation G ([x], [Earrow [e0] [e] er [ann]])
  | unnested_eq_cexp : forall x e,
      normalized_cexp e ->
      unnested_equation G ([x], [e]).

  Definition unnested_node G (n : node) :=
    Forall (unnested_equation G) (n_eqs n).

  Definition unnested_global G := ForallTail (fun n G => unnested_node G n) G.

  Hint Constructors normalized_lexp normalized_cexp unnested_equation.

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

  (** ** After normalization, equations and expressions are unnested *)

  Fact normalized_lexp_hd_default : forall es,
      Forall normalized_lexp es ->
      normalized_lexp (hd_default es).
  Proof.
    intros es Hf.
    destruct es; simpl.
    - constructor.
    - inv Hf; auto.
  Qed.

  Fact normalized_cexp_hd_default : forall es,
      Forall normalized_cexp es ->
      normalized_cexp (hd_default es).
  Proof.
    intros es Hf.
    destruct es; simpl.
    - repeat constructor.
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
  Hint Resolve normalized_lexp_hd_default normalized_cexp_hd_default.

  Lemma unnest_exp_normalized_lexp : forall G e es' eqs' st st',
      unnest_exp G false e st = (es', eqs', st') ->
      Forall normalized_lexp es'.
  Proof with eauto.
    induction e using exp_ind2; intros * Hnorm;
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
    - (* arrow *)
      simpl_forall.
      repeat rewrite_Forall_forall.
      repeat simpl_In. destruct a0...
    - (* when *)
      destruct a. repeat inv_bind. unfold unnest_when.
      apply map_bind2_normalized_lexp' in H0...
      repeat rewrite_Forall_forall.
      repeat simpl_In...
    - (* merge *)
      destruct a. repeat inv_bind. unfold unnest_merge.
      repeat rewrite_Forall_forall.
      repeat simpl_In. destruct a...
    - (* ite *)
      destruct a. repeat inv_bind. unfold unnest_ite.
      repeat rewrite_Forall_forall.
      repeat simpl_In. destruct a...
    - (* app *)
      repeat rewrite_Forall_forall.
      repeat simpl_In. destruct a0...
  Qed.
  Hint Resolve unnest_exp_normalized_lexp.

  Corollary map_bind2_normalized_lexp : forall G es es' eqs' st st',
      map_bind2 (unnest_exp G false) es st = (es', eqs', st') ->
      Forall normalized_lexp (concat es').
  Proof.
    intros * Hnorm.
    eapply map_bind2_normalized_lexp' in Hnorm; auto.
    solve_forall.
  Qed.
  Hint Resolve map_bind2_normalized_lexp.

  Corollary unnest_exps_normalized_lexp: forall G es es' eqs' st st',
      unnest_exps G es st = (es', eqs', st') ->
      Forall normalized_lexp es'.
  Proof.
    intros * Hnorm.
    unfold unnest_exps in Hnorm. repeat inv_bind.
    apply map_bind2_normalized_lexp in H; auto.
  Qed.
  Hint Resolve unnest_exps_normalized_lexp.

  Fact unnest_resets_is_var : forall k es es' eqs' st st',
      map_bind2 (unnest_reset k) es st = (es', eqs', st') ->
      Forall (fun e => exists x ann, e = Evar x ann) es'.
  Proof.
    intros * Hnorm.
    eapply map_bind2_values, Forall3_ignore3, Forall2_ignore1 in Hnorm.
    eapply Forall_impl; [|eauto]. intros * (?&?&?&?&?&Res).
    unnest_reset_spec; simpl; eauto.
  Qed.

  Fact unnest_resets_unnested_eq : forall G k es es' eqs' st st',
      Forall (fun e => forall es' eqs' st st',
                  k e st = (es', eqs', st') ->
                  Forall normalized_cexp es' /\ Forall (unnested_equation G) eqs') es ->
      map_bind2 (unnest_reset k) es st = (es', eqs', st') ->
      Forall (unnested_equation G) (concat eqs').
  Proof.
    intros * Hkunn Hnorm.
    eapply map_bind2_values, Forall3_ignore2, Forall2_ignore1 in Hnorm.
    eapply Forall_concat.
    eapply Forall_impl_In; [|eauto]. intros * ? (?&?&?&?&?&?).
    eapply Forall_forall in Hkunn; eauto.
    unnest_reset_spec; auto.
    1,2:eapply Hkunn in Hk0 as (?&?); auto.
  Qed.

  Fact unnest_merge_normalized_cexp : forall x ets efs tys ck,
      Forall normalized_cexp ets ->
      Forall normalized_cexp efs ->
      Forall normalized_cexp (unnest_merge x ets efs tys ck).
  Proof.
    intros. unfold unnest_merge.
    repeat rewrite_Forall_forall. repeat simpl_In.
    econstructor; eauto.
  Qed.

  Fact unnest_ite_normalized_cexp : forall e ets efs tys ck,
      normalized_lexp e ->
      Forall normalized_cexp ets ->
      Forall normalized_cexp efs ->
      Forall normalized_cexp (unnest_ite e ets efs tys ck).
  Proof.
    intros. unfold unnest_ite.
    repeat rewrite_Forall_forall. repeat simpl_In.
    econstructor; eauto.
  Qed.

  Lemma unnest_exp_normalized_cexp : forall G e es' eqs' st st',
      unnest_exp G true e st = (es', eqs', st') ->
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
    - (* arrow *)
      solve_forall.
      repeat simpl_In. destruct a0...
    - (* when *)
      destruct a. repeat inv_bind. unfold unnest_when.
      apply map_bind2_normalized_lexp in H0.
      repeat rewrite_Forall_forall.
      repeat simpl_In...
    - (* merge *)
      destruct a. repeat inv_bind.
      eapply unnest_merge_normalized_cexp...
      apply map_bind2_normalized_cexp' in H1; [|solve_forall]...
      apply map_bind2_normalized_cexp' in H2; [|solve_forall]...
    - (* ite *)
      destruct a. repeat inv_bind.
      eapply unnest_ite_normalized_cexp...
      apply map_bind2_normalized_cexp' in H2; [|solve_forall]...
      apply map_bind2_normalized_cexp' in H3; [|solve_forall]...
    - (* app *)
      solve_forall.
      repeat simpl_In. destruct a0...
  Qed.
  Hint Resolve unnest_exp_normalized_cexp.

  Corollary map_bind2_normalized_cexp : forall G es es' eqs' st st',
      map_bind2 (unnest_exp G true) es st = (es', eqs', st') ->
      Forall normalized_cexp (concat es').
  Proof.
    intros. apply map_bind2_normalized_cexp' in H; auto.
    solve_forall.
  Qed.

  Fact map_bind2_unnested_eq {A A1} :
    forall G (k : A -> FreshAnn (A1 * (list equation))) a a1s eqs' st st',
      map_bind2 k a st = (a1s, eqs', st') ->
      Forall (fun a => forall a1s eqs' st st',
                  k a st = (a1s, eqs', st') ->
                  Forall (unnested_equation G) eqs') a ->
      Forall (unnested_equation G) (concat eqs').
  Proof.
    induction a; intros * Hmap Hf;
      repeat inv_bind.
    - constructor.
    - inv Hf. simpl.
      rewrite Forall_app; eauto.
  Qed.

  Lemma is_noops_exp_spec : forall ck e,
      is_noops_exp ck e = true <->
      noops_exp ck e.
  Proof.
    induction ck; intros *; simpl in *; split; intros H; auto.
    - destruct e; simpl in *; auto; try congruence.
      destruct l; [|destruct l]; try congruence; simpl in *.
      rewrite <- IHck; auto.
    - destruct e; simpl in *; auto; try congruence.
      destruct l; [|destruct l]; try solve [exfalso; auto]; simpl in *.
      rewrite IHck; auto.
  Qed.

  Lemma unnest_noops_exp_noops_exp : forall G es f n es' es'' eqs' eqs'' st st' st'',
      Forall (wl_exp G) es ->
      length (annots es) = length (n_in n) ->
      find_node f G = Some n ->
      map_bind2 (unnest_exp G false) es st = (es', eqs', st') ->
      unnest_noops_exps (find_node_incks G f) (concat es') st' = (es'', eqs'', st'') ->
      Forall normalized_lexp es'' /\
      Forall2 noops_exp (map (fun '(_, (_, ck)) => ck) (n_in n)) es''.
  Proof.
    intros * Hwl Hlen Hfind Hmap Hun.
    assert (Hnormed:=Hmap). eapply map_bind2_normalized_lexp in Hnormed.
    eapply map_bind2_unnest_exp_length in Hmap; eauto. rewrite <- Hmap in Hlen.
    unfold find_node_incks, unnest_noops_exps in Hun. rewrite Hfind in Hun.
    repeat inv_bind.
    remember (concat es') as es0. clear Heqes0.
    clear Hfind Hwl Hmap st eqs'.
    revert es0 st' st'' es'' x0 H Hlen Hnormed.
    induction (n_in n); intros * Hmap Hlen Hnormed; simpl in *; repeat inv_bind; auto.
    destruct es0; simpl in *; repeat inv_bind. congruence.
    inv Hlen. inv Hnormed. eapply IHl in H0 as (?&?); eauto.
    destruct a as (?&?&?). unfold unnest_noops_exp in H.
    destruct (hd _ _) as (?&?&?).
    destruct (is_noops_exp _ _) eqn:Hnoops; repeat inv_bind.
    - split; econstructor; eauto. eapply is_noops_exp_spec in Hnoops; eauto.
    - destruct c; split; econstructor; simpl; eauto.
  Qed.

  Lemma unnest_noops_exp_unnested_eq : forall G es f n es' es'' eqs' eqs'' st st' st'',
      Forall (wl_exp G) es ->
      length (annots es) = length (n_in n) ->
      find_node f G = Some n ->
      map_bind2 (unnest_exp G false) es st = (es', eqs', st') ->
      unnest_noops_exps (find_node_incks G f) (concat es') st' = (es'', eqs'', st'') ->
      Forall (unnested_equation G) eqs''.
  Proof.
    intros * Hwl Hlen Hfind Hmap Hun.
    assert (Hnormed:=Hmap). eapply map_bind2_normalized_lexp in Hnormed.
    eapply map_bind2_unnest_exp_length in Hmap; eauto. rewrite <- Hmap in Hlen.
    unfold find_node_incks, unnest_noops_exps in Hun. rewrite Hfind in Hun.
    repeat inv_bind.
    remember (concat es') as es0. clear Heqes0.
    clear Hfind Hwl Hmap st eqs'.
    revert es0 st' st'' es'' x0 H Hlen Hnormed.
    induction (n_in n); intros * Hmap Hlen Hnormed; simpl in *; repeat inv_bind; simpl; auto.
    destruct es0; simpl in *; repeat inv_bind. congruence.
    inv Hlen; inv Hnormed; simpl. apply Forall_app; split; eauto.
    destruct a as (?&?&?). unfold unnest_noops_exp in H.
    destruct (hd _ _) as (?&?&?).
    destruct (is_noops_exp _ _) eqn:Hnoops; repeat inv_bind; auto.
  Qed.

  Lemma unnest_exp_unnested_eq : forall G e is_control es' eqs' st st',
      wl_exp G e ->
      unnest_exp G is_control e st = (es', eqs', st') ->
      Forall (unnested_equation G) eqs'.
  Proof with eauto.
    induction e using exp_ind2; intros * Hwl Hnorm; repeat inv_bind; eauto.
    - (* unop *)
      inv Hwl; eauto.
    - (* binop *)
      inv Hwl. apply Forall_app. split...
    - (* fby *)
      repeat rewrite Forall_app; repeat split.
      2:eapply map_bind2_unnested_eq in H2; eauto; inv Hwl; solve_forall.
      2:eapply map_bind2_unnested_eq in H3; eauto; inv Hwl; solve_forall.
      2:eapply unnest_resets_unnested_eq in H4; eauto; inv Hwl; solve_forall.
      eapply Forall_forall; intros ? Hin.
      unfold unnest_fby in Hin. repeat simpl_In.
      econstructor.
      eapply Forall_forall in H9...
      eapply Forall_forall in H7...
      eapply unnest_resets_is_var in H4; eauto.
    - (* fby *)
      repeat rewrite Forall_app; repeat split.
      2:eapply map_bind2_unnested_eq in H2; eauto; inv Hwl; solve_forall.
      2:eapply map_bind2_unnested_eq in H3; eauto; inv Hwl; solve_forall.
      2:eapply unnest_resets_unnested_eq in H4; eauto; inv Hwl; solve_forall.
      eapply Forall_forall; intros ? Hin.
      unfold unnest_arrow in Hin. repeat simpl_In.
      econstructor.
      eapply Forall_forall in H9...
      eapply Forall_forall in H7...
      eapply unnest_resets_is_var in H4; eauto.
    - (* when *)
      inv Hwl. repeat inv_bind.
      eapply map_bind2_unnested_eq in H0; eauto. solve_forall.
    - (* merge *)
      inv Hwl.
      destruct is_control; repeat inv_bind; unfold unnest_merge;
        repeat rewrite Forall_app; repeat split.
      1,2,4,5: (eapply map_bind2_unnested_eq; eauto; solve_forall).
      rewrite Forall_forall; intros [? ?] Hin. rewrite map_map in Hin; simpl in Hin.
      repeat simpl_In.
      do 2 constructor.
      + eapply map_bind2_normalized_cexp in H1.
        rewrite Forall_forall in H1...
      + eapply map_bind2_normalized_cexp in H2.
        rewrite Forall_forall in H2...
    - (* ite *)
      inv Hwl.
      destruct is_control; repeat inv_bind; unfold unnest_ite;
        repeat rewrite Forall_app; repeat split.
      1,5: (eapply IHe; eauto).
      1,2,4,5: (eapply map_bind2_unnested_eq; eauto; solve_forall).
      rewrite Forall_forall; intros [? ?] Hin. rewrite map_map in Hin; simpl in Hin.
      repeat simpl_In.
      constructor. constructor.
      + eapply normalized_lexp_hd_default.
        eapply unnest_exp_normalized_lexp...
      + eapply map_bind2_normalized_cexp in H2.
        rewrite Forall_forall in H2...
      + eapply map_bind2_normalized_cexp in H3.
        rewrite Forall_forall in H3...
    - (* app *)
      assert (length (concat x6) = length (find_node_incks G f)).
      { erewrite map_bind2_unnest_exp_length; [|inv Hwl |eauto]. 2:eauto.
        unfold find_node_incks. inv Hwl.
        rewrite H13, map_length. congruence. }
      constructor. 2:repeat rewrite Forall_app; repeat split.
      + eapply unnest_resets_is_var in H3.
        inv Hwl; eapply unnest_noops_exp_noops_exp in H2 as (?&?). 3-5:eauto. 1,2:eauto.
      + eapply map_bind2_unnested_eq in H1... inv Hwl; solve_forall.
      + inv Hwl; eapply unnest_noops_exp_unnested_eq in H2. 3-5:eauto. 1,2:eauto.
      + eapply unnest_resets_unnested_eq in H3...
        inv Hwl; solve_forall.
  Qed.
  Local Hint Resolve unnest_exp_unnested_eq.

  Corollary unnest_exps_unnested_eq : forall G es es' eqs' st st',
      Forall (wl_exp G) es ->
      unnest_exps G es st = (es', eqs', st') ->
      Forall (unnested_equation G) eqs'.
  Proof.
    intros * Hwl Hnorm.
    unfold unnest_exps in Hnorm. repeat inv_bind.
    eapply map_bind2_unnested_eq in H; eauto.
    solve_forall.
  Qed.
  Local Hint Resolve unnest_exps_unnested_eq.

  (* Intermediary predicate for unnested rhs *)
  Inductive unnested_rhs G : exp -> Prop :=
  | unnested_rhs_Eapp : forall f n es er lann,
      Forall normalized_lexp es ->
      find_node f G = Some n ->
      Forall2 noops_exp (map (fun '(_, (_, ck)) => ck) (n_in n)) es ->
      Forall (fun e => exists x ann, e = Evar x ann) er ->
      unnested_rhs G (Eapp f es er lann)
  | unnested_rhs_Efby : forall e0 e er ann,
      normalized_lexp e0 ->
      normalized_lexp e ->
      Forall (fun e => exists x ann, e = Evar x ann) er ->
      unnested_rhs G (Efby [e0] [e] er [ann])
  | unnested_rhs_Earrow : forall e0 e er ann,
      normalized_lexp e0 ->
      normalized_lexp e ->
      Forall (fun e => exists x ann, e = Evar x ann) er ->
      unnested_rhs G (Earrow [e0] [e] er [ann])
  | unnested_rhs_cexp : forall e,
      normalized_cexp e ->
      unnested_rhs G e.
  Hint Constructors unnested_rhs.

  Fact unnested_equation_unnested_rhs : forall G xs es,
      unnested_equation G (xs, es) ->
      Forall (unnested_rhs G) es.
  Proof with eauto.
    intros * Hnormed.
    inv Hnormed...
  Qed.

  Fact unnest_rhs_unnested_rhs : forall G e es' eqs' st st',
      wl_exp G e ->
      unnest_rhs G e st = (es', eqs', st') ->
      Forall (unnested_rhs G) es'.
  Proof with eauto.
    intros * Hwl Hnorm.
    destruct e; unfold unnest_rhs in Hnorm;
      try (apply unnest_exp_normalized_cexp in Hnorm; solve_forall; auto).
    - (* fby *)
      repeat inv_bind.
      apply unnest_exps_normalized_lexp in H.
      apply unnest_exps_normalized_lexp in H0.
      unfold unnest_fby.
      apply Forall_forall; intros * Hin.
      repeat simpl_In.
      eapply unnest_resets_is_var in H1.
      constructor; eauto.
      + eapply Forall_forall in H; eauto.
      + eapply Forall_forall in H0; eauto.
    - (* arrow *)
     repeat inv_bind.
     apply unnest_exps_normalized_lexp in H.
     apply unnest_exps_normalized_lexp in H0.
     unfold unnest_arrow.
     apply Forall_forall; intros * Hin.
     repeat simpl_In.
     eapply unnest_resets_is_var in H1.
     constructor; eauto.
     + eapply Forall_forall in H; eauto.
     + eapply Forall_forall in H0; eauto.
    - (* app *)
      repeat inv_bind...
      assert (Hr:=H1). eapply unnest_resets_is_var in H1.
      constructor; [|constructor].
      inv Hwl.
      simpl in Hr. repeat inv_bind.
      unfold unnest_exps in H; repeat inv_bind.
      econstructor; eauto.
      1,2:eapply unnest_noops_exp_noops_exp with (es:=l)...
  Qed.

  Corollary unnest_rhss_unnested_rhs : forall G es es' eqs' st st',
      Forall (wl_exp G) es ->
      unnest_rhss G es st = (es', eqs', st') ->
      Forall (unnested_rhs G) es'.
  Proof with eauto.
    intros * Hwl Hnorm.
    unfold unnest_rhss in Hnorm. repeat inv_bind.
    eapply map_bind2_values in H.
    induction H; simpl; try constructor.
    inv Hwl.
    apply Forall_app. split; auto.
    destruct H as [? [? H]].
    eapply unnest_rhs_unnested_rhs; eauto.
  Qed.

  Fact unnest_rhs_unnested_eq : forall G e es' eqs' st st',
      wl_exp G e ->
      unnest_rhs G e st = (es', eqs', st') ->
      Forall (unnested_equation G) eqs'.
  Proof with eauto.
    intros * Hwl Hnorm.
    destruct e; unfold unnest_rhs in Hnorm;
      try (eapply unnest_exp_unnested_eq in Hnorm; eauto).
    - (* fby *)
      repeat inv_bind.
      repeat rewrite Forall_app; repeat split...
      1,2:eapply unnest_exps_unnested_eq; [|eauto]; inv Hwl; eauto.
      eapply unnest_resets_unnested_eq in H1; eauto.
      inv Hwl; solve_forall.
    - (* arrow *)
      repeat inv_bind.
      repeat rewrite Forall_app; repeat split...
      1,2:eapply unnest_exps_unnested_eq; [|eauto]; inv Hwl; eauto.
      eapply unnest_resets_unnested_eq in H1; eauto.
      inv Hwl; solve_forall.
    - (* app *)
      repeat inv_bind...
      eapply unnest_resets_unnested_eq in H1.
      2:(inv Hwl; solve_forall).
      repeat rewrite Forall_app; repeat split; auto.
      apply unnest_exps_unnested_eq in H; inv Hwl; eauto.
      unfold unnest_exps in H; repeat inv_bind.
      inv Hwl.
      1,2:eapply unnest_noops_exp_unnested_eq with (es:=l) in H0; eauto.
  Qed.
  Hint Resolve unnest_rhs_unnested_eq.

  Corollary unnest_rhss_unnested_eq : forall G es es' eqs' st st',
      Forall (wl_exp G) es ->
      unnest_rhss G es st = (es', eqs', st') ->
      Forall (unnested_equation G) eqs'.
  Proof.
    intros * Hwl Hnorm.
    unfold unnest_rhss in Hnorm; repeat inv_bind.
    eapply map_bind2_unnested_eq in H; eauto.
    eapply Forall_impl; [|eauto]. intros; eauto.
  Qed.
  Hint Resolve unnest_rhss_unnested_eq.

  Lemma unnest_equation_unnested_eq : forall G eq eqs' st st',
      wl_equation G eq ->
      unnest_equation G eq st = (eqs', st') ->
      Forall (unnested_equation G) eqs'.
  Proof with eauto.
    intros G [xs es] * (Hwl1&Hwl2) Hnorm.
    unfold unnest_equation in Hnorm.
    repeat inv_bind.
    rewrite Forall_app. split.
    - assert (length xs = length (annots x)) as Hlen.
      { eapply unnest_rhss_annots_length in H...
        congruence. }
      eapply unnest_rhss_unnested_rhs in H; eauto.
      clear Hwl1 Hwl2.
      revert xs Hlen.
      induction H; intros xs Hlen; constructor.
      + inv H...
        1,2:destruct xs; simpl in *; try omega; constructor...
        simpl in Hlen. rewrite app_length in Hlen.
        rewrite length_annot_numstreams in Hlen.
        specialize (normalized_cexp_numstreams _ H1) as Hlen'.
        rewrite Hlen' in *. simpl.
        destruct xs... simpl in Hlen. omega.
      + eapply IHForall.
        rewrite skipn_length.
        rewrite Hlen. simpl. rewrite app_length.
        rewrite length_annot_numstreams. omega.
    - eapply unnest_rhss_unnested_eq in H; eauto.
  Qed.

  Corollary unnest_equations_unnested_eq : forall G eqs eqs' st st',
      Forall (wl_equation G) eqs ->
      unnest_equations G eqs st = (eqs', st') ->
      Forall (unnested_equation G) eqs'.
  Proof.
    induction eqs; intros * Hwl Hnorm;
      unfold unnest_equations in Hnorm; repeat inv_bind; simpl; auto.
    inv Hwl. apply Forall_app; split.
    - eapply unnest_equation_unnested_eq; eauto.
    - eapply IHeqs; eauto.
      unfold unnest_equations; repeat inv_bind; repeat eexists; eauto.
      inv_bind; eauto.
  Qed.

  (** ** No anonymous names in a unnested node *)

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

  Corollary unnest_exp_no_fresh : forall G e is_control es' eqs' st st',
      unnest_exp G is_control e st = (es', eqs', st') ->
      fresh_ins es' = [].
  Proof.
    intros * Hnorm.
    unfold fresh_ins. rewrite flat_map_concat_map, concat_eq_nil, Forall_map.
    destruct is_control.
    - apply unnest_exp_normalized_cexp in Hnorm.
      eapply Forall_impl; eauto. intros. apply normalized_cexp_no_fresh; auto.
    - apply unnest_exp_normalized_lexp in Hnorm.
      eapply Forall_impl; eauto. intros. apply normalized_lexp_no_fresh; auto.
  Qed.

  Corollary unnest_exps_no_fresh : forall G es es' eqs' st st',
      unnest_exps G es st = (es', eqs', st') ->
      fresh_ins es' = [].
  Proof.
    induction es; intros * Hnorm;
      unfold fresh_ins;
      unfold unnest_exps in Hnorm; repeat inv_bind; auto.
    simpl. rewrite flat_map_concat_map, map_app, concat_app.
    eapply unnest_exp_no_fresh in H.
    unfold fresh_ins in H, IHes. rewrite flat_map_concat_map in H. rewrite H; simpl.
    rewrite <- flat_map_concat_map.
    eapply IHes.
    unfold unnest_exps; inv_bind.
    repeat eexists; eauto. inv_bind; eauto.
  Qed.

  Fact unnested_equation_no_anon_in_eq : forall G e,
      unnested_equation G e ->
      anon_in_eq e = [].
  Proof with eauto.
    intros * Hnormed.
    induction Hnormed; unfold anon_in_eq, anon_ins; simpl; repeat rewrite app_nil_r.
    1-3:repeat rewrite normalized_lexp_no_fresh; repeat rewrite normalized_lexps_no_fresh...
    1-3:eapply Forall_impl; [|eauto]; intros ? (?&(?&?)&?); subst; constructor.
    - (* cexp *)
      specialize (anon_in_fresh_in e) as Hincl.
      rewrite normalized_cexp_no_fresh in Hincl...
      apply incl_nil...
  Qed.

  Lemma unnested_equations_no_anon : forall G eqs,
      Forall (unnested_equation G) eqs ->
      anon_in_eqs eqs = [].
  Proof.
    intros * Hnormed.
    unfold anon_in_eqs.
    rewrite flat_map_concat_map, concat_eq_nil, Forall_map.
    solve_forall. eapply unnested_equation_no_anon_in_eq; eauto.
  Qed.

  Corollary unnest_equations_no_anon : forall G eqs eqs' st st',
      Forall (wl_equation G) eqs ->
      unnest_equations G eqs st = (eqs', st') ->
      anon_in_eqs eqs' = [].
  Proof.
    intros * Hwl Hnorm.
    eapply unnested_equations_no_anon.
    eapply unnest_equations_unnested_eq; eauto.
  Qed.

  (** ** Normalization of a full node *)

  Import Facts Tactics.

  Lemma norm1_not_in_elab_prefs :
    ~PS.In norm1 elab_prefs.
  Proof.
    unfold elab_prefs.
    rewrite PSF.singleton_iff.
    intro contra; subst.
    pose proof gensym_prefs_NoDup as Hnd. unfold gensym_prefs in Hnd.
    rewrite contra in Hnd.
    repeat rewrite NoDup_cons_iff in Hnd. destruct Hnd as (Hnin&_).
    apply Hnin. left; auto.
  Qed.

  Lemma AtomOrGensym_add : forall pref prefs xs,
      Forall (AtomOrGensym prefs) xs ->
      Forall (AtomOrGensym (PS.add pref prefs)) xs.
  Proof.
    intros * Hat.
    eapply Forall_impl; [|eauto].
    intros ? [?|(pref'&?&?)]; [left|right]; subst; auto.
    exists pref'. auto using PSF.add_2.
  Qed.

  Program Definition unnest_node G (n : node)
          (Hwl : wl_node G n)
          (Hpref : n_prefixes n = elab_prefs) : node :=
    let eqs := unnest_equations' G (n_eqs n) init_st in
    let nvars := (st_anns (snd (proj1_sig eqs))) in
    {| n_name := (n_name n);
       n_hasstate := (n_hasstate n);
       n_in := (n_in n);
       n_out := (n_out n);
       n_vars := (n_vars n)++nvars;
       n_prefixes := PS.add norm1 (n_prefixes n);
       n_eqs := fst (proj1_sig eqs);
       n_ingt0 := (n_ingt0 n);
       n_outgt0 := (n_outgt0 n);
    |}.
  Next Obligation.
    eapply unnest_equations_vars_perm with (st:=init_st) in Hwl. 2: eapply surjective_pairing.
    specialize (n_defd n) as Hperm'.
    unfold st_ids, idty in *. rewrite init_st_anns in Hwl. rewrite app_nil_r in Hwl.
    etransitivity. apply Hwl.
    rewrite Permutation_app_comm. symmetry.
    rewrite <- app_assoc. rewrite Permutation_swap.
    repeat rewrite map_app in *.
    rewrite Hperm'. reflexivity.
  Qed.
  Next Obligation.
    remember (unnest_equations G (n_eqs n) init_st) as res.
    assert (st_valid_reuse (snd res) (PSP.of_list (map fst (n_in n ++ n_vars n ++ n_out n)))
                           PS.empty) as Hvalid.
    { specialize (n_nodup n) as Hndup. rewrite fst_NoDupMembers in Hndup.
      repeat rewrite map_app in Hndup.
      subst. eapply unnest_equations_st_valid.
      2: eapply surjective_pairing.
      2: eapply init_st_valid_reuse.
      - rewrite PSP.elements_empty, app_nil_r.
        repeat ndup_r Hndup.
      - replace (ps_adds _ PS.empty) with (ps_from_list (map fst (anon_in_eqs (n_eqs n)))); auto.
        rewrite ps_from_list_ps_of_list.
        repeat rewrite ps_of_list_ps_to_list_Perm; repeat rewrite map_app; repeat rewrite <- app_assoc in *; auto.
        repeat ndup_r Hndup.
        repeat rewrite app_assoc in Hndup. apply NoDup_app_l in Hndup.
        repeat rewrite <- app_assoc in Hndup; auto.
      - apply norm1_not_in_elab_prefs.
      - rewrite <- ps_from_list_ps_of_list, PS_For_all_Forall', <- Hpref.
        pose proof (n_good n) as (Good&_).
        eapply Forall_incl; [eauto|].
        repeat rewrite map_app.
        repeat apply incl_tl.
        repeat rewrite app_assoc. apply incl_appl. reflexivity.
      - replace (ps_adds _ PS.empty) with (ps_from_list (map fst (anon_in_eqs (n_eqs n)))); auto.
        rewrite PS_For_all_Forall', <- Hpref.
        pose proof (n_good n) as (Good&_).
        eapply Forall_incl; [eauto|].
        repeat rewrite map_app.
        repeat apply incl_tl.
        repeat apply incl_appr. reflexivity.
    }
    destruct res as [eqs st']. simpl in *.
    apply st_valid_reuse_NoDup in Hvalid.
    unfold PSP.to_list in Hvalid. rewrite PSP.elements_empty, app_nil_r in Hvalid.
    specialize (n_nodup n) as Hndup.
    rewrite ps_of_list_ps_to_list_Perm in Hvalid.
    - rewrite fst_NoDupMembers.
      repeat rewrite map_app in *.
      unfold idty, st_ids in *; simpl.
      rewrite <- app_assoc, app_assoc, Permutation_swap, <- app_assoc.
      assert (anon_in_eqs eqs = []).
      { symmetry in Heqres. eapply unnest_equations_no_anon in Heqres; eauto. }
      rewrite H; simpl. rewrite app_nil_r. assumption.
    - rewrite <- fst_NoDupMembers.
      repeat rewrite app_assoc in *.
      apply NoDupMembers_app_l in Hndup; auto.
  Qed.
  Next Obligation.
    specialize (n_good n) as (Hgood&Hname). split; auto.
    repeat rewrite map_app, Forall_app in Hgood. destruct Hgood as (?&?&?&?).
    destruct (unnest_equations G (n_eqs n) init_st) as (eqs&st') eqn:Heqres.
    assert (st_valid_reuse st' (PSP.of_list (map fst (n_in n ++ n_vars n ++ n_out n)))
                           PS.empty) as Hvalid.
    { specialize (n_nodup n) as Hndup. rewrite fst_NoDupMembers in Hndup.
      repeat rewrite map_app in Hndup.
      subst. eapply unnest_equations_st_valid.
      2: eauto.
      2: eapply init_st_valid_reuse.
      - rewrite PSP.elements_empty, app_nil_r.
        repeat ndup_r Hndup.
      - replace (ps_adds _ PS.empty) with (ps_from_list (map fst (anon_in_eqs (n_eqs n)))); auto.
        rewrite ps_from_list_ps_of_list.
        repeat rewrite ps_of_list_ps_to_list_Perm; repeat rewrite map_app; repeat rewrite <- app_assoc in *; auto.
        repeat ndup_r Hndup.
        repeat rewrite app_assoc in Hndup. apply NoDup_app_l in Hndup.
        repeat rewrite <- app_assoc in Hndup; auto.
      - apply norm1_not_in_elab_prefs.
      - rewrite <- ps_from_list_ps_of_list, PS_For_all_Forall', <- Hpref.
        pose proof (n_good n) as (Good&_).
        eapply Forall_incl; [eauto|].
        repeat rewrite map_app.
        repeat apply incl_tl.
        repeat rewrite app_assoc. apply incl_appl. reflexivity.
      - replace (ps_adds _ PS.empty) with (ps_from_list (map fst (anon_in_eqs (n_eqs n)))); auto.
        rewrite PS_For_all_Forall', <- Hpref.
        pose proof (n_good n) as (Good&_).
        eapply Forall_incl; [eauto|].
        repeat rewrite map_app.
        repeat apply incl_tl.
        repeat apply incl_appr. reflexivity.
    }
    erewrite unnested_equations_no_anon. 2:eapply unnest_equations_unnested_eq; eauto.
    rewrite app_nil_r.
    pose proof (n_good n) as (Good&_). rewrite Hpref in Good.
    repeat rewrite map_app, Forall_app in *. destruct Good as (?&?&?&_).
    repeat split; auto using AtomOrGensym_add.
    eapply st_valid_reuse_prefixed in Hvalid.
    rewrite Hpref. auto.
  Qed.

  Fixpoint unnest_global (G : global) :
    wl_global G ->
    Forall (fun n => n_prefixes n = elab_prefs) G ->
    global.
  Proof.
    destruct G as [|hd tl]; intros Hwl Hprefs.
    - exact [].
    - refine ((unnest_node tl hd _ _)::(unnest_global tl _ _)).
      + inv Hwl; eauto.
      + inv Hprefs; eauto.
      + inv Hwl; eauto.
      + inv Hprefs; eauto.
  Defined.

  (** *** unnest_global produces a global with the correct prefixes *)

  Lemma unnest_global_prefixes : forall G G' Hwl Hprefs,
      unnest_global G Hwl Hprefs = G' ->
      Forall (fun n => n_prefixes n = PS.add norm1 elab_prefs) G'.
  Proof.
    induction G; intros * Hwl; simpl in *; inv Hwl; constructor; simpl; eauto.
    inv Hprefs. congruence.
  Qed.

  (** *** unnest_global produces an equivalent global *)

  Fact unnest_global_eq : forall G Hwt Hprefs,
      global_iface_eq G (unnest_global G Hwt Hprefs).
  Proof.
    induction G; intros Hwt Hprefs.
    - reflexivity.
    - simpl. apply global_iface_eq_cons; auto.
  Qed.

  Fact unnest_global_names : forall a G Hwt Hprefs,
      Forall (fun n => (n_name a <> n_name n)%type) G ->
      Forall (fun n => (n_name a <> n_name n)%type) (unnest_global G Hwt Hprefs).
  Proof.
    induction G; intros * Hnames; simpl.
    - constructor.
    - inv Hnames.
      constructor; eauto.
  Qed.

  (** *** After normalization, a global is unnested *)

  Lemma iface_eq_unnested_equation : forall G G' eq,
      global_iface_eq G G' ->
      unnested_equation G eq ->
      unnested_equation G' eq.
  Proof.
    intros * Heq Hunt.
    inv Hunt; try constructor; eauto.
    specialize (Heq f).
    rewrite H0 in Heq. inv Heq. destruct H5 as (_&_&?&_).
    econstructor; eauto. congruence.
  Qed.

  Corollary iface_eq_unnested_node : forall G G' n,
      global_iface_eq G G' ->
      unnested_node G n ->
      unnested_node G' n.
  Proof.
    intros * Hglob Hunt.
    unfold unnested_node in *.
    eapply Forall_impl; [|eauto]. intros.
    eapply iface_eq_unnested_equation; eauto.
  Qed.

  Lemma unnest_node_unnested_node : forall G n Hwl Hprefs,
      unnested_node G (unnest_node G n Hwl Hprefs).
  Proof.
    intros *.
    unfold unnest_node.
    unfold unnested_node; simpl.
    eapply unnest_equations_unnested_eq; eauto.
    apply surjective_pairing.
  Qed.

  Lemma unnest_global_unnested_global : forall G Hwl Hprefs,
      unnested_global (unnest_global G Hwl Hprefs).
  Proof.
    induction G; intros *; constructor.
    - eapply iface_eq_unnested_node. eapply unnest_global_eq. apply unnest_node_unnested_node.
    - apply IHG.
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

  Fact unnested_equation_not_nil : forall G eq,
      unnested_equation G eq ->
      wl_equation G eq ->
      fst eq <> [].
  Proof.
    intros * Hunt Hwl contra.
    inv Hunt; simpl in *; subst. 3,4:congruence.
    1-2:(destruct Hwl as [Hwl1 Hwl2]; try rewrite app_nil_r in Hwl2; simpl in Hwl2;
       apply Forall_singl in Hwl1; inv Hwl1).
    - specialize (n_outgt0 n) as Hout.
      rewrite H11 in H0. inv H0.
      apply (Nat.lt_irrefl (length (n_out n))). rewrite <- H13 at 1. setoid_rewrite <- Hwl2; auto.
    - inv contra.
  Qed.

  (** ** fresh_ins appear in the state after normalisation *)

  Fact unnest_reset_fresh_incl : forall k e e' eqs' st st',
      (forall es' eqs' st st',
          k e st = (es', eqs', st') ->
          incl (fresh_in e) (st_anns st')) ->
      unnest_reset k e st = (e', eqs', st') ->
      incl (fresh_in e) (st_anns st').
  Proof.
    intros * Hkincl Hun.
    unnest_reset_spec; simpl; eauto.
    eapply fresh_ident_st_follows, st_follows_incl in Hfresh; eauto.
    etransitivity; eauto.
  Qed.

  Ltac solve_st_follows :=
    match goal with
    | |- incl (st_anns ?st1) (st_anns ?st2) =>
      eapply st_follows_incl
    | |- st_follows ?st ?st =>
      reflexivity
    | H : st_follows ?st1 ?st2 |- st_follows ?st1 _ =>
      etransitivity; [eapply H |]
    | H : fresh_ident _ _ ?st = _ |- st_follows ?st _ =>
      etransitivity; [ eapply fresh_ident_st_follows in H; eauto | ]
    | H : reuse_ident _ _ ?st = _ |- st_follows ?st _ =>
      etransitivity; [ eapply reuse_ident_st_follows in H; eauto | ]
    | H : idents_for_anns _ ?st = _ |- st_follows ?st _ =>
      etransitivity; [ eapply idents_for_anns_st_follows in H; eauto | ]
    | H : idents_for_anns' _ ?st = _ |- st_follows ?st _ =>
      etransitivity; [ eapply idents_for_anns'_st_follows in H; eauto | ]
    | H : unnest_noops_exps _ _ ?st = _ |- st_follows ?st _ =>
      etransitivity; [ eapply unnest_noops_exps_st_follows in H; eauto | ]
    | H : map_bind2 _ _ ?st = _ |- st_follows ?st _ =>
      etransitivity; [ eapply map_bind2_st_follows in H; eauto; solve_forall | ]
    | H : unnest_exp _ _ _ ?st = _ |- st_follows ?st _ =>
      etransitivity; [ eapply unnest_exp_st_follows in H; eauto |]
    | H : unnest_exps _ _ ?st = _ |- st_follows ?st _ =>
      etransitivity; [ eapply unnest_exps_st_follows in H; eauto |]
    | H : unnest_rhs _ _ _ ?st = _ |- st_follows ?st _ =>
      etransitivity; [ eapply unnest_rhs_st_follows in H; eauto |]
    | H : unnest_rhss _ _ _ ?st = _ |- st_follows ?st _ =>
      etransitivity; [ eapply unnest_rhss_st_follows in H; eauto |]
    | H : unnest_equation _ _ ?st = _ |- st_follows ?st _ =>
      etransitivity; [ eapply unnest_equation_st_follows in H; eauto |]
    | H: map_bind _ _ ?st = _ |- st_follows ?st _ =>
      etransitivity; [ eapply map_bind_st_follows in H; eauto; solve_forall |]
    | H : unnest_equations _ _ ?st = _ |- st_follows ?st _ =>
      etransitivity; [ eapply unnest_equations_st_follows in H; eauto |]
    | H : unnest_reset (unnest_exp _ _) _ ?st = _ |- st_follows ?st _ =>
      etransitivity; [ eapply unnest_reset_st_follows in H; eauto |]
    end.

  Fact map_bind2_fresh_incl {B C} : forall (k : exp -> FreshAnn (B * C)) es es' eqs' st st',
      (forall e es' eqs' st st', k e st = (es', eqs', st') -> st_follows st st') ->
      Forall (fun e => forall es' eqs' st st',
                  k e st = (es', eqs', st') ->
                  incl (fresh_in e) (st_anns st')) es ->
      map_bind2 k es st = (es', eqs', st') ->
      incl (fresh_ins es) (st_anns st').
  Proof with eauto.
    induction es; intros * Hk Hf Hmap;
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

  Fact unnest_exp_fresh_incl : forall G e is_control es' eqs' st st',
      unnest_exp G is_control e st = (es', eqs', st') ->
      incl (fresh_in e) (st_anns st').
  Proof with eauto.
    induction e using exp_ind2; intros * Hnorm;
      repeat inv_bind; eauto.
    - (* const *) apply incl_nil'.
    - (* var *) apply incl_nil'.
    - (* binop *)
      apply incl_app; eauto.
      etransitivity...
    - (* fby *)
      repeat apply incl_app.
      + assert (st_follows x1 st') by repeat solve_st_follows.
        apply map_bind2_fresh_incl in H2... 2:solve_forall.
        etransitivity...
      + assert (st_follows x4 st') by repeat solve_st_follows.
        apply map_bind2_fresh_incl in H3... 2:solve_forall.
        etransitivity...
      + eapply map_bind2_fresh_incl in H4... 2:solve_forall.
        etransitivity...
        eapply unnest_reset_fresh_incl...
    - (* arrow *)
      repeat apply incl_app.
      + assert (st_follows x1 st') by repeat solve_st_follows.
        apply map_bind2_fresh_incl in H2... 2:solve_forall.
        etransitivity...
      + assert (st_follows x4 st') by repeat solve_st_follows.
        apply map_bind2_fresh_incl in H3... 2:solve_forall.
        etransitivity...
      + eapply map_bind2_fresh_incl in H4... 2:solve_forall.
        etransitivity...
        eapply unnest_reset_fresh_incl...
    - (* when *)
      destruct a; repeat inv_bind.
      apply map_bind2_fresh_incl in H0... solve_forall.
    - (* merge *)
      destruct a; repeat inv_bind.
      assert (st_follows x2 x5) by repeat solve_st_follows.
      apply map_bind2_fresh_incl in H1...
      apply map_bind2_fresh_incl in H2... 2,3:solve_forall.
      assert (st_follows x5 st').
      { destruct is_control; repeat inv_bind; repeat solve_st_follows. }
      eapply incl_app; etransitivity; eauto. etransitivity...
    - (* ite *)
      destruct a; repeat inv_bind.
      assert (st_follows x1 x4) by repeat solve_st_follows.
      assert (st_follows x4 x7) by repeat solve_st_follows.
      eapply IHe in H1.
      eapply map_bind2_fresh_incl in H2...
      eapply map_bind2_fresh_incl in H3... 2,3:solve_forall.
      assert (st_follows x7 st').
      { destruct is_control; repeat inv_bind; repeat solve_st_follows. }
      repeat eapply incl_app; repeat (etransitivity; eauto).
    - (* app *)
      apply map_bind2_fresh_incl in H1... 2:solve_forall.
      assert (st_follows x7 st') by repeat solve_st_follows.
      assert (st_follows x4 st') by repeat solve_st_follows.
      apply map_bind2_fresh_incl in H3... 2:solve_forall; eapply unnest_reset_fresh_incl...
      repeat inv_bind; repeat eapply incl_app; simpl in *.
      3:eapply idents_for_anns'_fresh_incl...
      2:etransitivity; eauto.
      etransitivity; eauto; repeat solve_st_follows.
  Qed.

  Corollary map_bind2_unnest_exp_fresh_incl : forall G es is_control es' eqs' st st',
      map_bind2 (unnest_exp G is_control) es st = (es', eqs', st') ->
      incl (fresh_ins es) (st_anns st').
  Proof.
    intros * Hmap.
    apply map_bind2_fresh_incl in Hmap; eauto.
    solve_forall. apply unnest_exp_fresh_incl in H0; auto.
  Qed.

  Corollary unnest_exps_fresh_incl : forall G es es' eqs' st st',
      unnest_exps G es st = (es', eqs', st') ->
      incl (fresh_ins es) (st_anns st').
  Proof.
    intros * Hnorm.
    unfold unnest_exps in Hnorm; repeat inv_bind.
    apply map_bind2_unnest_exp_fresh_incl in H; auto.
  Qed.

  (** ** Preservation of clockof *)

  Fact unnest_exp_clockof : forall G e is_control es' eqs' st st',
      wl_exp G e ->
      unnest_exp G is_control e st = (es', eqs', st')  ->
      clocksof es' = clockof e.
  Proof with eauto.
    intros * Hwl Hnorm.
    eapply unnest_exp_annot in Hnorm...
    rewrite clocksof_annots, Hnorm, <- clockof_annot...
  Qed.
  Hint Resolve unnest_exp_clockof.
End UNNESTING.

Module UnnestingFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Syn : LSYNTAX Ids Op)
<: UNNESTING Ids Op OpAux Syn.
  Include UNNESTING Ids Op OpAux Syn.
End UnnestingFun.
