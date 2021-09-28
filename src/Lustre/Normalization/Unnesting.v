From Coq Require Import List Sorting.Permutation.
Import List.ListNotations.
Open Scope list_scope.
Require Import Omega.

From Coq Require Import Setoid Morphisms.

From Velus Require Import Common Environment.
From Velus Require Import CommonTyping.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Lustre.LSyntax.
From Velus Require Fresh.

(** * Normalization procedure *)

Module Type UNNESTING
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Import Cks : CLOCKS Ids Op OpAux)
       (Import Syn : LSYNTAX Ids Op OpAux Cks).

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
    repeat progress
           (try rewrite map_app in *; try rewrite idck_app in *;
            try rewrite <-app_assoc in *;
            try rewrite map_fst_idck in *).
  Ltac solve_ndup :=
    ndup_simpl; solve_NoDup_app.

  Definition default_ann : ann := (OpAux.bool_velus_type, (Cbase, None)).

  (** Fresh ident generation keeping type annotations *)
  Definition FreshAnn A := Fresh A (type * clock).

  Definition hd_default (l : list exp) : exp :=
    hd (Eenum 0 OpAux.bool_velus_type) l.

  Fixpoint idents_for_anns (anns : list ann) : FreshAnn (list (ident * ann)) :=
    match anns with
    | [] => ret []
    | (ty, (cl, name))::tl => do x <- fresh_ident norm1 None (ty, cl);
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
    | (ty, (ck, None))::tl => do x <- fresh_ident norm1 None (ty, ck);
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
      | e => let '(ty, (ck, _)) := hd (OpAux.bool_velus_type, (Cbase, None)) (annot e) in
            do x <- fresh_ident norm1 None (ty, ck);
            ret (Evar x (ty, (ck, Some x)), ([x], [e])::eqs1)
      end.

  Lemma unnest_reset_spec : forall k e es' eqs' st st',
      k e st = ((es', eqs'), st') ->
      (exists v, exists ann, (hd_default es') = Evar v ann /\ unnest_reset k e st = ((Evar v ann, eqs'), st'))
      \/ exists ty ck o x st'', hd (OpAux.bool_velus_type, (Cbase, None)) (annot (hd_default es')) = (ty, (ck, o)) /\
                          fresh_ident norm1 None (ty, ck) st' = (x, st'') /\
                          unnest_reset k e st = ((Evar x (ty, (ck, Some x)), ([x], [hd_default es'])::eqs'), st'').
  Proof.
    intros * Hk.
    unfold unnest_reset; simpl.
    destruct (hd_default es') eqn:Hes'.
    1-2,4-11:
      (right; destruct (hd _) as [ty [ck ?]] eqn:Hx; simpl;
       destruct (fresh_ident norm1 None (ty, ck) st') as [x st''] eqn:Hfresh;
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

  Definition unnest_fby (e0s : list exp) (es : list exp) (anns : list ann) :=
    map (fun '((e0, e), a) => Efby [e0] [e] [a]) (combine (combine e0s es) anns).

  Definition unnest_arrow (e0s : list exp) (es : list exp) (anns : list ann) :=
    map (fun '((e0, e), a) => Earrow [e0] [e] [a]) (combine (combine e0s es) anns).

  Definition unnest_when ckid b es tys ck :=
    map (fun '(e, ty) => Ewhen [e] ckid b ([ty], ck)) (combine es tys).

  Fixpoint unnest_merge ckid es tys ck :=
    match tys with
    | [] => []
    | ty::tys => (Emerge ckid (List.map (fun '(i, es) => (i, [hd_default es])) es) ([ty], ck))
                 ::(unnest_merge ckid (List.map (fun '(i, es) => (i, tl es)) es) tys ck)
    end.

  Fixpoint unnest_case e es d tys ck :=
    match tys with
    | [] => []
    | ty::tys => (Ecase e (List.map (fun '(i, es) => (i, [hd_default es])) es) (option_map (fun d => [hd_default d]) d) ([ty], ck))
                 ::(unnest_case e (List.map (fun '(i, es) => (i, tl es)) es) (option_map (@tl _) d) tys ck)
    end.

  Hint Unfold unnest_when unnest_merge unnest_case.

  Fixpoint is_noops_exp (ck: clock) (e : exp) : bool :=
    match ck with
    | Cbase => true
    | Con ck' _ _ =>
      match e with
      | Econst _ | Eenum _ _ | Evar _ _ => true
      | Ewhen [e'] _ _ _ => is_noops_exp ck' e'
      | _ => false
      end
    end.

  Definition find_node_incks (G: @global nolocal_top_block local_prefs) (f : ident) : list clock :=
    match find_node f G with
    | Some n => map (fun '(_, (_, ck, _)) => ck) (n_in n)
    | None => []
    end.

  Definition unnest_noops_exp (cki: clock) (e : exp) : FreshAnn (exp * list equation) :=
    let '(ty, (ck, o)) := hd (OpAux.bool_velus_type, (Cbase, None)) (annot e) in
    if is_noops_exp cki e then ret (e, [])
    else do x <- fresh_ident norm1 None (ty, ck);
         ret (Evar x (ty, (ck, o)), [([x], [e])]).

  Definition unnest_noops_exps (ckis : list clock) (es : list exp) : FreshAnn (list exp * list equation) :=
    do (es', eqs') <- mmap2 (fun '(cki, e) => unnest_noops_exp cki e) (combine ckis es);
    ret (es', concat eqs').

  (* For node well-formedness, we need all the xs to be there *)
  Fixpoint mk_equations (xs : list ident) (es : list exp) :=
    match xs with
    | [] => []
    | x::xs => ([x], [hd_default es])::(mk_equations xs (tl es))
    end.

  Fixpoint unnest_exp G (is_control : bool) (e : exp) {struct e} : FreshAnn (list exp * list equation) :=
    let unnest_exps := fun es => do (es, eqs) <- mmap2 (unnest_exp G false) es; ret (concat es, concat eqs) in
    let unnest_controls := fun es => do (es, eqs) <- mmap2 (unnest_exp G true) es; ret (concat es, concat eqs) in
    let unnest_resets := fun es => do (es, eqs) <- mmap2 (unnest_reset (unnest_exp G true)) es; ret (es, concat eqs) in
    match e with
    | Econst c => ret ([Econst c], [])
    | Eenum k ty => ret ([Eenum k ty], [])
    | Evar v ann => ret ([Evar v ann], [])
    | Eunop op e1 ann =>
      do (e1', eqs) <- unnest_exp G false e1;
      ret ([Eunop op (hd_default e1') ann], eqs)
    | Ebinop op e1 e2 ann =>
      do (e1', eqs1) <- unnest_exp G false e1;
      do (e2', eqs2) <- unnest_exp G false e2;
      ret ([Ebinop op (hd_default e1') (hd_default e2') ann], eqs1++eqs2)
    | Efby e0s es anns =>
      do (e0s', eqs1) <- unnest_exps e0s;
      do (es', eqs2) <- unnest_exps es;
      let fbys := unnest_fby e0s' es' anns in
      do xs <- idents_for_anns anns;
      ret (List.map (fun '(x, ann) => Evar x ann) xs,
           (mk_equations (map fst xs) fbys)++eqs1++eqs2)
    | Earrow e0s es anns =>
      do (e0s', eqs1) <- unnest_exps e0s;
      do (es', eqs2) <- unnest_exps es;
      let arrows := unnest_arrow e0s' es' anns in
      do xs <- idents_for_anns anns;
      ret (List.map (fun '(x, ann) => Evar x ann) xs,
           (mk_equations (map fst xs) arrows)++eqs1++eqs2)
    | Ewhen es ckid b (tys, ck) =>
      do (es', eqs) <- unnest_exps es;
      ret (unnest_when ckid b es' tys ck, eqs)
    | Emerge ckid es (tys, cl) =>
      do (es', eqs1) <- mmap2 (fun '(i, es) => do (es', eqs') <- mmap2 (unnest_exp G true) es;
                                           ret (i, concat es', concat eqs')) es;
      let merges := unnest_merge ckid es' tys cl in
      if is_control then
        ret (merges, concat eqs1)
      else
        do xs <- idents_for_anns (List.map (fun ty => (ty, cl)) tys);
        ret (List.map (fun '(id, ann) => Evar id ann) xs,
             (mk_equations (map fst xs) merges)++concat eqs1)
    | Ecase e es d (tys, ck) =>
      do (e', eqs0) <- unnest_exp G false e;
      do (es', eqs1) <- mmap2 (fun '(i, es) => do (es', eqs') <- mmap2 (unnest_exp G true) es;
                                           ret (i, concat es', concat eqs')) es;
      do (d', eqs2) <- or_default_with (ret (None, [])) (fun d => do (d', eqs') <- unnest_controls d; ret (Some d', eqs')) d;
      let cases :=  unnest_case (hd_default e') es' d' tys ck in
      if is_control then
        ret (cases, eqs0++concat eqs1++eqs2)
      else
        do xs <- idents_for_anns (List.map (fun ty => (ty, ck)) tys);
        ret (List.map (fun '(id, ann) => Evar id ann) xs,
             (mk_equations (map fst xs) cases)++eqs0++concat eqs1++eqs2)
    | Eapp f es er anns =>
      do (es', eqs1) <- unnest_exps es;
      do (es', eqs2) <- unnest_noops_exps (find_node_incks G f) es';
      do (er', eqs3) <- unnest_resets er;
      do xs <- idents_for_anns' anns;
      ret (List.map (fun '(id, ann) => Evar id ann) xs,
           (List.map fst xs, [Eapp f es' er' (List.map snd xs)])::eqs1++eqs2++eqs3)
    end.

  Definition unnest_exps G (es : list exp) :=
    do (es, eqs) <- mmap2 (unnest_exp G false) es;
    ret (concat es, concat eqs).

  Definition unnest_rhs G (e : exp) : FreshAnn (list exp * list equation) :=
    let unnest_resets := fun es => do (es, eqs) <- mmap2 (unnest_reset (unnest_exp G true)) es; ret (es, concat eqs) in
    match e with
    | Eapp f es er anns =>
      do (es', eqs1) <- unnest_exps G es;
      do (es', eqs2) <- unnest_noops_exps (find_node_incks G f) es';
      do (er', eqs3) <- unnest_resets er;
      ret ([Eapp f es' er' anns], eqs1++eqs2++eqs3)
    | Efby e0s es anns =>
      do (e0s', eqs1) <- unnest_exps G e0s;
      do (es', eqs2) <- unnest_exps G es;
      let fbys := unnest_fby e0s' es' anns in
      ret (fbys, eqs1++eqs2)
    | Earrow e0s es anns =>
      do (e0s', eqs1) <- unnest_exps G e0s;
      do (es', eqs2) <- unnest_exps G es;
      let arrows := unnest_arrow e0s' es' anns in
      ret (arrows, eqs1++eqs2)
    | _ => unnest_exp G true e
    end.

  Definition unnest_rhss G (es : list exp) :=
    do (es, eqs) <- mmap2 (unnest_rhs G) es; ret (concat es, concat eqs).

  (* Again, for node well-formedness, we need all the xs to be there *)
  Fixpoint combine_for_numstreams {B} (es : list exp) (vs : list B) :=
    match es with
    | [] => List.map (fun v => (hd_default es, [v])) vs
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

  Fixpoint unnest_block G (d : block) : FreshAnn (list block) :=
    match d with
    | Beq e =>
      do eqs' <- unnest_equation G e;
      ret (map Beq eqs')
    | Breset blocks er =>
      do blocks' <- mmap (unnest_block G) blocks;
      do (er', eqs') <- unnest_reset (unnest_exp G true) er;
      ret ((map (fun d => Breset [d] er') (concat blocks'))++map Beq eqs')
    | _ => (* Should not happen *) ret [d]
    end.

  Definition unnest_blocks G (blocks : list block) : FreshAnn (list block) :=
    do blocks' <- mmap (unnest_block G) blocks;
    ret (concat blocks').

  (** ** mk_equations properties *)

  Lemma mk_equations_map_fst : forall xs es,
      concat (map fst (mk_equations xs es)) = xs.
  Proof.
    induction xs; intros; simpl; f_equal; auto.
  Qed.

  Lemma mk_equations_length : forall xs es,
      length (mk_equations xs es) = length xs.
  Proof.
    induction xs; intros; simpl; f_equal; auto.
  Qed.

  Lemma mk_equations_In : forall v xs es,
      length xs = length es ->
      In v (mk_equations xs es) ->
      exists x e, v = ([x], [e]) /\ In x xs /\ In e es.
  Proof.
    induction xs as [|x xs]; intros * Hlen Hin; simpl in *; inv Hin.
    - destruct es; simpl in *; try congruence.
      exists x. exists e. auto.
    - destruct es; simpl in *; try congruence.
      inv Hlen. apply IHxs in H as (x'&e'&?&?&?); auto.
      exists x'. exists e'. auto.
  Qed.

  Lemma mk_equations_Forall : forall P xs es,
      Forall2 (fun x e => P ([x], [e])) xs es ->
      Forall P (mk_equations xs es).
  Proof.
    intros * Hf.
    induction Hf; simpl; constructor; auto.
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

  Definition st_valid_reuse {B} st aft reusable := @st_valid_reuse B st norm1 aft local_prefs reusable.
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
    eapply mmap2_st_valid_reuse; eauto.
    eapply Forall_forall. intros (?&?) _ * Hun Hval'.
    eapply unnest_noops_exp_st_valid; eauto.
  Qed.

  Fact mmap2_st_valid_reuse' {E A B} :
    forall (k : E -> list (ident * B)) (f : E -> FreshAnn (A * list equation)) es es' eqs' st st' aft reusable,
      Forall (fun e =>
                forall es' eqs' st st' aft reusable,
                  NoDup (map fst (k e)++PS.elements reusable) ->
                  f e st = (es', eqs', st') ->
                  st_valid_reuse st aft (ps_adds (map fst (k e)) reusable) ->
                  st_valid_reuse st' aft reusable) es ->
      NoDup (map fst (flat_map k es)++PS.elements reusable) ->
      mmap2 f es st = (es', eqs', st') ->
      st_valid_reuse st aft (ps_adds (map fst (flat_map k es)) reusable) ->
      st_valid_reuse st' aft reusable.
  Proof.
    induction es; intros es' eqs' st st' aft reusable Hf Hnd Hmap Hvalid;
      repeat inv_bind; auto.
    inv Hf.
    ndup_simpl.
    unfold st_valid_reuse in *.
    rewrite ps_adds_app in Hvalid; eauto.
    eapply IHes in H4; eauto; try solve_ndup. eapply H3; eauto.
    rewrite Permutation_PS_elements_ps_adds'; eauto.
    solve_ndup.
  Qed.

  Local Ltac solve_st_valid :=
    repeat inv_bind;
    match goal with
    | H : mmap2 _ _ _ = (_, _, ?st) |- st_valid_reuse ?st _ _ =>
      eapply mmap2_st_valid_reuse' in H; eauto; solve_forall
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
    - (* enum *)
      repeat inv_bind...
    - (* var *)
      repeat inv_bind...
    - (* unop *)
      repeat inv_bind...
    - (* binop *)
      repeat inv_bind. ndup_simpl.
      rewrite ps_adds_app in *...
      eapply IHe2... solve_ndup. eapply IHe1...
      rewrite Permutation_PS_elements_ps_adds'... solve_ndup.
    - (* fby *)
      repeat inv_bind. ndup_simpl.
      repeat rewrite ps_adds_app in Hvalid.
      repeat solve_st_valid. solve_ndup.
      repeat rewrite Permutation_PS_elements_ps_adds'; auto. solve_ndup.
    - (* arrow *)
      repeat inv_bind. ndup_simpl.
      repeat rewrite ps_adds_app in Hvalid.
      repeat solve_st_valid. solve_ndup.
      repeat rewrite Permutation_PS_elements_ps_adds'; auto. solve_ndup.
    - (* when *)
      destruct a.
      repeat inv_bind; repeat solve_st_valid.
    - (* merge *)
      destruct a. ndup_simpl.
      destruct is_control; repeat solve_st_valid.
    - (* case *)
      destruct a. ndup_simpl.
      assert (NoDup (map fst (fresh_in e)++PS.elements reusable)) by solve_ndup.
      assert (NoDup (map fst (flat_map (fun es => fresh_ins (snd es)) es)++PS.elements reusable)) by solve_ndup.
      assert (NoDup (map fst (or_default_with [] (flat_map fresh_in) d) ++ PS.elements reusable)) by solve_ndup.
      repeat inv_bind.
      assert (st_valid_reuse x7 aft reusable) as Hvalid'.
      { rewrite ps_adds_app in Hvalid.
        eapply IHe in H4; [| |eauto]. rewrite ps_adds_app in H4.
        eapply mmap2_st_valid_reuse' in H5. 4:eauto. 2:solve_forall; solve_st_valid.
        destruct d; repeat inv_bind; auto.
        solve_st_valid.
        1,2:rewrite Permutation_PS_elements_ps_adds'. 1-4:solve_ndup. }
      destruct is_control; repeat inv_bind; repeat solve_st_valid; auto.
    - (* app *)
      repeat inv_bind.
      eapply idents_for_anns'_st_valid; eauto. solve_ndup.
      eapply mmap2_st_valid_reuse' in H3; eauto.
      1:{ eapply Forall_impl; [|eapply H0]. intros.
          eapply unnest_reset_st_valid in H7; eauto. }
      rewrite Permutation_PS_elements_ps_adds'. 1,2:solve_ndup.
      repeat solve_st_valid.
      2:repeat rewrite map_app, ps_adds_app in *; eauto.
      repeat rewrite Permutation_PS_elements_ps_adds'; eauto.
      1-4:solve_ndup.
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
      repeat rewrite ps_adds_app in Hvalid; repeat solve_st_valid.
      1,2:repeat rewrite Permutation_PS_elements_ps_adds'; eauto.
      1,2:solve_ndup.
    - (* arrow *)
      ndup_simpl.
      repeat inv_bind.
      repeat rewrite ps_adds_app in Hvalid; repeat solve_st_valid.
      1,2:repeat rewrite Permutation_PS_elements_ps_adds'; eauto.
      1,2:solve_ndup.
    - (* app *)
      repeat inv_bind.
      eapply mmap2_st_valid_reuse' in H1; eauto.
      1:{ eapply Forall_forall; intros.
          eapply unnest_reset_st_valid in H4; eauto. } solve_ndup.
      repeat solve_st_valid.
      2:rewrite <- ps_adds_app, <- map_app; auto.
      rewrite Permutation_PS_elements_ps_adds'.
      rewrite map_app, <- app_assoc in Hnd; auto.
      solve_ndup.
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
    eapply mmap2_st_valid_reuse' in H; eauto.
    apply Forall_forall. intros; eauto.
  Qed.
  Hint Resolve unnest_equation_st_valid.

  Fact unnest_block_st_valid : forall G d blocks' st st' aft reusable,
      NoDup (map fst (local_anon_in_block d)++PS.elements reusable) ->
      unnest_block G d st = (blocks', st') ->
      st_valid_reuse st aft (ps_adds (map fst (local_anon_in_block d)) reusable) ->
      st_valid_reuse st' aft reusable.
  Proof.
    induction d using block_ind2; intros * Hnd Hnorm Hvalid; simpl in *;
      repeat inv_bind.
    - eapply unnest_equation_st_valid in H; eauto.
    - rewrite map_app, ps_adds_app in Hvalid.
      eapply unnest_reset_st_valid in H1; eauto.
      1:{ intros. eapply unnest_exp_st_valid in H2; eauto. solve_ndup. }
      clear H1.
      revert st x x0 H0 Hvalid.
      induction H; intros; simpl in *; repeat inv_bind; auto.
      eapply IHForall in H2; eauto. solve_ndup.
      eapply H; eauto.
      2:rewrite map_app, ps_adds_app in Hvalid; auto.
      repeat rewrite Permutation_PS_elements_ps_adds'; ndup_simpl; auto.
      1-3:solve_ndup.
    - eapply st_valid_reuse_PSSubset; eauto.
      intros ? Hin; auto.
  Qed.

  Corollary unnest_blocks_st_valid : forall G blocks res st st' aft reusable,
      NoDup (map fst (flat_map anon_in_block blocks)++PS.elements reusable) ->
      unnest_blocks G blocks st = (res, st') ->
      st_valid_reuse st aft (ps_adds (map fst (flat_map local_anon_in_block blocks)) reusable) ->
      st_valid_reuse st' aft reusable.
  Proof.
    induction blocks; intros * Hndup Hnorm Hvalid;
      unfold unnest_blocks in Hnorm; repeat inv_bind; auto.
    - ndup_simpl.
      rewrite ps_adds_app in Hvalid.
      eapply IHblocks; eauto. solve_ndup.
      unfold unnest_blocks; repeat inv_bind; repeat eexists; eauto.
      eapply unnest_block_st_valid; eauto.
      assert (NoDup (map fst (local_anon_in_block a) ++ map fst (flat_map local_anon_in_block blocks) ++ CommonPS.PS.elements reusable)) as Hnd'.
      { rewrite app_assoc in *. eapply NoDup_app'; eauto using NoDup_app_r.
        - eapply NoDup_app_l in Hndup. rewrite <-map_app, <-fst_NoDupMembers in *.
          eapply (local_anons_in_block_NoDupMembers (a::blocks)); eauto.
        - eapply Forall_forall; intros.
          eapply NoDup_app_In in Hndup; eauto.
          rewrite <-map_app in *.
          eapply incl_map; eauto.
          eapply (local_anons_in_block_incl (a::blocks)); eauto.
      }
      rewrite Permutation_PS_elements_ps_adds'; auto. solve_ndup.
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
    eapply mmap2_st_follows; eauto.
    eapply Forall_forall. intros (?&?) _ * Hun; eauto.
  Qed.
  Hint Resolve unnest_noops_exps_st_follows.

  Local Ltac solve_st_follows' :=
    repeat inv_bind;
    match goal with
    | |- st_follows ?st ?st =>
      reflexivity
    | H : st_follows ?st1 ?st2 |- st_follows ?st1 _ =>
      etransitivity; [eapply H |]
    | H : fresh_ident _ _ _ ?st = _ |- st_follows ?st _ =>
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
    | H : mmap2 _ _ ?st = _ |- st_follows ?st _ =>
      etransitivity; [ eapply mmap2_st_follows in H; eauto; solve_forall | ]
    end.

  Fact unnest_exp_st_follows : forall G e is_control res st st',
      unnest_exp G is_control e st = (res, st') ->
      st_follows st st'.
  Proof with eauto.
    induction e using exp_ind2; intros is_control res st st' Hnorm;
      simpl in Hnorm.
    - (* const *) now repeat inv_bind.
    - (* enum *) now repeat inv_bind.
    - (* var *) now repeat inv_bind.
    - (* unop *)
      repeat inv_bind...
    - (* binop *)
      repeat inv_bind; etransitivity...
    - (* fby *) repeat solve_st_follows'.
    - (* arrow *) repeat solve_st_follows'.
    - (* when *)
      destruct a. repeat solve_st_follows'.
    - (* merge *)
      destruct a.
      destruct is_control; repeat solve_st_follows'.
    - (* case *)
      destruct a.
      destruct is_control; repeat inv_bind;
        (etransitivity; [ eapply IHe; eauto | repeat solve_st_follows' ]).
      1,2:destruct d; repeat inv_bind; repeat solve_st_follows'.
    - (* app *)
      repeat inv_bind.
      etransitivity; eauto. repeat solve_st_follows'.
  Qed.
  Hint Resolve unnest_exp_st_follows.

  Corollary unnest_reset_st_follows : forall G b e res st st',
      unnest_reset (unnest_exp G b) e st = (res, st') ->
      st_follows st st'.
  Proof.
    intros * Hunn.
    apply unnest_reset_st_follows' in Hunn; auto.
    intros. eapply unnest_exp_st_follows; eauto.
  Qed.

  Corollary unnest_exps_st_follows : forall G es res st st',
      unnest_exps G es st = (res, st') ->
      st_follows st st'.
  Proof.
    intros * Hnorm.
    unfold unnest_exps in Hnorm. repeat inv_bind.
    eapply mmap2_st_follows; eauto.
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

  Lemma unnest_block_st_follows : forall G bck res st st',
      unnest_block G bck st = (res, st') ->
      st_follows st st'.
  Proof.
    induction bck using block_ind2; intros * Hun;
      repeat inv_bind; eauto.
    - eapply mmap_st_follows in H0; eauto.
      eapply unnest_reset_st_follows' in H1; eauto.
      etransitivity; eauto.
    - reflexivity.
  Qed.
  Hint Resolve unnest_block_st_follows.

  Corollary unnest_blocks_st_follows : forall G blocks res st st',
      unnest_blocks G blocks st = (res, st') ->
      st_follows st st'.
  Proof.
    intros * Hnorm.
    unfold unnest_blocks in Hnorm; repeat inv_bind.
    eapply mmap_st_follows; eauto.
    solve_forall.
  Qed.

  (** ** What do we know about the identifiers inside the state? *)

  Lemma fresh_ident_prefixed {B} P : forall (ann: B) id st st',
      Forall (fun id => P id \/ exists x hint, id = gensym norm1 hint x) (st_ids st) ->
      fresh_ident norm1 None ann st = (id, st') ->
      Forall (fun id => P id \/ exists x hint, id = gensym norm1 hint x) (st_ids st').
  Proof.
    intros * Hf Hfresh.
    unfold st_ids in *.
    erewrite fresh_ident_anns; eauto. constructor; auto.
    eapply fresh_ident_prefixed in Hfresh; eauto.
  Qed.

  Corollary idents_for_anns_prefixed P : forall anns ids st st',
      Forall (fun id => P id \/ exists x hint, id = gensym norm1 hint x) (st_ids st) ->
      idents_for_anns anns st = (ids, st') ->
      Forall (fun id => P id \/ exists x hint, id = gensym norm1 hint x) (st_ids st').
  Proof.
    induction anns as [|(?&?&?)]; intros * Hf Hids; repeat inv_bind; auto.
    eapply IHanns in H0; eauto using fresh_ident_prefixed.
  Qed.

  Lemma idents_for_anns'_prefixed : forall anns P ids st st',
      Forall (fun id => P id \/ exists x hint, id = gensym norm1 hint x) (st_ids st) ->
      idents_for_anns' anns st = (ids, st') ->
      Forall (fun id => P id \/ In id (map fst (anon_streams anns)) \/ exists x hint, id = gensym norm1 hint x) (st_ids st').
  Proof.
    induction anns as [|(?&?&[|])]; intros * Hf Hids; repeat inv_bind; auto.
    - eapply Forall_impl; [|eauto]. intros ? [?|?]; auto.
    - eapply IHanns with (P:=fun id => P id \/ i = id) in H0.
      + eapply Forall_impl; [|eauto]; intros ? [[?|?]|[?|?]]; auto.
      + unfold st_ids. destruct x. erewrite Ker.reuse_ident_anns; eauto.
        constructor; auto.
        eapply Forall_impl; [|eauto]; intros ? [?|?]; auto.
    - eapply IHanns in H0; eauto using fresh_ident_prefixed.
  Qed.

  Fact mmap_unnest_prefixed {A1 A2} (unnest : A1 -> FreshAnn A2) (fresh : _ -> list (ident * (type * clock))) : forall xs ys st st' P,
      Forall
        (fun x => forall ys st st' P,
         Forall (fun id : ident => P id \/ (exists x hint, id = gensym norm1 hint x)) (st_ids st) ->
         unnest x st = (ys, st') ->
         Forall (fun id : ident => P id \/ In id (map fst (fresh x)) \/ (exists x hint, id = gensym norm1 hint x)) (st_ids st')) xs ->
      Forall (fun id => P id \/ exists x hint, id = gensym norm1 hint x) (st_ids st) ->
      mmap unnest xs st = (ys, st') ->
      Forall (fun id => P id \/ In id (map fst (flat_map fresh xs)) \/ exists x hint, id = gensym norm1 hint x) (st_ids st').
  Proof.
    induction xs; intros * Hf Hids Hmap; inv Hf; repeat inv_bind.
    - eapply Forall_impl; [|eauto]. intros ? [?|?]; auto.
    - eapply IHxs with (P:=fun id => P id \/ In id (map fst (fresh a))) in H0; eauto.
      + eapply Forall_impl; [|eauto]; intros ??.
        rewrite map_app, in_app_iff. repeat rewrite or_assoc in *; auto.
      + setoid_rewrite or_assoc; eauto.
  Qed.

  Fact mmap2_unnest_prefixed {A1 A2 A3} (unnest : A1 -> FreshAnn (A2 * A3)) (fresh : _ -> list (ident * (type * clock))) : forall xs ys zs st st' P,
      Forall
        (fun x => forall ys zs st st' P,
         Forall (fun id : ident => P id \/ (exists x hint, id = gensym norm1 hint x)) (st_ids st) ->
         unnest x st = (ys, zs, st') ->
         Forall (fun id : ident => P id \/ In id (map fst (fresh x)) \/ (exists x hint, id = gensym norm1 hint x)) (st_ids st')) xs ->
      Forall (fun id => P id \/ exists x hint, id = gensym norm1 hint x) (st_ids st) ->
      mmap2 unnest xs st = (ys, zs, st') ->
      Forall (fun id => P id \/ In id (map fst (flat_map fresh xs)) \/ exists x hint, id = gensym norm1 hint x) (st_ids st').
  Proof.
    induction xs; intros * Hf Hids Hmap; inv Hf; repeat inv_bind.
    - eapply Forall_impl; [|eauto]. intros ? [?|?]; auto.
    - eapply IHxs with (P:=fun id => P id \/ In id (map fst (fresh a))) in H0; eauto.
      + eapply Forall_impl; [|eauto]; intros ??.
        rewrite map_app, in_app_iff. repeat rewrite or_assoc in *; auto.
      + setoid_rewrite or_assoc; eauto.
  Qed.

  Fact unnest_noops_exps_prefixed P : forall cks es es' eqs' st st',
      Forall (fun id => P id \/ exists x hint, id = gensym norm1 hint x) (st_ids st) ->
      unnest_noops_exps cks es st = (es', eqs', st') ->
      Forall (fun id => P id \/ exists x hint, id = gensym norm1 hint x) (st_ids st').
  Proof.
    unfold unnest_noops_exps.
    induction cks; destruct es; intros * Hf Hun; repeat inv_bind; auto.
    eapply IHcks. 2:repeat inv_bind; eauto.
    unfold unnest_noops_exp in H. cases; repeat inv_bind; auto.
    eapply fresh_ident_prefixed; eauto.
  Qed.

  Fact unnest_reset_prefixed unnest P P' : forall e e' eqs' st st',
      (forall es' eqs' st st',
          Forall (fun id => P id \/ exists x hint, id = gensym norm1 hint x) (st_ids st) ->
          unnest e st = (es', eqs', st') ->
          Forall (fun id => P' id \/ exists x hint, id = gensym norm1 hint x) (st_ids st')) ->
      Forall (fun id => P id \/ exists x hint, id = gensym norm1 hint x) (st_ids st) ->
      unnest_reset unnest e st = (e', eqs', st') ->
      Forall (fun id => P' id \/ exists x hint, id = gensym norm1 hint x) (st_ids st').
  Proof.
    intros * He Hf Hun.
    unfold unnest_reset in Hun; repeat inv_bind.
    cases; repeat inv_bind; try eapply fresh_ident_prefixed in H0; eauto.
  Qed.

  Fact unnest_exp_prefixed G : forall e is_control es' eqs' st st' P,
      Forall (fun id => P id \/ exists x hint, id = gensym norm1 hint x) (st_ids st) ->
      unnest_exp G is_control e st = (es', eqs', st') ->
      Forall (fun id => P id \/ In id (map fst (fresh_in e)) \/ exists x hint, id = gensym norm1 hint x) (st_ids st').
  Proof.
    induction e using exp_ind2;
      intros * Hf Hun; repeat inv_bind.
    - (* const *)
      eapply Forall_impl; [|eauto]. intros ? [?|?]; auto.
    - (* enum *)
      eapply Forall_impl; [|eauto]. intros ? [?|?]; auto.
    - (* var *)
      eapply Forall_impl; [|eauto]. intros ? [?|?]; auto.
    - (* unop *)
      eapply IHe in H; eauto.
    - (* binop *)
      eapply IHe1 in H; eauto.
      eapply IHe2 with (P:=fun id => P id \/ In id (map fst (fresh_in e1))) in H0; eauto. 2:now setoid_rewrite or_assoc.
      eapply Forall_impl; [|eauto]. intros ? Hp.
      rewrite map_app, in_app_iff. now repeat rewrite or_assoc in *.
    - (* fby *)
      eapply mmap2_unnest_prefixed in H1; eauto. 2:solve_forall.
      eapply mmap2_unnest_prefixed with (P0:=fun id => P id \/ In id (map fst (flat_map fresh_in e0s))) in H2; eauto. 2:solve_forall.
      2:now setoid_rewrite or_assoc.
      eapply idents_for_anns_prefixed with (P:=fun id => _ \/ _) in H3; eauto. 2:setoid_rewrite or_assoc; eauto.
      solve_forall. rewrite map_app, in_app_iff. repeat rewrite or_assoc in *; auto.
    - (* arrow *)
      eapply mmap2_unnest_prefixed in H1; eauto. 2:solve_forall.
      eapply mmap2_unnest_prefixed with (P0:=fun id => P id \/ In id (map fst (flat_map fresh_in e0s))) in H2; eauto. 2:solve_forall.
      2:now setoid_rewrite or_assoc.
      eapply idents_for_anns_prefixed with (P:=fun id => _ \/ _) in H3; eauto. 2:setoid_rewrite or_assoc; eauto.
      solve_forall. rewrite map_app, in_app_iff. repeat rewrite or_assoc in *; auto.
    - (* when *)
      destruct a. repeat inv_bind.
      eapply mmap2_unnest_prefixed in H0; eauto. solve_forall.
    - (* merge *)
      destruct a; repeat inv_bind.
      eapply mmap2_unnest_prefixed with (fresh:=fun x => flat_map fresh_in (snd x)) in H0; eauto.
      2:{ solve_forall. repeat inv_bind. eapply mmap2_unnest_prefixed in H4; eauto. solve_forall. }
      destruct is_control; repeat inv_bind; auto.
      eapply idents_for_anns_prefixed with (P:=fun id => _ \/ _) in H1; eauto. 2:setoid_rewrite or_assoc; eauto.
      solve_forall. repeat rewrite or_assoc in *; auto.
    - (* case *)
      destruct a; repeat inv_bind.
      eapply IHe in H1; eauto.
      eapply mmap2_unnest_prefixed with (P0:=fun id => _ \/ _) (fresh:=fun x => flat_map fresh_in (snd x)) in H2; eauto. 3:setoid_rewrite or_assoc; eauto.
      2:{ solve_forall. repeat inv_bind. eapply mmap2_unnest_prefixed in H7; eauto. solve_forall. }
      assert (Forall (fun id : ident => (P id \/ In id (map fst (fresh_in e)) \/ In id (map fst (flat_map (fun x => flat_map fresh_in (snd x)) es)))
                                     \/ In id (map fst (or_default_with [] (flat_map fresh_in) d))
                                     \/ (exists (x : ident) (hint : option ident), id = gensym norm1 hint x))
                     (st_ids x7)).
      { destruct d; simpl in *; repeat inv_bind.
        - eapply mmap2_unnest_prefixed with (P0:= fun id => _ \/ _) in H3; eauto. solve_forall.
          eapply Forall_impl; [|eauto]. intros ? [[?|?]|[?|?]]; auto.
        - eapply Forall_impl; [|eauto]. intros ? [[?|?]|[?|?]]; auto.
      }
      destruct is_control; repeat inv_bind; auto. solve_forall; repeat rewrite map_app, in_app_iff; repeat rewrite or_assoc in *; auto.
      eapply idents_for_anns_prefixed with (P:=fun id => _ \/ _) in H4; eauto. 2:setoid_rewrite or_assoc; eauto.
      solve_forall; repeat rewrite map_app, in_app_iff; repeat rewrite or_assoc in *; auto.
    - (* app *)
      eapply mmap2_unnest_prefixed in H1; eauto. 2:solve_forall.
      eapply unnest_noops_exps_prefixed with (P:=fun id => _ \/ _) in H2; eauto. 2:setoid_rewrite or_assoc; eauto.
      eapply mmap2_unnest_prefixed with (P0:=fun id => _ \/ _) in H3; eauto.
      2:{ solve_forall. eapply unnest_reset_prefixed with (P':=fun id => _ \/ _) in H7; eauto.
          2:setoid_rewrite or_assoc; eauto. setoid_rewrite or_assoc in H7; eauto. }
      eapply idents_for_anns'_prefixed with (P:=fun id => _ \/ _) in H4. 2:setoid_rewrite or_assoc; eauto.
      solve_forall.
      repeat rewrite map_app, in_app_iff. repeat rewrite or_assoc in *; auto.
  Qed.

  Corollary unnest_exps_prefixed G P : forall es es' eqs' st st',
      Forall (fun id => P id \/ exists x hint, id = gensym norm1 hint x) (st_ids st) ->
      unnest_exps G es st = (es', eqs', st') ->
      Forall (fun id => P id \/ In id (map fst (flat_map fresh_in es)) \/ exists x hint, id = gensym norm1 hint x) (st_ids st').
  Proof.
    unfold unnest_exps.
    intros * Hf Hun. repeat inv_bind.
    eapply mmap2_unnest_prefixed in H; eauto.
    solve_forall; eauto using unnest_exp_prefixed.
  Qed.

  Fact unnest_rhs_prefixed G : forall e es' eqs' st st' P,
      Forall (fun id => P id \/ exists x hint, id = gensym norm1 hint x) (st_ids st) ->
      unnest_rhs G e st = (es', eqs', st') ->
      Forall (fun id => P id \/ In id (map fst (anon_in e)) \/ exists x hint, id = gensym norm1 hint x) (st_ids st').
  Proof.
    intros * Hf Hun.
    destruct e; try eapply unnest_exp_prefixed in Hun; eauto; repeat inv_bind.
    - (* fby *)
      eapply unnest_exps_prefixed in H; eauto.
      eapply unnest_exps_prefixed with (P:=fun id => _ \/ _) in H0; eauto. 2:setoid_rewrite or_assoc; eauto.
      solve_forall. rewrite map_app, in_app_iff. now repeat rewrite or_assoc in *.
    - (* arrow *)
      eapply unnest_exps_prefixed in H; eauto.
      eapply unnest_exps_prefixed with (P:=fun id => _ \/ _) in H0; eauto. 2:setoid_rewrite or_assoc; eauto.
      solve_forall. rewrite map_app, in_app_iff. now repeat rewrite or_assoc in *.
    - (* app *)
      eapply unnest_exps_prefixed in H; eauto.
      eapply unnest_noops_exps_prefixed with (P:=fun id => _ \/ _) in H0; eauto. 2:setoid_rewrite or_assoc; eauto.
      eapply mmap2_unnest_prefixed with (P0:=fun id => _ \/ _) in H1; eauto.
      2:{ solve_forall. eapply unnest_reset_prefixed with (P':=fun id => _ \/ _) in H4; eauto.
          2:setoid_rewrite or_assoc; eauto. setoid_rewrite or_assoc in H4; eauto.
          intros. eapply unnest_exp_prefixed; eauto. }
      solve_forall. rewrite map_app, in_app_iff. repeat rewrite or_assoc in *; auto.
  Qed.

  Fact unnest_block_prefixed G : forall blk blks' st st' P,
      Forall (fun id => P id \/ exists x hint, id = gensym norm1 hint x) (st_ids st) ->
      unnest_block G blk st = (blks', st') ->
      Forall (fun id => P id \/ In id (map fst (anon_in_block blk)) \/ exists x hint, id = gensym norm1 hint x) (st_ids st').
  Proof.
    induction blk using block_ind2; intros * Hf Hun; repeat inv_bind.
    - (* equation *)
      unfold unnest_equation, unnest_rhss in *.
      destruct eq; repeat inv_bind.
      eapply mmap2_unnest_prefixed in H; eauto.
      solve_forall. eapply unnest_rhs_prefixed; eauto.
    - (* reset *)
      eapply mmap_unnest_prefixed in H0; eauto.
      eapply unnest_reset_prefixed with (P:=fun id => _ \/ _) (P':=fun id => _ \/ _) in H1; eauto. 3:setoid_rewrite or_assoc; eauto.
      2:{ intros. eapply unnest_exp_prefixed with (P:=fun id => _ \/ _) in H3; eauto.
          solve_forall. }
      solve_forall. rewrite map_app, in_app_iff. repeat rewrite or_assoc in *; eauto.
      destruct H2 as [?|[?|[?|[?|?]]]]; auto.
    - (* local *)
      solve_forall. destruct H1; auto.
  Qed.

  Corollary unnest_blocks_prefixed G : forall blks blks' st',
      unnest_blocks G blks init_st = (blks', st') ->
      Forall (fun id => In id (map fst (flat_map anon_in_block blks)) \/ exists x hint, id = gensym norm1 hint x) (st_ids st').
  Proof.
    intros * Hun.
    unfold unnest_blocks in Hun. repeat inv_bind.
    eapply mmap_unnest_prefixed with (P:=fun _ => False) in H.
    - solve_forall. destruct H0; eauto. inv H0.
    - solve_forall. eapply unnest_block_prefixed; eauto.
    - unfold st_ids. rewrite init_st_anns; simpl; auto.
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

  Fact mmap2_unnest_exp_length' : forall G is_control es es' eqs' st st',
      Forall2 (fun e es' => forall eqs' st st',
                   unnest_exp G is_control e st = (es', eqs', st') ->
                   length es' = numstreams e) es es' ->
      mmap2 (unnest_exp G is_control) es st = (es', eqs', st') ->
      length (concat es') = length (annots es).
  Proof.
    intros * Hf Hmap.
    apply mmap2_values in Hmap.
    repeat simpl_list.
    apply concat_length_eq.
    rewrite Forall2_map_2, Forall2_swap_args.
    eapply Forall3_ignore3, Forall2_Forall2 in Hmap; [| eapply Hf]. clear Hf.
    eapply Forall2_impl_In; eauto.
    intros ? ? _ _ [H1 [? [? [? H2]]]]. rewrite length_annot_numstreams; eauto.
  Qed.

  Fact unnest_fby_length : forall e0s es anns,
      length e0s = length anns ->
      length es = length anns ->
      length (unnest_fby e0s es anns) = length anns.
  Proof.
    intros * Hl1 Hl2.
    unfold unnest_fby. solve_length.
  Qed.

  Fact unnest_arrow_length : forall e0s es anns,
      length e0s = length anns ->
      length es = length anns ->
      length (unnest_arrow e0s es anns) = length anns.
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

  Fact unnest_merge_length : forall ckid es tys nck,
      length (unnest_merge ckid es tys nck) = length tys.
  Proof.
    intros *. revert es.
    induction tys; simpl; auto.
  Qed.

  Fact unnest_case_length : forall e es d tys nck,
      length (unnest_case e es d tys nck) = length tys.
  Proof.
    intros *. revert es d.
    induction tys; simpl; auto.
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
      apply idents_for_anns_length in H3...
    - (* arrow *)
      simpl in *. rewrite map_length.
      apply idents_for_anns_length in H3...
    - (* when *)
      unfold unnest_when. rewrite map_length.
      eapply mmap2_unnest_exp_length' in H0.
      + solve_length.
      + eapply mmap2_values in H0.
        repeat rewrite_Forall_forall...
    - (* merge *)
      destruct is_control; repeat inv_bind.
      + apply unnest_merge_length.
      + apply idents_for_anns_length in H1. solve_length.
    - (* case *)
      destruct is_control; repeat inv_bind; unfold unnest_case.
      + apply unnest_case_length.
      + apply idents_for_anns_length in H4. solve_length.
    - (* app (reset) *)
      apply idents_for_anns'_length in H4.
      solve_length.
  Qed.
  Hint Resolve unnest_exp_length.

  Corollary mmap2_unnest_exp_length : forall G is_control es es' eqs' st st',
      Forall (wl_exp G) es ->
      mmap2 (unnest_exp G is_control) es st = (es', eqs', st') ->
      length (concat es') = length (annots es).
  Proof.
    intros * Hf Hmap.
    eapply mmap2_unnest_exp_length'; eauto.
    eapply mmap2_values in Hmap.
    repeat rewrite_Forall_forall.
    eapply unnest_exp_length; eauto.
  Qed.
  Hint Resolve mmap2_unnest_exp_length.

  Corollary mmap2_mmap2_unnest_exp_length {A} : forall G is_control (es : list (A * list exp)) es' eqs' st st',
    Forall (fun es => Forall (wl_exp G) (snd es)) es ->
    mmap2 (fun '(i, es0) => do (es', eqs') <- mmap2 (unnest_exp G is_control) es0;
                         ret (i, concat es', concat eqs')) es st = (es', eqs', st') ->
    Forall2 (fun es es' => length (snd es') = length (annots (snd es))) es es'.
  Proof.
    intros * Hwl Hmap.
    eapply mmap2_values in Hmap. eapply Forall3_ignore3 in Hmap.
    eapply Forall2_impl_In; [|eauto]; intros (?&?) (?&?) Hin _ (?&?&?&?); repeat inv_bind.
    eapply Forall_forall in Hwl; eauto; simpl in *; eauto.
  Qed.

  (* Corollary mmap2_mmap2_unnest_exp_length' : forall G is_control es es' eqs' st st', *)
  (*   Forall (LiftO True (Forall (wl_exp G))) es -> *)
  (*   mmap2 *)
  (*       (or_default_with *)
  (*          (ret (None, [])) *)
  (*          (fun es => bind2 *)
  (*                    (bind2 (mmap2 (unnest_exp G is_control) es) (fun es0 eqs => ret (concat es0, concat eqs))) *)
  (*                    (fun es' eqs'  => ret (Some es', eqs')))) es st = (es', eqs', st') -> *)
  (*   Forall2 (fun oes oes' => forall es', oes' = Some es' -> exists es, oes = Some es /\ length es' = length (annots es)) es es'. *)
  (* Proof. *)
  (*   intros * Hwl Hmap. *)
  (*   eapply mmap2_values in Hmap. eapply Forall3_ignore3 in Hmap. *)
  (*   eapply Forall2_impl_In; [|eauto]; intros ?? Hin _ (?&?&?&?) ??; subst; repeat inv_bind. *)
  (*   destruct a; repeat inv_bind. *)
  (*   repeat esplit. *)
  (*   eapply Forall_forall in Hwl; eauto. *)
  (*   simpl in *; eauto. *)
  (* Qed. *)

  Corollary unnest_exps_length : forall G es es' eqs' st st',
      Forall (wl_exp G) es ->
      unnest_exps G es st = (es', eqs', st') ->
      length es' = length (annots es).
  Proof.
    intros * Hwt Hnorm.
    unfold unnest_exps in Hnorm.
    repeat inv_bind.
    eapply mmap2_unnest_exp_length; eauto.
  Qed.
  Hint Resolve unnest_exps_length.

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
    4,5:destruct l0, is_control; repeat inv_bind.
    1,2,5,7,8:rewrite Forall_map; eapply Forall_forall; intros [? ?] ?; auto.
    1,2,3:(unfold unnest_when, unnest_merge, unnest_case;
           rewrite Forall_forall; intros ? Hin).
    - repeat simpl_In. reflexivity.
    - clear - Hin. revert x Hin.
      induction l0; intros; simpl; inv Hin; eauto.
    - clear - Hin. revert Hin. revert x2 x5.
      induction l0; intros; simpl; inv Hin; eauto.
  Qed.

  Corollary mmap2_unnest_exp_numstreams : forall G es is_control es' eqs' st st',
      mmap2 (unnest_exp G is_control) es st = (es', eqs', st') ->
      Forall (fun e => numstreams e = 1) (concat es').
  Proof.
    intros * Hmap.
    apply mmap2_values in Hmap.
    induction Hmap; simpl.
    - constructor.
    - apply Forall_app; split; auto.
      destruct H as [? [? H]].
      eapply unnest_exp_numstreams; eauto.
  Qed.

  Corollary mmap2_mmap2_unnest_exp_numstreams {A} G : forall (es : list (A * _)) is_control es' eqs' st st',
      mmap2 (fun '(i, es) => bind2 (mmap2 (unnest_exp G is_control) es) (fun es' eqs' => ret (i, concat es', concat eqs'))) es st = (es', eqs', st') ->
      Forall (fun es => Forall (fun e => numstreams e = 1) (snd es)) es'.
  Proof.
    intros * Hmmap.
    eapply mmap2_values, Forall3_ignore13 in Hmmap.
    eapply Forall_impl; [|eauto]. intros (?&?) ((?&?)&?&_&_&?&?&?). repeat inv_bind.
    eapply mmap2_unnest_exp_numstreams; eauto.
  Qed.

  Corollary unnest_exps_numstreams : forall G es es' eqs' st st',
      unnest_exps G es st = (es', eqs', st') ->
      Forall (fun e => numstreams e = 1) es'.
  Proof.
    intros * Hnorm.
    unfold unnest_exps in Hnorm. repeat inv_bind.
    eapply mmap2_unnest_exp_numstreams. eauto.
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

  Fact unnest_fby_annot : forall anns e0s es,
      length e0s = length anns ->
      length es = length anns ->
      annots (unnest_fby e0s es anns) = anns.
  Proof.
    induction anns; intros * Hl1 Hl2;
      destruct e0s; destruct es; simpl in *; try congruence; auto.
    f_equal. eauto.
  Qed.

  Fact unnest_arrow_annot : forall anns e0s es,
      length e0s = length anns ->
      length es = length anns ->
      annots (unnest_arrow e0s es anns) = anns.
  Proof.
    induction anns; intros * Hl1 Hl2;
      destruct e0s; destruct es; simpl in *; try congruence; auto.
    f_equal. eauto.
  Qed.

  Fact unnest_fby_annot' : forall anns e0s es,
      length e0s = length anns ->
      length es = length anns ->
      Forall2 (fun e a => annot e = [a]) (unnest_fby e0s es anns) anns.
  Proof.
    induction anns; intros * Hl1 Hl2;
      destruct e0s; destruct es; simpl in *; try congruence; auto.
    - constructor.
    - simpl. constructor; eauto.
  Qed.

  Fact unnest_arrow_annot' : forall anns e0s es,
      length e0s = length anns ->
      length es = length anns ->
      Forall2 (fun e a => annot e = [a]) (unnest_arrow e0s es anns) anns.
  Proof.
    induction anns; intros * Hl1 Hl2;
      destruct e0s; destruct es; simpl in *; try congruence; auto.
    - constructor.
    - simpl. constructor; eauto.
  Qed.

  Fact unnest_merge_annot : forall ckid es tys ck,
      Forall2 (fun ty e => annot e = [(ty, ck)]) tys (unnest_merge ckid es tys ck).
  Proof.
    intros *. unfold unnest_merge.
    revert es. induction tys; intros; auto.
  Qed.

  Fact unnest_case_annot : forall e es tys d ck,
      Forall2 (fun ty e => annot e = [(ty, ck)]) tys (unnest_case e es d tys ck).
  Proof.
    intros *. unfold unnest_case.
    revert es d. induction tys; intros; auto.
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
    - (* fby *) apply idents_for_anns_annots in H1...
    - (* arrow *) apply idents_for_anns_annots in H1...
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
      + specialize (unnest_merge_annot p x tys nck) as Hf.
        clear - Hf. induction Hf; simpl; auto.
        rewrite H, IHHf; auto.
      + apply idents_for_anns_annots in H0...
    - (* case *)
      destruct is_control; repeat inv_bind.
      + specialize (unnest_case_annot (hd_default x) x2 tys x5 nck) as Hf.
        clear - Hf. induction Hf; simpl; auto.
        rewrite H, IHHf; auto.
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

  Fact mmap2_unnest_exp_annots': forall G is_control es es' eqs' st st',
      Forall (wl_exp G) es ->
      mmap2 (unnest_exp G is_control) es st = (es', eqs', st') ->
      Forall2 (fun es' e => annots es' = annot e) es' es.
  Proof.
    intros * Hf Hmap.
    apply mmap2_values in Hmap.
    induction Hmap.
    - constructor.
    - destruct H as [? [? Hnorm]]. inv Hf.
      constructor; eauto.
      eapply unnest_exp_annot; eauto.
  Qed.

  Corollary mmap2_unnest_exp_annots'' : forall G is_control es es' eqs' st st',
      Forall (wl_exp G) es ->
      mmap2 (unnest_exp G is_control) es st = (es', eqs', st') ->
      Forall2 (fun e ann => annot e = [ann]) (concat es') (annots es).
  Proof.
    intros * Hwl Hmap.
    assert (Forall (fun e => numstreams e = 1) (concat es')) as Hnumstreams.
    { eapply mmap2_unnest_exp_numstreams in Hmap; eauto. }
    eapply mmap2_unnest_exp_annots' in Hmap; eauto.
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

  Corollary mmap2_unnest_exp_annots_length' :
    forall G is_control es es' eqs' st st',
      Forall (wl_exp G) es ->
      mmap2 (unnest_exp G is_control) es st = (es', eqs', st') ->
      Forall2 (fun es' e => length (annots es') = length (annot e)) es' es.
  Proof.
    intros * Hf Hmap.
    eapply mmap2_unnest_exp_annots' in Hmap; eauto.
    induction Hmap; inv Hf; constructor; eauto.
    congruence.
  Qed.

  Fact mmap2_unnest_exp_annots :
    forall G is_control es es' eqs' st st',
      Forall (wl_exp G) es ->
      mmap2 (unnest_exp G is_control) es st = (es', eqs', st') ->
      annots (concat es') = annots es.
  Proof.
    intros * Hwl Hmap.
    eapply mmap2_unnest_exp_annots' in Hmap; eauto.
    induction Hmap; simpl; auto.
    inv Hwl.
    repeat simpl_list.
    f_equal; auto.
  Qed.

  Corollary mmap2_mmap2_unnest_exp_annots {A} : forall G is_control (es : list (A * _)) es' eqs' st st',
      Forall (fun es => Forall (wl_exp G) (snd es)) es ->
      mmap2 (fun '(i, es) => bind2 (mmap2 (unnest_exp G is_control) es) (fun es' eqs' => ret (i, concat es', concat eqs'))) es st = (es', eqs', st') ->
      Forall2 (fun es es' => annots (snd es') = annots (snd es)) es es'.
  Proof.
    intros * Hf Hmap.
    eapply mmap2_values, Forall3_ignore3 in Hmap.
    eapply Forall2_impl_In; [|eauto]; intros (?&?) (?&?) Hin _ (?&?&?&?). repeat inv_bind.
    eapply Forall_forall in Hf; eauto.
    eapply mmap2_unnest_exp_annots; eauto.
  Qed.

  Fact mmap2_unnest_exp_annots_length :
    forall G is_control es es' eqs' st st',
      Forall (wl_exp G) es ->
      mmap2 (unnest_exp G is_control) es st = (es', eqs', st') ->
      length (annots (concat es')) = length (annots es).
  Proof.
    intros * Hwl Hmap.
    eapply mmap2_unnest_exp_annots in Hmap; eauto.
    congruence.
  Qed.

  Fact unnest_exps_annots : forall G es es' eqs' st st',
      Forall (wl_exp G) es ->
      unnest_exps G es st = (es', eqs', st') ->
      annots es' = annots es.
  Proof.
    intros * Hwt Hnorm.
    unfold unnest_exps in Hnorm; repeat inv_bind.
    eapply mmap2_unnest_exp_annots in H; eauto.
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
    apply mmap2_values in H.
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

  Fact mmap2_vars_perm {A B} : forall (k : A -> FreshAnn (B * list equation)) es es' eqs' st st',
      mmap2 k es st = (es', eqs', st') ->
      Forall (fun e => forall es' eqs' st st',
                  k e st = (es', eqs', st') ->
                  Permutation ((flat_map fst eqs')++(st_ids st)) (st_ids st')) es ->
      Permutation ((flat_map fst (concat eqs'))++(st_ids st)) (st_ids st').
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
      Permutation (flat_map fst eqs'++st_ids st) (st_ids st').
  Proof.
    intros * Hun.
    unfold unnest_noops_exps in Hun. repeat inv_bind.
    eapply mmap2_vars_perm; eauto.
    eapply Forall_forall. intros (?&?) _ * Hun.
    unfold unnest_noops_exp in Hun.
    destruct (hd _ _) as (?&?&?). destruct is_noops_exp; repeat inv_bind; eauto.
    simpl. eapply fresh_ident_vars_perm; eauto.
  Qed.

  Fact unnest_reset_vars_perm : forall k e es' eqs' st st',
      (forall es' eqs' st st',
          k e st = ((es', eqs'), st') ->
          Permutation ((flat_map fst eqs')++(st_ids st)) (st_ids st')) ->
      unnest_reset k e st = ((es', eqs'), st') ->
      Permutation ((flat_map fst eqs')++(st_ids st)) (st_ids st').
  Proof.
    intros * Hkperm Hnorm.
    unnest_reset_spec; simpl; eauto.
    destruct (hd _ _) as [ty [ck o]]; repeat inv_bind.
    eapply Hkperm in Hk0.
    eapply fresh_ident_vars_perm in Hfresh; eauto.
    rewrite <- Hfresh, <- Hk0; auto.
  Qed.

  Fact unnest_exp_vars_perm : forall G e is_control es' eqs' st st',
      unnest_exp G is_control e st = ((es', eqs'), st') ->
      Permutation ((flat_map fst eqs')++(st_ids st)) (st_ids st')(* ++(fresh_in e) *).
  Proof with eauto.
    induction e using exp_ind2; intros is_control e' eqs' st st' Hnorm;
      simpl in Hnorm; repeat inv_bind...
    - (* binop *)
      repeat simpl_list.
      apply IHe1 in H...
      apply IHe2 in H0...
      etransitivity. 2: eauto. repeat simpl_list.
      rewrite Permutation_swap.
      apply Permutation_app_head...
    - (* fby *)
      remember (unnest_fby _ _ _) as fby.
      apply mmap2_vars_perm in H1. 2:solve_forall.
      apply mmap2_vars_perm in H2. 2:solve_forall.
      apply idents_for_anns_vars_perm in H3.
      rewrite <- H3, <- H2, <- H1.
      repeat simpl_list.
      rewrite mk_equations_map_fst.
      eapply Permutation_app_head.
      rewrite Permutation_swap; auto.
    - (* arrow *)
      repeat inv_bind.
      remember (unnest_arrow _ _ _) as fby.
      apply mmap2_vars_perm in H1. 2:solve_forall.
      apply mmap2_vars_perm in H2. 2:solve_forall.
      apply idents_for_anns_vars_perm in H3.
      rewrite <- H3, <- H2, <- H1.
      repeat simpl_list.
      rewrite mk_equations_map_fst.
      eapply Permutation_app_head.
      rewrite Permutation_swap; auto.
    - (* when *)
      destruct a; repeat inv_bind.
      eapply mmap2_vars_perm...
      rewrite Forall_forall in *. intros...
    - (* merge *)
      destruct a; repeat inv_bind.
      apply mmap2_vars_perm in H0.
      2:{ solve_forall; repeat inv_bind.
          eapply mmap2_vars_perm in H3; eauto. solve_forall. }
      destruct is_control; repeat inv_bind; auto.
      repeat simpl_list.
      apply idents_for_anns_vars_perm in H1.
      etransitivity. 2: eauto.
      rewrite mk_equations_map_fst.
      repeat rewrite <- app_assoc. apply Permutation_app_head.
      etransitivity; eauto.
    - (* case *)
      destruct a; repeat inv_bind.
      apply IHe in H1; eauto.
      apply mmap2_vars_perm in H2.
      2:{ solve_forall; repeat inv_bind; simpl; auto.
          eapply mmap2_vars_perm in H6... solve_forall. }
      assert (Permutation (flat_map fst x6 ++ st_ids x4) (st_ids x7)) as Hperm3.
      { destruct d; repeat inv_bind; simpl in *; auto.
        eapply mmap2_vars_perm in H3... solve_forall. }
      destruct is_control; repeat inv_bind.
      + etransitivity...
        now rewrite <-2 flat_map_app, <-app_assoc, Permutation_swap, H1,
        <-app_assoc, Permutation_swap, H2.
      + repeat simpl_list.
        rewrite mk_equations_map_fst.
        eapply idents_for_anns_vars_perm in H4.
        etransitivity. 2:eauto.
        replace (concat (map (fun '(id, _) => [id]) x8)) with (map fst x8).
        2: { clear - x8. induction x8; try destruct a; simpl; f_equal; auto. }
        repeat rewrite <- app_assoc. apply Permutation_app_head.
        etransitivity. 2:eauto.
        rewrite app_assoc, Permutation_swap. apply Permutation_app_head; auto.
        now rewrite <-app_assoc, Permutation_swap, H1.
    - (* app (reset) *)
      repeat inv_bind.
      apply mmap2_vars_perm in H3.
      2:{ eapply Forall_impl_In; [|eapply H0]. intros; simpl in *.
          eapply unnest_reset_vars_perm in H7; intros; eauto. }
      repeat rewrite <- flat_map_app; simpl.
      eapply idents_for_anns'_vars_perm in H4.
      simpl; repeat inv_bind.
      apply mmap2_vars_perm in H1. 2: (repeat rewrite_Forall_forall; eauto).
      apply unnest_noops_exps_vars_perm in H2.
      rewrite <- H4, <- H3, <- H2, <- H1; simpl.
      repeat simpl_list.
      apply Permutation_app_head. rewrite Permutation_app_comm, Permutation_swap, <- app_assoc, <- app_assoc.
      apply Permutation_app_head, Permutation_app_head. apply Permutation_app_comm.
  Qed.

  Corollary unnest_exps_vars_perm : forall G es es' eqs' st st',
      unnest_exps G es st = ((es', eqs'), st') ->
      Permutation ((flat_map fst eqs')++(st_ids st)) (st_ids st').
  Proof with eauto.
    intros * Hnorm.
    unfold unnest_exps in Hnorm.
    repeat inv_bind.
    eapply mmap2_vars_perm...
    repeat rewrite_Forall_forall.
    eapply unnest_exp_vars_perm...
  Qed.

  Fact unnest_rhs_vars_perm : forall G e es' eqs' st st',
      unnest_rhs G e st = ((es', eqs'), st') ->
      Permutation ((flat_map fst eqs')++(st_ids st)) (st_ids st').
  Proof with eauto.
    intros * Hnorm.
    destruct e; unfold unnest_rhs in Hnorm;
      try (solve [eapply unnest_exp_vars_perm; eauto]).
    - (* fby *)
      repeat inv_bind.
      eapply unnest_exps_vars_perm in H...
      eapply unnest_exps_vars_perm in H0...
      rewrite <- H0, <- H.
      repeat simpl_list.
      rewrite Permutation_swap...
    - (* arrow *)
      repeat inv_bind.
      eapply unnest_exps_vars_perm in H...
      eapply unnest_exps_vars_perm in H0...
      rewrite <- H0, <- H.
      repeat simpl_list.
      rewrite Permutation_swap...
    - (* app *)
      repeat inv_bind.
      apply mmap2_vars_perm in H1.
      2:{ eapply Forall_forall. intros * ? * Res.
          eapply unnest_reset_vars_perm in Res; intros; eauto.
          eapply unnest_exp_vars_perm; eauto. }
      repeat rewrite <- flat_map_app; repeat rewrite <- app_assoc; simpl.
      eapply unnest_exps_vars_perm in H; eauto.
      eapply unnest_noops_exps_vars_perm in H0.
      rewrite <- H1, <- H0, <- H.
      rewrite Permutation_swap, <- (Permutation_swap (flat_map fst x3)).
      apply Permutation_app_head.
      rewrite Permutation_swap. reflexivity.
  Qed.

  Corollary unnest_rhss_vars_perm : forall G es es' eqs' st st',
      unnest_rhss G es st = ((es', eqs'), st') ->
      Permutation ((flat_map fst eqs')++(st_ids st)) (st_ids st').
  Proof.
    intros * Hnorm.
    unfold unnest_rhss in Hnorm.
    repeat inv_bind.
    eapply mmap2_vars_perm in H; eauto.
    repeat rewrite_Forall_forall.
    eapply unnest_rhs_vars_perm; eauto.
  Qed.

  Fact split_equation_fst : forall xs es,
      flat_map fst (split_equation (xs, es)) = xs.
  Proof.
    intros xs es; revert xs.
    induction es; intros xs; simpl in *.
    - induction xs; simpl; f_equal; auto.
    - specialize (IHes (skipn (numstreams a) xs)).
      rewrite IHes.
      repeat rewrite app_nil_r. apply firstn_skipn.
  Qed.

  Corollary split_equations_fst : forall eqs,
      flat_map fst (flat_map split_equation eqs) = flat_map fst eqs.
  Proof.
    induction eqs; simpl in *.
    - reflexivity.
    - destruct a as [xs es].
      specialize (split_equation_fst xs es) as Heq.
      repeat simpl_list.
      f_equal; auto.
  Qed.

  Fact unnest_equation_vars_perm : forall G eq eqs' st st',
      unnest_equation G eq st = (eqs', st') ->
      Permutation (flat_map fst eqs'++st_ids st) (fst eq++st_ids st').
  Proof.
    intros * Hnorm.
    destruct eq; simpl in *.
    repeat inv_bind.
    specialize (unnest_rhss_vars_perm _ _ _ _ _ _ H) as Hperm1.
    assert (flat_map fst (flat_map split_equation [(l, x)]) = flat_map fst [(l, x)]) as Hxl.
    { apply split_equations_fst. }
    repeat simpl_list.
    apply Permutation_app; auto.
    rewrite <- Hxl at 2. reflexivity.
  Qed.

  Fact mmap_vars_perm : forall (f : block -> FreshAnn (list block)) blks blks' xs st st',
      Forall
        (fun blk => forall blks' xs st st',
             VarsDefined blk xs -> f blk st = (blks', st') ->
             exists ys, Forall2 VarsDefined blks' ys /\ Permutation (concat ys ++ st_ids st) (xs ++ st_ids st')) blks ->
      Forall2 VarsDefined blks xs ->
      mmap f blks st = (blks', st') ->
      exists ys, Forall2 VarsDefined (concat blks') ys /\ Permutation (concat ys ++ st_ids st) (concat xs ++ st_ids st').
  Proof.
    induction blks; intros * Hf Hvars Hnorm; inv Hf; inv Hvars; unfold unnest_blocks in Hnorm; repeat inv_bind; simpl.
    - exists []. split; auto.
    - eapply H1 in H as (ys1&Hvars1&Hperm1); eauto.
      eapply IHblks in H2 as (ys2&Hvars2&Hperm2); eauto. clear IHblks.
      exists (ys1 ++ ys2). split.
      + apply Forall2_app; auto.
      + rewrite <-app_assoc, <-Hperm2, Permutation_swap, <-Hperm1, Permutation_swap.
        now rewrite concat_app, <-app_assoc.
  Qed.

  Lemma unnest_block_vars_perm : forall G blk blks' xs st st',
      VarsDefined blk xs ->
      unnest_block G blk st = (blks', st') ->
      exists ys, Forall2 VarsDefined blks' ys /\ Permutation (concat ys ++ st_ids st) (xs ++ st_ids st').
  Proof.
    induction blk using block_ind2; intros * Hvars Hun; inv Hvars; repeat inv_bind.
    - exists (map fst x). split.
      + rewrite Forall2_map_1, Forall2_map_2. apply Forall2_same.
        eapply Forall_forall; intros. constructor.
      + eapply unnest_equation_vars_perm in H. now rewrite flat_map_concat_map in H.
    - eapply unnest_reset_vars_perm in H1; eauto using unnest_exp_vars_perm.
      eapply mmap_vars_perm in H0 as (ys1&Hvars1&Hperm1); eauto.
      exists (ys1++map fst x2). split.
      + apply Forall2_app; rewrite Forall2_map_1; try (rewrite Forall2_map_2; eapply Forall2_same).
        * eapply Forall2_impl_In; [|eauto]; intros.
          replace b with (concat [b]) by (simpl; now rewrite app_nil_r).
          repeat constructor; auto.
        * eapply Forall_forall; intros. constructor.
      + rewrite <-H1, Permutation_swap, <-Hperm1, Permutation_swap.
        now rewrite concat_app, <-app_assoc, flat_map_concat_map.
    - exists [xs]. split; try constructor; auto.
      + econstructor; eauto.
      + simpl; rewrite app_nil_r; auto.
  Qed.

  Corollary unnest_blocks_vars_perm : forall G blks blks' xs st st',
      Forall2 VarsDefined blks xs ->
      unnest_blocks G blks st = (blks', st') ->
      exists ys, Forall2 VarsDefined blks' ys /\ Permutation (concat ys ++ st_ids st) (concat xs ++ st_ids st').
  Proof.
    intros * Hvars Hun. unfold unnest_blocks in Hun. repeat inv_bind.
    eapply mmap_vars_perm; [|eauto|eauto].
    solve_forall. eapply unnest_block_vars_perm; eauto.
  Qed.

  (** ** Specification of an (almost) normalized node *)

  Inductive normalized_lexp : exp -> Prop :=
  | normalized_Econst : forall c, normalized_lexp (Econst c)
  | normalized_Eenum : forall k ty, normalized_lexp (Eenum k ty)
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

  Fixpoint noops_exp (ck: clock) (e : exp) : Prop :=
    match ck with
    | Cbase => True
    | Con ck' _ _ =>
      match e with
      | Econst _ | Eenum _ _ | Evar _ _ => True
      | Ewhen [e'] _ _ _ => noops_exp ck' e'
      | _ => False
      end
    end.

  Inductive normalized_cexp : exp -> Prop :=
  | normalized_Emerge : forall x es ty cl,
      Forall (fun es => exists e, (snd es) = [e] /\ normalized_cexp e) es ->
      normalized_cexp (Emerge x es ([ty], cl))
  | normalized_Ecase : forall e es d ty cl,
      normalized_lexp e ->
      Forall (fun es => exists e, (snd es) = [e] /\ normalized_cexp e) es ->
      (forall ds, d = Some ds -> exists d, ds = [d] /\ normalized_cexp d) ->
      normalized_cexp (Ecase e es d ([ty], cl))
  | normalized_lexp_cexp : forall e,
      normalized_lexp e ->
      normalized_cexp e.

  Inductive unnested_equation {PSyn prefs} (G: @global PSyn prefs) : equation -> Prop :=
  | unnested_eq_Eapp : forall xs f n es er lann,
      Forall normalized_lexp es ->
      find_node f G = Some n ->
      Forall2 noops_exp (map (fun '(_, (_, ck, _)) => ck) n.(n_in)) es ->
      Forall (fun e => exists x ann, e = Evar x ann) er ->
      unnested_equation G (xs, [Eapp f es er lann])
  | unnested_eq_Efby : forall x e0 e ann,
      normalized_lexp e0 ->
      normalized_lexp e ->
      unnested_equation G ([x], [Efby [e0] [e] [ann]])
  | unnested_eq_Earrow : forall x e0 e ann,
      normalized_lexp e0 ->
      normalized_lexp e ->
      unnested_equation G ([x], [Earrow [e0] [e] [ann]])
  | unnested_eq_cexp : forall x e,
      normalized_cexp e ->
      unnested_equation G ([x], [e]).

  Inductive unnested_block {PSyn prefs} (G: @global PSyn prefs) : block -> Prop :=
  | unnested_Beq : forall eq,
      unnested_equation G eq ->
      unnested_block G (Beq eq)
  | unnested_Breset : forall block x ann,
      unnested_block G block ->
      unnested_block G (Breset [block] (Evar x ann)).

  Inductive unnested_node {PSyn1 PSyn2 prefs1 prefs2} (G: @global PSyn1 prefs1) : @node PSyn2 prefs2 -> Prop :=
  | unnested_Node : forall n locs blks,
      n_block n = Blocal locs blks ->
      Forall (unnested_block G) blks ->
      unnested_node G n.

  Definition unnested_global {PSyn prefs} (G: @global PSyn prefs) :=
    wt_program unnested_node G.

  Hint Constructors normalized_lexp normalized_cexp unnested_equation unnested_block.

  (* Intermediary predicate for unnested rhs *)
  Inductive unnested_rhs {PSyn prefs} (G: @global PSyn prefs) : exp -> Prop :=
  | unnested_rhs_Eapp : forall f n es er lann,
      Forall normalized_lexp es ->
      find_node f G = Some n ->
      Forall2 noops_exp (map (fun '(_, (_, ck, _)) => ck) (n_in n)) es ->
      Forall (fun e => exists x ann, e = Evar x ann) er ->
      unnested_rhs G (Eapp f es er lann)
  | unnested_rhs_Efby : forall e0 e ann,
      normalized_lexp e0 ->
      normalized_lexp e ->
      unnested_rhs G (Efby [e0] [e] [ann])
  | unnested_rhs_Earrow : forall e0 e ann,
      normalized_lexp e0 ->
      normalized_lexp e ->
      unnested_rhs G (Earrow [e0] [e] [ann])
  | unnested_rhs_cexp : forall e,
      normalized_cexp e ->
      unnested_rhs G e.
  Hint Constructors unnested_rhs.

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

  Fact mmap2_normalized_lexp' {A A2} :
    forall (k : A -> FreshAnn ((list exp) * A2)) a es' a2s st st',
      mmap2 k a st = (es', a2s, st') ->
      Forall (fun a => forall es' a2s st st',
                  k a st = (es', a2s, st') ->
                  Forall normalized_lexp es') a ->
      Forall normalized_lexp (concat es').
  Proof.
    intros k a eqs' a2s st st' Hmap Hf.
    apply mmap2_values in Hmap.
    induction Hmap; simpl in *.
    - constructor.
    - destruct H as [? [? H]]. inv Hf.
      rewrite Forall_app.
      split; eauto.
  Qed.

  Fact mmap2_normalized_cexp' {A A2} :
    forall (k : A -> FreshAnn (list exp * A2)) a es' a2s st st',
      mmap2 k a st = (es', a2s, st') ->
      Forall (fun a => forall es' a2s st st',
                  k a st = (es', a2s, st') ->
                  Forall normalized_cexp es') a ->
      Forall normalized_cexp (concat es').
  Proof.
    intros k a eqs' a2s st st' Hmap Hf.
    apply mmap2_values in Hmap.
    induction Hmap; simpl in *.
    - constructor.
    - destruct H as [? [? H]]. inv Hf.
      rewrite Forall_app.
      split; eauto.
  Qed.

  Fact mmap2_normalized_cexp'' {A A2} :
    forall (k : A -> FreshAnn (enumtag * list exp * A2)) a es' a2s st st',
      mmap2 k a st = (es', a2s, st') ->
      Forall (fun a => forall es' a2s st st',
                  k a st = (es', a2s, st') ->
                  Forall normalized_cexp (snd es')) a ->
      Forall normalized_cexp (concat (map snd es')).
  Proof.
    intros k a eqs' a2s st st' Hmap Hf.
    apply mmap2_values in Hmap.
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
      apply mmap2_normalized_lexp' in H0...
      repeat rewrite_Forall_forall.
      repeat simpl_In...
    - (* merge *)
      destruct a. repeat inv_bind. unfold unnest_merge.
      repeat rewrite_Forall_forall.
      repeat simpl_In. destruct a...
    - (* case *)
      destruct a. repeat inv_bind. unfold unnest_case.
      repeat rewrite_Forall_forall.
      repeat simpl_In. destruct a...
    - (* app *)
      repeat rewrite_Forall_forall.
      repeat simpl_In. destruct a0...
  Qed.
  Hint Resolve unnest_exp_normalized_lexp.

  Corollary mmap2_normalized_lexp : forall G es es' eqs' st st',
      mmap2 (unnest_exp G false) es st = (es', eqs', st') ->
      Forall normalized_lexp (concat es').
  Proof.
    intros * Hnorm.
    eapply mmap2_normalized_lexp' in Hnorm; auto.
    solve_forall.
  Qed.
  Hint Resolve mmap2_normalized_lexp.

  Corollary unnest_exps_normalized_lexp: forall G es es' eqs' st st',
      unnest_exps G es st = (es', eqs', st') ->
      Forall normalized_lexp es'.
  Proof.
    intros * Hnorm.
    unfold unnest_exps in Hnorm. repeat inv_bind.
    apply mmap2_normalized_lexp in H; auto.
  Qed.
  Hint Resolve unnest_exps_normalized_lexp.

  Fact unnest_reset_is_var : forall k e e' eqs' st st',
      unnest_reset k e st = (e', eqs', st') ->
      exists x ann, e' = Evar x ann.
  Proof.
    intros * Hnorm.
    unnest_reset_spec; simpl; eauto.
  Qed.

  Corollary unnest_resets_is_var : forall k es es' eqs' st st',
      mmap2 (unnest_reset k) es st = (es', eqs', st') ->
      Forall (fun e => exists x ann, e = Evar x ann) es'.
  Proof.
    intros * Hnorm.
    eapply mmap2_values, Forall3_ignore3, Forall2_ignore1 in Hnorm.
    eapply Forall_impl; [|eauto]. intros * (?&?&?&?&?&Res).
    eapply unnest_reset_is_var; eauto.
  Qed.

  Corollary unnest_resets_no_fresh : forall k es es' eqs' st st' ,
      mmap2 (unnest_reset k) es st = (es', eqs', st') ->
      flat_map fresh_in es' = [].
  Proof.
    intros * Hmap.
    eapply unnest_resets_is_var in Hmap.
    clear - Hmap.
    induction es'; inversion_clear Hmap as [|?? (?&?&?) ?]; subst; simpl; auto.
  Qed.

  Lemma unnest_reset_unnested_eq {PSyn} : forall (G: @global PSyn local_prefs) k e es' eqs' st st',
      (forall es' eqs' st st',
          k e st = (es', eqs', st') ->
          Forall (unnested_rhs G) es' /\ Forall (unnested_equation G) eqs') ->
      unnest_reset k e st = (es', eqs', st') ->
      Forall (unnested_equation G) eqs'.
  Proof.
    intros * Hkunn Hnorm.
    unnest_reset_spec; auto.
    1,2:eapply Hkunn in Hk0 as (?&?); auto.
    constructor; auto.
    inv H; simpl; auto.
    inv H1; eauto.
  Qed.

  Corollary unnest_resets_unnested_eq {PSyn} : forall (G: @global PSyn local_prefs) k es es' eqs' st st',
      Forall (fun e => forall es' eqs' st st',
                  k e st = (es', eqs', st') ->
                  Forall (unnested_rhs G) es' /\ Forall (unnested_equation G) eqs') es ->
      mmap2 (unnest_reset k) es st = (es', eqs', st') ->
      Forall (unnested_equation G) (concat eqs').
  Proof.
    intros * Hkunn Hnorm.
    eapply mmap2_values, Forall3_ignore2, Forall2_ignore1 in Hnorm.
    eapply Forall_concat.
    eapply Forall_impl_In; [|eauto]. intros * ? (?&?&?&?&?&?).
    eapply Forall_forall in Hkunn; eauto.
    eapply unnest_reset_unnested_eq; eauto.
  Qed.

  Fact unnest_merge_normalized_cexp : forall x es tys ck,
      Forall (fun es => Forall normalized_cexp (snd es)) es ->
      Forall normalized_cexp (unnest_merge x es tys ck).
  Proof.
    intros. unfold unnest_merge. revert es H.
    induction tys; intros * Hnormed; constructor; eauto.
    - econstructor; eauto. rewrite Forall_map.
      eapply Forall_impl; [|eauto]; intros * Hn.
      destruct a0; simpl in *; inv Hn; eauto.
    - eapply IHtys. rewrite Forall_map.
      eapply Forall_impl; [|eauto]; intros * Hn.
      destruct a0; simpl in *; inv Hn; simpl; auto.
  Qed.

  Fact unnest_case_normalized_cexp : forall e es d tys ck,
      normalized_lexp e ->
      Forall (fun es => Forall normalized_cexp (snd es)) es ->
      LiftO True (Forall normalized_cexp) d ->
      Forall normalized_cexp (unnest_case e es d tys ck).
  Proof.
    intros * Hes Hd. unfold unnest_case. revert es d Hes Hd.
    induction tys; intros * Hnormed; constructor; eauto.
    - econstructor; eauto.
      + rewrite Forall_map.
        eapply Forall_impl; [|eauto]; intros * Hn.
        destruct a0; simpl in *; inv Hn; eauto.
      + intros ? Hopt. eapply option_map_inv in Hopt as (?&?&?); subst; simpl in *.
        inv H; eauto.
    - eapply IHtys; eauto.
      + rewrite Forall_map.
        eapply Forall_impl; [|eauto]; intros * Hn.
        destruct a0; simpl in *; inv Hn; simpl; auto.
      + destruct d; inv H; simpl; auto.
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
      apply mmap2_normalized_lexp in H0.
      repeat rewrite_Forall_forall.
      repeat simpl_In...
    - (* merge *)
      destruct a. repeat inv_bind.
      eapply unnest_merge_normalized_cexp...
      apply mmap2_normalized_cexp'' in H0; [|solve_forall].
      2:{ repeat inv_bind. eapply mmap2_normalized_cexp' in H2; solve_forall... }
      apply Forall_concat in H0; rewrite Forall_map in H0; auto.
    - (* case *)
      destruct a. repeat inv_bind.
      eapply unnest_case_normalized_cexp...
      + apply mmap2_normalized_cexp'' in H2; [|solve_forall]; eauto.
        { apply Forall_concat in H2; rewrite Forall_map in H2; auto. }
        repeat inv_bind; simpl; auto.
        eapply mmap2_normalized_cexp' in H5; eauto.
      + destruct d; repeat inv_bind; simpl in *; auto.
        eapply mmap2_normalized_cexp' in H3; [|solve_forall]; eauto.
    - (* app *)
      solve_forall.
      repeat simpl_In. destruct a0...
  Qed.
  Hint Resolve unnest_exp_normalized_cexp.

  Corollary mmap2_normalized_cexp : forall G es es' eqs' st st',
      mmap2 (unnest_exp G true) es st = (es', eqs', st') ->
      Forall normalized_cexp (concat es').
  Proof.
    intros. apply mmap2_normalized_cexp' in H; auto.
    solve_forall.
  Qed.

  Corollary mmap2_normalized_cexps : forall G (es : list (enumtag * list exp)) es' eqs' st st',
      mmap2 (fun '(i, es) => do (es', eqs') <- mmap2 (unnest_exp G true) es;
                          ret (i, concat es', concat eqs')) es st = (es', eqs', st') ->
      Forall (fun es => Forall normalized_cexp (snd es)) es'.
  Proof.
    intros. apply mmap2_normalized_cexp'' in H.
    - apply Forall_concat in H; rewrite Forall_map in H; auto.
    - solve_forall; repeat inv_bind.
      apply mmap2_normalized_cexp in H1; auto.
  Qed.

  Fact mmap2_unnested_eq {PSyn A A1} :
    forall (G: @global PSyn local_prefs) (k : A -> FreshAnn (A1 * (list equation))) a a1s eqs' st st',
      mmap2 k a st = (a1s, eqs', st') ->
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
      mmap2 (unnest_exp G false) es st = (es', eqs', st') ->
      unnest_noops_exps (find_node_incks G f) (concat es') st' = (es'', eqs'', st'') ->
      Forall normalized_lexp es'' /\
      Forall2 noops_exp (map (fun '(_, (_, ck, _)) => ck) (n_in n)) es''.
  Proof.
    intros * Hwl Hlen Hfind Hmap Hun.
    assert (Hnormed:=Hmap). eapply mmap2_normalized_lexp in Hnormed.
    eapply mmap2_unnest_exp_length in Hmap; eauto. rewrite <- Hmap in Hlen.
    unfold find_node_incks, unnest_noops_exps in Hun. rewrite Hfind in Hun.
    repeat inv_bind.
    remember (concat es') as es0. clear Heqes0.
    clear Hfind Hwl Hmap st eqs'.
    revert es0 st' st'' es'' x0 H Hlen Hnormed.
    induction (n_in n) as [|(?&(?&?)&?)]; intros * Hmap Hlen Hnormed; simpl in *; repeat inv_bind; auto.
    destruct es0; simpl in *; repeat inv_bind. congruence.
    inv Hlen. inv Hnormed. eapply IHl in H0 as (?&?); eauto.
    unfold unnest_noops_exp in H.
    destruct (hd _ _) as (?&?&?).
    destruct (is_noops_exp _ _) eqn:Hnoops; repeat inv_bind.
    - split; econstructor; eauto. eapply is_noops_exp_spec in Hnoops; eauto.
    - destruct c; split; econstructor; simpl; eauto.
  Qed.

  Lemma unnest_noops_exp_unnested_eq : forall G es f n es' es'' eqs' eqs'' st st' st'',
      Forall (wl_exp G) es ->
      length (annots es) = length (n_in n) ->
      find_node f G = Some n ->
      mmap2 (unnest_exp G false) es st = (es', eqs', st') ->
      unnest_noops_exps (find_node_incks G f) (concat es') st' = (es'', eqs'', st'') ->
      Forall (unnested_equation G) eqs''.
  Proof.
    intros * Hwl Hlen Hfind Hmap Hun.
    assert (Hnormed:=Hmap). eapply mmap2_normalized_lexp in Hnormed.
    eapply mmap2_unnest_exp_length in Hmap; eauto. rewrite <- Hmap in Hlen.
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
      2:eapply mmap2_unnested_eq in H1; eauto; inv Hwl; solve_forall.
      2:eapply mmap2_unnested_eq in H2; eauto; inv Hwl; solve_forall.
      eapply Forall_forall; intros ? Hin.
      eapply mk_equations_In in Hin as (?&?&?&?&Hfby); subst.
      2:{ inv Hwl. apply idents_for_anns_length in H3.
          rewrite unnest_fby_length, map_length; auto.
          - apply mmap2_unnest_exp_length in H1; auto.
            congruence.
          - apply mmap2_unnest_exp_length in H2; auto.
            congruence.
      }
      unfold unnest_fby in Hfby; repeat simpl_In.
      econstructor.
      eapply Forall_forall in H7...
      eapply Forall_forall in H4...
    - (* arrow *)
      repeat rewrite Forall_app; repeat split.
      2:eapply mmap2_unnested_eq in H1; eauto; inv Hwl; solve_forall.
      2:eapply mmap2_unnested_eq in H2; eauto; inv Hwl; solve_forall.
      eapply Forall_forall; intros ? Hin.
      eapply mk_equations_In in Hin as (?&?&?&?&Harrow); subst.
      2:{ inv Hwl. apply idents_for_anns_length in H3.
          rewrite unnest_arrow_length, map_length; auto.
          - apply mmap2_unnest_exp_length in H1; auto.
            congruence.
          - apply mmap2_unnest_exp_length in H2; auto.
            congruence.
      }
      unfold unnest_arrow in Harrow; repeat simpl_In.
      econstructor.
      eapply Forall_forall in H7...
      eapply Forall_forall in H4...
    - (* when *)
      inv Hwl. repeat inv_bind.
      eapply mmap2_unnested_eq in H0; eauto. solve_forall.
    - (* merge *)
      inv Hwl.
      destruct is_control; repeat inv_bind;
        repeat rewrite Forall_app; repeat split.
      1,3: (eapply mmap2_unnested_eq; eauto; solve_forall; repeat inv_bind;
            eapply mmap2_unnested_eq; eauto; solve_forall).
      rewrite Forall_forall; intros ? Hin.
      eapply mk_equations_In in Hin as (?&?&?&?&Hmerge); subst.
      2:{ apply idents_for_anns_length in H1. rewrite map_length in H1.
          rewrite unnest_merge_length, map_length... }
      econstructor; eauto.
      eapply Forall_forall in Hmerge; [|eapply unnest_merge_normalized_cexp]; eauto.
      eapply mmap2_normalized_cexps in H0; eauto.
    - (* case *)
      inv Hwl.
      destruct is_control; repeat inv_bind; unfold unnest_case;
        repeat rewrite Forall_app; repeat split.
      1,5:(eapply IHe; eauto).
      1,4: (eapply mmap2_unnested_eq; eauto; solve_forall;
            repeat inv_bind; auto;
            eapply mmap2_unnested_eq; eauto; solve_forall).
      1,3:(destruct d; repeat inv_bind; simpl in *; auto;
           eapply mmap2_unnested_eq; eauto; solve_forall;
           eapply Forall_forall in H11; eauto).
      rewrite Forall_forall; intros ? Hin.
      eapply mk_equations_In in Hin as (?&?&?&?&Hcase); subst.
      2:{ apply idents_for_anns_length in H4. rewrite map_length in H4.
          rewrite unnest_case_length, map_length... }
      econstructor; eauto.
      eapply Forall_forall in Hcase; [|eapply unnest_case_normalized_cexp]; eauto.
      + apply mmap2_normalized_cexp'' in H2; [|solve_forall]; eauto.
        apply Forall_concat in H2; rewrite Forall_map in H2; auto.
        repeat inv_bind; simpl; auto.
        eapply mmap2_normalized_cexp' in H10; eauto.
        solve_forall.
      + destruct d; repeat inv_bind; simpl; auto.
        eapply mmap2_normalized_cexp in H3; eauto.
    - (* app *)
      assert (length (concat x6) = length (find_node_incks G f)).
      { erewrite mmap2_unnest_exp_length; [|inv Hwl |eauto]. 2:eauto.
        unfold find_node_incks. inv Hwl.
        rewrite H13, map_length. congruence. }
      constructor. 2:repeat rewrite Forall_app; repeat split.
      + eapply unnest_resets_is_var in H3.
        inv Hwl; eapply unnest_noops_exp_noops_exp in H2 as (?&?). 3-5:eauto. 1,2:eauto.
      + eapply mmap2_unnested_eq in H1... inv Hwl; solve_forall.
      + inv Hwl; eapply unnest_noops_exp_unnested_eq in H2. 3-5:eauto. 1,2:eauto.
      + eapply unnest_resets_unnested_eq in H3...
        inv Hwl; solve_forall.
        split; eauto.
        eapply unnest_exp_normalized_cexp in H7.
        solve_forall.
  Qed.
  Local Hint Resolve unnest_exp_unnested_eq.

  Corollary unnest_exps_unnested_eq : forall G es es' eqs' st st',
      Forall (wl_exp G) es ->
      unnest_exps G es st = (es', eqs', st') ->
      Forall (unnested_equation G) eqs'.
  Proof.
    intros * Hwl Hnorm.
    unfold unnest_exps in Hnorm. repeat inv_bind.
    eapply mmap2_unnested_eq in H; eauto.
    solve_forall.
  Qed.
  Local Hint Resolve unnest_exps_unnested_eq.

  Fact unnested_equation_unnested_rhs {PSyn prefs} : forall (G: @global PSyn prefs) xs es,
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
    eapply mmap2_values in H.
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
    - (* arrow *)
      repeat inv_bind.
      repeat rewrite Forall_app; repeat split...
      1,2:eapply unnest_exps_unnested_eq; [|eauto]; inv Hwl; eauto.
    - (* app *)
      repeat inv_bind...
      eapply unnest_resets_unnested_eq with (G0:=G) in H1.
      2:{ inv Hwl; solve_forall.
          split; eauto.
          eapply unnest_exp_normalized_cexp in H4; eauto. solve_forall. }
      repeat rewrite Forall_app; repeat split; auto.
      apply unnest_exps_unnested_eq in H; inv Hwl; eauto.
      unfold unnest_exps in H; repeat inv_bind.
      inv Hwl.
      eapply unnest_noops_exp_unnested_eq with (es:=l) in H0; eauto.
  Qed.
  Hint Resolve unnest_rhs_unnested_eq.

  Corollary unnest_rhss_unnested_eq : forall G es es' eqs' st st',
      Forall (wl_exp G) es ->
      unnest_rhss G es st = (es', eqs', st') ->
      Forall (unnested_equation G) eqs'.
  Proof.
    intros * Hwl Hnorm.
    unfold unnest_rhss in Hnorm; repeat inv_bind.
    eapply mmap2_unnested_eq in H; eauto.
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
      induction H; intros xs Hlen; simpl in *; try constructor.
      + destruct xs; simpl in *; auto. congruence.
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

  Lemma unnest_block_unnested_block : forall G blk blks' st st',
      wl_block G blk ->
      nolocal_block blk ->
      unnest_block G blk st = (blks', st') ->
      Forall (unnested_block G) blks'.
  Proof.
    induction blk using block_ind2; intros * Hwl Hnl Hun; inv Hwl; inv Hnl; repeat inv_bind.
    - eapply unnest_equation_unnested_eq in H; eauto.
      rewrite Forall_map. rewrite Forall_forall in *; auto.
    - apply Forall_app. split.
      + eapply unnest_reset_is_var in H5 as (xr&ann&?); subst.
        clear - H H0 H1 H2.
        revert st x x0 H0. induction H; inv H1; inv H2; intros; repeat inv_bind; simpl; auto.
        rewrite map_app, Forall_app. split; eauto.
        eapply H in H1; eauto. clear - H1.
        induction H1; simpl; constructor; auto.
      + eapply unnest_reset_unnested_eq in H5.
        2:{ intros; split; eauto.
            eapply unnest_exp_normalized_cexp in H6; eauto.
            eapply Forall_impl; [|eauto]; intros; eauto. }
        rewrite Forall_map. rewrite Forall_forall in *; auto.
  Qed.

  Corollary unnest_blocks_unnested_blocks : forall G blks blks' st st',
      Forall (wl_block G) blks ->
      Forall nolocal_block blks ->
      unnest_blocks G blks st = (blks', st') ->
      Forall (unnested_block G) blks'.
  Proof.
    induction blks; intros * Hwl Hnl Hnorm;
      unfold unnest_blocks in Hnorm; repeat inv_bind; simpl; auto.
    inv Hwl. inv Hnl. apply Forall_app; split.
    - eapply unnest_block_unnested_block; eauto.
    - eapply IHblks; eauto.
      unfold unnest_blocks; repeat inv_bind; repeat eexists; eauto.
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
    induction e using exp_ind2; intros Hnormed; inv Hnormed; simpl...
    - inv H...
    - inv H. rewrite IHe1, IHe2...
    - inv H1.
    - inv H1.
    - inv H0... inv H. simpl. rewrite H3...
    - eapply Forall_Forall in H; eauto. clear H1.
      induction H; simpl; auto.
      destruct H as ((?&Heq&?)&Hf); subst. rewrite Heq in *; inv Hf.
      simpl. rewrite H3, IHForall; auto.
    - inv H0.
    - rewrite IHe; simpl; auto.
      replace (or_default_with [] (flat_map fresh_in) d) with (@nil (ident * (type * clock))).
      2:{ destruct d; simpl in *; auto.
          specialize (H7 _ eq_refl) as (?&?&Hnormed); subst.
          simpl. inv H0. rewrite H3; auto. }
      rewrite app_nil_r.
      eapply Forall_Forall in H; eauto. clear H6.
      induction H; simpl; auto.
      destruct H as ((?&Heq&?)&Hf); subst. rewrite Heq in *; inv Hf.
      simpl. rewrite H5, IHForall; auto.
    - inv H1.
    - inv H1.
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

  Corollary unnest_exp_no_anon : forall G e is_control es' eqs' st st',
      unnest_exp G is_control e st = (es', eqs', st') ->
      anon_ins es' = [].
  Proof.
    intros * Hnorm.
    unfold anon_ins. rewrite flat_map_concat_map, concat_eq_nil, Forall_map.
    destruct is_control.
    - apply unnest_exp_normalized_cexp in Hnorm.
      eapply Forall_impl; eauto. intros. apply normalized_cexp_no_fresh in H; auto.
      apply incl_nil. rewrite <-H. apply anon_in_fresh_in.
    - apply unnest_exp_normalized_lexp in Hnorm.
      eapply Forall_impl; eauto. intros. apply normalized_lexp_no_fresh in H; auto.
      apply incl_nil. rewrite <-H. apply anon_in_fresh_in.
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

  Fact unnested_equation_no_anon {PSyn prefs} : forall (G: @global PSyn prefs) e,
      unnested_equation G e ->
      anon_in_eq e = [].
  Proof with eauto.
    intros * Hnormed.
    induction Hnormed; unfold anon_in_eq, anon_ins; simpl; repeat rewrite app_nil_r.
    1-3:repeat rewrite normalized_lexp_no_fresh; repeat rewrite normalized_lexps_no_fresh...
    1:eapply Forall_impl; [|eauto]; intros ? (?&(?&?)&?); subst; constructor.
    - (* cexp *)
      specialize (anon_in_fresh_in e) as Hincl.
      rewrite normalized_cexp_no_fresh in Hincl...
      apply incl_nil...
  Qed.

  Fact unnested_block_no_anon {PSyn prefs} : forall (G: @global PSyn prefs) d,
      unnested_block G d ->
      anon_in_block d = [].
  Proof.
    induction d using block_ind2; intros * Hun; inv Hun; simpl.
    - eapply unnested_equation_no_anon; eauto.
    - apply Forall_singl in H. rewrite H; eauto.
  Qed.

  Corollary unnested_blocks_no_anon {PSyn prefs} : forall (G: @global PSyn prefs) blocks,
      Forall (unnested_block G) blocks ->
      flat_map anon_in_block blocks = [].
  Proof.
    induction blocks; intros * Hf; inv Hf; simpl; auto.
    erewrite unnested_block_no_anon; eauto.
  Qed.

  (** Weaker lemmas, but we dont need wl_exp : there is no anon in the generated equations *)

  Fact mk_equations_empty_no_anon_in_eq : forall xs,
      flat_map anon_in_eq (mk_equations xs []) = [].
  Proof.
    induction xs; simpl; auto.
  Qed.
  Hint Resolve mk_equations_empty_no_anon_in_eq.

  Fact unnest_noops_exps_no_fresh : forall ins es st es' eqs' st' ,
      Forall normalized_lexp es ->
      unnest_noops_exps ins es st = (es', eqs', st') ->
      fresh_ins es' = [].
  Proof.
    unfold unnest_noops_exps.
    induction ins; intros * Hnormed Hun; inv Hnormed; repeat inv_bind; auto.
    simpl. erewrite IHins; repeat inv_bind; eauto.
    unfold unnest_noops_exp in H1. destruct (hd _ _) as (?&?&?).
    destruct (is_noops_exp _ _); repeat inv_bind; simpl; auto.
    erewrite normalized_lexp_no_fresh; eauto.
  Qed.

  Fact unnest_noops_exps_no_anon_in_eq : forall ins es st es' eqs' st' ,
      Forall normalized_lexp es ->
      unnest_noops_exps ins es st = (es', eqs', st') ->
      flat_map anon_in_eq eqs' = [].
  Proof.
    unfold unnest_noops_exps.
    induction ins; intros * Hnormed Hun; inv Hnormed; repeat inv_bind; auto.
    simpl. erewrite <-flat_map_app, (IHins _ _ _ (concat x5)); repeat inv_bind; eauto.
    unfold unnest_noops_exp in H1. destruct (hd _ _) as (?&?&?).
    destruct (is_noops_exp _ _); repeat inv_bind; simpl; auto.
    unfold anon_in_eq; simpl.
    repeat rewrite app_nil_r.
    eapply incl_nil.
    erewrite <-normalized_lexp_no_fresh; eauto.
    apply anon_in_fresh_in.
  Qed.

  Fact mmap2_unnest_exp_no_anon_in_eq : forall G is_control es es' eqs' st st' ,
      Forall
        (fun e => forall is_control es' eqs' st st' ,
             unnest_exp G is_control e st = (es', eqs', st') ->
             flat_map anon_in_eq eqs' = []) es ->
      mmap2 (unnest_exp G is_control) es st = (es', eqs', st') ->
      flat_map anon_in_eq (concat eqs') = [].
  Proof.
    induction es; intros * Hf Hmap; inv Hf; repeat inv_bind; simpl; auto.
    rewrite <-flat_map_app.
    erewrite H1, IHes; eauto.
  Qed.

  Corollary mmap2_mmap2_unnest_exp_no_anon_in_eq : forall G is_control (es : list (enumtag * list exp)) es' eqs' st st' ,
      Forall
        (fun es => Forall
                  (fun e => forall is_control es' eqs' st st' ,
                       unnest_exp G is_control e st = (es', eqs', st') ->
                       flat_map anon_in_eq eqs' = []) (snd es)) es ->
      mmap2 (fun '(i, es) => do (es0, eqs)<- mmap2 (unnest_exp G is_control) es;
                          ret (i, concat es0, concat eqs)) es st = (es', eqs', st') ->
      flat_map anon_in_eq (concat eqs') = [].
  Proof.
    induction es as [|(?&?)]; intros * Hf Hmap; inv Hf; repeat inv_bind; simpl; auto.
    rewrite <-flat_map_app.
    erewrite mmap2_unnest_exp_no_anon_in_eq, IHes; eauto.
  Qed.

  (* Fact mmap2_mmap2_unnest_exp_no_anon_in_eq' : forall G is_control es es' eqs' st st', *)
  (*     Forall *)
  (*       (LiftO True *)
  (*          (Forall *)
  (*             (fun e => forall is_control es' eqs' st st', *)
  (*                  unnest_exp G is_control e st = (es', eqs', st') -> *)
  (*                  flat_map anon_in_eq eqs' = []))) es -> *)
  (*   mmap2 *)
  (*     (or_default_with *)
  (*        (ret (None, [])) *)
  (*        (fun es => *)
  (*           do (es', eqs')<- (do (es0, eqs)<- mmap2 (unnest_exp G is_control) es; ret (concat es0, concat eqs)); *)
  (*           ret (Some es', eqs'))) es st = (es', eqs', st') -> *)
  (*   flat_map anon_in_eq (concat eqs') = []. *)
  (* Proof. *)
  (*   induction es; intros * Hf Hmap; inv Hf; repeat inv_bind; simpl; auto. *)
  (*   rewrite <-flat_map_app. *)
  (*   erewrite IHes; eauto. *)
  (*   destruct a; repeat inv_bind; auto. *)
  (*   erewrite mmap2_unnest_exp_no_anon_in_eq; eauto. *)
  (* Qed. *)

  Lemma unnest_reset_no_anon_in_eq : forall f e es' eqs' st st' ,
      (forall es' eqs' st st' ,
          f e st = (es', eqs', st') ->
          anon_ins es' = []) ->
      (forall es' eqs' st st' ,
          f e st = (es', eqs', st') ->
          flat_map anon_in_eq eqs' = []) ->
      unnest_reset f e st = (es', eqs', st') ->
      flat_map anon_in_eq eqs' = [].
  Proof.
    intros * Hanon Hanoneq Hres.
    unnest_reset_spec.
    - erewrite Hanoneq; eauto.
    - simpl. erewrite Hanoneq; eauto.
      unfold anon_in_eq; simpl.
      eapply Hanon in Hk0.
      destruct l; simpl in *; auto.
      apply app_eq_nil in Hk0 as (Hk0&_).
      repeat rewrite app_nil_r; auto.
  Qed.

  Corollary mmap2_unnest_reset_no_anon_in_eq : forall G is_control es es' eqs' st st' ,
      Forall
        (fun e => forall is_control es' eqs' st st' ,
             unnest_exp G is_control e st = (es', eqs', st') ->
             flat_map anon_in_eq eqs' = []) es ->
      mmap2 (unnest_reset (unnest_exp G is_control)) es st = (es', eqs', st') ->
      flat_map anon_in_eq (concat eqs') = [].
  Proof.
    induction es; intros * Hf Hmap; inv Hf; repeat inv_bind; simpl; auto.
    rewrite <-flat_map_app.
    erewrite IHes, app_nil_r; eauto.
    clear IHes H0 H2.
    eapply unnest_reset_no_anon_in_eq; eauto.
    intros * Hun. eapply unnest_exp_no_fresh in Hun.
    eapply incl_nil. rewrite <-Hun. apply anon_ins_fresh_ins.
  Qed.

  Lemma unnest_exp_no_anon_in_eq : forall G e is_control es' eqs' st st' ,
      unnest_exp G is_control e st = (es', eqs', st') ->
      flat_map anon_in_eq eqs' = [].
  Proof.
    induction e using exp_ind2; intros * Hun; repeat inv_bind; repeat rewrite <-flat_map_app; auto.
    - (* unop *)
      eapply IHe in H; auto.
    - (* binop *)
      erewrite IHe1, IHe2; eauto.
    - (* fby *)
      eapply mmap2_unnest_exp_no_anon_in_eq in H; eauto.
      eapply mmap2_unnest_exp_no_anon_in_eq in H0; eauto.
      rewrite H, H0; simpl; rewrite app_nil_r.
      eapply mmap2_normalized_lexp in H1. eapply mmap2_normalized_lexp in H2.
      eapply idents_for_anns_values in H3.
      unfold unnest_fby.
      clear - H1 H2 H3. revert a H1 H2 H3.
      generalize (concat x2) (concat x6). clear x2 x6.
      induction x5; intros; simpl; auto.
      destruct a0, l, l0; simpl; auto.
      inv H1; inv H2; inv H3. erewrite IHx5; eauto.
      unfold anon_in_eq; simpl.
      repeat rewrite normalized_lexp_no_fresh; auto.
    - (* arrow *)
      eapply mmap2_unnest_exp_no_anon_in_eq in H; eauto.
      eapply mmap2_unnest_exp_no_anon_in_eq in H0; eauto.
      rewrite H, H0; simpl; rewrite app_nil_r.
      eapply mmap2_normalized_lexp in H1. eapply mmap2_normalized_lexp in H2.
      eapply idents_for_anns_values in H3.
      unfold unnest_arrow.
      clear - H1 H2 H3. revert a H1 H2 H3.
      generalize (concat x2) (concat x6). clear x2 x6.
      induction x5; intros; simpl; auto.
      destruct a0, l, l0; simpl; auto.
      inv H1; inv H2; inv H3. erewrite IHx5; eauto.
      unfold anon_in_eq; simpl.
      repeat rewrite normalized_lexp_no_fresh; auto.
    - (* when *)
      destruct a; repeat inv_bind.
      eapply mmap2_unnest_exp_no_anon_in_eq in H; eauto.
    - (* merge *)
      destruct a; repeat inv_bind.
      eapply mmap2_mmap2_unnest_exp_no_anon_in_eq in H; eauto.
      destruct is_control; repeat inv_bind; eauto.
      rewrite <- flat_map_app, H, app_nil_r.
      eapply mmap2_normalized_cexps in H0.
      clear - H0 H. revert x0 l H0.
      induction x3; simpl; intros; auto.
      destruct l; simpl; auto.
      rewrite IHx3; eauto.
      2:(rewrite Forall_map; eapply Forall_impl; [|eauto];
         intros es Hce; destruct es; inv Hce; simpl in *; subst; simpl; auto).
      unfold anon_in_eq; simpl.
      repeat rewrite app_nil_r.
      clear - H0. induction H0; simpl in *; auto.
      rewrite IHForall. destruct x; simpl in *. inv H; simpl; auto. rewrite normalized_cexp_no_fresh; auto.
    - (* case *)
      destruct a; repeat inv_bind.
      specialize (IHe _ _ _ _ _ H1).
      eapply mmap2_mmap2_unnest_exp_no_anon_in_eq in H; eauto.
      assert (flat_map anon_in_eq x6 = []) as Heq2.
      { destruct d; repeat inv_bind; simpl; auto.
        eapply mmap2_unnest_exp_no_anon_in_eq in H3; eauto. }
      destruct is_control; repeat inv_bind; repeat rewrite <-flat_map_app; eauto.
      1,2:erewrite IHe, H, Heq2; eauto; repeat rewrite app_nil_r.
      apply mmap2_normalized_cexp'', Forall_concat in H2; [|solve_forall]; eauto.
      2:{ repeat inv_bind; simpl; auto.
          eapply mmap2_normalized_cexp' in H6; eauto.
          solve_forall. }
      assert (LiftO True (Forall normalized_cexp) x5) as Hnormd.
      { destruct d; repeat inv_bind; simpl in *; auto.
        eapply mmap2_normalized_cexp in H3; eauto. }
      eapply unnest_exp_normalized_lexp in H1.
      clear - H1 H2 Hnormd. revert H2 Hnormd. revert l x2 x5.
      induction x8; simpl; intros; auto.
      destruct l; simpl; auto.
      rewrite IHx8; eauto.
      2:{ rewrite map_map. rewrite Forall_map in *.
          eapply Forall_impl; [|eauto]. intros (?&es) Hce; destruct es; inv Hce; simpl; auto. }
      2:destruct x5; inv Hnormd; simpl; auto.
      unfold anon_in_eq; simpl.
      repeat rewrite app_nil_r.
      replace (fresh_in (hd_default x)) with (@nil (ident * (type * clock))).
      2:{ inv H1; auto. rewrite normalized_lexp_no_fresh; auto. }
      replace (or_default_with [] (flat_map fresh_in) (option_map (fun d : list exp => [hd_default d]) x5)) with (@nil (ident * (type * clock))).
      2:{ destruct x5; simpl in *; auto. inv Hnormd; simpl; auto.
          rewrite normalized_cexp_no_fresh; eauto. }
      rewrite app_nil_r; simpl.
      clear - H2. rewrite Forall_map in H2. induction H2; simpl in *; auto.
      rewrite IHForall. destruct x; simpl in *; auto.
      inv H; auto. rewrite normalized_cexp_no_fresh; auto.
    - (* app *)
      eapply mmap2_unnest_exp_no_anon_in_eq in H; eauto.
      eapply mmap2_unnest_reset_no_anon_in_eq in H0; eauto.
      erewrite H, H0, app_nil_r; simpl.
      eapply mmap2_normalized_lexp in H1.
      erewrite unnest_noops_exps_no_anon_in_eq; eauto.
      unfold anon_in_eq; simpl.
      erewrite unnest_noops_exps_no_fresh; eauto.
      erewrite unnest_resets_no_fresh; eauto.
  Qed.

  Lemma unnest_rhs_no_anon : forall G e es' eqs' st st' ,
      unnest_rhs G e st = (es', eqs', st') ->
      anon_ins es' = [].
  Proof.
    unfold anon_ins.
    intros * Hun.
    destruct e; try apply unnest_exp_no_anon in Hun; eauto.
    - (* fby *)
      simpl in Hun; repeat inv_bind.
      eapply unnest_exps_no_fresh in H.
      eapply unnest_exps_no_fresh in H0.
      revert x x2 H H0.
      unfold unnest_fby.
      induction l1; intros; destruct x, x2; simpl in *; auto.
      apply app_eq_nil in H as (?&?). apply app_eq_nil in H0 as (?&?).
      now rewrite H, H0, IHl1.
    - (* arrow *)
      simpl in Hun; repeat inv_bind.
      eapply unnest_exps_no_fresh in H.
      eapply unnest_exps_no_fresh in H0.
      revert x x2 H H0.
      unfold unnest_arrow.
      induction l1; intros; destruct x, x2; simpl in *; auto.
      apply app_eq_nil in H as (?&?). apply app_eq_nil in H0 as (?&?).
      now rewrite H, H0, IHl1.
    - (* app *)
      simpl in Hun; repeat inv_bind.
      eapply unnest_noops_exps_no_fresh in H0; eauto using unnest_exps_normalized_lexp.
      eapply unnest_resets_no_fresh in H1.
      unfold fresh_ins in *.
      now rewrite H0, H1.
  Qed.

  Lemma unnest_rhs_no_anon_in_eq : forall G e es' eqs' st st' ,
      unnest_rhs G e st = (es', eqs', st') ->
      flat_map anon_in_eq eqs' = [].
  Proof.
    intros * Hun.
    destruct e; try apply unnest_exp_no_anon_in_eq in Hun; eauto.
    - (* fby *)
      simpl in Hun; unfold unnest_exps in Hun; repeat inv_bind.
      repeat rewrite <-flat_map_app.
      eapply mmap2_unnest_exp_no_anon_in_eq in H.
      eapply mmap2_unnest_exp_no_anon_in_eq in H0.
      2-4:solve_forall; eauto using unnest_exp_no_anon_in_eq.
      now rewrite H, H0.
    - (* arrow *)
      simpl in Hun; unfold unnest_exps in Hun; repeat inv_bind.
      repeat rewrite <-flat_map_app.
      eapply mmap2_unnest_exp_no_anon_in_eq in H.
      eapply mmap2_unnest_exp_no_anon_in_eq in H0.
      2-4:solve_forall; eauto using unnest_exp_no_anon_in_eq.
      now rewrite H, H0.
    - (* app *)
      simpl in Hun; unfold unnest_exps in Hun; repeat inv_bind.
      repeat rewrite <-flat_map_app.
      eapply unnest_noops_exps_no_anon_in_eq in H0. 2:eapply mmap2_normalized_lexp; eauto.
      eapply mmap2_unnest_exp_no_anon_in_eq in H.
      eapply mmap2_unnest_reset_no_anon_in_eq in H1.
      2-3:solve_forall; eauto using unnest_exp_no_anon_in_eq.
      now rewrite H, H0, H1.
  Qed.

  Lemma unnest_equation_no_anon_in_eq : forall G equ eqs' st st' ,
      unnest_equation G equ st = (eqs', st') ->
      flat_map anon_in_eq eqs' = [].
  Proof.
    intros ? (?&?) * Hun. simpl in Hun; repeat inv_bind.
    rewrite <-flat_map_app.
    replace (flat_map anon_in_eq x0) with (@nil (ident * (type * clock))).
    2:{ unfold unnest_rhss in H. revert x x0 st st' H.
        induction l0; intros; repeat inv_bind; auto.
        simpl.
        erewrite <-flat_map_app, unnest_rhs_no_anon_in_eq; eauto; simpl.
        eapply IHl0; eauto. repeat inv_bind; eauto. }
    rewrite app_nil_r.
    assert (flat_map anon_in x = []) as Hanon.
    { revert x x0 st st' H. unfold unnest_rhss.
      induction l0; intros; repeat inv_bind; simpl; auto.
      erewrite <-flat_map_app, (IHl0 (concat x4)). 2:repeat inv_bind; eauto.
      erewrite unnest_rhs_no_anon; eauto.
    }
    clear - Hanon.
    revert l. induction x; intros; repeat inv_bind; simpl.
    - induction l; simpl; auto.
    - simpl in *.
      apply app_eq_nil in Hanon as (Han1&Han2).
      unfold anon_in_eq; simpl. rewrite Han1; simpl; auto.
  Qed.

  Fact mmap_no_anon : forall f blks blks' st st',
      Forall (fun blk => forall blks' st st',
                  nolocal_block blk ->
                  f blk st = (blks', st') ->
                  flat_map anon_in_block blks' = []) blks ->
      Forall nolocal_block blks ->
      mmap (f : block -> FreshAnn _) blks st = (blks', st') ->
      flat_map anon_in_block (concat blks') = [].
  Proof.
    induction blks; intros * Hf Hnl Hmap; inv Hf; inv Hnl; repeat inv_bind; simpl.
    - reflexivity.
    - rewrite <-flat_map_app.
      erewrite H1; eauto. erewrite IHblks; eauto.
  Qed.

  Lemma unnest_block_no_anon : forall G blk blks' st st' ,
      nolocal_block blk ->
      unnest_block G blk st = (blks', st') ->
      flat_map anon_in_block blks' = [].
  Proof.
    induction blk using block_ind2; intros * Hnl Hun; inv Hnl; repeat inv_bind; simpl.
    - eapply unnest_equation_no_anon_in_eq in H.
      rewrite flat_map_concat_map, map_map; simpl.
      rewrite <-flat_map_concat_map. setoid_rewrite H. reflexivity.
    - assert (Hres:=H2). eapply unnest_reset_no_anon_in_eq in H2.
      2:eapply unnest_exp_no_anon; eauto.
      2:eapply unnest_exp_no_anon_in_eq; eauto.
      eapply unnest_reset_is_var in Hres as (id&ann&?); subst.
      rewrite <-flat_map_app, 2 flat_map_concat_map, 2 map_map; simpl.
      erewrite map_ext; [|intros; rewrite 2 app_nil_r; reflexivity].
      rewrite <-2 flat_map_concat_map.
      do 2 replace (flat_map _ _) with (@nil (ident * (type * clock))); auto.
      eapply mmap_no_anon in H0; eauto.
  Qed.

  Corollary unnest_blocks_no_anon : forall G blks blks' st st',
      Forall nolocal_block blks ->
      unnest_blocks G blks st = (blks', st') ->
      flat_map anon_in_block blks' = [].
  Proof.
    unfold unnest_blocks.
    intros * Hnl Hun; repeat inv_bind.
    eapply mmap_no_anon in H; eauto.
    eapply Forall_forall; intros; eauto using unnest_block_no_anon.
  Qed.

  Lemma unnest_block_GoodLocals G : forall prefs blk blk' st st',
      GoodLocals prefs blk ->
      unnest_block G blk st = (blk', st') ->
      Forall (GoodLocals prefs) blk'.
  Proof.
    induction blk using block_ind2; intros * Hgood Hun; inv Hgood; repeat inv_bind.
    - (* equation *)
      eapply Forall_map, Forall_forall; intros * Hin. constructor.
    - (* reset *)
      apply Forall_app; split.
      + assert (Forall (GoodLocals prefs) (concat x)) as Hgood.
        { eapply mmap_values, Forall2_ignore1 in H0.
          eapply Forall_concat. rewrite Forall_forall in *; intros.
          specialize (H0 _ H3) as (?&Hinblk&?&?&Hun).
          eapply H; eauto. }
        rewrite Forall_map, Forall_forall. intros ? Hin. constructor.
        eapply Forall_forall in Hgood; eauto.
      + rewrite Forall_map, Forall_forall. intros ? Hin. constructor.
    - (* locals *)
      do 2 (constructor; auto).
  Qed.

  Corollary unnest_blocks_GoodLocals G : forall prefs blks blks' st st',
      Forall (GoodLocals prefs) blks ->
      unnest_blocks G blks st = (blks', st') ->
      Forall (GoodLocals prefs) blks'.
  Proof.
    intros * Hgood Hun.
    unfold unnest_blocks in Hun. repeat inv_bind.
    eapply mmap_values, Forall2_ignore1 in H.
    eapply Forall_concat. rewrite Forall_forall in *; intros.
    specialize (H _ H0) as (?&Hinblk&?&?&Hun); eauto.
    eapply unnest_block_GoodLocals; eauto.
  Qed.

  Fact mmap_NoDupLocals (f : block -> FreshAnn (list block)) env : forall blks blks' st st',
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

  Lemma unnest_block_NoDupLocals G env : forall blk blks' st st',
      NoDupLocals env blk ->
      unnest_block G blk st = (blks', st') ->
      Forall (NoDupLocals env) blks'.
  Proof.
    induction blk using block_ind2; intros * Hnd Hun; repeat inv_bind.
    - (* equation *)
      inv Hnd.
      rewrite Forall_map. eapply Forall_forall; intros. constructor.
    - (* reset *)
      inv Hnd.
      eapply Forall_app; split; rewrite Forall_map.
      + eapply mmap_NoDupLocals in H; eauto.
        eapply Forall_impl; [|eauto]; intros. constructor; auto.
      + eapply Forall_forall; intros. constructor.
    - constructor; auto.
  Qed.

  Corollary unnest_blocks_NoDupLocals G env : forall blks blks' st st',
      Forall (NoDupLocals env) blks ->
      unnest_blocks G blks st = (blks', st') ->
      Forall (NoDupLocals env) blks'.
  Proof.
    intros * Hnd Hun. unfold unnest_blocks in Hun; repeat inv_bind.
    eapply mmap_NoDupLocals in H; eauto.
    solve_forall. eapply unnest_block_NoDupLocals; eauto.
  Qed.

  (** *** nolocal_block *)

  Lemma unnest_block_nolocal : forall G blk blks' st st',
      nolocal_block blk ->
      unnest_block G blk st = (blks', st') ->
      Forall nolocal_block blks'.
  Proof.
    induction blk using block_ind2; intros * Hnl Hun; inv Hnl; repeat inv_bind.
    - (* equation *)
      rewrite Forall_map, Forall_forall. intros. constructor.
    - (* reset *)
      apply Forall_app; split.
      + eapply mmap_values, Forall2_ignore1 in H0.
        rewrite Forall_map, <-Forall_concat.
        eapply Forall_impl; [|eauto]; intros ? (?&?&?&?&?).
        rewrite Forall_forall in *. eapply H in H4; eauto.
        rewrite Forall_forall in *.
        intros. repeat constructor; eauto.
      + rewrite Forall_map, Forall_forall. intros. constructor.
  Qed.

  Corollary unnest_blocks_nolocal : forall G blks blks' st st',
      Forall nolocal_block blks ->
      unnest_blocks G blks st = (blks', st') ->
      Forall nolocal_block blks'.
  Proof.
    unfold unnest_blocks.
    intros * Hf Hun; repeat inv_bind.
    eapply mmap_values, Forall2_ignore1 in H.
    eapply Forall_concat, Forall_impl; [|eauto]; intros ? (?&?&?&?&?).
    eapply Forall_forall in Hf; eauto.
    eapply unnest_block_nolocal; eauto.
  Qed.

  (** ** Normalization of a full node *)

  Import Facts Tactics.

  Lemma norm1_not_in_local_prefs :
    ~PS.In norm1 local_prefs.
  Proof.
    unfold local_prefs, elab_prefs.
    rewrite PSF.add_iff, PSF.singleton_iff.
    pose proof gensym_prefs_NoDup as Hnd. unfold gensym_prefs in Hnd.
    intros [contra|contra]; subst; rewrite contra in Hnd.
    1,2:repeat rewrite NoDup_cons_iff in Hnd.
    - destruct Hnd as (_&Hnin&_).
      apply Hnin. left; auto.
    - destruct Hnd as (Hnin&_).
      apply Hnin. right; left; auto.
  Qed.

  Lemma unnest_node_init_st_valid {A PSyn} : forall (n: @node PSyn local_prefs) locs blks,
      n_block n = Blocal locs blks ->
      st_valid_reuse (@init_st A) (PSP.of_list (map fst (n_in n ++ n_out n ++ locs)))
                     (ps_adds (map fst (flat_map local_anon_in_block blks)) PS.empty).
  Proof.
    intros * Hn.
    specialize (n_nodup n) as (Hndup&Hndl).
    rewrite fst_NoDupMembers, Hn, map_app, map_fst_idty in Hndup; simpl in Hndup.
    rewrite Hn in Hndl; simpl in Hndl. inv Hndl. rewrite fst_NoDupMembers in H3.
    eapply init_st_valid_reuse.
    - replace (ps_adds _ PS.empty) with (ps_from_list (map fst (flat_map local_anon_in_block blks))); auto.
      rewrite ps_from_list_ps_of_list.
      assert (NoDup (map fst (n_in n ++ n_out n ++ locs) ++ map fst (flat_map local_anon_in_block blks))) as Hnd'.
      { setoid_rewrite fst_InMembers in H4.
        apply NoDup_app'; eauto using NoDup_app_r.
        rewrite app_assoc, map_app; apply NoDup_app'; eauto using NoDup_app_l, NoDup_app_r.
        2:eapply fst_NoDupMembers, local_anons_in_block_NoDupMembers, fst_NoDupMembers; eauto using NoDup_app_r.
        1,2:(eapply Forall_forall; intros; intro contra).
        2:(rewrite app_assoc, map_app, in_app_iff in H; destruct H as [Hin|Hin]).
        1,3:(eapply H4; eauto using in_or_app).
        - eapply in_or_app, or_intror. eapply incl_map; eauto using local_anons_in_block_incl.
        - eapply NoDup_app_In in Hndup; eauto.
          eapply Hndup, incl_map; eauto using local_anons_in_block_incl.
      }
      repeat rewrite ps_of_list_ps_to_list_Perm; repeat rewrite <- app_assoc in *; eauto using NoDup_app_l, NoDup_app_r.
    - apply norm1_not_in_local_prefs.
    - rewrite <- ps_from_list_ps_of_list, PS_For_all_Forall'.
      pose proof (n_good n) as (Good1&Good2&_); eauto. rewrite Hn in Good2. inv Good2.
      rewrite app_assoc, map_app, Forall_app. apply Forall_app in Good1 as (?&?). split; auto.
    - replace (ps_adds _ PS.empty) with (ps_from_list (map fst (flat_map local_anon_in_block blks))); auto.
      rewrite PS_For_all_Forall'.
      pose proof (n_good n) as (Good&_). rewrite Hn in Good.
      apply Forall_app in Good as (?&Good); auto.
      eapply Forall_incl; [eauto|]. eapply incl_map; eauto using local_anons_in_block_incl.
  Qed.

  Program Definition unnest_node G (n : @node nolocal_top_block local_prefs) : @node nolocal_top_block norm1_prefs :=
    {| n_name := (n_name n);
       n_hasstate := (n_hasstate n);
       n_in := (n_in n);
       n_out := (n_out n);
       n_block := match (n_block n) with
                  | Blocal vars blks =>
                    let res := unnest_blocks G blks init_st in
                    let nvars := st_anns (snd res) in
                    Blocal (vars++map (fun xtc => (fst xtc, ((fst (snd xtc)), snd (snd xtc), xH))) nvars) (fst res)
                  | blk => blk
                  end;
       n_ingt0 := (n_ingt0 n);
       n_outgt0 := (n_outgt0 n);
    |}.
  Next Obligation.
    pose proof (n_defd n) as (?&Hvars&Hperm).
    destruct (n_block n) eqn:Hn; eauto. inv Hvars.
    destruct (unnest_blocks _ _) as (blks'&st') eqn:Heqs.
    do 2 esplit; [|eauto].
    eapply unnest_blocks_vars_perm in Heqs as (ys&Hvars&Hperm'); eauto.
    econstructor; eauto.
    unfold st_ids in *. rewrite init_st_anns, app_nil_r in Hperm'.
    rewrite Hperm', <-H3, map_app, <-2 app_assoc.
    apply Permutation_app_head. rewrite Permutation_app_comm. apply Permutation_app_head.
    rewrite map_map; simpl. reflexivity.
  Qed.
  Next Obligation.
    pose proof (n_good n) as (_&Hgood&_).
    pose proof (n_nodup n) as (Hndup&Hndl).
    pose proof (n_syn n) as Hsyn. inv Hsyn. simpl. rewrite <-H in *.
    destruct (unnest_blocks G blks init_st) as (blks'&st') eqn:Hunn.
    repeat erewrite unnest_blocks_no_anon; eauto. repeat rewrite app_nil_r.
    split; eauto using NoDupMembers_app_l.
    assert (st_valid_reuse st' (PSP.of_list (map fst (n_in n ++ n_out n ++ locs))) PS.empty) as Hvalid.
    { eapply unnest_blocks_st_valid; eauto.
      - rewrite PSP.elements_empty, app_nil_r.
        eapply fst_NoDupMembers; eauto using NoDupMembers_app_r.
      - eapply unnest_node_init_st_valid; eauto.
    }
    inv Hndl.
    eapply st_valid_reuse_NoDupMembers in Hvalid.
    constructor; simpl.
    - eapply unnest_blocks_NoDupLocals; [|eauto].
      inv Hgood.
      rewrite Forall_forall in *. intros.
      rewrite (map_app _ locs), map_map; simpl.
      eapply NoDupLocals_incl' with (npref:=norm1). 1,2,4:eauto using norm1_not_in_local_prefs.
      assert (Forall (fun id => In id (map fst (flat_map anon_in_block blks)) \/ (exists x hint, id = gensym norm1 hint x)) (st_ids st')) as Hids.
      { eapply unnest_blocks_prefixed; eauto. }
      intros ? Hin. rewrite 2 in_app_iff in *. destruct Hin as [?|[?|Hin]]; auto.
      eapply Forall_forall in Hids as [?|?]; eauto.
    - rewrite 2 map_app, <-app_assoc, <-app_assoc in Hvalid. do 2 apply NoDup_app_r in Hvalid.
      rewrite fst_NoDupMembers, map_app, map_map; simpl; auto.
    - setoid_rewrite InMembers_app. intros * [Hinm|Hinm] Hin'.
      + eapply H6; eauto using in_or_app.
      + eapply NoDup_app_In in Hvalid; eauto. 2:rewrite app_assoc, map_app; eauto using in_or_app.
        rewrite fst_InMembers, map_map in Hinm; eauto.
    - rewrite app_assoc. apply NoDupMembers_app; auto.
      + apply NoDupMembers_app_l in Hndup. now rewrite NoDupMembers_idty in Hndup.
      + intros ? Hinm contra. rewrite fst_InMembers in Hinm.
        eapply H6; eauto using in_or_app.
  Qed.
  Next Obligation.
    specialize (n_nodup n) as (Hndup&Hndl).
    specialize (n_good n) as (Hgood1&Hgood2&Hname).
    pose proof (n_syn n) as Hsyn. inv Hsyn. rewrite <-H in *. simpl in *.
    destruct (unnest_blocks G blks init_st) as (blks'&st') eqn:Hunn.
    repeat erewrite unnest_blocks_no_anon; eauto. rewrite app_nil_r.
    repeat split; auto.
    - apply Forall_app in Hgood1 as (Hgood1&_); eauto using AtomOrGensym_add.
    - assert (st_valid_reuse st' (PSP.of_list (map fst (n_in n ++ n_out n ++ locs))) PS.empty) as Hvalid.
      { eapply unnest_blocks_st_valid; eauto.
        - rewrite PSP.elements_empty, app_nil_r. rewrite <-fst_NoDupMembers; eauto using NoDupMembers_app_r.
        - eapply unnest_node_init_st_valid; eauto.
      }
      inv Hgood2.
      constructor.
      + apply Forall_app in Hgood1 as (?&?).
        repeat rewrite map_app. repeat rewrite Forall_app. repeat split; eauto using AtomOrGensym_add.
        eapply st_valid_reuse_AtomOrGensym in Hvalid; auto; simpl.
        erewrite map_map, map_ext; [eauto|]. intros (?&?&?); auto.
      + eapply unnest_blocks_GoodLocals in H4; eauto.
        rewrite Forall_forall in *; eauto using GoodLocals_add.
  Qed.
  Next Obligation.
    specialize (n_syn n) as Hsyn. inv Hsyn.
    constructor.
    eapply unnest_blocks_nolocal; eauto using surjective_pairing.
  Qed.

  Fixpoint unnest_nodes enums nds :=
    match nds with
    | [] => []
    | hd::tl => (unnest_node (Global enums tl) hd) :: (unnest_nodes enums tl)
    end.

  Definition unnest_global G :=
    Global G.(enums) (unnest_nodes G.(enums) G.(nodes)).

  (** *** unnest_global produces an equivalent global *)

  Fact unnest_nodes_eq : forall enums nds,
      global_iface_eq (Global enums nds)
                      (Global enums (unnest_nodes enums nds)).
  Proof.
    induction nds; intros; simpl in *; auto.
    - apply global_iface_eq_nil.
    - apply global_iface_eq_cons; simpl; auto.
  Qed.

  Corollary unnest_global_eq : forall G,
      global_iface_eq G (unnest_global G).
  Proof.
    destruct G as (enums&nodes).
    apply unnest_nodes_eq.
  Qed.

  Fact unnest_nodes_names {PSyn prefs} : forall (nd: @node PSyn prefs) enums nds,
      Forall (fun n => (n_name nd <> n_name n)%type) nds ->
      Forall (fun n => (n_name nd <> n_name n)%type) (unnest_nodes enums nds).
  Proof.
    induction nds; intros * Hnames; simpl; auto.
    inv Hnames. constructor; simpl; auto.
  Qed.

  (** *** After normalization, a global is unnested *)

  Lemma iface_eq_unnested_equation {PSyn1 PSyn2 prefs1 prefs2} : forall (G: @global PSyn1 prefs1) (G': @global PSyn2 prefs2) eq,
      global_iface_eq G G' ->
      unnested_equation G eq ->
      unnested_equation G' eq.
  Proof.
    intros * Heq Hunt.
    inv Hunt; try constructor; eauto.
    destruct Heq as (_&Heq).
    specialize (Heq f).
    rewrite H0 in Heq. inv Heq. destruct H5 as (_&_&?&_).
    econstructor; eauto. congruence.
  Qed.

  Lemma iface_eq_unnested_block {PSyn1 PSyn2 prefs1 prefs2} : forall (G: @global PSyn1 prefs1) (G': @global PSyn2 prefs2) d,
      global_iface_eq G G' ->
      unnested_block G d ->
      unnested_block G' d.
  Proof.
    induction d using block_ind2; intros * Heq Hunt; inv Hunt.
    - constructor.
      eapply iface_eq_unnested_equation; eauto.
    - apply Forall_singl in H.
      constructor; auto.
  Qed.

  Corollary iface_eq_unnested_node {P1 P2 P3 p1 p2 p3} : forall (G: @global P1 p1) (G': @global P2 p2) (n: @node P3 p3),
      global_iface_eq G G' ->
      unnested_node G n ->
      unnested_node G' n.
  Proof.
    intros * Hglob Hunt. inv Hunt.
    econstructor; eauto.
    eapply Forall_impl; [|eauto]. intros.
    eapply iface_eq_unnested_block; eauto.
  Qed.

  Lemma unnest_node_unnested_node : forall G n,
      wl_node G n ->
      unnested_node G (unnest_node G n).
  Proof.
    intros * Hwl.
    unfold unnest_node; simpl.
    pose proof (n_syn n) as Hsyn. inv Hsyn.
    econstructor; simpl. rewrite <-H; eauto.
    eapply unnest_blocks_unnested_blocks; [|eauto|eapply surjective_pairing]; eauto.
    unfold wl_node in Hwl. rewrite <-H in Hwl; inv Hwl; auto.
  Qed.

  Lemma unnest_global_unnested_global : forall G,
      wl_global G ->
      unnested_global (unnest_global G).
  Proof.
    unfold unnest_global. destruct G as (enums&nodes).
    induction nodes; intros * Hwl; constructor; auto.
    - constructor; auto.
      + eapply iface_eq_unnested_node; simpl.
        * apply unnest_nodes_eq.
        * inv Hwl. destruct H1. eapply unnest_node_unnested_node; eauto.
      + simpl in *. eapply unnest_nodes_names.
        inv Hwl; destruct H1; auto.
    - inv Hwl. apply IHnodes; auto.
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

  Fact unnested_equation_not_nil {PSyn prefs} : forall (G: @global PSyn prefs) eq,
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
    repeat inv_bind;
    match goal with
    | |- incl (st_anns ?st1) (st_anns ?st2) =>
      eapply st_follows_incl
    | |- st_follows ?st ?st =>
      reflexivity
    | H : st_follows ?st1 ?st2 |- st_follows ?st1 _ =>
      etransitivity; [eapply H |]
    | H : fresh_ident _ _ _ ?st = _ |- st_follows ?st _ =>
      etransitivity; [ eapply fresh_ident_st_follows in H; eauto | ]
    | H : reuse_ident _ _ ?st = _ |- st_follows ?st _ =>
      etransitivity; [ eapply reuse_ident_st_follows in H; eauto | ]
    | H : idents_for_anns _ ?st = _ |- st_follows ?st _ =>
      etransitivity; [ eapply idents_for_anns_st_follows in H; eauto | ]
    | H : idents_for_anns' _ ?st = _ |- st_follows ?st _ =>
      etransitivity; [ eapply idents_for_anns'_st_follows in H; eauto | ]
    | H : unnest_noops_exps _ _ ?st = _ |- st_follows ?st _ =>
      etransitivity; [ eapply unnest_noops_exps_st_follows in H; eauto | ]
    | H : mmap2 _ _ ?st = _ |- st_follows ?st _ =>
      etransitivity; [ eapply mmap2_st_follows in H; eauto; solve_forall | ]
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
    | H: mmap _ _ ?st = _ |- st_follows ?st _ =>
      etransitivity; [ eapply mmap_st_follows in H; eauto; solve_forall |]
    | H : unnest_block _ _ ?st = _ |- st_follows ?st _ =>
      etransitivity; [ eapply unnest_block_st_follows in H; eauto |]
    | H : unnest_blocks _ _ ?st = _ |- st_follows ?st _ =>
      etransitivity; [ eapply unnest_blocks_st_follows in H; eauto |]
    | H : unnest_reset (unnest_exp _ _) _ ?st = _ |- st_follows ?st _ =>
      etransitivity; [ eapply unnest_reset_st_follows in H; eauto |]
    end.

  Fact mmap2_fresh_incl {B C} : forall (k : exp -> FreshAnn (B * C)) es es' eqs' st st',
      (forall e es' eqs' st st', k e st = (es', eqs', st') -> st_follows st st') ->
      Forall (fun e => forall es' eqs' st st',
                  k e st = (es', eqs', st') ->
                  incl (fresh_in e) (st_anns st')) es ->
      mmap2 k es st = (es', eqs', st') ->
      incl (fresh_ins es) (st_anns st').
  Proof with eauto.
    induction es; intros * Hk Hf Hmap;
      repeat inv_bind; try apply incl_nil'.
    inv Hf.
    apply incl_app; eauto.
    etransitivity; eauto.
    apply st_follows_incl; repeat solve_st_follows.
  Qed.

  Fact mmap2_fresh_incl' {B C} : forall (k : (enumtag * list exp) -> FreshAnn (B * C)) (es : list (enumtag * list exp)) es' eqs' st st' ,
      (forall e es' eqs' st st', k e st = (es', eqs', st') -> st_follows st st') ->
      Forall (fun es => forall es' eqs' st st',
                  k es st = (es', eqs', st') ->
                  incl (fresh_ins (snd es)) (st_anns st')) es ->
      mmap2 k es st = (es', eqs', st') ->
      incl (flat_map (fun es => fresh_ins (snd es)) es) (st_anns st').
  Proof with eauto.
    induction es; intros * Hk Hf Hmap;
      repeat inv_bind; try apply incl_nil'.
    inv Hf.
    apply incl_app; eauto.
    etransitivity; eauto.
    apply st_follows_incl; repeat solve_st_follows.
  Qed.

  (* Fact mmap2_fresh_incl'' {B C} : forall (k : option (list exp) -> FreshAnn (B * C)) es es' eqs' st st' , *)
  (*     (forall e es' eqs' st st', k e st = (es', eqs', st') -> st_follows st st') -> *)
  (*     Forall (LiftO *)
  (*               True (fun es => forall es' eqs' st st', *)
  (*                      k (Some es) st = (es', eqs', st') -> *)
  (*                      incl (fresh_ins es) (st_anns st'))) es -> *)
  (*     mmap2 k es st = (es', eqs', st') -> *)
  (*     incl (flat_map (or_default_with [] fresh_ins) es) (st_anns st'). *)
  (* Proof with eauto. *)
  (*   induction es; intros * Hk Hf Hmap; *)
  (*     repeat inv_bind; try apply incl_nil'. *)
  (*   inv Hf. *)
  (*   apply incl_app; eauto. *)
  (*   destruct a; simpl in *; repeat inv_bind; eauto using incl_nil'. *)
  (*   etransitivity; eauto. *)
  (*   eapply st_follows_incl; repeat solve_st_follows. *)
  (* Qed. *)

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
    - (* enum *) apply incl_nil'.
    - (* var *) apply incl_nil'.
    - (* binop *)
      apply incl_app; eauto.
      etransitivity...
    - (* fby *)
      repeat apply incl_app.
      + assert (st_follows x1 st') by repeat solve_st_follows.
        apply mmap2_fresh_incl in H1... 2:solve_forall.
        etransitivity...
      + assert (st_follows x4 st') by repeat solve_st_follows.
        apply mmap2_fresh_incl in H2... 2:solve_forall.
        etransitivity...
    - (* arrow *)
      repeat apply incl_app.
      + assert (st_follows x1 st') by repeat solve_st_follows.
        apply mmap2_fresh_incl in H1... 2:solve_forall.
        etransitivity...
      + assert (st_follows x4 st') by repeat solve_st_follows.
        apply mmap2_fresh_incl in H2... 2:solve_forall.
        etransitivity...
    - (* when *)
      destruct a; repeat inv_bind.
      apply mmap2_fresh_incl in H0... solve_forall.
    - (* merge *)
      destruct a; repeat inv_bind.
      assert (st_follows st x2) by repeat solve_st_follows.
      eapply mmap2_fresh_incl' in H0... 2:{ intros (?&?) ?????; repeat solve_st_follows. }
      2:{ solve_forall. repeat inv_bind. eapply mmap2_fresh_incl in H4...
          solve_forall. }
      etransitivity... eapply st_follows_incl. destruct is_control; repeat solve_st_follows.
    - (* case *)
      destruct a; repeat inv_bind.
      assert (st_follows x4 x7) by (destruct d; repeat solve_st_follows).
      assert (st_follows x1 x7).
      { repeat solve_st_follows; simpl in *; repeat solve_st_follows. }
      eapply IHe in H1.
      eapply mmap2_fresh_incl' in H2; simpl... 2:{ intros (?&?) ?????; repeat solve_st_follows. }
      2:{ solve_forall. repeat inv_bind. eapply mmap2_fresh_incl in H8...
          solve_forall. }
      repeat eapply incl_app; etransitivity...
      3:{ destruct d; repeat inv_bind. eapply mmap2_fresh_incl in H3; eauto. solve_forall.
          apply incl_nil'. }
      1-3:eapply st_follows_incl; destruct is_control; repeat inv_bind; repeat solve_st_follows.
    - (* app *)
      apply mmap2_fresh_incl in H1... 2:solve_forall.
      assert (st_follows x7 st') by repeat solve_st_follows.
      assert (st_follows x4 st') by repeat solve_st_follows.
      apply mmap2_fresh_incl in H3... 2:solve_forall; eapply unnest_reset_fresh_incl...
      repeat inv_bind; repeat eapply incl_app; simpl in *.
      3:eapply idents_for_anns'_fresh_incl...
      2:etransitivity; eauto.
      etransitivity; eauto; repeat solve_st_follows.
  Qed.

  Corollary mmap2_unnest_exp_fresh_incl : forall G es is_control es' eqs' st st',
      mmap2 (unnest_exp G is_control) es st = (es', eqs', st') ->
      incl (fresh_ins es) (st_anns st').
  Proof.
    intros * Hmap.
    apply mmap2_fresh_incl in Hmap; eauto.
    solve_forall. apply unnest_exp_fresh_incl in H0; auto.
  Qed.

  Corollary unnest_exps_fresh_incl : forall G es es' eqs' st st',
      unnest_exps G es st = (es', eqs', st') ->
      incl (fresh_ins es) (st_anns st').
  Proof.
    intros * Hnorm.
    unfold unnest_exps in Hnorm; repeat inv_bind.
    apply mmap2_unnest_exp_fresh_incl in H; auto.
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
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks : CLOCKS Ids Op OpAux)
       (Syn : LSYNTAX Ids Op OpAux Cks)
<: UNNESTING Ids Op OpAux Cks Syn.
  Include UNNESTING Ids Op OpAux Cks Syn.
End UnnestingFun.
