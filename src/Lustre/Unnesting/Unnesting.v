From Coq Require Import List Sorting.Permutation.
Import List.ListNotations.
Open Scope list_scope.

From Coq Require Import Setoid Morphisms.

From Velus Require Import Common Environment.
From Velus Require Import CommonTyping.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Lustre.StaticEnv.
From Velus Require Import Lustre.LSyntax.
From Velus Require Fresh.

(** * Normalization procedure *)

Module Type UNNESTING
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Import Cks : CLOCKS Ids Op OpAux)
       (Import Senv : STATICENV Ids Op OpAux Cks)
       (Import Syn : LSYNTAX Ids Op OpAux Cks Senv).

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
      (* Try to put hyp Foralls in the same form as conclusion *)
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
    end; destruct_conjs; eauto with norm.

  Ltac simpl_In :=
    CommonList.simpl_In;
    repeat
      match goal with
      | H : In (?x1, ?x2) (combine ?l1 ?l2) |- _ =>
          specialize (in_combine_l _ _ _ _ H) as ?; apply in_combine_r in H
      end.

  Global Hint Unfold typesof annots clocksof : list.

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

  Definition default_ann : ann := (OpAux.bool_velus_type, Cbase).

  (** Fresh ident generation keeping type annotations *)

  Definition st_senv {pref} (st: fresh_st pref _) := senv_of_tyck (st_anns st).
  Global Hint Unfold st_senv senv_of_tyck : list.

  Lemma st_senv_senv_of_decls {pref} : forall (st : fresh_st pref _),
      st_senv st = senv_of_decls (map (fun xtc => (fst xtc, ((fst (snd xtc)), snd (snd xtc), xH, None))) (st_anns st)).
  Proof.
    intros.
    unfold st_senv, senv_of_decls, senv_of_tyck.
    repeat rewrite map_map. eapply map_ext. intros; destruct_conjs; auto.
  Qed.

  Definition FreshAnn A := Fresh norm1 A (type * clock).

  Definition hd_default (l : list exp) : exp :=
    hd (Eenum 0 OpAux.bool_velus_type) l.

  Fixpoint idents_for_anns (anns : list ann) : FreshAnn (list (ident * ann)) :=
    match anns with
    | [] => ret []
    | (ty, cl)::tl => do x <- fresh_ident None (ty, cl);
                    do xs <- idents_for_anns tl;
                    ret ((x, (ty, cl))::xs)
    end.

  Fact idents_for_anns_values: forall anns ids st st',
      idents_for_anns anns st = (ids, st') ->
      map snd ids = anns.
  Proof.
    induction anns; intros idents st st' Hanns; repeat inv_bind; auto.
    destruct a as [ty cl]. repeat inv_bind.
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
  Global Hint Resolve idents_for_anns_length : norm.

  Fact idents_for_anns_st_anns: forall anns ids st st',
      idents_for_anns anns st = (ids, st') ->
      Permutation (st_anns st') (ids++st_anns st).
  Proof.
    induction anns as [|(?&?)]; intros * Hids; simpl in *; repeat inv_bind; auto.
    apply IHanns in H0.
    apply fresh_ident_anns in H; rewrite H in H0.
    rewrite H0. symmetry. apply Permutation_middle.
  Qed.

  Definition unnest_reset k (e : exp) : FreshAnn (exp * list equation) :=
      do (e', eqs1) <- k e;
      match hd_default e' with
      | Evar v ann => ret (Evar v ann, eqs1)
      | e => let '(ty, ck) := hd default_ann (annot e) in
            do x <- fresh_ident None (ty, ck);
            ret (Evar x (ty, ck), ([x], [e])::eqs1)
      end.

  Lemma unnest_reset_spec : forall k e es' eqs' st st',
      k e st = ((es', eqs'), st') ->
      (exists v, exists ann, (hd_default es') = Evar v ann /\ unnest_reset k e st = ((Evar v ann, eqs'), st'))
      \/ exists ty ck x st'', hd default_ann (annot (hd_default es')) = (ty, ck) /\
                        fresh_ident None (ty, ck) st' = (x, st'') /\
                        unnest_reset k e st = ((Evar x (ty, ck), ([x], [hd_default es'])::eqs'), st'').
  Proof.
    intros * Hk.
    unfold unnest_reset; simpl.
    destruct (hd_default es') eqn:Hes'.
    1-2,4-13:
      (right; destruct (hd _) as [ty ck] eqn:Hx; simpl;
       destruct (fresh_ident None (ty, ck) st') as [x st''] eqn:Hfresh;
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
                              eapply unnest_reset_spec in Hk as [[? [[? ?] [? Hnorm']]]|[? [? [? [? [Hhd [Hfresh Hnorm']]]]]]]; subst;
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

  Global Hint Unfold unnest_when unnest_merge unnest_case : norm.

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

  Definition find_node_incks (G: @global nolocal local_prefs) (f : ident) : list clock :=
    match find_node f G with
    | Some n => map (fun '(_, (_, ck, _)) => ck) (n_in n)
    | None => []
    end.

  Definition unnest_noops_exp (cki: clock) (e : exp) : FreshAnn (exp * list equation) :=
    let '(ty, ck) := hd default_ann (annot e) in
    if is_noops_exp cki e then ret (e, [])
    else do x <- fresh_ident None (ty, ck);
         ret (Evar x (ty, ck), [([x], [e])]).

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
    | Econst _ | Eenum _ _ | Evar _ _ | Elast _ _ => ret ([e], [])
    | Eunop op e1 ann =>
      do (e1', eqs) <- unnest_exp G false e1;
      ret ([Eunop op (hd_default e1') ann], eqs)
    | Ebinop op e1 e2 ann =>
      do (e1', eqs1) <- unnest_exp G false e1;
      do (e2', eqs2) <- unnest_exp G false e2;
      ret ([Ebinop op (hd_default e1') (hd_default e2') ann], eqs1++eqs2)
    | Eextcall f es (tyout, ck) =>
      do (es', eqs1) <- unnest_exps es;
      do x <- fresh_ident None (Tprimitive tyout, ck);
      ret ([Evar x (Tprimitive tyout, ck)], ([x], [Eextcall f es' (tyout, ck)])::eqs1)
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
      do xs <- idents_for_anns anns;
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
    | Eextcall f es ann =>
        do (es', eqs1) <- unnest_exps G es;
        ret ([Eextcall f es' ann], eqs1)
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

  (* Again, for node well-formedness, we need all the vs to be there *)
  Fixpoint combine_for_numstreams {B} (es : list exp) (vs : list B) :=
    match es, vs with
    | [], _ => List.map (fun v => (hd_default es, [v])) vs
    | _, [] => []
    | hd::tl, _ => let n := numstreams hd in
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
    | Blast x e =>
      do (e', eqs') <- unnest_exp G false e;
      ret (Blast x (hd_default e')::map Beq eqs')
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

  Lemma mk_equations_In' : forall v xs es,
      In v (mk_equations xs es) ->
      exists x e, v = ([x], [e]) /\ In x xs /\ (In e es \/ e = Eenum 0 OpAux.bool_velus_type).
  Proof.
    induction xs as [|x xs]; intros * Hin; simpl in *; inv Hin.
    - destruct es; simpl in *.
      1,2:do 2 esplit; split; eauto.
    - eapply IHxs in H as (?&?&?&In1&[In2|]); subst.
      + destruct es; simpl in *; [inv In2|].
        do 2 esplit; split; eauto.
      + do 2 esplit; split; eauto.
  Qed.

  Lemma mk_equations_Forall : forall P xs es,
      Forall2 (fun x e => P ([x], [e])) xs es ->
      Forall P (mk_equations xs es).
  Proof.
    intros * Hf.
    induction Hf; simpl; constructor; auto.
  Qed.

  (** ** Propagation of the st_follows property *)

  Fact idents_for_anns_st_follows : forall anns res st st',
      idents_for_anns anns st = (res, st') ->
      st_follows st st'.
  Proof.
    induction anns; intros res st st' Hidforanns;
      repeat inv_bind.
    - reflexivity.
    - destruct a as [ty cl]. repeat inv_bind.
      etransitivity; eauto with fresh.
  Qed.
  Global Hint Resolve idents_for_anns_st_follows : norm.

  Corollary idents_for_anns_incl : forall anns ids st st',
      idents_for_anns anns st = (ids, st') ->
      incl ids (st_anns st').
  Proof.
    induction anns; intros ids st st' Hids; simpl in Hids; repeat inv_bind;
      unfold incl; intros ? Hin; simpl in *; try destruct Hin.
    destruct a as [ty cl]. repeat inv_bind.
    inv Hin.
    - apply fresh_ident_In in H.
      apply idents_for_anns_st_follows in H0.
      apply st_follows_incl in H0; auto.
    - apply IHanns in H0; auto.
  Qed.

  Corollary idents_for_anns_incl_ids : forall anns ids st st',
      idents_for_anns anns st = (ids, st') ->
      incl (List.map fst ids) (st_ids st').
  Proof.
    intros.
    eapply idents_for_anns_incl in H.
    unfold st_ids in *.
    eapply incl_map with (f:=fst) in H.
    repeat rewrite map_map in H; simpl in H.
    replace (map (fun x => fst (let '(id, (ty, cl)) := x in (id, (ty, cl)))) ids) with (map fst ids) in H.
    2: { eapply map_ext. intros [? [? ?]]; auto. }
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
  Global Hint Resolve unnest_reset_st_follows' : norm.

  Lemma unnest_noops_exp_st_follows : forall e ck e' eqs' st st' ,
      unnest_noops_exp ck e st = (e', eqs', st') ->
      st_follows st st'.
  Proof.
    intros * Hun.
    unfold unnest_noops_exp in Hun.
    destruct (hd _ _) as (?&?).
    destruct (is_noops_exp _ _); repeat inv_bind; eauto with fresh.
    reflexivity.
  Qed.
  Global Hint Resolve unnest_noops_exp_st_follows : norm.

  Lemma unnest_noops_exps_st_follows : forall es ckis es' eqs' st st' ,
      unnest_noops_exps ckis es st = (es', eqs', st') ->
      st_follows st st'.
  Proof.
    intros * Hun. unfold unnest_noops_exps in Hun.
    repeat inv_bind.
    eapply mmap2_st_follows; eauto.
    eapply Forall_forall. intros (?&?) _ * Hun; eauto with norm.
  Qed.
  Global Hint Resolve unnest_noops_exps_st_follows : norm.

  Local Ltac solve_st_follows' :=
    match goal with
    | |- st_follows ?st ?st =>
      reflexivity
    | H : st_follows ?st1 ?st2 |- st_follows ?st1 _ =>
      etransitivity; [eapply H |]
    | H : fresh_ident _ _ ?st = _ |- st_follows ?st _ =>
      etransitivity; [ eapply fresh_ident_st_follows in H; eauto with norm | ]
    | H : idents_for_anns _ ?st = _ |- st_follows ?st _ =>
      etransitivity; [ eapply idents_for_anns_st_follows in H; eauto with norm | ]
    | H : unnest_reset _ _ ?st = _ |- st_follows ?st _ =>
      etransitivity; [ eapply unnest_reset_st_follows' in H; eauto with norm | ]
    | H : unnest_noops_exps _ _ ?st = _ |- st_follows ?st _ =>
      etransitivity; [ eapply unnest_noops_exps_st_follows in H; eauto with norm | ]
    | H : mmap2 _ _ ?st = _ |- st_follows ?st _ =>
      etransitivity; [ eapply mmap2_st_follows in H; eauto with norm; simpl_Forall; eauto with norm | ]
    end.

  Fact unnest_exp_st_follows : forall G e is_control res st st',
      unnest_exp G is_control e st = (res, st') ->
      st_follows st st'.
  Proof with eauto.
    induction e using exp_ind2; intros is_control res st st' Hnorm;
      simpl in Hnorm; destruct_conjs; repeat inv_bind; repeat solve_st_follows'; eauto.
    - (* binop *)
      etransitivity...
    - (* when *)
      repeat inv_bind. repeat solve_st_follows'.
    - (* merge *)
      destruct is_control; repeat inv_bind; repeat solve_st_follows'.
    - (* case *)
      destruct is_control; repeat inv_bind;
        (etransitivity; [ eapply IHe; eauto | repeat inv_bind; repeat solve_st_follows' ]).
      1-4:destruct d; repeat inv_bind; repeat solve_st_follows'.
  Qed.
  Global Hint Resolve unnest_exp_st_follows : norm.

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
    rewrite Forall_forall; intros; eauto with norm.
  Qed.

  Fact unnest_rhs_st_follows : forall G e res st st',
      unnest_rhs G e st = (res, st') ->
      st_follows st st'.
  Proof.
    intros * Hnorm.
    destruct e; try (solve [eapply unnest_exp_st_follows; eauto]);
      simpl in Hnorm; unfold unnest_exps in *.
    all:
      repeat inv_bind;
      repeat solve_st_follows'; eauto with norm.
  Qed.
  Global Hint Resolve unnest_rhs_st_follows : norm.

  Corollary unnest_rhss_st_follows : forall G es res st st',
      unnest_rhss G es st = (res, st') ->
      st_follows st st'.
  Proof.
    intros * Hnorm.
    unfold unnest_rhss in Hnorm; repeat inv_bind.
    repeat solve_st_follows'.
  Qed.
  Global Hint Resolve unnest_rhss_st_follows : norm.

  Fact unnest_equation_st_follows : forall G e res st st',
      unnest_equation G e st = (res, st') ->
      st_follows st st'.
  Proof.
    intros G [xs es] * Hnorm.
    simpl in *; repeat inv_bind; eauto with norm.
  Qed.
  Global Hint Resolve unnest_equation_st_follows : norm.

  Lemma unnest_block_st_follows : forall G bck res st st',
      unnest_block G bck st = (res, st') ->
      st_follows st st'.
  Proof.
    induction bck using block_ind2; intros * Hun;
      repeat inv_bind; eauto with norm; try reflexivity.
    - eapply mmap_st_follows in H0; eauto.
      eapply unnest_reset_st_follows' in H1; eauto with norm.
      etransitivity; eauto.
  Qed.
  Global Hint Resolve unnest_block_st_follows : norm.

  Corollary unnest_blocks_st_follows : forall G blocks res st st',
      unnest_blocks G blocks st = (res, st') ->
      st_follows st st'.
  Proof.
    intros * Hnorm.
    unfold unnest_blocks in Hnorm; repeat inv_bind.
    eapply mmap_st_follows; eauto.
    simpl_Forall; eauto with norm.
  Qed.

  (** ** Length of unnested expression *)

  Fact mmap2_unnest_exp_length' : forall G is_control es es' eqs' st st',
      Forall2 (fun e es' => forall eqs' st st',
                   unnest_exp G is_control e st = (es', eqs', st') ->
                   length es' = numstreams e) es es' ->
      mmap2 (unnest_exp G is_control) es st = (es', eqs', st') ->
      length (concat es') = length (annots es).
  Proof.
    intros * Hf Hmap.
    apply mmap2_values in Hmap.
    unfold annots. rewrite flat_map_concat_map.
    apply concat_length_eq.
    rewrite Forall2_map_2, Forall2_swap_args.
    eapply Forall3_ignore3, Forall2_Forall2 in Hmap; [| eapply Hf]. clear Hf.
    simpl_Forall. rewrite length_annot_numstreams; eauto.
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

  Fact unnest_exp_length : forall G e is_control es' eqs' st st',
      wl_exp G e ->
      unnest_exp G is_control e st = (es', eqs', st') ->
      length es' = numstreams e.
  Proof with eauto with norm datatypes.
    induction e using exp_ind2; intros is_control es' eqs' st st' Hwl Hnorm;
      destruct_conjs; inv Hwl; repeat inv_bind; auto.
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
      + eapply mmap2_values, Forall3_ignore3 in H0.
        simpl_Forall; eauto.
    - (* merge *)
      destruct is_control; repeat inv_bind.
      + apply unnest_merge_length.
      + apply idents_for_anns_length in H1. solve_length.
    - (* case *)
      destruct is_control; repeat inv_bind; unfold unnest_case.
      + apply unnest_case_length.
      + apply idents_for_anns_length in H4. solve_length.
    - (* app (reset) *)
      apply idents_for_anns_length in H4.
      solve_length.
  Qed.
  Global Hint Resolve unnest_exp_length : norm.

  Corollary mmap2_unnest_exp_length : forall G is_control es es' eqs' st st',
      Forall (wl_exp G) es ->
      mmap2 (unnest_exp G is_control) es st = (es', eqs', st') ->
      length (concat es') = length (annots es).
  Proof.
    intros * Hf Hmap.
    eapply mmap2_unnest_exp_length'; eauto.
    eapply mmap2_values, Forall3_ignore3 in Hmap.
    simpl_Forall.
    eapply unnest_exp_length; eauto with datatypes.
  Qed.
  Global Hint Resolve mmap2_unnest_exp_length : norm.

  Corollary mmap2_mmap2_unnest_exp_length {A} : forall G is_control (es : list (A * list exp)) es' eqs' st st',
    Forall (fun es => Forall (wl_exp G) (snd es)) es ->
    mmap2 (fun '(i, es0) => do (es', eqs') <- mmap2 (unnest_exp G is_control) es0;
                         ret (i, concat es', concat eqs')) es st = (es', eqs', st') ->
    Forall2 (fun es es' => length (snd es') = length (annots (snd es))) es es'.
  Proof.
    intros * Hwl Hmap.
    eapply mmap2_values in Hmap. eapply Forall3_ignore3 in Hmap.
    simpl_Forall. repeat inv_bind. eauto with norm datatypes.
  Qed.

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
  Global Hint Resolve unnest_exps_length : norm.

  Fact unnest_rhs_length : forall G e es' eqs' st st',
      wl_exp G e ->
      unnest_rhs G e st = (es', eqs', st') ->
      (length es' = 1 \/ length es' = numstreams e).
  Proof.
    intros * Hwt Hnorm;
      destruct e; unfold unnest_rhs in Hnorm;
        try (solve [right; eapply unnest_exp_length; eauto]);
        try (destruct o); repeat inv_bind; auto.
    1,2:right; inv Hwt;
      eapply unnest_exps_length in H; eauto.
    1,2:eapply unnest_exps_length in H0; eauto.
    eapply unnest_fby_length; eauto; congruence.
    eapply unnest_arrow_length; eauto; congruence.
  Qed.
  Global Hint Resolve unnest_rhs_length : norm.

  Fact unnest_exp_numstreams : forall G e is_control es' eqs' st st',
      unnest_exp G is_control e st = (es', eqs', st') ->
      Forall (fun e => numstreams e = 1) es'.
  Proof.
    intros * Hnorm.
    induction e; destruct_conjs; simpl in *; repeat inv_bind; repeat constructor.
    4,5:destruct is_control; repeat inv_bind.
    all:simpl_Forall; auto.
    all:(unfold unnest_when, unnest_merge, unnest_case in *; simpl_In; auto).
    - clear - H0. revert x H0.
      induction l0; intros; simpl; inv H0; eauto.
    - clear - H2. revert x2 x5 H2.
      induction l0; intros; simpl; inv H2; eauto.
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

  Fact idents_for_anns_annots : forall anns ids st st',
      idents_for_anns anns st = (ids, st') ->
      annots (map (fun '(x, a) => Evar x a) ids) = anns.
  Proof.
    intros.
    eapply idents_for_anns_values in H; subst.
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
      destruct p as (?&?).
      destruct (is_noops_exp _); repeat inv_bind; eauto.
  Qed.

  Fact unnest_exp_annot : forall G e is_control es' eqs' st st',
      wl_exp G e ->
      unnest_exp G is_control e st = (es', eqs', st')  ->
      annots es' = annot e.
  Proof with eauto.
    destruct e; intros * Hwl Hnorm;
      (* specialize (unnest_exp_length _ _ _ es' eqs' st st' Hwl Hnorm) as Hlength; *)
      inv Hwl; destruct_conjs; repeat inv_bind...
    - (* fby *) apply idents_for_anns_annots in H1...
    - (* arrow *) apply idents_for_anns_annots in H1...
    - (* when *)
      assert (length (concat x0) = length (annots l)) as Hlen by eauto with norm.
      unfold unnest_when, annots in *. rewrite flat_map_concat_map, map_map in *.
      rewrite H5 in Hlen.
      remember (concat x0) as l0.
      clear x0 H H2 H5 Heql0. revert l0 Hlen.
      induction tys; intros l0 Hlen; destruct l0; simpl in *; try congruence; auto.
    - (* merge *)
      destruct is_control; repeat inv_bind.
      + specialize (unnest_merge_annot (i, t) x tys nck) as Hf.
        clear - Hf. induction Hf; simpl; auto.
        rewrite H, IHHf; auto.
      + apply idents_for_anns_annots in H0...
    - (* case *)
      destruct is_control; repeat inv_bind.
      + specialize (unnest_case_annot (hd_default x) x2 tys x5 nck) as Hf.
        clear - Hf. induction Hf; simpl; auto.
        rewrite H, IHHf; auto.
      + apply idents_for_anns_annots in H2...
    - (* app *) apply idents_for_anns_annots in H2...
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
    apply Forall2_concat. simpl_Forall.
    rewrite <- H1, <- (concat_map_singl1 a) at 1.
    unfold annots; rewrite flat_map_concat_map.
    apply Forall2_concat. simpl_Forall.
    assert (In x (concat es')) as HIn by eauto using in_concat'. simpl_Forall.
    rewrite <- length_annot_numstreams in Hnumstreams. singleton_length.
    repeat constructor; auto.
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
    unfold annots. rewrite <-flat_map_app.
    f_equal; auto.
  Qed.

  Corollary mmap2_mmap2_unnest_exp_annots {A} : forall G is_control (es : list (A * _)) es' eqs' st st',
      Forall (fun es => Forall (wl_exp G) (snd es)) es ->
      mmap2 (fun '(i, es) => bind2 (mmap2 (unnest_exp G is_control) es) (fun es' eqs' => ret (i, concat es', concat eqs'))) es st = (es', eqs', st') ->
      Forall2 (fun es es' => annots (snd es') = annots (snd es)) es es'.
  Proof.
    intros * Hf Hmap.
    eapply mmap2_values, Forall3_ignore3 in Hmap.
    simpl_Forall. repeat inv_bind.
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

  Fact unnest_rhs_annot : forall G e es' eqs' st st',
      wl_exp G e ->
      unnest_rhs G e st = (es', eqs', st') ->
      annots es' = annot e.
  Proof.
    intros * Hwt Hnorm.
    destruct e; unfold unnest_rhs in Hnorm;
      try (solve [eapply unnest_exp_annot in Hnorm; eauto]).
    - (* extcall *)
      repeat inv_bind. inv Hwt. destruct_conjs; auto.
    - (* fby *)
      repeat inv_bind. inv Hwt.
      eapply unnest_fby_annot; eauto.
      eapply unnest_exps_length in H; eauto; congruence.
      eapply unnest_exps_length in H0; eauto; congruence.
    - (* arrow *)
      repeat inv_bind. inv Hwt.
      eapply unnest_arrow_annot; eauto.
      eapply unnest_exps_length in H; eauto; congruence.
      eapply unnest_exps_length in H0; eauto; congruence.
    - (* app *)
      repeat inv_bind; simpl; rewrite app_nil_r; reflexivity.
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
      unfold annots. rewrite <-flat_map_app.
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
    - destruct a as [ty cl]. repeat inv_bind.
      apply fresh_ident_vars_perm in H.
      apply IHanns in H0.
      etransitivity. 2: eapply H0.
      etransitivity. eapply Permutation_middle.
      apply Permutation_app_head. assumption.
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
      simpl. rewrite <-flat_map_app, <-app_assoc, Permutation_swap.
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
    destruct (hd _ _) as (?&?). destruct is_noops_exp; repeat inv_bind; eauto.
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
    destruct (hd _ _) as [ty ck]; repeat inv_bind.
    eapply Hkperm in Hk0.
    eapply fresh_ident_vars_perm in Hfresh; eauto.
    rewrite <- Hfresh, <- Hk0; auto.
  Qed.

  Fact unnest_exp_vars_perm : forall G e is_control es' eqs' st st',
      unnest_exp G is_control e st = ((es', eqs'), st') ->
      Permutation ((flat_map fst eqs')++(st_ids st)) (st_ids st').
  Proof with eauto.
    induction e using exp_ind2; intros is_control e' eqs' st st' Hnorm;
      simpl in Hnorm; destruct_conjs; repeat inv_bind...
    - (* binop *)
      rewrite <-flat_map_app, <-app_assoc.
      apply IHe1 in H...
      apply IHe2 in H0...
      etransitivity. 2:eauto.
      rewrite Permutation_swap.
      apply Permutation_app_head...
    - (* extcall *)
      apply fresh_ident_vars_perm in H1.
      apply mmap2_vars_perm in H0. 2:simpl_Forall; eauto.
      now rewrite <-H1, <-H0.
    - (* fby *)
      remember (unnest_fby _ _ _) as fby.
      apply mmap2_vars_perm in H1. 2:simpl_Forall; eauto.
      apply mmap2_vars_perm in H2. 2:simpl_Forall; eauto.
      apply idents_for_anns_vars_perm in H3.
      rewrite <- H3, <- H2, <- H1.
      rewrite ? flat_map_concat_map, ? map_app, ? concat_app. simpl_app.
      rewrite mk_equations_map_fst.
      eapply Permutation_app_head.
      rewrite Permutation_swap; auto.
    - (* arrow *)
      repeat inv_bind.
      remember (unnest_arrow _ _ _) as fby.
      apply mmap2_vars_perm in H1. 2:simpl_Forall; eauto.
      apply mmap2_vars_perm in H2. 2:simpl_Forall; eauto.
      apply idents_for_anns_vars_perm in H3.
      rewrite <- H3, <- H2, <- H1.
      rewrite ? flat_map_concat_map, ? map_app, ? concat_app. simpl_app.
      rewrite mk_equations_map_fst.
      eapply Permutation_app_head.
      rewrite Permutation_swap; auto.
    - (* when *)
      eapply mmap2_vars_perm...
      rewrite Forall_forall in *. intros...
    - (* merge *)
      apply mmap2_vars_perm in H0.
      2:{ simpl_Forall; repeat inv_bind.
          eapply mmap2_vars_perm in H3; eauto. simpl_Forall; eauto. }
      destruct is_control; repeat inv_bind; auto.
      rewrite ? flat_map_concat_map, ? map_app, ? concat_app in *. simpl_app.
      apply idents_for_anns_vars_perm in H1.
      etransitivity. 2: eauto.
      rewrite mk_equations_map_fst.
      repeat rewrite <- app_assoc. apply Permutation_app_head.
      etransitivity; eauto.
    - (* case *)
      apply IHe in H1; eauto.
      apply mmap2_vars_perm in H2.
      2:{ simpl_Forall; repeat inv_bind; simpl; auto.
          eapply mmap2_vars_perm in H6... simpl_Forall; eauto. }
      assert (Permutation (flat_map fst x6 ++ st_ids x4) (st_ids x7)) as Hperm3.
      { destruct d; repeat inv_bind; simpl in *; auto.
        eapply mmap2_vars_perm in H3... simpl_Forall; eauto. }
      destruct is_control; repeat inv_bind.
      + etransitivity...
        now rewrite <-2 flat_map_app, <-app_assoc, Permutation_swap, H1,
        <-app_assoc, Permutation_swap, H2.
      + rewrite ? flat_map_concat_map, ? map_app, ? concat_app in *. simpl_app.
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
      eapply idents_for_anns_vars_perm in H4.
      simpl; repeat inv_bind.
      apply mmap2_vars_perm in H1. 2:(simpl_Forall; eauto).
      apply unnest_noops_exps_vars_perm in H2.
      rewrite <- H4, <- H3, <- H2, <- H1; simpl.
      rewrite ? flat_map_concat_map, ? map_app, ? concat_app in *. simpl_app.
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
    eapply mmap2_vars_perm... simpl_Forall.
    eapply unnest_exp_vars_perm...
  Qed.

  Fact unnest_rhs_vars_perm : forall G e es' eqs' st st',
      unnest_rhs G e st = ((es', eqs'), st') ->
      Permutation ((flat_map fst eqs')++(st_ids st)) (st_ids st').
  Proof with eauto.
    intros * Hnorm.
    destruct e; unfold unnest_rhs in Hnorm;
      try (solve [eapply unnest_exp_vars_perm; eauto]).
    - (* extcall *)
      repeat inv_bind.
      eapply unnest_exps_vars_perm in H...
    - (* fby *)
      repeat inv_bind.
      eapply unnest_exps_vars_perm in H...
      eapply unnest_exps_vars_perm in H0...
      rewrite <- H0, <- H.
      rewrite ? flat_map_concat_map, ? map_app, ? concat_app in *. simpl_app.
      rewrite Permutation_swap...
    - (* arrow *)
      repeat inv_bind.
      eapply unnest_exps_vars_perm in H...
      eapply unnest_exps_vars_perm in H0...
      rewrite <- H0, <- H.
      rewrite ? flat_map_concat_map, ? map_app, ? concat_app in *. simpl_app.
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
    simpl_Forall.
    eapply unnest_rhs_vars_perm; eauto.
  Qed.

  Fact split_equation_fst : forall xs es,
      flat_map fst (split_equation (xs, es)) = xs.
  Proof.
    intros xs es; revert xs.
    induction es; intros xs; simpl in *.
    - induction xs; simpl; f_equal; auto.
    - destruct xs; simpl; auto.
      specialize (IHes (skipn (numstreams a) (i::xs))).
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
      rewrite <-flat_map_app.
      f_equal; auto.
  Qed.

  (** *** VarsDefined *)

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
    rewrite ? flat_map_concat_map in *. simpl in *. simpl_app.
    apply Permutation_app; auto.
    rewrite <- Hxl at 2. reflexivity.
  Qed.

  Fact mmap_vars_perm {A} pref : forall (f : block -> Fresh pref (list block) A) blks blks' xs st st',
      Forall
        (fun blk => forall blks' xs st st',
             VarsDefinedComp blk xs -> f blk st = (blks', st') ->
             exists ys, Forall2 VarsDefinedComp blks' ys /\ Permutation (concat ys ++ st_ids st) (xs ++ st_ids st')) blks ->
      Forall2 VarsDefinedComp blks xs ->
      mmap f blks st = (blks', st') ->
      exists ys, Forall2 VarsDefinedComp (concat blks') ys /\ Permutation (concat ys ++ st_ids st) (concat xs ++ st_ids st').
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
      VarsDefinedComp blk xs ->
      unnest_block G blk st = (blks', st') ->
      exists ys, Forall2 VarsDefinedComp blks' ys /\ Permutation (concat ys ++ st_ids st) (xs ++ st_ids st').
  Proof.
    induction blk using block_ind2; intros * Hvars Hun; inv Hvars; repeat inv_bind.
    - exists (map fst x). split.
      + simpl_Forall. constructor.
      + eapply unnest_equation_vars_perm in H. now rewrite flat_map_concat_map in H.
    - exists ([]::map fst x1). repeat constructor.
      + simpl_Forall. constructor.
      + simpl. apply unnest_exp_vars_perm in H. now rewrite flat_map_concat_map in H.
    - eapply unnest_reset_vars_perm in H1; eauto using unnest_exp_vars_perm.
      eapply mmap_vars_perm in H0 as (ys1&Hvars1&Hperm1); eauto.
      exists (ys1++map fst x2). split.
      + apply Forall2_app; simpl_Forall.
        * replace b with (concat [b]) by (simpl; now rewrite app_nil_r).
          repeat constructor; auto.
        * constructor.
      + rewrite <-H1, Permutation_swap, <-Hperm1, Permutation_swap.
        now rewrite concat_app, <-app_assoc, flat_map_concat_map.
    - exists [xs]. split; try constructor; auto.
      + econstructor; eauto.
      + simpl; rewrite app_nil_r; auto.
    - exists [xs]. split; try constructor; auto.
      + econstructor; eauto.
      + simpl; rewrite app_nil_r; auto.
    - exists [xs]. split; try constructor; auto.
      + econstructor; eauto.
      + simpl; rewrite app_nil_r; auto.
  Qed.

  Corollary unnest_blocks_vars_perm : forall G blks blks' xs st st',
      Forall2 VarsDefinedComp blks xs ->
      unnest_blocks G blks st = (blks', st') ->
      exists ys, Forall2 VarsDefinedComp blks' ys /\ Permutation (concat ys ++ st_ids st) (concat xs ++ st_ids st').
  Proof.
    intros * Hvars Hun. unfold unnest_blocks in Hun. repeat inv_bind.
    eapply mmap_vars_perm; [|eauto|eauto].
    simpl_Forall. eapply unnest_block_vars_perm; eauto.
  Qed.

  (** *** LastsDefined *)

  Fact mmap_lasts_perm {A} pref : forall (f : block -> Fresh pref (list block) A) blks blks' xs st st',
      Forall
        (fun blk => forall blks' xs st st',
             LastsDefined blk xs -> f blk st = (blks', st') ->
             exists ys, Forall2 LastsDefined blks' ys /\ Permutation (concat ys) xs) blks ->
      Forall2 LastsDefined blks xs ->
      mmap f blks st = (blks', st') ->
      exists ys, Forall2 LastsDefined (concat blks') ys /\ Permutation (concat ys) (concat xs).
  Proof.
    induction blks; intros * Hf Hvars Hnorm; inv Hf; inv Hvars; unfold unnest_blocks in Hnorm; repeat inv_bind; simpl.
    - exists []. split; auto.
    - eapply H1 in H as (ys1&Hvars1&Hperm1); eauto.
      eapply IHblks in H2 as (ys2&Hvars2&Hperm2); eauto. clear IHblks.
      exists (ys1 ++ ys2). split.
      + apply Forall2_app; auto.
      + rewrite concat_app, Hperm1, Hperm2; auto.
  Qed.

  Lemma unnest_block_lasts_perm : forall G blk blks' xs st st',
      LastsDefined blk xs ->
      unnest_block G blk st = (blks', st') ->
      exists ys, Forall2 LastsDefined blks' ys /\ Permutation (concat ys) (xs).
  Proof.
    induction blk using block_ind2; intros * Hvars Hun; inv Hvars; repeat inv_bind.
    - exists (map (fun _ => []) x). repeat constructor.
      + simpl_Forall. constructor.
      + rewrite concat_map_nil; auto.
    - exists ([x]::map (fun _ => []) x1). repeat constructor.
      + simpl_Forall. constructor.
      + now setoid_rewrite concat_map_nil.
    - eapply mmap_lasts_perm in H0 as (ys1&Hvars1&Hperm1); eauto.
      do 2 esplit. apply Forall2_app.
      + instantiate (1:=ys1). simpl_Forall.
        replace b with (concat [b]) by (simpl; now rewrite app_nil_r).
        repeat constructor; auto.
      + instantiate (1:=map (fun _ => []) x2). simpl_Forall. constructor.
      + now rewrite concat_app, concat_map_nil, app_nil_r.
    - exists [[]]. repeat constructor; auto.
    - exists [[]]. repeat constructor; auto.
    - exists [xs]. repeat (constructor; auto).
      simpl; rewrite app_nil_r; auto.
  Qed.

  Corollary unnest_blocks_lasts_perm : forall G blks blks' xs st st',
      Forall2 LastsDefined blks xs ->
      unnest_blocks G blks st = (blks', st') ->
      exists ys, Forall2 LastsDefined blks' ys /\ Permutation (concat ys) (concat xs).
  Proof.
    intros * Hvars Hun. unfold unnest_blocks in Hun. repeat inv_bind.
    eapply mmap_lasts_perm; [|eauto|eauto].
    simpl_Forall. eapply unnest_block_lasts_perm; eauto.
  Qed.

  (** ** Specification of an (almost) normalized node *)

  (* Intermediary predicate for unnested rhs *)
  Inductive unnested_rhs : exp -> Prop :=
  | unnested_rhs_Eapp : forall f es er lann,
      Forall normalized_lexp es ->
      Forall (fun e => exists x ann, e = Evar x ann) er ->
      unnested_rhs (Eapp f es er lann)
  | unnested_rhs_Efby : forall e0 e ann,
      normalized_lexp e0 ->
      normalized_lexp e ->
      unnested_rhs (Efby [e0] [e] [ann])
  | unnested_rhs_Earrow : forall e0 e ann,
      normalized_lexp e0 ->
      normalized_lexp e ->
      unnested_rhs (Earrow [e0] [e] [ann])
  | unnested_rhs_Eextcall : forall f es ann,
      Forall normalized_lexp es ->
      unnested_rhs (Eextcall f es ann)
  | unnested_rhs_cexp : forall e,
      normalized_cexp e ->
      unnested_rhs e.
  Global Hint Constructors unnested_rhs : norm.

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

  (** **er normalization, equations and expressions are unnested *)

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

  Fact mmap2_normalized_lexp' {A2} :
    forall (k : exp -> FreshAnn ((list exp) * A2)) a es' a2s st st',
      mmap2 k a st = (es', a2s, st') ->
      Forall (fun a => forall es' a2s st st',
                  k a st = (es', a2s, st') ->
                  Forall normalized_lexp es') a ->
      Forall normalized_lexp (concat es').
  Proof.
    intros * Hmap Hf.
    apply mmap2_values in Hmap.
    induction Hmap; simpl in *; inv Hf; auto.
    - destruct H as [? [? H]].
      rewrite Forall_app.
      split; eauto.
  Qed.

  Fact mmap2_normalized_cexp' {A2} :
    forall (k : exp -> FreshAnn (list exp * A2)) es es' a2s st st',
      mmap2 k es st = (es', a2s, st') ->
      Forall (fun e => forall es' a2s st st',
                  k e st = (es', a2s, st') ->
                  Forall normalized_cexp es') es ->
      Forall normalized_cexp (concat es').
  Proof.
    intros * Hmap Hf.
    apply mmap2_values in Hmap.
    induction Hmap; simpl in *; inv Hf; auto.
    - destruct H as [? [? H]].
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

  Local Hint Resolve in_combine_l in_combine_r : norm.
  Global Hint Resolve normalized_lexp_hd_default normalized_cexp_hd_default : norm.

  Lemma unnest_exp_normalized_lexp : forall G e es' eqs' st st',
      unnest_exp G false e st = (es', eqs', st') ->
      Forall normalized_lexp es'.
  Proof with eauto with norm.
    induction e using exp_ind2; intros * Hnorm; destruct_conjs;
      repeat inv_bind; repeat constructor...
    - (* fby *)
      simpl_Forall...
    - (* arrow *)
      simpl_Forall...
    - (* when *)
      unfold unnest_when.
      eapply mmap2_normalized_lexp' in H0...
      simpl_Forall. simpl_In. simpl_Forall...
    - (* merge *)
      unfold unnest_merge.
      simpl_Forall...
    - (* case *)
      unfold unnest_case.
      simpl_Forall...
    - (* app *)
      simpl_Forall...
  Qed.
  Global Hint Resolve unnest_exp_normalized_lexp : norm.

  Corollary mmap2_normalized_lexp : forall G es es' eqs' st st',
      mmap2 (unnest_exp G false) es st = (es', eqs', st') ->
      Forall normalized_lexp (concat es').
  Proof.
    intros * Hnorm.
    eapply mmap2_normalized_lexp' in Hnorm; eauto.
    simpl_Forall. eapply unnest_exp_normalized_lexp in H0; eauto. simpl_Forall; eauto.
  Qed.
  Global Hint Resolve mmap2_normalized_lexp : norm.

  Corollary unnest_exps_normalized_lexp: forall G es es' eqs' st st',
      unnest_exps G es st = (es', eqs', st') ->
      Forall normalized_lexp es'.
  Proof.
    intros * Hnorm.
    unfold unnest_exps in Hnorm. repeat inv_bind.
    eapply mmap2_normalized_lexp in H; eauto.
  Qed.
  Global Hint Resolve unnest_exps_normalized_lexp : norm.

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

  Lemma unnest_reset_unnested_eq : forall k e es' eqs' st st',
      (forall es' eqs' st st',
          k e st = (es', eqs', st') ->
          Forall unnested_rhs es' /\ Forall (unnested_equation []) eqs') ->
      unnest_reset k e st = (es', eqs', st') ->
      Forall (unnested_equation []) eqs'.
  Proof.
    intros * Hkunn Hnorm.
    unnest_reset_spec; auto.
    1,2:eapply Hkunn in Hk0 as (?&?); auto.
    constructor; auto.
    inv H; simpl; auto with norm.
    inv H1; eauto with norm.
  Qed.

  Corollary unnest_resets_unnested_eq : forall k es es' eqs' st st',
      Forall (fun e => forall es' eqs' st st',
                  k e st = (es', eqs', st') ->
                  Forall unnested_rhs es' /\ Forall (unnested_equation []) eqs') es ->
      mmap2 (unnest_reset k) es st = (es', eqs', st') ->
      Forall (unnested_equation []) (concat eqs').
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
      destruct a0; simpl in *; inv Hn; eauto with norm.
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
        destruct a0; simpl in *; inv Hn; eauto with norm.
      + intros ? Hopt. eapply option_map_inv in Hopt as (?&?&?); subst; simpl in *.
        inv H; eauto with norm.
    - eapply IHtys; eauto.
      + rewrite Forall_map.
        eapply Forall_impl; [|eauto]; intros * Hn.
        destruct a0; simpl in *; inv Hn; simpl; auto.
      + destruct d; inv H; simpl; auto.
  Qed.

  Lemma unnest_exp_normalized_cexp : forall G e es' eqs' st st',
      unnest_exp G true e st = (es', eqs', st') ->
      Forall normalized_cexp es'.
  Proof with eauto with norm.
    induction e using exp_ind2; intros * Hnorm; destruct_conjs;
      repeat inv_bind; repeat constructor...
    - (* fby *) simpl_Forall...
    - (* arrow *) simpl_Forall...
    - (* when *)
      unfold unnest_when.
      eapply mmap2_normalized_lexp in H0; eauto.
      simpl_Forall. simpl_In. simpl_Forall...
    - (* merge *)
      eapply unnest_merge_normalized_cexp...
      apply mmap2_normalized_cexp'' in H0; [|simpl_Forall].
      2:{ repeat inv_bind. eapply mmap2_normalized_cexp' in H2; simpl_Forall...
          eapply Forall_forall in H; eauto. }
      apply Forall_concat in H0; rewrite Forall_map in H0; auto.
    - (* case *)
      eapply unnest_case_normalized_cexp...
      + apply mmap2_normalized_cexp'' in H2; [|simpl_Forall]; eauto.
        { apply Forall_concat in H2; rewrite Forall_map in H2; auto. }
        repeat inv_bind; simpl; auto.
        eapply mmap2_normalized_cexp' in H5; eauto; simpl_Forall...
      + destruct d; repeat inv_bind; simpl in *; auto.
        eapply mmap2_normalized_cexp' in H3; eauto.
    - (* app *)
      simpl_Forall...
  Qed.
  Global Hint Resolve unnest_exp_normalized_cexp : norm.

  Corollary mmap2_normalized_cexp : forall G es es' eqs' st st',
      mmap2 (unnest_exp G true) es st = (es', eqs', st') ->
      Forall normalized_cexp (concat es').
  Proof.
    intros. eapply mmap2_normalized_cexp' in H; eauto.
    simpl_Forall. eapply unnest_exp_normalized_cexp in H1; eauto. simpl_Forall; eauto.
  Qed.

  Corollary mmap2_normalized_cexps : forall G (es : list (enumtag * list exp)) es' eqs' st st',
      mmap2 (fun '(i, es) => do (es', eqs') <- mmap2 (unnest_exp G true) es;
                          ret (i, concat es', concat eqs')) es st = (es', eqs', st') ->
      Forall (fun es => Forall normalized_cexp (snd es)) es'.
  Proof.
    intros * Hmap. apply mmap2_normalized_cexp'' in Hmap.
    - apply Forall_concat in Hmap; simpl_Forall; auto.
    - simpl_Forall; repeat inv_bind.
      eapply mmap2_normalized_cexp in H0; eauto. simpl_Forall; eauto.
  Qed.

  Fact mmap2_unnested_eq {A A1} :
    forall (k : A -> FreshAnn (A1 * (list equation))) a a1s eqs' st st',
      mmap2 k a st = (a1s, eqs', st') ->
      Forall (fun a => forall a1s eqs' st st',
                  k a st = (a1s, eqs', st') ->
                  Forall (unnested_equation []) eqs') a ->
      Forall (unnested_equation []) (concat eqs').
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

  Lemma unnest_noops_exp_normalized_exp : forall G es f es' es'' eqs' eqs'' st st' st'',
      (* Forall (wl_exp G) es -> *)
      (* length (annots es) = length (n_in n) -> *)
      mmap2 (unnest_exp G false) es st = (es', eqs', st') ->
      unnest_noops_exps (find_node_incks G f) (concat es') st' = (es'', eqs'', st'') ->
      Forall normalized_lexp es''(*  /\ *)
      (* Forall2 noops_exp (map (fun '(_, (_, ck, _)) => ck) (n_in n)) es'' *).
  Proof.
    intros * Hmap Hun.
    assert (Hnormed:=Hmap). eapply mmap2_normalized_lexp in Hnormed; eauto.
    unfold find_node_incks, unnest_noops_exps in Hun.
    cases; repeat inv_bind; [|constructor].
    remember (concat es') as es0. clear Heqes0.
    clear Hmap st eqs'.
    revert es0 st' st'' es'' x0 H Hnormed.
    induction (n_in n) as [|(?&(?&?)&?)]; intros * Hmap Hnormed; simpl in *; repeat inv_bind; auto.
    destruct es0; simpl in *; repeat inv_bind; inv Hnormed; constructor; eauto.
    unfold unnest_noops_exp in H.
    cases_eqn Eq; repeat inv_bind; auto with norm.
  Qed.

  Lemma unnest_noops_exp_unnested_eq : forall G es f es' es'' eqs' eqs'' st st' st'',
      (* Forall (wl_exp G) es -> *)
      (* length (annots es) = length (n_in n) -> *)
      mmap2 (unnest_exp G false) es st = (es', eqs', st') ->
      unnest_noops_exps (find_node_incks G f) (concat es') st' = (es'', eqs'', st'') ->
      Forall (unnested_equation []) eqs''.
  Proof.
    intros * Hmap Hun.
    assert (Hnormed:=Hmap). eapply mmap2_normalized_lexp in Hnormed; eauto.
    unfold find_node_incks, unnest_noops_exps in Hun.
    cases; repeat inv_bind; [|constructor].
    remember (concat es') as es0. clear Heqes0.
    clear Hmap st eqs'.
    revert es0 st' st'' es'' x0 H Hnormed.
    induction (n_in n); intros * Hmap Hnormed; simpl in *; repeat inv_bind; simpl; auto.
    destruct es0; simpl in *; repeat inv_bind; simpl. constructor.
    inv Hnormed; simpl. apply Forall_app; split; eauto.
    destruct a as (?&?&?). unfold unnest_noops_exp in H.
    destruct (hd _ _) as (?&?).
    destruct (is_noops_exp _ _) eqn:Hnoops; repeat inv_bind; auto with norm.
  Qed.

  Lemma unnest_exp_unnested_eq : forall G e is_control es' eqs' st st',
      unnest_exp G is_control e st = (es', eqs', st') ->
      Forall (unnested_equation []) eqs'.
  Proof with eauto with norm.
    induction e using exp_ind2; intros * Hnorm;
      repeat inv_bind; eauto.
    - (* binop *)
      apply Forall_app. split...
    - (* extcall *)
      destruct_conjs; repeat inv_bind.
      repeat constructor...
      eapply mmap2_unnested_eq; eauto. solve_forall.
    - (* fby *)
      repeat rewrite Forall_app; repeat split.
      2:eapply mmap2_unnested_eq in H1; eauto; solve_forall.
      2:eapply mmap2_unnested_eq in H2; eauto; solve_forall.
      eapply Forall_forall; intros ? Hin.
      eapply mk_equations_In' in Hin as (?&?&?&?&[Hfby|]); subst.
      2:{ repeat constructor. }
      unfold unnest_fby in Hfby; simpl_In.
      econstructor.
      eapply mmap2_normalized_lexp in H1; eauto. simpl_Forall...
      eapply mmap2_normalized_lexp in H2; eauto. simpl_Forall...
      intros [].
    - (* arrow *)
      repeat rewrite Forall_app; repeat split.
      2:eapply mmap2_unnested_eq in H1; eauto; solve_forall.
      2:eapply mmap2_unnested_eq in H2; eauto; solve_forall.
      eapply Forall_forall; intros ? Hin.
      eapply mk_equations_In' in Hin as (?&?&?&?&[Hfby|]); subst.
      2:{ repeat constructor. }
      unfold unnest_fby in Hfby; simpl_In.
      econstructor.
      eapply mmap2_normalized_lexp in H1; eauto. simpl_Forall...
      eapply mmap2_normalized_lexp in H2; eauto. simpl_Forall...
    - (* when *)
      destruct a. repeat inv_bind.
      eapply mmap2_unnested_eq in H0; eauto. solve_forall.
    - (* merge *)
      destruct a, is_control; repeat inv_bind;
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
      destruct a, is_control; repeat inv_bind; unfold unnest_case;
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
      eapply Forall_forall in Hcase; [|eapply unnest_case_normalized_cexp]; eauto with norm.
      + apply mmap2_normalized_cexp'' in H2; [|solve_forall]; eauto.
        apply Forall_concat in H2; rewrite Forall_map in H2; auto.
        repeat inv_bind; simpl; auto.
        eapply mmap2_normalized_cexp' in H8; eauto.
        solve_forall.
      + destruct d; repeat inv_bind; simpl; auto.
        eapply mmap2_normalized_cexp in H3; eauto.
    - (* app *)
      constructor. 2:repeat rewrite Forall_app; repeat split.
      + eapply unnest_resets_is_var in H3.
        eapply unnest_noops_exp_normalized_exp in H1; eauto.
        repeat constructor; auto. simpl_Forall; intros [].
      + eapply mmap2_unnested_eq in H1... solve_forall.
      + eapply unnest_noops_exp_unnested_eq in H1; eauto.
      + eapply unnest_resets_unnested_eq in H3...
        simpl_Forall.
        split; eauto.
        eapply unnest_exp_normalized_cexp in H6; eauto.
        simpl_Forall; eauto with norm.
  Qed.
  Global Hint Resolve unnest_exp_unnested_eq : norm.

  Corollary unnest_exps_unnested_eq : forall G es es' eqs' st st',
      unnest_exps G es st = (es', eqs', st') ->
      Forall (unnested_equation []) eqs'.
  Proof.
    intros * Hnorm.
    unfold unnest_exps in Hnorm. repeat inv_bind.
    eapply mmap2_unnested_eq in H; eauto.
    solve_forall.
  Qed.
  Global Hint Resolve unnest_exps_unnested_eq : norm.

  Fact unnest_rhs_unnested_rhs : forall G e es' eqs' st st',
      unnest_rhs G e st = (es', eqs', st') ->
      Forall unnested_rhs es'.
  Proof with eauto with norm.
    intros * Hnorm.
    destruct e; unfold unnest_rhs in Hnorm;
      try (eapply unnest_exp_normalized_cexp in Hnorm; solve_forall; auto).
    - (* extcall *)
      repeat inv_bind. repeat constructor; eauto.
      eapply unnest_exps_normalized_lexp in H; eauto.
    - (* fby *)
      repeat inv_bind.
      eapply unnest_exps_normalized_lexp in H; eauto.
      eapply unnest_exps_normalized_lexp in H0; eauto.
      unfold unnest_fby.
      apply Forall_forall; intros * Hin.
      simpl_In.
      constructor; eauto.
      + eapply Forall_forall in H; eauto.
      + eapply Forall_forall in H0; eauto.
    - (* arrow *)
     repeat inv_bind.
     eapply unnest_exps_normalized_lexp in H; eauto.
     eapply unnest_exps_normalized_lexp in H0; eauto.
     unfold unnest_arrow.
     simpl_Forall.
     simpl_In.
     constructor; eauto.
     + eapply Forall_forall in H; eauto.
     + eapply Forall_forall in H0; eauto.
    - (* app *)
      repeat inv_bind...
      assert (Hr:=H1). eapply unnest_resets_is_var in H1.
      constructor; [|constructor].
      simpl in Hr. repeat inv_bind.
      unfold unnest_exps in H; repeat inv_bind.
      econstructor; eauto.
      eapply unnest_noops_exp_normalized_exp with (es:=l)...
  Qed.

  Corollary unnest_rhss_unnested_rhs : forall G es es' eqs' st st',
      unnest_rhss G es st = (es', eqs', st') ->
      Forall unnested_rhs es'.
  Proof with eauto.
    intros * Hnorm.
    unfold unnest_rhss in Hnorm. repeat inv_bind.
    eapply mmap2_values in H.
    induction H; simpl; try constructor.
    apply Forall_app. split; auto.
    destruct H as [? [? H]].
    eapply unnest_rhs_unnested_rhs; eauto.
  Qed.

  Fact unnest_rhs_unnested_eq : forall G e es' eqs' st st',
      unnest_rhs G e st = (es', eqs', st') ->
      Forall (unnested_equation []) eqs'.
  Proof with eauto.
    intros * Hnorm.
    destruct e; unfold unnest_rhs in Hnorm;
      try (eapply unnest_exp_unnested_eq in Hnorm; eauto).
    - (* extcall *)
      repeat inv_bind.
      eapply unnest_exps_unnested_eq; eauto.
    - (* fby *)
      repeat inv_bind.
      repeat rewrite Forall_app; repeat split...
      1,2:eapply unnest_exps_unnested_eq; eauto.
    - (* arrow *)
      repeat inv_bind.
      repeat rewrite Forall_app; repeat split...
      1,2:eapply unnest_exps_unnested_eq; eauto.
    - (* app *)
      repeat inv_bind...
      eapply unnest_resets_unnested_eq in H1.
      2:{ simpl_Forall.
          split; eauto with norm.
          eapply unnest_exp_normalized_cexp in H3; eauto. simpl_Forall; eauto with norm. }
      repeat rewrite Forall_app; repeat split; auto.
      eapply unnest_exps_unnested_eq in H; eauto.
      unfold unnest_exps in H; repeat inv_bind.
      eapply unnest_noops_exp_unnested_eq with (es:=l) in H0; eauto.
  Qed.
  Global Hint Resolve unnest_rhs_unnested_eq : norm.

  Corollary unnest_rhss_unnested_eq : forall G es es' eqs' st st',
      unnest_rhss G es st = (es', eqs', st') ->
      Forall (unnested_equation []) eqs'.
  Proof.
    intros * Hnorm.
    unfold unnest_rhss in Hnorm; repeat inv_bind.
    eapply mmap2_unnested_eq in H; eauto.
    rewrite Forall_forall in *; intros; eauto with norm.
  Qed.
  Global Hint Resolve unnest_rhss_unnested_eq : norm.

  Lemma unnest_equation_unnested_eq : forall G eq eqs' st st',
      unnest_equation G eq st = (eqs', st') ->
      Forall (unnested_equation []) eqs'.
  Proof with eauto with norm.
    intros ? [xs es] * Hnorm.
    unfold unnest_equation in Hnorm.
    repeat inv_bind.
    rewrite Forall_app. split.
    - eapply unnest_rhss_unnested_rhs in H; eauto.
      revert xs.
      induction H; intros xs; simpl in *.
      + simpl_Forall. repeat constructor.
      + destruct xs; simpl in *; auto.
        constructor; auto.
        inv H...
        1-3:destruct_conjs; destruct xs; simpl in *; try lia; constructor...
        3:constructor; auto. 1,2:simpl_Forall; intros [].
        specialize (normalized_cexp_numstreams _ H1) as Hlen'.
        rewrite Hlen' in *. simpl...
    - eapply unnest_rhss_unnested_eq in H; eauto.
  Qed.

  Lemma unnest_block_unnested_block : forall G blk blks' st st',
      nolocal_block blk ->
      unnest_block G blk st = (blks', st') ->
      Forall unnested_block blks'.
  Proof.
    induction blk using block_ind2; intros * Hnloc Hun; inv Hnloc; repeat inv_bind.
    - eapply unnest_equation_unnested_eq in H; eauto.
      rewrite Forall_map. rewrite Forall_forall in *; auto with norm.
    - repeat constructor; eauto with norm.
      eapply unnest_exp_unnested_eq in H; eauto.
      simpl_Forall. constructor; auto.
    - apply Forall_app. split.
      + eapply unnest_reset_is_var in H2 as (xr&ann&?); subst.
        apply mmap_values, Forall2_ignore1 in H0.
        eapply Forall_map, Forall_concat. simpl_Forall.
        constructor; eauto. eapply H in H3; eauto. simpl_Forall; auto.
      + eapply unnest_reset_unnested_eq in H2.
        2:{ intros; split; eauto with norm.
            eapply unnest_exp_normalized_cexp in H3; eauto.
            simpl_Forall; eauto with norm. }
        simpl_Forall; eauto with norm.
  Qed.

  Corollary unnest_blocks_unnested_blocks : forall G blks blks' st st',
      Forall nolocal_block blks ->
      unnest_blocks G blks st = (blks', st') ->
      Forall unnested_block blks'.
  Proof.
    induction blks; intros * Hnloc Hnorm;
      unfold unnest_blocks in Hnorm; repeat inv_bind; simpl; auto.
    inv Hnloc. apply Forall_app; split.
    - eapply unnest_block_unnested_block; eauto.
    - eapply IHblks; eauto.
      unfold unnest_blocks; repeat inv_bind; repeat eexists; eauto.
  Qed.

  (** *** GoodLocals *)

  Lemma unnest_block_GoodLocals G : forall prefs blk blk' st st',
      GoodLocals prefs blk ->
      unnest_block G blk st = (blk', st') ->
      Forall (GoodLocals prefs) blk'.
  Proof.
    induction blk using block_ind2; intros * Hgood Hun; inv Hgood; repeat inv_bind.
    - (* equation *)
      simpl_Forall. constructor.
    - (* last *)
      repeat constructor. simpl_Forall. constructor.
    - (* reset *)
      apply Forall_app; split.
      + assert (Forall (GoodLocals prefs) (concat x)) as Hgood.
        { eapply mmap_values, Forall2_ignore1 in H0.
          eapply Forall_concat. rewrite Forall_forall in *; intros.
          specialize (H0 _ H3) as (?&Hinblk&?&?&Hun).
          eapply H; eauto. }
        simpl_Forall. constructor. simpl_Forall.
      + simpl_Forall. constructor.
    - do 2 (constructor; auto).
    - do 2 (constructor; auto).
    - do 2 (constructor; auto).
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

  Fact mmap_NoDupLocals {pref A} (f : block -> Fresh pref (list block) A) env : forall blks blks' st st',
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
      inv Hnd. simpl_Forall. constructor.
    - (* last *)
      repeat constructor. simpl_Forall. constructor.
    - (* reset *)
      inv Hnd.
      eapply Forall_app; split; rewrite Forall_map.
      + eapply mmap_NoDupLocals in H; eauto.
        simpl_Forall. constructor. simpl_Forall.
      + simpl_Forall. constructor.
    - constructor; auto.
    - constructor; auto.
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

  (** ** Normalization of a full node *)

  Import Facts Tactics.

  Lemma norm1_not_in_local_prefs :
    ~PS.In norm1 local_prefs.
  Proof.
    unfold local_prefs, switch_prefs, auto_prefs, last_prefs, elab_prefs.
    rewrite ? PSF.add_iff, PSF.singleton_iff.
    pose proof gensym_prefs_NoDup as Hnd. unfold gensym_prefs in Hnd.
    repeat rewrite NoDup_cons_iff in Hnd. destruct_conjs.
    intros Eq. repeat take (_ \/ _) and destruct it as [Eq|Eq]; eauto 6 with datatypes.
  Qed.

  Program Definition unnest_node G (n : @node nolocal local_prefs) : @node unnested norm1_prefs :=
    {| n_name := (n_name n);
       n_hasstate := (n_hasstate n);
       n_in := (n_in n);
       n_out := (n_out n);
       n_block := match (n_block n) with
                  | Blocal (Scope vars blks) =>
                    let res := unnest_blocks G blks init_st in
                    let nvars := st_anns (snd res) in
                    Blocal (Scope (vars++map (fun xtc => (fst xtc, ((fst (snd xtc)), snd (snd xtc), xH, None))) nvars) (fst res))
                  | blk => blk
                  end;
       n_ingt0 := (n_ingt0 n);
       n_outgt0 := (n_outgt0 n);
    |}.
  Next Obligation.
    pose proof (n_syn n) as Syn. inversion_clear Syn as [?? Syn2 (?&Hvars&Hperm)].
    inv Syn2. rewrite <-H in *. inv Hvars. repeat inv_scope.
    destruct (unnest_blocks _ _) as (blks'&st') eqn:Heqs.
    do 2 esplit; [|eauto].
    eapply noswitch_VarsDefinedComp_VarsDefined.
    1:{ constructor.
        eapply unnest_blocks_unnested_blocks in Heqs; eauto.
        simpl_Forall; auto using unnested_nolocal, nolocal_noswitch. }
    eapply unnest_blocks_vars_perm in Heqs as (ys&Hvars&Hperm'); eauto.
    constructor. econstructor; eauto using incl_nil'.
    unfold st_ids in *. rewrite init_st_anns, app_nil_r in Hperm'. simpl.
    do 2 esplit; eauto. rewrite Hperm', H2, Hperm, map_app, <-app_assoc, map_fst_senv_of_decls.
    apply Permutation_app_head, Permutation_app_head.
    rewrite map_map; reflexivity.
  Qed.
  Next Obligation.
    pose proof (n_lastd n) as (?&Last&Perm).
    pose proof (n_syn n) as Hsyn. inversion_clear Hsyn as [?? Hsyn2 _]. inv Hsyn2. simpl. rewrite <-H in *.
    destruct (unnest_blocks G blks init_st) as (blks'&st') eqn:Hunn.
    inv Last. inv_scope.
    eapply unnest_blocks_lasts_perm in Hunn as (?&Lasts'&Perm'); eauto.
    do 2 esplit; eauto.
    repeat constructor. do 2 esplit; eauto.
    rewrite Perm', H2.
    unfold lasts_of_decls. rewrite map_filter_app, map_filter_nil with (xs:=map _ _), app_nil_r; auto.
    simpl_Forall; auto.
  Qed.
  Next Obligation.
    pose proof (n_good n) as (Hat&Hgood&_).
    pose proof (n_nodup n) as (Hndup&Hndl).
    pose proof (n_syn n) as Hsyn. inversion_clear Hsyn as [?? Hsyn2 _]. inv Hsyn2. simpl. rewrite <-H in *.
    destruct (unnest_blocks G blks init_st) as (blks'&st') eqn:Hunn.
    repeat erewrite unnest_blocks_no_anon; eauto. repeat rewrite app_nil_r.
    split; eauto using NoDupMembers_app_l.
    inv Hndl. inv H3.
    constructor; constructor; simpl.
    - eapply unnest_blocks_NoDupLocals; [|eauto].
      inv Hgood. inv H2.
      rewrite Forall_forall in *. intros.
      rewrite (map_app _ locs), map_map; simpl.
      eapply NoDupLocals_incl' with (npref:=norm1). 1,2,4:eauto using norm1_not_in_local_prefs.
      intros ? Hin. rewrite app_assoc, in_app_iff in Hin. destruct Hin as [?|Hin]; auto.
      specialize (st_valid_prefixed st') as Hvalid. simpl_Forall; subst; eauto.
    - apply NoDupMembers_app; auto.
      + specialize (st_valid_NoDup st') as Hnd'. unfold st_ids in Hnd'.
        erewrite fst_NoDupMembers, map_map, map_ext; eauto.
      + intros * Hinm1 Hinm2. rewrite fst_InMembers in Hinm1, Hinm2. simpl_In.
        inv Hgood. take (GoodLocalsScope _ _ _) and inv it. simpl_Forall; subst.
        eapply st_valid_AtomOrGensym_nIn; eauto using norm1_not_in_local_prefs.
        unfold st_ids. solve_In.
    - setoid_rewrite InMembers_app. intros * [Hinm|Hinm] Hin'.
      + eapply H7; eauto using in_or_app.
      + simpl_Forall. rewrite fst_InMembers in Hinm. simpl_In.
        eapply st_valid_AtomOrGensym_nIn; eauto using norm1_not_in_local_prefs.
        unfold st_ids. solve_In.
  Qed.
  Next Obligation.
    specialize (n_nodup n) as (Hndup&Hndl).
    specialize (n_good n) as (Hgood1&Hgood2&Hname).
    pose proof (n_syn n) as Hsyn. inversion_clear Hsyn as [?? Hsyn2 _]. inv Hsyn2. simpl. rewrite <-H in *.
    destruct (unnest_blocks G blks init_st) as (blks'&st') eqn:Hunn.
    repeat split; eauto using Forall_AtomOrGensym_add.
    inv Hgood2. inv H2.
    constructor. constructor.
    + repeat rewrite map_app. repeat rewrite Forall_app. repeat split; eauto using Forall_AtomOrGensym_add.
      specialize (st_valid_prefixed st') as Hvalid.
      erewrite map_map, map_ext; [eauto|]. eapply Forall_impl; [|eapply Hvalid]; intros ? (?&?&?); simpl in *; subst; eauto.
      right. do 2 esplit; eauto. apply PSF.add_1; auto.
      intros (?&?&?); auto.
    + eapply unnest_blocks_GoodLocals in H5; eauto.
      rewrite Forall_forall in *; eauto using GoodLocals_add.
  Qed.
  Next Obligation.
    pose proof (n_syn n) as Hsyn. inversion_clear Hsyn as [?? Hsyn2 (?&Hvars&Hperm)]. inv Hsyn2.
    rewrite <-H in *. inv Hvars. inv_scope.
    repeat constructor; auto.
    - eapply unnest_blocks_unnested_blocks; eauto using surjective_pairing.
    - do 2 esplit; eauto.
      destruct (unnest_blocks _ _) as (blks'&st') eqn:Heqs.
      eapply unnest_blocks_vars_perm in Heqs as (ys&Hvars'&Hperm'); eauto.
      constructor. econstructor; eauto using incl_nil'.
      unfold st_ids in *. rewrite init_st_anns, app_nil_r in Hperm'. simpl.
      do 2 esplit; eauto. rewrite Hperm', H2, map_app, <-app_assoc.
      apply Permutation_app_head, Permutation_app_head.
      rewrite map_map; reflexivity.
  Qed.

  Fixpoint unnest_nodes enums externs nds :=
    match nds with
    | [] => []
    | hd::tl => (unnest_node (Global enums externs tl) hd) :: (unnest_nodes enums externs tl)
    end.

  Definition unnest_global G :=
    Global G.(types) G.(externs) (unnest_nodes G.(types) G.(externs) G.(nodes)).

  (** *** unnest_global produces an equivalent global *)

  Fact unnest_nodes_eq : forall enums externs nds,
      global_iface_eq (Global enums externs nds)
                      (Global enums externs (unnest_nodes enums externs nds)).
  Proof.
    induction nds; intros; simpl in *; auto.
    - apply global_iface_eq_nil.
    - apply global_iface_eq_cons; simpl; auto.
  Qed.

  Corollary unnest_global_eq : forall G,
      global_iface_eq G (unnest_global G).
  Proof.
    destruct G.
    apply unnest_nodes_eq.
  Qed.

  Fact unnest_nodes_names {PSyn prefs} : forall (nd: @node PSyn prefs) enums externs nds,
      Forall (fun n => (n_name nd <> n_name n)%type) nds ->
      Forall (fun n => (n_name nd <> n_name n)%type) (unnest_nodes enums externs nds).
  Proof.
    induction nds; intros * Hnames; simpl; auto.
    inv Hnames. constructor; simpl; auto.
  Qed.

  (** *** after unnesting, a global has normalized arguments *)

  Local Ltac mmap_normal_args_eq :=
    match goal with
    | |- Forall _ (concat _) => apply Forall_concat
    | H: In _ (concat _) |- _ => apply List.in_concat in H as (?&?&?)
    | H:mmap2 _ _ _ = _ |- _ =>
        eapply mmap2_values, Forall3_ignore12 in H; simpl_Forall; repeat inv_bind
    | H:In ?x _ |- _ ?x => eapply Forall_forall in H; eauto
    end.

  Lemma unnest_noops_exp_noops_exp : forall G es f n es' es'' eqs' eqs'' st st' st'',
      Forall (wl_exp G) es ->
      length (annots es) = length (n_in n) ->
      find_node f G = Some n ->
      mmap2 (unnest_exp G false) es st = (es', eqs', st') ->
      unnest_noops_exps (find_node_incks G f) (concat es') st' = (es'', eqs'', st'') ->
      Forall2 noops_exp (map (fun '(_, (_, ck, _)) => ck) (n_in n)) es''.
  Proof.
    intros * Hwl Hlen Hfind Hmap Hun.
    assert (Hnormed:=Hmap). eapply mmap2_normalized_lexp in Hnormed; eauto.
    apply mmap2_unnest_exp_length in Hmap; eauto. rewrite <-Hmap in Hlen.
    unfold find_node_incks, unnest_noops_exps in Hun. rewrite Hfind in Hun.
    repeat inv_bind.
    remember (concat es') as es0. clear Heqes0.
    clear Hfind Hmap st eqs'.
    revert es0 st' st'' es'' x0 H Hnormed Hlen.
    induction (n_in n) as [|(?&(?&?)&?)]; intros * Hmap Hnormed Hlen; simpl in *; repeat inv_bind; auto.
    destruct es0; simpl in *; repeat inv_bind. congruence.
    inv Hlen. inv Hnormed. constructor; eauto.
    unfold unnest_noops_exp in H.
    destruct (hd _ _) as (?&?).
    destruct (is_noops_exp _ _) eqn:Hnoops; repeat inv_bind.
    - eapply is_noops_exp_spec in Hnoops; eauto.
    - destruct c; constructor.
  Qed.

  Lemma unnest_reset_normal_args {PSyn prefs} (G: @global PSyn prefs) : forall k e es' eqs' st st',
      (forall es' eqs' st st',
          k e st = (es', eqs', st') ->
          Forall normalized_cexp es' /\ Forall (normal_args_eq G) eqs') ->
      unnest_reset k e st = (es', eqs', st') ->
      Forall (normal_args_eq G) eqs'.
  Proof.
    intros * Hkunn Hnorm.
    unnest_reset_spec; auto.
    1,2:eapply Hkunn in Hk0 as (?&?); auto.
    constructor; auto.
    inv H; simpl; repeat (constructor; auto).
  Qed.

  Corollary unnest_resets_normal_args {PSyn prefs} (G: @global PSyn prefs) : forall k es es' eqs' st st',
      Forall (fun e => forall es' eqs' st st',
                  k e st = (es', eqs', st') ->
                  Forall normalized_cexp es' /\ Forall (normal_args_eq G) eqs') es ->
      mmap2 (unnest_reset k) es st = (es', eqs', st') ->
      Forall (normal_args_eq G) (concat eqs').
  Proof.
    intros * Hkunn Hnorm.
    eapply mmap2_values, Forall3_ignore2, Forall2_ignore1 in Hnorm.
    eapply Forall_concat. simpl_Forall.
    eapply unnest_reset_normal_args in H1; eauto. now simpl_Forall.
  Qed.

  Lemma unnest_noops_exp_normal_args : forall G es f es' es'' eqs' eqs'' st st' st'',
      mmap2 (unnest_exp G false) es st = (es', eqs', st') ->
      unnest_noops_exps (find_node_incks G f) (concat es') st' = (es'', eqs'', st'') ->
      Forall (normal_args_eq G) eqs''.
  Proof.
    intros * Hmap Hun.
    assert (Hnormed:=Hmap). eapply mmap2_normalized_lexp in Hnormed; eauto.
    unfold find_node_incks, unnest_noops_exps in Hun.
    cases; repeat inv_bind; [|constructor].
    remember (concat es') as es0. clear Heqes0.
    clear Hmap st eqs'.
    revert es0 st' st'' es'' x0 H Hnormed.
    induction (n_in n); intros * Hmap Hnormed; simpl in *; repeat inv_bind; simpl; auto.
    destruct es0; simpl in *; repeat inv_bind; simpl. constructor.
    inv Hnormed; simpl. apply Forall_app; split; eauto.
    destruct a as (?&(?&?)&?). unfold unnest_noops_exp in H.
    destruct (hd _ _) as (?&?).
    destruct (is_noops_exp _ _) eqn:Hnoops; repeat inv_bind; auto with norm.
    repeat (constructor; auto).
  Qed.

  Lemma unnest_exp_normal_args : forall G e is_control es' eqs' st st',
      wl_exp G e ->
      unnest_exp G is_control e st = (es', eqs', st') ->
      Forall (normal_args_eq G) eqs'.
  Proof with eauto with norm.
    induction e using exp_ind2; intros * Wl Hnorm; inv Wl;
      repeat inv_bind; eauto.
    - (* binop *)
      apply Forall_app. split...
    - (* extcall *)
      destruct_conjs; repeat inv_bind.
      repeat constructor...
      repeat mmap_normal_args_eq.
    - (* fby *)
      repeat rewrite Forall_app; repeat split.
      2,3:repeat mmap_normal_args_eq.
      eapply Forall_forall; intros ? Hin.
      eapply mk_equations_In' in Hin as (?&?&?&?&[Hfby|]); subst.
      2:{ repeat constructor. }
      unfold unnest_fby in Hfby; simpl_In.
      econstructor.
    - (* arrow *)
      repeat rewrite Forall_app; repeat split.
      2,3:repeat mmap_normal_args_eq.
      eapply Forall_forall; intros ? Hin.
      eapply mk_equations_In' in Hin as (?&?&?&?&[Hfby|]); subst.
      2:{ repeat constructor. }
      unfold unnest_fby in Hfby; simpl_In.
      econstructor.
    - (* when *)
      repeat mmap_normal_args_eq.
    - (* merge *)
      destruct is_control; repeat inv_bind;
        repeat rewrite Forall_app; repeat split.
      1,3:repeat mmap_normal_args_eq.
      rewrite Forall_forall; intros ? Hin.
      eapply mk_equations_In in Hin as (?&?&?&?&Hmerge); subst.
      2:{ apply idents_for_anns_length in H1. rewrite map_length in H1.
          rewrite unnest_merge_length, map_length... }
      econstructor; eauto.
      eapply Forall_forall in Hmerge; [|eapply unnest_merge_normalized_cexp]; eauto.
      eapply mmap2_normalized_cexps in H0; eauto.
    - (* case *)
      destruct is_control; repeat inv_bind; unfold unnest_case;
        repeat rewrite Forall_app; repeat split.
      1,5:(eapply IHe; eauto).
      1,4:repeat mmap_normal_args_eq.
      1,3:(destruct d; repeat (take (forall d, Some _ = Some _ -> _) and specialize (it _ eq_refl));
           repeat inv_bind; repeat mmap_normal_args_eq).
      rewrite Forall_forall; intros ? Hin.
      eapply mk_equations_In in Hin as (?&?&?&?&Hcase); subst.
      2:{ apply idents_for_anns_length in H4. rewrite map_length in H4.
          rewrite unnest_case_length, map_length... }
      econstructor; eauto.
      eapply Forall_forall in Hcase; [|eapply unnest_case_normalized_cexp]; eauto with norm.
      + apply mmap2_normalized_cexp'' in H2; [|solve_forall]; eauto.
        apply Forall_concat in H2; rewrite Forall_map in H2; auto.
        repeat inv_bind; simpl; auto.
        eapply mmap2_normalized_cexp in H10; eauto.
      + destruct d; repeat inv_bind; simpl; auto.
        eapply mmap2_normalized_cexp in H3; eauto.
    - (* app *)
      constructor. 2:repeat rewrite Forall_app; repeat split.
      + repeat econstructor; eauto.
        eapply unnest_noops_exp_noops_exp in H1; eauto.
      + repeat mmap_normal_args_eq.
      + eapply unnest_noops_exp_normal_args in H1; eauto.
      + eapply unnest_resets_normal_args in H3; eauto.
        simpl_Forall. eauto using unnest_exp_normalized_cexp.
  Qed.
  Global Hint Resolve unnest_exp_normal_args : norm.

  Corollary unnest_exps_normal_args : forall G es es' eqs' st st',
      Forall (wl_exp G) es ->
      unnest_exps G es st = (es', eqs', st') ->
      Forall (normal_args_eq G) eqs'.
  Proof.
    intros * Wl Hnorm.
    unfold unnest_exps in Hnorm. repeat inv_bind.
    do 2 mmap_normal_args_eq. eapply unnest_exp_normal_args in H2; eauto. now simpl_Forall.
  Qed.
  Global Hint Resolve unnest_exps_normal_args : norm.

  Fact unnest_rhs_normal_args : forall G e es' eqs' st st',
      wl_exp G e ->
      unnest_rhs G e st = (es', eqs', st') ->
      Forall (normal_args_eq G) eqs'.
  Proof with eauto.
    intros * Wl Hnorm.
    destruct e; unfold unnest_rhs in Hnorm;
      try (eapply unnest_exp_normal_args in Hnorm; eauto); inv Wl.
    - (* extcall *)
      repeat inv_bind.
      eapply unnest_exps_normal_args; eauto.
    - (* fby *)
      repeat inv_bind.
      repeat rewrite Forall_app; repeat split...
      eapply unnest_exps_normal_args in H; eauto.
      eapply unnest_exps_normal_args in H0; eauto.
    - (* arrow *)
      repeat inv_bind.
      repeat rewrite Forall_app; repeat split...
      eapply unnest_exps_normal_args in H; eauto.
      eapply unnest_exps_normal_args in H0; eauto.
    - (* app *)
      repeat inv_bind...
      eapply unnest_resets_normal_args in H1.
      2:{ simpl_Forall. eauto with norm. }
      repeat rewrite Forall_app; repeat split; auto.
      eapply unnest_exps_normal_args in H; eauto.
      unfold unnest_exps in H; repeat inv_bind.
      eapply unnest_noops_exp_normal_args with (es:=l) in H0; eauto.
  Qed.
  Global Hint Resolve unnest_rhs_normal_args : norm.

  Corollary unnest_rhss_normal_args : forall G es es' eqs' st st',
      Forall (wl_exp G) es ->
      unnest_rhss G es st = (es', eqs', st') ->
      Forall (normal_args_eq G) eqs'.
  Proof.
    intros * Wl Hnorm.
    unfold unnest_rhss in Hnorm; repeat inv_bind.
    do 2 mmap_normal_args_eq. eapply unnest_rhs_normal_args in H2; eauto. now simpl_Forall.
  Qed.
  Global Hint Resolve unnest_rhss_normal_args : norm.

  Fact combine_for_numstreams_In_inv {A} : forall es (vs: list A) e v,
      length vs = length (annots es) ->
      In (e, v) (combine_for_numstreams es vs) ->
      In e es /\ length v = numstreams e.
  Proof.
    induction es; intros * Len In.
    - destruct vs; simpl in *; try congruence. now inv In.
    - simpl in *.
      rewrite app_length, length_annot_numstreams in *.
      destruct vs; inv In.
      + inv H. split; auto.
        rewrite firstn_length. lia.
      + edestruct IHes; eauto.
        rewrite List.skipn_length. lia.
  Qed.

  Lemma unnest_equation_normal_args : forall G eq eqs' st st',
      wl_equation G eq ->
      unnest_equation G eq st = (eqs', st') ->
      Forall (normal_args_eq G) eqs'.
  Proof with eauto with norm.
    intros ? [xs es] * (Wl1&Wl2) Hnorm.
    unfold unnest_equation in Hnorm.
    repeat inv_bind.
    rewrite Forall_app. split.
    - apply unnest_rhss_annots in H as Anns; auto.
      unfold unnest_rhss in H. repeat inv_bind.
      simpl_Forall.
      apply combine_for_numstreams_In_inv in H0 as (In&Len); [|congruence].
      apply List.in_concat in In as (?&In1&In2).
      eapply mmap2_values, Forall3_ignore13 in H. simpl_Forall.
      destruct x0;
        try (eapply unnest_exp_normalized_cexp in H1 as Norm;
             eapply unnest_exp_numstreams in H1 as Num;
             simpl_Forall; rewrite Num in *; singleton_length;
             constructor; auto).
      all:repeat inv_bind.
      + apply In_singleton in In2; subst.
        simpl in *. singleton_length. repeat constructor.
      + unfold unnest_fby in In2. simpl_In. singleton_length. repeat constructor.
      + unfold unnest_arrow in In2. simpl_In. singleton_length. repeat constructor.
      + destruct In2 as [|[]]; subst. simpl in *.
        inv Wl1. econstructor; eauto.
        unfold unnest_exps in *. repeat inv_bind.
        eapply unnest_noops_exp_noops_exp in H1; eauto.
    - eapply unnest_rhss_normal_args in H; eauto.
  Qed.

  Lemma unnest_block_normal_args : forall G blk blks' st st',
      nolocal_block blk ->
      wl_block G blk ->
      unnest_block G blk st = (blks', st') ->
      Forall (normal_args_blk G) blks'.
  Proof.
    induction blk using block_ind2; intros * Hnloc Wl Hun; inv Hnloc; inv Wl; repeat inv_bind.
    - eapply unnest_equation_normal_args in H; eauto.
      simpl_Forall. constructor; auto.
    - repeat constructor; eauto with norm.
      eapply unnest_exp_normal_args in H; eauto.
      simpl_Forall. constructor; auto.
    - apply Forall_app. split.
      + eapply unnest_reset_is_var in H2 as (xr&ann&?); subst.
        apply mmap_values, Forall2_ignore1 in H0.
        eapply Forall_map, Forall_concat. simpl_Forall.
        constructor; eauto. eapply H in H6; eauto. simpl_Forall; auto.
      + eapply unnest_reset_normal_args in H2.
        2:{ intros; split; eauto with norm. }
        simpl_Forall. now constructor.
  Qed.

  Corollary unnest_blocks_normal_args : forall G blks blks' st st',
      Forall nolocal_block blks ->
      Forall (wl_block G) blks ->
      unnest_blocks G blks st = (blks', st') ->
      Forall (normal_args_blk G) blks'.
  Proof.
    induction blks; intros * Hnloc Wl Hnorm;
      unfold unnest_blocks in Hnorm; repeat inv_bind; simpl; auto.
    inv Hnloc. inv Wl. apply Forall_app; split.
    - eapply unnest_block_normal_args; eauto.
    - eapply IHblks; eauto.
      unfold unnest_blocks; repeat inv_bind; repeat eexists; eauto.
  Qed.

  Lemma unnest_node_normal_args : forall G n,
      wl_node G n ->
      normal_args_node (unnest_global G) (unnest_node G n).
  Proof.
    intros * Hwl. inv Hwl.
    unfold unnest_node, normal_args_node; simpl.
    pose proof (n_syn n) as Hsyn. inversion_clear Hsyn as [?? Hsyn2 _]. inv Hsyn2. rewrite <-H0 in *.
    inv H. inv_scope.
    constructor.
    eapply unnest_blocks_normal_args with (st:=init_st) in H1; eauto using surjective_pairing.
    simpl_Forall. eapply iface_eq_normal_args_blk; eauto using unnest_global_eq.
  Qed.

  Lemma unnest_global_normal_args : forall G,
      wl_global G ->
      normal_args (unnest_global G).
  Proof.
    unfold unnest_global. destruct G.
    induction nodes0; intros * Hwl; constructor; auto.
    - simpl. inv Hwl. destruct_conjs.
      eapply unnest_node_normal_args in H; eauto.
    - inv Hwl. apply IHnodes0; auto.
  Qed.

  (** ** Additional properties *)

  Ltac solve_st_follows :=
    repeat inv_bind;
    match goal with
    | |- incl (st_anns ?st1) (st_anns ?st2) =>
      eapply st_follows_incl
    | |- st_follows ?st ?st =>
      reflexivity
    | H : st_follows ?st1 ?st2 |- st_follows ?st1 _ =>
      etransitivity; [eapply H |]
    | H : fresh_ident _ _ ?st = _ |- st_follows ?st _ =>
      etransitivity; [ eapply fresh_ident_st_follows in H; eauto | ]
    | H : idents_for_anns _ ?st = _ |- st_follows ?st _ =>
      etransitivity; [ eapply idents_for_anns_st_follows in H; eauto | ]
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
  Global Hint Resolve unnest_exp_clockof : norm.
End UNNESTING.

Module UnnestingFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks : CLOCKS Ids Op OpAux)
       (Senv : STATICENV Ids Op OpAux Cks)
       (Syn : LSYNTAX Ids Op OpAux Cks Senv)
<: UNNESTING Ids Op OpAux Cks Senv Syn.
  Include UNNESTING Ids Op OpAux Cks Senv Syn.
End UnnestingFun.
