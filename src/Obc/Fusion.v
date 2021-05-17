From Coq Require Import FSets.FMapPositive.
From Coq Require Import PArith.
From Velus Require Import Common.
From Velus Require Import CommonTyping.
From Velus Require Import Operators.
From Velus Require Import Obc.ObcSyntax.
From Velus Require Import Obc.ObcSemantics.
From Velus Require Import Obc.ObcInvariants.
From Velus Require Import Obc.ObcTyping.
From Velus Require Import Obc.Equiv.

From Velus Require Import VelusMemory.

From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Coq Require Import Relations.
From Coq Require Import Morphisms.
From Coq Require Import Setoid.

Module Type FUSION
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import SynObc: OBCSYNTAX     Ids Op OpAux)
       (Import ComTyp: COMMONTYPING  Ids Op OpAux)
       (Import SemObc: OBCSEMANTICS  Ids Op OpAux SynObc)
       (Import InvObc: OBCINVARIANTS Ids Op OpAux SynObc        SemObc)
       (Import TypObc: OBCTYPING     Ids Op OpAux SynObc ComTyp SemObc)
       (Import Equ   : EQUIV         Ids Op OpAux SynObc ComTyp SemObc TypObc).

  (** ** Fusion functions *)

  Definition option_map2_defaults {A B C} (f: A -> B -> C) (da: A) (db: B) (oa: option A) (ob: option B) : option C :=
    match oa, ob with
    | Some a, Some b => Some (f a b)
    | Some a, None   => Some (f a db)
    | None, Some b   => Some (f da b)
    | None, None     => None
    end.

  Fixpoint zip s1 s2 : stmt :=
    match s1, s2 with
    | Switch e1 ss1 d1, Switch e2 ss2 d2 =>
      if e1 ==b e2
      then Switch e1 (CommonList.map2 (option_map2_defaults zip d1 d2) ss1 ss2) (zip d1 d2)
      else Comp s1 s2
    | Skip, s => s
    | s,    Skip => s
    | Comp s1' s2', _ => Comp s1' (zip s2' s2)
    | s1,   s2 => Comp s1 s2
    end.

  Fixpoint fuse' s1 s2 : stmt :=
    match s1, s2 with
    | s1, Comp s2 s3 => fuse' (zip s1 s2) s3
    | s1, s2 => zip s1 s2
    end.

  (*
      NB: almost got rid of zip, but this function decreases on the first
      argument, whereas the remaining instance of zip requires a decrease
      on the second argument...

      Fixpoint fuse' s1 s2 : stmt :=
        match s1, s2 with
        | Ifte e1 t1 f1, Ifte e2 t2 f2 =>
          if exp_eqb e1 e2
          then Ifte e1 (fuse' t1 t2) (fuse' f1 f2)
          else Comp s1 s2
        | s1, Comp s2 s3 => fuse' (fuse' s1 s2) s3
        | Skip, s => s
        | s,    Skip => s
        | Comp s1' s2', Ifte _ _ _ => Comp s1' (zip s2' s2)
        | s1,   s2 => Comp s1 s2
        end.
   *)

  Definition fuse s : stmt :=
    match s with
    | Comp s1 s2 => fuse' s1 s2
    | _ => s
    end.

  Definition fuse_method (m: method): method :=
    match m with
      mk_method name ins vars out body nodup good =>
      mk_method name ins vars out (fuse body) nodup good
    end.

  Lemma map_m_name_fuse_methods:
    forall methods,
      map m_name (map fuse_method methods) = map m_name methods.
  Proof.
    intro ms; induction ms as [|m ms]; auto.
    simpl. rewrite IHms.
    now destruct m.
  Qed.

  Program Definition fuse_class (c: class): class :=
    match c with
      mk_class name mems objs methods nodup _ _ =>
      mk_class name mems objs (map fuse_method methods) nodup _ _
    end.
  Next Obligation.
    now rewrite map_m_name_fuse_methods.
  Qed.

  Program Instance fuse_class_transform_unit: TransformUnit class class :=
    { transform_unit := fuse_class }.
  Next Obligation.
    unfold fuse_class; cases.
  Defined.

  Program Instance fuse_class_transform_state_unit: TransformStateUnit class class.
  Next Obligation.
    unfold fuse_class; cases.
  Defined.

  (** ** Basic lemmas around [fuse_class] and [fuse_method]. *)

  Lemma fuse_class_c_name:
    forall c, (fuse_class c).(c_name) = c.(c_name).
  Proof. destruct c; auto. Qed.

  Lemma fuse_class_c_objs:
    forall c,
      (fuse_class c).(c_objs) = c.(c_objs).
  Proof.
    unfold fuse_class. destruct c; auto.
  Qed.

  Lemma fuse_class_c_mems:
    forall c,
      (fuse_class c).(c_mems) = c.(c_mems).
  Proof.
    unfold fuse_class. destruct c; auto.
  Qed.

  Lemma fuse_method_m_name:
    forall m, (fuse_method m).(m_name) = m.(m_name).
  Proof. destruct m; auto. Qed.

  Lemma fuse_method_in:
    forall m, (fuse_method m).(m_in) = m.(m_in).
  Proof. destruct m; auto. Qed.

  Lemma fuse_method_out:
    forall m, (fuse_method m).(m_out) = m.(m_out).
  Proof. destruct m; auto. Qed.

  Lemma fuse_method_body:
    forall fm,
      (fuse_method fm).(m_body) = fuse fm.(m_body).
  Proof.
    now destruct fm.
  Qed.

  Definition fuse_program : program -> program := transform_units.

  Lemma fuse_find_class:
    forall p id c p',
      find_class id p = Some (c, p') ->
      find_class id (fuse_program p) = Some (fuse_class c, fuse_program p').
  Proof.
    intros * Find; apply find_unit_transform_units_forward in Find; auto.
  Qed.

  Lemma fuse_find_method:
    forall id c m,
      find_method id (fuse_class c).(c_methods) = Some m ->
      exists m', m = fuse_method m'
                 /\ find_method id c.(c_methods) = Some m'.
  Proof.
    intros * Find.
    destruct c as [? ? ? meths ? Nodup]; simpl in *.
    induction meths as [|m']; simpl in *; try discriminate.
    inv Nodup; auto.
    rewrite fuse_method_m_name in Find.
    destruct (ident_eqb (m_name m') id); auto.
    inv Find.
    exists m'; auto.
  Qed.

  Lemma map_fuse_class_c_name:
    forall p,
      map (fun cls => (fuse_class cls).(c_name)) p = map c_name p.
  Proof.
    induction p; auto.
    simpl. now rewrite IHp, fuse_class_c_name.
  Qed.

  Lemma fuse_find_method':
    forall f fm cls,
      find_method f cls.(c_methods) = Some fm ->
      find_method f (fuse_class cls).(c_methods) = Some (fuse_method fm).
  Proof.
    destruct cls; simpl.
    induction c_methods0 as [|m ms]; inversion 1.
    simpl.
    destruct (ident_eq_dec m.(m_name) f) as [He|Hne].
    - rewrite fuse_method_m_name, He, ident_eqb_refl in *.
      now injection H1; intro; subst.
    - apply ident_eqb_neq in Hne.
      rewrite fuse_method_m_name, Hne in *.
      inv c_nodupm0; auto.
  Qed.

  (** ** Invariant sufficient to justify semantic preservation of fusion. *)

  (*
   The property "Fusible (translate_eqns mems eqs)" is obtained above
   using scheduling assumptions for EqDef, since they are needed to treat
   the translation of merge expressions, and clocking assumptions for EqApp and
   EqFby. While the EqApp case can also be obtained from the scheduling
   assumptions alone, the EqFby case cannot. Consider the equations:
      y = (true when x) :: Con Cbase x true
      x = true fby y    :: Con Cbase x true

   These equations and their clocks are incorrect, since "Con Cbase x"
   requires that the clock of x be "Cbase", whereas the second equation
   requires that it be "Con Cbase x true". Still, we could try compiling
   them program:
      if x { y = true };
      if x { mem(x) = y }

   This program is well scheduled, but it does not satisfy the invariant
   Fusible. We could imagine a weaker invariant that allows the
   right-most write under an expression to change free variables in the
   expression, which suffices to justify the optimisation, but the
   preservation of this invariant under the optimisation likely becomes much
   trickier to prove. And, in any case, such programs are fundamentally
   incorrect.

   What about trying to reject such programs using sem_node rather than
   introducing clocking assumptions? The problem is that certain circular
   programs (like the one above) still have a semantics (since x and y
   are effectively always present).
  *)

  Inductive Fusible : stmt -> Prop :=
  | IFAssign: forall x e,
      Fusible (Assign x e)
  | IFAssignSt: forall x e,
      Fusible (AssignSt x e)
  | IFSwitch: forall e ss d,
      Forall (fun s => Fusible (or_default d s)) ss ->
      (forall x, Is_free_in_exp x e -> Forall (fun s => ~ Can_write_in x (or_default d s)) ss) ->
      Fusible (Switch e ss d)
  | IFStep_ap: forall xs cls i f es,
      Fusible (Call xs cls i f es)
  | IFComp: forall s1 s2,
      Fusible s1 ->
      Fusible s2 ->
      Fusible (Comp s1 s2)
  | IFSkip:
      Fusible Skip.

  Definition ClassFusible (c: class) : Prop :=
    Forall (fun m=> Fusible m.(m_body)) c.(c_methods).

  Definition ProgramFusible (p: program) : Prop :=
    Forall ClassFusible p.(classes).

  Lemma Fusible_fold_left_shift:
    forall A f (xs : list A) iacc,
      Fusible (fold_left (fun i x => Comp (f x) i) xs iacc)
      <->
      (Fusible (fold_left (fun i x => Comp (f x) i) xs Skip)
       /\ Fusible iacc).
  Proof.
    Hint Constructors Fusible.
    induction xs as [|x xs IH]; [now intuition|].
    intros; split.
    - intro HH. simpl in HH. apply IH in HH.
      destruct HH as [Hxs Hiacc].
      split; [simpl; rewrite IH|];
        repeat progress match goal with
                        | H:Fusible (Comp _ _) |- _ => inversion_clear H
                        | _ => now intuition
                        end.
    - intros [HH0 HH1].
      simpl in HH0; rewrite IH in HH0.
      simpl; rewrite IH.
      intuition.
      repeat progress match goal with
                      | H:Fusible (Comp _ _) |- _ => inversion_clear H
                      | _ => now intuition
                      end.
  Qed.

  Lemma lift_Switch:
    forall e ss d1 tt d2,
      (forall x, Is_free_in_exp x e -> Forall (fun s => ~ Can_write_in x (or_default d1 s)) ss) ->
      stmt_eval_eq (Comp (Switch e ss d1) (Switch e tt d2))
                   (Switch e (CommonList.map2 (option_map2_defaults Comp d1 d2) ss tt) (Comp d1 d2)).
  Proof.
    Hint Constructors stmt_eval.
    intros * Hfw prog menv env menv' env'.
    split; intro Hstmt.
    - inversion_clear Hstmt as [| | |? ? ? ? ? env'' menv'' ? ? Hs Ht| | ].
      inversion_clear Hs as   [| | | |? ? ? ? ? ? ? ? ? ? Hx1 Nths Hss|];
        inversion_clear Ht as [| | | |? ? ? ? ? ? ? ? ? ? Hx3 Ntht Hts|].
      econstructor; eauto.
      + apply cannot_write_exp_eval with (3:=Hss) in Hx1.
        * apply exp_eval_det with (1:=Hx3) in Hx1.
          inv Hx1.
          pose proof (conj Nths Ntht) as Nth.
          apply combine_nth_error in Nth.
          rewrite map2_combine.
          apply map_nth_error with (f := fun '(a, b) => option_map2_defaults Comp d1 d2 a b); eauto.
        * cannot_write.
          eapply nth_error_In, Forall_forall in Nths; eauto.
          contradiction.
      + simpl; unfold option_map2_defaults; cases; simpl in *; eauto.
    - inversion_clear Hstmt as [| | | |? ? ? ? ? ? ? ? ? ? Hx Hv Hs|].
      rewrite map2_combine in Hv.
      apply map_nth_error_inv in Hv as ((s1 & s2) & Nth & ?); subst.
      apply combine_nth_error in Nth as (Nth1 &?).
      unfold option_map2_defaults in Hs;
        cases; simpl in *; inv Hs; do 2 (econstructor; eauto);
        eapply cannot_write_exp_eval; eauto;
          cannot_write;
          eapply nth_error_In, Forall_forall in Nth1; eauto;
            contradiction.
  Qed.

  Lemma zip_Comp':
    forall s1 s2,
      Fusible s1 ->
      stmt_eval_eq (zip s1 s2) (Comp s1 s2).
  Proof.
    induction s1 using stmt_ind2; destruct s2;
      try rewrite stmt_eval_eq_Comp_Skip1;
      try rewrite stmt_eval_eq_Comp_Skip2;
      try reflexivity;
      inversion_clear 1;
      simpl;
      repeat progress
             match goal with
             | |- context [equiv_decb ?e1 ?e2]
               => destruct (equiv_decb e1 e2) eqn:Heq;
                    (rewrite equiv_decb_equiv in Heq; rewrite <-Heq in *)
                    || rewrite not_equiv_decb_equiv in Heq
             | H:Fusible ?s1,
                 IH:context [stmt_eval_eq (zip ?s1 _) _]
               |- context [zip ?s1 ?s2]
               => rewrite IH with (1:=H)
             end;
      try (rewrite lift_Switch; [|assumption]);
      try rewrite Comp_assoc;
      try reflexivity.
    intros p me ve me' ve'.
    rewrite 2 map2_combine.
    split; inversion_clear 1.
    - take (nth_error _ _ = _) and apply map_nth_error_inv in it as ((os1 & os2) & Hin & ?); subst.
      pose proof Hin.
      apply combine_nth_error in Hin as (Hin1 & Hin2).
      apply nth_error_In in Hin1.
      do 2 (take (Forall _ _) and eapply Forall_forall in it; eauto).
      rename it into IH.
      take (stmt_eval _ _ _ _ _) and unfold option_map2_defaults in it.
      cases; simpl in *; take (stmt_eval _ _ _ _ _) and apply IH in it; auto;
        econstructor; eauto; try erewrite map_nth_error; eauto.
    - take (nth_error _ _ = _) and apply map_nth_error_inv in it as ((os1 & os2) & Hin & ?); subst.
      pose proof Hin.
      apply combine_nth_error in Hin as (Hin1 & Hin2).
      apply nth_error_In in Hin1.
      do 2 (take (Forall _ _) and eapply Forall_forall in it; eauto).
      rename it into IH.
      take (stmt_eval _ _ _ _ _) and unfold option_map2_defaults in it.
      cases; simpl in *; take (stmt_eval _ _ _ _ _) and apply IH in it; auto;
        econstructor; eauto; try erewrite map_nth_error; eauto.
  Qed.

  Section CannotWriteZip.

    Variables (p: program)
              (insts: list (ident * ident))
              (Γm: list (ident * type))
              (Γv: list (ident * type)).

    Lemma Can_write_in_zip:
      forall s1 s2 x,
        wt_stmt p insts Γm Γv s1 ->
        wt_stmt p insts Γm Γv s2 ->
        (Can_write_in x s1 \/ Can_write_in x s2)
        <-> Can_write_in x (zip s1 s2).
    Proof.
      Hint Constructors Can_write_in wt_stmt.
      induction s1 using stmt_ind2; destruct s2; simpl; inversion_clear 1; inversion_clear 1;
        repeat progress
               match goal with
               | H:Can_write_in _ (Comp _ _) |- _ => inversion H; subst; clear H
               | H:Can_write_in _ (Switch _ _ _) |- _ => inversion H; subst; clear H
               | H:Can_write_in _ Skip |- _ => now inversion H
               | |- context [equiv_decb ?e1 ?e2] =>
                 destruct (equiv_decb e1 e2) eqn:Heq
               | H:Can_write_in _ (zip _ _) |- _ =>
                 (apply IHs1_1 in H || apply IHs1_2 in H); eauto
               | |- Can_write_in _ (Comp _ (zip _ _)) =>
                 now (apply CWIComp2; apply IHs1_2; eauto; intuition)
               | _ => intuition eauto
               end.
      - constructor.
        rewrite map2_combine, Exists_map, Exists_exists.
        take (Exists _ _) and apply Exists_exists in it as (d1 & Hin & Can).
        rewrite equiv_decb_equiv in Heq.
        assert (e = e0 ); auto; subst.
        match goal with H: typeof _ = _, H': typeof _ = _ |- _ => rewrite H in H'; inv H' end.
        assert (length l = length ss) by congruence.
        repeat take (Forall _ ss) and eapply Forall_forall in it; eauto.
        eapply length_in_left_combine with (l' := l) in Hin as (s & Hin); eauto.
        eexists; split; eauto.
        pose proof Hin as Hin'; apply in_combine_r in Hin; apply in_combine_l in Hin'.
        destruct d1, s; simpl in *; apply it; auto.
      - constructor.
        rewrite map2_combine, Exists_map, Exists_exists.
        take (Exists _ _) and apply Exists_exists in it as (d2 & Hin & Can).
        rewrite equiv_decb_equiv in Heq.
        assert (e = e0 ); auto; subst.
        match goal with H: typeof _ = _, H': typeof _ = _ |- _ => rewrite H in H'; inv H' end.
        assert (length l = length ss) by congruence.
        pose proof Hin as Hin'.
        eapply length_in_right_combine with (l0 := ss) in Hin as (s & Hin); eauto.
        eexists; split; eauto.
        apply in_combine_l in Hin.
        repeat take (Forall _ ss) and eapply Forall_forall in it; eauto.
        destruct d2, s; apply it; auto;
          eapply Forall_forall in Hin'; eauto; simpl in Hin'; auto.
      - take (Exists _ _) and apply Exists_exists in it as (s & Hin & Can).
        rewrite map2_combine, in_map_iff in Hin; destruct Hin as ((os1 & os2) & E & Hin); subst.
        pose proof Hin as Hin'.
        apply in_combine_l in Hin.
        apply in_combine_r in Hin'.
        repeat take (Forall _ _) and eapply Forall_forall in it; eauto; simpl in it.
        unfold option_map2_defaults in Can.
        cases; simpl in *; apply it in Can as [|]; auto;
          ((now left; constructor; apply Exists_exists; eauto) ||
           (now right; constructor; apply Exists_exists; eauto)).
    Qed.

    Corollary Cannot_write_in_zip:
      forall s1 s2 x,
        wt_stmt p insts Γm Γv s1 ->
        wt_stmt p insts Γm Γv s2 ->
        (~Can_write_in x s1 /\ ~Can_write_in x s2)
        <-> ~Can_write_in x (zip s1 s2).
    Proof.
      intros s1 s2 x.
      split; intro HH.
      - intro Hcan; eapply Can_write_in_zip in Hcan; intuition.
      - split; intro Hcan; apply HH; apply Can_write_in_zip; intuition.
    Qed.

    Lemma Can_write_in_var_zip:
      forall s1 s2 x,
        wt_stmt p insts Γm Γv s1 ->
        wt_stmt p insts Γm Γv s2 ->
        (Can_write_in_var x s1 \/ Can_write_in_var x s2)
        <-> Can_write_in_var x (zip s1 s2).
    Proof.
      Hint Constructors Can_write_in_var wt_stmt.
      induction s1 using stmt_ind2; destruct s2; simpl; inversion_clear 1; inversion_clear 1;
        repeat progress
               match goal with
               | H:Can_write_in_var _ (Comp _ _) |- _ => inversion H; subst; clear H
               | H:Can_write_in_var _ (Switch _ _ _) |- _ => inversion H; subst; clear H
               | H:Can_write_in_var _ Skip |- _ => now inversion H
               | |- context [equiv_decb ?e1 ?e2] =>
                 destruct (equiv_decb e1 e2) eqn:Heq
               | H:Can_write_in_var _ (zip _ _) |- _ =>
                 (apply IHs1_1 in H || apply IHs1_2 in H); eauto
               | |- Can_write_in_var _ (Comp _ (zip _ _)) =>
                 now (apply CWIVComp2; apply IHs1_2; eauto; intuition)
               | _ => intuition eauto
               end.
      - constructor.
        rewrite map2_combine, Exists_map, Exists_exists.
        take (Exists _ _) and apply Exists_exists in it as (d1 & Hin & Can).
        rewrite equiv_decb_equiv in Heq.
        assert (e = e0 ); auto; subst.
        match goal with H: typeof _ = _, H': typeof _ = _ |- _ => rewrite H in H'; inv H' end.
        assert (length l = length ss) by congruence.
        repeat take (Forall _ ss) and eapply Forall_forall in it; eauto.
        eapply length_in_left_combine with (l' := l) in Hin as (s & Hin); eauto.
        eexists; split; eauto.
        pose proof Hin as Hin'; apply in_combine_r in Hin; apply in_combine_l in Hin'.
        destruct d1, s; simpl in *; apply it; auto.
      - constructor.
        rewrite map2_combine, Exists_map, Exists_exists.
        take (Exists _ _) and apply Exists_exists in it as (d2 & Hin & Can).
        rewrite equiv_decb_equiv in Heq.
        assert (e = e0 ); auto; subst.
        match goal with H: typeof _ = _, H': typeof _ = _ |- _ => rewrite H in H'; inv H' end.
        assert (length l = length ss) by congruence.
        pose proof Hin as Hin'.
        eapply length_in_right_combine with (l0 := ss) in Hin as (s & Hin); eauto.
        eexists; split; eauto.
        apply in_combine_l in Hin.
        repeat take (Forall _ ss) and eapply Forall_forall in it; eauto.
        destruct d2, s; apply it; auto;
          eapply Forall_forall in Hin'; eauto; simpl in Hin'; auto.
      - take (Exists _ _) and apply Exists_exists in it as (s & Hin & Can).
        rewrite map2_combine, in_map_iff in Hin; destruct Hin as ((os1 & os2) & E & Hin); subst.
        pose proof Hin as Hin'.
        apply in_combine_l in Hin.
        apply in_combine_r in Hin'.
        repeat take (Forall _ _) and eapply Forall_forall in it; eauto; simpl in it.
        unfold option_map2_defaults in Can.
        cases; simpl in *; apply it in Can as [|]; auto;
          ((now left; constructor; apply Exists_exists; eauto) ||
           (now right; constructor; apply Exists_exists; eauto)).
    Qed.

    Corollary Cannot_write_in_var_zip:
      forall s1 s2 x,
        wt_stmt p insts Γm Γv s1 ->
        wt_stmt p insts Γm Γv s2 ->
        (~Can_write_in_var x s1 /\ ~Can_write_in_var x s2)
        <-> ~Can_write_in_var x (zip s1 s2).
    Proof.
      intros s1 s2 x.
      split; intro HH.
      - intro Hcan; eapply Can_write_in_var_zip in Hcan; intuition.
      - split; intro Hcan; apply HH; apply Can_write_in_var_zip; intuition.
    Qed.

    Lemma zip_free_write:
      forall s1 s2,
        wt_stmt p insts Γm Γv s1 ->
        wt_stmt p insts Γm Γv s2 ->
        Fusible s1 ->
        Fusible s2 ->
        Fusible (zip s1 s2).
    Proof.
      Hint Constructors Fusible Can_write_in wt_stmt.
      induction s1 using stmt_ind2; destruct s2;
        intros WTs1 WTs2 Hfree1 Hfree2; inv WTs1; inv WTs2;
          inversion_clear Hfree1; inversion_clear Hfree2;
            simpl;
            try now intuition eauto.
      destruct (e ==b e0) eqn: E; eauto.
      rewrite equiv_decb_equiv in E.
      assert (e = e0) by auto; subst.
      rewrite map2_combine.
      constructor.
      - apply Forall_map, Forall_forall.
        intros (s & s') Hin.
        pose proof Hin as Hin'.
        eapply in_combine_l in Hin.
        eapply in_combine_r in Hin'.
        repeat (take (Forall _ ss) and apply Forall_forall with (2 := Hin) in it).
        rename it into IH.
        repeat (take (Forall _ _) and apply Forall_forall with (2 := Hin') in it).
        unfold option_map2_defaults.
        cases; simpl in *; auto.
      - intros * Free.
        do 2 (take (forall x, Is_free_in_exp x _ -> _) and (specialize (it x Free))).
        apply Forall_map, Forall_forall.
        intros (s & s') Hin.
        pose proof Hin as Hin'.
        eapply in_combine_l in Hin.
        eapply in_combine_r in Hin'.
        repeat (take (Forall _ ss) and apply Forall_forall with (2 := Hin) in it).
        rename it into IH.
        repeat (take (Forall _ _) and apply Forall_forall with (2 := Hin') in it).
        unfold option_map2_defaults.
        cases; simpl in *; rewrite <-Cannot_write_in_zip; eauto.
    Qed.

    Lemma wt_stmt_zip:
      forall s1 s2,
        wt_stmt p insts Γm Γv s1 ->
        wt_stmt p insts Γm Γv s2 ->
        wt_stmt p insts Γm Γv (zip s1 s2).
    Proof.
      Hint Constructors wt_stmt.
      induction s1 using stmt_ind2'; destruct s2; simpl; inversion_clear 1; inversion_clear 1; eauto.
      cases_eqn E; eauto.
      rewrite equiv_decb_equiv in E; assert (e = e0) by auto; subst.
      match goal with H: typeof _ = _, H': typeof _ = _ |- _ => rewrite H in H'; inv H' end.
      assert (length ss = length l) as E' by congruence.
      rewrite map2_combine.
      econstructor; eauto.
      - rewrite map_length, combine_length.
        rewrite E', Min.min_idempotent; auto.
      - intros * Hin; apply in_map_iff in Hin as ((os1, os2) & Eq & Hin).
        pose proof Hin as Hin'; apply in_combine_l in Hin; apply in_combine_r in Hin'.
        take (Forall _ ss) and apply Forall_forall with (2 := Hin) in it; eauto.
        destruct os1, os2; simpl in *; inv Eq; eauto.
    Qed.

    Lemma Can_write_in_fuse':
      forall s1 s2 x,
        wt_stmt p insts Γm Γv s1 ->
        wt_stmt p insts Γm Γv s2 ->
        Can_write_in x (Comp s1 s2) <-> Can_write_in x (fuse' s1 s2).
    Proof.
      intros s1 s2; revert s1; induction s2; simpl; intros;
        try setoid_rewrite <-Can_write_in_zip;
        try setoid_rewrite Can_write_in_Comp;
        try reflexivity; auto.
      take (wt_stmt _ _ _ _ (Comp _ _)) and inv it.
      setoid_rewrite <-IHs2_2; auto.
      - setoid_rewrite Can_write_in_Comp.
        setoid_rewrite <-Can_write_in_zip; auto.
        intuition.
      - apply wt_stmt_zip; auto.
    Qed.

    Corollary Can_write_in_fuse:
      forall s x,
        wt_stmt p insts Γm Γv s ->
        Can_write_in x s <-> Can_write_in x (fuse s).
    Proof.
      destruct s; simpl; try reflexivity.
      inversion_clear 1; apply Can_write_in_fuse'; auto.
    Qed.

    Lemma fuse'_Comp:
      forall s2 s1,
        wt_stmt p insts Γm Γv s1 ->
        wt_stmt p insts Γm Γv s2 ->
        Fusible s1 ->
        Fusible s2 ->
        stmt_eval_eq (fuse' s1 s2) (Comp s1 s2).
    Proof.
      Hint Constructors Fusible.
      induction s2 using stmt_ind2;
        intros s1 WTs1 WTs2 Fus1 Fus2; simpl; inv WTs2;
          try now (rewrite zip_Comp'; intuition).
      rewrite Comp_assoc.
      inversion_clear Fus2.
      rewrite IHs2_2; auto.
      - intros prog menv env menv' env'.
        rewrite zip_Comp'; auto.
        reflexivity.
      - apply wt_stmt_zip; auto.
      - apply zip_free_write; auto.
    Qed.

    Corollary fuse_Comp:
      forall s,
        wt_stmt p insts Γm Γv s ->
        Fusible s ->
        stmt_eval_eq (fuse s) s.
    Proof.
      intros s WT Hfree prog menv env menv' env'.
      destruct s; simpl; try reflexivity.
      inversion_clear Hfree; inv WT.
      apply fuse'_Comp; auto.
    Qed.

    (* TODO: factorize proof *)
    Lemma No_Overwrites_zip:
      forall s1 s2,
        wt_stmt p insts Γm Γv s1 ->
        wt_stmt p insts Γm Γv s2 ->
        No_Overwrites (Comp s1 s2) ->
        No_Overwrites (zip s1 s2).
    Proof.
      induction s1 using stmt_ind2; destruct s2; inversion_clear 1; inversion_clear 1;
        intros Hno; inv Hno; simpl; eauto; repeat (take (No_Overwrites (_ _)) and inv it).
      - destruct (e ==b e0); auto.
        constructor.
        rewrite map2_combine; apply Forall_map, Forall_forall; intros (os1, os2) Hin.
        pose proof Hin as Hin'; apply in_combine_l in Hin; apply in_combine_r in Hin'.
        repeat (take (Forall _ ss) and eapply Forall_forall with (2:=Hin) in it).
        repeat (take (Forall _ _) and eapply Forall_forall with (2:=Hin') in it).
        match goal with H: (forall x: ident, _), H': (forall x: ident, _) |- _ =>
                        rename H into Cannot1; rename H' into Cannot2 end.
        unfold option_map2_defaults;
          cases; simpl in *; apply it1; auto;
            constructor; auto; intros x Can_s Can_t;
              ((now eapply Cannot1; constructor; apply Exists_exists; eauto) ||
               (now eapply Cannot2; constructor; apply Exists_exists; eauto)).
      - constructor; eauto.
        + intros x Can1 Can2.
          apply Can_write_in_var_zip in Can2 as [|]; eauto.
          * eapply H7; eauto.
          * eapply H5; eauto.
        + intros x Can1 Can2.
          apply Can_write_in_var_zip in Can1 as [|]; eauto.
          * eapply H7; eauto.
          * eapply H5; eauto.
        + eapply IHs1_2; eauto.
          constructor; auto.
          intros x Can1 Can2; eapply H5; eauto.
      - constructor; eauto.
        + intros x Can1 Can2.
          apply Can_write_in_var_zip in Can2 as [|]; eauto.
          * eapply H7; eauto.
          * eapply H5; eauto.
        + intros x Can1 Can2.
          apply Can_write_in_var_zip in Can1 as [|]; eauto.
          * eapply H7; eauto.
          * eapply H5; eauto.
        + eapply IHs1_2; eauto.
          constructor; auto.
          intros x Can1 Can2; eapply H5; eauto.
      - constructor; eauto.
        + intros x Can1 Can2.
          apply Can_write_in_var_zip in Can2 as [|]; eauto.
          * eapply H12; eauto.
          * eapply H9; eauto.
        + intros x Can1 Can2.
          apply Can_write_in_var_zip in Can1 as [|]; eauto.
          * eapply H12; eauto.
          * eapply H9; eauto.
        + eapply IHs1_2; eauto.
          constructor; auto.
          intros x Can1 Can2; eapply H9; eauto.
      - constructor; eauto.
        + intros x Can1 Can2.
          apply Can_write_in_var_zip in Can2 as [|]; eauto.
          * eapply H12; eauto.
          * eapply H5; eauto.
        + intros x Can1 Can2.
          apply Can_write_in_var_zip in Can1 as [|]; eauto.
          * eapply H12; eauto.
          * eapply H5; eauto.
        + eapply IHs1_2; eauto.
          constructor; auto.
          intros x Can1 Can2; eapply H5; eauto.
      - constructor; eauto.
        + intros x Can1 Can2.
          apply Can_write_in_var_zip in Can2 as [|]; eauto.
          * eapply H13; eauto.
          * eapply H10; eauto.
        + intros x Can1 Can2.
          apply Can_write_in_var_zip in Can1 as [|]; eauto.
          * eapply H13; eauto.
          * eapply H10; eauto.
        + eapply IHs1_2; eauto.
          constructor; auto.
          intros x Can1 Can2; eapply H10; eauto.
    Qed.

    Lemma No_Overwrites_fuse':
      forall s1 s2,
        wt_stmt p insts Γm Γv s1 ->
        wt_stmt p insts Γm Γv s2 ->
        No_Overwrites (Comp s1 s2) ->
        No_Overwrites (fuse' s1 s2).
    Proof.
      intros s1 s2; revert s1; induction s2; simpl; inversion_clear 2; inversion_clear 1;
        try apply No_Overwrites_zip; eauto using wt_stmt.
      match goal with H:No_Overwrites (Comp _ _) |- _ => inv H end.
      apply IHs2_2; auto.
      - now apply wt_stmt_zip.
      - constructor; auto.
        + intros x Hcw.
          apply Can_write_in_var_zip in Hcw as [Hcw|Hcw]; auto.
          match goal with H:forall x, Can_write_in_var x s1 -> _ |- _ => apply H in Hcw end.
          apply cannot_write_in_var_Comp in Hcw as (? & ?); auto.
        + intros x Hcw; apply Cannot_write_in_var_zip; auto.
        + apply No_Overwrites_zip; auto.
          constructor; auto. intros x Hcw.
          match goal with H:forall x, Can_write_in_var x s1 -> _ |- _ => apply H in Hcw end.
          apply cannot_write_in_var_Comp in Hcw as (? & ?); auto.
    Qed.

    Corollary No_Overwrites_fuse:
      forall s,
        wt_stmt p insts Γm Γv s ->
        No_Overwrites s ->
        No_Overwrites (fuse s).
    Proof.
      destruct s; intros WT Hnoo; auto; inv WT.
      now apply No_Overwrites_fuse'.
    Qed.

  End CannotWriteZip.

  Lemma fuse_call:
    forall p n me me' f xss rs,
      wt_program p ->
      ProgramFusible p ->
      stmt_call_eval p me n f xss me' rs ->
      stmt_call_eval (fuse_program p) me n f xss me' rs.
  Proof.
    cut ((forall p me ve stmt e',
             stmt_eval p me ve stmt e' ->
             wt_program p ->
             ProgramFusible p ->
             stmt_eval (fuse_program p) me ve stmt e')
         /\ (forall p me clsid f vs me' rvs,
                stmt_call_eval p me clsid f vs me' rvs ->
                wt_program p ->
                ProgramFusible p ->
                stmt_call_eval (fuse_program p) me clsid f vs me' rvs)).
    now destruct 1 as (Hf1 & Hf2); intros; apply Hf2; auto.
    apply stmt_eval_call_ind; intros; eauto using stmt_eval.
    take (find_class _ _ = _) and rename it into Find.
    take (find_method _ _ = _) and rename it into Findm.
    take (wt_program _) and rename it into WTp.
    take (ProgramFusible _) and rename it into Fusp.
    take (wt_program _ -> _) and rename it into IH.
    pose proof (find_unit_In _ _ _ _ Find) as [? Hinp].
    pose proof (find_method_In _ _ _ Findm) as Hinc.
    pose proof (find_unit_spec _ _ _ _ Find) as (?& Hprog').
    pose proof (wt_program_find_unit _ _ _ _ _ WTp Find) as (WTc & WTp').
    pose proof (wt_class_find_method _ _ _ _ WTc Findm) as (WTm & Henums).
    apply fuse_find_class in Find.
    apply fuse_find_method' in Findm.
    econstructor; eauto.
    - now rewrite fuse_method_in.
    - rewrite fuse_method_in.
      apply Forall_forall with (1:=Fusp) in Hinp.
      apply Forall_forall with (1:=Hinp) in Hinc.
      rewrite fuse_method_body.
      rewrite fuse_Comp with (2:=Hinc); eauto.
      destruct Hprog' as (cls'' & Hprog & Hfind).
      unfold ProgramFusible in Fusp; setoid_rewrite Hprog in Fusp.
      apply Forall_app in Fusp.
      rewrite Forall_cons2 in Fusp.
      apply IH; intuition.
    - now rewrite fuse_method_out; eassumption.
  Qed.

  Corollary fuse_loop_call:
    forall f c ins outs prog me,
      wt_program prog ->
      ProgramFusible prog ->
      loop_call prog c f ins outs 0 me ->
      loop_call (fuse_program prog) c f ins outs 0 me.
  Proof.
    intros ?????; generalize 0%nat.
    cofix COINDHYP.
    intros n me WT HCF Hdo.
    destruct Hdo.
    econstructor; eauto using fuse_call.
  Qed.

  (** ** Fusion preserves well-typing. *)

  Lemma wt_exp_fuse_program:
    forall p Γm Γv e,
      wt_exp p Γm Γv e ->
      wt_exp (fuse_program p) Γm Γv e.
  Proof.
    induction e; inversion_clear 1; eauto using wt_exp.
  Qed.

  Lemma wt_stmt_fuse_program:
    forall p insts Γm Γv s,
      wt_stmt p insts Γm Γv s ->
      wt_stmt (fuse_program p) insts Γm Γv s.
  Proof.
    induction s using stmt_ind2'; inversion_clear 1; eauto using wt_exp_fuse_program, wt_stmt.
    - econstructor; eauto using wt_exp_fuse_program.
      intros * Hin.
      take (Forall _ _) and eapply Forall_forall in it; eauto; simpl in *; eauto.
    - eapply wt_Call
        with (cls:=fuse_class cls) (p':=fuse_program p') (fm:=fuse_method fm);
        auto; try (now destruct fm; auto).
      + erewrite fuse_find_class; eauto.
      + now apply fuse_find_method'.
      + apply Forall_forall; intros * Hin.
        take (Forall _ _) and eapply Forall_forall in it; eauto using wt_exp_fuse_program.
  Qed.

  Lemma wt_stmt_fuse:
    forall p insts Γm Γv s,
      wt_stmt p insts Γm Γv s ->
      wt_stmt p insts Γm Γv (fuse s).
  Proof.
    intros * WTs.
    destruct s; auto; simpl; inv WTs.
    match goal with H1:wt_stmt _ _ _ _ s1, H2:wt_stmt _ _ _ _ s2 |- _ =>
                    revert s2 s1 H1 H2 end.
    induction s2; simpl; auto using wt_stmt_zip.
    intros s2 WTs1 WTcomp.
    inv WTcomp.
    apply IHs2_2; auto.
    apply wt_stmt_zip; auto.
  Qed.

  Lemma meth_vars_fuse_method:
    forall m,
      meth_vars (fuse_method m) = meth_vars m.
  Proof.
    destruct m; simpl; auto.
  Qed.

  Lemma fuse_wt_program:
    forall p,
      wt_program p ->
      wt_program (fuse_program p).
  Proof.
    intros * WT.
    eapply transform_units_wt_program in WT; eauto; simpl.
    inversion_clear 1 as (Hos & Hms).
    constructor.
    - rewrite fuse_class_c_objs.
      apply Forall_impl_In with (2:=Hos).
      intros ic Hin Hfind.
      apply not_None_is_Some in Hfind.
      destruct Hfind as ((cls & p') & Hfind).
      apply fuse_find_class in Hfind; unfold fuse_program in Hfind; simpl in *.
      setoid_rewrite Hfind.
      discriminate.
    - destruct u; simpl in *.
      clear c_nodup0 c_nodupm0 Hos.
      induction c_methods0 as [|m ms]; simpl; auto using Forall_nil.
      apply Forall_cons2 in Hms.
      destruct Hms as ((WTm & Henums) & WTms).
      apply Forall_cons; auto. clear IHms WTms.
      split; rewrite meth_vars_fuse_method; auto.
      destruct m; simpl in *.
      apply wt_stmt_fuse; eauto.
      apply wt_stmt_fuse_program in WTm; auto.
  Qed.

  Lemma fuse_wt_memory:
    forall me p c,
      wt_memory me p c.(c_mems) c.(c_objs) ->
      wt_memory me (fuse_program p) (fuse_class c).(c_mems) (fuse_class c).(c_objs).
  Proof.
    intros * WT.
    pose proof transform_units_wt_memory' as Spec; simpl in Spec.
    apply Spec in WT; auto.
  Qed.

  (** ** Fusion preserves [Can_write_in]. *)

  Lemma fuse_cannot_write_inputs:
    forall p,
      wt_program p ->
      Forall_methods (fun m => Forall (fun x => ~ Can_write_in x (m_body m)) (map fst (m_in m))) p ->
      Forall_methods (fun m => Forall (fun x => ~ Can_write_in x (m_body m)) (map fst (m_in m)))
                     (fuse_program p).
  Proof.
    intros * WTp HH.
    apply Forall_forall; intros * Hin;
      apply Forall_forall; intros * Hin';
        apply Forall_forall; intros ? Hin''.
    apply in_map_iff in Hin as (c &?& Hin); subst.
    edestruct In_find_unit as (?& Find); eauto using wt_program_nodup_classes.
    eapply wt_program_find_unit in Find as (WTc & ?); eauto; destruct WTc as (?& WTms).
    eapply Forall_forall in HH; eauto.
    destruct c; simpl in *.
    apply in_map_iff in Hin' as (m &?&?); subst.
    eapply Forall_forall in HH; eauto.
    eapply Forall_forall in WTms as (?&?); eauto.
    destruct m; simpl in *.
    eapply Forall_forall in HH; eauto.
    rewrite <-Can_write_in_fuse; eauto.
  Qed.

  (** ** Fusion preserves [No_Overwrites]. *)

  Lemma fuse_No_Overwrites:
    forall p,
      wt_program p ->
      Forall_methods (fun m => No_Overwrites (m_body m)) p ->
      Forall_methods (fun m => No_Overwrites (m_body m)) (fuse_program p).
  Proof.
    intros * WTp HH.
    apply Forall_forall; intros * Hin;
      apply Forall_forall; intros * Hin'.
    apply in_map_iff in Hin as (c &?&?); subst.
    edestruct In_find_unit as (?& Find); eauto using wt_program_nodup_classes.
    eapply wt_program_find_unit in Find as (WTc & ?); eauto; destruct WTc as (?& WTms).
    eapply Forall_forall in HH; eauto.
    destruct c; simpl in *.
    apply in_map_iff in Hin' as (m &?& Hin'); subst.
    eapply Forall_forall with (2 := Hin') in HH; eauto.
    eapply Forall_forall in WTms as (?&?); eauto.
    destruct m; simpl in *.
    eapply No_Overwrites_fuse; eauto.
  Qed.

End FUSION.

Module FusionFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (SynObc: OBCSYNTAX     Ids Op OpAux)
       (ComTyp: COMMONTYPING  Ids Op OpAux)
       (SemObc: OBCSEMANTICS  Ids Op OpAux SynObc)
       (InvObc: OBCINVARIANTS Ids Op OpAux SynObc         SemObc)
       (TypObc: OBCTYPING     Ids Op OpAux SynObc ComTyp SemObc)
       (Equ   : EQUIV         Ids Op OpAux SynObc ComTyp SemObc TypObc)
       <: FUSION Ids Op OpAux SynObc ComTyp SemObc InvObc TypObc Equ.
  Include FUSION Ids Op OpAux SynObc ComTyp SemObc InvObc TypObc Equ.
End FusionFun.
