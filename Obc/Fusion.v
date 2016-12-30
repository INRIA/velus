Require Import Coq.FSets.FMapPositive.
Require Import PArith.
Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.Obc.ObcSyntax.
Require Import Velus.Obc.ObcSemantics.
Require Import Velus.Obc.ObcTyping.
Require Import Velus.Obc.Equiv.

Require Import Velus.NLustre.NLSyntax.
Require Import Velus.RMemory.

Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Ltac inv H := inversion H; subst; clear H.

Module Type FUSION
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op)
       (Import SynObc: Velus.Obc.ObcSyntax.OBCSYNTAX Ids Op OpAux)
       (Import SemObc: Velus.Obc.ObcSemantics.OBCSEMANTICS Ids Op OpAux SynObc)
       (Import TypObc: Velus.Obc.ObcTyping.OBCTYPING Ids Op OpAux SynObc SemObc)
       (Import Equ   : Velus.Obc.Equiv.EQUIV Ids Op OpAux SynObc SemObc).
  
  (** ** Determine whether an Obc command can modify a variable. *)
  
  Inductive Can_write_in : ident -> stmt -> Prop :=
  | CWIAssign: forall x e,
      Can_write_in x (Assign x e)
  | CWIAssignSt: forall x e,
      Can_write_in x (AssignSt x e)
  | CWIIfteTrue: forall x e s1 s2,
      Can_write_in x s1 ->
      Can_write_in x (Ifte e s1 s2)
  | CWIIfteFalse: forall x e s1 s2,
      Can_write_in x s2 ->
      Can_write_in x (Ifte e s1 s2)
  | CWICall_ap: forall x xs cls i f es,
      In x xs ->
      Can_write_in x (Call xs cls i f es)
  | CWIComp1: forall x s1 s2,
      Can_write_in x s1 ->
      Can_write_in x (Comp s1 s2)
  | CWIComp2: forall x s1 s2,
      Can_write_in x s2 ->
      Can_write_in x (Comp s1 s2).
  
  Lemma cannot_write_in_Ifte:
    forall x e s1 s2,
      ~ Can_write_in x (Ifte e s1 s2)
      <->
      ~ Can_write_in x s1 /\ ~ Can_write_in x s2.
  Proof.
    Hint Constructors Can_write_in.
    intros; split; intro; try (intro HH; inversion_clear HH); intuition.
  Qed.

  Lemma cannot_write_in_Comp:
    forall x s1 s2,
      ~ Can_write_in x (Comp s1 s2)
      <->
      ~ Can_write_in x s1 /\ ~ Can_write_in x s2.
  Proof.
    Hint Constructors Can_write_in.
    intros; split; intro; try (intro HH; inversion_clear HH); intuition.
  Qed.

  Ltac cannot_write :=
    repeat progress
           match goal with
           | |- forall x, Is_free_in_exp x _ -> _ => intros
           | Hfw: (forall x, Is_free_in_exp x ?e -> _),
                  Hfree: Is_free_in_exp ?x ?e |- _
             => pose proof (Hfw x Hfree); clear Hfw
           | |- _ /\ _ => split
           | |- ~Can_write_in _ _ => intro
           | H: Can_write_in _ (Comp _ _) |- _ => inversion_clear H
           | _ => now intuition
           end.

  Lemma cannot_write_exp_eval:
    forall prog s menv env menv' env' e v,
      (forall x, Is_free_in_exp x e -> ~ Can_write_in x s)
      -> exp_eval menv env e v
      -> stmt_eval prog menv env s (menv', env')
      -> exp_eval menv' env' e v.
  Proof.
    Hint Constructors Is_free_in_exp Can_write_in exp_eval.
    induction s; intros menv env menv' env' e' v Hfree Hexp Hstmt.
    - inv Hstmt.
      apply exp_eval_extend_env; trivial.
      intro Habs. apply (Hfree i); auto.
    - inv Hstmt.
      apply exp_eval_extend_mem; trivial.
      intro Habs. apply (Hfree i); auto.
    - inv Hstmt. destruct b; [eapply IHs1|eapply IHs2];
                   try eassumption; try now cannot_write.
    - inv Hstmt.
      match goal with
      | Hs1: stmt_eval _ _ _ s1 _,
             Hs2: stmt_eval _ _ _ s2 _ |- _
        => apply IHs1 with (2:=Hexp) in Hs1;
          [apply IHs2 with (2:=Hs1) (3:=Hs2)|];
          now cannot_write
      end.
    - inv Hstmt.
      apply exp_eval_extend_mem_by_obj.
      unfold adds.
      remember (combine l rvs) as lr eqn:Heq.
      assert (forall x, In x lr -> In (fst x) l) as Hin
        by (destruct x; subst; apply in_combine_l).
      clear Heq. induction lr as [|x lr]; auto. 
      destruct x as [x v'].
      apply exp_eval_extend_env.
      + intro HH; apply (Hfree x HH).
        constructor.
        change (In (fst (x, v')) l).
        apply Hin, in_eq. 
      + apply IHlr. intros y Hin'. apply Hin.
        constructor (assumption).
    - now inv Hstmt.
  Qed.

  Lemma lift_Ifte:
    forall e s1 s2 t1 t2,
      (forall x, Is_free_in_exp x e
            -> (~Can_write_in x s1 /\ ~Can_write_in x s2))
      -> stmt_eval_eq (Comp (Ifte e s1 s2) (Ifte e t1 t2))
                      (Ifte e (Comp s1 t1) (Comp s2 t2)).
  Proof.
    Hint Constructors stmt_eval.
    intros e s1 s2 t1 t2 Hfw prog menv env menv' env'.
    split; intro Hstmt.
    - inversion_clear Hstmt as [| | |? ? ? ? ? env'' menv'' ? ? Hs Ht| | ].
      inversion_clear Hs as   [| | | |? ? ? ? ? bs ? ? ? ? Hx1 Hse Hss|];
        inversion_clear Ht as [| | | |? ? ? ? ? bt ? ? ? ? Hx3 Hte Hts|];
        destruct bs; destruct bt; econstructor; try eassumption;
          repeat progress match goal with
          | H:val_to_bool _ = Some true |- _ => apply val_to_bool_true' in H
          | H:val_to_bool _ = Some false |- _ => apply val_to_bool_false' in H
          end; subst.
      + econstructor (eassumption).
      + apply cannot_write_exp_eval with (3:=Hss) in Hx1; [|now cannot_write].
        apply exp_eval_det with (1:=Hx3) in Hx1.
        exfalso; now apply true_not_false_val.
      + apply cannot_write_exp_eval with (3:=Hss) in Hx1; [|now cannot_write].
        apply exp_eval_det with (1:=Hx3) in Hx1.
        exfalso; now apply true_not_false_val.
      + econstructor (eassumption).
    - inversion_clear Hstmt as [| | | |? ? ? ? ? ? ? ? ? ? Hx Hv Hs|].
      destruct b; assert (Hv':=Hv);
        [apply val_to_bool_true' in Hv'
        |apply val_to_bool_false' in Hv']; subst;
          inversion_clear Hs as [| | |? ? ? ? ? env'' menv'' ? ? Hs1 Ht1| | ];
          apply Icomp with (menv1:=menv'') (env1:=env'').
      + apply Iifte with (1:=Hx) (2:=Hv) (3:=Hs1).
      + apply cannot_write_exp_eval with (3:=Hs1) in Hx; [|now cannot_write].
        apply Iifte with (1:=Hx) (2:=Hv) (3:=Ht1).
      + apply Iifte with (1:=Hx) (2:=Hv) (3:=Hs1).
      + apply cannot_write_exp_eval with (3:=Hs1) in Hx; [|now cannot_write].
        apply Iifte with (1:=Hx) (2:=Hv) (3:=Ht1).
  Qed.

  (** ** Fusion functions *)
  
  Fixpoint zip s1 s2 : stmt :=
    match s1, s2 with
    | Ifte e1 t1 f1, Ifte e2 t2 f2 =>
      if equiv_decb e1 e2
      then Ifte e1 (zip t1 t2) (zip f1 f2)
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
      mk_class name mems objs methods nodup nodupm =>
      mk_class name mems objs (map fuse_method methods) nodup _
    end.
  Next Obligation.
    now rewrite map_m_name_fuse_methods.
  Qed.

  (** ** Basic lemmas around [fuse_class] and [fuse_method]. *)

  Lemma fuse_class_name:
    forall c, (fuse_class c).(c_name) = c.(c_name).
  Proof. destruct c; auto. Qed.

  Lemma fuse_method_name:
    forall m, (fuse_method m).(m_name) = m.(m_name).
  Proof. destruct m; auto. Qed.

  Lemma fuse_method_in:
    forall m, (fuse_method m).(m_in) = m.(m_in). 
  Proof. destruct m; auto. Qed.

  Lemma fuse_method_out:
    forall m, (fuse_method m).(m_out) = m.(m_out). 
  Proof. destruct m; auto. Qed.

  Lemma fuse_find_class:
    forall p id c p',
      find_class id p = Some (c, p') ->
      find_class id (map fuse_class p) = Some (fuse_class c, map fuse_class p').
  Proof.
    induction p as [|c']; simpl; intros ** Find; try discriminate.
    rewrite fuse_class_name.
    destruct (ident_eqb (c_name c') id); auto.
    inv Find; auto.
  Qed.

  Lemma fuse_find_method:
    forall id c m,
      find_method id (fuse_class c).(c_methods) = Some m ->
      exists m', m = fuse_method m'
                 /\ find_method id c.(c_methods) = Some m'.
  Proof.
    intros ** Find.
    destruct c as [? ? ? meths ? Nodup]; simpl in *.
    induction meths as [|m']; simpl in *; try discriminate.
    inv Nodup; auto.
    rewrite fuse_method_name in Find.
    destruct (ident_eqb (m_name m') id); auto.
    inv Find.
    exists m'; auto.
  Qed.

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

  Lemma fuse_class_c_name:
    forall c,
      (fuse_class c).(c_name) = c.(c_name).
  Proof.
    unfold fuse_class. destruct c; auto.
  Qed.

  Lemma fuse_method_m_name:
    forall m,
      (fuse_method m).(m_name) = m.(m_name).
  Proof.
    unfold fuse_method; destruct m; auto.
  Qed.

  Lemma fuse_method_body:
    forall fm,
      (fuse_method fm).(m_body) = fuse fm.(m_body).
  Proof.
    now destruct fm.
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
  | IFIfte: forall e s1 s2,
      Fusible s1 ->
      Fusible s2 ->
      (forall x, Is_free_in_exp x e -> ~Can_write_in x s1 /\ ~Can_write_in x s2) ->
      Fusible (Ifte e s1 s2)
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

  Lemma lift_Fusible:
    forall e s1 s2 t1 t2,
      Fusible (Comp (Ifte e s1 s2) (Ifte e t1 t2))
      <->
      Fusible (Ifte e (Comp s1 t1) (Comp s2 t2)).
  Proof.
    Hint Constructors Fusible.
    intros e s1 s2 t1 t2.
    split; intro Hifw.
    - inversion_clear Hifw as [| | | |? ? Hs Ht|].
      constructor; inversion_clear Hs; inversion_clear Ht; now cannot_write.
    - inversion_clear Hifw as [| |? ? ? Hfree1 Hfree2 Hcw| | | ].
      inversion_clear Hfree1; inversion_clear Hfree2.
      repeat constructor; cannot_write.
  Qed.

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

  Lemma Can_write_in_zip:
    forall s1 s2 x,
      (Can_write_in x s1 \/ Can_write_in x s2)
      <-> Can_write_in x (zip s1 s2).
  Proof.
    Hint Constructors Can_write_in.
    induction s1, s2; simpl;
      repeat progress
             match goal with
             | H:Can_write_in _ (Comp _ _) |- _ => inversion H; subst; clear H
             | H:Can_write_in _ (Ifte _ _ _) |- _ => inversion H; subst; clear H
             | H:Can_write_in _ Skip |- _ => now inversion H
             | H:Can_write_in _ _ \/ Can_write_in _ _ |- _ => destruct H
             | |- context [equiv_decb ?e1 ?e2] =>
               destruct (equiv_decb e1 e2) eqn:Heq
             | |- Can_write_in _ (Ifte _ _ _) =>
               (apply CWIIfteTrue; apply IHs1_1; now intuition)
               || (apply CWIIfteFalse; apply IHs1_2; now intuition)
             | H:Can_write_in _ (zip _ _) |- _ =>
               apply IHs1_1 in H || apply IHs1_2 in H
             | |- Can_write_in _ (Comp _ (zip _ _)) =>
               now (apply CWIComp2; apply IHs1_2; intuition)
             | _ => intuition
             end.
  Qed.

  Lemma Cannot_write_in_zip:
    forall s1 s2 x,
      (~Can_write_in x s1 /\ ~Can_write_in x s2)
      <-> ~Can_write_in x (zip s1 s2).
  Proof.
    intros s1 s2 x.
    split; intro HH.
    - intro Hcan; apply Can_write_in_zip in Hcan; intuition.
    - split; intro Hcan; apply HH; apply Can_write_in_zip; intuition.
  Qed.
  
  Lemma zip_free_write:
    forall s1 s2,
      Fusible s1
      -> Fusible s2
      -> Fusible (zip s1 s2).
  Proof.
    Hint Constructors Fusible Can_write_in.
    induction s1, s2;
      intros Hfree1 Hfree2;
      inversion_clear Hfree1;
      simpl;
      try now intuition.
    match goal with
    | |- context [equiv_decb ?e1 ?e2] => destruct (equiv_decb e1 e2) eqn:Heq
    end; [|intuition].
    rewrite equiv_decb_equiv in Heq.
    rewrite <-Heq in *.
    inversion_clear Hfree2;
      constructor;
      repeat progress
             match goal with
             | H1:Fusible ?s1,
                 H2:Fusible ?s2,
                 Hi:context [Fusible (zip _ _)]
               |- Fusible (zip ?s1 ?s2)
               => apply Hi with (1:=H1) (2:=H2)
             | |- forall x, Is_free_in_exp x ?e -> _
               => intros x Hfree
             | H1:context [Is_free_in_exp _ ?e -> _ /\ _],
                  H2:Is_free_in_exp _ ?e |- _
               => specialize (H1 _ H2)
             | |- _ /\ _ => split
             | |- ~Can_write_in _ (zip _ _)
               => apply Cannot_write_in_zip; intuition
             | _ => idtac
             end.
  Qed.
  
  Lemma zip_Comp':
    forall s1 s2,
      Fusible s1
      -> (stmt_eval_eq (zip s1 s2) (Comp s1 s2)).
  Proof.
    induction s1, s2;
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
      try (rewrite lift_Ifte; [|assumption]);
      try rewrite Comp_assoc;
      reflexivity.
  Qed.
  
  Lemma fuse'_free_write:
    forall s2 s1,
      Fusible s1
      -> Fusible s2
      -> Fusible (fuse' s1 s2).
  Proof.
    induction s2;
      try (intros; apply zip_free_write; assumption).
    intros s1 Hfree1 Hfree2.
    inversion_clear Hfree2.
    apply IHs2_2; [|assumption].
    apply zip_free_write; assumption.
  Qed.
  
  (** fuse_eval_eq *)
  
  Require Import Relations.
  Require Import Morphisms.
  Require Import Setoid.
  
  Definition fuse_eval_eq s1 s2: Prop :=
    stmt_eval_eq s1 s2 /\ (Fusible s1 /\ Fusible s2).
  
  (*
     Print relation.
     Check (fuse_eval_eq : relation stmt).
   *)

  Lemma fuse_eval_eq_refl:
    forall s,
      Fusible s
      -> Proper fuse_eval_eq s.
  Proof.
    intros s Hfree; unfold Proper, fuse_eval_eq; intuition.
  Qed.
  
  Lemma fuse_eval_eq_trans:
    transitive stmt fuse_eval_eq.
  Proof.
    intros s1 s2 s3 Heq1 Heq2.
    unfold fuse_eval_eq in *.
    split; [|now intuition].
    destruct Heq1 as [Heq1 ?].
    destruct Heq2 as [Heq2 ?].
    rewrite Heq1, Heq2; reflexivity.
  Qed.
  
  Lemma fuse_eval_eq_sym:
    symmetric stmt fuse_eval_eq.
  Proof.
    intros s1 s2 Heq.
    unfold fuse_eval_eq in *.
    split; [|now intuition].
    destruct Heq as [Heq ?].
    rewrite Heq; reflexivity.
  Qed.
  
  Add Relation stmt (fuse_eval_eq)
      symmetry proved by fuse_eval_eq_sym
      transitivity proved by fuse_eval_eq_trans
        as fuse_eval_equiv.
  
  Instance subrelation_stmt_fuse_eval_eq:
    subrelation fuse_eval_eq stmt_eval_eq.
  Proof.
    intros s1 s2 Heq x menv env menv' env'.
    now apply Heq.
  Qed.
  
  Lemma zip_Comp:
    forall s1 s2,
      Fusible s1
      -> Fusible s2
      -> fuse_eval_eq (zip s1 s2) (Comp s1 s2).
  Proof.
    intros s1 s2 Hfree1 Hfree2.
    unfold fuse_eval_eq.
    split; [|split].
    - rewrite zip_Comp' with (1:=Hfree1); reflexivity.
    - apply zip_free_write with (1:=Hfree1) (2:=Hfree2).
    - intuition.
  Qed.

  (* TODO: Why don't we get this automatically via the subrelation? *)
  Instance fuse_eval_eq_Proper:
    Proper (eq ==> eq ==> eq ==> fuse_eval_eq ==> eq ==> iff) stmt_eval.
  Proof.
    intros prog' prog HR1 menv' menv HR2 env' env HR3 s1 s2 Heq r' r HR4;
      subst; destruct r as [menv' env'].
    unfold fuse_eval_eq in Heq.
    destruct Heq as [Heq ?].
    rewrite Heq; reflexivity.
  Qed.
  
  Instance fuse_eval_eq_Comp_Proper:
    Proper (fuse_eval_eq ==> fuse_eval_eq ==> fuse_eval_eq) Comp.
  Proof.
    Hint Constructors Fusible.
    intros s s' Hseq t t' Hteq.
    unfold fuse_eval_eq in *.
    destruct Hseq as [Hseq [Hfrees Hfrees']].
    destruct Hteq as [Hteq [Hfreet Hfreet']].
    split; [|intuition].
    rewrite Hseq, Hteq; reflexivity.
  Qed.
  
  Instance zip_fuse_eval_eq_Proper:
    Proper (fuse_eval_eq ==> fuse_eval_eq ==> fuse_eval_eq) zip.
  Proof.
    intros s s' Hseq t t' Hteq.
    unfold fuse_eval_eq in *.
    destruct Hseq as [Hseq [Hfrees Hfrees']].
    destruct Hteq as [Hteq [Hfreet Hfreet']].
    split; [|split]; [|apply zip_free_write with (1:=Hfrees) (2:=Hfreet)
                      |apply zip_free_write with (1:=Hfrees') (2:=Hfreet')].
    rewrite zip_Comp' with (1:=Hfrees).
    rewrite zip_Comp' with (1:=Hfrees').
    rewrite Hseq, Hteq; reflexivity.
  Qed.
  
  Lemma fuse'_Comp:
    forall s2 s1,
      Fusible s1
      -> Fusible s2
      -> stmt_eval_eq (fuse' s1 s2) (Comp s1 s2).
  Proof.
    Hint Constructors Fusible.
    induction s2;
      intros s1 Hifte1 Hifte2; simpl;
        try now (rewrite zip_Comp'; intuition).
    rewrite Comp_assoc.
    inversion_clear Hifte2.
    rewrite IHs2_2;
      match goal with
      | H1:Fusible ?s1,
      H2:Fusible ?s2 |- Fusible (zip ?s1 ?s2)
        => apply zip_free_write with (1:=H1) (2:=H2)
      | |- Fusible ?s => assumption
      | H:Fusible s2_2 |- _ => pose proof (fuse_eval_eq_refl _ H)
      end.
    intros prog menv env menv' env'.
    rewrite zip_Comp; [now apply iff_refl|assumption|assumption].
  Qed.

  Instance fuse'_fuse_eval_eq_Proper:
    Proper (fuse_eval_eq ==> fuse_eval_eq ==> fuse_eval_eq) fuse'.
  Proof.
    intros s s' Hseq t t' Hteq.
    unfold fuse_eval_eq in *.
    destruct Hseq as [Hseq [Hfrees Hfrees']].
    destruct Hteq as [Hteq [Hfreet Hfreet']].
    split; [|split]; [|apply fuse'_free_write with (1:=Hfrees) (2:=Hfreet)
                      |apply fuse'_free_write with (1:=Hfrees') (2:=Hfreet')].
    repeat rewrite fuse'_Comp; try assumption.
    rewrite Hseq, Hteq.
    reflexivity.
  Qed.

  Lemma fuse_Comp:
    forall s,
      Fusible s
      -> stmt_eval_eq (fuse s) s.
  Proof.
    intros s Hfree prog menv env menv' env'.
    destruct s; simpl; try reflexivity.
    inversion_clear Hfree.
    destruct s2;
      match goal with
      | H: Fusible ?s2 |- context [fuse' _ ?s2]
        => pose proof (fuse_eval_eq_refl _ H)
      end;
      rewrite fuse'_Comp; auto; reflexivity.
  Qed.

  Lemma fuse_call:
    forall p n me me' f xss rs,
      Forall ClassFusible p ->
      stmt_call_eval p me n f xss me' rs ->
      stmt_call_eval (map fuse_class p) me n f xss me' rs.
  Proof.
    cut ((forall p me ve stmt e',
             stmt_eval p me ve stmt e' ->
             Forall ClassFusible p ->
             stmt_eval (map fuse_class p) me ve stmt e')
         /\ (forall p me clsid f vs me' rvs,
                stmt_call_eval p me clsid f vs me' rvs ->
                Forall ClassFusible p ->
                stmt_call_eval (map fuse_class p) me clsid f vs me' rvs)).
    now destruct 1 as (Hf1 & Hf2); intros; apply Hf2; auto.
    apply stmt_eval_call_ind; intros; eauto using stmt_eval.
    pose proof (find_class_In _ _ _ _ H) as Hinp.
    pose proof (find_method_In _ _ _ H0) as Hinc.
    pose proof (find_class_app _ _ _ _ H) as Hprog'.
    apply fuse_find_class in H.
    apply fuse_find_method' in H0.
    econstructor; eauto.
    2:now rewrite fuse_method_out; eassumption.
    rewrite fuse_method_in.
    apply In_Forall with (1:=H4) in Hinp.
    apply In_Forall with (1:=Hinp) in Hinc.
    rewrite fuse_method_body.
    rewrite fuse_Comp with (1:=Hinc).
    apply H2.
    destruct Hprog' as (cls'' & Hprog & Hfind).
    rewrite Hprog in H4.
    apply Forall_app in H4.
    rewrite Forall_cons2 in H4.
    intuition.
  Qed.

  (** ** Fusion preserves well-typing. *)

  Lemma wt_stmt_map_fuse_class:
    forall p objs mems vars body,
      wt_stmt p objs mems vars body ->
      wt_stmt (map fuse_class p) objs mems vars body.
  Proof.
    induction body; inversion_clear 1; eauto using wt_stmt.
    eapply wt_Call
    with (cls:=fuse_class cls) (p':=map fuse_class p') (fm:=fuse_method fm);
      auto; try (now destruct fm; auto).
    erewrite fuse_find_class; eauto.
    now apply fuse_find_method'.
  Qed.

  Lemma wt_stmt_zip:
    forall p objs mems vars s1 s2,
      wt_stmt p objs mems vars s1 ->
      wt_stmt p objs mems vars s2 ->
      wt_stmt p objs mems vars (zip s1 s2).
  Proof.
    induction s1, s2; simpl; repeat inversion_clear 1; eauto using wt_stmt.
    destruct (exp_dec e e0) as [He|Hne].
    - rewrite He, equiv_decb_refl; eauto using wt_stmt.
    - apply not_equiv_decb_equiv in Hne. rewrite Hne. eauto using wt_stmt.
  Qed.

  Lemma zip_wt:
    forall p insts mems vars s1 s2,
      wt_stmt p insts mems vars s1 ->
      wt_stmt p insts mems vars s2 ->
      wt_stmt p insts mems vars (zip s1 s2).
  Proof.
    induction s1, s2; simpl;
      try match goal with |- context [if ?e1 ==b ?e2 then _ else _] =>
                          destruct (equiv_decb e1 e2) end;
      auto with obctyping;
      inversion_clear 1;
      try inversion_clear 2;
      auto with obctyping.
    inversion_clear 1.
    auto with obctyping.
  Qed.

  Lemma fuse_wt:
    forall p insts mems vars s,
      wt_stmt p insts mems vars s ->
      wt_stmt p insts mems vars (fuse s).
  Proof.
    intros ** WTs.
    destruct s; auto; simpl; inv WTs.
    match goal with H1:wt_stmt _ _ _ _ s1, H2:wt_stmt _ _ _ _ s2 |- _ =>
                    revert s2 s1 H1 H2 end.
    induction s2; simpl; auto using zip_wt.
    intros s2 WTs1 WTcomp.
    inv WTcomp.
    apply IHs2_2; auto.
    apply zip_wt; auto.
  Qed.

  Lemma fuse_wt_program:
    forall G,
      wt_program G ->
      wt_program (map fuse_class G).
  Proof.
    intros ** WTG.
    induction G as [|c p]; simpl;
      inversion_clear WTG as [|? ? Wtc Wtp Nodup]; constructor; auto.
    - inversion_clear Wtc as (Hos & Hms).
      constructor.
      + rewrite fuse_class_c_objs.
        apply Forall_impl_In with (2:=Hos).
        intros ic Hin Hfind.
        apply not_None_is_Some in Hfind.
        destruct Hfind as ((cls & p') & Hfind).
        rewrite fuse_find_class with (1:=Hfind).
        discriminate.
      + destruct c; simpl in *.
        clear Nodup c_nodup0 c_nodupm0 Hos IHp Wtp.
        induction c_methods0 as [|m ms]; simpl; auto using Forall_nil.
        apply Forall_cons2 in Hms.
        destruct Hms as (WTm & WTms).
        apply Forall_cons; auto. clear IHms WTms.
        unfold wt_method in *.
        destruct m; unfold meth_vars in *; simpl in *.
        clear m_nodupvars0 m_good0.
        apply wt_stmt_map_fuse_class.
        destruct m_body0; simpl; inv WTm; eauto using wt_stmt.
        revert m_body0_1 H1.
        induction m_body0_2; simpl; eauto using wt_stmt_zip.
        intros s1 WT1. inv H2.
        eauto using wt_stmt_zip.
    - simpl.
      now rewrite fuse_class_c_name, map_map, map_fuse_class_c_name.
  Qed.

  Lemma fuse_wt_mem:
    forall me p c,
      wt_mem me p c ->
      wt_mem me (map fuse_class p) (fuse_class c).
  Proof.
    intros ** Hwt_mem.
    induction Hwt_mem
              using wt_mem_ind_mult
    with (P := fun me p cl Hwt => wt_mem me (map fuse_class p) (fuse_class cl))
         (Pinst := fun me p oc Hwt_inst => wt_mem_inst me (map fuse_class p) oc).
    - constructor.
      + rewrite fuse_class_c_mems; auto.
      + rewrite fuse_class_c_objs.
        eapply Forall_forall; intros oc Hin.
        eapply In_Forall in H as [? ?]; eauto.
    - now constructor.
    - simpl in *.
      econstructor 2; eauto.
      apply fuse_find_class. eauto.
  Qed.
  
End FUSION.

Module FusionFun
       (Import Ids  : IDS)
       (Import Op   : OPERATORS)
       (Import OpAux: OPERATORS_AUX Op)
       (Import SynObc: Velus.Obc.ObcSyntax.OBCSYNTAX Ids Op OpAux)
       (Import SemObc: Velus.Obc.ObcSemantics.OBCSEMANTICS Ids Op OpAux SynObc)
       (Import TypObc: Velus.Obc.ObcTyping.OBCTYPING Ids Op OpAux SynObc SemObc)
       (Import Equ  : Velus.Obc.Equiv.EQUIV Ids Op OpAux SynObc SemObc)
       <: FUSION Ids Op OpAux SynObc SemObc TypObc Equ.

  Include FUSION Ids Op OpAux SynObc SemObc TypObc Equ.

End FusionFun.

