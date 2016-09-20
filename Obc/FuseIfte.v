Require Import Coq.FSets.FMapPositive.
Require Import PArith.
Require Import Rustre.Common.
Require Import Rustre.Operators.
Require Import Rustre.Obc.
Require Import Rustre.Dataflow.Syntax.
Require Import Rustre.RMemory.

Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Ltac inv H := inversion H; subst; clear H.

Module Type FUSEIFTE
       (Import Ids  : IDS)
       (Import Op   : OPERATORS)
       (Import OpAux: OPERATORS_AUX Op)
       (Import SynDF: Rustre.Dataflow.Syntax.SYNTAX Ids Op)
       (Import SynMP: Rustre.Obc.Syntax.SYNTAX Ids Op OpAux)
       (Import SemMP: Rustre.Obc.Semantics.SEMANTICS Ids Op OpAux SynMP)
       (Import Equ  : Rustre.Obc.Equiv.EQUIV Ids Op OpAux SynMP SemMP).

  Inductive Is_free_in_exp : ident -> exp -> Prop :=
  | FreeVar: forall i ty,
      Is_free_in_exp i (Var i ty)
  | FreeState: forall i ty,
      Is_free_in_exp i (State i ty)
  | FreeUnop: forall i op e ty,
      Is_free_in_exp i e ->
      Is_free_in_exp i (Unop op e ty)
  |FreeBinop: forall i op e1 e2 ty,
      Is_free_in_exp i e1 \/ Is_free_in_exp i e2 ->
      Is_free_in_exp i (Binop op e1 e2 ty).

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
      InMembers x xs ->
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

  Lemma not_free_aux1 : forall i op e ty,
      ~Is_free_in_exp i (Unop op e ty) ->
      ~Is_free_in_exp i e.
  Proof.
    intros i op e ty Hfree H; apply Hfree. now constructor. 
  Qed.
  
  Lemma not_free_aux2 : forall i op e1 e2 ty,
      ~Is_free_in_exp i (Binop op e1 e2 ty) ->
      ~Is_free_in_exp i e1 /\ ~Is_free_in_exp i e2.
  Proof.
    intros i op e1 e2 ty Hfree; split; intro H; apply Hfree;
      constructor; [now left | now right].
  Qed.

  Ltac not_free :=
    lazymatch goal with
    | H : ~Is_free_in_exp ?x (Var ?i ?ty) |- _ =>
        let HH := fresh in
        assert (HH : i <> x) by (intro; subst; apply H; constructor);
        clear H; rename HH into H
    | H : ~Is_free_in_exp ?x (State ?i ?ty) |- _ =>
        let HH := fresh in
        assert (HH : i <> x) by (intro; subst; apply H; constructor);
        clear H; rename HH into H
    | H : ~Is_free_in_exp ?x (Unop ?op ?e ?ty) |- _ =>
        apply not_free_aux1 in H
    | H : ~Is_free_in_exp ?x (Binop ?op ?e1 ?e2 ?ty) |- _ =>
        destruct (not_free_aux2 x op e1 e2 ty H)
    end.

  (** If we add irrelevent values to [env], evaluation does not change. *)
  Lemma exp_eval_extend_env : forall mem env x v' e v,
      ~Is_free_in_exp x e -> exp_eval mem env e v -> exp_eval mem (PM.add x v' env) e v.
  Proof.
    intros mem env x v' e.
    induction e (* using exp_ind2 *); intros v1 Hfree Heval.
    - inv Heval. constructor. not_free. now rewrite PM.gso.
    - inv Heval. now constructor.
    - inv Heval. constructor.
    - inv Heval. constructor 4 with c; trivial.
      not_free.
      now apply IHe.
    - inv Heval. constructor 5 with (c1 := c1) (c2 := c2); trivial; not_free.
      + now apply IHe1.
      + now apply IHe2.
  Qed.

  (** If we add irrelevent values to [mem], evaluation does not change. *)
  Lemma exp_eval_extend_mem : forall mem env x v' e v,
      ~Is_free_in_exp x e -> exp_eval mem env e v -> exp_eval (madd_mem x v' mem) env e v.
  Proof.
    intros mem env x v' e.
    induction e (* using exp_ind2 *); intros v1 Hfree Heval.
    - inversion_clear Heval. now constructor.
    - inversion_clear Heval. constructor. not_free. now rewrite mfind_mem_gso.
    - inversion_clear Heval. constructor.
    - inversion_clear Heval. constructor 4 with c; trivial.
      not_free.
      now apply IHe.
    - inv Heval. constructor 5 with (c1 := c1) (c2 := c2); trivial; not_free.
      + now apply IHe1.
      + now apply IHe2.
  Qed.

  (** If we add objects to [mem], evaluation does not change. *)
  Lemma exp_eval_extend_mem_by_obj : forall mem env f obj e v,
      exp_eval mem env e v -> exp_eval (madd_obj f obj mem) env e v.
  Proof.
    intros mem env f v' e.
    induction e (* using exp_ind2 *); intros v1 Heval.
    - inversion_clear Heval. now constructor.
    - inversion_clear Heval. constructor. now rewrite mfind_mem_add_inst.
    - inversion_clear Heval. constructor.
    - inversion_clear Heval. constructor 4 with c; trivial.
      now apply IHe.
    - inv Heval. constructor 5 with (c1 := c1) (c2 := c2); trivial.
      + now apply IHe1.
      + now apply IHe2.
  Qed.

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
      clear Heq. induction lr as [|x lr]; [easy|].
      destruct x as [[x ty]].
      apply exp_eval_extend_env.
      + intro HH; apply (Hfree x HH).
        constructor.
        apply In_InMembers with (b:=ty).
        change (In (fst ((x, ty), v0)) l).
        apply Hin. now constructor.
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

  Inductive IsFusible : stmt -> Prop :=
  | IFAssign: forall x e,
      IsFusible (Assign x e)
  | IFAssignSt: forall x e,
      IsFusible (AssignSt x e)
  | IFIfte: forall e s1 s2,
      IsFusible s1 ->
      IsFusible s2 ->
      (forall x, Is_free_in_exp x e -> ~Can_write_in x s1 /\ ~Can_write_in x s2) ->
      IsFusible (Ifte e s1 s2)
  | IFStep_ap: forall xs cls i f es,
      IsFusible (Call xs cls i f es)
  | IFComp: forall s1 s2,
      IsFusible s1 ->
      IsFusible s2 ->
      IsFusible (Comp s1 s2)
  | IFSkip:
      IsFusible Skip.

  Lemma lift_IsFusible:
    forall e s1 s2 t1 t2,
      IsFusible (Comp (Ifte e s1 s2) (Ifte e t1 t2))
      <->
      IsFusible (Ifte e (Comp s1 t1) (Comp s2 t2)).
  Proof.
    Hint Constructors IsFusible.
    intros e s1 s2 t1 t2.
    split; intro Hifw.
    - inversion_clear Hifw as [| | | |? ? Hs Ht|].
      constructor; inversion_clear Hs; inversion_clear Ht; now cannot_write.
    - inversion_clear Hifw as [| |? ? ? Hfree1 Hfree2 Hcw| | | ].
      inversion_clear Hfree1; inversion_clear Hfree2.
      repeat constructor; cannot_write.
  Qed.

  Lemma IsFusible_fold_left_shift:
    forall A f (xs : list A) iacc,
      IsFusible (fold_left (fun i x => Comp (f x) i) xs iacc)
      <->
      (IsFusible (fold_left (fun i x => Comp (f x) i) xs Skip)
       /\ IsFusible iacc).
  Proof.
    Hint Constructors IsFusible.
    induction xs as [|x xs IH]; [now intuition|].
    intros; split.
    - intro HH. simpl in HH. apply IH in HH.
      destruct HH as [Hxs Hiacc].
      split; [simpl; rewrite IH|];
        repeat progress match goal with
                        | H:IsFusible (Comp _ _) |- _ => inversion_clear H
                        | _ => now intuition
                        end.
    - intros [HH0 HH1].
      simpl in HH0; rewrite IH in HH0.
      simpl; rewrite IH.
      intuition.
      repeat progress match goal with
                      | H:IsFusible (Comp _ _) |- _ => inversion_clear H
                      | _ => now intuition
                      end.
  Qed.

  (*
   The property "IsFusible (translate_eqns mems eqs)" is obtained above
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
   IsFusible. We could imagine a weaker invariant that allows the
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
      IsFusible s1
      -> IsFusible s2
      -> IsFusible (zip s1 s2).
  Proof.
    Hint Constructors IsFusible Can_write_in.
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
             | H1:IsFusible ?s1,
                 H2:IsFusible ?s2,
                 Hi:context [IsFusible (zip _ _)]
               |- IsFusible (zip ?s1 ?s2)
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
      IsFusible s1
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
             | H:IsFusible ?s1,
                 IH:context [stmt_eval_eq (zip ?s1 _) _]
               |- context [zip ?s1 ?s2]
               => rewrite IH with (1:=H)
             end;
      try (rewrite lift_Ifte; [|assumption]);
      try rewrite Comp_assoc;
      reflexivity.
  Qed.
  
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

  Lemma fuse'_free_write:
    forall s2 s1,
      IsFusible s1
      -> IsFusible s2
      -> IsFusible (fuse' s1 s2).
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
    stmt_eval_eq s1 s2 /\ (IsFusible s1 /\ IsFusible s2).
  
  (*
     Print relation.
     Check (fuse_eval_eq : relation stmt).
   *)

  Lemma fuse_eval_eq_refl:
    forall s,
      IsFusible s
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
      IsFusible s1
      -> IsFusible s2
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
    Hint Constructors IsFusible.
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
      IsFusible s1
      -> IsFusible s2
      -> stmt_eval_eq (fuse' s1 s2) (Comp s1 s2).
  Proof.
    Hint Constructors IsFusible.
    induction s2;
      intros s1 Hifte1 Hifte2; simpl;
        try now (rewrite zip_Comp'; intuition).
    rewrite Comp_assoc.
    inversion_clear Hifte2.
    rewrite IHs2_2;
      match goal with
      | H1:IsFusible ?s1,
      H2:IsFusible ?s2 |- IsFusible (zip ?s1 ?s2)
        => apply zip_free_write with (1:=H1) (2:=H2)
      | |- IsFusible ?s => assumption
      | H:IsFusible s2_2 |- _ => pose proof (fuse_eval_eq_refl _ H)
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
      IsFusible s
      -> stmt_eval_eq (fuse s) s.
  Proof.
    intros s Hfree prog menv env menv' env'.
    destruct s; simpl; try reflexivity.
    inversion_clear Hfree.
    destruct s2;
      match goal with
      | H: IsFusible ?s2 |- context [fuse' _ ?s2]
        => pose proof (fuse_eval_eq_refl _ H)
      end;
      rewrite fuse'_Comp; auto; reflexivity.
  Qed.

End FUSEIFTE.

Module FuseIfteFun
       (Import Ids  : IDS)
       (Import Op   : OPERATORS)
       (Import OpAux: OPERATORS_AUX Op)
       (Import SynDF: Rustre.Dataflow.Syntax.SYNTAX Ids Op)
       (Import SynMP: Rustre.Obc.Syntax.SYNTAX Ids Op OpAux)
       (Import SemMP: Rustre.Obc.Semantics.SEMANTICS Ids Op OpAux SynMP)
       (Import Equ  : Rustre.Obc.Equiv.EQUIV Ids Op OpAux SynMP SemMP)
       <: FUSEIFTE Ids Op OpAux SynDF SynMP SemMP Equ.

  Include FUSEIFTE Ids Op OpAux SynDF SynMP SemMP Equ.

End FuseIfteFun.
