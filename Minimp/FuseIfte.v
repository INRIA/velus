
Require Import Coq.FSets.FMapPositive.
Require Import PArith.
Require Import Rustre.Common.
Require Import Rustre.Minimp.Syntax.
Require Import Rustre.Minimp.Semantics.
Require Import Rustre.Minimp.Equiv.
Require Import Rustre.Dataflow.Syntax.
Require Import Rustre.Dataflow.Memories.
Require Import Rustre.Dataflow.IsFree.
Require Import Rustre.Dataflow.IsDefined.
Require Import Rustre.Dataflow.IsVariable.
Require Import Rustre.Dataflow.WellFormed.
Require Import Rustre.Memory.


Ltac inv H := inversion H; subst; clear H.


Inductive Is_free_in_exp : ident -> exp -> Prop :=
| FreeVar: forall i,
    Is_free_in_exp i (Var i)
| FreeState: forall i,
    Is_free_in_exp i (State i)
| FreeOp: forall i op es,
    Nelist.Exists (Is_free_in_exp i) es ->
    Is_free_in_exp i (Op op es).

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
| CWIStep_ap: forall x cls obj e,
    Can_write_in x (Step_ap x cls obj e)
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

(* Lionel: My own tactic because I don't want to break Tim's. *)
Lemma not_free_aux : forall i op es,
  ~Is_free_in_exp i (Op op es) -> Nelist.Forall (fun e => ~Is_free_in_exp i e) es.
Proof.
intros i op es Hfree. induction es.
+ constructor. intro Habs. apply Hfree. now do 2 constructor.
+ constructor.
  - intro Habs. apply Hfree. now do 2 constructor.
  - apply IHes. intro Habs. inversion_clear Habs.
    apply Hfree. constructor. now constructor 3.
Qed.

Ltac not_free :=
  lazymatch goal with
    | H : ~Is_free_in_exp ?x (Var ?i) |- _ => let HH := fresh in
        assert (HH : i <> x) by (intro; subst; apply H; constructor);
        clear H; rename HH into H
    | H : ~Is_free_in_exp ?x (State ?i) |- _ => let HH := fresh in
        assert (HH : i <> x) by (intro; subst; apply H; constructor);
        clear H; rename HH into H
    | H : ~Is_free_in_exp ?x (Op ?op ?es) |- _ => apply not_free_aux in H
  end.

(** If we add irrelevent values to [env], evaluation does not change. *)
Lemma exp_eval_extend_env : forall mem env x v' e v,
  ~Is_free_in_exp x e -> exp_eval mem env e v -> exp_eval mem (PM.add x v' env) e v.
Proof.
intros mem env x v' e.
induction e using exp_ind2; intros v Hfree Heval.
+ inv Heval. constructor. not_free. now rewrite PM.gso.
+ inv Heval. now constructor.
+ inv Heval. constructor.
+ inv Heval. constructor 4 with cs; trivial.
  not_free.
  assert (Hrec : Nelist.Forall (fun e => forall v,
          exp_eval mem env e v -> exp_eval mem (PM.add x v' env) e v) es).
  { rewrite Nelist.Forall_forall in IHes, Hfree |- *. intros. apply IHes; trivial. now apply Hfree. }
  clear IHes Hfree H3. revert cs H1.
  induction es; intros cs Hes; inv Hrec; inv Hes; constructor; auto.
Qed.

(** If we add irrelevent values to [mem], evaluation does not change. *)
Lemma exp_eval_extend_mem : forall mem env x v' e v,
  ~Is_free_in_exp x e -> exp_eval mem env e v -> exp_eval (madd_mem x v' mem) env e v.
Proof.
intros mem env x v' e.
induction e using exp_ind2; intros v Hfree Heval.
+ inversion_clear Heval. now constructor.
+ inversion_clear Heval. constructor. not_free. now rewrite mfind_mem_gso.
+ inversion_clear Heval. constructor.
+ inversion_clear Heval. constructor 4 with cs; trivial.
  not_free.
  assert (Hrec : Nelist.Forall (fun e => forall v,
          exp_eval mem env e v -> exp_eval (madd_mem x v' mem) env e v) es).
  { rewrite Nelist.Forall_forall in IHes, Hfree |- *. intros. apply IHes; trivial. now apply Hfree. }
  clear IHes Hfree H0. revert cs H.
  induction es; intros cs Hes; inv Hrec; inv Hes; constructor; auto.
Qed.

(** If we add objcets to [mem], evaluation does not change. *)
Lemma exp_eval_extend_mem_by_obj : forall mem env f obj e v,
  exp_eval mem env e v -> exp_eval (madd_obj f obj mem) env e v.
Proof.
intros mem env f v' e.
induction e using exp_ind2; intros v Heval.
+ inversion_clear Heval. now constructor.
+ inversion_clear Heval. constructor. now rewrite mfind_mem_add_inst.
+ inversion_clear Heval. constructor.
+ inversion_clear Heval. constructor 4 with cs; trivial.
  assert (Hrec : Nelist.Forall (fun e => forall v,
          exp_eval mem env e v -> exp_eval (madd_obj f v' mem) env e v) es).
  { rewrite Nelist.Forall_forall in IHes |- *. intros. now apply IHes. }
  clear IHes H0. revert cs H.
  induction es; intros cs Hes; inv Hrec; inv Hes; constructor; auto.
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
  - inv Hstmt; solve [eapply IHs1; eassumption || cannot_write | eapply IHs2; eassumption || cannot_write].
  - inv Hstmt.
    apply exp_eval_extend_env, exp_eval_extend_mem_by_obj; trivial.
    intro Habs. apply (Hfree i); auto.
  - inv Hstmt.
    now apply exp_eval_extend_mem_by_obj.
  - inv Hstmt.
    match goal with
    | Hs1: stmt_eval _ _ _ s1 _,
      Hs2: stmt_eval _ _ _ s2 _ |- _
      => apply IHs1 with (2:=Hexp) in Hs1;
         [apply IHs2 with (2:=Hs1) (3:=Hs2)|];
         now cannot_write
    end.
  - now inv Hstmt.
Qed.

Lemma lift_Ifte:
  forall e s1 s2 t1 t2,
    (forall x, Is_free_in_exp x e
               -> (~Can_write_in x s1 /\ ~Can_write_in x s2))
    -> stmt_eval_eq (Comp (Ifte e s1 s2) (Ifte e t1 t2))
                    (Ifte e (Comp s1 t1) (Comp s2 t2)).
Proof.
  intros prog e s1 s2 t1 t2 menv env menv' env' Hfw.
  split; intro Hstmt.
  - inversion_clear Hstmt as [| | | |? ? ? ? ? env'' menv'' ? ? Hs Ht| | | ].
    inversion_clear Hs as [| | | | |? ? ? ? ? ? ? ? Hexp Hs1
                                   |? ? ? ? ? ? ? ? Hexp Hs2| ];
    inversion_clear Ht as [| | | | |? ? ? ? ? ? ? ? Hexp' Ht1
                                   |? ? ? ? ? ? ? ? Hexp' Ht2| ].
    + constructor; [now apply Hexp|].
      econstructor; [now apply Hs1|now apply Ht1].
    + apply cannot_write_exp_eval with (2:=Hexp) in Hs1; [|now cannot_write].
      apply exp_eval_det with (1:=Hexp') in Hs1; discriminate.
    + apply cannot_write_exp_eval with (2:=Hexp) in Hs2; [|now cannot_write].
      apply exp_eval_det with (1:=Hexp') in Hs2; discriminate.
    + constructor 7; [now apply Hexp|].
      econstructor; [now apply Hs2|now apply Ht2].
  - inversion_clear Hstmt as [| | | | |? ? ? ? ? ? ? ? Hexp Hs|
                              ? ? ? ? ? ? ? ? Hexp Hs|].
    + inversion_clear Hs
        as [| | | |? ? ? ? ? env'' menv'' ? ? Hs1 Ht1| | | ].
      apply Icomp with (menv1:=menv'') (env1:=env'').
      apply Iifte_true with (1:=Hexp) (2:=Hs1).
      apply cannot_write_exp_eval with (2:=Hexp) in Hs1; [|now cannot_write].
      apply Iifte_true with (1:=Hs1) (2:=Ht1).
    + inversion_clear Hs
        as [| | | |? ? ? ? ? env'' menv'' ? ? Hs2 Ht2| | | ].
      apply Icomp with (menv1:=menv'') (env1:=env'').
      apply Iifte_false with (1:=Hexp) (2:=Hs2).
      apply cannot_write_exp_eval with (2:=Hexp) in Hs2; [|now cannot_write].
      apply Iifte_false with (1:=Hs2) (2:=Ht2).
Qed.

Inductive Is_fusible : stmt -> Prop :=
| IFWAssign: forall x e,
    Is_fusible (Assign x e)
| IFWAssignSt: forall x e,
    Is_fusible (AssignSt x e)
| IFWIfte: forall e s1 s2,
    Is_fusible s1 ->
    Is_fusible s2 ->
    (forall x, Is_free_in_exp x e -> ~Can_write_in x s1 /\ ~Can_write_in x s2) ->
    Is_fusible (Ifte e s1 s2)
| IFWStep_ap: forall x cls obj e,
    Is_fusible (Step_ap x cls obj e)
| IFWComp: forall s1 s2,
    Is_fusible s1 ->
    Is_fusible s2 ->
    Is_fusible (Comp s1 s2)
| IFWSkip:
    Is_fusible Skip.

Lemma lift_Is_fusible:
  forall e s1 s2 t1 t2,
    Is_fusible (Comp (Ifte e s1 s2) (Ifte e t1 t2))
    <->
    Is_fusible (Ifte e (Comp s1 t1) (Comp s2 t2)).
Proof.
  Hint Constructors Is_fusible.
  intros e s1 s2 t1 t2.
  split; intro Hifw.
  - inversion_clear Hifw as [| | | |? ? Hs Ht|].
    constructor; inversion_clear Hs; inversion_clear Ht; now cannot_write.
  - inversion_clear Hifw as [| |? ? ? Hfree1 Hfree2 Hcw| | | ].
    inversion_clear Hfree1; inversion_clear Hfree2.
    repeat constructor; cannot_write.
Qed.

Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Lemma Is_fusible_fold_left_shift:
  forall A f (xs : list A) iacc,
    Is_fusible (fold_left (fun i x => Comp (f x) i) xs iacc)
    <->
    (Is_fusible (fold_left (fun i x => Comp (f x) i) xs Skip)
     /\ Is_fusible iacc).
Proof.
  Hint Constructors Is_fusible.
  induction xs as [|x xs IH]; [now intuition|].
  intros; split.
  - intro HH. simpl in HH. apply IH in HH.
    destruct HH as [Hxs Hiacc].
    split; [simpl; rewrite IH|];
    repeat progress match goal with
    | H:Is_fusible (Comp _ _) |- _ => inversion_clear H
    | _ => now intuition
    end.
  - intros [HH0 HH1].
    simpl in HH0; rewrite IH in HH0.
    simpl; rewrite IH.
    intuition.
    repeat progress match goal with
    | H:Is_fusible (Comp _ _) |- _ => inversion_clear H
    | _ => now intuition
    end.
Qed.

(*
   The property "Is_fusible (translate_eqns mems eqs)" is obtained above
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
   Is_fusible. We could imagine a weaker invariant that allows the
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
      if exp_eqb e1 e2
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
           | |- context [exp_eqb ?e1 ?e2] =>
             destruct (exp_eqb e1 e2) eqn:Heq;
               [apply exp_eqb_eq in Heq; subst|]
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
    Is_fusible s1
    -> Is_fusible s2
    -> Is_fusible (zip s1 s2).
Proof.
  Hint Constructors Is_fusible Can_write_in.
  induction s1, s2;
    intros Hfree1 Hfree2;
    inversion_clear Hfree1;
    simpl;
    try now intuition.
  match goal with
  | |- context [exp_eqb ?e1 ?e2] => destruct (exp_eqb e1 e2) eqn:Heq
  end; [|intuition].
  apply exp_eqb_eq in Heq; subst.
  inversion_clear Hfree2;
  constructor;
    repeat progress
           match goal with
           | H1:Is_fusible ?s1,
             H2:Is_fusible ?s2,
             Hi:context [Is_fusible (zip _ _)]
             |- Is_fusible (zip ?s1 ?s2)
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
    Is_fusible s1
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
         | |- context [exp_eqb ?e1 ?e2]
           => destruct (exp_eqb e1 e2) eqn:Heq;
             [apply exp_eqb_eq in Heq; subst|]
         | H:Is_fusible ?s1,
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
    Is_fusible s1
    -> Is_fusible s2
    -> Is_fusible (fuse' s1 s2).
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
  stmt_eval_eq s1 s2 /\ (Is_fusible s1 /\ Is_fusible s2).

(*
Print relation.
Check (fuse_eval_eq : relation stmt).
 *)

Lemma fuse_eval_eq_refl:
  forall s,
    Is_fusible s
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
    Is_fusible s1
    -> Is_fusible s2
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
  Hint Constructors Is_fusible.
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
    Is_fusible s1
    -> Is_fusible s2
    -> stmt_eval_eq (fuse' s1 s2) (Comp s1 s2).
Proof.
  Hint Constructors Is_fusible.
  induction s2;
  intros s1 Hifte1 Hifte2; simpl;
  try now (rewrite zip_Comp'; intuition).
  rewrite Comp_assoc.
  inversion_clear Hifte2.
  rewrite IHs2_2;
    match goal with
    | H1:Is_fusible ?s1,
      H2:Is_fusible ?s2 |- Is_fusible (zip ?s1 ?s2)
      => apply zip_free_write with (1:=H1) (2:=H2)
    | |- Is_fusible ?s => assumption
    | H:Is_fusible s2_2 |- _ => pose proof (fuse_eval_eq_refl _ H)
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
    Is_fusible s
    -> stmt_eval_eq (fuse s) s.
Proof.
  intros s Hfree prog menv env menv' env'.
  destruct s; simpl; try reflexivity.
  inversion_clear Hfree.
  destruct s2;
  match goal with
  | H: Is_fusible ?s2 |- context [fuse' _ ?s2]
    => pose proof (fuse_eval_eq_refl _ H)
  end;
  rewrite fuse'_Comp; auto; reflexivity.
Qed.

(*
Open Scope positive_scope.
Eval cbv in (fuse (Comp (Ifte (Var 1) (Assign 2 (Const (Cint 7))) Skip)
                             (Comp (Ifte (Var 1) (Assign 4 (Var 2))
                                         (Assign 4 (State 3)))
                                   (Comp (Ifte (Var 1) Skip
                                               (Ifte (Var 2)
                                                     (AssignSt 3 (Var 2))
                                                     Skip))
                                         (Comp (Ifte (Var 1)
                                                     Skip
                                                     (Ifte (Var 2)
                                                           (AssignSt 3 (Var 4))
                                                           Skip)) Skip))))).
*)

