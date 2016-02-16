
Require Import Coq.FSets.FMapPositive.
Require Import PArith.
Require Import Rustre.Common.
Require Import Rustre.Minimp.Syntax.
Require Import Rustre.Minimp.Semantics.
Require Import Rustre.Dataflow.Syntax.
Require Import Rustre.Dataflow.Memories.
Require Import Rustre.Dataflow.IsFree.
Require Import Rustre.Dataflow.IsDefined.
Require Import Rustre.Dataflow.IsVariable.
Require Import Rustre.Dataflow.WellFormed.

Require Import Rustre.Translation.
Require Import Rustre.Correctness.
Require Import Heap.

Inductive Is_free_in_exp : ident -> exp -> Prop :=
| FreeVar: forall i,
    Is_free_in_exp i (Var i)
| FreeState: forall i,
    Is_free_in_exp i (State i).

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
    Can_write_in x (Comp s1 s2)
| CWIRepeat: forall x n s,
    Can_write_in x s ->
    Can_write_in x (Repeat n s).

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

Lemma cannot_write_in_Repeat:
  forall x s n,
    ~Can_write_in x s <-> ~Can_write_in x (Repeat n s).
Proof.
  Hint Constructors Can_write_in.
  intros; split; [|intuition].
  intros Hs HH; inversion_clear HH; intuition.
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
  - inversion Hstmt; subst; clear Hstmt.
    induction e; inversion Hexp; subst; intuition;
    constructor; (rewrite PM.gso; [now assumption|intro HH; subst; now eauto]).
  - inversion Hstmt; subst; clear Hstmt.
    induction e; inversion Hexp; subst; intuition;
    constructor; (rewrite mfind_mem_gso; [assumption|intro HH; subst; now eauto]).
  - inversion Hstmt; subst; clear Hstmt.
    match goal with
    | Hstmt: stmt_eval prog menv env s1 _ |- _
      => apply IHs1 with (2:=Hexp) (3:=Hstmt); now cannot_write
    end.
    match goal with
    | Hstmt: stmt_eval prog menv env s2 _ |- _
      => apply IHs2 with (2:=Hexp) (3:=Hstmt); now cannot_write
    end.
  - inversion Hstmt; subst; clear Hstmt.
    induction e'; inversion Hexp; subst; intuition;
    constructor; (rewrite PM.gso; [assumption|intro HH; subst; now eauto]).
  - inversion Hstmt; subst; clear Hstmt.
    induction e'; inversion_clear Hexp; intuition.
  - inversion Hstmt; subst; clear Hstmt.
    match goal with
    | Hs1: stmt_eval _ _ _ s1 _,
      Hs2: stmt_eval _ _ _ s2 _ |- _
      => apply IHs1 with (2:=Hexp) in Hs1;
         [apply IHs2 with (2:=Hs1) (3:=Hs2)|];
         now cannot_write
    end.
  - revert menv env menv' env' Hfree Hexp Hstmt.
    induction n; intros menv env menv' env' Hfree Hexp Hstmt.
    + inversion Hstmt; subst; assumption.
    + inversion_clear Hstmt.
      match goal with
      | Hsr: stmt_eval _ _ _ (Repeat n s) _ |- _
        => apply IHn with (2:=Hexp) in Hsr;
          [clear Hexp; rename Hsr into Hexp|]
      end.
      match goal with
      | Hs: stmt_eval _ _ _ s _ |- _
        => apply IHs with (2:=Hexp) (3:=Hs); now cannot_write
      end.
      intros x Hfree' Hcw.
      inversion_clear Hcw.
      apply Hfree with (1:=Hfree').
      intuition.
  - inversion Hstmt; subst; assumption.
Qed.

Lemma lift_Ifte:
  forall prog e s1 s2 t1 t2 menv env menv' env',
    (forall x, Is_free_in_exp x e
               -> (~Can_write_in x s1 /\ ~Can_write_in x s2))
    -> (stmt_eval prog menv env (Comp (Ifte e s1 s2) (Ifte e t1 t2))
                  (menv', env')
        <->
        stmt_eval prog menv env (Ifte e (Comp s1 t1) (Comp s2 t2))
                  (menv', env')).
Proof.
  intros prog e s1 s2 t1 t2 menv env menv' env' Hfw.
  split; intro Hstmt.
  - inversion_clear Hstmt as [| | | |? ? ? ? ? env'' menv'' ? ? Hs Ht| | | | |].
    inversion_clear Hs as [| | | | |? ? ? ? ? ? ? ? Hexp Hs1
                                   |? ? ? ? ? ? ? ? Hexp Hs2| | | ];
    inversion_clear Ht as [| | | | |? ? ? ? ? ? ? ? Hexp' Ht1
                                   |? ? ? ? ? ? ? ? Hexp' Ht2| | | ].
    + constructor; [now apply Hexp|].
      econstructor; [now apply Hs1|now apply Ht1].
    + apply cannot_write_exp_eval with (2:=Hexp) in Hs1; [|now cannot_write].
      apply exp_eval_det with (1:=Hexp') in Hs1; discriminate.
    + apply cannot_write_exp_eval with (2:=Hexp) in Hs2; [|now cannot_write].
      apply exp_eval_det with (1:=Hexp') in Hs2; discriminate.
    + constructor 7; [now apply Hexp|].
      econstructor; [now apply Hs2|now apply Ht2].
  - inversion_clear Hstmt as [| | | | |? ? ? ? ? ? ? ? Hexp Hs|
                              ? ? ? ? ? ? ? ? Hexp Hs| | |].
    + inversion_clear Hs
        as [| | | |? ? ? ? ? env'' menv'' ? ? Hs1 Ht1| | | | |].
      apply Icomp with (menv1:=menv'') (env1:=env'').
      apply Iifte_true with (1:=Hexp) (2:=Hs1).
      apply cannot_write_exp_eval with (2:=Hexp) in Hs1; [|now cannot_write].
      apply Iifte_true with (1:=Hs1) (2:=Ht1).
    + inversion_clear Hs
        as [| | | |? ? ? ? ? env'' menv'' ? ? Hs2 Ht2| | | | |].
      apply Icomp with (menv1:=menv'') (env1:=env'').
      apply Iifte_false with (1:=Hexp) (2:=Hs2).
      apply cannot_write_exp_eval with (2:=Hexp) in Hs2; [|now cannot_write].
      apply Iifte_false with (1:=Hs2) (2:=Ht2).
Qed.

Inductive Ifte_free_write : stmt -> Prop :=
| IFWAssign: forall x e,
    Ifte_free_write (Assign x e)
| IFWAssignSt: forall x e,
    Ifte_free_write (AssignSt x e)
| IFWIfte: forall e s1 s2,
    Ifte_free_write s1 ->
    Ifte_free_write s2 ->
    (forall x, Is_free_in_exp x e -> ~Can_write_in x s1 /\ ~Can_write_in x s2) ->
    Ifte_free_write (Ifte e s1 s2)
| IFWStep_ap: forall x cls obj e,
    Ifte_free_write (Step_ap x cls obj e)
| IFWComp: forall s1 s2,
    Ifte_free_write s1 ->
    Ifte_free_write s2 ->
    Ifte_free_write (Comp s1 s2)
| IFWRepeat: forall n s,
    Ifte_free_write s ->
    Ifte_free_write (Repeat n s)
| IFWSkip:
    Ifte_free_write Skip.

Lemma lift_Ifte_free_write:
  forall e s1 s2 t1 t2,
    Ifte_free_write (Comp (Ifte e s1 s2) (Ifte e t1 t2))
    <->
    Ifte_free_write (Ifte e (Comp s1 t1) (Comp s2 t2)).
Proof.
  Hint Constructors Ifte_free_write.
  intros e s1 s2 t1 t2.
  split; intro Hifw.
  - inversion_clear Hifw as [| | | |? ? Hs Ht| |].
    constructor; inversion_clear Hs; inversion_clear Ht; now cannot_write.
  - inversion_clear Hifw as [| |? ? ? Hfree1 Hfree2 Hcw| | | |].
    inversion_clear Hfree1; inversion_clear Hfree2.
    repeat constructor; cannot_write.
Qed.

Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Lemma Ifte_free_write_fold_left_shift:
  forall A f (xs : list A) iacc,
    Ifte_free_write (fold_left (fun i x => Comp (f x) i) xs iacc)
    <->
    (Ifte_free_write (fold_left (fun i x => Comp (f x) i) xs Skip)
     /\ Ifte_free_write iacc).
Proof.
  Hint Constructors Ifte_free_write.
  induction xs as [|x xs IH]; [now intuition|].
  intros; split.
  - intro HH. simpl in HH. apply IH in HH.
    destruct HH as [Hxs Hiacc].
    split; [simpl; rewrite IH|];
    repeat progress match goal with
    | H:Ifte_free_write (Comp _ _) |- _ => inversion_clear H
    | _ => now intuition
    end.
  - intros [HH0 HH1].
    simpl in HH0; rewrite IH in HH0.
    simpl; rewrite IH.
    intuition.
    repeat progress match goal with
    | H:Ifte_free_write (Comp _ _) |- _ => inversion_clear H
    | _ => now intuition
    end.
Qed.

Lemma not_Can_write_in_translate_cexp:
  forall x mems ce i,
    x <> i -> ~ Can_write_in i (translate_cexp mems x ce).
Proof.
  induction ce.
  - intros j Hxni Hcw.
    specialize (IHce1 _ Hxni).
    specialize (IHce2 _ Hxni).
    inversion_clear Hcw; intuition.
  - intros j Hxni Hcw.
    inversion Hcw; intuition.
Qed.

Lemma Is_free_in_tovar:
  forall mems i j,
    Is_free_in_exp j (tovar mems i) <-> i = j.
Proof.
  unfold tovar.
  intros mems i j.
  destruct (PS.mem i mems); split; intro HH;
  (inversion_clear HH; reflexivity || subst; now constructor).
Qed.

Lemma Ifte_free_write_translate_cexp:
  forall mems x ce,
    (forall i, Is_free_in_cexp i ce -> x <> i)
    -> Ifte_free_write (translate_cexp mems x ce).
Proof.
  intros mems x ce Hfree.
  induction ce.
  - simpl; constructor;
    [apply IHce1; now auto|apply IHce2; now auto|].
    intros j Hfree'; split;
    (apply not_Can_write_in_translate_cexp;
      apply Is_free_in_tovar in Hfree';
      subst; apply Hfree; constructor).
  - now constructor.
Qed.

Lemma Ifte_free_write_Control_caexp:
  forall mems ck f ce,
    (forall i, Is_free_in_caexp i (CAexp ck ce) -> ~Can_write_in i (f ce))
    -> Ifte_free_write (f ce)
    -> Ifte_free_write (Control mems ck (f ce)).
Proof.
  induction ck as [|ck IH i b]; [now intuition|].
  intros f ce Hxni Hfce.
  simpl.
  destruct b.
  - apply IH with (f:=fun ce=>Ifte (tovar mems i) (f ce) Skip).
    + intros j Hfree Hcw.
      apply Hxni with (i0:=j); [inversion_clear Hfree; now auto|].
      inversion_clear Hcw as [| | |? ? ? ? Hskip| | | |];
        [assumption|inversion Hskip].
    + repeat constructor; [assumption| |now inversion 1].
      apply Hxni.
      match goal with
      | H:Is_free_in_exp _ (tovar mems _) |- _ => rename H into Hfree
      end.
      unfold tovar in Hfree.
      destruct (PS.mem i mems); inversion Hfree; subst; now auto.
  - apply IH with (f:=fun ce=>Ifte (tovar mems i) Skip (f ce)).
    + intros j Hfree Hcw.
      apply Hxni with (i0:=j); [inversion_clear Hfree; now auto|].
      inversion_clear Hcw as [| |? ? ? ? Hskip| | | | |];
        [inversion Hskip|assumption].
    + repeat constructor; [assumption|now inversion 1|].
      apply Hxni.
      match goal with
      | H:Is_free_in_exp _ (tovar mems _) |- _ => rename H into Hfree
      end.
      unfold tovar in Hfree.
      destruct (PS.mem i mems); inversion Hfree; subst; now auto.
Qed.

Lemma Ifte_free_write_Control_laexp:
  forall mems ck s,
    (forall i, Is_free_in_clock i ck -> ~Can_write_in i s)
    -> Ifte_free_write s
    -> Ifte_free_write (Control mems ck s).
Proof.
  induction ck as [|ck IH i b]; [now intuition|].
  intros s Hxni Hfce.
  simpl.
  destruct b; apply IH.
  - intros j Hfree Hcw.
    apply Hxni with (i0:=j); [inversion_clear Hfree; now auto|].
    inversion_clear Hcw as [| | |? ? ? ? Hskip| | | |];
      [assumption|inversion Hskip].
  - repeat constructor; [assumption| |now inversion 1].
    apply Hxni.
    match goal with
    | H:Is_free_in_exp _ (tovar mems _) |- _ => rename H into Hfree
    end.
    unfold tovar in Hfree.
    destruct (PS.mem i mems); inversion Hfree; subst; now auto.
  - intros j Hfree Hcw.
    apply Hxni with (i0:=j); [inversion_clear Hfree; now auto|].
    inversion_clear Hcw as [| |? ? ? ? Hskip| | | | |];
      [inversion Hskip|assumption].
  - repeat constructor; [assumption|now inversion 1|].
    apply Hxni.
    match goal with
    | H:Is_free_in_exp _ (tovar mems _) |- _ => rename H into Hfree
      end.
    unfold tovar in Hfree.
    destruct (PS.mem i mems); inversion Hfree; subst; now auto.
Qed.

Require Import Rustre.Dataflow.Clocking.
Require Import Rustre.Dataflow.Clocking.Properties.

Lemma translate_eqns_Ifte_free_write:
  forall C mems inputs eqs,
    Well_clocked_env C
    -> Forall (Well_clocked_eq C) eqs
    -> Is_well_sch mems inputs eqs
    -> (forall x, PS.In x mems -> ~Is_variable_in x eqs)
    -> (forall input, List.In input inputs -> ~ Is_defined_in input eqs)
    -> Ifte_free_write (translate_eqns mems eqs).
Proof.
  intros C mems inputs eqs Hwk Hwks Hwsch Hnvi Hnin.
  induction eqs as [|eq eqs IH]; [now constructor|].
  inversion Hwks as [|eq' eqs' Hwkeq Hwks']; subst.
  specialize (IH Hwks' (Is_well_sch_cons _ _ _ _ Hwsch)).
  unfold translate_eqns.
  simpl; apply Ifte_free_write_fold_left_shift.
  split.
  - apply IH.
    + intros x Hin; apply Hnvi in Hin.
      apply not_Is_variable_in_cons in Hin.
      now intuition.
    + intros input Hin Hdefined. setoid_rewrite not_Is_defined_in_cons in Hnin.
      apply Hnin in Hin. destruct Hin. contradiction.
  - clear IH.
    repeat constructor.
    destruct eq as [x e|x f e|x v0 e]; simpl.
    + assert (~PS.In x mems) as Hnxm
          by (intro Hin; apply Hnvi with (1:=Hin); repeat constructor).
      inversion_clear Hwsch as [|? ? ? Hwsch' HH Hndef| |].
      assert (forall i, Is_free_in_caexp i e -> x <> i) as Hfni.
      { intros i Hfree.
        apply HH in Hfree.
        destruct Hfree as [Hm Hnm].
        assert (~ List.In x inputs) as Hninp
            by (intro Hin; apply (Hnin _ Hin); repeat constructor).
        assert (~PS.In x mems) as Hnxm' by intuition.
        intro Hxi; rewrite Hxi in *; clear Hxi.
        specialize (Hnm Hnxm').
        apply Hndef.
        destruct Hnm as [Hnm|Hnm]; [|now intuition].
        apply Is_variable_in_Is_defined_in with (1:=Hnm). }
      destruct e as [ck ce].
      apply Ifte_free_write_Control_caexp.
      intros i Hfree.
      apply (not_Can_write_in_translate_cexp).
      apply Hfni with (1:=Hfree).
      apply (Ifte_free_write_translate_cexp).
      intros i Hfree; apply Hfni; intuition.
    + destruct e as [ck e].
      assert (~Is_free_in_clock x ck) as Hnfree
          by (apply Well_clocked_EqApp_not_Is_free_in_clock
              with (1:=Hwk) (2:=Hwkeq));
      apply Ifte_free_write_Control_laexp;
      [intros i Hfree Hcw; inversion Hcw; subst; contradiction|intuition].
    + destruct e as [ck e];
      assert (~Is_free_in_clock x ck) as Hnfree
          by (apply Well_clocked_EqFby_not_Is_free_in_clock
              with (1:=Hwk) (2:=Hwkeq));
      apply Ifte_free_write_Control_laexp;
      [intros i Hfree Hcw; inversion Hcw; subst; contradiction|intuition].
Qed.

(*
   The property "Ifte_free_write (translate_eqns mems eqs)" is obtained above
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
   Ifte_free_write. We could imagine a weaker invariant that allows the
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

