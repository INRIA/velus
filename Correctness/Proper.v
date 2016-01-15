Require Import Rustre.Common.
Open Scope positive.

Require Import Rustre.Dataflow.
Require Import Rustre.Minimp.
Require Import Rustre.Translation.
Require Import Setoid.


(**
 Annoying morphism lemmas... 
*)



Instance eq_equiv : Equivalence PS.eq.
Proof. firstorder. Qed.

Require Import Morphisms.

Instance List_fold_left_add_Proper (xs: list ident) :
  Proper (PS.eq ==> PS.eq)
         (List.fold_left (fun s i => PS.add i s) xs).
Proof.
  induction xs as [|x xs IH]; intros S S' Heq; [exact Heq|].
  assert (PS.eq (PS.add x S) (PS.add x S')) as Heq'
      by (rewrite Heq; reflexivity).
  simpl; rewrite Heq'; reflexivity.
Qed.

Instance List_fold_left_memory_eq_Proper (eqs: list equation) :
  Proper (PS.eq ==> PS.eq)
         (List.fold_left memory_eq eqs).
Proof.
  induction eqs as [|eq eqs IH]; intros S S' Heq; [exact Heq|].
  simpl.
  apply IH.
  destruct eq; [apply Heq|apply Heq|].
  simpl; rewrite Heq; reflexivity.
Qed.

Lemma add_ps_from_list_cons:
  forall xs x, PS.eq (PS.add x (ps_from_list xs))
                     (ps_from_list (x::xs)).
Proof.
  intros; unfold ps_from_list; simpl.
  generalize PS.empty as S.
  induction xs as [|y xs IH]; [ reflexivity | ].
  intro S; simpl; rewrite IH; rewrite PSP.add_add; reflexivity.
Qed.

Lemma ps_from_list_gather_eqs_memories:
  forall eqs, PS.eq (ps_from_list (fst (gather_eqs eqs)))
                    (memories eqs).
Proof.
  induction eqs as [|eq eqs IH]; [reflexivity|].
  unfold memories, gather_eqs.
  assert (forall eqs F S,
             PS.eq (ps_from_list (fst (List.fold_left gather_eq eqs (F, S))))
                   (List.fold_left memory_eq eqs (ps_from_list F))) as HH.
  { clear eq eqs IH; induction eqs as [|eq eqs IH]; [reflexivity|].
    intros F S.
    destruct eq; [now apply IH|now apply IH|].
    simpl; rewrite IH; rewrite add_ps_from_list_cons; reflexivity. }
  rewrite HH; reflexivity.
Qed.

Instance tovar_Proper :
  Proper (PS.eq ==> eq ==> eq) tovar.
Proof.
  intros M M' HMeq x x' Hxeq; rewrite <- Hxeq; clear Hxeq x'.
  unfold tovar.
  destruct (PS.mem x M) eqn:Hmem;
    rewrite <- HMeq, Hmem; reflexivity.
Qed.

Instance translate_lexp_Proper :
  Proper (PS.eq ==> eq ==> eq) translate_lexp.
Proof.
intros M M' HMeq e e' Heq; rewrite <- Heq; clear Heq e'.
revert M M' HMeq.
induction e using lexp_ind2; intros M M' HMeq; simpl; auto.
+ rewrite HMeq; auto.
+ f_equal.
  induction les; simpl.
  - f_equal. inversion_clear H. now apply H0.
  - inversion_clear H. f_equal; auto.
Qed.

Instance translate_cexp_Proper :
  Proper (PS.eq ==> eq ==> eq ==> eq) translate_cexp.
Proof.
  intros M M' HMeq y y' Hyeq c c' Hceq; rewrite <- Hyeq, <- Hceq;
  clear y' c' Hyeq Hceq.
  revert M M' HMeq.
  induction c; intros; simpl.
  - erewrite IHc1; try eassumption.
    erewrite IHc2; try eassumption. 
    rewrite HMeq; auto.
  - rewrite HMeq; auto.
Qed.

Instance translate_caexp_Proper :
  Proper (PS.eq ==> eq ==> eq ==> eq) translate_caexp.
Proof.
  intros M M' HMeq y y' Hyeq c c' Hceq; rewrite <- Hyeq, <- Hceq;
  clear y' c' Hyeq Hceq.
  destruct c as [ck c].
  change (translate_cexp M y c = translate_cexp M' y c).
  rewrite HMeq; reflexivity.
Qed.

Instance Control_Proper :
  Proper (PS.eq ==> eq ==> eq ==> eq) Control.
Proof.
  intros M M' HMeq ck ck' Hckeq e e' Heq; rewrite <-Hckeq, <-Heq;
  clear ck' e' Hckeq Heq.
  revert e; induction ck as [ |ck' IH s sv].
  - reflexivity.
  - intro e.
    destruct sv; simpl; rewrite IH, HMeq; reflexivity.
Qed.

Instance translate_eqn_Proper :
  Proper (PS.eq ==> eq ==> eq) translate_eqn.
Proof.
  intros M M' HMeq eq eq' Heq; rewrite <- Heq; clear Heq eq'.
  destruct eq as [y e|y f e|y v0 e];
    (destruct e; simpl; rewrite HMeq; reflexivity).
Qed.

Instance translate_eqns_Proper :
  Proper (PS.eq ==> eq ==> eq) translate_eqns.
Proof.
  intros M M' Heq eqs eqs' Heqs.
  rewrite <- Heqs; clear Heqs.
  unfold translate_eqns.
  assert (forall S S',
             S = S' ->
             List.fold_left (fun i eq => Comp (translate_eqn M eq) i) eqs S
             = List.fold_left (fun i eq => Comp (translate_eqn M' eq) i) eqs S')
         as HH.
  { revert M M' Heq.
    induction eqs as [|eq eqs IH]; intros M M' Heq S S' HSeq; [apply HSeq|].
    simpl; apply IH with (1:=Heq); rewrite HSeq, Heq; reflexivity. }
  rewrite HH with (S':=Skip); reflexivity.
Qed.

