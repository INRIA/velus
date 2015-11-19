Require Import Coq.FSets.FMapPositive.
Require Import PArith.
Require Import Rustre.Common.
Require Import Rustre.Minimp.Syntax.
Require Import Rustre.Dataflow.Syntax.
Require Import Rustre.Dataflow.IsMemory.

Import List.ListNotations.
Open Scope positive.
Open Scope list.

(** * Translation *)

(*
   Note: it is necessary to distinguish different instantiations of
         the same node (i.e., different objects of the same class).

         This is done in Auger's thesis in the language LSNI, where
         node applications are assigned unique identifiers. His context
         is richer, in particular, because the result of a node application
         may be assigned to a pattern-tuple containing multiple identifiers.

         Here, we take advantage of the fact that the result of a node
         application is assigned to a single variable. We use the name of
         that variable to identify the instance.
 *)

Definition gather_eq (acc: list ident * list obj_dec) (eq: equation) :=
  match eq with
  | EqDef _ _ => acc
  | EqApp x f _ => (fst acc, mk_obj_dec x f :: snd acc)
  | EqFby x v0 _ => (x::fst acc, snd acc)
  end.

Definition gather_eqs (eqs: list equation) : (list ident * list obj_dec) :=
  List.fold_left gather_eq eqs ([], []).

Section Translate.

  Variable memories : PS.t.

  Definition tovar (x: ident) : exp :=
    if PS.mem x memories then State x else Var x.

  Fixpoint Control (ck: clock)(s: stmt): stmt :=
    match ck with
    | Cbase => s
    | Con ck x true  => Control ck (Ifte (tovar x) s Skip)
    | Con ck x false => Control ck (Ifte (tovar x) Skip s)
    end.

  Fixpoint translate_lexp (e: lexp): exp :=
    match e with
    | Econst c => Const c
    | Evar x => if PS.mem x memories then State x else Var x
    | Ewhen e c x => translate_lexp e
    end.
  
  Definition translate_laexp (lae: laexp): exp :=
    match lae with
      | LAexp ck e => translate_lexp e
    end.

  Fixpoint translate_cexp (x: ident)(e : cexp) {struct e}: stmt :=
    match e with
    | Emerge y t f => Ifte (tovar y) (translate_cexp x t) (translate_cexp x f)
    | Eexp l => Assign x (translate_lexp l)
    end.

  Definition translate_caexp (x: ident)(ae : caexp): stmt :=
    match ae with
      | CAexp ck e => translate_cexp x e
    end.

  Definition translate_eqn (eqn: equation): stmt :=
    match eqn with
    | EqDef x (CAexp ck ce) =>
      Control ck (translate_cexp x ce)
    | EqApp x f (LAexp ck le) =>
      Control ck (Step_ap x f x (translate_lexp le))
    | EqFby x v (LAexp ck le) =>
      Control ck (AssignSt x (translate_lexp le))
    end.

  (* NB: eqns ordered in reverse order of execution for coherence
         with Is_well_sch. *)
  Definition translate_eqns (eqns: list equation): stmt :=
    List.fold_left (fun i eq => Comp (translate_eqn eq) i) eqns Skip.

End Translate.

Definition ps_from_list (l: list ident) : PS.t :=
  List.fold_left (fun s i=>PS.add i s) l PS.empty.

Lemma ps_from_list_pre_spec:
  forall x l S, (List.In x l \/ PS.In x S)
                <->
                PS.In x (List.fold_left (fun s i=>PS.add i s) l S).
Proof.
  (* TODO: How to use auto to do this whole proof? *)
  induction l as [|l ls IH].
  split; intro HH;
    [ destruct HH as [HH|HH]; [ apply List.in_nil in HH; contradiction | auto]
    | auto ].
  split; intro HH.
  - apply IH.
    destruct HH as [HH|HH].
    apply List.in_inv in HH.
    destruct HH as [HH|HH].
    rewrite HH.
    right; apply PS.add_spec.
    intuition.
    intuition.
    right; apply PS.add_spec; intuition.
  - apply IH in HH.
    destruct HH as [HH|HH].
    left; apply List.in_cons; exact HH.
    apply PS.add_spec in HH.
    destruct HH as [HH|HH].
    rewrite HH; intuition.
    intuition.
Qed.

Lemma ps_from_list_spec:
  forall x l, List.In x l <-> PS.In x (ps_from_list l).
Proof.
  unfold ps_from_list.
  intros.
  rewrite <- ps_from_list_pre_spec with (S:=PS.empty).
  intuition.
  match goal with
  | H:PS.In _ PS.empty |- _ => apply not_In_empty in H; contradiction
  end.
Qed.


(* Annoying morphism lemmas... *)
Require Import Setoid.
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
  induction e; intros M M' HMeq; simpl; auto.
  rewrite HMeq; auto.
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

