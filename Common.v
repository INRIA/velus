Require Import Coq.FSets.FMapPositive.
Require Import List.
Require Coq.MSets.MSets.
Require Export PArith.


(** * Common definitions *)

Module PS := Coq.MSets.MSetPositive.PositiveSet.
Module PSP := MSetProperties.WPropertiesOn Pos PS.
Module PSF := MSetFacts.Facts PS.

Module PM := Coq.FSets.FMapPositive.PositiveMap.

Definition ident := positive.
Definition ident_eq_dec := Pos.eq_dec.
Definition ident_eqb := Pos.eqb.

Implicit Type i j: ident.

(* The basic types supported by Rustre *)
Inductive base_type := Tint | Tbool.
Inductive const : Set :=
| Cint : BinInt.Z -> const
| Cbool : bool -> const.

Definition nelist A := {l : list A | l <> nil}.

Inductive arity :=
  | Tout (t_out : base_type)
  | Tcons (t_in : base_type) (arr : arity).

(* Our own version of RelationClasses.arrows interpreting the arity *)
Definition base_interp t :=
  match t with
    | Tint => BinInt.Z
    | Tbool => bool
  end.

Fixpoint arrows (l : arity) : Set :=
  match l with
    | Tout t => base_interp t
    | Tcons A ar => base_interp A -> arrows ar
  end.

(* The set of external operators. idea: operator = sigT arrows but we want decidable equality *)
Parameter operator : Set.
Parameter get_arity : operator -> arity.
Parameter get_interp : forall op : operator, arrows (get_arity op).
Axiom op_dec : forall op1 op2 : operator, {op1 = op2} + {op1 <> op2}.

(*
Example plus : operator.
exists (Tcons Tint (Tcons Tint (Tout Tint))).
exact BinInt.Z.add.
Defined.*)

(** * Common (and preliminary) results **)

Lemma ident_eqb_neq:
  forall x y, ident_eqb x y = false <-> x <> y.
Proof.
  unfold ident_eqb; apply Pos.eqb_neq.
Qed.

Lemma ident_eqb_eq:
  forall x y, ident_eqb x y = true <-> x = y.
Proof.
  unfold ident_eqb; apply Pos.eqb_eq.
Qed.

Lemma ident_eqb_refl:
  forall f, ident_eqb f f = true.
Proof.
  unfold ident_eqb; apply Pos.eqb_refl.
Qed.

Lemma In_dec:
  forall x S, {PS.In x S}+{~PS.In x S}.
Proof.
  intros i m; unfold PS.In; case (PS.mem i m); auto.
Qed.

Definition const_eqb (c1: const) (c2: const) : bool :=
  match c1, c2 with
  | Cint z1, Cint z2 => BinInt.Z.eqb z1 z2
  | Cbool b1, Cbool b2 => Bool.eqb b1 b2
  | _, _ => false
  end.

Lemma const_eqb_eq:
  forall (c1 c2: const),
    const_eqb c1 c2 = true <-> c1 = c2.
Proof.
  split.
  - destruct c1, c2; simpl; intro H; try discriminate.
    + apply BinInt.Z.eqb_eq in H; rewrite H; reflexivity.
    + apply Bool.eqb_prop in H; rewrite H; reflexivity.
  - destruct c1, c2; simpl; intro H0; try discriminate H0.
    + injection H0.
      intro H1; rewrite H1.
      destruct z, z0; simpl;
      (reflexivity || discriminate || (apply Pos.eqb_eq; reflexivity)).
    + injection H0.
      intro H1; rewrite H1.
      destruct b, b0; simpl; try reflexivity.
Qed.

Lemma const_eq_dec: forall (c1 c2: const), {c1=c2}+{c1<>c2}.
Proof.
  intros c1 c2.
  destruct (const_eqb c1 c2) eqn:Heq; [left|right].
  apply const_eqb_eq; assumption.
  intro H; apply const_eqb_eq in H.
  rewrite Heq in H; discriminate.
Qed.

Lemma Forall_cons2:
  forall A P (x: A) l,
    List.Forall P (x :: l) <-> P x /\ List.Forall P l.
Proof. intros; split; inversion_clear 1; auto. Qed.

Lemma pm_in_dec: forall A i m, PM.In (A:=A) i m \/ ~PM.In (A:=A) i m.
Proof.
  unfold PM.In, PM.MapsTo.
  intros A i m.
  case (PM.find i m).
  eauto.
  right; intro; destruct H; discriminate H.
Qed.

Lemma Some_injection:
  forall A (x:A) (y:A), x = y <-> Some x = Some y.
Proof.
  split; intro H; [rewrite H|injection H]; auto.
Qed.

(* TODO: Is there a more direct way to negate PS.mem_spec?
         I.e., without creating a distinct lemma. *)
Lemma mem_spec_false:
  forall s x, PS.mem x s = false <-> ~PS.In x s.
Proof.
  split.
  intros Hmem Hin.
  apply PS.mem_spec in Hin.
  rewrite Hin in Hmem.
  discriminate.
  intro Hnin.
  apply Bool.not_true_iff_false.
  intro Hnmem.
  rewrite PS.mem_spec in Hnmem.
  contradiction.
Qed.

Import List.ListNotations.
Open Scope list_scope.

Lemma List_shift_first:
  forall (A:Set) ll (x : A) lr,
    ll ++ (x :: lr) = (ll ++ [x]) ++ lr.
Proof.
  induction ll as [|? ? IH]; [auto|intros].
  rewrite <- List.app_comm_cons.
  rewrite IH.
  now do 2 rewrite List.app_comm_cons.
Qed.

Lemma List_shift_away:
  forall (A:Set) alleqs (eq : A) eqs,
    (exists oeqs, alleqs = oeqs ++ (eq :: eqs))
    -> exists oeqs', alleqs = oeqs' ++ eqs.
Proof.
  intros A alleqs eq eqs Hall.
  destruct Hall as [oeqs Hall].
  exists (oeqs ++ [eq]).
  rewrite Hall.
  now rewrite List_shift_first.
Qed.

Lemma Forall_app:
  forall A (P: A -> Prop) ll rr,
    Forall P (ll ++ rr) <-> (Forall P ll /\ Forall P rr).
Proof.
  intros A P ll rr.
  induction ll as [|x ll IH]; [intuition|].
  rewrite Forall_cons2.
  rewrite and_assoc.
  rewrite <-IH.
  rewrite <-List.app_comm_cons.
  now rewrite Forall_cons2.
Qed.

Lemma Exists_app:
  forall A (P: A -> Prop) ll rr,
    Exists P rr
    -> Exists P (ll ++ rr).
Proof.
  intros A P ll rr Hex.
  induction ll as [|x ll IH]; [intuition|].
  rewrite <-List.app_comm_cons.
  constructor 2.
  exact IH.
Qed.

Lemma Forall_Forall:
  forall A P Q (xs : list A),
    Forall P xs -> Forall Q xs -> Forall (fun x=>P x /\ Q x) xs.
Proof.
  induction xs as [|x xs IH]; [now constructor|].
  intros HPs HQs.
  inversion_clear HPs as [|? ? HP HPs'].
  inversion_clear HQs as [|? ? HQ HQs'].
  intuition.
Qed.

Lemma Forall_Exists:
  forall A (P Q: A -> Prop) xs,
    Forall P xs
    -> Exists Q xs
    -> Exists (fun x=>P x /\ Q x) xs.
Proof.
  induction xs as [|x xs IH]; [now inversion 2|].
  intros Ha He.
  inversion_clear Ha.
  inversion_clear He; auto.
Qed.

Lemma not_None_is_Some:
  forall A (x : option A), x <> None <-> (exists v, x = Some v).
Proof.
  destruct x; intuition.
  exists a; reflexivity.
  discriminate.
  match goal with H:exists _, _ |- _ => destruct H end; discriminate.
Qed.


(* TODO: Why isn't this lemma already in the module PS?
   -> Actually it is ! *)
Check PS.empty_spec.
Lemma not_In_empty: forall x : ident, ~(PS.In x PS.empty).
Proof.
  unfold PS.In; unfold PS.empty;
  intros; rewrite PS.mem_Leaf; apply Bool.diff_false_true.
Qed.

Ltac not_In_empty :=
  match goal with H:PS.In _ PS.empty |- _ => now apply not_In_empty in H end.

(* A constant list of the same size *)
Definition alls {A B} c (l : list A) : list B := map (fun _ => c) l.


Definition op_eqb op1 op2 := if op_dec op1 op2 then true else false.

Lemma op_eqb_true_iff : forall op1 op2, op_eqb op1 op2 = true <-> op1 = op2.
Proof. intros op1 op2. unfold op_eqb. destruct (op_dec op1 op2); intuition discriminate. Qed.

Lemma op_eqb_false_iff : forall op1 op2, op_eqb op1 op2 = false <-> op1 <> op2.
Proof. intros op1 op2. unfold op_eqb. destruct (op_dec op1 op2); intuition discriminate. Qed.

Open Scope bool_scope.

Fixpoint forall2b {A B} (f : A -> B -> bool) l1 l2 :=
  match l1, l2 with
    | nil, nil => true
    | e1 :: l1, e2 :: l2 => f e1 e2 && forall2b f l1 l2
    | _, _ => false
  end.
