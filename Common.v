Require Import Coq.FSets.FMapPositive.
Require Coq.MSets.MSets.
Require Export PArith.
Require Import Rustre.Nelist.

(** * Common definitions *)

Module PS := Coq.MSets.MSetPositive.PositiveSet.
Module PSP := MSetProperties.WPropertiesOn Pos PS.
Module PSF := MSetFacts.Facts PS.

Module PM := Coq.FSets.FMapPositive.PositiveMap.

Definition ident := positive.
Definition ident_eq_dec := Pos.eq_dec.
Definition ident_eqb := Pos.eqb.

Implicit Type i j: ident.


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

Definition adds {A} (is : nelist ident) (vs : nelist A) (S : PM.t A) :=
  Nelist.fold_right (fun (iiv: ident * A) env => 
                    let (i , iv) := iiv in
                    PM.add i iv env) S (Nelist.combine is vs).

Inductive Assoc {A} : nelist ident -> nelist A -> ident -> A -> Prop :=
| AssocBase: 
    forall i v,
      Assoc (nebase i) (nebase v) i v
| AssocHere: 
    forall i v is vs,
      Assoc (necons i is) (necons v vs) i v
| AssocThere:
    forall i v i' v' is vs,
      Assoc is vs i' v' ->
      i <> i' ->
      Assoc (necons i is) (necons v vs) i' v'.


Lemma gsss: 
  forall {A: Type} is (vs : nelist A) i c, length is = length vs ->
    (Assoc is vs i c <-> PM.find i (adds is vs (PM.empty _)) = Some c).
Proof.
  Hint Constructors Assoc.
  intros A is vs i c Hlen.
  split.
  - intros ** Hassoc; induction Hassoc; try contradiction; unfold adds; simpl.
    * rewrite PM.gss; auto.
    * rewrite (@PM.gss A i); auto.
    * rewrite PM.gso; auto.
  - revert vs Hlen; induction is as [i1 |i1 is]; intros [v1 | v1 vs] Hlen;
    try now destruct is || destruct vs; simpl in Hlen; discriminate.
    + unfold adds. simpl. intro Hfind.
      destruct (ident_eqb i i1) eqn:Heqi.
      * apply ident_eqb_eq in Heqi. subst. 
        rewrite PM.gss in Hfind; injection Hfind; intro; subst; clear Hfind.
        econstructor.
      * apply ident_eqb_neq in Heqi.
        rewrite PM.gso, PM.gempty in Hfind; trivial. discriminate.
    + unfold adds. simpl. intro Hfind.
      destruct (ident_eqb i i1) eqn:Heqi.
      * apply ident_eqb_eq in Heqi. subst. 
        rewrite PM.gss in Hfind; injection Hfind; intro; subst; clear Hfind.
        econstructor.
      * apply ident_eqb_neq in Heqi.
        rewrite PM.gso in Hfind; auto.
Qed.

Lemma gsos: 
  forall (A: Type) is vs (m : PM.t A) i, length is = length vs ->
    ~ Nelist.In i is ->
    PM.find i (adds is vs m) = PM.find i m.
Proof.
  intros A is vs m i Hlen Hnin. revert vs Hlen.
  induction is as [i1 |i1 is]; intros [v1 |v1 vs] Hlen; 
  try now destruct is || destruct vs; simpl in Hlen; discriminate.
  - unfold adds; simpl; auto. now rewrite PM.gso.
  - simpl in Hlen. unfold adds; simpl; auto.
    destruct (ident_eqb i i1) eqn:Heqi.
    + exfalso.
      apply ident_eqb_eq in Heqi. subst.
      apply Hnin; simpl; auto.
    + apply ident_eqb_neq in Heqi.
      rewrite PM.gso; eauto.
      apply IHis; try omega; []. intro Hin. apply Hnin. simpl. auto.
Qed.


Lemma In_dec:
  forall x S, {PS.In x S}+{~PS.In x S}.
Proof.
  intros i m; unfold PS.In; case (PS.mem i m); auto.
Qed.

Inductive const : Set :=
| Cint : BinInt.Z -> const
| Cbool : bool -> const.

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

Require Import List.
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


(* TODO: Why isn't this lemma already in the module PS? *)
Lemma not_In_empty: forall x : ident, ~(PS.In x PS.empty).
Proof.
  unfold PS.In; unfold PS.empty;
  intros; rewrite PS.mem_Leaf; apply Bool.diff_false_true.
Qed.

Ltac not_In_empty :=
  match goal with H:PS.In _ PS.empty |- _ => now apply not_In_empty in H end.

Ltac inv H := inversion H; subst; clear H.
