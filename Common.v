Require Import Coq.FSets.FMapPositive.
Require Import List.
Require Import Coq.Sorting.Permutation.
Require Import Morphisms.
Import ListNotations.
Require Coq.MSets.MSets.
Require Export PArith.
Require Import Omega.
Require Import Coq.Classes.EquivDec.

Open Scope list.

(** * Common definitions *)

(** ** Finite sets and finite maps *)

(** These modules are used to manipulate identifiers. *)

Ltac inv H := inversion H; clear H; subst.

Module PS := Coq.MSets.MSetPositive.PositiveSet.
Module PSP := MSetProperties.WPropertiesOn Pos PS.
Module PSF := MSetFacts.Facts PS.
Module PSdec := Coq.MSets.MSetDecide.WDecide PS.

Module PM := Coq.FSets.FMapPositive.PositiveMap.

Definition ident := positive.
Definition ident_eq_dec := Pos.eq_dec.
Definition ident_eqb := Pos.eqb. (* TODO: replace with equiv_decb *)

Instance: EqDec ident eq := { equiv_dec := ident_eq_dec }.

Implicit Type i j: ident.

Module Type IDS.
  Parameter self : ident.
  Parameter out  : ident.

  Parameter step  : ident.
  Parameter reset : ident.

  Definition reserved : list ident := [ self; out ].

  Definition methods  : list ident := [ step; reset ].

  Axiom reserved_nodup: NoDup reserved.
  Axiom methods_nodup: NoDup methods.

  Definition NotReserved {typ: Type} (xty: ident * typ) : Prop :=
    ~In (fst xty) reserved.

End IDS.

(** ** Properties *)

(** *** About identifiers **)

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

(** *** Operator abstraction *)

Generalizable Variables A.
  
Lemma equiv_decb_equiv:
  forall `{EqDec A} (x y : A),
    equiv_decb x y = true <-> equiv x y.
Proof.
  intros ** x y.
  split; intro; unfold equiv_decb in *;
    destruct (equiv_dec x y); intuition.
Qed.

Lemma equiv_decb_refl:
  forall `{EqDec A} (x: A),
    equiv_decb x x = true.
Proof.
  intros. now apply equiv_decb_equiv.
Qed.

Lemma not_equiv_decb_equiv:
  forall `{EqDec A} (x y: A),
    equiv_decb x y = false <-> ~(equiv x y).
Proof.
  split; intro Hne.
  - unfold equiv_decb in Hne.
    now destruct (equiv_dec x y).
  - unfold equiv_decb.
    destruct (equiv_dec x y); [|reflexivity].
    exfalso; now apply Hne.
Qed.

Module Type OPERATORS.
  Parameter val : Type.
  Parameter typ : Type.
  Parameter const : Type.

  Parameter true_val  : val.
  Parameter false_val : val.
  Axiom true_not_false_val : true_val <> false_val.

  Parameter bool_typ : typ.

  Parameter typ_const : const -> typ.
  Parameter sem_const : const -> val.
  
  Parameter unary_op  : Type.
  Parameter binary_op : Type.

  Parameter sem_unary  : unary_op -> val -> typ -> option val.
  Parameter sem_binary : binary_op -> val -> typ -> val -> typ -> option val.

  Axiom val_dec   : forall v1 v2 : val, {v1 = v2} + {v1 <> v2}.
  Axiom typ_dec   : forall t1 t2 : typ, {t1 = t2} + {t1 <> t2}.
  Axiom const_dec : forall c1 c2 : const, {c1 = c2} + {c1 <> c2}.
  Axiom unop_dec  : forall op1 op2 : unary_op, {op1 = op2} + {op1 <> op2}.
  Axiom binop_dec : forall op1 op2 : binary_op, {op1 = op2} + {op1 <> op2}.

End OPERATORS.

Module Type OPERATORS_AUX (Import Ops : OPERATORS).
  Require Export Coq.Classes.EquivDec.
  Close Scope equiv_scope.

  Instance: EqDec val eq := { equiv_dec := val_dec }.
  Instance: EqDec typ eq := { equiv_dec := typ_dec }.
  Instance: EqDec const eq := { equiv_dec := const_dec }.
  Instance: EqDec unary_op eq := { equiv_dec := unop_dec }.
  Instance: EqDec binary_op eq := { equiv_dec := binop_dec }.
  
  Definition val_to_bool (v: val) : option bool :=
    if equiv_decb v true_val then Some true
    else if equiv_decb v false_val then Some false
         else None.

  Lemma val_to_bool_true:
    val_to_bool true_val = Some true.
  Proof.
    unfold val_to_bool. now rewrite equiv_decb_refl.
  Qed.
  
  Lemma val_to_bool_false:
    val_to_bool false_val = Some false.
  Proof.
    unfold val_to_bool.
    assert (equiv_decb false_val true_val = false) as Hne.
    apply not_equiv_decb_equiv.
    now intro HH; apply true_not_false_val; rewrite HH.
    now rewrite Hne, equiv_decb_refl.
  Qed.

  Lemma val_to_bool_true':
    forall v,
      val_to_bool v = Some true <-> v = true_val.
  Proof.
    intro; split; intro HH.
    2:now subst; apply val_to_bool_true.
    destruct (equiv_dec v true_val); [assumption|].
    apply not_equiv_decb_equiv in c.
    unfold val_to_bool in HH; rewrite c in HH.
    now destruct (equiv_decb v false_val).
  Qed.

  Lemma val_to_bool_false':
    forall v,
      val_to_bool v = Some false <-> v = false_val.
  Proof.
    intro; split; intro HH.
    2:now subst; apply val_to_bool_false.
    destruct (equiv_dec v false_val); [assumption|].
    apply not_equiv_decb_equiv in c.
    unfold val_to_bool in HH; rewrite c in HH.
    now destruct (equiv_decb v true_val).
  Qed.
  
End OPERATORS_AUX.

Module OperatorsAux (Import Ops : OPERATORS) <: OPERATORS_AUX Ops.
  Include OPERATORS_AUX Ops.
End OperatorsAux.

(** *** About Coq stdlib *)

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
  forall (A:Type) ll (x : A) lr,
    ll ++ (x :: lr) = (ll ++ [x]) ++ lr.
Proof.
  induction ll as [|? ? IH]; [auto|intros].
  rewrite <- List.app_comm_cons.
  rewrite IH.
  now do 2 rewrite List.app_comm_cons.
Qed.

Lemma List_shift_away:
  forall (A:Type) alleqs (eq : A) eqs,
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

Lemma Permutation_Forall:
  forall {A} (l l': list A) P,
    Permutation l l' ->
    Forall P l ->
    Forall P l'.
Proof.
    induction 1; inversion 1; auto.
    match goal with H:Forall _ (_ :: _) |- _ => inversion H end.
    repeat constructor; auto.
Qed.

Instance Forall_Permutation_Proper (A:Type):
  Proper (eq ==> Permutation (A:=A) ==> iff) Forall.
Proof.
  intros P Q HPQ xs ys Hperm.
  subst P.
  split; intro HH; [|symmetry in Hperm];
    apply Permutation_Forall with (1:=Hperm) (2:=HH).
Qed.

  Lemma Forall_app_weaken:
    forall {A} xs P (ys : list A),
      Forall P (xs ++ ys) ->
      Forall P ys.
  Proof.
    intros ** HH. apply Forall_app in HH. intuition.
  Qed.
  


Lemma not_None_is_Some:
  forall A (x : option A), x <> None <-> (exists v, x = Some v).
Proof.
  destruct x; intuition.
  exists a; reflexivity.
  discriminate.
  match goal with H:exists _, _ |- _ => destruct H end; discriminate.
Qed.

Lemma not_Some_is_None:
  forall A (x : option A),  (forall v, x <> Some v) <-> x = None.
Proof.
  destruct x; intuition.
  - exfalso; now apply (H a).
  - discriminate.
  - discriminate.
Qed.

Lemma combine_map_fst:
  forall {A B C} (f: A -> B) xs (ys: list C),
    combine (map f xs) ys = map (fun x=>(f (fst x), snd x)) (combine xs ys).
Proof.
  induction xs; try constructor.
  destruct ys; try constructor.
  simpl. now rewrite IHxs.
Qed.

Lemma combine_map_snd:
  forall {A B C} (f: A -> B) (xs: list C) ys,
    combine xs (map f ys) = map (fun x=>(fst x, f (snd x))) (combine xs ys).
Proof.
  induction xs; try constructor.
  destruct ys; try constructor.
  simpl. now rewrite IHxs.
Qed.

Lemma combine_map_both:
  forall {A B C D} (f: A -> B) (g: C -> D) xs ys,
    combine (map f xs) (map g ys)
    = map (fun x => (f (fst x), g (snd x))) (combine xs ys).
Proof.
  intros. now rewrite combine_map_fst, combine_map_snd, map_map.
Qed.

Definition not_In_empty: forall x : ident, ~(PS.In x PS.empty) := PS.empty_spec.

Ltac not_In_empty :=
  match goal with H:PS.In _ PS.empty |- _ => now apply not_In_empty in H end.

Lemma map_eq_cons : forall {A B} (f : A -> B) l y l',
  map f l = y :: l' -> exists x l'', l = x :: l'' /\ f x = y.
Proof.
intros A B f l y l' Hmap. destruct l; simpl in Hmap.
- discriminate.
- inversion_clear Hmap. eauto.
Qed.

Open Scope bool_scope.

Fixpoint forall2b {A B} (f : A -> B -> bool) l1 l2 :=
  match l1, l2 with
    | nil, nil => true
    | e1 :: l1, e2 :: l2 => f e1 e2 && forall2b f l1 l2
    | _, _ => false
  end.

Lemma Forall2_forall2 : forall {A B : Type} P l1 l2,
  Forall2 P l1 l2 <-> length l1 = length l2 /\
                      forall (a : A) (b : B) n x1 x2, n < length l1 -> nth n l1 a = x1 -> nth n l2 b = x2 -> P x1 x2.
Proof.
intros A B P l1. induction l1; intro l2.
* split; intro H.
  + inversion_clear H. split; simpl; auto. intros. omega.
  + destruct H as [H _]. destruct l2; try discriminate. constructor.
* split; intro H.
  + inversion_clear H. rewrite IHl1 in H1. destruct H1. split; simpl; auto.
    intros. destruct n; subst; trivial. eapply H1; eauto. omega.
  + destruct H as [Hlen H].
    destruct l2; simpl in Hlen; try discriminate. constructor.
    apply (H a b 0); trivial; simpl; try omega.
    rewrite IHl1. split; try omega.
    intros. eapply (H a0 b0 (S n)); simpl; eauto. simpl; omega.
Qed.


Lemma Forall2_det : forall {A B : Type} (R : A -> B -> Prop),
  (forall x y1 y2, R x y1 -> R x y2 -> y1 = y2) ->
  forall xs ys1 ys2, Forall2 R xs ys1 -> Forall2 R xs ys2 -> ys1 = ys2.
Proof.
intros A B R HR xs. induction xs as [x | x xs]; intros ys1 ys2 Hall1 Hall2.
- inversion Hall1. inversion Hall2; reflexivity. 
- inversion Hall1. inversion Hall2. f_equal; eauto.
Qed.

Lemma Forall2_combine:
  forall {A B} P (xs: list A) (ys: list B),
    Forall2 P xs ys -> Forall (fun x=>P (fst x) (snd x)) (combine xs ys).
Proof.
  intros A B P xs ys Hfa2.
  induction Hfa2; now constructor.
Qed.

Section InMembers.
  Context {A B: Type}.

  Fixpoint InMembers (a:A) (l:list (A * B)) : Prop :=
    match l with
    | nil => False
    | (a', _) :: m => a' = a \/ InMembers a m
    end.

  Inductive NoDupMembers: list (A * B) -> Prop :=
  | NoDupMembers_nil:
      NoDupMembers nil
  | NoDupMembers_cons: forall a b l,
      ~ InMembers a l ->
      NoDupMembers l ->
      NoDupMembers ((a, b)::l).

  Theorem inmembers_eq:
    forall a b l, InMembers a ((a, b) :: l).
  Proof.
    intros. constructor. reflexivity.
  Qed.

  Theorem inmembers_cons:
    forall a a' l, InMembers a l -> InMembers a (a' :: l).
  Proof.
    intros. destruct a'. simpl. intuition.
  Qed.

  Theorem In_InMembers:
    forall a b xs,
      In (a, b) xs -> InMembers a xs.
  Proof.
    intros ** Hin.
    induction xs as [|x xs IH]; inversion_clear Hin; subst.
    - simpl. left. reflexivity.
    - simpl. destruct x. right. intuition.
  Qed.

  Theorem InMembers_In:
    forall a xs,
      InMembers a xs -> exists b, In (a, b) xs.
  Proof.
    intros ** Hin.
    induction xs as [|x xs IH]; simpl in Hin.
    - contradiction. 
    - simpl. destruct x. destruct Hin; subst.
      + exists b; now left.
      + destruct IH as (b'); auto.
        exists b'; now right. 
  Qed.

  Theorem nodupmembers_cons:
    forall id ty xs,
      NoDupMembers ((id, ty) :: xs) <->
      ~InMembers id xs /\ NoDupMembers xs.
  Proof.
    split.
    - inversion_clear 1. auto.
    - destruct 1 as [Hnin Hndup].
      constructor; auto.
  Qed.

  Theorem NotInMembers_NotIn:
    forall a b xs, ~ InMembers a xs -> ~ In (a, b) xs.
  Proof.
    intros ** Hnim Hin.
    apply In_InMembers in Hin.
    intuition.
  Qed.

  Theorem NotInMembers_cons:
    forall y x xs,
      ~InMembers y (x::xs) -> ~InMembers y xs /\ y <> fst x.
  Proof.
    induction xs as [|x' xs IH]; intro Hnin.
    - split.
      + inversion 1.
      + intro Eq; apply Hnin.
        destruct x; simpl in *; now left.
    - split.
      + intro HH. apply Hnin.
        destruct x, x'.
        right. inversion HH; auto.
      + intro HH. apply Hnin.
        destruct x, x'.
        simpl in *; now left.
  Qed.

  Lemma InMembers_app:
    forall y ws xs,
      InMembers y (ws ++ xs) <-> (InMembers y ws) \/ (InMembers y xs).
  Proof.
    induction ws as [|y' ws IH].
    - intuition.
    - destruct y' as [y' yv]. simpl.
      split; intro HH; destruct HH as [HH|HH].
      + intuition.
      + apply IH in HH. intuition.
      + destruct HH as [HH|HH].
        * intuition.
        * right. apply IH. intuition.
      + right. apply IH. intuition.
  Qed.

  Instance InMembers_Permutation_Proper:
    Proper (eq ==> (@Permutation (A*B)) ==> iff) InMembers.
  Proof.
    intros x y Heq xs ys Hperm.
    rewrite Heq. clear Heq x.
    split; intro Hinm.
    - apply InMembers_In in Hinm.
      destruct Hinm as [b Hinm].
      apply Permutation_in with (2:=Hinm) in Hperm.
      apply In_InMembers with (1:=Hperm).
    - apply InMembers_In in Hinm.
      destruct Hinm as [b Hinm].
      symmetry in Hperm.
      apply Permutation_in with (2:=Hinm) in Hperm.
      apply In_InMembers with (1:=Hperm).
  Qed.
  
  Theorem NotInMembers_app:
    forall y ws xs,
      ~InMembers y (ws ++ xs) <-> (~InMembers y xs /\ ~InMembers y ws).
  Proof.
    destruct ws; repeat split.
    - assumption.
    - inversion 1.
    - destruct 1. assumption.
    - intro HH. apply H.
      apply InMembers_app. auto.
    - intro. apply H.
      apply InMembers_app. auto.
    - destruct 1 as [H1 H2].
      intro H. apply InMembers_app in H. intuition.
  Qed.

  Theorem NotInMembers_app_comm:
    forall y ws xs,
      ~InMembers y (ws ++ xs) <-> ~InMembers y (xs ++ ws).
  Proof.
    split; intro HH; apply NotInMembers_app in HH;
    apply NotInMembers_app; intuition.
  Qed.

  Theorem NoDupMembers_NoDup:
    forall xs, NoDupMembers xs -> NoDup xs.
  Proof.
    induction xs as [|x xs IH]; [now constructor|].
    intro Hndm.
    inversion_clear Hndm.
    constructor; [|now apply IH].
    apply NotInMembers_NotIn. assumption.
  Qed.

  Lemma NoDupMembers_app_cons:
    forall ws x y xs,
      NoDupMembers (ws ++ (x, y) :: xs)
      <-> ~InMembers x (ws ++ xs) /\ NoDupMembers (ws ++ xs).
  Proof.
    induction ws as [|w ws IH]; repeat split.
    - apply nodupmembers_cons in H. intuition.
    - apply nodupmembers_cons in H. intuition.
    - destruct 1 as [HH1 HH2].
      apply nodupmembers_cons. intuition.
    - destruct w as [w ww].
      simpl in H. apply nodupmembers_cons in H.
      destruct H as [H1 H2].
      apply IH in H2.
      destruct H2 as [H2 H3].
      intro HH. destruct HH as [HH|HH].
      + subst. apply H1.
        apply InMembers_app. right.
        now constructor.
      + apply H2. assumption.
    - destruct w as [w ww].
      simpl in *. apply nodupmembers_cons in H.
      destruct H as [H1 H2].
      apply IH in H2.
      apply nodupmembers_cons.
      destruct H2 as [H2 H3].
      apply NotInMembers_app in H1.
      destruct H1 as [H1 H4].
      apply NotInMembers_cons in H1.
      split; try apply NotInMembers_app; intuition.
    - destruct 1 as [H1 H2].
      destruct w as [w ww].
      simpl in H2. apply nodupmembers_cons in H2.
      destruct H2 as [H2 H3].
      simpl. apply nodupmembers_cons.
      split.
      + intro HH. apply H2.
        apply InMembers_app.
        apply InMembers_app in HH.
        destruct HH as [HH|HH]; [now auto|].
        destruct HH as [HH|HH]; [|now auto].
        exfalso; apply H1. subst.
        now constructor.
      + apply IH.
        split; [|assumption].
        intro HH. apply H1.
        constructor 2. assumption.
  Qed.

  Lemma NoDupMembers_remove_1:
    forall ws x xs,
      NoDupMembers (ws ++ x :: xs) -> NoDupMembers (ws ++ xs).
  Proof.
    intros ** HH.
    destruct x. apply NoDupMembers_app_cons in HH. intuition.
  Qed.

   Lemma NoDupMembers_app_assoc:
    forall ws xs,
      NoDupMembers (ws ++ xs) <-> NoDupMembers (xs ++ ws).
  Proof.
    induction ws as [|w ws IH]; split; intro HH.
    - rewrite app_nil_r. assumption.
    - rewrite app_nil_r in HH. assumption.
    - destruct w as [w ww].
      simpl in HH; apply nodupmembers_cons in HH.
      destruct HH as [HH1 HH2].
      apply NoDupMembers_app_cons.
      apply NotInMembers_app_comm in HH1.
      split; [assumption|].
      apply IH. assumption.
    - destruct w as [w ww].
      apply NoDupMembers_app_cons in HH.
      destruct HH as [HH1 HH2].
      apply IH in HH2.
      simpl; apply NoDupMembers_cons.
      now apply NotInMembers_app_comm.
      assumption.
  Qed.

  Lemma NoDupMembers_app_r:
    forall ws xs,
      NoDupMembers (ws ++ xs) -> NoDupMembers xs.
  Proof.
    induction ws as [|w ws IH]; auto.
    intros xs H.
    apply IH.
    rewrite <-app_comm_cons in H.
    destruct w; rewrite nodupmembers_cons in H; tauto.
  Qed.

  Lemma NoDupMembers_app_l:
    forall ws xs,
      NoDupMembers (ws ++ xs) -> NoDupMembers ws.
  Proof.
    intros ** Hndup.
    apply NoDupMembers_app_assoc in Hndup.
    apply NoDupMembers_app_r with (1:=Hndup).
  Qed.

  Lemma NoDupMembers_app_InMembers:
    forall x xs ws,
      NoDupMembers (xs ++ ws) ->
      InMembers x xs ->
      ~InMembers x ws.
  Proof.
    induction ws as [|w ws IH]; auto.
    intros Nodup Hin H.
    destruct w; simpl in H.
    destruct H.
    - apply NoDupMembers_app_cons in Nodup.
      destruct Nodup as (Notin & ?).
      apply NotInMembers_app in Notin.
      subst.
      destruct Notin as (? & Notin); now apply Notin. 
    - apply NoDupMembers_remove_1 in Nodup.
      apply IH; auto.
  Qed.
  
  Lemma NoDupMembers_det:
    forall x t t' xs,
      NoDupMembers xs ->
      In (x, t) xs ->
      In (x, t') xs ->
      t = t'.
  Proof.
    induction xs; intros H Hin Hin'.
    - contradict Hin.
    - inversion Hin; inversion Hin'; subst.
      + inversion H1; auto.
      + inversion H; subst.
        inversion Hin'.
        * inversion H0; auto.
        * exfalso. apply H3. eapply In_InMembers; eauto.
      + inversion H; subst.
        inversion Hin.
        * inversion H1; auto.
        * exfalso. apply H3. eapply In_InMembers; eauto.
      + apply IHxs; auto.
        destruct a; rewrite nodupmembers_cons in H; tauto. 
  Qed.

  Global Instance NoDupMembers_Permutation_Proper:
    Proper (Permutation (A:=A * B) ==> iff) NoDupMembers.
  Proof.
    intros xs ys Hperm.
    induction Hperm.
    - now intuition.
    - destruct x as [x y].
      rewrite 2 nodupmembers_cons, IHHperm, Hperm.
      reflexivity.
    - split; intro HH.
      + inversion HH as [|a b l' Hninm Hndup]. clear HH. subst.
        destruct x as [x y].
        inversion Hndup as [|c d l' Hinm' Hndup']. clear Hndup. subst.
        econstructor.
        * intro Hinm. apply Hinm'.
          inversion_clear Hinm; subst; auto.
          exfalso; apply Hninm. now constructor.
        * constructor; auto. intro Hinm.
          apply Hninm. constructor (assumption).
      + inversion HH as [|a b l' Hninm Hndup]. clear HH. subst.
        destruct y as [x y].
        inversion Hndup as [|c d l' Hinm' Hndup']. clear Hndup. subst.
        econstructor.
        * intro Hinm. apply Hinm'.
          inversion_clear Hinm; subst; auto.
          exfalso; apply Hninm. now constructor.
        * constructor; auto. intro Hinm.
          apply Hninm. constructor (assumption).
    - now rewrite IHHperm1.
  Qed.
  
  Lemma InMembers_neq:
    forall x y xs,
      InMembers x xs ->
      ~ InMembers y xs ->
      x <> y.
  Proof.
    intros ** Hx Hy; subst.
    now apply Hx.
  Qed.

  Remark fst_InMembers:
    forall x xs,
      InMembers x xs <-> In x (map (@fst A B) xs).
  Proof.
    induction xs; simpl; intuition.
  Qed.

  Remark fst_NoDupMembers:
    forall xs,
      NoDupMembers xs <-> NoDup (map (@fst A B) xs).
  Proof.
    induction xs as [|(x,y)].
    - split; constructor.
    - simpl; split; inversion 1.
      + inversion H as [|? ? ? Notin ? Heq]; subst.
        constructor.
        * now rewrite <-fst_InMembers.
        * now apply IHxs.
      + constructor.
        * now rewrite fst_InMembers.
        * now apply IHxs.
  Qed.

  Lemma InMembers_In_combine:
    forall x (xs: list A) (ys: list B),
      InMembers x (combine xs ys) ->
      In x xs.
  Proof.
    induction xs as [|x' xs]; auto.
    destruct ys; [contradiction|].
    destruct 1 as [Heq|Hin].
    now subst; constructor.
    constructor (apply IHxs with (1:=Hin)).
  Qed.

  Lemma In_InMembers_combine:
    forall x (xs: list A) (ys: list B),
      length xs = length ys ->
      (In x xs <-> InMembers x (combine xs ys)).
  Proof.
    intros x xs ys Hlen.
    split; [|now apply InMembers_In_combine].
    revert x xs ys Hlen.
    induction xs as [|x' xs]; auto.
    intros ys Hlen Hin.
    destruct ys; [discriminate|].
    inversion Hin; subst; [now left|right].
    apply IHxs; auto.
  Qed.

  Lemma NoDup_NoDupMembers_combine:
    forall (xs: list A) (ys: list B),
    NoDup xs -> NoDupMembers (combine xs ys).
  Proof.
    induction xs as [|x xs]; [now intros; constructor|].
    intros ys Hndup.
    destruct ys; simpl; constructor.
    - inversion_clear Hndup.
      intro Hin. apply InMembers_In_combine in Hin.
      contradiction.
    - apply IHxs; auto. now inversion Hndup.
  Qed.

End InMembers.

Ltac app_NoDupMembers_det :=
  match goal with
  | H: NoDupMembers ?xs,
         H1: In (?x, ?t1) ?xs,
             H2: In (?x, ?t2) ?xs |- _ =>
      assert (t1 = t2) by (eapply NoDupMembers_det; eauto); subst t2; clear H2 
    end.

(** adds and its properties *)

Definition adds {A B} (xs : list (ident * B)) (vs : list A) (S : PM.t A) :=
  fold_right (fun (xbv: (ident * B) * A) env => 
                    let '(x , b, v) := xbv in
                    PM.add x v env) S (combine xs vs).

Lemma find_gsso:
  forall {A B} x x' (ty: A) xs (vs: list B) S,
    x <> x' ->
    PM.find x (adds ((x', ty) :: xs) vs S) = PM.find x (adds xs (tl vs) S).
Proof.
  intros ** Hneq.
  unfold adds.
  destruct vs. destruct xs; reflexivity.
  simpl. rewrite PM.gso; auto.
Qed.      

Lemma NotInMembers_find_adds:
  forall {A B} x (xs: list (ident * A)) (v: option B) vs S,
    ~InMembers x xs ->
    PM.find x S = v ->
    PM.find x (adds xs vs S) = v.
Proof.
  induction xs as [|xty xs]; auto.
  intros v vs S Hnin Hfind.
  apply NotInMembers_cons in Hnin.
  destruct Hnin as [Hnin Hneq].
  destruct xty as [x' ty].
  rewrite find_gsso; auto.
Qed.

Section Lists.

  Context {A B : Type}.
  
  Fixpoint concat (l : list (list A)) : list A :=
    match l with
    | nil => nil
    | cons x l => x ++ concat l
    end.

  Lemma concat_nil : concat nil = nil.
  Proof eq_refl. 

  Lemma concat_cons : forall x l, concat (cons x l) = x ++ concat l.
  Proof. simpl; reflexivity. Qed.
                               
  Lemma concat_app : forall l1 l2, concat (l1 ++ l2) = concat l1 ++ concat l2.
  Proof.
    induction l1; auto.
    intro.
    rewrite <-app_comm_cons.
    repeat rewrite concat_cons.
    rewrite <-app_assoc.
    f_equal; auto.
  Qed.

  Global Instance In_Permutation_Proper (A:Type):
    Proper (eq ==> Permutation (A:=A) ==> iff) (@In A).
  Proof.
    intros x y Hxy xs ys Hperm.
    subst y.
    split; intro HH; [|symmetry in Hperm];
      now apply Permutation_in with (1:=Hperm) in HH.
  Qed.
  
  Remark not_In_app:
    forall (x: A) l1 l2,
      ~ In x l2 ->
      In x (l1 ++ l2) ->
      In x l1.
  Proof.
    intros ** HnIn Hin.
    induction l1.
    - contradiction.
    - rewrite <-app_comm_cons in Hin.
      inversion Hin; subst.
      + apply in_eq.
      + right; now apply IHl1.
  Qed.
  
  Remark In_Forall:
    forall (x: A) xs P,
      Forall P xs ->
      In x xs ->
      P x.
  Proof.
    intros ** Hforall Hin.
    induction xs; inversion Hin; inversion Hforall; subst; auto.
  Qed.

  Remark map_cons':
    forall (f: A -> A) l y ys,
      map f l = y :: ys ->
      exists x xs, y = f x /\ ys = map f xs.
  Proof.
    destruct l; simpl; intros ** H.
    - contradict H. apply nil_cons.
    - exists a, l. inversion H; auto.
  Qed.

  Remark map_app':
    forall (f: A -> A) l1 l l2,
      map f l = l1 ++ l2 ->
      exists k1 k2, l1 = map f k1 /\ l2 = map f k2.
  Proof.
    induction l1; simpl; intros ** H.
    - exists [], l; auto.
    - apply map_cons' in H.
      destruct H as (x & xs & Ha & Happ).
      symmetry in Happ.
      apply IHl1 in Happ.
      destruct Happ as (k1 & k2 & Hl1 & Hl2).
      exists (x :: k1), k2; simpl; split; auto.
      f_equal; auto.
  Qed.

  Lemma incl_cons':
    forall (x: A) xs ys,
      incl (x :: xs) ys -> In x ys /\ incl xs ys.
  Proof.
    unfold incl; intuition.
  Qed.

  Lemma incl_nil:
    forall (xs: list A),
      incl xs [] -> xs = [].
  Proof.
    intros xs H.
    induction xs; auto.
    unfold incl in H.
    specialize (H a (in_eq a xs)).
    contradict H.
  Qed.

  Lemma Permutation_incl1:
    forall (ws: list A) xs ys,
      Permutation xs ys ->
      (incl xs ws <-> incl ys ws).
  Proof.
    intros ** Hperm.
    induction Hperm.
    - reflexivity.
    - split; intro HH.
      + apply incl_cons' in HH.
        destruct HH as [Hin Hincl].
        apply IHHperm in Hincl.
        apply incl_cons; auto.
      + apply incl_cons' in HH.
        destruct HH as [Hin Hincl].
        apply IHHperm in Hincl.
        apply incl_cons; auto.
    - split; intro HH.
      + apply incl_cons' in HH.
        destruct HH as (Hiny & HH).
        apply incl_cons' in HH.
        destruct HH as (Hinx & Hincl).
        repeat (apply incl_cons; auto).
      + apply incl_cons' in HH.
        destruct HH as (Hinx & HH).
        apply incl_cons' in HH.
        destruct HH as (Hiny & Hincl).
        repeat (apply incl_cons; auto).
    - now rewrite IHHperm1, IHHperm2.
  Qed.      

  Global Instance Permutation_incl_Proper:
    Proper (@Permutation A ==> @Permutation A ==> iff) (@incl A).
  Proof.
    intros xs ys Hperm xs' ys' Hperm'.
    induction Hperm'; try rewrite (Permutation_incl1 _ _ _ Hperm).
    - reflexivity.
    - split; intro HH.
      + intros y Hin.
        apply HH in Hin.
        inversion_clear Hin as [|Hin'].
        now subst; constructor.
        rewrite Hperm' in Hin'.
        constructor (assumption).
      + intros y Hin.
        apply HH in Hin.
        inversion_clear Hin as [|Hin'].
        now subst; constructor.
        rewrite <-Hperm' in Hin'.
        constructor (assumption).
    - split; intro HH.
      + intros z Hin. apply HH in Hin. now rewrite perm_swap.
      + intros z Hin. apply HH in Hin. now rewrite perm_swap.
    - rewrite (Permutation_incl1 _ _ _ Hperm) in IHHperm'1.
      rewrite (Permutation_incl1 _ _ _ Hperm) in IHHperm'2.
      now rewrite IHHperm'1, IHHperm'2.
  Qed.

  Lemma app_last_app:
    forall xs xs' (x: A),
      (xs ++ [x]) ++ xs' = xs ++ x :: xs'.
  Proof.
    induction xs; simpl; auto.
    intros; f_equal; apply IHxs.
  Qed.

  Lemma Forall2_length :
    forall (P : A -> B -> Prop) l1 l2,
      Forall2 P l1 l2 -> length l1 = length l2.
  Proof.
    induction l1, l2; intros ** Hall; inversion Hall; clear Hall; subst; simpl; auto.    
  Qed.

  (* should be in standard lib... *)
  Lemma not_in_cons (x a : A) (l : list A):
    ~ In x (a :: l) <-> x <> a /\ ~ In x l.
  Proof.
    split.
    - intro Notin.
      split.
      + intro Eq.
        apply Notin.
        rewrite Eq.
        apply in_eq.
      + intro In.
        apply Notin.
        apply in_cons; auto.
    - intros [Neq Notin] In.
      apply in_inv in In.
      destruct In.
      + apply Neq; auto.
      + apply Notin; auto.
  Qed.

  Lemma Forall_impl_In :
    forall (P Q : A -> Prop) l,
      (forall a, In a l -> P a -> Q a) ->
      Forall P l -> Forall Q l.
  Proof.
    induction l; auto.
    intros H HP.
    inversion_clear HP.
    constructor.
    - apply H; auto.
      apply in_eq.
    - apply IHl; auto.
      intros a' Ha' HP.
      apply H; auto.
      apply in_cons; auto.
  Qed.

  Lemma NoDup_map_inv (f:A->B) l : NoDup (map f l) -> NoDup l.
  Proof.
    induction l; simpl; inversion_clear 1; subst; constructor; auto.
    intro H. now apply (in_map f) in H.
  Qed.

  Lemma NoDup_cons':
    forall {A} (x:A) xs,
      NoDup (x::xs) <-> ~In x xs /\ NoDup xs.
  Proof.
    split; intro HH.
    - inversion_clear HH. intuition.
    - destruct HH. constructor; auto.
  Qed.
  
  Global Instance NoDup_Permutation_Proper (A:Type):
    Proper (Permutation (A:=A) ==> iff) (@NoDup A).
  Proof.
    intros xs ys Hperm.
    induction Hperm.
    - now intuition.
    - rewrite 2 NoDup_cons', IHHperm, Hperm.
      reflexivity.
    - split; inversion_clear 1 as [|? ? Hnin Hndup];
        inversion_clear Hndup as [|? ? Hnin' Hndup'];
        (constructor; [|constructor]); auto; intro Hnin3;
          apply Hnin.
      + inversion Hnin3; [|contradiction].
        subst. now constructor.
      + constructor (assumption).
      + inversion Hnin3; [|contradiction].
        subst. now constructor.
      + constructor (assumption).
    - now rewrite IHHperm1, IHHperm2.
  Qed.

  Lemma NoDup_app_weaken:
    forall {A} (xs: list A) ys,
      NoDup (xs ++ ys) ->
      NoDup xs.
  Proof.
    Hint Constructors NoDup.
    intros ** Hndup.
    induction xs as [|x xs]; auto.
    inversion_clear Hndup as [|? ? Hnin Hndup'].
    apply IHxs in Hndup'.
    constructor; auto.
    intro Hin. apply Hnin.
    apply in_or_app; now left.
  Qed.
  
  Lemma cons_is_app:
    forall (x: A) xs,
      x :: xs = [x] ++ xs.
  Proof.
    destruct xs; simpl; auto.
  Qed.

  Lemma permutation_partition:
    forall p (l: list A),
      Permutation l (fst (partition p l) ++ snd (partition p l)).
  Proof.
    induction l as [|x l].
    now constructor.
    simpl.
    destruct (p x).
    - rewrite (surjective_pairing (partition _ _)).
      now simpl; apply Permutation_cons.
    - rewrite (surjective_pairing (partition _ _)).
      now simpl; apply Permutation_cons_app.
  Qed.

  Lemma Permutation_app_assoc:
    forall (ws: list A) xs ys,
      Permutation ((ws ++ xs) ++ ys) (ws ++ xs ++ ys).
  Proof.
    intros.
    induction ws.
    reflexivity.
    now apply Permutation_cons.
  Qed.

  Lemma partition_switch:
    forall f g,
      (forall x:A, f x = g x) ->
      forall xs, partition f xs = partition g xs.
  Proof.
    intros ** Hfg xs.
    induction xs as [|x xs]; auto. simpl.
    specialize (Hfg x). symmetry in Hfg. rewrite Hfg, IHxs.
    reflexivity.
  Qed.

  Lemma partition_filter:
    forall P (xs: list A),
      Permutation (fst (partition P xs)) (filter P xs).
  Proof.
    induction xs as [|x xs]; auto.
    simpl; rewrite (surjective_pairing (partition P xs)).
    destruct (P x); auto.
    now apply Permutation_cons.
  Qed.
  
  Lemma filter_app:
    forall (p:A->bool) xs ys,
      filter p xs ++ filter p ys = filter p (xs ++ ys).
  Proof.
    induction xs as [|x xs]; intro ys; auto.
    simpl; destruct (p x); simpl; rewrite IHxs; auto.
  Qed.

  Global Instance Permutation_filter_Proper (p:A->bool):
    Proper (@Permutation A ==> @Permutation A) (filter p).
  Proof.
    Hint Constructors Permutation.
    intros xs ys Hperm.
    induction Hperm; simpl; auto.
    - destruct (p x); auto.
    - destruct (p x); destruct (p y); auto.
    - now rewrite IHHperm1, IHHperm2.
  Qed.
  
End Lists.

      
