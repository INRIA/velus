Require Import Coq.FSets.FMapPositive.
Require Import Nelist.
Require Import List.
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
Definition ident_eqb := Pos.eqb.

Implicit Type i j: ident.

Definition ne_adds {A} (is : nelist ident) (vs : nelist A) (S : PM.t A) :=
  Nelist.fold_right (fun (iiv: ident * A) env =>
                    let (i , iv) := iiv in
                    PM.add i iv env) S (Nelist.combine is vs).

Definition adds {A B} (xs : list (ident * B)) (vs : list A) (S : PM.t A) :=
  fold_right (fun (xbv: (ident * B) * A) env => 
                    let '(x , b, v) := xbv in
                    PM.add x v env) S (combine xs vs).

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

(** ** Basic types supported by CoreDF: *)

Inductive base_type := Tint | Tbool.
Inductive const : Set :=
| Cint : BinInt.Z -> const
| Cbool : bool -> const.

Implicit Type c: const.

Definition const_eqb (c1: const) (c2: const) : bool :=
  match c1, c2 with
  | Cint z1, Cint z2 => BinInt.Z.eqb z1 z2
  | Cbool b1, Cbool b2 => Bool.eqb b1 b2
  | _, _ => false
  end.

(** ** Universe for typed signatures *)

(** These definitions are used to specify and import external
operators *)

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
Definition operator := sigT arrows.
Definition get_arity : operator -> arity := @projT1 _ _.
Definition get_interp : forall op : operator, arrows (get_arity op) := @projT2 _ _.

(* length function *)
Fixpoint nb_args (ar : arity) :=
  match ar with
    | Tout _ => 0
    | Tcons t ar => S (nb_args ar)
  end.

(* list of argument types *)
Fixpoint arg_interp (ar : arity) :=
  match ar with
    | Tout _ => nil
    | Tcons t ar => cons (base_interp t) (arg_interp ar)
  end.

(* result type *)
Fixpoint res_interp (ar : arity) :=
  match ar with
    | Tout t => base_interp t
    | Tcons _ ar => res_interp ar
  end.

(* base_type of result to const *)
Definition base_to_const t :=
  match t as t' return base_interp t' -> const with
    | Tint => fun v => Cint v
    | Tbool => fun b => Cbool b
  end.

(** Two possible versions: 
    1) arguments must be correct
    2) arguments are checked to have the proper type *)

(* Version 1 *)
(* List of valid arguments *)
Inductive valid_args : arity -> Set :=
  | noArg : forall t_out, valid_args (Tout t_out)
  | moreArg : forall {t_in ar} (c : base_interp t_in) (l : valid_args ar), valid_args (Tcons t_in ar).

(* TODO: make a better definition *)
Fixpoint apply_arity_1 {ar : arity} (f : arrows ar) (args : valid_args ar) : res_interp ar.
destruct ar; simpl in *.
- exact f.
- inversion_clear args.
  exact (apply_arity_1 ar (f c) l).
Defined.

(* Version 2 *)
(* Predicate accepting list of valid arguments *)
(* Inductive Valid_args : arity -> nelist const -> Prop := *)
(*   | OneInt : forall t_out n, Valid_args (Tcons Tint (Tout t_out)) (nebase (Cint n)) *)
(*   | OneBool : forall t_out b, Valid_args (Tcons Tbool (Tout t_out)) (nebase (Cbool b)) *)
(*   | MoreInt : forall ar (n : Z) l, Valid_args ar l -> Valid_args (Tcons Tint ar) (necons (Cint n) l) *)
(*   | MoreBool : forall ar (b : bool) l, Valid_args ar l -> Valid_args (Tcons Tbool ar) (necons (Cbool b) l). *)

(* Fixpoint apply_arity (ar : arity) (l : nelist const) : arrows ar -> option const := *)
(*   match ar as ar', l return arrows ar' -> option const with *)
(*     | Tout _, _ => fun _ => None *)
(*     | Tcons Tint (Tout Tint), nebase (Cint n) => fun f => Some (Cint (f n)) *)
(*     | Tcons Tint (Tout Tbool), nebase (Cint n) => fun f => Some (Cbool (f n)) *)
(*     | Tcons Tbool (Tout Tint), nebase (Cbool b) => fun f => Some (Cint (f b)) *)
(*     | Tcons Tbool (Tout Tbool), nebase (Cbool b) => fun f => Some (Cbool (f b)) *)
(*     | Tcons Tint ar, necons (Cint n) l => fun f => apply_arity ar l (f n) *)
(*     | Tcons Tbool ar, necons (Cbool b) l => fun f => apply_arity ar l (f b) *)
(*     | _, _ => fun _ => None (* Wrong type or number of arguments *) *)
(*   end. *)

(* Definition apply_op (op : operator) (l : nelist const) : option const := *)
(*   apply_arity (get_arity op) l (get_interp op). *)

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

Lemma gsss:
  forall {A: Type} is (vs : nelist A) i a, Nelist.length is = Nelist.length vs ->
    (Assoc is vs i a <-> PM.find i (ne_adds is vs (PM.empty _)) = Some a).
Proof.
  Hint Constructors Assoc.
  intros * Hlen.
  split.
  - intros ** Hassoc; induction Hassoc; try contradiction; unfold ne_adds; simpl.
    * rewrite PM.gss; auto.
    * rewrite (@PM.gss A i); auto.
    * rewrite PM.gso; auto.
  - revert vs Hlen; induction is as [i1 |i1 is]; intros [v1 | v1 vs] Hlen;
    try now destruct is || destruct vs; simpl in Hlen; discriminate.
    + unfold ne_adds. simpl. intro Hfind.
      destruct (ident_eqb i i1) eqn:Heqi.
      * apply ident_eqb_eq in Heqi. subst.
        rewrite PM.gss in Hfind; injection Hfind; intro; subst; clear Hfind.
        econstructor.
      * apply ident_eqb_neq in Heqi.
        rewrite PM.gso, PM.gempty in Hfind; trivial. discriminate.
    + unfold ne_adds. simpl. intro Hfind.
      destruct (ident_eqb i i1) eqn:Heqi.
      * apply ident_eqb_eq in Heqi. subst.
        rewrite PM.gss in Hfind; injection Hfind; intro; subst; clear Hfind.
        econstructor.
      * apply ident_eqb_neq in Heqi.
        rewrite PM.gso in Hfind; auto.
Qed.

Lemma gsos:
  forall (A: Type) is vs (m : PM.t A) i, Nelist.length is = Nelist.length vs ->
    ~ Nelist.In i is ->
    PM.find i (ne_adds is vs m) = PM.find i m.
Proof.
  intros A is vs m i Hlen Hnin. revert vs Hlen.
  induction is as [i1 |i1 is]; intros [v1 |v1 vs] Hlen;
  try now destruct is || destruct vs; simpl in Hlen; discriminate.
  - unfold ne_adds; simpl; auto. now rewrite PM.gso.
  - simpl in Hlen. unfold ne_adds; simpl; auto.
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

(** *** About basic types *)

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


(** *** About operators *)

Lemma arity_dec : forall ar1 ar2 : arity, {ar1 = ar2} + {ar1 <> ar2}.
Proof. do 2 decide equality. Qed.

(* Must be postulated because we do not have decidable equality on function types.
   Can be avoided, if we add an id field with a decidable equality. *)
Axiom op_dec : forall op1 op2 : operator, {op1 = op2} + {op1 <> op2}.

Example plus : operator.
exists (Tcons Tint (Tcons Tint (Tout Tint))).
exact BinInt.Z.add.
Defined.

Definition op_eqb op1 op2 := if op_dec op1 op2 then true else false.

Lemma op_eqb_true_iff : forall op1 op2, op_eqb op1 op2 = true <-> op1 = op2.
Proof. intros op1 op2. unfold op_eqb. destruct (op_dec op1 op2); intuition discriminate. Qed.

Lemma op_eqb_false_iff : forall op1 op2, op_eqb op1 op2 = false <-> op1 <> op2.
Proof. intros op1 op2. unfold op_eqb. destruct (op_dec op1 op2); intuition discriminate. Qed.

(* Lemma Valid_args_length : forall ar l, Valid_args ar l -> Nelist.length l = nb_args ar. *)
(* Proof. intros ar l Hvalid. induction Hvalid; simpl; auto. Qed. *)

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

  Parameter true_val  : val.
  Parameter false_val : val.
  Axiom true_not_false_val : true_val <> false_val.

  Parameter bool_typ : typ.
  (* TODO: This operation is impossible! Get rid of it. *)
  Parameter typ_of_val: val -> typ.
  
  Parameter unary_op  : Type.
  Parameter binary_op : Type.

  Parameter sem_unary  : unary_op -> val -> typ -> option val.
  Parameter sem_binary : binary_op -> val -> typ -> val -> typ -> option val.

  Axiom val_dec   : forall v1 v2 : val, {v1 = v2} + {v1 <> v2}.
  Axiom typ_dec   : forall t1 t2 : typ, {t1 = t2} + {t1 <> t2}.
  Axiom unop_dec  : forall op1 op2 : unary_op, {op1 = op2} + {op1 <> op2}.
  Axiom binop_dec : forall op1 op2 : binary_op, {op1 = op2} + {op1 <> op2}.

End OPERATORS.

Module Type OPERATORS_AUX (Import Ops : OPERATORS).
  Require Export Coq.Classes.EquivDec.
  Close Scope equiv_scope.

  Instance: EqDec val eq := { equiv_dec := val_dec }.
  Instance: EqDec typ eq := { equiv_dec := typ_dec }.
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

  Lemma NoDupMembers_app:
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

End InMembers.

Ltac app_NoDupMembers_det :=
  match goal with
  | H: NoDupMembers ?xs,
       H1: In (?x, ?t1) ?xs,
           H2: In (?x, ?t2) ?xs |- _ =>
    assert (t1 = t2) by (eapply NoDupMembers_det; eauto); subst t2; clear H2 
  end.

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

  Lemma cons_is_app:
    forall (x: A) xs,
      x :: xs = [x] ++ xs.
  Proof.
    destruct xs; simpl; auto.
  Qed.
  
End Lists.
