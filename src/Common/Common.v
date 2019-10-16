From Coq Require Import FSets.FMapPositive.
From Coq Require Import FSets.FMapFacts.
From Coq Require Import List.
From Coq Require Import Sorting.Permutation.

From Coq Require Import Setoid.
From Coq Require Import Relations RelationPairs.
From Coq Require Import Morphisms.

Import ListNotations.
From Coq Require MSets.MSets.
From Coq Require Export PArith.
(* Require Import Omega. *)
From Coq Require Import Classes.EquivDec.

From Velus Require Export Common.CommonTactics.
From Velus Require Export Common.CommonList.
From Velus Require Export ClockDefs.

Open Scope list.

(** * Common definitions *)

(** ** Finite sets and finite maps *)

(** These modules are used to manipulate identifiers. *)


Module PS := Coq.MSets.MSetPositive.PositiveSet.
Module PSP := MSetProperties.WPropertiesOn Pos PS.
Module PSF := MSetFacts.Facts PS.
Module PSE := MSetEqProperties.WEqPropertiesOn Pos PS.
Module PSdec := Coq.MSets.MSetDecide.WDecide PS.

Definition ident_eq_dec := Pos.eq_dec.
Definition ident_eqb := Pos.eqb.

Instance: EqDec ident eq := { equiv_dec := ident_eq_dec }.

Implicit Type i j: ident.

(** ** Properties *)

Lemma not_or':
  forall A B, ~(A \/ B) <-> ~A /\ ~B.
Proof.
  split; intuition.
Qed.

Lemma flip_impl:
  forall {P Q : Prop},
    (P -> Q) ->
    ~Q ->
    ~P.
Proof. intros P Q HPQ HnQ HP. auto. Qed.

Lemma None_eq_dne:
  forall {A} (v : option A),
    ~(v <> None) <-> (v = None).
Proof.
  destruct v; intuition.
  exfalso. apply H; discriminate.
Qed.

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

Lemma ident_eqb_sym:
  forall x y, ident_eqb x y = ident_eqb y x.
Proof Pos.eqb_sym.

Lemma ident_eq_sym:
  forall (x y: ident), x = y <-> y = x.
Proof.
  now intros; split; subst.
Qed.

Lemma decidable_eq_ident:
  forall (f g: ident),
    Decidable.decidable (f = g).
Proof.
  intros f g.
  unfold Decidable.decidable.
  setoid_rewrite <-ident_eqb_eq.
  destruct (ident_eqb f g); auto.
Qed.

Lemma equiv_decb_negb:
  forall x, (x ==b negb x) = false.
Proof. destruct x; simpl; auto. Qed.

Definition mem_assoc_ident {A} (x: ident): list (ident * A) -> bool :=
  existsb (fun y => ident_eqb (fst y) x).

Lemma mem_assoc_ident_false:
  forall {A} x xs (t: A),
    mem_assoc_ident x xs = false ->
    ~ In (x, t) xs.
Proof.
  intros ** Hin.
  apply Bool.not_true_iff_false in H.
  apply H.
  apply existsb_exists.
  exists (x, t); split; auto.
  apply ident_eqb_refl.
Qed.

Lemma mem_assoc_ident_true:
  forall {A} x xs,
    mem_assoc_ident x xs = true ->
    exists t: A, In (x, t) xs.
Proof.
  intros * Hin.
  unfold mem_assoc_ident in Hin; rewrite existsb_exists in Hin.
  destruct Hin as ((x', t) & ? & E).
  simpl in E; rewrite ident_eqb_eq in E; subst x'.
  eauto.
Qed.

Definition assoc_ident {A} (x: ident) (xs: list (ident * A)): option A :=
  match find (fun y => ident_eqb (fst y) x) xs with
  | Some (_, a) => Some a
  | None => None
  end.

Module Type IDS.
  Parameter self : ident.
  Parameter out  : ident.

  Parameter step  : ident.
  Parameter reset : ident.

  Parameter default : ident.

  Definition reserved : list ident := [ self; out ].

  Definition methods  : list ident := [ step; reset ].

  Axiom reserved_nodup: NoDup reserved.
  Axiom methods_nodup: NoDup methods.

  Axiom reset_not_step: reset <> step.

  Definition NotReserved {typ: Type} (xty: ident * typ) : Prop :=
    ~In (fst xty) reserved.

  Parameter prefix : ident -> ident -> ident.

  Parameter valid : ident -> Prop.

  Inductive prefixed: ident -> Prop :=
    prefixed_intro: forall pref id,
      prefixed (prefix pref id).

  Axiom valid_not_prefixed: forall x, valid x -> ~prefixed x.

  Definition ValidId {typ: Type} (xty: ident * typ) : Prop :=
    NotReserved xty /\ valid (fst xty).

End IDS.

Generalizable Variables A.

Lemma equiv_decb_equiv:
  forall `{EqDec A} (x y : A),
    equiv_decb x y = true <-> equiv x y.
Proof.
  intros.
  split; intro; unfold equiv_decb in *;
    destruct (equiv_dec x y); intuition.
Qed.

Lemma nequiv_decb_false:
  forall {A} `{EqDec A} (x y: A),
    (x <>b y) = false <-> (x ==b y) = true.
Proof.
  unfold nequiv_decb, equiv_decb.
  intros. destruct (equiv_dec x y); intuition.
Qed.

Lemma equiv_decb_refl:
  forall `{EqDec A} (x: A),
    equiv_decb x x = true.
Proof.
  intros. now apply equiv_decb_equiv.
Qed.

Lemma nequiv_decb_refl:
  forall x, (x <>b x) = false.
Proof.
  intro x. unfold nequiv_decb.
  apply Bool.negb_false_iff, equiv_decb_refl.
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

Lemma value_neqb_neq:
  forall x y, x <> y <-> (x <>b y) = true.
Proof.
  intros x y. unfold nequiv_decb. split; intro HH.
  - now apply Bool.negb_true_iff, not_equiv_decb_equiv.
  - intro; subst.
    apply Bool.negb_true_iff in HH.
    now rewrite equiv_decb_refl in HH.
Qed.

Lemma not_in_filter_nequiv_decb:
  forall y xs,
    ~In y xs ->
    filter (nequiv_decb y) xs = xs.
Proof.
  induction xs as [|x xs IH]; auto.
  intro Ny. apply not_in_cons in Ny as (Ny1 & Ny2). simpl.
  apply value_neqb_neq in Ny1 as ->.
  now apply IH in Ny2 as ->.
Qed.

(** *** About Coq stdlib *)

Lemma pos_le_plus1:
  forall x, (x <= x + 1)%positive.
Proof.
  intros.
  rewrite Pos.add_1_r.
  apply Pos.lt_eq_cases.
  left; apply Pos.lt_succ_diag_r.
Qed.

Lemma pos_lt_plus1:
  forall x, (x < x + 1)%positive.
Proof.
  intros. rewrite Pos.add_1_r. apply Pos.lt_succ_diag_r.
Qed.

Lemma PS_In_In_mem_mem:
  forall x m n,
    PS.In x m <-> PS.In x n <-> PS.mem x m = PS.mem x n.
Proof.
  intros x m n.
  destruct (PS.mem x n) eqn:Heq.
  - rewrite <- PS.mem_spec. intuition.
  - rewrite <-PSE.MP.Dec.F.not_mem_iff.
    apply PSE.MP.Dec.F.not_mem_iff in Heq. intuition.
Qed.

Lemma not_None_is_Some:
  forall A (x : option A), x <> None <-> (exists v, x = Some v).
Proof.
  destruct x; intuition.
  exists a; reflexivity.
  discriminate.
  match goal with H:exists _, _ |- _ => destruct H end; discriminate.
Qed.

Corollary not_None_is_Some_Forall:
  forall {A} (xs: list (option A)),
    Forall (fun (v: option A) => ~ v = None) xs ->
    exists ys, xs = map Some ys.
Proof.
  induction 1 as [|?? E].
    - exists []; simpl; eauto.
    - rewrite not_None_is_Some in E. destruct E as (v, E).
      destruct IHForall as (vs & ?); subst.
      exists (v :: vs); simpl; eauto.
Qed.

Lemma not_Some_is_None:
  forall A (x : option A),  (forall v, x <> Some v) <-> x = None.
Proof.
  destruct x; intuition.
  - exfalso; now apply (H a).
  - discriminate.
  - discriminate.
Qed.


(** Lemmas on PositiveSets *)

Definition not_In_empty: forall x : ident, ~(PS.In x PS.empty) := PS.empty_spec.

Ltac not_In_empty :=
  match goal with H:PS.In _ PS.empty |- _ => now apply not_In_empty in H end.

Lemma not_not_in:
  forall x A, ~~PS.In x A <-> PS.In x A.
Proof.
  split; intro HH.
  now apply Decidable.not_not in HH; intuition.
  now apply Decidable.not_not; intuition.
Qed.

Lemma PS_not_inter:
  forall s t x,
    ~PS.In x (PS.inter s t) <-> ~PS.In x s \/ ~PS.In x t.
Proof.
  setoid_rewrite PS.inter_spec.
  split; intro HH.
  apply Decidable.not_and in HH; auto using PSdec.MSetDecideAuxiliary.dec_In.
  intuition.
Qed.

Lemma PS_union_diff_same:
  forall s t,
    PS.Equal (PS.union (PS.diff s t) t) (PS.union s t).
Proof.
  unfold PS.Equal. setoid_rewrite PS.union_spec.
  setoid_rewrite PS.diff_spec.
  split; intro HH. now intuition.
  destruct HH. now destruct (PSP.In_dec a t); intuition.
  now intuition.
Qed.

Lemma PS_not_union:
  forall s t x,
    ~PS.In x (PS.union s t) <-> ~PS.In x s /\ ~PS.In x t.
Proof.
  setoid_rewrite PS.union_spec.
  split; intro HH; intuition.
Qed.

Lemma PS_not_diff:
  forall s t x,
    ~PS.In x (PS.diff s t) <-> ~PS.In x s \/ PS.In x (PS.inter s t).
Proof.
  setoid_rewrite PS.inter_spec.
  setoid_rewrite PS.diff_spec.
  split; intro HH.
  - apply Decidable.not_and in HH; auto using PSdec.MSetDecideAuxiliary.dec_In.
    destruct HH as [HH|HH]; auto.
    apply Decidable.not_not in HH; auto using PSdec.MSetDecideAuxiliary.dec_In.
    destruct (PSP.In_dec x s); auto.
  - destruct 1; destruct HH as [|[? ?]]; auto.
Qed.

Lemma PS_disjoint1:
  forall s1 s2,
    PS.Empty (PS.inter s1 s2) ->
    forall x, PS.In x s1 -> ~PS.In x s2.
Proof.
  intros s1 s2 Hdj x Hin1 Hin2.
  apply (Hdj x). rewrite PS.inter_spec; auto.
Qed.

Lemma PS_disjoint2:
  forall s1 s2,
    PS.Empty (PS.inter s1 s2) ->
    forall x, PS.In x s2 -> ~PS.In x s1.
Proof.
  setoid_rewrite PSP.inter_sym. eauto using PS_disjoint1.
Qed.

Lemma PS_diff_inter_same:
  forall A B C,
    PS.Equal (PS.diff (PS.inter A C) (PS.inter B C))
             (PS.inter (PS.diff A B) C).
Proof.
  intros A B C x. split; intro HH.
  - apply PS.diff_spec in HH.
    destruct HH as (HAC & HBC).
    apply PSP.FM.inter_3; [apply PSP.FM.diff_3|];
      eauto using PSF.inter_1, PSF.inter_2, PSF.inter_3.
  - apply PS.inter_spec in HH.
    destruct HH as (HAB & HC).
    apply PS.diff_spec in HAB.
    destruct HAB as (HA & HB).
    apply PSP.FM.diff_3; [apply PSP.FM.inter_3|];
      eauto using PSF.inter_1, PSF.inter_2, PSF.inter_3.
Qed.

Lemma PS_inter_union_dist:
  forall A B C D,
    PS.Equal (PS.inter (PS.union A B) (PS.union C D))
             (PS.union (PS.inter A C)
                       (PS.union (PS.inter A D)
                                 (PS.union (PS.inter B C)
                                           (PS.inter B D)))).
Proof.
  intros A B C D.
  split; intro HH.
  - rewrite PS.inter_spec in HH.
    setoid_rewrite PS.union_spec in HH.
    destruct HH as [[H1|H1] [H2|H2]]; intuition.
  - repeat setoid_rewrite PS.union_spec in HH.
    repeat setoid_rewrite PS.inter_spec in HH.
    destruct HH as [[HH1 HH2]|[[HH1 HH2]|[[HH1 HH2]|[HH1 HH2]]]];
      intuition.
Qed.

Lemma PS_inter_inter_same:
  forall A B C,
    PS.Equal (PS.inter (PS.inter A C) (PS.inter B C))
             (PS.inter (PS.inter A B) C).
Proof.
  split; intro HH; repeat rewrite PS.inter_spec in *; intuition.
Qed.

Lemma PS_For_all_Forall:
  forall P s,
    PS.For_all P s <-> Forall P (PS.elements s).
Proof.
  split; intro HH.
  - apply Forall_forall.
    intros x Hin. apply HH.
    apply PSF.elements_iff; auto.
  - intros x Hin.
    rewrite Forall_forall in HH; apply HH.
    apply PSF.elements_iff, SetoidList.InA_alt in Hin.
    destruct Hin as (? & ? & ?); subst; auto.
Qed.

Lemma PS_not_in_diff:
  forall x s t,
    ~PS.In x t ->
    ~PS.In x (PS.diff s t) ->
    ~PS.In x s.
Proof.
  setoid_rewrite PS.diff_spec. intuition.
Qed.

Lemma PS_For_all_empty:
  forall P,
    PS.For_all P PS.empty.
Proof.
  setoid_rewrite PS_For_all_Forall.
  setoid_rewrite PSP.elements_empty. auto.
Qed.

Lemma PS_In_Forall:
  forall P S,
    PS.For_all P S ->
    forall x, PS.In x S -> P x.
Proof.
  intros P S Hfa x Hin.
  apply PS_For_all_Forall in Hfa.
  apply PSP.FM.elements_iff in Hin.
  eapply Forall_forall in Hfa; eauto.
  apply SetoidList.InA_alt in Hin as (y & Heq & ?).
  subst; auto.
Qed.

Lemma PS_For_all_sub:
  forall P S T,
    PS.For_all P S ->
    (forall x, PS.In x T -> PS.In x S) ->
    PS.For_all P T.
Proof.
  intros P S T HP Hsub x HT.
  apply Hsub in HT.
  apply PS_In_Forall with (1:=HP) (2:=HT).
Qed.

Lemma PS_For_all_diff:
  forall P S T,
    PS.For_all P S ->
    PS.For_all P (PS.diff S T).
Proof.
  intros P S T HP. apply PS_For_all_sub with (1:=HP).
  intros x HH; apply PS.diff_spec in HH; intuition.
Qed.

Lemma PS_For_all_inter:
  forall P S T,
    PS.For_all P S ->
    PS.For_all P (PS.inter S T).
Proof.
  intros P S T HP. apply PS_For_all_sub with (1:=HP).
  intros x HH; apply PS.inter_spec in HH; intuition.
Qed.

Lemma PS_For_all_union:
  forall P S T,
    PS.For_all P S ->
    PS.For_all P T ->
    PS.For_all P (PS.union S T).
Proof.
  intros P S T HS HT x HH.
  apply PS.union_spec in HH as [HH|HH]; intuition.
Qed.

Lemma PS_For_all_impl_In:
  forall (P Q : PS.elt -> Prop) S,
    PS.For_all P S ->
    (forall x, PS.In x S -> P x -> Q x) ->
    PS.For_all Q S.
Proof.
  intros P Q S HP HPQ x HS.
  apply PS_In_Forall with (2:=HS) in HP; auto.
Qed.

Instance PS_For_all_Equals_Proper:
  Proper (pointwise_relation positive iff ==> PS.Equal ==> iff) PS.For_all.
Proof.
  intros P Q Hpw S T Heq.
  split; intros HH x Hx; apply PS_In_Forall with (x:=x) in HH;
    try apply Hpw; auto.
  now rewrite Heq. now rewrite Heq in Hx.
Qed.

Lemma PS_For_all_add:
  forall P a S,
    PS.For_all P (PS.add a S) <-> (P a /\ PS.For_all P S).
Proof.
  split.
  - intro HH. split.
    + apply PS_In_Forall with (1:=HH).
      now apply PS.add_spec; left.
    + apply PS_For_all_sub with (1:=HH).
      intros; apply PS.add_spec; auto.
  - intros (HPa, HPS) x Hadd.
    apply PS.add_spec in Hadd as [HH|HH]; subst; auto.
Qed.

Lemma In_PS_elements:
  forall x s,
    In x (PS.elements s) <-> PS.In x s.
Proof.
  intros x s. split; intro HH.
  - now apply (SetoidList.In_InA Pos.eq_equiv), PSF.elements_2 in HH.
  - cut (exists z, eq x z /\ In z (PS.elements s)).
    + intros (? & ? & ?); subst; auto.
    + now apply SetoidList.InA_alt, PSF.elements_1.
Qed.

Lemma Permutation_elements_add:
  forall xs x s,
    Permutation (PS.elements s) xs ->
    ~PS.In x s ->
    Permutation (PS.elements (PS.add x s)) (x::xs).
Proof.
  intros * Hperm Hnin.
  setoid_rewrite <- Hperm; clear Hperm.
  apply NoDup_Permutation.
  - apply NoDup_NoDupA, PS.elements_spec2w.
  - constructor; [|now apply NoDup_NoDupA, PS.elements_spec2w].
    setoid_rewrite PSF.elements_iff in Hnin; auto.
  - clear. intro z.
    setoid_rewrite In_PS_elements.
    setoid_rewrite PS.add_spec.
    split; intros [HH|HH]; subst; auto.
    + now constructor.
    + now constructor 2; apply In_PS_elements.
    + apply In_PS_elements in HH; auto.
Qed.

Add Morphism PS.elements
    with signature PS.Equal ==> @Permutation positive
        as PS_elements_Equal.
Proof.
  intros x y Heq.
  apply NoDup_Permutation;
    (try apply NoDup_NoDupA, PS.elements_spec2w).
  now setoid_rewrite In_PS_elements.
Qed.

Lemma Permutation_PS_elements_of_list:
  forall xs,
    NoDup xs ->
    Permutation (PS.elements (PSP.of_list xs)) xs.
Proof.
  induction xs as [|x xs IH]; auto.
  rewrite NoDup_cons'. intros (Hxni & Hnd).
  simpl. specialize (IH Hnd).
  setoid_rewrite (Permutation_elements_add xs); auto.
  rewrite PSP.of_list_1.
  rewrite SetoidList.InA_alt.
  intros (y & Hxy & Hyin); subst; auto.
Qed.

Definition ps_adds (xs: list positive) (s: PS.t) :=
  fold_left (fun s x => PS.add x s) xs s.

Definition ps_from_list (l: list positive) : PS.t :=
  ps_adds l PS.empty.

Lemma ps_adds_spec:
  forall s xs y,
    PS.In y (ps_adds xs s) <-> In y xs \/ PS.In y s.
Proof.
  intros s xs y. revert s.
  induction xs; intro s; simpl.
  - intuition.
  - rewrite IHxs. rewrite PS.add_spec. intuition.
Qed.

Instance eq_equiv : Equivalence PS.eq.
Proof. firstorder. Qed.

Instance ps_adds_Proper (xs: list ident) :
  Proper (PS.eq ==> PS.eq) (ps_adds xs).
Proof.
  induction xs as [|x xs IH]; intros S S' Heq; [exact Heq|].
  assert (PS.eq (PS.add x S) (PS.add x S')) as Heq'
      by (rewrite Heq; reflexivity).
  simpl; rewrite Heq'; reflexivity.
Qed.

Lemma add_ps_from_list_cons:
  forall xs x,
    PS.eq (PS.add x (ps_from_list xs))
          (ps_from_list (x :: xs)).
Proof.
  intros; unfold ps_from_list; simpl.
  generalize PS.empty as S.
  induction xs as [|y xs IH]; [ reflexivity | ].
  intro S; simpl; rewrite IH; rewrite PSP.add_add; reflexivity.
Qed.

Lemma ps_from_list_In:
  forall xs x,
    PS.In x (ps_from_list xs) <-> In x xs.
Proof.
  induction xs; simpl.
  - split; try contradiction; apply not_In_empty.
  - split; intros * Hin.
    + rewrite <-IHxs.
      rewrite <-add_ps_from_list_cons in Hin.
      apply PSE.MP.Dec.F.add_iff in Hin as []; auto.
    + rewrite <-IHxs in Hin; rewrite <-add_ps_from_list_cons, PS.add_spec; intuition.
Qed.

Instance ps_from_list_Permutation:
  Proper (@Permutation.Permutation ident ==> fun xs xs' => forall x, PS.In x xs -> PS.In x xs')
         ps_from_list.
Proof.
  intros * ?? E ? Hin.
  apply ps_from_list_In; apply ps_from_list_In in Hin.
  now rewrite <-E.
Qed.

Lemma ps_adds_In:
  forall x xs s,
    PS.In x (ps_adds xs s) ->
    ~PS.In x s ->
    In x xs.
Proof.
  induction xs as [|x' xs IH]. now intuition.
  simpl. intros s Hin Hnin.
  apply ps_adds_spec in Hin.
  rewrite PSF.add_iff in Hin.
  destruct Hin as [|[Hin|Hin]]; intuition.
Qed.

Lemma Permutation_PS_elements_ps_adds:
  forall xs S,
    NoDup xs ->
    Forall (fun x => ~PS.In x S) xs ->
    Permutation (PS.elements (ps_adds xs S)) (xs ++ PS.elements S).
Proof.
  induction xs as [|x xs IH]; auto.
  intros S Hnd Hni.
  apply NoDup_Permutation.
  - apply NoDup_NoDupA, PS.elements_spec2w.
  - apply NoDup_app'; auto.
    apply NoDup_NoDupA, PS.elements_spec2w.
    apply Forall_impl_In with (2:=Hni).
    setoid_rewrite In_PS_elements; auto.
  - apply NoDup_cons' in Hnd as (Hnxs & Hnd).
    apply Forall_cons2 in Hni as (HnS & Hni).
    simpl; intro y.
    setoid_rewrite (IH _ Hnd).
    + repeat rewrite in_app.
      repeat rewrite In_PS_elements.
      rewrite PS.add_spec.
      split; intros [HH|[HH|HH]]; auto.
    + apply Forall_impl_In with (2:=Hni).
      intros z Hzxs Hnzs HzxS.
      apply PSF.add_3 in HzxS; auto.
      intro; subst; auto.
Qed.

Lemma Subset_ps_adds:
  forall xs S S',
    PS.Subset S S' ->
    PS.Subset (ps_adds xs S) (ps_adds xs S').
Proof.
  induction xs as [|x xs IH]; auto.
  intros S S' Hsub. simpl. apply IH.
  rewrite Hsub. reflexivity.
Qed.

Definition ps_removes (xs: list positive) (s: PS.t)
  := fold_left (fun s x => PS.remove x s) xs s.

Lemma ps_removes_spec: forall s xs y,
    PS.In y (ps_removes xs s) <-> ~In y xs /\ PS.In y s.
Proof.
  intros s xs y. revert s.
  induction xs; intro s; simpl.
  - intuition.
  - rewrite IHxs. rewrite PS.remove_spec. intuition.
Qed.

Lemma PS_For_all_ps_adds:
  forall P xs S,
    PS.For_all P (ps_adds xs S) <-> (Forall P xs /\ PS.For_all P S).
Proof.
  induction xs. now intuition.
  simpl. setoid_rewrite IHxs.
  setoid_rewrite Forall_cons2.
  setoid_rewrite PS_For_all_add.
  intuition.
Qed.

Lemma ps_adds_of_list:
  forall xs,
    PS.Equal (ps_adds xs PS.empty) (PSP.of_list xs).
Proof.
  intros xs x. rewrite ps_adds_spec, PSP.of_list_1; split.
  -intros [Hin|Hin]; auto. now apply not_In_empty in Hin.
  - intro Hin. apply SetoidList.InA_alt in Hin as (y & Hy & Hin); subst; auto.
Qed.

(** Miscellaneous *)

Lemma relation_equivalence_subrelation:
  forall {A} (R1 R2 : relation A),
    relation_equivalence R1 R2 <-> (subrelation R1 R2 /\ subrelation R2 R1).
Proof.
  intros.
  unfold relation_equivalence, predicate_equivalence,
  pointwise_lifting, subrelation. firstorder.
Qed.

(** types and clocks *)

Section TypesAndClocks.

  Context {type clock : Type}.

  (* A Lustre variable is declared with a type and a clock.
     In the abstract syntax, a declaration is represented as a triple:
     (x, (ty, ck)) : ident * (type * clock)

     And nodes include lists of triples for lists of declarations.
     The following definitions and lemmas facilitate working with such
     values. *)

  (* Definition dty (x : ident * (type * clock)) : type := fst (snd x). *)
  (* Definition dck (x : ident * (type * clock)) : clock := snd (snd x). *)

  Definition idty : list (ident * (type * clock)) -> list (ident * type) :=
    map (fun xtc => (fst xtc, fst (snd xtc))).

  Definition idck : list (ident * (type * clock)) -> list (ident * clock) :=
    map (fun xtc => (fst xtc, snd (snd xtc))).

  (* idty *)

  Lemma idty_app:
    forall xs ys,
      idty (xs ++ ys) = idty xs ++ idty ys.
  Proof.
    induction xs; auto.
    simpl; intro; now rewrite IHxs.
  Qed.

  Lemma InMembers_idty:
    forall x xs,
      InMembers x (idty xs) <-> InMembers x xs.
  Proof.
    induction xs as [|x' xs]; split; auto; intro HH;
      destruct x' as (x' & tyck); simpl.
    - rewrite <-IHxs; destruct HH; auto.
    - rewrite IHxs. destruct HH; auto.
  Qed.

  Lemma NoDupMembers_idty:
    forall xs,
      NoDupMembers (idty xs) <-> NoDupMembers xs.
  Proof.
    induction xs as [|x xs]; split; inversion_clear 1;
      eauto using NoDupMembers_nil; destruct x as (x & tyck); simpl in *;
      constructor; try rewrite InMembers_idty in *;
      try rewrite IHxs in *; auto.
  Qed.

  Lemma map_fst_idty:
    forall xs,
      map fst (idty xs) = map fst xs.
  Proof.
    induction xs; simpl; try rewrite IHxs; auto.
  Qed.

  Lemma length_idty:
    forall xs,
      length (idty xs) = length xs.
  Proof.
    induction xs as [|x xs]; auto.
    destruct x; simpl. now rewrite IHxs.
  Qed.

  Lemma In_idty_exists:
    forall x (ty : type) xs,
      In (x, ty) (idty xs) <-> exists (ck: clock), In (x, (ty, ck)) xs.
  Proof.
    induction xs as [|x' xs].
    - split; inversion_clear 1. inv H0.
    - split.
      + inversion_clear 1 as [HH|HH];
          destruct x' as (x' & ty' & ck'); simpl in *.
        * inv HH; eauto.
        * apply IHxs in HH; destruct HH; eauto.
      + destruct 1 as (ck & HH).
        inversion_clear HH as [Hin|Hin].
        * subst; simpl; auto.
        * constructor 2; apply IHxs; eauto.
  Qed.

  Lemma idty_InMembers:
    forall x ty (xs : list (ident * (type * clock))),
      In (x, ty) (idty xs) ->
      InMembers x xs.
  Proof.
    intros * Ix.
    unfold idty in Ix.
    apply in_map_iff in Ix as ((y, (yt, yc)) & Dy & Iy). inv Dy.
    apply In_InMembers with (1:=Iy).
  Qed.

  Global Instance idty_Permutation_Proper:
    Proper (@Permutation (ident * (type * clock))
            ==> @Permutation (ident * type)) idty.
  Proof.
    intros xs ys Hperm.
    unfold idty. rewrite Hperm.
    reflexivity.
  Qed.

  (* idck *)

  Lemma idck_app:
    forall xs ys,
      idck (xs ++ ys) = idck xs ++ idck ys.
  Proof.
    induction xs; auto.
    simpl; intro; now rewrite IHxs.
  Qed.

  Lemma InMembers_idck:
    forall x xs,
      InMembers x (idck xs) <-> InMembers x xs.
  Proof.
    induction xs as [|x' xs]; split; auto; intro HH;
      destruct x' as (x' & tyck); simpl.
    - rewrite <-IHxs; destruct HH; auto.
    - rewrite IHxs. destruct HH; auto.
  Qed.

  Lemma NoDupMembers_idck:
    forall xs,
      NoDupMembers (idck xs) <-> NoDupMembers xs.
  Proof.
    induction xs as [|x xs]; split; inversion_clear 1;
      eauto using NoDupMembers_nil; destruct x as (x & tyck); simpl in *;
      constructor; try rewrite InMembers_idck in *;
      try rewrite IHxs in *; auto.
  Qed.

  Lemma map_fst_idck:
    forall xs,
      map fst (idck xs) = map fst xs.
  Proof.
    induction xs; simpl; try rewrite IHxs; auto.
  Qed.

  Lemma length_idck:
    forall xs,
      length (idck xs) = length xs.
  Proof.
    induction xs as [|x xs]; auto.
    destruct x; simpl. now rewrite IHxs.
  Qed.

  Lemma In_idck_exists:
    forall x (ck : clock) xs,
      In (x, ck) (idck xs) <-> exists (ty: type), In (x, (ty, ck)) xs.
  Proof.
    induction xs as [|x' xs].
    - split; inversion_clear 1. inv H0.
    - split.
      + inversion_clear 1 as [HH|HH];
          destruct x' as (x' & ty' & ck'); simpl in *.
        * inv HH; eauto.
        * apply IHxs in HH; destruct HH; eauto.
      + destruct 1 as (ty & HH).
        inversion_clear HH as [Hin|Hin].
        * subst; simpl; auto.
        * constructor 2; apply IHxs; eauto.
  Qed.

  Global Instance idck_Permutation_Proper:
    Proper (Permutation (A:=(ident * (type * clock)))
            ==> Permutation (A:=(ident * clock))) idck.
  Proof.
    intros xs ys Hperm.
    unfold idck. rewrite Hperm.
    reflexivity.
  Qed.

  Lemma filter_fst_idck:
    forall (xs: list (ident * (type * clock))) P,
      idck (filter (fun x => P (fst x)) xs) = filter (fun x => P (fst x)) (idck xs).
  Proof.
    induction xs; simpl; intros; auto.
    cases; simpl; now rewrite IHxs.
  Qed.

End TypesAndClocks.

(** Sets and maps of identifiers as efficient list lookups *)

Section Ps_From_Fo_List.

  Context {A : Type} (f: A -> option ident).

  Definition ps_from_fo_list' (xs: list A) (s: PS.t) : PS.t :=
    fold_left (fun s x=> match f x with
                      | None => s
                      | Some i => PS.add i s
                      end) xs s.

  Definition ps_from_fo_list (xs: list A) : PS.t :=
    ps_from_fo_list' xs PS.empty.

  Lemma In_ps_from_fo_list':
    forall x xs s,
      PS.In x (ps_from_fo_list' xs s) ->
      PS.In x s \/ In (Some x) (map f xs).
  Proof.
    induction xs as [|x' xs IH]; simpl; auto.
    intros s Hin.
    destruct (f x'); apply IH in Hin as [Hin|Hin]; auto.
    destruct (ident_eq_dec i x); subst; auto.
    rewrite PSF.add_neq_iff in Hin; auto.
  Qed.

End Ps_From_Fo_List.

Lemma In_of_list_InMembers:
  forall {A} x (xs : list (ident * A)),
    PS.In x (PSP.of_list (map fst xs)) <-> InMembers x xs.
Proof.
  split; intros Hin.
  - apply PSP.of_list_1, SetoidList.InA_alt in Hin as (y & Heq & Hin); subst y.
    now apply fst_InMembers.
  - apply PSP.of_list_1, SetoidList.InA_alt.
    apply fst_InMembers in Hin. eauto.
Qed.

(** Useful functions on lists of options *)

Section OptionLists.

  Context {A B : Type}.

  Definition omap (f : A -> option B) (xs : list A) : option (list B) :=
    List.fold_right (fun x ys => match f x, ys with
                              | Some y, Some ys => Some (y :: ys)
                              | _, _ => None
                              end) (Some []) xs.

  Definition ofold_right (f : A -> B -> option B) (acc : option B) (xs : list A)
    : option B :=
    fold_right (fun x acc => match acc with
                          | Some acc => f x acc
                          | None => None
                          end) acc xs.

End OptionLists.

(** Lift relations into the option type *)

Section ORel.

  Context {A : Type}
          (R : relation A).

  Inductive orel : relation (option A) :=
  | Oreln : orel None None
  | Orels : forall sx sy, R sx sy -> orel (Some sx) (Some sy).

  Global Instance orel_refl `{RR : Reflexive A R} : Reflexive orel.
  Proof.
    intro sx.
    destruct sx; constructor; auto.
  Qed.

  Global Instance orel_trans `{RT : Transitive A R} : Transitive orel.
  Proof.
    intros sx sy sz XY YZ.
    inv XY; inv YZ; try discriminate; constructor.
    transitivity sy0; auto.
  Qed.

  Global Instance orel_sym `{RS : Symmetric A R} : Symmetric orel.
  Proof.
    intros sx sy XY. inv XY; constructor; symmetry; auto.
  Qed.

  Global Instance orel_equiv `{Equivalence A R} : Equivalence orel.
  Proof (Build_Equivalence orel orel_refl orel_sym orel_trans).

  Global Instance orel_preord `{PreOrder A R} : PreOrder orel.
  Proof (Build_PreOrder orel orel_refl orel_trans).

  Global Instance orel_Some_Proper: Proper (R ==> orel) Some.
  Proof.
    intros x y Rxy. right. eauto.
  Qed.

  Global Instance orel_Proper `{Symmetric A R} `{Transitive A R} :
    Proper (orel ==> orel ==> iff) orel.
  Proof.
    intros ox1 ox2 ORx oy1 oy2 ORy.
    split; intro HH.
    - symmetry in ORx. transitivity ox1; auto. transitivity oy1; auto.
    - symmetry in ORy. transitivity ox2; auto. transitivity oy2; auto.
  Qed.

  Lemma orel_inversion:
    forall x y, orel (Some x) (Some y) <-> R x y.
  Proof.
    split.
    - now inversion 1.
    - intro Rxy. eauto using orel.
  Qed.

End ORel.

Arguments orel {A}%type R%signature.
Hint Extern 4 (orel _ None None) => now constructor.
Hint Extern 5 (orel _ ?x ?x) => reflexivity.

Lemma orel_eq {A : Type} :
  forall x y, orel (@eq A) x y <-> x = y.
Proof.
  intros x y. destruct x, y; split; intro HH; try discriminate; inv HH; auto.
Qed.

Lemma orel_eq_weaken:
  forall {A} R `{Reflexive A R} (x y : option A),
    x = y -> orel R x y.
Proof.
  now intros A R RR x y Exy; subst.
Qed.

Instance orel_option_map_Proper
         {A B} (RA : relation A) (RB : relation B) `{Equivalence B RB}:
  Proper ((RA ==> RB) ==> orel RA ==> orel RB) (@option_map A B).
Proof.
  intros f' f Ef oa' oa Eoa.
  destruct oa'; destruct oa; simpl; inv Eoa; auto.
  take (RA _ _) and specialize (Ef _ _ it).
  now rewrite Ef.
Qed.

Instance orel_option_map_pointwise_Proper
         {A B} (RA : relation A) (RB : relation B)
         `{Equivalence B RB}:
  Proper (pointwise_relation A RB ==> eq ==> orel RB) (@option_map A B).
Proof.
  intros f' f Hf oa' oa Eoa; subst.
  destruct oa; simpl; [|reflexivity].
  apply orel_inversion.
  rewrite Hf. reflexivity.
Qed.

Instance orel_subrelation {A} (R1 R2 : relation A) `{subrelation A R1 R2}:
  subrelation (orel R1) (orel R2).
Proof.
  intros xo yo Ro.
  destruct xo, yo; inv Ro; constructor; auto.
Qed.

(* Should not be necessary, but rewriting through RelProd is often
   very slow or fails. *)
Lemma orel_pair:
  forall {A B} (RA: relation A) (RB: relation B)
    a1 a2 b1 b2,
    RA a1 a2 ->
    RB b1 b2 ->
    orel (RelationPairs.RelProd RA RB) (Some (a1, b1)) (Some (a2, b2)).
Proof.
  intros until b2. intros Ea Eb.
  constructor; auto.
Qed.

Instance orel_subrelation_Proper {A}:
  Proper (@subrelation A ==> eq ==> eq ==> Basics.impl) orel.
Proof.
  intros R2 R1 HR ox2 ox1 ORx oy2 oy1 ORy HH; subst.
  destruct ox1, oy1; inv HH; auto.
  take (R2 _ _) and apply HR in it. now constructor.
Qed.

Instance orel_equivalence_Proper {A}:
  Proper (@relation_equivalence A ==> eq ==> eq ==> iff) orel.
Proof.
  intros R2 R1 HR ox2 ox1 ORx oy2 oy1 ORy; subst.
  apply relation_equivalence_subrelation in HR as (HR1 & HR2).
  split; intro HH. now setoid_rewrite <-HR1. now setoid_rewrite <-HR2.
Qed.

(** The option monad *)

(* Do notation, lemmas and tactis for the option monad taken directly
     from CompCert's error_monad_scope (X. Leroy).

     We introduce several operators to facilitate Proper lemmas around the
     orel relation and a notation for improved readability. *)

Definition obind {A B: Type} (f: option A) (g: A -> option B) : option B :=
  match f with
  | Some x => g x
  | None => None
  end.

Definition obind2 {A B C: Type} (f: option (A * B)) (g: A -> B -> option C) : option C :=
  match f with
  | Some (x, y) => g x y
  | None => None
  end.

Notation "'do' X <- A ; B" := (obind A (fun X => B))
                                (at level 200, X ident, A at level 100, B at level 200)
                              : option_monad_scope.

Notation "'do' ( X , Y ) <- A ; B" := (obind2 A (fun X Y => B))
                                        (at level 200, X ident, Y ident, A at level 100, B at level 200)
                                      : option_monad_scope.

Remark obind_inversion:
  forall (A B: Type) (f: option A) (g: A -> option B) (y: B),
    obind f g = Some y ->
    exists x, f = Some x /\ g x = Some y.
Proof.
  intros until y. destruct f; simpl; intros.
  exists a; auto. discriminate.
Qed.

Remark obind2_inversion:
  forall {A B C: Type} (f: option (A*B)) (g: A -> B -> option C) (z: C),
    obind2 f g = Some z ->
    exists x, exists y, f = Some (x, y) /\ g x y = Some z.
Proof.
  intros until z. destruct f; simpl.
  destruct p; simpl; intros. exists a; exists b; auto.
  intros; discriminate.
Qed.

Local Open Scope option_monad_scope.

Remark omap_inversion:
  forall (A B: Type) (f: A -> option B) (l: list A) (l': list B),
    omap f l = Some l' ->
    Forall2 (fun x y => f x = Some y) l l'.
Proof.
  induction l; simpl; intros.
  inversion_clear H. constructor.
  destruct (f a) eqn:Hfa; [|discriminate].
  destruct (omap f l); inversion_clear H.
  constructor; auto.
Qed.

(** The [omonadInv H] tactic below simplifies hypotheses of the form
<<
        H: (do x <- a; b) = OK res
>>
       By definition of the obind operation, both computations [a] and
       [b] must succeed for their composition to succeed.  The tactic
       therefore generates the following hypotheses:

         x: ...
        H1: a = OK x
        H2: b x = OK res
 *)

Ltac omonadInv1 H :=
  match type of H with
  | (Some _ = Some _) =>
    inversion H; clear H; try subst
  | (None = Some _) =>
    discriminate
  | (obind ?F ?G = Some ?X) =>
    let x := fresh "x" in (
      let EQ1 := fresh "EQ" in (
        let EQ2 := fresh "EQ" in (
          destruct (obind_inversion F G H) as (x & EQ1 & EQ2);
          clear H; try (omonadInv1 EQ2))))
  | (obind2 ?F ?G = Some ?X) =>
    let x1 := fresh "x" in (
      let x2 := fresh "x" in (
        let EQ1 := fresh "EQ" in (
          let EQ2 := fresh "EQ" in (
            destruct (obind2_inversion F G H) as (x1 & x2 & EQ1 & EQ2);
            clear H; try (omonadInv1 EQ2)))))
  | (match ?X with left _ => _ | right _ => None end = Some _) =>
    destruct X; [try (omonadInv1 H) | discriminate]
  | (match (negb ?X) with true => _ | false => None end = Some _) =>
    destruct X as [] eqn:?; [discriminate | try (omonadInv1 H)]
  | (match ?X with true => _ | false => None end = Some _) =>
    destruct X as [] eqn:?; [try (omonadInv1 H) | discriminate]
  | (omap ?F ?L = Some ?M) =>
    generalize (omap_inversion F L H); intro
  end.

Ltac omonadInv H :=
  omonadInv1 H ||
             match type of H with
             | (?F _ _ _ _ _ _ _ _ = Some _) =>
               ((progress simpl in H) || unfold F in H); omonadInv1 H
             | (?F _ _ _ _ _ _ _ = Some _) =>
               ((progress simpl in H) || unfold F in H); omonadInv1 H
             | (?F _ _ _ _ _ _ = Some _) =>
               ((progress simpl in H) || unfold F in H); omonadInv1 H
             | (?F _ _ _ _ _ = Some _) =>
               ((progress simpl in H) || unfold F in H); omonadInv1 H
             | (?F _ _ _ _ = Some _) =>
               ((progress simpl in H) || unfold F in H); omonadInv1 H
             | (?F _ _ _ = Some _) =>
               ((progress simpl in H) || unfold F in H); omonadInv1 H
             | (?F _ _ = Some _) =>
               ((progress simpl in H) || unfold F in H); omonadInv1 H
             | (?F _ = Some _) =>
               ((progress simpl in H) || unfold F in H); omonadInv1 H
             end.

(* Reasoning about the option monad *)

Section OptionReasoning.

  Context {A B C : Type}.

  (* Rewriting the first argument (in [orel RA]) induces a reflexivity/Proper
     requirement on the second (higher-order) argument. The simplest
     solution is to declare it [Proper (RA ==> orel RB)]. *)
  Global Add Parametric Morphism
         {RA : relation A} {RB : relation (option B)} `{Reflexive _ RB} : obind
      with signature (orel RA ==> (RA ==> RB) ==> RB)
        as obind_orel_ho.
  Proof.
    intros oa1 oa2 Eoa f1 f2 Ef.
    destruct oa1 as [a1|]; inv Eoa; auto.
    now take (RA _ _) and specialize (Ef _ _ it).
  Qed.

  Global Add Parametric Morphism (RB : relation (option B)) `{Reflexive _ RB} : obind
      with signature (@eq (option A) ==> (pointwise_relation A RB) ==> RB)
        as obind_pointwise.
  Proof.
    intros f g1 g2 PW.
    destruct f; simpl; auto.
  Qed.

  Global Add Parametric Morphism
         (RA : relation A) (RB : relation B) (RC : relation (option C))
         `{Reflexive _ RC} : obind2
      with signature (orel (RA * RB) ==> (RA ==> RB ==> RC) ==> RC)
        as obind2_orel_ho.
  Proof.
    intros oa1 oa2 Eoa f1 f2 Ef.
    destruct oa1 as [(a1, b1)|]; inv Eoa; auto.
    take (A * B)%type and destruct it.
    take ((RA * RB)%signature _ _) and destruct it as (HA & HB).
    specialize (Ef _ _ HA _ _ HB). auto.
  Qed.

  Lemma orel_obind_intro:
    forall (RA: relation A) {RB: relation B}
      {oa1 oa2 : option A} {f1 f2 : A -> option B},
      orel RA oa1 oa2 ->
      (forall a1 a2, oa1 = Some a1 ->
                oa2 = Some a2 ->
                RA a1 a2 ->
                orel RB (f1 a1) (f2 a2)) ->
      orel RB (obind oa1 f1) (obind oa2 f2).
  Proof.
    intros * Ha Hf.
    destruct oa1 as [a1|]; inv Ha; simpl; auto.
  Qed.

  Lemma orel_obind_intro_eq:
    forall {RB: relation B} {oa1 oa2 : option A} {f1 f2 : A -> option B},
      oa1 = oa2 ->
      (forall a, oa1 = Some a ->
            oa2 = Some a ->
            orel RB (f1 a) (f2 a)) ->
      orel RB (obind oa1 f1) (obind oa2 f2).
  Proof.
    intros * Ha Hf.
    apply orel_obind_intro with (RA:=eq); subst; [reflexivity|].
    intros a1 a2 Ha H2.
    destruct oa2; try discriminate.
    repeat match goal with H:Some _ = Some _ |- _ => inv H end; auto.
  Qed.

  Lemma orel_obind_intro_same:
    forall {RB: relation B} {oa : option A} {f1 f2 : A -> option B},
      (forall a, oa = Some a ->
            orel RB (f1 a) (f2 a)) ->
      orel RB (obind oa f1) (obind oa f2).
  Proof.
    intros * Hf.
    apply (orel_obind_intro eq); [reflexivity|].
    intros * a Haa; subst; inversion Haa; subst. auto.
  Qed.

  Lemma orel_obind_inversion
        (RA : relation A) `{Reflexive A RA}
        {RB : relation B} `{Equivalence B RB}
        {g} `{Proper _ (RA ==> orel RB) g} :
    forall f q,
      orel RB (obind f g) (Some q)
      <-> (exists p, orel RA f (Some p) /\ orel RB (g p) (Some q)).
  Proof.
    intros f q; split; [intro HH|intros (p & Hf & Hg)].
    2:now setoid_rewrite Hf.
    inversion HH as [|q' q'' Rq Ms]; subst; clear HH.
    symmetry in Ms. apply obind_inversion in Ms as (p & -> & Hg).
    apply (orel_eq_weaken RB) in Hg.
    setoid_rewrite Rq in Hg. exists p; split; auto.
  Qed.
  Global Arguments orel_obind_inversion RA%signature {_} {RB}%signature {_ _ _}.

  Lemma ofold_right_altdef:
    forall (f : A -> B -> option B) xs acc,
      ofold_right f acc xs = fold_right (fun x acc => obind acc (f x)) acc xs.
  Proof. reflexivity. Qed.

  Lemma ofold_right_cons:
    forall (f : A -> B -> option B) x xs acc,
      ofold_right f acc (x::xs) = obind (ofold_right f acc xs) (f x).
  Proof. reflexivity. Qed.

  Global Instance ofold_right_Proper (RA: relation A) (RB: relation B):
    Proper ((RA ==> RB ==> orel RB)
              ==> orel RB ==> SetoidList.eqlistA RA ==> orel RB) ofold_right.
  Proof.
    intros f1 f2 Ef a1 a2 RBa xs1 xs2 RAxs.
    revert xs2 RAxs; induction xs1; intros xs2; inversion 1; subst; auto.
    inv RAxs. simpl.
    take (SetoidList.eqlistA _ _ _) and specialize (IHxs1 _ it).
    destruct (ofold_right f1 a1 xs1); inv IHxs1; auto.
    now apply Ef.
  Qed.

  Global Instance omap_Proper (RA: relation A):
    Proper ((RA ==> orel RA) ==> SetoidList.eqlistA RA
                           ==> orel (SetoidList.eqlistA RA)) omap.
  Proof.
    intros f' f Ef xs' xs Exs.
    induction Exs; simpl. now constructor.
    take (RA x x') and pose proof (Ef _ _ it) as Efx.
    destruct (f' x); inv Efx; auto.
    destruct (omap f' l); inv IHExs; auto.
    constructor; auto.
  Qed.

  Global Instance omap_Proper_pointwise (RA: relation A):
    Proper (pointwise_relation A (orel RA) ==> eq
                               ==> orel (SetoidList.eqlistA RA)) omap.
  Proof.
    intros f' f Ef xs' xs Exs; subst.
    induction xs. now constructor.
    simpl. specialize (Ef a). destruct (f' a); inv Ef; auto.
    destruct (omap f' xs); inv IHxs; auto.
    constructor. auto.
  Qed.

  Lemma orel_omap:
    forall (f g : A -> option B) xs,
      (forall x, orel eq (f x) (g x)) ->
      orel eq (omap f xs) (omap g xs).
  Proof.
    intros f g xs HH.
    induction xs; simpl. now rewrite orel_inversion.
    specialize (HH a).
    destruct (f a); inv HH; auto.
    destruct (omap f xs); inv IHxs; auto.
  Qed.

  Lemma orel_omap_eqlistA (RB : relation B) :
    forall f g (xs : list A),
      (forall x, orel RB (f x) (g x)) ->
      orel (SetoidList.eqlistA RB) (omap f xs) (omap g xs).
  Proof.
    intros f g xs HH.
    induction xs; simpl. now rewrite orel_inversion.
    specialize (HH a).
    destruct (f a); inv HH; auto.
    destruct (omap f xs); inv IHxs; auto.
    constructor. auto.
  Qed.

  Lemma orel_option_map (RB :relation B):
    forall (f g : A -> B) x,
      (forall x, RB (f x) (g x)) ->
      orel RB (option_map f x) (option_map g x).
  Proof.
    intros f g x HH.
    destruct x; simpl; auto.
    constructor. auto.
  Qed.

  (* Helper lemma for rewriting modulo an equivalence at the head of an [obind]
     on the left-hand side of an [orel].
     Usage [setoid_rewrite (orel_obind_head EQ)].

     Rewriting with [orel RA f f'] in a goal like
     [forall z, orel RB (do x <- f; g x) (Some z)]
     requires showing that [g] is [Reflexive] or [Proper] modulo [RA], where
     [g] may be an abstraction over the non-[None] result of [f] or a
     sequence of [obind]s with nested abstractions. In any case, the
     automatically generated proof obligations often cause [typeclasses eauto]
     to fail or even loop. When the tactic does fail, it is difficult to
     translate the error message and debug trace into the required (often
     adhoc) [Proper] terms. This lemma is a lightweight attempt to solve
     the problem by generating and exposing the required term for interactive
     solution. Note that when rewriting under binders (e.g., [z]), only the
     right-hand side of the [orel] may depend on them (not [f], [f'] or [g]).

     Note: successive rewriting over a nesting of [obind]s modulo the same
     relation requires repeatedly solving the same obligations. E.g., in
     [do x <- f; do y <- g x; do z <- h x y; Some (x, y, z)],
     [Proper (RA ==> orel RA) (fun x => do y <- g x; do z <- h x y; Some (x, y, z))]
     contains an obligation that also appears for a second rewrite
     [Proper (RA ==> orel RA) (fun y => do z <- h x y; Some (x, y, z))]. Is
     this inevitable? *)
  Lemma orel_obind_head
        {RA : relation A} {RB : relation B} `{Equivalence _ RB} {f f'}:
    orel RA f f' ->
    forall g, Proper (RA ==> orel RB) g ->
         forall h, orel RB (obind f g) h <-> orel RB (obind f' g) h.
  Proof.
    intros Eff g h Pg. setoid_rewrite Eff. reflexivity.
  Qed.

  Lemma orel_obind2_head
        {RA : relation A} {RB : relation B} {RC : relation C}
        `{Equivalence _ RC} {f f'}:
    orel (RA * RB) f f' ->
    forall g, Proper (RA ==> RB ==> orel RC) g ->
         forall h, orel RC (obind2 f g) h <-> orel RC (obind2 f' g) h.
  Proof.
    intros Eff g h Pg. setoid_rewrite Eff. reflexivity.
  Qed.

End OptionReasoning.

Definition orel_obind_intro_endo {A} {R: relation A}
  := @orel_obind_intro A A R R.

Lemma orel_obind2_intro:
  forall {A B C} (RA: relation A) (RB: relation B) {RC: relation C}
    {oab1 oab2 : option (A * B)} {f1 f2 : A -> B -> option C},
    orel (RA * RB) oab1 oab2 ->
    (forall a1 b1 a2 b2, oab1 = Some (a1, b1) ->
                    oab2 = Some (a2, b2) ->
                    RA a1 a2 ->
                    RB b1 b2 ->
                    orel RC (f1 a1 b1) (f2 a2 b2)) ->
    orel RC (obind2 oab1 f1) (obind2 oab2 f2).
Proof.
  intros * Ha Hf.
  apply (orel_obind_intro (RelProd RA RB)); auto.
  intros (a1, b1) (a2, b2) H1 H2; subst.
  rewrite orel_inversion in Ha. destruct Ha; auto.
Qed.

Ltac split_orel_obinds :=
  repeat intro;
  repeat progress
         (subst*; match goal with
                  | |- orel ?RB (match ?e with _ => _ end) (match ?e with _ => _ end) =>
                    destruct e; split_orel_obinds
                  | H: ?equive ?e1 ?e2
                    |- orel ?RA (match ?e1 with _ => _ end)
                           (match ?e2 with _ => _ end) =>
                    setoid_rewrite H
                  | |- orel ?RB (obind ?oa ?f1) (obind ?oa ?f2) =>
                    eapply orel_obind_intro_same; split_orel_obinds
                  | |- orel ?RB (obind ?oa1 ?f1) (obind ?oa2 ?f2) =>
                    eapply orel_obind_intro; split_orel_obinds
                  | |- orel ?RB (obind2 ?oa1 ?f1) (obind2 ?oa2 ?f2) =>
                    eapply orel_obind2_intro; split_orel_obinds
                  | |- orel ?RB (Some _) (Some _) =>
                    eapply orel_inversion
                  | |- RelProd _ _ _ _ =>
                    eapply pair_compat; split_orel_obinds
                  end; (reflexivity || eassumption || idtac)).

Ltac rewrite_orel_obinds :=
  repeat progress
         (subst; match goal with
                 | [ H:?equiv ?L ?R |- context [ ?L ] ] => setoid_rewrite H
                 end; try reflexivity).

Ltac solve_orel_obinds := split_orel_obinds; repeat rewrite_orel_obinds.
