From Coq Require Import FSets.FMapPositive.
From Coq Require Import FSets.FMapFacts.
From Coq Require Import List.
Import ListNotations.
From Coq Require Import Sorting.Permutation.

From Coq Require Import Setoid.
From Coq Require Import Relations RelationPairs.
From Coq Require Import Morphisms.

From Coq Require MSets.MSets.
From Coq Require Export PArith.
From Coq Require Import Classes.EquivDec.

From Velus Require Import ClockDefs.
From Velus Require Import Common.CommonTactics.
From Velus Require Import Common.CommonList.

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

Lemma PS_elements_NoDup: forall s,
    NoDup (PS.elements s).
Proof.
  intros s.
  rewrite NoDup_NoDupA.
  apply PS.elements_spec2w.
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

Lemma ps_add_eq : forall x1 x2 s,
    PS.eq (PS.add x1 (PS.add x2 s)) (PS.add x2 (PS.add x1 s)).
Proof.
  intros x1 x2 s.
  split; intros Hin;
    repeat rewrite PS.add_spec in Hin; destruct Hin as [?|[?|?]]; subst.
  1,3,4,6: apply PSF.add_2.
  1,3,5,6: apply PSF.add_1; auto.
  1,2: apply PSF.add_2; eauto.
Qed.

Lemma ps_add_adds_eq : forall xs x s,
    PS.eq (PS.add x (ps_adds xs s)) (ps_adds xs (PS.add x s)).
Proof.
  induction xs; intros x s; simpl.
  - reflexivity.
  - rewrite IHxs. rewrite ps_add_eq. reflexivity.
Qed.

Lemma ps_adds_app: forall xs1 xs2 s,
    PS.eq (ps_adds (xs1 ++ xs2) s)
          (ps_adds xs1 (ps_adds xs2 s)).
Proof.
  induction xs1; intros xs2 s; simpl.
  - reflexivity.
  - rewrite IHxs1. rewrite ps_add_adds_eq. reflexivity.
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

Instance ps_from_list_Proper:
  Proper (@Permutation ident ==> PS.Equal) ps_from_list.
Proof.
  intros ? ? Hperm ?.
  split; intros; rewrite Hperm in *; auto.
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

Lemma Permutation_PS_elements_ps_adds':
  forall xs S,
    NoDup (xs ++ PS.elements S) ->
    Permutation (PS.elements (ps_adds xs S)) (xs ++ PS.elements S).
Proof.
  intros xs S Hnd.
  rewrite NoDup_app'_iff in Hnd. destruct Hnd as [Hnd1 [_ Hnd2]].
  eapply Permutation_PS_elements_ps_adds; eauto.
  eapply Forall_impl; [| eauto].
  intros a Hnin contra; simpl in *.
  rewrite In_PS_elements in Hnin. congruence.
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

Lemma ps_removes_app : forall xs1 xs2 s,
    ps_removes (xs1 ++ xs2) s = ps_removes xs2 (ps_removes xs1 s).
Proof.
  induction xs1; intros xs2 s; simpl.
  - reflexivity.
  - rewrite IHxs1. reflexivity.
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

Corollary PS_For_all_Forall': forall P xs,
    PS.For_all P (ps_from_list xs) <-> (Forall P xs).
Proof.
  intros P xs.
  unfold ps_from_list. rewrite PS_For_all_ps_adds.
  split; intros.
  - destruct H; auto.
  - split; auto.
    apply PS_For_all_empty.
Qed.

Lemma ps_adds_of_list:
  forall xs,
    PS.Equal (ps_adds xs PS.empty) (PSP.of_list xs).
Proof.
  intros xs x. rewrite ps_adds_spec, PSP.of_list_1; split.
  -intros [Hin|Hin]; auto. now apply not_In_empty in Hin.
  - intro Hin. apply SetoidList.InA_alt in Hin as (y & Hy & Hin); subst; auto.
Qed.

Corollary ps_from_list_ps_of_list : forall xs,
    PS.eq (ps_from_list xs) (PSP.of_list xs).
Proof.
  intros xs. unfold ps_from_list. apply ps_adds_of_list.
Qed.

Corollary ps_of_list_In : forall xs x,
    PS.In x (PSP.of_list xs) <-> In x xs.
Proof.
  intros *.
  rewrite <- ps_from_list_ps_of_list, ps_from_list_In.
  reflexivity.
Qed.

Lemma ps_of_list_ps_to_list : forall id xs,
    In id (PSP.to_list (PSP.of_list xs)) <-> In id xs.
Proof.
  intros id xs.
  specialize (PSP.of_list_2 xs id) as Heq.
  repeat rewrite InA_alt in Heq.
  split; intros Hin.
  - destruct Heq as [[? [? ?]] _]; subst; auto.
    exists id; auto.
  - destruct Heq as [_ [? [? ?]]]; subst; auto.
    exists id; auto.
Qed.

Lemma ps_of_list_ps_to_list_Perm : forall xs,
    NoDup xs ->
    Permutation (PSP.to_list (PSP.of_list xs)) xs.
Proof.
  intros xs Hnd; simpl.
  rewrite <- ps_from_list_ps_of_list.
  unfold PSP.to_list, ps_from_list.
  rewrite Permutation_PS_elements_ps_adds';
    rewrite PSP.elements_empty, app_nil_r; auto.
Qed.

Lemma ps_of_list_ps_to_list_SameElements : forall xs,
    SameElements eq xs (PSP.to_list (PSP.of_list xs)).
Proof.
  unfold PSP.to_list.
  induction xs; simpl.
  - rewrite PSP.elements_empty; auto.
  - destruct (in_dec CommonPS.EqDec_instance_0 a xs).
    + eapply SE_trans.
      2:{ eapply SE_perm. eapply PS_elements_Equal. symmetry.
          apply PSP.add_equal, ps_of_list_In; auto. }
      assert (In a (PS.elements (PSP.of_list xs))) as Hin'.
      { apply In_PS_elements, ps_of_list_In; auto. }
      eapply SE_trans; eauto.
    + eapply SE_trans.
      2:{ eapply SE_perm; symmetry; eapply Permutation_elements_add; eauto.
          rewrite ps_of_list_In; auto. }
      eapply SE_skip; eauto.
Qed.

Inductive DisjointSetList : list PS.t -> Prop :=
| DJSnil: DisjointSetList []
| DJScons: forall s ss,
    DisjointSetList ss ->
    Forall (fun t => PS.Empty (PS.inter s t)) ss ->
    DisjointSetList (s :: ss).

Instance DisjointSetList_Proper:
  Proper (@Permutation.Permutation PS.t ==> iff) DisjointSetList.
Proof.
  intros s' s Es.
  induction Es; split; intro DJ; auto using DisjointSetList;
    repeat match goal with
           | H:DisjointSetList (_ :: _) |- _ => inversion_clear DJ
           | H:_ <-> _ |- _ => destruct H
           | FA:Forall _ ?xs, H:Permutation ?xs ?ys |- DisjointSetList (_ :: ?ys) =>
             rewrite H in FA
           | FA:Forall _ ?ys, H:Permutation ?xs ?ys |- DisjointSetList (_ :: ?xs) =>
             rewrite <-H in FA
           | H:Forall _ (_ :: _) |- _ => apply Forall_cons2 in H as (? & ?)
           | |- DisjointSetList _ => constructor
           | |- Forall _ (_ :: _) => constructor
           | H:DisjointSetList (_ :: _) |- _ => inv H
           | H:PS.Empty (PS.inter ?x ?y) |- PS.Empty (PS.inter ?y ?x) =>
             now rewrite PSP.inter_sym
           end; auto using DisjointSetList.
Qed.

Definition PSUnion (xs : list PS.t) : PS.t :=
  List.fold_left PS.union xs PS.empty.

Instance fold_left_PS_Proper:
  Proper ((PS.Equal ==> PS.Equal ==> PS.Equal) ==> eq ==> PS.Equal ==> PS.Equal)
         (@fold_left PS.t PS.t).
Proof.
  intros f g Efg xs' xs Exs S' S ES; subst.
  revert S S' ES. induction xs; auto.
  simpl. intros S S' ES. apply IHxs.
  apply Efg in ES. now apply ES.
Qed.

Instance PSUnion_Proper:
  Proper (@Permutation.Permutation PS.t ==> PS.Equal) PSUnion.
Proof.
  unfold PSUnion. intros xs ys EE. generalize (PS.empty).
  induction EE; simpl.
  - reflexivity.
  - now setoid_rewrite IHEE.
  - setoid_rewrite PSP.union_assoc.
    now setoid_rewrite (PSP.union_sym x).
  - now setoid_rewrite IHEE1; setoid_rewrite IHEE2.
Qed.

Instance PSUnion_eqlistA_Proper:
  Proper (SetoidList.eqlistA PS.Equal ==> PS.Equal) PSUnion.
Proof.
  unfold PSUnion. intros xs ys EE. generalize (PS.empty).
  induction EE; simpl.
  - reflexivity.
  - setoid_rewrite IHEE.
    now take (PS.Equal _ _) and setoid_rewrite it.
Qed.

Lemma PSUnion_cons:
  forall T TS, (PSUnion (T :: TS)) === (PS.union T (PSUnion TS)).
Proof.
  unfold PSUnion. intros T TS. generalize PS.empty.
  induction TS; simpl in *. now setoid_rewrite (PSP.union_sym T).
  intros S.
  now rewrite <-IHTS, PSP.union_assoc, PSP.union_assoc, (PSP.union_sym T).
Qed.

Lemma Subset_PSUnion_cons:
  forall T TS, PS.Subset T (PSUnion (T :: TS)).
Proof.
  intros T TS. unfold PSUnion; simpl. revert T.
  induction TS; simpl; intros T S IST; auto.
  rewrite <-IHTS. now apply PSF.union_2.
Qed.

Lemma In_PSUnion:
  forall T TS,
    In T TS ->
    PS.Subset T (PSUnion TS).
Proof.
  induction TS. now inversion 1.
  intro IT. apply in_inv in IT as [IT|IT].
  - subst. apply Subset_PSUnion_cons.
  - apply IHTS in IT. rewrite IT, PSUnion_cons.
    apply PSP.union_subset_2.
Qed.

Lemma PS_union_empty1:
  forall s, PS.union PS.empty s === s.
Proof.
  intros s x. rewrite PS.union_spec.
  split; intro HH; auto. destruct HH as [HH|]; auto.
  inversion HH.
Qed.

Lemma PS_union_empty2:
  forall s, PS.union s PS.empty === s.
Proof.
  intros s x. rewrite PS.union_spec.
  split; intro HH; auto. destruct HH as [|HH]; auto.
  inversion HH.
Qed.

Lemma PSUnion_cons_empty:
  forall xs, PSUnion (PS.empty :: xs) === PSUnion xs.
Proof.
  setoid_rewrite PSUnion_cons at 1.
  now setoid_rewrite PS_union_empty1 at 1.
Qed.

Lemma PSUnion_nil:
  PSUnion nil = PS.empty.
Proof.
  reflexivity.
Qed.

Lemma PSUnion_app:
  forall xs ys,
    PSUnion (PSUnion xs :: ys) === PSUnion (xs ++ ys).
Proof.
  induction xs; intro ys; simpl.
  now rewrite PSUnion_nil, PSUnion_cons_empty.
  now rewrite PSUnion_cons, PSUnion_cons, PSUnion_cons,
  <-IHxs, PSUnion_cons, PSP.union_assoc.
Qed.

Lemma PSUnion_In_app:
  forall x xs ys,
    PS.In x (PSUnion (xs ++ ys)) <-> PS.In x (PSUnion xs) \/ PS.In x (PSUnion ys).
Proof.
  induction xs; simpl; intro ys.
  - rewrite PSUnion_nil; split; [intros HH|intros [HH|HH]]; auto.
    now inv HH.
  - repeat rewrite PSUnion_cons.
    now rewrite PS.union_spec, PS.union_spec, IHxs, or_assoc.
Qed.

Lemma In_In_PSUnion:
  forall x s ss,
    PS.In x s ->
    In s ss ->
    PS.In x (PSUnion ss).
Proof.
  intros x s ss Ix Is.
  apply in_split in Is as (bl & al & ?); subst.
  rewrite <-Permutation_middle, PSUnion_cons, PS.union_spec; auto.
Qed.

Lemma PSUnion_In_In:
  forall x ss,
    PS.In x (PSUnion ss) ->
    exists s, In s ss /\ PS.In x s.
Proof.
  induction ss as [|s' ss IH]; intro Ix.
  now rewrite PSUnion_nil in Ix; inv Ix.
  rewrite PSUnion_cons, PS.union_spec in Ix; destruct Ix as [Ix|Ix];
    eauto with datatypes. now firstorder.
Qed.

Definition In_ps (xs : list positive) (v : PS.t) :=
  Forall (fun x => PS.In x v) xs.

Lemma In_ps_nil:
  forall v, In_ps [] v.
Proof.
  intro v. apply Forall_nil.
Qed.

Lemma In_ps_singleton:
  forall x v,
    PS.In x v <-> In_ps [x] v.
Proof.
  split; intro HH; [|now inv HH].
  now apply Forall_cons; auto.
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
