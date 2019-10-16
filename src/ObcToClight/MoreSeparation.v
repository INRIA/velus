From compcert Require Import common.Separation.
From compcert Require Import common.Values.
From compcert Require common.Errors.
From compcert Require Import cfrontend.Ctypes.
From compcert Require Import lib.Maps.
From compcert Require Import lib.Coqlib.
From compcert Require Import lib.Integers.

From Velus Require Import Common.
From Velus Require Import VelusMemory.
From Velus Require Import Common.CompCertLib.

From Coq Require Import List.
From Coq Require Import ZArith.BinInt.

From Coq Require Import Program.Tactics.
From Coq Require Sorting.Permutation.

Open Scope list.
Open Scope sep_scope.
Open Scope Z.

Notation "m -*> m'" := (massert_imp m m') (at level 70, no associativity) : sep_scope.
Notation "m <-*-> m'" := (massert_eqv m m') (at level 70, no associativity) : sep_scope.

Lemma sepconj_eqv:
  forall P P' Q Q',
    P <-*-> P' ->
    Q <-*->  Q' ->
    (P ** Q) <-*-> (P' ** Q').
Proof.
  intros * HP HQ.
  rewrite HP. rewrite HQ.
  reflexivity.
Qed.

Lemma pure_imp:
  forall P Q,
    (pure P -*> pure Q) <-> (P -> Q).
Proof.
  split; intro Imp.
  - eapply Imp.
  - split; auto.
  Grab Existential Variables.
  exact Memory.Mem.empty.
Qed.

Lemma pure_eqv:
  forall P Q,
    (pure P <-*-> pure Q) <-> (P <-> Q).
Proof.
  split; intro Eqv; destruct Eqv.
  - split; now rewrite <-pure_imp.
  - split; now rewrite pure_imp.
Qed.

Lemma disjoint_footprint_sepconj:
  forall P Q R,
    disjoint_footprint R (P ** Q) <-> disjoint_footprint R P /\ disjoint_footprint R Q.
Proof.
  intros.
  split; intro H.
  - split; intros b ofs; specialize (H b ofs); intros HfR HfP; apply H; auto.
    + now left.
    + now right.
  - destruct H as [HfP HfQ].
    intros b ofs.
    specialize (HfP b ofs).
    specialize (HfQ b ofs).
    intros HfR HPQ.
    destruct HPQ.
    + now apply HfP.
    + now apply HfQ.
Qed.

(* * * * * * * * Separating Wand * * * * * * * * * * * * * * *)

From compcert Require Import common.Memory.
From Coq Require Import Morphisms.

Definition wand_footprint (P Q: massert) (b: block) (ofs: Z) : Prop :=
  ~m_footprint P b ofs /\ m_footprint Q b ofs.

Program Definition sepwand (P Q: massert) : massert := {|
  m_pred := fun m =>
              (forall m', Mem.unchanged_on (wand_footprint P Q) m m' ->
                          m' |= P -> m' |= Q)
              /\ (forall b ofs, wand_footprint P Q b ofs -> Mem.valid_block m b);
  m_footprint := wand_footprint P Q
|}.
Next Obligation.
  rename H into HPQ, H1 into Hval, H0 into Hun1.
  repeat split.
  - intros m'' Hun2 HP.
    apply Mem.unchanged_on_trans with (1:=Hun1) in Hun2.
    now apply HPQ with (1:=Hun2) (2:=HP).
  - intros b ofs Hwfoot.
    apply Mem.valid_block_unchanged_on with (1:=Hun1).
    apply Hval with (1:=Hwfoot).
Qed.

Infix "-*" := sepwand (at level 65, right associativity) : sep_scope.

Definition decidable_footprint (P: massert) : Prop :=
  forall b ofs, Decidable.decidable (m_footprint P b ofs).

Instance decidable_footprint_Proper:
  Proper (massert_eqv ==> iff) decidable_footprint.
Proof.
  intros P Q HPQ.
  unfold decidable_footprint, Decidable.decidable.
  split; intros.
  now rewrite <-HPQ.
  now rewrite HPQ.
Qed.

Lemma decidable_footprint_sepconj:
  forall P Q,
    decidable_footprint P ->
    decidable_footprint Q ->
    decidable_footprint (P ** Q).
Proof.
  intros P Q HP HQ b ofs.
  specialize (HP b ofs).
  specialize (HQ b ofs).
  simpl; intuition.
Qed.

Hint Resolve decidable_footprint_sepconj.

Lemma decidable_ident_eq:
  forall (b b': AST.ident), Decidable.decidable (b = b').
Proof.
  intros b b'. unfold Decidable.decidable.
  destruct (peq b' b); intuition.
Qed.

Lemma decidable_footprint_range:
  forall {f} b lo hi,
    decidable_footprint (range' f b lo hi).
Proof.
  unfold decidable_footprint.
  intros.
  apply Decidable.dec_and.
  apply decidable_ident_eq.
  apply Decidable.dec_and.
  apply Z.le_decidable.
  apply Z.lt_decidable.
Qed.

Hint Resolve decidable_footprint_range.

Lemma decidable_footprint_contains:
  forall {f} chunk b ofs spec,
    decidable_footprint (contains' f chunk b ofs spec).
Proof.
  unfold decidable_footprint.
  intros.
  apply Decidable.dec_and.
  apply decidable_ident_eq.
  apply Decidable.dec_and.
  apply Z.le_decidable.
  apply Z.lt_decidable.
Qed.

Hint Resolve decidable_footprint_contains.

Lemma sep_unwand:
  forall P Q,
    decidable_footprint P ->
    (P ** (P -* Q)) -*> Q.
Proof.
  intros P Q Hdec.
  split.
  - intros m HPPQ.
    destruct HPPQ as (HP & HW & Hdj).
    destruct HW as [Hu ?].
    apply Hu.
    apply Mem.unchanged_on_refl.
    assumption.
  - intros b ofs HfQ.
    destruct (Hdec b ofs); [now left|right].
    split; intuition.
Qed.

Lemma disjoint_sepwand:
  forall P Q, disjoint_footprint P (P -* Q).
Proof.
  intros P Q b ofs HfP HfPQ.
  destruct HfPQ as [HfnP HfQ].
  intuition.
Qed.

Lemma merge_disjoint:
  forall P Q R m,
    disjoint_footprint P Q ->
    m |= P ** R ->
    m |= Q ** R ->
    m |= P ** Q ** R.
Proof.
  intros P Q R m HdPQ HPR HQR.
  rewrite <-sep_assoc.
  repeat split.
  - apply sep_proj1 with (1:=HPR).
  - apply sep_proj1 with (1:=HQR).
  - assumption.
  - apply sep_proj2 with (1:=HPR).
  - intros b ofs Hfw HfR.
    destruct Hfw as [HfP|HfPQ].
    + destruct HPR as [? [? HdPR]].
      unfold disjoint_footprint in HdPR.
      apply HdPR with (1:=HfP) (2:=HfR).
    + destruct HQR as [? [? HdQR]].
      unfold disjoint_footprint in HdQR.
      apply HdQR with (1:=HfPQ) (2:=HfR).
Qed.

Lemma merge_sepwand:
  forall P Q R m,
    m |= P ** R ->
    m |= (P -* Q) ** R ->
    m |= P ** (P -* Q) ** R.
Proof.
  intros. apply merge_disjoint; try assumption.
  now apply disjoint_sepwand.
Qed.

Lemma sepwand_mp:
  forall m P Q,
    m |= P ->
    m |= P -* Q ->
    m |= Q.
Proof.
  intros m P Q HP HPQ.
  apply HPQ; [|assumption].
  apply Mem.unchanged_on_refl.
Qed.

Instance wand_footprint_massert_imp_Proper:
  Proper (massert_imp ==> massert_imp --> eq ==> eq ==> Basics.impl)
         wand_footprint.
Proof.
  intros P Q HPQ R S HRS b' b Hbeq ofs' ofs Hoeq.
  subst.
  unfold wand_footprint.
  now rewrite HPQ, HRS.
Qed.

Instance wand_footprint_massert_eqv_Proper:
  Proper (massert_eqv ==> massert_eqv ==> eq ==> eq ==> iff) wand_footprint.
Proof.
  intros P Q HPQ R S HRS b' b Hbeq ofs' ofs Hoeq.
  subst.
  unfold wand_footprint.
  rewrite HPQ, HRS. reflexivity.
Qed.

Instance sepwand_massert_Proper:
  Proper (massert_eqv ==> massert_eqv ==> massert_eqv) sepwand.
Proof.
  intros P Q HPQ R S HRS.
  split; [split|split].
  - intros m HPR.
    destruct HPR as [HPR1 HPR2].
    split.
    + intros m' Hun HQ.
      rewrite <-HRS.
      rewrite <-HPQ in HQ.
      apply HPR1 with (2:=HQ).
      apply Mem.unchanged_on_implies with (1:=Hun).
      intros b ofs HfW Hv.
      now rewrite HPQ, HRS in HfW.
    + intros b ofs.
      rewrite <-HPQ, <-HRS.
      apply HPR2.
  - intros b ofs Hf.
    simpl in Hf.
    now rewrite <-HPQ, <-HRS in Hf.
  - intros m HQS.
    destruct HQS as [HQS1 HQS2].
    split.
    + intros m' Hun HP.
      rewrite HPQ in HP.
      rewrite HRS.
      apply HQS1 with (2:=HP).
      apply Mem.unchanged_on_implies with (1:=Hun).
      intros b ofs HfW Hv.
      now rewrite HPQ, HRS.
    + intros b ofs.
      rewrite HPQ, HRS.
      apply HQS2.
  - intros b ofs Hf.
    simpl in Hf. rewrite HPQ, HRS in Hf.
    assumption.
Qed.

Lemma hide_in_sepwand:
  forall P Q R,
    decidable_footprint Q ->
    P <-*-> (Q ** R) ->
    P <-*-> (Q ** (Q -* P)).
Proof.
  intros P Q R HQdec HPQR.
  rewrite HPQR at 2.
  split; [split|].
  - intros m HP.
    apply HPQR in HP.
    split; [|split].
    + apply sep_proj1 with (1:=HP).
    + split.
      * intros m' Hun HQ'.
        destruct HP as (HQ & HR & Hdj).
        repeat split; try assumption.
        apply m_invar with (1:=HR).
        apply Mem.unchanged_on_implies with (1:=Hun).
        intros b ofs HfR Hv.
        destruct (HQdec b ofs).
        now (exfalso; apply Hdj with (2:=HfR)).
        split; [assumption|now right].
      * intros b ofs.
        destruct 1 as [HnfQ [|HfR]]; [contradiction|].
        apply sep_proj2 in HP.
        apply m_valid with (1:=HP) (2:=HfR).
    + apply disjoint_sepwand.
  - intros b ofs Hf.
    rewrite HPQR.
    destruct Hf as [|Hf]; [now left|].
    destruct Hf as [HfQ [|HfR]]; [now left|].
    now right.
  - rewrite sep_unwand with (1:=HQdec).
    rewrite HPQR. reflexivity.
Qed.

Lemma sepwand_out:
  forall P Q,
    decidable_footprint P ->
    (P ** Q) <-*-> (P ** (P -* (P ** Q))).
Proof.
  split.
  - now rewrite <-hide_in_sepwand.
  - now rewrite sep_unwand.
Qed.

Lemma pure_wand_footprint:
  forall (P: Prop) Q b ofs,
    wand_footprint (pure P) Q b ofs <-> m_footprint Q b ofs.
Proof.
  split.
  - inversion 1; auto.
  - split; auto.
Qed.

Lemma unchanged_on_imp:
  forall P (Q: block -> Z -> Prop) m m',
    Mem.unchanged_on P m m' ->
    (forall b ofs, Q b ofs -> P b ofs) ->
    Mem.unchanged_on Q m m'.
Proof.
  intros * Hun Hpq.
  inversion_clear Hun.
  constructor; auto.
Qed.

Lemma pure_sepwand:
  forall (P: Prop) Q,
    P -> (pure P -* Q) <-*-> Q.
Proof.
  intros P Q HH.
  constructor.
  - constructor.
    + inversion_clear 1 as (Hun & Hf).
      apply Hun; auto using Mem.unchanged_on_refl.
    + constructor; auto.
  - constructor.
    + intros m Hq. constructor.
      * intros m' Hun Hmp.
        apply m_invar with (1:=Hq).
        apply unchanged_on_imp with (1:=Hun).
        apply pure_wand_footprint.
      * intros * Hwf.
        apply pure_wand_footprint in Hwf.
        eauto using m_valid.
    + simpl. intros * Hf.
      now apply pure_wand_footprint in Hf.
Qed.

(* Reynold's "rules capturing the adjunctive relationship between separating
   conjunction and separating implication". *)

Lemma reynolds1:
  forall P1 P2 P3,
    (P1 ** P2) -*> P3 ->
    (forall b ofs, m_footprint P1 b ofs -> wand_footprint P2 P3 b ofs) ->
    P1 -*> (P2 -* P3).
Proof.
  intros P1 P2 P3 HH Hfi.
  split.
  - intros m HP1.
    split.
    + intros m' Hun HP2.
      apply HH.
      split; [|split].
      * apply m_invar with (1:=HP1).
        apply Mem.unchanged_on_implies with (1:=Hun).
        intros; now apply Hfi.
      * assumption.
      * intros b ofs HfP1 HfP2.
        apply Hfi in HfP1.
        destruct HfP1. contradiction.
    + intros b ofs.
      destruct 1 as [HnfP2 HfP3].
      destruct HH as [HHm HHf].
      apply HHf in HfP3.
      destruct HfP3 as [HfP1|]; [|contradiction].
      apply m_valid with (1:=HP1) (2:=HfP1).
  - intros b ofs.
    destruct 1 as [HnfP2 HfP3].
    destruct HH as [HHm HHf].
    apply HHf in HfP3.
    destruct HfP3; intuition.
Qed.

Lemma reynolds2:
  forall P1 P2 P3,
    decidable_footprint P2 ->
    P1 -*> (P2 -* P3) ->
    (P1 ** P2) -*> P3.
Proof.
  intros P1 P2 P3 HD2 HH.
  rewrite HH. rewrite sep_comm.
  rewrite sep_unwand with (1:=HD2).
  reflexivity.
Qed.

Definition footprint_perm' (p: permission) (P: massert) (b: block) (lo hi: Z) : Prop :=
  (forall m, m |= P ->
             (forall i k, m_footprint P b i ->
                          lo <= i < hi ->
                          Mem.perm m b i k p)).

Notation footprint_perm := (footprint_perm' Freeable).
Notation footprint_perm_w := (footprint_perm' Writable).

Lemma footprint_perm_sepconj:
  forall p P Q b lo hi,
    footprint_perm' p P b lo hi ->
    footprint_perm' p Q b lo hi ->
    footprint_perm' p (P ** Q) b lo hi.
Proof.
  intros f P Q b lo hi HfpP HfpQ.
  intros m HPQ i k Hf Hi.
  destruct HPQ as (HP & HQ & Hdj).
  destruct Hf as [HfP|HfQ].
  - now apply HfpP.
  - now apply HfpQ.
Qed.

Lemma footprint_perm_range:
  forall p b lo hi b' lo' hi',
    footprint_perm' p (range' p b lo hi) b' lo' hi'.
Proof.
  intros p b lo hi b' lo' hi' m Hm i k Hf Hi.
  destruct Hf. subst.
  destruct Hm as (Hlo & Hhi & Hp).
  now apply Hp.
Qed.

Lemma footprint_perm_contains:
  forall p chunk b ofs spec b' lo hi,
    footprint_perm' p (contains' p chunk b ofs spec) b' lo hi.
Proof.
  intros p chunk b ofs spec b' lo hi m Hm i k Hf Hi.
  destruct Hf. subst.
  destruct Hm as (Hlo & Hhi & Hv & Hl).
  destruct Hv as (Hperm & j & Hofs).
  apply Mem.perm_cur.
  now apply Hperm.
Qed.

Hint Resolve footprint_perm_sepconj
             footprint_perm_range
             footprint_perm_contains.

Lemma range_imp_with_wand:
  forall p P b lo hi,
    (range' p b lo hi) -*> P ->
    decidable_footprint P ->
    footprint_perm' p P b lo hi ->
    (range' p b lo hi) <-*-> (P ** (P -* range' p b lo hi)).
Proof.
  intros p P b lo hi HRP HPfdec HPperm.
  split; [|now rewrite sep_unwand].
  split.
  - intros m HR.
    split; [|split].
    + now apply HRP.
    + split.
      * intros m' Hun HP.
        assert (HR':=HR).
        destruct HR' as (Hlo & Hhi & Hperm).
        repeat split; try assumption.
        intros i k Hi.
        destruct (HPfdec b i) as [HfPi|HnfPi].
        now apply HPperm with (1:=HP) (2:=HfPi) (3:=Hi).
        apply Mem.perm_unchanged_on with (1:=Hun).
        split; [assumption|simpl; now intuition].
        now apply Hperm.
      * intros b' ofs.
        destruct 1 as [? HfR].
        assert (b = b') by (simpl in HfR; intuition).
        subst. apply (m_valid _ _ _ _ HR HfR).
    + intros b' ofs HfP HfPR.
      destruct HfPR. contradiction.
  - intros b' ofs Hf.
    destruct HRP as [HRP HfPR].
    destruct Hf as [|Hf]; [now apply HfPR|].
    now destruct Hf.
Qed.

Definition subseteq_footprint (P Q: massert) :=
  (forall b ofs, m_footprint P b ofs -> m_footprint Q b ofs).

Instance subseteq_footprint_footprint_Proper:
  Proper (subseteq_footprint ==> eq ==> eq ==> Basics.impl) m_footprint.
Proof.
  intros P Q Hsub b b' Heqb ofs ofs' Heqofs HP.
  subst. apply Hsub with (1:=HP).
Qed.

Lemma subseteq_footprint_refl:
  forall P, subseteq_footprint P P.
Proof.
  now unfold subseteq_footprint.
Qed.

Lemma subseteq_footprint_trans:
  forall P Q R, subseteq_footprint P Q ->
                subseteq_footprint Q R ->
                subseteq_footprint P R.
Proof.
  unfold subseteq_footprint. intuition.
Qed.

Add Parametric Relation: massert subseteq_footprint
    reflexivity proved by subseteq_footprint_refl
    transitivity proved by subseteq_footprint_trans
      as subseteq_footprint_rel.

Instance subseteq_footprint_massert_imp_Proper:
  Proper (massert_imp ==> massert_imp --> Basics.impl) subseteq_footprint.
Proof.
  intros P Q HPQ R S HSR HPsR b ofs HfQ.
  apply HPQ in HfQ.
  specialize (HPsR b ofs HfQ).
  now apply HSR in HPsR.
Qed.

Instance subseteq_footprint_massert_eqv_Proper:
  Proper (massert_eqv ==> massert_eqv ==> iff) subseteq_footprint.
Proof.
  intros P Q HPQ R S HSR.
  destruct HPQ as [HPQ HQP].
  destruct HSR as [HSR HRS].
  split; intro HH.
  - rewrite HPQ in HH; now rewrite HRS.
  - rewrite HQP in HH. now rewrite HSR.
Qed.

Lemma subseteq_footprint_sepconj:
  forall P Q R S,
    subseteq_footprint P Q ->
    subseteq_footprint R S ->
    subseteq_footprint (P ** R) (Q ** S).
Proof.
  intros P Q R S HPQ HRS.
  intros b ofs.
  destruct 1 as [HP|HR].
  - left; now apply HPQ.
  - right; now apply HRS.
Qed.

Lemma unify_distinct_wands:
  forall P Q R S,
    disjoint_footprint R S ->
    subseteq_footprint P R ->
    subseteq_footprint Q S ->
    (P -* R) ** (Q -* S)
    -*> (P ** Q) -* (R ** S).
Proof.
  intros P Q R S HdjRS HsPR HsQS.
  split.
  - intros m HH.
    split.
    + intros m' Hun.
      destruct HH as (HPR & HQS & Hdj).
      destruct 1 as (HP & HQ & HdjPQ).
      repeat split.
      * apply m_invar with (m':=m') in HPR.
        now apply sepwand_mp with (1:=HP) in HPR.
        apply Mem.unchanged_on_implies with (1:=Hun).
        intros b ofs HfPR Hv.
        destruct HfPR as (HnfP & HfR).
        split.
        destruct 1 as [HfP|HfQ]; [contradiction|].
        apply HdjRS with (1:=HfR).
        apply HsQS with (1:=HfQ).
        now left.
      * apply m_invar with (m':=m') in HQS.
        now apply sepwand_mp with (1:=HQ) in HQS.
        apply Mem.unchanged_on_implies with (1:=Hun).
        intros b ofs HfQS Hv.
        destruct HfQS as (HnfQ & HfS).
        split.
        destruct 1 as [HfP|HfQ]; [|contradiction].
        apply HdjRS with (2:=HfS).
        apply HsPR with (1:=HfP).
        now right.
      * assumption.
    + intros b ofs Hfw.
      apply (m_valid _ _ _ ofs HH).
      destruct Hfw as [HnfPQ [HfR|HfS]]; [left|right]; split;
        try (intro; apply HnfPQ; simpl); intuition.
  - intros b ofs.
    destruct 1 as [HnfPQ [HfR|HfS]]; [left|right]; split;
      try (intro; apply HnfPQ; simpl); intuition.
Qed.

(* * * * * * * * sepall * * * * * * * * * * * * * * *)

Program Definition sepemp: massert :=  pure True.

Lemma sepemp_disjoint:
  forall P, disjoint_footprint P sepemp.
Proof.
  unfold disjoint_footprint. auto.
Qed.

Lemma sepemp_trivial:
  forall m, m |= sepemp.
Proof.
  split.
Qed.
Hint Resolve sepemp_trivial.

Lemma sepemp_right:
  forall P,
    P <-*-> (P ** sepemp).
Proof.
  split; split; simpl; try (auto using sepemp_disjoint); intuition.
Qed.

Lemma sepemp_left:
  forall P,
    P <-*-> (sepemp ** P).
Proof.
  intros. rewrite sep_comm. rewrite <-sepemp_right. reflexivity.
Qed.

Lemma wandwand_sepemp:
  forall P, massert_eqv (P -* P) sepemp.
Proof.
  firstorder.
Qed.

Lemma wand_footprint_sepemp:
  forall P b ofs,
    wand_footprint sepemp P b ofs <-> m_footprint P b ofs.
Proof.
  firstorder.
Qed.

Lemma sepemp_wand:
  forall P,
    sepemp -* P <-*-> P.
Proof.
  split; split.
  - inversion 1 as [Hun Hv].
    apply Hun.
    apply Mem.unchanged_on_refl.
    now simpl.
  - now split.
  - intros m HP. split.
    + intros m' Hun He.
      apply m_invar with (1:=HP).
      apply Mem.unchanged_on_implies with (1:=Hun).
      intros; now apply wand_footprint_sepemp.
    + intros b ofs Hw.
      rewrite wand_footprint_sepemp in Hw.
      apply m_valid with (1:=HP) (2:=Hw).
  - intros b ofs Hf.
    simpl in Hf.
    now apply wand_footprint_sepemp in Hf.
Qed.

Lemma decidable_footprint_sepemp:
  decidable_footprint sepemp.
Proof.
  unfold decidable_footprint. simpl.
  intros; apply Decidable.dec_False.
Qed.

Lemma footprint_perm_sepemp:
  forall p b lo hi, footprint_perm' p sepemp b lo hi.
Proof.
  intros lo hi m. inversion 2.
Qed.

Hint Resolve decidable_footprint_sepemp footprint_perm_sepemp.

Lemma empty_range:
  forall {f} b lo hi,
    hi <= lo ->
    0 <= lo ->
    hi <= Ptrofs.modulus ->
    sepemp <-*-> (range' f b lo hi).
Proof.
  intros b lo hi Hgt.
  split; [split|split].
  - simpl. intuition.
  - inversion 1. intuition.
  - intros; exact I.
  - inversion 1.
Qed.

Definition sepfalse := pure False.

Lemma decidable_footprint_sepfalse:
  decidable_footprint sepfalse.
Proof.
  unfold decidable_footprint. simpl.
  intros; apply Decidable.dec_False.
Qed.

Lemma footprint_perm_sepfalse:
  forall p b lo hi, footprint_perm' p sepfalse b lo hi.
Proof.
  intros p b lo hi m Hm. inversion Hm.
Qed.

Hint Resolve decidable_footprint_sepfalse footprint_perm_sepfalse.

Section MassertPredEqv.
  Context {A: Type}.

  Definition massert_pred_eqv (P: A -> massert) (Q: A -> massert) : Prop :=
    forall x, massert_eqv (P x) (Q x).

  Lemma massert_pred_eqv_refl:
    forall P, massert_pred_eqv P P.
  Proof.
    now unfold massert_pred_eqv.
  Qed.

  Lemma massert_pred_eqv_sym:
    forall P Q, massert_pred_eqv P Q -> massert_pred_eqv Q P.
  Proof.
    unfold massert_pred_eqv. intros P Q HPQ x. now rewrite (HPQ x).
  Qed.

  Lemma massert_pred_eqv_trans:
    forall P Q R,
      massert_pred_eqv P Q ->
      massert_pred_eqv Q R ->
      massert_pred_eqv P R.
  Proof.
    unfold massert_pred_eqv. intros P Q R HPQ HQR x.
    now rewrite (HPQ x), (HQR x).
  Qed.

  Lemma massert_pred_eqv_inst:
    forall P Q x,
      massert_pred_eqv P Q ->
      massert_eqv (P x) (Q x).
  Proof.
    intros P Q x HPQ. apply HPQ.
  Qed.

End MassertPredEqv.

Add Parametric Relation (A: Type) : (A -> massert) massert_pred_eqv
    reflexivity proved by massert_pred_eqv_refl
    symmetry proved by massert_pred_eqv_sym
    transitivity proved by massert_pred_eqv_trans
as massert_pred_eqv_prel.

Section Sepall.
  Context {A: Type}.

  Definition sepall (p: A -> massert): list A -> massert :=
    fold_right (fun x => sepconj (p x)) sepemp.

  Lemma sepall_permutation:
    forall p xs ys,
      Permutation.Permutation xs ys ->
      (sepall p xs) <-*-> (sepall p ys).
  Proof.
    intros p xs ys Hperm.
    induction Hperm.
    - reflexivity.
    - simpl. now rewrite IHHperm.
    - simpl.
      rewrite sep_swap; reflexivity.
    - rewrite IHHperm1, <-IHHperm2.
      clear Hperm1 Hperm2 IHHperm1 IHHperm2.
      now induction l'.
  Qed.

  Lemma sepall_app:
    forall p xs ys,
      sepall p (xs ++ ys) <-*-> sepall p xs ** sepall p ys.
  Proof.
    intros.
    induction xs.
    - intros.
      rewrite sep_comm.
      rewrite <-sepemp_right.
      reflexivity.
    - intros.
      simpl.
      rewrite sep_assoc.
      rewrite IHxs.
      reflexivity.
  Qed.

  Lemma sepall_cons:
    forall p x xs,
      sepall p (x::xs) <-*-> p x ** sepall p xs.
  Proof.
    constructor; constructor; trivial.
  Qed.

  Lemma sepall_breakout:
    forall ys ws x xs p,
      ys = ws ++ x :: xs ->
      sepall p ys <-*-> p x ** sepall p (ws ++ xs).
  Proof.
    intros * Hys.
    rewrite sepall_app.
    rewrite sep_swap.
    rewrite <-sepall_cons.
    rewrite <-sepall_app.
    rewrite <-Hys.
    reflexivity.
  Qed.

  Lemma sepall_in:
    forall x ys,
      In x ys ->
      exists ws xs,
        ys = ws ++ x :: xs
        /\ (forall p,
              sepall p ys <-*-> p x ** sepall p (ws ++ xs)).
  Proof.
    intros x ys Hin.
    apply in_split in Hin.
    destruct Hin as [ws [xs Hys]].
    exists ws, xs.
    split; auto.
    intro p. apply sepall_breakout with (1:=Hys).
  Qed.

  Lemma sepall_wandout:
    forall p x xs,
      decidable_footprint (p x) ->
      In x xs ->
      (sepall p xs) <-*-> (p x ** (p x -* sepall p xs)).
  Proof.
    intros p x xs Hdec Hin.
    apply in_split in Hin.
    destruct Hin as (ws & ys & Hin).
    rewrite sepall_breakout with (1:=Hin).
    now apply sepwand_out.
  Qed.

  Lemma sepall_sepfalse:
    forall m p xs,
      m |= sepall p xs ->
      (forall x, In x xs -> p x <> sepfalse).
  Proof.
    intros m p xs Hall x Hin Hp.
    apply sepall_in in Hin.
    destruct Hin as [ws [ys [Hys Heq]]].
    rewrite Heq in Hall.
    apply sep_comm in Hall.
    apply sep_drop in Hall.
    rewrite Hp in Hall.
    destruct Hall.
  Qed.

  Lemma sepall_weakenp:
    forall P P' xs,
      (forall x, In x xs -> (P x) -*> (P' x)) ->
      (sepall P xs) -*> (sepall P' xs).
  Proof.
    intros P P' xs Hx.
    induction xs.
    reflexivity.
    simpl. apply sep_imp'.
    - apply Hx. apply in_eq.
    - rewrite IHxs. reflexivity.
      intros x Hin.
      apply Hx. apply in_cons with (1:=Hin).
  Qed.

  Lemma sepall_swapp:
    forall P P' xs,
      (forall x, In x xs -> P x <-*-> P' x) ->
      sepall P xs <-*-> sepall P' xs.
  Proof.
    intros P P' xs Hx.
    induction xs.
    reflexivity.
    simpl. apply sepconj_eqv.
    - rewrite Hx. reflexivity. apply in_eq.
    - rewrite IHxs. reflexivity.
      intros x Hin.
      apply Hx. apply in_cons with (1:=Hin).
  Qed.

  Lemma decidable_footprint_sepall:
    forall P xs,
      (forall x, decidable_footprint (P x)) ->
      decidable_footprint (sepall P xs).
  Proof.
    induction xs as [|x xs IH].
    now (intros; apply decidable_footprint_sepemp).
    intro HPx.
    simpl. apply decidable_footprint_sepconj.
    - apply HPx.
    - apply IH with (1:=HPx).
  Qed.

  Lemma footprint_perm_sepall:
    forall p P xs b lo hi,
      (forall x b lo hi, footprint_perm' p (P x) b lo hi) ->
      footprint_perm' p (sepall P xs) b lo hi.
  Proof.
    induction xs as [|x xs IH].
    now (intros; apply footprint_perm_sepemp).
    intros b lo hi Hfp.
    simpl. apply footprint_perm_sepconj.
    - apply Hfp.
    - apply IH with (1:=Hfp).
  Qed.

  Hint Resolve decidable_footprint_sepall footprint_perm_sepall.

  Lemma sepall_unwand:
  forall xs P Q,
    (forall x, decidable_footprint (P x)) ->
    (sepall P xs ** sepall (fun x => P x -* Q x) xs) -*> sepall Q xs.
  Proof.
    induction xs; simpl; intros * Hdec.
    - now rewrite sepemp_left.
    - rewrite sep_assoc, sep_swap23, <-sep_assoc.
      apply sep_imp'.
      + apply sep_unwand.
        apply Hdec.
      + apply IHxs; auto.
  Qed.

  Lemma subseteq_footprint_sepall:
    forall p q xs,
      (forall x, In x xs -> subseteq_footprint (p x) (q x)) ->
      subseteq_footprint (sepall p xs) (sepall q xs).
  Proof.
    intros p q xs Hsub.
    induction xs as [|x xs IH].
    now apply subseteq_footprint_refl.
    simpl. apply subseteq_footprint_sepconj.
    now (apply Hsub; constructor).
    apply IH.
    intros x' Hin.
    apply Hsub. now apply in_cons.
  Qed.

  Lemma sepall_outwand_cons:
    forall p q x xs,
      (forall x, decidable_footprint (p x)) ->
      (forall x, subseteq_footprint (p x) (q x)) ->
      (p x ** (p x -* q x)) ** sepall p xs ** (sepall p xs -* sepall q xs)
      -*> sepall p (x::xs) ** (sepall p (x::xs) -* sepall q (x::xs)).
  Proof.
    intros p q x xs Hdec Hsub.
    rewrite sep_assoc.
    split.
    - intros m Hm.
      rewrite sep_swap23 in Hm.
      rewrite unify_distinct_wands in Hm.
      + Opaque sepconj. simpl. Transparent sepconj. now rewrite sep_assoc.
      + rewrite sep_swap23 in Hm.
        rewrite <-sep_assoc in Hm.
        rewrite sep_unwand in Hm; [|now auto].
        rewrite sep_unwand in Hm; [|now auto].
        apply Hm.
      + apply Hsub.
      + apply subseteq_footprint_sepall.
        intros.
        apply Hsub.
    - intros b ofs Hf.
      rewrite sep_unwand; [|now auto].
      rewrite <-sep_assoc, sep_unwand; [|now auto].
      destruct Hf as [Hfp|Hf].
      + now rewrite subseteq_footprint_sepall with (q:=q) in Hfp.
      + now destruct Hf.
  Qed.

End Sepall.

Hint Resolve decidable_footprint_sepall footprint_perm_sepall.

Instance sepall_massert_pred_eqv_permutation_eqv_Proper A:
  Proper (massert_pred_eqv ==> @Permutation.Permutation A ==> massert_eqv)
         sepall.
Proof.
  intros p q Heq xs ys Hperm.
  rewrite sepall_permutation with (1:=Hperm).
  induction Hperm.
  - reflexivity.
  - simpl. now rewrite IHHperm, (massert_pred_eqv_inst _ _ _ Heq).
  - simpl.
    repeat rewrite (massert_pred_eqv_inst _ _ _ Heq).
    repeat apply sepconj_eqv; try reflexivity.
    induction l; [reflexivity|].
    simpl.
    now rewrite IHl, (massert_pred_eqv_inst _ _ _ Heq).
  - now rewrite IHHperm2.
Qed.

(* * * * * * * * Ranges * * * * * * * * * * * * * * *)

Section SplitRange.
  Variable env: composite_env.
  Variable id: ident.
  Variable co: composite.

  Hypothesis Henv: Ctypes.composite_env_consistent env.
  Hypothesis Hco: env!id = Some co.
  Hypothesis Hstruct: co_su co = Struct.

  Definition field_range' (p: permission) (flds: list (AST.ident * type))
             (b: block) (lo: Z) (fld: AST.ident * type) : massert :=
    let (id, ty) := fld in
    match field_offset env id flds with
      | Errors.OK ofs  => range' p b (lo + ofs) (lo + ofs + sizeof env ty)
      | Errors.Error _ => sepfalse
    end.

  Lemma decidable_footprint_field_range:
    forall p lo b flds,
      decidable_footprint (sepall (field_range' p flds b lo) flds).
  Proof.
    intros.
    apply decidable_footprint_sepall.
    intro fld. destruct fld as [x ty].
    simpl. destruct (field_offset env x flds); auto.
  Qed.

  Lemma footprint_perm_field_range:
    forall p flds b pos x b' lo hi,
      footprint_perm' p (field_range' p flds b pos x) b' lo hi.
  Proof.
    intros p flds b pos x b' lo hi.
    destruct x as [x ty].
    simpl. destruct (field_offset env x flds); auto.
  Qed.

  Lemma split_range_fields':
    forall p b lo flds,
      NoDupMembers flds ->
      massert_imp (range' p b lo (lo + sizeof_struct env 0 flds))
                  (sepall (field_range' p flds b lo) flds).
  Proof.
    intros p b lo flds Hndup.
    cut (forall cur,
            massert_imp
              (range' p b (lo + cur)
                       (lo + sizeof_struct env cur flds))
              (sepall (fun fld : AST.ident * type =>
                         let (id0, ty) := fld in
                         match field_offset_rec env id0 flds cur with
                         | Errors.OK ofs =>
                             range' p b (lo + ofs) (lo + ofs + sizeof env ty)
                         | Errors.Error _ => sepfalse
                         end) flds)).
    - intro HH.
      specialize HH with 0. rewrite Z.add_0_r in HH.
      apply HH.
    - induction flds as [|x xs IH]; [now constructor|].
      destruct x as [id' ty'].
      apply nodupmembers_cons in Hndup.
      destruct Hndup as [Hnin Hndup].
      specialize (IH Hndup).
      intro cur.
      Opaque sepconj. simpl.
      rewrite peq_true.
      erewrite sepall_swapp.
      + rewrite range_split'
        with (mid:=lo + (align cur (alignof env ty') + sizeof env ty')).
        * apply sep_imp'.
          2:now apply IH.
          rewrite range_split'
          with (mid:=lo + align cur (alignof env ty')).
          rewrite sep_drop. rewrite Z.add_assoc. reflexivity.
          split.
          now apply Z.add_le_mono_l; apply align_le; apply alignof_pos.
          apply Z.add_le_mono_l.
          rewrite <-Z.add_0_r at 1. apply Z.add_le_mono_l.
          apply Z.ge_le. apply sizeof_pos.
        * split.
          2:now apply Z.add_le_mono_l; apply sizeof_struct_incr.
          apply Z.add_le_mono_l.
          rewrite <-Z.add_0_r at 1. apply Z.add_le_mono.
          apply align_le. apply alignof_pos.
          apply Z.ge_le. apply sizeof_pos.
      + intros fld Hin.
        destruct fld.
        rewrite peq_false.
        reflexivity.
        intro Heq; subst.
        apply Hnin.
        eapply In_InMembers; eassumption.
  Qed.

  Lemma split_range_fields:
    forall p b lo,
      NoDupMembers (co_members co) ->
      massert_imp (range' p b lo (lo + co_sizeof co))
                  (sepall (field_range' p (co_members co) b lo) (co_members co)).
  Proof.
    intros p b lo Hndup.
    apply Henv in Hco.
    rewrite (co_consistent_sizeof _ _ Hco).
    rewrite (co_consistent_alignof _ _ Hco).
    rewrite Hstruct.
    simpl.
    rewrite range_split'
    with (mid:=lo + sizeof_struct env 0 (co_members co)).
    + rewrite split_range_fields' with (1:=Hndup).
      now rewrite sep_comm, sep_drop.
    + split.
      * rewrite <-Z.add_0_r at 1.
        apply Z.add_le_mono_l.
        apply sizeof_struct_incr.
      * apply Z.add_le_mono_l.
        apply align_le.
        apply alignof_composite_pos.
  Qed.

End SplitRange.

Notation field_range ge := (field_range' ge Freeable).
Notation field_range_w ge := (field_range' ge Writable).

(* * * * * * * * Initial memory * * * * * * * * * * * * * * *)

Import Globalenvs.
Import AST.
Import Clight.

Section Galloc.

  (* Variables F V : Type. *)
  Variable p : program (* (fundef F) V *).

  Definition grange (idg : ident * globdef fundef type) :=
    let (id, g) := idg in
    match Genv.find_symbol (Genv.globalenv p) id with
    | None => sepfalse
    | Some b =>
      match g with
      | Gfun f => range' Nonempty b 0 1
      | Gvar v =>
        pure (init_data_list_size (gvar_init v) <= Ptrofs.modulus)
             -* range' (Genv.perm_globvar v) b 0
                       (init_data_list_size v.(gvar_init))
      end
    end.

  Lemma init_grange:
    forall m0,
      NoDupMembers p.(prog_defs) ->
      Genv.init_mem p = Some m0 ->
      m0 |= sepall grange p.(prog_defs).
  Proof.
    pose proof (eq_refl p.(prog_defs)) as Hps.
    revert Hps. generalize p.(prog_defs) at 2 4.
    intros ps Hps' m0 Hndups Hinit.
    assert (exists ps', p.(prog_defs) = ps' ++ ps) as Hps
        by (exists nil; auto).
    clear Hps'.
    induction ps; auto.
    destruct a as (id, g).
    destruct Hps as (ps' & Hps).
    assert (m0 |= sepall grange ps) as IH
        by (apply IHps; exists (ps' ++ (id, g)::nil);
            now rewrite <- List_shift_first).
    clear IHps.
    assert ((prog_defmap p) ! id = Some g) as Hpdm
        by (apply prog_defmap_norepet;
            [now apply NoDup_norepet, fst_NoDupMembers|
             rewrite Hps; intuition]).
    apply Genv.find_def_symbol in Hpdm.
    destruct Hpdm as (b & Hfs & Hfd).
    apply sepall_cons.
    repeat constructor; auto.
    - (* m0 |= grange (id, g) *)
      simpl. rewrite Hfs.
      destruct g.
      + (* g = Gfun f *)
        apply Genv.find_funct_ptr_iff in Hfd.
        apply Genv.init_mem_characterization_2 with (2:=Hinit) in Hfd.
        destruct Hfd as (Hperm & Hperm').
        repeat constructor.
        * omega.
        * rewrite Z.one_succ; apply Zlt_le_succ, Z.gt_lt, two_power_nat_pos.
        * intros * HH. assert (i = 0) by omega.
          subst. now apply Mem.perm_cur.
      + (* g = Gvar v *)
        apply Genv.find_var_info_iff in Hfd.
        eapply Genv.init_mem_characterization with (2:=Hinit) in Hfd.
        destruct Hfd as (Hrp & Hfd).
        repeat constructor; auto.
        * reflexivity.
        * intros i k Hi.
          apply Mem.perm_cur.
          unfold wand_footprint in H.
          apply Mem.perm_unchanged_on with (1:=H); simpl; auto.
        * inversion_clear 1 as (? & Hf). simpl in *.
          destruct Hf as (Hb & Hf). subst.
          eapply Mem.perm_valid_block; eauto.
    - (* disjoint_footprint (grange (id, g)) (sepall grange ids) *)
      rewrite Hps in Hndups.
      apply NoDupMembers_app_cons in Hndups.
      destruct Hndups as (Hndups1 & Hndups2).
      apply NotInMembers_app in Hndups1.
      apply proj1 in Hndups1.
      clear Hndups2 Hinit Hps Hfd ps'.
      induction ps; auto using sepemp_disjoint.
      destruct a as (id' & g').
      apply NotInMembers_cons in Hndups1.
      destruct Hndups1 as (Hndups & Hnid').
      apply sepall_cons in IH.
      specialize (IHps Hndups (sep_proj2 _ _ _ IH)).
      apply sep_proj1 in IH.
      rewrite sepall_cons.
      apply disjoint_footprint_sepconj.
      split; auto. clear IHps.
      intros b' ofs' Hf1 Hf2.
      simpl in *.
      rewrite Hfs in Hf1.
      destruct (Genv.find_symbol (Genv.globalenv p) id') eqn:Hfs'; [|inv IH].
      apply Genv.global_addresses_distinct with (1:=Hnid') (2:=Hfs) in Hfs'.
      apply Hfs'.
      destruct g, g'; inversion_clear Hf1; inversion_clear Hf2;
        simpl in *; subst; intuition; now subst b b0.
  Qed.

End Galloc.

Lemma sep_swap56:
  forall P Q R S T U V, (P ** Q ** R ** S ** T ** U ** V) <-*-> (P ** Q ** R ** S ** U ** T ** V).
Proof.
  intros. rewrite (sep_swap T). reflexivity.
Qed.

Lemma sep_swap67:
  forall P Q R S T U V W, (P ** Q ** R ** S ** T ** U ** V ** W) <-*-> (P ** Q ** R ** S ** T ** V ** U ** W).
Proof.
  intros. rewrite (sep_swap U). reflexivity.
Qed.

Lemma sep_swap78:
  forall P Q R S T U V W X, (P ** Q ** R ** S ** T ** U ** V ** W ** X) <-*-> (P ** Q ** R ** S ** T ** U ** W ** V ** X).
Proof.
  intros. rewrite (sep_swap V). reflexivity.
Qed.
