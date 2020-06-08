From Coq Require Import List Sorting.Permutation.
Import List.ListNotations.
Open Scope list_scope.
From Coq Require Import Classes.RelationClasses.
From Coq Require Import Setoid Morphisms.

From Velus Require Import Common Ident.

(** * Fresh name generation *)

(** The fresh monad (with memory) : generates new names and keeps
    a record of each name generated along with some information *)
Module Type FRESH.

  Section st.
    Parameter fresh_st : Type -> Type.
    Context {B : Type}.
    Parameter st_anns : fresh_st B -> list (ident * B).
    Definition st_ids (st : fresh_st B) := map fst (st_anns st).
  End st.

  Definition Fresh (A B : Type) : Type := fresh_st B -> A * fresh_st B.

  Section ret.
    Context {A B : Type}.
    Parameter ret : A -> Fresh A B.
    Axiom ret_spec : forall a st,
        ret a st = (a, st).
  End ret.

  Section validity.
    Context {B : Type}.
    Parameter st_valid_after : fresh_st B -> PS.t -> Prop.
    Axiom st_valid_NoDup : forall st aft,
        st_valid_after st aft ->
        NoDup (st_ids st++PSP.to_list aft).
  End validity.

  (** Reusability: we can define a set of identifier to be reused by the state *)
  Section validity_reuse.
    Context {B : Type}.
    Parameter st_valid_reuse : fresh_st B -> PS.t -> PS.t -> Prop.
    Axiom st_valid_reuse_st_valid : forall st aft reusable,
        st_valid_reuse st aft reusable ->
        st_valid_after st aft.
    Axiom st_valid_reuse_nIn : forall st aft reusable,
        st_valid_reuse st aft reusable ->
        PS.For_all (fun x => ~In x (st_ids st)) reusable.
    Axiom st_valid_reuse_PSeq : forall st aft re1 re2,
        PS.eq re1 re2 ->
        st_valid_reuse st aft re1 ->
        st_valid_reuse st aft re2.
  End validity_reuse.

  (** Weak validity : only gives us information about fresh_ident *)
  Section weak_validity.
    Context {B : Type}.
    Parameter weak_valid_after : fresh_st B -> PS.t -> Prop.
    Axiom st_valid_weak_valid : forall st aft,
        st_valid_after st aft ->
        weak_valid_after st aft.
  End weak_validity.

  Section follows.
    Context {B : Type}.
    Parameter st_follows : fresh_st B -> fresh_st B -> Prop.
    Axiom st_follows_refl : Reflexive st_follows.
    Axiom st_follows_trans : Transitive st_follows.
    Axiom st_follows_incl : forall st st',
        st_follows st st' ->
        incl (st_anns st) (st_anns st').
  End follows.

  Section init.
    Context {B : Type}.
    Parameter init_st : ident -> fresh_st B.
    Axiom init_st_anns : forall id, st_anns (init_st id) = [].
    Axiom init_st_valid : forall id aft,
        PS.For_all (fun x => Pos.lt x id) aft ->
        st_valid_after (init_st id) aft.
    Axiom init_st_valid_reuse : forall id aft reusable,
        NoDup (PSP.to_list aft++PSP.to_list reusable) ->
        PS.For_all (fun x => Pos.lt x id) aft ->
        PS.For_all (fun x => Pos.lt x id) reusable ->
        st_valid_reuse (init_st id) aft reusable.
  End init.

  Section fresh_ident.
    Context {B : Type}.
    Parameter fresh_ident : B -> Fresh ident B.

    Axiom fresh_ident_anns : forall b id st st',
        fresh_ident b st = (id, st') ->
        st_anns st' = (id, b)::(st_anns st).

    Axiom fresh_ident_st_valid : forall b id st st' aft,
        fresh_ident b st = (id, st') ->
        st_valid_after st aft ->
        st_valid_after st' aft.
    Axiom fresh_ident_st_valid_reuse : forall b id st st' aft reusable,
        fresh_ident b st = (id, st') ->
        st_valid_reuse st aft reusable ->
        st_valid_reuse st' aft reusable.
    Axiom fresh_ident_weak_valid : forall b id st st' aft,
        fresh_ident b st = (id, st') ->
        weak_valid_after st aft ->
        weak_valid_after st' aft.
    Axiom fresh_ident_st_follows : forall b id st st',
        fresh_ident b st = (id, st') ->
        st_follows st st'.
    Axiom fresh_ident_weak_valid_nIn : forall b id st st' aft,
        fresh_ident b st = (id, st') ->
        weak_valid_after st aft ->
        ~PS.In id aft.
  End fresh_ident.

  Section reuse_ident.
    Context {B : Type}.
    Parameter reuse_ident : ident -> B -> Fresh unit B.

    Axiom reuse_ident_anns : forall b id st st',
        reuse_ident id b st = (tt, st') ->
        st_anns st' = (id, b)::(st_anns st).

    Axiom reuse_ident_st_valid_reuse : forall b id st st' aft reusable,
        ~PS.In id reusable ->
        reuse_ident id b st = (tt, st') ->
        st_valid_reuse st aft (PS.add id reusable) ->
        st_valid_reuse st' aft reusable.
    Axiom reuse_ident_weak_valid : forall b id st st' aft,
        reuse_ident id b st = (tt, st') ->
        weak_valid_after st aft ->
        weak_valid_after st' aft.
    Axiom reuse_ident_st_follows : forall b id st st',
        reuse_ident id b st = (tt, st') ->
        st_follows st st'.
  End reuse_ident.

  Section bind.
    Context {A A' B : Type}.
    Parameter bind : Fresh A B -> (A -> Fresh A' B) -> Fresh A' B.
    Axiom bind_spec : forall (x : Fresh A B) (k : A -> Fresh A' B) st a' st'',
        (bind x k) st = (a', st'') <->
        exists a, exists st', (x st = (a, st') /\ k a st' = (a', st'')).
  End bind.

  Section bind2.
    Context {A1 A2 A' B : Type}.
    Parameter bind2 : Fresh (A1 * A2) B -> (A1 -> A2 -> Fresh A' B) -> Fresh A' B.
    Axiom bind2_spec : forall (x : Fresh (A1 * A2) B) (k : A1 -> A2 -> Fresh A' B) st a' st'',
        (bind2 x k) st = (a', st'') <->
        exists a1, exists a2, exists st', (x st = ((a1, a2), st') /\ k a1 a2 st' = (a', st'')).
  End bind2.
End FRESH.

Module Fresh : FRESH.
  Section st.
    Definition fresh_st (B : Type) : Type := (ident * list (ident * B)).
    Context {B : Type}.
    Definition st_anns (st : fresh_st B) := snd st.
    Definition st_ids (st : fresh_st B) := map fst (st_anns st).
  End st.

  Definition Fresh (A B : Type) : Type := fresh_st B -> A * fresh_st B.

  Section ret.
    Context {A B : Type}.
    Definition ret (a : A) : Fresh A B := fun st => (a, st).

    Fact ret_spec : forall a st,
        ret a st = (a, st).
    Proof.
      intros a st. reflexivity.
    Qed.
  End ret.

  Section validity.
    Context {B : Type}.
    (** The state is valid if the next ident is greater than all generated idents,
        and if there is no duplicates in generated idents *)
    Definition st_valid_after (st : fresh_st B) (aft : PS.t) : Prop :=
      let '(n, l) := st in
      Forall (fun '(x, _) => Pos.lt x n) l /\
      PS.For_all (fun x => Pos.lt x n) aft /\
      NoDup (map fst l++PSP.to_list aft).

    Fact st_valid_NoDup : forall st aft,
        st_valid_after st aft ->
        NoDup (st_ids st++PSP.to_list aft).
    Proof.
      intros [n l] aft [_ [_ Hvalid]]; auto.
    Qed.
  End validity.

  Section validity_reuse.
    Context {B : Type}.
    Definition st_valid_reuse (st : fresh_st B) (aft : PS.t) (reusable : PS.t) : Prop :=
      st_valid_after st aft /\
      NoDup (PSP.to_list aft++PSP.to_list reusable) /\
      let '(n, l) := st in
      PS.For_all (fun x => Pos.lt x n) reusable /\
      PS.For_all (fun x => ~In x (st_ids st)) reusable.

    Fact st_valid_reuse_st_valid : forall st aft reusable,
        st_valid_reuse st aft reusable ->
        st_valid_after st aft.
    Proof. intros ? ? ? [? _]; auto. Qed.

    Fact st_valid_reuse_nIn : forall st aft reusable,
        st_valid_reuse st aft reusable ->
        PS.For_all (fun x => ~In x (st_ids st)) reusable.
    Proof. intros [? ?] ? ? [? [? [? ?]]]; auto. Qed.

    Fact st_valid_reuse_PSeq : forall st aft re1 re2,
        PS.eq re1 re2 ->
        st_valid_reuse st aft re1 ->
        st_valid_reuse st aft re2.
    Proof.
      intros [n l] aft re1 re2 Heq [Hv1 [Hv2 [Hv3 Hv4]]].
      repeat (constructor; auto); rewrite <- Heq; auto.
    Qed.
  End validity_reuse.

  Section weak_validity.
    Context {B : Type}.
    Definition weak_valid_after (st : fresh_st B) (aft : PS.t) :=
      let '(n, l) := st in
      PS.For_all (fun x => Pos.lt x n) aft.

    Fact st_valid_weak_valid : forall st aft,
        st_valid_after st aft ->
        weak_valid_after st aft.
    Proof. intros [? ?] ? [? [? ?]]; auto. Qed.
  End weak_validity.

  Section follows.
    Context {B : Type}.

    Definition st_follows (st st' : fresh_st B) :=
      incl (snd st) (snd st').

    Fact st_follows_refl : Reflexive st_follows.
    Proof. intros st. unfold st_follows. reflexivity. Qed.

    Fact st_follows_trans : Transitive st_follows.
    Proof.
      unfold Transitive. intros.
      unfold st_follows in *.
      etransitivity; eauto.
    Qed.

    Fact st_follows_incl : forall st st',
        st_follows st st' ->
        incl (st_anns st) (st_anns st').
    Proof. intuition. Qed.
  End follows.

  Section init.
    Context {B : Type}.

    Definition init_st ident : fresh_st B := (ident, []).

    Fact init_st_anns : forall id, st_anns (init_st id) = [].
    Proof. intros. reflexivity.
    Qed.

    Fact init_st_valid : forall id aft,
        PS.For_all (fun x => Pos.lt x id) aft ->
        st_valid_after (init_st id) aft.
    Proof.
      intros id aft Hlt.
      unfold init_st.
      repeat constructor; simpl; auto.
      apply PS_elements_NoDup.
    Qed.

    Fact init_st_valid_reuse : forall id aft reusable,
        NoDup (PSP.to_list aft++PSP.to_list reusable) ->
        PS.For_all (fun x => Pos.lt x id) aft ->
        PS.For_all (fun x => Pos.lt x id) reusable ->
        st_valid_reuse (init_st id) aft reusable.
    Proof.
      intros id ids Hnd Hps. unfold init_st.
      repeat constructor; simpl; auto.
      - apply PS_elements_NoDup.
      - intros x HIn. simpl. congruence.
    Qed.
  End init.

  Section fresh_ident.
    Context {B : Type}.

    Definition fresh_ident (b : B) : Fresh ident B :=
      fun '(n, l) => (n, (Pos.succ n, (cons (n, b) l))).

    Fact fresh_ident_anns : forall b id st st',
        fresh_ident b st = (id, st') ->
        st_anns st' = (id, b)::(st_anns st).
    Proof.
      intros.
      destruct st. inv H.
      reflexivity.
    Qed.

    Fact fresh_ident_st_valid :
      forall (b : B) id st st' aft,
        fresh_ident b st = (id, st') ->
        st_valid_after st aft ->
        st_valid_after st' aft.
    Proof.
      intros b res [n l] [n' l'] aft Hfresh Hvalid.
      simpl in Hfresh; inv Hfresh.
      destruct Hvalid as [Hv1 [Hv2 Hv3]].
      repeat constructor; auto.
      - apply Positive_as_DT.lt_succ_diag_r.
      - eapply Forall_impl; eauto.
        intros [x _] Hlt'.
        apply Positive_as_OT.lt_lt_succ; auto.
      - intros x HIn.
        apply Hv2 in HIn.
        rewrite Positive_as_DT.lt_succ_r.
        apply Positive_as_OT.lt_le_incl; auto.
      - intro contra; simpl in contra.
        rewrite in_app_iff in contra.
        destruct contra.
        + rewrite (in_map_iff fst l res) in H.
          destruct H as [[? ?] [? Hin]]; subst.
          rewrite Forall_forall in Hv1.
          apply Hv1 in Hin; simpl in Hin.
          apply Pos.lt_irrefl in Hin; auto.
        + rewrite PS_For_all_Forall in Hv2.
          rewrite Forall_forall in Hv2.
          apply Hv2 in H; simpl in H.
          apply Pos.lt_irrefl in H; auto.
    Qed.

    Fact fresh_ident_st_valid_reuse : forall b id st st' aft reusable,
        fresh_ident b st = (id, st') ->
        st_valid_reuse st aft reusable ->
        st_valid_reuse st' aft reusable.
    Proof.
      intros b id st st' aft reusable Hfresh [Hv1 [Hv2 Hv3]].
      constructor; auto.
      - eapply fresh_ident_st_valid; eauto.
      - destruct st as [n l]; destruct st' as [n' l'].
        destruct Hv3 as [Hv3 Hv4].
        repeat constructor; auto.
        + unfold fresh_ident in Hfresh. inv Hfresh.
          intros ? HIn. apply Hv3 in HIn.
          rewrite Positive_as_OT.lt_succ_r.
          apply Positive_as_OT.lt_le_incl; auto.
        + unfold fresh_ident in Hfresh. inv Hfresh.
          intros ? HIn.
          specialize (Hv3 _ HIn); specialize (Hv4 _ HIn); simpl in *.
          intro contra. destruct contra.
          * subst. apply Pos.lt_irrefl in Hv3; auto.
          * unfold st_ids in Hv4 . simpl in Hv4. congruence.
    Qed.

    Fact fresh_ident_weak_valid : forall b id st st' aft,
        fresh_ident b st = (id, st') ->
        weak_valid_after st aft ->
        weak_valid_after st' aft.
    Proof.
      intros b id [n l] [n' l'] aft Hfresh Hval.
      simpl in *; inv Hfresh.
      unfold weak_valid_after in *.
      eapply PS_For_all_impl_In; eauto.
      intros ? _ H; simpl in H.
      rewrite Positive_as_OT.lt_succ_r.
      apply Positive_as_OT.lt_le_incl; auto.
    Qed.

    Fact fresh_ident_st_follows :
      forall (b : B) id st st',
        fresh_ident b st = (id, st') ->
        st_follows st st'.
    Proof.
      intros b res [n l] [n' l'] Hfresh.
      simpl in *; inv Hfresh; simpl.
      unfold st_follows in *; simpl in *.
      apply incl_tl. reflexivity.
    Qed.

    Fact fresh_ident_weak_valid_nIn : forall b id st st' aft,
        fresh_ident b st = (id, st') ->
        weak_valid_after st aft ->
        ~PS.In id aft.
    Proof.
      intros b id [n l] [n' l'] aft Hfresh Hval.
      simpl in *; inv Hfresh.
      intro contra. apply Hval in contra.
      apply Pos.lt_irrefl in contra; auto.
    Qed.
  End fresh_ident.

  Section reuse_ident.
    Context {B : Type}.

    Definition reuse_ident (id : ident) (b : B) : Fresh unit B :=
      fun '(n, l) => (tt, (n, (id, b)::l)).

    Fact reuse_ident_anns : forall b id st st',
        reuse_ident id b st = (tt, st') ->
        st_anns st' = (id, b)::(st_anns st).
    Proof.
      intros b id [n l] [n' l'] H.
      unfold reuse_ident in H.
      inv H. reflexivity.
    Qed.

    Fact reuse_ident_st_valid_reuse : forall b id st st' aft reusable,
        ~PS.In id reusable ->
        reuse_ident id b st = (tt, st') ->
        st_valid_reuse st aft (PS.add id reusable) ->
        st_valid_reuse st' aft reusable.
    Proof with eauto.
      intros b id [n l] [n' l'] aft reusable Hnin Hreuse Hvalid.
      unfold reuse_ident in Hreuse. inv Hreuse.
      destruct Hvalid as [[Hv1 [Hv2 Hv3]] [Hv4 [Hv5 Hv6]]].
      repeat constructor...
      - rewrite PS_For_all_add in Hv5. destruct Hv5...
      - intro contra; simpl in contra.
        rewrite in_app_iff in contra.
        destruct contra.
        + rewrite (in_map_iff fst l id) in H.
          destruct H as [[? ?] [? HIn']]; subst; simpl in *.
          rewrite PS_For_all_add in Hv6. destruct Hv6 as [HIn _].
          unfold st_ids in HIn; simpl in HIn.
          apply HIn. rewrite in_map_iff. exists (i, b0)...
        + eapply NoDup_app_In in Hv4; eauto.
          rewrite In_PS_elements in Hv4. apply Hv4, PSF.add_1...
      - apply NoDup_app'.
        + apply PS_elements_NoDup.
        + apply PS_elements_NoDup.
        + rewrite <- PS_For_all_Forall. intros ? Hin.
          rewrite <- In_PS_elements in Hin.
          eapply NoDup_app_In in Hv4; eauto.
          rewrite In_PS_elements in *.
          intro contra. apply Hv4. apply PSF.add_2...
      - intros id' HIn'.
        apply PS_For_all_add in Hv5. destruct Hv5 as [_ Hv5].
        apply Hv5 in HIn'...
      - intros id' HIn' contra.
        unfold st_ids in contra; simpl in contra.
        destruct contra; subst.
        + congruence.
        + rewrite PS_For_all_add in Hv6. destruct Hv6 as [_ Hv6].
          eapply Hv6 in HIn'.
          unfold st_ids in HIn'; simpl in *...
    Qed.

    Fact reuse_ident_weak_valid : forall b id st st' aft,
        reuse_ident id b st = (tt, st') ->
        weak_valid_after st aft ->
        weak_valid_after st' aft.
    Proof.
      intros b id [n l] [n' l'] aft Hreuse Hval.
      simpl in *; inv Hreuse; auto.
    Qed.

    Fact reuse_ident_st_follows : forall b id st st',
        reuse_ident id b st = (tt, st') ->
        st_follows st st'.
    Proof.
      intros b id [n l] [n' l'] Hreuse.
      unfold reuse_ident in Hreuse. inv Hreuse.
      unfold st_follows; simpl.
      apply incl_tl. reflexivity.
    Qed.
  End reuse_ident.

  Section bind.
    Context {A A' B : Type}.

    Definition bind (x : Fresh A B) (k : A -> Fresh A' B) : Fresh A' B :=
      fun st => let '(a, st') := x st in k a st'.

    Lemma bind_spec : forall (x : Fresh A B) (k : A -> Fresh A' B) st a' st'',
        (bind x k) st = (a', st'') <->
        exists a, exists st', (x st = (a, st') /\ k a st' = (a', st'')).
    Proof.
      intros x k st a' st''. split; intros.
      - unfold bind in H.
        destruct (x st) as [a st']. exists a. exists st'.
        split; auto.
      - destruct H as [a [st' [H1 H2]]]. unfold bind.
        rewrite H1. assumption.
    Qed.
  End bind.

  Section bind2.
    Context {A1 A2 A' B : Type}.

    Definition bind2 (x: Fresh (A1 * A2) B) (k: A1 -> A2 -> Fresh A' B) : Fresh A' B :=
      fun n => let '((a1, a2), n') := x n in k a1 a2 n'.

    Lemma bind2_spec : forall (x : Fresh (A1 * A2) B) (k : A1 -> A2 -> Fresh A' B) st a' st'',
        (bind2 x k) st = (a', st'') <->
        exists a1, exists a2, exists st', (x st = ((a1, a2), st') /\ k a1 a2 st' = (a', st'')).
    Proof.
      intros x k st a' st''. split; intros.
      - unfold bind2 in H.
        destruct (x st) as [[a1 a2] st']. exists a1. exists a2. exists st'.
        split; auto.
      - destruct H as [a1 [a2 [st' [H1 H2]]]]. unfold bind2.
        rewrite H1. assumption.
    Qed.
  End bind2.
End Fresh.

Section Instances.
  Context {B : Type}.
  Global Instance st_follows_refl : Reflexive (@Fresh.st_follows B) := Fresh.st_follows_refl.
  Global Instance st_follows_trans : Transitive (@Fresh.st_follows B) := Fresh.st_follows_trans.

  Global Add Parametric Morphism st aft : (@Fresh.st_valid_reuse B st aft)
      with signature @PS.eq ==> Basics.impl
        as st_valid_reuse_PSeq.
  Proof.
    intros. intro Hv.
    eapply Fresh.st_valid_reuse_PSeq; eauto.
  Qed.
End Instances.

Module Facts.
  Import Fresh.

  Section st.
    Context {B : Type}.

    Fact st_anns_ids_In : forall (st : fresh_st B) id,
        (exists b, In (id, b) (st_anns st)) <-> In id (st_ids st).
    Proof.
      intros.
      split; intros.
      - destruct H as [b H].
        unfold st_ids. rewrite in_map_iff.
        exists (id, b); auto.
      - unfold st_ids in H. rewrite in_map_iff in H.
        destruct H as [[? b] [? H]]; simpl in *; subst.
        exists b. assumption.
    Qed.
  End st.

  Section fresh_ident.
    Context {B : Type}.

    Fact fresh_ident_In : forall (b : B) id st st',
        fresh_ident b st = (id, st') ->
        In (id, b) (st_anns st').
    Proof.
      intros. apply fresh_ident_anns in H.
      rewrite H. constructor. reflexivity.
    Qed.

    Corollary fresh_ident_Inids : forall (b : B) id st st',
        fresh_ident b st = (id, st') ->
        In id (st_ids st').
    Proof.
      intros b id st st' Hfresh.
      apply fresh_ident_In in Hfresh.
      unfold st_ids. rewrite in_map_iff.
      exists (id, b); auto.
    Qed.

    Fact fresh_ident_vars_perm : forall (b : B) id st st',
        fresh_ident b st = (id, st') ->
        Permutation (id::(st_ids st)) (st_ids st').
    Proof.
      intros. apply fresh_ident_anns in H.
      unfold st_ids in *. rewrite H.
      reflexivity.
    Qed.

    Fact fresh_ident_nIn : forall (b : B) id st st' aft,
        st_valid_after st aft ->
        fresh_ident b st = (id, st') ->
        ~List.In id (st_ids st).
    Proof.
      intros b id st st' aft Hvalid Hfresh.
      eapply fresh_ident_st_valid in Hvalid; eauto.
      apply st_valid_NoDup in Hvalid. apply NoDup_app_weaken in Hvalid.
      apply fresh_ident_vars_perm in Hfresh.
      unfold st_ids in *.
      rewrite <- Hfresh in Hvalid. inv Hvalid.
      assumption.
    Qed.

  End fresh_ident.

  Section reuse_ident.
    Context {B : Type}.

    Fact reuse_ident_In : forall (b : B) id st st',
        reuse_ident id b st = (tt, st') ->
        In (id, b) (st_anns st').
    Proof.
      intros. apply reuse_ident_anns in H.
      rewrite H. constructor. reflexivity.
    Qed.

    Fact reuse_ident_vars_perm : forall (b : B) id st st',
        reuse_ident id b st = (tt, st') ->
        Permutation (id::(st_ids st)) (st_ids st').
    Proof.
      intros. apply reuse_ident_anns in H.
      unfold st_ids in *. rewrite H.
      reflexivity.
    Qed.
  End reuse_ident.
End Facts.

Module Tactics.
  Import Fresh.
  Ltac inv_bind :=
    simpl in *;
    match goal with
    | H : context c [ret _ _] |- _ =>
      rewrite ret_spec in H
    | H : (_, _) = (_, _) |- _ =>
      inv H
    | H : bind _ _ _ = (_, _) |- _ =>
      apply bind_spec in H; destruct H as [? [? [? ?]]]; simpl in *
    | H : bind2 _ _ _ = (_, _) |- _ =>
      apply bind2_spec in H; destruct H as [? [? [? [? ?]]]]; simpl in *
    | |- context c [ret _ _] =>
      rewrite ret_spec
    | |- bind _ _ _ = (_, _) =>
      rewrite bind_spec
    | |- bind2 _ _ _ = (_, _) =>
      rewrite bind2_spec
    end.
End Tactics.

Module Notations.
  Import Fresh.
  (** [do] notation, inspired by CompCert's error monad *)
  Notation "'do' X <- A ; B" :=
    (bind A (fun X => B))
      (at level 200, X ident, A at level 100, B at level 200): fresh_monad_scope.

  Notation "'do' ( X , Y ) <- A ; B" :=
    (bind2 A (fun X Y => B))
      (at level 200, X ident, Y ident, A at level 100, B at level 200): fresh_monad_scope.
End Notations.

Section map_bind2.
  Import Fresh Tactics Notations.
  Open Scope fresh_monad_scope.
  Context {A A1 A2 B : Type}.
  Variable k : A -> Fresh (A1 * A2) B.

  Fixpoint map_bind2 a :=
    match a with
    | nil => ret (nil, nil)
    | hd::tl => do (a1, a2) <- k hd;
              do (a1s, a2s) <- map_bind2 tl;
              ret (a1::a1s, a2::a2s)
    end.

  Fact map_bind2_values : forall a st a1s a2s st',
      map_bind2 a st = (a1s, a2s, st') ->
      Forall3 (fun a a1 a2 => exists st'', exists st''', k a st'' = (a1, a2, st''')) a a1s a2s.
  Proof.
    induction a; intros st a1s a2s st' Hfold; simpl in *; repeat inv_bind.
    - constructor.
    - specialize (IHa _ _ _ _ H0).
      constructor; eauto.
  Qed.

  Fact map_bind2_st_valid : forall a a1s a2s st st' aft,
      map_bind2 a st = (a1s, a2s, st') ->
      Forall (fun a => forall a1 a2 st st',
                  k a st = (a1, a2, st') ->
                  st_valid_after st aft ->
                  st_valid_after st' aft) a ->
      st_valid_after st aft ->
      st_valid_after st' aft.
  Proof.
    induction a; intros a1s a2s st st' aft Hmap Hforall Hvalid;
      simpl in *; repeat inv_bind; auto.
    inv Hforall. eapply IHa; eauto.
  Qed.

  Fact map_bind2_st_valid_reuse : forall a a1s a2s st st' aft reusable,
      map_bind2 a st = (a1s, a2s, st') ->
      Forall (fun a => forall a1 a2 st st',
                  k a st = (a1, a2, st') ->
                  st_valid_reuse st aft reusable ->
                  st_valid_reuse st' aft reusable) a ->
      st_valid_reuse st aft reusable ->
      st_valid_reuse st' aft reusable.
  Proof.
    induction a; intros a1s a2s st st' aft reusable Hmap Hforall Hvalid;
      simpl in *; repeat inv_bind; auto.
    inv Hforall. eapply IHa; eauto.
  Qed.

  Fact map_bind2_weak_valid : forall a a1s a2s st st' aft,
      map_bind2 a st = (a1s, a2s, st') ->
      Forall (fun a => forall a1 a2 st st',
                  k a st = (a1, a2, st') ->
                  weak_valid_after st aft ->
                  weak_valid_after st' aft) a ->
      weak_valid_after st aft ->
      weak_valid_after st' aft .
  Proof.
    induction a; intros a1s a2s st st' aft Hmap Hforall Hvalid;
      simpl in *; repeat inv_bind; auto.
    inv Hforall. eapply IHa; eauto.
  Qed.

  Fact map_bind2_st_follows : forall a a1s a2s st st',
      map_bind2 a st = (a1s, a2s, st') ->
      Forall (fun a => forall a1 a2 st st', k a st = (a1, a2, st') -> st_follows st st') a ->
      st_follows st st'.
  Proof.
    induction a; intros a1s a2s st st' Hmap Hforall;
      simpl in *; repeat inv_bind; auto.
    - reflexivity.
    - inv Hforall.
      etransitivity; eauto.
  Qed.
End map_bind2.

Hint Resolve Fresh.st_valid_reuse_st_valid.
Hint Resolve Fresh.fresh_ident_st_valid.
Hint Resolve Fresh.fresh_ident_st_valid_reuse.
Hint Resolve Fresh.fresh_ident_weak_valid.
Hint Resolve Fresh.fresh_ident_st_follows.
Hint Resolve Fresh.reuse_ident_st_valid_reuse.
Hint Resolve Fresh.reuse_ident_weak_valid.
Hint Resolve Fresh.reuse_ident_st_follows.
Hint Resolve Fresh.st_follows_incl.
Hint Resolve map_bind2_st_valid.
Hint Resolve map_bind2_st_follows.
