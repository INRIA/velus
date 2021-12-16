From Velus Require Import Common.
From Velus Require Import Operators.

(* From Coq Require Import BinNums. *)
From Coq Require Import List.
From Coq Require Import Morphisms.
From Coq Require Import Permutation.
From Coq Require Import Classes.EquivDec.

Module Type CLOCKS
       (Import Ids : IDS)
       (Import Op     : OPERATORS)
       (Import OpAux  : OPERATORS_AUX Ids Op).

  (* Basic definitions around Clocks *)

  Inductive clock : Type :=
  | Cbase : clock                            (* base clock *)
  | Con   : clock -> ident -> type * enumtag -> clock. (* subclock *)

  (** ** Instantiate variable clocks from a base clock and substitution *)
  Fixpoint instck (bk: clock) (sub: ident -> option ident) (ck: clock)
    : option clock :=
    match ck with
    | Cbase => Some bk
    | Con ck x b =>
      match instck bk sub ck, sub x with
      | Some ck', Some x' => Some (Con ck' x' b)
      | _, _ => None
      end
    end.

  (* Named clocks *)

  (* Named clocks are used to track  interdependencies in clock
   annotations internal to expressions. *)

  Definition nclock : Type := clock * option ident.

  Definition stripname : nclock -> clock := fst.

  Definition indexes (ncks : list nclock) : list positive :=
    fold_right (fun nck acc => match snd nck with None => acc | Some nm => nm::acc end)
               nil ncks.

  Inductive Is_free_in_clock : ident -> clock -> Prop :=
  | FreeCon1:
      forall x ck' xc,
        Is_free_in_clock x (Con ck' x xc)
  | FreeCon2:
      forall x y ck' xc,
        Is_free_in_clock x ck'
        -> Is_free_in_clock x (Con ck' y xc).

  Open Scope bool.

  Fixpoint clock_eq (ck1 ck2: clock) : bool :=
    match ck1, ck2 with
    | Cbase, Cbase => true
    | Con ck1' x1 tc1, Con ck2' x2 tc2 =>
      (x1 ==b x2) && (tc1 ==b tc2) && clock_eq ck1' ck2'
    | _, _ => false
    end.

  Lemma clock_eq_spec:
    forall ck1 ck2,
      clock_eq ck1 ck2 = true <-> ck1 = ck2.
  Proof.
    induction ck1, ck2; split; intro HH; auto;
      try now inversion HH.
    - inversion HH as [Heq].
      apply andb_prop in Heq.
      destruct Heq as (Heq & Hc).
      apply andb_prop in Heq.
      destruct Heq as (Hi & Hb).
      rewrite equiv_decb_equiv in Hi; rewrite equiv_decb_equiv in Hb.
      rewrite Hi, Hb.
      apply IHck1 in Hc.
      subst. reflexivity.
    - inversion HH as [Heq].
      subst. simpl.
      rewrite Bool.andb_true_iff.
      split. 2:now apply IHck1.
      rewrite Bool.andb_true_iff.
      split; apply equiv_decb_refl.
  Qed.

  Global Instance clock_EqDec : EqDec clock eq.
  Proof.
    intros ck1 ck2. compute.
    pose proof (clock_eq_spec ck1 ck2) as Heq.
    destruct (clock_eq ck1 ck2); [left|right].
    now apply Heq.
    intro HH. apply Heq in HH.
    discriminate.
  Qed.

  Lemma clock_eqb_eq :
    forall (x y: clock), x ==b y = true <-> x = y.
  Proof.
    setoid_rewrite equiv_decb_equiv; reflexivity.
  Qed.

  Lemma clock_eqb_neq :
    forall (x y: clock), x ==b y = false <-> x <> y.
  Proof.
    intros *; split; intro H.
    - intro contra. rewrite <- clock_eqb_eq in contra. congruence.
    - destruct (x ==b y) eqn:Hec; auto.
      rewrite clock_eqb_eq in Hec. congruence.
  Qed.

  Global Instance nclock_EqDec : EqDec nclock eq.
  Proof.
    eapply prod_eqdec.
    - eapply clock_EqDec.
    - unfold EqDec.
      intros x y; destruct x; destruct y; try (right; congruence).
      + specialize (Common.EqDec_instance_0 i i0) as [?|?].
        * left. rewrite e. reflexivity.
        * right. intro contra. inv contra. congruence.
      + left. reflexivity.
  Qed.

  Lemma nclock_eqb_eq :
    forall (x y: nclock), x ==b y = true <-> x = y.
  Proof.
    setoid_rewrite equiv_decb_equiv; reflexivity.
  Qed.

  Lemma clock_not_in_clock:
    forall ck x b,
      ~(ck = Con ck x b).
  Proof.
    intros * Hck.
    induction ck; try discriminate.
    injection Hck; intros.
    apply IHck. now subst b x.
  Qed.

  (** ** Well-clocking *)

  Inductive wc_clock (vars: list (ident * clock)) : clock -> Prop :=
  | CCbase:
      wc_clock vars Cbase
  | CCon:
      forall ck x b,
        wc_clock vars ck ->
        In (x, ck) vars ->
        wc_clock vars (Con ck x b).

  Global Hint Constructors wc_clock : clocks lclocking.

  Definition wc_env vars : Prop :=
    Forall (fun xck => wc_clock vars (snd xck)) vars.

  Lemma wc_env_var:
    forall vars x ck,
      wc_env vars
      -> In (x, ck) vars
      -> wc_clock vars ck.
  Proof.
    intros vars x ck Hwc Hcv.
    now apply Forall_forall with (2:=Hcv) in Hwc.
  Qed.

  Lemma wc_clock_add:
    forall x v env ck,
      ~InMembers x env ->
      wc_clock env ck ->
      wc_clock ((x, v) :: env) ck.
  Proof.
    induction ck; auto using wc_clock.
    inversion 2.
    auto using wc_clock with datatypes.
  Qed.

  Lemma wc_env_add:
    forall x env ck,
      ~InMembers x env ->
      wc_clock env ck ->
      wc_env env ->
      wc_env ((x, ck) :: env).
  Proof.
    intros * Hnm Hwc Hwce.
    constructor.
    now apply wc_clock_add; auto.
    unfold wc_env in *. simpl_Forall.
    apply wc_clock_add; auto.
  Qed.

  Lemma wc_clock_sub:
    forall vars ck x b,
      wc_env vars
      -> wc_clock vars (Con ck x b)
      -> In (x, ck) vars.
  Proof.
    intros vars ck x b Hwc Hclock.
    inversion_clear Hclock as [|? ? ? Hclock' Hcv'].
    assumption.
  Qed.

  Global Instance wc_clock_Proper:
    Proper (@Permutation (ident * clock) ==> @eq clock ==> iff) wc_clock.
  Proof.
    intros env' env Henv ck' ck Hck.
    rewrite Hck; clear Hck ck'.
    induction ck.
    - split; auto using wc_clock.
    - destruct IHck.
      split; inversion_clear 1; constructor;
        try rewrite Henv in *;
        auto using wc_clock.
  Qed.

  Global Instance wc_env_Proper:
    Proper (@Permutation (ident * clock) ==> iff) wc_env.
  Proof.
    intros env' env Henv.
    unfold wc_env.
    split; intro HH.
    - rewrite <-Henv. simpl_Forall.
      now rewrite <-Henv.
    - rewrite Henv. simpl_Forall.
      now rewrite Henv.
  Qed.

  (** ** Parent relation *)

  Inductive clock_parent ck : clock -> Prop :=
  | CP0: forall x b,
      clock_parent ck (Con ck x b)
  | CP1: forall ck' x b,
      clock_parent ck ck'
      -> clock_parent ck (Con ck' x b).

  Global Hint Constructors clock_parent : clocks.

  Lemma clock_parent_parent':
    forall ck' ck i b,
      clock_parent (Con ck i b) ck'
      -> clock_parent ck ck'.
  Proof.
    induction ck' as [|? IH]; [now inversion 1|].
    intros ck i' b' Hcp.
    inversion Hcp as [|? ? ? Hcp']; [now auto with clocks|].
    apply IH in Hcp'; auto with clocks.
  Qed.

  Lemma clock_parent_parent:
    forall ck' ck i b,
      clock_parent (Con ck i b) ck'
      -> clock_parent ck (Con ck' i b).
  Proof.
    destruct ck'; [now inversion 1|].
    intros ck i' b' Hcp.
    inversion Hcp as [|? ? ? Hcp']; [now auto with clocks|].
    apply clock_parent_parent' in Hcp'; auto with clocks.
  Qed.

  Lemma clock_parent_trans:
    forall ck1 ck2 ck3,
      clock_parent ck1 ck2 ->
      clock_parent ck2 ck3 ->
      clock_parent ck1 ck3.
  Proof.
    induction ck2. now inversion 1.
    intros ck3 H12 H23.
    apply clock_parent_parent' in H23.
    inversion_clear H12; auto.
  Qed.

  Global Instance clock_parent_Transitive: Transitive clock_parent.
  Proof clock_parent_trans.

  Lemma clock_parent_Cbase:
    forall ck i b,
      clock_parent Cbase (Con ck i b).
  Proof.
    induction ck as [|? IH]; [now constructor|].
    intros; constructor; apply IH.
  Qed.

  Lemma clock_parent_not_refl:
    forall ck,
      ~clock_parent ck ck.
  Proof.
    induction ck as [|? IH]; [now inversion 1|].
    intro Hp; inversion Hp as [? ? HR|? ? ? Hp'].
    - rewrite HR in Hp; contradiction.
    - apply clock_parent_parent' in Hp'; contradiction.
  Qed.

  Lemma clock_parent_no_loops:
    forall ck ck',
      clock_parent ck ck'
      -> ck <> ck'.
  Proof.
    intros ck ck' Hck Heq.
    rewrite Heq in Hck.
    apply clock_parent_not_refl with (1:=Hck).
  Qed.

  Lemma clock_no_loops:
    forall ck x b,
      Con ck x b <> ck.
  Proof.
    induction ck as [|? IH]; [discriminate 1|].
    injection 1; intros ? Heq.
    apply IH.
  Qed.

  Lemma clock_parent_Con:
    forall ck ck' i b j c,
      clock_parent (Con ck i b) (Con ck' j c)
      -> clock_parent ck ck'.
  Proof.
    destruct ck; induction ck' as [|? IH].
    - inversion 1 as [|? ? ? Hp].
      apply clock_parent_parent' in Hp; inversion Hp.
    - intros; now apply clock_parent_Cbase.
    - inversion 1 as [|? ? ? Hp]; inversion Hp.
    - intros i' b' j  c.
      inversion 1 as [? ? Hck'|? ? ? Hp];
        [rewrite Hck' in IH; now constructor|].
      apply IH in Hp; auto with clocks.
  Qed.

  Lemma clock_parent_strict':
    forall ck' ck,
      ~(clock_parent ck ck' /\ clock_parent ck' ck).
  Proof.
    induction ck' as [|? IH]; destruct ck; destruct 1 as [Hp Hp'];
      try now (inversion Hp || inversion Hp').
    apply clock_parent_Con in Hp.
    apply clock_parent_Con in Hp'.
    eapply IH; split; eassumption.
  Qed.

  Lemma clock_parent_strict:
    forall ck' ck,
      (clock_parent ck ck' -> ~clock_parent ck' ck).
  Proof.
    destruct ck'; [now inversion 1|].
    intros ck Hp Hp'.
    eapply clock_parent_strict'; split; eassumption.
  Qed.

  Lemma Con_not_clock_parent:
    forall ck x b,
      ~clock_parent (Con ck x b) ck.
  Proof.
    intros ck x b Hp; apply clock_parent_strict with (1:=Hp); constructor.
  Qed.

  Lemma Is_free_in_clock_self_or_parent:
    forall x ck,
      Is_free_in_clock x ck
      -> exists ck' b, ck = Con ck' x b \/ clock_parent (Con ck' x b) ck.
  Proof.
    induction ck as [|? IH]; [now inversion 1|].
    intro Hfree.
    inversion Hfree as [|? ? ? ? Hfree']; clear Hfree; subst.
    - exists ck, p; now auto.
    - specialize (IH Hfree'); clear Hfree'.
      destruct IH as [ck' [b' Hcp]].
      exists ck', b'; right.
      destruct Hcp as [Hcp|Hcp]; [rewrite Hcp| inversion Hcp]; now auto with clocks.
  Qed.

  Lemma Is_free_in_clock_parent: forall vars x ck ck',
      NoDupMembers vars ->
      In (x, ck') vars ->
      wc_clock vars ck ->
      Is_free_in_clock x ck ->
      clock_parent ck' ck.
  Proof.
    induction ck as [|? IH]; intros ck' Hndup Hin Hwc Hfree;
      inv Hfree; inv Hwc.
    - clear IH.
      eapply NoDupMembers_det with (t:=ck) (t':=ck') in Hndup; eauto; subst.
      constructor.
    - constructor; auto.
  Qed.

  Lemma wc_clock_parent:
    forall C ck' ck,
      wc_env C
      -> clock_parent ck ck'
      -> wc_clock C ck'
      -> wc_clock C ck.
  Proof.
    induction ck' as [|ck' IH]; destruct ck as [|ck i' ty'];
      try now (inversion 3 || auto with clocks); auto with clocks.
    intros Hwc Hp Hck.
    inversion Hp as [j c [HR1 HR2 HR3]|ck'' j c Hp' [HR1 HR2 HR3]].
    - rewrite <-HR1 in *; clear HR1 HR2 HR3.
      now inversion_clear Hck.
    - subst.
      apply IH with (1:=Hwc) (2:=Hp').
      now inversion Hck.
  Qed.

  Lemma instck_parent:
    forall bk sub ck ck',
      instck bk sub ck = Some ck' ->
      ck' = bk \/ clock_parent bk ck'.
  Proof.
    induction ck.
    now inversion_clear 1; auto.
    simpl. intros ck' Hi. right.
    destruct (instck bk sub ck). 2:discriminate.
    destruct (sub i). 2:discriminate.
    specialize (IHck c eq_refl).
    inversion_clear Hi.
    destruct IHck; subst; auto with clocks.
  Qed.

  Lemma instck_subclock_not_clock_eq:
    forall ck isub xck c x b,
      instck ck isub xck = Some c ->
      clock_eq ck (Con c x b) = false.
  Proof.
    intros * Hck.
    apply Bool.not_true_is_false.
    intro Heq. apply clock_eq_spec in Heq.
    apply instck_parent in Hck as [Hck|Hck].
    now subst c; apply clock_not_in_clock in Heq.
    now subst ck; apply Con_not_clock_parent in Hck.
  Qed.

  Lemma clock_parent_dec : forall ck ck',
      clock_parent ck ck' \/ ~clock_parent ck ck'.
  Proof.
    intros ck; induction ck'.
    - right. intro contra; inv contra.
    - destruct IHck'.
      + left. constructor; auto.
      + destruct (clock_EqDec ck ck') as [Heq|Hneq].
        * rewrite Heq. left. constructor.
        * right. intro contra. inv contra; try congruence.
  Qed.

  Lemma exists_child_clock : forall (vars : list (ident * clock)),
      vars = nil \/
      exists id, exists ck,
          In (id, ck) vars /\
          Forall (fun '(_, ck') => ~clock_parent ck ck') vars.
  Proof.
    induction vars; auto.
    right. destruct a as [id ck]. destruct IHvars as [?|[id' [ck' [HIn cl]]]]; subst.
    - exists id. exists ck. split; constructor; auto.
      intro contra. apply clock_parent_no_loops in contra; auto.
    - destruct (clock_parent_dec ck' ck).
      + exists id. exists ck. split.
        * left; auto.
        * constructor; auto.
          intro contra.
          eapply clock_parent_strict; eauto.
          eapply Forall_impl; eauto.
          intros [id'' ck''] Hpar; simpl in Hpar.
          intro contra. apply Hpar. etransitivity; eauto.
      + exists id'. exists ck'. split.
        * right; auto.
        * constructor; auto.
  Qed.

  Corollary exists_child_clock' : forall (vars : list (ident * clock)),
      NoDupMembers vars ->
      wc_env vars ->
      vars = nil \/
      exists id, exists ck,
          In (id, ck) vars /\
          Forall (fun '(_, ck') => ~Is_free_in_clock id ck') vars.
  Proof.
    intros vars Hndup Hwc.
    destruct (exists_child_clock vars) as [?|[id [ck [Hin Hclock]]]]; auto.
    right. exists id. exists ck. split; auto.
    eapply Forall_impl_In; eauto.
    intros [id' ck'] Hin' H; simpl in H.
    intro contra. apply H; clear H.
    eapply Is_free_in_clock_parent; eauto.
    unfold wc_env in Hwc. simpl_Forall; auto.
  Qed.

  Lemma wc_clock_nparent_remove : forall vars id ck ck',
      ~clock_parent ck' ck ->
      wc_clock ((id, ck')::vars) ck ->
      wc_clock vars ck.
  Proof.
    induction ck; intros ck' Hnpar Hwc; constructor; inv Hwc.
    - eapply IHck; eauto with clocks.
    - destruct H3; eauto with clocks.
      inv H.
      exfalso. apply Hnpar. constructor.
  Qed.

  Corollary wc_clock_no_loops_remove : forall vars id ck,
      wc_clock ((id, ck)::vars) ck ->
      wc_clock vars ck.
  Proof.
    intros vars id ck Hwc.
    apply wc_clock_nparent_remove in Hwc; auto.
    intro contra. apply clock_parent_no_loops in contra. congruence.
  Qed.

  Lemma instck_inv :
    forall bck sub ck ck' x,
      instck bck sub ck = Some ck' ->
      Is_free_in_clock x ck' ->
      Is_free_in_clock x bck \/
      (exists x', sub x' = Some x /\ Is_free_in_clock x' ck).
  Proof.
    induction ck; intros * Hinst Hfree.
    - inv Hinst. auto.
    - inversion Hinst as [Hins]. cases_eqn Hins. inv Hins.
      inversion_clear Hfree as [| ???? Hfr].
      right. exists i. split. auto. constructor.
      apply IHck in Hfr as [|[y []]] ; auto. right.
      exists y. split; auto. now constructor.
  Qed.

  Lemma instck_free_bck :
    forall bck sub ck ck' x,
      instck bck sub ck = Some ck' ->
      Is_free_in_clock x bck ->
      Is_free_in_clock x ck'.
  Proof.
    induction ck; intros * Hinst Hfree.
    - inv Hinst. auto.
    - inversion Hinst as [Hins]. cases_eqn Hins. inv Hins.
      specialize (IHck c x eq_refl Hfree). now constructor.
  Qed.

  Lemma instck_free_sub :
    forall bck sub ck ck' x x',
      instck bck sub ck = Some ck' ->
      Is_free_in_clock x ck ->
      sub x = Some x' ->
      Is_free_in_clock x' ck'.
  Proof.
    induction ck; intros * Hinst Hfree Hsub.
    - inv Hfree.
    - inv Hfree.
      + inversion Hinst as [Hins]. cases_eqn Hins. inv Hsub. inv Hins.
        constructor.
      + inversion Hinst as [Hins]. cases_eqn Hins. inv Hins.
        specialize (IHck c x x' eq_refl H1 Hsub). now constructor.
  Qed.

  (** ** Checking parent relation *)

  Fixpoint is_clock_parent ck1 ck2 :=
    match ck2 with
    | Cbase => false
    | Con ck2' _ _ =>
      (ck1 ==b ck2') || (is_clock_parent ck1 ck2')
    end.

  Lemma is_clock_parent_spec : forall ck1 ck2,
      is_clock_parent ck1 ck2 = true <-> clock_parent ck1 ck2.
  Proof.
    split; intros Hck; induction ck2; simpl in *; try congruence.
    - apply Bool.orb_true_iff in Hck as [Heq|Hck]; auto with clocks.
      apply clock_eqb_eq in Heq; subst.
      constructor.
    - inv Hck.
    - apply Bool.orb_true_iff. inv Hck; auto.
      left. apply equiv_decb_refl.
  Qed.

End CLOCKS.

Module ClocksFun
       (Ids    : IDS)
       (Op     : OPERATORS)
       (OpAux  : OPERATORS_AUX Ids Op)
<: CLOCKS Ids Op OpAux.
  Include CLOCKS Ids Op OpAux.
End ClocksFun.
