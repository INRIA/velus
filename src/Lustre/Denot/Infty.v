From Velus Require Import Common.
From Velus Require Import Lustre.Denot.Cpo.
Require Import Cpo_ext SDfuns.

(** * Infinity of streams defined in SDfuns  *)

(** Definition and specification of [nrem] : [n] applications of [rem].
    It is useful to show the productivity of stream functions.
    A function [f] of a stream [xs] is producive/length-preserving if
    for all n, [is_cons (nrem n xs)] implies [is_cons (n_rem n (f xs))].
 *)
Section Nrem.

Context {A : Type}.

Fixpoint nrem (n : nat) (xs : DS A) : DS A :=
  match n with
  | O => xs
  | S n => nrem n (rem xs)
  end.

Lemma nrem_S : forall n (xs : DS A),
    nrem (S n) xs = nrem n (rem xs).
Proof.
  trivial.
Qed.

(** On prend True pour n = 0 afin de simplifier les cas de base dans
    les preuves d'InftyProof (voir [exp_n] par exemple). *)
Definition is_ncons (n : nat) (xs : DS A) : Prop :=
  match n with
  | O => True
  | S n => is_cons (nrem n xs)
  end.

Lemma nrem_inf :
  forall (s : DS A), (forall n, is_ncons n s) -> infinite s.
Proof.
  cofix Cof; intros * Hc.
  constructor.
  - apply (Hc 1).
  - apply Cof.
    intros []; simpl; auto.
    apply (Hc (S (S n))).
Qed.

Lemma inf_nrem :
  forall (s : DS A), infinite s -> forall n, is_ncons n s.
Proof.
  intros * Hf n.
  revert dependent s.
  induction n as [|[]]; intros; inversion Hf; simpl; auto.
  apply IHn; auto.
Qed.

Lemma nrem_inf_iff :
  forall (s : DS A), (forall n, is_ncons n s) <-> infinite s.
Proof.
  split; auto using nrem_inf, inf_nrem.
Qed.

Lemma is_consn_DS_const :
  forall (c : A) n,
    is_cons (nrem n (DS_const c)).
Proof.
  induction n; simpl; rewrite DS_const_eq, ?rem_cons; auto.
Qed.

Lemma is_ncons_DS_const :
  forall (c : A) n,
    is_ncons n (DS_const c).
Proof.
  induction n as [|[]]; simpl; auto; rewrite DS_const_eq, ?rem_cons; auto.
Qed.

Lemma nrem_rem :
  forall (s : DS A) n,
    nrem n (rem s) == rem (nrem n s).
Proof.
  intros.
  revert s.
  induction n; simpl; auto.
Qed.

Lemma is_ncons_S :
  forall (s : DS A) n,
    is_ncons (S n) s -> is_ncons n s.
Proof.
  induction n as [|[]]; simpl; auto.
  rewrite nrem_rem; auto.
Qed.

Lemma is_ncons_SS :
  forall n (xs : DS A),
    is_ncons (S (S n)) xs <-> is_ncons (S n) (rem xs).
Proof.
  destruct n; simpl; split; auto.
Qed.

Lemma is_ncons_is_cons :
  forall (s : DS A) n,
    is_ncons (S n) s -> is_cons s.
Proof.
  induction n; simpl; auto.
  rewrite nrem_rem.
  intro.
  now apply IHn, rem_is_cons.
Qed.

Lemma nrem_eq_compat : forall n (s t:DS A), s==t -> nrem n s == nrem n t.
Proof.
  induction n; simpl; auto.
Qed.

Global Add Parametric Morphism n : (nrem n)
       with signature (@Oeq (DS A)) ==> (@Oeq (DS A)) as nrem_eq_compat_morph.
Proof.
  exact (@nrem_eq_compat n).
Qed.

Global Add Parametric Morphism n : (is_ncons n)
       with signature (@Oeq (DS A)) ==> iff as is_ncons_morph.
Proof.
  unfold is_ncons.
  intros * H.
  cases; now rewrite ?H.
Qed.


End Nrem.

Lemma nrem_map :
  forall {A B} (f : A -> B) n xs,
    nrem n (map f xs) == map f (nrem n xs).
Proof.
  induction n; simpl; intros; auto.
  rewrite rem_map; auto.
Qed.

Module Alt_inf.
  (** example of usage *)
  Definition alt : DS bool := FIXP _ (CONS true @_ MAP negb).
  Lemma alt_inf : infinite alt.
  Proof.
    apply nrem_inf.
    induction n as [|[]]; simpl; auto.
    - unfold alt.
      rewrite FIXP_eq.
      autorewrite with cpodb; auto.
    - unfold alt in *.
      rewrite FIXP_eq.
      autorewrite with cpodb.
      rewrite nrem_map; auto.
  Qed.
End Alt_inf.


Ltac solve_err :=
  try match goal with
    | |- context [ DS_const _ ] =>
        repeat rewrite DS_const_eq, rem_cons;
        now auto using is_cons_DS_const, is_consn_DS_const, is_ncons_DS_const
    end.

(** ** Productivity of primitive stream functions  *)

Section Ncons_DS.

Context {A B D : Type}.

Lemma is_ncons_zip :
  forall (f : A -> B -> D) n xs ys,
    is_ncons n xs ->
    is_ncons n ys ->
    is_ncons n (ZIP f xs ys).
Proof.
  induction n as [|[]]; simpl; intros * Cx Cy; auto using is_cons_zip.
  apply is_ncons_is_cons in Cx as Hx.
  apply is_cons_rem in Hx as (?&?&?& Hx); rewrite Hx in *.
  apply is_ncons_is_cons in Cy as Hy.
  apply is_cons_rem in Hy as (?&?&?& Hy); rewrite Hy in *.
  rewrite zip_cons, rem_cons in *.
  apply IHn; auto.
Qed.

Lemma is_ncons_map :
  forall A B (f : A -> B) s n,
    is_ncons n s ->
    is_ncons n (map f s).
Proof.
  unfold is_ncons.
  intros; cases.
  rewrite nrem_map.
  now apply is_cons_map.
Qed.

End Ncons_DS.


(** ** Productivity of Lustre operators *)

Section Ncons_ops.

Context {A B D : Type}.

Lemma is_ncons_sconst :
  forall (c : A) bs n,
    is_ncons n bs ->
    is_ncons n (sconst c bs).
Proof.
  intros.
  now apply is_ncons_map.
Qed.

Lemma sconst_inf :
  forall (c : A) bs,
    infinite bs ->
    infinite (sconst c bs).
Proof.
  setoid_rewrite <- nrem_inf_iff.
  intros.
  auto using is_ncons_sconst.
Qed.

Lemma is_ncons_sunop :
  forall (f : A -> option B) s n,
    is_ncons n s ->
    is_ncons n (sunop f s).
Proof.
  intros.
  now apply is_ncons_map.
Qed.

Lemma sunop_inf :
  forall (op : A -> option B) s,
    infinite s ->
    infinite (sunop op s).
Proof.
  setoid_rewrite <- nrem_inf_iff.
  intros.
  auto using is_ncons_sunop.
Qed.

Lemma is_ncons_sbinop :
  forall (f : A -> B -> option D) s1 s2 n,
    is_ncons n s1 ->
    is_ncons n s2 ->
    is_ncons n (sbinop f s1 s2).
Proof.
  intros.
  unfold sbinop.
  autorewrite with cpodb; simpl.
  now apply is_ncons_map, is_ncons_zip.
Qed.

Lemma sbinop_inf :
  forall (f : A -> B -> option D) s1 s2,
    infinite s1 ->
    infinite s2 ->
    infinite (sbinop f s1 s2).
Proof.
  setoid_rewrite <- nrem_inf_iff.
  intros.
  auto using is_ncons_sbinop.
Qed.

Lemma is_cons_fby :
  forall (xs ys : DS (sampl A)),
    is_cons xs ->
    is_cons (fby xs ys).
Proof.
  intros * Hx.
  apply is_cons_elim in Hx as (?&?&->).
  rewrite fby_eq.
  cases; solve_err.
Qed.

Lemma is_ncons_S_fby1 :
  forall n v (xs ys : DS (sampl A)),
    is_ncons (S n) xs ->
    is_ncons n ys ->
    is_ncons (S n) (fby1 v xs ys).
Proof.
  induction n as [|[]]; intros * Hx Hy.
  - apply is_cons_elim in Hx as (?&?&->).
    rewrite fby1_eq. simpl. cases; solve_err.
  - simpl in *.
    apply is_cons_rem in Hx as (?&?&?&->).
    apply is_cons_elim in Hy as (?&?&->).
    rewrite fby1_eq.
    cases; solve_err; rewrite fby1AP_eq.
    all: cases; solve_err; rewrite fby1_eq.
    all: cases; solve_err; autorewrite with cpodb; auto.
  - (* FIXME: pas de simpl sur nrem ici sinon Qed est interminable *)
    unfold is_ncons in *.
    repeat rewrite nrem_S in *.
    setoid_rewrite nrem_S in IHn.
    apply is_ncons_is_cons in Hx as Hc.
    apply is_cons_rem in Hc as (x2 & x3 & xs' & Hc).
    apply rem_eq_cons in Hc as (x1 & Hc).
    apply is_ncons_is_cons in Hy as Hd.
    apply is_cons_rem in Hd as (y1 & y2 & ys' & Hd).
    rewrite Hc, Hd, fby1_eq, 2 rem_cons in *.
    cases; solve_err; rewrite fby1AP_eq; autorewrite with cpodb.
    all: cases; solve_err.
    all: apply IHn; autorewrite with cpodb; auto.
Qed.

Lemma is_ncons_S_fby :
  forall n (xs ys : DS (sampl A)),
    is_ncons (S n) xs ->
    is_ncons n ys ->
    is_ncons (S n) (fby xs ys).
Proof.
  induction n as [|[]]; intros * Hx Hy.
  - apply is_cons_elim in Hx as (?&?&->).
    rewrite fby_eq. simpl. cases; solve_err.
  - simpl.
    apply is_cons_rem in Hx as (?&?&?&->).
    apply is_cons_elim in Hy as (?&?&->).
    rewrite fby_eq.
    cases; solve_err; rewrite ?fbyA_eq, ?fby1AP_eq.
    all: cases; solve_err; rewrite ?fby_eq, ?fby1_eq.
    all: cases; solve_err; autorewrite with cpodb; auto.
  - unfold is_ncons in *.
    repeat rewrite nrem_S in *.
    setoid_rewrite nrem_S in IHn.
    apply is_ncons_is_cons in Hx as Hc.
    apply is_cons_rem in Hc as (x2 & x3 & xs' & Hc).
    apply rem_eq_cons in Hc as (x1 & Hc).
    apply is_ncons_is_cons in Hy as Hd.
    apply is_cons_rem in Hd as (y1 & y2 & ys' & Hd).
    rewrite Hc, Hd, fby_eq, 2 rem_cons in *.
    cases; solve_err; rewrite ?fbyA_eq, ?fby1AP_eq.
    all: autorewrite with cpodb; cases; solve_err.
    + apply IHn; autorewrite with cpodb; auto.
    + rewrite <- nrem_S.
      apply is_ncons_S_fby1; unfold is_ncons;
        rewrite ?nrem_S; now autorewrite with cpodb.
Qed.

Lemma is_ncons_fby :
  forall n (xs ys : DS (sampl A)),
    is_ncons n xs ->
    is_ncons n ys ->
    is_ncons n (SDfuns.fby xs ys).
Proof.
  intros.
  destruct n as [|[]]; auto.
  apply is_cons_fby; auto.
  apply is_ncons_S_fby, is_ncons_S; auto.
Qed.

Lemma fby_inf :
  forall (xs ys : DS (sampl A)),
    infinite xs ->
    infinite ys ->
    infinite (SDfuns.fby xs ys).
Proof.
  setoid_rewrite <- nrem_inf_iff.
  intros.
  auto using is_ncons_fby.
Qed.

Lemma is_cons_swhen :
  forall T OT TB,
  forall k xs cs,
    is_cons xs ->
    is_cons cs ->
    is_cons (@swhen A B T OT TB k xs cs).
Proof.
  intros * Hx Hc.
  apply is_cons_elim in Hx as (?&?&->).
  apply is_cons_elim in Hc as (?&?&->).
  rewrite swhen_eq.
  cases; solve_err.
Qed.

Lemma is_ncons_swhen :
  forall T OT TB,
  forall k n xs cs,
    is_ncons n xs ->
    is_ncons n cs ->
    is_ncons n (@swhen A B T OT TB k xs cs).
Proof.
  induction n as [|[]]; simpl; intros * Hx Hc; auto.
  - apply is_cons_swhen; auto.
  - unfold is_ncons in *.
    apply is_ncons_is_cons in Hx as Hx'.
    apply is_ncons_is_cons in Hc as Hc'.
    apply is_cons_rem in Hx' as (?&?&?& Hx').
    apply is_cons_rem in Hc' as (?&?&?& Hc').
    rewrite Hx', Hc' in *.
    rewrite swhen_eq.
    cases; solve_err.
    all: autorewrite with cpodb in Hx,Hc |- *; auto.
Qed.

Lemma swhen_inf :
  forall T OT TB,
  forall k xs cs,
    infinite xs ->
    infinite cs ->
    infinite (@swhen A B T OT TB k xs cs).
Proof.
  setoid_rewrite <- nrem_inf_iff.
  intros.
  eauto using is_ncons_swhen.
Qed.

Lemma is_ncons_zip3 :
  forall A B C D (op : A -> B -> C -> D),
  forall xs ys zs n,
    is_ncons n xs /\ is_ncons n ys /\ is_ncons n zs ->
    is_ncons n (ZIP3 op xs ys zs).
Proof.
  intros * (Cx & Cy & Cz).
  rewrite zip3_eq.
  auto using is_ncons_zip.
Qed.

Lemma is_ncons_smerge :
  forall T OT TB,
  forall l n xs cs,
    is_ncons n cs ->
    forall_nprod (@is_ncons _ n) xs ->
    is_ncons n (@smerge A B T OT TB l cs xs).
Proof.
  intros * Hc Hx.
  rewrite smerge_eq.
  eapply forall_nprod_Foldi in Hx; eauto using is_ncons_map.
  simpl; intros.
  now apply is_ncons_zip3.
Qed.

Lemma smerge_inf :
  forall T OT TB,
  forall l xs cs,
    infinite cs ->
    forall_nprod (@infinite _) xs ->
    infinite (@smerge A B T OT TB l cs xs).
Proof.
  setoid_rewrite <- nrem_inf_iff.
  intros * Inf Hf n.
  apply is_ncons_smerge; eauto using inf_nrem, forall_nprod_impl.
Qed.

Lemma is_ncons_scase :
  forall T OT TB,
  forall l n xs cs,
    is_ncons n cs ->
    forall_nprod (@is_ncons _ n) xs ->
    is_ncons n (@scase A B T OT TB l cs xs).
Proof.
  intros * Hc Hx.
  rewrite scase_eq.
  eapply forall_nprod_Foldi in Hx; eauto using is_ncons_map.
  simpl; intros.
  now apply is_ncons_zip3.
Qed.

Lemma scase_inf :
  forall T OT TB,
  forall l xs cs,
    infinite cs ->
    forall_nprod (@infinite _) xs ->
    infinite (@scase A B T OT TB l cs xs).
Proof.
  setoid_rewrite <- nrem_inf_iff.
  intros * Inf Hf n.
  apply is_ncons_scase; eauto using inf_nrem, forall_nprod_impl.
Qed.

Lemma is_ncons_scase_def_ :
  forall T OT TB,
  forall l n cs ds xs,
    is_ncons n cs ->
    is_ncons n ds ->
    forall_nprod (@is_ncons _ n) xs ->
    is_ncons n (@scase_def_ A B T OT TB l cs ds xs).
Proof.
  intros * Hc Hd Hx.
  rewrite scase_def__eq.
  apply forall_nprod_Foldi with (Q := is_ncons n);
    auto using is_ncons_zip3, is_ncons_zip.
Qed.

Lemma is_ncons_scase_def :
  forall T OT TB,
  forall l n cs dxs,
    is_ncons n cs ->
    forall_nprod (@is_ncons _ n) dxs ->
    is_ncons n (@scase_def A B T OT TB l cs dxs).
Proof.
  intros * Hc [Hh Ht] % forall_nprod_inv.
  rewrite (nprod_hd_tl dxs).
  rewrite scase_def_eq; auto using is_ncons_scase_def_.
Qed.

Lemma scase_def__inf :
  forall T OT TB,
  forall l cs ds xs,
    infinite cs ->
    infinite ds ->
    forall_nprod (@infinite _) xs ->
    infinite (@scase_def_ A B T OT TB l cs ds xs).
Proof.
  setoid_rewrite <- nrem_inf_iff.
  intros * Infc Infd Infx n.
  apply is_ncons_scase_def_; eauto using inf_nrem, forall_nprod_impl.
Qed.

Lemma scase_def_inf :
  forall T OT TB,
  forall l cs dxs,
    infinite cs ->
    forall_nprod (@infinite _) dxs ->
    infinite (@scase_def A B T OT TB l cs dxs).
Proof.
  setoid_rewrite <- nrem_inf_iff.
  intros * Infc Infd n.
  apply is_ncons_scase_def; eauto using inf_nrem, forall_nprod_impl.
Qed.

End Ncons_ops.
