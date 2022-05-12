From Velus Require Import Common.
From Cpo Require Import Cpo_def Cpo_streams_type Systems.

Require Import Cpo_ext.
Require Import SDfuns.

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

Lemma nrem_inf :
  forall (s : DS A), (forall n, is_cons (nrem n s)) -> infinite s.
Proof.
  cofix Cof; intros * Hc.
  constructor.
  - apply (Hc O).
  - apply Cof.
    intro n.
    apply (Hc (S n)).
Qed.

Lemma inf_nrem :
  forall (s : DS A), infinite s -> forall n, is_cons (nrem n s).
Proof.
  intros * Hf n.
  revert dependent s.
  induction n; intros; inversion Hf; simpl; auto.
Qed.

Lemma is_consn_DS_const :
  forall (c : A) n,
    is_cons (nrem n (DS_const c)).
Proof.
  induction n; simpl; rewrite DS_const_eq, ?rem_cons; auto.
Qed.

Lemma nrem_rem :
  forall (s : DS A) n,
    nrem n (rem s) == rem (nrem n s).
Proof.
  intros.
  revert s.
  induction n; simpl; auto.
Qed.

Lemma is_consn_S :
  forall (s : DS A) n,
    is_cons (nrem (S n) s) -> is_cons (nrem n s).
Proof.
  induction n; simpl; auto.
  rewrite nrem_rem.
  auto using is_cons_rem.
Qed.

Lemma is_consn_is_cons :
  forall (s : DS A) n,
    is_cons (nrem n s) -> is_cons s.
Proof.
  induction n; simpl; auto.
  rewrite nrem_rem.
  auto using is_cons_rem.
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
    induction n; simpl.
    - unfold alt.
      rewrite FIXP_eq.
      autorewrite with cpodb; auto.
    - unfold alt in *.
      rewrite FIXP_eq.
      autorewrite with cpodb.
      rewrite nrem_map; auto.
  Qed.
End Alt_inf.


(** ** Productivity of stream operators *)

Section Ncons_ops.

Context {A B : Type}.

Ltac solve_err :=
  try match goal with
    | |- context [ DS_const _ ] =>
        repeat rewrite DS_const_eq, rem_cons;
        now auto using is_cons_DS_const, is_consn_DS_const
    end.

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

Lemma is_consn_S_fby1 :
  forall n v (xs ys : DS (sampl A)),
    is_cons (nrem (S n) xs) ->
    is_cons (nrem n ys) ->
    is_cons (nrem (S n) (fby1 v xs ys)).
Proof.
  induction n; intros * Hx Hy.
  - simpl.
    apply is_cons_rem in Hx as (?&?&?&->).
    apply is_cons_elim in Hy as (?&?&->).
    rewrite fby1_eq.
    cases; solve_err; rewrite fby1AP_eq.
    all: cases; solve_err; rewrite fby1_eq.
    all: cases; solve_err; autorewrite with cpodb; auto.
  - (* FIXME: pas de simpl sur nrem ici sinon Qed est interminable *)
    repeat rewrite nrem_S in *.
    setoid_rewrite nrem_S in IHn.
    apply is_consn_is_cons in Hx as Hc.
    apply is_cons_rem in Hc as (x2 & x3 & xs' & Hc).
    apply rem_eq_cons in Hc as (x1 & Hc).
    apply is_consn_is_cons in Hy as Hd.
    apply is_cons_rem in Hd as (y1 & y2 & ys' & Hd).
    rewrite Hc, Hd, fby1_eq, 2 rem_cons in *.
    cases; solve_err; rewrite fby1AP_eq; autorewrite with cpodb.
    all: cases; solve_err.
    all: apply IHn; autorewrite with cpodb; auto using is_consn_S.
Qed.

Lemma is_consn_S_fby :
  forall n (xs ys : DS (sampl A)),
    is_cons (nrem (S n) xs) ->
    is_cons (nrem n ys) ->
    is_cons (nrem (S n) (fby xs ys)).
Proof.
  induction n; intros * Hx Hy.
  - simpl.
    apply is_cons_rem in Hx as (?&?&?&->).
    apply is_cons_elim in Hy as (?&?&->).
    rewrite fby_eq.
    cases; solve_err; rewrite ?fbyA_eq, ?fby1AP_eq.
    all: cases; solve_err; rewrite ?fby_eq, ?fby1_eq.
    all: cases; solve_err; autorewrite with cpodb; auto.
  - repeat rewrite nrem_S in *.
    setoid_rewrite nrem_S in IHn.
    apply is_consn_is_cons in Hx as Hc.
    apply is_cons_rem in Hc as (x2 & x3 & xs' & Hc).
    apply rem_eq_cons in Hc as (x1 & Hc).
    apply is_consn_is_cons in Hy as Hd.
    apply is_cons_rem in Hd as (y1 & y2 & ys' & Hd).
    rewrite Hc, Hd, fby_eq, 2 rem_cons in *.
    cases; solve_err; rewrite ?fbyA_eq, ?fby1AP_eq.
    all: autorewrite with cpodb; cases; solve_err.
    + apply IHn; autorewrite with cpodb; auto using is_consn_S.
    + rewrite <- nrem_S.
      apply is_consn_S_fby1; rewrite ?nrem_S; now autorewrite with cpodb.
Qed.

Lemma is_consn_fby :
  forall n (xs ys : DS (sampl A)),
    is_cons (nrem n xs) ->
    is_cons (nrem n ys) ->
    is_cons (nrem n (SDfuns.fby xs ys)).
Proof.
  intros.
  destruct n.
  apply is_cons_fby; auto.
  apply is_consn_S_fby, is_consn_S; auto.
Qed.


Lemma is_consn_sunop :
  forall (f : A -> option B) s n,
    is_cons (nrem n s) ->
    is_cons (nrem n (sunop f s)).
Proof.
  intros.
  unfold sunop.
  rewrite MAP_map, nrem_map.
  now apply is_cons_map.
Qed.

Lemma is_consn_sconst :
  forall (c : A) bs n,
    is_cons (nrem n bs) ->
    is_cons (nrem n (sconst c bs)).
Proof.
  intros.
  unfold sconst.
  rewrite MAP_map, nrem_map.
  now apply is_cons_map.
Qed.

End Ncons_ops.
