
Require Import Common.

Require Import lib.Coqlib.
Require Import cfrontend.Clight.

Lemma NoDup_norepet:
  forall {A} (l: list A),
    NoDup l <-> list_norepet l.
Proof.
  induction l; split; constructor.
  - now inversion H.
  - apply IHl; now inversion H.
  - now inversion H.
  - apply IHl; now inversion H.
Qed.

Lemma NoDupMembers_disjoint:
  forall l1 l2,
    NoDupMembers (l1 ++ l2) ->
    list_disjoint (var_names l1) (var_names l2).
Proof.
  unfold list_disjoint, var_names.
  intros l1 l2 H x y Hx Hy.
  apply in_map_iff in Hx; destruct Hx as ((x', tx) & Ex & Hx);
    apply in_map_iff in Hy; destruct Hy as ((y', ty) & Ey & Hy);
      simpl in *; subst.
  intro E; subst.
  apply in_split in Hx; destruct Hx as (lx & lx' & Hx);
    apply in_split in Hy; destruct Hy as (ly & ly' & Hy);
      subst.
  rewrite <-app_assoc in H.
  apply NoDupMembers_app_r in H.
  rewrite <-app_comm_cons, nodupmembers_cons in H.
  destruct H as [Notin]; apply Notin.
  apply InMembers_app; right; apply InMembers_app; right; apply inmembers_eq.
Qed.

