Require Import Coq.FSets.FMapPositive.
Require Import Rustre.Common.
Require Import Rustre.DataflowSyntax.
Require Import SynchronousNat.

Definition history := PM.t stream.

Inductive sem_var (H: history)(x: ident)(n: nat)(v: value): Prop :=
| Sv:
    forall xs,
      PM.find x H = Some xs ->
      xs n = v ->
      sem_var H x n v.

Inductive sem_clock (H: history): clock -> nat -> bool -> Prop :=
| Sbase:
    forall n,
      sem_clock H Cbase n true
| Son_tick:
    forall ck x c n,
      sem_clock H ck n true ->
      sem_var H x n (present (Cbool c)) ->
      sem_clock H (Con ck x c) n true
| Son_abs1:
    forall ck x c n,
      sem_clock H ck n false ->
      sem_clock H (Con ck x c) n false
| Son_abs2:
    forall ck x c c' n,
      sem_clock H ck n true ->
      sem_var H x n (present (Cbool c')) ->
      ~ (c = c') ->
      sem_clock H (Con ck x c) n false.

Inductive sem_laexp (H: history): laexp -> nat -> value -> Prop:=
| SLtick:
    forall ck ce n c,
      sem_lexp H ce n (present c) ->
      sem_clock H ck n true ->
      sem_laexp H (LAexp ck ce) n (present c)
| SLabs:
    forall ck ce n,
      sem_lexp H ce n absent ->
      sem_clock H ck n false ->
      sem_laexp H (LAexp ck ce) n absent
with sem_lexp (H: history): lexp -> nat -> value -> Prop :=
| Sconst:
    forall c n,
      sem_lexp H (Econst c) n (present c)
| Svar:
    forall x v n,
      sem_var H x n v ->
      sem_lexp H (Evar x) n v
| Swhen_eq:
    forall s x b n v,
      sem_var H x n (present (Cbool b)) ->
      sem_laexp H s n v ->
      sem_lexp H (Ewhen s x b) n v
| Swhen_abs:
    forall s x b b' n,
      sem_var H x n (present (Cbool b')) ->
      ~ (b = b') ->
      (* Note: says nothing about 's'. *)
      sem_lexp H (Ewhen s x b) n absent.


Inductive sem_caexp (H: history): caexp -> nat -> value -> Prop :=
| SCtick:
    forall ck ce n c,
      sem_cexp H ce n (present c) ->
      sem_clock H ck n true ->
      sem_caexp H (CAexp ck ce) n (present c)
| SCabs:
    forall ck ce n,
      sem_cexp H ce n absent ->
      sem_clock H ck n false ->
      sem_caexp H (CAexp ck ce) n absent
with sem_cexp (H: history): cexp -> nat -> value -> Prop :=
| Smerge_true:
    forall x t f n v,
      sem_var H x n (present (Cbool true)) ->
      sem_caexp H t n v ->
      sem_cexp H (Emerge x t f) n v
| Smerge_false:
    forall x t f n v,
      sem_var H x n (present (Cbool false)) ->
      sem_caexp H f n v ->
      sem_cexp H (Emerge x t f) n v
| Sexp:
    forall e n v,
      sem_lexp H e n v ->
      sem_cexp H (Eexp e) n v.

Inductive sem_equation (G: global) : history -> equation -> Prop :=
| SEqDef:
    forall H x cae,
      (forall n,
       exists v, sem_var H x n v
              /\ sem_caexp H cae n v) ->
      sem_equation G H (EqDef x cae)
| SEqApp:
    forall H x f arg,
      (forall ls xs,
          (forall n, sem_laexp H arg n (ls n)) ->
          (forall n, sem_var H x n (xs n)) ->
          sem_node G f ls xs) ->
      sem_equation G H (EqApp x f arg)
| SEqFby:
    forall H x ls v0 lae,
      (forall n, sem_laexp H lae n (ls n)) ->
      (forall n v, sem_var H x n v <-> fbyR v0 ls n v) ->
      sem_equation G H (EqFby x v0 lae)

with sem_node (G: global) : ident -> stream -> stream -> Prop :=
| SNode:
    forall f xs ys i o eqs,
      find_node f G = Some (mk_node f i o eqs) ->
      (exists (H: history),
        (forall n, sem_var H i.(v_name) n (xs n))
        /\ (forall n, sem_var H o.(v_name) n (ys n))
        /\ List.Forall (sem_equation G H) eqs) ->
        sem_node G f xs ys.

Definition sem_nodes (G: global) : Prop :=
  List.Forall (fun no => exists xs ys, sem_node G no.(n_name) xs ys) G.

Lemma sem_var_det:
  forall H x n v1 v2,
    sem_var H x n v1
    -> sem_var H x n v2
    -> v1 = v2.
Proof.
  intros H x n v1 v2 H1 H2.
  inversion_clear H1 as [xs1 Hf1];
    inversion_clear H2 as [xs2 Hf2];
    rewrite Hf1 in Hf2; injection Hf2;
    intro Heq; rewrite <- Heq in *;
    rewrite <- H0, <- H1; reflexivity.
Qed.

Lemma sem_var_repr:
  forall H x xs,
    (forall n, sem_var H x n (xs n))
    <->
    (forall n v, sem_var H x n v <-> xs n = v).
Proof.
  intros H x xs.
  split; intro H0.
  - intros n v.
    specialize H0 with n.
    split;
      intro H1;
      [ apply (sem_var_det _ _ _ _ _ H0 H1)
      | rewrite <- H1; exact H0 ].
  - intro n.
    specialize H0 with n (xs n).
    apply H0.
    reflexivity.
Qed.

Lemma sem_var_gso:
  forall x y xs n v H,
    x <> y
    -> (sem_var (PM.add x xs H) y n v <-> sem_var H y n v).
Proof.
  split; inversion_clear 1;
  repeat progress match goal with
                  | H:?xs _ = _ |- _ => apply Sv with xs
                  | H:PM.find _ _ = Some _ |- _ => rewrite <- H
                  | |- context [PM.find _ (PM.add _ _ _)] => rewrite PM.gso
                  end; intuition.
Qed.

Lemma sem_clock_det:
  forall H ck n v1 v2,
    sem_clock H ck n v1
    -> sem_clock H ck n v2
    -> v1 = v2.
Proof.
  induction ck; repeat inversion_clear 1; intuition;
  match goal with
  | H1:sem_clock _ _ _ _, H2:sem_clock _ _ _ _ |- _
    => apply (IHck _ _ _ H1) in H2; discriminate
  | H1:sem_var _ _ _ _, H2: sem_var _ _ _ _ |- _
    => apply (sem_var_det _ _ _ _ _ H1) in H2; now injection H2
  end.
Qed.

Lemma sem_lexp_det:
  forall H n e v1 v2,
    sem_lexp H e n v1
    -> sem_lexp H e n v2
    -> v1 = v2.
Proof.
  intros H n.
  induction e using lexp_mult
  with (P:=fun e=> forall v1 v2, sem_laexp H e n v1
                                 -> sem_laexp H e n v2
                                 -> v1 = v2);
    do 2 inversion_clear 1;
    match goal with
    | H1:sem_clock _ _ _ true, H2:sem_clock _ _ _ false |- _ =>
      pose proof (sem_clock_det _ _ _ _ _ H1 H2); discriminate
    | H1:sem_var _ _ _ _, H2:sem_var _ _ _ _ |- _ =>
      solve [ apply sem_var_det with (1:=H1) (2:=H2)
            | pose proof (sem_var_det _ _ _ _ _ H1 H2) as Hcc;
              injection Hcc; contradiction ]
    | _ => auto
    end.
Qed.

Lemma sem_laexp_det:
  forall v1 v2 H n e,
    sem_laexp H e n v1
    -> sem_laexp H e n v2
    -> v1 = v2.
Proof.
  intros v1 v2 H n e.
  do 2 inversion_clear 1;
  match goal with
  | H1:sem_lexp _ _ _ _, H2:sem_lexp _ _ _ _ |- _ =>
    pose proof (sem_lexp_det _ _ _ _ _ H1 H2) as Heq
  end; auto.
Qed.

Lemma sem_laexp_repr:
  forall H x xs,
    (forall n, sem_laexp H x n (xs n))
    <->
    (forall n v, sem_laexp H x n v <-> xs n = v).
Proof.
  intros H x xs.
  split; intro H0.
  - intros n v.
    specialize H0 with n.
    split;
      intro H1;
      [ apply (sem_laexp_det _ _ _ _ _ H0 H1)
      | rewrite <- H1; exact H0 ].
  - intro n.
    specialize H0 with n (xs n).
    apply H0.
    reflexivity.
Qed.

Lemma find_node_other:
  forall f node G node',
    node.(n_name) <> f
    -> find_node f (node::G) = Some node'
    -> find_node f G = Some node'.
Proof.
  intros f node G node' Hnf Hfind.
  apply BinPos.Pos.eqb_neq in Hnf.
  simpl in Hfind.
  unfold ident_eqb in Hfind.
  rewrite Hnf in Hfind.
  exact Hfind.
Qed.



(* TODO: prove this equation together with the next one using a mutual
         recursion scheme.
         First we need to get this scheme !

         Afterward, apply the same technique for msem_node_cons... *)

Lemma sem_node_cons:
  forall node G f xs ys,
    Ordered_nodes (node::G)
    -> sem_node (node::G) f xs ys
    -> node.(n_name) <> f
    -> sem_node G f xs ys.
Proof.
  intros node G f xs ys Hord Hsem Hnf.
  inversion_clear Hsem as [? ? ? ? ? ? Hfind Hsems].
  apply find_node_other with (1:=Hnf) in Hfind.
  pose proof (find_node_later_not_Is_node_in _ _ _ _ Hord Hfind) as Hnini;
    simpl in Hnini.
  econstructor; [exact Hfind|].
  destruct Hsems as [H [Hxs [Hys Heqs]]].
  exists H.
  split; [exact Hxs|].
  split; [exact Hys|].
  clear Hfind.
  induction eqs as [|eq eqs IH]; [now constructor|].
  apply Forall_cons2 in Heqs.
  destruct Heqs as [Heq Heqs].
  apply not_Is_node_in_cons in Hnini.
  destruct Hnini as [Hneq Hnini].
  constructor; [clear IH|now apply IH with (1:=Heqs) (2:=Hnini)].
  destruct eq; inversion_clear Heq.
  - constructor; trivial.
  - constructor.
    SearchAbout Ordered_nodes.

    intros ls' xs' Hlae Hvar.
    pose proof (H1 _ _ Hlae Hvar).
(*
    Ordered_nodes (node::G)
    -> sem_node (node::G) f xs ys
    -> node.(n_name) <> f
    -> sem_node G f xs ys
*)
    admit.
  - econstructor; eassumption; assumption.
Qed.

Lemma Forall_sem_equation_global_tl:
  forall nd G H eqs,
    Ordered_nodes (nd::G)
    -> ~ Is_node_in nd.(n_name) eqs
    -> List.Forall (sem_equation (nd::G) H) eqs
    -> List.Forall (sem_equation G H) eqs.
Proof.
  intros nd G H eqs Hord.
  induction eqs as [|eq eqs IH]; [trivial|].
  intros Hnini Hsem.
  apply Forall_cons2 in Hsem; destruct Hsem as [Hseq Hseqs].
  apply IH in Hseqs.
  2:(apply not_Is_node_in_cons in Hnini;
     destruct Hnini; assumption).
  apply List.Forall_cons with (2:=Hseqs).
  inversion Hseq as [|H' ? ? ? Hsem HR1 HR2|]; subst.
  - constructor; auto.
  - apply not_Is_node_in_cons in Hnini.
    destruct Hnini as [Hninieq Hnini].
    assert (nd.(n_name) <> f) as Hnf
      by (intro HH; apply Hninieq; rewrite HH; constructor).
    econstructor.
    intros ls xs Hlae Hvar.
    pose proof (Hsem _ _ Hlae Hvar) as Hnode.
    now apply sem_node_cons with (1:=Hord) (2:=Hnode) (3:=Hnf).
  - econstructor; eassumption; assumption.
Qed.


