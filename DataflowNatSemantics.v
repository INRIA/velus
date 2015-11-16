
Require Import List.
Import List.ListNotations.
Open Scope list_scope.

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

Inductive sem_lexp (H: history): lexp -> nat -> value -> Prop :=
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
      sem_lexp H s n v ->
      sem_lexp H (Ewhen s x b) n v
| Swhen_abs:
    forall s x b b' n,
      sem_var H x n (present (Cbool b')) ->
      ~ (b = b') ->
      (* Note: says nothing about 's'. *)
      sem_lexp H (Ewhen s x b) n absent.

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
      sem_laexp H (LAexp ck ce) n absent.

Inductive sem_cexp (H: history): cexp -> nat -> value -> Prop :=
| Smerge_true:
    forall x t f n v,
      sem_var H x n (present (Cbool true)) ->
      sem_cexp H t n v ->
      sem_cexp H (Emerge x t f) n v
| Smerge_false:
    forall x t f n v,
      sem_var H x n (present (Cbool false)) ->
      sem_cexp H f n v ->
      sem_cexp H (Emerge x t f) n v
| Sexp:
    forall e n v,
      sem_lexp H e n v ->
      sem_cexp H (Eexp e) n v.

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
      sem_caexp H (CAexp ck ce) n absent.

Inductive rhs_absent (H: history) (n: nat) : equation -> Prop :=
| AEqDef:
    forall x cae,
      sem_caexp H cae n absent ->
      rhs_absent H n (EqDef x cae)
| AEqApp:
    forall x f lae,
      sem_laexp H lae n absent ->
      rhs_absent H n (EqApp x f lae)
| AEqFby:
    forall x v0 lae,
      sem_laexp H lae n absent ->
      rhs_absent H n (EqFby x v0 lae).

Inductive sem_equation (G: global) : history -> equation -> Prop :=
| SEqDef:
    forall H x cae,
      (forall n,
       exists v, sem_var H x n v
              /\ sem_caexp H cae n v) ->
      sem_equation G H (EqDef x cae)
| SEqApp:
    forall H x f arg ls xs,
      (forall n, sem_laexp H arg n (ls n)) ->
      (forall n, sem_var H x n (xs n)) ->
      sem_node G f ls xs ->
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
        (* no clocks faster than input *)
        /\ (forall n, xs n = absent ->
                      Forall (rhs_absent H n) eqs)
        (* output clock matches input clock *)
        /\ (forall n, xs n = absent <-> ys n = absent)
        /\ Forall (sem_equation G H) eqs) ->
      sem_node G f xs ys.

Section sem_node_mult.
  Variable G: global.

  Variable P : forall (H: history) (eq: equation), sem_equation G H eq -> Prop.
  Variable Pn : forall (f: ident) (xs ys: stream), sem_node G f xs ys -> Prop.

  Hypothesis EqDef_case :
    forall (H    : history)
	   (x    : ident)
	   (cae  : caexp)
	   (Hvar : forall n, exists v,
                     sem_var H x n v /\ sem_caexp H cae n v),
      P H (EqDef x cae) (SEqDef G H x cae Hvar).

  Hypothesis EqApp_case :
    forall (H     : history)
	   (y     : ident)
	   (f     : ident)
	   (lae   : laexp)
           (ls    : stream)
           (ys    : stream)
	   (Hlae  : forall n, sem_laexp H lae n (ls n))
           (Hvar  : forall n, sem_var H y n (ys n))
	   (Hnode : sem_node G f ls ys),
      Pn f ls ys Hnode ->
      P H (EqApp y f lae) (SEqApp G H y f lae ls ys Hlae Hvar Hnode).

  Hypothesis EqFby_case :
    forall (H   : history)
	   (y   : ident)
	   (ls  : stream)
	   (v0  : const)
	   (lae : laexp)
	   (Hls : forall n, sem_laexp H lae n (ls n))
	   (Hys : forall n v, sem_var H y n v <-> fbyR v0 ls n v),
      P H (EqFby y v0 lae) (SEqFby G H y ls v0 lae Hls Hys).

  Hypothesis SNode_case :
    forall (f   : ident)
	   (xs  : stream)
	   (ys  : stream)
	   (i   : var_dec)
	   (o   : var_dec)
	   (eqs : list equation)
	   (Hf  : find_node f G = Some (mk_node f i o eqs))
           (Heqs : exists H : history,
                        (forall n, sem_var H (v_name i) n (xs n))
	             /\ (forall n, sem_var H (v_name o) n (ys n))
                     /\ (forall n, xs n = absent
                                   -> Forall (rhs_absent H n) eqs)
                     /\ (forall n, xs n = absent <-> ys n = absent)
	             /\ Forall (sem_equation G H) eqs),
      (exists H : history,
          (forall n, sem_var H (v_name i) n (xs n))
          /\ (forall n, sem_var H (v_name o) n (ys n))
          /\ (forall n, xs n = absent
                        -> Forall (rhs_absent H n) eqs)
          /\ (forall n, xs n = absent <-> ys n = absent)
          /\ Forall (fun eq=>exists Hsem, P H eq Hsem) eqs)
      -> Pn f xs ys (SNode G f xs ys i o eqs Hf Heqs).

  Fixpoint sem_equation_mult (H  : history)
			     (eq : equation)
			     (Heq : sem_equation G H eq) {struct Heq}
                                                                : P H eq Heq :=
    match Heq in (sem_equation _ H eq) return (P H eq Heq) with
    | SEqDef H y cae Hvar => EqDef_case H y cae Hvar
    | SEqApp H y f lae ls ys Hlae Hvar Hnode =>
      EqApp_case H y f lae ls ys Hlae Hvar Hnode
                 (sem_node_mult f ls ys Hnode)
    | SEqFby H y ls v0 lae Hls Hys => EqFby_case H y ls v0 lae Hls Hys
    end

  with sem_node_mult (f  : ident)
		     (ls : stream)
		     (ys : stream)
		     (Hn : sem_node G f ls ys) {struct Hn} : Pn f ls ys Hn :=
    match Hn in (sem_node _ f ls ys) return (Pn f ls ys Hn) with
    | SNode f ls ys i o eqs Hf Hnode =>
        SNode_case f ls ys i o eqs Hf Hnode
          (* Turn: exists H : history,
                        (forall n, sem_var H (v_name i) n (xs n))
	             /\ (forall n, sem_var H (v_name o) n (ys n))
                     /\ (forall n, xs n = absent
                                   -> Forall (rhs_absent H n) eqs)
                     /\ (forall n, xs n = absent <-> ys n = absent)
	             /\ Forall (sem_equation G H) eqs
             into: exists H : history,
                        (forall n, sem_var H (v_name i) n (xs n))
                     /\ (forall n, sem_var H (v_name o) n (ys n))
                     /\ (forall n, xs n = absent
                                   -> Forall (rhs_absent H n) eqs)
                     /\ (forall n, xs n = absent <-> ys n = absent)
                     /\ Forall (fun eq=>exists Hsem, P H eq Hsem) eqs *)
           (match Hnode with
            | ex_intro H (conj Hxs (conj Hys (conj Habs (conj Hout Heqs)))) =>
                ex_intro _ H (conj Hxs (conj Hys (conj Habs (conj Hout
                  (((fix map (eqs : list equation)
                             (Heqs: Forall (sem_equation G H) eqs) :=
                       match Heqs in Forall _ fs
                             return (Forall (fun eq=> exists Hsem,
                                                        P H eq Hsem) fs)
                       with
                       | Forall_nil => Forall_nil _
                       | Forall_cons eq eqs Heq Heqs' =>
                         Forall_cons eq (@ex_intro _ _ Heq
                                           (sem_equation_mult H eq Heq))
                                     (map eqs Heqs')
                       end) eqs Heqs))))))
            end)
    end.

End sem_node_mult.

(* The original idea was to 'bake' the following assumption into sem_node:

       (forall n y, xs n = absent
                    -> Is_defined_in y eqs
                    -> sem_var H y n absent)

   That is, when the node input is absent then so are all of the
   variables defined within the node. This is enough to show
   Memory_Corres_unchanged for EqFby, but not for EqApp. Consider
   the counter-example:

       node f (x) = y where
         y = 1 when false
         s = 0 fby x

       node g (x) = y where
         y = f (3 when Cbase)

   Now can instantiate g on a slower value (1 :: Con Cbase x true), and the
   internal value y satisfies the assumption (it is always absent), but the
   instantiation of f is still called at a faster rate.

   The current (proposed) solution is to insist that all of the rhs' be
   absent when the input is. This should be enough to ensure the two
   key properties:
   1. for (x = f e), e absent implies x absent (important for translation
                     correctness),
   2. for (x = f e) and (x = v0 fby e), e absent implies that the memories
                     'stutter'.
   This constraint _should_ follow readily from the clock calculus. Note that
   we prefer a semantic condition here even if it will be shown via a static
   analysis witnessed by clocks in expressions.

   This extra condition
   is only necessary for the correctness proof of imperative code generation.
   A translated node is only executed when the clock of its input expression
   is true. For this 'optimization' to be correct, whenever the input is
   absent, the output must be absent and the internal memories must not change.
   These facts are consequences of the clock constraint above (see the
   absent_invariant lemma below).
 *)

Definition sem_nodes (G: global) : Prop :=
  Forall (fun no => exists xs ys, sem_node G no.(n_name) xs ys) G.

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
  induction e;
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

Lemma sem_cexp_det:
  forall H n e v1 v2,
    sem_cexp H e n v1
    -> sem_cexp H e n v2
    -> v1 = v2.
Proof.
  intros H n.
  induction e;
    do 2 inversion_clear 1;
    match goal with
    | H1:sem_clock _ _ _ true, H2:sem_clock _ _ _ false |- _ =>
      pose proof (sem_clock_det _ _ _ _ _ H1 H2); discriminate
    | H1:sem_var _ _ _ _, H2:sem_var _ _ _ _ |- _ =>
      solve [ apply sem_var_det with (1:=H1) (2:=H2)
            | pose proof (sem_var_det _ _ _ _ _ H1 H2) as Hcc;
              injection Hcc; contradiction ]
    | H1:sem_var _ _ _ (present (Cbool true)),
      H2:sem_var _ _ _ (present (Cbool false)) |- _ =>
      solve [apply sem_var_det with (1:=H1) in H2; discriminate]
    | H1: sem_lexp ?H ?x ?n ?v1,
      H2: sem_lexp ?H ?x ?n ?v2 |- ?v1 = ?v2 =>
      now apply sem_lexp_det with (1:=H1) (2:=H2)
    | _ => auto
    end.
Qed.

Lemma sem_caexp_det:
  forall v1 v2 H n e,
    sem_caexp H e n v1
    -> sem_caexp H e n v2
    -> v1 = v2.
Proof.
  intros v1 v2 H n e.
  do 2 inversion_clear 1;
  match goal with
  | H1:sem_cexp _ _ _ _, H2:sem_cexp _ _ _ _ |- _ =>
    pose proof (sem_cexp_det _ _ _ _ _ H1 H2) as Heq
  end; auto.
Qed.

Lemma find_node_other:
  forall f node G node',
    node.(n_name) <> f
    -> (find_node f (node::G) = Some node'
        <-> find_node f G = Some node').
Proof.
  intros f node G node' Hnf.
  apply BinPos.Pos.eqb_neq in Hnf.
  simpl.
  unfold ident_eqb.
  rewrite Hnf.
  reflexivity.
Qed.

Lemma sem_node_cons:
  forall node G f xs ys,
    Ordered_nodes (node::G)
    -> sem_node (node::G) f xs ys
    -> node.(n_name) <> f
    -> sem_node G f xs ys.
Proof.
  intros node G f xs ys Hord Hsem Hnf.
  revert Hnf.
  induction Hsem as [|H y f lae ls ys Hlae Hvar Hnode IH| |
                      f xs ys i o eqs Hf Heqs IH]
  using sem_node_mult
  with (P := fun H eq Hsem => ~Is_node_in_eq node.(n_name) eq
                              -> sem_equation G H eq).
  - constructor; intuition.
  - intro Hnin.
    apply SEqApp with (1:=Hlae) (2:=Hvar).
    apply IH. intro Hnf. apply Hnin. rewrite Hnf. constructor.
  - intro; apply SEqFby with (1:=Hls) (2:=Hys).
  - intro.
    rewrite find_node_tl with (1:=Hnf) in Hf.
    apply SNode with (1:=Hf).
    clear Heqs.
    destruct IH as [H [Hxs [Hys [Habs [Hout Heqs]]]]].
    exists H.
    intuition.
    apply find_node_later_not_Is_node_in with (2:=Hf) in Hord.
    apply Is_node_in_Forall in Hord.
    apply Forall_Forall with (1:=Hord) in Heqs.
    apply Forall_impl with (2:=Heqs).
    destruct 1 as [Hnini [Hsem HH]].
    intuition.
Qed.

Lemma find_node_find_again:
  forall G f i o eqs g,
    Ordered_nodes G
    -> find_node f G =
       Some {| n_name := f; n_input := i; n_output := o; n_eqs := eqs |}
    -> Is_node_in g eqs
    -> Exists (fun nd=> g = nd.(n_name)) G.
Proof.
  intros G f i o eqs g Hord Hfind Hini.
  apply find_node_split in Hfind.
  destruct Hfind as [bG [aG Hfind]].
  rewrite Hfind in *.
  clear Hfind.
  apply Ordered_nodes_append in Hord.
  apply Exists_app.
  constructor 2.
  inversion_clear Hord as [|? ? ? HH H0]; clear H0.
  apply HH in Hini; clear HH.
  intuition.
Qed.

Lemma sem_node_cons2:
  forall nd G f xs ys,
    Ordered_nodes G
    -> sem_node G f xs ys
    -> Forall (fun nd' : node => n_name nd <> n_name nd') G
    -> sem_node (nd::G) f xs ys.
Proof.
  Hint Constructors sem_equation.
  intros nd G f xs ys Hord Hsem Hnin.
  assert (Hnin':=Hnin).
  revert Hnin'.
  induction Hsem as [|H y f lae ls ys Hlae Hvar Hnode IH| |
                      f xs ys i o eqs Hfind Heqs IH]
  using sem_node_mult
  with (P := fun H eq Hsem => ~Is_node_in_eq nd.(n_name) eq
                              -> sem_equation (nd::G) H eq);
    try eauto; intro HH.
  clear HH.
  assert (nd.(n_name) <> f) as Hnf.
  { intro Hnf.
    rewrite Hnf in *.
    apply find_node_split in Hfind.
    destruct Hfind as [bG [aG Hge]].
    rewrite Hge in Hnin.
    apply Forall_app in Hnin.
    destruct Hnin as [H0 Hfg]; clear H0.
    inversion_clear Hfg.
    match goal with H:f<>_ |- False => apply H end.
    reflexivity. }
  apply find_node_other with (2:=Hfind) in Hnf.
  econstructor; [exact Hnf|clear Hnf].
  clear Heqs.
  destruct IH as [H [Hxs [Hys [Habs [Hout Heqs]]]]].
  exists H.
  intuition; clear Hxs Hys Habs.
  assert (forall g, Is_node_in g eqs
                    -> Exists (fun nd=> g = nd.(n_name)) G)
    as Hniex
    by (intros g Hini;
        apply find_node_find_again with (1:=Hord) (2:=Hfind) in Hini;
        exact Hini).
  assert (Forall
            (fun eq=> forall g,
                 Is_node_in_eq g eq
                 -> Exists (fun nd=> g = nd.(n_name)) G) eqs) as HH.
  {
    clear Hfind Heqs.
    induction eqs as [|eq eqs IH]; [now constructor|].
    constructor.
    - intros g Hini.
      apply Hniex.
      constructor 1; apply Hini.
    - apply IH.
      intros g Hini; apply Hniex.
      constructor 2; apply Hini.
  }
  apply Forall_Forall with (1:=HH) in Heqs.
  apply Forall_impl with (2:=Heqs).
  intros eq IH.
  destruct IH as [Hsem [IH0 IH1]].
  apply IH1.
  intro Hini.
  apply Hsem in Hini.
  apply Forall_Exists with (1:=Hnin) in Hini.
  apply Exists_exists in Hini.
  destruct Hini as [nd' [Hin [Hneq Heq]]].
  intuition.
Qed.

Lemma Forall_sem_equation_global_tl:
  forall nd G H eqs,
    Ordered_nodes (nd::G)
    -> ~ Is_node_in nd.(n_name) eqs
    -> Forall (sem_equation (nd::G) H) eqs
    -> Forall (sem_equation G H) eqs.
Proof.
  intros nd G H eqs Hord.
  induction eqs as [|eq eqs IH]; [trivial|].
  intros Hnini Hsem.
  apply Forall_cons2 in Hsem; destruct Hsem as [Hseq Hseqs].
  apply IH in Hseqs.
  2:(apply not_Is_node_in_cons in Hnini;
     destruct Hnini; assumption).
  apply Forall_cons with (2:=Hseqs).
  inversion Hseq as [|? ? ? ? ? ? Hsem Hvar Hnode|]; subst.
  - constructor; auto.
  - apply not_Is_node_in_cons in Hnini.
    destruct Hnini as [Hninieq Hnini].
    assert (nd.(n_name) <> f) as Hnf
      by (intro HH; apply Hninieq; rewrite HH; constructor).
    econstructor. exact Hsem. exact Hvar.
    now apply sem_node_cons with (1:=Hord) (2:=Hnode) (3:=Hnf).
  - econstructor; eassumption; assumption.
Qed.

