Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Require Import Coq.FSets.FMapPositive.
Require Import Rustre.Common.
Require Import Rustre.Dataflow.Syntax.
Require Import Rustre.Dataflow.Ordered.
Require Import Rustre.Dataflow.Stream.


Definition option_const_to_value co :=
  match co with
    | None => absent
    | Some v => present v
  end.

(* TODO: put R as a section variable *)


(**

  We provide a "standard" dataflow semantics relating an environment
  of streams to a stream of outputs.

 *)


(** ** Environment and history *)

(**

An history maps variables to streams of values (the variables'
histories). Taking a snapshot of the history at a given time yields an
environment.

 *)

Definition env := PM.t value.
Definition history := PM.t (stream value).

Implicit Type R: env.
Implicit Type H: history.

(** ** Instantaneous semantics *)

Inductive sem_var_instant R (x: ident) v: Prop :=
| Sv:
      PM.find x R = Some v ->
      sem_var_instant R x v.

Inductive sem_clock_instant R: clock -> bool -> Prop :=
| Sbase:
      sem_clock_instant R Cbase true
| Son_tick:
    forall ck x c,
      sem_clock_instant R ck true ->
      sem_var_instant R x (present (Cbool c)) ->
      sem_clock_instant R (Con ck x c) true
| Son_abs1:
    forall ck x c,
      sem_clock_instant R ck false ->
      sem_clock_instant R (Con ck x c) false
| Son_abs2:
    forall ck x c c',
      sem_clock_instant R ck true ->
      sem_var_instant R x (present (Cbool c')) ->
      ~ (c = c') ->
      sem_clock_instant R (Con ck x c)  false.

Inductive sem_lexp_instant R: lexp -> value -> Prop:=
| Sconst:
    forall c,
      sem_lexp_instant R (Econst c) (present c)
| Svar:
    forall x v,
      sem_var_instant R x v ->
      sem_lexp_instant R (Evar x) v
| Swhen_eq:
    forall s x b v,
      sem_var_instant R x (present (Cbool b)) ->
      sem_lexp_instant R s v ->
      sem_lexp_instant R (Ewhen s x b) v
| Swhen_abs1:
    forall s x b b',
      sem_var_instant R x (present (Cbool b')) ->
      ~ (b = b') ->
      (* Note: says nothing about 's'. *)
      sem_lexp_instant R (Ewhen s x b) absent
| Swhen_abs2:
    forall s x b,
      sem_var_instant R x absent ->
      (* Note: says nothing about 's'. *)
      sem_lexp_instant R (Ewhen s x b) absent
| Sop_eq: forall les op cs,
    Nelist.Forall2 (sem_lexp_instant R) les (Nelist.map present cs) ->
    Valid_args (get_arity op) cs ->
    sem_lexp_instant R (Eop op les) (option_const_to_value (apply_op op cs))
| Sop_abs: forall les op,
    Nelist.Forall2 (sem_lexp_instant R) les (alls absent les) ->
    sem_lexp_instant R (Eop op les) absent.

Inductive sem_laexp_instant R: laexp -> value -> Prop:=
| SLtick:
    forall ck ce c,
      sem_lexp_instant R ce (present c) ->
      sem_clock_instant R ck true ->
      sem_laexp_instant R (LAexp ck ce) (present c)
| SLabs:
    forall ck ce,
      sem_lexp_instant R ce absent ->
      sem_clock_instant R ck false ->
      sem_laexp_instant R (LAexp ck ce) absent.

Inductive sem_cexp_instant R: cexp -> value -> Prop :=
| Smerge_true:
    forall x t f v,
      sem_var_instant R x (present (Cbool true)) ->
      sem_cexp_instant R t v ->
      sem_cexp_instant R (Emerge x t f) v
| Smerge_false:
    forall x t f v,
      sem_var_instant R x (present (Cbool false)) ->
      sem_cexp_instant R f v ->
      sem_cexp_instant R (Emerge x t f) v
| Smerge_abs:
    forall x t f,
      sem_var_instant R x absent ->
      sem_cexp_instant R (Emerge x t f) absent
| Sexp:
    forall e v,
      sem_lexp_instant R e v ->
      sem_cexp_instant R (Eexp e) v.

Inductive sem_caexp_instant R: caexp -> value -> Prop :=
| SCtick:
    forall ck ce c,
      sem_cexp_instant R ce (present c) ->
      sem_clock_instant R ck true ->
      sem_caexp_instant R (CAexp ck ce) (present c)
| SCabs:
    forall ck ce,
      sem_cexp_instant R ce absent ->
      sem_clock_instant R ck false ->
      sem_caexp_instant R (CAexp ck ce) absent.

Inductive rhs_absent_instant R: equation -> Prop :=
| AEqDef:
    forall x cae,
      sem_caexp_instant R cae absent ->
      rhs_absent_instant R (EqDef x cae)
| AEqApp:
    forall x f lae,
      sem_laexp_instant R lae absent ->
      rhs_absent_instant R (EqApp x f lae)
| AEqFby:
    forall x v0 lae,
      sem_laexp_instant R lae absent ->
      rhs_absent_instant R (EqFby x v0 lae).

(** ** Liftings of instantaneous semantics *)

Definition restr H (n: nat): env :=
  PM.map (fun xs => xs n) H.
Hint Unfold restr.

Definition lift {A} (sem: env -> A -> Prop) H (xs: stream A): Prop :=
  forall n, sem (restr H n) (xs n).
Hint Unfold lift.

Definition sem_clock H (ck: clock)(xs: stream bool): Prop :=
  lift (fun env b => sem_clock_instant env ck b) H xs.

Definition sem_var H (x: ident)(xs: stream value): Prop :=
  lift (fun env v => sem_var_instant env x v) H xs.
Hint Unfold sem_var.

Definition sem_laexp H (e: laexp)(xs: stream value): Prop :=
  lift (fun env v => sem_laexp_instant env e v) H xs.

Definition sem_lexp H (e: lexp)(xs: stream value): Prop :=
  lift (fun env v => sem_lexp_instant env e v) H xs.

Definition sem_caexp H (c: caexp)(xs: stream value): Prop :=
  lift (fun env v => sem_caexp_instant env c v) H xs.

Definition sem_cexp H (c: cexp)(xs: stream value): Prop :=
  lift (fun env v => sem_cexp_instant env c v) H xs.

(** ** Time-dependent semantics *)

Inductive sem_equation G: history -> equation -> Prop :=
| SEqDef:
    forall H x xs cae,
      sem_var H x xs ->
      sem_caexp H cae xs ->
      sem_equation G H (EqDef x cae)
| SEqApp:
    forall H x f arg ls xs,
      sem_laexp H arg ls ->
      sem_var H x xs ->
      sem_node G f ls xs ->
      sem_equation G H (EqApp x f arg)
| SEqFby:
    forall H x ls xs v0 lae,
      sem_laexp H lae ls ->
      sem_var H x xs ->
      xs = fby v0 ls ->
      sem_equation G H (EqFby x v0 lae)

with sem_node G: ident -> stream value -> stream value -> Prop :=
| SNode:
    forall f (xs ys: stream value) i o eqs,
      find_node f G = Some (mk_node f i o eqs) ->
      (exists H,
           sem_var H i xs
        /\ sem_var H o ys
        (* no clocks faster than input *)
        /\ (forall n, xs n = absent ->
                      Forall (rhs_absent_instant (restr H n)) eqs)
        (* output clock matches input clock *)
        /\ (forall n, xs n = absent <-> ys n = absent)
        /\ Forall (sem_equation G H) eqs) ->
      sem_node G f xs ys.

Definition sem_nodes (G: global) : Prop :=
  Forall (fun no => exists xs ys, sem_node G no.(n_name) xs ys) G.


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




(** ** Induction principle for [sem_node] and [sem_equation] *)

Section sem_node_mult.
  Variable G: global.

  Variable P : forall H (eq: equation), sem_equation G H eq -> Prop.
  Variable Pn : forall (f: ident) (xs ys: stream value), sem_node G f xs ys -> Prop.

  Hypothesis EqDef_case :
    forall (H    : history)
	   (x    : ident)
           (xs   : stream value)
	   (cae  : caexp)
	   (Hvar : sem_var H x xs)
           (Hexp : sem_caexp H cae xs),
      P H (EqDef x cae) (SEqDef G H x xs cae Hvar Hexp).

  Hypothesis EqApp_case :
    forall (H     : history)
	   (y     : ident)
	   (f     : ident)
	   (lae   : laexp)
           (ls    : stream value)
           (ys    : stream value)
	   (Hlae  : sem_laexp H lae ls)
           (Hvar  : sem_var H y ys)
	   (Hnode : sem_node G f ls ys),
      Pn f ls ys Hnode ->
      P H (EqApp y f lae) (SEqApp G H y f lae ls ys Hlae Hvar Hnode).

  Hypothesis EqFby_case :
    forall (H   : history)
	   (y   : ident)
	   (ls  : stream value)
	   (yS  : stream value)
	   (v0  : const)
	   (lae : laexp)
	   (Hls : sem_laexp H lae ls)
	   (Hys : sem_var H y yS)
           (Hfby: yS = fby v0 ls),
      P H (EqFby y v0 lae) (SEqFby G H y ls yS v0 lae Hls Hys Hfby).

  Hypothesis SNode_case :
    forall (f   : ident)
	   (xs  : stream value)
	   (ys  : stream value)
	   (i   : ident)
	   (o   : ident)
	   (eqs : list equation)
	   (Hf  : find_node f G = Some (mk_node f i o eqs))
           (Heqs : exists H,
                        sem_var H i xs
	             /\ sem_var H o ys
                     /\ (forall n, xs n = absent
                                   -> Forall (rhs_absent_instant (restr H n)) eqs)
                     /\ (forall n, xs n = absent <-> ys n = absent)
	             /\ Forall (sem_equation G H) eqs),
      (exists H,
             sem_var H i xs
          /\ sem_var H o ys
          /\ (forall n, xs n = absent
                        -> Forall (rhs_absent_instant (restr H n)) eqs)
          /\ (forall n, xs n = absent <-> ys n = absent)
          /\ Forall (fun eq=>exists Hsem, P H eq Hsem) eqs)
      -> Pn f xs ys (SNode G f xs ys i o eqs Hf Heqs).

  Fixpoint sem_equation_mult (H  : history)
			     (eq : equation)
			     (Heq : sem_equation G H eq) {struct Heq}
                                                                : P H eq Heq :=
    match Heq in (sem_equation _ H eq) return (P H eq Heq) with
    | SEqDef H y cae xs Hvar Hexp => EqDef_case H y cae xs Hvar Hexp
    | SEqApp H y f lae ls ys Hlae Hvar Hnode =>
      EqApp_case H y f lae ls ys Hlae Hvar Hnode
                 (sem_node_mult f ls ys Hnode)
    | SEqFby H y ls yS v0 lae Hls Hys Hfby => EqFby_case H y ls yS v0 lae Hls Hys Hfby
    end

  with sem_node_mult (f  : ident)
		     (ls : stream value)
		     (ys : stream value)
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

(** ** Determinism of semantics *)

Lemma sem_var_instant_det:
  forall x R v1 v2,
    sem_var_instant R x v1
    -> sem_var_instant R x v2
    -> v1 = v2.
Proof.
  intros R x v1 v2 H1 H2.
  inversion_clear H1 as [Hf1];
    inversion_clear H2 as [Hf2];
    congruence.
Qed.

Lemma sem_clock_instant_det:
  forall ck R v1 v2,
    sem_clock_instant R ck v1
    -> sem_clock_instant R ck v2
    -> v1 = v2.
Proof.
  induction ck; repeat inversion_clear 1; intuition;
  try match goal with
        | H1: sem_clock_instant ?R ?ck ?l,
          H2: sem_clock_instant ?R ?ck ?r |- ?l = ?r =>
          eapply IHck; eassumption
        | H1: sem_var_instant ?R ?i (present (Cbool ?l)),
          H2: sem_var_instant ?R ?i (present (Cbool ?r)),
          H3: ?l = ?r -> False |- _ = _ =>
          exfalso; apply H3;
          cut (present (Cbool l) = present (Cbool r)); [injection 1; auto|];
          eapply sem_var_instant_det; eassumption
      end.
Qed.


Lemma sem_lexp_instant_det:
  forall e R v1 v2,
    sem_lexp_instant R e v1
    -> sem_lexp_instant R e v2
    -> v1 = v2.
Proof.
  intros e R.
  induction e using lexp_ind2;
    try now do 2 inversion_clear 1;
    match goal with
    | H1:sem_var_instant ?R ?e (present (Cbool ?b1)),
      H2:sem_var_instant ?R ?e (present (Cbool ?b2)),
      H3: ?b1 <> ?b2 |- _ =>
      exfalso; apply H3;
      cut (present (Cbool b1) = present (Cbool b2)); [injection 1; auto|];
      eapply sem_var_instant_det; eassumption
    | H1:sem_var_instant ?R ?e ?v1,
      H2:sem_var_instant ?R ?e ?v2 |- ?v1 = ?v2 =>
      eapply sem_var_instant_det; eassumption
    | H1:sem_var_instant ?R ?e (present _),
      H2:sem_var_instant ?R ?e absent |- _ =>
      apply (sem_var_instant_det _ _ _ _ H1) in H2;
      discriminate
    | _ => auto
    end.
intros v1 v2 Hsem1 Hsem2.
inversion_clear Hsem1; inversion_clear Hsem2.
* do 2 f_equal. clear H1 H3. revert cs cs0 H0 H2.
  induction les as [| le les]; intros cs1 cs2 Hrec1 Hrec2.
  + inversion Hrec1. inversion Hrec2. subst. symmetry in H1, H4.
    apply Nelist.map_eq_nebase in H1. destruct H1 as [? [? ?]].
    apply Nelist.map_eq_nebase in H4. destruct H4 as [? [? ?]]. subst.
    f_equal. rewrite present_injection. inversion_clear H. now apply H0.
  + inversion Hrec1; subst. inversion Hrec2; subst.
    symmetry in H2, H5.
    apply Nelist.map_eq_necons in H2. destruct H2 as [x1 [cs1' [Hcs1 [Hx1 Hmap1]]]].
    apply Nelist.map_eq_necons in H5. destruct H5 as [x2 [cs2' [Hcs2 [Hx2 Hmap2]]]]. subst.
    assert (Hx : x1 = x2).
    { inversion_clear H. rewrite present_injection. now apply H0. }
    inversion_clear H. inversion_clear Hrec1; inversion_clear Hrec2.
    f_equal; trivial. now apply (IHles H1).
* exfalso. destruct les as [le | le les].
  + inversion H0. inversion H2. subst. symmetry in H4.
    apply Nelist.map_eq_nebase in H4. destruct H4 as [? [? ?]]. subst. simpl in *.
    inversion_clear H. specialize (H3 _ _ H8 H5). discriminate.
  + inversion H0; subst. inversion H2; subst.
    inversion_clear H. specialize (H3 _ _ H6 H9).
    symmetry in H5. apply Nelist.map_eq_necons in H5. decompose [ex and] H5. subst. discriminate.
* exfalso. destruct les as [| le les].
  + inversion H0. inversion H1. subst. symmetry in H7.
    apply Nelist.map_eq_nebase in H7. destruct H7 as [? [? ?]]. subst. simpl in *.
    inversion_clear H. specialize (H3 _ _ H8 H5). discriminate.
  + inversion H0; subst. inversion H1; subst.
    inversion_clear H. specialize (H3 _ _ H6 H7).
    symmetry in H5. apply Nelist.map_eq_necons in H5. decompose [ex and] H5. subst. discriminate.
* reflexivity.
Qed.

Lemma sem_laexp_instant_det:
  forall e R v1 v2,
    sem_laexp_instant R e v1
    -> sem_laexp_instant R e v2
    -> v1 = v2.
Proof.
  intros e v1 v2 R.
  do 2 inversion_clear 1;
  match goal with
  | H1:sem_lexp_instant _ _ _, H2:sem_lexp_instant _ _ _ |- _ =>
    eapply sem_lexp_instant_det; eassumption
  end; auto.
Qed.


Lemma sem_cexp_instant_det:
  forall e R v1 v2,
    sem_cexp_instant R e v1
    -> sem_cexp_instant R e v2
    -> v1 = v2.
Proof.
  intros e R.
  induction e;
  do 2 inversion_clear 1;
    try match goal with
      | H1: sem_cexp_instant ?R ?e ?l,
        H2: sem_cexp_instant ?R ?e ?r
        |- ?l = ?r =>
        (eapply IHe1; eassumption)
     || (eapply IHe2; eassumption)
      | H1: sem_var_instant ?R ?i (present (Cbool true)),
        H2: sem_var_instant ?R ?i (present (Cbool false)) |- _ =>
        exfalso;
          assert (present (Cbool true) = present (Cbool false))
          by (eapply sem_var_instant_det; eassumption);
          discriminate
      | H1: sem_lexp_instant ?R ?l ?v1,
        H2: sem_lexp_instant ?R ?l ?v2 |- ?v1 = ?v2 =>
        eapply sem_lexp_instant_det; eassumption
      | H1: sem_var_instant ?R ?i (present _),
        H2: sem_var_instant ?R ?i absent |- _ =>
        apply sem_var_instant_det with (1:=H1) in H2; discriminate
      | |- absent = absent => reflexivity
    end.
Qed.

Lemma sem_caexp_instant_det:
  forall e R v1 v2,
    sem_caexp_instant R e v1
    -> sem_caexp_instant R e v2
    -> v1 = v2.
Proof.
  intros e R v1 v2.
  do 2 inversion_clear 1;
  match goal with
  | H1: sem_cexp_instant _ _ _,
    H2: sem_cexp_instant _ _ _ |- _ =>
    eapply sem_cexp_instant_det; eassumption
  end.
Qed.


Require Import Logic.FunctionalExtensionality.

Lemma lift_det:
  forall {A}(P: env -> A -> Prop) H (xs1 xs2: stream A),
    (forall R v1 v2, P R v1 -> P R v2 -> v1 = v2) ->
    lift P H xs1 -> lift P H xs2 -> xs1 = xs2.
Proof.
  intros ** Hpoint H1 H2.
  extensionality n. specialize (H1 n). specialize (H2 n).
  eapply Hpoint; eassumption.
Qed.

Ltac apply_lift sem_det x :=
  intros; eapply lift_det; try eassumption;
  apply (sem_det x).

Lemma sem_var_det:
  forall H x xs1 xs2,
    sem_var H x xs1 -> sem_var H x xs2 -> xs1 = xs2.
Proof.
  apply_lift sem_var_instant_det x.
Qed.

Lemma sem_clock_det:
  forall H ck bs1 bs2,
    sem_clock H ck bs1 -> sem_clock H ck bs2 -> bs1 = bs2.
Proof.
  apply_lift sem_clock_instant_det ck.
Qed.

Lemma sem_lexp_det:
  forall H e xs1 xs2,
    sem_lexp H e xs1 -> sem_lexp H e xs2 -> xs1 = xs2.
Proof.
  apply_lift sem_lexp_instant_det e.
Qed.

Lemma sem_laexp_det:
  forall H e xs1 xs2,
    sem_laexp H e xs1 -> sem_laexp H e xs2 -> xs1 = xs2.
Proof.
  apply_lift sem_laexp_instant_det e.
Qed.

Lemma sem_cexp_det:
  forall H c xs1 xs2,
    sem_cexp H c xs1 -> sem_cexp H c xs2 -> xs1 = xs2.
Proof.
  apply_lift sem_cexp_instant_det c.
Qed.

Lemma sem_caexp_det:
  forall H c xs1 xs2,
    sem_caexp H c xs1 -> sem_caexp H c xs2 -> xs1 = xs2.
Proof.
  apply_lift sem_caexp_instant_det c.
Qed.

(** ** Global management *)

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
  - econstructor; eassumption.
  - intro Hnin.
    apply SEqApp with (1:=Hlae) (2:=Hvar).
    apply IH. intro Hnf. apply Hnin. rewrite Hnf. constructor.
  - intro; eapply SEqFby; eassumption.
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
  - econstructor; eassumption.
  - apply not_Is_node_in_cons in Hnini.
    destruct Hnini as [Hninieq Hnini].
    assert (nd.(n_name) <> f) as Hnf
      by (intro HH; apply Hninieq; rewrite HH; constructor).
    econstructor. exact Hsem. exact Hvar.
    now apply sem_node_cons with (1:=Hord) (2:=Hnode) (3:=Hnf).
  - econstructor; eauto.
Qed.
