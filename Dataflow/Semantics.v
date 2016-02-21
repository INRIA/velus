Require Import Rustre.Nelist.
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

  We provide a "standard" dataflow semantics relating an Rironment
  of streams to a stream of outputs.

 *)


(** ** Rironment and history *)

(**

An history maps variables to streams of values (the variables'
histories). Taking a snapshot of the history at a given time yields an
Rironment.

 *)

Definition R := PM.t value.
Definition history := PM.t (stream value).

Implicit Type R: R.
Implicit Type H: history.

(** ** Instantaneous semantics *)

Section InstantSemantics.

Variable base : bool.

Inductive sem_var_instant R (x: ident) v: Prop :=
| Sv:
      PM.find x R = Some v ->
      sem_var_instant R x v.


Inductive sem_clock_instant R: clock -> bool -> Prop :=
| Sbase:
      sem_clock_instant R Cbase base
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
    forall c v,
      v = (if base then present c else absent) ->
      sem_lexp_instant R (Econst c) v
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

Definition sem_lexps_instant R (les: nelist lexp)(vs: nelist value) :=
  Nelist.Forall2 (sem_lexp_instant R) les vs.

Inductive sem_laexp_instant R: clock -> lexp -> value -> Prop:=
| SLtick:
    forall ck ce c,
      sem_lexp_instant R ce (present c) ->
      sem_clock_instant R ck true ->
      sem_laexp_instant R ck ce (present c)
| SLabs:
    forall ck ce,
      sem_lexp_instant R ce absent ->
      sem_clock_instant R ck false ->
      sem_laexp_instant R ck ce absent.

Inductive sem_laexps_instant R: clock -> lexps -> nelist value -> Prop:=
| SLticks:
    forall ck ces cs vs,
      vs = Nelist.map present cs ->
      Nelist.Forall2 (fun ce v => sem_lexp_instant R ce v) ces vs ->
      sem_clock_instant R ck true ->
      sem_laexps_instant R ck ces vs
| SLabss:
    forall ck ces vs,
      vs = Nelist.map (fun _ => absent) ces ->
      Nelist.Forall2 (fun ce v => sem_lexp_instant R ce v) ces vs ->
      sem_clock_instant R ck false ->
      sem_laexps_instant R ck ces vs.

(*
Definition sem_laexps_instant R (ck: clock)(e: lexps)(xs: nelist value): Prop :=
  Nelist.Forall2 
    (fun e xs => sem_laexp_instant R ck e xs)
    e xs.
*)

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

Inductive sem_caexp_instant R: clock -> cexp -> value -> Prop :=
| SCtick:
    forall ck ce c,
      sem_cexp_instant R ce (present c) ->
      sem_clock_instant R ck true ->
      sem_caexp_instant R ck ce (present c)
| SCabs:
    forall ck ce,
      sem_cexp_instant R ce absent ->
      sem_clock_instant R ck false ->
      sem_caexp_instant R ck ce absent.

Inductive rhs_absent_instant R: equation -> Prop :=
| AEqDef:
    forall x ck cae,
      sem_caexp_instant R ck cae absent ->
      rhs_absent_instant R (EqDef x ck cae)
| AEqApp:
    forall x f ck laes vs,
      sem_laexps_instant R ck laes vs ->
      Nelist.Forall (fun c => c = absent) vs ->
      rhs_absent_instant R (EqApp x ck f laes)
| AEqFby:
    forall x ck v0 lae,
      sem_laexp_instant R ck lae absent ->
      rhs_absent_instant R (EqFby x ck v0 lae).

End InstantSemantics.

(** ** Liftings of instantaneous semantics *)

Section LiftSemantics.

Variable bk : stream bool.

Definition restr H (n: nat): R :=
  PM.map (fun xs => xs n) H.
Hint Unfold restr.

Definition lift1 {A B} (f : A -> B) (s : stream A) : stream B := fun n => f (s n).
Hint Unfold lift1.

Definition lift {A B} (sem: bool -> R -> A -> B -> Prop) H x (ys: stream B): Prop :=
  forall n, sem (bk n) (restr H n) x (ys n).
Hint Unfold lift.

(*
Lemma Forall2_lift_restr : forall {A B} sem H (args : nelist A) (xss : nelist (stream B)),
  Nelist.Forall2 (fun x => lift sem H x) args xss ->
  forall n, Nelist.Forall2 (sem (restr H n)) args (Nelist.map (fun f => f n) xss).
Proof. intros * Hall n. induction Hall; simpl; constructor; auto. Qed.
*)

Definition sem_clock H (ck: clock)(xs: stream bool): Prop :=
  lift sem_clock_instant H ck xs.

Definition sem_var H (x: ident)(xs: stream value): Prop :=
  lift (fun base => sem_var_instant) H x xs.

Definition sem_vars H (x: nelist ident)(xs: stream (nelist value)): Prop :=
  lift (fun base R => Nelist.Forall2 (sem_var_instant R)) H x xs.

Definition sem_laexp H ck (e: lexp)(xs: stream value): Prop :=
  lift (fun base R => sem_laexp_instant base R ck) H e xs.

Definition sem_laexps H (ck: clock)(e: lexps)(xs: stream (nelist value)): Prop :=
  lift (fun base R => sem_laexps_instant base R ck) H e xs.

Definition sem_lexp H (e: lexp)(xs: stream value): Prop :=
  lift sem_lexp_instant H e xs.

Definition sem_lexps H (e: lexps)(xs: stream (nelist value)): Prop :=
  lift sem_lexps_instant H e xs.

Definition sem_caexp H ck (c: cexp)(xs: stream value): Prop :=
  lift (fun base R => sem_caexp_instant base R ck) H c xs.

Definition sem_cexp H (c: cexp)(xs: stream value): Prop :=
  lift sem_cexp_instant H c xs.

End LiftSemantics.

(** ** Time-dependent semantics *)

Definition absent_list (xss: stream (nelist value))(n: nat): Prop :=
  Nelist.Forall (fun xs => xs = absent) (xss n).

Definition present_list (xss: stream (nelist value))(n: nat)(vs: nelist const): Prop :=
  xss n = Nelist.map present vs.

Lemma not_absent_present_list:
  forall xss n vs,
    present_list xss n vs -> ~ absent_list xss n.
Proof.
  intros * Hpres Habs.
  unfold present_list in Hpres.
  unfold absent_list in Habs.
  rewrite Hpres in *. destruct vs; inversion_clear Habs; discriminate.
Qed.

Definition clock_of (xss: stream (nelist value))(bs: stream bool): Prop :=
  forall n, 
    (exists vs, present_list xss n vs) <-> bs n = true.

(* FIXME: should we introduce the semantics of clocks somewhere? *)
Inductive sem_equation G : stream bool -> history -> equation -> Prop :=
| SEqDef:
    forall bk H x xs ck ce,
      sem_var bk H x xs ->
      sem_caexp bk H ck ce xs ->
      sem_equation G bk H (EqDef x ck ce)
| SEqApp:
    forall bk H x ck f arg ls xs,
      sem_laexps bk H ck arg ls ->
      sem_var bk H x xs ->
      sem_node G f ls xs ->
      sem_equation G bk H (EqApp x ck f arg)
| SEqFby:
    forall bk H x ls xs v0 ck le,
      sem_laexp bk H ck le ls ->
      sem_var bk H x xs ->
      xs = fby v0 ls ->
      sem_equation G bk H (EqFby x ck v0 le)

with sem_node G: ident -> stream (nelist value) -> stream value -> Prop :=
| SNode:
    forall bk f xss ys i o eqs,
      clock_of xss bk ->
      find_node f G = Some (mk_node f i o eqs) ->
      (exists H,
           sem_vars bk H i xss
        /\ sem_var bk H o ys
        (* XXX: This should be in Welldef_glob: *)
        (* no clocks faster than input *)
        /\ (forall n, absent_list xss n ->
                      List.Forall (rhs_absent_instant (bk n) (restr H n)) eqs)
        (* output clock matches input clock *) 
        /\ (forall n, absent_list xss n <-> ys n = absent)
        (* XXX: END *)
        /\ List.Forall (sem_equation G bk H) eqs) ->
      sem_node G f xss ys.

Definition sem_nodes (G: global) : Prop :=
  List.Forall (fun no => exists xs ys, sem_node G no.(n_name) xs ys) G.


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

  Variable P : forall bk H (eq: equation), sem_equation G bk H eq -> Prop.
  Variable Pn : forall (f: ident) xss ys, sem_node G f xss ys -> Prop.

  Hypothesis EqDef_case :
    forall (bk : stream bool)
           (H    : history)
	   (x    : ident)
           (ck   : clock)
	   (ce  : cexp)
           (xs   : stream value)
	   (Hvar : sem_var bk H x xs)
           (Hexp : sem_caexp bk H ck ce xs),
      P bk H (EqDef x ck ce) (SEqDef G bk H x xs ck ce Hvar Hexp).

  Hypothesis EqApp_case :
    forall (bk: stream bool)
           (H     : history)
	   (y     : ident)
           (ck    : clock)
	   (f     : ident)
	   (les   : lexps)
           (ls    : stream (nelist value))
           (ys    : stream value)
	   (Hlaes  : sem_laexps bk H ck les ls)
           (Hvar  : sem_var bk H y ys)
	   (Hnode : sem_node G f ls ys),
      Pn f ls ys Hnode ->
      P bk H (EqApp y ck f les) (SEqApp G bk H y ck f les ls ys Hlaes Hvar Hnode).

  Hypothesis EqFby_case :
    forall (bk: stream bool)
           (H   : history)
	   (y   : ident)
	   (ls  : stream value)
	   (yS  : stream value)
	   (v0  : const)
           (ck  : clock)
	   (lae : lexp)
	   (Hls : sem_laexp bk H ck lae ls)
	   (Hys : sem_var bk H y yS)
           (Hfby: yS = fby v0 ls),
      P bk H (EqFby y ck v0 lae) (SEqFby G bk H y ls yS v0 ck lae Hls Hys Hfby).

  Hypothesis SNode_case :
    forall (bk: stream bool)
           (f   : ident)
	   (xss : stream (nelist value))
	   (ys  : stream value)
	   (i   : nelist ident)
	   (o   : ident)
	   (eqs : list equation)
           (Hck : clock_of xss bk)
	   (Hf  : find_node f G = Some (mk_node f i o eqs))
           (Heqs : exists H,
                        sem_vars bk H i xss
	             /\ sem_var bk H o ys
                     /\ (forall n, absent_list xss n 
                                   -> List.Forall (rhs_absent_instant (bk n) (restr H n)) eqs)
                     /\ (forall n, absent_list xss n <-> ys n = absent)
	             /\ List.Forall (sem_equation G bk H) eqs),
      (exists H,
             sem_vars bk H i xss
          /\ sem_var bk H o ys
          /\ (forall n, absent_list xss n
                        -> List.Forall (rhs_absent_instant (bk n) (restr H n)) eqs)
          /\ (forall n, absent_list xss n <-> ys n = absent)
          /\ List.Forall (fun eq=> exists Hsem, P bk H eq Hsem) eqs)
      -> Pn f xss ys (SNode G bk f xss ys i o eqs Hck Hf Heqs).

  Fixpoint sem_equation_mult (bk: stream bool)
                             (H  : history)
			     (eq : equation)
			     (Heq : sem_equation G bk H eq) {struct Heq}
                                                                : P bk H eq Heq :=
    match Heq in (sem_equation _ bk H eq) return (P bk H eq Heq) with
    | SEqDef bk H y xs ck ce Hvar Hexp => EqDef_case bk H y ck ce xs Hvar Hexp
    | SEqApp bk H y ck f lae ls ys Hlae Hvar Hnode =>
      EqApp_case bk H y ck f lae ls ys Hlae Hvar Hnode
                 (sem_node_mult f ls ys Hnode)
    | SEqFby bk H y ls yS ck v0 lae Hls Hys Hfby => EqFby_case bk H y ls yS ck v0 lae Hls Hys Hfby
    end

  with sem_node_mult (f  : ident)
		     (ls : stream (nelist value))
		     (ys : stream value)
		     (Hn : sem_node G f ls ys) {struct Hn} : Pn f ls ys Hn :=
    match Hn in (sem_node _ f ls ys) return (Pn f ls ys Hn) with
    | SNode bk f ls ys i o eqs Hck Hf Hnode =>
        SNode_case bk f ls ys i o eqs Hck Hf Hnode
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
                             (Heqs: List.Forall (sem_equation G bk H) eqs) :=
                       match Heqs in List.Forall _ fs
                             return (List.Forall (fun eq=> exists Hsem,
                                                        P bk H eq Hsem) fs)
                       with
                       | List.Forall_nil => List.Forall_nil _
                       | List.Forall_cons eq eqs Heq Heqs' =>
                         List.Forall_cons eq (@ex_intro _ _ Heq
                                           (sem_equation_mult bk H eq Heq))
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

Section InstantDeterminism.

Variable base: bool.

Lemma sem_clock_instant_det:
  forall ck R v1 v2,
    sem_clock_instant base R ck v1
    -> sem_clock_instant base R ck v2
    -> v1 = v2.
Proof.
  induction ck; repeat inversion_clear 1; intuition;
  try match goal with
        | H1: sem_clock_instant ?bk ?R ?ck ?l,
          H2: sem_clock_instant ?bk ?R ?ck ?r |- ?l = ?r =>
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
  forall R e v1 v2,
    sem_lexp_instant base R e v1
    -> sem_lexp_instant base R e v2
    -> v1 = v2.
Proof.
  intros R e.
  induction e using lexp_ind2;
    try now (do 2 inversion_clear 1);
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
- do 2 inversion_clear 1; destruct base; congruence.
- intros v1 v2 Hsem1 Hsem2.
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
  forall R ck e v1 v2,
    sem_laexp_instant base R ck e v1
    -> sem_laexp_instant base R ck e v2
    -> v1 = v2.
Proof.
  intros R ck e v1 v2.
  do 2 inversion_clear 1;
  match goal with
  | H1:sem_lexp_instant _ _ _ _, H2:sem_lexp_instant _ _ _ _ |- _ =>
    eapply sem_lexp_instant_det; eassumption
  end; auto.
Qed.

Lemma sem_lexps_instant_det:
  forall R les cs1 cs2,
    sem_lexps_instant base R les cs1 ->
    sem_lexps_instant base R les cs2 ->
    cs1 = cs2.
Proof.
  intros R les cs1 cs2. apply Nelist.Forall2_det. apply sem_lexp_instant_det.
Qed.

Lemma sem_laexps_instant_det:
  forall R ck e v1 v2,
    sem_laexps_instant base R ck e v1
    -> sem_laexps_instant base R ck e v2
    -> v1 = v2.
Proof.
  intros until v2.
  do 2 inversion_clear 1;
  eapply sem_lexps_instant_det; eauto.
Qed.

Lemma sem_cexp_instant_det:
  forall R e v1 v2,
    sem_cexp_instant base R e v1
    -> sem_cexp_instant base R e v2
    -> v1 = v2.
Proof.
  intros R e.
  induction e;
  do 2 inversion_clear 1;
    try match goal with
      | H1: sem_cexp_instant ?bk ?R ?e ?l,
        H2: sem_cexp_instant ?bk ?R ?e ?r
        |- ?l = ?r =>
        (eapply IHe1; eassumption)
     || (eapply IHe2; eassumption)
      | H1: sem_var_instant ?R ?i (present (Cbool true)),
        H2: sem_var_instant ?R ?i (present (Cbool false)) |- _ =>
        exfalso;
          assert (present (Cbool true) = present (Cbool false))
          by (eapply sem_var_instant_det; eassumption);
          discriminate
      | H1: sem_lexp_instant ?bk ?R ?l ?v1,
        H2: sem_lexp_instant ?bk ?R ?l ?v2 |- ?v1 = ?v2 =>
        eapply sem_lexp_instant_det; eassumption
      | H1: sem_var_instant ?R ?i (present _),
        H2: sem_var_instant ?R ?i absent |- _ =>
        apply sem_var_instant_det with (1:=H1) in H2; discriminate
      | |- absent = absent => reflexivity
    end.
Qed.

Lemma sem_caexp_instant_det:
  forall R ck e v1 v2,
    sem_caexp_instant base R ck e v1
    -> sem_caexp_instant base R ck e v2
    -> v1 = v2.
Proof.
  intros until v2.
  do 2 inversion_clear 1;
  match goal with
  | H1: sem_cexp_instant _ _ _ _,
    H2: sem_cexp_instant _ _ _ _ |- _ =>
    eapply sem_cexp_instant_det; eassumption
  end.
Qed.

End InstantDeterminism.

Section LiftDeterminism.

Variable bk : stream bool.

Require Import Logic.FunctionalExtensionality.

Lemma lift_det:
  forall {A B} (P: bool -> R -> A -> B -> Prop) (bk: stream bool) H x (xs1 xs2 : stream B),
    (forall b R v1 v2, P b R x v1 -> P b R x v2 -> v1 = v2) ->
    lift bk P H x xs1 -> lift bk P H x xs2 -> xs1 = xs2.
Proof.
  intros ** Hpoint H1 H2.
  extensionality n. specialize (H1 n). specialize (H2 n).
  eapply Hpoint; eassumption.
Qed.

Ltac apply_lift sem_det :=
  intros; eapply lift_det; try eassumption;
  compute; intros; eapply sem_det; eauto.

Lemma sem_var_det:
  forall H x xs1 xs2,
    sem_var bk H x xs1 -> sem_var bk H x xs2 -> xs1 = xs2.
Proof.
  apply_lift sem_var_instant_det.
Qed.

Lemma sem_clock_det : forall H ck bs1 bs2,
  sem_clock bk H ck bs1 -> sem_clock bk H ck bs2 -> bs1 = bs2.
Proof.
  apply_lift sem_clock_instant_det.
Qed.

Lemma sem_lexp_det:
  forall H e xs1 xs2,
    sem_lexp bk H e xs1 -> sem_lexp bk H e xs2 -> xs1 = xs2.
Proof.
  apply_lift sem_lexp_instant_det.
Qed.

Lemma sem_lexps_det:
  forall H les cs1 cs2,    
    sem_lexps bk H les cs1 ->
    sem_lexps bk H les cs2 ->
    cs1 = cs2.
Proof.
  apply_lift sem_lexps_instant_det.
Qed.


Lemma sem_laexp_det:
  forall H ck e xs1 xs2,  
    sem_laexp bk H ck e xs1 -> sem_laexp bk H ck e xs2 -> xs1 = xs2.
Proof.
  apply_lift sem_laexp_instant_det.
Qed.

Lemma sem_laexps_det:
  forall H ck e xs1 xs2,  
    sem_laexps bk H ck e xs1 -> sem_laexps bk H ck e xs2 -> xs1 = xs2.
Proof.
  apply_lift sem_laexps_instant_det.
Qed.

Lemma sem_cexp_det:
  forall H c xs1 xs2,
    sem_cexp bk H c xs1 -> sem_cexp bk H c xs2 -> xs1 = xs2.
Proof.
  apply_lift sem_cexp_instant_det.
Qed.

Lemma sem_caexp_det:
  forall H ck c xs1 xs2,  
    sem_caexp bk H ck c xs1 -> sem_caexp bk H ck c xs2 -> xs1 = xs2.
Proof.
  apply_lift sem_caexp_instant_det.
Qed.


(* XXX: every semantics definition, including [sem_var] which doesn't
need it, takes a base clock value or base clock stream, except
[sem_var_instant]. For uniformity, we may want to pass a (useless)
clock to [sem_var_instant] too. *)

End LiftDeterminism.

Ltac sem_det :=
  match goal with
    | H1: sem_cexp_instant ?bk ?H ?C ?X,
      H2: sem_cexp_instant ?bk ?H ?C ?Y |- ?X = ?Y =>
      eapply sem_cexp_instant_det; eexact H1 || eexact H2
    | H1: sem_cexp ?bk ?H ?C ?X,
      H2: sem_cexp ?bk ?H ?C ?Y |- ?X = ?Y =>
      eapply sem_cexp_det; eexact H1 || eexact H2
    | H1: sem_lexps_instant ?bk ?H ?C ?X,
      H2: sem_lexps_instant ?bk ?H ?C ?Y |- ?X = ?Y =>
      eapply sem_lexps_instant_det; eexact H1 || eexact H2
    | H1: sem_lexps ?bk ?H ?C ?X,
      H2: sem_lexps ?bk ?H ?C ?Y |- ?X = ?Y =>
      eapply sem_lexps_det; eexact H1 || eexact H2
    | H1: sem_laexps_instant ?bk ?H ?ck ?C ?X,
      H2: sem_laexps_instant ?bk ?H ?ck ?C ?Y |- ?X = ?Y =>
      eapply sem_laexps_instant_det; eexact H1 || eexact H2
    | H1: sem_laexps ?bk ?H ?ck ?C ?X,
      H2: sem_laexps ?bk ?H ?ck ?C ?Y |- ?X = ?Y =>
      eapply sem_laexps_det; eexact H1 || eexact H2
    | H1: sem_lexp_instant ?bk ?H ?C ?X,
      H2: sem_lexp_instant ?bk ?H ?C ?Y |- ?X = ?Y =>
      eapply sem_lexp_instant_det; eexact H1 || eexact H2
    | H1: sem_lexp ?bk ?H ?C ?X,
      H2: sem_lexp ?bk ?H ?C ?Y |- ?X = ?Y =>
      eapply sem_lexp_det; eexact H1 || eexact H2
    | H1: sem_laexp_instant ?bk ?H ?CK ?C ?X,
      H2: sem_laexp_instant ?bk ?H ?CK ?C ?Y |- ?X = ?Y =>
      eapply sem_laexp_instant_det; eexact H1 || eexact H2
    | H1: sem_laexp ?bk ?H ?CK ?C ?X,
      H2: sem_laexp ?bk ?H ?CK ?C ?Y |- ?X = ?Y =>
      eapply sem_laexp_det; eexact H1 || eexact H2
    | H1: sem_var_instant ?H ?C ?X,
      H2: sem_var_instant ?H ?C ?Y |- ?X = ?Y =>
      eapply sem_var_instant_det; eexact H1 || eexact H2
    | H1: sem_var ?bk ?H ?C ?X,
      H2: sem_var ?bk ?H ?C ?Y |- ?X = ?Y =>
      eapply sem_var_det; eexact H1 || eexact H2
  end.

(** ** Global management *)

(* Section GlobalManagement. *)

(* Variable bk: stream bool. *)

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
  induction Hsem as [
                    | bk H y ck f lae ls ys Hlae Hvar Hnode IH
                    | 
                    | bk f xs ys i o eqs Hbk Hf Heqs IH]
  using sem_node_mult
  with (P := fun bk H eq Hsem => ~Is_node_in_eq node.(n_name) eq
                              -> sem_equation G bk H eq).
  - econstructor; eassumption.
  - intro Hnin.
    eapply @SEqApp with (1:=Hlae) (2:=Hvar).
    apply IH. intro Hnf. apply Hnin. rewrite Hnf. constructor.
  - intro; eapply SEqFby; eassumption.
  - intro.
    rewrite find_node_tl with (1:=Hnf) in Hf.
    eapply SNode; eauto.
    clear Heqs.
    destruct IH as [H [Hxs [Hys [Habs [Hout Heqs]]]]].
    exists H.
    repeat (split; eauto).
    set (cnode := {| n_name := f; n_input := i; n_output := o; n_eqs := eqs |}).
    assert (List.Forall (fun eq => ~ Is_node_in_eq (n_name node) eq) (n_eqs cnode)) 
      by (eapply Is_node_in_Forall; try eassumption;
          eapply find_node_later_not_Is_node_in; try eassumption).
    eapply Forall_Forall in Heqs; try eauto.
    eapply Forall_impl with (2:=Heqs).
    destruct 1 as [Hnini [Hsem HH]].
    intuition.
Qed.

Lemma find_node_find_again:
  forall G f i o eqs g,
    Ordered_nodes G
    -> find_node f G =
       Some {| n_name := f; n_input := i; n_output := o; n_eqs := eqs |}
    -> Is_node_in g eqs
    -> List.Exists (fun nd=> g = nd.(n_name)) G.
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
    -> List.Forall (fun nd' : node => n_name nd <> n_name nd') G
    -> sem_node (nd::G) f xs ys.
Proof.
  Hint Constructors sem_equation.
  intros nd G f xs ys Hord Hsem Hnin.
  assert (Hnin':=Hnin).
  revert Hnin'.
  induction Hsem as [
                    | bk H y f lae ls ys Hlae Hvar Hnode IH
                    |
                    | bk f xs ys i o eqs Hbk Hfind Heqs IH]
  using sem_node_mult
  with (P := fun bk H eq Hsem => ~Is_node_in_eq nd.(n_name) eq
                              -> sem_equation (nd::G) bk H eq);
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
  econstructor; eauto.
  clear Heqs.
  destruct IH as [H [Hxs [Hys [Habs [Hout Heqs]]]]].
  exists H.
  intuition; clear Hxs Hys Habs.
  assert (forall g, Is_node_in g eqs
                    -> List.Exists (fun nd=> g = nd.(n_name)) G)
    as Hniex
    by (intros g Hini;
        apply find_node_find_again with (1:=Hord) (2:=Hfind) in Hini;
        exact Hini).
  assert (List.Forall
            (fun eq=> forall g,
                 Is_node_in_eq g eq
                 -> List.Exists (fun nd=> g = nd.(n_name)) G) eqs) as HH.
  {
    clear Hfind Heqs Hnf.
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
  apply List.Exists_exists in Hini.
  destruct Hini as [nd' [Hin [Hneq Heq]]].
  intuition.
Qed.


Lemma Forall_sem_equation_global_tl:
  forall bk nd G H eqs,
    Ordered_nodes (nd::G)
    -> ~ Is_node_in nd.(n_name) eqs
    -> List.Forall (sem_equation (nd::G) bk H) eqs
    -> List.Forall (sem_equation G bk H) eqs.
Proof.
  intros bk nd G H eqs Hord.
  induction eqs as [|eq eqs IH]; [trivial|].
  intros Hnini Hsem.
  apply Forall_cons2 in Hsem; destruct Hsem as [Hseq Hseqs].
  apply IH in Hseqs.
  2:(apply not_Is_node_in_cons in Hnini;
     destruct Hnini; assumption).
  apply List.Forall_cons with (2:=Hseqs).
  inversion Hseq as [|? ? ? ? ? ? ? Hsem Hvar Hnode|]; subst.
  - econstructor; eassumption.
  - apply not_Is_node_in_cons in Hnini.
    destruct Hnini as [Hninieq Hnini].
    assert (nd.(n_name) <> f) as Hnf
      by (intro HH; apply Hninieq; rewrite HH; constructor).
    econstructor; eauto.
    eapply sem_node_cons; eauto.
  - econstructor; eauto.
Qed.
