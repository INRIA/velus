Require Import Coq.FSets.FMapPositive.
Require Import Rustre.Nelist.
Require Import List.

Require Import Rustre.Common.
Require Import Rustre.Memory.
Require Import Rustre.Minimp.Syntax.

(** * Minimp semantics *)

(** 

  The semantics of Minimp relies on a tree-structure [memory], based
  on [Rustre.Memory], to store object instances and a [stack] to keep
  track of local variables during method calls.

 *)

Definition heap: Type := memory const.
Definition stack : Set := PM.t const.

Implicit Type mmem: heap.
Implicit Type stack: stack.

Definition sempty: stack := PM.empty const.
Definition hempty: heap := empty_memory _.

Inductive exp_eval heap stack:
  exp -> const -> Prop :=
| evar:
    forall x v,
      PM.find x stack = Some(v) ->
      exp_eval heap stack (Var(x)) v
| estate:
    forall x v,
      mfind_mem x heap = Some(v) ->
      exp_eval heap stack (State(x)) v
| econst:
    forall c ,
      exp_eval heap stack (Const(c)) c
| eop:
    forall op es cs c,
      Nelist.Forall2 (exp_eval heap stack) es cs ->
      apply_op op cs = Some c ->
      exp_eval heap stack (Op op es) c.

Lemma exps_eval_const:
  forall h s cs,
    Nelist.Forall2 (exp_eval h s) (Nelist.map Const cs) cs.
Proof.
  Hint Constructors exp_eval.
  intros h s cs. induction cs; constructor; eauto.
Qed.

(* =stmt_eval= *)
Inductive stmt_eval :
    program -> heap -> stack -> stmt -> heap * stack -> Prop :=
| Iassign: forall prog menv env x e v env',
      exp_eval menv env e v ->
      PM.add x v env = env' ->
      stmt_eval prog menv env (Assign x e) (menv, env')
| (*...*)
(* =end= *)
  Iassignst:
    forall prog menv env x e v menv',
      exp_eval menv env e v ->
      madd_mem x v menv = menv' ->
      stmt_eval prog menv env (AssignSt x e) (menv', env)
(* =stmt_eval:step= *)
| Istep: forall prog menv env es vs clsid o y menv' env' omenv omenv' rv,
      mfind_inst o menv = Some(omenv) ->
      Nelist.Forall2 (exp_eval menv env) es vs ->
      stmt_step_eval prog omenv clsid vs omenv' rv ->
      madd_obj o omenv' menv = menv' ->
      PM.add y rv env  = env' ->
      stmt_eval prog menv env (Step_ap y clsid o es) (menv', env')
| (*...*)
(* =end= *)
  Ireset:
    forall prog menv env o clsid omenv' menv',
      stmt_reset_eval prog clsid omenv' ->
      madd_obj o omenv' menv = menv' ->
      stmt_eval prog menv env (Reset_ap clsid o) (menv', env)
| Icomp:
    forall prog menv env a1 a2 env1 menv1 env2 menv2,
      stmt_eval prog menv env a1 (menv1, env1) ->
      stmt_eval prog menv1 env1 a2 (menv2, env2) ->
      stmt_eval prog menv env (Comp a1 a2) (menv2, env2)
| Iifte_true:
    forall prog menv env b ifTrue ifFalse env' menv',
      exp_eval menv env b (Cbool true) ->
      stmt_eval prog menv env ifTrue (menv', env') ->
      stmt_eval prog menv env (Ifte b ifTrue ifFalse) (menv', env')
| Iifte_false:
    forall prog menv env b ifTrue ifFalse env' menv',
      exp_eval menv env b (Cbool false) ->
      stmt_eval prog menv env ifFalse (menv', env') ->
      stmt_eval prog menv env (Ifte b ifTrue ifFalse) (menv', env')
| Iskip:
    forall prog menv env,
      stmt_eval prog menv env Skip (menv, env)
(* =stmt_step_eval= *)
with stmt_step_eval :
       program -> heap -> ident -> nelist const -> heap -> const -> Prop :=
| Iestep:
    forall prog menv env clsid ivs prog' menv' ov cls env',
      find_class clsid prog = Some(cls, prog') ->
      env = adds cls.(c_input) ivs sempty ->
      stmt_eval prog' menv env cls.(c_step)
                (menv', env') ->
      PM.find cls.(c_output) env' = Some(ov) ->
      stmt_step_eval prog menv clsid ivs menv' ov
(* =end= *)

with stmt_reset_eval : program -> ident -> heap -> Prop :=
| Iereset:
    forall prog clsid cls prog' menv' env',
      find_class clsid prog = Some(cls, prog') ->
      stmt_eval prog' hempty sempty cls.(c_reset) (menv', env') ->
      stmt_reset_eval prog clsid menv'.

Scheme stmt_eval_mult := Induction for stmt_eval Sort Prop
with stmt_step_eval_mult := Induction for stmt_step_eval Sort Prop
with stmt_reset_eval_mult := Induction for stmt_reset_eval Sort Prop.

(*
Definition class_eval prog f menv input output menv' :=
  forall fclass prog' env env',
    find_class f prog = Some (fclass, prog') ->
    env = PM.add (c_input fclass) input sempty ->
    stmt_eval prog' menv env (c_step fclass) (menv', env')
    /\ PM.find (c_output fclass) env' = Some output.
*)

(** ** Determinism of semantics *)

Lemma exp_eval_det:
  forall menv env e v1 v2,
    exp_eval menv env e v1 ->
    exp_eval menv env e v2 ->
    v1 = v2.
Proof.
  induction e using exp_ind2;
    intros v1 v2 H1 H2;
    inversion H1 as [xa va Hv1|xa va Hv1|xa va Hv1| xa opa esa IHa Hv1];
    inversion H2 as [xb vb Hv2|xb vb Hv2|xb vb Hv2| xb opb esb IHb Hv2];
    try (rewrite Hv1 in Hv2; (injection Hv2; trivial) || apply Hv2).
  subst.
  assert (esa = esb).
  { clear H1 H2 H4 H8. revert esa esb Hv1 Hv2. induction es; intros esa esb Hv1 Hv2.
    * inversion_clear Hv1. inversion_clear Hv2. f_equal. inversion_clear IHes. now apply H1.
    * inversion_clear Hv1. inversion_clear Hv2. inversion_clear IHes. f_equal.
      + now apply H3.
      + now apply IHes0. }
  subst. rewrite H4 in *. now inversion H8.
Qed.

Lemma stmt_eval_fold_left_shift:
  forall A prog f (xs:list A) iacc menv env menv' env',
    stmt_eval prog menv env
              (List.fold_left (fun i x => Comp (f x) i) xs iacc)
              (menv', env')
    <->
    exists menv'' env'',
      stmt_eval prog menv env
                (List.fold_left (fun i x => Comp (f x) i) xs Skip)
                (menv'', env'')
      /\
      stmt_eval prog menv'' env'' iacc (menv', env').
Proof.
  Hint Constructors stmt_eval.
  induction xs.
  - split; [ now eauto | ].
    intro H; do 2 destruct H.
    destruct H as [H0 H1].
    inversion_clear H0; apply H1.
  - intros.
    split.
    + intro H0.
      apply IHxs in H0.
      destruct H0 as [menv'' H0].
      destruct H0 as [env'' H0].
      destruct H0 as [H0 H1].
      inversion_clear H1.
      exists menv1. exists env1.
      split; try apply IHxs; eauto.
    + intros;
      repeat progress
             match goal with
             | H:exists _, _ |- _ => destruct H
             | H:_ /\ _ |- _ => destruct H
             | H:stmt_eval _ _ _ (Comp _ Skip) _ |- _ => inversion_clear H
             | H:stmt_eval _ _ _ Skip _ |- _ => inversion H; subst
             | H:stmt_eval _ _ _ (List.fold_left _ _ _) _ |- _ => apply IHxs in H
             | _ => eauto
             end.
      apply IHxs; eauto.
Qed.

Lemma exp_evals_det:
  forall menv env es vs1 vs2,
    Nelist.Forall2 (exp_eval menv env) es vs1 ->
    Nelist.Forall2 (exp_eval menv env) es vs2 ->
    vs1 = vs2.
Proof.
  intros menv env es vs1 vs2 H1; generalize dependent vs2.
  induction H1 as [|e1 c1 es1 cs1]; intros vs2 H2;
  inversion_clear H2 as [|e2 c2 es2 cs2].
  - f_equal. eauto using exp_eval_det.
  - assert (c1 = c2) by eauto using exp_eval_det.
    assert (cs1 = cs2) by eauto using IHForall2.
    congruence.
Qed.

Lemma stmt_eval_det:
  forall prog s menv env renv1 renv2,
    stmt_eval prog menv env s renv1
    -> stmt_eval prog menv env s renv2
    -> renv1 = renv2.
Proof.
  intros prog s menv env renv1 renv2 Hs1.
  revert renv2.
  induction Hs1 using stmt_eval_mult
  with (P:=fun prog menv env s renv1 sev=>
             forall renv2, stmt_eval prog menv env s renv2 -> renv1 = renv2)
       (P0:=fun prog menv clsid v menv' rv ssev=>
              forall menv'' rv', stmt_step_eval prog menv clsid v menv'' rv'
                                 -> menv' = menv'' /\ rv = rv')
       (P1:=fun prog i menv srev=>
              forall menv', stmt_reset_eval prog i menv' -> menv = menv');
    inversion_clear 1;
    repeat progress match goal with
    | H: ?env = adds _ _ _ |- _ => subst env
    | Ht: exp_eval ?menv ?env ?e (Cbool true),
      Hf: exp_eval ?menv ?env ?e (Cbool false) |- _ =>
      pose proof (exp_eval_det _ _ _ _ _ Ht Hf) as Hneq; discriminate
    | H1:exp_eval ?menv ?env ?e ?v1,
      H2:exp_eval ?menv ?env ?e ?v2 |- _ =>
      pose proof (exp_eval_det _ _ _ _ _ H1 H2) as Heq;
        rewrite Heq in *; clear Heq H1 H2
    | H1: Nelist.Forall2 (exp_eval ?menv ?env) ?es ?vs1,
      H2: Nelist.Forall2 (exp_eval ?menv ?env) ?es ?vs2 |- _ =>
      pose proof (exp_evals_det _ _ _ _ _ H1 H2) as Heq;
        rewrite Heq in *; clear Heq H1 H2
    | H1: PM.add ?x ?v ?env = ?env1,
      H2: PM.add ?x ?v ?env = ?env2 |- _ =>
      rewrite H1 in H2; rewrite H2 in *; clear H1 H2
    | H1: madd_mem ?x ?v ?menv = ?menv1,
      H2: madd_mem ?x ?v ?menv = ?menv2 |- _ =>
      rewrite H1 in H2; rewrite H2 in *; clear H1 H2
    | H1: mfind_inst ?o ?menv = Some ?omenv1,
      H2: mfind_inst ?o ?menv = Some ?omenv2 |- _ =>
      rewrite H1 in H2; injection H2; intro Heq; rewrite Heq in *;
      clear H1 H2 Heq
    | H1: find_class ?clsid ?prog = _,
      H2: find_class ?clsid ?prog = _ |- _ =>
      rewrite H1 in H2; injection H2;
      intros Heq1 Heq2; rewrite Heq1, Heq2 in *; clear H2 H2 Heq1 Heq2
    | H1: PM.find ?x ?env = ?rv1,
      H2: PM.find ?x ?env = ?rv2 |- _ =>
      rewrite H1 in H2; injection H2; rewrite H2 in *; clear H1 H2
    | Hs: stmt_step_eval ?prog ?omenv ?clsid ?v _ _,
          IH: context[stmt_step_eval ?prog ?omenv ?clsid ?v _ _ -> _ = _ /\ _ = _]
              |- _ =>
      apply IH in Hs; destruct Hs as [Heq1 Heq2]; try rewrite Heq1 in *;
      try rewrite Heq2 in *; clear Heq1 Heq2
    | Hs: stmt_reset_eval ?prog ?clsid _,
      IH: context[stmt_reset_eval ?prog ?clsid _ -> _ = _] |- _ =>
      apply IH in Hs; try rewrite Hs in *; clear Hs
    | Hs: stmt_eval ?prog ?menv ?env ?stmt _,
      IH: context[stmt_eval ?prog ?menv ?env ?stmt _ -> (_, _) = _] |- _ =>
      apply IH in Hs; injection Hs; intros Heq1 Heq2;
      try rewrite Heq1 in *; try rewrite Heq2 in *; clear Heq1 Heq2 Hs
    | H1: madd_obj ?o ?omenv ?menv = ?menv1,
      H2: madd_obj ?o ?omenv ?menv = ?menv2 |- _ =>
      rewrite H1 in H2; rewrite H2 in *; clear H1 H2
    | _ => intuition
    end.
Qed.

