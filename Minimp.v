Require Import Coq.FSets.FMapPositive.
Require Import Rustre.Common.

Import List.ListNotations.
Open Scope list_scope.

(** * Imperative language *)

(** ** Syntax *)

Inductive exp : Set :=
| Var : ident -> exp
| State : ident -> exp
| Const : const -> exp.

Inductive stmt : Set :=
  | Assign : ident -> exp -> stmt
  | AssignSt : ident -> exp -> stmt
  | Ifte : exp -> stmt -> stmt -> stmt
  | Step_ap : ident -> ident -> ident -> exp -> stmt
           (* y = Step_ap class object arg *)
  | Reset_ap : ident -> ident -> stmt
           (* Reset_ap class object *)
  | Comp : stmt -> stmt -> stmt
  | Repeat : nat -> stmt -> stmt
  | Skip.

Record obj_dec : Set := mk_obj_dec {
  obj_inst  : ident;
  obj_class : ident
}.

Record class : Set := mk_class {
  c_name   : ident;

  c_input  : ident;
  c_output : ident;

  c_mems   : list ident;       (* TODO: should track type of each *)
  c_objs   : list obj_dec;

  c_step   : stmt;
  c_reset  : stmt
}.

Definition program : Type := list class.

Definition find_class (n: ident) : program -> option (class * list class) :=
  fix find (p: program) :=
    match p with
    | [] => None
    | c :: p' => if ident_eqb c.(c_name) n then Some (c, p') else find p'
    end.

(** ** Semantics *)

Inductive memoryEnv : Set :=
  mk_memory
    { m_values  : PM.t const;
      m_objects : PM.t memoryEnv }.

Definition add_mem (id: ident) (v: const) (menv: memoryEnv) : memoryEnv :=
  mk_memory (PM.add id v menv.(m_values))
            (menv.(m_objects)).

Definition find_mem (id: ident) (menv: memoryEnv) : option const :=
  PM.find id (menv.(m_values)).

Definition add_obj (id: ident) (omenv: memoryEnv) (menv: memoryEnv)
  : memoryEnv := mk_memory menv.(m_values)
                           (PM.add id omenv menv.(m_objects)).

Definition find_obj (id: ident) (menv: memoryEnv) : option memoryEnv :=
  PM.find id (menv.(m_objects)).

Definition constEnv : Set := PM.t const.

Definition empty: constEnv := PM.empty const.
Definition mempty: memoryEnv := mk_memory empty (PM.empty memoryEnv).

Inductive exp_eval (menv: memoryEnv)(env: constEnv):
  exp -> const -> Prop :=
| evar:
    forall x v,
      PM.find x env = Some(v) ->
      exp_eval menv env (Var(x)) v
| estate:
    forall x v,
      find_mem x menv = Some(v) ->
      exp_eval menv env (State(x)) v
| econst:
    forall c ,
      exp_eval menv env (Const(c)) c.

Lemma exp_eval_det:
  forall menv env e v1 v2,
    exp_eval menv env e v1 ->
    exp_eval menv env e v2 ->
    v1 = v2.
Proof.
  induction e;
    intros v1 v2 H1 H2;
    inversion H1 as [xa va Hv1|xa va Hv1|xa va Hv1];
    inversion H2 as [xb vb Hv2|xb vb Hv2|xb vb Hv2];
    rewrite Hv1 in Hv2;
    ( injection Hv2; trivial ) || apply Hv2.
Qed.

Inductive stmt_eval :
  program -> memoryEnv -> constEnv -> stmt -> memoryEnv * constEnv -> Prop :=
| Iassign:
    forall prog menv env x e v env',
      exp_eval menv env e v ->
      PM.add x v env = env' ->
      stmt_eval prog menv env (Assign x e) (menv, env')
| Iassignst:
    forall prog menv env x e v menv',
      exp_eval menv env e v ->
      add_mem x v menv = menv' ->
      stmt_eval prog menv env (AssignSt x e) (menv', env)
| Istep:
    forall prog menv env e v clsid o y menv' env' omenv omenv' rv,
      find_obj o menv = Some(omenv) ->
      exp_eval menv env e v ->
      stmt_step_eval prog omenv clsid v omenv' rv ->
      add_obj o omenv' menv = menv' ->
      PM.add y rv env  = env' ->
      stmt_eval prog menv env (Step_ap y clsid o e) (menv', env')
| Ireset:
    forall prog menv env o clsid omenv' menv',
      stmt_reset_eval prog clsid omenv' ->
      add_obj o omenv' menv = menv' ->
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
| IrepeatO:
    forall prog a menv env,
      stmt_eval prog menv env (Repeat 0 a) (menv, env)
| IrepeatS:
    forall prog n a menv0 env0 menv1 env1 menv2 env2,
      stmt_eval prog menv0 env0 a (menv1, env1) ->
      stmt_eval prog menv1 env1 (Repeat n a) (menv2, env2) ->
      stmt_eval prog menv0 env0 (Repeat (S n) a) (menv2, env2)
| Iskip:
    forall prog menv env,
      stmt_eval prog menv env Skip (menv, env)
with stmt_step_eval :
       program -> memoryEnv -> ident -> const -> memoryEnv -> const -> Prop :=
| Iestep:
    forall prog menv clsid iv prog' menv' ov cls env',
      find_class clsid prog = Some(cls, prog') ->
      stmt_eval prog' menv (PM.add cls.(c_input) iv empty) cls.(c_step)
                (menv', env') ->
      PM.find cls.(c_output) env' = Some(ov) ->
      stmt_step_eval prog menv clsid iv menv' ov
with stmt_reset_eval : program -> ident -> memoryEnv -> Prop :=
| Iereset:
    forall prog clsid cls prog' menv' env',
      find_class clsid prog = Some(cls, prog') ->
      stmt_eval prog' mempty empty cls.(c_reset) (menv', env') ->
      stmt_reset_eval prog clsid menv'.

Scheme stmt_eval_mult := Induction for stmt_eval Sort Prop
with stmt_step_eval_mult := Induction for stmt_step_eval Sort Prop
with stmt_reset_eval_mult := Induction for stmt_reset_eval Sort Prop.

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
    | Ht: exp_eval ?menv ?env ?e (Cbool true),
      Hf: exp_eval ?menv ?env ?e (Cbool false) |- _ =>
      pose proof (exp_eval_det _ _ _ _ _ Ht Hf) as Hneq; discriminate
    | H1:exp_eval ?menv ?env ?e ?v1,
      H2:exp_eval ?menv ?env ?e ?v2 |- _ =>
      pose proof (exp_eval_det _ _ _ _ _ H1 H2) as Heq;
        rewrite Heq in *; clear Heq H1 H2
    | H1: PM.add ?x ?v ?env = ?env1,
      H2: PM.add ?x ?v ?env = ?env2 |- _ =>
      rewrite H1 in H2; rewrite H2 in *; clear H1 H2
    | H1: add_mem ?x ?v ?menv = ?menv1,
      H2: add_mem ?x ?v ?menv = ?menv2 |- _ =>
      rewrite H1 in H2; rewrite H2 in *; clear H1 H2
    | H1: find_obj ?o ?menv = Some ?omenv1,
      H2: find_obj ?o ?menv = Some ?omenv2 |- _ =>
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
    | H1: add_obj ?o ?omenv ?menv = ?menv1,
      H2: add_obj ?o ?omenv ?menv = ?menv2 |- _ =>
      rewrite H1 in H2; rewrite H2 in *; clear H1 H2
    | _ => intuition
    end.
Qed.

Lemma find_mem_gss:
  forall y c m, find_mem y (add_mem y c m) = Some c.
Proof.
  intros. apply PM.gss.
Qed.

Lemma find_mem_gso:
  forall x y c m, x <> y -> find_mem x (add_mem y c m) = find_mem x m.
Proof.
  intros. apply PM.gso. assumption.
Qed.

