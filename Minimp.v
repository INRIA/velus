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
  | Step_ap : ident -> ident -> exp -> stmt
  | Comp : stmt -> stmt -> stmt
  | Skip.

Record obj_dec : Set := mk_obj_dec {
  obj_name : ident;
  obj_value : ident
}.

Record step_fun : Set := mk_step_fun {
  input : ident;
  output : ident;
  locals : list ident;
  body : stmt
}.

Record class_def : Set := mk_class {
  c_id : ident;
  c_objs : list obj_dec;
  c_step : step_fun
}.

Definition program : Type := list class_def.

(** ** Semantics *)

(* TODO: I never seem to use/need machines and global
environment. Joperationnal.v doesn't seem use them either. Yet, that's
disturbing: where are the compiled ojects, in the memory env?

Record machine : Set :=
  mk_machine {
      m_instances: PositiveMap.t ident;
      m_step: step_fun
    }.

Definition globalEnv : Set := PositiveMap.t machine.
 *)

Record memoryEnv : Set :=
  mk_memory {
      m_values : PM.t const;
      m_instances : PM.t step_fun
    }.

Definition add_mem (id: ident) (v: const) (menv: memoryEnv) : memoryEnv :=
  mk_memory (PM.add id v menv.(m_values))
            (menv.(m_instances)).

Definition find_mem (id: ident) (menv: memoryEnv) : option const :=
  PM.find id (menv.(m_values)).

Definition add_object (id: ident) (f: step_fun) (menv: memoryEnv) : memoryEnv :=
  mk_memory menv.(m_values)
            (PM.add id f menv.(m_instances)).

Definition find_object (id: ident) (menv: memoryEnv) : option step_fun :=
  PM.find id (menv.(m_instances)).


Definition constEnv : Set := PM.t const.

Definition empty: constEnv := PM.empty const.

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

Inductive stmt_eval (menv: memoryEnv)(env: constEnv) :
  stmt -> memoryEnv * constEnv -> Prop :=
| Iassign:
    forall x e v env',
      exp_eval menv env e v ->
      PM.add x v env = env' ->
      stmt_eval menv env (Assign x e) (menv, env')
| Iassignst:
    forall x e v menv',
      exp_eval menv env e v ->
      add_mem x v menv = menv' ->
      stmt_eval menv env (AssignSt x e) (menv', env)
| Iapp:
    forall e v o y env' s_fun res_value res_memory,
      exp_eval menv env e v ->
      find_object o menv = Some(s_fun) ->
      application menv empty s_fun v (res_value, res_memory) ->
      PM.add y res_value env  = env' ->
      stmt_eval menv env (Step_ap y o e) (menv, env')
| Icomp:
    forall a1 a2 env1 menv1 env2 menv2,
      stmt_eval menv env a1 (menv1, env1) ->
      stmt_eval menv1 env1 a2 (menv2, env2) ->
      stmt_eval menv env (Comp a1 a2) (menv2, env2)
| Iifte_true:
    forall b ifTrue ifFalse env' menv',
      exp_eval menv env b (Cbool true) ->
      stmt_eval menv env ifTrue (menv', env') ->
      stmt_eval menv env (Ifte b ifTrue ifFalse) (menv', env')
| Iifte_false:
    forall b ifTrue ifFalse env' menv',
      exp_eval menv env b (Cbool false) ->
      stmt_eval menv env ifFalse (menv', env') ->
      stmt_eval menv env (Ifte b ifTrue ifFalse) (menv', env')
| Iskip:
    stmt_eval menv env Skip (menv, env)

with application (menv: memoryEnv)(env: constEnv) :
       step_fun -> const -> const * memoryEnv -> Prop :=
| Aapp:
    forall s_fun arg_v v res_env res_memory,
      stmt_eval menv (PM.add s_fun.(input) arg_v empty)
           s_fun.(body) (res_memory, res_env) ->
      PM.find s_fun.(output) res_env = Some(v) ->
      application menv env s_fun arg_v (v, res_memory).

Inductive run :
  memoryEnv -> constEnv -> stmt -> nat -> memoryEnv * constEnv -> Prop :=
| Run_empty:
    forall menvInit envInit stmt,
      run menvInit envInit stmt 0 (menvInit, envInit)
| Run_cons:
    forall menvInit menvInter menvFinal
           envInit envInter envFinal
           stmt n,
      stmt_eval menvInit envInit stmt (menvInter, envInter) ->
      run menvInter envInter stmt n (menvFinal, envFinal) ->
      run menvInit envInit stmt (S n) (menvFinal, envFinal).


Lemma stmt_eval_fold_left_shift:
  forall A f (xs:list A) iacc menv env menv' env',
    stmt_eval menv env
              (List.fold_left (fun i x => Comp (f x) i) xs iacc)
              (menv', env')
    <->
    exists menv'' env'',
      stmt_eval menv env
                (List.fold_left (fun i x => Comp (f x) i) xs Skip)
                (menv'', env'')
      /\
      stmt_eval menv'' env'' iacc (menv', env').
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
             | H:stmt_eval _ _ (Comp _ Skip) _ |- _ => inversion_clear H
             | H:stmt_eval _ _ Skip _ |- _ => inversion H; subst
             | H:stmt_eval _ _ (List.fold_left _ _ _) _ |- _ => apply IHxs in H
             | _ => eauto
             end.
      apply IHxs; eauto.
Qed.

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

Lemma stmt_eval_det:
  forall s menv env menv1 env1 menv2 env2,
    stmt_eval menv env s (menv1, env1)
    -> stmt_eval menv env s (menv2, env2)
    -> menv2 = menv1 /\ env2 = env1.
Proof.
  induction s.
  - intros menv env menv1 env1 menv2 env2 Hs1 Hs2.
    inversion Hs1; inversion Hs2.
    rewrite <- H7 in *.
    rewrite <- H1 in *.
    rewrite (exp_eval_det _ _ _ _ _ H8 H2) in *.
    rewrite H10 in H4.
    rewrite H4 in *.
    intuition.
  - intros menv env menv1 env1 menv2 env2 Hs1 Hs2.
    inversion Hs1; inversion Hs2.
    rewrite <- H3 in *.
    rewrite <- H9 in *.
    rewrite (exp_eval_det _ _ _ _ _ H8 H2) in *.
    rewrite H10 in H4.
    rewrite H4 in *.
    intuition.
  - intros menv env menv1 env1 menv2 env2 Hs1 Hs2.
    inversion Hs1; inversion Hs2.
    apply (IHs1 _ _ _ _ _ _ H5 H12).
    discriminate (exp_eval_det _ _ _ _ _ H1 H8).
    discriminate (exp_eval_det _ _ _ _ _ H1 H8).
    apply (IHs2 _ _ _ _ _ _ H5 H12).
  - intros menv env menv1 env1 menv2 env2 Hs1 Hs2.
    inversion Hs1; inversion Hs2.
    rewrite <- H11 in *.
    rewrite <- H2 in *.
    admit. (* TODO: handle node application *)
  - intros menv env menv1 env1 menv2 env2 Hs1 Hs2.
    inversion Hs1; inversion Hs2.
    pose proof (IHs1 _ _ _ _ _ _ H2 H8) as HR.
    destruct HR as [HR1 HR2].
    rewrite HR1, HR2 in *.
    pose proof (IHs2 _ _ _ _ _ _ H4 H10) as HR.
    destruct HR as [HR3 HR4].
    rewrite HR3, HR4 in *.
    intuition.
  - intros menv env menv1 env1 menv2 env2 Hs1 Hs2.
    inversion Hs1; inversion Hs2.
    rewrite <- H, <- H1, <- H0, <- H3.
    intuition.
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


