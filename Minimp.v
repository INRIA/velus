Require Import Coq.FSets.FMapPositive.
Require Import Rustre.Common.


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


Definition valueEnv : Set := PM.t const.

Definition empty: valueEnv := PM.empty const.

Inductive exp_eval (menv: memoryEnv)(env: valueEnv):
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

  
Inductive stmt_eval (menv: memoryEnv)(env: valueEnv) : 
  stmt -> memoryEnv * valueEnv -> Prop :=
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
      stmt_eval menv env ifTrue (env', menv') ->
      stmt_eval menv env (Ifte b ifTrue ifFalse) (env', menv')
| Iifte_false:
    forall b ifTrue ifFalse env' menv',
      exp_eval menv env b (Cbool false) ->
      stmt_eval menv env ifFalse (env', menv') ->
      stmt_eval menv env (Ifte b ifTrue ifFalse) (env', menv')

with application (menv: memoryEnv)(env: valueEnv) : 
       step_fun -> const -> const * memoryEnv -> Prop :=
| Aapp:
    forall s_fun arg_v v res_env res_memory,
      stmt_eval menv (PM.add s_fun.(input) arg_v empty)
           s_fun.(body) (res_memory, res_env) ->
      PM.find s_fun.(output) res_env = Some(v) ->
      application menv env s_fun arg_v (v, res_memory).

Inductive run :
  memoryEnv -> valueEnv -> stmt -> nat -> memoryEnv * valueEnv -> Prop :=
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

