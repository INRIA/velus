Require Import Coq.FSets.FMapPositive.
Require Import Rustre.Common.


(** * Imperative language *)

(** ** Syntax *)

Inductive exp : Set :=
  | Var : ident -> exp
  | Const : const -> exp.

Inductive stmt : Set :=
  | Assign : ident -> exp -> stmt
  | Ifte : ident -> stmt -> stmt -> stmt
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
                                            
Definition memoryEnv : Set := PositiveMap.t step_fun.
Definition valueEnv : Set := PositiveMap.t const.

Definition empty: valueEnv := PositiveMap.empty const.

Inductive exp_eval (menv: memoryEnv)(env: valueEnv):
  exp -> const -> Prop :=
| evar: 
    forall x v, 
      PositiveMap.find x env = Some(v) -> 
      exp_eval menv env (Var(x)) v
| econst:
    forall c ,
      exp_eval menv env (Const(c)) c.

  
Inductive stmt_eval (menv: memoryEnv)(env: valueEnv) : 
  stmt -> memoryEnv * valueEnv -> Prop :=
| Iassign:
    forall x e v env',
      exp_eval menv env e v ->
      PositiveMap.add x v env = env' ->
      stmt_eval menv env (Assign x e) (menv, env')
| Iapp:
    forall e v o y env' s_fun res_value res_memory,
      exp_eval menv env e v ->
      PositiveMap.find o menv = Some(s_fun) ->
      application menv empty s_fun v (res_value, res_memory) ->
      PositiveMap.add y res_value env  = env' ->
      stmt_eval menv env (Step_ap y o e) (menv, env')
| Icomp:
    forall a1 a2 env1 menv1 env2 menv2,
      stmt_eval menv env a1 (menv1, env1) ->
      stmt_eval menv1 env1 a2 (menv2, env2) ->
      stmt_eval menv env (Comp a1 a2) (menv2, env2)
| Iifte_true:
    forall x ifTrue ifFalse env' menv',
      PositiveMap.find x env = Some(Cbool true) ->
      stmt_eval menv env ifTrue (env', menv') ->
      stmt_eval menv env (Ifte x ifTrue ifFalse) (env', menv')
| Iifte_false:
    forall x ifTrue ifFalse env' menv',
      PositiveMap.find x env = Some(Cbool false) ->
      stmt_eval menv env ifFalse (env', menv') ->
      stmt_eval menv env (Ifte x ifTrue ifFalse) (env', menv')

with application (menv: memoryEnv)(env: valueEnv) : 
       step_fun -> const -> const * memoryEnv -> Prop :=
| Aapp:
    forall s_fun arg_v v res_env res_memory,
      stmt_eval menv (PositiveMap.add s_fun.(input) arg_v empty)
           s_fun.(body) (res_memory, res_env) ->
      PositiveMap.find s_fun.(output) res_env = Some(v) ->
      application menv env s_fun arg_v (v, res_memory).

Inductive run :
  memoryEnv -> valueEnv -> stmt -> nat -> valueEnv * memoryEnv -> Prop :=
| Run_empty:
    forall menvInit envInit stmt,
      run menvInit envInit stmt 0 (envInit, menvInit)
| Run_cons:
    forall menvInit menvInter menvFinal
           envInit envInter envFinal
           stmt n,
      stmt_eval menvInit envInit stmt (menvInter, envInter) ->
      run menvInter envInter stmt n (envFinal, menvFinal) ->
      run menvInit envInit stmt (S n) (envFinal, menvFinal).
