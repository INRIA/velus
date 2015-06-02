Require Import Coq.FSets.FMapPositive.
Require Import List.
Require Import Rustre.Common.
Require Import Rustre.DataflowSyntax.


(** *  Dataflow semantics with lists  **)

(* Idea?: clocks -> instantaneous semantics
          expressions -> list semantics *)
Inductive value :=
  | abs
  | here (v : const).
Coercion here : const >-> value.

Definition venv := PositiveMap.t value.
Definition history := list venv.

Definition alls {A B} (v : B) (l : list A) := List.map (fun _ => v) l.


Definition sem_var (H : history) (x : ident) (cl : list value) : Prop :=
  List.map (PositiveMap.find x) H = List.map (@Some _) cl.

(** **  Clock semantics  **)

(** ***  Clock semantics for one instant  **)

Inductive instant_sem_clock (env : venv) : clock -> bool -> Prop :=
| base: instant_sem_clock env Cbase true
| on_tick:
    forall ck x b,
      instant_sem_clock env ck true ->
      PositiveMap.find x env = Some (here (Cbool b)) -> 
      instant_sem_clock env (Con ck x b) true
| on_abs1:
    forall ck x b,
      instant_sem_clock env ck false ->
      instant_sem_clock env (Con ck x b) false
| on_abs2:
    forall ck x c c',
      instant_sem_clock env ck true ->
      PositiveMap.find x env = Some (here c') -> 
      Cbool c <> c' ->
      instant_sem_clock env (Con ck x c) false.

(** ***  Lifting to lists  **)

Inductive sem_clock : history -> clock -> list bool -> Prop :=
  | Snil : forall ck, sem_clock nil ck nil
  | Scons : forall env H ck b bl, 
      instant_sem_clock env ck b -> sem_clock H ck bl -> sem_clock (env :: H) ck (b :: bl).

Inductive sem_laexp (H : history) : laexp -> value -> Prop :=
  | Stick : forall ck ce c,
      sem_lexp H ce c ->
      sem_clock H ck true ->
      sem_laexp H (LAexp ck ce) (here c)
  | Sabs : forall ck ce,
      sem_lexp H ce None ->
      sem_clock H ck false ->
      sem_laexp H (LAexp ck ce) None

with sem_lexp (H: history): lexp -> value -> Prop :=
| Sconst: 
    forall c n,
      sem_lexp H (Econst c) n (Some c)
| Svar: 
    forall x c n,
      sem_var H x n c ->
      sem_lexp H (Evar x) n (Some c)
| Swhen_eq:
    forall s x b n c,
      sem_var H x n  (Cbool b) ->
      sem_laexp H s n c ->
      sem_lexp H (Ewhen s x b) n c
| Swhen_abs:
    forall s x b b' n,
      sem_var H x n (Cbool b') ->
      ~ (b = b') ->
      sem_lexp H (Ewhen s x b) n None.
               

Inductive sem_caexp (H: history): caexp -> nat -> value -> Prop :=
| SCtick:
    forall ck ce n c,
      sem_cexp H ce n (Some c) ->
      sem_clock H ck n true ->
      sem_caexp H (CAexp ck ce) n (Some c)
| SCabs:
    forall ck ce n,
      sem_cexp H ce n None ->
      sem_clock H ck n false ->
      sem_caexp H (CAexp ck ce) n None
with sem_cexp (H: history): cexp -> nat -> option const -> Prop :=
| Smerge_true:
    forall x t f n c,
      sem_var H x n (Cbool true) ->
      sem_caexp H t n c ->
      sem_cexp H (Emerge x t f) n c
| Smerge_false:
    forall x t f n c,
      sem_var H x n (Cbool false) ->
      sem_caexp H f n c ->
      sem_cexp H (Emerge x t f) n c
| Sexp:
    forall e n c,
      sem_lexp H e n c ->
      sem_cexp H (Eexp e) n c.

Inductive sem_equation (G: global): history -> equation -> Prop :=
| SEqDef:
    forall H x cae,
      (forall n, 
       exists v, sem_lexp H (Evar x) n v
              /\ sem_caexp H cae n v) ->
      sem_equation G H (EqDef x cae)
| SEqApp:
    forall H x f arg input output eqs,
      PositiveMap.find f G = Some (mk_node f input output eqs) ->
      (exists H' vi vo,
         forall n, sem_laexp H arg n vi
                /\ sem_lexp H (Evar x) n vo
                /\ sem_lexp H' (Evar input.(v_name)) n vi
                /\ sem_lexp H' (Evar output.(v_name)) n vo
                /\ List.Forall (sem_equation G H') eqs) ->
    sem_equation G H (EqApp x f arg).







Definition sem_var env x c := PositiveMap.find x env = Some (here c).
Check Con. Print const.
Inductive Lsem_clock (env : Lvenv) : clock -> bool -> Prop :=
| Lbase: Lsem_clock env Cbase true
| Lon_tick:
    forall ck x b,
      Lsem_clock env ck true ->
      Lsem_var env x (Cbool b) -> 
      Lsem_clock env (Con ck x b) true
| Lon_abs1:
    forall ck x b,
      Lsem_clock env ck false ->
      Lsem_clock env (Con ck x b) false
| Lon_abs2:
    forall ck x c c',
      Lsem_clock env ck true ->
      Lsem_var env x c' -> 
      Cbool c <> c' ->
      Lsem_clock env (Con ck x c) false.

Inductive Lsem_laexp (env : Lvenv) : laexp -> Lvalue -> Prop :=
| Ltick :
    forall ck ce c,
      Lsem_lexp env ce (here c) ->
      Lsem_clock env ck true ->
      Lsem_laexp env (LAexp ck ce) c
| Labs :
    forall ck ce,
      Lsem_lexp env ce abs ->
      Lsem_clock env ck false ->
      Lsem_laexp env (LAexp ck ce) abs

with Lsem_lexp (env : Lvenv) : lexp -> Lvalue -> Prop :=
| Lconst : 
    forall c,
      Lsem_lexp env (Econst c) (here c)
| Lvar :
    forall x c,
      PositiveMap.find x env = Some c ->
      Lsem_lexp env (Evar x) c
| Lwhen_eq :
    forall s x b c,
      Lsem_var env x (Cbool b) ->
      Lsem_laexp env s c ->
      Lsem_lexp env (Ewhen s x b) c
| Lwhen_abs :
    forall s x b b',
      Lsem_var env x (Cbool b') ->
      b <> b' ->
      Lsem_lexp env (Ewhen s x b) abs.

Inductive Lsem_caexp (env : Lvenv) : caexp -> Lvalue -> Prop :=
| LCtick:
    forall ck ce c,
      Lsem_cexp env ce (here c) ->
      Lsem_clock env ck true ->
      Lsem_caexp env (CAexp ck ce) (here c)
| LCabs:
    forall ck ce,
      Lsem_cexp env ce abs ->
      Lsem_clock env ck false ->
      Lsem_caexp env (CAexp ck ce) abs
with Lsem_cexp (env: Lvenv) : cexp -> Lvalue -> Prop :=
| Lmerge_true:
    forall x t f c,
      Lsem_var env x (Cbool true) ->
      Lsem_caexp env t c ->
      Lsem_cexp env (Emerge x t f) c
| Lmerge_false:
    forall x t f c,
      Lsem_var env x (Cbool false) ->
      Lsem_caexp env t c ->
      Lsem_cexp env (Emerge x t f) c
| Lexp:
    forall e c,
      Lsem_lexp env e c ->
      Lsem_cexp env (Eexp e) c.

Inductive Lsem_equation (env: Lvenv) : equation -> Prop :=
| LEqDef:
    forall x cae,
      (exists v, Lsem_lexp env (Evar x) v
              /\ Lsem_caexp env cae v) ->
      Lsem_equation env (EqDef x cae)
| LEqApp:
    forall x f arg,
      (* TODO: what is the semantics of node application? *)
    Lsem_equation env (EqApp x f arg).

Definition Lsem_equations (env : Lvenv) (eqs : list equation) : Prop :=
  List.Forall (Lsem_equation env) eqs.

Inductive Lsem_node (env : Lvenv) : node -> Prop :=
| Lnode:
    forall name input output eqs env' s_input s_output,
      PositiveMap.add input.(v_name) s_input 
       (PositiveMap.add output.(v_name) s_output env) = env' ->
      Lsem_equations env' eqs ->
      Lsem_node env (mk_node name input output eqs).
