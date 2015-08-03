Require Import Coq.FSets.FMapPositive.
Require Import Rustre.Common.
Require Import Rustre.DataflowSyntax.
Require Import SynchronousNat.

Definition history := PM.t stream.
Definition global := PM.t node.

Inductive sem_var (H: history)(x: ident)(n: nat)(c: const): Prop :=
| Sv:
    forall xs,
      PM.find x H = Some xs ->
      xs n = present c ->
      sem_var H x n c.

Inductive sem_var_value (H: history)(x: ident)(n: nat): value -> Prop :=
| Svv:
    forall xs,
      PM.find x H = Some xs ->
      sem_var_value H x n (xs n).

Inductive sem_clock (H: history): clock -> nat -> bool -> Prop :=
| Sbase:
    forall n,
      sem_clock H Cbase n true
| Son_tick:
    forall ck x c n,
      sem_clock H ck n true ->
      sem_var H x n (Cbool c) ->
      sem_clock H (Con ck x c) n true
| Son_abs1:
    forall ck x c n,
      sem_clock H ck n false ->
      sem_clock H (Con ck x c) n false
| Son_abs2:
    forall ck x c c' n,
      sem_clock H ck n true ->
      sem_var H x n (Cbool c') ->
      ~ (c = c') ->
      sem_clock H (Con ck x c) n false.

Inductive sem_laexp (H: history): laexp -> nat -> value -> Prop:=
| SLtick:
    forall ck ce n c,
      sem_lexp H ce n c ->
      sem_clock H ck n true ->
      sem_laexp H (LAexp ck ce) n c
| SLabs:
    forall ck ce n,
      sem_lexp H ce n absent ->
      sem_clock H ck n false ->
      sem_laexp H (LAexp ck ce) n absent
with sem_lexp (H: history): lexp -> nat -> value -> Prop :=
| Sconst: 
    forall c n,
      sem_lexp H (Econst c) n c
| Svar: 
    forall x c n,
      sem_var H x n c ->
      sem_lexp H (Evar x) n c
| Swhen_eq:
    forall s x b n c,
      sem_var H x n  (Cbool b) ->
      sem_laexp H s n c ->
      sem_lexp H (Ewhen s x b) n c
| Swhen_abs:
    forall s x b b' n,
      sem_var H x n (Cbool b') ->
      ~ (b = b') ->
      sem_lexp H (Ewhen s x b) n absent.
               

Inductive sem_caexp (H: history): caexp -> nat -> value -> Prop :=
| SCtick:
    forall ck ce n c,
      sem_cexp H ce n c ->
      sem_clock H ck n true ->
      sem_caexp H (CAexp ck ce) n c
| SCabs:
    forall ck ce n,
      sem_cexp H ce n absent ->
      sem_clock H ck n false ->
      sem_caexp H (CAexp ck ce) n absent
with sem_cexp (H: history): cexp -> nat -> value -> Prop :=
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


Inductive sem_equation (G: global) (H: history) : equation -> Prop :=
| SEqDef:
    forall x cae,
      (forall n, 
       exists v, sem_var H x n v
              /\ sem_caexp H cae n v) ->
      sem_equation G H (EqDef x cae)
| SEqApp:
    forall x f arg input output eqs,
      PositiveMap.find f G = Some (mk_node f input output eqs) ->
      (exists H' vi vo,
         forall n, sem_laexp H arg n vi
                /\ sem_lexp H (Evar x) n vo
                /\ sem_lexp H' (Evar input.(v_name)) n vi
                /\ sem_lexp H' (Evar output.(v_name)) n vo
                /\ List.Forall (sem_equation G H') eqs) ->
      sem_equation G H (EqApp x f arg)
| SEqFby:
    forall x xs v0 lae,
      (forall n, sem_laexp H lae n (xs n)) ->  (* TODO: Is this reasonable? *)
      (forall n, exists xs v, sem_var H x n v
                           /\ fbyR v0 xs n v) ->
      sem_equation G H (EqFby x v0 lae).

Inductive sem_held_equation (H: history) : equation -> nat -> const -> Prop :=
| SHEqDef:
    forall x cae n c,
      sem_var H x n c ->
      sem_held_equation H (EqDef x cae) n c
| SHEqApp:
    forall x f lae n c,
      sem_var H x n c ->
      sem_held_equation H (EqApp x f lae) n c
| SHEqFby0:
    forall x v0 lae,
      sem_held_equation H (EqFby x v0 lae) 0 v0
| SHEqFby_absent:
    forall x v0 lae n c,
      sem_var_value H x (S n) absent ->
      sem_held_equation H (EqFby x v0 lae) n c ->
      sem_held_equation H (EqFby x v0 lae) (S n) c
| SHEqFby_present:
    forall x v0 lae n c,
      sem_var_value H x (S n) (present c) ->
      sem_held_equation H (EqFby x v0 lae) (S n) c.

Definition sem_equations (G: global) (H: history) (eqs: list equation) : Prop :=
  List.Forall (sem_equation G H) eqs.

