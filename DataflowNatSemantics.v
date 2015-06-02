Require Import Coq.FSets.FMapPositive.
Require Import Rustre.Common.
Require Import Rustre.DataflowSyntax.


Inductive value :=
  | abs
  | here (v : const).
Coercion here : const >-> value.
Definition venv := PositiveMap.t value.
Definition history := nat -> venv.
Definition global := PositiveMap.t node.


Inductive sem_var (H: history)(x: ident)(n: nat)(c: const): Prop :=
| Sv: 
      PositiveMap.find x (H(n)) = Some (here c) ->
      sem_var H x n c.
  
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
      sem_lexp H ce n abs ->
      sem_clock H ck n false ->
      sem_laexp H (LAexp ck ce) n abs
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
      sem_lexp H (Ewhen s x b) n abs.
               

Inductive sem_caexp (H: history): caexp -> nat -> value -> Prop :=
| SCtick:
    forall ck ce n c,
      sem_cexp H ce n c ->
      sem_clock H ck n true ->
      sem_caexp H (CAexp ck ce) n c
| SCabs:
    forall ck ce n,
      sem_cexp H ce n abs ->
      sem_clock H ck n false ->
      sem_caexp H (CAexp ck ce) n abs
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
    sem_equation G H (EqApp x f arg)
(*| SEqFby : forall H x (v : const) cae,
    (* First value: we return the value v from x = v fby cae *)
    (forall n, (forall n', n' < n -> sem_caexp H cae n' abs) -> sem_lexp H (Evar x) n v) ->
    (* Next values: we return the previous value of cae *)
    (forall n, exists n' (xv : const), n' < n /\ sem_lexp H (Evar x) n xv /\ sem_caexp H cae n' xv 
                                       /\ forall n'', n' < n'' < n -> sem_caexp H cae n'' abs) ->
    sem_equation G H (EqFby x v cae) *).
