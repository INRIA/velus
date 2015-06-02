Require Import Coq.FSets.FMapPositive.
Require Import Rustre.Common.
Require Import Rustre.Minimp.
Require Import Rustre.DataflowSyntax.
Require Import Rustre.DataflowNatSemantics.
Require Import Rustre.Translation.


(* * Compatibility & equivalences *)


Definition submap (rho: valueEnv)(R: venv): Prop :=
  forall x, PositiveMap.In x rho -> PositiveMap.In x R.

Definition compat_env (rho: valueEnv)(R: venv): Prop :=
  submap rho R /\ 
  forall x,  PositiveMap.In x rho ->
             forall c, PositiveMap.find x R = Some (here c) ->
             PositiveMap.find x rho = Some c.

Definition compat_caexp (ae: caexp)(s: stmt)(m: memoryEnv) :=
  match ae with
    | CAexp ck ce =>
      forall H n v rho,
        sem_caexp H ae n v ->
        compat_env rho (H n) ->
        sem_clock H ck n true -> 
        (* TODO: there seems to be a problem with Def.12 *)
        False
  end.

Definition compat_eqns (eqns: list equation)(m: memoryEnv)(l: stmt): Prop. Admitted.

(*  compat_eqns eqns  ??? *)
Definition compat_wf (eqns: list equation)(c: class_def): Prop. Admitted.
