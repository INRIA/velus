Require Import Coq.FSets.FMapPositive.
Require Import Rustre.Common.
Require Import Rustre.Minimp.
Require Import Rustre.DataflowSyntax.
Require Import Rustre.DataflowNatSemantics.
Require Import Rustre.Translation.

Module PM := PositiveMap.

(*
Lemma sem_laexp_some:
  forall H ck ce n v,
    sem_laexp H (LAexp ck ce) n (Some v) ->
    sem_lexp H ce n (Some v).
Proof.
  intros until v.
  inversion 1.
  apply H5.
Qed.
*)

Lemma compat_laexp:
  forall (H: history)(menv: memoryEnv)(env: valueEnv),
  forall (lae: laexp),
  forall (n: nat)(v: const),
    (forall x, PS.In x (freevar_laexp lae) ->
               PM.find x (H n) = Some (PM.find x env)) ->
    (sem_laexp H lae n (Some v)
    <->
    exp_eval menv env (translate_laexp lae) v).
Proof.
  intros until v.
  elim lae.
  intros k e.
  elim e.
  - intros c.
    split.
    + simpl.
      intro H1.
      inversion H1.
      inversion H6.
      constructor.
    + simpl.
      intro H1.
      inversion H1.
      constructor.
      constructor.

      sem_clock H k n true
                
      destruct H1.
    
    inversion 0.
    Search (_ <-> _).
    Check (iff_to_and).
    Locate "<->".
    Print iff.

           HIN HH.
  simpl.
  inversion 0.
Print econst.
  
  Check (econst).
  Check (SLtick).
  apply econst.
  case v.
  discriminate.
  
  intros HIN HH.

  intros c e.
  elim e.
  simpl.


  






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
