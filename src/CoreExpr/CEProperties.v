From Velus Require Import Common.
From Velus Require Import Operators.
From Velus Require Import Environment.
From Velus Require Import Clocks.
From Velus Require Export CoreExpr.Stream.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import CoreExpr.CETyping.
From Velus Require Import CoreExpr.CESemantics.
From Velus Require Import CoreExpr.CEIsFree.

Import List.

(** * Properties of Core Expressions *)

Module Type CEPROPERTIES
       (Ids          : IDS)
       (Op           : OPERATORS)
       (       OpAux : OPERATORS_AUX   Op)
       (Import Syn   : CESYNTAX        Op)
       (       Str   : STREAM          Op OpAux)
       (Import Sem   : CESEMANTICS Ids Op OpAux Syn Str)
       (Import Typ   : CETYPING    Ids Op       Syn)
       (Import IsF   : CEISFREE    Ids Op       Syn).

  Lemma sem_var_instant_switch_env:
    forall R R' x v,
      Env.find x R = Env.find x R' ->
      sem_var_instant R x v <-> sem_var_instant R' x v.
  Proof.
    intros; split; unfold sem_var_instant;
      take (Env.find x R = _) and rewrite it; auto.
  Qed.

  Lemma sem_exp_instant_switch_env:
    forall b R R' e v,
      (forall x, Is_free_in_exp x e -> Env.find x R = Env.find x R') ->
      sem_exp_instant b R e v <-> sem_exp_instant b R' e v.
  Proof.
    induction e; intros v RRx.
    - (* Econst *)
      split; inversion 1; destruct b; eauto using sem_exp_instant.
    - (* Evar *)
      split; inversion_clear 1;
        take (sem_var_instant _ _ _) and eapply sem_var_instant_switch_env in it;
        eauto using sem_exp_instant.
      symmetry; auto.
    - (* Ewhen *)
      split; inversion_clear 1;
        take (sem_var_instant _ _ _) and eapply sem_var_instant_switch_env in it;
        take (sem_exp_instant _ _ _ _)
             and (erewrite IHe in it || rewrite <-IHe in it);
        eauto using sem_exp_instant;
        symmetry; auto.
    - (* Eunop *)
      split; inversion_clear 1;
        take (sem_exp_instant _ _ _ _)
             and (erewrite IHe in it || rewrite <-IHe in it);
        eauto using sem_exp_instant.
    - (* Ebinop *)
      split; inversion_clear 1;
        take (sem_exp_instant _ _ e1 _)
             and (erewrite IHe1 in it || rewrite <-IHe1 in it);
        take (sem_exp_instant _ _ e2 _)
             and (erewrite IHe2 in it || rewrite <-IHe2 in it);
        eauto using sem_exp_instant.
  Qed.

  Lemma sem_exps_instant_switch_env:
    forall b R R' es vs,
      (forall x, Exists (Is_free_in_exp x) es -> Env.find x R = Env.find x R') ->
      sem_exps_instant b R es vs <-> sem_exps_instant b R' es vs.
  Proof.
    induction es as [|e es IH]. now split; inversion 1; subst; auto.
    intros vs HH. destruct vs. now split; inversion 1.
    repeat rewrite sem_exps_instant_cons.
    rewrite IH; auto.
    now rewrite sem_exp_instant_switch_env with (R':=R'); auto.
  Qed.

  Lemma sem_cexp_instant_switch_env:
    forall b R R' e v,
      (forall x, Is_free_in_cexp x e -> Env.find x R = Env.find x R') ->
      sem_cexp_instant b R e v <-> sem_cexp_instant b R' e v.
  Proof.
    induction e; intros v RRx.
    - (* Emerge *)
      split; inversion_clear 1;
        take (sem_cexp_instant _ _ e1 _)
           and (erewrite IHe1 in it || rewrite <-IHe1 in it);
        take (sem_cexp_instant _ _ e2 _)
             and (erewrite IHe2 in it || rewrite <-IHe2 in it);
        take (sem_var_instant _ _ _) and eapply sem_var_instant_switch_env in it;
        eauto using sem_cexp_instant;
        symmetry; auto.
    - (* Eite *)
      split; inversion_clear 1;
        take (sem_cexp_instant _ _ e2 _)
           and (erewrite IHe1 in it || rewrite <-IHe1 in it);
        take (sem_cexp_instant _ _ e3 _)
             and (erewrite IHe2 in it || rewrite <-IHe2 in it);
        take (sem_exp_instant _ _ _ _) and
             eapply sem_exp_instant_switch_env in it;
        eauto using sem_cexp_instant;
        symmetry; auto.
    - (* Eexp *)
      split; inversion_clear 1;
        take (sem_exp_instant _ _ _ _) and
             eapply sem_exp_instant_switch_env in it;
        eauto using sem_cexp_instant;
        symmetry; auto.
  Qed.

  Lemma sem_clock_instant_switch_env:
    forall b R R' ck v,
      (forall x, Is_free_in_clock x ck -> Env.find x R = Env.find x R') ->
      sem_clock_instant b R ck v <-> sem_clock_instant b R' ck v.
  Proof.
    induction ck; intros v RRx.
    - (* Cbase *)
      split; inversion_clear 1; eauto using sem_clock_instant.
    - (* Con *)
      split; inversion_clear 1;
        take (sem_clock_instant _ _ _ _) and apply IHck in it;
        take (sem_var_instant _ _ _) and eapply sem_var_instant_switch_env in it;
        eauto using sem_clock_instant;
        symmetry; auto.
  Qed.

  Lemma sem_aexp_instant_switch_env:
    forall b R R' ck e v,
      (forall x, Is_free_in_clock x ck \/ Is_free_in_exp x e ->
            Env.find x R = Env.find x R') ->
      sem_aexp_instant b R ck e v <-> sem_aexp_instant b R' ck e v.
  Proof.
    intros * RRx. split.
    - inversion_clear 1;
        take (sem_exp_instant _ _ _ _)
             and apply sem_exp_instant_switch_env with (R':=R') in it; auto;
          take (sem_clock_instant _ _ _ _)
               and apply sem_clock_instant_switch_env with (R':=R') in it; eauto;
            constructor; auto.
    - inversion_clear 1;
        take (sem_exp_instant _ _ _ _)
             and apply sem_exp_instant_switch_env with (R:=R) in it; auto;
          take (sem_clock_instant _ _ _ _)
               and apply sem_clock_instant_switch_env with (R:=R) in it; eauto;
            constructor; auto.
  Qed.

  Lemma sem_caexp_instant_switch_env:
    forall b R R' ck e v,
      (forall x, Is_free_in_clock x ck \/ Is_free_in_cexp x e ->
            Env.find x R = Env.find x R') ->
      sem_caexp_instant b R ck e v <-> sem_caexp_instant b R' ck e v.
  Proof.
    intros * RRx. split.
    - inversion_clear 1;
        take (sem_cexp_instant _ _ _ _)
             and apply sem_cexp_instant_switch_env with (R':=R') in it; auto;
          take (sem_clock_instant _ _ _ _)
               and apply sem_clock_instant_switch_env with (R':=R') in it; eauto;
            constructor; auto.
    - inversion_clear 1;
        take (sem_cexp_instant _ _ _ _)
             and apply sem_cexp_instant_switch_env with (R:=R) in it; auto;
          take (sem_clock_instant _ _ _ _)
               and apply sem_clock_instant_switch_env with (R:=R) in it; eauto;
            constructor; auto.
  Qed.

  Ltac solve_switch_env_obligation :=
    match goal with
    | [Henv: Env.refines ?R ?env1 ?env2 |- forall x, ?P -> Env.find x ?env2 = Env.find x ?Env1] =>
      let y := fresh "y" in
      let H := fresh "H" in
      intros y H; try match type of H with _ \/ _ => destruct H end;
      (apply Env.refines_orel_find with (x0:=y) in Henv; auto;
       symmetry; apply orel_eq, Henv)
    | [Henv: Env.refines ?R ?env1 ?env2 |- Env.find ?x ?env2 = Env.find ?x ?Env1] =>
      apply Env.refines_orel_find with (x0:=x) in Henv; auto;
      symmetry; apply orel_eq, Henv
    end.

  (** Well-typed expressions and free variables *)

  Lemma Is_free_in_wt_exp:
    forall (xs : list (ident * (Op.type * clock))) x e,
      Is_free_in_exp x e ->
      wt_exp (idty xs) e ->
      InMembers x xs.
  Proof.
    induction e; inversion_clear 1; inversion_clear 1; eauto using idty_InMembers.
    take (_ \/ _) and destruct it; auto.
  Qed.

  Lemma Is_free_in_wt_clock:
    forall (xs : list (ident * (Op.type * clock))) x ck,
      Is_free_in_clock x ck ->
      wt_clock (idty xs) ck ->
      InMembers x xs.
  Proof.
    induction ck; inversion_clear 1; inversion_clear 1;
      eauto using idty_InMembers.
  Qed.

  Lemma Is_free_in_wt_aexps:
    forall (xs : list (ident * (Op.type * clock))) x ck es,
      Is_free_in_aexps x ck es ->
      Forall (wt_exp (idty xs)) es ->
      wt_clock (idty xs) ck ->
      InMembers x xs.
  Proof.
    intros * Fs WT WC.
    inv Fs; eauto using Is_free_in_wt_clock.
    take (Exists (Is_free_in_exp _) _) and
         apply Exists_exists in it as (? & Ix & ?).
    eapply Forall_forall in WT; eauto using Is_free_in_wt_exp.
  Qed.

  Lemma Is_free_in_wt_cexp:
    forall (xs : list (ident * (Op.type * clock))) x e,
      Is_free_in_cexp x e ->
      wt_cexp (idty xs) e ->
      InMembers x xs.
  Proof.
    induction e; inversion_clear 1; inversion_clear 1; auto;
      eauto using Is_free_in_wt_exp, idty_InMembers.
  Qed.

  Lemma Is_free_in_wt_aexp:
    forall (xs : list (ident * (Op.type * clock))) x ck e,
      Is_free_in_aexp x ck e ->
      wt_exp (idty xs) e ->
      wt_clock (idty xs) ck ->
      InMembers x xs.
  Proof.
    intros * Fx WTe WTc.
    inv Fx; eauto using Is_free_in_wt_exp, Is_free_in_wt_clock.
  Qed.

  Lemma Is_free_in_wt_caexp:
    forall (xs : list (ident * (Op.type * clock))) x ck e,
      Is_free_in_caexp x ck e ->
      wt_cexp (idty xs) e ->
      wt_clock (idty xs) ck ->
      InMembers x xs.
  Proof.
    intros * Fx WTe WTc.
    inv Fx; eauto using Is_free_in_wt_cexp, Is_free_in_wt_clock.
  Qed.

End CEPROPERTIES.

Module CEProperties
       (Ids          : IDS)
       (Op           : OPERATORS)
       (       OpAux : OPERATORS_AUX   Op)
       (Import Syn   : CESYNTAX        Op)
       (       Str   : STREAM          Op OpAux)
       (Import Sem   : CESEMANTICS Ids Op OpAux Syn Str)
       (Import Typ   : CETYPING    Ids Op       Syn)
       (Import IsF   : CEISFREE    Ids Op       Syn)
       <: CEPROPERTIES Ids Op OpAux Syn Str Sem Typ IsF.
  Include CEPROPERTIES Ids Op OpAux Syn Str Sem Typ IsF.
End CEProperties.
