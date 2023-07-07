From Velus Require Import Common.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import FunctionalEnvironment.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import CoreExpr.CEIsFree.
From Coq Require Import List.

(** * Free variables *)

(**

The predicate [Is_free x t : Prop] states that the variable [x] is
used in the term [t]. If [t] is an equation, this collects the
variables in the right-hand side of the equation. In particular, if
[t] is [x = v0 fby x], [x] will (perhaps confusingly) be free.

 *)

Module Type ISFREE
       (Ids          : IDS)
       (Op           : OPERATORS)
       (OpAux        : OPERATORS_AUX Ids Op)
       (Import Cks   : CLOCKS        Ids Op OpAux)
       (Import CESyn : CESYNTAX      Ids Op OpAux Cks)
       (Import Syn   : NLSYNTAX Ids  Op OpAux Cks CESyn)
       (Import CEIsF : CEISFREE Ids  Op OpAux Cks CESyn).

  Inductive Is_free_in_eq : var_last -> equation -> Prop :=
  | FreeEqDef:
      forall x ck ce i,
        Is_free_in_arhs i ck ce ->
        Is_free_in_eq i (EqDef x ck ce)
  | FreeEqLast:
      forall x ty ck c0 xrs i,
        Is_free_in_clock i ck \/
        Exists (fun '(xr, ckr) => i = xr \/ Is_free_in_clock i ckr) xrs ->
        Is_free_in_eq (Var i) (EqLast x ty ck c0 xrs)
  | FreeEqApp:
      forall x f ck les xrs i,
        Is_free_in_aexps i ck les \/
        Exists (fun '(xr, ckr) => i = Var xr \/ exists y, i = Var y /\ Is_free_in_clock y ckr) xrs ->
        Is_free_in_eq i (EqApp x ck f les xrs)
  | FreeEqFby:
      forall x v ck le xrs i,
        Is_free_in_aexp i ck le \/
        Exists (fun '(xr, ckr) => i = Var xr \/ exists y, i = Var y /\ Is_free_in_clock y ckr) xrs ->
        Is_free_in_eq i (EqFby x ck v le xrs).

  Global Hint Constructors Is_free_in_clock Is_free_in_exp
       Is_free_in_aexp Is_free_in_aexps Is_free_in_cexp
       Is_free_in_rhs Is_free_in_arhs Is_free_in_eq : nlfree.

  (** * Decision procedure *)

  Definition free_in_equation (eq: equation) (fvs: (PS.t * PS.t)) : (PS.t * PS.t) :=
    match eq with
    | EqDef _ ck cae      => free_in_arhs ck cae fvs
    | EqLast _ _ ck _ xrs =>
        (fold_left (fun fvs '(xr, ckr) => PS.add xr (free_in_clock ckr fvs)) xrs (free_in_clock ck (fst fvs)), snd fvs)
    | EqApp _ ck f laes xrs =>
        let fvs := free_in_aexps ck laes fvs in
        (fold_left (fun fvs '(xr, ckr) => PS.add xr (free_in_clock ckr fvs)) xrs (fst fvs), (snd fvs))
    | EqFby _ ck v lae xrs =>
        let fvs := free_in_aexp ck lae fvs in
        (fold_left (fun fvs '(xr, ckr) => PS.add xr (free_in_clock ckr fvs)) xrs (fst fvs), (snd fvs))
    end.

  (** * Specification lemmas *)

  Lemma free_in_fold_left_spec : forall xr fvs x,
    PS.In x (fold_left (fun fvs '(xr, ckr) => PS.add xr (free_in_clock ckr fvs)) xr fvs) <->
    PS.In x fvs \/ Exists (fun '(xr, ckr) => x = xr \/ Is_free_in_clock x ckr) xr.
  Proof.
    intros *; split; revert fvs.
    1,2:induction xr as [|(?&?)]; intros * Hin; simpl in *; auto.
    - apply IHxr in Hin as [Hin|]; auto.
      rewrite PSF.add_iff, free_in_clock_spec in Hin.
      destruct Hin as [|[|]]; auto; right; left;
        rewrite PSF.add_iff, free_in_clock_spec'; auto.
    - destruct Hin as [|Hin]; auto. inv Hin.
    - apply IHxr. rewrite PSF.add_iff, free_in_clock_spec.
      destruct Hin; auto.
      inv H; auto. destruct H1; auto.
  Qed.

  Lemma free_in_equation_spec1: forall x eq m,
      PS.In x (fst (free_in_equation eq m))
      <-> (Is_free_in_eq (Var x) eq \/ PS.In x (fst m)).
  Proof.
    intros. unfold free_in_equation. cases; simpl.
    all:rewrite ?free_in_fold_left_spec, ?free_in_aexp_spec1, ?free_in_aexps_spec1, ?free_in_arhs_spec1, ?free_in_clock_spec.
    all:(split; intros [|]; try (take (Is_free_in_eq _ _) and inv it);
         repeat (take (_ \/ _) and destruct it); auto with nlfree).
    1,3:left; constructor; right; solve_Exists; take (_ \/ _) and destruct it; subst; eauto.
    all:right; solve_Exists; take (_ \/ _) and destruct it as [Eq|]; [|destruct_conjs]; take (Var _ = Var _) and inv it; eauto.
  Qed.

  Corollary free_in_equation_spec1': forall x eq,
      PS.In x (fst (free_in_equation eq (PS.empty, PS.empty)))
      <-> Is_free_in_eq (Var x) eq.
  Proof.
    intros. rewrite free_in_equation_spec1, PSF.empty_iff; simpl.
    split; [intros [|[]]|intros]; auto.
  Qed.

  Lemma free_in_equation_spec2: forall x eq m,
      PS.In x (snd (free_in_equation eq m))
      <-> (Is_free_in_eq (Last x) eq \/ PS.In x (snd m)).
  Proof.
    intros. unfold free_in_equation. cases; simpl.
    all:rewrite ?free_in_fold_left_spec, ?free_in_aexp_spec2, ?free_in_aexps_spec2, ?free_in_arhs_spec2, ?free_in_clock_spec.
    all:(split; auto; intros [|]; try (take (Is_free_in_eq _ _) and inv it);
         repeat (take (_ \/ _) and destruct it); auto with nlfree).
    1-2:simpl_Exists; take (_ \/ _) and destruct it; destruct_conjs; congruence.
  Qed.

  Corollary free_in_equation_spec2': forall x eq,
      PS.In x (snd (free_in_equation eq (PS.empty, PS.empty)))
      <-> Is_free_in_eq (Last x) eq.
  Proof.
    intros. rewrite free_in_equation_spec2, PSF.empty_iff; simpl.
    split; [intros [|[]]|intros]; auto.
  Qed.

End ISFREE.

Module IsFreeFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks   : CLOCKS        Ids Op OpAux)
       (CESyn : CESYNTAX      Ids Op OpAux Cks)
       (Syn   : NLSYNTAX Ids  Op OpAux Cks CESyn)
       (CEIsF : CEISFREE Ids  Op OpAux Cks CESyn)
       <: ISFREE Ids Op OpAux Cks CESyn Syn CEIsF.
  Include ISFREE Ids Op OpAux Cks CESyn Syn CEIsF.
End IsFreeFun.
