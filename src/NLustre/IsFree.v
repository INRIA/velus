From Velus Require Import Common.
From Velus Require Import Operators.
From Velus Require Import Clocks.
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

  Inductive Is_free_in_eq : ident -> equation -> Prop :=
  | FreeEqDef:
      forall x ck ce i,
        Is_free_in_caexp i ck ce ->
        Is_free_in_eq i (EqDef x ck ce)
  | FreeEqApp:
      forall x f ck les xrs i,
        Is_free_in_aexps i ck les \/
        Exists (fun '(xr, ckr) => xr = i \/ Is_free_in_clock i ckr) xrs ->
        Is_free_in_eq i (EqApp x ck f les xrs)
  | FreeEqFby:
      forall x v ck le xrs i,
        Is_free_in_aexp i ck le \/
        Exists (fun '(xr, ckr) => xr = i \/ Is_free_in_clock i ckr) xrs ->
        Is_free_in_eq i (EqFby x ck v le xrs).

  Hint Constructors Is_free_in_clock Is_free_in_exp
       Is_free_in_aexp Is_free_in_aexps Is_free_in_cexp
       Is_free_in_caexp Is_free_in_eq.

  (** * Decision procedure *)


  Fixpoint free_in_equation (eq: equation) (fvs: PS.t) : PS.t :=
    match eq with
    | EqDef _ ck cae      => free_in_caexp ck cae fvs
    | EqApp _ ck f laes xrs =>
      let fvs := free_in_aexps ck laes fvs in
      fold_left (fun fvs '(xr, ckr) => PS.add xr (free_in_clock ckr fvs)) xrs fvs
    | EqFby _ ck v lae xrs =>
      let fvs := free_in_aexp ck lae fvs in
      fold_left (fun fvs '(xr, ckr) => PS.add xr (free_in_clock ckr fvs)) xrs fvs
    end.

  (** * Specification lemmas *)

  Lemma free_in_fold_left_spec : forall xr fvs x,
    PS.In x (fold_left (fun fvs '(xr, ckr) => PS.add xr (free_in_clock ckr fvs)) xr fvs) <->
    PS.In x fvs \/ Exists (fun '(xr, ckr) => xr = x \/ Is_free_in_clock x ckr) xr.
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

  Lemma free_in_equation_spec:
    forall x eq m, PS.In x (free_in_equation eq m)
                   <-> (Is_free_in_eq x eq \/ PS.In x m).
  Proof.
    Local Ltac aux :=
      repeat (simpl in *;
              match goal with
              | o:option (_ * _) |- _ => destruct o as [[? ?]|]
              | H:Is_free_in_eq _ _ |- _ => inversion_clear H
              | H:PS.In _ (free_in_caexp _ _ _) |- _ => rewrite free_in_caexp_spec in H
              | H:PS.In _ (free_in_aexp _ _ _) |- _ => rewrite free_in_aexp_spec in H
              | H:PS.In _ (free_in_aexps _ _ _) |- _ => rewrite free_in_aexps_spec in H
              | H:PS.In _ (free_in_clock _ _) |- _  => rewrite free_in_clock_spec in H
              | H:PS.In _ (PS.add _ _) |- _ => rewrite PS.add_spec in H
              | H:PS.In _ (fold_left _ _ _) |- _ => rewrite free_in_fold_left_spec in H
              | |- context [PS.In _ (free_in_caexp _ _ _)] => rewrite free_in_caexp_spec
              | |- context [PS.In _ (free_in_aexp _ _ _)] => rewrite free_in_aexp_spec
              | |- context [PS.In _ (free_in_aexps _ _ _)] => rewrite free_in_aexps_spec
              | |- context [PS.In _ (free_in_clock _ _)] => rewrite free_in_clock_spec
              | |- context [PS.In _ (PS.add _ _)] => rewrite PS.add_spec
              | |- context [PS.In _ (fold_left _ _ _)] => rewrite free_in_fold_left_spec
              | H:_ \/ _ |- _ => destruct H
              end; eauto).

    destruct eq; split; intro H; aux; simpl in *.
  Qed.

  Lemma free_in_equation_spec':
    forall x eq, PS.In x (free_in_equation eq PS.empty)
               <-> Is_free_in_eq x eq.
  Proof.
    intros; rewrite (free_in_equation_spec x eq PS.empty).
    intuition.
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
