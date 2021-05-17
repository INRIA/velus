From Velus Require Import Common.
From Velus Require Import Operators.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import Stc.StcSyntax.
From Velus Require Import Clocks.

From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Module Type STCISSYSTEM
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks   : CLOCKS    Ids Op OpAux)
       (Import CESyn : CESYNTAX  Ids Op OpAux Cks)
       (Import Syn   : STCSYNTAX Ids Op OpAux Cks CESyn).

  Inductive Is_system_in_tc : ident -> trconstr -> Prop :=
  | Is_system_inTcStep:
      forall s ys ck rst f es,
        Is_system_in_tc f (TcStep s ys ck rst f es)
  | Is_system_inTcInstReset:
      forall s ck f,
        Is_system_in_tc f (TcInstReset s ck f).

  Definition Is_system_in (f: ident) (tcs: list trconstr) : Prop :=
    Exists (Is_system_in_tc f) tcs.

  Lemma not_Is_system_in_cons:
    forall b tc tcs,
      ~ Is_system_in b (tc :: tcs) <-> ~Is_system_in_tc b tc /\ ~Is_system_in b tcs.
  Proof.
    split; intro HH.
    - split; intro; apply HH; unfold Is_system_in; intuition.
    - destruct HH; inversion_clear 1; intuition.
  Qed.

  Lemma steps_iresets_of_Is_system_in:
    forall tcs b,
      Is_system_in b tcs <-> In b (map snd (steps_of tcs ++ iresets_of tcs)).
  Proof.
    induction tcs as [|[]]; simpl.
    - split; try contradiction; inversion 1.
    - setoid_rewrite <-IHtcs; split; try (right; auto);
        inversion_clear 1 as [?? IsSystem|]; auto; inv IsSystem.
    - setoid_rewrite <-IHtcs; split; try (right; auto);
        inversion_clear 1 as [?? IsSystem|]; auto; inv IsSystem.
    - setoid_rewrite <-IHtcs; split; try (right; auto);
        inversion_clear 1 as [?? IsSystem|]; auto; inv IsSystem.
    - split; rewrite map_app, in_app; simpl.
      + inversion_clear 1 as [?? IsSystem|?? Systems]; try inv IsSystem; auto.
        apply IHtcs in Systems.
        rewrite map_app, in_app in Systems; destruct Systems; auto.
      + intros [?|[?|?]].
        * right; apply IHtcs; rewrite map_app, in_app; auto.
        * subst; left; constructor.
        * right; apply IHtcs; rewrite map_app, in_app; auto.
    - split; rewrite map_app, in_app; simpl.
      + inversion_clear 1 as [?? IsSystem|?? Systems]; try inv IsSystem; auto.
        apply IHtcs in Systems.
        rewrite map_app, in_app in Systems; destruct Systems; auto.
      + intros [?|[?|?]].
        * subst; left; constructor.
        * right; apply IHtcs; rewrite map_app, in_app; auto.
        * right; apply IHtcs; rewrite map_app, in_app; auto.
  Qed.

End STCISSYSTEM.

Module StcIsSystemFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks   : CLOCKS    Ids Op OpAux)
       (CESyn : CESYNTAX  Ids Op OpAux Cks)
       (Syn   : STCSYNTAX Ids Op OpAux Cks CESyn)
<: STCISSYSTEM Ids Op OpAux Cks CESyn Syn.
  Include STCISSYSTEM Ids Op OpAux Cks CESyn Syn.
End StcIsSystemFun.
