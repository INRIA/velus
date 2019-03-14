Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.NLustre.NLExprSyntax.
Require Import Velus.SyBloc.SBSyntax.
Require Import Velus.Clocks.

Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Module Type SBISBLOCK
       (Import Ids     : IDS)
       (Import Op      : OPERATORS)
       (Import Clks    : CLOCKS       Ids)
       (Import ExprSyn : NLEXPRSYNTAX     Op)
       (Import Syn     : SBSYNTAX     Ids Op Clks ExprSyn).

  Inductive Is_block_in_eq : ident -> equation -> Prop :=
  | Is_block_inEqCall:
      forall s ys ck rst f es,
        Is_block_in_eq f (EqCall s ys ck rst f es)
  | Is_block_inEqReset:
      forall s ck f,
        Is_block_in_eq f (EqReset s ck f).

  Definition Is_block_in (f: ident) (eqs: list equation) : Prop :=
    Exists (Is_block_in_eq f) eqs.

  Lemma not_Is_block_in_cons:
    forall b eq eqs,
      ~ Is_block_in b (eq :: eqs) <-> ~Is_block_in_eq b eq /\ ~Is_block_in b eqs.
  Proof.
    split; intro HH.
    - split; intro; apply HH; unfold Is_block_in; intuition.
    - destruct HH; inversion_clear 1; intuition.
  Qed.

  Lemma calls_resets_of_Is_block_in:
    forall eqs b,
      Is_block_in b eqs <-> In b (map snd (calls_of eqs ++ resets_of eqs)).
  Proof.
    induction eqs as [|[]]; simpl.
    - split; try contradiction; inversion 1.
    - setoid_rewrite <-IHeqs; split; try (right; auto);
        inversion_clear 1 as [?? IsBlock|]; auto; inv IsBlock.
    - setoid_rewrite <-IHeqs; split; try (right; auto);
        inversion_clear 1 as [?? IsBlock|]; auto; inv IsBlock.
    - split; rewrite map_app, in_app; simpl.
      + inversion_clear 1 as [?? IsBlock|?? Blocks]; try inv IsBlock; auto.
        apply IHeqs in Blocks.
        rewrite map_app, in_app in Blocks; destruct Blocks; auto.
      + intros [?|[?|?]].
        * right; apply IHeqs; rewrite map_app, in_app; auto.
        * subst; left; constructor.
        * right; apply IHeqs; rewrite map_app, in_app; auto.
    - split; rewrite map_app, in_app; simpl.
      + inversion_clear 1 as [?? IsBlock|?? Blocks]; try inv IsBlock; auto.
        apply IHeqs in Blocks.
        rewrite map_app, in_app in Blocks; destruct Blocks; auto.
      + intros [?|[?|?]].
        * subst; left; constructor.
        * right; apply IHeqs; rewrite map_app, in_app; auto.
        * right; apply IHeqs; rewrite map_app, in_app; auto.
  Qed.

End SBISBLOCK.

Module SBIsBlockFun
       (Ids     : IDS)
       (Op      : OPERATORS)
       (Clks    : CLOCKS       Ids)
       (ExprSyn : NLEXPRSYNTAX     Op)
       (Syn     : SBSYNTAX     Ids Op Clks ExprSyn)
<: SBISBLOCK Ids Op Clks ExprSyn Syn.
  Include SBISBLOCK Ids Op Clks ExprSyn Syn.
End SBIsBlockFun.
