Require Import List.
Import List.ListNotations.
Open Scope list_scope.
Require Import Coq.Sorting.Permutation.
Require Import Morphisms.

Require Import Coq.FSets.FMapPositive.
Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.Clocks.
Require Import Velus.NLustre.NLSyntax.
Require Import Velus.NLustre.Ordered.
Require Import Velus.NLustre.Stream.
Require Import Velus.NLustre.Streams.

Require Import Velus.NLustre.NLSemantics.
Require Import Velus.NLustre.NLSemanticsCoInd.

Require Import Setoid.
Module Type COINDTONATMAP
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op)
       (Import Clks  : CLOCKS    Ids)
       (Import Syn   : NLSYNTAX  Ids Op Clks)
       (Import Str   : STREAM        Op OpAux)
       (Import Ord   : ORDERED   Ids Op Clks Syn)
       (Sem          : NLSEMANTICS Ids Op OpAux Clks Syn Str Ord)
       (Mod          : NLSEMANTICSCOIND Ids Op OpAux Clks Syn Ord).

  Section Global.

    Variable G : global.

    Fixpoint to_map {A} (xss: list (Stream A)) : stream (list A) :=
      match xss with
      | [] => fun n => []
      | xs :: xss => fun n => Str_nth n xs :: to_map xss n
      end.

    Definition hist_to_map (H: Mod.history) : Sem.history :=
      PM.map (fun xs => fun n => Str_nth n xs) H.

    Lemma sem_var_impl:
      forall H b xs xss,
      Forall2 (Mod.sem_var H) xs xss ->
      Sem.sem_vars b (hist_to_map H) xs (to_map xss).
    Proof.
      induction 1 as [|? ? ? ? Find];
        simpl; unfold Sem.sem_vars, Sem.lift; auto.
      intro; constructor; auto.
      constructor.
      inv Find.
      unfold Sem.restr, hist_to_map.
      unfold PM.map.
      rewrite 2 PM.gmapi.
      erewrite PM.find_1; eauto; simpl.
      f_equal.
      apply eqst_ntheq; symmetry; auto.
    Qed.

    Theorem implies:
      forall f xss oss,
        Mod.sem_node G f xss oss ->
        Sem.sem_node G f (to_map xss) (to_map oss).
    Proof.
      intros ** Sem.
      induction Sem as [
                      |
                      |
                      |
                      |
                      | ? ? ? ? ? Find]
                         using Mod.sem_node_mult with
          (P_equation := fun H b e => True)
          (P_reset := fun f r xss oss => True).
      - auto.
      - auto.
      - auto.
      - auto.
      - auto.
      - econstructor; eauto.
        + apply Sem.clock_of_equiv.
        + apply sem_var_impl; eauto.
        + apply sem_var_impl; eauto.
        + admit.
        + admit.
        + admit.
        + admit.
    Qed.


  End Global.

End COINDTONATMAP.
