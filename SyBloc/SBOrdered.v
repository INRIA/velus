Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.CoreExpr.CESyntax.
Require Import Velus.SyBloc.SBSyntax.
Require Import Velus.SyBloc.SBIsBlock.
Require Import Velus.Clocks.

Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Module Type SBORDERED
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import CESyn : CESYNTAX      Op)
       (Import Syn   : SBSYNTAX  Ids Op CESyn)
       (Import Block : SBISBLOCK Ids Op CESyn Syn).

  Inductive Ordered_blocks: program -> Prop :=
  | Ordered_nil:
      Ordered_blocks []
  | Ordered_cons:
      forall bl P,
        Ordered_blocks P ->
        Forall (fun xb =>
                  snd xb <> bl.(b_name)
                  /\ exists bl' P', find_block (snd xb) P = Some (bl', P'))
               bl.(b_blocks) ->
        Forall (fun bl' => bl.(b_name) <> bl'.(b_name))%type P ->
        Ordered_blocks (bl :: P).

  Remark Ordered_blocks_split:
    forall P1 bl P,
      Ordered_blocks (P1 ++ bl :: P) ->
      Forall (fun xb =>
                  find_block (snd xb) P1 = None
                  /\ snd xb <> bl.(b_name)
                  /\ exists bl' P', find_block (snd xb) P = Some (bl', P'))
             bl.(b_blocks).
  Proof.
    induction P1; inversion_clear 1 as [|?? Ord]; apply Forall_Forall; auto.
    - apply Forall_forall; auto.
    - apply IHP1 in Ord; apply Forall_forall; intros.
      eapply Forall_forall in Ord as (?&?&(bl' &?& Find)); eauto.
      rewrite find_block_other; auto.
      pose proof Find as Find'; apply find_block_name in Find'.
      apply find_block_In in Find.
      assert (In bl' (P1 ++ bl :: P)) as Hin
          by (apply in_app; right; right; auto).
      eapply Forall_forall in Hin; eauto.
      congruence.
    - apply IHP1 in Ord; apply Forall_forall; intros.
      eapply Forall_forall in Ord as (?&?&?); eauto.
  Qed.

  Lemma Ordered_blocks_append:
    forall P P',
      Ordered_blocks (P ++ P') ->
      Ordered_blocks P'.
  Proof.
    induction P; [intuition|].
    intros * HnPP.
    apply IHP; inversion_clear HnPP; assumption.
  Qed.

  Lemma Ordered_blocks_find_In_blocks:
    forall P b bl P',
      Ordered_blocks P ->
      find_block b P = Some (bl, P') ->
      forall x b,
        In (x, b) bl.(b_blocks) ->
        exists bl P'', find_block b P' = Some (bl, P'').
  Proof.
    induction P as [|block]; try now inversion 2.
    intros * Ord Find ?? Hin.
    inv Ord.
    simpl in Find.
    destruct (ident_eqb (b_name block) b) eqn: E; eauto.
    inv Find.
    eapply Forall_forall in Hin; eauto.
    destruct Hin; eauto.
  Qed.

  Lemma Ordered_blocks_find_block:
    forall P b bl P',
      Ordered_blocks P ->
      find_block b P = Some (bl, P') ->
      Ordered_blocks P'.
  Proof.
    induction P as [|block]; try now inversion 2.
    intros * Ord Find.
    inv Ord.
    simpl in Find.
    destruct (ident_eqb (b_name block) b) eqn: E; eauto.
    inv Find; auto.
  Qed.
 Lemma find_block_later_not_Is_block_in:
    forall f bl P bl' P',
      Ordered_blocks (bl :: P) ->
      find_block f P = Some (bl', P') ->
      ~ Is_block_in bl.(b_name) bl'.(b_eqs).
  Proof.
    intros * Hord Hfind Hini.
    apply find_block_app in Hfind as (?& E &?); rewrite E, app_comm_cons in Hord.
    pose proof Hord as Hord'; inversion_clear Hord' as [|??? Sub Hnin]; clear Sub.
    apply Ordered_blocks_split in Hord.
    apply calls_resets_of_Is_block_in in Hini.
    apply b_blocks_in_eqs, in_map_iff in Hini as (?&?& Hin).
    eapply Forall_forall in Hin; eauto; destruct Hin as (?&?&?&?& Find); simpl in Find.
    apply Forall_app_weaken in Hnin; inversion_clear Hnin as [|??? Hnin'].
    pose proof Find as Find'; apply find_block_name in Find'.
    apply find_block_In in Find.
    eapply Forall_forall in Find; eauto.
    congruence.
  Qed.

  Lemma find_block_not_Is_block_in:
    forall f bl P P',
      Ordered_blocks P ->
      find_block f P = Some (bl, P') ->
      ~ Is_block_in bl.(b_name) bl.(b_eqs).
  Proof.
    intros * Hord Hfind Hini.
    apply find_block_app in Hfind as (?& E &?); rewrite E in Hord.
    apply Ordered_blocks_split in Hord.
    apply calls_resets_of_Is_block_in in Hini.
    apply b_blocks_in_eqs, in_map_iff in Hini as (?&?& Hin).
    eapply Forall_forall in Hin; eauto; destruct Hin as (?&?&?); auto.
  Qed.

End SBORDERED.

Module SBOrderedFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (CESyn : CESYNTAX      Op)
       (Syn   : SBSYNTAX  Ids Op CESyn)
       (Block : SBISBLOCK Ids Op CESyn Syn)
<: SBORDERED Ids Op CESyn Syn Block.
  Include SBORDERED Ids Op CESyn Syn Block.
End SBOrderedFun.
