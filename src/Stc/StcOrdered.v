From Velus Require Import Common.
From Velus Require Import CommonProgram.
From Velus Require Import Operators.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import Stc.StcSyntax.
From Velus Require Import Clocks.

From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Module Type STCORDERED
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX   Ids Op)
       (Import Cks   : CLOCKS      Ids Op OpAux)
       (Import CESyn : CESYNTAX    Ids Op OpAux Cks)
       (Import Syn   : STCSYNTAX   Ids Op OpAux Cks CESyn).

  Definition Ordered_systems {prefs} := Ordered_program (fun f (s: @system prefs) => In f (map snd s.(s_subs))).
  (* Inductive Ordered_systems: program -> Prop := *)
  (* | Ordered_nil: forall enums, *)
  (*     Ordered_systems (Program enums []) *)
  (* | Ordered_cons: *)
  (*     forall s P enums, *)
  (*       Ordered_systems (Program enums P) -> *)
  (*       Forall (fun xb => *)
  (*                 snd xb <> s.(s_name) *)
  (*                 /\ exists s' P', find_system (snd xb) (Program enums P) = Some (s', P')) *)
  (*              s.(s_subs) -> *)
  (*       Forall (fun s' => s.(s_name) <> s'.(s_name))%type P -> *)
  (*       Ordered_systems (Program enums (s :: P)). *)

  Lemma Ordered_systems_append {prefs}:
    forall (P P': list (@system prefs)) enums externs,
      Ordered_systems (Program enums externs (P ++ P')) ->
      Ordered_systems (Program enums externs P').
  Proof.
    intros * Ord; eapply Ordered_program_append' in Ord as (?&?); simpl in *; eauto.
  Qed.

  Lemma Ordered_systems_split {prefs}:
    forall P1 (s: @system prefs) P enums externs,
      Ordered_systems (Program enums externs (P1 ++ s :: P)) ->
      Forall (fun xb =>
                  find_system (snd xb) (Program enums externs P1) = None
                  /\ snd xb <> s.(s_name)
                  /\ exists s' P', find_system (snd xb) (Program enums externs P) = Some (s', P'))
             s.(s_subs).
  Proof.
    intros * Ord.
    eapply Ordered_program_append' in Ord as (Ndp & Ord); simpl in *; eauto.
    inversion_clear Ord as [|?? [Spec]].
    apply Forall_forall; intros [] Hin; simpl in *.
    split.
    - apply in_map with (f := snd) in Hin; apply Spec in Hin as (?&?&?& Find); simpl in *.
      apply find_unit_spec in Find as (?&?&?&?); simpl in *; subst.
      apply find_unit_None; simpl.
      apply Forall_forall; intros * Hin'.
      eapply Forall'_In in Hin' as (?&?&?& Hnn); eauto; simpl in *; subst.
      rewrite Forall_app, Forall_cons2, Forall_app, Forall_cons2 in Hnn; auto with *.
    - apply Spec, in_map_iff.
      eexists.
      split; eauto with *.
      reflexivity.
  Qed.

  Corollary Ordered_systems_find_In_systems {prefs} :
    forall P b (s: @system prefs) P',
      Ordered_systems P ->
      find_system b P = Some (s, P') ->
      forall x b,
        In (x, b) s.(s_subs) ->
        exists s P'', find_system b P' = Some (s, P'').
  Proof.
    intros * Ord Find.
    assert (equiv_program P P') as E by (eapply find_unit_equiv_program; eauto).
    specialize (E nil); inv E.
    apply find_unit_spec in Find as (?&?&?&?).
    destruct P, P'; simpl in *; subst.
    apply Ordered_systems_split in Ord.
    intros * Hin.
    eapply Forall_forall in Hin; eauto.
    simpl in *.
    intuition.
  Qed.

  Lemma Ordered_systems_find_system {prefs} :
    forall P b (s: @system prefs) P',
      Ordered_systems P ->
      find_system b P = Some (s, P') ->
      Ordered_systems P'.
  Proof.
    intros * Ord Find.
    assert (types P = types P') as Etypes
        by (apply find_unit_equiv_program in Find; specialize (Find nil); inv Find; auto).
    assert (externs P = externs P') as Eexterns
        by (apply find_unit_equiv_program in Find; specialize (Find nil); inv Find; auto).
    eapply Ordered_program_find_unit in Ord; simpl in *; eauto.
    rewrite Etypes, Eexterns in Ord; now inv Ord.
  Qed.

  Lemma find_system_other_not_Is_system_in {prefs} :
    forall f (s: @system prefs) P s' P' types externs,
      Ordered_systems (Program types externs (s :: P)) ->
      find_system f (Program types externs P) = Some (s', P') ->
      ~ Is_system_in s.(s_name) s'.(s_tcs).
  Proof.
    intros * Ord Find.
    eapply find_unit_other_not_Is_called_in with (u := s) in Ord; eauto; simpl; auto.
    intro Hin; apply Ord.
    apply steps_iresets_of_Is_system_in in Hin.
    now apply s_subs_in_tcs.
  Qed.

  Lemma find_system_not_Is_system_in {prefs}:
    forall f (s: @system prefs) P P',
      Ordered_systems P ->
      find_system f P = Some (s, P') ->
      ~ Is_system_in s.(s_name) s.(s_tcs).
  Proof.
    intros * Ord Find.
    eapply not_Is_called_in_self in Ord; eauto.
    assert (s_name s = f) as -> by (apply find_unit_In in Find as []; auto).
    intro Hin; apply Ord.
    apply steps_iresets_of_Is_system_in in Hin.
    now apply s_subs_in_tcs.
  Qed.

End STCORDERED.

Module StcOrderedFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX   Ids Op)
       (Cks   : CLOCKS      Ids Op OpAux)
       (CESyn : CESYNTAX    Ids Op OpAux Cks)
       (Syn   : STCSYNTAX   Ids Op OpAux Cks CESyn)
<: STCORDERED Ids Op OpAux Cks CESyn Syn.
  Include STCORDERED Ids Op OpAux Cks CESyn Syn.
End StcOrderedFun.
