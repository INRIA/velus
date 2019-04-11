Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.CoreExpr.CESyntax.
Require Import Velus.SyBloc.SBSyntax.
Require Import Velus.Clocks.

Require Import Velus.RMemory.

Require Import Velus.SyBloc.SBIsLast.

Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Module Type SBMEMORYCORRES
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import CESyn : CESYNTAX     Op)
       (Import Syn   : SBSYNTAX Ids Op CESyn)
       (Import Last  : SBISLAST Ids Op CESyn Syn).

  Definition state := memory val.
  Definition menv := memory val.
  Definition transient_states := Env.t (memory val).

  Definition value_corres (x: ident) (S: state) (me: menv) : Prop :=
    find_val x S = find_val x me.

  Definition state_corres (s: ident) (S: state) (me: menv) : Prop :=
    (forall Ss,
        sub_inst s S Ss ->
        exists me',
          sub_inst s me me'
          /\ me' ≋ Ss)
    /\ forall me',
      sub_inst s me me' ->
      exists Ss,
        sub_inst s S Ss.

  Definition transient_state_corres (s: ident) (I: transient_states) (me: menv) : Prop :=
    (forall Is,
        Env.find s I = Some Is ->
        exists me',
          sub_inst s me me'
          /\ me' ≋ Is)
    /\ forall me',
      sub_inst s me me' ->
      exists Is,
        Env.find s I = Some Is.

  Definition Memory_Corres_eqs
             (eqs: list equation)
             (S: state) (I: transient_states) (S': state)
             (me: menv) : Prop :=
    (forall x,
        (Is_last_in x eqs -> value_corres x S' me)
        /\
        (~ Is_last_in x eqs -> value_corres x S me))
    /\
    (forall s,
        (~ Step_in s eqs /\ ~ Reset_in s eqs ->
         state_corres s S me)
        /\
        (~ Step_in s eqs /\ Reset_in s eqs ->
         transient_state_corres s I me)
        /\
        (Step_in s eqs ->
         state_corres s S' me)).

  Lemma Memory_Corres_eqs_Def:
    forall x ck ce S I S' me eqs,
      Memory_Corres_eqs eqs S I S' me ->
      Memory_Corres_eqs (EqDef x ck ce :: eqs) S I S' me.
  Proof.
    intros ** (Lasts & Insts); split; [split|split; [|split]].
    - inversion_clear 1 as [?? Last|]; eauto.
      + inv Last.
      + apply Lasts; auto.
    - intro NLast; apply Lasts.
      intro; apply NLast; right; auto.
    - intros (Nstep & Nrst).
      apply Insts; split.
      + intro; apply Nstep; right; auto.
      + intro; apply Nrst; right; auto.
    - intros (Nstep & Rst).
      apply Insts; split.
      + intro; apply Nstep; right; auto.
      + inversion_clear Rst as [?? IsSt|]; auto.
        inv IsSt.
    - intros Step.
      apply Insts; inversion_clear Step as [?? IsSt|]; auto.
      inv IsSt.
  Qed.

  Lemma Memory_Corres_eqs_Next_present:
    forall x ck e S I S' me eqs c,
      Memory_Corres_eqs eqs S I S' me ->
      find_val x S' = Some c ->
      Memory_Corres_eqs (EqNext x ck e :: eqs) S I S' (add_val x c me).
  Proof.
    intros ** (Lasts & Insts); split; [split|split; [|split]].
    - inversion_clear 1 as [?? Last|?? Last]; eauto; unfold value_corres.
      + inv Last; rewrite find_val_gss; auto.
      + intros.
        destruct (ident_eq_dec x0 x).
        * subst; rewrite find_val_gss; auto.
        * rewrite find_val_gso; auto;
            apply Lasts with (1 := Last); auto.
    - intros NLast **; unfold value_corres.
      assert (x0 <> x)
        by (intro; subst; apply NLast; left; constructor).
      assert ( ~ Is_last_in x0 eqs)
        by (intro; apply NLast; right; auto).
      rewrite find_val_gso; auto;
        apply Lasts; auto.
    - intros (Nstep & Nrst).
      assert (~ Step_in s eqs) by (intro; apply Nstep; right; auto).
      assert (~ Reset_in s eqs) by (intro; apply Nrst; right; auto).
      split; unfold sub_inst; setoid_rewrite find_inst_add_val;
        apply Insts; auto.
    - intros (Nstep & Rst).
      assert (~ Step_in s eqs) by (intro; apply Nstep; right; auto).
      assert (Reset_in s eqs)
        by (inversion_clear Rst as [?? IsSt|]; auto; inv IsSt).
      split; unfold sub_inst; setoid_rewrite find_inst_add_val;
        apply Insts; auto.
    - intros Step.
      assert (Step_in s eqs)
        by (inversion_clear Step as [?? IsSt|]; auto; inv IsSt).
      split; unfold sub_inst; setoid_rewrite find_inst_add_val;
        apply Insts; auto.
  Qed.

  Lemma Memory_Corres_eqs_Next_absent:
    forall x ck e S I S' me eqs,
      Memory_Corres_eqs eqs S I S' me ->
      find_val x S' = find_val x S ->
      Memory_Corres_eqs (EqNext x ck e :: eqs) S I S' me.
  Proof.
    intros ** (Lasts & Insts) Eq; split; [split|split; [|split]].
    - inversion_clear 1 as [?? Last|?? Last]; eauto; unfold value_corres.
      + inv Last.
        destruct (Is_last_in_dec x eqs).
        * apply Lasts; auto.
        * setoid_rewrite Eq; apply Lasts; auto.
      + apply Lasts; auto.
    - intros NLast.
      apply Lasts; intro; apply NLast; right; auto.
    - intros (Nstep & Nrst).
      apply Insts; split.
      + intro; apply Nstep; right; auto.
      + intro; apply Nrst; right; auto.
    - intros (Nstep & Rst).
      apply Insts; split.
      + intro; apply Nstep; right; auto.
      + inversion_clear Rst as [?? IsSt|]; auto.
        inv IsSt.
    - intros Step.
      apply Insts; inversion_clear Step as [?? IsSt|]; auto.
      inv IsSt.
  Qed.

  Lemma Memory_Corres_eqs_Reset_present:
    forall s ck b S I S' Is me eqs me',
      Memory_Corres_eqs eqs S I S' me ->
      Env.find s I = Some Is ->
      me' ≋ Is ->
      ~ Step_in s eqs ->
      Memory_Corres_eqs (EqReset s ck b :: eqs) S I S' (add_inst s me' me).
  Proof.
    intros ** (Lasts & Insts) ??; split; [split|split; [|split]].
    - inversion_clear 1 as [?? Last|]; eauto.
      + inv Last.
      + apply Lasts; auto.
    - intro NLast; apply Lasts.
      intro; apply NLast; right; auto.
    - intros (Nstep & Nrst).
      assert (s0 <> s)
        by (intro; subst; apply Nrst; left; constructor).
      assert (~ Step_in s0 eqs) by (intro; apply Nstep; right; auto).
      assert (~ Reset_in s0 eqs) by (intro; apply Nrst; right; auto).
      split; unfold sub_inst; rewrite find_inst_gso; auto;
        apply Insts; auto.
    - intros (Nstep & Rst).
      inversion_clear Rst as [?? Rst'|].
      + inv Rst'.
        split; unfold sub_inst; setoid_rewrite find_inst_gss.
        * intros; exists me'; intuition; congruence.
        * inversion 1; subst; intros; exists Is; eauto.
      + destruct (ident_eq_dec s0 s).
        *{ split; subst; unfold sub_inst; rewrite find_inst_gss.
           - exists me'; intuition; congruence.
           - inversion 1; subst; intros; exists Is; eauto.
         }
        * assert (~ Step_in s0 eqs) by (intro; apply Nstep; right; auto).
          split; unfold sub_inst; rewrite find_inst_gso; auto;
            apply (proj1 (proj2 (Insts s0))); auto.
    - intros Step.
      inversion_clear Step as [?? Step'|].
      + inv Step'.
      + destruct (ident_eq_dec s0 s).
        * split; subst; intuition.
        * split; unfold sub_inst; rewrite find_inst_gso; auto;
            apply Insts; auto.
  Qed.

  Lemma Memory_Corres_eqs_Reset_absent:
    forall s ck b S I S' Is Ss me eqs,
      Memory_Corres_eqs eqs S I S' me ->
      Env.find s I = Some Is ->
      sub_inst s S Ss ->
      Is ≋ Ss ->
      ~ Reset_in s eqs ->
      Memory_Corres_eqs (EqReset s ck b :: eqs) S I S' me.
  Proof.
    intros ** (Lasts & Insts) Find_I Find_S E; split; [split|split; [|split]].
    - inversion_clear 1 as [?? Last|]; eauto.
      + inv Last.
      + apply Lasts; auto.
    - intro NLast; apply Lasts.
      intro; apply NLast; right; auto.
    - intros (Nstep & Nrst).
      apply Insts; split.
      + intro; apply Nstep; right; auto.
      + intro; apply Nrst; right; auto.
    - intros (Nstep & Rst).
      inversion_clear Rst as [?? Rst'|].
      + inv Rst'.
        assert (~ Step_in s eqs) by (intro; apply Nstep; right; auto).
        split; unfold sub_inst.
        * intros ** Find.
          rewrite Find in Find_I; inv Find_I.
          setoid_rewrite E.
          apply (proj1 (Insts s)); auto.
        * assert (state_corres s S me) as StCorr by (apply Insts; auto).
          intros ** Find; apply StCorr in Find as (?& Find).
          unfold sub_inst in *; rewrite Find in Find_S; inv Find_S.
          exists Is; eauto.
      + apply Insts; split; auto.
        intro; apply Nstep; right; auto.
    - intros Step.
      inversion_clear Step as [?? Step'|].
      + inv Step'.
      + apply Insts; eauto.
  Qed.

  Lemma Memory_Corres_eqs_Call_present:
    forall s ys ck (rst: bool) b es S I S' Ss' eqs me me',
      Memory_Corres_eqs eqs S I S' me ->
      sub_inst s S' Ss' ->
      me' ≋ Ss' ->
      Memory_Corres_eqs (EqCall s ys ck rst b es :: eqs) S I S' (add_inst s me' me).
  Proof.
    intros ** (Lasts & Insts) Find_S' E;
      split; [split|split; [|split]].
    - inversion_clear 1 as [?? Last|]; eauto.
      + inv Last.
      + apply Lasts; auto.
    - intro NLast; apply Lasts.
      intro; apply NLast; right; auto.
    - intros (Nstep & Nrst).
      assert (s0 <> s) as Neq
          by (intro; subst; apply Nstep; left; constructor).
      assert (~ Step_in s0 eqs) by (intro; apply Nstep; right; auto).
      assert (~ Reset_in s0 eqs) by (intro; apply Nrst; right; auto).
      split; unfold sub_inst; rewrite find_inst_gso; auto;
        apply Insts; auto.
    - intros (Nstep & Rst).
      assert (s0 <> s) as Neq
          by (intro; subst; apply Nstep; left; constructor).
      assert (~ Step_in s0 eqs) by (intro; apply Nstep; right; auto).
      inversion_clear Rst as [?? Rst'|]; try inv Rst'.
      split; unfold sub_inst; rewrite find_inst_gso; auto;
        apply Insts; auto.
    - intros Step.
      inversion_clear Step as [?? Step'|].
      + inv Step'.
        split; unfold sub_inst; rewrite find_inst_gss.
        * exists me'; intuition; congruence.
        * inversion 1; subst; exists Ss'; intuition.
      + destruct (ident_eq_dec s0 s).
        *{ split; subst; unfold sub_inst; rewrite find_inst_gss.
           - exists me'; intuition; congruence.
           - inversion 1; subst; exists Ss'; intuition.
         }
        * split; unfold sub_inst; rewrite find_inst_gso; auto;
            apply Insts; auto.
  Qed.

  Lemma Memory_Corres_eqs_Call_absent:
    forall s ys ck (rst: bool) b es S I S' Is Ss' eqs me,
      Memory_Corres_eqs eqs S I S' me ->
      Env.find s I = Some Is ->
      (rst = false -> exists Ss, sub_inst s S Ss /\ Is ≋ Ss) ->
      sub_inst s S' Ss' ->
      Ss' ≋ Is ->
      ~ Step_in s eqs /\ (if rst then Reset_in s eqs else ~ Reset_in s eqs) ->
      Memory_Corres_eqs (EqCall s ys ck rst b es :: eqs) S I S' me.
  Proof.
    intros ** (Lasts & Insts) Find_I Find_S Find_S' E NstepRst;
      split; [split|split; [|split]].
    - inversion_clear 1 as [?? Last|]; eauto.
      + inv Last.
      + apply Lasts; auto.
    - intro NLast; apply Lasts.
      intro; apply NLast; right; auto.
    - intros (Nstep & Nrst).
      apply Insts; split.
      + intro; apply Nstep; right; auto.
      + intro; apply Nrst; right; auto.
    - intros (Nstep & Rst).
      apply Insts; split.
      + intro; apply Nstep; right; auto.
      + inversion_clear Rst as [?? Rst'|]; auto.
        inv Rst'.
    - intros Step.
      inversion_clear Step as [?? Step'|].
      + inv Step'.
        destruct rst.
        *{ apply Insts in Find_I as (me' & Sub &?); auto.
           split; intros ** Sub'; unfold sub_inst in *.
           - rewrite Find_S' in Sub'; inv Sub'.
             exists me'; rewrite E; auto.
           - rewrite Sub' in Sub; inv Sub.
             exists Ss'; auto.
         }
        *{ destruct Find_S as (Ss & Find_S &?); auto.
           apply Insts in Find_S as (me' & Sub &?); auto.
           split; intros ** Sub'; unfold sub_inst in *.
           - rewrite Find_S' in Sub'; inv Sub'.
             exists me'; split; auto.
             transitivity Ss; auto.
             transitivity Is; symmetry; auto.
           - rewrite Sub' in Sub; inv Sub.
             exists Ss'; auto.
         }
      + apply Insts; eauto.
  Qed.

End SBMEMORYCORRES.

Module SBMemoryCorresFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (CESyn : CESYNTAX     Op)
       (Syn   : SBSYNTAX Ids Op CESyn)
       (Last  : SBISLAST Ids Op CESyn Syn)
<: SBMEMORYCORRES Ids Op CESyn Syn Last.
  Include SBMEMORYCORRES Ids Op CESyn Syn Last.
End SBMemoryCorresFun.
