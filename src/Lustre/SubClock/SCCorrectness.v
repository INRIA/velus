From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.
From Coq Require Import Setoid Morphisms.

From Velus Require Import Common.
From Velus Require Import Operators Environment.
From Velus Require Import Clocks.
From Velus Require Import CoindStreams IndexedStreams.
From Velus Require Import CoindIndexed.
From Velus Require Import Fresh.
From Velus Require Import Lustre.StaticEnv.
From Velus Require Import Lustre.LSyntax Lustre.LOrdered Lustre.LTyping Lustre.LClocking Lustre.LSemantics Lustre.LClockedSemantics.
From Velus Require Import Lustre.SubClock.SubClock.
From Velus Require Import Lustre.SubClock.SCClocking.

Module Type SCCORRECTNESS
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks   : CLOCKS Ids Op OpAux)
       (Import SCtr  : COINDSTREAMS Ids Op OpAux Cks)
       (Import Senv  : STATICENV Ids Op OpAux Cks)
       (Import Syn   : LSYNTAX Ids Op OpAux Cks Senv)
       (Import Cl    : LCLOCKING Ids Op OpAux Cks Senv Syn)
       (Import Ord   : LORDERED Ids Op OpAux Cks Senv Syn)
       (Sem          : LSEMANTICS Ids Op OpAux Cks Senv Syn Ord SCtr)
       (Import LSC   : LCLOCKEDSEMANTICS Ids Op OpAux Cks Senv Syn Cl Ord SCtr Sem)
       (Import SC    : SUBCLOCK Ids Op OpAux Cks Senv Syn).

  Module Clocking := SCClockingFun Ids Op OpAux Cks Senv Syn Cl SC.
  Module Import CIStr := CoindIndexedFun Ids Op OpAux Cks SCtr IStr.

  Lemma rename_var_sem sub : forall H H' x vs,
      (forall y vs, Env.find x sub = Some y -> sem_var H x vs -> sem_var H' y vs) ->
      (forall vs, Env.find x sub = None -> sem_var H x vs -> sem_var H' x vs) ->
      sem_var H x vs ->
      sem_var H' (rename_var sub x) vs.
  Proof.
    intros * Hsub Hnsub Hv. unfold rename_var.
    destruct (Env.find x sub) eqn:Hfind; eauto.
  Qed.

  Section subclock.
    Context {PSyn1 PSyn2 : block -> Prop} {prefs1 prefs2 : PS.t}.
    Variable G1 : @global PSyn1 prefs1.
    Variable G2 : @global PSyn2 prefs2.

    Hypothesis HGref : global_sem_refines G1 G2.

    Variable bck : clock.
    Variable sub : Env.t ident.
    Variable bs bs' : Stream bool.
    Variable H H' Hl : history.

    Hypothesis Hbck : sem_clock H' bs' bck bs.

    Corollary add_whens_const_sem : forall c ty,
        sem_exp_ck G2 (H', Hl) bs' (add_whens (Econst c) ty bck) [const bs c].
    Proof.
      revert bs bs' H' Hbck.
      induction bck as [|??? (?&?)]; intros * Hbck *; simpl.
      - inv Hbck. rewrite H1. constructor; auto.
        reflexivity.
      - assert (Hbck':=Hbck). inv Hbck'; simpl.
        eapply Swhen; eauto; simpl.
        repeat constructor; try eapply IHc; eauto using sem_clock_when_const.
    Qed.

    Corollary add_whens_enum_sem : forall ty k,
        sem_exp_ck G2 (H', Hl) bs' (add_whens (Eenum k ty) ty bck) [enum bs k].
    Proof.
      revert bs bs' H' Hbck.
      induction bck as [|??? (?&?)]; intros * Hbck *; simpl.
      - inv Hbck. rewrite H1. constructor; auto.
        reflexivity.
      - assert (Hbck':=Hbck). inv Hbck'; simpl.
        eapply Swhen; eauto; simpl.
        repeat constructor; try eapply IHc; eauto using sem_clock_when_enum.
    Qed.

    Hypothesis Hsub : forall x y vs,
        Env.find x sub = Some y ->
        sem_var H x vs ->
        sem_var H' y vs.

    Hypothesis Hnsub : forall x vs,
        Env.find x sub = None ->
        sem_var H x vs ->
        sem_var H' x vs.

    Lemma subclock_exp_sem : forall e vs,
        sem_exp_ck G1 (H, Hl) bs e vs ->
        sem_exp_ck G2 (H', Hl) bs' (subclock_exp bck sub e) vs.
    Proof.
      induction e using exp_ind2; intros * Hsem; inv Hsem; simpl.
      - (* const *)
        rewrite H4. apply add_whens_const_sem.
      - (* enum *)
        rewrite H6. apply add_whens_enum_sem.
      - (* var *)
        constructor.
        eapply rename_var_sem; eauto.
      - constructor. auto.
      - (* unop *)
        econstructor; eauto.
        now rewrite subclock_exp_typeof.
      - (* binop *)
        econstructor; eauto.
        1,2:now rewrite subclock_exp_typeof.
      - (* extcall *)
        econstructor; eauto.
        1,2:simpl_Forall; eauto.
        now rewrite subclock_exp_typesof.
      - (* fby *)
        econstructor; eauto.
        1,2:simpl_Forall; eauto.
      - (* arrow *)
        econstructor; eauto.
        1,2:simpl_Forall; eauto.
      - (* when *)
        econstructor; eauto using rename_var_sem.
        simpl_Forall; eauto.
      - (* merge *)
        econstructor; eauto using rename_var_sem.
        rewrite <-Sem.Forall2Brs_map_1.
        eapply Sem.Forall2Brs_impl_In; [|eauto]; intros ?? Hex Hsem.
        simpl_Exists. simpl_Forall. eauto.
      - (* case (total) *)
        econstructor; eauto.
        rewrite <-Sem.Forall2Brs_map_1.
        eapply Sem.Forall2Brs_impl_In; [|eauto]; intros ?? Hex Hsem.
        simpl_Exists. simpl_Forall. eauto.
      - (* case (default) *)
        econstructor; eauto; simpl in *.
        + now rewrite subclock_exp_typeof.
        + rewrite <-Sem.Forall2Brs_map_1.
          eapply Sem.Forall2Brs_impl_In; [|eauto]; intros ?? Hex Hsem.
          simpl_Exists. simpl_Forall. eauto.
        + simpl_Forall; eauto.
      - (* app *)
        eapply Sapp with (ss:=ss); eauto.
        1,2:simpl_Forall; eauto.
        intros. eapply HGref; eauto.
    Qed.

    Lemma subclock_equation_sem : forall equ,
        sem_equation_ck G1 (H, Hl) bs equ ->
        sem_equation_ck G2 (H', Hl) bs' (subclock_equation bck sub equ).
    Proof.
      intros (?&?) Hsem. inv Hsem.
      eapply Seq with (ss:=ss); simpl_Forall;
        eauto using subclock_exp_sem, rename_var_sem.
    Qed.

  End subclock.

  Lemma subclock_clock_sem : forall bck sub Hi Hi' bs bs' ck bs1,
      (forall x y vs, Env.find x sub = Some y -> sem_var Hi x vs -> sem_var Hi' y vs) ->
      (forall x vs, Env.find x sub = None -> sem_var Hi x vs -> sem_var Hi' x vs) ->
      sem_clock Hi' bs' bck bs ->
      sem_clock Hi bs ck bs1 ->
      sem_clock Hi' bs' (subclock_clock bck sub ck) bs1.
  Proof.
    induction ck; intros * Hsub Hnsub Hbck * Hsemck; simpl; inv Hsemck.
    - rewrite <-H0. assumption.
    - econstructor; eauto using rename_var_sem.
  Qed.

End SCCORRECTNESS.

Module SCCorrectnessFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks   : CLOCKS Ids Op OpAux)
       (SCtr  : COINDSTREAMS Ids Op OpAux Cks)
       (Senv  : STATICENV Ids Op OpAux Cks)
       (Syn   : LSYNTAX Ids Op OpAux Cks Senv)
       (Clo   : LCLOCKING Ids Op OpAux Cks Senv Syn)
       (Lord  : LORDERED Ids Op OpAux Cks Senv Syn)
       (Sem   : LSEMANTICS Ids Op OpAux Cks Senv Syn Lord SCtr)
       (LSC   : LCLOCKEDSEMANTICS Ids Op OpAux Cks Senv Syn Clo Lord SCtr Sem)
       (SC    : SUBCLOCK Ids Op OpAux Cks Senv Syn)
       <: SCCORRECTNESS Ids Op OpAux Cks SCtr Senv Syn Clo Lord Sem LSC SC.
  Include SCCORRECTNESS Ids Op OpAux Cks SCtr Senv Syn Clo Lord Sem LSC SC.
End SCCorrectnessFun.
