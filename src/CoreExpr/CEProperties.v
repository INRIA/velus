From Velus Require Import Common.
From Velus Require Import Operators.
From Velus Require Import Environment.
From Velus Require Import Clocks.
From Velus Require Export IndexedStreams.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import CoreExpr.CETyping.
From Velus Require Import CoreExpr.CESemantics.
From Velus Require Import CoreExpr.CEIsFree.

Import List.

(** * Properties of Core Expressions *)

Module Type CEPROPERTIES
       (Ids        : IDS)
       (Op         : OPERATORS)
       (OpAux      : OPERATORS_AUX   Ids Op)
       (Import Cks : CLOCKS          Ids Op OpAux)
       (Import Syn : CESYNTAX        Ids Op OpAux Cks)
       (Import Str : INDEXEDSTREAMS  Ids Op OpAux Cks)
       (Import Sem : CESEMANTICS Ids Op OpAux Cks Syn Str)
       (Import Typ : CETYPING    Ids Op OpAux Cks Syn)
       (Import IsF : CEISFREE    Ids Op OpAux Cks Syn).

  Lemma sem_var_instant_switch_env:
    forall R R' x v,
      R x = R' x ->
      sem_var_instant R x v <-> sem_var_instant R' x v.
  Proof.
    intros; split; unfold sem_var_instant;
      take (R x = _) and rewrite it; auto.
  Qed.

  Lemma sem_exp_instant_switch_env:
    forall b R R' e v,
      (forall x, Is_free_in_exp x e -> R x = R' x) ->
      sem_exp_instant b R e v <-> sem_exp_instant b R' e v.
  Proof.
    induction e; intros * RRx.
    - (* Econst *)
      split; inversion 1; destruct b; eauto using sem_exp_instant.
    - (* Eenum *)
      split; inversion 1; eauto using sem_exp_instant.
    - (* Evar *)
      split; inversion_clear 1;
        take (sem_var_instant _ _ _) and eapply sem_var_instant_switch_env in it;
        eauto using sem_exp_instant with nlfree.
      symmetry; auto with nlfree.
    - (* Ewhen *)
      destruct_conjs.
      split; inversion_clear 1;
        take (sem_var_instant _ _ _) and eapply sem_var_instant_switch_env in it;
        take (sem_exp_instant _ _ _ _)
             and (erewrite IHe in it || rewrite <-IHe in it);
        eauto using sem_exp_instant with nlfree;
        symmetry; auto with nlfree.
    - (* Eunop *)
      split; inversion_clear 1;
        take (sem_exp_instant _ _ _ _)
             and (erewrite IHe in it || rewrite <-IHe in it);
        eauto using sem_exp_instant with nlfree.
    - (* Ebinop *)
      split; inversion_clear 1;
        take (sem_exp_instant _ _ e1 _)
             and (erewrite IHe1 in it || rewrite <-IHe1 in it);
        take (sem_exp_instant _ _ e2 _)
             and (erewrite IHe2 in it || rewrite <-IHe2 in it);
        eauto using sem_exp_instant with nlfree.
  Qed.

  Lemma sem_exps_instant_switch_env:
    forall b R R' es vs,
      (forall x, Exists (Is_free_in_exp x) es -> R x = R' x) ->
      sem_exps_instant b R es vs <-> sem_exps_instant b R' es vs.
  Proof.
    induction es as [|e es IH]. now split; inversion 1; subst; auto with nlsem.
    intros vs HH. destruct vs. now split; inversion 1.
    repeat rewrite sem_exps_instant_cons.
    rewrite IH; auto.
    now rewrite sem_exp_instant_switch_env with (R':=R'); auto.
  Qed.

  Lemma sem_cexp_instant_switch_env:
    forall b R R' e v,
      (forall x, Is_free_in_cexp x e -> R x = R' x) ->
      sem_cexp_instant b R e v <-> sem_cexp_instant b R' e v.
  Proof with eauto with nlfree.
    induction e using cexp_ind2; intros * RRx.
    - (* Emerge *)
      destruct x.
      split; inversion_clear 1.
      + take (sem_var_instant _ _ _) and eapply (sem_var_instant_switch_env _ R') in it...
        subst; take (Forall _ (_ ++ _ :: _)) and apply Forall_app in it as (Hes1 & Hes2');
          inversion_clear Hes2' as [|?? He Hes2].
        take (Forall _ (_ ++ _)) and apply Forall_app in it as (?&?).
        econstructor...
        * apply He; auto.
          intros * Free.
          apply RRx; constructor.
          apply Exists_app; auto.
        * apply Forall_app; split; apply Forall_forall; intros * Hin.
          -- repeat (take (Forall _ es1) and eapply Forall_forall in it; eauto).
             apply it; auto.
             intros * Free.
             apply RRx; constructor.
             apply Exists_app'; left; auto.
             apply Exists_exists; eauto.
          -- repeat (take (Forall _ es2) and eapply Forall_forall in it; eauto).
             apply it1; auto.
             intros * Free.
             apply RRx; constructor.
             apply Exists_app; right; right; auto.
             apply Exists_exists; eauto.
      + take (sem_var_instant _ _ _) and eapply (sem_var_instant_switch_env _ R') in it...
        econstructor; eauto.
        apply Forall_forall; intros * Hin.
        repeat (take (Forall _ _) and eapply Forall_forall in it; eauto).
        apply it; auto.
        intros * Free.
        apply RRx; constructor.
        apply Exists_exists; eauto.
      + take (sem_var_instant _ _ _) and eapply (sem_var_instant_switch_env _ R) in it; eauto.
        2: { rewrite RRx... }
        subst; take (Forall _ (_ ++ _ :: _)) and apply Forall_app in it as (Hes1 & Hes2');
          inversion_clear Hes2' as [|?? He Hes2].
        take (Forall _ (_ ++ _)) and apply Forall_app in it as (?&?).
        econstructor; eauto.
        * apply He; auto.
          intros * Free.
          apply RRx; constructor.
          apply Exists_app; auto.
        * apply Forall_app; split; apply Forall_forall; intros * Hin.
          -- repeat (take (Forall _ es1) and eapply Forall_forall in it; eauto).
             apply it; auto.
             intros * Free.
             apply RRx; constructor.
             apply Exists_app'; left; auto.
             apply Exists_exists; eauto.
          -- repeat (take (Forall _ es2) and eapply Forall_forall in it; eauto).
             apply it1; auto.
             intros * Free.
             apply RRx; constructor.
             apply Exists_app; right; right.
             apply Exists_exists; eauto.
      + take (sem_var_instant _ _ _) and eapply (sem_var_instant_switch_env _ R) in it; eauto.
        2: { rewrite RRx... }
        econstructor; eauto.
        apply Forall_forall; intros * Hin.
        repeat (take (Forall _ _) and eapply Forall_forall in it; eauto).
        apply it; auto.
        intros * Free.
        apply RRx; constructor.
        apply Exists_exists; eauto.

    - (* Ecase *)
      split; inversion_clear 1.
      + take (sem_exp_instant _ _ _ _) and eapply (sem_exp_instant_switch_env _ R') in it; eauto.
        2: { intros * Free; rewrite RRx... }
        econstructor; eauto.
        take (nth_error _ _ = _) and clear it.
        revert dependent l.
        induction vs; intros; (take (Forall2 _ _ _) and inv it); constructor;
          take (Forall _ (_ :: _)) and inversion_clear it as [|?? He].
        * apply He; auto.
          intros ? Hfree. destruct x; simpl in *; eauto 8 with nlfree.
        * apply IHvs; auto.
          inversion_clear 1; apply RRx...
      + take (sem_exp_instant _ _ _ _) and eapply (sem_exp_instant_switch_env _ R') in it...
        2: { intros * Free; rewrite RRx... }
        econstructor...
        apply Forall_forall; intros * Hin.
        repeat (take (Forall _ _) and eapply Forall_forall in it; eauto).
        apply it; auto.
        intros * Free.
        destruct x; simpl in *...
        apply RRx, FreeEcase_branches, Exists_exists...
      + take (sem_exp_instant _ _ _ _) and eapply (sem_exp_instant_switch_env _ R) in it...
        econstructor...
        take (nth_error _ _ = _) and clear it.
        revert dependent l.
        induction vs; intros; (take (Forall2 _ _ _) and inv it); constructor;
          take (Forall _ (_ :: _)) and inversion_clear it as [|?? He].
        * apply He; auto. intros ??.
          destruct x; simpl in *; eauto 8 with nlfree.
        * apply IHvs; auto.
          inversion_clear 1; apply RRx...
      + take (sem_exp_instant _ _ _ _) and eapply (sem_exp_instant_switch_env _ R) in it...
        econstructor; eauto.
        apply Forall_forall; intros * Hin.
        repeat (take (Forall _ _) and eapply Forall_forall in it; eauto).
        apply it; auto.
        intros * Free.
        destruct x; simpl in *...
        apply RRx, FreeEcase_branches, Exists_exists...

    - (* Eexp *)
      split; inversion_clear 1;
        take (sem_exp_instant _ _ _ _) and
             eapply sem_exp_instant_switch_env in it;
        eauto using sem_cexp_instant with nlfree;
        symmetry...
  Qed.

  Lemma sem_clock_instant_switch_env:
    forall b R R' ck v,
      (forall x, Is_free_in_clock x ck -> R x = R' x) ->
      sem_clock_instant b R ck v <-> sem_clock_instant b R' ck v.
  Proof.
    induction ck; intros v RRx.
    - (* Cbase *)
      split; inversion_clear 1; eauto using sem_clock_instant.
    - (* Con *)
      split; inversion_clear 1;
        take (sem_clock_instant _ _ _ _) and apply IHck in it;
        take (sem_var_instant _ _ _) and eapply sem_var_instant_switch_env in it;
        eauto using sem_clock_instant with nlfree;
        symmetry; auto with nlfree.
  Qed.

  Lemma sem_aexp_instant_switch_env:
    forall b R R' ck e v,
      (forall x, Is_free_in_clock x ck \/ Is_free_in_exp x e ->
            R x = R' x) ->
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
            R x = R' x) ->
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

  (** Well-typed expressions and free variables *)

  Lemma Is_free_in_wt_exp:
    forall tenv (xs : list (ident * (Op.type * clock))) x e,
      Is_free_in_exp x e ->
      wt_exp tenv (idty xs) e ->
      InMembers x xs.
  Proof.
    induction e; inversion_clear 1; inversion_clear 1; eauto using idty_InMembers;
      take (_ \/ _) and destruct it; auto.
  Qed.

  Lemma Is_free_in_wt_clock:
    forall tenv (xs : list (ident * (Op.type * clock))) x ck,
      Is_free_in_clock x ck ->
      wt_clock tenv (idty xs) ck ->
      InMembers x xs.
  Proof.
    induction ck; inversion_clear 1; inversion_clear 1;
      eauto using idty_InMembers.
  Qed.

  Lemma Is_free_in_wt_aexps:
    forall tenv (xs : list (ident * (Op.type * clock))) x ck es,
      Is_free_in_aexps x ck es ->
      Forall (wt_exp tenv (idty xs)) es ->
      wt_clock tenv (idty xs) ck ->
      InMembers x xs.
  Proof.
    intros * Fs WT WC.
    inv Fs; eauto using Is_free_in_wt_clock.
    take (Exists (Is_free_in_exp _) _) and
         apply Exists_exists in it as (? & Ix & ?).
    eapply Forall_forall in WT; eauto using Is_free_in_wt_exp.
  Qed.

  Lemma Is_free_in_wt_cexp:
    forall tenv (xs : list (ident * (Op.type * clock))) x e,
      Is_free_in_cexp x e ->
      wt_cexp tenv (idty xs) e ->
      InMembers x xs.
  Proof.
    induction e using cexp_ind2'; inversion_clear 1; inversion_clear 1; auto;
      eauto using Is_free_in_wt_exp, idty_InMembers.
    - take (Exists _ _) and apply Exists_exists in it as (ce & Hin & Free).
      repeat (take (Forall _ _) and eapply Forall_forall in it; eauto).
    - take (Exists _ _) and apply Exists_exists in it as (ce & Hin & Free).
      repeat (take (Forall _ _) and eapply Forall_forall in it; eauto).
      destruct Free as (?&?&?); subst.
      apply it; auto.
  Qed.

  Lemma Is_free_in_wt_rhs:
    forall tenv texterns (xs : list (ident * (Op.type * clock))) x e,
      Is_free_in_rhs x e ->
      wt_rhs tenv texterns (idty xs) e ->
      InMembers x xs.
  Proof.
    intros * Hf Hwt; inv Hf; inv Hwt; eauto using Is_free_in_wt_cexp.
    simpl_Exists. simpl_Forall. eauto using Is_free_in_wt_exp.
  Qed.

  Lemma Is_free_in_wt_aexp:
    forall tenv (xs : list (ident * (Op.type * clock))) x ck e,
      Is_free_in_aexp x ck e ->
      wt_exp tenv (idty xs) e ->
      wt_clock tenv (idty xs) ck ->
      InMembers x xs.
  Proof.
    intros * Fx WTe WTc.
    inv Fx; eauto using Is_free_in_wt_exp, Is_free_in_wt_clock.
  Qed.

  Lemma Is_free_in_wt_arhs:
    forall tenv texterns (xs : list (ident * (Op.type * clock))) x ck e,
      Is_free_in_arhs x ck e ->
      wt_rhs tenv texterns (idty xs) e ->
      wt_clock tenv (idty xs) ck ->
      InMembers x xs.
  Proof.
    intros * Fx WTe WTc.
    inv Fx; eauto using Is_free_in_wt_rhs, Is_free_in_wt_clock.
  Qed.

End CEPROPERTIES.

Module CEProperties
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX   Ids Op)
       (Cks   : CLOCKS          Ids Op OpAux)
       (Syn   : CESYNTAX        Ids Op OpAux Cks)
       (Str   : INDEXEDSTREAMS  Ids Op OpAux Cks)
       (Sem   : CESEMANTICS Ids Op OpAux Cks Syn Str)
       (Typ   : CETYPING    Ids Op OpAux Cks Syn)
       (IsF   : CEISFREE    Ids Op OpAux Cks Syn)
       <: CEPROPERTIES Ids Op OpAux Cks Syn Str Sem Typ IsF.
  Include CEPROPERTIES Ids Op OpAux Cks Syn Str Sem Typ IsF.
End CEProperties.
