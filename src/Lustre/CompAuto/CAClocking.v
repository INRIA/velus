From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Velus Require Import Common.
From Velus Require Import Operators Environment.
From Velus Require Import Clocks.
From Velus Require Import Lustre.StaticEnv.
From Velus Require Import Lustre.LSyntax Lustre.LClocking.
From Velus Require Import Lustre.CompAuto.CompAuto.
From Velus Require Import Lustre.SubClock.SCClocking.

Module Type CACLOCKING
       (Import Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Import Cks : CLOCKS Ids Op OpAux)
       (Import Senv : STATICENV Ids Op OpAux Cks)
       (Import Syn : LSYNTAX Ids Op OpAux Cks Senv)
       (Import Clo : LCLOCKING Ids Op OpAux Cks Senv Syn)
       (Import CA  : COMPAUTO Ids Op OpAux Cks Senv Syn).

  Module Import SCC := SCClockingFun Ids Op OpAux Cks Senv Syn Clo SC. Import SC.

  Ltac inv_branch := (Syn.inv_branch || Clo.inv_branch).
  Ltac inv_scope := (Syn.inv_scope || Clo.inv_scope).
  Ltac inv_block := (Syn.inv_block || Clo.inv_block).

  Import Fresh Notations Facts Tactics.
  Local Open Scope fresh_monad_scope.

  Lemma init_state_exp_clockof : forall ty ck trans def,
      clockof (init_state_exp ty ck trans def) = [ck].
  Proof.
    induction trans as [|(?&?)]; intros *; simpl; auto.
    apply add_whens_clockof; auto.
  Qed.

  Lemma trans_exp_clockof : forall ty trans def,
      clocksof (trans_exp ty trans def) = [Cbase; Cbase].
  Proof.
    induction trans as [|(?&?&?)]; intros *; simpl; auto.
  Qed.

  Section wc_node.
    Variable G1 : @global complete elab_prefs.
    Variable G2 : @global noauto auto_prefs.

    Hypothesis Hiface : global_iface_incl G1 G2.

    Lemma init_state_exp_wc {A} Γ Γ' (states : list (Op.enumtag * A)) : forall tx tn ck trans oth,
        (forall x ck', HasClock Γ' x ck' -> HasClock Γ x ck /\ ck' = Cbase) ->
        (forall x, IsLast Γ' x -> IsLast Γ x) ->
        wc_clock (idck Γ) ck ->
        Forall (fun '(e, t) => wc_exp G1 Γ' e /\ clockof e = [Cbase]) trans ->
        wc_exp G2 Γ (init_state_exp (Op.Tenum tx tn) ck trans oth).
    Proof.
      induction trans as [|(?&?)]; intros * Hck Hl Hwck Hf; inv Hf; destruct_conjs; simpl.
      - apply add_whens_wc; auto. constructor.
      - econstructor; repeat constructor; simpl; auto; try congruence.
        + eapply subclock_exp_wc with (Γ:=Γ'); eauto using iface_incl_wc_exp.
          * intros * _ Hack. apply Hck in Hack as (?&?); subst; auto.
          * intros * _ Hack Hl'. apply Hck in Hack as (?&?); subst; auto.
          * intros * Hfind. rewrite Env.gempty in Hfind; congruence.
          * intros * Hfind. rewrite Env.gempty in Hfind; congruence.
        + rewrite subclock_exp_clockof, H0; eauto.
        + apply add_whens_wc; auto. constructor.
        + rewrite add_whens_clockof; simpl; auto.
        + rewrite init_state_exp_clockof; simpl; auto.
        + rewrite add_whens_clockof; simpl; auto.
        + rewrite init_state_exp_clockof; simpl; auto.
    Qed.

    Lemma trans_exp_wc Γ : forall tx tn trans oth,
        Forall (fun '(e, _) => wc_exp G1 Γ e /\ clockof e = [Cbase]) trans ->
        Forall (wc_exp G2 Γ) (trans_exp (Op.Tenum tx tn) trans oth).
    Proof.
      induction trans as [|(?&?&?)]; intros * Hf; inv Hf; destruct_conjs; simpl.
      - repeat constructor; auto.
      - repeat constructor; eauto using iface_incl_wc_exp; simpl; try congruence.
        + rewrite trans_exp_clockof; auto.
        + rewrite trans_exp_clockof; auto.
    Qed.

    Lemma auto_scope_wc {A} P_wc f_auto :
      forall locs (blk: A) s' tys Γ Γ' st st',
        wc_scope P_wc G1 Γ (Scope locs blk) ->
        auto_scope f_auto (Scope locs blk) st = (s', tys, st') ->
        (forall Γ blks' tys st st',
            P_wc Γ blk ->
            f_auto blk st = (blks', tys, st') ->
            Forall (wc_block G2 (Γ'++Γ)) blks') ->
        wc_scope (fun Γ => Forall (wc_block G2 Γ)) G2 (Γ'++Γ) s'.
    Proof.
      intros * Hwc Hat Hind; repeat inv_scope; repeat inv_bind; subst Γ'0.
      econstructor; eauto.
      - simpl_Forall.
        eapply wc_clock_incl; [|eauto]. solve_incl_app.
      - take (P_wc _ _ ) and eapply Hind in it; eauto.
        + now rewrite <-app_assoc.
    Qed.

    Lemma auto_block_wc : forall blk blk' tys Γ st st',
        wc_block G1 Γ blk ->
        auto_block blk st = (blk', tys, st') ->
        wc_block G2 Γ blk'.
    Proof.
      Opaque auto_scope.
      induction blk using block_ind2; intros * Hwc (* Htypes  *)Hat; try destruct type;
        repeat inv_block; repeat inv_bind.
      - (* equation *)
        constructor; eauto with lclocking.

      - (* last *)
        econstructor; eauto with lclocking.

      - (* reset *)
        econstructor; eauto with lclocking.
        auto_block_simpl_Forall.

      - (* switch *)
        econstructor; eauto with lclocking.
        + apply mmap2_values, Forall3_ignore3 in H0. inv H0; congruence.
        + auto_block_simpl_Forall.
          repeat inv_branch. repeat inv_bind. constructor.
          auto_block_simpl_Forall.

      - (* automaton (weak) *)
        Local Ltac wc_automaton :=
          match goal with
          | Hincl: incl (?x::_) (types G2) |- In ?x G2.(types) =>
            apply Hincl; eauto with datatypes
          | |- HasClock _ _ _ =>
            apply HasClock_app; auto; right; econstructor; eauto with datatypes
          | H:HasClock ?x _ _ |- HasClock (_::_::_::_::?x) _ _ => inv H; econstructor; eauto with datatypes
          | |- IsLast _ _ =>
            apply IsLast_app; auto
          | H:IsLast ?x _ |- IsLast (_::_::_::_::?x) _ => inv H; econstructor; eauto with datatypes
          | |- wc_clock _ _ =>
            eapply wc_clock_incl; [|eauto]; solve_incl_app
          | _ => idtac
          end.

        do 2 econstructor; eauto; simpl.
        2:repeat (apply Forall_cons); auto.
        + repeat apply Forall_cons; auto. all:wc_automaton.
        + econstructor. repeat constructor.
          all:wc_automaton.
          *{ eapply init_state_exp_wc in H9; eauto.
             - intros. edestruct H7; eauto. rewrite HasClock_app; eauto.
             - intros. rewrite IsLast_app; eauto.
             - wc_automaton.
           }
          * apply add_whens_wc; auto. wc_automaton.
            constructor.
          * simpl. rewrite init_state_exp_clockof, add_whens_clockof; auto.
        + remember [_;_;_;_] as Γ''.
          eapply wc_Bswitch with (Γ':=map (fun '(x, e) => (x, ann_with_clock e Cbase)) Γ''++Γ'); simpl; eauto; wc_automaton.
          * subst. constructor; wc_automaton.
          * take (mmap2 _ _ _ = _) and apply mmap2_values, Forall3_ignore3 in it; inv it; auto; congruence.
          * intros *. rewrite 2 HasClock_app. subst; intros [|]; eauto.
            -- take (HasClock _ _ _) and inv it. simpl in *.
               take (_ \/ _) and destruct it as [Heq|[Heq|[Heq|[Heq|Heq]]]]; inv Heq; split; auto; right; econstructor; eauto with datatypes.
            -- edestruct H7; eauto.
          * intros *. rewrite 2 IsLast_app. intros [|]; eauto.
            take (IsLast _ _) and inv it. simpl in *.
            take (_ \/ _) and destruct it as [Heq|[Heq|[Heq|[Heq|Heq]]]]; inv Heq; right; econstructor; eauto with datatypes.
          * auto_block_simpl_Forall. repeat inv_branch; destruct s as [?(?&?)]; repeat inv_bind.
            do 3 econstructor; eauto. 3:simpl; eauto. 1,2:repeat constructor.
            2:{ simpl. econstructor; eauto with datatypes. }
            take (auto_scope _ _ _ = _) and eapply auto_scope_wc with (Γ':=[_;_;_;_]) in it; simpl in *; eauto.
            intros; repeat inv_bind. repeat constructor.
            { eapply trans_exp_wc; eauto.
              simpl_Forall. split; auto.
              eapply wc_exp_incl; [| |eauto]; intros * Hi; inv Hi; econstructor; eauto with datatypes. }
            { rewrite trans_exp_clockof; repeat constructor; econstructor; eauto with datatypes. }
            { auto_block_simpl_Forall.
              take (wc_block _ _ _) and eapply H in it; eauto.
              - eapply wc_block_incl; [| |eauto]; intros * Hi; inv Hi; econstructor; eauto with datatypes.
            }

      - (* automaton (strong) *)
        do 2 econstructor; eauto; simpl.
        2:repeat (apply Forall_cons); auto.
        + repeat apply Forall_cons; auto. all:wc_automaton.
        + econstructor. repeat constructor.
          all:wc_automaton.
          * apply add_whens_wc; auto. wc_automaton.
            constructor.
          * apply add_whens_wc; auto. wc_automaton.
            constructor.
          * simpl. rewrite 2 add_whens_clockof; auto.
        + remember [_;_;_;_] as Γ''.
          eapply wc_Bswitch with (Γ':=map (fun '(x, e) => (x, ann_with_clock e Cbase)) Γ''++Γ'); simpl; eauto.
          * constructor. subst. wc_automaton.
          * destruct states; simpl in *; try congruence. auto.
          * intros *. rewrite 2 HasClock_app. subst; intros [|]; eauto.
            -- take (HasClock _ _ _) and inv it. simpl in *.
               take (_ \/ _) and destruct it as [Heq|[Heq|[Heq|[Heq|Heq]]]]; inv Heq; split; auto; right; econstructor; eauto with datatypes.
            -- edestruct H7; eauto.
          * intros *. rewrite 2 IsLast_app. intros [|]; eauto.
            take (IsLast _ _) and inv it. simpl in *.
            take (_ \/ _) and destruct it as [Heq|[Heq|[Heq|[Heq|Heq]]]]; inv Heq; right; econstructor; eauto with datatypes.
          *{ simpl_Forall. repeat inv_branch; repeat inv_bind. do 2 econstructor; eauto.
             econstructor; simpl; eauto. repeat constructor.
             - eapply trans_exp_wc. simpl_Forall.
               split; auto. eapply wc_exp_incl; [| |eauto]; intros; wc_automaton.
             - rewrite trans_exp_clockof. repeat constructor.
               1,2:econstructor; eauto with datatypes.
             - constructor. econstructor; eauto with datatypes.
            }
        + remember [_;_;_;_] as Γ''.
          eapply wc_Bswitch with (Γ':=map (fun '(x, e) => (x, ann_with_clock e Cbase)) Γ''++Γ'); simpl; eauto; wc_automaton.
          * subst. constructor; wc_automaton.
          * take (mmap2 _ _ _ = _) and apply mmap2_values, Forall3_ignore3 in it. inv it; auto; congruence.
          * intros *. rewrite 2 HasClock_app. subst; intros [|]; eauto.
            -- take (HasClock _ _ _) and inv it. simpl in *.
               take (_ \/ _) and destruct it as [Heq|[Heq|[Heq|[Heq|Heq]]]]; inv Heq; split; auto; right; econstructor; eauto with datatypes.
            -- edestruct H7; eauto.
          * intros *. rewrite 2 IsLast_app. intros [|]; eauto.
            take (IsLast _ _) and inv it. simpl in *.
            take (_ \/ _) and destruct it as [Heq|[Heq|[Heq|[Heq|Heq]]]]; inv Heq; right; econstructor; eauto with datatypes.
          * auto_block_simpl_Forall. repeat inv_branch. destruct s as [?(?&?)]; repeat inv_bind.
            do 3 econstructor; eauto. 1,2:repeat constructor. 3:simpl; eauto.
            2:{ simpl. econstructor; eauto with datatypes. }
            take (auto_scope _ _ _ = _) and eapply auto_scope_wc with (Γ':=[_;_;_;_]) in it; simpl in *; eauto.
            intros; repeat inv_bind. repeat constructor.
            auto_block_simpl_Forall.
            take (wc_block _ _ _) and eapply H in it; eauto.
            eapply wc_block_incl; [| |eauto]; intros * Hi; inv Hi; econstructor; eauto with datatypes.

      - (* local *)
        econstructor; eauto.
        eapply auto_scope_wc with (Γ':=[]) in H2; eauto.
        + intros. auto_block_simpl_Forall.
    Qed.

    Lemma auto_node_wc : forall n,
        wc_node G1 n ->
        wc_node G2 (fst (auto_node n)).
    Proof.
      intros * Hwcn. inv Hwcn.
      pose proof (n_syn n) as Hsyn. inv Hsyn.
      repeat split; auto.
      - unfold auto_node in *; simpl in *.
        destruct (auto_block _ _) as ((blk'&?)&?) eqn:Haut; simpl in *.
        eapply auto_block_wc; eauto.
    Qed.

  End wc_node.

  Theorem auto_global_wc : forall G,
      wc_global G ->
      wc_global (auto_global G).
  Proof.
    intros []. revert types0.
    induction nodes0; intros * Hwc.
    - constructor.
    - inv Hwc. destruct H1 as (Hwcn&Hnames).
      assert (wc_global {| types := types0; externs := externs0; nodes := nodes0 |}) as Hwc' by auto.
      specialize (IHnodes0 _ Hwc').
      constructor; simpl in *; auto with datatypes. split.
      + eapply auto_node_wc; eauto.
        eapply global_iface_incl_trans. apply auto_global_iface_incl.
        repeat split; simpl; solve_incl_app.
        intros * Hfind. do 2 esplit; eauto. 2:apply node_iface_eq_refl.
        erewrite find_node_change_types. apply Hfind; eauto.
      + simpl_Forall. simpl_In.
        simpl_Forall. auto.
      + eapply Forall'_impl; [|eapply IHnodes0].
        intros * (?&?). split; auto.
        eapply iface_incl_wc_node; eauto. simpl.
        repeat split; simpl; solve_incl_app.
        intros * Hfind. do 2 esplit; eauto. 2:apply node_iface_eq_refl.
        erewrite find_node_change_types, Hfind; eauto.
  Qed.

End CACLOCKING.

Module CAClockingFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks : CLOCKS Ids Op OpAux)
       (Senv : STATICENV Ids Op OpAux Cks)
       (Syn : LSYNTAX Ids Op OpAux Cks Senv)
       (Clo : LCLOCKING Ids Op OpAux Cks Senv Syn)
       (CA  : COMPAUTO Ids Op OpAux Cks Senv Syn)
       <: CACLOCKING Ids Op OpAux Cks Senv Syn Clo CA.
  Include CACLOCKING Ids Op OpAux Cks Senv Syn Clo CA.
End CAClockingFun.
