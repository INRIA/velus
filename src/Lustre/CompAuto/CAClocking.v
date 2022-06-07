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
    Variable G1 : @global nolast_block last_prefs.
    Variable G2 : @global noauto_block auto_prefs.

    Hypothesis Hiface : global_iface_incl G1 G2.

    Lemma init_state_exp_wc {A} Γ Γ' (states : list (Op.enumtag * A)) : forall tx tn ck trans oth,
        (forall x, ~IsLast Γ' x) ->
        (forall x ck', HasClock Γ' x ck' -> HasClock Γ x ck /\ ck' = Cbase) ->
        wc_clock (idck Γ) ck ->
        Forall (fun '(e, t) => wc_exp G1 Γ' e /\ clockof e = [Cbase]) trans ->
        wc_exp G2 Γ (init_state_exp (Op.Tenum tx tn) ck trans oth).
    Proof.
      induction trans as [|(?&?)]; intros * Hnl Hck Hwck Hf; inv Hf; destruct_conjs; simpl.
      - apply add_whens_wc; auto. constructor.
      - econstructor; repeat constructor; simpl; auto; try congruence.
        + eapply subclock_exp_wc with (Γ:=Γ'); eauto using iface_incl_wc_exp.
          * intros * Hfind. rewrite Env.gempty in Hfind; congruence.
          * intros * _ Hack. apply Hck in Hack as (?&?); subst; auto.
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

    Lemma auto_scope_wc {A} P_nl P_wc f_auto :
      forall locs caus (blk: A) s' tys Γ Γ' st st',
        (forall x, ~IsLast Γ x) ->
        (forall x, ~IsLast Γ' x) ->
        nolast_scope P_nl (Scope locs caus blk) ->
        wc_scope P_wc G1 Γ (Scope locs caus blk) ->
        auto_scope f_auto (Scope locs caus blk) st = (s', tys, st') ->
        (forall Γ blks' tys st st',
            (forall x, ~IsLast Γ x) ->
            P_nl blk ->
            P_wc Γ blk ->
            f_auto blk st = (blks', tys, st') ->
            Forall (wc_block G2 (Γ'++Γ)) blks') ->
        wc_scope (fun Γ => Forall (wc_block G2 Γ)) G2 (Γ'++Γ) s'.
    Proof.
      intros * Hnl1 Hnl2 Hnl3 Hwc Hat Hind; inv Hnl3; inv Hwc; repeat inv_bind.
      econstructor; eauto.
      - simpl_Forall.
        eapply wc_clock_incl; [|eauto]. solve_incl_app.
      - simpl_Forall; subst; auto.
      - eapply Hind in H8; eauto.
        + now rewrite <-app_assoc.
        + repeat rewrite NoLast_app in *; repeat split; auto.
          intros ? Hl; inv Hl. simpl_In. simpl_Forall. subst; simpl in *; congruence.
    Qed.

    Lemma auto_block_wc : forall blk blk' tys Γ st st',
        (forall x, ~IsLast Γ x) ->
        nolast_block blk ->
        wc_block G1 Γ blk ->
        auto_block blk st = (blk', tys, st') ->
        wc_block G2 Γ blk'.
    Proof.
      Opaque auto_scope.
      induction blk using block_ind2; intros * Hnl1 Hnl2 Hwc (* Htypes  *)Hat; try destruct type;
        inv Hnl2; inv Hwc; repeat inv_bind.
      - (* equation *)
        constructor; eauto with lclocking.

      - (* reset *)
        econstructor; eauto with lclocking.
        auto_block_simpl_Forall.

      - (* switch *)
        econstructor; eauto with lclocking.
        + apply mmap2_values, Forall3_ignore3 in H0. inv H0; congruence.
        + auto_block_simpl_Forall.
          destruct s0. eapply auto_scope_wc with (Γ':=[]) in H10; eauto.
          * intros ??; eapply Hnl1; eauto.
          * intros * Hl. inv Hl. inv H11.
          * intros. auto_block_simpl_Forall.

      - (* automaton (weak) *)
        Local Ltac wc_automaton :=
          match goal with
          | Hincl: incl (?x::_) (types G2) |- In ?x G2.(types) =>
            apply Hincl; eauto with datatypes
          | |- HasClock _ _ _ =>
            apply HasClock_app; auto; right; econstructor; eauto with datatypes
          | |- IsLast _ _ =>
            apply IsLast_app; auto
          | |- wc_clock _ _ =>
            eapply wc_clock_incl; [|eauto]; solve_incl_app
          | _ => idtac
          end.

        do 2 econstructor; eauto; simpl.
        3:repeat (apply Forall_cons); auto.
        + repeat apply Forall_cons; auto. all:wc_automaton.
        + repeat constructor.
        + econstructor. repeat constructor.
          all:wc_automaton.
          *{ eapply init_state_exp_wc in H10; eauto.
             - intros ??. eapply Hnl1; eauto.
             - intros. edestruct H8; eauto. rewrite HasClock_app; eauto.
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
            -- edestruct H8; eauto.
          * intros *. rewrite 2 IsLast_app. intros [|]; eauto.
            take (IsLast _ _) and inv it. simpl in *.
            take (_ \/ _) and destruct it as [Heq|[Heq|[Heq|[Heq|Heq]]]]; inv Heq; right; econstructor; eauto with datatypes.
          * auto_block_simpl_Forall. destruct s0; destruct p as (?&?).
            econstructor; eauto. 1,2:repeat constructor. rewrite app_nil_r. econstructor; eauto; repeat constructor.
            2:{ simpl. econstructor; eauto with datatypes. }
            take (auto_scope _ _ _ = _) and eapply auto_scope_wc in it; eauto.
            1:{ intros ??. eapply Hnl1; eauto. }
            1:{ intros ? Hl; inv Hl. simpl_In.
                destruct Hin as [Heq|[Heq|[Heq|[Heq|Heq]]]]; inv Heq; simpl in *; congruence. }
            intros; repeat inv_bind. repeat constructor.
            repeat constructor.
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
        3:repeat (apply Forall_cons); auto.
        + repeat apply Forall_cons; auto. all:wc_automaton.
        + repeat constructor.
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
            -- edestruct H8; eauto.
          * intros *. rewrite 2 IsLast_app. intros [|]; eauto.
            take (IsLast _ _) and inv it. simpl in *.
            take (_ \/ _) and destruct it as [Heq|[Heq|[Heq|[Heq|Heq]]]]; inv Heq; right; econstructor; eauto with datatypes.
          *{ simpl_Forall. econstructor; eauto. 1,2:constructor; auto.
             simpl. rewrite app_nil_r.
             econstructor; simpl; eauto. repeat constructor.
             - eapply trans_exp_wc. simpl_Forall.
               split; auto. eapply wc_exp_incl; [| |eauto]; intros; wc_automaton.
             - rewrite trans_exp_clockof. repeat constructor.
               1,2:subst; rewrite HasClock_app; left; simpl; econstructor; eauto with datatypes.
             - constructor. subst; rewrite HasClock_app; left; simpl; econstructor; eauto with datatypes.
            }
        + remember [_;_;_;_] as Γ''.
          eapply wc_Bswitch with (Γ':=map (fun '(x, e) => (x, ann_with_clock e Cbase)) Γ''++Γ'); simpl; eauto; wc_automaton.
          * subst. constructor; wc_automaton.
          * take (mmap2 _ _ _ = _) and apply mmap2_values, Forall3_ignore3 in it. inv it; auto; congruence.
          * intros *. rewrite 2 HasClock_app. subst; intros [|]; eauto.
            -- take (HasClock _ _ _) and inv it. simpl in *.
               take (_ \/ _) and destruct it as [Heq|[Heq|[Heq|[Heq|Heq]]]]; inv Heq; split; auto; right; econstructor; eauto with datatypes.
            -- edestruct H8; eauto.
          * intros *. rewrite 2 IsLast_app. intros [|]; eauto.
            take (IsLast _ _) and inv it. simpl in *.
            take (_ \/ _) and destruct it as [Heq|[Heq|[Heq|[Heq|Heq]]]]; inv Heq; right; econstructor; eauto with datatypes.
          * auto_block_simpl_Forall. destruct s0; destruct p as (?&?).
            econstructor; eauto. 1,2:repeat constructor. rewrite app_nil_r. econstructor; eauto; repeat constructor.
            2:{ simpl. econstructor; eauto with datatypes. }
            take (auto_scope _ _ _ = _) and eapply auto_scope_wc in it; eauto.
            1:{ intros ??. eapply Hnl1; eauto. }
            1:{ intros ? Hl; inv Hl. simpl_In.
                destruct Hin as [Heq|[Heq|[Heq|[Heq|Heq]]]]; inv Heq; simpl in *; congruence. }
            intros; repeat inv_bind. repeat constructor.
            auto_block_simpl_Forall.
            take (wc_block _ _ _) and eapply H in it; eauto.
            eapply wc_block_incl; [| |eauto]; intros * Hi; inv Hi; econstructor; eauto with datatypes.

      - (* local *)
        econstructor; eauto.
        eapply auto_scope_wc with (Γ':=[]) in H3; eauto.
        + intros * Hl. inv Hl. inv H2.
        + intros. auto_block_simpl_Forall.
    Qed.

    Lemma auto_node_wc : forall n,
        wc_node G1 n ->
        wc_node G2 (fst (auto_node n)).
    Proof.
      intros * Hwcn.
      destruct Hwcn as (Hwc1&Hwc2&Hwc3).
      repeat split; auto.
      unfold auto_node in *; simpl in *.
      destruct (auto_block _ _) as ((blk'&?)&?) eqn:Haut; simpl in *.
      eapply auto_block_wc; eauto.
      - apply senv_of_inout_NoLast.
      - apply n_syn.
    Qed.

  End wc_node.

  Theorem auto_global_wc : forall G,
      wc_global G ->
      wc_global (auto_global G).
  Proof.
    intros (enms&nds). revert enms.
    induction nds; intros * Hwc.
    - constructor.
    - inv Hwc. destruct H1 as (Hwcn&Hnames).
      assert (wc_global {| types := enms; nodes := nds |}) as Hwc' by auto.
      specialize (IHnds _ Hwc').
      constructor; simpl in *; auto with datatypes. split.
      + eapply auto_node_wc; eauto.
        eapply global_iface_incl_trans. apply auto_global_iface_incl.
        split; simpl; solve_incl_app.
        intros * Hfind. do 2 esplit; eauto. 2:apply node_iface_eq_refl.
        erewrite find_node_change_types. apply Hfind; eauto.
      + simpl_Forall.
        apply in_map_iff in H as (?&?&Hin); subst. apply in_map_iff in Hin as (?&?&Hin); subst.
        simpl_Forall. auto.
      + eapply Forall'_impl; [|eapply IHnds].
        intros * (?&?). split; auto.
        eapply iface_incl_wc_node; eauto. simpl.
        split; simpl; solve_incl_app.
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
