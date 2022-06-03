From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Velus Require Import Common.
From Velus Require Import Operators Environment.
From Velus Require Import Clocks.
From Velus Require Import Fresh.
From Velus Require Import Lustre.StaticEnv.
From Velus Require Import Lustre.LSyntax Lustre.LTyping.
From Velus Require Import Lustre.CompAuto.CompAuto.
From Velus Require Import Lustre.SubClock.SCTyping.

Module Type CATYPING
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks : CLOCKS Ids Op OpAux)
       (Import Senv : STATICENV Ids Op OpAux Cks)
       (Import Syn : LSYNTAX Ids Op OpAux Cks Senv)
       (Import Typ : LTYPING Ids Op OpAux Cks Senv Syn)
       (Import IL  : COMPAUTO Ids Op OpAux Cks Senv Syn).

  Module Import SCT := SCTypingFun Ids Op OpAux Cks Senv Syn Typ SC. Import SC.

  Import Fresh Notations Facts Tactics.
  Local Open Scope fresh_monad_scope.

  Lemma init_state_exp_typeof : forall ty ck trans def,
      typeof (init_state_exp ty ck trans def) = [ty].
  Proof.
    induction trans as [|(?&?)]; intros *; simpl; auto.
    apply add_whens_typeof; auto.
  Qed.

  Lemma trans_exp_typeof : forall ty trans def,
      typesof (trans_exp ty trans def) = [ty; OpAux.bool_velus_type].
  Proof.
    induction trans as [|(?&?&?)]; intros *; simpl; auto.
  Qed.

  Import Permutation.

  Section wt_node.
    Variable G1 : @global nolast_block last_prefs.
    Variable G2 : @global noauto_block auto_prefs.

    Hypothesis HwtG1 : wt_global G1.
    Hypothesis Hiface : global_iface_incl G1 G2.

    Lemma init_state_exp_wt {A} Γ (states : list (Op.enumtag * A)) : forall tx tn ck trans oth,
        wt_type G2.(types) (Tenum tx tn) ->
        (forall x, ~IsLast Γ x) ->
        wt_clock G2.(types) Γ ck ->
        Permutation.Permutation (map fst states) (seq 0 (length tn)) ->
        Forall (fun '(e, t) => wt_exp G1 Γ e /\ typeof e = [OpAux.bool_velus_type] /\ InMembers t states) trans ->
        InMembers oth states ->
        wt_exp G2 Γ (init_state_exp (Op.Tenum tx tn) ck trans oth).
    Proof.
      induction trans as [|(?&?)]; intros * Htype Hnl Hwtc Hperm Hf Hoth; inv Hf; destruct_conjs; simpl.
      - apply add_whens_wt; auto.
        econstructor; auto; simpl.
        rewrite fst_InMembers, Hperm in Hoth. apply in_seq in Hoth; lia.
      - econstructor; repeat constructor; simpl; auto.
        + eapply subclock_exp_wt; eauto using iface_incl_wt_exp.
          intros * Hfind. rewrite Env.gempty in Hfind; congruence.
        + rewrite subclock_exp_typeof; eauto.
        + apply Hiface. destruct HwtG1 as (Hbool&_). now inv Hbool.
        + simpl. apply perm_swap.
        + congruence.
        + apply add_whens_wt; auto.
          constructor; auto.
          rewrite fst_InMembers, Hperm in H1. apply in_seq in H1; simpl in *; lia.
        + rewrite add_whens_typeof; auto.
        + rewrite init_state_exp_typeof; auto.
    Qed.

    Lemma trans_exp_wt {A} Γ (states : list (Op.enumtag * A)) : forall tx tn trans oth,
        wt_type G2.(types) (Tenum tx tn) ->
        Permutation.Permutation (map fst states) (seq 0 (length tn)) ->
        Forall (fun '(e, (t, _)) => wt_exp G1 Γ e /\ typeof e = [OpAux.bool_velus_type] /\ InMembers t states) trans ->
        InMembers oth states ->
        Forall (wt_exp G2 Γ) (trans_exp (Op.Tenum tx tn) trans oth).
    Proof.
      induction trans as [|(?&?&?)]; intros * Henum Hperm Hf Hoth; inv Hf; destruct_conjs; simpl.
      - constructor; [|constructor]; auto; constructor; auto.
        + rewrite fst_InMembers, Hperm in Hoth. apply in_seq in Hoth; simpl in *; lia.
        + eapply iface_incl_wt_type, HwtG1; eauto.
        + unfold false_tag. simpl. lia.
      - repeat constructor; auto. econstructor; eauto using iface_incl_wt_exp; simpl.
        + apply Hiface. destruct HwtG1 as (Hbool&_). now inv Hbool.
        + apply perm_swap.
        + congruence.
        + repeat apply Forall_cons; eauto.
          * constructor; auto.
            rewrite fst_InMembers, Hperm in H1. apply in_seq in H1; simpl in *; lia.
          * constructor. eapply iface_incl_wt_type, HwtG1; eauto.
            unfold OpAux.true_tag, OpAux.false_tag. destruct b; simpl; lia.
        + repeat apply Forall_cons; auto; simpl.
          rewrite trans_exp_typeof; auto.
        + constructor.
    Qed.

    Lemma auto_scope_wt {A} P_nl P_wt f_auto aft :
      forall locs caus (blk: A) s' tys Γ Γ' st st',
        st_valid_after st auto aft ->
        (forall x, ~IsLast Γ x) ->
        nolast_scope P_nl (Scope locs caus blk) ->
        wt_scope P_wt G1 Γ (Scope locs caus blk) ->
        incl tys G2.(types) ->
        auto_scope f_auto (Scope locs caus blk) st = (s', tys, st') ->
        (forall Γ blks' tys st st',
            st_valid_after st auto aft ->
            (forall x, ~IsLast Γ x) ->
            P_nl blk ->
            P_wt Γ blk ->
            f_auto blk st = (blks', tys, st') ->
            incl (concat tys) G2.(types) ->
            Forall (wt_block G2 (Γ'++Γ)) blks') ->
        wt_scope (fun Γ => Forall (wt_block G2 Γ)) G2 (Γ'++Γ) s'.
    Proof.
      intros * Hvalid Hnl1 Hnl3 Hwt Hincl Hat Hind; inv Hnl3; inv Hwt; repeat inv_bind.
      econstructor; eauto.
      - unfold wt_clocks in *. simpl_Forall.
        eapply wt_clock_incl; [|eauto with ltyping].
        intros. repeat rewrite HasType_app in *. intuition.
      - simpl_Forall; subst; eauto with ltyping.
      - simpl_Forall; subst; eauto.
      - eapply Hind in H9; eauto.
        + now rewrite <-app_assoc.
        + repeat rewrite NoLast_app in *; repeat split; auto.
          intros ? Hl; inv Hl. simpl_In. simpl_Forall. subst; simpl in *; congruence.
    Qed.

  Ltac auto_block_simpl_Forall :=
    repeat
      (match goal with
       | Hmap: mmap2 _ _ _ = (?blks', _, _) |- Forall _ ?blks' =>
         eapply mmap2_values_valid, Forall3_ignore13 in Hmap; simpl_Forall
       end; repeat inv_bind);
    eauto.

    Lemma auto_block_wt aft : forall blk blk' tys Γ st st',
        st_valid_after st auto aft ->
        (forall x, ~IsLast Γ x) ->
        nolast_block blk ->
        wt_block G1 Γ blk ->
        incl tys G2.(types) ->
        auto_block blk st = (blk', tys, st') ->
        wt_block G2 Γ blk'.
    Proof.
      Opaque auto_scope.
      induction blk using block_ind2; intros * Hvalid Hnl1 Hnl2 Hwt Htypes Hat;
        inv Hnl2; inv Hwt; repeat inv_bind.
      - (* equation *)
        constructor; eauto with ltyping.

      - (* reset *)
        constructor; eauto with ltyping.
        auto_block_simpl_Forall; eauto using auto_block_st_valid.
        take (auto_block _ _ = _) and eapply H in it; eauto.
        etransitivity; eauto using incl_concat.

      - (* switch *)
        econstructor; eauto with ltyping.
        + apply Hiface; auto.
        + assert (map fst x = map fst branches) as Heq; [|setoid_rewrite Heq]; auto.
          apply mmap2_values, Forall3_ignore3 in H0.
          apply Forall2_map_eq, Forall2_swap_args. simpl_Forall; repeat inv_bind; auto.
        + apply mmap2_values, Forall3_ignore3 in H0. inv H0; congruence.
        + auto_block_simpl_Forall.
          2:{ intros; destruct_conjs; repeat inv_bind; eauto using auto_scope_st_valid1. }
          destruct s0. eapply auto_scope_wt with (Γ':=[]) in H11; eauto.
          * etransitivity; eauto using incl_concat.
          * intros. auto_block_simpl_Forall; eauto using auto_block_st_valid.
            take (auto_block _ _ = _) and eapply H in it; eauto.
            etransitivity; eauto using incl_concat.

      - (* automaton (weak) *)
        Local Ltac wt_automaton :=
          match goal with
          | Hincl: incl (?x::_) (types G2) |- In ?x G2.(types) =>
            apply Hincl; eauto with datatypes
          | |- HasType _ _ _ =>
            apply HasType_app; auto; right; econstructor; eauto with datatypes
          | |- IsLast _ _ =>
            apply IsLast_app; auto
          | |- wt_clock _ _ _ =>
            eapply wt_clock_incl; [|eauto with ltyping]; intros; apply HasType_app; auto
          | _ => idtac
          end.

        assert (length x1 = length states) as Hlen by (eapply generate_constructors_length; eauto).
        assert (wt_type G2.(types) (Tenum x x1)) as Hwty.
        { constructor; auto with datatypes.
          - rewrite Hlen.
            destruct states; simpl in *; try lia.
          - take (generate_constructors _ _ = _) and eapply generate_constructors_NoDup in it; eauto with fresh.
        }
        assert (wt_type (types G2) bool_velus_type) as Hwtbool
            by (eapply iface_incl_wt_type, HwtG1; eauto).

        do 2 econstructor; eauto; simpl.
        4:repeat (apply Forall_cons); auto.
        + unfold wt_clocks; repeat constructor; simpl.
          all:wt_automaton.
        + repeat (apply Forall_cons); auto.
        + repeat constructor.
        + econstructor. repeat constructor.
          all:wt_automaton.
          * eapply init_state_exp_wt; eauto; wt_automaton.
            1:{ apply NoLast_app; split; auto. intros * Hl; inv Hl; simpl in *.
                destruct H14 as [Heq|[Heq|[Heq|[Heq|Heq]]]]; inv Heq; simpl in *; congruence. }
            1:{ now rewrite Hlen. }
            simpl_Forall; split; auto. eapply wt_exp_incl; [| |eauto]; intros; wt_automaton.
          * apply add_whens_wt; auto; wt_automaton.
            constructor; simpl; auto.
          * simpl. rewrite app_nil_r.
            rewrite add_whens_typeof, init_state_exp_typeof; simpl; auto.
        + eapply wt_block_incl with (Γ:=_++Γ).
          1,2:intros * Hin; [rewrite HasType_app in *||rewrite IsLast_app in *]; (destruct Hin; eauto).
          econstructor; simpl; eauto; wt_automaton.
          * constructor. econstructor; eauto with datatypes.
            eapply wt_clock_incl; [|eauto with ltyping]. intros * Ht; inv Ht; econstructor; eauto with datatypes.
          * rewrite Hlen.
            assert (map fst x11 = map fst states) as Heq; [|setoid_rewrite Heq]; auto.
            apply mmap2_values, Forall3_ignore3 in H13.
            clear - H13. induction H13; destruct_conjs; repeat inv_bind; auto.
          * apply mmap2_values, Forall3_ignore3 in H13. inv H13; auto; congruence.
          * auto_block_simpl_Forall. 2:eauto 7 with fresh.
            2:{ intros; destruct_conjs; repeat inv_bind; eauto using auto_scope_st_valid2. }
            destruct s0; destruct_conjs.
            econstructor; eauto; repeat constructor. 1,2:rewrite app_nil_r.
            2:{ econstructor; eauto with datatypes. }
            take (auto_scope _ _ _ = _) and eapply auto_scope_wt with (Γ':=[_;_;_;_]) in it; eauto. eapply it.
            1:{ etransitivity; eauto. eauto using incl_tl, incl_concat. }
            intros; repeat inv_bind.
            repeat constructor.
            { eapply trans_exp_wt; eauto using In_InMembers; wt_automaton. now rewrite Hlen.
              simpl_Forall; split; [|split]; eauto.
              eapply wt_exp_incl; [| |eauto]; intros * Hin; inv Hin; econstructor; eauto with datatypes.
            }
            { rewrite trans_exp_typeof; simpl.
              repeat constructor; econstructor; eauto with datatypes. }
            { auto_block_simpl_Forall. 2:intros; eauto using auto_block_st_valid.
              take (auto_block _ _ = _) and eapply H in it; eauto.
              - intros * Hl. inv Hl.
                take (_ \/ _) and destruct it as [Heq|[Heq|[Heq|[Heq|Heq]]]]; eauto; try inv Heq; simpl in *; try congruence.
                eapply H17; eauto with senv.
              - eapply wt_block_incl; [| |eauto]; intros * Hin; inv Hin; econstructor; eauto with datatypes.
              - etransitivity; eauto. eauto using incl_tl, incl_concat.
            }

      - (* automaton (strong) *)
        assert (length x1 = length states) as Hlen by (eapply generate_constructors_length; eauto).
        assert (wt_type G2.(types) (Tenum x x1)) as Hwty.
        { constructor; auto with datatypes.
          - rewrite Hlen.
            destruct states; simpl in *; try lia.
          - take (generate_constructors _ _ = _) and eapply generate_constructors_NoDup in it; eauto with fresh.
        }
        assert (wt_type (types G2) bool_velus_type) as Hwtbool
            by (eapply iface_incl_wt_type, HwtG1; eauto).

        do 2 econstructor; eauto; simpl.
        4:repeat (apply Forall_cons); auto.
        + unfold wt_clocks; repeat constructor; simpl.
          all:wt_automaton.
        + repeat (apply Forall_cons); auto.
        + repeat constructor.
        + econstructor. repeat constructor.
          all:wt_automaton.
          * apply add_whens_wt; auto; wt_automaton.
            econstructor; eauto.
            apply fst_InMembers in H7. rewrite H8 in H7. apply in_seq in H7 as (?&?); auto.
            now rewrite Hlen.
          * apply add_whens_wt; auto; wt_automaton.
            econstructor; simpl; eauto.
          * simpl. rewrite app_nil_r.
            rewrite 2 add_whens_typeof; simpl; auto.
        + econstructor; simpl; eauto. 5:simpl_Forall; econstructor; eauto. 5-7:constructor; auto.
          * repeat constructor. 1,2:wt_automaton.
          * apply Htypes; auto with datatypes.
          * erewrite Hlen, map_map, map_ext; eauto.
            intros; destruct_conjs; auto.
          * destruct states; simpl in *; try congruence.
          *{ rewrite app_nil_r. repeat constructor.
             - eapply trans_exp_wt; eauto using In_InMembers.
               + now rewrite Hlen.
               + simpl_Forall. split; [|split]; auto.
                 eapply wt_exp_incl; [| |eauto]; intros; wt_automaton.
             - rewrite trans_exp_typeof. repeat constructor. 1,2:wt_automaton.
             - wt_automaton.
            }
        + eapply wt_block_incl with (Γ:=_++Γ).
          1,2:intros * Hin; [rewrite HasType_app in *||rewrite IsLast_app in *]; (destruct Hin; eauto).
          econstructor; simpl; eauto; wt_automaton.
          * constructor. econstructor; eauto with datatypes.
            eapply wt_clock_incl; [|eauto with ltyping]. intros * Ht; inv Ht; econstructor; eauto with datatypes.
          * rewrite Hlen.
            assert (map fst x11 = map fst states) as Heq; [|setoid_rewrite Heq]; auto.
            apply mmap2_values, Forall3_ignore3 in H12.
            clear - H12. induction H12; destruct_conjs; repeat inv_bind; auto.
          * apply mmap2_values, Forall3_ignore3 in H12. inv H12; auto; congruence.
          * auto_block_simpl_Forall. 2:eauto 7 with fresh.
            2:{ intros; destruct_conjs; repeat inv_bind; eauto using auto_scope_st_valid3. }
            destruct s0; destruct_conjs.
            econstructor; eauto; repeat constructor. 1,2:rewrite app_nil_r.
            2:{ econstructor; eauto with datatypes. }
            take (auto_scope _ _ _ = _) and eapply auto_scope_wt with (Γ':=[_;_;_;_]) in it; eauto. eapply it.
            1:{ etransitivity; eauto. eauto using incl_tl, incl_concat. }
            intros; repeat inv_bind.
            { auto_block_simpl_Forall. 2:intros; eauto using auto_block_st_valid.
              take (auto_block _ _ = _) and eapply H in it; eauto.
              - intros * Hl. inv Hl.
                destruct H25 as [Heq|[Heq|[Heq|[Heq|Heq]]]]; eauto; try inv Heq; simpl in *; try congruence.
                eapply H18; eauto with senv.
              - eapply wt_block_incl; [| |eauto]; intros * Hin; inv Hin; econstructor; eauto with datatypes.
              - etransitivity; eauto. eauto using incl_tl, incl_concat.
            }

      - (* local *)
        constructor.
        eapply auto_scope_wt with (Γ':=[]) in H0; eauto.
        + intros. auto_block_simpl_Forall. 2:eauto using auto_block_st_valid.
          eapply H in H12; eauto.
          etransitivity; eauto using incl_concat.
    Qed.

    Lemma auto_node_wt : forall n,
        wt_node G1 n ->
        incl (snd (auto_node n)) G2.(types) ->
        wt_node G2 (fst (auto_node n)).
    Proof.
      intros * Hwtn Htypes.
      destruct Hwtn as (Hwt1&Hwt2&Hwt3&Hwt4).
      repeat split.
      1-3:unfold wt_clocks in *; simpl_Forall; eauto with ltyping.
      unfold auto_node in *; simpl in *.
      destruct (auto_block _ _) as ((blk'&?)&?) eqn:Haut; simpl in *.
      eapply auto_block_wt; eauto.
      - eapply init_st_valid; eauto using auto_not_in_last_prefs, PS_For_all_empty.
      - apply senv_of_inout_NoLast.
      - apply n_syn.
    Qed.

  End wt_node.

  Theorem auto_global_wt : forall G,
      wt_global G ->
      wt_global (auto_global G).
  Proof.
    intros (enms&nds). revert enms.
    induction nds; intros * Hwt.
    - destruct Hwt. constructor; simpl in *; auto with datatypes.
      now rewrite app_nil_r.
      constructor.
    - destruct Hwt.
      inv H0. destruct H3 as (Hwtn&Hnames). constructor; simpl; eauto with datatypes.
      1:{ inv H. constructor; auto. rewrite in_app_iff; auto. }
      assert (wt_global {| types := enms; nodes := nds |}) as Hwt' by (constructor; auto).
      specialize (IHnds _ Hwt').
      constructor; simpl in *; auto with datatypes. split.
      + eapply auto_node_wt; eauto.
        * eapply global_iface_incl_trans. apply auto_global_iface_incl.
          split; simpl; solve_incl_app.
          intros * Hfind. do 2 esplit; eauto. 2:apply node_iface_eq_refl.
          erewrite find_node_change_types. apply Hfind; eauto.
        * simpl. solve_incl_app.
      + simpl_Forall.
        apply in_map_iff in H0 as (?&?&Hin); subst. apply in_map_iff in Hin as (?&?&Hin); subst.
        simpl_Forall. auto.
      + destruct IHnds as (?&IHnds).
        eapply Forall'_impl; [|eapply IHnds].
        intros * (?&?). split; auto.
        eapply iface_incl_wt_node; eauto. simpl.
        split; simpl; solve_incl_app.
        intros * Hfind. do 2 esplit; eauto. 2:apply node_iface_eq_refl.
        erewrite find_node_change_types, Hfind; eauto.
  Qed.

End CATYPING.

Module CATypingFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks : CLOCKS Ids Op OpAux)
       (Senv : STATICENV Ids Op OpAux Cks)
       (Syn : LSYNTAX Ids Op OpAux Cks Senv)
       (Clo : LTYPING Ids Op OpAux Cks Senv Syn)
       (IL  : COMPAUTO Ids Op OpAux Cks Senv Syn)
       <: CATYPING Ids Op OpAux Cks Senv Syn Clo IL.
  Include CATYPING Ids Op OpAux Cks Senv Syn Clo IL.
End CATypingFun.
