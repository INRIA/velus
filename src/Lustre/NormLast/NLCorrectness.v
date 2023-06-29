From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.
From Coq Require Import Setoid Morphisms.

From Velus Require Import Common.
From Velus Require Import Operators Environment.
From Velus Require Import FunctionalEnvironment.
From Velus Require Import Clocks.
From Velus Require Import CoindStreams IndexedStreams.
From Velus Require Import CoindIndexed.
From Velus Require Import StaticEnv.
From Velus Require Import Lustre.LSyntax Lustre.LOrdered Lustre.LClocking Lustre.LSemantics Lustre.LClockedSemantics.
From Velus Require Import Lustre.NormLast.NormLast Lustre.NormLast.NLClocking.

Module Type NLCORRECTNESS
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks : CLOCKS Ids Op OpAux)
       (Import CStr : COINDSTREAMS Ids Op OpAux Cks)
       (Import Senv : STATICENV Ids Op OpAux Cks)
       (Import Syn : LSYNTAX Ids Op OpAux Cks Senv)
       (Import Cl : LCLOCKING Ids Op OpAux Cks Senv Syn)
       (Import Ord : LORDERED Ids Op OpAux Cks Senv Syn)
       (Import Sem : LSEMANTICS Ids Op OpAux Cks Senv Syn Ord CStr)
       (Import LCS : LCLOCKEDSEMANTICS Ids Op OpAux Cks Senv Syn Cl Ord CStr Sem)
       (Import NL  : NORMLAST Ids Op OpAux Cks Senv Syn).

  Import Fresh Facts Tactics.
  Import List Permutation.


  Section node.
    Context {PSyn : list decl -> block -> Prop}.
    Context {prefs : PS.t}.
    Variable G : @global PSyn prefs.

    (** ** Phase 1 *)
    Section initialize.
      Variable sub : Env.t ident.

      Lemma init_exp_sem : forall H H' bs e vs,
          (forall x vs, sem_var H (Var x) vs -> sem_var H' (Var x) vs) ->
          (forall x y vs, Env.find x sub = Some y -> sem_var H (Last x) vs -> sem_var H' (Var y) vs) ->
          (forall x vs, Env.find x sub = None -> sem_var H (Last x) vs -> sem_var H' (Last x) vs) ->
          sem_exp_ck G H bs e vs ->
          sem_exp_ck G H' bs (init_exp sub e) vs.
      Proof.
        induction e using exp_ind2; intros * Var Sub NSub Sem; inv Sem; simpl;
          try econstructor; eauto;
          simpl_Forall; eauto;
          rewrite ? init_exp_typeof, ? init_exp_typesof; eauto.
        2-4:(rewrite <-Forall2Brs_map_1; eapply Forall2Brs_impl_In; [|eauto];
             intros; simpl_Exists; simpl_Forall; eauto).
        cases_eqn Find; constructor; eauto.
      Qed.

      Lemma init_block_sem : forall blk H H' bs,
          (forall x vs, sem_var H (Var x) vs -> sem_var H' (Var x) vs) ->
          (forall x y vs, Env.find x sub = Some y -> sem_var H (Last x) vs -> sem_var H' (Var y) vs) ->
          (forall x vs, Env.find x sub = None -> sem_var H (Last x) vs -> sem_var H' (Last x) vs) ->
          unnested_block blk ->
          sem_block_ck G H bs blk ->
          sem_block_ck G H' bs (init_block sub blk).
      Proof.
        induction blk using block_ind2; intros * Var Sub NSub Un Sem; inv Un; inv Sem; simpl.
        - (* equation *)
          constructor.
          take (sem_equation_ck _ _ _ _) and inv it.
          eapply Seq with (ss:=ss); simpl_Forall; eauto using init_exp_sem.
        - (* last *)
          cases_eqn Find.
          + constructor.
            eapply Seq with (ss:=[[vs]]); simpl; simpl_Forall; eauto.
            eapply Sfby with (s0ss:=[[vs0]]) (sss:=[[vs1]]); repeat constructor; eauto using init_exp_sem.
          + econstructor; eauto using init_exp_sem.
        - (* reset *)
          econstructor; eauto.
          + take (sem_exp_ck _ _ _ _ _) and inv it. econstructor; eauto.
          + intros. take (forall k, _) and specialize (it k). simpl_Forall.
            take (sem_block_ck _ _ _ _) and eapply H6 in it; eauto.
            all:(intros; take (sem_var _ _ _) and eapply sem_var_mask_inv in it as (?&V&Eq);
                 rewrite Eq; eapply sem_var_mask; eauto).
      Qed.

    End initialize.

    Lemma init_top_block_sem H bs : forall ins outs locs blks outs' blk' st st',
        unnested outs (Blocal (Scope locs blks)) ->
        NoDupMembers outs ->
        NoDupLocals (map fst ins ++ map fst outs) (Blocal (Scope locs blks)) ->
        Forall (AtomOrGensym norm1_prefs) (map fst ins ++ map fst outs) ->
        Forall (fun x => AtomOrGensym norm1_prefs x \/ In x (st_ids st)) (map fst locs) ->
        dom H (ins ++ senv_of_decls outs) ->
        sc_vars (ins ++ senv_of_decls outs) H bs ->
        sem_block_ck G H bs (Blocal (Scope locs blks)) ->
        init_top_block outs (Blocal (Scope locs blks)) st = (outs', blk', st') ->
        exists H',
          (forall x vs, sem_var H (Var x) vs -> sem_var H' (Var x) vs)
          /\ dom H' (ins ++ senv_of_decls outs')
          /\ sc_vars (ins ++ senv_of_decls outs') H' bs
          /\ sem_block_ck G H' bs blk'.
    Proof.
      intros * Un ND1 ND2 At1 At2 (Dom&DomL) (Sc&ScL) Sem Init.
      assert (forall x, IsVar (ins ++ senv_of_decls outs') x <-> IsVar (ins ++ senv_of_decls outs) x) as Vars.
      { inversion Un; subst; repeat inv_bind.
        intros *. rewrite ?IsVar_app. split; intros [|]; auto; right.
        1,2:take (IsVar _ _) and inv it; simpl_In.
        - cases; inv_equalities; econstructor; solve_In.
        - econstructor; solve_In. cases; auto.
      }
      assert (forall x ck, HasClock(ins ++ senv_of_decls outs') x ck <-> HasClock (ins ++ senv_of_decls outs) x ck) as Clocks.
      { inversion Un; subst; repeat inv_bind.
        intros *. rewrite ?HasClock_app. split; intros [|]; auto; right.
        1,2:take (HasClock _ _ _) and inv it; simpl_In.
        - cases; inv_equalities; econstructor; solve_In; auto.
        - destruct (Env.mem x0 (Env.from_list (map fst x))) eqn:Mem.
          1,2:econstructor; solve_In; [rewrite Mem;eauto|]; auto.
      }
      assert (forall x, IsLast (ins ++ senv_of_decls outs') x -> IsLast (ins ++ senv_of_decls outs) x) as Lasts.
      { intros *. rewrite ?IsLast_app. intros [|]; auto; right.
        inversion Un; subst; repeat inv_bind. inv H0. simpl_In.
        cases; inv_equalities; econstructor; solve_In.
        - congruence.
        - destruct o; try congruence. auto.
      }

      exists (restrict H (ins ++ senv_of_decls outs')).
      split; [|split; [|split]].
      - intros * V. eapply sem_var_restrict; eauto.
        apply sem_var_In, Dom in V. apply vars_of_senv_Var, Vars; auto.
      - unfold dom, restrict in *.
        split; intros ?; rewrite FEnv.restrict_In, ? vars_of_senv_Var, ? vars_of_senv_Last, ? Dom, ? DomL.
        1,2:(split; [intros (?&?)|intros; split]); auto; apply Vars; auto.
      - split.
        + intros * Ck V. apply sem_var_restrict_inv in V as (?&V).
          eapply Sc in V; [|apply Clocks]; eauto.
          eapply sem_clock_refines; eauto.
          eapply var_history_refines'; intros.
          eapply sem_var_restrict; eauto.
          eapply vars_of_senv_Var, Vars, Dom, sem_var_In; eauto.
        + intros * Ck L V. apply sem_var_restrict_inv in V as (?&V).
          eapply ScL in V; auto; [|apply Clocks]; eauto.
          eapply sem_clock_refines; eauto.
          eapply var_history_refines'; intros.
          eapply sem_var_restrict; eauto.
          eapply vars_of_senv_Var, Vars, Dom, sem_var_In; eauto.
      - inversion Un; subst; repeat inv_bind. rename x into locs'.
        inv Sem. inv_scope.
        inv ND2. Syn.inv_scope.

        (* Some static lemmas *)
        assert (NoDupMembers (map fst locs')) as ND1'.
        { eapply fresh_idents_NoDupMembers; eauto.
          apply NoDupMembers_filter, NoDupMembers_app.
          1,2:eapply NoDupMembers_map_filter; eauto; intros; destruct_conjs; destruct o; simpl; auto.
          intros * In1 In2; simpl_In.
          take (forall x, _ -> ~_) and eapply it; eauto using In_InMembers.
          apply in_app_iff; right; solve_In.
        }
        assert (NoDup (map snd (map fst locs'))) as ND2'.
        { eapply fresh_idents_NoDup in H0.
          erewrite fst_NoDupMembers, map_map, map_ext, <-map_map in H0; eauto.
          intros; destruct_conjs; auto.
        }
        assert (forall x, InMembers x (ins ++ senv_of_decls outs ++ senv_of_decls locs) ->
                     ~In x (map snd (map fst locs'))) as ND3'.
        { intros * In1 In2. simpl_In.
          rewrite app_assoc, in_app_iff in Hin. destruct Hin; [|simpl_In].
          - eapply Forall_forall in At1. 2:rewrite <-map_fst_senv_of_decls, <-map_app; solve_In.
            eapply fresh_idents_prefixed in H0; simpl_Forall; subst.
            eapply contradict_AtomOrGensym; eauto using last_not_in_norm1_prefs.
          - simpl_Forall. destruct At2.
            + eapply fresh_idents_prefixed in H0; simpl_Forall; subst.
              eapply contradict_AtomOrGensym; eauto using last_not_in_norm1_prefs.
            + eapply fresh_idents_nIn_ids in H0; simpl_Forall. contradiction.
        }
        specialize (Env.from_list_rev _ ND1' ND2') as Equiv.

        (* Building a new history *)
        remember (fun x => match x with
                        | Var x =>
                            match Env.find x (Env.from_list (map (fun x => (snd x, fst x)) (map fst locs'))) with
                            | Some y => (H + Hi') (Last y)
                            | None => Hi' (Var x)
                            end
                        | Last x =>
                            match Env.find x (Env.from_list (map fst locs')) with
                            | Some y => None
                            | None => Hi' (Last x)
                            end
                        end) as Hi2'.
        take (dom Hi' _) and destruct it as (Dom2&DomL2).
        assert (forall x vs, sem_var Hi' (Var x) vs -> sem_var Hi2' (Var x) vs) as V'.
        { intros * Var. inv Var. econstructor; [|eauto].
          cases_eqn Find. exfalso.
          apply Env.from_list_find_In in Find. simpl_In.
          eapply FEnv.find_In, Dom2 in H5. inv H5. simpl_In.
          eapply ND3'. rewrite ? InMembers_app; do 2 right; solve_In. solve_In. }

        assert (dom Hi2'
                  (senv_of_decls
                     (map
                        (fun '(x0, (ty, ck, cx, o)) =>
                           (x0, (ty, ck, cx, if PS.mem x0 (PSUnion (map non_constant_lasts blks)) then None else o))) locs ++
                        map (fun '(_, lx, (ty, ck)) => (lx, (ty, ck, 1%positive, None))) locs'))
               ) as Dom'.
        { subst. unfold dom, FEnv.In.
          rewrite ? senv_of_decls_app. setoid_rewrite IsVar_app. setoid_rewrite IsLast_app.
          repeat split; intros; destruct_conjs.
          - cases_eqn Find; [right|left].
            + apply Env.from_list_find_In in Find. simpl_In.
              econstructor. solve_In.
            + take (_ (Var _) = _) and apply FEnv.find_In, Dom2 in it. inv it. simpl_In.
              econstructor. solve_In.
          - take (_ \/ _) and destruct it as [In|In]; inv In; simpl_In.
            + cases_eqn Find.
              1:{ exfalso. apply Env.from_list_find_In in Find; simpl_In.
                  eapply ND3'. rewrite ? InMembers_app; do 2 right; solve_In. solve_In. }
              eapply Dom2. econstructor. solve_In.
            + erewrite Env.find_In_from_list. 2:solve_In.
              2:now rewrite fst_NoDupMembers, map_map. simpl.
              apply FEnv.union_In.
              eapply fresh_idents_In' in Hin0; eauto. simpl_In.
              apply in_app_iff in Hin as [Hin|Hin]; simpl_In;
                [left; apply DomL; apply IsLast_app; right|right; apply DomL2];
                econstructor; solve_In; simpl; congruence.
          - cases_eqn Find. take (_ (Last _) = _) and apply FEnv.find_In, DomL2 in it; inv it.
            simpl_In. destruct o; try congruence.
            left. econstructor. solve_In. simpl.
            cases_eqn Mem; auto. exfalso.
            eapply Env.Props.P.F.not_find_in_iff; eauto. apply Env.In_from_list.
            eapply fresh_idents_In in H0 as (?&?).
            2:solve_In; apply in_app_iff; right; solve_In; simpl; eauto.
            solve_In.
          - take (_ \/ _) and destruct it as [In|In]; inv In; simpl_In; [|congruence].
            destruct (PS.mem _ _) eqn:Mem; try congruence. destruct o0; try congruence.
            replace (Env.find x0 (Env.from_list (map fst locs'))) with (@None ident).
            2:{ symmetry. erewrite <-Env.Props.P.F.not_find_in_iff, Env.In_from_list, <-fresh_idents_InMembers; eauto.
                intros contra. simpl_In. congruence. }
            apply DomL2. econstructor. solve_In. auto.
        }

        assert (FEnv.refines (@EqSt _) H (H + Hi')) as Ref.
        { eapply local_hist_dom_refines; eauto. 2,3:split; eauto.
          intros * In1 In2. inv In2.
          take (forall x, InMembers _ locs -> ~_) and eapply it; eauto.
          now rewrite fst_InMembers, map_app, map_fst_senv_of_decls in H4. }

        remember (restrict H _) as Hi2.
        assert (forall x vs, sem_var (H + Hi') (Var x) vs -> sem_var (Hi2 + Hi2') (Var x) vs) as RefV.
        { subst.
          intros * Var. apply sem_var_union' in Var as [(Nin&Var)|Var]; eauto using sem_var_union3'.
          apply sem_var_union2.
          2:{ destruct Dom' as (Dom'&_). rewrite Dom', senv_of_decls_app, IsVar_app.
              intros [In|In]; inv In; simpl_In.
              - eapply Nin, Dom2. econstructor. solve_In.
              - apply sem_var_In, Dom in Var. inv Var.
                eapply ND3'. rewrite app_assoc, InMembers_app; eauto. solve_In.
          }
          eapply sem_var_restrict; eauto.
          eapply vars_of_senv_Var, Vars, Dom, sem_var_In; eauto.
        }

        constructor. eapply Sscope with (Hi':=Hi2'); eauto.
        + take (sc_vars _ (_ + _) _) and destruct it as (Sc2&Sc2L). split.
          * intros * Ck V.
            eapply sem_clock_refines; eauto using var_history_refines'.
            rewrite senv_of_decls_app in *.
            apply HasClock_app in Ck as [Ck|Ck]; inv Ck; simpl_In.
            -- eapply Sc2; [econstructor; solve_In; auto|].
               apply sem_var_union' in V as [(Nin&Var)|Var]; eauto using sem_var_union3'.
               ++ exfalso.
                  apply sem_var_restrict_inv in Var as (In&_).
                  apply vars_of_senv_Var in In.
                  take (forall x, InMembers _ locs -> ~_) and eapply it; eauto using In_InMembers.
                  apply IsVar_app in In as [V|V]; apply in_app_iff; [left|right]; inv V; solve_In.
                  cases; inv_equalities; auto.
               ++ apply sem_var_union3'. inv Var. econstructor; eauto.
                  cases_eqn Find; auto. exfalso.
                  apply Equiv, Env.from_list_find_In in Find. simpl_In.
                  eapply ND3'; [|solve_In]; simpl. rewrite ? InMembers_app; do 2 right; solve_In.
            -- apply sem_var_union' in V as [(Nin&Var)|Var].
               ++ exfalso. apply sem_var_restrict_inv in Var as (In&Var).
                  apply vars_of_senv_Var in In. inv In.
                  eapply ND3'. 2:solve_In. simpl.
                  rewrite ? InMembers_app in *.
                  take (_ \/ _) and destruct it; auto. right; left; solve_In. cases; auto.
               ++ inv Var. take (_ ≡ _) and rewrite it.
                  erewrite Env.find_In_from_list in H5. 2:solve_In.
                  2:now rewrite fst_NoDupMembers, map_map. simpl in *.
                  eapply fresh_idents_In' in Hin0; eauto. simpl_In.
                  apply FEnv.union4 in H5 as [Find|Find]; apply in_app_iff in Hin as [In|In]; simpl_In.
                  ** eapply sem_clock_refines, ScL; eauto using var_history_refines.
                     3:econstructor; eauto; reflexivity.
                     1,2:econstructor; [apply in_app_iff; right; solve_In|]; simpl; congruence.
                  ** exfalso. eapply FEnv.find_In, DomL in Find.
                     take (forall x, InMembers _ locs -> ~_) and eapply it; eauto using In_InMembers.
                     apply in_app_iff.
                     apply IsLast_app in Find as [L|L]; inv L; [left|right]; solve_In.
                  ** exfalso. eapply FEnv.find_In, DomL2 in Find. inv Find. simpl_In.
                     take (forall x, InMembers _ locs -> ~_) and eapply it; eauto using In_InMembers.
                     apply in_app_iff; right; solve_In.
                  ** eapply Sc2L, sem_var_union3'. 1,2:econstructor; solve_In; simpl; congruence.
                     econstructor; eauto. reflexivity.
          * intros * Ck L V.
            eapply sem_clock_refines; eauto using var_history_refines'.
            rewrite senv_of_decls_app in *.
            eapply HasClock_IsLast_app in L as [(Ck1&L1)|(Ck1&L1)]; eauto; clear Ck.
            3:{ eapply NoDupMembers_app. 1,2:repeat apply NoDupMembers_map; auto.
                all:intros; destruct_conjs; auto.
                - erewrite fst_NoDupMembers, map_map, map_ext, <-map_map; eauto. intros; destruct_conjs; auto.
                - intros In2. simpl_In.
                  eapply ND3'. rewrite ? InMembers_app; do 2 right; solve_In. solve_In.
            }
            -- inv Ck1. inv L1. simpl_In.
               eapply NoDupMembers_det in Hin1; eauto. inv_equalities. cases; [|destruct o1]; try congruence.
               eapply Sc2L. 1,2:econstructor; solve_In; simpl; auto; congruence.
               apply sem_var_union' in V as [(Nin&Var)|Var]; eauto using sem_var_union3'.
               ++ exfalso.
                  apply sem_var_restrict_inv in Var as (In&_).
                  apply vars_of_senv_Last in In.
                  take (forall x, InMembers _ locs -> ~_) and eapply it; eauto using In_InMembers.
                  apply IsLast_app in In as [V|V]; apply in_app_iff; [left|right]; inv V; solve_In.
                  cases; inv_equalities; auto.
               ++ apply sem_var_union3'. inv Var. econstructor; eauto.
                  cases_eqn Find; auto.
            -- inv L1. simpl_In. congruence.
        + simpl_Forall.
          take (sem_block_ck _ _ _ _) and eapply init_block_sem in it; eauto.
          * intros * Find Var. apply Equiv in Find as Find'.
            eapply sem_var_union3'. subst.
            inv Var. econstructor; eauto.
            setoid_rewrite Find'; eauto.
          * intros * Find Var.
            apply sem_var_union' in Var as [(Nin&Var)|Var].
            -- apply sem_var_union2.
               2:{ destruct Dom' as (_&Dom'). rewrite Dom', senv_of_decls_app, IsLast_app.
                   intros [In|In]; inv In; simpl_In; [|congruence].
                   cases; try congruence. eapply Nin, DomL2. econstructor. solve_In. auto.
               }
               subst. eapply sem_var_restrict; eauto.
               apply sem_var_In, DomL in Var. apply vars_of_senv_Last.
               rewrite IsLast_app in *. destruct Var as [L|L]; auto; right.
               inv L; simpl_In; econstructor; solve_In. rewrite Env.mem_find, Find. eauto. auto.
            -- apply sem_var_union3'. subst.
               inv Var. econstructor; eauto. now rewrite Find.
    Qed.

    (** ** Phase 2 *)
    Section rename.
      Variable sub : Env.t ident.

      Lemma rename_exp_sem : forall H H' bs e vs,
          (forall x vs, sem_var H (Var x) vs -> sem_var H' (Var x) vs) ->
          (forall x y vs, Env.find x sub = Some y -> sem_var H (Last x) vs -> sem_var H' (Last y) vs) ->
          (forall x vs, Env.find x sub = None -> sem_var H (Last x) vs -> sem_var H' (Last x) vs) ->
          sem_exp_ck G H bs e vs ->
          sem_exp_ck G H' bs (rename_exp sub e) vs.
      Proof.
        induction e using exp_ind2; intros * Var Sub NSub Sem; inv Sem; simpl;
          try econstructor; eauto;
          simpl_Forall; eauto;
          rewrite ? rename_exp_typeof, ? rename_exp_typesof; eauto.
        2-4:(rewrite <-Forall2Brs_map_1; eapply Forall2Brs_impl_In; [|eauto];
             intros; simpl_Exists; simpl_Forall; eauto).
        unfold rename_var, or_default.
        cases_eqn Eq; eauto.
      Qed.

      Lemma rename_equation_sem : forall H H' bs e,
          (forall x vs, sem_var H (Var x) vs -> sem_var H' (Var x) vs) ->
          (forall x y vs, Env.find x sub = Some y -> sem_var H (Var x) vs -> sem_var H' (Var y) vs) ->
          (forall x y vs, Env.find x sub = Some y -> sem_var H (Last x) vs -> sem_var H' (Last y) vs) ->
          (forall x vs, Env.find x sub = None -> sem_var H (Last x) vs -> sem_var H' (Last x) vs) ->
          unnested_equation [] e ->
          sem_equation_ck G H bs e ->
          Forall (sem_equation_ck G H' bs) (rename_equation sub e).
      Proof.
        intros * Var SVar Sub NSub Un Sem.
        inv Un; inv Sem; simpl.
        5:take (normalized_cexp _) and inv it; try take (normalized_lexp _) and inv it.
        all:(take (Forall2 (sem_exp_ck _ _ _) [_] _) and inv it; take (Forall2 _ [] _) and inv it; simpl in *; rewrite app_nil_r in *;
             try (take (Forall2 _ [_] _) and inv it; take (Forall2 _ [] _) and inv it)).
        all:repeat constructor.
        all:take (sem_exp_ck _ _ _ _ _) and eapply rename_exp_sem in it as Exp; eauto.
        all:try now (econstructor; eauto; simpl; simpl_Forall; unfold rename_var, or_default; cases_eqn Eq; eauto).
        all:try (cases_eqn Eq; repeat constructor; eapply Seq with (ss:=[[_]]); simpl; simpl_Forall; eauto;
                 econstructor; eauto).
        - (* app *)
          econstructor. repeat constructor; eauto.
          simpl. rewrite app_nil_r. simpl_Forall. eauto.
        - (* auxiliary eqs for app *)
          take (Forall2 _ _ _) and clear - Var SVar it.
          revert lann0. induction it; intros; simpl; auto.
          cases_eqn Eq; auto.
          constructor; auto.
          eapply Seq with (ss:=[[_]]); simpl; repeat constructor; eauto.
      Qed.

      Lemma rename_block_sem : forall blk H H' bs,
          (forall x vs, sem_var H (Var x) vs -> sem_var H' (Var x) vs) ->
          (forall x y vs, Env.find x sub = Some y -> sem_var H (Var x) vs -> sem_var H' (Var y) vs) ->
          (forall x y vs, Env.find x sub = Some y -> sem_var H (Last x) vs -> sem_var H' (Last y) vs) ->
          (forall x vs, Env.find x sub = None -> sem_var H (Last x) vs -> sem_var H' (Last x) vs) ->
          unnested_block blk ->
          sem_block_ck G H bs blk ->
          Forall (sem_block_ck G H' bs) (rename_block sub blk).
      Proof.
        induction blk using block_ind2;
          intros * Var SVar Sub NSub Un Sem; inv Un; inv Sem; simpl.
        - (* equation *)
          take (sem_equation_ck _ _ _ _) and eapply rename_equation_sem in it; eauto.
          simpl_Forall. now constructor.
        - (* last *)
          repeat constructor.
          econstructor; eauto using rename_exp_sem.
          1,2:unfold rename_var, or_default; cases_eqn Eq; eauto.
        - (* reset *)
          simpl_Forall.
          take (sem_exp_ck _ _ _ _ _) and eapply rename_exp_sem in it; eauto.
          econstructor; eauto.
          intros ?. take (forall (k : nat), _) and specialize (it k). simpl_Forall.
          take (sem_block_ck _ _ _ _) and eapply H4 in it; simpl_Forall; eauto.
          all:(intros; take (sem_var _ _ _) and eapply sem_var_mask_inv in it as (?&V&Eq);
               rewrite Eq; eapply sem_var_mask; eauto).
      Qed.
    End rename.

    Lemma output_top_block_sem H bs : forall ins outs locs blks blk' st st',
        unnested outs (Blocal (Scope locs blks)) ->
        NoDupMembers outs ->
        NoDupLocals (map fst ins ++ map fst outs) (Blocal (Scope locs blks)) ->
        Forall (AtomOrGensym norm1_prefs) (map fst ins ++ map fst outs) ->
        Forall (fun x => AtomOrGensym norm1_prefs x \/ In x (st_ids st)) (map fst locs) ->
        dom H (senv_of_ins ins ++ senv_of_decls outs) ->
        sc_vars (senv_of_ins ins ++ senv_of_decls outs) H bs ->
        sem_block_ck G H bs (Blocal (Scope locs blks)) ->
        output_top_block outs (Blocal (Scope locs blks)) st = (blk', st') ->
        exists H',
          (forall x vs, sem_var H (Var x) vs -> sem_var H' (Var x) vs)
          /\ dom H' (senv_of_ins ins ++ senv_of_decls (remove_lasts outs))
          /\ sc_vars (senv_of_ins ins ++ senv_of_decls (remove_lasts outs)) H' bs
          /\ sem_block_ck G H' bs blk'.
    Proof.
      intros * Un ND1 ND2 At1 At2 (Dom&DomL) (Sc&ScL) Sem Init.
      assert (forall x, IsVar (senv_of_ins ins ++ senv_of_decls (remove_lasts outs)) x
                   <-> IsVar (senv_of_ins ins ++ senv_of_decls outs) x) as Vars.
      { inversion Un; subst; repeat inv_bind. unfold remove_lasts.
        intros *. rewrite ?IsVar_app. split; intros [|]; auto; right.
        1,2:take (IsVar _ _) and inv it; simpl_In.
        - cases; inv_equalities; econstructor; solve_In.
        - econstructor; solve_In.
      }
      assert (forall x ck, HasClock(senv_of_ins ins ++ senv_of_decls (remove_lasts outs)) x ck
                      <-> HasClock (senv_of_ins ins ++ senv_of_decls outs) x ck) as Clocks.
      { inversion Un; subst; repeat inv_bind. unfold remove_lasts.
        intros *. rewrite ?HasClock_app. split; intros [|]; auto; right.
        1,2:take (HasClock _ _ _) and inv it; simpl_In.
        - cases; inv_equalities; econstructor; solve_In; auto.
        - destruct (Env.mem x0 (Env.from_list (map fst x))) eqn:Mem.
          1,2:econstructor; solve_In; auto.
      }
      assert (forall x, IsLast (senv_of_ins ins ++ senv_of_decls (remove_lasts outs)) x ->
                   IsLast (senv_of_ins ins ++ senv_of_decls outs) x) as Lasts.
      { intros *. unfold remove_lasts. rewrite ?IsLast_app. intros [|]; auto; right.
        inversion Un; subst; repeat inv_bind. inv H0. simpl_In.
        congruence.
      }

      exists (restrict H (senv_of_ins ins ++ senv_of_decls (remove_lasts outs))).
      split; [|split; [|split]].
      - intros * V. eapply sem_var_restrict; eauto.
        apply sem_var_In, Dom in V. apply vars_of_senv_Var, Vars; auto.
      - unfold dom, restrict in *.
        split; intros ?; rewrite FEnv.restrict_In, ? vars_of_senv_Var, ? vars_of_senv_Last, ? Dom, ? DomL.
        1,2:(split; [intros (?&?)|intros; split]); auto; apply Vars; auto.
      - split.
        + intros * Ck V. apply sem_var_restrict_inv in V as (?&V).
          eapply Sc in V; [|apply Clocks]; eauto.
          eapply sem_clock_refines; eauto.
          eapply var_history_refines'; intros.
          eapply sem_var_restrict; eauto.
          eapply vars_of_senv_Var, Vars, Dom, sem_var_In; eauto.
        + intros * Ck L V. apply sem_var_restrict_inv in V as (?&V).
          eapply ScL in V; auto; [|apply Clocks]; eauto.
          eapply sem_clock_refines; eauto.
          eapply var_history_refines'; intros.
          eapply sem_var_restrict; eauto.
          eapply vars_of_senv_Var, Vars, Dom, sem_var_In; eauto.
      - inversion Un; subst; repeat inv_bind. rename x into locs'.
        inv Sem. inv_scope.
        inv ND2. Syn.inv_scope.

        (* Some static lemmas *)
        assert (NoDupMembers (map fst locs')) as ND1'.
        { eapply fresh_idents_NoDupMembers; eauto.
          eapply NoDupMembers_map_filter; eauto; intros; destruct_conjs; destruct o; simpl; auto.
        }
        assert (NoDup (map snd (map fst locs'))) as ND2'.
        { eapply fresh_idents_NoDup in H0.
          erewrite fst_NoDupMembers, map_map, map_ext, <-map_map in H0; eauto.
          intros; destruct_conjs; auto.
        }
        assert (forall x, InMembers x (senv_of_ins ins ++ senv_of_decls outs ++ senv_of_decls locs) ->
                     ~In x (map snd (map fst locs'))) as ND3'.
        { intros * In1 In2. simpl_In.
          rewrite app_assoc, in_app_iff in Hin. destruct Hin; [|simpl_In].
          - eapply Forall_forall in At1. 2:rewrite <-map_fst_senv_of_ins, <-map_fst_senv_of_decls, <-map_app; solve_In.
            eapply fresh_idents_prefixed in H0; simpl_Forall; subst.
            eapply contradict_AtomOrGensym; eauto using last_not_in_norm1_prefs.
          - simpl_Forall. destruct At2.
            + eapply fresh_idents_prefixed in H0; simpl_Forall; subst.
              eapply contradict_AtomOrGensym; eauto using last_not_in_norm1_prefs.
            + eapply fresh_idents_nIn_ids in H0; simpl_Forall. contradiction.
        }
        specialize (Env.from_list_rev _ ND1' ND2') as Equiv.

        (* Building a new history *)
        remember (fun x => match x with
                        | Var x =>
                            match Env.find x (Env.from_list (map (fun x => (snd x, fst x)) (map fst locs'))) with
                            | Some y => H (Var y)
                            | None => Hi' (Var x)
                            end
                        | Last x =>
                            match Env.find x (Env.from_list (map (fun x => (snd x, fst x)) (map fst locs'))) with
                            | Some y => H (Last y)
                            | None => Hi' (Last x)
                            end
                        end) as Hi2'.
        take (dom Hi' _) and destruct it as (Dom2&DomL2).
        assert (forall x vs, sem_var Hi' (Var x) vs -> sem_var Hi2' (Var x) vs) as V'.
        { intros * Var. inv Var. econstructor; eauto.
          cases_eqn Find. exfalso.
          apply Env.from_list_find_In in Find. simpl_In.
          eapply FEnv.find_In, Dom2 in H5. inv H5. simpl_In.
          eapply ND3'. rewrite ? InMembers_app; do 2 right; solve_In. solve_In. }

        assert (dom Hi2'
                  (senv_of_decls (locs ++ map (fun '(_, lx, (ty, ck)) => (lx, (ty, ck, 1%positive, Some 1%positive))) locs'))
               ) as Dom'.
        { subst. unfold dom, FEnv.In.
          rewrite ? senv_of_decls_app. setoid_rewrite IsVar_app. setoid_rewrite IsLast_app.
          repeat split; intros; destruct_conjs.
          - cases_eqn Find; [right|left].
            + apply Env.from_list_find_In in Find. simpl_In.
              econstructor. solve_In.
            + take (_ (Var _) = _) and apply FEnv.find_In, Dom2 in it. auto.
          - take (_ \/ _) and destruct it as [In|In]; inv In; simpl_In.
            + cases_eqn Find.
              1:{ exfalso. apply Env.from_list_find_In in Find; simpl_In.
                  eapply ND3'. rewrite ? InMembers_app; do 2 right; solve_In. solve_In. }
              eapply Dom2. econstructor. solve_In.
            + erewrite Env.find_In_from_list. 2:solve_In.
              2:now rewrite fst_NoDupMembers, map_map. simpl.
              eapply fresh_idents_In' in Hin0; eauto. simpl_In.
              eapply Dom, IsVar_app. right. econstructor. solve_In.
          - cases_eqn Find.
            + eapply Env.from_list_find_In in Find. simpl_In.
              right. econstructor. solve_In. simpl. congruence.
            + left. eapply DomL2. econstructor; eauto.
          - take (_ \/ _) and destruct it as [In|In]; inv In; simpl_In.
            + destruct o; try congruence.
              cases_eqn Find.
              * exfalso. apply Equiv, Env.from_list_find_In in Find; simpl_In.
                eapply ND3'; [|solve_In].
                rewrite ? InMembers_app. do 2 right. solve_In.
              * eapply DomL2. econstructor. solve_In. simpl. congruence.
            + edestruct Equiv as (Equiv1&_). rewrite Equiv1.
              2:eapply Env.find_In_from_list; eauto; solve_In.
              apply DomL, IsLast_app, or_intror.
              eapply fresh_idents_In' in H0; eauto. simpl_In.
              econstructor. solve_In. simpl; congruence.
        }

        assert (FEnv.refines (@EqSt _) H (H + Hi')) as Ref.
        { eapply local_hist_dom_refines; eauto. 2,3:split; eauto.
          intros * In1 In2. inv In2.
          take (forall x, InMembers _ locs -> ~_) and eapply it; eauto.
          now rewrite fst_InMembers, map_app, map_fst_senv_of_ins, map_fst_senv_of_decls in H4. }

        remember (restrict H _) as Hi2.
        assert (forall x vs, sem_var (H + Hi') (Var x) vs -> sem_var (Hi2 + Hi2') (Var x) vs) as RefV.
        { subst.
          intros * Var. apply sem_var_union' in Var as [(Nin&Var)|Var]; eauto using sem_var_union3'.
          apply sem_var_union2.
          2:{ destruct Dom' as (Dom'&_). rewrite Dom', senv_of_decls_app, IsVar_app.
              intros [In|In]; inv In; simpl_In.
              - eapply Nin, Dom2. econstructor. solve_In.
              - apply sem_var_In, Dom in Var. inv Var.
                eapply ND3'. rewrite app_assoc, InMembers_app; eauto. solve_In.
          }
          eapply sem_var_restrict; eauto.
          eapply vars_of_senv_Var, Vars, Dom, sem_var_In; eauto.
        }

        constructor. eapply Sscope with (Hi':=Hi2'); eauto.
        + take (sc_vars _ (_ + _) _) and destruct it as (Sc2&Sc2L). split.
          * intros * Ck V.
            eapply sem_clock_refines; eauto using var_history_refines'.
            rewrite senv_of_decls_app in *.
            apply HasClock_app in Ck as [Ck|Ck]; inv Ck; simpl_In.
            -- eapply Sc2; [econstructor; solve_In; auto|].
               apply sem_var_union' in V as [(Nin&Var)|Var]; eauto using sem_var_union3'.
               ++ exfalso.
                  apply sem_var_restrict_inv in Var as (In&_).
                  apply vars_of_senv_Var in In.
                  take (forall x, InMembers _ locs -> ~_) and eapply it; eauto using In_InMembers.
                  apply IsVar_app in In as [V|V]; apply in_app_iff; [left|right]; inv V; solve_In.
               ++ apply sem_var_union3'. inv Var. econstructor; eauto.
                  cases_eqn Find; auto. exfalso.
                  apply Equiv, Env.from_list_find_In in Find. simpl_In.
                  eapply ND3'; [|solve_In]; simpl. rewrite ? InMembers_app; do 2 right; solve_In.
            -- apply sem_var_union' in V as [(Nin&Var)|Var].
               ++ exfalso. apply sem_var_restrict_inv in Var as (In&Var).
                  apply vars_of_senv_Var in In. inv In.
                  eapply ND3'. 2:solve_In. simpl.
                  rewrite ? InMembers_app in *.
                  take (_ \/ _) and destruct it; auto. right; left; solve_In.
               ++ inv Var. take (_ ≡ _) and rewrite it.
                  erewrite Env.find_In_from_list in H5. 2:solve_In.
                  2:now rewrite fst_NoDupMembers, map_map. simpl in *.
                  eapply fresh_idents_In' in Hin0; eauto. simpl_In.
                  eapply sem_clock_refines, Sc; eauto using var_history_refines.
                  2:econstructor; eauto; reflexivity.
                  econstructor; [apply in_app_iff; right; solve_In|]; simpl; congruence.
          * intros * Ck L V.
            eapply sem_clock_refines; eauto using var_history_refines'.
            rewrite senv_of_decls_app in *.
            eapply HasClock_IsLast_app in L as [(Ck1&L1)|(Ck1&L1)]; eauto; clear Ck.
            3:{ eapply NoDupMembers_app. 1,2:repeat apply NoDupMembers_map; auto.
                all:intros; destruct_conjs; auto.
                - erewrite fst_NoDupMembers, map_map, map_ext, <-map_map; eauto. intros; destruct_conjs; auto.
                - intros In2. simpl_In.
                  eapply ND3'. rewrite ? InMembers_app; do 2 right; solve_In. solve_In.
            }
            -- inv Ck1. inv L1. simpl_In.
               eapply NoDupMembers_det in Hin0; eauto. inv_equalities. destruct o0; try congruence.
               eapply Sc2L. 1,2:econstructor; solve_In; simpl; auto; congruence.
               apply sem_var_union' in V as [(Nin&Var)|Var]; eauto using sem_var_union3'.
               ++ exfalso.
                  apply sem_var_restrict_inv in Var as (In&_).
                  apply vars_of_senv_Last in In.
                  take (forall x, InMembers _ locs -> ~_) and eapply it; eauto using In_InMembers.
                  apply IsLast_app in In as [V|V]; apply in_app_iff; [left|right]; inv V; solve_In.
               ++ apply sem_var_union3'. inv Var. econstructor; eauto.
                  cases_eqn Find; auto. exfalso.
                  apply Equiv, Env.from_list_find_In in Find. simpl_In.
                  eapply ND3'; [|solve_In]; simpl. rewrite ? InMembers_app; do 2 right; solve_In.
            -- inv Ck1. inv L1. simpl_In.
               eapply NoDup_snd_det in ND2' as EQ. 2:solve_In. 2:clear Hin0; solve_In. subst.
               eapply NoDupMembers_det in Hin1; eauto. inv_equalities.
               2:now apply NoDupMembers_NoDup, fst_NoDupMembers in ND1'.
               apply sem_var_union' in V as [(Nin&Var)|Var].
               ++ exfalso.
                  apply sem_var_restrict_inv in Var as (In&_).
                  apply vars_of_senv_Last in In.
                  eapply ND3'; [|solve_In]. simpl.
                  rewrite ? InMembers_app.
                  apply IsLast_app in In as [V|V]; [left|right;left]; inv V; solve_In.
               ++ inv Var. erewrite Env.find_In_from_list in H5. 2:solve_In.
                  2:now rewrite fst_NoDupMembers, map_map.
                  eapply fresh_idents_In' in Hin0; eauto. simpl_In.
                  eapply sem_clock_refines, ScL; eauto using var_history_refines.
                  3:econstructor; eauto; reflexivity.
                  1,2:econstructor; [apply in_app_iff; right; solve_In|]; simpl; congruence.
        + apply Forall_flat_map. simpl_Forall.
          take (sem_block_ck _ _ _ _) and eapply rename_block_sem, Forall_forall in it; eauto.
          * intros * Find Var. apply Equiv in Find as Find'.
            apply sem_var_union' in Var as [(Nin&Var)|Var].
            -- eapply sem_var_union3'. inv Var. econstructor; eauto.
               setoid_rewrite Find'; auto.
            -- exfalso. eapply Env.from_list_find_In in Find. simpl_In.
               apply sem_var_In, Dom2 in Var. inv Var. simpl_In.
               eapply fresh_idents_In' in Hin; eauto. simpl_In.
               take (forall x, InMembers _ locs -> ~_) and eapply it; eauto using In_InMembers.
               apply in_app_iff, or_intror. solve_In.
          * intros * Find Var. apply Equiv in Find as Find'.
            apply sem_var_union' in Var as [(Nin&Var)|Var].
            -- eapply sem_var_union3'. inv Var. econstructor; eauto.
               setoid_rewrite Find'; auto.
            -- exfalso. eapply Env.from_list_find_In in Find. simpl_In.
               apply sem_var_In, DomL2 in Var. inv Var. simpl_In.
               eapply fresh_idents_In' in Hin; eauto. simpl_In.
               take (forall x, InMembers _ locs -> ~_) and eapply it; eauto using In_InMembers.
               apply in_app_iff, or_intror. solve_In.
          * intros * Find Var.
            apply sem_var_union' in Var as [(Nin&Var)|Var].
            -- apply sem_var_union2.
               2:{ destruct Dom' as (_&Dom'). rewrite Dom', senv_of_decls_app, IsLast_app.
                   apply sem_var_In, DomL in Var. inv Var.
                   intros [In|In]; inv In; simpl_In.
                   - take (forall x, InMembers _ locs -> ~_) and eapply it; eauto using In_InMembers.
                     rewrite <-map_fst_senv_of_ins, <-map_fst_senv_of_decls, <-map_app; solve_In.
                   - eapply ND3'; [|solve_In]. simpl.
                     rewrite app_assoc, InMembers_app; eauto using In_InMembers.
               }
               subst. eapply sem_var_restrict; eauto.
               apply sem_var_In, DomL in Var. apply vars_of_senv_Last.
               rewrite IsLast_app in *. destruct Var as [L|L]; auto. exfalso.
               inv L. simpl_In. destruct o; try congruence.
               eapply Env.Props.P.F.not_find_in_iff; eauto. apply Env.In_from_list.
               erewrite <-fresh_idents_InMembers; eauto. solve_In. auto.
            -- apply sem_var_union3'. subst.
               inv Var. econstructor; eauto. cases_eqn Find; auto.
               exfalso. eapply Env.from_list_find_In in Find0. simpl_In.
               take (_ (Last _) = _) and apply FEnv.find_In, DomL2 in it. inv it. simpl_In.
               eapply ND3'; [|solve_In]. rewrite ? InMembers_app. do 2 right. solve_In.
    Qed.

    (** ** Phase 3 *)
    Section unnest.
      Variable sub : Env.t ident.

      Lemma unnest_block_sem : forall blk H H' bs,
          (forall x vs, sem_var H (Var x) vs -> sem_var H' (Var x) vs) ->
          (forall x y vs, Env.find x sub = Some y -> sem_var H (Var x) vs -> sem_var H' (Var y) vs) ->
          (forall x y vs, Env.find x sub = Some y -> sem_var H (Last x) vs -> sem_var H' (Last y) vs) ->
          (forall x vs, Env.find x sub = None -> sem_var H (Last x) vs -> sem_var H' (Last x) vs) ->
          unnested_block blk ->
          sem_block_ck G H bs blk ->
          sem_block_ck G H' bs (unnest_block sub blk).
      Proof.
        induction blk using block_ind2;
          intros * Var SVar Sub NSub Un Sem; inv Un; inv Sem; simpl.
        - (* equation *)
          destruct eq. constructor.
          take (sem_equation_ck _ _ _ _) and inv it.
          eapply Seq with (ss:=ss); simpl_Forall; eauto using rename_exp_sem.
        - (* last *)
          econstructor; eauto using rename_exp_sem.
          1,2:unfold rename_var, or_default; cases_eqn Eq; eauto.
        - (* reset *)
          take (sem_exp_ck _ _ _ _ _) and eapply rename_exp_sem in it; eauto.
          econstructor; eauto.
          intros ?. take (forall (k : nat), _) and specialize (it k). simpl_Forall.
          take (sem_block_ck _ _ _ _) and eapply H5 in it; simpl_Forall; eauto.
          all:(intros; take (sem_var _ _ _) and eapply sem_var_mask_inv in it as (?&V&Eq);
               rewrite Eq; eapply sem_var_mask; eauto).
      Qed.
    End unnest.

    Lemma unnest_top_block_sem H bs : forall ins outs locs blks blk' st st',
        unnested outs (Blocal (Scope locs blks)) ->
        NoDupMembers outs ->
        NoDupLocals (map fst ins ++ map fst outs) (Blocal (Scope locs blks)) ->
        Forall (AtomOrGensym norm1_prefs) (map fst ins ++ map fst outs) ->
        Forall (fun x => AtomOrGensym norm1_prefs x \/ In x (st_ids st)) (map fst locs) ->
        dom H (senv_of_ins ins ++ senv_of_decls outs) ->
        sc_vars (senv_of_ins ins ++ senv_of_decls outs) H bs ->
        sem_block_ck G H bs (Blocal (Scope locs blks)) ->
        unnest_top_block (Blocal (Scope locs blks)) st = (blk', st') ->
        sem_block_ck G H bs blk'.
    Proof.
      intros * Un ND1 ND2 At1 At2 (Dom&DomL) (Sc&ScL) Sem Init.

      - inversion Un; subst; repeat inv_bind. rename x into locs'.
        inv Sem. inv_scope.
        inv ND2. Syn.inv_scope.

        (* Some static lemmas *)
        assert (NoDupMembers (map fst locs')) as ND1'.
        { eapply fresh_idents_NoDupMembers; eauto.
          eapply NoDupMembers_filter, NoDupMembers_map_filter; eauto.
          intros; destruct_conjs; destruct o; simpl; auto.
        }
        assert (NoDup (map snd (map fst locs'))) as ND2'.
        { eapply fresh_idents_NoDup in H0.
          erewrite fst_NoDupMembers, map_map, map_ext, <-map_map in H0; eauto.
          intros; destruct_conjs; auto.
        }
        assert (forall x, InMembers x (senv_of_ins ins ++ senv_of_decls outs ++ senv_of_decls locs) ->
                     ~In x (map snd (map fst locs'))) as ND3'.
        { intros * In1 In2. simpl_In.
          rewrite app_assoc, in_app_iff in Hin. destruct Hin; [|simpl_In].
          - eapply Forall_forall in At1. 2:rewrite <-map_fst_senv_of_ins, <-map_fst_senv_of_decls, <-map_app; solve_In.
            eapply fresh_idents_prefixed in H0; simpl_Forall; subst.
            eapply contradict_AtomOrGensym; eauto using last_not_in_norm1_prefs.
          - simpl_Forall. destruct At2.
            + eapply fresh_idents_prefixed in H0; simpl_Forall; subst.
              eapply contradict_AtomOrGensym; eauto using last_not_in_norm1_prefs.
            + eapply fresh_idents_nIn_ids in H0; simpl_Forall. contradiction.
        }
        specialize (Env.from_list_rev _ ND1' ND2') as Equiv.

        (* Building a new history *)
        remember (fun x => match x with
                        | Var x =>
                            match Env.find x (Env.from_list (map (fun x => (snd x, fst x)) (map fst locs'))) with
                            | Some y => Hi' (Var y)
                            | None => Hi' (Var x)
                            end
                        | Last x =>
                            match Env.find x (Env.from_list (map (fun x => (snd x, fst x)) (map fst locs'))) with
                            | Some y => Hi' (Last y)
                            | None => match Env.find x (Env.from_list (map fst locs')) with
                                     | Some y => None
                                     | None => Hi' (Last x)
                                     end
                            end
                        end) as Hi2'.
        take (dom Hi' _) and destruct it as (Dom2&DomL2).
        assert (forall x vs, sem_var Hi' (Var x) vs -> sem_var Hi2' (Var x) vs) as V'.
        { intros * Var. inv Var. econstructor; eauto.
          cases_eqn Find. exfalso.
          apply Env.from_list_find_In in Find. simpl_In.
          eapply FEnv.find_In, Dom2 in H5. inv H5. simpl_In.
          eapply ND3'. rewrite ? InMembers_app; do 2 right; solve_In. solve_In. }

        assert (dom Hi2'
                  (senv_of_decls
                     (map (fun '(x0, (ty, ck, cx, o)) =>
                             (x0, (ty, ck, cx, if PS.mem x0 (PSUnion (map non_cexp_defs blks)) then None else o))) locs ++
                        map (fun '(_, lx, (ty, ck)) => (lx, (ty, ck, 1%positive, Some 1%positive))) locs'))
               ) as Dom'.
        { subst. unfold dom, FEnv.In.
          rewrite ? senv_of_decls_app. setoid_rewrite IsVar_app. setoid_rewrite IsLast_app.
          repeat split; intros; destruct_conjs.
          - cases_eqn Find; [right|left].
            + apply Env.from_list_find_In in Find. simpl_In.
              econstructor.  solve_In.
            + take (_ (Var _) = _) and apply FEnv.find_In, Dom2 in it.
              inv it. econstructor. solve_In.
          - take (_ \/ _) and destruct it as [In|In]; inv In; simpl_In.
            + cases_eqn Find.
              1:{ exfalso. apply Env.from_list_find_In in Find; simpl_In.
                  eapply ND3'. rewrite ? InMembers_app; do 2 right; solve_In. solve_In. }
              eapply Dom2. econstructor. solve_In.
            + erewrite Env.find_In_from_list. 2:solve_In.
              2:now rewrite fst_NoDupMembers, map_map. simpl.
              eapply fresh_idents_In' in Hin0; eauto. simpl_In.
              eapply Dom2. econstructor. solve_In.
          - cases_eqn Find.
            + right. apply Env.from_list_find_In in Find; simpl_In.
              econstructor. solve_In. simpl; congruence.
            + left. take (_ (Last _) = _) and eapply FEnv.find_In, DomL2 in it.
              inv it. econstructor; eauto. simpl_In. destruct o; try congruence.
              solve_In. cases_eqn Mem; auto. exfalso.
              eapply Env.Props.P.F.not_find_in_iff; eauto.
              erewrite Env.In_from_list, <-fresh_idents_InMembers; eauto.
              solve_In. auto.
          - take (_ \/ _) and destruct it as [In|In]; inv In; simpl_In.
            + destruct (PS.mem _ _) eqn:Mem, o0; try congruence.
              cases_eqn Eq.
              * eapply Env.from_list_find_In in Eq. simpl_In.
                eapply fresh_idents_In' in Hin1; eauto. simpl_In.
                apply DomL2. econstructor. solve_In. simpl. congruence.
              * exfalso. apply Env.from_list_find_In in Eq0 as Eq1. simpl_In.
                eapply fresh_idents_In' in Hin; eauto. simpl_In. congruence.
              * apply DomL2. econstructor. solve_In. auto.
            + edestruct Equiv as (Equiv1&_). rewrite Equiv1.
              2:eapply Env.find_In_from_list; eauto; solve_In.
              apply DomL2.
              eapply fresh_idents_In' in H0; eauto. simpl_In.
              econstructor. solve_In. simpl; congruence.
        }

        assert (FEnv.refines (@EqSt _) H (H + Hi')) as Ref.
        { eapply local_hist_dom_refines; eauto. 2,3:split; eauto.
          intros * In1 In2. inv In2.
          take (forall x, InMembers _ locs -> ~_) and eapply it; eauto.
          now rewrite fst_InMembers, map_app, map_fst_senv_of_ins, map_fst_senv_of_decls in H4. }
        assert (forall x vs, sem_var (H + Hi') (Var x) vs -> sem_var (H + Hi2') (Var x) vs) as RefV.
        { subst.
          intros * Var. apply sem_var_union' in Var as [(Nin&Var)|Var]; eauto using sem_var_union3'.
          apply sem_var_union2; eauto.
          destruct Dom' as (Dom'&_). rewrite Dom', senv_of_decls_app, IsVar_app.
          intros [In|In]; inv In; simpl_In.
          - eapply Nin, Dom2. econstructor. solve_In.
          - apply sem_var_In, Dom in Var. inv Var.
            eapply ND3'. rewrite app_assoc, InMembers_app; eauto. solve_In.
        }
        assert (forall x1 y vs,
                   Env.find x1 (Env.from_list (map fst locs')) = Some y ->
                   sem_var (H + Hi') (Var x1) vs -> sem_var (H + Hi2') (Var y) vs
               ) as FindV.
        { intros * Find Var. apply Equiv in Find as Find'.
          apply sem_var_union' in Var as [(Nin&Var)|Var].
          - exfalso. eapply Env.from_list_find_In in Find. simpl_In.
            apply sem_var_In, Dom in Var. inv Var. simpl_In.
            eapply fresh_idents_In' in Hin; eauto. simpl_In.
            take (forall x, InMembers _ locs -> ~_) and eapply it; eauto using In_InMembers.
            rewrite <-map_fst_senv_of_ins, <-map_fst_senv_of_decls, <-map_app; solve_In.
          - eapply sem_var_union3'. inv Var. econstructor; eauto.
            setoid_rewrite Find'; auto.
        }

        constructor. eapply Sscope with (Hi':=Hi2'); eauto. 2:apply Forall_app; split.
        + take (sc_vars _ (_ + _) _) and destruct it as (Sc2&Sc2L). split.
          * intros * Ck V.
            eapply sem_clock_refines; eauto using var_history_refines'.
            rewrite senv_of_decls_app in *.
            apply HasClock_app in Ck as [Ck|Ck]; inv Ck; simpl_In.
            -- eapply Sc2; [econstructor; solve_In; auto|].
               apply sem_var_union' in V as [(Nin&Var)|Var]; eauto using sem_var_union3'.
               ++ exfalso.
                  apply sem_var_In, Dom in Var as In. inv In.
                  take (forall x, InMembers _ locs -> ~_) and eapply it; eauto using In_InMembers.
                  now take (InMembers _ _) and rewrite fst_InMembers, map_app, map_fst_senv_of_ins, map_fst_senv_of_decls in it.
               ++ apply sem_var_union3'. inv Var. econstructor; eauto.
                  cases_eqn Find; auto. exfalso.
                  apply Equiv, Env.from_list_find_In in Find. simpl_In.
                  eapply ND3'; [|solve_In]; simpl. rewrite ? InMembers_app; do 2 right; solve_In.
            -- apply sem_var_union' in V as [(Nin&Var)|Var].
               ++ exfalso. apply sem_var_In, Dom in Var as In. inv In.
                  eapply ND3'. 2:solve_In. simpl.
                  rewrite ? InMembers_app in *.
                  take (_ \/ _) and destruct it; auto.
               ++ inv Var. take (_ ≡ _) and rewrite it.
                  erewrite Env.find_In_from_list in H5. 2:solve_In.
                  2:now rewrite fst_NoDupMembers, map_map. simpl in *.
                  eapply fresh_idents_In' in Hin0; eauto. simpl_In.
                  eapply Sc2, sem_var_union3'.
                  2:econstructor; eauto; reflexivity.
                  econstructor. solve_In. auto.
          * intros * Ck L V.
            eapply sem_clock_refines; eauto using var_history_refines'.
            rewrite senv_of_decls_app in *.
            eapply HasClock_IsLast_app in L as [(Ck1&L1)|(Ck1&L1)]; eauto; clear Ck.
            3:{ eapply NoDupMembers_app. 1,2:repeat apply NoDupMembers_map; auto.
                all:intros; destruct_conjs; auto.
                - erewrite fst_NoDupMembers, map_map, map_ext, <-map_map; eauto. intros; destruct_conjs; auto.
                - intros In2. simpl_In.
                  eapply ND3'. rewrite ? InMembers_app; do 2 right; solve_In. solve_In.
            }
            -- inv Ck1. inv L1. simpl_In.
               eapply NoDupMembers_det in Hin1; eauto. inv_equalities.
               destruct (PS.mem _ _) eqn:Mem, o1; try congruence.
               eapply Sc2L. 1,2:econstructor; solve_In; simpl; auto; congruence.
               apply sem_var_union' in V as [(Nin&Var)|Var].
               ++ exfalso.
                  apply sem_var_In, DomL in Var as In. inv In.
                  take (forall x, InMembers _ locs -> ~_) and eapply it; eauto using In_InMembers.
                  rewrite <-map_fst_senv_of_ins, <-map_fst_senv_of_decls, <-map_app; solve_In.
               ++ apply sem_var_union3'. inv Var. econstructor; eauto.
                  cases_eqn Find; auto. exfalso.
                  apply Equiv, Env.from_list_find_In in Find. simpl_In.
                  eapply ND3'; [|solve_In]; simpl. rewrite ? InMembers_app; do 2 right; solve_In.
            -- inv Ck1. inv L1. simpl_In.
               eapply NoDup_snd_det in ND2' as EQ. 2:solve_In. 2:clear Hin0; solve_In. subst.
               eapply NoDupMembers_det in Hin1; eauto. inv_equalities.
               2:now apply NoDupMembers_NoDup, fst_NoDupMembers in ND1'.
               apply sem_var_union' in V as [(Nin&Var)|Var].
               ++ exfalso.
                  apply sem_var_In, DomL in Var as In.
                  eapply ND3'; [|solve_In]. simpl.
                  rewrite ? InMembers_app.
                  apply IsLast_app in In as [V|V]; [left|right;left]; inv V; solve_In.
               ++ inv Var. erewrite Env.find_In_from_list in H5. 2:solve_In.
                  2:now rewrite fst_NoDupMembers, map_map.
                  eapply fresh_idents_In' in Hin0; eauto. simpl_In.
                  eapply Sc2L, sem_var_union3'.
                  3:econstructor; eauto; reflexivity.
                  1,2:econstructor; solve_In; simpl; congruence.
        + simpl_Forall. constructor.
          assert (FEnv.In (Var i) Hi') as (vs&Find).
          { eapply fresh_idents_In' in H4; eauto. simpl_In.
            apply Dom2. econstructor. solve_In. }
          eapply Seq with (ss:=[[vs]]); simpl; simpl_Forall.
          * econstructor. eapply RefV, sem_var_union3'.
            econstructor; eauto; reflexivity.
          * eapply FindV, sem_var_union3'; [|econstructor; eauto; reflexivity].
            apply Env.find_In_from_list; eauto. solve_In.
        + simpl_Forall.
          take (sem_block_ck _ _ _ _) and eapply unnest_block_sem in it; eauto.
          * intros * Find Var. apply Equiv in Find as Find'.
            apply sem_var_union' in Var as [(Nin&Var)|Var].
            -- exfalso. eapply Env.from_list_find_In in Find. simpl_In.
               apply sem_var_In, DomL in Var. inv Var. simpl_In.
               eapply fresh_idents_In' in Hin; eauto. simpl_In.
               take (forall x, InMembers _ locs -> ~_) and eapply it; eauto using In_InMembers.
               rewrite <-map_fst_senv_of_ins, <-map_fst_senv_of_decls, <-map_app; solve_In.
            -- eapply sem_var_union3'. inv Var. econstructor; eauto.
               setoid_rewrite Find'; auto.
          * intros * Find Var.
            apply sem_var_union' in Var as [(Nin&Var)|Var].
            -- apply sem_var_union2; auto.
               1:{ destruct Dom' as (_&Dom'). rewrite Dom', senv_of_decls_app, IsLast_app.
                   apply sem_var_In, DomL in Var. inv Var.
                   intros [In|In]; inv In; simpl_In.
                   - take (forall x, InMembers _ locs -> ~_) and eapply it; eauto using In_InMembers.
                     rewrite <-map_fst_senv_of_ins, <-map_fst_senv_of_decls, <-map_app; solve_In.
                   - eapply ND3'; [|solve_In]. simpl.
                     rewrite app_assoc, InMembers_app; eauto using In_InMembers.
               }
            -- apply sem_var_union3'. subst.
               inv Var. econstructor; eauto. rewrite Find. cases_eqn Find.
               exfalso. eapply Env.from_list_find_In in Find0. simpl_In.
               take (_ (Last _) = _) and apply FEnv.find_In, DomL2 in it. inv it. simpl_In.
               eapply ND3'; [|solve_In]. rewrite ? InMembers_app. do 2 right. solve_In.
    Qed.

    Lemma normlast_top_block_sem : forall ins outs H bs blk blk' st st',
        unnested outs blk ->
        (exists ls : list ident, LastsDefined blk ls /\ Permutation ls (lasts_of_decls outs)) ->
        NoDupMembers outs ->
        NoDupLocals (map fst ins ++ map fst outs) blk ->
        Forall (AtomOrGensym norm1_prefs) (map fst ins ++ map fst outs) ->
        GoodLocals norm1_prefs blk ->
        dom H (senv_of_ins ins ++ senv_of_decls outs) ->
        sc_vars (senv_of_ins ins ++ senv_of_decls outs) H bs ->
        sem_block_ck G H bs blk ->
        normlast_top_block outs blk st = (blk', st') ->
        exists H',
          (forall x vs, sem_var H (Var x) vs -> sem_var H' (Var x) vs)
          /\ dom H' (senv_of_ins ins ++ senv_of_decls (remove_lasts outs))
          /\ sc_vars (senv_of_ins ins ++ senv_of_decls (remove_lasts outs)) H' bs
          /\ sem_block_ck G H' bs blk'.
    Proof.
      intros * Un Lasts NDo ND At Good Dom Sc Sem NL.
      unfold normlast_top_block in *. repeat inv_bind.
      eapply init_top_block_unnested in H0 as Un1; eauto.
      2:{ eapply NoDupLocals_incl; eauto. solve_incl_app. }
      inversion Un. inversion Un1. subst.
      assert (Forall (fun x : ident => AtomOrGensym norm1_prefs x \/ In x (st_ids st)) (map fst locs)) as AtL0.
      { inv Good. repeat Syn.inv_scope. simpl_Forall. auto. }
      eapply init_top_block_NoDupLocals with (xs:=map fst ins ++ map fst outs) in H0 as ND1; eauto.
      assert (remove_lasts x = remove_lasts outs) as RM.
      { clear - H0. repeat inv_bind. unfold remove_lasts.
        erewrite map_map, map_ext; [reflexivity|].
        intros; destruct_conjs; cases; auto.
      }
      assert (map fst x = map fst outs) as Fst.
      { now rewrite <-remove_lasts_fst, RM, remove_lasts_fst. }
      assert (NoDupLocals (map fst x) (Blocal (Scope locs0 blks0))) as ND'1.
      { rewrite Fst. eapply NoDupLocals_incl; [|eauto]. apply incl_appr, incl_refl. }
      eapply output_top_block_unnested in H1 as Un2; eauto.
      2:rewrite fst_NoDupMembers, Fst, <-fst_NoDupMembers; auto.
      inversion Un2; subst.
      assert (Forall (fun x => AtomOrGensym norm1_prefs x \/ In x (st_ids x1)) (map fst locs0)) as AtL1.
      { clear - H0 AtL0. repeat inv_bind. rewrite map_app, Forall_app. split.
        + simpl_Forall. destruct AtL0; auto.
          right. eapply incl_map; eauto. apply st_follows_incl; eauto using fresh_idents_st_follows.
        + eapply fresh_idents_In_ids in H. simpl_Forall. auto.
      }
      assert (Forall (fun x => AtomOrGensym norm1_prefs x \/ In x (st_ids x3)) (map fst locs1)) as AtL2.
      { clear - H1 AtL1. repeat inv_bind. rewrite map_app, Forall_app. split.
        + simpl_Forall. destruct AtL1; auto.
          right. eapply incl_map; eauto. apply st_follows_incl; eauto using fresh_idents_st_follows.
        + eapply fresh_idents_In_ids in H. simpl_Forall. auto.
      }
      eapply output_top_block_NoDupLocals with (outs:=x) in H1 as ND2; eauto.
      eapply unnest_top_block_unnested in H2 as Un3; eauto.
      2:{ rewrite fst_NoDupMembers, remove_lasts_fst, Fst, <-fst_NoDupMembers; auto. }
      2:{ eapply NoDupLocals_incl; [|eauto]. apply incl_appr.
          now rewrite remove_lasts_fst, Fst. }
      inversion Un3; subst.

      eapply init_top_block_sem with (outs:=outs) in H0 as (?&Ref1&Dom1&Sc1&Sem1); eauto.
      2,3:rewrite map_fst_senv_of_ins; auto.
      eapply output_top_block_sem with (outs:=x) in H1 as (Hi2&Ref2&Dom2&Sc2&Sem2); eauto.
      3,4:rewrite Fst; auto.
      2:rewrite fst_NoDupMembers, Fst, <-fst_NoDupMembers; auto.
      eapply unnest_top_block_sem in H2 as Sem3; eauto.
      3,4:rewrite remove_lasts_fst, Fst; auto.
      2:rewrite fst_NoDupMembers, remove_lasts_fst, Fst, <-fst_NoDupMembers; auto.
      rewrite <-RM.
      exists Hi2; split; [|split; [|split]]; eauto.
    Qed.

  End node.

  Lemma normlast_node_sem G1 G2 : forall f n ins outs,
      global_sem_refines G1 G2 ->
      Ordered_nodes (Global G1.(types) G1.(externs) (n::G1.(nodes))) ->
      Ordered_nodes (Global G2.(types) G2.(externs) (normlast_node n::G2.(nodes))) ->
      sem_node_ck (Global G1.(types) G1.(externs) (n::G1.(nodes))) f ins outs ->
      sem_node_ck (Global G2.(types) G2.(externs) ((normlast_node n)::G2.(nodes))) f ins outs.
  Proof with eauto.
    intros * Gref Hord1 Hord2 Hsem.

    inv Hsem; rename H0 into Hfind; simpl in Hfind. destruct (ident_eq_dec (n_name n) f).
    - erewrite find_node_now in Hfind; eauto. inv Hfind.
      (*The semantics of equations can be given according to G only *)
      assert (~Is_node_in_block (n_name n0) (n_block n0)) as Blk.
      { inv Hord1. destruct H6 as (Hisin&_). intro contra. eapply Hisin in contra as [? _]; auto. }
      eapply sem_block_ck_cons1 in Blk; eauto. clear H3.

      replace {| types := types G1; nodes := nodes G1 |} with G1 in * by (destruct G1; auto).
      take (clocked_node _ _ _) and destruct it as (Dom&Sc).

      eapply normlast_top_block_sem in Blk as (Hi'&Ref&Dom'&Sc'&Blk'); eauto using surjective_pairing.
      eapply Snode with (H:=Hi'); eauto.
      + erewrite find_node_now; eauto.
      + simpl_Forall. eauto.
      + simpl. unfold remove_lasts. simpl_Forall. eauto.
      + apply sem_block_ck_cons2; simpl...
        2:{ eapply find_node_not_Is_node_in in Hord2.
            2:erewrite find_node_now; eauto. contradict Hord2. auto. }
        destruct G1, G2. eapply sem_ref_sem_block; eauto.
      + simpl. constructor; simpl; auto.
      + apply n_syn.
      + apply n_lastd.
      + pose proof (n_nodup n0) as (Nd1&_). now apply NoDup_app_r, fst_NoDupMembers in Nd1.
      + apply n_nodup.
      + apply n_good.
      + apply n_good.
    - erewrite find_node_other in Hfind; eauto.
      eapply sem_node_ck_cons2...
      destruct G2; apply Gref.
      destruct G1; econstructor...
      eapply sem_block_ck_cons1; eauto using find_node_later_not_Is_node_in.
  Qed.

  Module Clocking := NLClockingFun(Ids)(Op)(OpAux)(Cks)(Senv)(Syn)(Cl)(NL).

  Lemma normlast_global_refines : forall G,
      wc_global G ->
      global_sem_refines G (normlast_global G).
  Proof with eauto using wc_global_Ordered_nodes.
    intros [].
    induction nodes0; intros * Hwc; simpl.
    - apply global_sem_ref_nil.
    - assert (Hwc':=Hwc).
      eapply Clocking.normlast_global_wc, wc_global_Ordered_nodes in Hwc' ;
        unfold normlast_global in Hwc'; simpl in Hwc'.
      apply global_sem_ref_cons with (f:=n_name a)...
      + inv Hwc. eapply IHnodes0...
      + intros ins outs Hsem; simpl in *.
        change types0 with ((Global types0 externs0 (map normlast_node nodes0)).(types)).
        eapply normlast_node_sem with (G1:=Global types0 externs0 nodes0)...
        inv Hwc...
  Qed.

  Theorem normlast_global_sem : forall G f ins outs,
      wc_global G ->
      sem_node_ck G f ins outs ->
      sem_node_ck (normlast_global G) f ins outs.
  Proof.
    intros.
    eapply normlast_global_refines in H; eauto.
    specialize (H f ins outs); auto.
  Qed.

End NLCORRECTNESS.

Module NLCorrectnessFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks : CLOCKS Ids Op OpAux)
       (CStr : COINDSTREAMS Ids Op OpAux Cks)
       (Senv : STATICENV Ids Op OpAux Cks)
       (Syn : LSYNTAX Ids Op OpAux Cks Senv)
       (Clo : LCLOCKING Ids Op OpAux Cks Senv Syn)
       (Lord : LORDERED Ids Op OpAux Cks Senv Syn)
       (Sem : LSEMANTICS Ids Op OpAux Cks Senv Syn Lord CStr)
       (LClockSem : LCLOCKEDSEMANTICS Ids Op OpAux Cks Senv Syn Clo Lord CStr Sem)
       (NL  : NORMLAST Ids Op OpAux Cks Senv Syn)
       <: NLCORRECTNESS Ids Op OpAux Cks CStr Senv Syn Clo Lord Sem LClockSem NL.
  Include NLCORRECTNESS Ids Op OpAux Cks CStr Senv Syn Clo Lord Sem LClockSem NL.
End NLCorrectnessFun.
