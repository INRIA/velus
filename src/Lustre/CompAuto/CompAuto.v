From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Velus Require Import Common.
From Velus Require Import CommonTyping.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Fresh.
From Velus Require Import Lustre.StaticEnv.
From Velus Require Import Lustre.LSyntax.
From Velus Require Import Lustre.SubClock.SubClock.

(** * Remove State Machines *)

Module Type COMPAUTO
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Import Cks : CLOCKS Ids Op OpAux)
       (Import Senv : STATICENV Ids Op OpAux Cks)
       (Import Syn : LSYNTAX Ids Op OpAux Cks Senv).

  Module Import SC := SubClockFun Ids Op OpAux Cks Senv Syn.

  Module Fresh := Fresh.Fresh(Ids).
  Import Fresh Notations Facts Tactics.
  Local Open Scope fresh_monad_scope.

  Definition FreshAnn A := Fresh auto A (type * clock).

  Definition fresh_ident : FreshAnn _ := fresh_ident None (OpAux.bool_velus_type, Cbase).

  Fixpoint init_state_exp ty ck (ini : list (exp * enumtag)) oth : exp :=
    match ini with
    | [] => add_whens (Eenum oth ty) ty ck
    | (e, k)::ini =>
        Ecase (subclock_exp ck (@Env.empty _) (@Env.empty _) e)
              [(OpAux.true_tag, [add_whens (Eenum k ty) ty ck]);
              (OpAux.false_tag, [init_state_exp ty ck ini oth])]
              None ([ty], ck)
    end.

  Fixpoint trans_exp ty (trans : list (exp * (enumtag * bool))) current : list exp :=
    match trans with
    | [] => [Eenum current ty; Eenum OpAux.false_tag OpAux.bool_velus_type]
    | (e, (k, r))::trans =>
      [Ecase e [(OpAux.true_tag, [Eenum k ty; Eenum (if r then OpAux.true_tag else OpAux.false_tag) OpAux.bool_velus_type]);
               (OpAux.false_tag, trans_exp ty trans current)]
             None ([ty; OpAux.bool_velus_type], Cbase)]
    end.

  Section auto_scope.
    Context {A : Type}.
    Variable f_auto : A -> FreshAnn (list block * list (list type)).
    (* Variable f_add_eqs : list block -> A -> A. *)

    Definition auto_scope (s : scope A) : FreshAnn (_ * list type) :=
      let 'Scope locs blks := s in
      do (blks', tys) <- f_auto blks;
      ret (Scope locs blks', concat tys).

  End auto_scope.

  Fixpoint auto_block (blk : block) : FreshAnn (block * list type) :=
    match blk with
    | Beq _ | Blast _ _ => ret (blk, [])
    | Breset blks er =>
        do (blks', tys) <- mmap2 auto_block blks;
        ret (Breset blks' er, concat tys)
    | Bswitch ec branches =>
        do (branches', tys) <- mmap2 (fun '(e, Branch _ blks) =>
                                       do (blks', tys) <- mmap2 auto_block blks;
                                       ret ((e, Branch [] blks'), concat tys)) branches;
        ret (Bswitch ec branches', concat tys)
    | Blocal s =>
        do (s', tys) <- auto_scope (mmap2 auto_block) s;
        ret (Blocal s', tys)
    | Bauto Weak ck (ini, oth) states =>
        do tyid <- fresh_ident;
        let xs := map snd (map fst states) in
        let ty := Tenum tyid xs in
        do st <- fresh_ident;
        do pst <- fresh_ident;
        do res <- fresh_ident;
        do pres <- fresh_ident;
        let stateq := Beq ([st; res],
                            [Efby [ init_state_exp ty ck ini oth;
                                    add_whens (Eenum OpAux.false_tag OpAux.bool_velus_type) OpAux.bool_velus_type ck]
                                  [Evar pst (ty, ck); Evar pres (OpAux.bool_velus_type, ck)]
                                  [(ty, ck); (OpAux.bool_velus_type, ck)]]) in
        do (branches, tys) <- mmap2 (fun '((e, _), Branch _ (_, s)) =>
                                      do (s', tys) <- auto_scope
                                                       (fun '(blks, trans) =>
                                                          do (blks', tys) <- mmap2 auto_block blks;
                                                          let transeq := Beq ([pst; pres], trans_exp ty trans e) in
                                                          ret (transeq::blks', tys))
                                                       s;
                                      ret ((e, (Branch [] [Breset [Blocal s'] (Evar res (OpAux.bool_velus_type, Cbase))])), tys)) states;
        let switch := Bswitch (Evar st (ty, ck)) branches in
        ret (Blocal (Scope [(st, (ty, ck, xH, None));
                            (pst, (ty, ck, xH, None));
                            (res, (OpAux.bool_velus_type, ck, xH, None));
                            (pres, (OpAux.bool_velus_type, ck, xH, None))]
                           [stateq;switch]), ty::concat tys)
    | Bauto Strong ck (_, oth) states =>
        do tyid <- fresh_ident;
        let xs := map snd (map fst states) in
        let ty := Tenum tyid xs in
        do st <- fresh_ident;
        do st1 <- fresh_ident;
        do res <- fresh_ident;
        do res1 <- fresh_ident;
        let stateq := Beq ([st; res],
                            [Efby [ add_whens (Eenum oth ty) ty ck;
                                    add_whens (Eenum OpAux.false_tag OpAux.bool_velus_type) OpAux.bool_velus_type ck]
                                  [Evar st1 (ty, ck); Evar res1 (OpAux.bool_velus_type, ck)]
                                  [(ty, ck); (OpAux.bool_velus_type, ck)]]) in
        let branches := map (fun '((e, _), Branch _ (unl, _)) =>
                               let transeq := Beq ([st1; res1], trans_exp (ty) unl e) in
                               (e, Branch [] [Breset [transeq] (Evar res (OpAux.bool_velus_type, Cbase))])) states in
        let switch1 := Bswitch (Evar st (ty, ck)) branches in
        do (branches, tys) <- mmap2 (fun '((e, _), Branch _ (_, s)) =>
                                      do (s', tys) <- auto_scope
                                                       (fun '(blks, trans) =>
                                                          do (blks', tys) <- mmap2 auto_block blks;
                                                          ret (blks', tys))
                                                       s;
                                      ret ((e, (Branch [] [Breset [Blocal s'] (Evar res1 (OpAux.bool_velus_type, Cbase))])), tys)) states;
        let switch2 := Bswitch (Evar st1 (ty, ck)) branches in
        ret (Blocal (Scope [(st, (ty, ck, xH, None));
                            (st1, (ty, ck, xH, None));
                            (res, (OpAux.bool_velus_type, ck, xH, None));
                            (res1, (OpAux.bool_velus_type, ck, xH, None))]
                           [stateq;switch1;switch2]), ty::concat tys)
    end.

  (** Preservation of st_follows *)

  Lemma auto_block_st_follows : forall blk blk' tys st st',
      auto_block blk st = ((blk', tys), st') ->
      st_follows st st'.
  Proof.
    induction blk using block_ind2; intros * Haut; try destruct type0;
      destruct_conjs; repeat inv_bind.
    - (* equation *) reflexivity.
    - (* last *) reflexivity.
    - (* reset *)
      eapply mmap2_st_follows; eauto.
    - (* switch *)
      eapply mmap2_st_follows; eauto; simpl_Forall.
      destruct b0. repeat inv_bind.
      eapply mmap2_st_follows; eauto; simpl_Forall; eauto.
    - (* automaton (weak) *)
      etransitivity. 2:eapply mmap2_st_follows; eauto.
      repeat (etransitivity; eauto with fresh).
      simpl_Forall. destruct b0 as [?(?&[?(?&?)])]. repeat inv_bind.
      eapply mmap2_st_follows; eauto; simpl_Forall; eauto.
    - (* automaton (strong) *)
      etransitivity. 2:eapply mmap2_st_follows; eauto.
      repeat (etransitivity; eauto with fresh).
      simpl_Forall. destruct b0 as [?(?&[?(?&?)])]. repeat inv_bind.
      eapply mmap2_st_follows; eauto; simpl_Forall; eauto.
    - (* local *)
      eapply mmap2_st_follows; eauto.
  Qed.

  (** Defined variables *)

  Import Permutation.

  Ltac auto_block_simpl_Forall :=
    repeat
      (match goal with
       | Hmap: mmap2 _ _ _ = (?blks', _, _) |- Forall _ ?blks' =>
         apply mmap2_values, Forall3_ignore13 in Hmap; simpl_Forall
       end; repeat inv_bind);
    eauto.

  Lemma auto_block_VarsDefinedComp : forall blk xs blk' tys st st',
      VarsDefinedComp blk xs ->
      auto_block blk st = ((blk', tys), st') ->
      VarsDefinedComp blk' xs.
  Proof.
    induction blk using block_ind2; intros * Hvd Haut; try destruct type0;
      inv Hvd; destruct_conjs; repeat inv_bind.
    - (* equation *) constructor.
    - (* last *) constructor.
    - (* reset *)
      constructor.
      apply mmap2_values, Forall3_ignore3, Forall2_swap_args in H0.
      eapply Forall2_trans_ex in H3; eauto. simpl_Forall; eauto.
    - (* switch *)
      apply mmap2_values in H0.
      constructor.
      + apply Forall3_ignore3 in H0; inv H0; congruence.
      + apply Forall3_ignore13 in H0; simpl_Forall.
        destruct b0; repeat inv_bind. take (VarsDefinedCompBranch _ _ _) and inv it; inv_VarsDefined.
        constructor; eauto using incl_nil'. do 2 esplit; eauto.
        apply mmap2_values, Forall3_ignore3, Forall2_swap_args in H5.
        eapply Forall2_trans_ex in Hvars; eauto. simpl_Forall; eauto.
    - (* automaton (weak) *)
      do 3 (econstructor; eauto using incl_nil'). split; [do 2 constructor; eauto|].
      2:{ simpl. rewrite app_nil_r.
          rewrite Permutation_app_comm. apply perm_skip, perm_swap. }
      take (mmap2 _ _ _ = _) and rename it into Hmmap. apply mmap2_values in Hmmap.
      constructor; eauto using incl_nil'.
      + apply Forall3_ignore3 in Hmmap; inv Hmmap; try congruence. auto.
      + apply Forall3_ignore13 in Hmmap; simpl_Forall.
        destruct b0 as [?(?&[?(?&?)])]; repeat inv_bind.
        take (VarsDefinedCompBranch _ _ _) and inv it; take (VarsDefinedCompScope _ _ _) and inv it; inv_VarsDefined.
        constructor; eauto using incl_nil'.
        apply mmap2_values, Forall3_ignore3, Forall2_swap_args in H10.
        eapply Forall2_trans_ex in Hvars; eauto.
        do 2 esplit.
        * repeat constructor; eauto using incl_nil'.
          do 2 esplit. repeat constructor. instantiate (1:=x12). simpl_Forall; eauto.
          simpl. rewrite Hperm. rewrite 2 app_comm_cons. reflexivity.
        * simpl. repeat rewrite app_nil_r; eauto using Permutation.
    - (* automaton (strong) *)
      do 3 (econstructor; eauto using incl_nil'). split; [do 2 constructor; eauto; [|constructor; eauto]|].
      + repeat econstructor; simpl. destruct states; simpl in *; auto. congruence.
        simpl_Forall. destruct b as [?(?&[?(?&?)])]. constructor; simpl; auto using incl_nil'.
        do 2 esplit; eauto. repeat constructor. instantiate (1:=[x3;x7]). constructor.
      + take (mmap2 _ _ _ = _) and rename it into Hmmap. apply mmap2_values in Hmmap.
        constructor; eauto using incl_nil'.
        * apply Forall3_ignore3 in Hmmap; inv Hmmap; try congruence.
        * apply Forall3_ignore13 in Hmmap; simpl_Forall.
          destruct b0 as [?(?&[?(?&?)])]; repeat inv_bind.
          take (VarsDefinedCompBranch _ _ _) and inv it; take (VarsDefinedCompScope _ _ _) and inv it; inv_VarsDefined.
          constructor; eauto using incl_nil'.
          apply mmap2_values, Forall3_ignore3, Forall2_swap_args in H10.
          eapply Forall2_trans_ex in Hvars; eauto.
          do 2 esplit.
          -- repeat constructor; eauto using incl_nil'.
             do 2 esplit. instantiate (1:=x11). simpl_Forall; eauto.
             eauto.
          -- simpl. repeat rewrite app_nil_r. reflexivity.
      + simpl. rewrite app_nil_r, Permutation_app_comm.
        apply perm_skip, perm_swap.
    - (* local *)
      inv H1; inv_VarsDefined.
      do 2 econstructor; eauto using incl_nil'. do 2 esplit; [|eauto].
      apply mmap2_values, Forall3_ignore3, Forall2_swap_args in H0.
      eapply Forall2_trans_ex in Hvars; eauto. simpl_Forall; eauto.
  Qed.

  Lemma auto_block_LastsDefined : forall blk xs blk' tys st st',
      LastsDefined blk xs ->
      auto_block blk st = ((blk', tys), st') ->
      LastsDefined blk' xs.
  Proof.
    induction blk using block_ind2; intros * Hvd Haut; try destruct type0;
      inv Hvd; destruct_conjs; repeat inv_bind.
    - (* equation *) constructor.
    - (* last *) constructor.
    - (* reset *)
      constructor.
      apply mmap2_values, Forall3_ignore3, Forall2_swap_args in H0.
      eapply Forall2_trans_ex in H3; eauto. simpl_Forall; eauto.
    - (* switch *)
      apply mmap2_values in H0.
      constructor.
      + apply Forall3_ignore3 in H0; inv H0; congruence.
      + apply Forall3_ignore13 in H0; simpl_Forall.
        destruct b0; repeat inv_bind. repeat inv_branch.
        constructor; eauto using incl_nil'.
        apply mmap2_values, Forall3_ignore13 in H5. simpl_Forall. eauto.
    - (* automaton (weak) *)
      take (mmap2 _ _ _ = _) and rename it into Hmmap. apply mmap2_values in Hmmap.
      repeat econstructor.
      + apply Forall3_ignore3 in Hmmap; inv Hmmap; try congruence. auto.
      + apply Forall3_ignore13 in Hmmap; simpl_Forall.
        repeat inv_branch. repeat inv_scope. repeat inv_bind.
        repeat constructor. replace [] with (@concat ident ([]::[])); repeat constructor.
        simpl.
        apply mmap2_values, Forall3_ignore3, Forall2_swap_args in H10.
        eapply Forall2_trans_ex in H6; eauto.
        do 2 esplit.
        * repeat constructor. instantiate (1:=x11). simpl_Forall; eauto.
        * simpl. repeat rewrite app_nil_r; eauto using Permutation.
    - (* automaton (strong) *)
      take (mmap2 _ _ _ = _) and rename it into Hmmap. apply mmap2_values in Hmmap.
      repeat econstructor.
      + intros Map. apply map_eq_nil in Map. contradiction.
      + simpl_Forall. repeat inv_branch. repeat econstructor.
        replace [] with (@concat ident [[]]); auto. repeat constructor.
      + apply Forall3_ignore3 in Hmmap; inv Hmmap; try congruence.
      + apply Forall3_ignore13 in Hmmap; simpl_Forall.
        repeat inv_branch. repeat inv_scope. repeat inv_bind.
        repeat constructor.
        replace [] with (@concat ident [[]]); auto. repeat constructor.
        apply mmap2_values, Forall3_ignore3, Forall2_swap_args in H10.
        eapply Forall2_trans_ex in H6; eauto.
        do 2 esplit; [|eauto].
        simpl_Forall. eauto.
    - (* local *)
      repeat inv_scope.
      do 2 econstructor; eauto using incl_nil'. do 2 esplit; [|eauto].
      apply mmap2_values, Forall3_ignore3, Forall2_swap_args in H0.
      eapply Forall2_trans_ex in H1; eauto. simpl_Forall; eauto.
  Qed.

  (** NoDupLocals *)

  Lemma auto_not_in_elab_prefs :
    ~PS.In auto elab_prefs.
  Proof.
    unfold elab_prefs, elab_prefs.
    rewrite PSF.singleton_iff.
    pose proof gensym_prefs_NoDup as Hnd. unfold gensym_prefs in Hnd.
    repeat rewrite NoDup_cons_iff in Hnd. destruct_conjs.
    intros contra; subst; rewrite contra in *; eauto with datatypes.
  Qed.

  Lemma fresh_idents_NoDup : forall x1 x2 x3 x4 st st1 st2 st3 st4,
      fresh_ident st = (x1, st1) ->
      fresh_ident st1 = (x2, st2) ->
      fresh_ident st2 = (x3, st3) ->
      fresh_ident st3 = (x4, st4) ->
      NoDup [x1;x2;x3;x4].
  Proof.
    intros * Hf1 Hf2 Hf3 Hf4.
    specialize (st_valid_NoDup st4) as Hvalid'.
    repeat (take (fresh_ident _ = _) and apply fresh_ident_vars_perm in it).
    repeat (take (Permutation _ _) and rewrite <-it in Hvalid'; clear it; simpl in Hvalid').
    repeat rewrite app_comm_cons in Hvalid'.
    repeat rewrite app_comm_cons in Hvalid'.
    repeat (take (NoDup (_ :: _)) and inv it).
    repeat constructor; intros Hin;
      repeat (take (In _ _) and inv it); subst; eauto with datatypes.
  Qed.

  Lemma auto_scope_NoDupScope {A} P_good P_nd f_auto : forall locs (blk: A) xs s' tys st st',
      auto_scope f_auto (Scope locs blk) st = ((s', tys), st') ->
      Forall (fun x => AtomOrGensym elab_prefs x \/ In x (st_ids st)) xs ->
      GoodLocalsScope P_good elab_prefs (Scope locs blk) ->
      NoDupScope P_nd xs (Scope locs blk) ->
      (forall xs blks' tys st st',
          f_auto blk st = ((blks', tys), st') ->
          Forall (fun x => AtomOrGensym elab_prefs x \/ In x (st_ids st)) xs ->
          P_good blk ->
          P_nd xs blk ->
          Forall (NoDupLocals xs) blks') ->
      NoDupScope (fun xs => Forall (NoDupLocals xs)) xs s'.
  Proof.
    intros * Haut Hat Hgood Hnd; inv Hgood; inv Hnd; repeat inv_bind.
    repeat econstructor; eauto.
    eapply H0; eauto.
    apply Forall_app; split; auto.
    simpl_Forall. auto.
  Qed.

  Lemma auto_block_NoDupLocals : forall blk xs blk' tys st st',
      auto_block blk st = ((blk', tys), st') ->
      Forall (fun x => AtomOrGensym elab_prefs x \/ In x (st_ids st)) xs ->
      GoodLocals elab_prefs blk ->
      NoDupLocals xs blk ->
      NoDupLocals xs blk'.
  Proof.
    Opaque auto_scope.
    induction blk using block_ind2; intros * Haut Hat Hgood Hnd; try destruct type0;
      inv Hgood; inv Hnd; destruct_conjs; repeat inv_bind.
    - (* equation *) constructor.
    - (* last *) constructor.

    - (* reset *)
      constructor.
      eapply mmap2_values_follows, Forall3_ignore13 in H0; eauto using auto_block_st_follows.
      simpl_Forall. eapply H; eauto.
      simpl_Forall. destruct Hat; eauto. right; eapply incl_map; eauto using st_follows_incl.

    - (* switch *)
      constructor.
      eapply mmap2_values_follows, Forall3_ignore13 in H0; eauto.
      2:intros; destruct_conjs; destruct b0; repeat inv_bind.
      2:{ eapply mmap2_st_follows; eauto. simpl_Forall; eauto using auto_block_st_follows. }
      simpl_Forall.
      take (NoDupBranch _ _) and inv it. take (GoodLocalsBranch _ _) and inv it. repeat inv_bind.
      repeat constructor.
      eapply mmap2_values_follows, Forall3_ignore13 in H1; eauto using auto_block_st_follows.
      simpl_Forall. eapply H; eauto.
      simpl_Forall. destruct Hat; eauto. right; eapply incl_map; eauto. eapply st_follows_incl; etransitivity; eauto.
      Transparent auto_scope.

    - (* automaton (weak) *)
      do 2 constructor; simpl.
      + repeat constructor.
        eapply mmap2_values_follows, Forall3_ignore13 in H7; eauto 6 with fresh.
        2:{ intros; destruct_conjs; destruct b0 as [?(?&[?(?&?)])]; destruct_conjs; repeat inv_bind.
            eapply mmap2_st_follows; eauto. simpl_Forall; eauto using auto_block_st_follows. }
        Opaque auto_scope.
        simpl_Forall. take (NoDupBranch _ _) and inv it. take (GoodLocalsBranch _ _) and inv it. destruct blks as (?&[?(?&?)]). repeat inv_bind.
        repeat constructor.
        eapply auto_scope_NoDupScope; eauto.
        1:apply Forall_app; split.
        * simpl_Forall. destruct Hat; auto. right; eapply incl_map; eauto.
          apply st_follows_incl; repeat (etransitivity; eauto with fresh).
        * repeat apply Forall_cons; auto.
          all:right; eapply incl_map; eauto using fresh_ident_Inids.
          all:apply st_follows_incl; repeat (try reflexivity; etransitivity; eauto using fresh_ident_st_follows).
        * eapply NoDupScope_incl' in H3; eauto using auto_not_in_elab_prefs.
          2:{ intros; simpl_Forall. eapply NoDupLocals_incl' in H14; eauto using auto_not_in_elab_prefs. }
          intros * Hin. apply in_app_iff in Hin as [|]; auto.
          repeat (take (fresh_ident _ = _) and apply fresh_ident_prefixed in it as (?&?&?)); subst.
          repeat (take (In x15 _) and inv it; eauto).
        * intros; repeat inv_bind.
          eapply mmap2_values_follows, Forall3_ignore13 in H11; eauto using auto_block_st_follows.
          repeat constructor. simpl_Forall. eapply H; eauto.
          simpl_Forall. destruct H14; auto. right. eapply incl_map; eauto using st_follows_incl.
      + rewrite fst_NoDupMembers; simpl.
        eapply fresh_idents_NoDup; eauto with fresh.
      + intros * Heq Hin. simpl_Forall.
        destruct Hat.
        * repeat (take (fresh_ident _ = _) and apply fresh_ident_prefixed in it as (?&?&?)); subst.
          destruct Heq as [|[|[|[|]]]]; subst; auto;
            eapply contradict_AtomOrGensym; eauto using auto_not_in_elab_prefs.
        * destruct Heq as [|[|[|[|]]]]; auto; subst;
            repeat (take (fresh_ident _ = (x11, _)) and eapply fresh_ident_nIn in it; eauto 7 with fresh;
                    eapply it, incl_map; eauto;
                    apply st_follows_incl; repeat (try reflexivity; etransitivity; eauto with fresh)).
          Transparent auto_scope.

    - (* automaton (strong) *)
      do 2 constructor; simpl. do 2 constructor.
      + repeat constructor. simpl_Forall.
        destruct b as [?(?&[?(?&?)])]. repeat constructor.
      + repeat constructor.
        eapply mmap2_values_follows, Forall3_ignore13 in H7; eauto 7 with fresh.
        2:{ intros; destruct_conjs; destruct b0 as [?(?&[?(?&?)])]; destruct_conjs; repeat inv_bind.
            eapply mmap2_st_follows; eauto. simpl_Forall; eauto using auto_block_st_follows. }
        Opaque auto_scope.
        simpl_Forall. take (NoDupBranch _ _) and inv it. take (GoodLocalsBranch _ _) and inv it. destruct blks as (?&[?(?&?)]). repeat inv_bind.
        repeat constructor.
        eapply auto_scope_NoDupScope; eauto.
        1:apply Forall_app; split.
        * simpl_Forall. destruct Hat; auto. right; eapply incl_map; eauto.
          apply st_follows_incl; repeat (etransitivity; eauto with fresh).
        * repeat apply Forall_cons; auto.
          all:right; eapply incl_map; eauto using fresh_ident_Inids.
          all:apply st_follows_incl; repeat (try reflexivity; etransitivity; eauto using fresh_ident_st_follows).
        * eapply NoDupScope_incl' in H3; eauto using auto_not_in_elab_prefs.
          2:{ intros; simpl_Forall. eapply NoDupLocals_incl' in H14; eauto using auto_not_in_elab_prefs. }
          intros * Hin. apply in_app_iff in Hin as [|]; auto.
          repeat (take (fresh_ident _ = _) and apply fresh_ident_prefixed in it as (?&?&?)); subst.
          repeat (take (In _ _) and inv it; eauto).
        * intros; repeat inv_bind.
          eapply mmap2_values_follows, Forall3_ignore13 in H11; eauto using auto_block_st_follows.
          repeat constructor. simpl_Forall. eapply H; eauto.
          simpl_Forall. destruct H14; auto. right. eapply incl_map; eauto using st_follows_incl.
      + rewrite fst_NoDupMembers; simpl.
        eapply fresh_idents_NoDup; eauto with fresh.
      + intros * Heq Hin. simpl_Forall.
        destruct Hat.
        * repeat (take (fresh_ident _ = _) and apply fresh_ident_prefixed in it as (?&?&?)); subst.
          destruct Heq as [|[|[|[|]]]]; subst; auto;
            eapply contradict_AtomOrGensym; eauto using auto_not_in_elab_prefs.
        * destruct Heq as [|[|[|[|]]]]; auto; subst;
            repeat (take (fresh_ident _ = (x11, _)) and eapply fresh_ident_nIn in it; eauto 7 with fresh;
                    eapply it, incl_map; eauto;
                    apply st_follows_incl; repeat (try reflexivity; etransitivity; eauto with fresh)).

    - (* local *)
      constructor; auto.
      eapply auto_scope_NoDupScope; eauto.
      intros.
      eapply mmap2_values_follows, Forall3_ignore13 in H2; eauto using auto_block_st_follows.
      simpl_Forall. eapply H; eauto. simpl_Forall.
      destruct H4; eauto. right; eapply incl_map; eauto using st_follows_incl.
      Transparent auto_scope.
  Qed.

  (** GoodLocals *)

  Lemma auto_block_GoodLocals : forall blk blk' tys st st',
      GoodLocals elab_prefs blk ->
      auto_block blk st = ((blk', tys), st') ->
      GoodLocals auto_prefs blk'.
  Proof.
    induction blk using block_ind2; intros * Hgood Haut; try destruct type0;
      inv Hgood; destruct_conjs; repeat inv_bind.
    - (* equation *) constructor.
    - (* last *) constructor.
    - (* reset *)
      constructor. auto_block_simpl_Forall.
    - (* switch *)
      constructor. auto_block_simpl_Forall.
      destruct b0; repeat inv_bind. take (GoodLocalsBranch _ _) and inv it.
      constructor; eauto using Forall_AtomOrGensym_add. auto_block_simpl_Forall.
    - (* automaton (weak) *)
      do 2 constructor; simpl.
      + repeat (take (fresh_ident _ = _) and apply fresh_ident_prefixed in it as (?&?&?)); subst.
        repeat apply Forall_cons; auto.
        all:right; do 2 esplit; eauto; now apply PSF.add_1.
      + repeat constructor. auto_block_simpl_Forall.
        destruct b0 as [?(?&[?(?&?)])]; repeat inv_bind. take (GoodLocalsBranch _ _) and inv it. take (GoodLocalsScope _ _ _) and inv it.
        repeat constructor; eauto using Forall_AtomOrGensym_add.
        auto_block_simpl_Forall.
    - (* automaton (strong) *)
      do 2 constructor; simpl. 2:do 2 constructor.
      + repeat (take (fresh_ident _ = _) and apply fresh_ident_prefixed in it as (?&?&?)); subst.
        repeat apply Forall_cons; auto.
        all:right; do 2 esplit; eauto; now apply PSF.add_1.
      + constructor. simpl_Forall. destruct b as [?(?&[?(?&?)])]; repeat inv_bind. repeat constructor.
      + repeat constructor. auto_block_simpl_Forall.
        destruct b0 as [?(?&[?(?&?)])]; repeat inv_bind. take (GoodLocalsBranch _ _) and inv it. take (GoodLocalsScope _ _ _) and inv it.
        repeat constructor; eauto using Forall_AtomOrGensym_add.
        auto_block_simpl_Forall.
    - (* local *)
      inv H1. do 2 constructor; eauto using Forall_AtomOrGensym_add.
      auto_block_simpl_Forall.
  Qed.

  (** No more automaton *)

  Lemma auto_block_noauto : forall blk blk' tys st st',
      auto_block blk st = ((blk', tys), st') ->
      noauto_block blk'.
  Proof.
    induction blk using block_ind2; intros * Haut; try destruct type0;
      destruct_conjs; repeat inv_bind.
    - (* equation *)
      constructor.
    - (* last *)
      constructor.
    - (* reset *)
      constructor. auto_block_simpl_Forall.
    - (* switch *)
      constructor. auto_block_simpl_Forall.
      destruct b0. repeat inv_bind. constructor; auto. auto_block_simpl_Forall.
    - (* automaton (weak) *)
      repeat constructor. auto_block_simpl_Forall.
      destruct b0 as (?&[?(?&?&?)]).
      repeat inv_bind. repeat constructor; auto.
      auto_block_simpl_Forall.
    - (* automaton (strong) *)
      repeat constructor.
      + simpl_Forall. destruct b as [?(?&[?(?&?)])]. repeat constructor.
      + auto_block_simpl_Forall.
        destruct b0 as (?&[?(?&?&?)]).
        repeat inv_bind. repeat constructor; auto.
        auto_block_simpl_Forall.
    - (* local *)
      repeat constructor; auto. auto_block_simpl_Forall.
  Qed.

  Program Definition auto_node (n: @node complete elab_prefs) : @node noauto auto_prefs * list type :=
    let res := auto_block (n_block n) init_st in
    ({| n_name := n_name n;
        n_hasstate := n_hasstate n;
        n_in := n_in n;
        n_out := n_out n;
        n_block := (fst (fst res));
        n_ingt0 := n_ingt0 n;
        n_outgt0 := n_outgt0 n
     |}, snd (fst res)).
  Next Obligation.
    destruct (auto_block _ _) as ((?&?)&?) eqn:Hauto; simpl.
    pose proof (n_syn n) as Syn. inversion_clear Syn as [??? Vars Perm].
    pose proof (n_nodup n) as (Hnd1&Hnd2).
    pose proof (n_good n) as (Hgood1&Hgood2&Hgood3).
    apply Permutation_map_inv in Perm as (?&?&Perm); subst.
    do 2 esplit; [|symmetry; eapply Permutation_map; eauto].
    eapply VarsDefinedComp_VarsDefined, auto_block_VarsDefinedComp; eauto.
    1:{ erewrite map_map, map_ext with (g:=fst), <-Perm; simpl. 2:intros; destruct_conjs; auto.
        eapply NoDupLocals_incl, auto_block_NoDupLocals, Hnd2; eauto. 2:simpl_Forall; auto.
        solve_incl_app. }
    erewrite map_map, map_ext; eauto. intros; destruct_conjs; auto.
  Qed.
  Next Obligation.
    pose proof (n_lastd n) as (?&Last&Perm).
    destruct (auto_block _ _) as ((?&?)&?) eqn:Hauto; simpl.
    do 2 esplit; eauto using auto_block_LastsDefined.
  Qed.
  Next Obligation.
    destruct (auto_block _ _) as ((?&?)&?) eqn:Hauto; simpl.
    pose proof (n_nodup n) as (Hnd1&Hnd2).
    pose proof (n_good n) as (Hgood1&Hgood2&Hgood3).
    split; auto.
    eapply auto_block_NoDupLocals; eauto.
    - simpl_Forall; auto.
  Qed.
  Next Obligation.
    destruct (auto_block _ _) as ((?&?)&?) eqn:Hauto; simpl.
    pose proof (n_good n) as (Hgood1&Hgood2&Hgood3).
    repeat (split; eauto using Forall_AtomOrGensym_add, auto_block_GoodLocals).
  Qed.
  Next Obligation.
    destruct (auto_block _ _) as ((?&?)&?) eqn:Hauto; simpl.
    pose proof (n_syn n) as Hsyn. inversion_clear Hsyn as [??? Vars Perm].
    constructor; eauto using auto_block_noauto.
    do 2 esplit; eauto using auto_block_VarsDefinedComp.
  Qed.

  Definition auto_global (G : @global complete elab_prefs) : @global noauto auto_prefs :=
    let ndstys := map auto_node G.(nodes) in
    Global (G.(types)++flat_map snd ndstys) G.(externs) (map fst ndstys).

  Lemma auto_node_iface_eq : forall n,
      node_iface_eq n (fst (auto_node n)).
  Proof.
    intros *; simpl.
    constructor; simpl; auto.
  Qed.

  Lemma auto_global_find_node : forall G f n,
      find_node f G = Some n ->
      exists n', find_node f (auto_global G) = Some n' /\ node_iface_eq n n'.
  Proof.
    intros []. revert types0. unfold auto_global.
    induction nodes0; intros * Hfind; simpl in *. inv Hfind.
    apply find_node_cons in Hfind as [(?&?)|(Hneq&?)]; subst; simpl in *.
    - do 2 esplit. apply find_node_now; auto.
      apply auto_node_iface_eq.
    - edestruct IHnodes0 as (?&?&?); eauto.
      do 2 esplit; eauto.
      rewrite find_node_other; eauto.
      erewrite find_node_change_types; eauto.
  Qed.

  Lemma auto_global_iface_incl : forall G,
      global_iface_incl G (auto_global G).
  Proof.
    repeat split.
    - simpl. apply incl_appl, incl_refl.
    - reflexivity.
    - intros. apply auto_global_find_node; auto.
  Qed.

  Lemma auto_global_find_node' : forall G f n,
      find_node f (auto_global G) = Some n ->
      exists n', find_node f G = Some n' /\ node_iface_eq n n'.
  Proof.
    intros []. revert types0. unfold auto_global.
    induction nodes0; intros * Hfind; simpl in *. inv Hfind.
    apply find_node_cons in Hfind as [(?&?)|(Hneq&?)]; subst; simpl in *.
    - do 2 esplit. apply find_node_now; auto.
      apply node_iface_eq_sym, auto_node_iface_eq.
    - edestruct IHnodes0 as (?&?&?); eauto.
      2:{ do 2 esplit; eauto.
          rewrite find_node_other; eauto. }
      erewrite find_node_change_types; eauto.
  Qed.

End COMPAUTO.

Module CompAutoFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks : CLOCKS Ids Op OpAux)
       (Senv : STATICENV Ids Op OpAux Cks)
       (Syn : LSYNTAX Ids Op OpAux Cks Senv)
       <: COMPAUTO Ids Op OpAux Cks Senv Syn.
  Include COMPAUTO Ids Op OpAux Cks Senv Syn.
End CompAutoFun.
