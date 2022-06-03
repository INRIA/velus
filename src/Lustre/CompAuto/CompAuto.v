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

  Definition FreshAnn A := Fresh A (type * clock).

  Definition fresh_ident := fresh_ident auto None (OpAux.bool_velus_type, Cbase).

  Fixpoint init_state_exp ty ck (ini : list (exp * enumtag)) oth : exp :=
    match ini with
    | [] => add_whens (Eenum oth ty) ty ck
    | (e, k)::ini =>
        Ecase (subclock_exp ck (@Env.empty _) e)
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
      let 'Scope locs _ blks := s in
      do (blks', tys) <- f_auto blks;
      ret (Scope locs [] blks', concat tys).

  End auto_scope.

  Fixpoint generate_constructors (n : nat) :=
    match n with
    | 0 => ret []
    | S n => do xs <- generate_constructors n;
            do x <- fresh_ident;
            ret (x::xs)
    end.

  Fixpoint auto_block (blk : block) : FreshAnn (block * list type) :=
    match blk with
    | Beq _ => ret (blk, [])
    | Breset blks er =>
        do (blks', tys) <- mmap2 auto_block blks;
        ret (Breset blks' er, concat tys)
    | Bswitch ec branches =>
        do (branches', tys) <- mmap2 (fun '(e, blks) =>
                                       do (blks', tys) <- auto_scope (mmap2 auto_block) blks;
                                       ret ((e, blks'), tys)) branches;
        ret (Bswitch ec branches', concat tys)
    | Blocal s =>
        do (s', tys) <- auto_scope (mmap2 auto_block) s;
        ret (Blocal s', tys)
    | Bauto Weak ck (ini, oth) states =>
        do tyid <- fresh_ident;
        do xs <- generate_constructors (length states);
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
        do (branches, tys) <- mmap2 (fun '(e, (_, s)) =>
                                      do (s', tys) <- auto_scope
                                                       (fun '(blks, trans) =>
                                                          do (blks', tys) <- mmap2 auto_block blks;
                                                          let transeq := Beq ([pst; pres], trans_exp ty trans e) in
                                                          ret (transeq::blks', tys))
                                                       s;
                                      ret ((e, (Scope [] [] [Breset [Blocal s'] (Evar res (OpAux.bool_velus_type, Cbase))])), tys)) states;
        let switch := Bswitch (Evar st (ty, ck)) branches in
        ret (Blocal (Scope [(st, (ty, ck, xH, None));
                            (pst, (ty, ck, xH, None));
                            (res, (OpAux.bool_velus_type, ck, xH, None));
                            (pres, (OpAux.bool_velus_type, ck, xH, None))] []
                           [stateq;switch]), ty::concat tys)
    | Bauto Strong ck (_, oth) states =>
        do tyid <- fresh_ident;
        do xs <- generate_constructors (length states);
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
        let branches := map (fun '(e, (unl, _)) =>
                               let transeq := Beq ([st1; res1], trans_exp (ty) unl e) in
                               (e, Scope [] [] [Breset [transeq] (Evar res (OpAux.bool_velus_type, Cbase))])) states in
        let switch1 := Bswitch (Evar st (ty, ck)) branches in
        do (branches, tys) <- mmap2 (fun '(e, (_, s)) =>
                                      do (s', tys) <- auto_scope
                                                       (fun '(blks, trans) =>
                                                          do (blks', tys) <- mmap2 auto_block blks;
                                                          ret (blks', tys))
                                                       s;
                                      ret ((e, (Scope [] [] [Breset [Blocal s'] (Evar res1 (OpAux.bool_velus_type, Cbase))])), tys)) states;
        let switch2 := Bswitch (Evar st1 (ty, ck)) branches in
        ret (Blocal (Scope [(st, (ty, ck, xH, None));
                            (st1, (ty, ck, xH, None));
                            (res, (OpAux.bool_velus_type, ck, xH, None));
                            (res1, (OpAux.bool_velus_type, ck, xH, None))] []
                           [stateq;switch1;switch2]), ty::concat tys)
    end.

  (** Preservation of st_valid_after *)

  Lemma generate_constructors_st_valid aft : forall n xs st st',
      st_valid_after st auto aft ->
      generate_constructors n st = (xs, st') ->
      st_valid_after st' auto aft.
  Proof.
    induction n; intros * Hval Hgen; repeat inv_bind; auto.
    eapply IHn in H; [|eauto]; eauto with fresh.
  Qed.

  Global Hint Resolve generate_constructors_st_valid : fresh.

  Lemma auto_block_st_valid aft : forall blk blk' tys st st',
      st_valid_after st auto aft ->
      auto_block blk st = ((blk', tys), st') ->
      st_valid_after st' auto aft.
  Proof.
    induction blk using block_ind2; intros * Hvalid Haut; try destruct type0;
      destruct_conjs; repeat inv_bind; auto.
    - (* reset *)
      eapply mmap2_st_valid; eauto. simpl_Forall; eauto.
    - (* switch *)
      eapply mmap2_st_valid; eauto. simpl_Forall.
      destruct s0. repeat inv_bind.
      eapply mmap2_st_valid; eauto. simpl_Forall; eauto.
    - (* automaton (weak) *)
      eapply mmap2_st_valid; eauto 8 using fresh_ident_st_valid, generate_constructors_st_valid. simpl_Forall.
      destruct s0; destruct_conjs. repeat inv_bind.
      eapply mmap2_st_valid; eauto. simpl_Forall; eauto.
    - (* automaton (strong) *)
      eapply mmap2_st_valid; eauto 8 using fresh_ident_st_valid, generate_constructors_st_valid. simpl_Forall.
      destruct s0; destruct_conjs. repeat inv_bind.
      eapply mmap2_st_valid; eauto. simpl_Forall; eauto.
    - (* local *)
      eapply mmap2_st_valid; eauto. simpl_Forall; eauto.
  Qed.

  Corollary auto_scope_st_valid1 aft : forall s blks' tys st st',
      st_valid_after st auto aft ->
      auto_scope (mmap2 auto_block) s st = (blks', tys, st') ->
      st_valid_after st' auto aft.
  Proof.
    intros [] * Hval Hauto.
    repeat inv_bind. eapply mmap2_st_valid; eauto.
    simpl_Forall; eauto using auto_block_st_valid.
  Qed.

  Corollary auto_scope_st_valid2 aft pst pres ty e : forall s blks' tys st st',
      st_valid_after st auto aft ->
      auto_scope
        (fun '(blks, trans) =>
           do (blks', tys) <- mmap2 auto_block blks;
           let transeq := Beq ([pst; pres], trans_exp ty trans e) in
           ret (transeq::blks', tys))
        s st = (blks', tys, st') ->
      st_valid_after st' auto aft.
  Proof.
    intros [] * Hval Hauto. destruct_conjs.
    repeat inv_bind. eapply mmap2_st_valid; eauto.
    simpl_Forall; eauto using auto_block_st_valid.
  Qed.

  Corollary auto_scope_st_valid3 aft : forall (s : scope (_ * list transition)) blks' tys st st',
      st_valid_after st auto aft ->
      auto_scope (fun '(blks, trans) =>
                    do (blks', tys) <- mmap2 auto_block blks;
                    ret (blks', tys))
        s st = (blks', tys, st') ->
      st_valid_after st' auto aft.
  Proof.
    intros [] * Hval Hauto. destruct_conjs.
    repeat inv_bind. eapply mmap2_st_valid; eauto.
    simpl_Forall; eauto using auto_block_st_valid.
  Qed.

  (** st_follows *)

  Lemma generate_constructors_st_follows : forall n xs st st',
      generate_constructors n st = (xs, st') ->
      st_follows st st'.
  Proof.
    induction n; intros * Hgen; repeat inv_bind; try reflexivity.
    etransitivity; eauto with fresh.
  Qed.

  Global Hint Resolve generate_constructors_st_follows : fresh.

  Lemma auto_block_st_follows : forall blk blk' tys st st',
      auto_block blk st = ((blk', tys), st') ->
      st_follows st st'.
  Proof.
    induction blk using block_ind2; intros * Haut; try destruct type0;
      destruct_conjs; repeat inv_bind.
    - (* equation *)
      reflexivity.
    - (* reset *)
      eapply mmap2_st_follows; eauto.
    - (* switch *)
      eapply mmap2_st_follows; eauto; simpl_Forall.
      destruct s0. repeat inv_bind.
      eapply mmap2_st_follows; eauto; simpl_Forall; eauto.
    - (* automaton (weak) *)
      etransitivity. 2:eapply mmap2_st_follows; eauto.
      repeat (etransitivity; eauto with fresh).
      simpl_Forall. destruct s0; destruct_conjs. repeat inv_bind.
      eapply mmap2_st_follows; eauto; simpl_Forall; eauto.
    - (* automaton (strong) *)
      etransitivity. 2:eapply mmap2_st_follows; eauto.
      repeat (etransitivity; eauto with fresh).
      simpl_Forall. destruct s0; destruct_conjs. repeat inv_bind.
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

  Lemma auto_block_VarsDefined : forall blk xs blk' tys st st',
      VarsDefined blk xs ->
      auto_block blk st = ((blk', tys), st') ->
      VarsDefined blk' xs.
  Proof.
    induction blk using block_ind2; intros * Hvd Haut; try destruct type0;
      inv Hvd; destruct_conjs; repeat inv_bind.
    - (* equation *)
      constructor.
    - (* reset *)
      constructor.
      apply mmap2_values, Forall3_ignore3, Forall2_swap_args in H0.
      eapply Forall2_trans_ex in H3; eauto. simpl_Forall; eauto.
    - (* switch *)
      apply mmap2_values in H0.
      constructor.
      + apply Forall3_ignore3 in H0; inv H0; congruence.
      + apply Forall3_ignore13 in H0; simpl_Forall.
        destruct s0; repeat inv_bind.
        inv H4; inv_VarsDefined. constructor; eauto using incl_nil'. do 2 esplit; eauto.
        apply mmap2_values, Forall3_ignore3, Forall2_swap_args in H5.
        eapply Forall2_trans_ex in Hvars; eauto. simpl_Forall; eauto.
    - (* automaton (weak) *)
      do 3 (econstructor; eauto using incl_nil'). split; [do 2 constructor; eauto|].
      2:{ simpl. rewrite app_nil_r.
          rewrite Permutation_app_comm. apply perm_skip, perm_swap. }
      apply mmap2_values in H8.
      constructor; eauto using incl_nil'.
      + apply Forall3_ignore3 in H8; inv H8; try congruence. auto.
      + apply Forall3_ignore13 in H8; simpl_Forall.
        destruct s0; destruct_conjs; repeat inv_bind.
        inv H6; inv_VarsDefined. constructor; eauto using incl_nil'.
        apply mmap2_values, Forall3_ignore3, Forall2_swap_args in H11.
        eapply Forall2_trans_ex in Hvars; eauto.
        do 2 esplit.
        * repeat constructor; eauto using incl_nil'.
          do 2 esplit. repeat constructor. instantiate (1:=x14). simpl_Forall; eauto.
          simpl. rewrite Hperm. rewrite 2 app_comm_cons. reflexivity.
        * simpl. repeat rewrite app_nil_r; eauto using Permutation.
    - (* automaton (strong) *)
      do 3 (econstructor; eauto using incl_nil'). split; [do 2 constructor; eauto; [|constructor; eauto]|].
      + repeat econstructor; simpl. destruct states; simpl in *; auto. congruence.
        simpl_Forall. constructor. rewrite app_nil_r.
        do 2 esplit; eauto. repeat constructor. instantiate (1:=[x5;x9]). constructor.
        apply incl_nil'.
      + apply mmap2_values in H8.
        constructor; eauto using incl_nil'.
        * apply Forall3_ignore3 in H8; inv H8; try congruence.
        * apply Forall3_ignore13 in H8; simpl_Forall.
          destruct s0; destruct_conjs; repeat inv_bind.
          inv H6; inv_VarsDefined. constructor; eauto using incl_nil'.
          apply mmap2_values, Forall3_ignore3, Forall2_swap_args in H11.
          eapply Forall2_trans_ex in Hvars; eauto.
          do 2 esplit.
          -- repeat constructor; eauto using incl_nil'.
             do 2 esplit. instantiate (1:=x13). simpl_Forall; eauto.
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

  (** NoDupLocals *)

  Lemma auto_not_in_last_prefs :
    ~PS.In auto last_prefs.
  Proof.
    unfold last_prefs, elab_prefs.
    rewrite PSF.add_iff, PSF.singleton_iff.
    pose proof gensym_prefs_NoDup as Hnd. unfold gensym_prefs in Hnd.
    repeat rewrite NoDup_cons_iff in Hnd. destruct_conjs.
    intros [contra|contra]; subst; rewrite contra in *; eauto with datatypes.
  Qed.

  Lemma fresh_idents_NoDup aft : forall x1 x2 x3 x4 st st1 st2 st3 st4,
      fresh_ident st = (x1, st1) ->
      fresh_ident st1 = (x2, st2) ->
      fresh_ident st2 = (x3, st3) ->
      fresh_ident st3 = (x4, st4) ->
      st_valid_after st auto aft ->
      NoDup [x1;x2;x3;x4].
  Proof.
    intros * Hf1 Hf2 Hf3 Hf4 Hvalid.
    assert (st_valid_after st4 auto aft) as Hvalid' by (eauto using fresh_ident_st_valid).
    apply st_valid_NoDup in Hvalid'.
    repeat (take (fresh_ident _ = _) and apply fresh_ident_vars_perm in it).
    repeat (take (Permutation _ _) and rewrite <-it in Hvalid'; clear it; simpl in Hvalid').
    repeat rewrite app_comm_cons in Hvalid'. apply NoDup_app_l in Hvalid'.
    repeat rewrite app_comm_cons in Hvalid'.
    repeat (take (NoDup (_ :: _)) and inv it).
    repeat constructor; intros Hin;
      repeat (take (In _ _) and inv it); subst; eauto with datatypes.
  Qed.

  Lemma auto_scope_NoDupScope {A} P_good P_nd f_auto aft : forall locs caus (blk: A) xs s' tys st st',
      st_valid_after st auto aft ->
      Forall (fun x => AtomOrGensym last_prefs x \/ In x (st_ids st)) xs ->
      GoodLocalsScope P_good last_prefs (Scope locs caus blk) ->
      NoDupScope P_nd xs (Scope locs caus blk) ->
      auto_scope f_auto (Scope locs caus blk) st = ((s', tys), st') ->
      (forall xs blks' tys st st',
          st_valid_after st auto aft ->
          Forall (fun x => AtomOrGensym last_prefs x \/ In x (st_ids st)) xs ->
          P_good blk ->
          P_nd xs blk ->
          f_auto blk st = ((blks', tys), st') ->
          Forall (NoDupLocals xs) blks') ->
      NoDupScope (fun xs => Forall (NoDupLocals xs)) xs s'.
  Proof.
    intros * Hvalid Hat Hgood Hnd Haut; inv Hgood; inv Hnd; repeat inv_bind.
    repeat econstructor; eauto.
    eapply H0; eauto.
    apply Forall_app; split; auto.
    simpl_Forall. auto.
  Qed.

  Lemma auto_block_NoDupLocals aft : forall blk xs blk' tys st st',
      st_valid_after st auto aft ->
      Forall (fun x => AtomOrGensym last_prefs x \/ In x (st_ids st)) xs ->
      GoodLocals last_prefs blk ->
      NoDupLocals xs blk ->
      auto_block blk st = ((blk', tys), st') ->
      NoDupLocals xs blk'.
  Proof.
    Opaque auto_scope.
    induction blk using block_ind2; intros * Hvalid Hat Hgood Hnd Haut; try destruct type0;
      inv Hgood; inv Hnd; destruct_conjs; repeat inv_bind.
    - (* equation *)
      constructor.

    - (* reset *)
      constructor.
      eapply mmap2_values_valid_follows, Forall3_ignore13 in H0; eauto using auto_block_st_valid, auto_block_st_follows.
      simpl_Forall. eapply H; eauto.
      simpl_Forall. destruct Hat; eauto. right; eapply incl_map; eauto using st_follows_incl.

    - (* switch *)
      constructor.
      eapply mmap2_values_valid_follows, Forall3_ignore13 in H0; eauto.
      Transparent auto_scope.
      2,3:intros; destruct_conjs; destruct s0; repeat inv_bind.
      2:{ eapply mmap2_st_valid; eauto. simpl_Forall; eauto using auto_block_st_valid. }
      2:{ eapply mmap2_st_follows; eauto. simpl_Forall; eauto using auto_block_st_follows. }
      Opaque auto_scope.
      simpl_Forall. destruct s0; repeat inv_bind. eapply auto_scope_NoDupScope; eauto.
      + simpl_Forall. destruct Hat; eauto. right; eapply incl_map; eauto using st_follows_incl.
      + intros.
        eapply mmap2_values_valid_follows, Forall3_ignore13 in H12; eauto using auto_block_st_valid, auto_block_st_follows.
        simpl_Forall. eapply H; eauto.
        simpl_Forall. destruct H9; eauto. right; eapply incl_map; eauto using st_follows_incl.
      Transparent auto_scope.

    - (* automaton (weak) *)
      do 2 constructor; simpl.
      + repeat constructor.
        eapply mmap2_values_valid_follows, Forall3_ignore13 in H8; eauto 7 with fresh.
        2,3:intros; destruct_conjs; destruct s0; destruct_conjs; repeat inv_bind.
        2:{ eapply mmap2_st_valid; eauto. simpl_Forall; eauto using auto_block_st_valid. }
        2:{ eapply mmap2_st_follows; eauto. simpl_Forall; eauto using auto_block_st_follows. }
        Opaque auto_scope.
        simpl_Forall. repeat inv_bind. destruct s0; destruct_conjs.
        repeat constructor. 2:{ intros * Hin; inv Hin. } rewrite app_nil_r.
        eapply auto_scope_NoDupScope; eauto.
        1:apply Forall_app; split.
        * simpl_Forall. destruct Hat; auto. right; eapply incl_map; eauto.
          apply st_follows_incl; repeat (etransitivity; eauto with fresh).
        * repeat apply Forall_cons; auto.
          all:right; eapply incl_map; eauto using fresh_ident_Inids.
          all:apply st_follows_incl; repeat (try reflexivity; etransitivity; eauto using fresh_ident_st_follows).
        * eapply NoDupScope_incl' in H3; eauto using auto_not_in_last_prefs.
          2:{ intros; simpl_Forall. eapply NoDupLocals_incl' in H14; eauto using auto_not_in_last_prefs. }
          intros * Hin. apply in_app_iff in Hin as [|]; auto.
          repeat (take (fresh_ident _ = _) and apply fresh_ident_prefixed in it as (?&?&?)); subst.
          repeat (take (In x17 _) and inv it; eauto).
        * intros; repeat inv_bind.
          eapply mmap2_values_valid_follows, Forall3_ignore13 in H18; eauto using auto_block_st_valid, auto_block_st_follows.
          repeat constructor. simpl_Forall. eapply H; eauto.
          simpl_Forall. destruct H15; auto. right. eapply incl_map; eauto using st_follows_incl.
      + rewrite fst_NoDupMembers; simpl.
        eapply fresh_idents_NoDup; eauto with fresh.
      + intros * Heq Hin. simpl_Forall.
        destruct Hat.
        * repeat (take (fresh_ident _ = _) and apply fresh_ident_prefixed in it as (?&?&?)); subst.
          destruct Heq as [|[|[|[|]]]]; subst; auto;
            eapply contradict_AtomOrGensym; eauto using auto_not_in_last_prefs.
        * destruct Heq as [|[|[|[|]]]]; auto; subst;
            repeat (take (fresh_ident _ = (x13, _)) and eapply fresh_ident_nIn in it; eauto 7 with fresh;
                    eapply it, incl_map; eauto;
                    apply st_follows_incl; repeat (try reflexivity; etransitivity; eauto with fresh)).
      + constructor.
        Transparent auto_scope.

    - (* automaton (strong) *)
      do 2 constructor; simpl. do 2 constructor.
      + repeat constructor. simpl_Forall.
        constructor; auto with datatypes.
        repeat constructor.
      + repeat constructor.
        eapply mmap2_values_valid_follows, Forall3_ignore13 in H8; eauto 7 with fresh.
        2,3:intros; destruct_conjs; destruct s0; destruct_conjs; simpl in *; repeat inv_bind.
        2:{ eapply mmap2_st_valid; eauto. simpl_Forall; eauto using auto_block_st_valid. }
        2:{ eapply mmap2_st_follows; eauto. simpl_Forall; eauto using auto_block_st_follows. }
        Opaque auto_scope.
        simpl_Forall. repeat inv_bind. destruct s0; destruct_conjs.
        repeat constructor. 2:{ intros * Hin; inv Hin. } rewrite app_nil_r.
        eapply auto_scope_NoDupScope; eauto.
        1:apply Forall_app; split.
        * simpl_Forall. destruct Hat; auto. right; eapply incl_map; eauto.
          apply st_follows_incl; repeat (etransitivity; eauto with fresh).
        * repeat apply Forall_cons; auto.
          all:right; eapply incl_map; eauto using fresh_ident_Inids.
          all:apply st_follows_incl; repeat (try reflexivity; etransitivity; eauto using fresh_ident_st_follows).
        * eapply NoDupScope_incl' in H3; eauto using auto_not_in_last_prefs.
          2:{ intros; simpl_Forall. eapply NoDupLocals_incl' in H14; eauto using auto_not_in_last_prefs. }
          intros * Hin. apply in_app_iff in Hin as [|]; auto.
          repeat (take (fresh_ident _ = _) and apply fresh_ident_prefixed in it as (?&?&?)); subst.
          repeat (take (In x17 _) and inv it; eauto).
        * intros; repeat inv_bind.
          eapply mmap2_values_valid_follows, Forall3_ignore13 in H18; eauto using auto_block_st_valid, auto_block_st_follows.
          repeat constructor. simpl_Forall. eapply H; eauto.
          simpl_Forall. destruct H15; auto. right. eapply incl_map; eauto using st_follows_incl.
      + rewrite fst_NoDupMembers; simpl.
        eapply fresh_idents_NoDup; eauto with fresh.
      + intros * Heq Hin. simpl_Forall.
        destruct Hat.
        * repeat (take (fresh_ident _ = _) and apply fresh_ident_prefixed in it as (?&?&?)); subst.
          destruct Heq as [|[|[|[|]]]]; subst; auto;
            eapply contradict_AtomOrGensym; eauto using auto_not_in_last_prefs.
        * destruct Heq as [|[|[|[|]]]]; auto; subst;
            repeat (take (fresh_ident _ = (x13, _)) and eapply fresh_ident_nIn in it; eauto 7 with fresh;
                    eapply it, incl_map; eauto;
                    apply st_follows_incl; repeat (try reflexivity; etransitivity; eauto with fresh)).
      + constructor.

    - (* local *)
      constructor; auto.
      eapply auto_scope_NoDupScope; eauto.
      intros.
      eapply mmap2_values_valid_follows, Forall3_ignore13 in H7; eauto using auto_block_st_valid, auto_block_st_follows.
      simpl_Forall. eapply H; eauto. simpl_Forall.
      destruct H4; eauto. right; eapply incl_map; eauto using st_follows_incl.
      Transparent auto_scope.
  Qed.

  (** GoodLocals *)

  Lemma auto_block_GoodLocals : forall blk blk' tys st st',
      GoodLocals last_prefs blk ->
      auto_block blk st = ((blk', tys), st') ->
      GoodLocals auto_prefs blk'.
  Proof.
    induction blk using block_ind2; intros * Hgood Haut; try destruct type0;
      inv Hgood; destruct_conjs; repeat inv_bind.
    - (* equation *)
      constructor.
    - (* reset *)
      constructor. auto_block_simpl_Forall.
    - (* switch *)
      constructor. auto_block_simpl_Forall.
      destruct s0; repeat inv_bind. inv H1. constructor; eauto using AtomOrGensym_add. auto_block_simpl_Forall.
    - (* automaton (weak) *)
      do 2 constructor; simpl.
      + repeat (take (fresh_ident _ = _) and apply fresh_ident_prefixed in it as (?&?&?)); subst.
        repeat apply Forall_cons; auto.
        all:right; do 2 esplit; eauto; now apply PSF.add_1.
      + repeat constructor.
        auto_block_simpl_Forall. destruct s0; destruct_conjs; repeat inv_bind. inv H1.
        repeat constructor; eauto using AtomOrGensym_add.
        auto_block_simpl_Forall.
    - (* automaton (strong) *)
      do 2 constructor; simpl. 2:do 2 constructor.
      + repeat (take (fresh_ident _ = _) and apply fresh_ident_prefixed in it as (?&?&?)); subst.
        repeat apply Forall_cons; auto.
        all:right; do 2 esplit; eauto; now apply PSF.add_1.
      + constructor. simpl_Forall. repeat constructor.
      + repeat constructor.
        auto_block_simpl_Forall. destruct s0; destruct_conjs; repeat inv_bind. inv H1.
        repeat constructor; eauto using AtomOrGensym_add.
        auto_block_simpl_Forall.
    - (* local *)
      inv H1. do 2 constructor; eauto using AtomOrGensym_add.
      auto_block_simpl_Forall.
  Qed.

  (** No more automaton *)

  Lemma auto_block_noauto : forall blk blk' tys st st',
      nolast_block blk ->
      auto_block blk st = ((blk', tys), st') ->
      noauto_block blk'.
  Proof.
    induction blk using block_ind2; intros * Hnl Haut; try destruct type0;
      inv Hnl; destruct_conjs; repeat inv_bind.
    - (* equation *)
      constructor.
    - (* reset *)
      constructor. auto_block_simpl_Forall.
    - (* switch *)
      constructor. auto_block_simpl_Forall.
      inv H1. repeat inv_bind. constructor; auto. auto_block_simpl_Forall.
    - (* automaton (weak) *)
      repeat constructor. auto_block_simpl_Forall.
      inv H1; destruct blks. repeat inv_bind. repeat constructor; auto.
      auto_block_simpl_Forall.
    - (* automaton (strong) *)
      repeat constructor.
      + simpl_Forall. repeat constructor.
      + auto_block_simpl_Forall.
        inv H1; destruct blks. repeat inv_bind. repeat constructor; auto.
        auto_block_simpl_Forall.
    - (* local *)
      inv H1. repeat constructor; auto. auto_block_simpl_Forall.
  Qed.

  Program Definition auto_node (n: @node nolast_block last_prefs) : @node noauto_block auto_prefs * list type :=
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
    pose proof (n_defd n) as (?&?&?).
    esplit; split; eauto using auto_block_VarsDefined.
  Qed.
  Next Obligation.
    destruct (auto_block _ _) as ((?&?)&?) eqn:Hauto; simpl.
    pose proof (n_nodup n) as (Hnd1&Hnd2).
    pose proof (n_good n) as (Hgood1&Hgood2&Hgood3).
    split; auto.
    eapply auto_block_NoDupLocals; eauto.
    - eapply init_st_valid; eauto using PS_For_all_empty, auto_not_in_last_prefs.
    - simpl_Forall; auto.
  Qed.
  Next Obligation.
    destruct (auto_block _ _) as ((?&?)&?) eqn:Hauto; simpl.
    pose proof (n_good n) as (Hgood1&Hgood2&Hgood3).
    repeat (split; eauto using AtomOrGensym_add, auto_block_GoodLocals).
  Qed.
  Next Obligation.
    destruct (auto_block _ _) as ((?&?)&?) eqn:Hauto; simpl.
    pose proof (n_syn n) as Hsyn.
    eapply auto_block_noauto; eauto.
  Qed.

  Definition auto_global (G : @global nolast_block last_prefs) : @global noauto_block auto_prefs :=
    let ndstys := map auto_node G.(nodes) in
    Global (G.(types)++flat_map snd ndstys) (map fst ndstys).

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
    intros (enms&nds). revert enms. unfold auto_global.
    induction nds; intros * Hfind; simpl in *. inv Hfind.
    apply find_node_cons in Hfind as [(?&?)|(Hneq&?)]; subst; simpl in *.
    - do 2 esplit. apply find_node_now; auto.
      apply auto_node_iface_eq.
    - edestruct IHnds as (?&?&?); eauto.
      do 2 esplit; eauto.
      rewrite find_node_other; eauto.
      erewrite find_node_change_types; eauto.
  Qed.

  Lemma auto_global_iface_incl : forall G,
      global_iface_incl G (auto_global G).
  Proof.
    split.
    - simpl. apply incl_appl, incl_refl.
    - intros. apply auto_global_find_node; auto.
  Qed.

  Lemma auto_global_find_node' : forall G f n,
      find_node f (auto_global G) = Some n ->
      exists n', find_node f G = Some n' /\ node_iface_eq n n'.
  Proof.
    intros (enms&nds). revert enms. unfold auto_global.
    induction nds; intros * Hfind; simpl in *. inv Hfind.
    apply find_node_cons in Hfind as [(?&?)|(Hneq&?)]; subst; simpl in *.
    - do 2 esplit. apply find_node_now; auto.
      apply node_iface_eq_sym, auto_node_iface_eq.
    - edestruct IHnds as (?&?&?); eauto.
      2:{ do 2 esplit; eauto.
          rewrite find_node_other; eauto. }
      erewrite find_node_change_types; eauto.
  Qed.

  (** Additional generate_constructors props *)

  Lemma generate_constructors_length : forall n xs st st',
      generate_constructors n st = (xs, st') ->
      length xs = n.
  Proof.
    induction n; intros * Hgen; repeat inv_bind; auto.
    simpl. f_equal; eauto.
  Qed.

  Lemma generate_constructors_In : forall n xs st st',
      generate_constructors n st = (xs, st') ->
      forall x, In x xs -> In x (st_ids st').
  Proof.
    unfold st_ids.
    induction n; intros * Hgen; repeat inv_bind; intros * []; subst; eauto.
    - eapply fresh_ident_In in H0. solve_In.
    - eapply IHn in H; eauto.
      solve_In. 2:eapply st_follows_incl; eauto with fresh. auto.
  Qed.

  Lemma generate_constructors_NoDup aft : forall n xs st st',
      st_valid_after st auto aft ->
      generate_constructors n st = (xs, st') ->
      NoDup xs.
  Proof.
    induction n; intros * Hvalid Hgen; repeat inv_bind;
      constructor; eauto with fresh.
    eapply fresh_ident_nIn in H0 as Hnin; eauto with fresh.
    contradict Hnin.
    eapply generate_constructors_In in H; eauto.
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
