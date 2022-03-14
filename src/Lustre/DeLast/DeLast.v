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

(** * Remove Local Blocks *)

Module Type DELAST
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Import Cks : CLOCKS Ids Op OpAux)
       (Import Senv : STATICENV Ids Op OpAux Cks)
       (Import Syn : LSYNTAX Ids Op OpAux Cks Senv).

  (** ** Rename some variables *)
  Section rename.
    Variable (sub : Env.t ident).

    Definition rename_in_var (x : ident) :=
      or_default x (Env.find x sub).

    Fixpoint rename_in_exp (e : exp) :=
      match e with
      | Econst _ | Eenum _ _ | Evar _ _ => e
      | Elast x ann => Evar (rename_in_var x) ann
      | Eunop op e1 ann => Eunop op (rename_in_exp e1) ann
      | Ebinop op e1 e2 ann => Ebinop op (rename_in_exp e1) (rename_in_exp e2) ann
      | Efby e0s e1s anns => Efby (map rename_in_exp e0s) (map rename_in_exp e1s) anns
      | Earrow e0s e1s anns => Earrow (map rename_in_exp e0s) (map rename_in_exp e1s) anns
      | Ewhen es x t ann => Ewhen (map rename_in_exp es) x t ann
      | Emerge (x, ty) es ann => Emerge (x, ty) (map (fun '(i, es) => (i, map rename_in_exp es)) es) ann
      | Ecase e es d ann =>
        Ecase (rename_in_exp e) (map (fun '(i, es) => (i, map rename_in_exp es)) es) (option_map (map rename_in_exp) d) ann
      | Eapp f es er ann => Eapp f (map rename_in_exp es) (map rename_in_exp er) ann
      end.

    Definition rename_in_equation '(xs, es) : equation :=
      (xs, map rename_in_exp es).

  End rename.

  (** ** More properties *)

  Section rename_empty.

    Fact rename_in_var_empty : forall x,
      rename_in_var (Env.empty _) x = x.
    Proof.
      intros. unfold rename_in_var.
      simpl. rewrite Env.gempty. reflexivity.
    Qed.

    Corollary rename_in_vars_empty : forall xs,
        map (rename_in_var (Env.empty _)) xs = xs.
    Proof.
      induction xs; simpl; f_equal; auto using rename_in_var_empty.
    Qed.

  End rename_empty.

  Fact not_in_union_rename1 : forall x sub sub',
      ~Env.In x sub ->
      rename_in_var (Env.union sub sub') x = rename_in_var sub' x.
  Proof.
    unfold rename_in_var.
    intros * Hnin.
    eapply Env.Props.P.F.not_find_in_iff in Hnin.
    destruct (Env.find x (Env.union sub sub')) eqn:Hfind.
    - eapply Env.union_find4 in Hfind as [Hfind|Hfind]; congruence.
    - eapply Env.union_find_None in Hfind as (Hfind1&Hfind2).
      now rewrite Hfind2.
  Qed.

  Fact not_in_union_rename2 : forall x sub sub',
      ~Env.In x sub' ->
      rename_in_var (Env.union sub sub') x = rename_in_var sub x.
  Proof.
    unfold rename_in_var.
    intros * Hnin.
    destruct (Env.find x (Env.union sub sub')) eqn:Hfind.
    - eapply Env.union_find4 in Hfind as [Hfind|Hfind].
      + now rewrite Hfind.
      + exfalso.
        eapply Env.Props.P.F.not_find_in_iff in Hnin. congruence.
    - eapply Env.union_find_None in Hfind as (Hfind1&Hfind2).
      now rewrite Hfind1.
  Qed.

  Lemma disjoint_union_rename_in_var : forall (sub1 sub2: Env.t ident) x,
      (forall x, Env.In x sub1 -> ~Env.In x sub2) ->
      (forall x y, Env.MapsTo x y sub1 -> ~Env.In y sub2) ->
      rename_in_var sub2 (rename_in_var sub1 x) = rename_in_var (Env.union sub1 sub2) x.
  Proof.
    unfold rename_in_var.
    intros * Hnin1 Hnin2.
    destruct (Env.find x (Env.union _ _)) eqn:Hfind; simpl.
    - destruct (Env.find x sub1) eqn:Hfind1; simpl.
      + specialize (Hnin2 _ _ Hfind1). eapply Env.Props.P.F.not_find_in_iff in Hnin2.
        rewrite Hnin2; simpl.
        erewrite Env.union_find2 in Hfind; eauto. now inv Hfind.
        eapply Env.Props.P.F.not_find_in_iff, Hnin1. econstructor; eauto.
      + eapply Env.union_find4 in Hfind as [Hfind|Hfind]; try congruence.
        rewrite Hfind; auto.
    - eapply Env.union_find_None in Hfind as (Hfind1&Hfind2).
      rewrite Hfind1; simpl. now rewrite Hfind2.
  Qed.

  (** ** Inlining of local blocks *)

  Module Fresh := Fresh.Fresh(Ids).
  Import Fresh Notations Facts Tactics.
  Local Open Scope fresh_monad_scope.

  Definition FreshAnn A := Fresh A (type * clock).

  Definition fresh_idents (lasts : list (ident * (type * clock * exp))) :=
    mmap (fun '(x, (ty, ck, e)) => do lx <- fresh_ident last (Some x) (ty, ck);
                                ret (x, lx, (ty, ck, e))) lasts.

  Fixpoint delast_block sub (blk : block) : FreshAnn block :=
    match blk with
    | Beq eq => ret (Beq (rename_in_equation sub eq))
    | Breset blks er =>
        do blks' <- mmap (delast_block sub) blks;
        ret (Breset blks' (rename_in_exp sub er))
    | Bswitch ec branches =>
        do branches' <- mmap (fun '(k, blks) => do blks' <- mmap (delast_block sub) blks;
                                            ret (k, blks')) branches;
        ret (Bswitch (rename_in_exp sub ec) branches')
    | Bauto ck (ini, oth) states =>
        do states' <- mmap (fun '(k, (blks, trans)) =>
                             do blks' <- mmap (delast_block sub) blks;
                             ret (k, (blks', map (fun '(e, k) => (rename_in_exp sub e, k)) trans))) states;
        ret (Bauto ck (map (fun '(e, k) => (rename_in_exp sub e, k)) ini, oth) states')
    | Blocal locs blks =>
        let lasts := map_filter (fun '(x, (ty, ck, _, o)) => option_map (fun '(e, _) => (x, (ty, ck, e))) o) locs in
        do lasts' <- fresh_idents lasts;
        let sub1 := Env.from_list (map fst lasts') in
        let sub' := Env.union sub sub1 in
        do blks' <- mmap (delast_block sub') blks;
        let fbyeqs :=
          map (fun '(x, lx, (ty, ck, e)) =>
                 Beq ([lx], [Efby [rename_in_exp sub' e]
                                  [Evar x (ty, ck)] [(ty, ck)]])) lasts' in
        ret (Blocal (map (fun '(x, (ty, ck, cx, _)) => (x, (ty, ck, cx, None))) locs
                     ++ map (fun '(_, lx, (ty, ck, _)) => (lx, (ty, ck, xH, None))) lasts')
                    (fbyeqs++blks'))
    end.

  (** ** Some properties *)

  Lemma fresh_idents_In : forall lasts lasts' st st',
      fresh_idents lasts st = (lasts', st') ->
      forall x ty ck e, In (x, (ty, ck, e)) lasts ->
                   exists lx, In (x, lx, (ty, ck, e)) lasts'.
  Proof.
    intros * Hfresh * Hin.
    apply mmap_values, Forall2_ignore2 in Hfresh. simpl_Forall.
    repeat inv_bind. eauto.
  Qed.

  Lemma fresh_idents_In' : forall lasts lasts' st st',
      fresh_idents lasts st = (lasts', st') ->
      forall x lx ty ck e, In (x, lx, (ty, ck, e)) lasts' ->
                      In (x, (ty, ck, e)) lasts.
  Proof.
    intros * Hfresh * Hin.
    apply mmap_values, Forall2_ignore1 in Hfresh. simpl_Forall.
    repeat inv_bind. eauto.
  Qed.

  Lemma fresh_idents_InMembers : forall lasts lasts' st st',
      fresh_idents lasts st = (lasts', st') ->
      forall x, InMembers x lasts <-> InMembers x (map fst lasts').
  Proof.
    intros * Hfresh ?. apply mmap_values in Hfresh.
    rewrite 2 fst_InMembers.
    split; intros Hin; simpl_In.
    - apply Forall2_ignore2 in Hfresh; simpl_Forall.
      repeat inv_bind. solve_In.
    - apply Forall2_ignore1 in Hfresh; simpl_Forall.
      repeat inv_bind. solve_In.
  Qed.

  Lemma fresh_idents_NoDupMembers : forall lasts lasts' st st',
      NoDupMembers lasts ->
      fresh_idents lasts st = (lasts', st') ->
      NoDupMembers (map fst lasts').
  Proof.
    induction lasts; intros * Hnd Hfresh; inv Hnd; destruct_conjs;
      repeat inv_bind; simpl; constructor; eauto.
    erewrite <-fresh_idents_InMembers; eauto.
  Qed.

  Lemma fresh_idents_In_rename : forall lasts lasts' st st',
      NoDupMembers lasts ->
      fresh_idents lasts st = (lasts', st') ->
      forall x ty ck e, In (x, (ty, ck, e)) lasts ->
                   In (x, (rename_in_var (Env.from_list (map fst lasts')) x), (ty, ck, e)) lasts'.
  Proof.
    intros * Hnd Hfresh * Hin.
    assert (Hf:=Hfresh). apply mmap_values, Forall2_ignore2 in Hf. simpl_Forall.
    repeat inv_bind. unfold rename_in_var. erewrite Env.find_In_from_list.
    2:solve_In. simpl; auto. eapply fresh_idents_NoDupMembers; eauto.
  Qed.

  Lemma fresh_idents_In'_rename : forall lasts lasts' st st',
      NoDupMembers lasts ->
      fresh_idents lasts st = (lasts', st') ->
      forall x lx ty ck e, In (x, lx, (ty, ck, e)) lasts' ->
                      In (x, (ty, ck, e)) lasts /\ lx = rename_in_var (Env.from_list (map fst lasts')) x.
  Proof.
    intros * Hnd Hfresh * Hin.
    assert (Hf:=Hfresh). apply mmap_values, Forall2_ignore1 in Hf. simpl_Forall.
    repeat inv_bind. split; eauto.
    unfold rename_in_var. erewrite Env.find_In_from_list. 2:solve_In. auto.
    eapply fresh_idents_NoDupMembers; eauto.
  Qed.

  Lemma fresh_idents_sub : forall lasts lasts' st st',
      NoDupMembers lasts ->
      fresh_idents lasts st = (lasts', st') ->
      forall x lx, In (x, lx) (map fst lasts') ->
              Env.find x (Env.from_list (map fst lasts')) = Some lx.
  Proof.
    intros * Hnd Hfresh * Hin.
    apply Env.find_In_from_list; auto.
    eapply fresh_idents_NoDupMembers in Hfresh; eauto.
  Qed.

  (** ** State properties *)

  Definition st_valid_after {B} st aft := @st_valid_after B st last aft.

  Lemma fresh_idents_st_valid_after : forall lasts lasts' st st' aft,
      fresh_idents lasts st = (lasts', st') ->
      st_valid_after st aft ->
      st_valid_after st' aft.
  Proof.
    intros * Hfresh Hvalid.
    eapply mmap_st_valid in Hfresh; eauto.
    simpl_Forall. repeat inv_bind. eapply fresh_ident_st_valid in H0; eauto.
  Qed.

  Lemma delast_block_st_valid_after : forall blk sub blks' st st' aft,
      delast_block sub blk st = (blks', st') ->
      st_valid_after st aft ->
      st_valid_after st' aft.
  Proof.
    induction blk using block_ind2; intros * Hdl Hvalid; repeat inv_bind; auto.
    - (* reset *)
      eapply mmap_st_valid; eauto.
      simpl_Forall. eapply H; eauto.
    - (* switch *)
      eapply mmap_st_valid; eauto. simpl_Forall; repeat inv_bind.
      eapply mmap_st_valid; eauto. simpl_Forall.
      eapply H; eauto.
    - (* automaton *)
      destruct ini; repeat inv_bind.
      eapply mmap_st_valid; eauto. simpl_Forall; repeat inv_bind.
      eapply mmap_st_valid; eauto. simpl_Forall.
      eapply H; eauto.
    - (* local *)
      eapply fresh_idents_st_valid_after in H0; eauto.
      eapply mmap_st_valid; eauto.
      simpl_Forall. eapply H; eauto.
  Qed.

  Lemma fresh_idents_st_follows : forall lasts lasts' st st',
      fresh_idents lasts st = (lasts', st') ->
      st_follows st st'.
  Proof.
    intros * Hfresh.
    eapply mmap_st_follows in Hfresh; eauto.
    simpl_Forall. repeat inv_bind; eauto with fresh.
  Qed.

  Lemma delast_block_st_follows : forall blk sub blks' st st',
      delast_block sub blk st = (blks', st') ->
      st_follows st st'.
  Proof.
    induction blk using block_ind2; intros * Hdl; repeat inv_bind; try reflexivity.
    - (* reset *)
      eapply mmap_st_follows; eauto.
      simpl_Forall; eauto.
    - (* switch *)
      eapply mmap_st_follows; eauto. simpl_Forall; repeat inv_bind.
      eapply mmap_st_follows; eauto. simpl_Forall; eauto.
    - (* automaton *)
      destruct ini; repeat inv_bind.
      eapply mmap_st_follows; eauto. simpl_Forall; repeat inv_bind.
      eapply mmap_st_follows; eauto. simpl_Forall.
      eapply H; eauto.
    - (* local *)
      etransitivity; [eapply fresh_idents_st_follows; eauto|].
      eapply mmap_st_follows; eauto. simpl_Forall; eauto.
  Qed.

  Global Hint Resolve delast_block_st_follows : fresh.

  (** ** Wellformedness properties *)

  (** *** VarsDefined *)

  Import Permutation.

  Fact mmap_vars_perm : forall (f : (Env.t ident) -> block -> FreshAnn block) blks sub blks' xs st st',
      Forall
        (fun blk => forall sub blk' xs st st',
             VarsDefined blk xs ->
             f sub blk st = (blk', st') ->
             VarsDefined blk' xs) blks ->
      Forall2 VarsDefined blks xs ->
      mmap (f sub) blks st = (blks', st') ->
      Forall2 VarsDefined blks' xs.
  Proof.
    induction blks; intros * Hf (* Hns *) Hvars (* Hnd *) Hnorm;
      inv Hf; inv Hvars; repeat inv_bind; simpl; constructor; eauto.
  Qed.

  Lemma delast_block_vars_perm : forall blk sub blk' xs st st',
      VarsDefined blk xs ->
      (* NoDupLocals (map fst (Env.elements sub) ++ xs) blk -> *)
      delast_block sub blk st = (blk', st') ->
      VarsDefined blk' xs.
  Proof.
    induction blk using block_ind2; intros * Hvars (* Hnd  *)Hdl;
      inv Hvars; (* inv Hnd;  *)repeat inv_bind.
    - (* equation *)
      destruct eq. simpl. constructor.
    - (* reset *)
      constructor.
      eapply mmap_vars_perm in H0; eauto.
    - (* switch *)
      constructor.
      + apply mmap_values in H0. inv H0; congruence.
      + eapply mmap_values, Forall2_ignore1 in H0. simpl_Forall.
        repeat inv_bind.
        eapply mmap_vars_perm in H3; eauto.
    - (* automaton *)
      destruct ini; repeat inv_bind.
      constructor.
      + apply mmap_values in H0. inv H0; congruence.
      + eapply mmap_values, Forall2_ignore1 in H0. simpl_Forall.
        repeat inv_bind.
        eapply mmap_vars_perm in H3; eauto.
    - (* local *)
      eapply mmap_vars_perm in H; eauto. clear H1.
      econstructor.
      + apply Forall2_app; eauto.
        instantiate (1:=map (fun '(_, x, _) => [x]) x).
        simpl_Forall. constructor.
      + rewrite concat_app. simpl_app. rewrite (Permutation_app_comm _ xs), app_assoc, Permutation_app_comm.
        apply Permutation_app.
        * erewrite map_map, map_ext. symmetry. erewrite <-map_ext, <-map_map, concat_map_singl1. reflexivity.
          instantiate (1:=fun '(_, x, _) => x). 1,2:intros; destruct_conjs; auto.
        * erewrite map_map, map_ext; eauto. intros; destruct_conjs; auto.
  Qed.

  (** *** GoodLocals *)

  Fact fresh_idents_prefixed : forall lasts lasts' st st',
      fresh_idents lasts st = (lasts', st') ->
      Forall (fun '(_, lx, _) => exists n hint, lx = gensym last hint n) lasts'.
  Proof.
    intros * Hfresh.
    eapply mmap_values, Forall2_ignore1 in Hfresh. simpl_Forall. repeat inv_bind.
    eapply fresh_ident_prefixed in H1; auto.
  Qed.

  Lemma delast_block_GoodLocals : forall blk sub blk' st st',
      GoodLocals elab_prefs blk ->
      delast_block sub blk st = (blk', st') ->
      GoodLocals last_prefs blk'.
  Proof.
    induction blk using block_ind2; intros * Hg Hdl; inv Hg; repeat inv_bind.
    - (* equation *)
      repeat constructor.
    - (* reset *)
      repeat constructor.
      eapply mmap_values, Forall2_ignore1 in H0.
      simpl_Forall; eauto.
    - (* switch *)
      repeat constructor.
      eapply mmap_values, Forall2_ignore1 in H0. simpl_Forall. repeat inv_bind.
      eapply mmap_values, Forall2_ignore1 in H3.
      simpl_Forall; eauto.
    - (* automaton *)
      destruct ini; repeat inv_bind.
      repeat constructor.
      eapply mmap_values, Forall2_ignore1 in H0. simpl_Forall. repeat inv_bind.
      eapply mmap_values, Forall2_ignore1 in H3.
      simpl_Forall; eauto.
    - (* local *)
      constructor.
      + rewrite map_app. apply Forall_app; split.
        * erewrite map_map, map_ext; eauto using AtomOrGensym_add.
          intros; destruct_conjs; auto.
        * apply fresh_idents_prefixed in H0.
          simpl_Forall; subst.
          right. repeat esplit; eauto. apply PSF.add_iff; auto.
      + apply Forall_app; split.
        * simpl_Forall. constructor.
        * eapply mmap_values, Forall2_ignore1 in H1.
          simpl_Forall; eauto.
  Qed.

  (** *** NoDupLocals *)

  Lemma last_not_in_elab_prefs :
    ~PS.In last elab_prefs.
  Proof.
    unfold elab_prefs.
    rewrite PSF.singleton_iff.
    pose proof gensym_prefs_NoDup as Hnd. unfold gensym_prefs in Hnd.
    repeat rewrite NoDup_cons_iff in Hnd. destruct_conjs.
    intros contra; subst; rewrite contra in *; eauto with datatypes.
  Qed.

  Fact fresh_idents_In_ids : forall lasts lasts' st st',
      fresh_idents lasts st = (lasts', st') ->
      Forall (fun '(_, lx, _) => In lx (st_ids st')) lasts'.
  Proof.
    unfold fresh_idents.
    induction lasts; intros; destruct_conjs; repeat inv_bind; constructor; eauto.
    apply fresh_ident_Inids in H. eapply incl_map; [|eauto].
    eapply st_follows_incl, mmap_st_follows; eauto.
    simpl_Forall. repeat inv_bind; eauto with fresh.
  Qed.

  Fact fresh_idents_nIn_ids aft : forall lasts lasts' st st',
      st_valid_after st aft ->
      fresh_idents lasts st = (lasts', st') ->
      Forall (fun '(_, lx, _) => ~In lx (st_ids st)) lasts'.
  Proof.
    unfold fresh_idents.
    induction lasts; intros; destruct_conjs; repeat inv_bind; constructor; eauto.
    - eapply fresh_ident_nIn in H; eauto.
    - eapply IHlasts in H1. 2:eapply fresh_ident_st_valid in H0; eauto.
      simpl_Forall. contradict H1.
      eapply incl_map; eauto.
      apply st_follows_incl; eauto with fresh.
  Qed.

  Fact fresh_idents_NoDup aft : forall lasts lasts' st st',
      st_valid_after st aft ->
      fresh_idents lasts st = (lasts', st') ->
      NoDupMembers (map (fun '(_, lx, (ty, ck, _)) => (lx, (ty, ck, xH, @None (exp * ident)))) lasts').
  Proof.
    unfold fresh_idents.
    induction lasts; intros * Hvalid Hfresh;
      destruct_conjs; repeat inv_bind; constructor; eauto.
    - intros Hinm. rewrite fst_InMembers in Hinm; simpl_In.
      eapply fresh_idents_nIn_ids in H0. 2:eapply fresh_ident_st_valid in H; eauto.
      simpl_Forall.
      eapply H0, fresh_ident_Inids; eauto.
    - eapply IHlasts in H0; eauto.
      eapply fresh_ident_st_valid in H; eauto.
  Qed.

  Fact mmap_delast_NoDupLocals sub aft : forall blks blks' xs st st',
      Forall
        (fun blk => forall xs sub blk' st st',
             st_valid_after st aft ->
             Forall (fun x : ident => AtomOrGensym elab_prefs x \/ In x (st_ids st)) xs ->
             GoodLocals elab_prefs blk ->
             NoDupLocals xs blk ->
             delast_block sub blk st = (blk', st') ->
             NoDupLocals xs blk') blks ->
      st_valid_after st aft ->
      Forall (fun x : ident => AtomOrGensym elab_prefs x \/ In x (st_ids st)) xs ->
      Forall (GoodLocals elab_prefs) blks ->
      Forall (NoDupLocals xs) blks ->
      mmap (delast_block sub) blks st = (blks', st') ->
      Forall (NoDupLocals xs) blks'.
  Proof.
    induction blks; intros * Hf Hvalid Hat Hgood Hnd Hdl;
      inv Hf; inv Hgood; inv Hnd; repeat inv_bind; constructor; eauto.
    eapply IHblks in H0; eauto using delast_block_st_valid_after.
    simpl_Forall. destruct Hat; auto.
    right. eapply incl_map; eauto. apply st_follows_incl; eauto with fresh.
  Qed.

  Lemma delast_block_NoDupLocals aft : forall blk xs sub blk' st st',
      st_valid_after st aft ->
      Forall (fun x => AtomOrGensym elab_prefs x \/ In x (st_ids st)) xs ->
      GoodLocals elab_prefs blk ->
      NoDupLocals xs blk ->
      delast_block sub blk st = (blk', st') ->
      NoDupLocals xs blk'.
  Proof.
    induction blk using block_ind2; intros * Hvalid Hat Hgood Hnd Hdl;
      inv Hgood; inv Hnd; repeat inv_bind.
    - (* equation *)
      constructor.
    - (* reset *)
      constructor.
      eapply mmap_delast_NoDupLocals; eauto.
    - (* switch *)
      constructor. revert x st st' Hvalid H0 Hat.
      induction branches as [|(?&?)]; intros; inv H; inv H1; inv H3; repeat inv_bind; auto.
      constructor.
      + eapply mmap_delast_NoDupLocals in H; eauto.
      + eapply IHbranches in H0; eauto.
        1:{ eapply mmap_st_valid in H; eauto.
            simpl_Forall. eapply delast_block_st_valid_after in H3; eauto. }
        simpl_Forall. destruct Hat; auto.
        right. eapply incl_map; eauto. apply st_follows_incl; eauto.
        eapply mmap_st_follows; eauto. simpl_Forall; eauto with fresh.
    - (* automaton *)
      destruct ini; repeat inv_bind.
      constructor. revert x st st' Hvalid H0 Hat.
      induction states as [|(?&?&?)]; intros; inv H; inv H1; inv H3; repeat inv_bind; auto.
      constructor.
      + eapply mmap_delast_NoDupLocals in H; eauto.
      + eapply IHstates in H0; eauto.
        1:{ eapply mmap_st_valid in H; eauto.
            simpl_Forall. eapply delast_block_st_valid_after in H3; eauto. }
        simpl_Forall. destruct Hat; auto.
        right. eapply incl_map; eauto. apply st_follows_incl; eauto.
        eapply mmap_st_follows; eauto. simpl_Forall; eauto with fresh.
    - (* local *)
      assert (Forall (fun '(_, lx, _) => exists n hint, lx = gensym last hint n) x) as Hgen.
      { eapply mmap_values, Forall2_ignore1 in H0. simpl_Forall. repeat inv_bind.
        eapply fresh_ident_prefixed in H8; auto. }
      constructor.
      + apply Forall_app; split. 1:simpl_Forall; constructor.
        eapply mmap_delast_NoDupLocals in H1; eauto using fresh_idents_st_valid_after.
        * simpl_app. repeat rewrite in_app_iff. repeat rewrite Forall_app. repeat split.
          -- simpl_Forall. destruct Hat; eauto. right.
             eapply incl_map; eauto using st_follows_incl, fresh_idents_st_follows.
          -- simpl_Forall; eauto.
          -- eapply fresh_idents_In_ids in H0. simpl_Forall; auto.
        * simpl_Forall.
          eapply NoDupLocals_incl' in H4; eauto using last_not_in_elab_prefs.
          intros * Hin. simpl_app. repeat rewrite in_app_iff in *.
          erewrite 2 map_map, map_ext in Hin. destruct Hin as [|[|]]; eauto. 2:intros; destruct_conjs; auto.
          simpl_In.
          eapply Forall_forall in Hgen; eauto. simpl in *; auto.
      + apply NoDupMembers_app.
        * apply nodupmembers_map; auto. intros; destruct_conjs; auto.
        * eapply fresh_idents_NoDup; eauto.
        * intros * Hinm1 Hinm2. rewrite fst_InMembers in Hinm1, Hinm2. simpl_In.
          simpl_Forall; subst. eapply contradict_AtomOrGensym; eauto using last_not_in_elab_prefs.
      + intros * Hinm1 Hin2. apply InMembers_app in Hinm1 as [Hinm1|Hinm1].
        * eapply H7; eauto. rewrite fst_InMembers in *. solve_In.
        * rewrite fst_InMembers in Hinm1. simpl_In.
          simpl_Forall; subst. destruct Hat.
          -- eapply contradict_AtomOrGensym in H5; eauto using last_not_in_elab_prefs.
          -- eapply fresh_idents_nIn_ids in H0; [|eauto].
             simpl_Forall; eauto.
  Qed.

  (** *** No last remaining *)

  Lemma delast_block_nolast : forall blk sub blk' st st',
      delast_block sub blk st = (blk', st') ->
      nolast_block blk'.
  Proof.
    induction blk using block_ind2; intros * Hdl; repeat inv_bind.
    - (* equation *)
      constructor.
    - (* reset *)
      constructor.
      eapply mmap_values, Forall2_ignore1 in H0.
      simpl_Forall; eauto.
    - (* switch *)
      constructor.
      eapply mmap_values, Forall2_ignore1 in H0. simpl_Forall. repeat inv_bind.
      eapply mmap_values, Forall2_ignore1 in H2.
      simpl_Forall; eauto.
    - (* automaton *)
      destruct ini; repeat inv_bind.
      constructor.
      eapply mmap_values, Forall2_ignore1 in H0. simpl_Forall. repeat inv_bind.
      eapply mmap_values, Forall2_ignore1 in H2.
      simpl_Forall; eauto.
    - (* local *)
      constructor.
      + apply Forall_app; split; simpl_Forall; auto.
      + apply Forall_app; split.
        * simpl_Forall. constructor.
        * eapply mmap_values, Forall2_ignore1 in H1.
          simpl_Forall; eauto.
  Qed.

  (** ** Transformation of node and program *)

  Program Definition delast_node (n: @node (fun _ => True) elab_prefs) : @node nolast_block last_prefs :=
    let res := delast_block (@Env.empty _) (n_block n) init_st in
    {|
      n_name := (n_name n);
      n_hasstate := (n_hasstate n);
      n_in := (n_in n);
      n_out := (n_out n);
      n_block := fst res;
      n_ingt0 := (n_ingt0 n);
      n_outgt0 := (n_outgt0 n);
    |}.
  Next Obligation.
    pose proof (n_defd n) as (?&Hvars&Hperm).
    pose proof (n_nodup n) as (_&Hndup).
    pose proof (n_syn n) as Hns.
    repeat esplit; eauto.
    destruct (delast_block _ _) as (?&?) eqn:Hdl.
    eapply delast_block_vars_perm in Hvars; eauto.
  Qed.
  Next Obligation.
    pose proof (n_good n) as (Hgood1&Hgood2&_).
    pose proof (n_nodup n) as (Hnd1&Hnd2).
    pose proof (n_syn n) as Hsyn.
    repeat split; auto.
    destruct (delast_block _ _) as (?&st') eqn:Hdl.
    eapply delast_block_NoDupLocals; eauto.
    - eapply init_st_valid; eauto using last_not_in_elab_prefs, PS_For_all_empty.
    - simpl_Forall; auto.
  Qed.
  Next Obligation.
    pose proof (n_good n) as (Hgood1&Hgood2&Hatom).
    pose proof (n_nodup n) as (Hnd1&Hnd2).
    destruct (delast_block _ _) as (?&?) eqn:Hdl. simpl.
    repeat split; eauto using AtomOrGensym_add.
    eapply delast_block_GoodLocals; eauto.
  Qed.
  Next Obligation.
    destruct (delast_block _ _) as (?&?) eqn:Hdl.
    eapply delast_block_nolast; eauto.
  Qed.

  Global Program Instance delast_node_transform_unit: TransformUnit (@node (fun _ => True) elab_prefs) node :=
    { transform_unit := delast_node }.

  Global Program Instance delast_global_without_units : TransformProgramWithoutUnits (@global (fun _ => True) elab_prefs) (@global nolast_block last_prefs) :=
    { transform_program_without_units := fun g => Global g.(enums) [] }.

  Definition delast_global : @global (fun _ => True) elab_prefs -> @global nolast_block last_prefs :=
    transform_units.

  (** *** Equality of interfaces *)

  Lemma delast_global_iface_eq : forall G,
      global_iface_eq G (delast_global G).
  Proof.
    split; auto.
    intros f. unfold find_node.
    destruct (find_unit f G) as [(?&?)|] eqn:Hfind; simpl.
    - setoid_rewrite find_unit_transform_units_forward; eauto.
      simpl. repeat constructor.
    - destruct (find_unit f (delast_global G)) as [(?&?)|] eqn:Hfind'; simpl; try constructor.
      eapply find_unit_transform_units_backward in Hfind' as (?&?&?&?); congruence.
  Qed.

End DELAST.

Module DeLastFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks : CLOCKS Ids Op OpAux)
       (Senv : STATICENV Ids Op OpAux Cks)
       (Syn : LSYNTAX Ids Op OpAux Cks Senv)
       <: DELAST Ids Op OpAux Cks Senv Syn.
  Include DELAST Ids Op OpAux Cks Senv Syn.
End DeLastFun.
