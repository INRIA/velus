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
      | Eextcall f es ann => Eextcall f (map rename_in_exp es) ann
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

  Definition FreshAnn A := Fresh last A (type * clock).

  Definition fresh_idents (lasts : list (ident * (type * clock * exp))) : FreshAnn _ :=
    mmap (fun '(x, (ty, ck, e)) => do lx <- fresh_ident (Some x) (ty, ck);
                                ret (x, lx, (ty, ck, e))) lasts.

  Section delast_scope.
    Context {A : Type}.
    Variable f_delast : Env.t ident -> A -> FreshAnn A.
    Variable f_add_eqs : list block -> A -> A.

    Definition delast_scope sub (s : scope A) : FreshAnn (scope A) :=
      let 'Scope locs blks := s in
      let lasts := map_filter (fun '(x, (ty, ck, _, o)) => option_map (fun '(e, _) => (x, (ty, ck, e))) o) locs in
      do lasts' <- fresh_idents lasts;
      let sub1 := Env.from_list (map fst lasts') in
      let sub' := Env.union sub sub1 in
      do blks' <- f_delast sub' blks;
      let fbyeqs :=
        map (fun '(x, lx, (ty, ck, e)) =>
               ([lx], [Efby [rename_in_exp sub' e]
                            [Evar x (ty, ck)] [(ty, ck)]])) lasts' in
      ret (Scope (map (fun '(x, (ty, ck, cx, _)) => (x, (ty, ck, cx, None))) locs
                      ++ map (fun '(_, lx, (ty, ck, _)) => (lx, (ty, ck, xH, None))) lasts')
                  (f_add_eqs (map Beq fbyeqs) blks')).
  End delast_scope.

  Fixpoint delast_block sub (blk : block) : FreshAnn block :=
    match blk with
    | Beq eq => ret (Beq (rename_in_equation sub eq))
    | Breset blks er =>
        do blks' <- mmap (delast_block sub) blks;
        ret (Breset blks' (rename_in_exp sub er))
    | Bswitch ec branches =>
        do branches' <- mmap (fun '(k, Branch _ blks) =>
                               do blks' <- mmap (delast_block sub) blks;
                               ret (k, Branch [] blks')) branches;
        ret (Bswitch (rename_in_exp sub ec) branches')
    | Bauto type ck (ini, oth) states =>
        do states' <- mmap (fun '(k, Branch _ (unl, scope)) =>
                             let unl' := map (fun '(e, k) => (rename_in_exp sub e, k)) unl in
                             do scope' <- delast_scope (fun sub '(blks, trans) =>
                                                        do blks' <- mmap (delast_block sub) blks;
                                                        ret (blks', map (fun '(e, k) => (rename_in_exp sub e, k)) trans))
                                                     (fun eqs '(blks, trans) => (eqs++blks, trans))
                                                     sub scope;
                             ret (k, Branch [] (unl', scope'))) states;
        ret (Bauto type ck (map (fun '(e, k) => (rename_in_exp sub e, k)) ini, oth) states')
    | Blocal scope =>
        do scope' <- delast_scope (fun sub => mmap (delast_block sub))
                                 (fun eqs blks => eqs++blks) sub scope;
        ret (Blocal scope')
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

  Lemma fresh_idents_st_follows : forall lasts lasts' st st',
      fresh_idents lasts st = (lasts', st') ->
      st_follows st st'.
  Proof.
    intros * Hfresh.
    eapply mmap_st_follows in Hfresh; eauto.
    simpl_Forall. repeat inv_bind; eauto with fresh.
  Qed.

  Fact delast_scope_st_follows {A} f_dl f_add : forall sub locs (blks : A) s' st st',
      delast_scope f_dl f_add sub (Scope locs blks) st = (s', st') ->
      (forall sub blks' st st',
          f_dl sub blks st = (blks', st') ->
          st_follows st st') ->
      st_follows st st'.
  Proof.
    intros * Hdl Hind; repeat inv_bind.
    etransitivity; eauto using fresh_idents_st_follows.
  Qed.

  Lemma delast_block_st_follows : forall blk sub blks' st st',
      delast_block sub blk st = (blks', st') ->
      st_follows st st'.
  Proof.
    Opaque delast_scope.
    induction blk using block_ind2; intros * Hdl; repeat inv_bind; try reflexivity.
    - (* reset *)
      eapply mmap_st_follows; eauto.
      simpl_Forall; eauto.
    - (* switch *)
      eapply mmap_st_follows; eauto. simpl_Forall; repeat inv_bind.
      destruct b0. repeat inv_bind.
      eapply mmap_st_follows; eauto. simpl_Forall; eauto.
    - (* automaton *)
      destruct ini; repeat inv_bind.
      eapply mmap_st_follows; eauto. simpl_Forall; repeat inv_bind.
      destruct b0 as [?(?&[?(?&?)])]; destruct_conjs. repeat inv_bind. eapply delast_scope_st_follows; eauto.
      intros; repeat inv_bind.
      eapply mmap_st_follows; eauto. simpl_Forall; eauto.
    - (* local *)
      eapply delast_scope_st_follows; eauto.
      intros; simpl in *.
      eapply mmap_st_follows; eauto. simpl_Forall; eauto.
      Transparent delast_scope.
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

  Lemma delast_scope_vars_perm {A} P_vd f_dl f_add : forall locs (blks: A) sub s' xs st st',
      VarsDefinedScope P_vd (Scope locs blks) xs ->
      delast_scope f_dl f_add sub (Scope locs blks) st = (s', st') ->
      (forall xs sub blks' st st',
          P_vd blks xs ->
          f_dl sub blks st = (blks', st') ->
          P_vd blks' xs) ->
      (forall xs1 xs2 blks1 blks2,
          Forall2 VarsDefined blks1 xs2 ->
          P_vd blks2 xs1 ->
          P_vd (f_add blks1 blks2) (xs1 ++ concat xs2)) ->
      VarsDefinedScope P_vd s' xs.
  Proof.
    intros * Hvd Hdl Hind Hadd; inv Hvd. repeat inv_bind.
    eapply Hind in H0; eauto.
    econstructor; eauto using incl_nil'. rewrite map_app, app_assoc, map_map.
    rewrite <-concat_map_singl1 with (l:=map _ (map _ x)).
    eapply Hadd.
    - simpl_Forall. constructor.
    - erewrite map_map, map_ext; eauto.
      intros; destruct_conjs; auto.
  Qed.

  Lemma delast_block_vars_perm : forall blk sub blk' xs st st',
      VarsDefined blk xs ->
      delast_block sub blk st = (blk', st') ->
      VarsDefined blk' xs.
  Proof.
    Opaque delast_scope.
    induction blk using block_ind2; intros * Hvars Hdl;
      inv Hvars; repeat inv_bind.
    - (* equation *)
      destruct eq. simpl. constructor.
    - (* reset *)
      constructor.
      eapply mmap_vars_perm in H0; eauto.
    - (* switch *)
      constructor.
      + apply mmap_values in H0. inv H0; congruence.
      + eapply mmap_values, Forall2_ignore1 in H0. simpl_Forall; repeat inv_bind.
        destruct b0. repeat inv_bind. take (VarsDefinedBranch _ _ _) and inv it. inv_VarsDefined.
        constructor; simpl; auto using incl_nil'.
        eapply mmap_vars_perm in H3; eauto.
    - (* automaton *)
      destruct ini; repeat inv_bind.
      constructor.
      + apply mmap_values in H0. inv H0; congruence.
      + eapply mmap_values, Forall2_ignore1 in H0. simpl_Forall; repeat inv_bind.
        destruct b0 as [?(?&[?(?&?)])]. repeat inv_bind.
        take (VarsDefinedBranch _ _ _) and inv it. inv_VarsDefined.
        econstructor; simpl; auto using incl_nil'.
        eapply delast_scope_vars_perm; eauto.
        * intros; repeat inv_bind; destruct_conjs. do 2 esplit; [|eauto].
          eapply mmap_vars_perm; eauto.
        * intros; destruct_conjs.
          do 2 esplit. eapply Forall2_app; eauto.
          now rewrite concat_app, Permutation_app_comm, H7.
    - (* local *)
      constructor. eapply delast_scope_vars_perm; eauto.
      * intros; simpl in *; destruct_conjs. do 2 esplit; [|eauto].
        eapply mmap_vars_perm; eauto.
      * intros; destruct_conjs.
        do 2 esplit. eapply Forall2_app; eauto.
        now rewrite concat_app, Permutation_app_comm, H4.
      Transparent delast_scope.
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

  Lemma delast_scope_GoodLocals {A} P_good1 (P_good2: _ -> Prop) f_dl f_add : forall locs (blks: A) sub s' st st',
      GoodLocalsScope P_good1 elab_prefs (Scope locs blks) ->
      delast_scope f_dl f_add sub (Scope locs blks) st = (s', st') ->
      (forall sub blks' st st',
          P_good1 blks ->
          f_dl sub blks st = (blks', st') ->
          P_good2 blks') ->
      (forall blks1 blks2,
          Forall (GoodLocals last_prefs) blks1 ->
          P_good2 blks2 ->
          P_good2 (f_add blks1 blks2)) ->
      GoodLocalsScope P_good2 last_prefs s'.
  Proof.
    intros * Hgood Hdl Hind Hadd; inv Hgood. repeat inv_bind.
    eapply Hind in H0; eauto.
    econstructor.
    - rewrite map_app. apply Forall_app; split.
      + erewrite map_map, map_ext; eauto using AtomOrGensym_add.
        intros; destruct_conjs; auto.
      + apply fresh_idents_prefixed in H.
        simpl_Forall; subst.
        right. repeat esplit; eauto. apply PSF.add_iff; auto.
    - apply Hadd; auto.
      simpl_Forall. constructor.
  Qed.

  Lemma delast_block_GoodLocals : forall blk sub blk' st st',
      GoodLocals elab_prefs blk ->
      delast_block sub blk st = (blk', st') ->
      GoodLocals last_prefs blk'.
  Proof.
    Opaque delast_scope.
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
      destruct b0. repeat inv_bind.
      take (GoodLocalsBranch _ _) and inv it. constructor.
      eapply mmap_values, Forall2_ignore1 in H3. simpl_Forall; eauto.
    - (* automaton *)
      destruct ini; repeat inv_bind.
      repeat constructor.
      eapply mmap_values, Forall2_ignore1 in H0. simpl_Forall. destruct b0 as [?(?&[?(?&?)])]. repeat inv_bind.
      take (GoodLocalsBranch _ _) and inv it. constructor.
      eapply delast_scope_GoodLocals; eauto.
      + intros; repeat inv_bind. eapply mmap_values, Forall2_ignore1 in H5.
        simpl_Forall; eauto.
      + intros. destruct blks2. apply Forall_app; auto.
    - (* local *)
      constructor.
      eapply delast_scope_GoodLocals; eauto.
      + intros. eapply mmap_values, Forall2_ignore1 in H3.
        simpl_Forall; eauto.
      + intros. apply Forall_app; auto.
        Transparent delast_scope.
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

  Fact fresh_idents_nIn_ids : forall lasts lasts' st st',
      fresh_idents lasts st = (lasts', st') ->
      Forall (fun '(_, lx, _) => ~In lx (st_ids st)) lasts'.
  Proof.
    unfold fresh_idents.
    induction lasts; intros; destruct_conjs; repeat inv_bind; constructor; eauto.
    - eapply fresh_ident_nIn in H; eauto.
    - eapply IHlasts in H0.
      simpl_Forall. contradict H0.
      eapply incl_map; eauto.
      apply st_follows_incl; eauto with fresh.
  Qed.

  Fact fresh_idents_NoDup : forall lasts lasts' st st',
      fresh_idents lasts st = (lasts', st') ->
      NoDupMembers (map (fun '(_, lx, (ty, ck, _)) => (lx, (ty, ck, xH, @None (exp * ident)))) lasts').
  Proof.
    unfold fresh_idents.
    induction lasts; intros * Hfresh;
      destruct_conjs; repeat inv_bind; constructor; eauto.
    - intros Hinm. rewrite fst_InMembers in Hinm; simpl_In.
      eapply fresh_idents_nIn_ids in H0.
      simpl_Forall.
      eapply H0, fresh_ident_Inids; eauto.
  Qed.

  Fact mmap_delast_NoDupLocals sub : forall blks blks' xs st st',
      Forall
        (fun blk => forall xs sub blk' st st',
             Forall (fun x : ident => AtomOrGensym elab_prefs x \/ In x (st_ids st)) xs ->
             GoodLocals elab_prefs blk ->
             NoDupLocals xs blk ->
             delast_block sub blk st = (blk', st') ->
             NoDupLocals xs blk') blks ->
      Forall (fun x : ident => AtomOrGensym elab_prefs x \/ In x (st_ids st)) xs ->
      Forall (GoodLocals elab_prefs) blks ->
      Forall (NoDupLocals xs) blks ->
      mmap (delast_block sub) blks st = (blks', st') ->
      Forall (NoDupLocals xs) blks'.
  Proof.
    intros * Hf Hat Hgood Hnd Hdl; repeat inv_bind.
    eapply mmap_values_follows in Hdl; eauto.
    2:{ intros. eapply delast_block_st_follows; eauto. }
    eapply Forall2_ignore1 in Hdl; simpl_Forall.
    eapply Hf in H2; eauto.
    simpl_Forall. destruct Hat; auto.
    right. eapply incl_map; eauto. apply st_follows_incl; eauto with fresh.
  Qed.

  Lemma delast_scope_NoDupLocals {A} P_good P_nd f_dl f_add :
    forall locs (blks: A) xs sub s' st st',
      Forall (fun x => AtomOrGensym elab_prefs x \/ In x (st_ids st)) xs ->
      GoodLocalsScope P_good elab_prefs (Scope locs blks) ->
      NoDupScope P_nd xs (Scope locs blks) ->
      delast_scope f_dl f_add sub (Scope locs blks) st = (s', st') ->
      (forall xs ys,
          P_good blks ->
          (forall x : ident, In x ys -> In x xs \/ (exists id hint, x = gensym last hint id)) ->
          P_nd xs blks ->
          P_nd ys blks) ->
      (forall sub xs blks' st st',
          Forall (fun x => AtomOrGensym elab_prefs x \/ In x (st_ids st)) xs ->
          P_good blks ->
          P_nd xs blks ->
          f_dl sub blks st = (blks', st') ->
          P_nd xs blks') ->
      (forall xs blks1 blks2,
          Forall (NoDupLocals xs) blks1 ->
          P_nd xs blks2 ->
          P_nd xs (f_add blks1 blks2)) ->
      NoDupScope P_nd xs s'.
  Proof.
    intros * Hat Hgood Hnd Hdl Hincl' Hind Hadd; inv Hgood; inv Hnd;
      repeat inv_bind.
    assert (Forall (fun '(_, lx, _) => exists n hint, lx = gensym last hint n) x) as Hgen.
    { eapply mmap_values, Forall2_ignore1 in H. simpl_Forall. repeat inv_bind.
      eapply fresh_ident_prefixed in H7; auto. }
    constructor.
    - apply Hadd. 1:simpl_Forall; constructor.
      eapply Hind in H0; eauto.
      + simpl_app. repeat rewrite Forall_app. repeat split.
        * simpl_Forall. destruct Hat; eauto. right.
          eapply incl_map; eauto using st_follows_incl, fresh_idents_st_follows.
        * simpl_Forall; eauto.
        * eapply fresh_idents_In_ids in H. simpl_Forall; auto.
      + eapply Hincl'. 1,3:eauto.
        intros * Hin. simpl_app. repeat rewrite in_app_iff in *.
        erewrite 2 map_map, map_ext in Hin. destruct Hin as [|[|]]; eauto. 2:intros; destruct_conjs; auto.
        simpl_In.
        eapply Forall_forall in Hgen; eauto. simpl in *; auto.
    - apply NoDupMembers_app.
      + apply NoDupMembers_map; auto. intros; destruct_conjs; auto.
      + eapply fresh_idents_NoDup; eauto.
      + intros * Hinm1 Hinm2. rewrite fst_InMembers in Hinm1, Hinm2. simpl_In.
        simpl_Forall; subst. eapply contradict_AtomOrGensym; eauto using last_not_in_elab_prefs.
    - intros * Hinm1 Hin2. apply InMembers_app in Hinm1 as [Hinm1|Hinm1].
      + eapply H6; eauto. rewrite fst_InMembers in *. solve_In.
      + rewrite fst_InMembers in Hinm1. simpl_In.
        simpl_Forall; subst. destruct Hat.
        * eapply contradict_AtomOrGensym in H4; eauto using last_not_in_elab_prefs.
        * eapply fresh_idents_nIn_ids in H.
          simpl_Forall; eauto.
  Qed.

  Lemma delast_block_NoDupLocals : forall blk xs sub blk' st st',
      Forall (fun x => AtomOrGensym elab_prefs x \/ In x (st_ids st)) xs ->
      GoodLocals elab_prefs blk ->
      NoDupLocals xs blk ->
      delast_block sub blk st = (blk', st') ->
      NoDupLocals xs blk'.
  Proof.
    Opaque delast_scope.
    induction blk using block_ind2; intros * Hat Hgood Hnd Hdl;
      inv Hgood; inv Hnd; repeat inv_bind.
    - (* equation *)
      constructor.
    - (* reset *)
      constructor.
      eapply mmap_delast_NoDupLocals; eauto.
    - (* switch *)
      eapply mmap_values_follows in H0; eauto.
      2:{ intros; destruct_conjs; repeat inv_bind.
          destruct b0. repeat inv_bind.
          eapply mmap_st_follows; eauto.
          simpl_Forall. eapply delast_block_st_follows; eauto. }
      constructor. eapply Forall2_ignore1 in H0; simpl_Forall; repeat inv_bind.
      take (NoDupBranch _ _) and inv it. take (GoodLocalsBranch _ _) and inv it. repeat inv_bind. repeat constructor.
      eapply mmap_delast_NoDupLocals in H1; eauto.
      simpl_Forall. destruct Hat; auto. right.
      eapply incl_map; eauto. apply st_follows_incl; eauto with fresh.
    - (* automaton *)
      destruct ini; repeat inv_bind.
      eapply mmap_values_follows in H0; eauto.
      2:{ intros; destruct_conjs; repeat inv_bind.
          destruct b0 as [?(?&[?(?&?)])]. repeat inv_bind.
          eapply delast_scope_st_follows; eauto.
          intros; repeat inv_bind; eapply mmap_st_follows; eauto.
          simpl_Forall. eapply delast_block_st_follows; eauto. }
      constructor. eapply Forall2_ignore1 in H0; simpl_Forall; repeat inv_bind.
      destruct b0 as [?(?&[?(?&?)])]. take (NoDupBranch _ _) and inv it. take (GoodLocalsBranch _ _) and inv it.
      repeat inv_bind. repeat constructor.
      eapply delast_scope_NoDupLocals in H1; eauto.
      + simpl_Forall. destruct Hat; auto.
        right. eapply incl_map; eauto. apply st_follows_incl; eauto with fresh.
      + intros; simpl in *. simpl_Forall.
        eapply NoDupLocals_incl'; eauto using last_not_in_elab_prefs.
      + intros; repeat inv_bind. eapply mmap_delast_NoDupLocals; eauto.
      + intros. destruct blks2. apply Forall_app; auto.
    - (* local *)
      constructor.
      eapply delast_scope_NoDupLocals; eauto.
      * intros. simpl_Forall.
        eapply NoDupLocals_incl'; eauto using last_not_in_elab_prefs.
      * intros; simpl in *. eapply mmap_delast_NoDupLocals; eauto.
      * intros. apply Forall_app; auto.
        Transparent delast_scope.
  Qed.

  (** *** No last remaining *)

  Fact delast_scope_nolast {A} f_dl f_add (P_nl: _ -> Prop) : forall sub locs (blks : A) s' st st',
      delast_scope f_dl f_add sub (Scope locs blks) st = (s', st') ->
      (forall sub blks' st st',
          f_dl sub blks st = (blks', st') ->
          P_nl blks') ->
      (forall blks1 blks2,
          Forall nolast_block blks1 ->
          P_nl blks2 ->
          P_nl (f_add blks1 blks2)) ->
      nolast_scope P_nl s'.
  Proof.
    intros * Hdl Hind Hadd; repeat inv_bind.
    constructor.
    - apply Forall_app. split; simpl_Forall; auto.
    - eapply Hadd; eauto.
      simpl_Forall. constructor.
  Qed.

  Lemma delast_block_nolast : forall blk sub blk' st st',
      delast_block sub blk st = (blk', st') ->
      nolast_block blk'.
  Proof.
    Opaque delast_scope.
    induction blk using block_ind2; intros * Hdl; repeat inv_bind.
    - (* equation *)
      constructor.
    - (* reset *)
      constructor.
      eapply mmap_values, Forall2_ignore1 in H0.
      simpl_Forall; eauto.
    - (* switch *)
      constructor.
      eapply mmap_values, Forall2_ignore1 in H0. simpl_Forall; repeat inv_bind.
      destruct b0. repeat inv_bind. constructor.
      eapply mmap_values, Forall2_ignore1 in H2. simpl_Forall; eauto.
    - (* automaton *)
      destruct ini; repeat inv_bind.
      constructor.
      eapply mmap_values, Forall2_ignore1 in H0. simpl_Forall. repeat inv_bind.
      destruct b0 as [?(?&[?(?&?)])]; repeat inv_bind. constructor.
      eapply delast_scope_nolast; eauto.
      + intros; repeat inv_bind. eapply mmap_values, Forall2_ignore1 in H3.
        simpl_Forall; eauto.
      + intros. destruct blks2. apply Forall_app; auto.
    - (* local *)
      constructor. eapply delast_scope_nolast; eauto.
      + intros. eapply mmap_values, Forall2_ignore1 in H1.
        simpl_Forall; eauto.
      + intros. apply Forall_app; auto.
        Transparent delast_scope.
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
    simpl_Forall; auto.
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
    { transform_program_without_units := fun g => Global g.(types) g.(externs) [] }.

  Definition delast_global : @global (fun _ => True) elab_prefs -> @global nolast_block last_prefs :=
    transform_units.

  (** *** Equality of interfaces *)

  Lemma delast_global_iface_eq : forall G,
      global_iface_eq G (delast_global G).
  Proof.
    repeat split; auto.
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
