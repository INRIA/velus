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
From Velus Require Import Lustre.StaticEnv.
From Velus Require Import Lustre.LSyntax Lustre.LOrdered Lustre.LTyping Lustre.LClocking Lustre.LSemantics Lustre.LClockedSemantics.
From Velus Require Import Lustre.InlineLocal.InlineLocal Lustre.InlineLocal.ILTyping Lustre.InlineLocal.ILClocking.

Module Type ILCORRECTNESS
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks : CLOCKS Ids Op OpAux)
       (Import CStr : COINDSTREAMS Ids Op OpAux Cks)
       (Import Senv : STATICENV Ids Op OpAux Cks)
       (Import Syn : LSYNTAX Ids Op OpAux Cks Senv)
       (Import Ty : LTYPING Ids Op OpAux Cks Senv Syn)
       (Import Cl : LCLOCKING Ids Op OpAux Cks Senv Syn)
       (Import Ord : LORDERED Ids Op OpAux Cks Senv Syn)
       (Import Sem : LSEMANTICS Ids Op OpAux Cks Senv Syn Ord CStr)
       (Import LCS : LCLOCKEDSEMANTICS Ids Op OpAux Cks Senv Syn Cl Ord CStr Sem)
       (Import IL  : INLINELOCAL Ids Op OpAux Cks Senv Syn).

  Module Typing := ILTypingFun Ids Op OpAux Cks Senv Syn Ty IL.
  Module Clocking := ILClockingFun Ids Op OpAux Cks Senv Syn Cl IL.

  Lemma rename_var_sem sub : forall H H' x vs,
      (forall y vs, Env.find x sub = Some y -> sem_var H (Var x) vs -> sem_var H' (Var y) vs) ->
      (forall vs, Env.find x sub = None -> sem_var H (Var x) vs -> sem_var H' (Var x) vs) ->
      sem_var H (Var x) vs ->
      sem_var H' (Var (rename_var sub x)) vs.
  Proof.
    intros * Hsub Hnsub Hv. unfold rename_var.
    destruct (Env.find x sub) eqn:Hfind; eauto.
  Qed.

  Lemma rename_last_sem sub : forall H H' x vs,
      (forall y vs, Env.find x sub = Some y -> sem_var H (Last x) vs -> sem_var H' (Last y) vs) ->
      (forall vs, Env.find x sub = None -> sem_var H (Last x) vs -> sem_var H' (Last x) vs) ->
      sem_var H (Last x) vs ->
      sem_var H' (Last (rename_var sub x)) vs.
  Proof.
    intros * Hsub Hnsub Hv. unfold rename_var.
    destruct (Env.find x sub) eqn:Hfind; eauto.
  Qed.

  Lemma rename_var_sem' sub : forall H H' x vs,
      (forall y vs, Env.find x sub = Some y -> sem_var H x vs -> sem_var H' y vs) ->
      (forall vs, Env.find x sub = None -> sem_var H x vs -> sem_var H' x vs) ->
      sem_var H x vs ->
      sem_var H' (rename_var sub x) vs.
  Proof.
    intros * Hsub Hnsub Hv. unfold rename_var.
    destruct (Env.find x sub) eqn:Hfind; setoid_rewrite Hfind; eauto.
  Qed.

  Section rename.
    Context {PSyn1 PSyn2 : list decl -> block -> Prop} {prefs1 prefs2 : PS.t}.
    Variable G1 : @global PSyn1 prefs1.
    Variable G2 : @global PSyn2 prefs2.

    Hypothesis HGref : global_sem_refines G1 G2.

    Variable sub : Env.t ident.
    Variable bs : Stream bool.
    Variable H H' : history.

    Hypothesis Hsub : forall x y vs,
        Env.find x sub = Some y ->
        sem_var H (Var x) vs ->
        sem_var H' (Var y) vs.

    Hypothesis Hnsub : forall x vs,
        Env.find x sub = None ->
        sem_var H (Var x) vs ->
        sem_var H' (Var x) vs.

    Hypothesis Hlsub : forall x y vs,
        Env.find x sub = Some y ->
        sem_var H (Last x) vs ->
        sem_var H' (Last y) vs.

    Hypothesis Hlnsub : forall x vs,
        Env.find x sub = None ->
        sem_var H (Last x) vs ->
        sem_var H' (Last x) vs.

    Lemma rename_exp_sem : forall e vs,
        sem_exp_ck G1 H bs e vs ->
        sem_exp_ck G2 H' bs (rename_exp sub e) vs.
    Proof.
      induction e using exp_ind2; intros * Hsem; inv Hsem; simpl.
      - (* const *)
        constructor; auto.
      - (* enum *)
        constructor; auto.
      - (* var *)
        constructor.
        eapply rename_var_sem; eauto.
      - (* last *)
        constructor.
        eapply rename_last_sem; eauto.
      - (* unop *)
        econstructor; eauto.
        now rewrite rename_exp_typeof.
      - (* binop *)
        econstructor; eauto.
        1,2:now rewrite rename_exp_typeof.
      - (* extcall *)
        econstructor; eauto.
        1,2:simpl_Forall; eauto.
        now rewrite rename_exp_typesof.
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
        + now rewrite rename_exp_typeof.
        + rewrite <-Sem.Forall2Brs_map_1.
          eapply Sem.Forall2Brs_impl_In; [|eauto]; intros ?? Hex Hsem.
          simpl_Exists. simpl_Forall. eauto.
        + simpl_Forall; eauto.
      - (* app *)
        eapply Sapp with (ss:=ss); eauto.
        1,2:simpl_Forall; eauto.
        intros. eapply HGref; eauto.
    Qed.

    Lemma rename_equation_sem : forall equ,
        sem_equation_ck G1 H bs equ ->
        sem_equation_ck G2 H' bs (rename_equation sub equ).
    Proof.
      intros (?&?) Hsem. inv Hsem.
      eapply Seq with (ss:=ss); simpl_Forall;
        eauto using rename_exp_sem, rename_var_sem.
    Qed.

  End rename.

  Lemma rename_clock_sem : forall bck sub Hi Hi' bs bs' ck bs1,
      (forall x y vs, Env.find x sub = Some y -> sem_var Hi x vs -> sem_var Hi' y vs) ->
      (forall x vs, Env.find x sub = None -> sem_var Hi x vs -> sem_var Hi' x vs) ->
      sem_clock Hi' bs' bck bs ->
      sem_clock Hi bs ck bs1 ->
      sem_clock Hi' bs (rename_clock sub ck) bs1.
  Proof.
    induction ck; intros * Hsub Hnsub Hbck * Hsemck; simpl; inv Hsemck.
    - constructor; auto.
    - econstructor; eauto using rename_var_sem'.
  Qed.

  Fact mask_hist_sub sub : forall k r H H',
      (forall x y vs, Env.find x sub = Some y -> sem_var H (Var x) vs -> sem_var H' (Var y) vs) ->
      forall x y vs, Env.find x sub = Some y -> sem_var (mask_hist k r H) (Var x) vs -> sem_var (mask_hist k r H') (Var y) vs.
  Proof.
    intros * Hsub * Hfind Hv.
    eapply sem_var_mask_inv in Hv as (?&Hv&Heq).
    eapply Hsub, sem_var_mask in Hv; eauto. rewrite Heq; eauto.
  Qed.

  Fact mask_hist_nsub (sub : Env.t ident) : forall k r H H',
      (forall x vs, Env.find x sub = None -> sem_var H (Var x) vs -> sem_var H' (Var x) vs) ->
      forall x vs, Env.find x sub = None -> sem_var (mask_hist k r H) (Var x) vs -> sem_var (mask_hist k r H') (Var x) vs.
  Proof.
    intros * Hsub * Hfind Hv.
    eapply sem_var_mask_inv in Hv as (?&Hv&Heq).
    eapply Hsub, sem_var_mask in Hv; eauto. rewrite Heq; eauto.
  Qed.

  Import List.

  Fact find_snd_spec {A} : forall (locs : list (ident * A)) (locs' : list ident) x y,
      NoDup locs' ->
      In (x, y) (combine (map fst locs) locs') ->
      find (fun '(_, y') => Var y' ==b Var y) (combine (map fst locs) locs') = Some (x, y).
  Proof.
    induction locs; intros * Nd In; simpl in *; [inv In|].
    inv Nd; [inv In|]. inv In; inv_equalities.
    - now rewrite equiv_decb_refl.
    - cases_eqn Eq.
      rewrite equiv_decb_equiv in Eq; inv Eq.
      eapply in_combine_r in H1. contradiction.
  Qed.

  Section inlinelocal_node_sem.
    Variable G1 : @global noswitch switch_prefs.
    Variable G2 : @global nolocal local_prefs.

    Hypothesis HGref : global_sem_refines G1 G2.
    Hypothesis HwG1 : wc_global G1.

    Fact InMembers_sub {A} : forall (sub : Env.t ident) (xs : list (ident * A)) x,
        InMembers x (map_filter (fun '(x, vs) => option_map (fun y : ident => (y, vs)) (Env.find x sub)) xs) ->
        exists y, Env.MapsTo y x sub.
    Proof.
      intros * Hinm.
      eapply InMembers_In in Hinm as (?&Hin).
      eapply map_filter_In' in Hin as ((?&?)&Hin&Hopt).
      eapply option_map_inv in Hopt as (?&Hfind'&Heq); inv Heq.
      eauto.
    Qed.

    Fact InMembers_sub_iff {A} : forall (sub : Env.t ident) (xs : list (ident * A)) x,
        InMembers x (map_filter (fun '(x, vs) => option_map (fun y : ident => (y, vs)) (Env.find x sub)) xs) <->
        exists y, InMembers y xs /\ Env.MapsTo y x sub.
    Proof.
      intros *; split; [intros Hinm|intros (?&Hinm&Hfind)].
      - eapply InMembers_In in Hinm as (?&Hin).
        eapply map_filter_In' in Hin as ((?&?)&Hin&Hopt).
        eapply option_map_inv in Hopt as (?&Hfind'&Heq); inv Heq.
        eauto using In_InMembers.
      - eapply InMembers_In in Hinm as (?&Hin).
        eapply In_InMembers, map_filter_In; eauto.
        simpl. rewrite Hfind; simpl; eauto.
    Qed.

    Fact NoDupMembers_sub {A} : forall (sub : Env.t ident) (xs : list (ident * A)),
        NoDupMembers xs ->
        NoDup (map snd (Env.elements sub)) ->
        NoDupMembers (map_filter (fun '(x, vs) => option_map (fun y => (y, vs)) (Env.find x sub)) xs).
    Proof.
      intros * Hnd1 Hnd2.
      induction xs as [|(?&?)]; inv Hnd1; simpl; auto with datatypes.
      destruct (option_map _ _) as [(?&?)|] eqn:Hopt; auto.
      econstructor; auto.
      intros Hinm.
      eapply option_map_inv in Hopt as (?&Hfind&Heq); inv Heq.
      apply InMembers_In in Hinm as (?&Hin).
      eapply map_filter_In' in Hin as ((?&?)&Hin&Hopt).
      eapply option_map_inv in Hopt as (?&Hfind'&Heq); inv Heq.
      eapply Env.NoDup_snd_elements in Hnd2; [|eapply Hfind|eapply Hfind']; subst.
      eapply H1, In_InMembers; eauto.
    Qed.

    (** Induction on blocks *)

    Import Permutation.

    Local Hint Resolve InMembers_incl : datatypes.
    Local Hint Resolve <- fst_InMembers InMembers_idsnd InMembers_idfst : datatypes.
    Local Hint Resolve -> fst_InMembers InMembers_idsnd InMembers_idfst : datatypes.

    Fact HasClock_app2 : forall Γ Γ1 Γ2 x ck,
        HasClock (Γ ++ Γ1 ++ Γ2) x ck ->
        HasClock (Γ ++ Γ1) x ck \/ HasClock (Γ ++ Γ2) x ck.
    Proof.
      intros *. rewrite ? HasClock_app. intuition.
    Qed.

    Fact IsLast_app2 : forall Γ Γ1 Γ2 x,
        IsLast (Γ ++ Γ1 ++ Γ2) x ->
        IsLast (Γ ++ Γ1) x \/ IsLast (Γ ++ Γ2) x.
    Proof.
      intros *. rewrite ? IsLast_app. intuition.
    Qed.

    Fact HasClock_IsLast_app2 : forall Γ Γ1 Γ2 x ck,
        NoDupMembers (Γ1 ++ Γ2) ->
        HasClock (Γ ++ Γ1 ++ Γ2) x ck ->
        IsLast (Γ ++ Γ1 ++ Γ2) x ->
        (HasClock (Γ ++ Γ1) x ck /\ IsLast (Γ ++ Γ1) x)
        \/ (HasClock (Γ ++ Γ2) x ck /\ IsLast (Γ ++ Γ2) x).
    Proof.
      intros * ND Ck Last.
      rewrite ? HasClock_app, ? IsLast_app in *.
      repeat take (_ \/ _) and destruct it; auto.
      1,2:exfalso; take (HasClock _ _ _) and inv it; take (IsLast _ _) and inv it.
      - eapply NoDupMembers_app_InMembers in ND; eauto using In_InMembers.
      - eapply NoDupMembers_app_InMembers in ND; eauto using In_InMembers.
    Qed.

    Lemma sc_vars_app2 : forall Γ Γ1 Γ2 Hi1 Hi2 bs,
        NoDupMembers (Γ1 ++ Γ2) ->
        Hi1 ⊑ (Hi1 + Hi2) ->
        dom Hi1 (Γ ++ Γ1) ->
        dom Hi2 (Γ ++ Γ2) ->
        sc_vars (Γ ++ Γ1) Hi1 bs ->
        sc_vars (Γ ++ Γ2) Hi2 bs ->
        sc_vars (Γ ++ Γ1 ++ Γ2) (Hi1 + Hi2) bs.
    Proof.
      intros * ND Ref1 Dom1 Dom2 Sc1 Sc2.
      assert (Hi2 ⊑ (Hi1 + Hi2)) as Ref2.
      { eapply FEnv.union_refines4'. apply EqStrel_Reflexive. }
      split.
      - intros * Ck Var.
        apply HasClock_app2 in Ck as [Ck|Ck].
        + destruct Sc1 as (Sc&_). eapply sem_clock_refines, Sc; eauto using var_history_refines.
          eapply sem_var_refines'; [|eauto|eauto].
          eapply Dom1; eauto with senv.
        + destruct Sc2 as (Sc&_). eapply sem_clock_refines, Sc; eauto using var_history_refines.
          eapply sem_var_refines'; [|eauto|eauto].
          eapply Dom2; eauto with senv.
      - intros * Ck Last Var.
        eapply HasClock_IsLast_app2 in Ck as [(Ck&L)|(Ck&L)]; eauto.
        + destruct Sc1 as (_&Sc). eapply sem_clock_refines, Sc; eauto using var_history_refines.
          eapply sem_var_refines'; [|eauto|eauto].
          eapply Dom1; eauto.
        + destruct Sc2 as (_&Sc). eapply sem_clock_refines, Sc; eauto using var_history_refines.
          eapply sem_var_refines'; [|eauto|eauto].
          eapply Dom2; eauto.
    Qed.

    Fact mmap_inlinelocal_block_sem : forall Γ blks sub Γ' Γ'' locs' blks' st st' bs Hi1 Hi2,
        Forall
          (fun blk => forall sub Γ' Γ'' locs' blks' st st' bs Hi1 Hi2,
               (forall x, IsVar Γ x -> ~IsVar Γ' x) ->
               (forall x, Env.In x sub <-> IsVar Γ' x) ->
               (forall x y, Env.MapsTo x y sub -> InMembers y Γ' \/ exists n hint, y = gensym local hint n) ->
               (forall x y vs, Env.find x sub = Some y -> sem_var Hi1 (Var x) vs -> sem_var Hi2 (Var y) vs) ->
               (forall x vs, IsVar Γ x -> sem_var Hi1 (Var x) vs -> sem_var Hi2 (Var x) vs) ->
               (forall x y vs, Env.find x sub = Some y -> sem_var Hi1 (Last x) vs -> sem_var Hi2 (Last y) vs) ->
               (forall x vs, IsLast Γ x -> sem_var Hi1 (Last x) vs -> sem_var Hi2 (Last x) vs) ->
               NoDupMembers (Γ++Γ') ->
               noswitch_block blk ->
               NoDupLocals (map fst Γ++map fst Γ'++map fst Γ'') blk ->
               Forall (AtomOrGensym switch_prefs) (map fst Γ) ->
               GoodLocals switch_prefs blk ->
               dom_ub Hi1 (Γ++Γ') ->
               sem_block_ck G1 Hi1 bs blk ->
               dom Hi2 (Γ++Γ'') ->
               sc_vars (Γ++Γ'') Hi2 bs ->
               st_valid st ->
               Forall (fun x => st_In x st) (map fst (Γ ++ Γ'')) ->
               inlinelocal_block sub blk st = (locs', blks', st') ->
               exists Hi3,
                 Hi2 ⊑ Hi3 /\
                 dom Hi3 (Γ++Γ''++senv_of_decls locs') /\
                 sc_vars (Γ++Γ''++senv_of_decls locs') Hi3 bs /\
                 Forall (sem_block_ck G2 Hi3 bs) blks')
          blks ->
        (forall x, IsVar Γ x -> ~IsVar Γ' x) ->
        (forall x, Env.In x sub <-> IsVar Γ' x) ->
        (forall x y, Env.MapsTo x y sub -> InMembers y Γ' \/ exists n hint, y = gensym local hint n) ->
        (forall x y vs, Env.find x sub = Some y -> sem_var Hi1 (Var x) vs -> sem_var Hi2 (Var y) vs) ->
        (forall x vs, IsVar Γ x -> sem_var Hi1 (Var x) vs -> sem_var Hi2 (Var x) vs) ->
        (forall x y vs, Env.find x sub = Some y -> sem_var Hi1 (Last x) vs -> sem_var Hi2 (Last y) vs) ->
        (forall x vs, IsLast Γ x -> sem_var Hi1 (Last x) vs -> sem_var Hi2 (Last x) vs) ->
        NoDupMembers (Γ++Γ') ->
        Forall noswitch_block blks ->
        Forall (NoDupLocals (map fst Γ++map fst Γ'++map fst Γ'')) blks ->
        Forall (AtomOrGensym switch_prefs) (map fst Γ) ->
        Forall (GoodLocals switch_prefs) blks ->
        dom_ub Hi1 (Γ++Γ') ->
        Forall (sem_block_ck G1 Hi1 bs) blks ->
        dom Hi2 (Γ++Γ'') ->
        sc_vars (Γ++Γ'') Hi2 bs ->
        st_valid st ->
        Forall (fun x => st_In x st) (map fst (Γ ++ Γ'')) ->
        mmap2 (inlinelocal_block sub) blks st = (locs', blks', st') ->
        exists Hi3,
          Hi2 ⊑ Hi3 /\
          dom Hi3 (Γ++Γ''++senv_of_decls (concat locs')) /\
          sc_vars (Γ++Γ''++senv_of_decls (concat locs')) Hi3 bs /\
          Forall (sem_block_ck G2 Hi3 bs) (concat blks').
    Proof with eauto.
      induction blks;
        intros * Hf Hdisj Hsubin Hsubgen Hvar Hnvar Hlast Hnlast Hnd1 Hns Hnd2 Hatgen Hgood Hub Hsem Hdom Hsc V InSt Hmmap;
        inv Hf; inv Hns; inv Hnd2; inv Hgood; (* inv Hwc; *) inv Hsem; repeat monadInv; simpl in *.
      - repeat rewrite app_nil_r. exists Hi2. repeat (split; auto with env). reflexivity.
      - assert (Il:=H). assert (Ils:=H0).
        eapply H1 with (Hi1:=Hi1) (Hi2:=Hi2) in H as (Hi3&Href3&Hdom3&Hsc3&Hsem3); eauto.
        eapply IHblks with (Hi1:=Hi1) (Hi2:=Hi2) in H0 as (Hi4&Href4&Hdom4&Hsc4&Hsem4);
          eauto using inlinelocal_block_st_valid.
        2:{ simpl_Forall. eapply inlinelocal_block_st_follows in Il; eauto using st_follows_In. }
        clear H1 IHblks H2.
        remember (FEnv.union Hi3 Hi4) as Hi5.
        assert (FEnv.refines (@EqSt _) Hi4 Hi5) as Ref2.
        { subst. eapply FEnv.union_refines4'; eauto using EqStrel_Reflexive. }
        assert (FEnv.refines (@EqSt _) Hi3 Hi5) as Ref1.
        { subst. intros [] ? Find.
          - apply FEnv.find_In in Find as In. apply Hdom3 in In.
            rewrite app_assoc, IsVar_app in In. destruct In as [In|In].
            + assert (sem_var Hi2 (Var x4) v) as Var. 2:inversion_clear Var as [???? Find' Eq].
              { eapply sem_var_refines' in Href3; eauto.
                - now apply Hdom.
                - econstructor; eauto. reflexivity. }
              eapply Href4 in Find' as (?&Eq2&Find').
              eapply Ref2 in Find' as (?&Eq3&Find'').
              do 2 esplit; [|eauto]. now rewrite Eq, Eq2, Eq3.
            + erewrite FEnv.union2; eauto. do 2 esplit; eauto. reflexivity.
              apply FEnv.not_find_In. intros In2. eapply Hdom4 in In2.
              rewrite app_assoc, IsVar_app in In2. destruct In2 as [In2|In2].
              * eapply inlinelocal_block_st_nIn in Il; eauto.
                clear - InSt In In2 Il. inv In. inv In2. simpl_In. simpl_Forall. contradiction.
              * eapply inlinelocal_blocks_st_nIn in Ils; eauto using inlinelocal_block_st_valid.
                eapply inlinelocal_block_st_In in Il; [|eauto].
                clear - In In2 Ils Il. inv In. inv In2. simpl_In. simpl_Forall. contradiction.
          - apply FEnv.find_In in Find as In. apply Hdom3 in In.
            rewrite app_assoc, IsLast_app in In. destruct In as [In|In].
            + assert (sem_var Hi2 (Last x4) v) as Var. 2:inversion_clear Var as [???? Find' Eq].
              { eapply sem_var_refines' in Href3; eauto.
                - now apply Hdom.
                - econstructor; eauto. reflexivity. }
              eapply Href4 in Find' as (?&Eq2&Find').
              eapply Ref2 in Find' as (?&Eq3&Find'').
              do 2 esplit; [|eauto]. now rewrite Eq, Eq2, Eq3.
            + erewrite FEnv.union2; eauto. do 2 esplit; eauto. reflexivity.
              apply FEnv.not_find_In. intros In2. eapply Hdom4 in In2.
              rewrite app_assoc, IsLast_app in In2. destruct In2 as [In2|In2].
              * eapply inlinelocal_block_st_nIn in Il; eauto.
                clear - InSt In In2 Il. inv In. inv In2. simpl_In. simpl_Forall. contradiction.
              * eapply inlinelocal_blocks_st_nIn in Ils; eauto using inlinelocal_block_st_valid.
                eapply inlinelocal_block_st_In in Il; [|eauto].
                clear - In In2 Ils Il. inv In. inv In2. simpl_In. simpl_Forall. contradiction.
        }
        exists Hi5; subst. split; [|split; [|split; [|apply Forall_app; split]]].
        + etransitivity; eauto.
        + rewrite senv_of_decls_app. unfold dom.
          destruct Hdom3 as (D3&DL3). destruct Hdom4 as (D4&DL4).
          split; intros ?; rewrite FEnv.union_In; [rewrite D3, D4|rewrite DL3, DL4];
            repeat rewrite IsVar_app; repeat rewrite IsLast_app;
            split; intros; repeat take (_ \/ _) and destruct it; auto.
        + rewrite senv_of_decls_app.
          rewrite app_assoc with (m:=Γ'') in *.
          eapply sc_vars_app2; eauto.
          rewrite <-senv_of_decls_app. apply NoDupMembers_senv_of_decls.
          eapply mmap_inlinelocal_block_NoDupMembers with (sub:=sub) (blks:=a::blks) (locs':=(x::x2)); eauto.
          2:{ simpl. unfold bind2, ret. rewrite Il, Ils; eauto. }
          simpl_Forall. eauto using inlinelocal_block_NoDupMembers.
        + simpl_Forall. eauto using sem_block_refines.
        + simpl_Forall. eauto using sem_block_refines.
    Qed.

    Ltac inv_scope :=
      (Syn.inv_scope || Ty.inv_scope || Cl.inv_scope || Sem.inv_scope || LCS.inv_scope).

    (* TODO move *)
    Fact combine_permute {A B} : forall (xs: list A) (ys: list B) x y,
        In (x, y) (combine xs ys) ->
        In (y, x) (combine ys xs).
    Proof.
      induction xs; destruct ys; intros * In; inv In; simpl; auto with datatypes.
      inv H; auto.
    Qed.

    Fact rename_var_idem : forall xs ys sub x,
        In x xs ->
        length ys = length xs ->
        NoDup xs ->
        NoDup ys ->
        Env.find (rename_var (Env.adds xs ys sub) x) (Env.from_list (combine ys xs)) = Some x.
    Proof.
      intros * In Len ND1 ND2.
      assert (exists y, List.In (x, y) (combine xs ys)) as (?&In1).
      { apply In_nth_error in In as (n&Nth).
        assert (n < length ys) as Len1.
        { rewrite Len. eapply nth_error_Some. congruence. }
        apply nth_error_Some in Len1. destruct (nth_error ys n) eqn:Eq; try congruence.
        setoid_rewrite In_combine_nth_error; eauto.
      }
      unfold rename_var, or_default.
      erewrite Env.In_find_adds; eauto using combine_permute.
      erewrite Env.find_In_from_list; eauto using combine_permute, NoDup_NoDupMembers_combine.
    Qed.

    Fact rename_var_injective : forall xs ys sub x1 x2,
        In x1 xs ->
        In x2 xs ->
        length ys = length xs ->
        NoDup xs ->
        NoDup ys ->
        rename_var (Env.adds xs ys sub) x1 = rename_var (Env.adds xs ys sub) x2 ->
        x1 = x2.
    Proof.
      intros * In1 In2 Len ND1 ND2 Eq.
      assert (exists y, List.In (x1, y) (combine xs ys)) as (?&In1').
      { apply In_nth_error in In1 as (n&Nth).
        assert (n < length ys) as Len1.
        { rewrite Len. eapply nth_error_Some. congruence. }
        apply nth_error_Some in Len1. destruct (nth_error ys n) eqn:Eq'; try congruence.
        setoid_rewrite In_combine_nth_error; eauto.
      }
      assert (exists y, List.In (x2, y) (combine xs ys)) as (?&In2').
      { apply In_nth_error in In2 as (n&Nth).
        assert (n < length ys) as Len1.
        { rewrite Len. eapply nth_error_Some. congruence. }
        apply nth_error_Some in Len1. destruct (nth_error ys n) eqn:Eq'; try congruence.
        setoid_rewrite In_combine_nth_error; eauto.
      }
      unfold rename_var, or_default in *.
      erewrite ? Env.In_find_adds in Eq. 3,5:eauto. 2,3:eauto.
      subst.
      eapply NoDupMembers_det; eauto using combine_permute, NoDup_NoDupMembers_combine.
    Qed.

    (** Central correctness lemma                                              *)
    (* - vars : not renamed (in + out of the node)
       - vars' : renamed (local vars already encountered)
       - Hi1 : history before renaming
       - Hi2 : history after renaming of the enclosing blocks
       - Hi3 : refines Hi2 by adding the renamed variables of the subblocks
     *)
    Lemma inlinelocal_block_sem Γ : forall blk sub Γ' Γ'' locs' blks' st st' bs Hi1 Hi2,
        (forall x, IsVar Γ x -> ~IsVar Γ' x) ->
        (forall x, Env.In x sub <-> IsVar Γ' x) ->
        (forall x y, Env.MapsTo x y sub -> InMembers y Γ' \/ exists n hint, y = gensym local hint n) ->
        (forall x y vs, Env.find x sub = Some y -> sem_var Hi1 (Var x) vs -> sem_var Hi2 (Var y) vs) ->
        (forall x vs, IsVar Γ x -> sem_var Hi1 (Var x) vs -> sem_var Hi2 (Var x) vs) ->
        (forall x y vs, Env.find x sub = Some y -> sem_var Hi1 (Last x) vs -> sem_var Hi2 (Last y) vs) ->
        (forall x vs, IsLast Γ x -> sem_var Hi1 (Last x) vs -> sem_var Hi2 (Last x) vs) ->
        NoDupMembers (Γ++Γ') ->
        noswitch_block blk ->
        NoDupLocals (map fst Γ++map fst Γ'++map fst Γ'') blk ->
        Forall (AtomOrGensym switch_prefs) (map fst Γ) ->
        GoodLocals switch_prefs blk ->
        dom_ub Hi1 (Γ++Γ') ->
        sem_block_ck G1 Hi1 bs blk ->
        dom Hi2 (Γ ++ Γ'') ->
        sc_vars (Γ++Γ'') Hi2 bs ->
        st_valid st ->
        Forall (fun x => st_In x st) (map fst (Γ ++ Γ'')) ->
        inlinelocal_block sub blk st = (locs', blks', st') ->
        exists Hi3,
          Hi2 ⊑ Hi3 /\
          dom Hi3 (Γ++Γ''++senv_of_decls locs') /\
          sc_vars (Γ++Γ''++senv_of_decls locs') Hi3 bs /\
          Forall (sem_block_ck G2 Hi3 bs) blks'.
    Proof with eauto with datatypes.
      induction blk using block_ind2;
        intros * Hdisj Hsubin Hsubgen Hsvar Hnsvar Hslast Hnslast Hnd1 Hns Hnd2 Hgenat Hgood Hub Hsem Hdom Hsc V StIn Hdl;
        inv Hns; inv Hnd2; inv Hgood; inv Hsem; repeat monadInv; simpl.

      - (* equation *)
        repeat rewrite app_nil_r.
        exists Hi2. repeat (split; auto with env). reflexivity.
        repeat constructor; auto.
        eapply rename_equation_sem with (H:=Hi1); eauto using sem_ref_sem_equation.
        + intros * Hnone Hv.
          assert (Hin:=Hv). eapply sem_var_In, Hub in Hin.
          repeat rewrite map_app, in_app_iff in Hin.
          apply IsVar_app in Hin as [|]; eauto.
          * exfalso. eapply Env.Props.P.F.not_find_in_iff in Hnone. eapply Hnone, Hsubin...
        + intros * Hnone Hv.
          assert (Hin:=Hv). eapply sem_var_In, Hub in Hin.
          repeat rewrite map_app, in_app_iff in Hin.
          apply IsLast_app in Hin as [|]; eauto.
          * exfalso. eapply Env.Props.P.F.not_find_in_iff in Hnone. eapply Hnone, Hsubin; eauto with senv.

      - (* last *)
        repeat rewrite app_nil_r.
        exists Hi2. repeat (split; auto with env). reflexivity.
        assert (forall x vs2, Env.find x sub = None -> sem_var Hi1 (Var x) vs2 -> sem_var Hi2 (Var x) vs2) as Nsub.
        { intros * Hnone Hv.
          assert (Hin:=Hv). eapply sem_var_In, Hub in Hin.
          repeat rewrite map_app, in_app_iff in Hin.
          apply IsVar_app in Hin as [|]; eauto.
          exfalso. eapply Env.Props.P.F.not_find_in_iff in Hnone. eapply Hnone, Hsubin...
        }
        assert (forall x vs, Env.find x sub = None -> sem_var Hi1 (Last x) vs -> sem_var Hi2 (Last x) vs) as Nsubl.
        { intros * Hnone Hv.
          assert (Hin:=Hv). eapply sem_var_In, Hub in Hin.
          repeat rewrite map_app, in_app_iff in Hin.
          apply IsLast_app in Hin as [|]; eauto.
          exfalso. eapply Env.Props.P.F.not_find_in_iff in Hnone. eapply Hnone, Hsubin; eauto with senv.
        }
        repeat constructor; auto. econstructor; eauto using rename_var_sem, rename_last_sem.
        eapply rename_exp_sem with (H:=Hi1); eauto using sem_ref_sem_exp.

      - (* reset *)
        rename x into locs', x0 into blks'.
        assert (forall k, exists Hi4, (CStr.mask_hist k r Hi2) ⊑ (CStr.mask_hist k r Hi4) /\
                            dom (CStr.mask_hist k r Hi4) (Γ++Γ''++senv_of_decls (concat locs')) /\
                            sc_vars (Γ++Γ''++senv_of_decls (concat locs')) (mask_hist k r Hi4) (maskb k r bs) /\
                            Forall (sem_block_ck G2 (mask_hist k r Hi4) (maskb k r bs)) (concat blks')) as Hblks.
        { intros k. specialize (H10 k).
          eapply mmap_inlinelocal_block_sem with (Hi2:=CStr.mask_hist k r Hi2) in H10
            as (Hi4&Href1&Hdom1&Hsc1&Hsem1); eauto.
          2:{ intros ??? Hfind Hv.
              eapply sem_var_mask_inv in Hv as (?&Hv&Hmask).
              rewrite Hmask. eapply sem_var_mask... }
          2:{ intros ?? Hin Hv.
              eapply sem_var_mask_inv in Hv as (?&Hv&Hmask).
              rewrite Hmask. eapply sem_var_mask... }
          2:{ intros ??? Hfind Hv.
              eapply sem_var_mask_inv in Hv as (?&Hv&Hmask).
              rewrite Hmask. eapply sem_var_mask... }
          2:{ intros ?? Hin Hv.
              eapply sem_var_mask_inv in Hv as (?&Hv&Hmask).
              rewrite Hmask. eapply sem_var_mask... }
          2:{ eapply dom_ub_map; eauto. }
          2:{ eapply dom_map; eauto. }
          2:{ eapply sc_vars_mask in Hsc; eauto; subst. }
          assert (FEnv.Equiv (@EqSt _) Hi4 (CStr.mask_hist k r Hi4)) as Heqmask.
          { eapply slower_mask_hist. eapply sc_vars_slower_hist in Hsc1; eauto.
            simpl_app. auto using dom_dom_ub.
          }
          exists Hi4. split; [|split; [|split]].
          + rewrite <-Heqmask; auto.
          + apply dom_map; auto.
          + unfold mask_hist. simpl. eapply sc_vars_morph. 1,3,4:eauto; reflexivity. auto.
          + simpl_Forall. unfold mask_hist.
            eapply sem_block_ck_morph; eauto. reflexivity.
        }
        unfold mask_hist.
        eapply consolidate_mask_hist
          with (P := fun k H'k =>
                       (CStr.mask_hist k r Hi2) ⊑ H'k /\
                       dom H'k (Γ++Γ''++senv_of_decls (concat locs')) /\
                       sc_vars (Γ++Γ''++senv_of_decls (concat locs')) H'k (maskb k r bs) /\
                       Forall (sem_block_ck G2 H'k (maskb k r bs)) (concat blks'))
        in Hblks as (Hi4&HHi4).
        2:{ intros ????? Heq (Ref&Dom&(Sc1&Sc2)&Sem); subst. split; [|split; [|repeat split]].
            - rewrite <-Heq; auto.
            - split; intros ?; rewrite <-Heq; apply Dom.
            - intros. rewrite <-Heq. eapply Sc1; eauto. now rewrite Heq.
            - intros. rewrite <-Heq. eapply Sc2; eauto. now rewrite Heq.
            - simpl_Forall.
              eapply sem_block_ck_morph; eauto. reflexivity.
        }
        2:{ intros ?? (?&?&?). eapply dom_fenv_dom; eauto. }
        assert (Hi2 ⊑ Hi4) as Href1.
        { eapply refines_unmask; intros. eapply HHi4. }
        exists Hi4. split; [|split; [|repeat split]]; try rewrite app_nil_r; repeat rewrite <-app_assoc...
        + erewrite <-dom_map. eapply (HHi4 0)...
        + eapply sc_vars_unmask. intros k. eapply (HHi4 k)...
        + eapply sc_vars_unmask. intros k. eapply (HHi4 k)...
        + do 2 (econstructor; eauto).
          * eapply sem_exp_refines; [eauto|].
            eapply rename_exp_sem with (H:=Hi1); eauto using sem_ref_sem_exp.
            { intros * Hnone Hv.
              assert (Hin:=Hv). eapply sem_var_In, Hub in Hin; eauto.
              repeat rewrite map_app, in_app_iff in Hin.
              apply IsVar_app in Hin as [|]...
              exfalso. eapply Env.Props.P.F.not_find_in_iff in Hnone. eapply Hnone, Hsubin...
            }
            { intros * Hnone Hv.
              assert (Hin:=Hv). eapply sem_var_In, Hub in Hin; eauto.
              repeat rewrite map_app, in_app_iff in Hin.
              apply IsLast_app in Hin as [|]...
              exfalso. eapply Env.Props.P.F.not_find_in_iff in Hnone. eapply Hnone, Hsubin; eauto with senv.
            }
          * intros. eapply HHi4...

      - (* local *)
        repeat inv_scope.
        take (forall x, InMembers x locs -> ~_) and rename it into Hnd'; eauto.

        assert (forall y, Env.In y (Env.from_list (combine (map fst locs) x)) <-> InMembers y locs) as Hsubin'.
        { intros.
          rewrite Env.In_from_list, <-In_InMembers_combine, fst_InMembers; try reflexivity.
          now apply mmap_values, Forall2_length in H0. }

        assert (forall y, FEnv.In y Hi2 -> ~FEnv.In y Hi') as Hdisj1.
        { subst. intros * In1 In2.
          destruct y; apply Hdom in In1; apply H5 in In2.
          - apply IsVar_senv_of_decls in In2. inv In1.
            eapply Hnd'; eauto. rewrite InMembers_app in *.
            rewrite ? in_app_iff, <- ? fst_InMembers. tauto.
          - apply IsLast_senv_of_decls in In2. apply IsLast_IsVar in In1. inv In1.
            eapply Hnd'; eauto. rewrite InMembers_app in *.
            rewrite ? in_app_iff, <- ? fst_InMembers. tauto.
        }

        assert (forall y, FEnv.In y Hi2 -> ~In (var_last_ident y) x) as Hdisj2.
        { subst. intros * In1 In2.
          destruct y; eapply Hdom in In1; inv In1; simpl_In.
          1,2:eapply reuse_idents_st_nIn in H0; eauto; simpl_Forall.
          1,2:contradiction. }

        assert (forall y, Env.In y sub -> ~In y (map fst locs)) as Hsub1.
        { intros ?. rewrite Hsubin. intros Hin1 Hin2. inv Hin1.
          eapply Hnd'; eauto with datatypes. rewrite 2 in_app_iff; eauto with datatypes. }
        assert (forall x1 x2, Env.MapsTo x1 x2 sub -> ~In x2 (map fst locs)) as Hsub2.
        { intros ??. intros Hin1 Hin2.
          eapply Hsubgen in Hin1 as [Hin|(?&?&Hgen)]; subst.
          - simpl_In. eapply Hnd'; eauto using In_InMembers. rewrite 2 in_app_iff; eauto with datatypes.
          - simpl_In. simpl_Forall.
            eapply Fresh.Facts.contradict_AtomOrGensym; eauto using local_not_in_switch_prefs. }

        remember (Env.from_list (combine x (map fst locs))) as revsub.
        remember (fun y => match y with
                        | Var y => obind (Env.find y revsub) (fun x => Hi' (Var x))
                        | Last y => obind (Env.find y revsub) (fun x => Hi' (Last x))
                        end) as Hi2'.

        assert (forall x, FEnv.In x Hi2 -> ~FEnv.In x Hi2') as Hdisj2'.
        { subst. intros * In1 (?&Find2). unfold rename_var in *.
          eapply Hdisj2 in In1 as Nin1.
          cases; (destruct (Env.find _ _) eqn:Find; simpl in *;
                  [apply Env.from_list_find_In, in_combine_l in Find; contradiction
                  |congruence]).
        }

        assert (Hi2 ⊑ Hi2 + Hi2') as Ref.
        { intros ?? Hfind. do 2 esplit; try reflexivity.
          apply FEnv.union2; auto.
          eapply FEnv.not_find_In, Hdisj2'. econstructor; eauto. }

        assert (dom Hi2' (senv_of_decls (map (fun '(x3, (ty, ck, cx, clx)) =>
                                               (rename_var (Env.adds (map fst locs) x sub) x3,
                                                 (ty, rename_clock (Env.adds (map fst locs) x sub) ck, cx, clx))) locs))) as Hdom'.
        { subst; split.
          - intros ?. unfold senv_of_decls. erewrite IsVar_fst, 2 map_map.
            split; [intros (?&Find)|intros In].
            + apply obind_inversion in Find as (?&Find1&Find2).
              apply FEnv.find_In, H5 in Find2. inv Find2. solve_In.
              unfold rename_var, or_default in *.
              apply Env.from_list_find_In in Find1.
              erewrite Env.In_find_adds; eauto using combine_permute.
              now apply fst_NoDupMembers.
            + simpl_In.
              assert (FEnv.In (Var i) Hi') as [? Find] by (eapply H5; econstructor; solve_In).
              econstructor.
              rewrite rename_var_idem; eauto using reuse_idents_NoDup.
              * solve_In.
              * apply mmap_values, Forall2_length in H0; auto.
              * now apply fst_NoDupMembers.
          - intros ?. unfold senv_of_decls.
            split; [intros (?&Find)|intros In].
            + apply obind_inversion in Find as (?&Find1&Find2).
              apply FEnv.find_In, H5 in Find2. inv Find2. simpl_In. econstructor. solve_In.
              unfold rename_var, or_default in *.
              apply Env.from_list_find_In in Find1.
              erewrite Env.In_find_adds; eauto using combine_permute.
              now apply fst_NoDupMembers. destruct o; simpl in *; auto.
            + inv In. simpl_In.
              assert (FEnv.In (Last i) Hi') as [? Find].
              { eapply H5. econstructor. solve_In. destruct o; simpl in *; auto. }
              econstructor.
              rewrite rename_var_idem; eauto using reuse_idents_NoDup.
              * solve_In.
              * apply mmap_values, Forall2_length in H0; auto.
              * now apply fst_NoDupMembers.
        }

        eapply mmap_inlinelocal_block_sem with
            (Γ':=Γ'++senv_of_decls locs) (Hi1:=Hi1 + Hi') (Hi2:=Hi2 + Hi2') in H4 as (Hi3&Href1&Hdom1&Hsc1&Hsem1); eauto; clear H.
        + exists Hi3. split; [|split; [|split]]; eauto.
          * etransitivity...
          * rewrite senv_of_decls_app, app_assoc with (n:=senv_of_decls _); eauto.
          * rewrite senv_of_decls_app, app_assoc with (n:=senv_of_decls _); eauto.
        + intros ?. rewrite IsVar_app. intros Hinm1 [Hinm2|Hinm2].
          * eapply Hdisj; eauto.
          * apply IsVar_senv_of_decls in Hinm2. eapply Hnd'; eauto.
            rewrite 2 in_app_iff, <-IsVar_fst; auto.
        + intros ?. rewrite Env.In_adds_spec, Hsubin, IsVar_app, IsVar_senv_of_decls, <-fst_InMembers;
            eauto using mmap_values, Forall2_length.
          apply or_comm.
        + intros ?? Hfind. rewrite InMembers_app, InMembers_senv_of_decls.
         eapply Env.find_adds'_In in Hfind as [Hfind|Hfind]; eauto.
         * eapply in_combine_r in Hfind.
           eapply reuse_idents_gensym in H0. simpl_Forall. destruct H0; eauto.
         * eapply Hsubgen in Hfind as [|]; eauto.
        + intros ??? Hfind Hv.
          erewrite sem_var_disj_union; eauto.
          eapply Env.find_adds'_In in Hfind as [Hfind|Hfind]; eapply sem_var_union in Hv as [Hv|Hv]; eauto.
          * exfalso.
            apply sem_var_In, Hub in Hv.
            take (forall x, InMembers x locs -> ~_) and eapply it; eauto.
            eapply fst_InMembers, InMembers_In_combine; eauto using In_InMembers.
            rewrite app_assoc, in_app_iff. left. rewrite <-map_app, <-IsVar_fst; auto.
          * right. inv Hv. econstructor; eauto. subst.
            erewrite Env.find_In_from_list; eauto using combine_permute, NoDup_NoDupMembers_combine, reuse_idents_NoDup.
          * exfalso. apply Env.find_In, Hsubin in Hfind.
            apply sem_var_In, H5, IsVar_senv_of_decls in Hv.
            take (forall x, InMembers x locs -> ~_) and eapply it...
            rewrite 2 in_app_iff, <-2 IsVar_fst; auto.
        + intros ?? Hfind Hv.
          erewrite sem_var_disj_union; eauto.
          eapply sem_var_union in Hv as [Hv|Hv]; eauto.
          exfalso. apply sem_var_In, H5, IsVar_senv_of_decls in Hv.
          eapply Hnd'; eauto.
          rewrite 2 in_app_iff, <-IsVar_fst; auto.
        + intros ??? Hfind Hv.
          erewrite sem_var_disj_union; eauto.
          eapply Env.find_adds'_In in Hfind as [Hfind|Hfind]; eapply sem_var_union in Hv as [Hv|Hv]; eauto.
          * exfalso.
            apply sem_var_In, Hub in Hv.
            take (forall x, InMembers x locs -> ~_) and eapply it; eauto.
            eapply fst_InMembers, InMembers_In_combine; eauto using In_InMembers.
            rewrite app_assoc, in_app_iff. left. rewrite <-map_app, <-IsVar_fst; auto with senv.
          * right. inv Hv. econstructor; eauto. subst.
            erewrite Env.find_In_from_list; eauto using combine_permute, NoDup_NoDupMembers_combine, reuse_idents_NoDup.
          * exfalso. apply Env.find_In, Hsubin in Hfind.
            apply sem_var_In, H5, IsLast_senv_of_decls in Hv.
            take (forall x, InMembers x locs -> ~_) and eapply it...
            rewrite 2 in_app_iff, <-2 IsVar_fst; auto.
        + intros ?? Hfind Hv.
          erewrite sem_var_disj_union; eauto.
          eapply sem_var_union in Hv as [Hv|Hv]; eauto.
          exfalso. apply sem_var_In, H5, IsLast_senv_of_decls in Hv.
          eapply Hnd'; eauto.
          rewrite 2 in_app_iff, <-IsVar_fst; auto with senv.
        + rewrite app_assoc. eapply NoDupScope_NoDupMembers; eauto.
          intros * InM1 In2. eapply Hnd'; eauto.
          rewrite app_assoc, <-map_app, in_app_iff; auto.
        + simpl_app. simpl_Forall.
          eapply NoDupLocals_incl'. 4:eauto. all:eauto using local_not_in_switch_prefs.
          intros *. repeat rewrite in_app_iff.
          intros [|[|[In|[In|In]]]]; auto.
          * clear - In. simpl_In. left. right. right. right. solve_In.
          * clear - H0 H10 In. simpl_In.
            eapply reuse_idents_find in H0 as (?&?&?&Reu&Find); eauto using In_InMembers.
            unfold rename_var. rewrite Find.
            eapply reuse_ident_gensym in Reu as [|]; subst; eauto.
            left. right. right. right. solve_In.
        + rewrite app_assoc. eapply local_hist_dom_ub; eauto.
        + rewrite app_assoc.
          eapply local_hist_dom; eauto.
        + rewrite app_assoc.
          eapply local_hist_sc_vars; eauto using dom_dom_ub. reflexivity.
          *{ intros * In1 In2. apply IsVar_fst in In2. simpl_In.
             eapply reuse_idents_find' in H0 as (?&?&?&V1&Fol1&Fol2&Reu&Find); eauto using In_InMembers.
             unfold rename_var in Hin. erewrite Find in Hin. simpl in *. simpl_Forall.
             eapply reuse_ident_st_nIn in Reu as Nin; eauto.
             eapply Nin; eauto using st_follows_In. }
          *{ split.
             - assert (forall x, InMembers x locs -> ~FEnv.In (Var x) Hi2) as Hdisj3.
               { intros ? Hinm Henv. eapply Hdom in Henv.
                 eapply Hnd'; eauto.
                 rewrite <-2 map_app, <-IsVar_fst, 2 IsVar_app. apply IsVar_app in Henv as [|]; auto. }

               intros * Ck Var. inv Ck. simpl_In.

               take (sc_vars (senv_of_decls _) _ _) and destruct it as (Hsc2&_).
               rewrite <-disjoint_union_rename_in_clock; auto.
               eapply rename_clock_sem, rename_clock_sem
                 with (Hi':= var_history (Hi2 + _)). 3,6:constructor; reflexivity.
               + intros * Hs Hvar. rewrite sem_var_history in *.
                 apply sem_var_union in Hvar as [Hvar|Hvar].
                 * exfalso. eapply Hdisj3; eauto using sem_var_In.
                   apply Hsubin'. econstructor; eauto.
                 * apply Env.from_list_find_In in Hs.
                   inv Hvar. econstructor; eauto.
                   eapply FEnv.union3'. erewrite Env.find_In_from_list; eauto using combine_permute, NoDup_NoDupMembers_combine, reuse_idents_NoDup.
               + intros * Hs Hvar. rewrite sem_var_history in *.
                 apply sem_var_union in Hvar as [Hvar|Hvar].
                 * apply sem_var_disj_union; eauto.
                 * exfalso.
                   eapply Env.Props.P.F.not_find_in_iff; eauto.
                   eapply Hsubin', IsVar_senv_of_decls, H5; eauto using sem_var_In.
               + intros * Hs Hvar. rewrite sem_var_history in *.
                 apply sem_var_union in Hvar as [Hvar|Hvar].
                 * eapply sem_var_disj_union; eauto.
                 * exfalso. apply sem_var_In, H5, IsVar_senv_of_decls, Hnd' in Hvar.
                   eapply Hvar. rewrite 2 in_app_iff. right; left. apply IsVar_fst, Hsubin. econstructor; eauto.
               + intros * Hs Hvar. rewrite sem_var_history in *.
                 apply sem_var_union in Hvar as [Hvar|Hvar].
                 * eapply sem_var_disj_union; eauto.
                   left. eapply Hnsvar; eauto.
                   apply sem_var_In, Hub, IsVar_app in Hvar as [|Hvar]; auto with datatypes.
                   apply Hsubin, Env.Props.P.F.in_find_iff in Hvar. contradiction.
                 * eapply sem_var_disj_union; eauto.
               + eapply Hsc2; eauto. econstructor; solve_In. auto.
                 assert (Reus:=H0). eapply reuse_idents_find in H0 as (?&?&?&Reu&Find); eauto using In_InMembers.
                 apply Env.find_adds'_In in Find as [Find|Find]. 2:rewrite Env.gempty in Find; inv Find.
                 apply sem_var_union in Var as [Var|Var].
                 * exfalso. eapply sem_var_In, Hdisj2 in Var.
                   eapply Var; eauto. unfold rename_var.
                   erewrite Env.In_find_adds; eauto using in_combine_r.
                   now apply fst_NoDupMembers.
                 * eapply sem_var_union3'. inv Var.
                   apply obind_inversion in H0 as (?&Find'&?).
                   rewrite rename_var_idem in Find'; eauto using reuse_idents_NoDup.
                   -- inv Find'; econstructor; eauto.
                   -- solve_In.
                   -- apply mmap_values, Forall2_length in Reus; auto.
                   -- now apply fst_NoDupMembers.
             - assert (forall x, InMembers x locs -> ~FEnv.In (Var x) Hi2) as Hdisj3.
               { intros ? Hinm Henv. eapply Hdom in Henv.
                 eapply Hnd'; eauto.
                 rewrite <-2 map_app, <-IsVar_fst, 2 IsVar_app. apply IsVar_app in Henv as [|]; auto. }

               intros * Ck L Var. inv Ck. inv L. simpl_In.
               assert (length (map fst locs) = length x) as Len.
               { apply mmap_values, Forall2_length in H0; auto. }
               assert (i1 = i); subst.
               { eapply rename_var_injective in H2; eauto using reuse_idents_NoDup.
                 + clear - Hin1. solve_In.
                 + clear - Hin0. solve_In.
                 + now apply fst_NoDupMembers.
               }
               eapply NoDupMembers_det in Hin1; eauto. inv Hin1.

               take (sc_vars (senv_of_decls _) _ _) and destruct it as (_&Hsc2).
               rewrite <-disjoint_union_rename_in_clock; auto.
               eapply rename_clock_sem, rename_clock_sem
                 with (Hi':= var_history (Hi2 + _)). 3,6:constructor; reflexivity.
               + intros * Hs Hvar. rewrite sem_var_history in *.
                 apply sem_var_union in Hvar as [Hvar|Hvar].
                 * exfalso. eapply Hdisj3; eauto using sem_var_In.
                   apply Hsubin'. econstructor; eauto.
                 * apply Env.from_list_find_In in Hs.
                   inv Hvar. econstructor; eauto.
                   eapply FEnv.union3'. erewrite Env.find_In_from_list; eauto using combine_permute, NoDup_NoDupMembers_combine, reuse_idents_NoDup.
               + intros * Hs Hvar. rewrite sem_var_history in *.
                 apply sem_var_union in Hvar as [Hvar|Hvar].
                 * apply sem_var_disj_union; eauto.
                 * exfalso.
                   eapply Env.Props.P.F.not_find_in_iff; eauto.
                   eapply Hsubin', IsVar_senv_of_decls, H5; eauto using sem_var_In.
               + intros * Hs Hvar. rewrite sem_var_history in *.
                 apply sem_var_union in Hvar as [Hvar|Hvar].
                 * eapply sem_var_disj_union; eauto.
                 * exfalso. apply sem_var_In, H5, IsVar_senv_of_decls, Hnd' in Hvar.
                   eapply Hvar. rewrite 2 in_app_iff. right; left. apply IsVar_fst, Hsubin. econstructor; eauto.
               + intros * Hs Hvar. rewrite sem_var_history in *.
                 apply sem_var_union in Hvar as [Hvar|Hvar].
                 * eapply sem_var_disj_union; eauto.
                   left. eapply Hnsvar; eauto.
                   apply sem_var_In, Hub, IsVar_app in Hvar as [|Hvar]; auto with datatypes.
                   apply Hsubin, Env.Props.P.F.in_find_iff in Hvar. contradiction.
                 * eapply sem_var_disj_union; eauto.
               + eapply Hsc2; eauto. 1,2:(econstructor; solve_In; auto).
                 assert (Reus:=H0). eapply reuse_idents_find in H0 as (?&?&?&Reu&Find); eauto using In_InMembers.
                 apply Env.find_adds'_In in Find as [Find|Find]. 2:rewrite Env.gempty in Find; inv Find.
                 apply sem_var_union in Var as [Var|Var].
                 * exfalso. eapply sem_var_In, Hdisj2 in Var.
                   eapply Var; eauto. unfold rename_var.
                   erewrite Env.In_find_adds; eauto using in_combine_r.
                   now apply fst_NoDupMembers.
                 * eapply sem_var_union3'. inv Var.
                   apply obind_inversion in H0 as (?&Find'&?).
                   rewrite rename_var_idem in Find'; eauto using reuse_idents_NoDup.
                   -- inv Find'; econstructor; eauto.
                   -- solve_In.
                   -- now apply fst_NoDupMembers.
           }
        + eauto using reuse_idents_st_valid.
        + rewrite app_assoc, map_app, Forall_app. split.
          * simpl_Forall. eapply mmap_st_follows in H0; eauto using st_follows_In.
            simpl_Forall; eauto using reuse_ident_st_follows.
          * simpl_Forall. simpl_In.
            eapply reuse_idents_find_follows in H0 as (?&?&?&Fol1&Fol2&Reu&Find); eauto using In_InMembers.
            unfold rename_var. rewrite Find.
            eapply reuse_ident_st_In in Reu; eauto using st_follows_In.
    Qed.

    Lemma inlinelocal_node_sem : forall f n ins outs,
        Ordered_nodes (Global G1.(types) G1.(externs) (n::G1.(nodes))) ->
        Ordered_nodes (Global G2.(types) G2.(externs) ((inlinelocal_node n)::G2.(nodes))) ->
        sem_node_ck (Global G1.(types) G1.(externs) (n::G1.(nodes))) f ins outs ->
        sem_node_ck (Global G2.(types) G2.(externs) ((inlinelocal_node n)::G2.(nodes))) f ins outs.
    Proof with eauto.
      intros * Hord1 Hord2 Hsem.

      inv Hsem; rename H0 into Hfind; simpl in Hfind. destruct (ident_eq_dec (n_name n) f).
      - erewrite find_node_now in Hfind; eauto. inv Hfind.
        (*The semantics of equations can be given according to G only *)
        assert (~Is_node_in_block (n_name n0) (n_block n0)) as Blk.
        { inv Hord1. destruct H6 as (Hisin&_). intro contra. eapply Hisin in contra as [? _]; auto. }
        eapply sem_block_ck_cons1 in Blk; eauto. clear H3.

        replace {| types := types G1; nodes := nodes G1 |} with G1 in Blk by (destruct G1; auto).
        pose proof (n_nodup n0) as (Hnd1&Hnd2).
        pose proof (n_good n0) as (Hgood1&Hgood2&_).
        pose proof (n_syn n0) as Hsyn. inversion_clear Hsyn as [?? Hsyn2 _].
        take (clocked_node _ _ _) and destruct it as (Hdom1&Hsc1).
        destruct (inlinelocal_block
                    (Env.empty _) (n_block n0)
                    {| fresh_st := Fresh.init_st; used := PSP.of_list (map fst (n_in n0) ++ map fst (n_out n0))|})
          as ((locs'&blks')&st') eqn:Il. assert (Il':=Il).
        eapply inlinelocal_block_sem
                 with (Γ:=senv_of_ins (n_in n0) ++ senv_of_decls (n_out n0)) (Γ':=[]) (Γ'':=[])
          in Il' as (Hf&Href&Hdom&Hsc&Hsem); repeat rewrite app_nil_r; eauto.
        econstructor; eauto.
        + erewrite find_node_now; eauto.
        + eauto.
        + eauto.
        + apply sem_block_ck_cons2; simpl...
          2:{ eapply find_node_not_Is_node_in in Hord2. contradict Hord2.
            2:erewrite find_node_now; eauto. eauto. }
          assert (FEnv.Equiv (@EqSt _) Hf (H + restrict Hf (senv_of_decls locs'))) as Heq.
          { intros ?. destruct (Hf x) eqn:Hfind.
            - unfold restrict, FEnv.restrict. destruct (existsb (fun y : var_last => y ==b x) (vars_of_senv (senv_of_decls locs'))) eqn:Ex.
              + erewrite FEnv.union3'; eauto using FEnv.restrict_find. 2:setoid_rewrite Ex; eauto.
                reflexivity.
              + assert (FEnv.In x H) as (?&Hfind').
                { destruct Hdom as (D2&DL2). apply FEnv.find_In in Hfind.
                  apply existsb_Forall, forallb_Forall, Forall_flat_map in Ex.
                  destruct x; apply Hdom1; [apply D2 in Hfind|apply DL2 in Hfind].
                  1,2:simpl in *. apply IsVar_app in Hfind as [|Hfind]; auto. 2:apply IsLast_app in Hfind as [|Hfind]; auto.
                  - inv Hfind. simpl_In. unfold senv_of_decls in *. simpl_Forall.
                    rewrite equiv_decb_refl in H4. inv H4.
                  - inv Hfind. simpl_In. unfold senv_of_decls in *. simpl_Forall.
                    destruct o; simpl in *; try congruence. simpl_Forall.
                    rewrite equiv_decb_refl in H7. inv H7.
                }
                assert (Hfind'':=Hfind'). apply Href in Hfind'' as (?&?&Hfind''). rewrite Hfind in Hfind''; inv Hfind''.
                erewrite FEnv.union2; eauto using FEnv.restrict_find_None1.
                2:setoid_rewrite Ex; auto.
                constructor. now symmetry.
            - replace ((_ + _) x) with (@None (Stream svalue)); [constructor|].
              symmetry. apply FEnv.union_None; split; eauto using FEnv.restrict_find_None2, FEnv.refines_None.
          }
          rewrite Il in *. simpl in *.
          econstructor. eapply Sscope with (Hi':=restrict Hf (senv_of_decls locs')).
          *{ destruct Hdom as (D&DL). split; intros *; unfold restrict.
             1,2:rewrite FEnv.restrict_In.
             - rewrite D, vars_of_senv_Var, IsVar_app.
               split; intros; repeat (progress destruct_conjs || take (_ \/ _) and destruct it); auto.
             - rewrite DL, vars_of_senv_Last, IsLast_app.
               split; intros; repeat (progress destruct_conjs || take (_ \/ _) and destruct it); auto.
           }
          * eapply sc_vars_morph. 1,3:reflexivity. eauto.
            eapply sc_vars_incl; [|eauto]. unfold senv_of_decls, senv_of_tyck. solve_incl_app.
          * destruct G2; simpl in *. simpl_Forall.
            eapply sem_block_ck_morph; eauto. reflexivity.
        + simpl. constructor; simpl; auto.
        + intros * _ In. inv In. inv H0.
        + intros ?. rewrite Env.Props.P.F.empty_in_iff. split; intros In; inv In. inv H0.
        + intros * Find. unfold Env.MapsTo in Find. rewrite Env.gempty in Find. congruence.
        + intros * Find. rewrite Env.gempty in Find. congruence.
        + intros * Find. rewrite Env.gempty in Find. congruence.
        + apply node_NoDupMembers.
        + apply node_NoDupLocals.
        + now rewrite map_app, map_fst_senv_of_ins, map_fst_senv_of_decls.
        + auto using dom_dom_ub.
        + intros ? In. apply In_of_list in In. now simpl_Forall.
        + simpl_Forall. right. apply In_of_list.
          rewrite <-map_fst_senv_of_ins, <-map_fst_senv_of_decls, <-map_app. solve_In.
      - erewrite find_node_other in Hfind; eauto.
        eapply sem_node_ck_cons2...
        destruct G2; apply HGref.
        destruct G1; econstructor...
        eapply sem_block_ck_cons1; eauto using find_node_later_not_Is_node_in.
    Qed.

  End inlinelocal_node_sem.

  Lemma inlinelocal_global_refines : forall G,
      wc_global G ->
      global_sem_refines G (inlinelocal_global G).
  Proof with eauto using wc_global_Ordered_nodes.
    intros [].
    induction nodes0; intros * Hwc; simpl.
    - apply global_sem_ref_nil.
    - assert (Hwc':=Hwc).
      eapply Clocking.inlinelocal_global_wc, wc_global_Ordered_nodes in Hwc' ;
        unfold inlinelocal_global in Hwc'; simpl in Hwc'.
      apply global_sem_ref_cons with (f:=n_name a)...
      + inv Hwc. eapply IHnodes0...
      + intros ins outs Hsem; simpl in *.
        change types0 with ((Global types0 externs0 (map inlinelocal_node nodes0)).(types)).
        eapply inlinelocal_node_sem with (G1:=Global types0 externs0 nodes0)...
        1,2:inv Hwc...
  Qed.

  Theorem inlinelocal_global_sem : forall G f ins outs,
      wc_global G ->
      sem_node_ck G f ins outs ->
      sem_node_ck (inlinelocal_global G) f ins outs.
  Proof.
    intros.
    eapply inlinelocal_global_refines in H; eauto.
    specialize (H f ins outs); auto.
  Qed.

End ILCORRECTNESS.

Module ILCorrectnessFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks : CLOCKS Ids Op OpAux)
       (CStr : COINDSTREAMS Ids Op OpAux Cks)
       (Senv : STATICENV Ids Op OpAux Cks)
       (Syn : LSYNTAX Ids Op OpAux Cks Senv)
       (Ty : LTYPING Ids Op OpAux Cks Senv Syn)
       (Clo : LCLOCKING Ids Op OpAux Cks Senv Syn)
       (Lord : LORDERED Ids Op OpAux Cks Senv Syn)
       (Sem : LSEMANTICS Ids Op OpAux Cks Senv Syn Lord CStr)
       (LClockSem : LCLOCKEDSEMANTICS Ids Op OpAux Cks Senv Syn Clo Lord CStr Sem)
       (IL  : INLINELOCAL Ids Op OpAux Cks Senv Syn)
       <: ILCORRECTNESS Ids Op OpAux Cks CStr Senv Syn Ty Clo Lord Sem LClockSem IL.
  Include ILCORRECTNESS Ids Op OpAux Cks CStr Senv Syn Ty Clo Lord Sem LClockSem IL.
End ILCorrectnessFun.
