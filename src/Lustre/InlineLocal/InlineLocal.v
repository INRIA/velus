From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Velus Require Import Common.
From Velus Require Import CommonTyping.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Fresh.
From Velus Require Import StaticEnv.
From Velus Require Import Lustre.LSyntax.
From Velus Require Import Lustre.SubClock.SubClock.

(** * Remove Local Blocks *)

Module Type INLINELOCAL
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Import Cks : CLOCKS Ids Op OpAux)
       (Import Senv : STATICENV Ids Op OpAux Cks)
       (Import Syn : LSYNTAX Ids Op OpAux Cks Senv).

  (** ** Rename some variables *)

  Module Import SC := SubClockFun Ids Op OpAux Cks Senv Syn.

  Definition rename_in_clock := subclock_clock Cbase.
  Definition rename_in_exp := subclock_exp Cbase.
  Definition rename_in_equation := subclock_equation Cbase.

  (** ** More properties *)

  Fact not_in_union_rename1 : forall x sub sub',
      ~Env.In x sub ->
      rename_var (Env.union sub sub') x = rename_var sub' x.
  Proof.
    unfold rename_var.
    intros * Hnin.
    eapply Env.Props.P.F.not_find_in_iff in Hnin.
    destruct (Env.find x (Env.union sub sub')) eqn:Hfind.
    - eapply Env.union_find4 in Hfind as [Hfind|Hfind]; congruence.
    - eapply Env.union_find_None in Hfind as (Hfind1&Hfind2).
      now rewrite Hfind2.
  Qed.

  Corollary not_in_union_map_rename1 : forall xs sub sub',
      Forall (fun x => ~Env.In x sub) xs ->
      map (rename_var (Env.union sub sub')) xs = map (rename_var sub') xs.
  Proof.
    induction xs; intros * Hf; inv Hf; simpl; f_equal; auto using not_in_union_rename1.
  Qed.

  Fact not_in_union_rename2 : forall x sub sub',
      ~Env.In x sub' ->
      rename_var (Env.union sub sub') x = rename_var sub x.
  Proof.
    unfold rename_var.
    intros * Hnin.
    destruct (Env.find x (Env.union sub sub')) eqn:Hfind.
    - eapply Env.union_find4 in Hfind as [Hfind|Hfind].
      + now rewrite Hfind.
      + exfalso.
        eapply Env.Props.P.F.not_find_in_iff in Hnin. congruence.
    - eapply Env.union_find_None in Hfind as (Hfind1&Hfind2).
      now rewrite Hfind1.
  Qed.

  Corollary not_in_union_map_rename2 : forall xs sub sub',
      Forall (fun x => ~Env.In x sub') xs ->
      map (rename_var (Env.union sub sub')) xs = map (rename_var sub) xs.
  Proof.
    induction xs; intros * Hf; inv Hf; simpl; f_equal; auto using not_in_union_rename2.
  Qed.

  Lemma disjoint_union_rename_var : forall (sub1 sub2: Env.t ident) x,
      (forall x, Env.In x sub1 -> ~Env.In x sub2) ->
      (forall x y, Env.MapsTo x y sub1 -> ~Env.In y sub2) ->
      rename_var sub2 (rename_var sub1 x) = rename_var (Env.union sub1 sub2) x.
  Proof.
    unfold rename_var.
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

  Corollary disjoint_union_rename_in_clock : forall (sub1 sub2: Env.t ident) ck,
      (forall x, Env.In x sub1 -> ~Env.In x sub2) ->
      (forall x y, Env.MapsTo x y sub1 -> ~Env.In y sub2) ->
      rename_in_clock sub2 (rename_in_clock sub1 ck) = rename_in_clock (Env.union sub1 sub2) ck.
  Proof.
    intros * Hsub1 Hsub2.
    induction ck; simpl; auto.
    f_equal; auto using disjoint_union_rename_var.
  Qed.

  (** ** Inlining of local blocks *)

  Module Fresh := Fresh.Fresh(Ids).
  Import Fresh Notations Facts Tactics.
  Local Open Scope fresh_monad_scope.

  Definition FreshAnn A := Fresh local A (type * clock).

  Fixpoint inlinelocal_block sub (blk : block) : FreshAnn (list block) :=
    match blk with
    | Beq eq => ret [Beq (rename_in_equation sub eq)]
    | Breset blks er =>
      do blks' <- mmap (inlinelocal_block sub) blks;
      ret [Breset (concat blks') (rename_in_exp sub er)]
    | Blocal (Scope locs _ blks) =>
      let locs' := map (fun '(x, (ty, ck, _, _)) => (x, (ty, (rename_in_clock sub ck)))) locs in
      do (_, sub1) <- fresh_idents_rename locs' (fun sub '(ty, ck) => (ty, rename_in_clock sub ck));
      let sub' := Env.union sub sub1 in
      do blks' <- mmap (inlinelocal_block sub') blks;
      ret (concat blks')
    | _ => (* Should not happen *) ret [blk]
    end.

  Definition inlinelocal_topblock (blk : block) : FreshAnn (list block * list (ident * _)) :=
    match blk with
    | Blocal (Scope locs _ blks) =>
      do blks' <- mmap (inlinelocal_block (@Env.empty _)) blks;
      ret (concat blks', locs)
    | _ =>
      do blks' <- inlinelocal_block (@Env.empty _) blk;
      ret (blks', [])
    end.

  (** ** State properties *)

  Lemma inlinelocal_block_st_follows : forall blk sub blks' st st',
      inlinelocal_block sub blk st = (blks', st') ->
      st_follows st st'.
  Proof.
    induction blk using block_ind2; intros * Hdl; repeat inv_bind; try reflexivity.
    - (* reset *)
      eapply mmap_st_follows in H0; eauto.
      rewrite Forall_forall in *; eauto.
    - (* local *)
      eapply fresh_idents_rename_st_follows in H0; eauto.
      etransitivity; eauto.
      eapply mmap_st_follows in H1; eauto.
      rewrite Forall_forall in *; eauto.
  Qed.

  Lemma inlinelocal_topblock_st_follows : forall blk res st st',
      inlinelocal_topblock blk st = (res, st') ->
      st_follows st st'.
  Proof.
    Opaque inlinelocal_block.
    destruct blk; intros * Hil; try destruct s; repeat inv_bind.
    1-4:eapply inlinelocal_block_st_follows; eauto.
    eapply mmap_st_follows; eauto.
    eapply Forall_forall; intros; eauto using inlinelocal_block_st_follows.
    Transparent inlinelocal_block.
  Qed.

  Global Hint Resolve inlinelocal_block_st_follows : fresh.

  (** ** Wellformedness properties *)

  (** *** VarsDefined *)

  Import Permutation.

  Fact mmap_vars_perm : forall (f : _ -> block -> FreshAnn (list block)) blks sub blks' xs st st',
      Forall
        (fun blk => forall sub blks' xs st st',
             noswitch_block blk ->
             VarsDefined blk xs ->
             NoDupLocals (map fst (Env.elements sub) ++ xs) blk ->
             f sub blk st = (blks', st') ->
             exists ys, Forall2 VarsDefined blks' ys /\ Permutation (concat ys ++ st_ids st) (map (rename_var sub) xs ++ st_ids st')) blks ->
      Forall noswitch_block blks ->
      Forall2 VarsDefined blks xs ->
      Forall (NoDupLocals (map fst (Env.elements sub) ++ concat xs)) blks ->
      mmap (f sub) blks st = (blks', st') ->
      exists ys, Forall2 VarsDefined (concat blks') ys /\ Permutation (concat ys ++ st_ids st) (map (rename_var sub) (concat xs) ++ st_ids st').
  Proof.
    induction blks; intros * Hf Hns Hvars Hnd Hnorm; inv Hf; inv Hns; inv Hvars; inv Hnd; repeat inv_bind; simpl.
    - exists []. split; auto.
    - eapply H1 in H as (ys1&Hvars1&Hperm1); eauto.
      2:eapply NoDupLocals_incl; [|eauto]; solve_incl_app.
      eapply IHblks in H2 as (ys2&Hvars2&Hperm2); eauto. clear IHblks.
      2:eapply Forall_impl; [|eapply H8]; intros; eapply NoDupLocals_incl; [|eauto]; solve_incl_app.
      exists (ys1 ++ ys2). split.
      + apply Forall2_app; auto.
      + rewrite map_app, <-app_assoc, <-Hperm2, Permutation_swap, <-Hperm1, Permutation_swap.
        now rewrite concat_app, <-app_assoc.
  Qed.

  Lemma inlinelocal_block_vars_perm : forall blk sub blks' xs st st',
      noswitch_block blk ->
      VarsDefined blk xs ->
      NoDupLocals (map fst (Env.elements sub) ++ xs) blk ->
      inlinelocal_block sub blk st = (blks', st') ->
      exists ys, Forall2 VarsDefined blks' ys /\ Permutation (concat ys ++ st_ids st) (map (rename_var sub) xs ++ st_ids st').
  Proof.
    induction blk using block_ind2; intros * Hns Hvars Hnd Hdl;
      inv Hns; inv Hvars; inv Hnd; repeat inv_bind.
    - (* equation *)
      destruct eq.
      repeat esplit; simpl; eauto using VarsDefined with datatypes.
      simpl. now rewrite <-app_assoc.
    - (* reset *)
      eapply mmap_vars_perm in H0 as (ys1&Hvars1&Hperm1); eauto.
      do 2 esplit; eauto using VarsDefined.
      simpl. now rewrite <-app_assoc.
    - (* local *)
      inv H1. inv H5. inv_VarsDefined.
      eapply mmap_vars_perm in H4 as (ys1&Hvars1&Hperm1); eauto.
      2:{ simpl_Forall.
          eapply NoDupLocals_incl; [|eauto].
          rewrite <-app_assoc, <-Hperm.
          apply incl_app; try solve [solve_incl_app].
          intros ? Hin. simpl_In.
          eapply Env.elements_complete, Env.union_find4 in Hin0 as [Hfind|Hfind].
          - eapply Env.elements_correct in Hfind.
            apply in_or_app, or_introl; solve_In.
          - eapply fresh_idents_rename_sub1 in H0; eauto. 2:econstructor; eauto.
            rewrite fst_InMembers in H0. simpl_In.
            rewrite Hperm, 2 in_app_iff. right; right. solve_In.
      }
      rewrite Hperm, map_app in Hperm1.
      unfold st_ids in Hperm1. do 1 (erewrite fresh_idents_rename_anns in Hperm1; eauto); simpl in *.
      do 2 esplit; eauto.
      rewrite map_app, not_in_union_map_rename2, not_in_union_map_rename1,
        (Permutation_swap (concat ys1)), <-app_assoc in Hperm1.
      2:{ simpl_Forall; subst.
          intros (?&contra). eapply H13; eauto using In_InMembers.
          apply in_or_app; left. solve_In.
          2:eapply Env.elements_correct; eauto. reflexivity. }
      2:{ simpl_Forall; subst.
          intro contra. eapply fresh_idents_rename_sub1 in contra; eauto.
          rewrite fst_InMembers in contra; simpl_In.
          eapply H13; eauto using In_InMembers, in_or_app. }
      eapply Ker.fresh_idents_rename_ids in H0.
      2:{ apply NoDupMembers_map; auto. intros; destruct_conjs; auto. }
      rewrite H0 in Hperm1. repeat rewrite map_map in Hperm1; simpl in Hperm1.
      rewrite Permutation_swap with (xs:=map _ xs) in Hperm1.
      erewrite map_ext in Hperm1. eapply Permutation_app_inv_l in Hperm1; auto.
      intros; destruct_conjs; auto.
  Qed.

  Lemma inlinelocal_topblock_vars_perm : forall blk blks' vars xs st st',
      noswitch_block blk ->
      VarsDefined blk xs ->
      NoDupLocals xs blk ->
      inlinelocal_topblock blk st = (blks', vars, st') ->
      exists ys, Forall2 VarsDefined blks' ys /\ Permutation (concat ys ++ st_ids st) (xs ++ map fst vars ++ st_ids st').
  Proof.
    Opaque inlinelocal_block.
    destruct blk; intros * Hns Hvars Hnd Hil; try destruct s; repeat inv_bind; simpl.
    1-4:eapply inlinelocal_block_vars_perm in H as (?&?&Hperm); eauto.
    5:(inv Hvars; inv Hnd;
       take (VarsDefinedScope _ _ _) and inv it; inv_VarsDefined;
       take (NoDupScope _ _ _) and inv it; eapply mmap_vars_perm in H as (?&?&Hperm'); eauto).
    1-5:try rewrite rename_vars_empty in Hperm; eauto.
    - rewrite rename_vars_empty in Hperm'; eauto.
      do 2 esplit; eauto. rewrite Hperm', Hperm, <-app_assoc; auto.
    - eapply Forall_forall; intros; eauto using inlinelocal_block_vars_perm.
    - inv Hns; auto.
    - rewrite Env.Props.P.elements_empty; simpl.
      eapply Forall_impl; [|eauto]; intros.
      now rewrite Hperm.
    Transparent inlinelocal_block.
  Qed.

  (** *** GoodLocals *)

  Lemma inlinelocal_block_GoodLocals : forall blk sub blks' st st',
      noswitch_block blk ->
      inlinelocal_block sub blk st = (blks', st') ->
      Forall (GoodLocals local_prefs) blks'.
  Proof.
    induction blk using block_ind2; intros * Hns Hdl; inv Hns; repeat inv_bind.
    - (* equation *)
      repeat constructor.
    - (* reset *)
      repeat constructor. apply Forall_concat.
      eapply mmap_values, Forall2_ignore1 in H0.
      rewrite Forall_forall in *; intros * Hin.
      edestruct H0 as (?&Hin'&?&?&Hdl); eauto.
    - (* local *)
      apply Forall_concat.
      eapply mmap_values, Forall2_ignore1 in H1.
      rewrite Forall_forall in *; intros * Hin.
      edestruct H1 as (?&Hin'&?&?&Hdl); eauto.
  Qed.

  Lemma inlinelocal_topblock_GoodLocals : forall blk blks' vars st st',
      noswitch_block blk ->
      inlinelocal_topblock blk st = (blks', vars, st') ->
      Forall (GoodLocals local_prefs) blks'.
  Proof.
    Opaque inlinelocal_block.
    destruct blk; intros * Hns Hil; try destruct s; repeat inv_bind.
    1-4:eapply inlinelocal_block_GoodLocals; eauto.
    apply Forall_concat.
    eapply mmap_values, Forall2_ignore1 in H. inv Hns.
    rewrite Forall_forall in *; intros * Hin.
    edestruct H as (?&Hin'&?&?&Hdl); eauto using inlinelocal_block_GoodLocals.
    Transparent inlinelocal_block.
  Qed.

  (** *** NoDupLocals *)

  Lemma rename_var_injective : forall sub x y,
      Env.In x sub ->
      Env.In y sub ->
      NoDup (map snd (Env.elements sub)) ->
      rename_var sub x = rename_var sub y ->
      x = y.
  Proof.
    unfold rename_var.
    intros * (?&Hfind1) (?&Hfind2) Hndsub Hren.
    rewrite Hfind1, Hfind2 in Hren; simpl in Hren; inv Hren.
    eapply NoDup_snd_det; eauto using Env.elements_correct.
  Qed.

  Lemma inlinelocal_block_NoDupLocals xs : forall blk sub blks' st st',
      noswitch_block blk ->
      inlinelocal_block sub blk st = (blks', st') ->
      Forall (NoDupLocals xs) blks'.
  Proof.
    induction blk using block_ind2; intros * Hns Hdl; inv Hns; repeat inv_bind.
    - (* equation *)
      repeat constructor.
    - (* reset *)
      repeat constructor.
      eapply mmap_values, Forall2_ignore1 in H0.
      eapply Forall_concat. rewrite Forall_forall in *; intros.
      edestruct H0 as (?&?&?&?&?); eauto.
    - (* local *)
      eapply mmap_values, Forall2_ignore1 in H1.
      eapply Forall_concat. rewrite Forall_forall in *; intros.
      edestruct H1 as (?&?&?&?&?); eauto.
  Qed.

  Lemma inlinelocal_topblock_NoDupLocals xs : forall blk blks' vars st st',
      noswitch_block blk ->
      inlinelocal_topblock blk st = (blks', vars, st') ->
      Forall (NoDupLocals xs) blks'.
  Proof.
    Opaque inlinelocal_block.
    destruct blk; intros * Hns Hil; try destruct s; repeat inv_bind.
    1-4:eapply inlinelocal_block_NoDupLocals; eauto.
    eapply mmap_values, Forall2_ignore1 in H. inv Hns.
    eapply Forall_concat. rewrite Forall_forall in *; intros.
    edestruct H as (?&?&?&?&?); eauto using inlinelocal_block_NoDupLocals.
    Transparent inlinelocal_block.
  Qed.

  Lemma inlinelocal_topblock_incl : forall blk blks' vars st st',
      inlinelocal_topblock blk st = (blks', vars, st') ->
      incl (map fst vars) (map fst (locals blk)).
  Proof.
    Opaque inlinelocal_block.
    destruct blk; intros * Hil; try destruct s; repeat inv_bind.
    1-4:apply incl_nil'.
    erewrite map_app, map_map, map_ext.
    apply incl_appl, incl_refl. intros; destruct_conjs; auto.
    Transparent inlinelocal_block.
  Qed.

  Lemma inlinelocal_topblock_NoDupMembers xs : forall blk blks' vars st st',
      NoDupLocals xs blk ->
      inlinelocal_topblock blk st = (blks', vars, st') ->
      NoDupMembers vars.
  Proof.
    Opaque inlinelocal_block.
    destruct blk; intros * Hnd Hil; inv Hnd; try destruct s; repeat inv_bind; auto.
    1-4:constructor.
    inv H1; auto.
    Transparent inlinelocal_block.
  Qed.

  Lemma inlinelocal_topblock_nIn xs : forall blk blks' vars st st',
      NoDupLocals xs blk ->
      inlinelocal_topblock blk st = (blks', vars, st') ->
      forall x, InMembers x vars -> ~In x xs.
  Proof.
    Opaque inlinelocal_block.
    destruct blk; intros * Hnd Hil; inv Hnd; try destruct s; repeat inv_bind; auto.
    inv H1; auto.
    Transparent inlinelocal_block.
  Qed.

  (** *** No local block *)

  Lemma inlinelocal_block_nolocal : forall blk sub blks' st st',
      noswitch_block blk ->
      inlinelocal_block sub blk st = (blks', st') ->
      Forall nolocal_block blks'.
  Proof.
    induction blk using block_ind2; intros * Hns Hdl; inv Hns; repeat inv_bind.
    - (* equation *)
      repeat constructor.
    - (* reset *)
      repeat constructor.
      eapply mmap_values, Forall2_ignore1 in H0.
      eapply Forall_concat.
      rewrite Forall_forall in *; intros.
      edestruct H0 as (?&?&(?&?&?)); eauto.
    - (* local *)
      eapply mmap_values, Forall2_ignore1 in H1.
      eapply Forall_concat.
      rewrite Forall_forall in *; intros.
      edestruct H1 as (?&?&?&?&Hdl); eauto.
  Qed.

  Lemma inlinelocal_topblock_nolocal : forall blk blks' vars st st',
      noswitch_block blk ->
      inlinelocal_topblock blk st = (blks', vars, st') ->
      Forall nolocal_block blks'.
  Proof.
    Opaque inlinelocal_block.
    destruct blk; intros * Hns Hil; try destruct s; repeat inv_bind.
    1-4:eapply inlinelocal_block_nolocal; eauto.
    eapply mmap_values, Forall2_ignore1 in H. inv Hns.
    eapply Forall_concat.
    rewrite Forall_forall in *; intros.
    edestruct H as (?&?&?&?&Hdl); eauto using inlinelocal_block_nolocal.
    Transparent inlinelocal_block.
  Qed.

  Lemma inlinelocal_topblock_nolast : forall blk blks' vars st st',
      noswitch_block blk ->
      inlinelocal_topblock blk st = (blks', vars, st') ->
      Forall (fun '(_, (_, _, _, o)) => o = None) vars.
  Proof.
    intros * Hns Hil.
    inv Hns; repeat inv_bind; auto.
  Qed.

  (** ** Transformation of node and program *)

  Lemma local_not_in_switch_prefs :
    ~PS.In local switch_prefs.
  Proof.
    unfold switch_prefs, auto_prefs, last_prefs, elab_prefs.
    rewrite 3 PS.add_spec, PSF.singleton_iff.
    pose proof gensym_prefs_NoDup as Hnd. unfold gensym_prefs in Hnd.
    repeat rewrite NoDup_cons_iff in Hnd. destruct_conjs.
    intros [contra|[contra|[contra|contra]]]; subst; rewrite contra in *; eauto 10 with datatypes.
  Qed.

  Program Definition inlinelocal_node (n: @node noswitch_block switch_prefs) : @node nolocal_top_block local_prefs :=
    let res := inlinelocal_topblock (n_block n) init_st in
    {|
      n_name := (n_name n);
      n_hasstate := (n_hasstate n);
      n_in := (n_in n);
      n_out := (n_out n);
      n_block := Blocal
                   (Scope
                      (snd (fst res)++map (fun xtc => (fst xtc, ((fst (snd xtc)), snd (snd xtc), xH, None)))
                           (st_anns (snd res))) []
                      (fst (fst res)));
      n_ingt0 := (n_ingt0 n);
      n_outgt0 := (n_outgt0 n);
    |}.
  Next Obligation.
    pose proof (n_defd n) as (?&Hvars&Hperm).
    pose proof (n_nodup n) as (_&Hndup).
    pose proof (n_syn n) as Hns.
    repeat esplit; eauto.
    destruct (inlinelocal_topblock _ _) as ((?&?)&?) eqn:Hdl.
    eapply inlinelocal_topblock_vars_perm in Hvars as (?&?&Hperm'); eauto.
    2:{ rewrite Hperm.
        eapply NoDupLocals_incl; [|eauto]. solve_incl_app. }
    do 2 econstructor; eauto using incl_nil'. do 2 esplit; eauto.
    unfold st_ids in *. rewrite init_st_anns, app_nil_r in Hperm'.
    erewrite Hperm', map_app; simpl.
    repeat apply Permutation_app_head.
    erewrite map_map; eauto.
  Qed.
  Next Obligation.
    pose proof (n_good n) as (Hgood1&Hgood2&_).
    pose proof (n_nodup n) as (Hnd1&Hnd2).
    pose proof (n_syn n) as Hsyn.
    repeat rewrite app_nil_r.
    destruct (inlinelocal_topblock _ _) as ((?&?)&st') eqn:Hdl. simpl.
    split; eauto. do 2 constructor; eauto.
    - eapply inlinelocal_topblock_NoDupLocals; eauto.
    - specialize (st_valid_NoDup st') as Hndup.
      apply NoDupMembers_app.
      + eapply inlinelocal_topblock_NoDupMembers; eauto.
      + rewrite fst_NoDupMembers, map_map; eauto.
      + intros * Hinm1 Hinm2.
        rewrite fst_InMembers in Hinm1, Hinm2. rewrite map_map in Hinm2.
        eapply st_valid_AtomOrGensym_nIn in Hinm2; eauto using local_not_in_switch_prefs.
        eapply Forall_forall; [|eapply Hinm1].
        eapply Forall_incl, inlinelocal_topblock_incl; eauto.
        eapply GoodLocals_locals; eauto.
    - intros ? Hinm contra. simpl_Forall.
      apply InMembers_app in Hinm as [Hinm|Hinm].
      + eapply inlinelocal_topblock_nIn; eauto.
      + apply fst_InMembers in Hinm.
        eapply st_valid_AtomOrGensym_nIn; eauto using local_not_in_switch_prefs.
        unfold st_ids. solve_In.
    - constructor.
  Qed.
  Next Obligation.
    pose proof (n_good n) as (Hgood1&Hgood2&Hatom).
    pose proof (n_nodup n) as (Hnd1&Hnd2).
    destruct (inlinelocal_topblock _ _) as ((?&?)&?) eqn:Hdl. simpl.
    pose proof (n_syn n) as Hsyn.
    repeat split; eauto using AtomOrGensym_add.
    do 2 constructor.
    - assert (Hil:=Hdl). specialize (st_valid_prefixed f) as Hpref.
      rewrite map_app, map_map, Forall_app; split; simpl.
      eapply AtomOrGensym_add, Forall_incl, inlinelocal_topblock_incl; eauto.
      eapply GoodLocals_locals; eauto.
      + eapply Forall_impl; [|eauto]; intros; simpl in *.
        right. do 2 eexists; eauto using PSF.add_1.
    - eapply inlinelocal_topblock_GoodLocals; eauto.
  Qed.
  Next Obligation.
    pose proof (n_syn n) as Hsyn.
    destruct (inlinelocal_topblock _ _) as ((?&?)&?) eqn:Hdl.
    constructor.
    - simpl_Forall. apply in_app_iff in H as [|]; simpl_In; auto.
      apply inlinelocal_topblock_nolast in Hdl; auto. simpl_Forall; auto.
    - eapply inlinelocal_topblock_nolocal; eauto.
  Qed.

  Global Program Instance inlinelocal_node_transform_unit: TransformUnit (@node noswitch_block switch_prefs) node :=
    { transform_unit := inlinelocal_node }.

  Global Program Instance inlinelocal_global_without_units : TransformProgramWithoutUnits (@global noswitch_block switch_prefs) (@global nolocal_top_block local_prefs) :=
    { transform_program_without_units := fun g => Global g.(types) g.(externs) [] }.

  Definition inlinelocal_global : @global noswitch_block switch_prefs -> @global nolocal_top_block local_prefs :=
    transform_units.

  (** *** Equality of interfaces *)

  Lemma inlinelocal_global_iface_eq : forall G,
      global_iface_eq G (inlinelocal_global G).
  Proof.
    repeat split; auto.
    intros f. unfold find_node.
    destruct (find_unit f G) as [(?&?)|] eqn:Hfind; simpl.
    - setoid_rewrite find_unit_transform_units_forward; eauto.
      simpl. repeat constructor.
    - destruct (find_unit f (inlinelocal_global G)) as [(?&?)|] eqn:Hfind'; simpl; try constructor.
      eapply find_unit_transform_units_backward in Hfind' as (?&?&?&?); congruence.
  Qed.

End INLINELOCAL.

Module InlineLocalFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks : CLOCKS Ids Op OpAux)
       (Senv : STATICENV Ids Op OpAux Cks)
       (Syn : LSYNTAX Ids Op OpAux Cks Senv)
       <: INLINELOCAL Ids Op OpAux Cks Senv Syn.
  Include INLINELOCAL Ids Op OpAux Cks Senv Syn.
End InlineLocalFun.
