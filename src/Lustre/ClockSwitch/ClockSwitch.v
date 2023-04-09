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

(** * Remove Switches *)

Module Type CLOCKSWITCH
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Import Cks : CLOCKS Ids Op OpAux)
       (Import Senv : STATICENV Ids Op OpAux Cks)
       (Import Syn : LSYNTAX Ids Op OpAux Cks Senv).

  Module Import SC := SubClockFun Ids Op OpAux Cks Senv Syn.

  (** ** Eliminating switches *)

  Module Fresh := Fresh.Fresh(Ids).
  Import Fresh Notations Facts Tactics.
  Local Open Scope fresh_monad_scope.

  Definition FreshAnn A := Fresh switch A (type * clock).

  Section mmap2.
    Import Tactics Notations.
    Open Scope fresh_monad_scope.
    Context {A1 A2 B : Type}.
    Variable k : A1 -> A2 -> FreshAnn B.

    Fixpoint mmap2 a1 a2 :=
      match a1, a2 with
      | hd1::tl1, hd2::tl2 => do b <- k hd1 hd2;
                           do bs <- mmap2 tl1 tl2;
                           ret (b::bs)
      | _, _ => ret nil
      end.

    Fact mmap2_st_follows : forall a1s a2s bs st st',
        mmap2 a1s a2s st = (bs, st') ->
        Forall2 (fun a1 a2 => forall b st st', k a1 a2 st = (b, st') -> st_follows st st') a1s a2s ->
        st_follows st st'.
    Proof.
      induction a1s; intros * Hmap Hforall;
        simpl in *; repeat inv_bind; auto.
      - reflexivity.
      - inv Hforall. repeat inv_bind.
        etransitivity; eauto.
    Qed.

    Fact mmap2_values : forall a1s a2s bs st st',
        length a1s = length a2s ->
        mmap2 a1s a2s st = (bs, st') ->
        Forall3 (fun a1 a2 b => exists st1 st2, k a1 a2 st1 = (b, st2)) a1s a2s bs.
    Proof.
      induction a1s; intros * Hlen Hmmap; simpl in *; repeat inv_bind.
      - destruct a2s; simpl in *; try congruence. constructor.
      - destruct a2s; simpl in *; try congruence.
        repeat inv_bind.
        constructor; eauto.
    Qed.

    Fact mmap2_values' : forall a1s a2s bs st st',
        length a1s = length a2s ->
        (forall a1 a2 b st st', k a1 a2 st = (b, st') -> st_follows st st') ->
        mmap2 a1s a2s st = (bs, st') ->
        Forall3 (fun a1 a2 b => exists st1 st2, st_follows st st1 /\ k a1 a2 st1 = (b, st2)) a1s a2s bs.
    Proof.
      induction a1s; intros * Hlen Hk2 Hmmap; simpl in *; repeat inv_bind.
      - destruct a2s; simpl in *; try congruence. constructor.
      - destruct a2s; simpl in *; try congruence.
        repeat inv_bind.
        constructor; eauto.
        + repeat esplit; [|eauto]. reflexivity.
        + eapply Forall3_impl_In; [|eauto]. intros ??? _ _ _ (?&?&?&?).
          repeat esplit; [|eauto]. etransitivity; eauto.
    Qed.

  End mmap2.

  Definition cond_eq e tx bck : FreshAnn (ident * list (ident * (type * clock)) * list equation) :=
    match e with
    | Evar x (ty, ck) => ret (x, [], [])
    | _ =>
      do xc <- fresh_ident None (tx, bck);
      ret (xc, [(xc, (tx, bck))], [([xc], [e])])
    end.

  Definition new_idents bck xc tx k (ids : static_env) : FreshAnn _ :=
    mmap (fun '(x, ann) => do y <- fresh_ident (Some x) (ann.(typ), bck);
                        ret (x, y, (ann.(typ), Con bck xc (tx, k)))) ids.

  Definition when_free (x y : ident) ty ck xc tx k :=
    Beq ([y], [Ewhen [Evar x (ty, ck)] (xc, tx) k ([ty], Con ck xc (tx, k))]).

  Definition merge_defs sub (y : ident) ty ck xc tx (brs : list (enumtag * Env.t ident)) :=
    Beq ([rename_var sub y], [Emerge (xc, tx)
                                     (map (fun '(k, sub') => (k, [Evar (rename_var sub' y) (ty, Con ck xc (tx, k))])) brs)
                                     ([ty], ck)]).

  Section switch_scope.
    Context {A : Type}.
    Variable f_s : static_env -> A -> FreshAnn A.

    Definition switch_scope (env : static_env) bck sub scop : FreshAnn (scope A) :=
      let 'Scope locs blks := scop in
      let locs' := map (fun '(x, (ty, ck, cx, o)) => (x, (ty, subclock_clock bck sub ck, cx, o))) locs in
      let env := env++senv_of_decls locs in
      do blks' <- f_s env blks;
      ret (Scope locs' blks').

  End switch_scope.

  Fixpoint switch_block (env : static_env) bck sub blk : FreshAnn block :=
    match blk with
    | Beq eq => ret (Beq (subclock_equation bck sub eq))

    | Breset blks er =>
      do blks' <- mmap (switch_block env bck sub) blks;
      ret (Breset blks' (subclock_exp bck sub er))

    | Blocal s =>
        do s' <- switch_scope (fun env => mmap (switch_block env bck sub)) env bck sub s;
        ret (Blocal s')

    | Bswitch ec branches =>
      let vd := vars_defined (Bswitch ec branches) in

      (* Get defined and free variables *)
      let (defs, frees) := partition (fun '(x, _) => PS.mem x vd) env in

      (* Filtering available free variables *)
      let eck := hd Cbase (clockof ec) in
      let frees := List.filter (fun '(_, ann) => ann.(clo) ==b eck) frees in

      (* Transforming the condition *)
      let ec' := subclock_exp bck sub ec in
      let tx := hd OpAux.bool_velus_type (typeof ec') in
      let bck := hd Cbase (clockof ec') in
      do (xcs, condeqs) <- cond_eq ec' tx bck;
      let (xc, xcs) := xcs in

      do xs' <- mmap (fun '(k, _) =>
                       do nfrees <- new_idents bck xc tx k frees;
                       do ndefs <- new_idents bck xc tx k defs;
                       let sub' := Env.from_list (map (fun '(x, y, _) => (x, y)) (nfrees++ndefs)) in
                       ret (k, sub', nfrees, ndefs)
                    ) branches;

      let env := map (fun '(x, ann) => (x, ann_with_clock ann Cbase)) (defs++frees) in
      do blks' <-
         mmap2 (fun '(k, Branch _ blks) '(_, sub', nfrees, ndefs) =>
                  let wheneqs := List.map (fun '(x, y, (ty, _)) => when_free (rename_var sub x) y ty bck xc tx k) nfrees in
                  do blks' <-  mmap (switch_block env (Con bck xc (tx, k)) sub') blks;
                  ret (blks'++wheneqs)
               ) branches xs';
      let mergeeqs := map (fun '(x, ann) => merge_defs sub x ann.(typ) bck xc tx (map (fun '(k, sub, _, _) => (k, sub)) xs')) defs in
      let locs := flat_map (fun '(_, _, nfrees, ndefs) => (map (fun '(_, x, (ty, ck)) => (x, (ty, ck, xH, None))) (nfrees++ndefs))) xs' in
      ret (Blocal (Scope (List.map (fun '(xc, (ty, ck)) => (xc, (ty, ck, xH, None))) xcs++locs) (mergeeqs++concat blks'++map Beq condeqs)))

    | _ => ret blk
    end.

  (** *** Some properties *)

  Lemma switch_not_in_auto_prefs :
    ~PS.In switch auto_prefs.
  Proof.
    unfold auto_prefs, last_prefs, elab_prefs.
    rewrite 2 PSF.add_iff, PSF.singleton_iff.
    pose proof gensym_prefs_NoDup as Hnd. unfold gensym_prefs in Hnd.
    repeat rewrite NoDup_cons_iff in Hnd. destruct_conjs.
    intros [contra|[contra|contra]]; subst; rewrite contra in *; eauto with datatypes.
  Qed.

  Lemma new_idents_old : forall bck xc tx k ids nids st st',
      new_idents bck xc tx k ids st = (nids, st') ->
      map (fun '(x, _, _) => x) nids = map fst ids.
  Proof.
    intros * Hni.
    eapply mmap_values in Hni.
    induction Hni as [|(?&?) ((?&?)&?&?)]; simpl; auto.
    destruct H as (?&?&?); repeat inv_bind.
    f_equal; auto.
  Qed.

  Lemma rename_vars_idem : forall sub xs,
      (forall x, Env.In x sub -> ~In x xs) ->
      map (rename_var sub) xs = xs.
  Proof.
    intros * Hsub.
    induction xs; intros *; simpl; auto.
    rewrite IHxs.
    2:{ intros ? Hin1 Hin2. eapply Hsub; eauto with datatypes. }
    unfold rename_var.
    destruct (Env.find a sub) eqn:Hfind; auto. exfalso.
    apply Env.find_In, Hsub in Hfind.
    eauto with datatypes.
  Qed.

  Corollary rename_vars_empty : forall xs,
      map (rename_var (Env.empty _)) xs = xs.
  Proof.
    intros *.
    apply rename_vars_idem.
    intros ? Hin. apply Env.Props.P.F.empty_in_iff in Hin. inv Hin.
  Qed.

  Lemma switch_block_NoDupMembers_env {A B} pred1 pred2 : forall (env defs frees : list (A * B)),
      NoDupMembers env ->
      Partition pred1 env defs frees ->
      NoDupMembers (defs ++ filter pred2 frees).
  Proof.
    intros * Hnd Hpart.
    apply Partition_Permutation in Hpart. rewrite Hpart in Hnd.
    apply NoDupMembers_app; eauto using NoDupMembers_app_l, NoDupMembers_app_r, NoDupMembers_filter.
    intros ? Hinm1 Hinm2.
    eapply NoDupMembers_app_InMembers in Hnd; eauto using filter_InMembers'.
  Qed.

  (** *** VarsDefinedComp *)

  Import Permutation.

  Lemma new_idents_rename : forall bck xc tx k ids1 ids2 nids1 nids2 sub st1 st2 st3 st4,
      NoDupMembers (ids1++ids2) ->
      new_idents bck xc tx k ids1 st1 = (nids1, st2) ->
      new_idents bck xc tx k ids2 st3 = (nids2, st4) ->
      sub = Env.from_list (map (fun '(x, y, _) => (x, y)) (nids1++nids2)) ->
      map (fun '(_, x, _) => x) nids1 = map (rename_var sub) (map fst ids1) /\
      map (fun '(_, x, _) => x) nids2 = map (rename_var sub) (map fst ids2).
  Proof.
    intros * Hnd Hni1 Hni2 Hs.
    assert (NoDupMembers (map (fun '(x, y, _) => (x, y)) (nids1 ++ nids2))) as Hnd2.
    { erewrite fst_NoDupMembers, map_map, map_ext, map_app, 2 new_idents_old; eauto.
      rewrite <-map_app, <-fst_NoDupMembers; auto.
      intros ((?&?)&?&?); auto. }
    erewrite <-2 new_idents_old; eauto.
    rewrite 2 map_map. split; eapply map_ext_in; intros ((?&?)&?&?) Hin; subst.
    - unfold rename_var.
      erewrite Env.find_In_from_list; eauto. simpl; auto.
      rewrite map_app, in_app_iff. left.
      eapply in_map_iff; do 2 esplit; eauto. auto.
    - unfold rename_var.
      erewrite Env.find_In_from_list; eauto. simpl; auto.
      rewrite map_app, in_app_iff. right.
      eapply in_map_iff; do 2 esplit; eauto. auto.
  Qed.

  Lemma incl_Permutation : forall (xs ys zs : list ident),
      incl xs (ys ++ zs) ->
      (forall x, In x xs <-> In x ys) ->
      NoDup xs ->
      NoDup (ys ++ zs) ->
      Permutation xs ys.
  Proof.
    induction xs; intros * Hincl Hxy Hnd1 Hnd2; inv Hnd1.
    - destruct ys; auto. exfalso.
      specialize (Hxy i) as (_&Hin).
      apply Hin; auto with datatypes.
    - apply incl_cons' in Hincl as (Hin&Hincl); simpl in *.
      assert (In a ys) as Hin'.
      { specialize (Hxy a) as (?&_); auto; subst. }
      apply Add_inv in Hin' as (ys'&Haddy).
      specialize (IHxs ys' zs).
      rewrite IHxs; auto.
      + apply Permutation_Add; auto.
      + intros ? Hinx. apply in_or_app.
        assert (Hiny:=Hinx). apply Hincl, in_app_iff in Hiny as [Hiny|]; auto.
        left. rewrite Add_in in Hiny; eauto. inv Hiny; auto.
        exfalso; eauto.
      + intros x. specialize (Hxy x) as (Hxy&Hyx).
        split; intros Hinx.
        * eapply Add_in in Hxy; eauto. inv Hxy; auto.
          exfalso; eauto.
        * destruct Hyx as [|]; eauto; subst.
          eapply Add_in; eauto with datatypes.
          exfalso.
          apply NoDup_app_l in Hnd2.
          eapply NoDup_Add in Haddy. apply Haddy in Hnd2 as (?&?); eauto.
      + eapply NoDup_cons'. rewrite app_comm_cons, Permutation_Add; eauto.
  Qed.

  Lemma cond_eq_VarsDefinedComp: forall e tx bck xc xcs eqs st st',
      cond_eq e tx bck st = ((xc, xcs), eqs, st') ->
      Forall2 VarsDefinedComp (map Beq eqs) (map (fun '(x, _) => [x])  xcs).
  Proof.
    unfold cond_eq. intros * Hcond.
    cases; repeat inv_bind; simpl; repeat constructor; auto.
  Qed.

  Lemma switch_scope_VarsDefinedComp {A} P_na P_vd P_nd f_switch :
    forall xs env bck sub locs (blk: A) s' st st',
      incl xs (map fst env) ->
      (forall x, Env.In x sub -> InMembers x env) ->
      NoDupMembers env ->
      NoDup xs ->
      noauto_scope P_na (Scope locs blk) ->
      VarsDefinedCompScope P_vd (Scope locs blk) xs ->
      NoDupScope P_nd (map fst env) (Scope locs blk) ->
      switch_scope f_switch env bck sub (Scope locs blk) st = (s', st') ->
      (forall xs env blk' st st',
          incl xs (map fst env) ->
          (forall x, Env.In x sub -> InMembers x env) ->
          NoDupMembers env ->
          NoDup xs ->
          P_na blk ->
          P_vd blk xs ->
          P_nd (map fst env) blk ->
          f_switch env blk st = (blk', st') ->
          P_vd blk' (map (rename_var sub) xs)) ->
      VarsDefinedCompScope P_vd s' (map (rename_var sub) xs).
  Proof.
    intros * Hincl Hsub Hnd1 Hnd2 Hnauto Hvars Hnd3 Hf Hind;
      inv Hnauto; inv Hvars; inv Hnd3; repeat inv_bind.
    take (forall x, InMembers _ _ -> ~ _) and rename it into Hnd'.
    eapply Hind with (xs:=xs++map fst locs) in H; eauto.
    - econstructor; eauto using incl_nil'.
      rewrite map_map, map_ext with (g:=fst). 2:intros; destruct_conjs; auto.
      rewrite map_app, rename_vars_idem with (xs:=map fst locs) in H; auto.
      intros * Hsub' Hnin. eapply Hnd'; apply fst_InMembers; eauto.
    - rewrite map_app, map_fst_senv_of_decls.
      eapply incl_appl'; eauto.
    - intros. rewrite InMembers_app; auto.
    - apply NoDupMembers_app; auto.
      + now apply NoDupMembers_senv_of_decls.
      + intros * Hinm1 Hinm2.
        eapply Hnd', fst_InMembers; eauto. apply InMembers_senv_of_decls; auto.
    - apply NoDup_app'; auto.
      + now apply fst_NoDupMembers.
      + simpl_Forall. eapply Hincl in H0. intros ?.
        eapply Hnd'; eauto. now apply fst_InMembers.
    - now rewrite map_app, map_fst_senv_of_decls.
  Qed.

  Lemma switch_block_VarsDefinedComp : forall blk xs bck sub env blk' st st',
      incl xs (map fst env) ->
      (forall x, Env.In x sub -> InMembers x env) ->
      NoDupMembers env ->
      NoDup xs ->
      noauto_block blk ->
      VarsDefinedComp blk xs ->
      NoDupLocals (map fst env) blk ->
      switch_block env bck sub blk st = (blk', st') ->
      VarsDefinedComp blk' (map (rename_var sub) xs).
  Proof.
    Opaque switch_scope.
    induction blk using block_ind2; intros * Hincl Hsub Hnd1 Hnd2 Hnauto Hvd Hnd3 Hsw;
      inv Hvd; inv Hnd3;
      inversion_clear Hnauto as [|?? Hnauto'|?? Hnauto'|?? Hnauto']; simpl in *; repeat inv_bind.
    - (* equation *)
      destruct eq as (xs&es); simpl.
      constructor.

    - (* reset *)
      rewrite concat_map.
      constructor. simpl_Forall.
      eapply mmap_values, Forall2_swap_args in H0.
      eapply Forall2_trans_ex in H3; eauto. simpl_Forall.
      eapply H; eauto using NoDup_concat.
      etransitivity; eauto using incl_concat.

    - (* switch *)
      destruct (partition _ _) as (defs&frees) eqn:Hpart. eapply partition_Partition in Hpart.
      repeat inv_bind. destruct x; repeat inv_bind.
      assert (Permutation (map fst defs) xs) as Hdefs.
      { clear H1 H.
        assert (Hperm:=Hpart). apply Partition_Permutation in Hperm.
        rewrite Hperm, map_app in Hincl.
        symmetry. eapply incl_Permutation; eauto.
        - assert (VarsDefinedComp (Bswitch ec branches) xs) as Hdef by (constructor; auto).
          assert (NoDupLocals xs (Bswitch ec branches)) as Hnd'.
          { eapply NoDupLocals_incl; [|constructor; eauto].
            now rewrite Hperm, map_app. }
          intros ?; split; intros Hin.
          + eapply VarsDefinedComp_Is_defined in Hdef; eauto.
            apply Is_defined_in_vars_defined in Hdef; simpl in *.
            apply Hincl, in_app_iff in Hin as [|Hin]; auto.
            eapply in_map_iff in Hin as ((?&?)&?&?); subst; simpl in *.
            eapply Partition_Forall2, Forall_forall in Hpart; eauto; simpl in *.
            apply Bool.not_true_is_false, PSF.not_mem_iff in Hpart. congruence.
          + eapply in_map_iff in Hin as ((?&?)&?&?); subst; simpl in *.
            eapply VarsDefinedComp_Is_defined'; eauto.
            eapply Partition_Forall1, Forall_forall in Hpart; eauto; simpl in *.
            eapply PSF.mem_2 in Hpart.
            eapply vars_defined_Is_defined_in; simpl; auto.
        - rewrite <-map_app, <-fst_NoDupMembers, <-Hperm; auto.
      }

      assert (Forall2 (fun blks '(_, _, nfree, ndefs) =>
                           exists ndefs', Forall2 VarsDefinedComp blks (ndefs'++map (fun '(_, x, _) => [x]) nfree)
                                     /\ Permutation (concat ndefs') (map (fun '(_, x, _) => x) ndefs))
                  x3 x) as Hdef'.
      { eapply mmap2_values in H5. eapply mmap_values in H1.
        eapply Forall3_ignore3' with (zs:=x3) in H1.
        2:{ eapply Forall3_length in H5 as (?&?). congruence. }
        2:{ eapply mmap_length in H1; eauto. }
        eapply Forall3_Forall3, Forall3_ignore1 in H1; eauto. clear H5.
        apply Forall2_swap_args. simpl_Forall. clear H1.
        repeat Syn.inv_branch. repeat inv_bind.
        assert (Hnids:=H9). eapply new_idents_rename with (ids1:=(filter _ _)) (ids2:=defs) in H9 as (_&Hdefs'); eauto.
        2:{ apply Partition_Permutation in Hpart. rewrite Hpart in Hnd1.
            apply NoDupMembers_app;
              eauto using NoDupMembers_app_l, NoDupMembers_app_r, NoDupMembers_filter.
            intros ? Hinm1 Hinm2. apply filter_InMembers in Hinm1 as (?&Hinm1&_).
            apply In_InMembers in Hinm1.
            eapply NoDupMembers_app_InMembers in Hnd1; eauto. }
        do 2 esplit. apply Forall2_app.
        - eapply mmap_values, Forall2_swap_args in H8.
          take (Forall2 VarsDefinedComp _ _) and eapply Forall2_trans_ex in it; eauto.
          instantiate (1:=map (map (rename_var _)) x4). simpl_Forall.
          eapply H in H15; eauto.
          + simpl_app. apply incl_appl.
            erewrite map_map, map_ext, Hdefs, <-H4; auto using incl_concat.
            intros; destruct_conjs; auto.
          + intros ? Hin. apply Env.In_from_list, fst_InMembers in Hin.
            erewrite map_map, map_ext, map_app, 2 new_idents_old, <-map_app, <-fst_InMembers in Hin; eauto.
            erewrite fst_InMembers, map_map, map_ext, <-fst_InMembers, Permutation_app_comm; eauto.
            1,2:intros; destruct_conjs; auto.
          + apply NoDupMembers_map; auto.
            eapply switch_block_NoDupMembers_env; eauto.
          + take (Permutation (concat x4) _) and rewrite <-it in Hnd2.
            eauto using NoDup_concat.
          + eapply NoDupLocals_incl; eauto.
            apply Partition_Permutation in Hpart. rewrite Hpart.
            rewrite map_map, 2 map_app.
            apply incl_app; [apply incl_appl|apply incl_appr].
            * erewrite map_ext; try reflexivity. intros (?&?); auto.
            * erewrite map_ext; try eapply incl_map, incl_filter', incl_refl.
              intros (?&?); auto.
        - simpl_Forall. constructor.
        - take (Permutation (concat x4) _) and now rewrite Hdefs', Hdefs, <-it, concat_map.
      } clear H1 H5.

      assert (exists vars',
                 Forall2 (fun blks '(nfree, ndefs) => Forall2 VarsDefinedComp blks (ndefs++nfree)) x3 vars'
                 /\ Permutation (concat (concat (map (fun '(nfree, ndefs) => ndefs ++ nfree) vars')))
                     (concat
                        (map
                           (fun '(_, _, nfrees, ndefs) =>
                              map fst
                                (map (fun '(_, x5, (ty, ck)) => (x5, (ty, ck, 1%positive, @None ident))) (nfrees ++ ndefs))) x)))
        as (vars'&Hdef''&Hperm').
      { clear - Hdef'. induction Hdef'; destruct_conjs; do 2 esplit; try constructor; eauto.
        instantiate (1:=(_,_)); simpl; eauto. simpl.
        repeat rewrite concat_app. simpl_app.
        rewrite H2, H1. rewrite 2 app_assoc. apply Permutation_app_tail.
        rewrite Permutation_app_comm. apply Permutation_app.
        - erewrite <-map_ext, <-map_map, concat_map_singl1, map_map. reflexivity.
          intros; destruct_conjs; eauto.
        - symmetry. erewrite map_map, map_ext. reflexivity.
          intros; destruct_conjs; eauto. }

      do 2 constructor; eauto using incl_nil'. do 2 esplit.
      repeat apply Forall2_app; simpl_Forall.
      + instantiate (1:=map (fun '(x, _) => [rename_var sub x]) defs). simpl_Forall.
        constructor.
      + apply Forall2_concat. instantiate (1:=map (fun '(nfree, ndefs) => ndefs++nfree) vars').
        simpl_Forall; eauto.
      + instantiate (1:=map (fun '(x, _) => [x]) l).
        eapply cond_eq_VarsDefinedComp in H0. simpl_Forall; eauto.
      + rewrite 2 concat_app, map_app. apply Permutation_app; [|rewrite Permutation_app_comm; apply Permutation_app].
        * erewrite map_ext, <-map_map, concat_map_singl1, <-Hdefs, map_map. reflexivity.
          intros; destruct_conjs; auto.
        * erewrite map_ext, <-map_map, concat_map_singl1, map_map. reflexivity.
          intros; destruct_conjs; auto.
        * rewrite flat_map_concat_map, concat_map, map_map; simpl.
          erewrite map_ext with (l:=x); eauto.
          intros; destruct_conjs; auto.

    - (* local *)
      constructor.
      eapply switch_scope_VarsDefinedComp; eauto.
      intros; simpl; destruct_conjs.
      do 2 esplit; eauto. 2:rewrite <-H12, concat_map; reflexivity.
      simpl_Forall.
      eapply mmap_values, Forall2_swap_args in H11.
      eapply Forall2_trans_ex in H9; eauto. simpl_Forall.
      eapply H; eauto.
      + etransitivity; [|eauto]. rewrite <-H12; eauto using incl_concat.
      + rewrite <-H12 in *; eauto using NoDup_concat.
        Transparent switch_scope.
  Qed.

  (* LastsDefined *)

  Lemma switch_block_LastsDefined : forall blk xs bck sub env blk' st st',
      noauto_block blk ->
      LastsDefined blk xs ->
      switch_block env bck sub blk st = (blk', st') ->
      LastsDefined blk' xs.
  Proof.
    induction blk using block_ind2; intros * NoAuto VD Switch; try destruct type0;
      inv NoAuto; inv VD; destruct_conjs; repeat inv_bind.
    - (* equation *) constructor.
    - (* reset *)
      constructor.
      apply mmap_values, Forall2_swap_args in H0.
      eapply Forall2_trans_ex in H4; eauto. simpl_Forall; eauto.
    - (* switch *)
      cases. repeat inv_bind. cases. repeat inv_bind.
      repeat constructor; simpl.
      do 2 esplit. repeat apply Forall2_app.
      + instantiate (1:=map (fun _ => []) l). simpl_Forall. constructor.
      + eapply mmap2_values, Forall3_ignore12 in H4.
        2:{ apply mmap_length in H2; auto. }
        instantiate (1:=map (fun _ => []) (concat x3)).
        simpl_Forall. take (In _ (concat _)) and apply in_concat in it as (?&?&?).
        simpl_Forall. repeat inv_branch. repeat inv_bind.
        take (In _ (_ ++ _)) and apply in_app_iff in it as [|]; simpl_In; [|constructor].
        eapply mmap_values, Forall2_ignore1 in H1. simpl_Forall. eauto.
      + instantiate (1:=map (fun _ => []) x0). simpl_Forall. constructor.
      + rewrite 2 concat_app, 3 concat_map_nil; simpl.
        unfold lasts_of_decls. rewrite map_filter_app, 2 map_filter_nil; auto.
        1,2:simpl_Forall; auto.
        simpl_In; auto.
    - (* local *)
      repeat inv_scope. repeat constructor.
      do 2 esplit; eauto.
      2:{ unfold lasts_of_decls in *. rewrite map_filter_map.
          erewrite map_filter_ext; eauto.
          intros; destruct_conjs; auto. }
      apply mmap_values, Forall2_swap_args in H0.
      eapply Forall2_trans_ex in H2; eauto. simpl_Forall; eauto.
  Qed.

  (** *** Preservation of st_follows *)

  Lemma cond_eq_st_follows : forall e tx bck xcs eqs' st st',
      cond_eq e tx bck st = (xcs, eqs', st') ->
      st_follows st st'.
  Proof.
    unfold cond_eq. intros * Hst.
    cases; repeat inv_bind; eauto using fresh_ident_st_follows.
    reflexivity.
  Qed.

  Lemma new_idents_st_follows : forall ck xc tx k ids nids st st',
      new_idents ck xc tx k ids st = (nids, st') ->
      st_follows st st'.
  Proof.
    intros * Hnids.
    eapply mmap_st_follows in Hnids; eauto.
    eapply Forall_forall; intros (?&?) ?????; repeat inv_bind.
    eapply fresh_ident_st_follows; eauto.
  Qed.

  Global Hint Resolve cond_eq_st_follows new_idents_st_follows : fresh.

  Lemma switch_block_st_follows : forall blk env bck sub blk' st st',
      switch_block env bck sub blk st = (blk', st') ->
      st_follows st st'.
  Proof.
    induction blk using block_ind2; intros * Hst;
      repeat inv_bind; simpl in *; auto.
    - (* equation *) reflexivity.
    - (* last *) reflexivity.
    - (* reset *)
      eapply mmap_st_follows; eauto.
      eapply Forall_impl; [|eauto]; intros; eauto.
    - (* switch *)
      destruct (partition _ _) as (defs&frees).
      repeat inv_bind; destruct x; repeat inv_bind.
      etransitivity; eauto with fresh.
      etransitivity. eapply mmap_st_follows in H1; eauto with fresh.
      { simpl_Forall. destruct b; repeat inv_bind.
        etransitivity; eauto with fresh. }
      eapply mmap2_st_follows in H2; eauto.
      eapply mmap2_values, Forall3_ignore3 in H2.
      2:{ eapply mmap_length in H1; eauto. }
      simpl_Forall. destruct b; repeat inv_bind. simpl_Forall.
      eapply mmap_st_follows in H6; eauto.
      simpl_Forall; eauto.
    - reflexivity.
    - (* local *)
      eapply mmap_st_follows; eauto.
      simpl_Forall; eauto.
  Qed.

  Corollary switch_scope_st_follows : forall blk env bck sub blk' st st',
      switch_scope (fun env => mmap (switch_block env bck sub)) env bck sub blk st = (blk', st') ->
      st_follows st st'.
  Proof.
    intros * Hswitch; destruct blk; repeat inv_bind.
    eapply mmap_st_follows; eauto. simpl_Forall; eauto using switch_block_st_follows.
  Qed.

  (** *** NoDup *)

  Lemma cond_eq_NoDupMembers : forall e tx bck xc xcs eqs st st',
      cond_eq e tx bck st = (xc, xcs, eqs, st') ->
      NoDupMembers xcs.
  Proof.
    unfold cond_eq. intros * Hcond.
    cases; repeat inv_bind; repeat constructor; intros [].
  Qed.

  Lemma cond_eq_st_ids : forall e tx bck xc xcs eqs st st',
      cond_eq e tx bck st = (xc, xcs, eqs, st') ->
      Permutation (st_ids st') (st_ids st ++ map fst xcs).
  Proof.
    unfold cond_eq. intros * Hcond.
    cases; repeat inv_bind; simpl in *;
      rewrite Permutation_app_comm; simpl.
    3:reflexivity.
    all:symmetry; eapply fresh_ident_vars_perm; eauto.
  Qed.

  Corollary cond_eq_incl : forall e tx bck xc xcs eqs st st',
      cond_eq e tx bck st = (xc, xcs, eqs, st') ->
      incl (map fst xcs) (st_ids st').
  Proof.
    intros * Hcond.
    apply cond_eq_st_ids in Hcond. rewrite Hcond.
    apply incl_appr, incl_refl.
  Qed.

  Lemma new_idents_st_ids : forall ck xc tx k ids nids st st',
      new_idents ck xc tx k ids st = (nids, st') ->
      Permutation (st_ids st') (st_ids st++map (fun '(_, x, _) => x) nids).
  Proof.
    induction ids as [|(?&?)]; intros * Hni; repeat inv_bind; auto. now rewrite app_nil_r.
    eapply fresh_ident_vars_perm in H.
    rewrite <-Permutation_middle, IHids, <-H; simpl; eauto.
  Qed.

  Lemma new_idents_st_ids' {A} : forall (branches : list (_ * A)) ck xc tx frees defs nids st st',
      mmap
        (fun '(k, _) =>
           do nfrees <- new_idents ck xc tx k frees;
           do ndefs <- new_idents ck xc tx k defs;
           ret (k, Env.from_list (map (fun '(x, y2, _) => (x, y2)) (nfrees ++ ndefs)), nfrees, ndefs)) branches st = (nids, st') ->
      Permutation (st_ids st')
                  (st_ids st ++ map fst (flat_map (fun '(_, _, nfrees, ndefs) => map (fun '(_, x4, (ty, ck)) => (x4, (ty, ck, xH))) (nfrees ++ ndefs)) nids)).
  Proof.
    induction branches as [|(?&?)]; intros * Hmmap; repeat inv_bind; simpl; auto. now rewrite app_nil_r.
    repeat rewrite map_app. repeat rewrite <-app_assoc.
    erewrite app_assoc, map_map, map_ext, <-new_idents_st_ids; eauto.
    erewrite app_assoc, map_map, map_ext, <-new_idents_st_ids; eauto.
    1,2:intros ((?&?)&?&?); auto.
  Qed.

  Fact switch_blocks_NoDupLocals' : forall blks xs env bck sub blks' st st',
      Forall
        (fun blk => forall xs env bck sub blk' st st',
             NoDup xs ->
             NoDupLocals xs blk ->
             Forall (fun x : ident => AtomOrGensym auto_prefs x \/ In x (st_ids st)) xs ->
             GoodLocals auto_prefs blk ->
             switch_block env bck sub blk st = (blk', st') ->
             NoDupLocals xs blk') blks ->
      NoDup xs ->
      Forall (NoDupLocals xs) blks ->
      Forall (fun x => AtomOrGensym auto_prefs x \/ In x (st_ids st)) xs ->
      Forall (GoodLocals auto_prefs) blks ->
      mmap (switch_block env bck sub) blks st = (blks', st') ->
      Forall (NoDupLocals xs) blks'.
  Proof.
    intros * Hf Hnd1 Hnd2 Hat1 Hgood Hmmap.
    eapply mmap_values_follows, Forall2_ignore1 in Hmmap;
      eauto using switch_block_st_follows.
    simpl_Forall.
    eapply Hf in H2; eauto.
    simpl_Forall. destruct Hat1; auto.
    right. eapply incl_map; eauto using st_follows_incl, switch_block_st_follows.
  Qed.

  Lemma switch_scope_NoDupScope {A} P_nd P_good f_switch :
    forall locs (blk: A) xs env bck sub s' st st',
      NoDup xs ->
      NoDupScope P_nd xs (Scope locs blk) ->
      Forall (fun x => AtomOrGensym auto_prefs x \/ In x (st_ids st)) xs ->
      GoodLocalsScope P_good auto_prefs (Scope locs blk) ->
      switch_scope f_switch env bck sub (Scope locs blk) st = (s', st') ->
      (forall xs env blk' st st',
          NoDup xs ->
          P_nd xs blk ->
          Forall (fun x => AtomOrGensym auto_prefs x \/ In x (st_ids st)) xs ->
          P_good blk ->
          f_switch env blk st = (blk', st') ->
          P_nd xs blk') ->
      NoDupScope P_nd xs s'.
  Proof.
    intros * Hnd1 Hnd2 Hat Hgood Hs; inv Hnd2; inv Hgood; repeat inv_bind.
    constructor.
    + eapply H0; eauto.
      * apply NoDup_app'; auto. apply fst_NoDupMembers, NoDupMembers_map; auto.
        intros; destruct_conjs; auto.
        eapply Forall_forall; intros ? Hinm1 Hinm2; simpl_In.
        eapply H4; eauto using In_InMembers.
      * erewrite map_map, map_ext; eauto. intros; destruct_conjs; auto.
      * apply Forall_app; split; auto.
        simpl_Forall; auto.
    + apply NoDupMembers_map; auto.
      intros; destruct_conjs; auto.
    + intros ? Hinm Hinm2. eapply H4; eauto.
      erewrite fst_InMembers, map_map, map_ext, <-fst_InMembers in Hinm; eauto.
      intros; destruct_conjs; auto.
  Qed.

  Lemma switch_block_NoDupLocals : forall blk xs env bck sub blk' st st',
      NoDup xs ->
      NoDupLocals xs blk ->
      Forall (fun x => AtomOrGensym auto_prefs x \/ In x (st_ids st)) xs ->
      GoodLocals auto_prefs blk ->
      switch_block env bck sub blk st = (blk', st') ->
      NoDupLocals xs blk'.
  Proof.
    Opaque switch_scope.
    induction blk using block_ind2; intros * Hnd1 Hnd2 Hat1 Hgood Hswi;
      inv Hgood; inv Hnd2; repeat inv_bind; simpl in *; auto using NoDupLocals.

    - (* reset *)
      constructor.
      eapply switch_blocks_NoDupLocals'; eauto.

    - (* switch *)
      destruct (partition _ _) as (defs&frees). repeat inv_bind; destruct x; repeat inv_bind.
      simpl. repeat rewrite <-flat_map_app. repeat rewrite map_app.

      remember (xs ++ map fst l ++
                   map fst
                   (flat_map
                      (fun '(_, _, nfrees, ndefs) =>
                         map (fun '(_, x4, (ty, ck0)) => (x4, (ty, ck0, 1%positive))) (nfrees ++ ndefs)) x)) as xs'.
      assert (NoDup xs') as Hnd1'.
      { subst.
        specialize (Ker.st_valid_NoDup x2) as Hnd.
        erewrite new_idents_st_ids', cond_eq_st_ids, <-app_assoc in Hnd; eauto.
        apply NoDup_app'; eauto using NoDup_app_r.
        eapply Forall_impl; [|eauto]; intros ? [?|?].
        - intros Hin. eapply st_valid_AtomOrGensym_nIn; eauto using switch_not_in_auto_prefs.
          erewrite new_idents_st_ids', cond_eq_st_ids, <-app_assoc; eauto.
          apply in_app_iff; auto.
        - eapply NoDup_app_In in Hnd; eauto.
      }

      repeat constructor. repeat rewrite Forall_app; repeat split. 4:apply NoDupMembers_app.
      + rewrite Forall_map. eapply Forall_forall; intros (?&?) _. constructor.
      + assert (st_follows x1 x2) as Hfollows.
        { eapply mmap_st_follows in H2; eauto.
          simpl_Forall; destruct b; repeat inv_bind.
          etransitivity; eauto with fresh. }

        assert (Forall (fun blks => NoDupBranch (Forall (NoDupLocals xs')) (snd blks)) branches) as Hnd2'.
        { subst. simpl_Forall.
          destruct b. repeat inv_branch. constructor; auto.
          simpl_Forall. take (NoDupLocals _ _) and eapply NoDupLocals_incl' in it; eauto using switch_not_in_auto_prefs.
          - intros ? Hin. rewrite in_app_iff in *. destruct Hin as [|]; auto. right.
            assert (Hincl1:=H0). eapply cond_eq_incl in Hincl1.
            assert (Hincl2:=H2). eapply new_idents_st_ids' in Hincl2.
            eapply incl_app in H3. 2:eapply incl_appl; eauto. 2:eapply incl_appr, incl_refl.
            rewrite <-Hincl2 in H3.
            specialize (st_valid_prefixed x2) as Hvalid'. simpl_Forall; eauto.
        } clear H3.
        assert (Forall (fun x0 : ident => AtomOrGensym auto_prefs x0 \/ In x0 (st_ids x2)) xs') as Hat'.
        { subst. apply Forall_app; split; auto.
          1,2:apply Forall_forall; intros ? Hin.
          - eapply Forall_forall in Hat1 as [|]; eauto.
            right. (eapply incl_map; [|eauto with datatypes]). eapply st_follows_incl; etransitivity; eauto with fresh.
          - right. erewrite new_idents_st_ids', cond_eq_st_ids; eauto.
            rewrite <-app_assoc. apply in_app_iff; auto.
        }

        simpl_Forall.
        eapply NoDupLocals_incl with (xs':=xs').
        { subst. simpl_app.
          apply incl_app; [apply incl_appl, incl_refl|apply incl_app; apply incl_appr].
          - eapply cond_eq_incl in H0; eauto. erewrite map_map, map_ext.
            apply incl_appl, incl_refl.
            intros (?&?&?); auto.
          - apply incl_appr. intros ? Hin. solve_In. auto.
        }

        eapply mmap2_values' in H4; eauto. eapply mmap_values, Forall3_ignore3' with (zs:=x3) in H2.
        2:{ eapply Forall3_length in H4 as (?&?). congruence. }
        2:{ eapply mmap_length in H2; eauto. }
        2:{ intros; destruct_conjs; destruct b0; repeat inv_bind.
            eapply mmap_st_follows; eauto. simpl_Forall; eauto using switch_block_st_follows. }
        eapply Forall3_Forall3, Forall3_ignore12 in H2; eauto. clear H4.
        eapply in_concat in H3 as (?&Hin1&Hin2). simpl_Forall.
        repeat inv_branch; repeat inv_bind; simpl_Forall.
        apply in_app_iff in Hin1 as [Hin1|Hin1]; simpl_In; subst; try constructor.
        eapply switch_blocks_NoDupLocals' in H6; eauto.
        * simpl_Forall; auto.
        * simpl_Forall. destruct Hat'; auto.
          right. eapply incl_map; eauto using st_follows_incl.
      + simpl_Forall. constructor.
      + eapply NoDupMembers_map, cond_eq_NoDupMembers; eauto.
        intros; destruct_conjs; auto.
      + eapply new_idents_st_ids' in H2.
        specialize (st_valid_NoDup x2) as Hvalid'. rewrite H2 in Hvalid'.
        apply NoDup_app_r in Hvalid'; auto.
        rewrite fst_NoDupMembers. rewrite flat_map_concat_map, concat_map, map_map in *.
        do 2 (repeat rewrite map_map; erewrite map_ext; eauto; intros; destruct_conjs; auto).
      + intros ? Hin1 Hinm2.
        erewrite fst_InMembers, map_map, map_ext in Hin1. eapply cond_eq_incl in Hin1; eauto.
        2:intros (?&?&?); auto.
        eapply new_idents_st_ids' in H2.
        specialize (st_valid_NoDup x2) as Hvalid'. rewrite H2 in Hvalid'.
        rewrite fst_InMembers in Hinm2.
        eapply NoDup_app_In in Hvalid'; eauto.
        apply Hvalid'. rewrite flat_map_concat_map, concat_map, map_map in *.
        do 2 (repeat rewrite map_map; erewrite map_ext; eauto; intros; destruct_conjs; auto).
      + subst. intros ? Hinm1 Hinm2. eapply NoDup_app_In in Hnd1'; eauto.
        eapply Hnd1'. apply fst_InMembers in Hinm1. erewrite map_app in Hinm1.
        rewrite in_app_iff in *. destruct Hinm1 as [Hinm1|Hinm1]; [left|auto].
        erewrite map_map, map_ext in Hinm1; eauto. intros (?&?&?); auto. right.
        rewrite flat_map_concat_map, concat_map, map_map in *.
        do 2 (repeat rewrite map_map; erewrite map_ext; eauto; intros; destruct_conjs; auto).

    - (* local *)
      constructor.
      eapply switch_scope_NoDupScope; eauto.
      intros; simpl in *.
      eapply switch_blocks_NoDupLocals'; eauto.
      Transparent switch_scope.
  Qed.

  (** *** GoodLocals *)

  Lemma new_idents_prefixed : forall bck xc tx k ids nids st st',
      new_idents bck xc tx k ids st = (nids, st') ->
      Forall (fun '(_, x, _) => exists n hint, x = gensym switch hint n) nids.
  Proof.
    intros * Hnids.
    apply mmap_values, Forall2_ignore1 in Hnids. simpl_Forall. repeat inv_bind.
    eapply fresh_ident_prefixed; eauto.
  Qed.

  Corollary new_idents_AtomOrGensym : forall bck xc tx k ids nids st st',
      new_idents bck xc tx k ids st = (nids, st') ->
      Forall (fun '(_, x, _) => AtomOrGensym switch_prefs x) nids.
  Proof.
    intros * Hnids.
    apply new_idents_prefixed in Hnids. simpl_Forall; subst.
    right. do 2 esplit; eauto.
    apply PSF.add_1; auto.
  Qed.

  Lemma cond_eq_AtomOrGensym : forall e tx bck xc xcs eqs' st st',
      cond_eq e tx bck st = ((xc, xcs), eqs', st') ->
      Forall (AtomOrGensym switch_prefs) (map fst xcs).
  Proof.
    unfold cond_eq. intros * Hcond.
    cases; repeat inv_bind; simpl; auto.
    all:try take (fresh_ident _ _ _ = _) and eapply fresh_ident_prefixed in it as (?&?&?); subst.
    all:constructor; auto; right; do 2 esplit; eauto; apply PSF.add_1; auto.
  Qed.

  Lemma switch_scope_GoodLocals {A} P_good f_switch : forall locs (blk: A) env bck sub s' st st',
      (forall x y, Env.MapsTo x y sub -> AtomOrGensym switch_prefs y) ->
      GoodLocalsScope P_good switch_prefs (Scope locs blk) ->
      switch_scope f_switch env bck sub (Scope locs blk) st = (s', st') ->
      (forall env blk' st st',
          (forall x y, Env.MapsTo x y sub -> AtomOrGensym switch_prefs y) ->
          P_good blk -> f_switch env blk st = (blk', st') -> P_good blk') ->
      GoodLocalsScope P_good switch_prefs s'.
  Proof.
    intros * Hat Hgood Hind; inv Hgood; intros; repeat inv_bind.
    econstructor; eauto.
    simpl_Forall; auto.
  Qed.

  Lemma switch_block_GoodLocals : forall blk env bck sub blk' st st',
      (forall x y, Env.MapsTo x y sub -> AtomOrGensym switch_prefs y) ->
      GoodLocals switch_prefs blk ->
      switch_block env bck sub blk st = (blk', st') ->
      GoodLocals switch_prefs blk'.
  Proof.
    Opaque switch_scope.
    induction blk using block_ind2; intros * Hsub Hgood Hsw;
      inv Hgood; simpl in *; repeat inv_bind.
    - (* equation *) constructor.
    - (* last *) constructor.
    - (* reset *)
      constructor.
      eapply mmap_values, Forall2_ignore1 in H0.
      simpl_Forall; eauto.
    - (* switch *)
      destruct (partition _ _) as (defs&frees); repeat inv_bind; destruct x; repeat inv_bind.
      do 2 constructor; simpl; auto.
      1,2:repeat rewrite map_app; repeat rewrite Forall_app; repeat split.
      + erewrite map_map, map_ext. eapply cond_eq_AtomOrGensym; eauto.
        intros (?&?&?); auto.
      + rewrite flat_map_concat_map, concat_map. apply Forall_concat. simpl_Forall.
        eapply mmap_values, Forall2_ignore1 in H2. simpl_Forall.
        repeat inv_branch. repeat inv_bind.
        apply new_idents_AtomOrGensym in H1. apply new_idents_AtomOrGensym in H6.
        apply in_app_iff in H5 as [|]; simpl_Forall; eauto.
      + simpl_Forall. constructor.
      + apply Forall_concat. simpl_Forall.
        eapply mmap2_values in H3. eapply mmap_values, Forall3_ignore3' with (zs:=x3) in H2.
        2:{ eapply Forall3_length in H3 as (?&?); congruence. }
        2:{ eapply mmap_length in H2; eauto. }
        eapply Forall3_Forall3 in H2; eauto. clear H3.
        eapply Forall3_ignore12 in H2. simpl_Forall. repeat inv_branch; repeat inv_bind.
        apply in_app_iff in H5 as [|]; simpl_In; subst. 2:constructor.
        eapply mmap_values, Forall2_ignore1 in H6; simpl_Forall; eauto.
        eapply H in H9; eauto.
        * intros ?? Hfind. apply Env.from_list_find_In, in_map_iff in Hfind as (((?&?)&?&?)&Heq&Hin); inv Heq.
          eapply new_idents_AtomOrGensym in H1. eapply new_idents_AtomOrGensym in H7.
          eapply in_app_iff in Hin as [Hin|Hin]; simpl_Forall; eauto.
      + simpl_Forall. constructor.
    - (* automaton *) constructor; auto.
    - (* local *)
      constructor.
      eapply switch_scope_GoodLocals in H0; eauto.
      intros.
      eapply mmap_values, Forall2_ignore1 in H4; simpl_Forall; eauto.
      Transparent switch_scope.
  Qed.

  (** *** noswitch_block *)

  Lemma switch_noswitch : forall blk env bck sub blk' st st',
      noauto_block blk ->
      switch_block env bck sub blk st = (blk', st') ->
      noswitch_block blk'.
  Proof.
    induction blk using block_ind2; intros * Hnl Hswitch; simpl in *; inv Hnl; repeat inv_bind.
    - (* equation *)
      constructor.
    - (* reset *)
      constructor. simpl_Forall.
      eapply mmap_values, Forall2_ignore1 in H0. simpl_Forall; eauto.
    - (* switch *)
      destruct (partition _ _). repeat inv_bind; destruct x; repeat inv_bind.
      repeat constructor; repeat rewrite Forall_app; repeat split.
      + simpl_Forall. reflexivity.
      + simpl_Forall. simpl_In. reflexivity.
      + simpl_Forall. constructor.
      + apply Forall_concat. simpl_Forall.
        eapply mmap2_values in H3. eapply mmap_values, Forall3_ignore3' with (zs:=x3) in H2.
        2:{ eapply Forall3_length in H3 as (?&?); congruence. }
        2:{ eapply mmap_length in H2; eauto. }
        eapply Forall3_Forall3 in H2; eauto. clear H3.
        eapply Forall3_ignore12 in H2. simpl_Forall.
        repeat inv_branch; repeat inv_bind.
        apply in_app_iff in H5 as [|]; simpl_In; subst; [|constructor].
        eapply mmap_values, Forall2_ignore1 in H6. simpl_Forall; eauto.
      + simpl_Forall. constructor.
    - (* local *)
      inv H1. constructor. simpl_Forall; auto.
      eapply mmap_values, Forall2_ignore1 in H0. simpl_Forall; eauto.
  Qed.

  (** ** Transformation of a node and program *)

  Program Definition switch_node (n: @node noauto auto_prefs) : @node noswitch switch_prefs :=
    let res := switch_block (senv_of_ins (n_in n) ++ senv_of_decls (n_out n)) Cbase (@Env.empty _) (n_block n) init_st in
    {| n_name := n_name n;
       n_hasstate := n_hasstate n;
       n_in := n_in n;
       n_out := n_out n;
       n_block := fst res;
       n_ingt0 := n_ingt0 n;
       n_outgt0 := n_outgt0 n
    |}.
  Next Obligation.
    destruct (switch_block _ _ _ _) eqn:Hsw; simpl in *.
    pose proof (n_syn n) as Syn. inversion_clear Syn as [?? Syn1 Syn2 (xs&Vars&Perm)].
    pose proof (n_nodup n) as (Hnd1&Hnd2).
    pose proof (n_good n) as (Hgood1&Hgood2&_).
    apply Permutation_map_inv in Perm as (?&?&Perm); auto; subst.
    assert (VD':=Hsw). eapply switch_block_VarsDefinedComp with (xs:=map _ x) in VD';
      eauto using node_NoDupMembers, node_NoDupLocals.
    do 2 esplit.
    - rewrite rename_vars_empty, <-map_fst_senv_of_decls in VD'.
      eapply VarsDefinedComp_VarsDefined; [|eauto].
      eapply NoDupLocals_incl, switch_block_NoDupLocals; eauto. 2:simpl_Forall; auto.
      rewrite map_fst_senv_of_decls, Perm. solve_incl_app.
    - apply Permutation_map. now symmetry.
    - rewrite <-Perm, map_app, map_fst_senv_of_decls. now solve_incl_app.
    - intros ? Hin. apply Env.Props.P.F.empty_in_iff in Hin. inv Hin.
    - rewrite <-Perm. eauto using NoDup_app_r.
  Qed.
  Next Obligation.
    pose proof (n_lastd n) as (?&Last&Perm).
    pose proof (n_syn n) as Syn. inversion_clear Syn as [?? Syn1 Syn2 _].
    destruct (switch_block _ _ _ _) eqn:Hsw; simpl in *.
    do 2 esplit; eauto using switch_block_LastsDefined.
  Qed.
  Next Obligation.
    destruct (switch_block _ _ _ _) eqn:Hsw; simpl in *.
    pose proof (n_nodup n) as (Hnd1&Hnd2).
    pose proof (n_good n) as (Hgood1&Hgood2&_).
    split; auto.
    eapply switch_block_NoDupLocals; eauto.
    + eapply Forall_impl; eauto.
  Qed.
  Next Obligation.
    destruct (switch_block _ _ _ _) eqn:Hsw; simpl in *.
    pose proof (n_nodup n) as (Hnd1&Hnd2).
    pose proof (n_good n) as (Hgood1&Hgood2&Hgood3).
    repeat split; eauto using Forall_AtomOrGensym_add.
    eapply switch_block_GoodLocals; eauto using GoodLocals_add, Forall_AtomOrGensym_add.
    intros ?? Hfind. apply Env.Props.P.F.empty_mapsto_iff in Hfind. inv Hfind.
  Qed.
  Next Obligation.
    destruct (switch_block _ _ _ _) eqn:Hsw.
    pose proof (n_syn n) as Hsyn. inversion_clear Hsyn as [?? Syn1 Syn2 (?&Vars&Perm)].
    econstructor; eauto using switch_noswitch.
    do 2 esplit; eauto.
    pose proof (n_nodup n) as (Hnd1&Hnd2).
    eapply switch_block_VarsDefinedComp with (xs:=x) in Hsw; eauto using node_NoDupMembers, node_NoDupLocals.
    - rewrite rename_vars_empty in Hsw; eauto.
    - rewrite Perm, map_app, map_fst_senv_of_decls. now solve_incl_app.
    - intros ? Hin. apply Env.Props.P.F.empty_in_iff in Hin. inv Hin.
    - rewrite Perm. eauto using NoDup_app_r.
  Qed.

  Global Program Instance switch_node_transform_unit: TransformUnit node node :=
    { transform_unit := switch_node }.

  Global Program Instance switch_global_without_units : TransformProgramWithoutUnits (@global noauto auto_prefs) (@global noswitch switch_prefs) :=
    { transform_program_without_units := fun g => Global g.(types) g.(externs) [] }.

  Definition switch_global : @global noauto auto_prefs -> @global noswitch switch_prefs :=
    transform_units.

  (** *** Equality of interfaces *)

  Lemma switch_global_iface_eq : forall G,
      global_iface_eq G (switch_global G).
  Proof.
    repeat split; auto.
    intros f. unfold find_node.
    destruct (find_unit f G) as [(?&?)|] eqn:Hfind; simpl.
    - setoid_rewrite find_unit_transform_units_forward; eauto.
      simpl. repeat constructor.
    - destruct (find_unit f (switch_global G)) as [(?&?)|] eqn:Hfind'; simpl; try constructor.
      eapply find_unit_transform_units_backward in Hfind' as (?&?&?&?); congruence.
  Qed.

  (** ** Additional properties *)

  Lemma new_idents_In_inv : forall ck cx tx k ids nids st st' x y ck1 ty,
      new_idents ck cx tx k ids st = (nids, st') ->
      In (x, y, (ty, ck1)) nids ->
      exists ann, In (x, ann) ids /\ ann.(typ) = ty.
  Proof.
    intros * Hni Hin.
    eapply mmap_values, Forall2_ignore1 in Hni. simpl_Forall. repeat inv_bind; eauto.
  Qed.

End CLOCKSWITCH.

Module ClockSwitchFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks : CLOCKS Ids Op OpAux)
       (Senv : STATICENV Ids Op OpAux Cks)
       (Syn : LSYNTAX Ids Op OpAux Cks Senv)
       <: CLOCKSWITCH Ids Op OpAux Cks Senv Syn.
  Include CLOCKSWITCH Ids Op OpAux Cks Senv Syn.
End ClockSwitchFun.
