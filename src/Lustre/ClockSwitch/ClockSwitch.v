From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Velus Require Import Common.
From Velus Require Import CommonTyping.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Fresh.
From Velus Require Import Lustre.LSyntax.

(** * Remove Switches *)

Module Type CLOCKSWITCH
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Import Cks : CLOCKS Ids Op OpAux)
       (Import Syn : LSYNTAX Ids Op OpAux Cks).

  Section subclock.
    Variable base: clock.
    Variable sub : Env.t ident.

    Definition rename_var (x : ident) :=
      or_default x (Env.find x sub).

    Fixpoint subclock_clock (ck : clock) :=
      match ck with
      | Cbase => base
      | Con ck' x t => Con (subclock_clock ck') (rename_var x) t
      end.

    Definition subclock_nclock (nck : nclock) :=
      (subclock_clock (fst nck), option_map rename_var (snd nck)).

    Definition subclock_ann {A} (ann : (A * clock)) :=
      (fst ann, subclock_clock (snd ann)).

    Fixpoint add_whens (e : exp) (ty : type) (ck : clock) :=
      match ck with
      | Cbase => e
      | Con ck' ckid (_, b) => Ewhen [(add_whens e ty ck')] ckid b ([ty], ck)
      end.

    Fixpoint subclock_exp (e : exp) :=
      match e with
      | Econst c => add_whens e (Tprimitive (ctype_cconst c)) base
      | Eenum _ ty => add_whens e ty base
      | Evar x ann => Evar (rename_var x) (subclock_ann ann)
      | Eunop op e1 ann => Eunop op (subclock_exp e1) (subclock_ann ann)
      | Ebinop op e1 e2 ann => Ebinop op (subclock_exp e1) (subclock_exp e2) (subclock_ann ann)
      | Efby e0s e1s anns => Efby (map subclock_exp e0s) (map subclock_exp e1s) (map subclock_ann anns)
      | Earrow e0s e1s anns => Earrow (map subclock_exp e0s) (map subclock_exp e1s) (map subclock_ann anns)
      | Ewhen es x t ann => Ewhen (map subclock_exp es) (rename_var x) t (subclock_ann ann)
      | Emerge (x, ty) es ann => Emerge (rename_var x, ty) (map (fun '(i, es) => (i, map subclock_exp es)) es) (subclock_ann ann)
      | Ecase e es d ann =>
        Ecase (subclock_exp e) (map (fun '(i, es) => (i, map subclock_exp es)) es) (option_map (map subclock_exp) d) (subclock_ann ann)
      | Eapp f es er ann => Eapp f (map subclock_exp es) (map subclock_exp er) (map subclock_ann ann)
      end.

    Definition subclock_equation '(xs, es) : equation :=
      (map rename_var xs, map subclock_exp es).

    (** *** Properties *)

    Lemma subclock_ann_clock {A} : forall (ann : (A * clock)),
        snd (subclock_ann ann) = subclock_clock (snd ann).
    Proof. reflexivity. Qed.

    Corollary map_subclock_ann_clock {A} : forall (anns : list (A * clock)),
        map snd (map subclock_ann anns) = map subclock_clock (map snd anns).
    Proof.
      induction anns; simpl; auto.
    Qed.

    Lemma map_subclock_ann_type {A} : forall (anns : list (A * clock)),
        map fst (map subclock_ann anns) = map fst anns.
    Proof.
      induction anns; simpl; auto.
    Qed.

  End subclock.

  (** ** Eliminating switches *)

  Module Fresh := Fresh.Fresh(Ids).
  Import Fresh Notations Facts Tactics.
  Local Open Scope fresh_monad_scope.

  Definition FreshAnn A := Fresh A (type * clock).

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

    Fact mmap2_st_valid : forall a1s a2s bs st st' pref aft,
        mmap2 a1s a2s st = (bs, st') ->
        Forall2 (fun a1 a2 => forall b st st',
                    k a1 a2 st = (b, st') ->
                    st_valid_after st pref aft ->
                    st_valid_after st' pref aft) a1s a2s ->
        st_valid_after st pref aft ->
        st_valid_after st' pref aft.
    Proof.
      induction a1s; intros * Hmap Hforall Hvalid;
        simpl in *; repeat inv_bind; auto.
      inv Hforall. repeat inv_bind. eauto.
    Qed.

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

    Fact mmap2_values' : forall a1s a2s bs st st' pref aft,
        length a1s = length a2s ->
        st_valid_after st pref aft ->
        (forall a1 a2 b st st', st_valid_after st pref aft -> k a1 a2 st = (b, st') -> st_valid_after st' pref aft) ->
        (forall a1 a2 b st st', k a1 a2 st = (b, st') -> st_follows st st') ->
        mmap2 a1s a2s st = (bs, st') ->
        Forall3 (fun a1 a2 b => exists st1 st2, st_valid_after st1 pref aft /\ st_follows st st1 /\ k a1 a2 st1 = (b, st2)) a1s a2s bs.
    Proof.
      induction a1s; intros * Hlen Hvalid Hk1 Hk2 Hmmap; simpl in *; repeat inv_bind.
      - destruct a2s; simpl in *; try congruence. constructor.
      - destruct a2s; simpl in *; try congruence.
        repeat inv_bind.
        constructor; eauto.
        + repeat esplit; eauto. reflexivity.
        + eapply Forall3_impl_In; [|eauto]. intros ??? _ _ _ (?&?&?&?&?).
          repeat esplit; eauto. etransitivity; eauto.
    Qed.

  End mmap2.

  Definition cond_eq e tx bck : FreshAnn (ident * list (ident * (type * clock)) * list equation) :=
    match e with
    | Evar x (ty, ck) => ret (x, [], [])
    | _ =>
      do xc <- fresh_ident switch None (tx, bck);
      ret (xc, [(xc, (tx, bck))], [([xc], [e])])
    end.

  Definition new_idents bck xc tx k (ids : list (ident * (type * clock))) :=
    mmap (fun '(x, (ty, _)) => do y <- fresh_ident switch (Some x) (ty, bck);
                            ret (x, y, (ty, Con bck xc (tx, k)))) ids.

  Definition when_free (x y : ident) ty ck xc tx k :=
    Beq ([y], [Ewhen [Evar x (ty, ck)] xc k ([ty], Con ck xc (tx, k))]).

  Definition merge_defs sub (y : ident) ty ck xc tx (brs : list (enumtag * Env.t ident)) :=
    Beq ([rename_var sub y], [Emerge (xc, tx)
                                     (map (fun '(k, sub') => (k, [Evar (rename_var sub' y) (ty, Con ck xc (tx, k))])) brs)
                                     ([ty], ck)]).

  Fixpoint switch_block (env : list (ident * (type * clock))) bck sub blk : FreshAnn block :=
    match blk with
    | Beq eq => ret (Beq (subclock_equation bck sub eq))

    | Breset blks er =>
      do blks' <- mmap (switch_block env bck sub) blks;
      ret (Breset blks' (subclock_exp bck sub er))

    | Blocal locs blks =>
      let locs' := map (fun '(x, (ty, ck, cx)) => (x, (ty, subclock_clock bck sub ck, cx))) locs in
      let env := (idty locs)++env in
      do blks' <- mmap (switch_block env bck sub) blks;
      ret (Blocal locs' blks')

    | Bswitch ec branches =>
      let vd := vars_defined (Bswitch ec branches) in

      (* Get defined and free variables *)
      let (defs, frees) := partition (fun '(x, _) => PS.mem x vd) env in

      (* Filtering available free variables *)
      let eck := hd Cbase (clockof ec) in
      let frees := List.filter (fun '(_, (_, ck')) => ck' ==b eck) frees in

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

      let env := map (fun '(x, (ty, ck)) => (x, (ty, Cbase))) (defs++frees) in
      do blks' <-
         mmap2 (fun '(k, blks) '(_, sub', nfrees, ndefs) =>
                  let wheneqs := List.map (fun '(x, y, (ty, _)) => when_free (rename_var sub x) y ty bck xc tx k) nfrees in
                  do blks' <- mmap (switch_block env (Con bck xc (tx, k)) sub') blks;
                  ret (blks'++wheneqs)
               ) branches xs';
      let mergeeqs := map (fun '(x, (ty, _)) => merge_defs sub x ty bck xc tx (map (fun '(k, sub, _, _) => (k, sub)) xs')) defs in
      let locs := flat_map (fun '(_, _, nfrees, ndefs) => (map (fun '(_, x, (ty, ck)) => (x, (ty, ck, xH))) (nfrees++ndefs))) xs' in
      ret (Blocal (List.map (fun '(xc, (ty, ck)) => (xc, (ty, ck, xH))) xcs++locs) (mergeeqs++concat blks'++map Beq condeqs))
    end.

  (** *** Some properties *)

  Lemma switch_not_in_elab_prefs :
    ~PS.In switch elab_prefs.
  Proof.
    unfold elab_prefs.
    rewrite PSF.singleton_iff.
    pose proof gensym_prefs_NoDup as Hnd. unfold gensym_prefs in Hnd.
    repeat rewrite NoDup_cons_iff in Hnd. destruct Hnd as (Hnin1&Hnin2&Hnin3&Hnin4&_).
    intros contra; subst; rewrite contra in *; eauto with datatypes.
  Qed.

  Lemma new_idents_old : forall bck xc tx k ids nids st st',
      new_idents bck xc tx k ids st = (nids, st') ->
      map (fun '(x, _, _) => x) nids = map fst ids.
  Proof.
    intros * Hni.
    eapply mmap_values in Hni.
    induction Hni as [|(?&?&?) ((?&?)&?&?)]; simpl; auto.
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
    apply NoDupMembers_app; eauto using NoDupMembers_app_l, NoDupMembers_app_r, nodupmembers_filter.
    intros ? Hinm1 Hinm2.
    eapply NoDupMembers_app_InMembers in Hnd; eauto using filter_InMembers'.
  Qed.

  (** *** VarsDefined *)

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

  Lemma cond_eq_VarsDefined: forall e tx bck xc xcs eqs st st',
      cond_eq e tx bck st = ((xc, xcs), eqs, st') ->
      Forall2 VarsDefined (map Beq eqs) (map (fun '(x, _) => [x])  xcs).
  Proof.
    unfold cond_eq. intros * Hcond.
    cases; repeat inv_bind; simpl; repeat constructor; auto.
  Qed.

  Fact switch_blocks_VarsDefined : forall blks xs env bck sub blks' st st',
      Forall
        (fun blk => forall xs bck sub env blk' st st',
             incl xs (map fst env) ->
             (forall x, Env.In x sub -> InMembers x env) ->
             NoDupMembers env ->
             NoDup xs ->
             VarsDefined blk xs ->
             NoDupLocals (map fst env) blk ->
             switch_block env bck sub blk st = (blk', st') ->
             exists xs' : list ident, VarsDefined blk' xs' /\ Permutation xs' (map (rename_var sub) xs)) blks ->
      incl (concat xs) (map fst env) ->
      (forall x, Env.In x sub -> InMembers x env) ->
      NoDupMembers env ->
      NoDup (concat xs) ->
      Forall2 VarsDefined blks xs ->
      Forall (NoDupLocals (map fst env)) blks ->
      mmap (switch_block env bck sub) blks st = (blks', st') ->
      exists xs', Forall2 VarsDefined blks' xs' /\ Permutation (concat xs') (map (rename_var sub) (concat xs)).
  Proof.
    induction blks; intros * Hf Hincl Hsub Hnd1 Hnd2 Hvars Hnd3 Hmmap;
      inv Hf; inv Hvars; inv Hnd3; simpl in *; repeat inv_bind.
    - exists []. auto.
    - apply incl_app' in Hincl as (?&?).
      eapply H1 with (xs:=y) in H as (ys1&Hvars1&Hperm1); eauto using NoDup_app_l. clear H1.
      eapply IHblks in H2 as (ys2&Hvars2&Hperm2); eauto using NoDup_app_r. clear IHblks.
      exists (ys1::ys2). repeat constructor; simpl; auto.
      rewrite map_app.
      apply Permutation_app; auto.
  Qed.

  Lemma switch_block_VarsDefined : forall blk xs bck sub env blk' st st',
      incl xs (map fst env) ->
      (forall x, Env.In x sub -> InMembers x env) ->
      NoDupMembers env ->
      NoDup xs ->
      VarsDefined blk xs ->
      NoDupLocals (map fst env) blk ->
      switch_block env bck sub blk st = (blk', st') ->
      exists xs', VarsDefined blk' xs' /\ Permutation xs' (map (rename_var sub) xs).
  Proof.
    induction blk using block_ind2; intros * Hincl Hsub Hnd1 Hnd2 Hvd Hnd3 Hsw;
      inv Hvd; inv Hnd3; simpl in *; repeat inv_bind.
    - (* equation *)
      destruct eq as (xs&es); simpl.
      exists (map (rename_var sub) xs); split; auto.
      constructor.

    - (* reset *)
      eapply switch_blocks_VarsDefined in H as (?&Hvars&Hperm); eauto.
      repeat esplit; eauto. constructor; auto.

    - (* switch *)
      destruct (partition _ _) as (defs&frees) eqn:Hpart. eapply partition_Partition in Hpart.
      repeat inv_bind. destruct x; repeat inv_bind.
      assert (Permutation (map fst defs) xs) as Hdefs.
      { clear H1 H.
        assert (Hperm:=Hpart). apply Partition_Permutation in Hperm.
        rewrite Hperm, map_app in Hincl.
        symmetry. eapply incl_Permutation; eauto.
        - assert (VarsDefined (Bswitch ec branches) xs) as Hdef by (constructor; auto).
          assert (NoDupLocals xs (Bswitch ec branches)) as Hnd'.
          { constructor. do 2 (eapply Forall_forall; intros).
            repeat (eapply Forall_forall in H3; eauto).
            eapply NoDupLocals_incl; [|eauto]. now rewrite Hperm, map_app. }
          intros ?; split; intros Hin.
          + eapply VarsDefined_Is_defined in Hdef; eauto.
            apply Is_defined_in_vars_defined in Hdef; simpl in *.
            apply Hincl, in_app_iff in Hin as [|Hin]; auto.
            eapply in_map_iff in Hin as ((?&?)&?&?); subst; simpl in *.
            eapply Partition_Forall2, Forall_forall in Hpart; eauto; simpl in *.
            apply Bool.not_true_is_false, PSF.not_mem_iff in Hpart. congruence.
          + eapply in_map_iff in Hin as ((?&?)&?&?); subst; simpl in *.
            eapply VarsDefined_Is_defined'; eauto.
            eapply Partition_Forall1, Forall_forall in Hpart; eauto; simpl in *.
            eapply PSF.mem_2 in Hpart.
            eapply vars_defined_Is_defined_in; simpl; auto.
        - rewrite <-map_app, <-fst_NoDupMembers, <-Hperm; auto.
      }
      exists (map (rename_var sub) (map fst defs)). split.
      2:now apply Permutation_map.

      assert (Forall2 (fun '(_, _, nfree, ndefs) blks =>
                         exists xs, Forall2 VarsDefined blks xs /\
                               Permutation (concat xs) (map (fun '(_, x, _) => x) ndefs ++ map (fun '(_, x, _) => x) nfree)) x x3) as Hf.
      { eapply mmap2_values in H5. eapply mmap_values in H1.
        eapply Forall3_ignore3' with (zs:=x3) in H1.
        2:{ eapply Forall3_length in H5 as (?&?). congruence. }
        2:{ eapply mmap_length in H1; eauto. }
        eapply Forall3_Forall3, Forall3_ignore1 in H1; eauto. clear H5.
        eapply Forall2_impl_In; [|eauto]. intros (((?&?)&nfrees)&ndefs) ? Hin1 Hin2 ((?&?)&?&(?&?&?)&?&?&?).
        repeat inv_bind.
        repeat (take (Forall _ branches) and eapply Forall_forall in it; eauto).
        destruct it1 as (?&Hvars&Hperm).
        eapply switch_blocks_VarsDefined in H6 as (?&Hvars'&Hperm'); eauto. clear it.
        2:{ rewrite Hperm, <-Hdefs, map_map, map_app.
            apply incl_appl. erewrite map_ext; try reflexivity.
            intros (?&?&?); auto. }
        2:{ intros ? Hin. apply Env.In_from_list, fst_InMembers in Hin.
            erewrite map_map, map_ext, map_app, 2 new_idents_old, <-map_app, <-fst_InMembers in Hin; eauto.
            erewrite fst_InMembers, map_map, map_ext, <-fst_InMembers, Permutation_app_comm; eauto.
            intros (?&?&?); eauto. intros ((?&?)&?&?); eauto.
        }
        2:{ erewrite fst_NoDupMembers, map_map, map_ext, <-fst_NoDupMembers; eauto. 2:intros (?&?&?); auto.
            eapply switch_block_NoDupMembers_env; eauto. }
        2:{ rewrite Hperm; auto. }
        2:{ eapply Forall_impl; [|eapply it0]. intros ? Hnd.
            eapply NoDupLocals_incl; eauto.
            apply Partition_Permutation in Hpart. rewrite Hpart.
            rewrite map_map, 2 map_app.
            apply incl_app; [apply incl_appl|apply incl_appr].
            - erewrite map_ext; try reflexivity. intros (?&?&?); auto.
            - erewrite map_ext; try eapply incl_map, incl_filter', incl_refl.
              intros (?&?&?); auto.
        }
        remember (Env.from_list _) as sub'.
        exists (x11 ++ map (fun '(_, x, _) => [x]) nfrees).
        split.
        - apply Forall2_app; auto.
          rewrite Forall2_map_1, Forall2_map_2. apply Forall2_same, Forall_forall; intros ((?&?)&?&?) _.
          constructor.
        - rewrite concat_app. apply Permutation_app.
          + rewrite Hperm', Hperm.
            eapply new_idents_rename with (ids1:=(filter _ _)) (ids2:=defs) in H7 as (_&Hdefs'); eauto.
            2:{ apply Partition_Permutation in Hpart. rewrite Hpart in Hnd1.
                apply NoDupMembers_app;
                  eauto using NoDupMembers_app_l, NoDupMembers_app_r, nodupmembers_filter.
                intros ? Hinm1 Hinm2. apply filter_InMembers in Hinm1 as ((?&?)&Hinm1&_).
                apply In_InMembers in Hinm1.
                eapply NoDupMembers_app_InMembers in Hnd1; eauto. }
            rewrite Hdefs'; subst.
            now apply Permutation_map.
          + erewrite map_ext, <-map_map, concat_map_singl1. reflexivity.
            intros ((?&?)&?&?); auto.
      }
      eapply Forall2_impl_In, Forall2_Forall2_exists in Hf as (?&Hperm&Hvars).
      2:{ intros (((?&?)&?)&?) ? _ _ (?&?&?). exists x4. split. 2:apply H6.
          instantiate (1:= (fun '(_, _, nfrees, ndefs) x => Permutation (concat x) _)); simpl; eauto.
      }

      econstructor; simpl. repeat apply Forall2_app. 1-4:simpl in *.
      3:{ eapply cond_eq_VarsDefined; eauto. }
      1:{ instantiate (1:=map (fun x => [rename_var sub x]) (map fst defs)).
          rewrite map_map, Forall2_map_1, Forall2_map_2.
          apply Forall2_same, Forall_forall; intros (?&?&?) _.
          constructor.
      }
      + eapply Forall2_concat; eauto.
      + rewrite concat_app. rewrite Permutation_app_comm; apply Permutation_app.
        2:rewrite concat_app, map_app, Permutation_app_comm; apply Permutation_app.
        * symmetry. erewrite map_ext, <-map_map, concat_map_singl1. reflexivity.
          intros; simpl; auto.
        * clear - Hperm. induction Hperm as [|(((?&?)&?)&?)]; simpl; auto.
          rewrite map_app, concat_app. apply Permutation_app; auto. rewrite Permutation_app_comm.
          erewrite map_map, map_ext, map_app, H. reflexivity.
          intros ((?&?)&?&?); auto.
        * clear - l. induction l as [|(?&?&?)]; simpl; auto.

    - (* local *)
      eapply switch_blocks_VarsDefined with (env:=idty locs++env) in H as (?&Hvd&Hperm); eauto.
      2:{ rewrite <-H4, map_app, map_fst_idty.
          apply incl_app; [apply incl_appl, incl_refl|apply incl_appr; auto]. }
      2:{ intros ? Hin. eapply InMembers_app; eauto. }
      2:{ apply NoDupMembers_app; auto.
          - rewrite NoDupMembers_idty; auto.
          - intros ? Hin Hinm. rewrite InMembers_idty in Hin.
            eapply H7; eauto. rewrite <-fst_InMembers; auto.
      }
      2:{ rewrite <-H4. apply NoDup_app'; auto.
          - rewrite <-fst_NoDupMembers; auto.
          - eapply Forall_forall; intros ? Hin1 Hin2. apply fst_InMembers in Hin1.
            apply Hincl, H7 in Hin2; eauto.
      }
      2:{ rewrite map_app, map_fst_idty; auto.
          eapply Forall_impl; [|eapply H3]; intros. now rewrite Permutation_app_comm.
      }
      do 2 esplit; try reflexivity.
      econstructor; eauto. rewrite map_map, map_ext with (g:=fst). 2:intros (?&(?&?)&?); auto.
      rewrite Hperm, <-H4, map_app.
      apply Permutation_app; auto.
      rewrite rename_vars_idem; auto.
      intros ? Hin contra. eapply H7; eapply fst_InMembers; eauto.
  Qed.

  (** *** Preservation of st_valid_after *)

  Lemma cond_eq_st_valid : forall e tx bck xcs eqs' st st' aft,
      st_valid_after st switch aft ->
      cond_eq e tx bck st = (xcs, eqs', st') ->
      st_valid_after st' switch aft.
  Proof.
    unfold cond_eq. intros * Hst Hcond.
    cases; repeat inv_bind; eauto using fresh_ident_st_valid.
  Qed.

  Lemma new_idents_st_valid : forall ck xc tx k ids nids st st' aft,
      st_valid_after st switch aft ->
      new_idents ck xc tx k ids st = (nids, st') ->
      st_valid_after st' switch aft.
  Proof.
    intros * Hst Hnids.
    eapply mmap_st_valid in Hnids; eauto.
    eapply Forall_forall; intros (?&?&?) ??????; repeat inv_bind.
    eapply fresh_ident_st_valid; eauto.
  Qed.

  Global Hint Resolve cond_eq_st_valid new_idents_st_valid : fresh.

  Lemma switch_block_st_valid : forall blk env bck sub blk' st st' aft,
      st_valid_after st switch aft ->
      switch_block env bck sub blk st = (blk', st') ->
      st_valid_after st' switch aft.
  Proof.
    induction blk using block_ind2; intros * Hst Hsw;
      repeat inv_bind; simpl in *; auto.
    - (* reset *)
      eapply mmap_st_valid; eauto.
      eapply Forall_impl; [|eauto]; intros; eauto.
    - (* switch *)
      destruct (partition _ _) as (defs&frees).
      repeat inv_bind; destruct x; repeat inv_bind.
      eapply cond_eq_st_valid in H0; eauto.
      assert (Hmap:=H1). eapply mmap_st_valid in H1; eauto.
      2:{ eapply Forall_forall; intros (?&?) ? (((?&?)&?)&?) ????.
          repeat inv_bind. eauto with fresh.
      }
      eapply mmap2_st_valid in H2; eauto.
      eapply mmap2_values, Forall3_ignore3 in H2.
      2:{ eapply mmap_length in Hmap; eauto. }
      eapply Forall2_impl_In; [|eauto]. intros (?&?) (((?&?)&?)&?) ?? _ ?????.
      clear H2. repeat inv_bind.
      repeat (take (Forall _ branches) and eapply Forall_forall in it; eauto).
      eapply mmap_st_valid in H6; eauto.
      eapply Forall_impl; [|eauto]; intros; eauto.
    - (* local *)
      eapply mmap_st_valid; eauto.
      eapply Forall_impl; [|eauto]; intros; eauto.
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
    eapply Forall_forall; intros (?&?&?) ?????; repeat inv_bind.
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
    - (* reset *)
      eapply mmap_st_follows; eauto.
      eapply Forall_impl; [|eauto]; intros; eauto.
    - (* switch *)
      destruct (partition _ _) as (defs&frees).
      repeat inv_bind; destruct x; repeat inv_bind.
      etransitivity; eauto with fresh.
      etransitivity. eapply mmap_st_follows in H1; eauto with fresh.
      { eapply Forall_forall; intros (?&?) ? (((?&?)&?)&?) ???. repeat inv_bind.
        etransitivity; eauto with fresh. }
      eapply mmap2_st_follows in H2; eauto.
      eapply mmap2_values, Forall3_ignore3 in H2.
      2:{ eapply mmap_length in H1; eauto. }
      eapply Forall2_impl_In; [|eauto]. intros (?&?) (((?&?)&?)&?) ?? _ ????.
      clear H2. repeat inv_bind.
      repeat (take (Forall _ branches) and eapply Forall_forall in it; eauto).
      eapply mmap_st_follows in H2; eauto.
      eapply Forall_impl; [|eauto]; intros; eauto.
    - (* local *)
      eapply mmap_st_follows; eauto.
      eapply Forall_impl; [|eauto]; intros; eauto.
  Qed.

  (** *** NoDup *)

  Fact switch_blocks_NoDupLocals' : forall blks xs env bck sub blks' st st' aft,
      Forall
        (fun blk => forall xs env bck sub blk' st st' aft,
             NoDup xs ->
             NoDupLocals xs blk ->
             Forall (fun x : ident => AtomOrGensym elab_prefs x \/ In x (st_ids st)) xs ->
             GoodLocals elab_prefs blk ->
             st_valid_after st switch aft ->
             switch_block env bck sub blk st = (blk', st') ->
             NoDupLocals xs blk') blks ->
      NoDup xs ->
      Forall (NoDupLocals xs) blks ->
      Forall (fun x => AtomOrGensym elab_prefs x \/ In x (st_ids st)) xs ->
      Forall (GoodLocals elab_prefs) blks ->
      st_valid_after st switch aft ->
      mmap (switch_block env bck sub) blks st = (blks', st') ->
      Forall (NoDupLocals xs) blks'.
  Proof.
    induction blks; intros * Hf Hnd1 Hnd2 Hat1 Hgood Hv Hmmap; repeat inv_bind;
      inv Hf; inv Hgood; inv Hnd2; constructor; simpl in *; eauto.
    eapply IHblks in H0; eauto.
    + eapply Forall_impl; [|eauto]. intros ? [?|?]; auto.
      right. eapply incl_map; eauto. eapply st_follows_incl, switch_block_st_follows; eauto.
    + eapply switch_block_st_valid; eauto.
  Qed.

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
    1-10:symmetry; eapply fresh_ident_vars_perm; eauto.
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
    induction ids as [|(?&?&?)]; intros * Hni; repeat inv_bind; auto. now rewrite app_nil_r.
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

  Lemma switch_block_NoDupLocals : forall blk xs env bck sub blk' st st' aft,
      NoDup xs ->
      NoDupLocals xs blk ->
      Forall (fun x => AtomOrGensym elab_prefs x \/ In x (st_ids st)) xs ->
      GoodLocals elab_prefs blk ->
      st_valid_after st switch aft ->
      switch_block env bck sub blk st = (blk', st') ->
      NoDupLocals xs blk'.
  Proof.
    induction blk using block_ind2; intros * Hnd1 Hnd2 Hat1 Hgood Hvalid Hswi;
      inv Hgood; inv Hnd2; repeat inv_bind; simpl in *; auto using NoDupLocals.

    - (* reset *)
      constructor.
      eapply switch_blocks_NoDupLocals'; eauto.

    - (* switch *)
      take (Forall (fun blks => Forall (GoodLocals _) _) _) and rename it into Hgood.
      take (Forall (fun blks => Forall (NoDupLocals _) _) _) and rename it into Hnd2.
      destruct (partition _ _) as (defs&frees). repeat inv_bind; destruct x; repeat inv_bind.
      simpl. repeat rewrite <-flat_map_app. repeat rewrite map_app.
      assert (st_valid_after x2 switch aft) as Hvalid'.
      { eapply mmap_st_valid, cond_eq_st_valid; eauto.
        eapply Forall_forall; intros (?&?) _ (((?&?)&?)&?) ????. repeat inv_bind. eauto with fresh. }

      remember (xs ++ map fst l ++
                   map fst
                   (flat_map
                      (fun '(_, _, nfrees, ndefs) =>
                         map (fun '(_, x4, (ty, ck0)) => (x4, (ty, ck0, 1%positive))) (nfrees ++ ndefs)) x)) as xs'.
      assert (NoDup xs') as Hnd1'.
      { subst.
        assert (Hnd:=Hvalid'). apply Ker.st_valid_NoDup, NoDup_app_l in Hnd.
        erewrite new_idents_st_ids', cond_eq_st_ids, <-app_assoc in Hnd; eauto.
        apply NoDup_app'; eauto using NoDup_app_r.
        eapply Forall_impl; [|eauto]; intros ? [?|?].
        - intros Hin. eapply st_valid_after_AtomOrGensym_nIn in Hvalid'; eauto using switch_not_in_elab_prefs.
          eapply Hvalid'. erewrite new_idents_st_ids', cond_eq_st_ids, <-app_assoc; eauto.
          apply in_app_iff; auto.
        - eapply NoDup_app_In in Hnd; eauto.
      }

      repeat constructor. repeat rewrite Forall_app; repeat split. 4:apply NoDupMembers_app.
      + rewrite Forall_map. eapply Forall_forall; intros (?&?&?) _. constructor.
      + assert (st_follows x1 x2) as Hfollows.
        { eapply mmap_st_follows in H1; eauto.
          eapply Forall_forall; intros (?&?) ? (((?&?)&?)&?) ???. repeat inv_bind.
          etransitivity; eauto with fresh. }

        assert (Forall (fun blks => Forall (NoDupLocals xs') (snd blks)) branches) as Hnd2'.
        { subst. clear - Hgood Hnd2 H0 H1 H2 Hvalid'. do 2 (eapply Forall_forall; intros).
          repeat (take (Forall _ _) and eapply Forall_forall in it; eauto).
          eapply NoDupLocals_incl'. 2,4:eauto.
          - eapply switch_not_in_elab_prefs.
          - intros ? Hin. rewrite in_app_iff in *. destruct Hin as [|]; auto. right.
            assert (Hincl1:=H0). eapply cond_eq_incl in Hincl1.
            assert (Hincl2:=H1). eapply new_idents_st_ids' in Hincl2.
            eapply incl_app in H4. 2:eapply incl_appl; eauto. 2:eapply incl_appr, incl_refl.
            rewrite <-Hincl2 in H4.
            eapply st_valid_prefixed, Forall_forall in Hvalid'; eauto.
        } clear Hnd2.
        assert (Forall (fun x0 : ident => AtomOrGensym elab_prefs x0 \/ In x0 (st_ids x2)) xs') as Hat'.
        { subst. apply Forall_app; split; auto.
          1,2:apply Forall_forall; intros ? Hin.
          - eapply Forall_forall in Hat1 as [|]; eauto.
            right. (eapply incl_map; [|eauto with datatypes]). eapply st_follows_incl; etransitivity; eauto with fresh.
          - right. erewrite new_idents_st_ids', cond_eq_st_ids; eauto.
            rewrite <-app_assoc. apply in_app_iff; auto.
        }

        eapply Forall_impl; intros.
        eapply NoDupLocals_incl with (xs':=xs').
        2:eauto.
        { subst. simpl_app.
          apply incl_app; [apply incl_appl, incl_refl|apply incl_app; apply incl_appr].
          - eapply cond_eq_incl in H0; eauto. erewrite map_map, map_ext.
            apply incl_appl, incl_refl.
            intros (?&?&?); auto.
          - apply incl_appr, incl_refl.
        }

        clear - H H2 Hnd1' Hnd2' Hgood Hvalid' Hat'. revert xs' x x2 x3 st' Hnd1' Hnd2' H2 Hvalid' Hat'.
        induction H as [|(?&?)]; intros; inv Hnd2'; inv Hgood; simpl in *; try destruct x as [|(((?&?)&?)&?)];
          repeat inv_bind; simpl; auto.
        repeat rewrite <-flat_map_app. repeat rewrite map_app.
        repeat rewrite Forall_app. repeat split.
        * eapply switch_blocks_NoDupLocals'; eauto.
        * apply Forall_map, Forall_forall; intros ((?&?)&?&?) _. constructor.
        * eapply IHForall; eauto.
          eapply mmap_st_valid; eauto. eapply Forall_forall; intros. eapply switch_block_st_valid; eauto.
          eapply Forall_impl; [|eauto]; intros.
          destruct H3; auto. right.
          eapply incl_map; eauto. eapply st_follows_incl; eauto.
          eapply mmap_st_follows; eauto. eapply Forall_forall; intros. eapply switch_block_st_follows; eauto.
      + rewrite Forall_map. eapply Forall_forall; intros. constructor.
      + erewrite fst_NoDupMembers, map_map, map_ext, <-fst_NoDupMembers. 2:intros (?&?&?); auto.
        eapply cond_eq_NoDupMembers; eauto.
      + clear - H1 Hvalid'.
        eapply new_idents_st_ids' in H1.
        apply st_valid_NoDup in Hvalid'. rewrite H1 in Hvalid'.
        apply NoDup_app_l, NoDup_app_r, fst_NoDupMembers in Hvalid'; auto.
      + intros ? Hin1 Hinm2.
        erewrite fst_InMembers, map_map, map_ext in Hin1. eapply cond_eq_incl in Hin1; eauto.
        2:intros (?&?&?); auto.
        eapply new_idents_st_ids' in H1.
        apply st_valid_NoDup in Hvalid'. rewrite H1 in Hvalid'. apply NoDup_app_l in Hvalid'.
        rewrite fst_InMembers in Hinm2.
        eapply NoDup_app_In in Hvalid'; eauto.
      + subst. intros ? Hinm1 Hinm2. eapply NoDup_app_In in Hnd1'; eauto.
        eapply Hnd1'. apply fst_InMembers in Hinm1. erewrite map_app in Hinm1.
        rewrite in_app_iff in *. destruct Hinm1 as [Hinm1|Hinm1]; [left|auto].
        erewrite map_map, map_ext in Hinm1; eauto. intros (?&?&?); auto.
    - (* local *)
      constructor.
      + eapply switch_blocks_NoDupLocals' with (xs:=xs ++ map fst locs) in H0; eauto.
        * erewrite map_map, map_ext; eauto. intros (?&(?&?)&?); auto.
        * apply NoDup_app'; auto. apply fst_NoDupMembers; auto.
          eapply Forall_forall; intros ? Hinm1 Hinm2.
          eapply H7; eauto. apply fst_InMembers; auto.
        * apply Forall_app; split; auto.
          eapply Forall_impl; [|eauto]; intros; auto.
      + erewrite fst_NoDupMembers, map_map, map_ext, <-fst_NoDupMembers; eauto.
        intros (?&(?&?)&?); auto.
      + intros ? Hinm Hinm2. eapply H7; eauto.
        erewrite fst_InMembers, map_map, map_ext, <-fst_InMembers in Hinm; eauto.
        intros (?&(?&?)&?); auto.
  Qed.

  (** *** GoodLocals *)

  Lemma new_idents_AtomOrGensym : forall bck xc tx k ids nids st st',
      new_idents bck xc tx k ids st = (nids, st') ->
      Forall (fun '(_, x, _) => AtomOrGensym switch_prefs x) nids.
  Proof.
    intros * Hnids.
    apply mmap_values, Forall2_ignore1 in Hnids.
    eapply Forall_impl; [|eauto]. intros ((?&?)&?&?) ((?&?&?)&?&?&?&?); repeat inv_bind.
    eapply fresh_ident_prefixed in H0 as (?&?&?); subst.
    right. do 2 esplit; eauto.
    apply PSF.add_1; auto.
  Qed.

  Lemma cond_eq_AtomOrGensym : forall e tx bck xc xcs eqs' st st',
      cond_eq e tx bck st = ((xc, xcs), eqs', st') ->
      Forall (AtomOrGensym switch_prefs) (map fst xcs).
  Proof.
    unfold cond_eq. intros * Hcond.
    cases; repeat inv_bind; simpl; auto.
    1-10:try take (fresh_ident _ _ _ _ = _) and eapply fresh_ident_prefixed in it as (?&?&?); subst.
    1-10:constructor; auto; right; do 2 esplit; eauto; apply PSF.add_1; auto.
  Qed.

  Lemma switch_block_GoodLocals : forall blk env bck sub blk' st st',
      (forall x y, Env.MapsTo x y sub -> AtomOrGensym switch_prefs y) ->
      GoodLocals switch_prefs blk ->
      switch_block env bck sub blk st = (blk', st') ->
      GoodLocals switch_prefs blk'.
  Proof.
    induction blk using block_ind2; intros * Hsub Hgood Hsw;
      inv Hgood; simpl in *; repeat inv_bind.
    - (* equation *)
      constructor.
    - (* reset *)
      constructor.
      eapply Forall_forall; intros.
      eapply mmap_values, Forall2_ignore1, Forall_forall in H0 as (?&?&?&?&?); eauto.
      eapply Forall_forall in H; eauto. eapply H; eauto.
      eapply Forall_forall in H1; eauto.
    - (* switch *)
      destruct (partition _ _) as (defs&frees); repeat inv_bind; destruct x; repeat inv_bind.
      constructor; simpl; auto.
      1,2:repeat rewrite map_app; repeat rewrite Forall_app; repeat split.
      + erewrite map_map, map_ext. eapply cond_eq_AtomOrGensym; eauto.
        intros (?&?&?); auto.
      + rewrite flat_map_concat_map, concat_map. apply Forall_concat. rewrite map_map, Forall_map.
        eapply Forall_forall; intros (((?&?)&?)&?) ?.
        eapply mmap_values, Forall2_ignore1, Forall_forall in H2 as ((?&?)&?&?&?&?); eauto.
        repeat inv_bind. rewrite map_map, Forall_map.
        apply new_idents_AtomOrGensym in H5. apply new_idents_AtomOrGensym in H6.
        apply Forall_app; split; (eapply Forall_impl; [|eauto]); intros ((?&?)&?&?); auto.
      + rewrite Forall_map. apply Forall_forall; intros (?&?&?) _.
        constructor.
      + apply Forall_concat, Forall_forall; intros.
        eapply mmap2_values in H3. eapply mmap_values, Forall3_ignore3' with (zs:=x3) in H2.
        2:{ eapply Forall3_length in H3 as (?&?); congruence. }
        2:{ eapply mmap_length in H2; eauto. }
        eapply Forall3_Forall3 in H2; eauto. clear H3.
        eapply Forall3_ignore2, Forall2_ignore1, Forall_forall in H2 as ((?&?)&?&(((?&?)&?)&?)&(?&?&?)&?&?&?); eauto.
        repeat inv_bind.
        apply Forall_app; split.
        * eapply Forall_forall; intros.
          eapply mmap_values, Forall2_ignore1, Forall_forall in H3 as (?&?&?&?&?); eauto.
          repeat (eapply Forall_forall in H; eauto). eapply H with (sub:=Env.from_list _); eauto.
          -- intros ?? Hfind. apply Env.from_list_find_In, in_map_iff in Hfind as (((?&?)&?&?)&Heq&Hin); inv Heq.
             eapply new_idents_AtomOrGensym in H5. eapply new_idents_AtomOrGensym in H6.
             eapply in_app_iff in Hin as [Hin|Hin]; eapply Forall_forall in Hin; eauto; simpl in *; auto.
          -- repeat (eapply Forall_forall in H1; eauto).
        * rewrite Forall_map. eapply Forall_forall; intros ((?&?)&?&?) _. constructor.
      + rewrite Forall_map. eapply Forall_forall; intros. constructor.
    - (* local *)
      constructor; auto.
      + erewrite map_map, map_ext; eauto. intros (?&(?&?)&?); auto.
      + eapply Forall_forall; intros.
        eapply mmap_values, Forall2_ignore1, Forall_forall in H0 as (?&?&?&?&?); eauto.
        eapply Forall_forall in H; eauto. eapply H; eauto.
        eapply Forall_forall in H3; eauto.
  Qed.

  (** *** noswitch_block *)

  Lemma switch_noswitch : forall blk env bck sub blk' st st',
      switch_block env bck sub blk st = (blk', st') ->
      noswitch_block blk'.
  Proof.
    induction blk using block_ind2; intros * Hswitch; simpl in *; repeat inv_bind.
    - (* equation *)
      constructor.
    - (* reset *)
      constructor. eapply Forall_forall; intros.
      eapply mmap_values, Forall2_ignore1, Forall_forall in H0 as (?&?&?&?&?); eauto.
      repeat (take (Forall _ _) and eapply Forall_forall in it; eauto).
    - (* switch *)
      destruct (partition _ _). repeat inv_bind; destruct x; repeat inv_bind.
      repeat constructor. repeat rewrite Forall_app. repeat split.
      + rewrite Forall_map. eapply Forall_forall; intros (?&?&?) _.
        constructor.
      + apply Forall_concat. repeat (rewrite Forall_forall; intros).
        eapply mmap2_values in H2. eapply mmap_values, Forall3_ignore3' with (zs:=x3) in H1.
        2:{ eapply Forall3_length in H2 as (?&?); congruence. }
        2:{ eapply mmap_length in H1; eauto. }
        eapply Forall3_Forall3 in H1; eauto. clear H2.
        eapply Forall3_ignore2, Forall2_ignore1, Forall_forall in H1 as ((?&?)&?&(((?&?)&?)&?)&(?&?&?)&?&?&?); eauto.
        repeat inv_bind. apply in_app_iff in H4 as [Hin|Hin].
        * eapply mmap_values, Forall2_ignore1, Forall_forall in H2 as (?&?&?&?&?); eauto.
          repeat (take (Forall _ _) and eapply Forall_forall in it; eauto).
        * eapply in_map_iff in Hin as (((?&?)&?&?)&?&Hin); subst.
          constructor.
      + rewrite Forall_map. eapply Forall_forall; intros ??.
        constructor.
    - (* local *)
      constructor. eapply Forall_forall; intros.
      eapply mmap_values, Forall2_ignore1, Forall_forall in H0 as (?&?&?&?&?); eauto.
      repeat (take (Forall _ _) and eapply Forall_forall in it; eauto).
  Qed.

  (** ** Transformation of a node and program *)

  Program Definition switch_node (n: @node (fun _ => True) elab_prefs) : @node noswitch_block switch_prefs :=
    let res := switch_block (idty (n_in n ++ n_out n)) Cbase (@Env.empty _) (n_block n) init_st in
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
    pose proof (n_defd n) as (xs&Hperm&Hvars).
    pose proof (n_nodup n) as (Hnd1&Hnd2).
    eapply switch_block_VarsDefined with (xs:=xs) in Hsw as (xs'&Hperm'&Hvars'); eauto.
    exists xs'; split; auto.
    - rewrite Hvars'. now rewrite rename_vars_empty.
    - rewrite Hvars, map_fst_idty. solve_incl_app.
    - intros ? Hin. apply Env.Props.P.F.empty_in_iff in Hin. inv Hin.
    - rewrite NoDupMembers_idty; auto.
    - rewrite Hvars. apply fst_NoDupMembers; eauto using NoDupMembers_app_r.
    - eapply NoDupLocals_incl; [|eauto]. rewrite map_fst_idty. solve_incl_app.
  Qed.
  Next Obligation.
    destruct (switch_block _ _ _ _) eqn:Hsw; simpl in *.
    pose proof (n_nodup n) as (Hnd1&Hnd2).
    pose proof (n_good n) as (Hgood1&Hgood2&_).
    split; auto.
    eapply switch_block_NoDupLocals; eauto.
    + apply fst_NoDupMembers; auto.
    + eapply Forall_impl; eauto.
    + eapply init_st_valid; eauto using switch_not_in_elab_prefs, PS_For_all_empty.
  Qed.
  Next Obligation.
    destruct (switch_block _ _ _ _) eqn:Hsw; simpl in *.
    pose proof (n_nodup n) as (Hnd1&Hnd2).
    pose proof (n_good n) as (Hgood1&Hgood2&Hgood3).
    repeat split; eauto using AtomOrGensym_add.
    eapply switch_block_GoodLocals; eauto using GoodLocals_add, AtomOrGensym_add.
    intros ?? Hfind. apply Env.Props.P.F.empty_mapsto_iff in Hfind. inv Hfind.
  Qed.
  Next Obligation.
    destruct (switch_block _ _ _ _) eqn:Hsw.
    eapply switch_noswitch; eauto.
  Qed.

  Global Program Instance switch_node_transform_unit: TransformUnit node node :=
    { transform_unit := switch_node }.

  Global Program Instance switch_global_without_units : TransformProgramWithoutUnits (@global (fun _ => True) elab_prefs) (@global noswitch_block switch_prefs) :=
    { transform_program_without_units := fun g => Global g.(enums) [] }.

  Definition switch_global : @global (fun _ => True) elab_prefs -> @global noswitch_block switch_prefs :=
    transform_units.

  (** *** Equality of interfaces *)

  Lemma switch_global_iface_eq : forall G,
      global_iface_eq G (switch_global G).
  Proof.
    split; auto.
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
      exists ck2, In (x, (ty, ck2)) ids.
  Proof.
    intros * Hni Hin.
    eapply mmap_values, Forall2_ignore1, Forall_forall in Hni; eauto.
    destruct Hni as ((?&?&?)&?&?&?&?); repeat inv_bind; eauto.
  Qed.

  Section subclock_clockof.

    Variable bck : clock.
    Variable sub : Env.t ident.

    Lemma add_whens_clockof : forall e ty ck,
        clockof e = [Cbase] ->
        clockof (add_whens e ty ck) = [ck].
    Proof.
      intros * Hck.
      destruct ck as [|?? (?&?)]; simpl in *; auto.
    Qed.

    Lemma add_whens_nclockof : forall e ty ck,
        nclockof e = [(Cbase, None)] ->
        nclockof (add_whens e ty ck) = [(ck, None)].
    Proof.
      intros * Hck.
      destruct ck as [|?? (?&?)]; simpl in *; auto.
    Qed.

    Lemma subclock_exp_nclockof : forall e,
        nclockof (subclock_exp bck sub e) = map (subclock_nclock bck sub) (nclockof e).
    Proof.
      destruct e; simpl in *; auto.
      - (* const *)
        apply add_whens_nclockof; auto.
      - (* enum *)
        apply add_whens_nclockof; auto.
      - (* fby *)
        rewrite 2 map_map; auto.
      - (* arrow *)
        rewrite 2 map_map; auto.
      - (* when *)
        rewrite map_map; auto.
      - (* merge *)
        destruct p; simpl. rewrite map_map; auto.
      - (* case *)
        rewrite map_map; auto.
      - (* app *)
        rewrite 2 map_map; auto.
    Qed.

    Corollary subclock_exp_nclocksof : forall es,
        nclocksof (map (subclock_exp bck sub) es) = map (subclock_nclock bck sub) (nclocksof es).
    Proof.
      intros es.
      unfold nclocksof. rewrite 2 flat_map_concat_map, concat_map, 2 map_map.
      f_equal.
      eapply map_ext; intros. apply subclock_exp_nclockof.
    Qed.

    Corollary subclock_exp_clockof : forall e,
        clockof (subclock_exp bck sub e) = map (subclock_clock bck sub) (clockof e).
    Proof.
      intros.
      rewrite 2 clockof_nclockof, subclock_exp_nclockof, 2 map_map; auto.
    Qed.

    Corollary subclock_exp_clocksof : forall es,
        clocksof (map (subclock_exp bck sub) es) = map (subclock_clock bck sub) (clocksof es).
    Proof.
      intros es.
      unfold clocksof. rewrite 2 flat_map_concat_map, concat_map, 2 map_map.
      f_equal.
      eapply map_ext; intros. apply subclock_exp_clockof.
    Qed.

  End subclock_clockof.

  Section subclock_typeof.

    Variable bck : clock.
    Variable sub : Env.t ident.

    Lemma add_whens_typeof : forall e ty ck,
        typeof e = [ty] ->
        typeof (add_whens e ty ck) = [ty].
    Proof.
      intros * Hty.
      destruct ck as [|?? (?&?)]; simpl in *; auto.
    Qed.

    Lemma subclock_exp_typeof : forall e,
        typeof (subclock_exp bck sub e) = typeof e.
    Proof.
      destruct e; simpl in *; auto.
      - (* const *)
        apply add_whens_typeof; auto.
      - (* enum *)
        apply add_whens_typeof; auto.
      - (* fby *)
        rewrite map_map; auto.
      - (* arrow *)
        rewrite map_map; auto.
      - (* merge *)
        destruct p; simpl; auto.
      - (* app *)
        rewrite map_map; auto.
    Qed.

    Corollary subclock_exp_typesof : forall es,
        typesof (map (subclock_exp bck sub) es) = typesof es.
    Proof.
      intros es.
      unfold typesof . rewrite 2 flat_map_concat_map, map_map.
      f_equal.
      eapply map_ext; intros. apply subclock_exp_typeof.
    Qed.
  End subclock_typeof.

End CLOCKSWITCH.

Module ClockSwitchFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks : CLOCKS Ids Op OpAux)
       (Syn : LSYNTAX Ids Op OpAux Cks)
       <: CLOCKSWITCH Ids Op OpAux Cks Syn.
  Include CLOCKSWITCH Ids Op OpAux Cks Syn.
End ClockSwitchFun.
