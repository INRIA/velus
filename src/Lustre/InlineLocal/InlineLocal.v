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

  (* Be your own, personal, monad *)
  Record reuse_st := {
      fresh_st: fresh_st local unit; (* We dont actually need to keep type information in here *)
      used: PS.t; (* Identifiers already used *)
    }.

  Definition Reuse A := reuse_st -> (A * reuse_st).

  Definition reuse_ident (x : ident) : Reuse ident :=
    fun st =>
      if PS.mem x st.(used) then
        let (y, st') := fresh_ident (Some x) tt st.(fresh_st) in
        (y, {| fresh_st := st'; used := st.(used) |})
      else
        (x, {| fresh_st := st.(fresh_st); used := PS.add x st.(used) |}).

  Section ret.
    Context {A : Type}.
    Definition ret (x : A) : Reuse A := fun st => (x, st).

    Fact ret_spec : forall a st,
        ret a st = (a, st).
    Proof.
      intros a st. reflexivity.
    Qed.
  End ret.

  Section bind.
    Context {A B : Type}.
    Definition bind (x : Reuse A) (k : A -> Reuse B) : Reuse B :=
      fun st => let '(a, st') := x st in k a st'.

    Lemma bind_spec : forall (x : Reuse A) (k : A -> Reuse B) st a' st'',
        (bind x k) st = (a', st'') <->
        exists a, exists st', (x st = (a, st') /\ k a st' = (a', st'')).
    Proof.
      intros x k st a' st''. split; intros.
      - unfold bind in H.
        destruct (x st) as [a st']. exists a. exists st'.
        split; auto.
      - destruct H as [a [st' [H1 H2]]]. unfold bind.
        rewrite H1. assumption.
    Qed.
  End bind.

  Section bind2.
    Context {A1 A2 B : Type}.
    Definition bind2 (x : Reuse (A1 * A2)) (k : A1 -> A2 -> Reuse B) : Reuse B :=
      fun st => let '((a1, a2), st') := x st in k a1 a2 st'.

    Lemma bind2_spec : forall (x : Reuse (A1 * A2)) (k : A1 -> A2 -> Reuse B) st a' st'',
        (bind2 x k) st = (a', st'') <->
          exists a1, exists a2, exists st', (x st = ((a1, a2), st') /\ k a1 a2 st' = (a', st'')).
    Proof.
      intros x k st a' st''. split; intros.
      - unfold bind2 in H.
        destruct (x st) as [[a1 a2] st']. exists a1. exists a2. exists st'.
        split; auto.
      - destruct H as [a1 [a2 [st' [H1 H2]]]]. unfold bind2.
        rewrite H1. assumption.
    Qed.
  End bind2.

  Definition st_In x (st : reuse_st) :=
    In x (st_ids (fresh_st st)) \/ PS.In x (used st).

  Definition st_valid (st : reuse_st) :=
    PS.For_all (AtomOrGensym switch_prefs) (used st).

  Definition st_follows (st1 st2 : reuse_st) :=
    st_follows (fresh_st st1) (fresh_st st2) /\ PS.Subset (used st1) (used st2).

  Global Instance st_follows_Reflexive : Reflexive st_follows.
  Proof. split; reflexivity. Qed.
  Global Instance st_follows_Transitive : Transitive st_follows.
  Proof. intros ??? (?&?) (?&?). split; etransitivity; eauto. Qed.

  Lemma st_follows_In : forall st1 st2,
      st_follows st1 st2 ->
      forall x, st_In x st1 -> st_In x st2.
  Proof.
    intros * (F1&F2) ? [In|In]; [left|right]; eauto.
    eapply incl_map; eauto using st_follows_incl.
  Qed.

  Declare Scope reuse_monad_scope.
  Notation "'do' X <- A ; B" :=
    (bind A (fun X => B))
      (at level 200, X name, A at level 100, B at level 200): reuse_monad_scope.
  Notation "'do' ( X , Y ) <- A ; B" :=
    (bind2 A (fun X Y => B))
      (at level 200, X name, Y name, A at level 100, B at level 200): reuse_monad_scope.
  Open Scope reuse_monad_scope.

  Ltac monadInv :=
    simpl in *;
    match goal with
    | H : context c [ret _ _] |- _ =>
        rewrite ret_spec in H
    | H : (_, _) = (_, _) |- _ =>
        inv H
    | H : bind _ _ _ = (_, _) |- _ =>
        apply bind_spec in H; destruct H as [? [? [? ?]]]; simpl in *
    | H : bind2 _ _ _ = (_, _) |- _ =>
        apply bind2_spec in H; destruct H as [? [? [? [? ?]]]]; simpl in *
    | |- context c [ret _ _] =>
        rewrite ret_spec
    | |- bind _ _ _ = (_, _) =>
        rewrite bind_spec; repeat esplit
    | |- bind2 _ _ _ = (_, _) =>
        rewrite bind2_spec; repeat esplit
    end.

  Section mmap.
    Context {A B : Type}.
    Variable k : A -> Reuse B.
    Fixpoint mmap a :=
      match a with
      | nil => ret nil
      | hd::tl => do a1 <- k hd;
                do a1s <- mmap tl;
                ret (a1::a1s)
      end.

    Fact mmap_values : forall a st a1s st',
        mmap a st = (a1s, st') ->
        Forall2 (fun a a1 => exists st'', exists st''', k a st'' = (a1, st''')) a a1s.
    Proof.
      induction a; intros st a1s st' Hfold; simpl in *; repeat monadInv.
      - constructor.
      - specialize (IHa _ _ _ H0).
        constructor; eauto.
    Qed.

    Fact mmap_st_valid : forall a a1s st st',
        mmap a st = (a1s, st') ->
        Forall (fun a => forall a1 st st', k a st = (a1, st') -> st_valid st -> st_valid st') a ->
        st_valid st ->
        st_valid st'.
    Proof.
      induction a; intros * Hmap F Val; inv F; repeat monadInv; eauto.
    Qed.

    Fact mmap_st_follows : forall a a1s st st',
        mmap a st = (a1s, st') ->
        Forall (fun a => forall a1 st st', k a st = (a1, st') -> st_follows st st') a ->
        st_follows st st'.
    Proof.
      induction a; intros * Hmap F; inv F; repeat monadInv; auto.
      - reflexivity.
      - etransitivity; eauto.
    Qed.

    Fact mmap_values_follows : forall a st a1s st',
        (forall a a1 st st', k a st = (a1, st') -> st_follows st st') ->
        mmap a st = (a1s, st') ->
        Forall2 (fun a a1 =>
                   exists st'' st''',
                     st_follows st st''
                     /\ st_follows st''' st'
                     /\ k a st'' = (a1, st''')) a a1s.
    Proof.
      induction a; intros * Follows Hfold; repeat monadInv.
      - constructor.
      - constructor.
        + do 2 esplit; split; [|split]. 3:eauto. reflexivity.
          eapply mmap_st_follows; eauto. simpl_Forall; eauto.
        + eapply IHa in H0; eauto.
          simpl_Forall.
          do 2 esplit; split; [|split]. 3:eauto. 2:eauto. etransitivity; eauto.
    Qed.

    Fact mmap_values' : forall a st a1s st',
        Forall (fun a => forall a1 st st', k a st = (a1, st') -> st_valid st -> st_valid st') a ->
        (forall a a1 st st', k a st = (a1, st') -> st_follows st st') ->
        mmap a st = (a1s, st') ->
        st_valid st ->
        Forall2 (fun a a1 =>
                   exists st'' st''',
                     st_valid st''
                     /\ st_follows st st''
                     /\ st_follows st''' st'
                     /\ k a st'' = (a1, st''')) a a1s.
    Proof.
      induction a; intros * Valid Follows Hfold V; inv Valid; repeat monadInv.
      - constructor.
      - constructor.
        + do 2 esplit; split; [|split; [|split]]. 1,4:eauto. reflexivity.
          eapply mmap_st_follows; eauto. simpl_Forall; eauto.
        + eapply IHa in H0; eauto.
          simpl_Forall.
          do 2 esplit; split; [|split; [|split]]. 1,4:eauto. 2:eauto. etransitivity; eauto.
    Qed.
  End mmap.

  Section mmap2.
    Context {A A1 A2 : Type}.
    Variable k : A -> Reuse (A1 * A2).
    Fixpoint mmap2 (a : list A) : Reuse (list A1 * list A2) :=
      match a with
      | nil => ret (nil, nil)
      | hd::tl => do (a1, a2) <- k hd;
                do (a1s, a2s) <- mmap2 tl;
                ret (a1::a1s, a2::a2s)
      end.

    Fact mmap2_values : forall a st a1s a2s st',
        mmap2 a st = (a1s, a2s, st') ->
        Forall3 (fun a a1 a2 => exists st'', exists st''', k a st'' = (a1, a2, st''')) a a1s a2s.
    Proof.
      induction a; intros st a1s a2s st' Hfold; simpl in *; repeat monadInv.
      - constructor.
      - specialize (IHa _ _ _ _ H0).
        constructor; eauto.
    Qed.

    Fact mmap2_st_valid : forall a a1s a2s st st',
        mmap2 a st = (a1s, a2s, st') ->
        Forall (fun a => forall a1 a2 st st', k a st = (a1, a2, st') -> st_valid st -> st_valid st') a ->
        st_valid st ->
        st_valid st'.
    Proof.
      induction a; intros a1s a2s st st' Hmap F; inv F; repeat monadInv; eauto.
    Qed.

    Fact mmap2_st_follows : forall a a1s a2s st st',
        mmap2 a st = (a1s, a2s, st') ->
        Forall (fun a => forall a1 a2 st st', k a st = (a1, a2, st') -> st_follows st st') a ->
        st_follows st st'.
    Proof.
      induction a; intros a1s a2s st st' Hmap F; inv F; repeat monadInv.
      - reflexivity.
      - etransitivity; eauto.
    Qed.

    Fact mmap2_values_follows : forall a st a1s a2s st',
        (forall a a1 a2 st st', k a st = (a1, a2, st') -> st_follows st st') ->
        mmap2 a st = (a1s, a2s, st') ->
        Forall3 (fun a a1 a2 =>
                   exists st'' st''',
                     st_follows st st''
                     /\ st_follows st''' st'
                     /\ k a st'' = (a1, a2, st''')) a a1s a2s.
    Proof.
      induction a; intros * Follows Hfold; simpl in *; repeat monadInv.
      - constructor.
      - constructor.
        + do 2 esplit; split; [|split]. 3:eauto. reflexivity.
          eapply mmap2_st_follows; eauto. simpl_Forall; eauto.
        + eapply IHa in H0; eauto.
          eapply Forall3_impl_In; [|eauto]. intros; destruct_conjs.
          do 2 esplit; split; [|split]. 3:eauto. 2:eauto. etransitivity; eauto.
    Qed.

    Fact mmap2_values' : forall a st a1s a2s st',
        Forall (fun a => forall a1 a2 st st', k a st = (a1, a2, st') -> st_valid st -> st_valid st') a ->
        (forall a a1 a2 st st', k a st = (a1, a2, st') -> st_follows st st') ->
        mmap2 a st = (a1s, a2s, st') ->
        st_valid st ->
        Forall3 (fun a a1 a2 =>
                   exists st'' st''',
                     st_valid st''
                     /\ st_follows st st''
                     /\ st_follows st''' st'
                     /\ k a st'' = (a1, a2, st''')) a a1s a2s.
    Proof.
      induction a; intros * Valid Follows Hfold V; inv Valid; repeat monadInv.
      - constructor.
      - constructor.
        + do 2 esplit; split; [|split; [|split]]. 1,4:eauto. reflexivity.
          eapply mmap2_st_follows; eauto. simpl_Forall; eauto.
        + eapply IHa in H0; eauto.
          eapply Forall3_impl_In; [|eauto]. intros; destruct_conjs.
          do 2 esplit; split; [|split; [|split]]. 1,4:eauto. 2:eauto. etransitivity; eauto.
    Qed.
  End mmap2.

  Fixpoint inlinelocal_block sub (blk : block) : Reuse (list (ident * ann) * list block) :=
    match blk with
    | Beq eq => ret ([], [Beq (rename_in_equation sub eq)])
    | Breset blks er =>
        do (locs, blks') <- mmap2 (inlinelocal_block sub) blks;
        ret (concat locs, [Breset (concat blks') (rename_in_exp sub er)])
    | Blocal (Scope locs blks) =>
        let xs := map fst locs in
        do newlocs <- mmap reuse_ident xs;
        let sub1 := Env.from_list (combine xs newlocs) in
        let sub' := Env.union sub sub1 in
        let locs' := map (fun '(x, (ty, ck, _, _)) => (rename_var sub' x, (ty, (rename_in_clock sub' ck)))) locs in
        do (locs1, blks') <- mmap2 (inlinelocal_block sub') blks;
        ret (locs'++concat locs1, concat blks')
    | _ => (* Should not happen *) ret ([], [blk])
    end.

  (** ** State properties *)

  (* Lemma inlinelocal_block_st_follows : forall blk sub blks' st st', *)
  (*     inlinelocal_block sub blk st = (blks', st') -> *)
  (*     st_follows st st'. *)
  (* Proof. *)
  (*   induction blk using block_ind2; intros * Hdl; repeat inv_bind; try reflexivity. *)
  (*   - (* reset *) *)
  (*     eapply mmap_st_follows in H0; eauto. *)
  (*     rewrite Forall_forall in *; eauto. *)
  (*   - (* local *) *)
  (*     eapply fresh_idents_rename_st_follows in H0; eauto. *)
  (*     etransitivity; eauto. *)
  (*     eapply mmap_st_follows in H1; eauto. *)
  (*     rewrite Forall_forall in *; eauto. *)
  (* Qed. *)

  (* Global Hint Resolve inlinelocal_block_st_follows : fresh. *)

  (** ** Wellformedness properties *)

  (** *** VarsDefined *)

  Import Permutation.

  Fact mmap_vars_perm : forall (f : _ -> block -> Reuse (list (ident * ann) * list block)) blks sub locs' blks' xs st st',
      Forall
        (fun blk => forall sub locs' blks' xs st st',
             noswitch_block blk ->
             VarsDefined blk xs ->
             NoDupLocals (map fst (Env.elements sub) ++ xs) blk ->
             f sub blk st = (locs', blks', st') ->
             exists ys, Forall2 VarsDefined blks' ys /\ Permutation (concat ys) (map (rename_var sub) xs ++ map fst locs')) blks ->
      Forall noswitch_block blks ->
      Forall2 VarsDefined blks xs ->
      Forall (NoDupLocals (map fst (Env.elements sub) ++ concat xs)) blks ->
      mmap2 (f sub) blks st = (locs', blks', st') ->
      exists ys, Forall2 VarsDefined (concat blks') ys /\ Permutation (concat ys) (map (rename_var sub) (concat xs) ++ map fst (concat locs')).
  Proof.
    induction blks; intros * Hf Hns Hvars Hnd Hnorm; inv Hf; inv Hns; inv Hvars; inv Hnd; repeat monadInv; simpl.
    - exists []. split; auto.
    - eapply H1 in H as (ys1&Hvars1&Hperm1); eauto.
      2:eapply NoDupLocals_incl; [|eauto]; solve_incl_app.
      eapply IHblks in H2 as (ys2&Hvars2&Hperm2); eauto. clear IHblks.
      2:simpl_Forall; intros; eapply NoDupLocals_incl; [|eauto]; solve_incl_app.
      exists (ys1 ++ ys2). split.
      + apply Forall2_app; auto.
      + rewrite concat_app, Hperm1, Hperm2. solve_Permutation_app.
  Qed.

  Lemma inlinelocal_block_vars_perm : forall blk sub locs' blks' xs st st',
      noswitch_block blk ->
      VarsDefined blk xs ->
      NoDupLocals (map fst (Env.elements sub) ++ xs) blk ->
      inlinelocal_block sub blk st = (locs', blks', st') ->
      exists ys, Forall2 VarsDefined blks' ys /\ Permutation (concat ys) (map (rename_var sub) xs ++ map fst locs').
  Proof.
    induction blk using block_ind2; intros * Hns Hvars Hnd Hdl;
      inv Hns; inv Hvars; inv Hnd; repeat monadInv.
    - (* equation *)
      destruct eq.
      repeat esplit; simpl; eauto using VarsDefined with datatypes.
    - (* reset *)
      eapply mmap_vars_perm in H0 as (ys1&Hvars1&Hperm1); eauto.
      do 2 esplit; eauto using VarsDefined.
      simpl. now rewrite app_nil_r.
    - (* local *)
      repeat inv_scope. take (Permutation _ _) and rename it into Hperm.
      eapply mmap_vars_perm in H4 as (ys1&Hvars1&Hperm1); eauto.
      2:{ simpl_Forall.
          eapply NoDupLocals_incl; [|eauto].
          rewrite <-app_assoc, Hperm.
          apply incl_app; try solve [solve_incl_app].
          intros ? Hin. simpl_In.
          eapply Env.elements_complete, Env.union_find4 in Hin0 as [Hfind|Hfind].
          - eapply Env.elements_correct in Hfind.
            apply in_or_app, or_introl; solve_In.
          - eapply Env.from_list_find_In, in_combine_l in Hfind.
            rewrite 2 in_app_iff. auto.
      }
      rewrite Hperm, map_app in Hperm1.
      do 2 esplit; eauto. rewrite Hperm1, map_app, 2 map_map, <-app_assoc.
      erewrite not_in_union_map_rename2, map_ext with (l:=locs). reflexivity.
      + intros; destruct_conjs. reflexivity.
      + simpl_Forall. intros In.
        eapply Env.In_from_list, InMembers_In_combine, fst_InMembers in In.
        eapply H12; eauto with datatypes.
  Qed.

  (** *** st_valid *)

  Lemma reuse_ident_st_valid : forall x y st st',
      AtomOrGensym switch_prefs x ->
      reuse_ident x st = (y, st') ->
      st_valid st ->
      st_valid st'.
  Proof.
    intros * At Reu V. unfold reuse_ident in *.
    cases_eqn EQ; inv_equalities; simpl.
    apply PS_For_all_add. split; auto.
  Qed.

  Corollary reuse_idents_st_valid : forall locs locs' st st',
      Forall (AtomOrGensym switch_prefs) locs ->
      mmap reuse_ident locs st = (locs', st') ->
      st_valid st ->
      st_valid st'.
  Proof.
    intros * At Map V.
    eapply mmap_st_valid; eauto. simpl_Forall; eauto using reuse_ident_st_valid.
  Qed.

  Lemma inlinelocal_block_st_valid : forall blk sub locs' blks' st st',
      GoodLocals switch_prefs blk ->
      inlinelocal_block sub blk st = (locs', blks', st') ->
      st_valid st ->
      st_valid st'.
  Proof.
    induction blk using block_ind2; intros * Good Il V; inv Good;
      repeat monadInv; auto.
    - (* reset *)
      eapply mmap2_st_valid; eauto.
      simpl_Forall; eauto.
    - (* local *)
      repeat inv_scope.
      eapply mmap2_st_valid; eauto using reuse_idents_st_valid. simpl_Forall; eauto.
  Qed.

  (** *** st_follows *)

  Lemma reuse_ident_st_follows : forall x y st st',
      reuse_ident x st = (y, st') ->
      st_follows st st'.
  Proof.
    intros * Reu. unfold reuse_ident in *.
    cases_eqn EQ; inv_equalities; split; try reflexivity; simpl.
    - eauto using fresh_ident_st_follows.
    - intros ??; eauto using PSF.add_2.
  Qed.

  Lemma inlinelocal_block_st_follows : forall blk sub locs' blks' st st',
      inlinelocal_block sub blk st = (locs', blks', st') ->
      st_follows st st'.
  Proof.
    induction blk using block_ind2; intros * Il; repeat monadInv; try reflexivity.
    - (* reset *)
      eapply mmap2_st_follows; eauto.
      simpl_Forall; eauto.
    - (* local *)
      etransitivity.
      + eapply mmap_st_follows; eauto. simpl_Forall; eauto using reuse_ident_st_follows.
      + eapply mmap2_st_follows; eauto.
        simpl_Forall; eauto.
  Qed.

  (** *** GoodLocals *)

  Lemma inlinelocal_block_GoodLocals : forall blk sub blks' locs' st st',
      noswitch_block blk ->
      inlinelocal_block sub blk st = (locs', blks', st') ->
      Forall (GoodLocals local_prefs) blks'.
  Proof.
    induction blk using block_ind2; intros * Hns Hdl; inv Hns; repeat monadInv.
    - (* equation *)
      repeat constructor.
    - (* reset *)
      repeat constructor. apply Forall_concat.
      eapply mmap2_values, Forall3_ignore12 in H0. simpl_Forall.
      eapply H in H4; eauto. simpl_Forall; auto.
    - (* local *)
      apply Forall_concat.
      eapply mmap2_values, Forall3_ignore12 in H1. simpl_Forall.
      eapply H in H6; eauto. simpl_Forall; auto.
  Qed.

  Lemma reuse_idents_find {A} : forall (locs: list (ident * A)) locs' st st' x,
      NoDupMembers locs ->
      mmap reuse_ident (map fst locs) st = (locs', st') ->
      InMembers x locs ->
      exists st st' y,
        reuse_ident x st = (y, st')
        /\ Env.find x (Env.from_list (combine (map fst locs) locs')) = Some y.
  Proof.
    intros * ND Reuse In. apply fst_InMembers in In.
    eapply mmap_values, Forall2_forall2 in Reuse as (Len&Nth).
    eapply In_nth with (d:=xH) in In as (?&N&NthLocs); subst.
    setoid_rewrite Env.find_In_from_list.
    3:now apply NoDup_NoDupMembers_combine, fst_NoDupMembers.
    2:{ erewrite <-combine_nth; [|eauto].
        eapply nth_In with (d:=(xH, xH)). now rewrite combine_length, <-Len, Nat.min_id. }
    specialize (Nth xH xH _ _ _ N eq_refl eq_refl) as (?&?&?).
    do 2 esplit; eauto.
  Qed.

  Lemma reuse_idents_find_follows {A} : forall (locs: list (ident * A)) locs' st st' x,
      NoDupMembers locs ->
      mmap reuse_ident (map fst locs) st = (locs', st') ->
      InMembers x locs ->
      exists st1 st1' y,
        st_follows st st1
        /\ st_follows st1' st'
        /\ reuse_ident x st1 = (y, st1')
        /\ Env.find x (Env.from_list (combine (map fst locs) locs')) = Some y.
  Proof.
    intros * ND Reuse In. apply fst_InMembers in In.
    eapply mmap_values_follows, Forall2_forall2 in Reuse as (Len&Nth); eauto using reuse_ident_st_follows.
    eapply In_nth with (d:=xH) in In as (?&N&NthLocs); subst.
    setoid_rewrite Env.find_In_from_list.
    3:now apply NoDup_NoDupMembers_combine, fst_NoDupMembers.
    2:{ erewrite <-combine_nth; [|eauto].
        eapply nth_In with (d:=(xH, xH)). now rewrite combine_length, <-Len, Nat.min_id. }
    specialize (Nth xH xH _ _ _ N eq_refl eq_refl) as (?&?&?&?&?).
    do 2 esplit; eauto.
  Qed.

  Lemma reuse_idents_find' {A} : forall (locs: list (ident * A)) locs' st st' x,
      NoDupMembers locs ->
      Forall (AtomOrGensym switch_prefs) (map fst locs) ->
      mmap reuse_ident (map fst locs) st = (locs', st') ->
      st_valid st ->
      InMembers x locs ->
      exists st1 st1' y,
        st_valid st1
        /\ st_follows st st1
        /\ st_follows st1' st'
        /\ reuse_ident x st1 = (y, st1')
        /\ Env.find x (Env.from_list (combine (map fst locs) locs')) = Some y.
  Proof.
    intros * ND At Reuse V In. apply fst_InMembers in In.
    eapply mmap_values', Forall2_forall2 in Reuse as (Len&Nth); eauto using reuse_ident_st_follows.
    2:{ clear In. simpl_Forall; eauto using reuse_ident_st_valid. }
    eapply In_nth with (d:=xH) in In as (?&N&NthLocs); subst.
    setoid_rewrite Env.find_In_from_list.
    3:now apply NoDup_NoDupMembers_combine, fst_NoDupMembers.
    2:{ erewrite <-combine_nth; [|eauto].
        eapply nth_In with (d:=(xH, xH)). now rewrite combine_length, <-Len, Nat.min_id. }
    specialize (Nth xH xH _ _ _ N eq_refl eq_refl) as (?&?&?&?&?&?).
    do 2 esplit; eauto 6.
  Qed.

  Lemma inlinelocal_block_AtomOrGensym : forall blk Γ sub blks' locs' st st',
      NoDupLocals Γ blk ->
      GoodLocals switch_prefs blk ->
      inlinelocal_block sub blk st = (locs', blks', st') ->
      Forall (fun '(x, _) => AtomOrGensym local_prefs x) locs'.
  Proof.
    induction blk using block_ind2; intros * ND Good Hdl; inv ND; inv Good; repeat monadInv; try constructor.
    - (* reset *)
      apply Forall_concat.
      eapply mmap2_values, Forall3_ignore13 in H0. simpl_Forall.
      eapply H in H5; eauto. simpl_Forall; auto.
    - (* local *)
      repeat inv_scope.
      apply Forall_app; split.
      + simpl_Forall. eapply reuse_idents_find in H0 as (?&?&?&Reu&Find); eauto using In_InMembers.
        unfold rename_var. erewrite Env.union_find3'; eauto. simpl.
        unfold reuse_ident in Reu. cases_eqn EQ; inv_equalities.
        * eapply fresh_ident_prefixed in EQ0 as (?&?&?); subst.
          right. do 2 esplit; eauto using PSF.add_1.
        * eauto using AtomOrGensym_add.
      + apply Forall_concat.
        eapply mmap2_values, Forall3_ignore13 in H3. simpl_Forall.
        eapply H in H4; eauto. simpl_Forall; auto.
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

  Lemma inlinelocal_block_NoDupLocals xs : forall blk sub locs' blks' st st',
      noswitch_block blk ->
      inlinelocal_block sub blk st = (locs', blks', st') ->
      Forall (NoDupLocals xs) blks'.
  Proof.
    induction blk using block_ind2; intros * Hns Hdl; inv Hns; repeat monadInv; repeat constructor.
    - (* reset *)
      eapply mmap2_values, Forall3_ignore12 in H0.
      eapply Forall_concat. simpl_Forall.
      eapply H in H4; eauto. now simpl_Forall.
    - (* local *)
      eapply mmap2_values, Forall3_ignore12 in H1.
      eapply Forall_concat. simpl_Forall.
      eapply H in H6; eauto. now simpl_Forall.
  Qed.

  Lemma local_not_in_switch_prefs :
    ~PS.In local switch_prefs.
  Proof.
    unfold switch_prefs, auto_prefs, last_prefs, elab_prefs.
    rewrite 3 PS.add_spec, PSF.singleton_iff.
    pose proof gensym_prefs_NoDup as Hnd. unfold gensym_prefs in Hnd.
    repeat rewrite NoDup_cons_iff in Hnd. destruct_conjs.
    intros [contra|[contra|[contra|contra]]]; subst; rewrite contra in *; eauto 10 with datatypes.
  Qed.

  Lemma reuse_ident_In : forall x y st st',
      reuse_ident x st = (y, st') ->
      PS.In x (used st').
  Proof.
    intros * Reu. unfold reuse_ident in *.
    cases_eqn EQ.
    inv Reu; eauto using PSF.add_1.
  Qed.

  Corollary reuse_idents_In : forall locs locs' st st',
    mmap reuse_ident locs st = (locs', st') ->
    Forall (fun x => PS.In x (used st')) locs.
  Proof.
    intros * Reu.
    eapply mmap_values_follows, Forall2_ignore2 in Reu; eauto using reuse_ident_st_follows.
    simpl_Forall.
    eapply H2, reuse_ident_In; eauto.
  Qed.

  Lemma reuse_ident_st_In : forall x y st st',
      reuse_ident x st = (y, st') ->
      st_In y st'.
  Proof.
    intros * Reu. unfold reuse_ident in *.
    cases_eqn EQ; inv_equalities.
    - left. eapply fresh_ident_Inids; eauto.
    - right. eauto using PSF.add_1.
  Qed.

  Corollary reuse_idents_st_In : forall locs locs' st st',
    mmap reuse_ident locs st = (locs', st') ->
    Forall (fun x => st_In x st') locs'.
  Proof.
    intros * Reu.
    eapply mmap_values_follows, Forall2_ignore1 in Reu; eauto using reuse_ident_st_follows.
    simpl_Forall.
    eapply reuse_ident_st_In in H3; eauto using st_follows_In.
  Qed.

  Lemma inlinelocal_block_st_In : forall blk Γ sub blks' locs' st st',
      NoDupLocals Γ blk ->
      inlinelocal_block sub blk st = (locs', blks', st') ->
      Forall (fun '(x, _) => st_In x st') locs'.
  Proof.
    induction blk using block_ind2; intros * ND IL; inv ND;
      repeat monadInv; try constructor.
    - (* reset *)
      eapply mmap2_values_follows, Forall3_ignore13 in H0; eauto using inlinelocal_block_st_follows.
      apply Forall_concat. simpl_Forall.
      eapply H in H6; eauto. simpl_Forall; eauto using st_follows_In.
    - (* local *)
      inv H2.
      apply Forall_app; split.
      + simpl_Forall.
        eapply reuse_idents_find_follows in H0 as (?&?&?&F1&F2&Reu&Find); eauto using In_InMembers.
        unfold rename_var. erewrite Env.union_find3'; eauto. simpl.
        eapply reuse_ident_st_In in Reu. eapply st_follows_In; [|eauto].
        etransitivity; eauto. eapply mmap2_st_follows; eauto. simpl_Forall; eauto using inlinelocal_block_st_follows.
      + eapply mmap2_values_follows, Forall3_ignore13 in H1; eauto using inlinelocal_block_st_follows.
        apply Forall_concat. simpl_Forall.
        eapply H in H9; eauto. simpl_Forall. eauto using st_follows_In.
  Qed.

  Lemma reuse_ident_st_nIn : forall x y st st',
      AtomOrGensym switch_prefs x ->
      st_valid st ->
      reuse_ident x st = (y, st') ->
      ~st_In y st.
  Proof.
    intros * At1 At2 Reu. unfold reuse_ident in *.
    cases_eqn EQ; inv_equalities.
    - intros [In|In].
      + eapply fresh_ident_nIn; eauto.
      + eapply At2 in In.
        eapply st_valid_AtomOrGensym_nIn; eauto using local_not_in_switch_prefs, fresh_ident_Inids.
    - apply PSE.mem_4 in EQ.
      contradict EQ. destruct EQ as [In|In]; auto.
      exfalso. eapply st_valid_AtomOrGensym_nIn; eauto using local_not_in_switch_prefs.
  Qed.

  Corollary reuse_idents_st_nIn : forall locs locs' st st',
      Forall (AtomOrGensym switch_prefs) locs ->
      st_valid st ->
      mmap reuse_ident locs st = (locs', st') ->
      Forall (fun y => ~st_In y st) locs'.
  Proof.
    intros * F V Map.
    eapply mmap_values', Forall2_ignore1 in Map; eauto using reuse_ident_st_follows.
    2:{ simpl_Forall; eauto using reuse_ident_st_valid. }
    simpl_Forall. eapply reuse_ident_st_nIn in H4; eauto using st_follows_In.
  Qed.

  Lemma inlinelocal_block_st_nIn : forall blk Γ sub blks' locs' st st',
      NoDupLocals Γ blk ->
      GoodLocals switch_prefs blk ->
      st_valid st ->
      inlinelocal_block sub blk st = (locs', blks', st') ->
      Forall (fun '(x, _) => ~ (st_In x st)) locs'.
  Proof.
    induction blk using block_ind2; intros * ND Good V IL; inv ND; inv Good;
      repeat monadInv; try constructor.
    - (* reset *)
      eapply mmap2_values', Forall3_ignore13 in H0; eauto using inlinelocal_block_st_follows.
      2:{ simpl_Forall; eauto using inlinelocal_block_st_valid. }
      apply Forall_concat. simpl_Forall.
      take (inlinelocal_block _ _ _ = _) and eapply H in it; eauto. simpl_Forall; eauto using st_follows_In.
    - (* local *)
      repeat inv_scope.
      apply Forall_app; split.
      + eapply Forall_forall. intros. simpl_In.
        eapply reuse_idents_find' in H0 as (?&?&?&V1&F1&F2&Reu&Find); eauto using In_InMembers.
        unfold rename_var. erewrite Env.union_find3'; eauto. simpl.
        simpl_Forall. eapply reuse_ident_st_nIn in Reu; eauto.
        contradict Reu; eauto using st_follows_In.
      + eapply mmap2_values', Forall3_ignore13 in H3; eauto using inlinelocal_block_st_follows, reuse_idents_st_valid.
        2:{ simpl_Forall; eauto using inlinelocal_block_st_valid. }
        apply Forall_concat. simpl_Forall.
        take (inlinelocal_block _ _ _ = _) and eapply H in it; eauto. simpl_Forall. contradict it.
        eapply st_follows_In; [|eauto].
        etransitivity; eauto. eapply mmap_st_follows; eauto. simpl_Forall; eauto using reuse_ident_st_follows.
  Qed.

  Corollary inlinelocal_blocks_st_nIn : forall blks Γ sub blks' locs' st st',
      Forall (NoDupLocals Γ) blks ->
      Forall (GoodLocals switch_prefs) blks ->
      st_valid st ->
      mmap2 (inlinelocal_block sub) blks st = (locs', blks', st') ->
      Forall (fun '(x, _) => ~ (st_In x st)) (concat locs').
  Proof.
    intros * ND Good V IL.
    eapply mmap2_values', Forall3_ignore13 in IL; eauto using inlinelocal_block_st_follows.
    2:{ simpl_Forall; eauto using inlinelocal_block_st_valid. }
    apply Forall_concat. simpl_Forall.
    take (inlinelocal_block _ _ _ = _) and eapply inlinelocal_block_st_nIn in it; eauto.
    simpl_Forall; eauto using st_follows_In.
  Qed.

  Corollary inlinelocal_block_nIn : forall blk sub xs locs' blks' st st',
      Forall (fun x => PS.In x (used st)) xs ->
      NoDupLocals xs blk ->
      GoodLocals switch_prefs blk ->
      st_valid st ->
      inlinelocal_block sub blk st = (locs', blks', st') ->
      Forall (fun '(x, _) => ~In x xs) locs'.
  Proof.
    intros * In ND Good Il V.
    eapply inlinelocal_block_st_nIn in Il; eauto.
    simpl_Forall. contradict Il. simpl_Forall. right; auto.
  Qed.

  Lemma mmap_inlinelocal_block_NoDupMembers : forall blks Γ sub locs' blks' st st',
      Forall
        (fun blk =>
           forall Γ sub locs' blks' st st',
             NoDupLocals Γ blk ->
             GoodLocals switch_prefs blk ->
             st_valid st ->
             inlinelocal_block sub blk st = (locs', blks', st') ->
             NoDupMembers locs') blks ->
      Forall (NoDupLocals Γ) blks ->
      Forall (GoodLocals switch_prefs) blks ->
      st_valid st ->
      mmap2 (inlinelocal_block sub) blks st = (locs', blks', st') ->
      NoDupMembers (concat locs').
  Proof.
    induction blks; intros * F ND Good V IL; inv F; inv ND; inv Good;
      repeat monadInv; simpl. constructor.
    apply NoDupMembers_app; eauto using inlinelocal_block_st_valid.
    - intros * In1 In2.
      eapply inlinelocal_blocks_st_nIn in H0; eauto using inlinelocal_block_st_valid.
      eapply inlinelocal_block_st_In in H; eauto.
      simpl_In. simpl_Forall. contradiction.
  Qed.

  Lemma reuse_idents_rename {A} sub : forall (locs : list (ident * A)) locs' st st',
      NoDupMembers locs ->
      mmap reuse_ident (map fst locs) st = (locs', st') ->
      map (rename_var (Env.union sub (Env.from_list (combine (map fst locs) locs')))) (map fst locs) = locs'.
  Proof.
    intros * ND Map. eapply Forall2_eq, Forall2_forall2.
    assert (Map':=Map). eapply mmap_values, Forall2_forall2 in Map as (Len&F2).
    rewrite map_length. split; auto.
    intros * N Nth1 Nth2; subst.
    erewrite map_nth' with (d':=xH); eauto.
    unfold rename_var. erewrite Env.union_find3'; eauto. simpl; eauto.
    apply Env.find_In_from_list. 2:now apply NoDup_NoDupMembers_combine, fst_NoDupMembers.
    erewrite <-combine_nth; eauto. eapply nth_In.
    now rewrite combine_length, <-Len, Nat.min_id.
  Qed.

  Lemma reuse_idents_NoDup {A} : forall (locs : list (ident * A)) locs' st st',
      Forall (AtomOrGensym switch_prefs) (map fst locs) ->
      st_valid st ->
      mmap reuse_ident (map fst locs) st = (locs', st') ->
      NoDup locs'.
  Proof.
    induction locs; intros * At V Reu; inv At;
      repeat monadInv; constructor; eauto using reuse_ident_st_valid.
    - intros In.
      eapply reuse_ident_st_In in H as StIn.
      eapply reuse_idents_st_nIn in H0 as StIns; eauto using reuse_ident_st_valid.
      simpl_Forall. contradiction.
  Qed.

  Lemma inlinelocal_block_NoDupMembers : forall blk Γ sub locs' blks' st st',
      NoDupLocals Γ blk ->
      GoodLocals switch_prefs blk ->
      st_valid st ->
      inlinelocal_block sub blk st = (locs', blks', st') ->
      NoDupMembers locs'.
  Proof.
    induction blk using block_ind2; intros * ND Good V IL; inv ND; inv Good;
      repeat monadInv; try constructor.
    - (* reset *)
      eapply mmap_inlinelocal_block_NoDupMembers; eauto.
    - (* local *)
      repeat inv_scope.
      apply NoDupMembers_app.
      + erewrite fst_NoDupMembers, map_map, map_ext, <-map_map, reuse_idents_rename; eauto.
        2:intros; destruct_conjs; auto.
        eapply reuse_idents_NoDup; eauto.
      + eapply mmap_inlinelocal_block_NoDupMembers in H3; eauto using reuse_idents_st_valid.
      + intros * In1 In2. erewrite fst_InMembers, map_map, map_ext, <-map_map, reuse_idents_rename in In1; eauto.
        2:intros; destruct_conjs; auto.
        eapply inlinelocal_blocks_st_nIn in H3; eauto using reuse_idents_st_valid.
        eapply reuse_idents_st_In in H0.
        simpl_In. simpl_Forall. contradiction.
  Qed.

  (** *** No local block *)

  Lemma inlinelocal_block_nolocal : forall blk sub locs' blks' st st',
      noswitch_block blk ->
      inlinelocal_block sub blk st = (locs', blks', st') ->
      Forall nolocal_block blks'.
  Proof.
    induction blk using block_ind2; intros * Hns Hdl; inv Hns; repeat monadInv.
    - (* equation *)
      repeat constructor.
    - (* reset *)
      repeat constructor.
      eapply mmap2_values, Forall3_ignore12 in H0.
      eapply Forall_concat. simpl_Forall.
      eapply H in H4; eauto. now simpl_Forall.
    - (* local *)
      eapply mmap2_values, Forall3_ignore12 in H1.
      eapply Forall_concat. simpl_Forall.
      eapply H in H6; eauto. now simpl_Forall.
  Qed.

  (** ** Transformation of node and program *)

  Program Definition inlinelocal_node (n: @node noswitch_block switch_prefs) : @node nolocal_top_block local_prefs :=
    let res := inlinelocal_block (Env.empty _)
                 (n_block n)
                 {| fresh_st := init_st; used := PSP.of_list (map fst (n_in n ++ n_out n)) |} in
    {|
      n_name := (n_name n);
      n_hasstate := (n_hasstate n);
      n_in := (n_in n);
      n_out := (n_out n);
      n_block := Blocal
                   (Scope
                      (map (fun xtc => (fst xtc, ((fst (snd xtc)), snd (snd xtc), xH, None)))
                           (fst (fst res)))
                      (snd (fst res)));
      n_ingt0 := (n_ingt0 n);
      n_outgt0 := (n_outgt0 n);
    |}.
  Next Obligation.
    pose proof (n_defd n) as (?&Hvars&Hperm).
    pose proof (n_nodup n) as (_&Hndup).
    pose proof (n_syn n) as Hns.
    repeat esplit; eauto.
    destruct (inlinelocal_block _ _) as ((?&?)&?) eqn:Hdl.
    eapply inlinelocal_block_vars_perm in Hvars as (?&?&Hperm'); eauto.
    rewrite rename_vars_empty in Hperm'.
    2:{ rewrite Hperm.
        eapply NoDupLocals_incl; [|eauto]. solve_incl_app. }
    do 2 econstructor; eauto using incl_nil'. do 2 esplit; eauto.
    erewrite map_map, map_ext; eauto.
  Qed.
  Next Obligation.
    pose proof (n_good n) as (Hgood1&Hgood2&_).
    pose proof (n_nodup n) as (Hnd1&Hnd2).
    pose proof (n_syn n) as Hsyn.
    repeat rewrite app_nil_r.
    destruct (inlinelocal_block _ _) as ((?&?)&st') eqn:Hdl. simpl.
    split; auto. do 2 constructor; eauto.
    - eapply inlinelocal_block_NoDupLocals; eauto.
    - eapply inlinelocal_block_NoDupMembers in Hdl; eauto.
      2:{ intros ? In. apply In_of_list in In. now simpl_Forall. }
      apply NoDupMembers_map; auto.
    - intros * In1 In2.
      eapply inlinelocal_block_nIn in Hdl. 3-5:eauto.
      2:{ simpl_Forall. apply In_of_list. solve_In. }
      2:{ intros ? In. apply In_of_list in In. now simpl_Forall. }
      simpl_In. simpl_Forall.
      eapply Hdl. solve_In.
  Qed.
  Next Obligation.
    pose proof (n_good n) as (Hgood1&Hgood2&Hatom).
    pose proof (n_nodup n) as (Hnd1&Hnd2).
    destruct (inlinelocal_block _ _) as ((?&?)&?) eqn:Hdl. simpl.
    pose proof (n_syn n) as Hsyn.
    repeat split; eauto using Forall_AtomOrGensym_add.
    do 2 constructor.
    - eapply inlinelocal_block_AtomOrGensym in Hdl; eauto.
      simpl_Forall; auto.
    - eapply inlinelocal_block_GoodLocals; eauto.
  Qed.
  Next Obligation.
    pose proof (n_syn n) as Hsyn.
    destruct (inlinelocal_block _ _) as ((?&?)&?) eqn:Hdl.
    constructor.
    - simpl_Forall. auto.
    - eapply inlinelocal_block_nolocal; eauto.
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

  (* Additional properties *)

  Definition senv_of_anns (locs' : list (ident * ann)) : static_env :=
    map (fun '(x, (ty, ck)) => (x, (Build_annotation ty ck xH None))) locs'.
  Global Hint Unfold senv_of_anns : list.

  Fact senv_of_anns_app : forall locs1 locs2,
      senv_of_anns (locs1 ++ locs2) = senv_of_anns locs1 ++ senv_of_anns locs2.
  Proof.
    intros. apply map_app.
  Qed.

  Fact senv_of_anns_concat_incl Γ : forall locs locs',
      In locs locs' ->
      incl (Γ ++ senv_of_anns locs) (Γ ++ senv_of_anns (concat locs')).
  Proof.
    intros * In.
    now apply incl_appr', incl_map, incl_concat.
  Qed.
  Global Hint Resolve senv_of_anns_concat_incl : senv.

  Lemma reuse_ident_gensym : forall x y st st',
      reuse_ident x st = (y, st') ->
      y = x \/ exists n hint, y = gensym local hint n.
  Proof.
    intros * Reu.
    unfold reuse_ident in *. cases_eqn EQ; inv_equalities.
    - right. eapply Fresh.Ker.fresh_ident_prefixed in EQ0; eauto.
  Qed.

  Lemma reuse_idents_gensym {A} : forall (locs : list (ident * A)) locs' st st',
      mmap reuse_ident (map fst locs) st = (locs', st') ->
      Forall (fun x => InMembers x locs \/ exists n hint, x = gensym local hint n) locs'.
  Proof.
    intros * Map.
    eapply mmap_values, Forall2_ignore1 in Map. simpl_Forall.
    eapply reuse_ident_gensym in H1 as [|]; subst; eauto.
    - left. now apply fst_InMembers.
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
