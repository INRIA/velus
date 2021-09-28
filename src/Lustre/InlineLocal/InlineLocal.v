From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Coq Require Import Recdef.

From Velus Require Import Common.
From Velus Require Import CommonTyping.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Fresh.
From Velus Require Import Lustre.LSyntax.

(** * Remove Local Blocks *)

Module Type INLINELOCAL
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Import Cks : CLOCKS Ids Op OpAux)
       (Import Syn : LSYNTAX Ids Op OpAux Cks).

  (** ** Rename some variables *)
  Section rename.
    Variable (sub : Env.t ident).

    Definition rename_in_var (x : ident) :=
      or_default x (Env.find x sub).

    Fixpoint rename_in_clock (ck : clock) :=
      match ck with
      | Cbase => Cbase
      | Con ck' x t => Con (rename_in_clock ck') (rename_in_var x) t
      end.

    Definition rename_in_nclock (nck : nclock) :=
      (rename_in_clock (fst nck), option_map rename_in_var (snd nck)).

    Definition rename_in_ann {A} (ann : (A * nclock)) :=
      (fst ann, rename_in_nclock (snd ann)).

    Fixpoint rename_in_exp (e : exp) :=
      match e with
      | Econst _ | Eenum _ _ => e
      | Evar x ann => Evar (rename_in_var x) (rename_in_ann ann)
      | Eunop op e1 ann => Eunop op (rename_in_exp e1) (rename_in_ann ann)
      | Ebinop op e1 e2 ann => Ebinop op (rename_in_exp e1) (rename_in_exp e2) (rename_in_ann ann)
      | Efby e0s e1s anns => Efby (map rename_in_exp e0s) (map rename_in_exp e1s) (map rename_in_ann anns)
      | Earrow e0s e1s anns => Earrow (map rename_in_exp e0s) (map rename_in_exp e1s) (map rename_in_ann anns)
      | Ewhen es x t ann => Ewhen (map rename_in_exp es) (rename_in_var x) t (rename_in_ann ann)
      | Emerge (x, ty) es ann => Emerge (rename_in_var x, ty) (map (fun '(i, es) => (i, map rename_in_exp es)) es) (rename_in_ann ann)
      | Ecase e es d ann =>
        Ecase (rename_in_exp e) (map (fun '(i, es) => (i, map rename_in_exp es)) es) (option_map (map rename_in_exp) d) (rename_in_ann ann)
      | Eapp f es er ann => Eapp f (map rename_in_exp es) (map rename_in_exp er) (map rename_in_ann ann)
      end.

    Definition rename_in_reset :=
      map (fun '(xr, ckr) => (rename_in_var xr, rename_in_clock ckr)).

    Definition rename_in_equation '(xs, es) : equation :=
      (map rename_in_var xs, map rename_in_exp es).

    (** *** Properties *)

    Lemma rename_in_ann_clock {A} : forall (ann : (A * nclock)),
        clock_of_nclock (rename_in_ann ann) = rename_in_clock (clock_of_nclock ann).
    Proof. reflexivity. Qed.

    Corollary map_rename_in_ann_clock {A} : forall (anns : list (A * nclock)),
        map clock_of_nclock (map rename_in_ann anns) = map rename_in_clock (map clock_of_nclock anns).
    Proof.
      induction anns; simpl; auto.
      f_equal; auto.
    Qed.

    Lemma rename_in_ann_anon_streams : forall anns,
        anon_streams (map rename_in_ann anns) =
        map (fun '(x, (ty, ck)) => (rename_in_var x, (ty, rename_in_clock ck))) (anon_streams anns).
    Proof.
      induction anns as [|(?&?&[|])]; simpl; f_equal; auto.
    Qed.

    Lemma rename_in_exp_fresh_in : forall e,
        fresh_in (rename_in_exp e) =
        map (fun '(x, (ty, ck)) => (rename_in_var x, (ty, rename_in_clock ck))) (fresh_in e).
    Proof.
      induction e using exp_ind2; simpl; auto. 5:destruct x; simpl.
      1-7:repeat rewrite map_app; try f_equal; auto.
      1-9:repeat rewrite flat_map_concat_map; repeat rewrite concat_map; repeat f_equal; auto using rename_in_ann_anon_streams.
      1-10:repeat rewrite map_map; try (eapply map_ext_in; intros * Hin; try rewrite Forall_forall in *; eauto).
      - (* merge *)
        specialize (H _ Hin). rewrite Forall_forall in *. destruct a0; simpl.
        rewrite 2 flat_map_concat_map, concat_map, 2 map_map.
        f_equal. eapply map_ext_in; intros; auto.
      - (* case *)
        specialize (H _ Hin). rewrite Forall_forall in *. destruct a0; simpl.
        rewrite 2 flat_map_concat_map, concat_map, 2 map_map.
        f_equal. eapply map_ext_in; intros; auto.
      - (* case (default) *)
        destruct d; simpl in *; auto.
        rewrite 2 flat_map_concat_map, concat_map, 2 map_map.
        f_equal. eapply map_ext_in; intros; auto.
        eapply Forall_forall in H0; eauto.
    Qed.

    Corollary rename_in_exp_fresh_ins : forall es,
        fresh_ins (map rename_in_exp es) =
        map (fun '(x, (ty, ck)) => (rename_in_var x, (ty, rename_in_clock ck))) (fresh_ins es).
    Proof.
      intros. unfold fresh_ins.
      rewrite 2 flat_map_concat_map, concat_map, 2 map_map.
      f_equal. eapply map_ext; intros.
      eapply rename_in_exp_fresh_in.
    Qed.

    Lemma rename_in_exp_anon_in : forall e,
        anon_in (rename_in_exp e) =
        map (fun '(x, (ty, ck)) => (rename_in_var x, (ty, rename_in_clock ck))) (anon_in e).
    Proof.
      intros []; try destruct p; try eapply rename_in_exp_fresh_in.
      simpl.
      rewrite map_app. f_equal; apply rename_in_exp_fresh_ins.
    Qed.

    Lemma rename_in_equation_anon_in : forall eq,
        anon_in_eq (rename_in_equation eq) =
        map (fun '(x, (ty, ck)) => (rename_in_var x, (ty, rename_in_clock ck))) (anon_in_eq eq).
    Proof.
      unfold anon_in_eq, anon_ins.
      intros (?&?); simpl.
      rewrite 2 flat_map_concat_map, concat_map, 2 map_map.
      f_equal. eapply map_ext; intros.
      eapply rename_in_exp_anon_in.
    Qed.

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

  Corollary not_in_union_map_rename1 : forall xs sub sub',
      Forall (fun x => ~Env.In x sub) xs ->
      map (rename_in_var (Env.union sub sub')) xs = map (rename_in_var sub') xs.
  Proof.
    induction xs; intros * Hf; inv Hf; simpl; f_equal; auto using not_in_union_rename1.
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

  Corollary not_in_union_map_rename2 : forall xs sub sub',
      Forall (fun x => ~Env.In x sub') xs ->
      map (rename_in_var (Env.union sub sub')) xs = map (rename_in_var sub) xs.
  Proof.
    induction xs; intros * Hf; inv Hf; simpl; f_equal; auto using not_in_union_rename2.
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

  Corollary disjoint_union_rename_in_clock : forall (sub1 sub2: Env.t ident) ck,
      (forall x, Env.In x sub1 -> ~Env.In x sub2) ->
      (forall x y, Env.MapsTo x y sub1 -> ~Env.In y sub2) ->
      rename_in_clock sub2 (rename_in_clock sub1 ck) = rename_in_clock (Env.union sub1 sub2) ck.
  Proof.
    intros * Hsub1 Hsub2.
    induction ck; simpl; auto.
    f_equal; auto using disjoint_union_rename_in_var.
  Qed.

  (** ** Inlining of local blocks *)

  Module Fresh := Fresh.Fresh(Ids).
  Import Fresh Notations Facts Tactics.
  Local Open Scope fresh_monad_scope.

  Definition FreshAnn A := Fresh A (type * clock).

  Fixpoint inlinelocal_block sub (blk : block) : FreshAnn (list block) :=
    match blk with
    | Beq eq => ret [Beq (rename_in_equation sub eq)]
    | Breset blks er =>
      do blks' <- mmap (inlinelocal_block sub) blks;
      ret [Breset (concat blks') (rename_in_exp sub er)]
    | Blocal locs blks =>
      let locs' := map (fun '(x, (ty, ck)) => (x, (ty, (rename_in_clock sub ck)))) (idty locs) in
      do (_, sub1) <- fresh_idents_rename local locs' (fun sub '(ty, ck) => (ty, rename_in_clock sub ck));
      let sub' := Env.union sub sub1 in
      do blks' <- mmap (inlinelocal_block sub') blks;
      ret (concat blks')
    end.

  Definition inlinelocal_topblock (blk : block) : FreshAnn (list block * list (ident * (type * clock * ident))) :=
    match blk with
    | Blocal locs blks =>
      do blks' <- mmap (inlinelocal_block (@Env.empty _)) blks;
      ret (concat blks', locs)
    | _ =>
      do blks' <- inlinelocal_block (@Env.empty _) blk;
      ret (blks', [])
    end.

  (** ** State properties *)

  Definition st_valid_after {B} st aft := @st_valid_after B st local aft.

  Lemma inlinelocal_block_st_valid_after : forall blk sub blks' st st' aft,
      inlinelocal_block sub blk st = (blks', st') ->
      st_valid_after st aft ->
      st_valid_after st' aft.
  Proof.
    induction blk using block_ind2; intros * Hdl Hvalid; repeat inv_bind; auto.
    - (* reset *)
      eapply mmap_st_valid; eauto.
      eapply Forall_impl; [|eauto]; intros ? Hdl ?????.
      eapply Hdl; eauto.
    - (* local *)
      eapply fresh_idents_rename_st_valid in H0; eauto.
      eapply mmap_st_valid in H1; eauto.
      eapply Forall_impl; [|eauto]; intros ? Hdl ?????.
      eapply Hdl; eauto.
  Qed.

  Lemma inlinelocal_topblock_st_valid_after : forall blk res st st' aft,
      inlinelocal_topblock blk st = (res, st') ->
      st_valid_after st aft ->
      st_valid_after st' aft.
  Proof.
    Opaque inlinelocal_block.
    destruct blk; intros * Hdl Hvalid; repeat inv_bind; auto.
    1,2:eapply inlinelocal_block_st_valid_after; eauto.
    eapply mmap_st_valid in H; eauto.
    eapply Forall_forall; intros.
    eapply inlinelocal_block_st_valid_after; eauto.
    Transparent inlinelocal_block.
  Qed.

  Lemma inlinelocal_block_st_follows : forall blk sub blks' st st',
      inlinelocal_block sub blk st = (blks', st') ->
      st_follows st st'.
  Proof.
    induction blk using block_ind2; intros * Hdl; repeat inv_bind.
    - (* equation *) reflexivity.
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
    destruct blk; intros * Hil; repeat inv_bind.
    1,2:eapply inlinelocal_block_st_follows; eauto.
    eapply mmap_st_follows; eauto.
    eapply Forall_forall; intros; eauto using inlinelocal_block_st_follows.
    Transparent inlinelocal_block.
  Qed.

  Hint Resolve inlinelocal_block_st_follows.

  (** *** anon stay the same *)

  Lemma not_in_sub_same {B} : forall sub (xs : list (ident * (B * clock))),
      (forall x, InMembers x xs -> ~ Env.In x sub) ->
      map fst (map (fun '(x, (ty, ck)) => (rename_in_var sub x, (ty, rename_in_clock sub ck))) xs) =
      map fst xs.
  Proof.
    induction xs as [|(?&?&?)]; intros * Hsub; simpl; auto.
    f_equal; auto.
    - unfold rename_in_var.
      eapply Env.Props.P.F.not_find_in_iff in Hsub; [|left; eauto].
      rewrite Hsub; auto.
    - eapply IHxs; intros.
      eapply Hsub. right; auto.
  Qed.

  Fact mmap_inlinelocal_block_anon' : forall blks sub blks' st st',
      Forall
        (fun blk => forall sub blks' st st',
         (forall x : ident, InMembers x (anon_in_block blk) -> ~ Env.In x sub) ->
         NoDupLocals (map fst (anon_in_block blk)) blk ->
         inlinelocal_block sub blk st = (blks', st') ->
         map fst (flat_map anon_in_block blks') = map fst (anon_in_block blk)) blks ->
      (forall x, InMembers x (flat_map anon_in_block blks) -> ~ Env.In x sub) ->
      Forall (NoDupLocals (map fst (flat_map anon_in_block blks))) blks ->
      mmap (inlinelocal_block sub) blks st = (blks', st') ->
      map fst (flat_map anon_in_block (concat blks')) = map fst (flat_map anon_in_block blks).
  Proof.
    induction blks; intros * Hf Hsub Hnd Hmap;
      inv Hf; inv Hnd; repeat inv_bind; auto; simpl.
    rewrite <-flat_map_app, 2 map_app.
    f_equal.
    - eapply H1; eauto.
      intros ? Hinm. eapply Hsub, InMembers_incl; eauto.
      2:eapply NoDupLocals_incl; [|eauto].
      1,2:solve_incl_app.
    - eapply IHblks; eauto.
      intros ? Hinm. eapply Hsub, InMembers_incl; eauto.
      2:eapply Forall_impl; [|eauto]; intros; eapply NoDupLocals_incl; [|eauto].
      1,2:solve_incl_app.
  Qed.

  Lemma inlinelocal_block_anon : forall blk sub blks' st st',
      (forall x, InMembers x (anon_in_block blk) -> ~Env.In x sub) ->
      NoDupLocals (map fst (anon_in_block blk)) blk ->
      inlinelocal_block sub blk st = (blks', st') ->
      map fst (flat_map anon_in_block blks') = map fst (anon_in_block blk).
  Proof.
    induction blk using block_ind2;
      intros * Hsub Hnl Hdl; inv Hnl; repeat inv_bind.
    - (* equation *)
      simpl. rewrite app_nil_r, rename_in_equation_anon_in.
      rewrite not_in_sub_same; auto.
    - (* reset *)
      simpl. rewrite app_nil_r, 2 map_app. f_equal.
      + eapply mmap_inlinelocal_block_anon'; eauto.
        intros ? Hinm. eapply Hsub, InMembers_incl; eauto.
        2:eapply Forall_impl; [|eauto]; intros; eapply NoDupLocals_incl; [|eauto].
        1,2:solve_incl_app.
      + rewrite rename_in_exp_fresh_in.
        rewrite not_in_sub_same; auto.
        intros ? Hinm. eapply Hsub. rewrite InMembers_app; auto.
    - (* local *)
      eapply mmap_inlinelocal_block_anon' in H1; eauto.
      2:eapply Forall_impl; [|eauto]; intros; eapply NoDupLocals_incl; [|eauto]; solve_incl_app.
      intros ? Hinm.
      rewrite Env.union_In, not_or'; split; eauto.
      intro contra.
      eapply fresh_idents_rename_sub1 in contra; eauto.
      erewrite fst_InMembers, map_map, map_ext, map_fst_idty in contra.
      2:intros (?&?&?); auto.
      eapply H5; eauto. 1,2:try rewrite fst_InMembers; eauto; try rewrite <-fst_InMembers; eauto.
  Qed.

  Corollary mmap_inlinelocal_block_anon : forall blks sub blks' st st',
      (forall x, InMembers x (flat_map anon_in_block blks) -> ~ Env.In x sub) ->
      Forall (NoDupLocals (map fst (flat_map anon_in_block blks))) blks ->
      mmap (inlinelocal_block sub) blks st = (blks', st') ->
      map fst (flat_map anon_in_block (concat blks')) = map fst (flat_map anon_in_block blks).
  Proof.
    intros. eapply mmap_inlinelocal_block_anon'; eauto.
    eapply Forall_forall; intros.
    eapply inlinelocal_block_anon; eauto.
  Qed.

  Lemma inlinelocal_topblock_anon : forall blk blks' vars st st',
      NoDupLocals (map fst (anon_in_block blk)) blk ->
      inlinelocal_topblock blk st = (blks', vars, st') ->
      map fst (flat_map anon_in_block blks') = map fst (anon_in_block blk).
  Proof.
    Opaque inlinelocal_block.
    destruct blk; intros * Hnd Hil; repeat inv_bind.
    1,2:eapply inlinelocal_block_anon in H; eauto.
    3:inv Hnd; eapply mmap_inlinelocal_block_anon; eauto.
    1-3:intros; rewrite Env.Props.P.F.empty_in_iff; eauto.
    eapply Forall_impl; [|eauto]; intros.
    eapply NoDupLocals_incl; [|eauto]; solve_incl_app.
    Transparent inlinelocal_block.
  Qed.

  (** ** Wellformedness properties *)

  (** *** VarsDefined *)

  Import Permutation.

  Hint Constructors VarsDefined.

  Fact mmap_vars_perm : forall (f : _ -> block -> FreshAnn (list block)) blks sub blks' xs st st',
      Forall
        (fun blk => forall sub blks' xs st st',
             VarsDefined blk xs ->
             NoDupLocals (map fst (Env.elements sub) ++ xs) blk ->
             f sub blk st = (blks', st') ->
             exists ys, Forall2 VarsDefined blks' ys /\ Permutation (concat ys ++ st_ids st) (map (rename_in_var sub) xs ++ st_ids st')) blks ->
      Forall2 VarsDefined blks xs ->
      Forall (NoDupLocals (map fst (Env.elements sub) ++ concat xs)) blks ->
      mmap (f sub) blks st = (blks', st') ->
      exists ys, Forall2 VarsDefined (concat blks') ys /\ Permutation (concat ys ++ st_ids st) (map (rename_in_var sub) (concat xs) ++ st_ids st').
  Proof.
    induction blks; intros * Hf Hvars Hnd Hnorm; inv Hf; inv Hvars; inv Hnd; repeat inv_bind; simpl.
    - exists []. split; auto.
    - eapply H1 in H as (ys1&Hvars1&Hperm1); eauto.
      2:eapply NoDupLocals_incl; [|eauto]; solve_incl_app.
      eapply IHblks in H2 as (ys2&Hvars2&Hperm2); eauto. clear IHblks.
      2:eapply Forall_impl; [|eapply H6]; intros; eapply NoDupLocals_incl; [|eauto]; solve_incl_app.
      exists (ys1 ++ ys2). split.
      + apply Forall2_app; auto.
      + rewrite map_app, <-app_assoc, <-Hperm2, Permutation_swap, <-Hperm1, Permutation_swap.
        now rewrite concat_app, <-app_assoc.
  Qed.

  Lemma inlinelocal_block_vars_perm : forall blk sub blks' xs st st',
      VarsDefined blk xs ->
      NoDupLocals (map fst (Env.elements sub) ++ xs) blk ->
      inlinelocal_block sub blk st = (blks', st') ->
      exists ys, Forall2 VarsDefined blks' ys /\ Permutation (concat ys ++ st_ids st) (map (rename_in_var sub) xs ++ st_ids st').
  Proof.
    induction blk using block_ind2; intros * Hvars Hnd Hdl; inv Hvars; inv Hnd; repeat inv_bind.
    - (* equation *)
      destruct eq.
      repeat esplit; simpl; auto.
      simpl. now rewrite <-app_assoc.
    - (* reset *)
      eapply mmap_vars_perm in H0 as (ys1&Hvars1&Hperm1); eauto.
      do 2 esplit; eauto.
      simpl. now rewrite <-app_assoc.
    - (* local *)
      eapply mmap_vars_perm in H1 as (ys1&Hvars1&Hperm1); eauto.
      2:{ eapply Forall_impl; [|eapply H3]; intros.
          eapply NoDupLocals_incl; [|eauto].
          rewrite <-H4, (Permutation_app_comm _ xs). repeat rewrite app_assoc.
          apply incl_app; try solve [solve_incl_app].
          apply incl_app; try solve [solve_incl_app].
          rewrite (Permutation_app_comm _ xs), <-app_assoc. apply incl_appr.
          intros ? Hin. eapply in_map_iff in Hin as ((?&?)&?&Hin); subst.
          eapply Env.elements_complete, Env.union_find4 in Hin as [Hfind|Hfind].
          - eapply Env.elements_correct in Hfind.
            apply in_or_app, or_introl, in_map_iff; eauto.
          - eapply fresh_idents_rename_sub1 in H0; eauto. 2:econstructor; eauto.
            unfold idty in H0. rewrite fst_InMembers, 2 map_map in H0.
            erewrite map_ext in H0; eauto using in_or_app. intros (?&(?&?)&?); eauto.
      }
      rewrite <-H4, map_app in Hperm1.
      unfold st_ids in Hperm1. do 1 (erewrite fresh_idents_rename_anns in Hperm1; eauto); simpl in *.
      rewrite map_app, not_in_union_map_rename1, not_in_union_map_rename2,
              (Permutation_swap (concat ys1)), <-app_assoc in Hperm1.
      2:{ eapply Forall_forall; intros * Hin contra.
          eapply fresh_idents_rename_sub1 in contra; eauto.
          unfold idty in contra. rewrite fst_InMembers, 2 map_map in contra.
          erewrite map_ext, <-fst_InMembers in contra.
          eapply H7; eauto using in_or_app. intros (?&(?&?)&?); auto. }
      2:{ eapply Forall_forall; intros * Hin (?&contra). apply fst_InMembers in Hin.
          eapply H7; eauto. apply in_or_app; left.
          eapply in_map_iff. do 2 esplit.
          2:eapply Env.elements_correct; eauto. reflexivity. }
      eapply Ker.fresh_idents_rename_ids in H0.
      2:{ rewrite fst_NoDupMembers in H6.
          unfold idty. rewrite fst_NoDupMembers, 2 map_map; simpl.
          erewrite map_ext; eauto. intros (?&(?&?)&?); auto. }
      rewrite H0 in Hperm1. unfold idty in Hperm1. repeat rewrite map_map in Hperm1; simpl in Hperm1.
      erewrite map_ext in Hperm1. eapply Permutation_app_inv_l in Hperm1.
      2:(intros (?&(?&?)&?); simpl; auto).
      repeat esplit; eauto.
  Qed.

  Lemma inlinelocal_topblock_vars_perm : forall blk blks' vars xs st st',
      VarsDefined blk xs ->
      NoDupLocals xs blk ->
      inlinelocal_topblock blk st = (blks', vars, st') ->
      exists ys, Forall2 VarsDefined blks' ys /\ Permutation (concat ys ++ st_ids st) (xs ++ map fst vars ++ st_ids st').
  Proof.
    Opaque inlinelocal_block.
    destruct blk; intros * Hvars Hnd Hil; repeat inv_bind; simpl.
    1,2:eapply inlinelocal_block_vars_perm in H as (?&?&Hperm); eauto.
    3:inv Hvars; inv Hnd; eapply mmap_vars_perm in H as (?&?&Hperm); eauto.
    1-3:rewrite rename_in_vars_empty in Hperm; eauto.
    - do 2 esplit; eauto. rewrite Hperm, <-H4, (Permutation_app_comm _ xs), <-app_assoc; auto.
    - eapply Forall_forall; intros; eauto using inlinelocal_block_vars_perm.
    - rewrite Env.Props.P.elements_empty; simpl.
      eapply Forall_impl; [|eauto]; intros.
      now rewrite <-H4, Permutation_app_comm.
    Transparent inlinelocal_block.
  Qed.

  (** *** GoodLocals *)

  Lemma inlinelocal_block_GoodLocals : forall blk sub blks' st st',
      inlinelocal_block sub blk st = (blks', st') ->
      Forall (GoodLocals local_prefs) blks'.
  Proof.
    induction blk using block_ind2; intros * Hdl; repeat inv_bind.
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
      inlinelocal_topblock blk st = (blks', vars, st') ->
      Forall (GoodLocals local_prefs) blks'.
  Proof.
    Opaque inlinelocal_block.
    destruct blk; intros * Hil; repeat inv_bind.
    1,2:eapply inlinelocal_block_GoodLocals; eauto.
    apply Forall_concat.
    eapply mmap_values, Forall2_ignore1 in H.
    rewrite Forall_forall in *; intros * Hin.
    edestruct H as (?&Hin'&?&?&Hdl); eauto using inlinelocal_block_GoodLocals.
    Transparent inlinelocal_block.
  Qed.

  (** *** NoDupLocals *)

  Lemma rename_in_var_injective : forall sub x y,
      Env.In x sub ->
      Env.In y sub ->
      NoDup (map snd (Env.elements sub)) ->
      rename_in_var sub x = rename_in_var sub y ->
      x = y.
  Proof.
    unfold rename_in_var.
    intros * (?&Hfind1) (?&Hfind2) Hndsub Hren.
    rewrite Hfind1, Hfind2 in Hren; simpl in Hren; inv Hren.
    eapply NoDup_snd_det; eauto using Env.elements_correct.
  Qed.

  Lemma inlinelocal_block_NoDupLocals xs : forall blk sub blks' st st',
      inlinelocal_block sub blk st = (blks', st') ->
      Forall (NoDupLocals xs) blks'.
  Proof.
    induction blk using block_ind2; intros * Hdl; repeat inv_bind.
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
      inlinelocal_topblock blk st = (blks', vars, st') ->
      Forall (NoDupLocals xs) blks'.
  Proof.
    Opaque inlinelocal_block.
    destruct blk; intros * Hil; repeat inv_bind.
    1,2:eapply inlinelocal_block_NoDupLocals; eauto.
    eapply mmap_values, Forall2_ignore1 in H.
    eapply Forall_concat. rewrite Forall_forall in *; intros.
    edestruct H as (?&?&?&?&?); eauto using inlinelocal_block_NoDupLocals.
    Transparent inlinelocal_block.
  Qed.

  Lemma inlinelocal_topblock_incl : forall blk blks' vars st st',
      inlinelocal_topblock blk st = (blks', vars, st') ->
      incl vars (locals blk).
  Proof.
    Opaque inlinelocal_block.
    destruct blk; intros * Hil; repeat inv_bind.
    1,2:apply incl_nil'.
    apply incl_appl, incl_refl.
    Transparent inlinelocal_block.
  Qed.

  Lemma inlinelocal_topblock_NoDupMembers xs : forall blk blks' vars st st',
      NoDupLocals xs blk ->
      inlinelocal_topblock blk st = (blks', vars, st') ->
      NoDupMembers vars.
  Proof.
    Opaque inlinelocal_block.
    destruct blk; intros * Hnd Hil; inv Hnd; repeat inv_bind; auto.
    1-2:constructor.
    Transparent inlinelocal_block.
  Qed.

  Lemma inlinelocal_topblock_nIn xs : forall blk blks' vars st st',
      NoDupLocals xs blk ->
      inlinelocal_topblock blk st = (blks', vars, st') ->
      forall x, InMembers x vars -> ~In x xs.
  Proof.
    Opaque inlinelocal_block.
    destruct blk; intros * Hnd Hil; inv Hnd; repeat inv_bind; auto.
    Transparent inlinelocal_block.
  Qed.

  (** *** No local block *)

  Lemma inlinelocal_block_nolocal : forall blk sub blks' st st',
      inlinelocal_block sub blk st = (blks', st') ->
      Forall nolocal_block blks'.
  Proof.
    induction blk using block_ind2; intros * Hdl; repeat inv_bind.
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
      inlinelocal_topblock blk st = (blks', vars, st') ->
      Forall nolocal_block blks'.
  Proof.
    Opaque inlinelocal_block.
    destruct blk; intros * Hil; repeat inv_bind.
    1,2:eapply inlinelocal_block_nolocal; eauto.
    eapply mmap_values, Forall2_ignore1 in H.
    eapply Forall_concat.
    rewrite Forall_forall in *; intros.
    edestruct H as (?&?&?&?&Hdl); eauto using inlinelocal_block_nolocal.
    Transparent inlinelocal_block.
  Qed.

  (** ** Transformation of node and program *)

  Lemma local_not_in_elab_prefs :
    ~PS.In local elab_prefs.
  Proof.
    unfold elab_prefs.
    rewrite PSF.singleton_iff.
    pose proof gensym_prefs_NoDup as Hnd. unfold gensym_prefs in Hnd.
    repeat rewrite NoDup_cons_iff in Hnd.
    intros contra; subst; rewrite contra in Hnd.
    destruct Hnd as (Hnin&_). apply Hnin. left; auto.
  Qed.

  Program Definition inlinelocal_node {PSyn} (n: @node PSyn elab_prefs) : @node nolocal_top_block local_prefs :=
    let res := inlinelocal_topblock (n_block n) init_st in
    {| n_name := (n_name n);
       n_hasstate := (n_hasstate n);
       n_in := (n_in n);
       n_out := (n_out n);
       n_block := Blocal (snd (fst res)++map (fun xtc => (fst xtc, ((fst (snd xtc)), snd (snd xtc), xH))) (st_anns (snd res)))
                         (fst (fst res));
       n_ingt0 := (n_ingt0 n);
       n_outgt0 := (n_outgt0 n);
    |}.
  Next Obligation.
    pose proof (n_defd n) as (?&Hvars&Hperm).
    pose proof (n_nodup n) as (_&Hndup).
    repeat esplit; eauto.
    destruct (inlinelocal_topblock _ _) as ((?&?)&?) eqn:Hdl.
    eapply inlinelocal_topblock_vars_perm in Hvars as (?&?&Hperm'); eauto.
    2:{ rewrite Hperm.
        eapply NoDupLocals_incl; [|eauto]. solve_incl_app. }
    econstructor; eauto.
    unfold st_ids in *. rewrite init_st_anns, app_nil_r in Hperm'.
    erewrite map_app, map_map, Hperm', <-app_assoc; simpl.
    rewrite (app_assoc x), (Permutation_app_comm x), <-app_assoc. apply Permutation_app_head.
    now rewrite Permutation_app_comm.
  Qed.
  Next Obligation.
    pose proof (n_good n) as (Hgood1&Hgood2&_).
    pose proof (n_nodup n) as (Hnd1&Hnd2).
    repeat rewrite app_nil_r.
    destruct (inlinelocal_topblock _ _) as ((?&?)&st') eqn:Hdl. simpl.
    assert (map fst (flat_map anon_in_block l) = map fst (anon_in_block (n_block n))) as Hanon.
    { eapply inlinelocal_topblock_anon; eauto.
      eapply NoDupLocals_incl; [|eauto]. solve_incl_app. }
    assert (st_valid_after st' (PSP.of_list (map fst (idty (n_in n ++ n_out n) ++ anon_in_block (n_block n))))).
    { eapply inlinelocal_topblock_st_valid_after, init_st_valid; eauto using local_not_in_elab_prefs.
      rewrite <-ps_from_list_ps_of_list.
      apply PS_For_all_Forall'.
      now rewrite map_app, map_fst_idty.
    }
    split; eauto. 2:econstructor; eauto.
    - rewrite fst_NoDupMembers, map_app in *.
      rewrite Hanon; auto.
    - rewrite Hanon.
      eapply inlinelocal_topblock_NoDupLocals; eauto.
    - assert (Hvalid:=H). eapply st_valid_NoDup, NoDup_app_l in H.
      apply NoDupMembers_app.
      + eapply inlinelocal_topblock_NoDupMembers; eauto.
      + rewrite fst_NoDupMembers, map_map; eauto.
      + intros * Hinm1 Hinm2.
        rewrite fst_InMembers in Hinm1, Hinm2. rewrite map_map in Hinm2.
        eapply st_valid_after_AtomOrGensym_nIn in Hinm2; eauto using local_not_in_elab_prefs.
        eapply Forall_forall; [|eapply Hinm1]. eapply Forall_incl, incl_map, inlinelocal_topblock_incl; eauto.
        eapply GoodLocals_locals; eauto.
    - setoid_rewrite Hanon.
      intros ? Hinm contra.
      eapply st_valid_after_NoDupMembers in H; eauto.
      rewrite map_app, map_fst_idty in H.
      eapply NoDup_app_In in H; eauto using in_or_app.
      erewrite InMembers_app, 2 fst_InMembers, map_map, map_ext in Hinm; destruct Hinm as [Hinm|]; eauto.
      eapply inlinelocal_topblock_nIn; eauto. eapply fst_InMembers; eauto.
  Qed.
  Next Obligation.
    pose proof (n_good n) as (Hgood1&Hgood2&Hatom).
    pose proof (n_nodup n) as (Hnd1&Hnd2).
    destruct (inlinelocal_topblock _ _) as ((?&?)&?) eqn:Hdl.
    assert (map fst (flat_map anon_in_block l) = map fst (anon_in_block (n_block n))) as Hanon.
    { eapply inlinelocal_topblock_anon; eauto.
      eapply NoDupLocals_incl; [|eauto]. solve_incl_app. }
    simpl. rewrite Hanon.
    repeat split; eauto using AtomOrGensym_add.
    constructor.
    - assert (Hil:=Hdl). eapply inlinelocal_topblock_st_valid_after, st_valid_prefixed in Hdl.
      2:{ eapply init_st_valid. eapply local_not_in_elab_prefs. eapply PS_For_all_empty. }
      rewrite map_app, map_map, Forall_app; split; simpl.
      + eapply AtomOrGensym_add, Forall_incl, incl_map, inlinelocal_topblock_incl; eauto.
        eapply GoodLocals_locals; eauto.
      + eapply Forall_impl; [|eauto]; intros; simpl in *.
        right. do 2 eexists; eauto using PSF.add_1.
    - eapply inlinelocal_topblock_GoodLocals; eauto.
  Qed.
  Next Obligation.
    constructor.
    destruct (inlinelocal_topblock _ _) as ((?&?)&?) eqn:Hdl.
    eapply inlinelocal_topblock_nolocal; eauto.
  Qed.

  Program Instance inlinelocal_node_transform_unit: TransformUnit (@node (fun _ => True) elab_prefs) node :=
    { transform_unit := inlinelocal_node }.

  Program Instance inlinelocal_global_without_units : TransformProgramWithoutUnits (@global (fun _ => True) elab_prefs) (@global nolocal_top_block local_prefs) :=
    { transform_program_without_units := fun g => Global g.(enums) [] }.

  Definition inlinelocal_global : @global (fun _ => True) elab_prefs -> @global nolocal_top_block local_prefs :=
    transform_units.

  (** *** Equality of interfaces *)

  Lemma inlinelocal_global_iface_eq : forall G,
      global_iface_eq G (inlinelocal_global G).
  Proof.
    split; auto.
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
       (Syn : LSYNTAX Ids Op OpAux Cks)
       <: INLINELOCAL Ids Op OpAux Cks Syn.
  Include INLINELOCAL Ids Op OpAux Cks Syn.
End InlineLocalFun.
