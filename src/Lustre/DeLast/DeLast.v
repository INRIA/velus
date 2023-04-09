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

  Fact not_in_union_rename1 : forall x y sub xs,
      NoDupMembers xs ->
      In (x, y) xs ->
      rename_in_var (Env.adds' xs sub) x = y.
  Proof.
    unfold rename_in_var.
    intros * ND In.
    erewrite Env.In_find_adds'; simpl; eauto.
  Qed.

  Fact not_in_union_rename2 : forall x sub xs,
      ~InMembers x xs ->
      rename_in_var (Env.adds' xs sub) x = rename_in_var sub x.
  Proof.
    unfold rename_in_var.
    intros * Hnin.
    destruct (Env.find x _) eqn:Hfind.
    - eapply Env.find_adds'_In in Hfind as [Hfind|Hfind].
      + exfalso. eapply Hnin; eauto using In_InMembers.
      + now rewrite Hfind.
    - apply Env.find_adds'_nIn in Hfind as (Hfind1&Hfind2).
      simpl. destruct (Env.find x sub); simpl in *; auto. congruence.
  Qed.

  (** ** Inlining of local blocks *)

  Module Fresh := Fresh.Fresh(Ids).
  Import Fresh Notations Facts Tactics.
  Local Open Scope fresh_monad_scope.

  Definition FreshAnn A := Fresh last A (type * clock).

  Definition fresh_idents (lasts : list (ident * (type * clock))) : FreshAnn _ :=
    mmap (fun '(x, (ty, ck)) => do lx <- fresh_ident (Some x) (ty, ck);
                             ret (x, lx, (ty, ck))) lasts.

  Section delast_scope.
    Context {A : Type}.
    Variable f_delast : Env.t ident -> A -> FreshAnn A.

    Definition delast_scope sub (s : scope A) : FreshAnn (scope A) :=
      let 'Scope locs blks := s in
      let lasts := map_filter (fun '(x, (ty, ck, _, o)) => option_map (fun _ => (x, (ty, ck))) o) locs in
      do lasts' <- fresh_idents lasts;
      let sub' := Env.adds' (map fst lasts') sub in
      do blks' <- f_delast sub' blks;
      ret (Scope (map (fun '(x, (ty, ck, cx, _)) => (x, (ty, ck, cx, None))) locs
                      ++ map (fun '(_, lx, (ty, ck)) => (lx, (ty, ck, xH, None))) lasts')
                 blks').
  End delast_scope.

  Fixpoint delast_block sub (blk : block) : FreshAnn block :=
    match blk with
    | Beq eq => ret (Beq (rename_in_equation sub eq))
    | Blast x e =>
        let '(ty, ck) := List.hd (OpAux.bool_velus_type, Cbase) (annot e) in
        ret (Beq ([rename_in_var sub x], [Efby [rename_in_exp sub e] [Evar x (ty, ck)] [(ty, ck)]]))
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
                                                     sub scope;
                             ret (k, Branch [] (unl', scope'))) states;
        ret (Bauto type ck (map (fun '(e, k) => (rename_in_exp sub e, k)) ini, oth) states')
    | Blocal scope =>
        do scope' <- delast_scope (fun sub => mmap (delast_block sub)) sub scope;
        ret (Blocal scope')
    end.

  Definition delast_outs_and_block (outs : list decl) blk : FreshAnn block :=
    let lasts := map_filter (fun '(x, (ty, ck, _, o)) => option_map (fun _ => (x, (ty, ck))) o) outs in
    do lasts' <- fresh_idents lasts;
    let sub := Env.from_list (map fst lasts') in
    do blk' <- delast_block sub blk;
    if is_nil lasts' then
      ret blk'
    else
      ret (Blocal (Scope (map (fun '(_, lx, (ty, ck)) => (lx, (ty, ck, xH, None))) lasts') [blk'])).

  (** ** Some properties *)

  Lemma fresh_idents_In : forall lasts lasts' st st',
      fresh_idents lasts st = (lasts', st') ->
      forall x ty ck, In (x, (ty, ck)) lasts ->
                 exists lx, In (x, lx, (ty, ck)) lasts'.
  Proof.
    intros * Hfresh * Hin.
    apply mmap_values, Forall2_ignore2 in Hfresh. simpl_Forall.
    repeat inv_bind. eauto.
  Qed.

  Lemma fresh_idents_In' : forall lasts lasts' st st',
      fresh_idents lasts st = (lasts', st') ->
      forall x lx ty ck, In (x, lx, (ty, ck)) lasts' ->
                    In (x, (ty, ck)) lasts.
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

  Lemma fresh_idents_In_rename sub : forall lasts lasts' st st',
      NoDupMembers lasts ->
      fresh_idents lasts st = (lasts', st') ->
      forall x ty ck, In (x, (ty, ck)) lasts ->
                 In (x, (rename_in_var (Env.adds' (map fst lasts') sub) x), (ty, ck)) lasts'.
  Proof.
    intros * Hnd Hfresh * Hin.
    assert (Hf:=Hfresh). apply mmap_values, Forall2_ignore2 in Hf. simpl_Forall.
    repeat inv_bind. unfold rename_in_var. erewrite Env.In_find_adds'. 1,3:simpl; solve_In; auto.
    eapply fresh_idents_NoDupMembers; eauto.
  Qed.

  Lemma fresh_idents_In'_rename sub : forall lasts lasts' st st',
      NoDupMembers lasts ->
      fresh_idents lasts st = (lasts', st') ->
      forall x lx ty ck, In (x, lx, (ty, ck)) lasts' ->
                    In (x, (ty, ck)) lasts /\ lx = rename_in_var (Env.adds' (map fst lasts') sub) x.
  Proof.
    intros * Hnd Hfresh * Hin.
    assert (Hf:=Hfresh). apply mmap_values, Forall2_ignore1 in Hf. simpl_Forall.
    repeat inv_bind. split; eauto.
    unfold rename_in_var. erewrite Env.In_find_adds'. 1,3:simpl; eauto; solve_In.
    eapply fresh_idents_NoDupMembers; eauto.
  Qed.

  Import Permutation.

  Lemma fresh_idents_Perm : forall lasts lasts' sub st st',
      NoDupMembers lasts ->
      fresh_idents lasts st = (lasts', st') ->
      Permutation (map (fun '((_, lx), _) => lx) lasts')
        (map (rename_in_var (Env.adds' (map fst lasts') sub)) (map fst lasts)).
  Proof.
    induction lasts as [|(?&?&?)]; intros * Nd Fr; inv Nd; repeat inv_bind; auto.
    simpl.
    rewrite IHlasts; eauto.
    rewrite not_in_union_rename2.
    2:{ intros InM. eapply fresh_idents_InMembers in InM; eauto. }
    unfold rename_in_var. now rewrite Env.gss.
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

  Fact delast_scope_st_follows {A} f_dl : forall sub locs (blks : A) s' st st',
      delast_scope f_dl sub (Scope locs blks) st = (s', st') ->
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
    - (* last *)
      simpl in *. cases. now repeat inv_bind.
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

  (** *** VarsDefinedComp *)

  (* Fact mmap_vars_perm : forall (f : (Env.t ident) -> block -> FreshAnn block) blks sub blks' xs st st', *)
  (*     Forall *)
  (*       (fun blk => forall sub blk' xs st st', *)
  (*            VarsDefinedComp blk xs -> *)
  (*            f sub blk st = (blk', st') -> *)
  (*            VarsDefinedComp blk' xs) blks -> *)
  (*     Forall2 VarsDefinedComp blks xs -> *)
  (*     mmap (f sub) blks st = (blks', st') -> *)
  (*     Forall2 VarsDefinedComp blks' xs. *)
  (* Proof. *)
  (*   induction blks; intros * Hf (* Hns *) Hvars (* Hnd *) Hnorm; *)
  (*     inv Hf; inv Hvars; repeat inv_bind; simpl; constructor; eauto. *)
  (* Qed. *)

  Lemma delast_scope_vars_perm {A} P_vd P_ld P_nd f_dl : forall locs (blks: A) sub s' xs ls Γ st st',
      VarsDefinedCompScope P_vd (Scope locs blks) xs ->
      LastsDefinedScope P_ld (Scope locs blks) ls ->
      NoDupScope P_nd Γ (Scope locs blks) ->
      incl ls Γ ->
      delast_scope f_dl sub (Scope locs blks) st = (s', st') ->
      (forall blks xs ys, Permutation xs ys -> P_vd blks xs -> P_vd blks ys) ->
      (forall sub blks' xs ls Γ st st',
          P_vd blks xs ->
          P_ld blks ls ->
          P_nd Γ blks ->
          incl ls Γ ->
          f_dl sub blks st = (blks', st') ->
          exists ys, P_vd blks' ys /\ Permutation ys (xs ++ map (rename_in_var sub) ls)) ->
      VarsDefinedCompScope P_vd s' (xs ++ map (rename_in_var sub) ls).
  Proof.
    intros * Hvd Hld Hnd Hincl Hdl Hperm Hind; inv Hvd; inv Hld; inv Hnd; repeat inv_bind.
    eapply Hind in H2 as (?&Vars&Perm); eauto using incl_app, incl_appl, incl_appr, lasts_of_decls_incl.
    econstructor. eapply Hperm in Vars; eauto.
    rewrite Perm. simpl_app.
    apply Permutation_app_head.
    erewrite Permutation_swap, 2 map_map, map_ext_in with (l:=ls), map_ext_in with (l:=locs).
    apply Permutation_app_head, Permutation_app_head.
    2:{ intros []; destruct_conjs; auto. }
    2:{ intros * In. eapply not_in_union_rename2.
        intros InM. eapply fresh_idents_InMembers in InM; eauto.
        eapply H6; eauto. solve_In. }
    eapply fresh_idents_Perm in H.
    2:{ eapply NoDupMembers_map_filter; eauto.
        intros; destruct_conjs. destruct o; simpl; auto. }
    symmetry. erewrite map_ext with (l:=x), H. 2:intros; destruct_conjs; auto.
    unfold lasts_of_decls. erewrite map_map_filter, map_filter_ext; eauto.
    intros; destruct_conjs; auto. destruct o; simpl; auto.
  Qed.

  Fact mmap_vars_perm : forall blks sub blks' xs ls Γ st st',
      Forall
        (fun blk => forall sub blk' xs ls Γ st st',
             VarsDefinedComp blk xs ->
             LastsDefined blk ls ->
             NoDupLocals Γ blk ->
             incl ls Γ ->
             delast_block sub blk st = (blk', st') ->
             exists ys, VarsDefinedComp blk' ys /\ Permutation ys (xs ++ map (rename_in_var sub) ls)) blks ->
      Forall2 VarsDefinedComp blks xs ->
      Forall2 LastsDefined blks ls ->
      Forall (NoDupLocals Γ) blks ->
      incl (concat ls) Γ ->
      mmap (delast_block sub) blks st = (blks', st') ->
      exists ys, Forall2 VarsDefinedComp blks' ys /\ Permutation (concat ys) (concat xs ++ map (rename_in_var sub) (concat ls)).
  Proof.
    induction blks; intros * Hf Hvd Hld Hnd Hincl Hnorm; inv Hf; inv Hvd; inv Hld; inv Hnd; repeat inv_bind; simpl.
    - exists []. split; auto.
    - eapply H1 in H as (ys1&Hvars1&Hperm1); eauto.
      2:etransitivity; eauto; apply incl_appl, incl_refl.
      eapply IHblks in H2 as (ys2&Hvars2&Hperm2); eauto. clear IHblks.
      2:etransitivity; eauto; apply incl_appr, incl_refl.
      exists (ys1::ys2). split; [constructor; auto|].
      simpl. rewrite Hperm1, Hperm2. solve_Permutation_app.
  Qed.

  Lemma delast_block_vars_perm : forall blk sub blk' xs ls Γ st st',
      VarsDefinedComp blk xs ->
      LastsDefined blk ls ->
      NoDupLocals Γ blk ->
      incl ls Γ ->
      delast_block sub blk st = (blk', st') ->
      exists ys, VarsDefinedComp blk' ys /\ Permutation ys (xs ++ map (rename_in_var sub) ls).
  Proof.
    Opaque delast_scope.
    induction blk using block_ind2; intros * Hvars Hlast Hnd Hincl Hdl;
      inv Hvars; inv Hlast; inv Hnd; repeat inv_bind.
    - (* equation *)
      rewrite app_nil_r.
      destruct eq. simpl. do 2 esplit; eauto. constructor.
    - (* last *)
      simpl in *. cases. repeat inv_bind.
      do 2 esplit; eauto. constructor.
    - (* reset *)
      eapply mmap_vars_perm in H as (?&Vars&Perm); eauto.
      do 2 esplit; eauto. constructor; auto.
    - (* switch *)
      rewrite app_nil_r. do 2 esplit; [|reflexivity].
      constructor.
      + apply mmap_values in H0. inv H0; congruence.
      + eapply mmap_values, Forall2_ignore1 in H0. simpl_Forall; repeat inv_bind.
        repeat inv_branch. repeat inv_bind. repeat constructor; simpl; auto using incl_nil'.
        eapply mmap_vars_perm in H as (?&Vars&Perm); eauto.
        2:now eapply Forall2_map_2 with (f:=fun _ => []), Forall2_same.
        2:{ rewrite concat_map_nil; auto using incl_nil'. }
        rewrite concat_map_nil, app_nil_r in Perm.
        do 2 esplit; eauto. etransitivity; eauto.
    - (* automaton *)
      rewrite app_nil_r. do 2 esplit; [|reflexivity].
      simpl in *. cases. repeat inv_bind.
      constructor.
      + apply mmap_values in H0. inv H0; congruence.
      + eapply mmap_values, Forall2_ignore1 in H0. simpl_Forall; repeat inv_bind.
        repeat inv_branch. repeat inv_bind. constructor; eauto using incl_nil'.
        destruct s. eapply delast_scope_vars_perm in H2; eauto.
        * now rewrite app_nil_r in H2.
        * intros * Perm (?&?&?); eauto using Permutation_trans.
        * intros * (?&?&Perm1) (?&?&Perm2) Nd Incl MMap. cases. repeat inv_bind.
          eapply mmap_vars_perm in H8 as (?&Vars&Perm); eauto.
          2:{ rewrite Perm2; auto. }
          repeat (esplit; eauto).
          now rewrite Perm1, Perm2.
    - (* local *)
      eapply delast_scope_vars_perm in H0; eauto using VarsDefinedComp.
      + intros * Perm (?&?&?); eauto using Permutation_trans.
      + intros * (?&?&Perm1) (?&?&Perm2) Nd Incl MMap.
        eapply mmap_vars_perm in MMap as (?&Vars&Perm); eauto.
        2:{ rewrite Perm2; auto. }
        repeat (esplit; eauto).
        now rewrite Perm1, Perm2.
      Transparent delast_scope.
  Qed.

  Lemma delast_outs_and_block_vars_perm : forall outs blk blk' xs ls Γ st st',
      VarsDefinedComp blk xs ->
      LastsDefined blk ls ->
      NoDupLocals Γ blk ->
      incl ls Γ ->
      NoDupMembers outs ->
      Permutation ls (lasts_of_decls outs) ->
      delast_outs_and_block outs blk st = (blk', st') ->
      exists ys, VarsDefinedComp blk' ys /\ Permutation ys xs.
  Proof.
    unfold delast_outs_and_block.
    intros * VD LD ND1 Incl ND2 Perm DL. repeat inv_bind.
    cases_eqn Nil; repeat inv_bind.
    - eapply delast_block_vars_perm in H0 as (?&Vars&Perm1); eauto.
      do 2 esplit; eauto. rewrite Perm1, Perm.
      unfold lasts_of_decls. rewrite map_filter_nil, app_nil_r; auto.
      simpl_Forall.
      destruct o; simpl; auto. exfalso.
      eapply fresh_idents_In in H as (?&In). 2:solve_In; simpl; auto.
      apply is_nil_spec in Nil; subst. inv In.
    - eapply delast_block_vars_perm in H0 as (?&Vars&Perm1); eauto.
      do 2 esplit; eauto.
      repeat (econstructor; eauto). simpl. rewrite app_nil_r.
      eapply fresh_idents_Perm in H.
      2:{ eapply NoDupMembers_map_filter; eauto.
          intros; destruct_conjs. destruct o; simpl; auto. }
      rewrite Perm1. apply Permutation_app_head.
      symmetry. erewrite map_map, map_ext, H. 2:intros; destruct_conjs; auto.
      rewrite Perm. unfold lasts_of_decls.
      unfold Env.from_list. erewrite map_map_filter, map_filter_ext; eauto.
      intros; destruct_conjs. destruct o; simpl; auto.
  Qed.

  (** *** No more LastsDefined ! *)

  Lemma delast_block_lasts : forall blk sub blk' st st' ls,
      LastsDefined blk ls ->
      delast_block sub blk st = (blk', st') ->
      LastsDefined blk' [].
  Proof.
    induction blk using block_ind2; intros * Hld Hdl; inv Hld; simpl in *; repeat inv_bind.
    - (* equation *) constructor.
    - (* last *)
      cases. repeat inv_bind.
      constructor.
    - (* reset *)
      eapply mmap_values, Forall2_ignore1 in H0.
      rewrite <-concat_map_nil with (l:=x). constructor.
      simpl_Forall. inv_VarsDefined. eauto.
    - (* switch *)
      constructor.
      + apply mmap_values in H0. inv H0; congruence.
      + eapply mmap_values, Forall2_ignore1 in H0. simpl_Forall; repeat inv_bind.
        repeat inv_branch. repeat inv_bind. constructor.
        eapply mmap_values, Forall2_ignore1 in H3.
        simpl_Forall. eauto.
    - (* automaton *)
      cases. repeat inv_bind. constructor.
      + apply mmap_values in H0. inv H0; congruence.
      + eapply mmap_values, Forall2_ignore1 in H0. simpl_Forall; repeat inv_bind.
        repeat inv_branch. repeat inv_scope. repeat inv_bind. do 2 constructor. simpl.
        exists (map (fun _ => []) x3); split.
        * eapply mmap_values, Forall2_ignore1 in H6.
          simpl_Forall. inv_VarsDefined. eauto.
        * unfold lasts_of_decls.
          rewrite concat_map_nil, map_filter_app, 2 map_filter_nil; auto.
          1,2:simpl_Forall; auto.
    - (* local *)
      repeat inv_scope. repeat constructor.
      exists (map (fun _ => []) x2); split.
      + eapply mmap_values, Forall2_ignore1 in H2.
        simpl_Forall. inv_VarsDefined. eauto.
      + unfold lasts_of_decls.
        rewrite concat_map_nil, map_filter_app, 2 map_filter_nil; auto.
        1,2:simpl_Forall; auto.
  Qed.

  Lemma delast_outs_and_block_lasts : forall outs blk blk' ls st st',
      LastsDefined blk ls ->
      delast_outs_and_block outs blk st = (blk', st') ->
      LastsDefined blk' [].
  Proof.
    unfold delast_outs_and_block.
    intros * VF DL. repeat inv_bind.
    cases; repeat inv_bind; eauto using delast_block_lasts.
    do 2 econstructor. do 2 esplit; eauto using delast_block_lasts.
    unfold lasts_of_decls.
    rewrite map_filter_nil; auto.
    simpl_Forall. auto.
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

  Lemma delast_scope_GoodLocals {A} P_good1 (P_good2: _ -> Prop) f_dl : forall locs (blks: A) sub s' st st',
      GoodLocalsScope P_good1 elab_prefs (Scope locs blks) ->
      delast_scope f_dl sub (Scope locs blks) st = (s', st') ->
      (forall sub blks' st st',
          P_good1 blks ->
          f_dl sub blks st = (blks', st') ->
          P_good2 blks') ->
      GoodLocalsScope P_good2 last_prefs s'.
  Proof.
    intros * Hgood Hdl Hind; inv Hgood. repeat inv_bind.
    eapply Hind in H2; eauto.
    econstructor; eauto.
    - rewrite map_app. apply Forall_app; split.
      + erewrite map_map, map_ext; eauto using Forall_AtomOrGensym_add.
        intros; destruct_conjs; auto.
      + apply fresh_idents_prefixed in H.
        simpl_Forall; subst.
        right. repeat esplit; eauto. apply PSF.add_iff; auto.
  Qed.

  Lemma delast_block_GoodLocals : forall blk sub blk' st st',
      GoodLocals elab_prefs blk ->
      delast_block sub blk st = (blk', st') ->
      GoodLocals last_prefs blk'.
  Proof.
    Opaque delast_scope.
    induction blk using block_ind2; intros * Hg Hdl; inv Hg; repeat inv_bind.
    - (* equation *)
      constructor.
    - (* last *)
      unfold delast_block in *. cases. repeat inv_bind.
      constructor.
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
    - (* local *)
      constructor.
      eapply delast_scope_GoodLocals; eauto.
      + intros. eapply mmap_values, Forall2_ignore1 in H3.
        simpl_Forall; eauto.
        Transparent delast_scope.
  Qed.

  Lemma delast_outs_and_block_GoodLocals : forall outs blk blk' st st',
      GoodLocals elab_prefs blk ->
      delast_outs_and_block outs blk st = (blk', st') ->
      GoodLocals last_prefs blk'.
  Proof.
    unfold delast_outs_and_block.
    intros * VF DL. repeat inv_bind.
    cases; repeat inv_bind; eauto using delast_block_GoodLocals.
    do 2 constructor.
    - eapply fresh_idents_prefixed in H. simpl_Forall; subst.
      right. do 2 esplit; eauto using PSF.add_1.
    - eauto using delast_block_GoodLocals.
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
      NoDupMembers (map (fun '(_, lx, (ty, ck)) => (lx, (ty, ck, xH, @None ident))) lasts').
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

  Lemma delast_scope_NoDupLocals {A} P_good P_nd f_dl :
    forall locs (blks: A) xs sub s' st st',
      Forall (fun x => AtomOrGensym elab_prefs x \/ In x (st_ids st)) xs ->
      GoodLocalsScope P_good elab_prefs (Scope locs blks) ->
      NoDupScope P_nd xs (Scope locs blks) ->
      delast_scope f_dl sub (Scope locs blks) st = (s', st') ->
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
      NoDupScope P_nd xs s'.
  Proof.
    intros * Hat Hgood Hnd Hdl Hincl' Hind; inv Hgood; inv Hnd;
      repeat inv_bind.
    assert (Forall (fun '(_, lx, _) => exists n hint, lx = gensym last hint n) x) as Hgen.
    { eapply mmap_values, Forall2_ignore1 in H. simpl_Forall. repeat inv_bind.
      eapply fresh_ident_prefixed in H7; auto. }
    constructor.
    - eapply Hind in H0; eauto.
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
    - (* last *)
      unfold delast_block in *. cases. repeat inv_bind.
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
    - (* local *)
      constructor.
      eapply delast_scope_NoDupLocals; eauto.
      * intros. simpl_Forall.
        eapply NoDupLocals_incl'; eauto using last_not_in_elab_prefs.
      * intros; simpl in *. eapply mmap_delast_NoDupLocals; eauto.
        Transparent delast_scope.
  Qed.

  Lemma delast_outs_and_block_NoDupLocals : forall outs blk xs blk' st st',
      Forall (fun x => AtomOrGensym elab_prefs x \/ In x (st_ids st)) xs ->
      GoodLocals elab_prefs blk ->
      NoDupLocals xs blk ->
      delast_outs_and_block outs blk st = (blk', st') ->
      NoDupLocals xs blk'.
  Proof.
    unfold delast_outs_and_block.
    intros * At Good ND DL. repeat inv_bind.
    assert (Forall (fun x1 : ident => AtomOrGensym elab_prefs x1 \/ In x1 (st_ids x0)) xs) as At2.
    { simpl_Forall. destruct At as [|In]; eauto.
      right. eapply incl_map; eauto using st_follows_incl, fresh_idents_st_follows. }
    cases; repeat inv_bind; eauto using delast_block_NoDupLocals.
    do 2 constructor.
    - simpl_Forall.
      eapply delast_block_NoDupLocals; eauto.
      + apply Forall_app; split; auto.
        simpl_Forall. eapply fresh_idents_In_ids in H. simpl_Forall; auto.
      + eapply NoDupLocals_incl'. 4:eauto. 1-3:eauto using last_not_in_elab_prefs.
        intros * In. apply in_app_iff in In as [|]; auto.
        right. simpl_In.
        eapply fresh_idents_prefixed in H. simpl_Forall; eauto.
    - eapply fresh_idents_NoDup in H; eauto.
    - intros * In1 In2. simpl_In. simpl_Forall.
      destruct At as [At|StIn].
      + eapply fresh_idents_prefixed in H. simpl_Forall. subst.
        eapply contradict_AtomOrGensym; eauto using last_not_in_elab_prefs.
      + eapply fresh_idents_nIn_ids in H. simpl_Forall. contradiction.
  Qed.

  (** *** No last remaining *)

  Fact delast_scope_nolast {A} f_dl (P_nl: _ -> Prop) : forall sub locs (blks : A) s' st st',
      delast_scope f_dl sub (Scope locs blks) st = (s', st') ->
      (forall sub blks' st st',
          f_dl sub blks st = (blks', st') ->
          P_nl blks') ->
      nolast_scope P_nl s'.
  Proof.
    intros * Hdl Hind; repeat inv_bind.
    constructor; eauto.
    apply Forall_app. split; simpl_Forall; auto.
  Qed.

  Lemma delast_block_nolast : forall blk sub blk' st st',
      delast_block sub blk st = (blk', st') ->
      nolast_block blk'.
  Proof.
    Opaque delast_scope.
    induction blk using block_ind2; intros * Hdl; repeat inv_bind.
    - (* equation *)
      constructor.
    - (* last *)
      unfold delast_block in *. cases. repeat inv_bind.
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
    - (* local *)
      constructor. eapply delast_scope_nolast; eauto.
      + intros. eapply mmap_values, Forall2_ignore1 in H1.
        simpl_Forall; eauto.
        Transparent delast_scope.
  Qed.

  Lemma delast_outs_and_block_nolast : forall blk outs blk' st st',
      delast_outs_and_block outs blk st = (blk', st') ->
      nolast_block blk'.
  Proof.
    unfold delast_outs_and_block.
    intros * DL. repeat inv_bind.
    cases; repeat inv_bind; eauto using delast_block_nolast.
    do 2 constructor.
    all:simpl_Forall; eauto using delast_block_nolast.
  Qed.

  (** ** Transformation of node and program *)

  Program Definition delast_node (n: @node complete elab_prefs) : @node nolast last_prefs :=
    let res := delast_outs_and_block (n_out n) (n_block n) init_st in
    {|
      n_name := (n_name n);
      n_hasstate := (n_hasstate n);
      n_in := (n_in n);
      n_out := List.map (fun xtc => (fst xtc, (fst (fst (fst (snd xtc))), (snd (fst (fst (snd xtc)))), xH, None))) (n_out n);
      n_block := fst res;
      n_ingt0 := (n_ingt0 n);
      n_outgt0 := (n_outgt0 n);
    |}.
  Next Obligation.
    now rewrite map_length.
  Qed.
  Next Obligation.
    pose proof (n_syn n) as Syn. inversion_clear Syn as [??? Hvars Hperm].
    pose proof (n_lastd n) as (?&Last&PermL).
    pose proof (n_nodup n) as (Nd&Hndup).
    pose proof (n_good n) as (Hgood1&Hgood2&Hatom).
    apply Permutation_map_inv in Hperm as (?&?&Hperm); subst.
    destruct (delast_outs_and_block _ _ _) as (?&?) eqn:Hdl.
    assert (Hdl':=Hdl). eapply delast_outs_and_block_vars_perm in Hdl as (?&Vars&Perm); eauto.
    2:{ rewrite PermL. apply incl_appr, lasts_of_decls_incl. }
    2:{ apply fst_NoDupMembers. eauto using NoDup_app_r. }
    apply Permutation_map_inv in Perm as (?&?&Perm); subst.
    do 2 esplit.
    - eapply VarsDefinedComp_VarsDefined
        with (Γ:=senv_of_decls (map (fun '(x, (ty, ck, cx, o)) => (x, (ty, ck, xH, None))) x2)); simpl; eauto.
      1,2:erewrite map_fst_senv_of_decls, map_map, map_ext with (g:=fst); eauto.
      2,3:intros; destruct_conjs; auto.
      rewrite <-Perm, <-Hperm.
      eapply NoDupLocals_incl, delast_outs_and_block_NoDupLocals. 3-5:eauto.
      2:simpl_Forall; auto.
      solve_incl_app; reflexivity.
    - unfold senv_of_decls.
      rewrite <-Perm, <-Hperm.
      erewrite 2 map_map, map_ext; eauto. intros; destruct_conjs; auto.
  Qed.
  Next Obligation.
    pose proof (n_lastd n) as (?&Last&_).
    destruct (delast_outs_and_block _ _ _) as (?&st') eqn:Hdl.
    do 2 esplit; eauto using delast_outs_and_block_lasts.
    unfold lasts_of_decls. rewrite map_filter_nil; auto.
    simpl_Forall; auto.
  Qed.
  Next Obligation.
    pose proof (n_good n) as (Hgood1&Hgood2&_).
    pose proof (n_nodup n) as (Hnd1&Hnd2).
    rewrite map_map. repeat split; auto.
    destruct (delast_outs_and_block _ _ _) as (?&st') eqn:Hdl.
    eapply delast_outs_and_block_NoDupLocals; eauto.
    simpl_Forall; auto.
  Qed.
  Next Obligation.
    pose proof (n_good n) as (Hgood1&Hgood2&Hatom).
    pose proof (n_nodup n) as (Hnd1&Hnd2).
    rewrite map_map.
    destruct (delast_outs_and_block _ _) as (?&?) eqn:Hdl. simpl.
    repeat split; eauto using Forall_AtomOrGensym_add.
    eapply delast_outs_and_block_GoodLocals; eauto.
  Qed.
  Next Obligation.
    pose proof (n_syn n) as Syn. inversion_clear Syn as [??? Hvars Hperm].
    pose proof (n_lastd n) as (?&Last&PermL).
    pose proof (n_nodup n) as (Nd&Hndup).
    destruct (delast_outs_and_block _ _) as (?&?) eqn:Hdl.
    constructor; eauto using delast_outs_and_block_nolast.
    - simpl_Forall; auto.
    - eapply delast_outs_and_block_vars_perm in Hdl as (?&?&Perm). 2-7:eauto.
      + do 2 esplit; eauto.
        rewrite Perm, Hperm, map_map; auto.
      + rewrite PermL; auto using incl_appr, lasts_of_decls_incl.
      + apply fst_NoDupMembers; eauto using NoDup_app_r.
  Qed.

  Global Program Instance delast_node_transform_unit: TransformUnit (@node complete elab_prefs) node :=
    { transform_unit := delast_node }.

  Global Program Instance delast_global_without_units : TransformProgramWithoutUnits (@global complete elab_prefs) (@global nolast last_prefs) :=
    { transform_program_without_units := fun g => Global g.(types) g.(externs) [] }.

  Definition delast_global : @global complete elab_prefs -> @global nolast last_prefs :=
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
      simpl. erewrite map_map. apply map_ext. intros; destruct_conjs; auto.
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
