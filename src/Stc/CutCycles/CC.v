From Coq Require Import List Permutation.
Import List.ListNotations.
Open Scope list_scope.

From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import FunctionalEnvironment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import CommonProgram.
From Velus Require Import Fresh.

From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import Stc.StcSyntax.

Module Type EXT_CC
  (Ids   : IDS)
  (Op    : OPERATORS)
  (OpAux : OPERATORS_AUX Ids Op)
  (Cks   : CLOCKS Ids Op OpAux)
  (CESyn : CESYNTAX    Ids Op OpAux Cks)
  (Syn   : STCSYNTAX Ids Op OpAux Cks CESyn).

  (** In the returned list a pair (x, y) indicates
      that x should be cut in transition constraint y *)
  Parameter cutting_points : list ident -> list ident -> list Syn.trconstr -> list (ident * ident).

End EXT_CC.

Module Type CC
  (Import Ids   : IDS)
  (Import Op    : OPERATORS)
  (OpAux        : OPERATORS_AUX Ids Op)
  (Import Cks   : CLOCKS Ids Op OpAux)
  (Import CESyn : CESYNTAX    Ids Op OpAux Cks)
  (Import Syn   : STCSYNTAX Ids Op OpAux Cks CESyn)
  (ECC          : EXT_CC Ids Op OpAux Cks CESyn Syn).

  Module Fresh := Fresh.Fresh(Ids).
  Import Fresh Notations Facts Tactics.
  Local Open Scope fresh_monad_scope.

  Section rename.
    Variable x : var_last.
    Variable y : ident.

    Definition rename_var id :=
      match x with
      | Var x => if id ==b x then y else id
      | _ => id
      end.

    (* Definition rename_last id := *)
    (*   match x with *)
    (*   | Last x => if id ==b x then y else id *)
    (*   | _ => id *)
    (*   end. *)

    (* Variable subl subn : Env.t (ident * ident). *)

    Fixpoint rename_clock (ck : clock) :=
      match ck with
      | Cbase => Cbase
      | Con ck x (ty, k) => Con (rename_clock ck) (rename_var x) (ty, k)
      end.

    Fixpoint rename_exp (e : exp) :=
      match e with
      | Econst _ | Eenum _ _ => e
      | Evar x ty => Evar (rename_var x) ty
      | Elast id ty => match x with
                     | Last x => if id ==b x then Evar y ty else Elast id ty
                     | _ => Elast id ty
                     end
      | Ewhen e (x, ty) k => Ewhen (rename_exp e) (x, ty) k
      | Eunop op e1 ty => Eunop op (rename_exp e1) ty
      | Ebinop op e1 e2 ty => Ebinop op (rename_exp e1) (rename_exp e2) ty
      end.

    Fixpoint rename_cexp (e : cexp) :=
      match e with
      | Emerge (x, tx) es ty => Emerge (x, tx) (map rename_cexp es) ty
      | Ecase e es d => Ecase (rename_exp e) (map (option_map rename_cexp) es) (rename_cexp d)
      | Eexp e => Eexp (rename_exp e)
      end.

    Definition rename_rhs (e : rhs) :=
      match e with
      | Eextcall f es ty => Eextcall f (map rename_exp es) ty
      | Ecexp e => Ecexp (rename_cexp e)
      end.
  End rename.

  Definition rename_trconstr i x y (tc : trconstr) :=
    match tc with
    | TcDef ck i' rhs =>
        if i' ==b i then TcDef ck i' (rename_rhs x y rhs)
        else tc
    | TcReset _ _ => tc (* Reset constraints do not contain expressions *)
    | TcUpdate ck ckrs (UpdLast i' e) =>
        if i' ==b i then TcUpdate ck ckrs (UpdLast i' (rename_cexp x y e))
        else tc
    | TcUpdate ck ckrs (UpdNext i' e) =>
        if i' ==b i then TcUpdate ck ckrs (UpdNext i' (rename_exp x y e))
        else tc
    | TcUpdate ck ckrs (UpdInst i' xs f es) =>
        match x with
        | Last _ =>
            if i' ==b i then TcUpdate ck ckrs (UpdInst i' xs f (map (rename_exp x y) es))
            else tc
        | Var _ => tc
        end
    end.

  (** System *)

  Definition FreshAnn A := Fresh stc A (ident * (type * clock)).

  Definition cut_cycles_tcs (lasts nexts: list ((ident * ident) * (const * type * clock))) tcs : FreshAnn (list trconstr) :=
    (* Lasts *)
    do nlasts <- fresh_idents (map (fun '((x, i), (_, ty, ck)) => (x, (i, (ty, ck)))) lasts);
    let tcs := fold_left (fun tcs '(x, lx, (i, _)) => map (rename_trconstr i (Last x) lx) tcs) nlasts tcs in
    let eqlasts := map (fun '(x, lx, (_, (ty, ck))) => TcDef ck lx (Ecexp (Eexp (Elast x ty)))) nlasts in
    (* Nexts *)
    do nnexts <- fresh_idents (map (fun '((x, i), (_, ty, ck)) => (x, (i, (ty, ck)))) nexts);
    let tcs := fold_left (fun tcs '(x, lx, (i, _)) => map (rename_trconstr i (Var x) lx) tcs) nnexts tcs in
    let eqnexts := map (fun '(x, lx, (_, (ty, ck))) => TcDef ck lx (Ecexp (Eexp (Evar x ty)))) nnexts in

    ret (eqlasts++eqnexts++tcs).

  (** ** Properties *)

  Lemma map_fold_rename {A} (cons: ident -> var_last) : forall (xs: list (ident * ident * (ident * A))) tcs,
      fold_left (fun tcs '(x, lx, (i, _)) => map (rename_trconstr i (cons x) lx) tcs) xs tcs
      = map (fun tc => fold_left (fun tc '(x, lx, (i, _)) => rename_trconstr i (cons x) lx tc) xs tc) tcs.
  Proof.
    intros.
    erewrite <-fold_left_rev_right, map_ext with (g:=fun _ => fold_right _ _ _).
    2:intros; now rewrite <-fold_left_rev_right.
    generalize (rev xs) as xs'.
    induction xs'; destruct_conjs; simpl.
    - intros. now rewrite map_id.
    - intros *. rewrite IHxs', map_map. reflexivity.
  Qed.

  (** Typeof *)
  Section rename_typeof.
    Lemma rename_exp_typeof subl subn : forall e,
        typeof (rename_exp subl subn e) = typeof e.
    Proof.
      induction e; simpl; cases; auto.
    Qed.

    Lemma rename_cexp_typeofc subl subn : forall ce,
        typeofc (rename_cexp subl subn ce) = typeofc ce.
    Proof.
      induction ce using cexp_ind2'; simpl; cases; eauto using rename_exp_typeof.
    Qed.

    Lemma rename_rhs_typeofr subl subn : forall e,
        typeofr (rename_rhs subl subn e) = typeofr e.
    Proof.
      intros []; simpl; auto using rename_cexp_typeofc.
    Qed.
  End rename_typeof.

  (** *** Variables, Last, Next Definitions *)

  Lemma fresh_idents_vars_perm : forall xs xs' st st',
      @fresh_idents stc (ident * (type * clock)) xs st = (xs', st') ->
      Permutation (st_ids st') (map (fun '(_, lx, _) => lx) xs' ++ st_ids st).
  Proof.
    induction xs as [|(?&?&?)]; intros * Fr; repeat inv_bind; simpl; auto.
    apply fresh_ident_vars_perm in H.
    erewrite IHxs, <-H, Permutation_middle; eauto.
  Qed.

  Lemma cut_cycles_tcs_variables : forall lasts nexts tcs tcs' st',
      cut_cycles_tcs lasts nexts tcs init_st = (tcs', st') ->
      Permutation (variables tcs') (variables tcs ++ st_ids st').
  Proof.
    intros * Cut. unfold cut_cycles_tcs in *. repeat inv_bind.
    do 2 (erewrite fresh_idents_vars_perm; eauto).
    unfold st_ids. rewrite ? variables_app, init_st_anns, app_nil_r.
    rewrite Permutation_app_comm, <-app_assoc, Permutation_app_comm, <-app_assoc.
    apply Permutation_app; [|rewrite Permutation_app_comm; apply Permutation_app].
    - eapply fold_left_ind2, fold_left_ind2; try reflexivity.
      1,2:intros * Perm; rewrite <-Perm; clear Perm.
      1,2:induction acc as [|[]]; simpl; destruct_conjs; cases; simpl; auto using Permutation_app.
    - clear - x1. induction x1 as [|]; destruct_conjs; simpl; auto.
    - clear - x. induction x as [|]; destruct_conjs; simpl; auto.
  Qed.

  Lemma cut_cycles_tcs_lasts_of : forall lasts nexts tcs tcs' st',
      cut_cycles_tcs lasts nexts tcs init_st = (tcs', st') ->
      lasts_of tcs' = lasts_of tcs.
  Proof.
    intros * Cut. unfold cut_cycles_tcs in *. repeat inv_bind.
    rewrite ? lasts_of_app.
    replace (lasts_of (map _ x)) with (@nil (ident * type)).
    2:{ clear - x. induction x as [|]; destruct_conjs; simpl; auto. }
    replace (lasts_of (map _ x1)) with (@nil (ident * type)).
    2:{ clear - x1. induction x1 as [|]; destruct_conjs; simpl; auto. }
    simpl.
    eapply fold_left_ind2, fold_left_ind2; try reflexivity.
    1,2:intros * Perm; rewrite <-Perm; clear Perm.
    1,2:destruct_conjs.
    1,2:induction acc as [|[| |?? []]]; simpl in *; try destruct (_ ==b _); auto.
    1,2:rewrite rename_cexp_typeofc; auto.
  Qed.

  Lemma cut_cycles_tcs_nexts_of : forall lasts nexts tcs tcs' st',
      cut_cycles_tcs lasts nexts tcs init_st = (tcs', st') ->
      nexts_of tcs' = nexts_of tcs.
  Proof.
    intros * Cut. unfold cut_cycles_tcs in *. repeat inv_bind.
    rewrite ? nexts_of_app.
    replace (nexts_of (map _ x)) with (@nil (ident * type)).
    2:{ clear - x. induction x as [|]; destruct_conjs; simpl; auto. }
    replace (nexts_of (map _ x1)) with (@nil (ident * type)).
    2:{ clear - x1. induction x1 as [|]; destruct_conjs; simpl; auto. }
    simpl.
    eapply fold_left_ind2, fold_left_ind2; try reflexivity.
    1,2:intros * Perm; rewrite <-Perm; clear Perm.
    1,2:destruct_conjs.
    1,2:induction acc as [|[| |?? []]]; simpl in *; try destruct (_ ==b _); auto.
    1,2:rewrite rename_exp_typeof; auto.
  Qed.

  Lemma cut_cycles_tcs_state_resets_of : forall lasts nexts tcs tcs' st',
      cut_cycles_tcs lasts nexts tcs init_st = (tcs', st') ->
      state_resets_of tcs' = state_resets_of tcs.
  Proof.
    intros * Cut. unfold cut_cycles_tcs in *. repeat inv_bind.
    rewrite ? state_resets_of_app.
    replace (state_resets_of (map _ x)) with (@nil ident).
    2:{ clear - x. induction x as [|]; destruct_conjs; simpl; auto. }
    replace (state_resets_of (map _ x1)) with (@nil ident).
    2:{ clear - x1. induction x1 as [|]; destruct_conjs; simpl; auto. }
    simpl.
    eapply fold_left_ind2, fold_left_ind2; try reflexivity.
    1,2:intros * Perm; rewrite <-Perm; clear Perm.
    1,2:destruct_conjs.
    1,2:induction acc as [|[| |?? []]]; simpl in *; try destruct (_ ==b _); cases; auto.
  Qed.

  Lemma cut_cycles_tcs_insts_of : forall lasts nexts tcs tcs' st',
      cut_cycles_tcs lasts nexts tcs init_st = (tcs', st') ->
      insts_of tcs' = insts_of tcs.
  Proof.
    intros * Cut. unfold cut_cycles_tcs in *. repeat inv_bind.
    rewrite ? insts_of_app.
    replace (insts_of (map _ x)) with (@nil (ident * ident)).
    2:{ clear - x. induction x as [|]; destruct_conjs; simpl; auto. }
    replace (insts_of (map _ x1)) with (@nil (ident * ident)).
    2:{ clear - x1. induction x1 as [|]; destruct_conjs; simpl; auto. }
    simpl.
    eapply fold_left_ind2, fold_left_ind2; try reflexivity.
    1,2:intros * Perm; rewrite <-Perm; clear Perm.
    1,2:destruct_conjs.
    1,2:induction acc as [|[| |?? []]]; simpl in *; try destruct (_ ==b _); cases; auto.
  Qed.

  Lemma cut_cycles_tcs_inst_resets_of : forall lasts nexts tcs tcs' st',
      cut_cycles_tcs lasts nexts tcs init_st = (tcs', st') ->
      inst_resets_of tcs' = inst_resets_of tcs.
  Proof.
    intros * Cut. unfold cut_cycles_tcs in *. repeat inv_bind.
    rewrite ? inst_resets_of_app.
    replace (inst_resets_of (map _ x)) with (@nil (ident * ident)).
    2:{ clear - x. induction x as [|]; destruct_conjs; simpl; auto. }
    replace (inst_resets_of (map _ x1)) with (@nil (ident * ident)).
    2:{ clear - x1. induction x1 as [|]; destruct_conjs; simpl; auto. }
    simpl.
    eapply fold_left_ind2, fold_left_ind2; try reflexivity.
    1,2:intros * Perm; rewrite <-Perm; clear Perm.
    1,2:destruct_conjs.
    1,2:induction acc as [|[| |?? []]]; simpl in *; try destruct (_ ==b _); cases; auto.
  Qed.

  (** *** AtomOrGensym / NoDup *)

  Fact AtomOrGensym_add : forall x,
      AtomOrGensym (PSP.of_list lustre_prefs) x ->
      AtomOrGensym (PSP.of_list gensym_prefs) x.
  Proof.
    intros * At. simpl in *.
    destruct At as [|(?&In&At)]; [left|right]; auto.
    do 2 esplit; eauto.
    rewrite ? PS.add_spec in *. firstorder.
  Qed.

  Lemma stc_not_in_lustre_prefs :
    ~PS.In stc (PSP.of_list lustre_prefs).
  Proof.
    intros In. simpl in *.
    rewrite ? PS.add_spec, PSF.empty_iff in In.
    pose proof gensym_prefs_NoDup as ND. unfold gensym_prefs in ND.
    rewrite ? NoDup_cons_iff in ND. destruct_conjs.
    repeat take (_ \/ _) and destruct it as [Eq|Eq]; eauto 9 with datatypes.
  Qed.

  Program Definition cut_cycles_system (b: @system (PSP.of_list lustre_prefs)) : @system (PSP.of_list gensym_prefs) :=
    let tocut := ECC.cutting_points (map fst b.(s_lasts)) (map fst b.(s_nexts)) b.(s_tcs) in
    let tocut := Env.from_list tocut in
    let res := cut_cycles_tcs
                 (map_filter (fun x => match Env.find (fst x) tocut with
                                    | Some i => Some (fst x, i, snd x)
                                    | None => None
                                    end) b.(s_lasts))
                 (map_filter (fun x => match Env.find (fst x) tocut with
                                    | Some i => Some (fst x, i, snd x)
                                    | None => None
                                    end) b.(s_nexts))
                 b.(s_tcs) init_st in
    {|
      s_name  := b.(s_name);
      s_subs  := b.(s_subs);
      s_in    := b.(s_in);
      s_vars  := b.(s_vars)++map (fun xann => (fst xann, snd (snd xann))) (st_anns (snd res));
      s_lasts := b.(s_lasts);
      s_nexts := b.(s_nexts);
      s_out   := b.(s_out);
      s_tcs   := fst res;

      s_ingt0             := b.(s_ingt0);
      s_nodup_states_subs := b.(s_nodup_states_subs);
    |}.
  Next Obligation.
    destruct (cut_cycles_tcs _ _ _) as (tcs'&st') eqn:Htcs; simpl.
    pose proof (s_nodup b) as ND.
    pose proof (s_good b) as Good. rewrite ? map_app, ? Forall_app in Good. destruct_conjs.
    rewrite map_app, <-app_assoc.
    eapply Permutation_NoDup, NoDup_app' with (ws:=map fst (st_anns st'));
      [|apply ND|apply st_valid_NoDup|].
    - rewrite map_map. solve_Permutation_app.
    - rewrite ? Forall_app; repeat split; simpl_Forall.
      all:eapply st_valid_AtomOrGensym_nIn; eauto using stc_not_in_lustre_prefs.
  Qed.
  Next Obligation.
    destruct (cut_cycles_tcs _ _ _) as (tcs'&st') eqn:Htcs; simpl.
    apply cut_cycles_tcs_variables in Htcs.
    pose proof (s_vars_out_in_tcs b) as Perm.
    erewrite map_app, <-app_assoc, Permutation_swap, Perm, Htcs, map_map.
    apply Permutation_app_comm.
  Qed.
  Next Obligation.
    destruct (cut_cycles_tcs _ _ _) as (tcs'&st') eqn:Htcs; simpl.
    pose proof (s_lasts_in_tcs b) as Lasts.
    eapply cut_cycles_tcs_lasts_of in Htcs. now rewrite Htcs.
  Qed.
  Next Obligation.
    destruct (cut_cycles_tcs _ _ _) as (tcs'&st') eqn:Htcs; simpl.
    pose proof (s_last_consistency b) as Cons.
    unfold cut_cycles_tcs in *. repeat inv_bind.
    intros ?? Ex ?. unfold last_consistency, Last_with_reset_in, Is_reset_state_in in *.
    rewrite ? List.Exists_app in *. destruct Ex as [Ex|[Ex|Ex]]; simpl_Exists; try now inv Ex.
    rewrite ? map_fold_rename in *. simpl_In.
    assert (exists ck e, x2 = TcUpdate ck ckrs (UpdLast s e)) as (?&?&?); subst.
    { revert Ex. eapply fold_left_ind2, fold_left_ind2.
      3:intros * Ex; inv Ex; eauto.
      1,2:(intros; destruct_conjs; subst; destruct acc as [|? []|?? []]; simpl in *; cases;
           inv Ex; eauto with stcsyntax).
    }
    rewrite Cons; [|solve_Exists; constructor]. clear Ex.
    split; [intros Ex|intros [Ex|[Ex|Ex]]]; simpl_Exists; try now inv Ex.
    - do 2 right. solve_Exists. inv Ex.
      eapply fold_left_ind2, fold_left_ind2; try constructor.
      1,2:intros; destruct_conjs; inv H1; simpl; constructor.
    - revert Ex. eapply fold_left_ind2, fold_left_ind2.
      3:intros * Ex; inv Ex; eauto.
      1,2:(intros; destruct_conjs; subst; destruct acc as [|? []|?? []]; simpl in *; cases;
           inv Ex; eauto with stcsyntax).
      solve_Exists. constructor.
  Qed.
  Next Obligation.
    destruct (cut_cycles_tcs _ _ _) as (tcs'&st') eqn:Htcs; simpl.
    pose proof (s_nexts_in_tcs b) as Nexts.
    eapply cut_cycles_tcs_nexts_of in Htcs. now rewrite Htcs.
  Qed.
  Next Obligation.
    destruct (cut_cycles_tcs _ _ _) as (tcs'&st') eqn:Htcs; simpl.
    pose proof (s_next_consistency b) as Cons.
    unfold cut_cycles_tcs in *. repeat inv_bind.
    intros ?? Ex ?. unfold next_consistency, Next_with_reset_in, Is_reset_state_in in *.
    rewrite ? List.Exists_app in *. destruct Ex as [Ex|[Ex|Ex]]; simpl_Exists; try now inv Ex.
    rewrite ? map_fold_rename in *. simpl_In.
    assert (exists ck e, x2 = TcUpdate ck ckrs (UpdNext s e)) as (?&?&?); subst.
    { revert Ex. eapply fold_left_ind2, fold_left_ind2.
      3:intros * Ex; inv Ex; eauto.
      1,2:(intros; destruct_conjs; subst; destruct acc as [|? []|?? []]; simpl in *; cases;
           inv Ex; eauto with stcsyntax).
    }
    rewrite Cons; [|solve_Exists; constructor]. clear Ex.
    split; [intros Ex|intros [Ex|[Ex|Ex]]]; simpl_Exists; try now inv Ex.
    - do 2 right. solve_Exists. inv Ex.
      eapply fold_left_ind2, fold_left_ind2; try constructor.
      1,2:intros; destruct_conjs; inv H1; simpl; constructor.
    - revert Ex. eapply fold_left_ind2, fold_left_ind2.
      3:intros * Ex; inv Ex; eauto.
      1,2:(intros; destruct_conjs; subst; destruct acc as [|? []|?? []]; simpl in *; cases;
           inv Ex; eauto with stcsyntax).
      solve_Exists. constructor.
  Qed.
  Next Obligation.
    destruct (cut_cycles_tcs _ _ _) as (tcs'&st') eqn:Htcs; simpl.
    pose proof (s_state_reset_incl b) as Incl.
    erewrite cut_cycles_tcs_state_resets_of, cut_cycles_tcs_lasts_of, cut_cycles_tcs_nexts_of; eauto.
  Qed.
  Next Obligation.
    destruct (cut_cycles_tcs _ _ _) as (tcs'&st') eqn:Htcs; simpl.
    pose proof (s_subs_in_tcs b) as Sub.
    erewrite cut_cycles_tcs_inst_resets_of, cut_cycles_tcs_insts_of; eauto.
  Qed.
  Next Obligation.
    destruct (cut_cycles_tcs _ _ _) as (tcs'&st') eqn:Htcs; simpl.
    pose proof (s_subs_insts_of b) as Sub.
    erewrite cut_cycles_tcs_insts_of; eauto.
  Qed.
  Next Obligation.
    destruct (cut_cycles_tcs _ _ _) as (tcs'&st') eqn:Htcs; simpl.
    pose proof (s_inst_consistency b) as Cons.
    unfold cut_cycles_tcs in *. repeat inv_bind.
    intros ?? Ex ?. unfold inst_consistency, Inst_with_reset_in, Is_reset_inst_in in *.
    rewrite ? List.Exists_app in *. destruct Ex as [Ex|[Ex|Ex]]; simpl_Exists; try now inv Ex.
    rewrite ? map_fold_rename in *. simpl_In.
    assert (exists ck xs f es, x2 = TcUpdate ck ckrs (UpdInst s xs f es)) as (?&?&?&?&?); subst.
    { revert Ex. eapply fold_left_ind2, fold_left_ind2.
      3:intros * Ex; inv Ex; eauto.
      1,2:(intros; destruct_conjs; subst; destruct acc as [|? []|?? []]; simpl in *; cases;
           inv Ex; eauto with stcsyntax).
    }
    rewrite Cons; [|solve_Exists; constructor]. clear Ex.
    split; [intros Ex|intros [Ex|[Ex|Ex]]]; simpl_Exists; try now inv Ex.
    - do 2 right. solve_Exists. inv Ex.
      eapply fold_left_ind2, fold_left_ind2; try constructor.
      1,2:intros; destruct_conjs; inv H1; simpl; constructor.
    - revert Ex. eapply fold_left_ind2, fold_left_ind2.
      3:intros * Ex; inv Ex; eauto.
      1,2:(intros; destruct_conjs; subst; destruct acc as [|? []|?? []]; simpl in *; cases;
           inv Ex; eauto with stcsyntax).
      solve_Exists. constructor.
  Qed.
  Next Obligation.
    destruct (cut_cycles_tcs _ _ _) as (tcs'&st') eqn:Htcs; simpl.
    pose proof (s_inst_reset_incl b) as Sub.
    erewrite cut_cycles_tcs_inst_resets_of, cut_cycles_tcs_insts_of; eauto.
  Qed.
  Next Obligation.
    destruct (cut_cycles_tcs _ _ _) as (tcs'&st') eqn:Htcs.
    pose proof b.(s_good) as Good.
    rewrite ? map_app, ? Forall_app in *. destruct_conjs.
    repeat (split; auto); simpl_Forall; eauto using AtomOrGensym_add.
    pose proof (Ker.st_valid_prefixed st') as Pref. unfold Ker.st_ids in Pref.
    simpl_Forall; subst.
    right. do 2 esplit; eauto.
    rewrite ? PS.add_spec. firstorder.
  Qed.

  Definition cut_cycles P : program :=
    Program P.(types) P.(externs) (map cut_cycles_system P.(systems)).

  Lemma cut_cycles_map_name : forall P,
      map s_name (map cut_cycles_system P) = map s_name P.
  Proof.
    induction P as [|b]; auto.
    destruct b; simpl.
    simpl in *; now rewrite IHP.
  Qed.

  Lemma cut_cycles_find_system :
    forall P P' f s,
      find_system f P = Some (s, P') ->
      find_system f (cut_cycles P) = Some (cut_cycles_system s, cut_cycles P').
  Proof.
    intros []; induction systems0 as [|s']; [now inversion 1|].
    intros * Hfind.
    setoid_rewrite find_unit_cons; simpl; eauto.
    eapply find_unit_cons in Hfind as [[E Hfind]|[E Hfind]]; simpl in *; eauto.
    inv Hfind; auto.
  Qed.

  Lemma cut_cycles_find_system' :
    forall P f s P',
      find_system f (cut_cycles P) = Some (s, P') ->
      exists s' P'',
        find_system f P = Some (s', P'')
        /\ s = cut_cycles_system s'
        /\ P' = cut_cycles P''.
  Proof.
    intros []; induction systems0 as [|sys]; [now inversion 1|].
    intros * Hfind; unfold find_system, find_unit in *; simpl in *.
    destruct (ident_eq_dec sys.(s_name) f); eauto.
    inv Hfind; eauto.
  Qed.

  (** Additional properties of fresh_idents *)

  Lemma fresh_idents_In_anns2 {prefs A} : forall xs1 xs2 xs1' xs2' st0 st1 st2,
      @fresh_idents prefs A xs1 st0 = (xs1', st1) ->
      @fresh_idents prefs A xs2 st1 = (xs2', st2) ->
      Forall (fun '(_, lx, ann) => In (lx, ann) (st_anns st2)) (xs1' ++ xs2').
  Proof.
    intros * Fr1 Fr2.
    apply Forall_app; split; eauto using fresh_idents_In_anns.
    apply fresh_idents_In_anns in Fr1.
    simpl_Forall. eapply st_follows_incl; eauto using fresh_idents_st_follows.
  Qed.

  Lemma fresh_idents_In_anns2' {prefs A} : forall xs1 xs2 xs1' xs2' st1 st2,
      @fresh_idents prefs A xs1 init_st = (xs1', st1) ->
      @fresh_idents prefs A xs2 st1 = (xs2', st2) ->
      Forall (fun '(lx, ann) => exists x, In (x, ann) (xs1 ++ xs2)) (st_anns st2).
  Proof.
    intros * Fr1 Fr2.
    do 2 (erewrite fresh_idents_anns; eauto).
    rewrite init_st_anns, app_nil_r.
    apply Forall_app; split; simpl_Forall.
    - eapply fresh_idents_In' in Fr2; eauto with datatypes.
    - eapply fresh_idents_In' in Fr1; eauto with datatypes.
  Qed.

End CC.

Module CCFun
  (Ids   : IDS)
  (Op    : OPERATORS)
  (OpAux : OPERATORS_AUX Ids Op)
  (Cks   : CLOCKS Ids Op OpAux)
  (CESyn : CESYNTAX    Ids Op OpAux Cks)
  (Syn   : STCSYNTAX Ids Op OpAux Cks CESyn)
  (ECC   : EXT_CC Ids Op OpAux Cks CESyn Syn)
  <: CC Ids Op OpAux Cks CESyn Syn ECC.
  Include CC Ids Op OpAux Cks CESyn Syn ECC.
End CCFun.
