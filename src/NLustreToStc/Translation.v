From Coq Require Import FSets.FMapPositive.
From Coq Require Import PArith.
From Velus Require Import Common.
From Velus Require Import CommonProgram.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Environment.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import NLustre.Memories.
From Velus Require Import Stc.StcSyntax.
From Velus Require Environment.

From Coq Require Import List.
Import List.ListNotations.
From Coq Require Import Sorting.Permutation.
From Coq Require Import Morphisms.

(* Open Scope positive. *)
Open Scope list.

(** * Translation *)

Module Type TRANSLATION
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks   : CLOCKS    Ids Op OpAux)
       (Import CESyn : CESYNTAX  Ids Op OpAux Cks)
       (Import SynNL : NLSYNTAX  Ids Op OpAux Cks CESyn)
       (SynStc       : STCSYNTAX Ids Op OpAux Cks CESyn)
       (Import Mem   : MEMORIES  Ids Op OpAux Cks CESyn SynNL).

  Definition gather_eq acc (eq: equation): (_ * _ * _) :=
    match eq with
    | EqLast x ty ck c0 xrs => ((x, (c0, ty, ck, xrs)) :: fst (fst acc), snd (fst acc), snd acc)
    | EqFby x ck c0 e xrs => (fst (fst acc), (x, (c0, typeof e, ck)) :: snd (fst acc), snd acc)
    | EqApp (x :: _) _ f _ _ => (fst acc, (x, f) :: snd acc)
    | _ => acc
    end.

  Definition gather_eqs (eqs: list equation) :=
    fold_left gather_eq eqs (([], []), []).

  (** ** Translation *)

  Section translate_eqns.
    Variable lasts : Env.t (list (ident * clock)).

    Definition translate_eqn (eqn: equation) : list SynStc.trconstr :=
      match eqn with
      | EqDef x ck (Ecexp e) =>
          match Env.find x lasts with
          | None => [ SynStc.TcDef ck x (Ecexp e) ]
          | Some xrs =>
              let ckrs := map (fun '(xr, ckr) => Con ckr xr (bool_velus_type, true_tag)) xrs in
              [ SynStc.TcUpdate ck ckrs (SynStc.UpdLast x e) ]
          end
      | EqDef x ck r => [ SynStc.TcDef ck x r ]
      | EqApp [] _ _ _ _ =>
          []                        (* This way we can ensure b_blocks_in_eqs *)
      | EqApp (x :: xs) ck f les xrs =>
          let ckrs := map (fun '(xr, ckr) => Con ckr xr (bool_velus_type, true_tag)) xrs in
          SynStc.TcUpdate ck ckrs (SynStc.UpdInst x (x :: xs) f les)
            ::(map (fun ckr => SynStc.TcReset ckr (SynStc.ResInst x f)) ckrs)
      | EqLast x ty ck c0 xrs =>
          let ckrs := map (fun '(xr, ckr) => Con ckr xr (bool_velus_type, true_tag)) xrs in
          (map (fun ckr => SynStc.TcReset ckr (SynStc.ResState x ty c0)) ckrs)
      | EqFby x ck c0 e xrs =>
          let ckrs := map (fun '(xr, ckr) => Con ckr xr (bool_velus_type, true_tag)) xrs in
          SynStc.TcUpdate ck ckrs (SynStc.UpdNext x e)
            ::(map (fun ckr => SynStc.TcReset ckr (SynStc.ResState x (typeof e) c0)) ckrs)
      end.

    Definition translate_eqns (eqns: list equation) : list SynStc.trconstr :=
      flat_map translate_eqn eqns.

  End translate_eqns.

  (** Properties of translation functions *)

  Lemma gather_eqs_last_flat_map:
    forall eqs, Permutation (fst (fst (gather_eqs eqs)))
             (flat_map (fun eq => fst (fst (gather_eq ([], [], []) eq))) eqs).
  Proof.
    unfold gather_eqs. intros eqs.
    rewrite <-fold_left_rev_right, Permutation_flat_map; [|apply Permutation_rev].
    generalize (rev eqs) as eqs'. clear eqs.
    induction eqs' as [ | eq eqs IHeqs ]; intros; simpl; auto.
    unfold gather_eq. cases; simpl; auto.
  Qed.

  Lemma gather_eqs_next_flat_map:
    forall eqs, Permutation (snd (fst (gather_eqs eqs)))
             (flat_map (fun eq => snd (fst (gather_eq ([], [], []) eq))) eqs).
  Proof.
    unfold gather_eqs. intros eqs.
    rewrite <-fold_left_rev_right, Permutation_flat_map; [|apply Permutation_rev].
    generalize (rev eqs) as eqs'. clear eqs.
    induction eqs' as [ | eq eqs IHeqs ]; intros; simpl; auto.
    unfold gather_eq. cases; simpl; auto.
  Qed.

  Lemma gather_eqs_inst_flat_map:
    forall eqs, Permutation (snd (gather_eqs eqs))
             (flat_map (fun eq => snd (gather_eq ([], [], []) eq)) eqs).
  Proof.
    unfold gather_eqs. intros eqs.
    rewrite <-fold_left_rev_right, Permutation_flat_map; [|apply Permutation_rev].
    generalize (rev eqs) as eqs'. clear eqs.
    induction eqs' as [ | eq eqs IHeqs ]; intros; simpl; auto.
    unfold gather_eq. cases; simpl; auto.
  Qed.

  Lemma gather_eqs_inst:
    forall eqs, Permutation (snd (gather_eqs eqs)) (gather_insts eqs).
  Proof.
    intro eqs.
    assert (Hgen: forall F S,
               Permutation (snd (fold_left gather_eq eqs (F, S)))
                           (S ++ gather_insts eqs)).
    { induction eqs as [ | eq eqs IHeqs ]; intros F S; simpl.
      - now rewrite app_nil_r.
      - destruct eq as [| | is ck f les | ]; simpl; try rewrite IHeqs; auto.
        unfold gather_insts.
        destruct is; rewrite IHeqs; auto;
          rewrite <-app_comm_cons, Permutation_middle; auto.
    }
    now apply Hgen.
  Qed.

  Lemma gather_eqs_inst_var_defined:
    forall eqs,
      Permutation (map fst (snd (gather_eqs eqs)) ++ gather_app_vars eqs)
                  (vars_defined (filter is_app eqs)).
  Proof.
    intro eqs.
    rewrite gather_eqs_inst.
    induction eqs as [|[] eqs]; simpl; auto.
    cases; simpl; auto.
    constructor. now rewrite Permutation_swap, IHeqs.
  Qed.

  Lemma gather_eqs_last_defined:
    forall eqs,
      Permutation (map fst (fst (fst (gather_eqs eqs)))) (lasts_defined eqs).
  Proof.
    intros. rewrite gather_eqs_last_flat_map.
    induction eqs as [|eq eqs]; simpl; auto.
    rewrite map_app, IHeqs. apply Permutation_app_tail.
    unfold gather_eq, last_defined.
    cases; simpl; auto.
  Qed.

  Lemma gather_eqs_next_defined:
    forall eqs,
      Permutation (map fst (snd (fst (gather_eqs eqs)))) (vars_defined (filter is_fby eqs)).
  Proof.
    intros. rewrite gather_eqs_next_flat_map.
    induction eqs as [|eq eqs]; simpl; auto.
    rewrite map_app, IHeqs.
    destruct eq; simpl; auto.
    cases; simpl; auto.
  Qed.

  Lemma In_snd_fold_left_gather_eq:
    forall eqs xf mems insts,
      In xf (snd (fold_left gather_eq eqs (mems, insts))) <->
      In xf insts \/ In xf (snd (fold_left gather_eq eqs (mems, []))).
  Proof.
    induction eqs as [|[]]; simpl; intros; auto.
    - split; auto; intros [|]; auto; contradiction.
    - destruct l; simpl in *; auto.
      rewrite IHeqs; symmetry; rewrite IHeqs.
      split; intros [Hin|Hin']; auto.
      + now left; right.
      + destruct Hin' as [[|]|]; auto; try contradiction.
        now left; left.
      + destruct Hin; auto.
        now right; left; left.
  Qed.

  Lemma translate_eqn_variables env : forall eqs,
      (forall x, Env.In x env ->
            ~In x (vars_defined (filter is_def_rhs [eqs]))
            /\ ~In x (vars_defined (filter is_app [eqs]))) ->
      SynStc.variables (translate_eqn env eqs)
      = filter (notb (fun x => (Env.mem x env))) (vars_defined (filter (notb is_fby) [eqs])).
  Proof.
    intros * Env. unfold notb.
    destruct eqs; simpl in *.
    - cases_eqn Eq; simpl in *.
      + exfalso. edestruct Env as (?&?); eauto using Env.mem_2.
      + exfalso. rewrite Env.mem_find, Eq2 in Eq1. congruence.
      + exfalso. rewrite Env.mem_find, Eq2 in Eq1. congruence.
    - induction l; simpl; auto.
    - rewrite filter_idem.
      2:{ simpl_Forall. apply Bool.negb_true_iff, Env.Props.P.F.not_mem_in_iff.
          intros EnvIn. edestruct Env as (?&?); eauto. }
      cases. induction l1; simpl; auto.
    - induction l; auto.
  Qed.

  Lemma translate_eqns_variables env : forall eqs,
      (forall x, Env.In x env ->
            ~In x (vars_defined (filter is_def_rhs eqs))
            /\ ~In x (vars_defined (filter is_app eqs))) ->
      SynStc.variables (translate_eqns env eqs)
      = filter (notb (fun x => (Env.mem x env))) (vars_defined (filter (notb is_fby) eqs)).
  Proof.
    intros * Env. unfold notb.
    induction eqs; simpl; auto.
    rewrite SynStc.variables_app, translate_eqn_variables, IHeqs; simpl.
    - unfold notb. cases. rewrite app_nil_r, filter_app; auto.
    - intros. edestruct Env as (Nin1&Nin2); eauto. simpl in *.
      split; cases; simpl in *; auto with datatypes.
    - intros. edestruct Env as (Nin1&Nin2); eauto. simpl in *.
      split; cases; simpl in *; rewrite app_nil_r; auto with datatypes.
  Qed.

  Lemma translate_eqn_last env : forall eqs,
      SynStc.lasts_of (translate_eqn env eqs)
      = map_filter (fun eq => match eq with
                           | EqDef x _ (Ecexp e) =>
                               if Env.mem x env then Some (x, typeofc e) else None
                           | _ => None
                           end) [eqs].
  Proof.
    intros.
    destruct eqs; simpl in *.
    - cases_eqn Eq; simpl in *.
      + exfalso. rewrite Env.mem_find, Eq0 in Eq2. congruence.
      + exfalso. rewrite Env.mem_find, Eq0 in Eq2. congruence.
    - induction l; simpl; auto.
    - cases. simpl. induction l1; auto.
    - induction l; auto.
  Qed.

  Lemma translate_eqns_last env : forall eqs,
      SynStc.lasts_of (translate_eqns env eqs)
      = map_filter (fun eq => match eq with
                           | EqDef x _ (Ecexp e) =>
                               if (Env.mem x env) then Some (x, typeofc e) else None
                           | _ => None
                           end) eqs.
  Proof.
    induction eqs; simpl; auto.
    rewrite SynStc.lasts_of_app, translate_eqn_last, IHeqs; simpl.
    cases; auto.
  Qed.

  Lemma translate_eqn_next env : forall eqs x,
      SynStc.Is_update_next_in x (translate_eqn env eqs) <-> Is_fby_in_eq x eqs.
  Proof.
    unfold SynStc.Is_update_next_in.
    intros *. destruct eqs; (split; [intros Ex|intros Fby; inv Fby]); simpl in *.
    - cases; simpl_Exists; destruct Hin; subst; inv Ex; now exfalso.
    - simpl_Exists. inv Ex.
    - cases. simpl_Exists. destruct Hin; subst; [inv Ex|]. simpl_In. inv Ex.
    - simpl_Exists. destruct Hin; subst; [inv Ex; constructor|]. simpl_In. inv Ex.
    - left. constructor.
  Qed.

  Corollary translate_eqns_next env : forall eqs x,
      SynStc.Is_update_next_in x (translate_eqns env eqs) <-> Is_fby_in x eqs.
  Proof.
    intros *.
    unfold SynStc.Is_update_next_in, Is_fby_in, translate_eqns.
    rewrite Exists_flat_map.
    apply Exists_Exists_iff; eauto using translate_eqn_next.
  Qed.

  Lemma translate_eqn_reset_state env : forall eqs x ck,
      SynStc.Is_reset_state_in x ck (translate_eqn env eqs) -> Is_fby_in_eq x eqs \/ Is_last_in_eq x eqs.
  Proof.
    unfold SynStc.Is_reset_state_in.
    intros * Ex. destruct eqs; simpl in *.
    - cases; simpl_Exists; destruct Hin; subst; inv Ex; now exfalso.
    - simpl_Exists. inv Ex. right. constructor.
    - cases. simpl_Exists. destruct Hin; subst; [inv Ex|]. simpl_In. inv Ex.
    - simpl_Exists. destruct Hin; subst; [inv Ex; constructor|]. simpl_In. inv Ex.
      left. constructor.
  Qed.

  Corollary translate_eqns_reset_state env : forall eqs x ck,
      SynStc.Is_reset_state_in x ck (translate_eqns env eqs) -> Is_fby_in x eqs \/ Is_last_in x eqs.
  Proof.
    intros * Res.
    unfold Is_fby_in, Is_last_in, translate_eqns in *.
    apply Exists_or_inv. apply Exists_flat_map in Res.
    eapply Exists_impl; [|eauto]; intros; simpl in *; eauto using translate_eqn_reset_state.
  Qed.

  Lemma translate_eqn_inst env : forall eqs x,
      SynStc.Is_update_inst_in x (translate_eqn env eqs) -> In x (vars_defined (filter is_app [eqs])).
  Proof.
    unfold SynStc.Is_update_inst_in.
    intros * Ex. destruct eqs; simpl in *.
    - cases; simpl_Exists; destruct Hin; subst; inv Ex; now exfalso.
    - simpl_Exists. inv Ex.
    - cases. simpl_Exists. destruct Hin; subst; [inv Ex|]; auto. simpl_In. inv Ex.
    - simpl_Exists. destruct Hin; subst; [inv Ex; constructor|]. simpl_In. inv Ex.
  Qed.

  Corollary translate_eqns_inst env : forall eqs x,
      SynStc.Is_update_inst_in x (translate_eqns env eqs) -> In x (vars_defined (filter is_app eqs)).
  Proof.
    intros * Upd.
    unfold SynStc.Is_update_inst_in, Is_fby_in, translate_eqns.
    apply Exists_flat_map, Exists_exists in Upd as (?&?&Ex).
    eapply translate_eqn_inst in Ex.
    unfold vars_defined in *; simpl in *.
    cases_eqn Eq; simpl in *. solve_In.
  Qed.

  Lemma translate_eqn_reset_inst env : forall eqs x ck,
      SynStc.Is_reset_inst_in x ck (translate_eqn env eqs) -> In x (vars_defined (filter is_app [eqs])).
  Proof.
    unfold SynStc.Is_reset_inst_in.
    intros * Ex. destruct eqs; simpl in *.
    - cases; simpl_Exists; destruct Hin; subst; inv Ex; now exfalso.
    - simpl_Exists. inv Ex.
    - cases. simpl_Exists. destruct Hin; subst; [inv Ex|]. simpl_In. inv Ex; auto.
    - simpl_Exists. destruct Hin; subst; [inv Ex; constructor|]. simpl_In. inv Ex.
  Qed.

  Corollary translate_eqns_reset_inst env : forall eqs x ck,
      SynStc.Is_reset_inst_in x ck (translate_eqns env eqs) -> In x (vars_defined (filter is_app eqs)).
  Proof.
    intros * Res.
    apply Exists_flat_map, Exists_exists in Res as (?&?&Res). eapply translate_eqn_reset_inst in Res.
    unfold vars_defined in *; simpl in *.
    cases_eqn Eq; simpl in *. solve_In.
  Qed.

  (** *** Full node *)

  Program Definition translate_node (n: node) : @SynStc.system (PSP.of_list lustre_prefs) :=
    let gathered := gather_eqs n.(n_eqs) in
    let lasts := fst (fst gathered) in
    let nexts := snd (fst gathered) in
    let lastsenv := Env.from_list (List.map (fun xr => (fst xr, snd (snd xr))) lasts) in
    let tcs := translate_eqns lastsenv n.(n_eqs) in
    let subs := snd gathered in
    let mems := ps_from_list (map fst lasts ++ map fst nexts) in
    let vars := filter (notb (fun x => PS.mem (fst x) mems)) n.(n_vars) in
    {| SynStc.s_name  := n.(n_name);
       SynStc.s_subs  := subs;
       SynStc.s_in    := n.(n_in);
       SynStc.s_vars  := idfst vars;
       SynStc.s_lasts := idfst lasts;
       SynStc.s_nexts := nexts;
       SynStc.s_out   := n.(n_out);
       SynStc.s_tcs   := tcs;
    |}.
  Next Obligation. apply n_ingt0. Qed.
  Next Obligation.
    pose proof (n_nodup n) as ND.
    rewrite ? map_app, ? map_fst_idfst.
    eapply Permutation_NoDup, n_nodup.
    rewrite gather_eqs_last_defined, gather_eqs_next_defined.
    apply Permutation_app_head. rewrite Permutation_swap, Permutation_app_comm. apply Permutation_app_head.
    erewrite <-filter_notb_app with (xs:=n_vars _) at 1. rewrite ? map_app.
    apply Permutation_app_head.
    eapply NoDup_Permutation.
    - apply fst_NoDupMembers, NoDupMembers_filter, fst_NoDupMembers.
      eauto using NoDup_app_l, NoDup_app_r.
    - apply NoDup_app'; auto using NoDup_last_defined_n_eqs, NoDup_var_defined_fby.
      simpl_Forall. eapply n_lastfby; eauto.
    - unfold notb. split; intros * In.
      + simpl_In. apply Bool.negb_true_iff, Bool.negb_false_iff, ps_from_list_In in Hf.
        now rewrite gather_eqs_last_defined, gather_eqs_next_defined in Hf.
      + assert (List.In x (map fst (n_vars n))) as In'.
        { apply in_app_iff in In as [In|In].
          - rewrite n_lastd1 in In. solve_In.
          - apply vars_defined_fby_vars in In; auto. }
        solve_In.
        apply Bool.negb_true_iff, Bool.negb_false_iff, ps_from_list_In.
        now rewrite gather_eqs_last_defined, gather_eqs_next_defined.
  Qed.
  Next Obligation.
    rewrite ? map_fst_idfst, gather_eqs_last_defined, gather_eqs_next_defined.
    apply NoDup_app'; [|apply NoDup_app'|]; auto using NoDup_last_defined_n_eqs, NoDup_var_defined_fby.
    - pose proof (NoDup_var_defined_app n) as ND.
      rewrite <-gather_eqs_inst_var_defined in ND. eauto using NoDup_app_l.
    - simpl_Forall. intros contra.
      pose proof (NoDup_var_defined_n_eqs n) as ND. rewrite <-is_filtered_vars_defined in ND.
      eapply NoDup_app_r, NoDup_app_In in ND; eauto.
      rewrite <-gather_eqs_inst_var_defined; auto using in_or_app.
    - simpl_Forall. rewrite in_app_iff, not_or'.
      split; auto using n_lastfby.
      intros contra.
      pose proof (NoDup_var_defined_n_eqs n) as ND. rewrite <-is_filtered_vars_defined in ND.
      eapply n_lastapp; eauto.
      rewrite <-gather_eqs_inst_var_defined; auto using in_or_app.
  Qed.
  Next Obligation.
    pose proof (n_nodup n) as ND.
    rewrite map_fst_idfst.
    rewrite translate_eqns_variables.
    2:{ intros * In. rewrite Env.In_from_list, fst_InMembers, map_map, gather_eqs_last_defined in In.
        split; eauto using n_lastapp, n_lastrhs. }
    apply NoDup_Permutation.
    - eapply NoDup_app'; eauto using NoDup_app_l, NoDup_app_r.
      + apply fst_NoDupMembers, NoDupMembers_filter, fst_NoDupMembers.
        eauto using NoDup_app_l, NoDup_app_r.
      + simpl_Forall. intros ?.
        eapply NoDup_app_r, NoDup_app_In in ND; eauto. solve_In.
    - apply NoDup_filter.
      pose proof (NoDup_var_defined_n_eqs n) as ND1. unfold vars_defined in *.
      rewrite <-filter_notb_app with (xs:=n_eqs _), flat_map_app in ND1.
      eauto using NoDup_app_r.
    - intros. rewrite in_app_iff.
      split; [intros [|]|intros]; simpl_In.
      + apply Bool.negb_true_iff, PSE.mem_4 in Hf.
        rewrite ps_from_list_In, gather_eqs_last_defined, gather_eqs_next_defined, in_app_iff in Hf.
        apply not_or' in Hf as (N1&N2).
        solve_In.
        * assert (In x (vars_defined (n_eqs n))) as Def.
          { rewrite n_defd, in_app_iff. left. solve_In. }
          unfold vars_defined in *.
          erewrite <-filter_notb_app with (xs:=n_eqs _), flat_map_app, in_app_iff in Def.
          destruct Def; [|eauto]. contradiction.
        * apply Bool.negb_true_iff, Env.Props.P.F.not_mem_in_iff.
          rewrite Env.In_from_list, fst_InMembers, map_map, gather_eqs_last_defined. auto.
      + solve_In.
        * assert (In x (vars_defined (n_eqs n))) as Def.
          { rewrite n_defd, in_app_iff. right. solve_In. }
          unfold vars_defined in *.
          erewrite <-filter_notb_app with (xs:=n_eqs _), flat_map_app, in_app_iff in Def.
          destruct Def; [|eauto]. exfalso.
          eapply n_vout; eauto. solve_In.
        * apply Bool.negb_true_iff, Env.Props.P.F.not_mem_in_iff.
          rewrite Env.In_from_list, fst_InMembers, map_map, gather_eqs_last_defined.
          rewrite n_lastd1. intros In. simpl_In.
          eapply NoDup_app_r, NoDup_app_In in ND. eapply ND. 1,2:solve_In.
      + apply Bool.negb_true_iff, Env.Props.P.F.not_mem_in_iff in Hf.
        rewrite Env.In_from_list, fst_InMembers, map_map, gather_eqs_last_defined in Hf.
        assert (In x (vars_defined (n_eqs n))) as Def.
        { unfold vars_defined in *. solve_In. }
        rewrite n_defd, in_app_iff in Def. destruct Def; auto.
        left. solve_In.
        apply Bool.negb_true_iff, PSE.mem_3.
        rewrite ps_from_list_In, gather_eqs_last_defined, gather_eqs_next_defined, not_In_app.
        split; auto. intros contra.
        pose proof (NoDup_var_defined_n_eqs n) as ND1. unfold vars_defined in *.
        erewrite <-filter_notb_app with (xs:=n_eqs _), flat_map_app in ND1.
        eapply NoDup_app_In in ND1; eauto.
  Qed.
  Next Obligation.
    rewrite map_fst_idfst, translate_eqns_last, gather_eqs_last_defined.
    remember (Env.from_list _) as env.
    assert (forall x ckrs,
               (exists ty ck c0, In (EqLast x ty ck c0 ckrs) (n_eqs n)) <->
               Env.find x env = Some ckrs) as Env.
    { subst. split; intros * In.
      - apply Env.find_In_from_list.
        + rewrite gather_eqs_last_flat_map. solve_In. auto.
        + rewrite fst_NoDupMembers, map_map, gather_eqs_last_defined.
          apply NoDup_last_defined_n_eqs.
      - apply Env.from_list_find_In in In.
        rewrite gather_eqs_last_flat_map in In. simpl_In.
        unfold gather_eq in *. cases. simpl in *.
        destruct Hinf as [Eq|Eq]; inv Eq. eauto.
    }
    clear Heqenv.

    eapply NoDup_Permutation; eauto using NoDup_last_defined_n_eqs.
    - apply fst_NoDupMembers.
      pose proof (NoDup_var_defined_n_eqs n) as ND. clear Env.
      induction (n_eqs n); simpl in *; [constructor|].
      destruct a as [?? []| | |]; eauto using NoDup_app_r. inv ND.
      destruct (Env.mem _ _); auto. constructor; eauto using NoDup_app_r.
      contradict H1. unfold vars_defined. solve_In.
      destruct x as [?? []| | |]; simpl in *; try congruence.
      cases; auto.
    - intros. split; intros In.
      + assert (L:=In). rewrite n_lastd1 in In. simpl_In.
        apply n_lastd2 in Hin0. unfold vars_defined in Hin0. simpl_In.
        destruct x0 as [?? []| | |]; simpl in *; try congruence.
        destruct Hinf; [|now exfalso]; subst.
        solve_In.
        2:{ unfold lasts_defined in *. simpl_In.
            destruct x0; simpl in *; try now exfalso.
            destruct Hinf as [|]; [|now exfalso]; subst; eauto.
            edestruct Env as (Env1&_); eauto.
            erewrite Env.mem_find, Env1; eauto. }
        simpl; auto.
      + simpl_In. cases_eqn Eq; subst; auto. inv Hf.
        rewrite Env.mem_find in Eq1. cases_eqn Eq.
        apply Env in Eq as (?&?&?&In).
        unfold lasts_defined. clear - In. solve_In. simpl; auto.
  Qed.
  Next Obligation.
    intros ?? LR.
    unfold SynStc.Last_with_reset_in, translate_eqns in *.
    simpl_Exists. simpl_In.
    destruct x0; simpl in *.
    2:{ simpl_In. inv LR. }
    2:{ cases. inv Hinf; simpl_In; inv LR. }
    2:{ destruct Hinf; subst; simpl_In; inv LR. }
    cases_eqn Eq; apply In_singleton in Hinf; subst; inv LR.
    apply Env.from_list_find_In in Eq0. rewrite gather_eqs_last_flat_map in Eq0.
    simpl_In.
    unfold gather_eq in *. cases. destruct Hinf as [Hinf|Hinf]; inv Hinf.
    intros; split; intros In; simpl_In.
    - apply Exists_exists; do 2 esplit. solve_In. simpl. solve_In.
      constructor.
    - apply Exists_exists in In as (?&?&R). simpl_In.
      destruct x0; simpl in *.
      + cases; apply In_singleton in Hinf; subst; inv R.
      + simpl_In. inv R.
        assert (l = l0); subst; [|solve_In].
        pose proof (NoDup_last_defined_n_eqs n) as ND. unfold lasts_defined in ND.
        clear - Hin1 Hin ND.
        induction (n_eqs n); inv Hin1; inv Hin; simpl in *.
        * now inv H.
        * exfalso. eapply NoDup_cons'; eauto. solve_In. simpl; auto.
        * exfalso. eapply NoDup_cons'; eauto. solve_In. simpl; auto.
        * eauto using NoDup_app_r.
      + cases. inv Hinf; simpl_In; inv R.
      + destruct Hinf; subst; simpl_In; inv R. exfalso.
        pose proof (n_lastfby n) as ND.
        eapply ND; unfold lasts_defined, vars_defined.
        * clear Hin. solve_In. simpl; auto.
        * clear Hin1. solve_In. simpl; auto.
  Qed.
  Next Obligation.
    rewrite gather_eqs_next_defined.
    remember (Env.from_list _) as env. clear Heqenv.
    induction (n_eqs n) as [|[]]; simpl; auto.
    - cases; auto.
    - induction l; auto.
    - cases. induction l1; auto.
    - constructor. induction l; auto.
  Qed.
  Next Obligation.
    remember (Env.from_list _) as env. clear Heqenv.
    pose proof (NoDup_var_defined_fby n) as NDFby.
    pose proof (fby_last_NoDup n) as ND.
    intros ?? Next ?.
    induction (n_eqs n); simpl in *. inv Next.
    unfold SynStc.Is_reset_state_in. rewrite Exists_app.
    apply Exists_app in Next as [|Ex].
    - clear IHl. rewrite or_not_right.
      2:{ intros In.
          apply SynStc.Next_with_reset_in_Is_update_next_in, translate_eqn_next in H. inv H; simpl in *.
          apply translate_eqns_reset_state in In as [Fby|Last].
          + apply Is_fby_in_vars_defined in Fby. inv NDFby; auto.
          + eapply ND; [right|left]; eauto. constructor.
      }
      destruct a; simpl_Exists.
      + cases; simpl_Exists; take (_ \/ _) and destruct it; subst; inv H; now exfalso.
      + simpl_In. inv H.
      + cases. inv Hin; [inv H|]. simpl_In. inv H.
      + rewrite Exists_cons, or_not_left.
        destruct Hin; subst.
        * inv H. split; [intros; simpl_In; solve_Exists; constructor
                        |intros; simpl_Exists; inv H; solve_In].
        * simpl_In. inv H.
        * intros * Res. inv Res.
    - rewrite or_not_left; auto.
      2:{ clear - NDFby ND Ex. intros In.
          apply SynStc.Next_with_reset_in_Is_update_next_in, translate_eqns_next, Is_fby_in_vars_defined in Ex.
          apply translate_eqn_reset_state in In as [Fby|Last].
          + inv Fby. simpl in *. inv NDFby; eauto.
          + eapply ND; [left|right]; eauto.
            apply Is_fby_in_vars_defined; auto.
      }
      apply IHl; auto.
      + cases; eauto using NoDup_app_r.
      + intros * L1 F. eapply ND; right; eauto.
  Qed.
  Next Obligation.
    remember (Env.from_list _) as env.
    assert (forall x ty ck c0 ckrs,
               In (EqLast x ty ck c0 ckrs) (n_eqs n) ->
               Env.find x env = Some ckrs) as Env.
    { subst. intros * In.
      apply Env.find_In_from_list.
      - rewrite gather_eqs_last_flat_map. solve_In. auto.
      - rewrite fst_NoDupMembers, map_map, gather_eqs_last_defined.
        apply NoDup_last_defined_n_eqs.
    }
    clear Heqenv.
    intros ? In. rewrite map_app, in_app_iff.
    apply SynStc.reset_states_of_In in In as (?&Res).
    rewrite <-SynStc.lasts_of_In, <-SynStc.nexts_of_In.
    unfold SynStc.Is_reset_state_in, SynStc.Is_update_last_in, SynStc.Is_update_next_in in *.
    rewrite Exists_or_iff. unfold translate_eqns in *.
    simpl_Exists. simpl_In.
    destruct x1; simpl in *.
    - cases; simpl_In; apply In_singleton in Hinf; subst; inv Res.
    - simpl_In. inv Res.
      assert (In i (lasts_defined (n_eqs n))) as Last.
      { unfold lasts_defined. solve_In. simpl. auto. }
      rewrite n_lastd1 in Last. simpl_In.
      apply n_lastd2 in Hin2. unfold vars_defined in Hin2. simpl_In.
      destruct x; simpl in *; try congruence. destruct r; simpl in *; try congruence.
      destruct Hinf; subst; try now exfalso.
      solve_Exists; [|left; constructor].
      solve_In. simpl. erewrite Env; eauto with datatypes.
    - cases. inv Hinf; [|simpl_In]; inv Res.
    - inv Hinf; [|simpl_In]; inv Res.
      solve_Exists. solve_In. simpl; eauto.
      right; constructor.
  Qed.
  Next Obligation.
    remember (Env.from_list _) as env. clear Heqenv.
    rewrite gather_eqs_inst, map_app, in_app_iff.
    split; [intros In|intros []];
      induction (n_eqs n) as [|]; simpl in *; eauto.
    all:rewrite ? SynStc.insts_of_app, ? SynStc.inst_resets_of_app, ? map_app, ? in_app_iff in *.
    - destruct In; [clear IHl|edestruct IHl; eauto].
      destruct a; simpl in *.
      + cases.
      + induction l0; auto.
      + cases; simpl in *; inv H; subst; auto. now exfalso.
      + induction l0; simpl in *; auto.
    - destruct H; auto; clear IHl.
      destruct a; simpl in *.
      + cases.
      + induction l0; auto.
      + cases; inv H; simpl; auto with datatypes.
        induction l2; simpl in *; auto.
      + induction l0; simpl in *; auto.
    - destruct H; auto; clear IHl.
      destruct a; simpl in *.
      + cases.
      + induction l0; auto.
      + cases. simpl in *.
        induction l2; simpl in *; inv H; auto.
      + induction l0; simpl in *; auto.
  Qed.
  Next Obligation.
    remember (Env.from_list _) as env. clear Heqenv.
    rewrite  gather_eqs_inst_flat_map.
    induction (n_eqs n) as [|[]]; simpl; auto.
    - cases; auto.
    - induction l; auto.
    - cases. constructor. induction l1; auto.
    - induction l; auto.
  Qed.
  Next Obligation.
    remember (Env.from_list _) as env. clear Heqenv.
    pose proof (NoDup_var_defined_app n) as ND.
    intros ?? Inst ?.
    induction (n_eqs n); simpl in *. inv Inst.
    unfold SynStc.Is_reset_inst_in. rewrite Exists_app.
    apply Exists_app in Inst as [|Ex].
    - clear IHl. rewrite or_not_right.
      2:{ intros In.
          apply SynStc.Inst_with_reset_in_Is_update_inst_in, translate_eqn_inst in H.
          apply translate_eqns_reset_inst in In. simpl in *.
          cases. simpl in *. rewrite app_nil_r in *.
          eapply NoDup_app_In in ND; eauto.
      }
      destruct a; simpl_Exists.
      + cases; simpl_Exists; take (_ \/ _) and destruct it; subst; inv H; now exfalso.
      + simpl_In. inv H.
      + cases. rewrite Exists_cons, or_not_left.
        destruct Hin; subst.
        * inv H. split; [intros; simpl_In; solve_Exists; constructor
                        |intros; simpl_Exists; inv H; solve_In].
        * simpl_In. inv H.
        * intros * Res. inv Res.
      + cases. inv Hin; [inv H|]. simpl_In. inv H.
    - rewrite or_not_left; auto.
      2:{ clear - ND Ex. intros In.
          apply SynStc.Inst_with_reset_in_Is_update_inst_in, translate_eqns_inst in Ex.
          apply translate_eqn_reset_inst in In. simpl in *.
          cases. simpl in *. rewrite app_nil_r in *.
          eapply NoDup_app_In in ND; eauto.
      }
      apply IHl; auto.
      + cases; eauto using NoDup_app_r.
  Qed.
  Next Obligation.
    remember (Env.from_list _) as env; clear Heqenv.
    induction (n_eqs) as [|[]]; simpl; auto.
    - reflexivity.
    - cases; simpl; auto.
    - induction l; auto.
    - cases. induction l1; simpl in *; auto using incl_tl, incl_cons with datatypes.
    - induction l; auto.
  Qed.
  Next Obligation.
    pose proof (n_good n) as (Good1&Good2).
    assert (Forall (AtomOrGensym (PSP.of_list lustre_prefs)) (vars_defined (n_eqs n))) as Good3.
    { rewrite n_defd. apply Forall_app in Good1 as (?&?); auto. }
    rewrite <-is_filtered_vars_defined in Good3.
    rewrite ? map_app, ? map_fst_idfst. rewrite gather_eqs_last_defined, gather_eqs_next_defined.
    rewrite ? Forall_app in *. destruct Good1 as (G1&G2&G3). destruct Good3 as (G4&G5&G6).
    repeat split; auto.
    - simpl_Forall. simpl_In. simpl_Forall. auto.
    - eapply Forall_incl; [eapply G2|].
      rewrite n_lastd1. intros ??. solve_In.
    - eapply Forall_incl; [eapply G5|].
      rewrite <-gather_eqs_inst_var_defined. apply incl_appl, incl_refl.
  Qed.

  Global Program Instance translate_node_transform_unit: TransformUnit node SynStc.system :=
    { transform_unit := translate_node }.

  Global Program Instance global_program_without_units : TransformProgramWithoutUnits global (@SynStc.program (PSP.of_list lustre_prefs)) :=
    { transform_program_without_units := fun g => SynStc.Program g.(types) g.(externs) [] }.

  Definition translate : global -> SynStc.program := transform_units.

End TRANSLATION.

Module TranslationFun
       (Ids    : IDS)
       (Op     : OPERATORS)
       (OpAux  : OPERATORS_AUX Ids Op)
       (Cks    : CLOCKS    Ids Op OpAux)
       (CESyn  : CESYNTAX  Ids Op OpAux Cks)
       (SynNL  : NLSYNTAX  Ids Op OpAux Cks CESyn)
       (SynStc : STCSYNTAX Ids Op OpAux Cks CESyn)
       (Mem    : MEMORIES  Ids Op OpAux Cks CESyn SynNL)
<: TRANSLATION Ids Op OpAux Cks CESyn SynNL SynStc Mem.
  Include TRANSLATION Ids Op OpAux Cks CESyn SynNL SynStc Mem.
End TranslationFun.
