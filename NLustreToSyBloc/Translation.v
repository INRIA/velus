Require Import Coq.FSets.FMapPositive.
Require Import PArith.
Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.Clocks.
Require Import Velus.NLustre.NLExprSyntax.
Require Import Velus.NLustre.NLSyntax.
Require Import Velus.NLustre.Memories.
Require Import Velus.SyBloc.SBSyntax.
Require Velus.Environment.

Require Import List.
Import List.ListNotations.
Require Import Coq.Sorting.Permutation.
Require Import Morphisms.

Open Scope positive.
Open Scope list.

(** * Translation *)

Module Type TRANSLATION
       (Import Ids     : IDS)
       (Import Op      : OPERATORS)
       (Import Clks    : CLOCKS   Ids)
       (Import ExprSyn : NLEXPRSYNTAX Op)
       (Import SynNL   : NLSYNTAX Ids Op Clks ExprSyn)
       (SynSB          : SBSYNTAX Ids Op Clks ExprSyn)
       (Import Mem     : MEMORIES Ids Op Clks ExprSyn SynNL).

  Definition gather_eq (acc: list (ident * const) * list (ident * ident)) (eq: equation):
    list (ident * const) * list (ident * ident) :=
    match eq with
    | EqDef _ _ _ => acc
    | EqApp [] _ _ _ _ => acc
    | EqApp (x :: _) _ f _ _ => (fst acc, (x, f) :: snd acc)
    | EqFby x _ c0 _ => ((x, c0) :: fst acc, snd acc)
    end.

  Definition gather_eqs (eqs: list equation) : list (ident * const) * list (ident * ident) :=
    fold_left gather_eq eqs ([], []).


  (** ** Translation *)

  Definition translate_eqn (eqn: equation) : list SynSB.equation :=
    match eqn with
    | EqDef x ck e =>
      [ SynSB.EqDef x ck e ]
    | EqApp [] _ _ _ _ =>
      []                        (* This way we can ensure b_blocks_in_eqs *)
    | EqApp (x :: xs) ck f les None =>
      [ SynSB.EqCall x (x :: xs) ck false f les ]
    | EqApp (x :: xs) ck f les (Some r) =>
      [ SynSB.EqReset x (Con ck r true) f;
          SynSB.EqCall x (x :: xs) ck true f les ]
    | EqFby x ck _ e =>
      [ SynSB.EqNext x ck e ]
    end.

  (*   (** Remark: eqns ordered in reverse order of execution for coherence with *)
  (*      [Is_well_sch]. *) *)

  Definition translate_eqns (eqns: list equation) : list SynSB.equation :=
    concatMap translate_eqn eqns.

  Definition ps_from_list (l: idents) : PS.t :=
    fold_left (fun s i => PS.add i s) l PS.empty.

  Hint Constructors NoDupMembers.

  (** Properties of translation functions *)

  Instance eq_equiv : Equivalence PS.eq.
  Proof. firstorder. Qed.

  Instance List_fold_left_add_Proper (xs: idents) :
    Proper (PS.eq ==> PS.eq)
           (fold_left (fun s i => PS.add i s) xs).
  Proof.
    induction xs as [|x xs IH]; intros S S' Heq; [exact Heq|].
    assert (PS.eq (PS.add x S) (PS.add x S')) as Heq'
        by (rewrite Heq; reflexivity).
    simpl; rewrite Heq'; reflexivity.
  Qed.

  Instance List_fold_left_memory_eq_Proper (eqs: list equation) :
    Proper (PS.eq ==> PS.eq)
           (fold_left memory_eq eqs).
  Proof.
    induction eqs as [|eq eqs IH]; intros S S' Heq; [exact Heq|].
    simpl.
    apply IH.
    destruct eq; [apply Heq|apply Heq|].
    simpl; rewrite Heq; reflexivity.
  Qed.

  Lemma add_ps_from_list_cons:
    forall xs x, PS.eq (PS.add x (ps_from_list xs))
                  (ps_from_list (x::xs)).
  Proof.
    intros; unfold ps_from_list; simpl.
    generalize PS.empty as S.
    induction xs as [|y xs IH]; [ reflexivity | ].
    intro S; simpl; rewrite IH; rewrite PSP.add_add; reflexivity.
  Qed.

  Lemma ps_from_list_gather_eqs_memories:
    forall eqs, PS.eq (ps_from_list (map fst (fst (gather_eqs eqs)))) (memories eqs).
  Proof.
    induction eqs as [|eq eqs IH]; [reflexivity|].
    unfold memories, gather_eqs.
    assert (forall eqs F S,
               PS.eq (ps_from_list (map fst (fst (fold_left gather_eq eqs (F, S)))))
                     (fold_left memory_eq eqs (ps_from_list (map fst F)))) as HH.
    {
      clear eq eqs IH; induction eqs as [|eq eqs IH]; [reflexivity|].
      intros F S.
      destruct eq;
        [ now apply IH
        | now destruct i; apply IH
        | ].
      simpl; rewrite IH; rewrite add_ps_from_list_cons; reflexivity.
    }
    rewrite HH; reflexivity.
  Qed.

  Lemma filter_mem_fst:
    forall p (xs: list (ident * (type * clock))),
      map fst (filter (fun (x:ident*(type*clock)) => PS.mem (fst x) p) xs)
      = filter (fun x => PS.mem x p) (map fst xs).
  Proof.
    induction xs as [|x xs]; auto.
    simpl.
    destruct (PS.mem (fst x) p); simpl;
      now rewrite IHxs.
  Qed.

  Lemma in_memories_var_defined:
    forall x eqs,
      PS.In x (memories eqs) ->
      In x (vars_defined eqs).
  Proof.
    intros x eqs Hin.
    induction eqs as [|eq eqs].
    now apply PSF.empty_iff in Hin.
    unfold memories in *. simpl in *.
    apply In_fold_left_memory_eq in Hin.
    destruct Hin as [Hin|Hin].
    - specialize (IHeqs Hin); apply in_app; now right.
    - destruct eq; simpl in Hin;
        try (apply PSF.empty_iff in Hin; contradiction).
      apply PS.add_spec in Hin.
      destruct Hin as [Hin|Hin].
      now subst; simpl; left.
      now apply PSF.empty_iff in Hin.
  Qed.

  Lemma in_memories_is_fby:
    forall eqs eq,
      In eq eqs ->
      NoDup (vars_defined eqs) ->
      forall x, In x (var_defined eq) ->
      PS.mem x (memories eqs) = is_fby eq.
  Proof.
    induction eqs as [|eq eqs].
    - (* Case: eqs ~ [] *)
      now intuition.
    - (* Case: eqs ~ eq' :: eqs *)
      intros eq' Hin Hndup.
      simpl in Hndup.

      assert (  NoDup (var_defined eq)
                /\ NoDup (vars_defined eqs)
                /\ Forall (fun x => ~In x (vars_defined eqs)) (var_defined eq))
        as (Hndup_eq & Hndup_eqs & Hndup_def)
        by now apply NoDup_app'_iff.
      clear Hndup.

      unfold memories.
      destruct Hin as [|Hin]; intros x ?.
      + (* Case: eq' = eq *)
        subst eq'.

        assert (PS.mem x (fold_left memory_eq eqs PS.empty) = false).
        {
          apply mem_spec_false; intro.
          eapply Forall_forall in Hndup_def; eauto.
          eapply Hndup_def; eauto.
          now apply in_memories_var_defined.
        }

        destruct eq; simpl in *; auto.
        apply In_fold_left_memory_eq.
        right. apply PS.add_spec. now intuition.
      + (* Case: In eq' eqs *)
        assert (IHrec: PS.mem x (memories eqs) = is_fby eq')
          by now apply IHeqs.
        rewrite <- IHrec; clear IHrec.

        destruct eq; simpl; auto.

        assert (x <> i).
        {
          intro; subst x.
          eapply Forall_forall in Hndup_def; [|simpl; eauto].
          apply Hndup_def; simpl; eauto.
          eapply in_concat'; eauto.
          now apply in_map.
        }

        assert (mem_fold_left_memory_eq:
                  PS.In x (fold_left memory_eq eqs (PS.add i PS.empty)) <->
                  PS.In x (fold_left memory_eq eqs PS.empty)).
        {
          assert (PS.In x (fold_left memory_eq eqs (PS.add i PS.empty)) <->
                  PS.In x (fold_left memory_eq eqs PS.empty) \/ PS.In x (PS.add i PS.empty))
            by apply In_fold_left_memory_eq.

          assert (PS.In x (fold_left memory_eq eqs PS.empty) \/ PS.In x (PS.add i PS.empty)
                  <-> PS.In x (fold_left memory_eq eqs PS.empty)).
          {
            split. 2: intuition.
            intros [Hin_eqs | Hin_empty]; auto.
            exfalso.
            apply PS.add_spec in Hin_empty.
            destruct Hin_empty as [|Hin_empty]; try contradiction.
            apply not_In_empty in Hin_empty. contradiction.
          }

          intuition.
        }

        assert (In_mem: forall m n, (PS.In x m <-> PS.In x n) <-> PS.mem x m = PS.mem x n).
        {
          (* XXX: isn't that already defined in PS? *)
          intros m n.
          destruct (PS.mem x n) eqn:Heq.
          - rewrite <- PS.mem_spec. intuition.
          - rewrite -> mem_spec_false.
            apply mem_spec_false in Heq. intuition.
        }

        now apply In_mem.
  Qed.


  Lemma in_memories_filter_is_fby:
    forall x eqs,
      PS.In x (memories eqs) <-> In x (vars_defined (filter is_fby eqs)).
  Proof.
    unfold memories.
    induction eqs as [|eq eqs].
    - split; intro HH; try apply not_In_empty in HH; intuition.
    - destruct eq; simpl; (try now rewrite IHeqs).
      split; intro HH.
      + apply In_fold_left_memory_eq in HH.
        destruct HH as [HH|HH].
        * right; now apply IHeqs.
        * apply PS.add_spec in HH.
          destruct HH as [HH|HH]; subst; auto.
          contradiction (not_In_empty x).
      + apply In_fold_left_memory_eq.
        destruct HH as [HH|HH].
        * rewrite PS.add_spec; intuition.
        * apply IHeqs in HH; now left.
  Qed.

  Lemma fby_In_filter_memories:
    forall eqs vars x (ty: type) ck c0 e,
      In (EqFby x ck c0 e) eqs ->
      In (x, ty) vars ->
      In (x, ty) (filter (fun x => PS.mem (fst x) (memories eqs)) vars).
  Proof.
    intros ** Heqs Hvars.
    apply filter_In. split; auto.
    apply PS.mem_spec.
    assert (In (EqFby x ck c0 e) (filter is_fby eqs)) as Heqs'
        by (apply filter_In; auto).
    assert (In (fst (x, ty)) (vars_defined (filter is_fby eqs))).
    {
      eapply in_concat'.
      2:now apply in_map; eauto.
      simpl; eauto.
    }
    now apply in_memories_filter_is_fby.
  Qed.

  Lemma not_in_memories_filter_notb_is_fby:
    forall x eqs,
      NoDup (vars_defined eqs) ->
      In x (vars_defined (filter (notb is_fby) eqs)) ->
      ~PS.In x (memories eqs).
  Proof.
    intros x eqs Hnodup HH.
    rewrite in_memories_filter_is_fby.

    induction eqs as [|eq eqs]; [intuition|].

      assert (concat_filter:
                forall f,
                  In x (vars_defined (filter f eqs)) ->
                  In x (vars_defined eqs)).
      {
        intros f Hinx.
        unfold vars_defined, concatMap in Hinx.
        apply in_concat in Hinx as (l & Hinl & Hindef).
        eapply in_concat'; eauto.
        eapply in_map_iff in Hindef as (eq' & Heq & Hineq).
        eapply filter_In in Hineq as [? _].
        now rewrite in_map_iff; eauto.
      }

    destruct eq; simpl in *; intro Hin.
    - (* Case: eq ~ EqDef *)
      inversion_clear Hnodup as [|? ? Hnin Hnodup'].
      destruct HH as [HH|HH]; [|now apply IHeqs].
      clear IHeqs Hnodup'; subst i.

      now apply Hnin, (concat_filter is_fby).

    - (* Case: eq ~ EqApp *)
      assert (    NoDup i
                /\ NoDup (vars_defined eqs)
                /\ Forall (fun x => ~In x (vars_defined eqs)) i)
        as (_ & Hnodup_eqs & Hnodup_def)
        by now apply NoDup_app'_iff.
      clear Hnodup.

      unfold vars_defined in HH;
        rewrite concatMap_cons in HH;
        apply in_app in HH as [HH | HH]; [| now apply IHeqs].

      eapply Forall_forall in Hnodup_def; eauto.

    - (* Case: eq ~ EqFby *)
      destruct Hin.
      + (* Case: i = x *)
        subst i.
        unfold vars_defined in Hnodup;
          rewrite concatMap_cons in Hnodup;
          unfold var_defined in Hnodup.
          apply NoDup_cons' in Hnodup as [Hnodup _].
        now apply Hnodup, (concat_filter (notb is_fby)).

      + (* Case: In x (concat (map var_defined (filter is_fby eqs))) *)
        eapply IHeqs; eauto.
        now unfold vars_defined in Hnodup;
          rewrite concatMap_cons in Hnodup;
          unfold var_defined in Hnodup;
          apply NoDup_cons' in Hnodup as [_ ?].
  Qed.


  Lemma fst_partition_memories_var_defined:
    forall n,
      Permutation
        (map fst (fst (partition
                         (fun x => PS.mem (fst x) (memories n.(n_eqs)))
                         n.(n_vars))))
        (vars_defined (filter is_fby n.(n_eqs))).
  Proof.
    intro n.
    match goal with |- Permutation (map fst (fst (partition ?p ?l))) _ =>
      assert (Permutation (map fst (fst (partition p l)))
                          (map fst (filter p n.(n_vars))))
        as Hperm by (apply Permutation_map_aux; apply fst_partition_filter)
    end.
    rewrite Hperm; clear Hperm.
    match goal with |- context[filter ?p ?l] =>
      rewrite <-(app_nil_r (filter p l))
    end.

    assert (NoDup (filter (fun x => PS.mem (fst x) (memories (n_eqs n))) (n_out n))).
    {
      apply NoDupMembers_NoDup, fst_NoDupMembers.
      rewrite filter_mem_fst.
      apply nodup_filter.
      pose proof (n.(n_nodup)) as Hnodup.
      do 2 apply NoDupMembers_app_r in Hnodup.
      now apply fst_NoDupMembers.
    }

    assert (filter (fun x=>PS.mem (fst x) (memories n.(n_eqs))) n.(n_out) = [])
      as Hfout.
    { simpl.
      apply Permutation_nil.
      apply NoDup_Permutation; auto using NoDup. intros x.
      split; try (now intuition); []. intro Hin.

      apply filter_In in Hin as [Hin Hmem].

      assert (In (fst x) (map fst (n_out n)))
        by now eapply in_map.

      assert (In (fst x) (vars_defined (filter is_fby (n_eqs n))))
        by now apply in_memories_filter_is_fby.

      eapply n.(n_vout); eauto.
    }

    rewrite <-Hfout; clear Hfout.
    rewrite filter_app, filter_mem_fst, <-n_defd.
    remember (memories n.(n_eqs)) as mems.
    set (P:=fun eqs eq=> In eq eqs ->
                      forall x, In x (var_defined eq) ->
                           PS.mem x mems = is_fby eq).
    assert (forall eq, P n.(n_eqs) eq) as Peq.
    { subst P mems.
      intro. intro Hin.
      apply in_memories_is_fby; auto.
      rewrite n_defd.
      apply fst_NoDupMembers.
      pose proof (n.(n_nodup)) as Hnodup.
      now apply NoDupMembers_app_r in Hnodup.
    }
    clear Heqmems.
    induction n.(n_eqs) as [|eq eqs]; auto.
    assert (forall eq, P eqs eq) as Peq'
        by (intros e Hin; apply Peq; constructor (assumption)).
    specialize (IHeqs Peq'). clear Peq'.
    destruct eq eqn:Heq; simpl;
      specialize (Peq eq); red in Peq; subst eq;
        simpl in Peq.

    + (* Case: EqDef *)
      rewrite Peq; eauto.
    + (* Case: EqApp *)
      assert (Pfilter: Permutation (filter (fun x => PS.mem x mems) i) []).
      {
        assert (Hmem_in: forall x, In x i -> PS.mem x mems = false)
          by now apply Peq; eauto.

        assert (Hfilter: filter (fun x => PS.mem x mems) i = []).
        {
          clear - Hmem_in.
          induction i as [ | a i IHi] ; auto; simpl.
          rewrite Hmem_in; try now constructor.
          apply IHi. intros.
          apply Hmem_in. constructor(assumption).
        }

        now rewrite Hfilter.
      }

      unfold vars_defined;
        rewrite concatMap_cons;
        unfold var_defined.
      now rewrite <- filter_app, IHeqs, Pfilter.

    + (* Case: EqFby *)
      unfold vars_defined;
        rewrite concatMap_cons;
        unfold var_defined; simpl.
      rewrite Peq; eauto.
  Qed.


  Lemma gather_eqs_fst_spec:
    forall eqs, Permutation (map fst (fst (gather_eqs eqs))) (gather_mem eqs).
  Proof.
    intro eqs.
    assert (Hgen: forall F S,
               Permutation (map fst (fst (fold_left gather_eq eqs (F, S))))
                           (map fst F ++ gather_mem eqs)).
    {
      induction eqs as [ | eq eqs IHeqs ]; intros F S; simpl.
      - now rewrite app_nil_r.
      - destruct eq as [ | i | i ck v0 le ]; simpl;
          match goal with
          | |- context[ EqApp _ _ _ _ _ ] => destruct i
          | _ => idtac
          end; rewrite IHeqs; auto.
        assert (Hmem: gather_mem (EqFby i ck v0 le :: eqs)
                      = i :: gather_mem eqs)
          by now unfold gather_mem; rewrite concatMap_cons.

        now rewrite Hmem, <- Permutation_middle, app_comm_cons.
    }

    now apply Hgen.
  Qed.

  Lemma gather_eqs_snd_spec:
    forall eqs, Permutation (snd (gather_eqs eqs)) (gather_insts eqs).
  Proof.
    intro eqs.
    assert (Hgen: forall F S,
               Permutation (snd (fold_left gather_eq eqs (F, S)))
                           (S ++ gather_insts eqs)).
    {
      induction eqs as [ | eq eqs IHeqs ]; intros F S; simpl.
      - now rewrite app_nil_r.
      - destruct eq as [ | is ck f les | ]; simpl; try rewrite IHeqs; auto.
        unfold gather_insts; rewrite concatMap_cons.
        destruct is; rewrite IHeqs; auto;
          rewrite <-app_comm_cons, Permutation_middle; auto.
    }

    now apply Hgen.
  Qed.

  Lemma fst_snd_gather_eqs_var_defined:
    forall eqs,
      Permutation (map fst (snd (gather_eqs eqs)) ++ gather_app_vars eqs)
                  (vars_defined (filter is_app eqs)).
  Proof.
    intro eqs.
    assert (Hperm: Permutation (map fst (gather_insts eqs) ++ gather_app_vars eqs)
                               (vars_defined (filter is_app eqs))).
    {
      induction eqs as [|[] eqs]; simpl; auto.
      destruct i as [ | x xs ]; auto.
      assert (Happ: gather_app_vars (EqApp (x :: xs) c i0 l o :: eqs)
                    = xs ++ gather_app_vars eqs)
        by now unfold gather_app_vars; rewrite concatMap_cons.

      assert (Hinst: map fst (gather_insts (EqApp (x :: xs) c i0 l o :: eqs))
                     = x :: map fst (gather_insts eqs))
        by now unfold gather_insts; rewrite concatMap_cons.

      rewrite Happ, Hinst.
      simpl;
        unfold vars_defined;
        rewrite concatMap_cons, <- IHeqs.
      unfold var_defined; simpl.
      apply Permutation_cons.
      do 2rewrite <- Permutation_app_assoc.
      now apply Permutation_app_tail, Permutation_app_comm.
    }

    rewrite <- Hperm.
    apply Permutation_app_tail.
    now rewrite gather_eqs_snd_spec.
  Qed.

  Lemma fst_fst_gather_eqs_var_defined:
    forall eqs,
      Permutation (map fst (fst (gather_eqs eqs)))
                  (vars_defined (filter is_fby eqs)).
  Proof.
    intro eqs.
    assert (Hperm: Permutation (gather_mem eqs)
                               (vars_defined (filter is_fby eqs))).
    {
      induction eqs as [|eq eqs]; auto.
      destruct eq; try (now simpl; auto).
      simpl.
      unfold gather_mem, vars_defined; simpl.
      rewrite 2 concatMap_cons.
      apply Permutation_cons.
      auto.
    }

    rewrite <- Hperm.
    apply gather_eqs_fst_spec.
  Qed.

  Lemma In_fst_fold_left_gather_eq:
    forall eqs xc mems insts,
      In xc (fst (fold_left gather_eq eqs (mems, insts))) <->
      In xc mems \/ In xc (fst (fold_left gather_eq eqs ([], insts))).
  Proof.
    induction eqs as [|[]]; simpl; intros; auto.
    - split; auto; intros [|]; auto; contradiction.
    - destruct i; simpl in *; auto.
    - rewrite IHeqs; symmetry; rewrite IHeqs.
      split; intros [Hin|Hin']; auto.
      + now left; right.
      + destruct Hin' as [[|]|]; auto; try contradiction.
        now left; left.
      + destruct Hin; auto.
        now right; left; left.
  Qed.

  Lemma In_snd_fold_left_gather_eq:
    forall eqs xf mems insts,
      In xf (snd (fold_left gather_eq eqs (mems, insts))) <->
      In xf insts \/ In xf (snd (fold_left gather_eq eqs (mems, []))).
  Proof.
    induction eqs as [|[]]; simpl; intros; auto.
    - split; auto; intros [|]; auto; contradiction.
    - destruct i; simpl in *; auto.
      rewrite IHeqs; symmetry; rewrite IHeqs.
      split; intros [Hin|Hin']; auto.
      + now left; right.
      + destruct Hin' as [[|]|]; auto; try contradiction.
        now left; left.
      + destruct Hin; auto.
        now right; left; left.
  Qed.

  Lemma Forall_ValidId_idty:
    forall A B (xs: list (ident * (A * B))),
      Forall ValidId (idty xs) <-> Forall ValidId xs.
  Proof.
    induction xs as [|x xs]; split; inversion_clear 1; simpl; eauto;
      destruct x as (x & tyck); constructor; try rewrite IHxs in *; auto.
  Qed.

  (* =translate_node= *)
  Program Definition translate_node (n: node) : SynSB.block :=
    (* TODO: fst (gather_eqs) should be a PS.t
               (i.e., do ps_from_list directly) *)
    let gathered := gather_eqs n.(n_eqs) in
    let lasts := fst gathered in
    let lasts_ids := ps_from_list (map fst lasts) in
    let blocks := snd gathered in
    let partitioned := partition (fun x => PS.mem (fst x) lasts_ids) n.(n_vars) in
    let vars := snd partitioned in
    {| SynSB.b_name  := n.(n_name);
       SynSB.b_blocks := blocks;
       SynSB.b_in   := idty n.(n_in);
       SynSB.b_vars := idty vars;
       SynSB.b_lasts := lasts;
       SynSB.b_out  := idty n.(n_out);
       SynSB.b_eqs  := translate_eqns n.(n_eqs)
    |}.
  Next Obligation.
    repeat rewrite <-idty_app. rewrite NoDupMembers_idty.
    rewrite (Permutation_app_comm n.(n_in)).
    rewrite Permutation_app_assoc.
    match goal with |- context [snd (partition ?p ?l)] =>
                    apply (NoDupMembers_app_r (fst (partition p l))) end.
    rewrite <-(Permutation_app_assoc (fst _)).
    rewrite <- (permutation_partition _ n.(n_vars)).
    rewrite (Permutation_app_comm n.(n_out)), <-Permutation_app_assoc.
    rewrite (Permutation_app_comm n.(n_vars)), Permutation_app_assoc.
    apply n.(n_nodup).
  Qed.
  Next Obligation.
    rewrite fst_fst_gather_eqs_var_defined.
    eapply (NoDup_app_weaken _ (gather_app_vars n.(n_eqs))).
    rewrite <-app_assoc.
    rewrite fst_snd_gather_eqs_var_defined.
    rewrite Permutation_app_comm.
    eapply (NoDup_app_weaken _ (vars_defined (filter is_def n.(n_eqs)))).
    rewrite Permutation_app_comm.
    unfold vars_defined, concatMap.
    rewrite <- 2 concat_app.
    rewrite <- 2 map_app.
    rewrite is_filtered_eqs.
    apply NoDup_var_defined_n_eqs.
  Qed.
  Next Obligation.
    unfold translate_eqns, gather_eqs, concatMap.
    generalize (@nil (ident * const)).
    induction (n_eqs n) as [|[]]; simpl.
    - split; intros ** H.
      + destruct H; contradiction.
      + inv H.
    - setoid_rewrite IHl; split; intros ** H.
      + right; auto.
      + inversion_clear H as [?? Hin|]; auto; inv Hin.
    - destruct o as [|].
      + destruct i.
        * setoid_rewrite IHl; reflexivity.
        *{ setoid_rewrite In_snd_fold_left_gather_eq; split.
           - intros (?&[Hin|Hin]).
             + destruct Hin as [E|]; try contradiction; inv E; simpl.
               do 2 constructor.
             + right; right; eapply IHl; eauto.
           - intro BlockIn.
             inversion_clear BlockIn as [?? Hin|?? BlockIn'].
             + inv Hin; eexists; left; constructor; eauto.
             + inversion_clear BlockIn' as [?? Hin|?? BlockIn].
               * inv Hin; eexists; left; constructor; eauto.
               * eapply IHl in BlockIn as (?&?).
                 eexists; right; eauto.
         }
      + destruct i.
        * setoid_rewrite IHl; reflexivity.
        *{ setoid_rewrite In_snd_fold_left_gather_eq; split.
           - intros (?&[Hin|Hin]).
             + destruct Hin as [E|]; try contradiction; inv E; simpl.
               do 2 constructor.
             + right; eapply IHl; eauto.
           - intro BlockIn.
             inversion_clear BlockIn as [?? Hin|?? BlockIn'].
             + inv Hin; eexists; left; constructor; eauto.
             + eapply IHl in BlockIn' as (?&?).
               eexists; right; eauto.
         }
    - setoid_rewrite IHl; split; intros ** H.
      + right; auto.
      + inversion_clear H as [?? Hin|]; auto; inv Hin.
  Qed.
  Next Obligation.
    pose proof n.(n_good) as [ValidApp].
    split; [|split; [|split]]; auto.
    - repeat rewrite <-idty_app. apply Forall_ValidId_idty.
      rewrite (Permutation_app_comm n.(n_in)).
      rewrite Permutation_app_assoc.
      match goal with |- context [snd (partition ?p ?l)] =>
                      apply (Forall_app_weaken (fst (partition p l))) end.
      rewrite <-(Permutation_app_assoc (fst _)).
      rewrite <- (permutation_partition _ n.(n_vars)).
      rewrite <-(Permutation_app_assoc n.(n_vars)).
      rewrite Permutation_app_comm; auto.
    - pose proof (n_defd n) as Perm.
      unfold ValidId, NotReserved in *.
      apply Forall_forall; rewrite Forall_forall in ValidApp.
      intros ** Hin.
      apply in_map with (f := fst) in Hin.
      rewrite fst_fst_gather_eqs_var_defined in Hin.
      rewrite <-is_filtered_vars_defined in Perm.
      assert (In (fst x) (vars_defined (filter is_def (n_eqs n)) ++
                                       vars_defined (filter is_app (n_eqs n)) ++
                                       vars_defined (filter is_fby (n_eqs n)))) as Hin'
          by (rewrite 2 in_app; intuition).
      eapply Permutation_in in Perm; eauto.
      apply in_map_iff in Perm as (? & E & Perm).
      rewrite <-E; apply ValidApp.
      apply in_app; auto.
    - pose proof (n_defd n) as Perm.
      unfold ValidId, NotReserved in *.
      apply Forall_forall; rewrite Forall_forall in ValidApp.
      intros ** Hin.
      apply in_map with (f := fst) in Hin.
      assert (In (fst x) (map fst (snd (gather_eqs (n_eqs n))) ++ gather_app_vars (n_eqs n))) as Hin'
          by (apply in_app; auto).
      rewrite fst_snd_gather_eqs_var_defined in Hin'.
      rewrite <-is_filtered_vars_defined in Perm.
      assert (In (fst x) (vars_defined (filter is_def (n_eqs n)) ++
                                       vars_defined (filter is_app (n_eqs n)) ++
                                       vars_defined (filter is_fby (n_eqs n)))) as Hin''
          by (rewrite 2 in_app; intuition).
      eapply Permutation_in in Perm; eauto.
      apply in_map_iff in Perm as (? & E & Perm).
      rewrite <-E; apply ValidApp.
      apply in_app; auto.
  Qed.
  (* Next Obligation. *)
  (*   destruct n; simpl. *)
  (*   now rewrite length_idty. *)
  (* Qed. *)
  (* Next Obligation. *)
  (*   destruct n; simpl. *)
  (*   now rewrite length_idty. *)
  (* Qed. *)

  Definition translate (G: global) : SynSB.program :=
    map translate_node G.

  Lemma map_c_name_translate:
    forall g,
      map SynSB.b_name (translate g) = map n_name g.
  Proof.
    induction g as [|n g]; auto.
    simpl; rewrite IHg. reflexivity.
  Qed.

  Lemma find_block_translate:
    forall n G bl prog',
      SynSB.find_block n (translate G) = Some (bl, prog') ->
      exists node, find_node n G = Some node
              /\ bl = translate_node node.
  Proof.
    induction G as [|node G]; [now inversion 1|].
    intros ** Hfind.
    simpl in Hfind.
    destruct (EquivDec.equiv_dec node.(n_name) n) as [Heq|Hneq].
    - rewrite Heq, ident_eqb_refl in Hfind.
      injection Hfind; intros; subst.
      exists node. split; auto.
      simpl. now rewrite Heq, ident_eqb_refl.
    - apply ident_eqb_neq in Hneq. rewrite Hneq in Hfind.
      apply IHG in Hfind. destruct Hfind as (node' & Hfind & Hcls).
      exists node'. simpl. rewrite Hneq. auto.
  Qed.

  Lemma find_node_translate:
    forall n g node,
      find_node n g = Some node ->
      exists bl prog',
        SynSB.find_block n (translate g) = Some (bl, prog')
        /\ bl = translate_node node.
  Proof.
    induction g as [|node g]; [now inversion 1|].
    intros ** Hfind.
    simpl in Hfind.
    destruct (EquivDec.equiv_dec node.(n_name) n) as [Heq|Hneq].
    - rewrite Heq, ident_eqb_refl in Hfind.
      injection Hfind; intros; subst node0.
      exists (translate_node node), (translate g). split; auto.
      simpl. now rewrite Heq, ident_eqb_refl.
    - apply ident_eqb_neq in Hneq. rewrite Hneq in Hfind.
      apply IHg in Hfind. destruct Hfind as (bl & prog' & Hfind & Hbl).
      exists bl, prog'. split; auto. simpl. now rewrite Hneq.
  Qed.

End TRANSLATION.

Module TranslationFun
       (Ids     : IDS)
       (Op      : OPERATORS)
       (Clks    : CLOCKS Ids)
       (ExprSyn : NLEXPRSYNTAX Op)
       (SynNL   : NLSYNTAX Ids Op Clks ExprSyn)
       (SynSB   : SBSYNTAX Ids Op Clks ExprSyn)
       (Mem     : MEMORIES Ids Op Clks ExprSyn SynNL)
<: TRANSLATION Ids Op Clks ExprSyn SynNL SynSB Mem.
  Include TRANSLATION Ids Op Clks ExprSyn SynNL SynSB Mem.
End TranslationFun.
