From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Coq Require Import Sorting.Permutation.
From Coq Require Import Morphisms.
From Coq Require Import Program.Tactics.
From Coq Require Import Omega.

From Coq Require Import FSets.FMapPositive.
From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import NLustre.NLOrdered.
From Velus Require Import IndexedStreams.
From Velus Require Import CoindStreams.
From Velus Require Import CoindToIndexed.

From Velus Require Import CoreExpr.CESemantics.
From Velus Require Import NLustre.NLIndexedSemantics.
From Velus Require Import NLustre.NLCoindSemantics.

From Coq Require Import Setoid.

Module Type NLCOINDTOINDEXED
       (Import Ids     : IDS)
       (Import Op      : OPERATORS)
       (Import OpAux   : OPERATORS_AUX          Op)
       (Import CESyn   : CESYNTAX               Op)
       (Import Syn     : NLSYNTAX           Ids Op       CESyn)
       (Import IStr    : INDEXEDSTREAMS         Op OpAux)
       (Import CStr    : COINDSTREAMS           Op OpAux)
       (Import CIStr   : COINDTOINDEXED         Op OpAux           CStr IStr)
       (Import Ord     : NLORDERED          Ids Op       CESyn Syn)
       (CESem          : CESEMANTICS        Ids Op OpAux CESyn     IStr)
       (Indexed        : NLINDEXEDSEMANTICS Ids Op OpAux CESyn Syn IStr Ord CESem)
       (CoInd          : NLCOINDSEMANTICS   Ids Op OpAux CESyn Syn CStr Ord).

  Section Global.

    Variable G : global.

    (** * SEMANTICS CORRESPONDENCE *)

    (** ** Variables *)

    Corollary sem_vars_impl:
      forall H xs xss,
      Forall2 (sem_var H) xs xss ->
      CESem.sem_vars (tr_history H) xs (tr_Streams xss).
    Proof.
      unfold CESem.sem_vars, IStr.lift'.
      induction 1 as [|? ? ? ? Find];
        simpl; intro; constructor; auto.
      - apply sem_var_impl; auto.
      - apply IHForall2.
    Qed.
    Hint Resolve sem_vars_impl.

    (** ** Semantics of exps *)

    (** State the correspondence for [exp].
        Goes by induction on the coinductive semantics of [exp]. *)
    Hint Constructors CESem.sem_exp_instant.
    Lemma sem_exp_impl:
      forall H b e es,
        CoInd.sem_exp H b e es ->
        CESem.sem_exp (tr_Stream b) (tr_history H) e (tr_Stream es).
    Proof.
      unfold tr_Stream.
      induction 1 as [? ? ? ? Hconst
                            |? ? ? ? ? Hvar
                            |? ? ? ? ? ? ? ? ? ? Hvar Hwhen
                            |? ? ? ? ? ? ? ? ? Hlift1
                            |? ? ? ? ? ? ? ? ? ? ? ? ? Hlift2]; intro n.
      - rewrite const_spec in Hconst; rewrite Hconst.
        destruct (tr_Stream b n); eauto.
      - apply sem_var_impl in Hvar; eauto.
      - specialize (IHsem_exp n).
        apply sem_var_impl in Hvar;
          unfold tr_Stream, IStr.sem_var, IStr.lift in Hvar.
        specialize (Hvar n); simpl in *.
        rewrite when_spec in Hwhen.
        destruct (Hwhen n)
          as [(Hes & Hxs & Hos)
             |[(? & ? & Hes & Hxs & ? & Hos)
              |(? & ? & Hes & Hxs & ? & Hos)]];
          rewrite Hos; rewrite Hes in IHsem_exp; rewrite Hxs in Hvar;
            eauto.
        rewrite <-(Bool.negb_involutive k); eauto.
      - specialize (IHsem_exp n); simpl in IHsem_exp.
        rewrite lift1_spec in Hlift1; destruct (Hlift1 n)
          as [(Hes & Hos)|(? & ? & Hes & ? & Hos)];
          rewrite Hos; rewrite Hes in IHsem_exp; eauto.
      - specialize (IHsem_exp1 n); specialize (IHsem_exp2 n); simpl in *.
        rewrite lift2_spec in Hlift2; destruct (Hlift2 n)
          as [(Hes1 & Hes2 & Hos)|(? & ? & ? & Hes1 & Hes2 & ? & Hos)];
          rewrite Hos; rewrite Hes1 in IHsem_exp1; rewrite Hes2 in IHsem_exp2;
            eauto.
    Qed.
    Hint Resolve sem_exp_impl.

    Corollary sem_exps_impl:
      forall H b es ess,
        Forall2 (CoInd.sem_exp H b) es ess ->
        CESem.sem_exps (tr_Stream b) (tr_history H) es (tr_Streams ess).
    Proof.
      induction 1; simpl; constructor.
      - apply sem_exp_impl; auto.
      - apply IHForall2.
    Qed.
    Hint Resolve sem_exps_impl.

    (** Give an indexed specification for annotated [exp], using the previous
        lemma. *)
    Lemma sem_aexp_index:
      forall n H b ck le es,
        CoInd.sem_aexp H b ck le es ->
        (sem_clock_instant (tr_Stream b n)
                                   (tr_history H n) ck false
         /\ CESem.sem_exp_instant
             (tr_Stream b n) (tr_history H n) le absent
         /\ tr_Stream es n = absent)
        \/
        (exists e,
            sem_clock_instant (tr_Stream b n)
                                      (tr_history H n) ck true
            /\ CESem.sem_exp_instant
                (tr_Stream b n) (tr_history H n) le (present e)
            /\ tr_Stream es n = present e).
    Proof.
      induction n; intros * Indexed.
      - inversion_clear Indexed as [? ? ? ? ? ? ? Indexed' Hck
                                      |? ? ? ? ? ? Indexed' Hck];
          apply sem_exp_impl in Indexed'; specialize (Indexed' 0);
            repeat rewrite tr_Stream_0; repeat rewrite tr_Stream_0 in Indexed';
              eapply (sem_clock_impl) in Hck; specialize (Hck 0); rewrite tr_Stream_0 in Hck.
        + right. eexists; intuition; auto.
        + left; intuition.
      - inversion_clear Indexed as [? ? ? ? ? ? ? Indexed'|? ? ? ? ? ? Indexed'];
          apply sem_exp_impl in Indexed';
          rewrite tr_Stream_S, tr_history_tl; eauto.
    Qed.

    (** We deduce from the previous lemma the correspondence for annotated
        [exp]. *)
    (* Hint Constructors CESem.sem_aexp_instant. *)
    Corollary sem_aexp_impl:
      forall H b e es ck,
        CoInd.sem_aexp H b ck e es ->
        CESem.sem_aexp (tr_Stream b) (tr_history H) ck e (tr_Stream es).
    Proof.
      intros * Indexed n.
      apply (sem_aexp_index n) in Indexed;
        destruct Indexed as [(? & ? & Hes)|(? & ? & ? & Hes)];
        rewrite Hes; constructor; auto.
    Qed.
    Hint Resolve sem_aexp_impl.

    (** [fby] is not a predicate but a function, so we directly state the
        correspondence.  *)
    Lemma fby_impl:
      forall c xs,
      tr_Stream (sfby c xs) ≈ Indexed.fby c (tr_Stream xs).
    Proof.
      intros * n; revert c xs.
      induction n; intros.
      - unfold_Stv xs; rewrite unfold_Stream at 1;
          unfold Indexed.fby; simpl; now rewrite tr_Stream_0.
      - unfold_Stv xs; rewrite unfold_Stream at 1;
          unfold Indexed.fby; simpl; repeat rewrite tr_Stream_S;
            rewrite IHn; unfold Indexed.fby;
              destruct (tr_Stream xs n); auto; f_equal;
                clear IHn; induction n; simpl; auto;
                  rewrite tr_Stream_S; destruct (tr_Stream xs n); auto.
    Qed.

    (** ** Semantics of cexps *)

    (** State the correspondence for [cexp].
        Goes by induction on the coinductive semantics of [cexp]. *)
    Hint Constructors CESem.sem_cexp_instant.
    Lemma sem_cexp_impl:
      forall H b e es,
        CoInd.sem_cexp H b e es ->
        CESem.sem_cexp (tr_Stream b) (tr_history H) e (tr_Stream es).
    Proof.
      unfold tr_Stream.
      induction 1 as [? ? ? ? ? ? ? ? ? Hvar Ht ? ? ? Hmerge
                    |? ? ? ? ? ? ? ? ? He Ht ? ? ? Hite
                    |? ? ? ? He]; intro n.
      - specialize (IHsem_cexp1 n); specialize (IHsem_cexp2 n).
        apply sem_var_impl in Hvar; eauto.
        unfold tr_Stream, IStr.sem_var, IStr.lift in Hvar.
        specialize (Hvar n); simpl in *.
        rename H0_ into Hf.
        rewrite merge_spec in Hmerge; destruct (Hmerge n)
          as [(Hxs & Hts & Hfs & Hos)
             |[(? & Hxs & Hts & Hfs & Hos)
              |(? & Hxs & Hts & Hfs & Hos)]];
          rewrite Hos; rewrite Hts in IHsem_cexp1; rewrite Hfs in IHsem_cexp2;
            rewrite Hxs in Hvar; auto.

      - specialize (IHsem_cexp1 n); specialize (IHsem_cexp2 n).
        eapply sem_exp_impl in He; unfold tr_Stream in He.
        specialize (He n); simpl in *.
        rewrite ite_spec in Hite; destruct (Hite n)
          as [(Hes & Hts & Hfs & Hos)
             |[(ct & cf & Hes & Hts & Hfs & Hos)
              |(ct & cf & Hes & Hts & Hfs & Hos)]];
          rewrite Hos; rewrite Hts in IHsem_cexp1; rewrite Hfs in IHsem_cexp2;
            rewrite Hes in He; auto.
        + change (present ct) with (if true then present ct else present cf).
          eapply CESem.Site_eq; eauto.
          apply val_to_bool_true.
        + change (present cf) with (if false then present ct else present cf).
          eapply CESem.Site_eq; eauto.
          apply val_to_bool_false.

      - apply sem_exp_impl in He; unfold tr_Stream in *; auto.
    Qed.
    Hint Resolve sem_cexp_impl.

    (** Give an indexed specification for annotated [cexp], using the previous
        lemma.  *)
    Lemma sem_caexp_index:
      forall n H b ck le es,
        CoInd.sem_caexp H b ck le es ->
        (sem_clock_instant (tr_Stream b n)
                                   (tr_history H n) ck false
         /\ CESem.sem_cexp_instant
             (tr_Stream b n) (tr_history H n) le absent
         /\ tr_Stream es n = absent)
        \/
        (exists e,
            sem_clock_instant (tr_Stream b n)
                                      (tr_history H n) ck true
            /\ CESem.sem_cexp_instant
                (tr_Stream b n) (tr_history H n) le (present e)
            /\ tr_Stream es n = present e).
    Proof.
      induction n; intros * Indexed.
      - inversion_clear Indexed as [? ? ? ? ? ? ? Indexed' Hck
                                      |? ? ? ? ? ? Indexed' Hck];
          apply sem_cexp_impl in Indexed'; specialize (Indexed' 0);
            repeat rewrite tr_Stream_0; repeat rewrite tr_Stream_0 in Indexed';
              apply sem_clock_impl in Hck; specialize (Hck 0); rewrite tr_Stream_0 in Hck.
        + right. eexists; intuition; auto.
        + left; intuition.
      - inversion_clear Indexed as [? ? ? ? ? ? ? Indexed'|? ? ? ? ? ? Indexed'];
          apply sem_cexp_impl in Indexed';
          repeat rewrite tr_Stream_S; rewrite tr_history_tl; eauto.
    Qed.

    (** We deduce from the previous lemma the correspondence for annotated
        [cexp]. *)
    Corollary sem_caexp_impl:
      forall H b e es ck,
        CoInd.sem_caexp H b ck e es ->
        CESem.sem_caexp (tr_Stream b) (tr_history H) ck e (tr_Stream es).
    Proof.
      intros * Indexed n.
      apply (sem_caexp_index n) in Indexed; destruct Indexed
        as [(? & ? & Hes)|(? & ? & ? & Hes)];
        rewrite Hes; constructor; auto.
    Qed.
    Hint Resolve sem_caexp_impl.

    (** * RESET CORRESPONDENCE  *)

    (** We state the correspondence for [bools_of]. *)
    Lemma bools_of_impl:
      forall xs rs,
        CStr.bools_of xs rs ->
        CESem.bools_of (tr_Stream xs) (tr_Stream rs).
    Proof.
      intros ** n; revert dependent xs; revert rs.
      induction n; intros * Rst.
      - unfold_Stv xs; unfold_Stv rs; rewrite tr_Stream_0; auto;
          inv Rst; simpl in *; auto.
      - unfold_Stv xs; unfold_Stv rs; rewrite 2 tr_Stream_S;
          inv Rst; simpl in *; auto.
    Qed.

    (** ** Properties about [count] and [mask] *)

    (** When a reset occurs initially, the count at [n] is the count at [n]
        forgetting the first instant, plus one if no reset occurs at [n] when
        shifting. *)
    Lemma count_true_shift:
      forall n r,
        IStr.count (tr_Stream (true ⋅ r)) n
        = if tr_Stream r n
          then IStr.count (tr_Stream r) n
          else S (IStr.count (tr_Stream r) n).
    Proof.
      induction n; simpl; intros.
      - destruct (tr_Stream r 0); auto.
      - specialize (IHn r).
        rewrite tr_Stream_S.
        destruct (tr_Stream r n) eqn: E';
          destruct (tr_Stream r (S n)); rewrite IHn; auto.
    Qed.

    (** When no reset occurs initially, the count at [n] is the count at [n]
        forgetting the first instant, minus one if a reset occurs at [n] when
        shifting. *)
    Lemma count_false_shift:
      forall n r,
        IStr.count (tr_Stream (false ⋅ r)) n
        = if tr_Stream r n
          then IStr.count (tr_Stream r) n - 1
          else IStr.count (tr_Stream r) n.
    Proof.
      induction n; simpl; intros.
      - destruct (tr_Stream r 0); auto.
      - specialize (IHn r).
        rewrite tr_Stream_S.
        destruct (tr_Stream r n) eqn: E';
          destruct (tr_Stream r (S n)); rewrite IHn; try omega.
        + apply Minus.minus_Sn_m, count_true_ge_1; auto.
        + rewrite Minus.minus_Sn_m; try omega.
          apply count_true_ge_1; auto.
    Qed.

    (** State the correspondence for [count]. *)
    Lemma count_impl:
      forall r,
        tr_Stream (CStr.count r) ≈ IStr.count (tr_Stream r).
    Proof.
      intros ** n.
      unfold CStr.count.
      revert r; induction n; intros; simpl.
      - rewrite (unfold_Stream (count_acc 0 r)); simpl.
        rewrite tr_Stream_0; auto.
      - rewrite (unfold_Stream (count_acc 0 r)); simpl.
        rewrite tr_Stream_S. destruct (hd r) eqn: R.
        + unfold tr_Stream at 1; unfold tr_Stream in IHn; unfold Str_nth in *.
          rewrite count_S_nth, IHn.
          destruct r; simpl in *; rewrite R, count_true_shift, tr_Stream_S.
          now destruct (tr_Stream r n).
        + rewrite IHn.
          destruct r; simpl in *; rewrite R, count_false_shift, tr_Stream_S.
          destruct (tr_Stream r n) eqn: R'; auto.
          apply count_true_ge_1 in R'; rewrite Minus.minus_Sn_m; omega.
    Qed.

    (** State the correspondence for [mask]. *)
    Lemma mask_impl:
      forall k r xss,
        tr_Streams (List.map (CStr.mask k r) xss)
        ≈ IStr.mask k (tr_Stream r) (tr_Streams xss).
    Proof.
      induction xss as [|xs];
        simpl; intros * n; unfold IStr.mask in *.
      - destruct (k =? IStr.count (tr_Stream r) n); auto.
      - simpl; unfold tr_Stream at 1; rewrite mask_nth.
        rewrite IHxss; simpl.
        rewrite <-count_impl, Nat.eqb_sym.
        unfold tr_Stream; cases.
    Qed.

    (** * FINAL LEMMAS *)


    (** Correspondence for [clocks_of], used to give a base clock for node
        applications. *)
    Lemma tr_clocks_of:
      forall xss,
        CESem.clock_of (tr_Streams xss) ≈ tr_Stream (CStr.clocks_of xss).
    Proof.
      unfold CESem.clock_of.
      intros xss n; revert dependent xss; induction n; intros.
      - rewrite unfold_Stream at 1; simpl; rewrite tr_Stream_0, tr_Streams_hd.
        induction xss; simpl; auto.
        f_equal; auto.
      - rewrite unfold_Stream at 1; simpl.
        rewrite tr_Stream_S, <-tr_Streams_tl; auto.
    Qed.
    Hint Resolve tr_clocks_of.

    (** Give an indexed specification for Streams synchronization. *)
    Lemma aligned_index:
      forall xs bs,
        aligned xs bs ->
        forall n, tr_Stream bs n = true <-> tr_Stream xs n <> absent.
    Proof.
      intros * Sync n; revert dependent xs; revert bs; induction n; intros.
      - inversion_clear Sync; rewrite 2 tr_Stream_0; intuition; discriminate.
      - rewrite <-2 tr_Stream_tl; apply IHn.
        inv Sync; auto.
    Qed.

    Lemma sem_clocked_var_impl:
      forall H b x ck xs,
        sem_var H x xs ->
        CoInd.sem_clocked_var H b x ck ->
        CESem.sem_clocked_var (tr_Stream b) (tr_history H) x ck.
    Proof.
      intros * Var (Sem & Sem').
      pose proof Var as Var'.
      apply Sem in Var as (bs & Clock & Sync); rename Var' into Var.
      apply sem_var_impl in Var;
        apply sem_clock_impl in Clock.
      pose proof (aligned_index _ _ Sync) as Spec.
      intro n; specialize (Var n); specialize (Clock n).
      split; split.
      - intros * Clock'.
        eapply IStr.sem_clock_instant_det in Clock; eauto.
        symmetry in Clock; apply Spec, not_absent_present in Clock as (?& E).
        rewrite E in Var; eauto.
      - intros (?& Var').
        eapply IStr.sem_var_instant_det in Var; eauto.
        assert (tr_Stream bs n = true) as <-; auto.
        apply Spec; intro; congruence.
      - intros * Clock'.
        eapply IStr.sem_clock_instant_det in Clock; eauto.
        symmetry in Clock; rewrite <-Bool.not_true_iff_false, Spec in Clock.
        assert (tr_Stream xs n = absent) as <-; auto.
        apply Decidable.not_not in Clock; auto.
        apply decidable_eq_value.
      - intros Var'.
        eapply IStr.sem_var_instant_det in Var; eauto.
        assert (tr_Stream bs n = false) as <-; auto.
        rewrite <-Bool.not_true_iff_false, Spec; auto.
    Qed.

    Lemma sem_clocked_vars_impl:
      forall H b xcs xss,
        Forall2 (sem_var H) (List.map fst xcs) xss ->
        CoInd.sem_clocked_vars H b xcs ->
        CESem.sem_clocked_vars (tr_Stream b) (tr_history H) xcs.
    Proof.
      intros * Vars Sem n.
      apply Forall_forall; intros (x, ck) Hin; simpl.
      pose proof Hin as Hin'.
      apply in_map with (f := fst) in Hin.
      eapply Forall2_in_left in Vars as (?&?&?); eauto.
      eapply sem_clocked_var_impl; eauto.
      eapply Forall_forall in Sem; eauto; auto.
    Qed.
    Hint Resolve sem_clocked_vars_impl.

    (** The final theorem stating the correspondence for nodes applications.
        We have to use a custom mutually recursive induction scheme [sem_node_mult]. *)
    Hint Constructors Indexed.sem_equation.
    Theorem implies:
      forall f xss yss,
        CoInd.sem_node G f xss yss ->
        Indexed.sem_node G f (tr_Streams xss) (tr_Streams yss).
    Proof.
      induction 1 as [| |???????????????? IH| |???????? Same Heqs IH]
                       using CoInd.sem_node_mult with
          (P_equation := fun H b e =>
                           CoInd.sem_equation G H b e ->
                           Indexed.sem_equation G (tr_Stream b) (tr_history H) e);
        eauto.

      - econstructor; eauto.
        intro; rewrite tr_clocks_of; auto.
        apply sem_clock_impl; auto.

      - econstructor; eauto.
        + intro; rewrite tr_clocks_of; auto.
          apply sem_clock_impl; auto.
        + apply bools_of_impl; eauto.
        + intro k; destruct (IH k).
          now rewrite <- 2 mask_impl.

      - econstructor; auto; subst; eauto.
        rewrite <-fby_impl; auto.

      - econstructor; eauto.
        + intro; rewrite tr_clocks_of; auto.
          eapply sem_clocked_vars_impl; auto.
          rewrite map_fst_idck; eauto.
        + apply Forall_forall; intros * Hin.
          rewrite tr_clocks_of.
          eapply Forall_forall in IH; eauto; eapply Forall_forall in Heqs; eauto.
    Qed.

  End Global.

End NLCOINDTOINDEXED.

Module NLCoindToIndexedFun
       (Ids     : IDS)
       (Op      : OPERATORS)
       (OpAux   : OPERATORS_AUX          Op)
       (CESyn   : CESYNTAX               Op)
       (Syn     : NLSYNTAX           Ids Op       CESyn)
       (IStr    : INDEXEDSTREAMS         Op OpAux)
       (CStr    : COINDSTREAMS           Op OpAux)
       (CIStr   : COINDTOINDEXED         Op OpAux           CStr IStr)
       (Ord     : NLORDERED          Ids Op       CESyn Syn)
       (CESem   : CESEMANTICS        Ids Op OpAux CESyn     IStr)
       (Indexed : NLINDEXEDSEMANTICS Ids Op OpAux CESyn Syn IStr Ord CESem)
       (CoInd   : NLCOINDSEMANTICS   Ids Op OpAux CESyn Syn CStr Ord)
<: NLCOINDTOINDEXED Ids Op OpAux CESyn Syn IStr CStr CIStr Ord CESem Indexed CoInd.
  Include NLCOINDTOINDEXED Ids Op OpAux CESyn Syn IStr CStr CIStr Ord CESem Indexed CoInd.
End NLCoindToIndexedFun.
