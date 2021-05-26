From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.
From Coq Require Import Sorting.Permutation.
From Coq Require Import Setoid.
From Coq Require Import Morphisms.
From Coq Require Import Program.Tactics.

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
From Velus Require Import IndexedToCoind.

From Velus Require Import CoreExpr.CESemantics.
From Velus Require Import CoreExpr.CEInterpreter.
From Velus Require Import NLustre.NLIndexedSemantics.
From Velus Require Import NLustre.NLCoindSemantics.

(** We can simplify the proofs a bit :p *)
From Velus Require Import CoindToIndexed NLCoindToIndexed.

From Coq Require Import Setoid.

Module Type NLINDEXEDTOCOIND
       (Import Ids    : IDS)
       (Import Op     : OPERATORS)
       (Import OpAux  : OPERATORS_AUX      Ids Op)
       (Import Cks    : CLOCKS             Ids Op OpAux)
       (Import CESyn  : CESYNTAX           Ids Op OpAux Cks)
       (Import Syn    : NLSYNTAX           Ids Op OpAux Cks CESyn)
       (Import IStr   : INDEXEDSTREAMS     Ids Op OpAux Cks)
       (Import CStr   : COINDSTREAMS       Ids Op OpAux Cks)
       (Import ICStr  : INDEXEDTOCOIND     Ids Op OpAux Cks IStr CStr)
       (Import Ord    : NLORDERED          Ids Op OpAux Cks CESyn Syn)
       (CESem         : CESEMANTICS        Ids Op OpAux Cks CESyn     IStr)
       (Indexed       : NLINDEXEDSEMANTICS Ids Op OpAux Cks CESyn Syn IStr Ord CESem)
       (Import Interp : CEINTERPRETER      Ids Op OpAux Cks CESyn     IStr     CESem)
       (CoInd         : NLCOINDSEMANTICS   Ids Op OpAux Cks CESyn Syn CStr Ord).

  (* Simplifying the proof a bit :p *)
  Module CIStr := CoindToIndexedFun Ids Op OpAux Cks CStr IStr.
  Module NLCIStr := NLCoindToIndexedFun Ids Op OpAux Cks CESyn Syn IStr CStr CIStr Ord CESem Indexed CoInd.

  Section Global.

    Variable G : global.

    (** * SEMANTICS CORRESPONDENCE *)

    (** ** Variables *)

    (* (** An inversion principle for [sem_var]. *) *)
    (* Lemma sem_var_inv: *)
    (*   forall H x xs, *)
    (*     CESem.sem_var H x xs -> *)
    (*     exists xs', *)
    (*       Env.find x H = Some xs' *)
    (*       /\ xs ≈ xs'. *)
    (* Proof. *)
    (*   unfold CESem.sem_var, CESem.lift'. *)
    (*   intros * Sem. *)
    (*   destruct (Env.find x H) as [xs'|] eqn: E; simpl in *. *)
    (*   - exists xs'; intuition. *)
    (*     intro n; specialize (Sem n). *)
    (*     unfold CESem.sem_var_instant, CESem.restr_hist in Sem. *)
    (*     rewrite Env.Props.P.F.map_o in Sem. *)
    (*     setoid_rewrite E in Sem. *)
    (*     now inv Sem. *)
    (*   - specialize (Sem 0). *)
    (*     unfold CESem.sem_var_instant, CESem.restr_hist in Sem. *)
    (*     rewrite Env.Props.P.F.map_o in Sem. *)
    (*     now setoid_rewrite E in Sem. *)
    (* Qed. *)

    (** An inversion principle for [sem_vars]. *)
    Lemma sem_vars_inv_from:
      forall H xs xss,
        CESem.sem_vars H xs xss ->
        forall n,
          Forall2 (fun x k => IStr.sem_var H x (streams_nth k xss))
                  (skipn n xs) (seq n (length xs - n)).
    Proof.
      unfold CESem.sem_vars, IStr.lift.
      intros * Sem n.
      apply Forall2_forall2; split.
      - now rewrite skipn_length, seq_length.
      - intros x_d k_d n' x k Length Hskipn Hseq.
        rewrite skipn_length in Length.
        rewrite nth_skipn in Hskipn.
        rewrite nth_seq in Hseq; auto; subst.
        intro m; specialize (Sem m).
        apply Forall2_forall2 in Sem.
        eapply Sem; eauto.
        + now apply Nat.lt_add_lt_sub_r.
        + unfold streams_nth; eauto.
    Qed.

    Corollary sem_vars_inv:
      forall H xs xss,
        CESem.sem_vars H xs xss ->
        Forall2 (fun x k => IStr.sem_var H x (streams_nth k xss))
                xs (seq 0 (length xs)).
    Proof.
      intros * Sem; apply sem_vars_inv_from with (n:=0) in Sem.
      now rewrite Nat.sub_0_r in Sem.
    Qed.

    Corollary sem_vars_impl_from:
      forall n H xs xss,
      CESem.sem_vars H xs xss ->
      Forall2 (sem_var (tr_history_from n H)) xs (tr_streams_from n xss).
    Proof.
      intros * Sem.
      assert (length xs = length (xss n)) as Length by
            (unfold CESem.sem_vars, IStr.lift in Sem; specialize (Sem n);
             now apply Forall2_length in Sem).
      apply Forall2_forall2; split.
      - now rewrite tr_streams_from_length.
      - apply sem_vars_inv in Sem.
        intros x_d xs_d n' x xs' En' Ex Exs'.
        apply Forall2_forall2 in Sem as (? & Sem).
        assert (nth n' (seq 0 (length xs)) 0 = n') as Nth by
              (rewrite <-(Nat.sub_0_r (length xs)), plus_n_O;
               apply nth_seq; rewrite Nat.sub_0_r; auto).
        eapply Sem in Nth; eauto.
        apply (sem_var_impl_from n) in Nth.
        subst.
        rewrite nth_tr_streams_from_nth; auto.
        now rewrite <-Length.
    Qed.

    Corollary sem_vars_impl:
      forall H xs xss,
      CESem.sem_vars H xs xss ->
      Forall2 (sem_var (tr_history H)) xs (tr_streams xss).
    Proof. apply sem_vars_impl_from. Qed.
    Hint Resolve sem_vars_impl_from sem_vars_impl.

    (** ** exp level synchronous operators inversion principles

        The indexed semantics is inductive only instant-speaking, therefore we
        can't use usual tactics like inversion nor induction.
        We prove some lemmas to provide inversion-like tactics on the semantics
        of exps.
        These lemmas could be proven using the classical axiom of choice which
        gives, from an instant semantics entailment true at every instant,
        the existence of a stream verifying the general entailment.
        But we rather use the interpretor to seq_streams these witnesses, with 2
        benefits :
        1) this is a constructive way of obtaining a witness
        2) we don't rely on an axiom whose use would have to be be deeply
           justified since it would raise some logical contradictions in Coq
     *)

    (** This tactic automatically uses the interpretor to give a witness stream. *)
    Ltac interp_str b H x Sem :=
      let Sem_x := fresh "Sem_" x in
      let sol sem interp complete :=
          assert (sem b H x (interp b H x)) as Sem_x
              by (intro; match goal with n:nat |- _ => specialize (Sem n) end;
                  unfold interp, lift_interp; inv Sem; erewrite <-complete; eauto)
      in
      let sol' sem interp complete :=
          assert (sem H x (interp H x)) as Sem_x
              by (intro; match goal with n:nat |- _ => specialize (Sem n) end;
                  unfold interp, lift_interp'; inv Sem; erewrite <-complete; eauto)
      in
      match type of x with
      | exp => sol CESem.sem_exp interp_exp interp_exp_instant_complete
      | cexp => sol CESem.sem_cexp interp_cexp interp_cexp_instant_complete
      | ident => sol' IStr.sem_var interp_var interp_var_instant_complete
      | clock => sol IStr.sem_clock interp_clock interp_clock_instant_complete
      end.

    Lemma when_inv:
      forall H b e x k es,
        CESem.sem_exp b H (Ewhen e x k) es ->
        exists ys xs,
          CESem.sem_exp b H e ys
          /\ IStr.sem_var H x xs
          /\
          (forall n,
              (exists sc,
                  ys n = present sc
                  /\ xs n = present (Venum k)
                  /\ es n = present sc)
              \/
              (exists sc k',
                  ys n = present sc
                  /\ xs n = present (Venum k')
                  /\ k <> k'
                  /\ es n = absent)
              \/
              (ys n = absent
               /\ xs n = absent
               /\ es n = absent)).
    Proof.
      intros * Sem.
      interp_str b H e Sem.
      interp_str b H x Sem.
      do 2 eexists; intuition; eauto.
      specialize (Sem_e n); specialize (Sem_x n); specialize (Sem n); inv Sem.
      - left; exists sc.
        repeat split; auto; intuition CESem.sem_det.
      - right; left; exists sc, b'; intuition; try CESem.sem_det.
      - right; right; repeat split; auto; intuition CESem.sem_det.
    Qed.

    Lemma unop_inv:
      forall H b op e ty es,
        CESem.sem_exp b H (Eunop op e ty) es ->
        exists ys,
          CESem.sem_exp b H e ys
          /\ forall n,
            (exists v v',
                ys n = present v
                /\ sem_unop op v (typeof e) = Some v'
                /\ es n = present v')
            \/
            (ys n = absent
             /\ es n = absent).
    Proof.
      intros * Sem.
      interp_str b H e Sem.
      eexists; intuition; eauto.
      specialize (Sem_e n); specialize (Sem n); inv Sem;
        try match goal with H: typeof ?e = _, H': typeof ?e = _ |- _ => rewrite H in H'; inv H' end.
      - left; do 2 eexists; intuition; eauto; CESem.sem_det.
      - right; intuition; auto; CESem.sem_det.
    Qed.

    Lemma binop_inv:
      forall H b op e1 e2 ty es,
        CESem.sem_exp b H (Ebinop op e1 e2 ty) es ->
        exists ys zs,
          CESem.sem_exp b H e1 ys
          /\ CESem.sem_exp b H e2 zs
          /\ forall n,
              (exists v1 v2 v',
                  ys n = present v1
                  /\ zs n = present v2
                  /\ sem_binop op v1 (typeof e1) v2 (typeof e2) = Some v'
                  /\ es n = present v')
              \/
              (ys n = absent
               /\ zs n = absent
               /\ es n = absent).
    Proof.
      intros * Sem.
      interp_str b H e1 Sem.
      interp_str b H e2 Sem.
      do 2 eexists; intuition; eauto.
      specialize (Sem_e1 n); specialize (Sem_e2 n); specialize (Sem n); inv Sem;
        repeat match goal with H: typeof ?e = _, H': typeof ?e = _ |- _ => rewrite H in H'; inv H' end.
      - left; do 3 eexists; intuition; eauto; try CESem.sem_det.
      - right; intuition; auto; CESem.sem_det.
    Qed.

    (** ** Semantics of exps *)

    Ltac use_spec Spec :=
      match goal with
        n: nat |- _ =>
        let m := fresh "m" in
        intro m; repeat rewrite init_from_nth;
        specialize (Spec (m + n));
        repeat match goal with
                 H: _ \/ _ |- _ => destruct H
               end;
        destruct_conjs; firstorder
      end.

    (** State the correspondence for [exp].
        Goes by induction on [exp] and uses the previous inversion lemmas. *)
    Hint Constructors when lift1 lift2.
    Lemma sem_exp_impl_from:
      forall n H b e es,
        CESem.sem_exp b H e es ->
        CoInd.sem_exp (tr_history_from n H) (tr_stream_from n b) e
                       (tr_stream_from n es).
    Proof.
      intros * Sem.
      revert dependent H; revert b es n.
      induction e; intros * Sem; unfold CESem.sem_exp, lift in Sem.

      - constructor.
        apply const_spec; use_spec Sem; inv Sem; auto.

      - constructor.
        apply enum_spec; use_spec Sem; inv Sem; auto.

      - constructor.
        apply sem_var_impl_from.
        intros n'; specialize (Sem n').
        now inv Sem.

      - apply when_inv in Sem as (ys & xs & ? & ? & Spec).
        econstructor; eauto using sem_var_impl_from.
        apply when_spec; use_spec Spec.

      - apply unop_inv in Sem as (ys & ? & Spec).
        econstructor; eauto.
        apply lift1_spec; use_spec Spec.

      - apply binop_inv in Sem as (ys & zs & ? & ? & Spec).
        econstructor; eauto.
        apply lift2_spec.
        intro m; repeat rewrite init_from_nth; specialize (Spec (m + n)).
        repeat match goal with H: _ \/ _ |- _ => destruct H end; destruct_conjs; intuition.
        right; do 3 eexists; intuition; eauto.
    Qed.

    Corollary sem_exp_impl:
      forall H b e es,
        CESem.sem_exp b H e es ->
        CoInd.sem_exp (tr_history H) (tr_stream b) e (tr_stream es).
    Proof. apply sem_exp_impl_from. Qed.
    Hint Resolve sem_exp_impl_from sem_exp_impl.

    (** An inversion principle for lists of [exp]. *)
    Lemma sem_exps_inv:
      forall H b es ess,
        CESem.sem_exps b H es ess ->
        exists ess',
          Forall2 (CESem.sem_exp b H) es ess'
          /\ forall n, ess n = List.map (fun es => es n) ess'.
    Proof.
      intros * Sem.
      exists (interp_exps' b H es); split.
      - eapply interp_exps'_complete; eauto.
      - intro n; specialize (Sem n); induction Sem; simpl; auto.
        f_equal; auto.
        unfold interp_exp; now apply interp_exp_instant_complete.
    Qed.

    (** Generalization for lists of [exp]. *)
    Corollary sem_exps_impl_from:
      forall n H b es ess,
        CESem.sem_exps b H es ess ->
        Forall2 (CoInd.sem_exp (tr_history_from n H) (tr_stream_from n b)) es
                (tr_streams_from n ess).
    Proof.
      intros * Sem.
      apply sem_exps_inv in Sem as (ess' & Sem & Eess').
      assert (length es = length (ess n)) as Length by
          (rewrite Eess', map_length; simpl; eapply Forall2_length; eauto).
      apply Forall2_forall2; split.
      - unfold_tr_streams; rewrite seq_streams_length; simpl; lia.
      - intros; subst.
        rewrite nth_tr_streams_from_nth; try lia.
        apply sem_exp_impl_from.
        eapply (Forall2_forall2_eq _ _ (@eq_refl exp) (eq_str_refl))
          in Sem as (? & Sem).
        + eapply Sem; eauto.
          unfold streams_nth.
          intros k; rewrite Eess'.
          change absent with ((fun es => es k) (fun _ => absent)).
          rewrite map_nth; eauto.
        + unfold CESem.sem_exp; clear.
          intros ?? E ?? E' Sem; subst.
          eapply CESem.lift_eq_str; eauto; reflexivity.
    Qed.

    Corollary sem_exps_impl:
      forall H b es ess,
        CESem.sem_exps b H es ess ->
        Forall2 (CoInd.sem_exp (tr_history H) (tr_stream b)) es (tr_streams ess).
    Proof. apply sem_exps_impl_from. Qed.
    Hint Resolve sem_exps_impl_from sem_exps_impl.

    (** An inversion principle for annotated [exp]. *)
    Lemma sem_aexp_inv:
      forall H b e es ck,
        CESem.sem_aexp b H ck e es ->
        CESem.sem_exp b H e es
        /\ exists bs,
            IStr.sem_clock b H ck bs
            /\ forall n,
              bs n = match es n with
                     | present _ => true
                     | absent => false
                     end.
    Proof.
      intros * Sem; split.
      - intro n; specialize (Sem n); inv Sem; auto.
      - exists (fun n => match es n with
                 | present _ => true
                 | absent => false
                 end); split; intro n; specialize (Sem n); inv Sem; auto.
    Qed.

    (** We deduce from the previous lemmas the correspondence for annotated
        [exp]. *)
    Corollary sem_aexp_impl_from:
      forall n H b e es ck,
        CESem.sem_aexp b H ck e es ->
        CoInd.sem_aexp (tr_history_from n H) (tr_stream_from n b) ck e
                        (tr_stream_from n es).
    Proof.
      cofix Cofix; intros * Sem.
      pose proof Sem as Sem';
        apply sem_aexp_inv in Sem' as (Sem' & bs & Sem_ck & Ebs);
        apply (sem_exp_impl_from n) in Sem';
        apply sem_clock_impl_from with (n:=n) in Sem_ck.
      rewrite (init_from_n es) in *.
      rewrite (init_from_n bs), Ebs in Sem_ck.
      destruct (es n); econstructor; eauto;
        rewrite init_from_tl, tr_history_from_tl;
        apply Cofix; auto.
    Qed.

    Corollary sem_aexp_impl:
      forall H b e es ck,
        CESem.sem_aexp b H ck e es ->
        CoInd.sem_aexp (tr_history H) (tr_stream b) ck e (tr_stream es).
    Proof. apply sem_aexp_impl_from. Qed.
    Hint Resolve sem_aexp_impl_from sem_aexp_impl.

    (** ** cexp level synchronous operators inversion principles *)

    (** An inversion principle for lists of [cexp]. *)
    Lemma sem_cexps_inv:
      forall H b es ess,
        (forall n, Forall2 (CESem.sem_cexp_instant (b n) (H n)) es (ess n)) ->
        exists ess',
          Forall2 (CESem.sem_cexp b H) es ess'
          /\ forall n, ess n = List.map (fun es => es n) ess'.
    Proof.
      intros * Sem.
      exists (interp_cexps' b H es); split.
      - eapply interp_cexps'_complete; eauto.
      - intro n; specialize (Sem n); induction Sem; simpl; auto.
        f_equal; auto.
        unfold interp_cexp; now apply interp_cexp_instant_complete.
    Qed.

    Lemma merge_inv:
      forall H b x tx l ty os,
        CESem.sem_cexp b H (Emerge (x, tx) l ty) os ->
        exists xs ess,
          IStr.sem_var H x xs
          /\ Forall2 (CESem.sem_cexp b H) l ess
          /\
          (forall n,
              (exists b c ess1 es ess2,
                  xs n = present (Venum b)
                  /\ ess = ess1 ++ es :: ess2
                  /\ length ess1 = b
                  /\ es n = present c
                  /\ Forall (fun xs => xs n = absent) (ess1 ++ ess2)
                  /\ os n = present c)
              \/
              (xs n = absent
               /\ Forall (fun xs => xs n = absent) ess
               /\ os n = absent)).
    Proof.
      intros * Sem.
      interp_str b H x Sem.
      assert (forall n, Forall2 (CESem.sem_cexp_instant (b n) (H n)) l (interp_cexps b H l n)) as Seml.
      { intro n; specialize (Sem n); inv Sem.
        - take (Forall _ _) and apply Forall_app in it as (Hes1 & Hes2).
          unfold interp_cexps, lift_interp, interp_cexps_instant.
          rewrite map_app; apply Forall2_app.
          + clear - Hes1; induction Hes1; simpl; constructor; auto.
            erewrite <-interp_cexp_instant_complete; eauto.
          + simpl; constructor.
            * erewrite <-interp_cexp_instant_complete; eauto.
            * clear - Hes2; induction Hes2; simpl; constructor; auto.
              erewrite <-interp_cexp_instant_complete; eauto.
        - take (Forall _ _) and induction it; simpl; constructor; auto.
          erewrite <-interp_cexp_instant_complete; eauto.
      }
      apply sem_cexps_inv in Seml as (ess' & Sem_l & E).
      do 2 eexists; split; eauto; split; eauto.
      intro; specialize (Sem_x n); specialize (Sem n); inv Sem.
      - left; exists (length es1), c.
        apply Forall2_app_inv_l in Sem_l as (ess1 & ess2' & Hess1 & Hess2' & E'); subst.
        inversion Hess2' as [|? es ? ess2 He Hess2]; subst.
        assert (length es1 = length ess1) by (eapply Forall2_length; eauto).
        specialize (E n).
        unfold interp_cexps, lift_interp, interp_cexps_instant in E.
        rewrite ? map_app in E; simpl in E.
        apply app_inv in E as (E1 & E2'); [|rewrite ? map_length; auto].
        inversion E2' as [[E E2]]; clear E2'.
        do 3 eexists; intuition eauto; try CESem.sem_det.
        + erewrite <-E, <-interp_cexp_instant_complete; eauto.
        + apply Forall_app; take (Forall _ _) and apply Forall_app in it as (Sem1 & Sem2); split.
          * clear - E1 Sem1; revert dependent ess1;
              induction Sem1, ess1; simpl in *; try discriminate; constructor; inv E1; auto.
            erewrite <-interp_cexp_instant_complete; eauto.
          * clear - E2 Sem2; revert dependent ess2;
              induction Sem2, ess2; simpl in *; try discriminate; constructor; inv E2; auto.
            erewrite <-interp_cexp_instant_complete; eauto.
      - right; repeat split; auto; try CESem.sem_det.
        take (Forall _ _) and rename it into Sem; clear - Sem E.
        specialize (E n).
        revert dependent ess'; induction Sem, ess'; simpl in *; try discriminate; constructor; inv E; auto.
        erewrite <-interp_cexp_instant_complete; eauto.
    Qed.

    (** An inversion principle for lists of [option cexp]. *)
    Lemma sem_ocexps_inv:
      forall H b es ess e,
        (forall n, Forall2 (fun oe => CESem.sem_cexp_instant (b n) (H n) (or_default e oe)) es (ess n)) ->
        exists ess',
          Forall2 (fun oe => CESem.sem_cexp b H (or_default e oe)) es ess'
          /\ forall n, ess n = List.map (fun es => es n) ess'.
    Proof.
      intros * Sem.
      exists (interp_ocexps' b H e es); split.
      - eapply interp_ocexps'_complete; eauto.
      - intro n; specialize (Sem n); induction Sem; simpl; auto.
        f_equal; auto.
        unfold interp_cexp; now apply interp_cexp_instant_complete.
    Qed.

    Lemma case_inv:
      forall H b e l d os,
        CESem.sem_cexp b H (Ecase e l d) os ->
        exists xs ess,
          CESem.sem_exp b H e xs
          /\ Forall2 (fun oe => CESem.sem_cexp b H (or_default d oe)) l ess
          /\
          (forall n,
              (Forall (fun xs => xs n <> absent) ess
               /\ exists b c es,
                  xs n = present (Venum b)
                  /\ nth_error ess b = Some es
                  /\ es n = present c
                  /\ os n = present c)
              \/
              (xs n = absent
               /\ Forall (fun xs => xs n = absent) ess
               /\ os n = absent)).
    Proof.
      intros * Sem.
      interp_str b H e Sem.
      assert (forall n, Forall2 (fun oe => CESem.sem_cexp_instant (b n) (H n) (or_default d oe))
                                l (interp_ocexps b H d l n)) as Seml.
      { intro n; specialize (Sem n); inv Sem.
        - assert (Forall2 (fun e v => CESem.sem_cexp_instant (b n) (H n) (or_default d e) v)
                          l (List.map present vs)) by now apply Forall2_map_2.
          unfold interp_ocexps, lift_interp.
          erewrite <-interp_ocexps_instant_complete; eauto.
        - take (Forall _ _) and clear - it; induction it; simpl; constructor; auto.
          erewrite <-interp_cexp_instant_complete; eauto.
      }
      apply sem_ocexps_inv in Seml as (ess' & Sem_l & E).
      do 2 eexists; split; eauto; split; eauto.
      intro; specialize (Sem_e n); specialize (Sem n); inv Sem.
      - left.
        specialize (E n).
        unfold interp_ocexps, lift_interp, interp_ocexps_instant in E.
        rewrite ? map_app in E; simpl in E.
        split.
        + revert dependent ess'.
          take (Forall2 _ _ _) and clear - it; induction it, ess';
            inversion_clear 1; constructor; simpl in E; inv E; auto.
          erewrite <-interp_cexp_instant_complete; eauto; discriminate.
        + exists b0, c.
          take (nth_error _ _ = _) and apply nth_error_split in it as (vs1 & vs2 & Nth & Length); subst.
          take (Forall2 _ _ (_ ++ _)) and apply Forall2_app_inv_r in it as (es1 & es2' & Hes1 & Hes2' & ?); subst.
          take (Forall2 _ (_ ++ _) _) and apply Forall2_app_inv_l in it as (ess1 & ess2' & Hess1 & Hess2' & ?); subst.
          apply Forall2_length in Hes1 as L1; apply Forall2_length in Hess1 as L1'.
          rewrite <-L1, L1'.
          rewrite nth_error_app2, Nat.sub_diag; auto.
          inv Hes2'; inv Hess2'; simpl.
          rewrite <-L1', L1.
          eexists; intuition eauto; try CESem.sem_det.
          rewrite ? map_app in E.
          apply app_inv in E as (?& E'); [|now rewrite 2 map_length].
          simpl in E'; inv E'.
          erewrite <-interp_cexp_instant_complete; eauto.
      - right; repeat split; auto; try CESem.sem_det.
        take (Forall _ _) and rename it into Sem; clear - Sem E.
        specialize (E n).
        revert dependent ess'; induction Sem, ess'; simpl in *; try discriminate; constructor; inv E; auto.
        erewrite <-interp_cexp_instant_complete; eauto.
    Qed.

    Lemma exp_inv:
      forall H b le es,
        CESem.sem_cexp b H (Eexp le) es ->
        CESem.sem_exp b H le es.
    Proof.
      intros * Sem n.
      now specialize (Sem n); inv Sem.
    Qed.

    (** [fby] is not a predicate but a function, so we directly state the
        correspondence.  *)
    Lemma fby_impl_from:
      forall n c xs,
        tr_stream_from n (Indexed.fby c xs) ≡
        sfby (Indexed.hold c xs n) (tr_stream_from n xs).
    Proof.
      cofix Cofix; intros.
      rewrite init_from_n; rewrite (init_from_n xs).
      unfold Indexed.fby at 1.
      destruct (xs n) eqn: E.
      - constructor; simpl; auto.
        rewrite Indexed.hold_abs; auto.
      - constructor; simpl; auto.
        erewrite (Indexed.hold_pres v); eauto.
    Qed.

    Corollary fby_impl:
      forall c xs,
      tr_stream (Indexed.fby c xs) ≡ sfby c (tr_stream xs).
    Proof.
      now setoid_rewrite fby_impl_from.
    Qed.

    Fact tr_Stream_eqst {A} : forall (x : stream A),
        CIStr.tr_Stream (tr_stream x) ≈ x.
    Proof.
      unfold tr_stream, tr_stream_from, CIStr.tr_Stream.
      intros x n.
      rewrite ICStr.init_from_nth, Nat.add_0_r.
      reflexivity.
    Qed.

    Lemma reset_impl:
      forall v0 xs rs,
        tr_stream (Indexed.reset v0 xs rs) ≡
        CoInd.reset v0 (tr_stream xs) (tr_stream rs).
    Proof.
      intros *.
      apply ntheq_eqst. intros n.
      unfold tr_stream, tr_stream_from. rewrite init_from_nth, Nat.add_0_r.
      replace (Indexed.reset v0 xs rs n) with
          (Indexed.reset v0 (CIStr.tr_Stream (tr_stream xs)) (CIStr.tr_Stream (tr_stream rs)) n).
      2:{ unfold Indexed.reset.
          rewrite tr_Stream_eqst. destruct (xs n); auto.
          induction n; simpl; rewrite tr_Stream_eqst; auto.
          destruct (rs _); auto.
          rewrite tr_Stream_eqst. destruct (xs _); auto. }
      rewrite <- NLCIStr.reset_impl. reflexivity.
    Qed.

    Corollary reset_fby_impl:
      forall v0 xs rs,
        tr_stream (Indexed.reset v0 (Indexed.fby v0 xs) rs) ≡
        CoInd.reset v0 (sfby v0 (tr_stream xs)) (tr_stream rs).
    Proof.
      intros *.
      rewrite reset_impl, fby_impl. reflexivity.
    Qed.

    (** ** Semantics of cexps *)

    (** State the correspondence for [cexp].
        Goes by induction on [cexp] and uses the previous inversion lemmas. *)
    Hint Constructors merge case.
    Lemma sem_cexp_impl_from:
      forall n H b e es,
        CESem.sem_cexp b H e es ->
        CoInd.sem_cexp (tr_history_from n H) (tr_stream_from n b) e
                       (tr_stream_from n es).
    Proof.
      intros * Sem.
      revert dependent H; revert b es n.
      induction e using cexp_ind2; intros * Sem; unfold CESem.sem_cexp, IStr.lift in Sem.

      - destruct x; apply merge_inv in Sem as (xs & ess & ? & Hess & Spec).
        econstructor; eauto.
        + instantiate (1 := List.map (tr_stream_from n) ess).
          clear Spec.
          take (Forall _ _) and rename it into IH.
          induction Hess; simpl; constructor; inv IH; auto.
        + apply merge_spec.
          intro m; specialize (Spec (m + n)); destruct Spec;
            destruct_conjs; subst; repeat rewrite init_from_nth.
          * right; do 5 eexists; intuition eauto.
            -- rewrite map_app; simpl; reflexivity.
            -- now rewrite map_length.
            -- rewrite init_from_nth; auto.
            -- rewrite <-map_app; apply Forall_map; setoid_rewrite init_from_nth; auto.
          * left; intuition eauto.
            apply Forall_map; setoid_rewrite init_from_nth; auto.

      - apply case_inv in Sem as (xs & ess & ? & Hess & Spec).
        econstructor; eauto.
        + instantiate (1 := List.map (tr_stream_from n) ess).
          clear Spec.
          take (Forall _ _) and rename it into IH.
          induction Hess; simpl; constructor; inv IH; auto.
        + apply case_spec.
          intro m; specialize (Spec (m + n)); destruct Spec;
            destruct_conjs; subst; repeat rewrite init_from_nth.
          * right; do 3 eexists; intuition eauto.
            -- rewrite Forall_map; setoid_rewrite init_from_nth; auto.
            -- erewrite map_nth_error; eauto; reflexivity.
            -- rewrite init_from_nth; auto.
          * left; intuition eauto.
            apply Forall_map; setoid_rewrite init_from_nth; auto.

      - apply exp_inv in Sem; constructor; auto.
    Qed.

    Corollary sem_cexp_impl:
      forall H b e es,
        CESem.sem_cexp b H e es ->
        CoInd.sem_cexp (tr_history H) (tr_stream b) e (tr_stream es).
    Proof. apply sem_cexp_impl_from. Qed.
    Hint Resolve sem_cexp_impl_from sem_cexp_impl.

    (** An inversion principle for annotated [cexp]. *)
    Lemma sem_caexp_inv:
      forall H b e es ck,
        CESem.sem_caexp b H ck e es ->
        CESem.sem_cexp b H e es
        /\ exists bs,
            IStr.sem_clock b H ck bs
            /\ (forall n, bs n = match es n with
                           | present _ => true
                           | absent => false
                           end).
    Proof.
      intros * Sem; split.
      - intro n; specialize (Sem n); inv Sem; auto.
      - exists (fun n => match es n with
                 | present _ => true
                 | absent => false
                 end); split; intro n; specialize (Sem n); inv Sem; auto.
    Qed.

    (** We deduce from the previous lemmas the correspondence for annotated
        [cexp]. *)
    Corollary sem_caexp_impl_from:
      forall n H b e es ck,
        CESem.sem_caexp b H ck e es ->
        CoInd.sem_caexp (tr_history_from n H) (tr_stream_from n b) ck e
                        (tr_stream_from n es).
    Proof.
      cofix Cofix; intros * Sem.
      pose proof Sem as Sem';
        apply sem_caexp_inv in Sem' as (Sem' & bs & Sem_ck & Ebs);
        apply (sem_cexp_impl_from n) in Sem';
        apply sem_clock_impl_from with (n:=n) in Sem_ck.
      rewrite (init_from_n es) in *.
      rewrite (init_from_n bs), Ebs in Sem_ck.
      destruct (es n); econstructor; eauto;
        rewrite init_from_tl, tr_history_from_tl;
        apply Cofix; auto.
    Qed.

    Corollary sem_caexp_impl:
      forall H b e es ck,
        CESem.sem_caexp b H ck e es ->
        CoInd.sem_caexp (tr_history H) (tr_stream b) ck e (tr_stream es).
    Proof. apply sem_caexp_impl_from. Qed.
    Hint Resolve sem_caexp_impl_from sem_caexp_impl.

    (** * RESET CORRESPONDENCE  *)

    (** We state the correspondence for [bools_of]. *)
    Lemma bools_of_impl_from:
      forall n xs rs,
        Indexed.bools_of xs rs ->
        CStr.bools_of (tr_stream_from n xs) (tr_stream_from n rs).
    Proof.
      cofix Cofix; intros * Rst.
      pose proof Rst.
      specialize (Rst n).
      rewrite (init_from_n xs), (init_from_n rs).
      destruct Rst as [(-> & ->)|(? & -> & ->)]; auto using bools_of.
    Qed.

    Corollary bools_of_impl:
      forall xs rs,
        Indexed.bools_of xs rs ->
        CStr.bools_of (tr_stream xs) (tr_stream rs).
    Proof. apply bools_of_impl_from. Qed.

    (** And for [bools_ofs] *)
    Corollary bools_ofs_impl:
      forall xss rs,
        Indexed.bools_ofs xss rs ->
        CStr.bools_ofs (List.map tr_stream xss) (tr_stream rs).
    Proof.
      unfold CStr.bools_ofs, Indexed.bools_ofs.
      intros * (rss&Bools1&Bools2).
      exists (List.map tr_stream rss). split.
      - rewrite Forall2_map_1, Forall2_map_2.
        eapply Forall2_impl_In; [|eauto].
        auto using bools_of_impl.
      - eapply ntheq_eqst.
        intros n. specialize (Bools2 n).
        rewrite disj_str_spec.
        unfold tr_stream, tr_stream_from. rewrite init_from_nth, Nat.add_0_r, Bools2.
        rewrite existsb_map. eapply existsb_ext.
        intros ?. rewrite init_from_nth, Nat.add_0_r; auto.
    Qed.

    (** ** Properties about [count] and [mask] *)

    (** State the correspondance for [count].  *)
    Lemma count_impl_from:
      forall n (r: stream bool),
        count_acc (if r n then IStr.count r n - 1 else IStr.count r n)
                  (tr_stream_from n r)
        ≡ tr_stream_from n (IStr.count r).
    Proof.
      (* cofix-based proof encounter the guardness criterion (Why ??)  *)
      intros; apply ntheq_eqst; intro m.
      unfold Str_nth; revert n; induction m; intro; simpl.
      - destruct (r n) eqn: R; auto.
        apply count_true_ge_1 in R; rewrite Minus.minus_Sn_m; lia.
      - rewrite <-IHm; simpl; destruct (r n) eqn: R; destruct (r (S n));
          try (apply count_true_ge_1 in R; rewrite Minus.minus_Sn_m; auto);
          try (rewrite Nat.sub_succ, Nat.sub_0_r); auto.
    Qed.

    (** Generalizing is too intricate: we can use the generalized lemma above to
        deduce this one which states the correspondence for [mask]. *)
    Corollary mask_impl:
      forall k (r: stream bool) xss,
        wf_streams xss ->
        EqSts (tr_streams (IStr.mask k r xss))
              (List.map (CStr.mask k (tr_stream r)) (tr_streams xss)).
    Proof.
      intros * Const; unfold tr_streams, tr_stream.
      apply Forall2_forall2; split.
      - rewrite map_length, 2 tr_streams_from_length, mask_length; auto.
      - intros d1 d2 n' xs1 xs2 Len Nth1 Nth2.
        rewrite tr_streams_from_length in Len.
        rewrite <-Nth1, <-Nth2.
        assert (n' < length (tr_streams_from 0 xss)) by
            (rewrite mask_length in Len; auto;
             rewrite tr_streams_from_length; auto).
        rewrite map_nth' with (d':=d2), nth_tr_streams_from_nth; auto.
        rewrite mask_length in Len; auto.
        rewrite nth_tr_streams_from_nth; auto.
        unfold CStr.mask, IStr.mask.
        apply ntheq_eqst; intro m.
        unfold nth_tr_streams_from.
        rewrite init_from_nth, mask_nth, init_from_nth.
        unfold CStr.count, streams_nth.
        pose proof (count_impl_from 0 r) as Count.
        assert ((if r 0 then IStr.count r 0 - 1 else IStr.count r 0) = 0) as E
            by (simpl; destruct (r 0); auto).
        rewrite E in Count; rewrite Count, init_from_nth, Nat.eqb_sym.
        destruct (IStr.count r (m + 0) =? k); auto.
        apply nth_all_absent.
    Qed.

    (** * FINAL LEMMAS *)

    (** Correspondence for [clocks_of], used to give a base clock for node
        applications. *)
    Lemma tr_clocks_of_from:
      forall n xss,
        wf_streams xss ->
        CStr.clocks_of (tr_streams_from n xss) ≡ tr_stream_from n (CESem.clock_of xss).
    Proof.
      cofix Cofix; intros.
      constructor; simpl.
      - unfold CESem.clock_of, CESem.clock_of_instant.
        destruct (existsb (fun v : svalue => v <>b absent) (xss n)) eqn: E.
        + assert (forall v, v <> absent <-> (v <>b absent) = true)
            by (unfold nequiv_decb; setoid_rewrite Bool.negb_true_iff;
                setoid_rewrite not_equiv_decb_equiv; reflexivity).
          rewrite <-Exists_existsb with (P := fun v => hd v <> absent); auto.
          rewrite <-Exists_existsb with (P := fun v => v <> absent) in E; auto.
          apply Exists_In_tr_streams_from_hd in E; auto.
        + unfold nequiv_decb in *.
          apply existsb_Forall_neg, forallb_Forall in E.
          apply existsb_Forall_neg, forallb_Forall, Forall_forall.
          intros * Hin.
          eapply Forall_In_tr_streams_from_hd in E; eauto.
      - rewrite tr_streams_from_tl; auto.
    Qed.

    Corollary tr_clocks_of:
      forall xss,
        wf_streams xss ->
        CStr.clocks_of (tr_streams xss) ≡ tr_stream (CESem.clock_of xss).
    Proof. apply tr_clocks_of_from. Qed.

    Lemma sem_clocked_var_inv:
      forall b H x xs ck,
        IStr.sem_var H x xs ->
        CESem.sem_clocked_var b H x ck ->
        exists bs,
          IStr.sem_clock b H ck bs
          /\ (forall n, bs n = true <-> xs n <> absent).
    Proof.
      intros * Var Sem.
      assert (IStr.sem_clock b H ck (interp_clock b H ck)) as SemCk.
      { intro n; specialize (Sem n); specialize (Var n); destruct Sem as (Sem & Sem').
        unfold interp_clock, lift_interp.
        destruct (xs n).
        - erewrite <-interp_clock_instant_complete; eauto; apply Sem'; auto.
        - erewrite <-interp_clock_instant_complete; eauto; apply Sem; eauto.
      }
      exists (interp_clock b H ck); split; auto.
      intro n; specialize (Var n); specialize (SemCk n); specialize (Sem n);
        destruct Sem as (Sem & Sem').
      split.
      - intros E E'.
        rewrite E in SemCk; apply Sem in SemCk as (?&?).
        rewrite E' in Var.
        eapply sem_var_instant_det in Var; eauto; discriminate.
      - intro E; apply not_absent_present in E as (?& E).
        rewrite E in Var.
        assert (sem_clock_instant (b n) (H n) ck true)
          by (apply Sem; eauto).
        eapply sem_clock_instant_det; eauto.
    Qed.

    Lemma sem_clocked_var_impl_from:
      forall n H b x xs ck,
        IStr.sem_var H x xs ->
        CESem.sem_clocked_var b H x ck ->
        CoInd.sem_clocked_var (tr_history_from n H) (tr_stream_from n b) x ck.
    Proof.
      intros * Var Sem; eapply sem_clocked_var_inv in Sem as (bs & Clock & Spec); eauto.
      apply sem_var_impl_from with (n := n) in Var;
        apply sem_clock_impl_from with (n := n) in Clock.
      split; eauto.
      intros * Var'.
      eapply sem_var_det in Var; eauto.
      eexists; split; eauto.
      rewrite Var.
      clear - Spec.
      generalize n; clear n.
      cofix COFIX; intros.
      rewrite init_from_n, (init_from_n bs).
      destruct (xs n) eqn: E.
      - assert (bs n = false) as ->
            by (rewrite <-Bool.not_true_iff_false, Spec; auto).
        constructor; auto.
      - assert (bs n = true) as ->
            by (apply Spec; intro; congruence).
        constructor; auto.
    Qed.

    Corollary sem_clocked_var_impl:
      forall H b x xs ck,
        IStr.sem_var H x xs ->
        CESem.sem_clocked_var b H x ck ->
        CoInd.sem_clocked_var (tr_history H) (tr_stream b) x ck.
    Proof. apply sem_clocked_var_impl_from. Qed.

    Lemma sem_clocked_vars_impl:
      forall H b xs xss,
        CESem.sem_vars H (List.map fst xs) xss ->
        CESem.sem_clocked_vars b H xs ->
        CoInd.sem_clocked_vars (tr_history H) (tr_stream b) xs.
    Proof.
      unfold CESem.sem_clocked_vars; intros * Vars Sem.
      apply Forall_forall; intros (x, ck) Hin.
      apply sem_vars_inv in Vars.
      pose proof Hin as Hin'.
      apply in_map with (f := fst) in Hin.
      eapply Forall2_in_left in Vars as (?&?&?); eauto.
      eapply sem_clocked_var_impl; eauto.
      intro n; specialize (Sem n).
      eapply Forall_forall in Sem; eauto.
    Qed.

    Lemma sem_clocked_vars_impl':
      forall H b xs xss,
        Forall2 (IStr.sem_var H) (List.map fst xs) xss ->
        CESem.sem_clocked_vars b H xs ->
        CoInd.sem_clocked_vars (tr_history H) (tr_stream b) xs.
    Proof.
      unfold CESem.sem_clocked_vars; intros * Vars Sem.
      apply Forall_forall; intros (x, ck) Hin.
      pose proof Hin as Hin'.
      apply in_map with (f := fst) in Hin.
      eapply Forall2_in_left in Vars as (?&?&?); eauto.
      eapply sem_clocked_var_impl; eauto.
      intro n; specialize (Sem n).
      eapply Forall_forall in Sem; eauto.
    Qed.
    Hint Resolve sem_clocked_vars_impl'.

    (** The final theorem stating the correspondence for nodes applications.
        We have to use a custom mutually recursive induction scheme [sem_node_mult]. *)
    Hint Constructors CoInd.sem_equation.
    Theorem implies:
      forall f xss oss,
        Indexed.sem_node G f xss oss ->
        CoInd.sem_node G f (tr_streams xss) (tr_streams oss).
    Proof.
      induction 1 as [|???????????????? IH| |??????????? Heqs IH]
                       using Indexed.sem_node_mult with
          (P_equation := fun b H e =>
                           Indexed.sem_equation G b H e ->
                           CoInd.sem_equation G (tr_history H) (tr_stream b) e);
        eauto.

      - econstructor; eauto.
        3:eapply bools_ofs_impl; eauto.
        + rewrite tr_clocks_of; eauto.
          eapply wf_streams_mask.
          intro k; destruct (IH k) as (Sem &?).
          apply Indexed.sem_node_wf in Sem as (?&?); eauto.
        + rewrite Forall2_map_2. eapply Forall2_impl_In; [|eauto]; intros.
          eapply sem_var_impl; eauto.
        + intro k; destruct (IH k) as (?&?).
          rewrite <- 2 mask_impl; eauto;
            eapply wf_streams_mask; intro n'; destruct (IH n') as (Sem &?);
              apply Indexed.sem_node_wf in Sem as (?&?); eauto.

      - econstructor; eauto; subst.
        2:eapply bools_ofs_impl; eauto.
        + rewrite Forall2_map_2. eapply Forall2_impl_In; [|eauto]; intros.
          eapply sem_var_impl; eauto.
        + rewrite <-reset_fby_impl; eauto.

      - subst.
        CESem.assert_const_length xss.
        econstructor; eauto.
        + rewrite tr_clocks_of; eauto.
          eapply sem_clocked_vars_impl; eauto.
          rewrite map_fst_idck; eauto.
        + apply Forall_forall; intros * Hin.
          rewrite tr_clocks_of; auto.
          eapply Forall_forall in Heqs; eapply Forall_forall in IH; eauto.
    Qed.

  End Global.

End NLINDEXEDTOCOIND.
