Require Import Coq.FSets.FMapPositive.
Require Import PArith.
Require Import Logic.FunctionalExtensionality.

Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.Clocks.
Require Import Velus.RMemory.

Require Import Velus.NLustre.NLExprSyntax.
Require Import Velus.NLustre.NLExprSemantics.

Require Import Velus.NLustre.
Require Import Velus.SyBloc.

Require Import Velus.NLustreToSyBloc.Translation.

Require Import List.
Import List.ListNotations.

Open Scope list.
Open Scope nat.

Module Type CORRECTNESS
       (Import Ids      : IDS)
       (Import Op       : OPERATORS)
       (Import OpAux    : OPERATORS_AUX       Op)
       (Import Clks     : CLOCKS          Ids)
       (Import ExprSyn  : NLEXPRSYNTAX        Op)
       (Import Str      : STREAM              Op OpAux)
       (Import ExprSem  : NLEXPRSEMANTICS Ids Op OpAux Clks ExprSyn Str)
       (Import NL       : NLUSTRE         Ids Op OpAux Clks ExprSyn Str ExprSem)
       (Import SB       : SYBLOC          Ids Op OpAux Clks ExprSyn Str ExprSem NL.Syn NL.IsF)
       (Import Trans    : TRANSLATION     Ids Op       Clks ExprSyn             NL.Syn SB.Syn NL.Mem).

  Lemma In_snd_gather_eqs_Is_node_in:
    forall eqs i f,
      In (i, f) (snd (gather_eqs eqs)) ->
      Is_node_in f eqs.
  Proof.
    unfold gather_eqs.
    intro.
    generalize (@nil (ident * const)).
    induction eqs as [|[]]; simpl; try contradiction; intros ** Hin; auto.
    - right; eapply IHeqs; eauto.
    - destruct i.
      + right; eapply IHeqs; eauto.
      + apply In_snd_fold_left_gather_eq in Hin as [Hin|Hin].
        * destruct Hin as [E|]; try contradiction; inv E.
          left; constructor.
        * right; eapply IHeqs; eauto.
    - right; eapply IHeqs; eauto.
  Qed.

  Lemma Ordered_nodes_blocks:
    forall G,
      Ordered_nodes G ->
      Ordered_blocks (translate G).
  Proof.
    induction 1 as [|??? IH NodeIn Nodup]; simpl; constructor; auto.
    - destruct nd; simpl in *; clear - NodeIn.
      apply Forall_forall; intros ** Hin.
      destruct x; apply In_snd_gather_eqs_Is_node_in in Hin.
      apply NodeIn in Hin as [? E]; split; auto.
      clear NodeIn.
      induction nds as [|n].
      + inv E.
      + simpl; destruct (ident_eqb (n_name n) i0) eqn: Eq.
        * inv E; eauto.
        * inv E; eauto.
          rewrite ident_eqb_refl in Eq; discriminate.
    - clear - Nodup.
      induction Nodup; simpl; auto.
  Qed.

  Lemma msem_eqs_reset_lasts:
    forall G bk H M M' n,
      memory_closed_n M (n_eqs n) ->
      Forall (msem_equation G bk H M M') (n_eqs n) ->
      reset_lasts (translate_node n) (M 0).
  Proof.
    intros ** Closed Heqs ?? Hin.
    destruct n; simpl in *.
    unfold gather_eqs in *.
    clear - Heqs Hin.
    revert Hin; generalize (@nil (ident * ident)).
    induction n_eqs0 as [|[] ? IH]; simpl in *; intros; try contradiction;
      inversion_clear Heqs as [|?? Heq]; inv Heq; eauto.
    - destruct i; try discriminate; eauto.
    - destruct i; try discriminate; eauto.
    - apply In_fst_fold_left_gather_eq in Hin as [Hin|]; eauto.
      destruct Hin as [E|]; try contradiction; inv E.
      match goal with H: mfby _ _ _ _ _ _ |- _ => destruct H as (?&?) end; auto.
  Qed.

  Lemma msem_eqs_In_snd_gather_eqs_spec:
    forall eqs G bk H M M' x f,
      Forall (msem_equation G bk H M M') eqs ->
      In (x, f) (snd (gather_eqs eqs)) ->
      exists xss Mx Mx' yss,
        (msem_node G f xss Mx Mx' yss
         \/ exists r, msem_reset G f r xss Mx Mx' yss)
        /\ sub_inst_n x M Mx.
  Proof.
    unfold gather_eqs.
    intro; generalize (@nil (ident * const)).
    induction eqs as [|[]]; simpl; intros ** Heqs Hin;
      inversion_clear Heqs as [|?? Heq];
      try inversion_clear Heq as [|????????????? Hd|???????????????? Hd|];
      try contradiction; eauto.
    - destruct i; try discriminate.
      apply In_snd_fold_left_gather_eq in Hin as [Hin|]; eauto.
      destruct Hin as [E|]; try contradiction; inv E; inv Hd.
      do 4 eexists; split; eauto.
    - destruct i; try discriminate.
      apply In_snd_fold_left_gather_eq in Hin as [Hin|]; eauto.
      destruct Hin as [E|]; try contradiction; inv E; inv Hd.
      do 4 eexists; split; eauto.
  Qed.

  Lemma msem_node_initial_state:
    forall G f xss M M' yss,
      Ordered_nodes G ->
      msem_node G f xss M M' yss ->
      initial_state (translate G) f (M 0).
  Proof.
    induction G as [|node ? IH].
    inversion 2;
      match goal with Hf: find_node _ [] = _ |- _ => inversion Hf end.
    intros ** Hord Hsem.
    assert (Hsem' := Hsem).
    inversion_clear Hsem' as [???????? Clock Hfind Ins ????? Heqs Closed].
    pose proof (find_node_not_Is_node_in _ _ _ Hord Hfind) as Hnini.
    pose proof Hord; inversion_clear Hord as [|??? NodeIn].
    pose proof Hfind as Hfind'.
    simpl in Hfind.
    destruct (ident_eqb node.(n_name) f) eqn:Hnf.
    - inversion Hfind; subst n.
      apply find_node_translate in Hfind' as (?&?&Hfind'&?); subst.
      pose proof Hfind';
        simpl in Hfind'; rewrite Hnf in Hfind'; inv Hfind'.
      eapply msem_equations_cons in Heqs; eauto.
      econstructor; eauto.
      + eapply msem_eqs_reset_lasts; eauto.
      + intros ** Hin.
        destruct node; simpl in *.
        edestruct msem_eqs_In_snd_gather_eqs_spec
          as (?& Mx &?&?& [Node|(rs & Reset)] & Sub); eauto.
        inversion_clear Reset as [?????? Nodes].
        destruct (Nodes (if rs 0 then pred (count rs 0) else count rs 0))
          as (M0 &?& Node & Mmask &?).
        apply IH in Node; auto.
        specialize (Mmask 0); specialize (Sub 0).
        rewrite Mmask in Sub.
        * eexists; split; eauto.
        * simpl; cases.
    - assert (n_name node <> f) by now apply ident_eqb_neq.
      eapply msem_node_cons in Hsem; eauto.
      simpl; rewrite <-initial_state_other; eauto.
  Qed.

  Definition sem_equations_n
             (P: program) (bk: stream bool) (H: history)
             (E: stream state) (T: stream transient_states) (E': stream state)
             (eqs: list equation) :=
    forall n, Forall (sem_equation P (bk n) (restr_hist H n) (E n) (T n) (E' n)) eqs.

  Definition sem_block_n
             (P: program) (f: ident)
             (E: stream state) (xss yss: stream (list value)) (E': stream state) :=
    forall n, sem_block P f (E n) (xss n) (yss n) (E' n).

  Definition add_n (x: ident) (Mx: stream state) (I: stream transient_states) :=
    fun n => Env.add x (Mx n) (I n).

  Lemma sem_equations_n_add_n:
    forall P eqs bk H S S' Is x Sx,
      sem_equations_n P bk H S Is S' eqs ->
      (forall k, ~ Is_state_in x k eqs) ->
      sem_equations_n P bk H S (add_n x Sx Is) S' eqs.
  Proof.
    induction eqs as [|eq eqs]; intros ** Sem Notin n; constructor.
    - specialize (Sem n); inversion_clear Sem as [|?? Sem'].
      inv Sem'; eauto using sem_equation.
      + econstructor; eauto.
        unfold add_n; rewrite Env.gso; auto.
        intro E; eapply Notin; rewrite E; do 2 constructor.
      + econstructor; eauto.
        unfold add_n; rewrite Env.gso; auto.
        intro E; eapply Notin; rewrite E; do 2 constructor.
    - apply IHeqs.
      + intro n'; specialize (Sem n'); inv Sem; auto.
      + apply not_Is_state_in_cons in Notin as []; auto.
  Qed.

  Inductive translate_eqn_nodup_states: NL.Syn.equation -> list equation -> Prop :=
    | TrNodupEqDef:
        forall x ck e eqs,
          translate_eqn_nodup_states (NL.Syn.EqDef x ck e) eqs
    | TrNodupEqApp:
        forall xs ck f es r eqs x,
          hd_error xs = Some x ->
          (forall k, ~ Is_state_in x k eqs) ->
          translate_eqn_nodup_states (EqApp xs ck f es r) eqs
    | TrNodupEqFby:
        forall x ck c e eqs,
          translate_eqn_nodup_states (EqFby x ck c e) eqs.

  Inductive memory_closed_rec: global -> ident -> memory val -> Prop :=
    memory_closed_rec_intro:
      forall G f M n,
        find_node f G = Some n ->
        (forall x, find_val x M <> None -> In x (gather_mems n.(n_eqs))) ->
        (forall i M', find_inst i M = Some M' ->
              exists f',
                In (i, f') (gather_insts n.(n_eqs))
                /\ memory_closed_rec G f' M') ->
        memory_closed_rec G f M.

  Definition memory_closed_rec_n (G: global) (f: ident) (M: memories) : Prop :=
    forall n, memory_closed_rec G f (M n).

  Lemma memory_closed_rec_other:
    forall M G f node,
      Ordered_nodes (node :: G) ->
      node.(n_name) <> f ->
      (memory_closed_rec (node :: G) f M
       <-> memory_closed_rec G f M).
  Proof.
    induction M as [? IH] using memory_ind'; unfold sub_inst in *.
    split; inversion_clear 1 as [???? Find ? Insts].
    - apply find_node_other in Find; auto.
      econstructor; eauto.
      intros ** Find'; pose proof Find';
        apply Insts in Find' as (?& Hin & Closed).
      erewrite IH in Closed; eauto.
      rewrite <-gather_eqs_snd_spec in Hin.
      apply In_snd_gather_eqs_Is_node_in in Hin.
      intro; subst; contradict Hin.
      eapply find_node_later_not_Is_node_in; eauto.
    - pose proof Find; eapply find_node_other in Find; eauto.
      econstructor; eauto.
      intros ** Find'; pose proof Find';
        apply Insts in Find' as (?& Hin & Closed).
      erewrite <-IH in Closed; eauto.
      rewrite <-gather_eqs_snd_spec in Hin.
      apply In_snd_gather_eqs_Is_node_in in Hin.
      intro; subst; contradict Hin.
      eapply find_node_later_not_Is_node_in; eauto.
  Qed.

  Lemma memory_closed_rec_n_other:
    forall M G f node,
      Ordered_nodes (node :: G) ->
      node.(n_name) <> f ->
      (memory_closed_rec_n (node :: G) f M
       <-> memory_closed_rec_n G f M).
  Proof.
    split; intros Closed n; specialize (Closed n).
    - apply memory_closed_rec_other in Closed; auto.
    - apply memory_closed_rec_other; auto.
  Qed.

  Lemma msem_equations_memory_closed_rec:
    forall eqs G bk H M M' n x f Mx,
      (forall f xss M M' yss,
          msem_node G f xss M M' yss ->
          memory_closed_rec_n G f M) ->
      Forall (msem_equation G bk H M M') eqs ->
      find_inst x (M n) = Some Mx ->
      In (x, f) (gather_insts eqs) ->
      memory_closed_rec G f Mx.
  Proof.
    unfold gather_insts, concatMap.
    induction eqs as [|eq]; simpl; intros ** IH Heqs Find Hin;
      inversion_clear Heqs as [|?? Heq]; try contradiction.
    apply in_app in Hin as [Hin|]; eauto.
    destruct eq; simpl in Hin; try contradiction.
    destruct i; try contradiction.
    inversion_clear Hin as [E|]; try contradiction; inv E.
    inversion_clear Heq as [|????????????? Hd Sub ??? Node|
                            ???????????????? Hd Sub ????? Rst|];
      unfold sub_inst_n, sub_inst in Sub;
      inv Hd; rewrite Sub in Find; inv Find.
    - eapply IH; eauto.
    - inversion_clear Rst as [?????? Nodes].
      specialize (Nodes (if rs n then pred (count rs n) else count rs n));
        destruct Nodes as (?&?& Node & Mask &?).
      apply IH in Node.
      rewrite Mask; auto.
      cases_eqn Hr; apply count_true_ge_1 in Hr.
      erewrite <-Lt.S_pred; eauto.
  Qed.

  Lemma msem_equations_memory_closed_rec':
    forall eqs G bk H M M' n x f Mx,
      (forall f xss M M' yss,
          msem_node G f xss M M' yss ->
          memory_closed_rec_n G f M') ->
      Forall (msem_equation G bk H M M') eqs ->
      find_inst x (M' n) = Some Mx ->
      In (x, f) (gather_insts eqs) ->
      memory_closed_rec G f Mx.
  Proof.
    unfold gather_insts, concatMap.
    induction eqs as [|eq]; simpl; intros ** IH Heqs Find Hin;
      inversion_clear Heqs as [|?? Heq]; try contradiction.
    apply in_app in Hin as [Hin|]; eauto.
    destruct eq; simpl in Hin; try contradiction.
    destruct i; try contradiction.
    inversion_clear Hin as [E|]; try contradiction; inv E.
    inversion_clear Heq as [|????????????? Hd ? Sub ?? Node|
                            ???????????????? Hd ? Sub ???? Rst|];
      unfold sub_inst_n, sub_inst in Sub;
      inv Hd; rewrite Sub in Find; inv Find.
    - eapply IH; eauto.
    - inversion_clear Rst as [?????? Nodes].
      specialize (Nodes (count rs n)); destruct Nodes as (?&?& Node &?& Mask).
      apply IH in Node.
      rewrite Mask; auto.
  Qed.

  Lemma msem_node_memory_closed_rec_n:
    forall G f xss M M' yss,
      Ordered_nodes G ->
      msem_node G f xss M M' yss ->
      memory_closed_rec_n G f M /\ memory_closed_rec_n G f M'.
  Proof.
    induction G as [|node]; intros ????? Ord;
      inversion_clear 1 as [????????? Find ?????? Heqs Closed Closed'];
      try now inv Find.
    pose proof Find; simpl in Find.
    destruct (ident_eqb node.(n_name) f) eqn:Eq.
    - inv Find.
      split; econstructor; eauto.
      + apply Closed.
      + intros ** Find_i.
        assert (exists f', In (i, f') (gather_insts (n_eqs n))) as (f' & Hin)
            by (eapply InMembers_In, Closed, not_None_is_Some; eauto).
        eexists; split; eauto.
        assert (f' <> n.(n_name)).
        { rewrite <-gather_eqs_snd_spec in Hin.
          apply In_snd_gather_eqs_Is_node_in in Hin.
          intro; subst; contradict Hin; eapply find_node_not_Is_node_in; eauto.
        }
        apply memory_closed_rec_other; auto.
        assert (~ Is_node_in (n_name n) (n_eqs n))
          by (eapply find_node_not_Is_node_in; eauto).
        apply msem_equations_cons in Heqs; auto.
        inv Ord.
        eapply msem_equations_memory_closed_rec; eauto.
        intros; edestruct IHG; eauto.
      + apply Closed'.
      + intros ** Find_i.
        assert (exists f', In (i, f') (gather_insts (n_eqs n))) as (f' & Hin)
            by (eapply InMembers_In, Closed', not_None_is_Some; eauto).
        eexists; split; eauto.
        assert (f' <> n.(n_name)).
        { rewrite <-gather_eqs_snd_spec in Hin.
          apply In_snd_gather_eqs_Is_node_in in Hin.
          intro; subst; contradict Hin; eapply find_node_not_Is_node_in; eauto.
        }
        apply memory_closed_rec_other; auto.
        assert (~ Is_node_in (n_name n) (n_eqs n))
          by (eapply find_node_not_Is_node_in; eauto).
        apply msem_equations_cons in Heqs; auto.
        inv Ord.
        eapply msem_equations_memory_closed_rec'; eauto.
        intros; edestruct IHG; eauto.
    - apply ident_eqb_neq in Eq.
      assert (~ Is_node_in (n_name node) (n_eqs n))
        by (eapply find_node_later_not_Is_node_in; eauto).
      apply msem_equations_cons in Heqs; auto.
      split; apply memory_closed_rec_n_other; auto; inv Ord;
        edestruct IHG; eauto.
  Qed.

  Lemma memory_closed_rec_state_closed:
    forall M G f,
      Ordered_nodes G ->
      memory_closed_rec G f M ->
      state_closed (translate G) f M.
  Proof.
    induction M as [? IH] using memory_ind'.
    intros ** Ord Closed; inversion_clear Closed as [???? Find ? Insts].
    apply find_node_translate in Find as (?&?&?&?); subst.
    econstructor; eauto; simpl.
    - intros ** ??; rewrite gather_eqs_fst_spec; auto.
    - unfold sub_inst in *.
      intros ** Find; pose proof Find as Find'.
      apply Insts in Find as (?& Hin & Closed).
      rewrite <-gather_eqs_snd_spec in Hin.
      eexists; split; eauto.
      eapply IH in Closed; eauto.
      apply Ordered_nodes_blocks in Ord.
      eapply state_closed_find_block_other; eauto.
  Qed.

  Lemma transient_states_closed_add:
    forall P insts I x f M,
      transient_states_closed P insts I ->
      state_closed P f M ->
      ~ InMembers x insts ->
      transient_states_closed P ([(x, f)] ++ insts) (Env.add x M I).
  Proof.
    intros ** Trans Closed Notin.
    apply Forall_app; split.
    - constructor; auto.
      setoid_rewrite Env.gss; inversion 1; subst; auto.
    - induction Trans as [|(y,?) ? Closed'];
        try apply NotInMembers_cons in Notin as (); constructor; auto.
      intros ** Find; apply Closed'.
      rewrite Env.gso in Find; auto.
  Qed.

  Lemma equation_correctness:
    forall G eq eqs bk H M M' Is vars insts,
      (forall f xss M M' yss,
          msem_node G f xss M M' yss ->
          sem_block_n (translate G) f M xss yss M') ->
      Ordered_nodes G ->
      wc_equation G vars eq ->
      Forall (clock_match bk H) vars ->
      translate_eqn_nodup_states eq eqs ->
      (forall n, transient_states_closed (translate G) insts (Is n)) ->
      (forall x, InMembers x insts -> exists k, Is_state_in x k eqs) ->
      msem_equation G bk H M M' eq ->
      sem_equations_n (translate G) bk H M Is M' eqs ->
      exists Is',
        sem_equations_n (translate G) bk H M Is' M' (translate_eqn eq ++ eqs)
        /\ forall n, transient_states_closed (translate G) (gather_inst_eq eq ++ insts) (Is' n).
  Proof.
    intros ** IHnode Hord WC ClkM TrNodup Closed SpecInsts Heq Heqs.
    destruct Heq as [|?????????????????? Node|
                     ????????????????????? Var Hr Reset|
                     ?????????? Arg Var Mfby];
      inversion_clear TrNodup as [|???????? Notin|]; simpl.

    - eexists; split; eauto.
      do 2 (econstructor; eauto).

    - destruct xs; try discriminate.
      match goal with
      | H: hd_error ?l = Some x,
           H': hd_error ?l = _ |- _ =>
        rewrite H' in H; inv H; simpl in H'; inv H'
      end.
      exists (add_n x Mx Is); split.
      + constructor; auto.
        *{ econstructor; eauto.
           - eexists; split; eauto; reflexivity.
           - apply Env.gss.
           - now apply IHnode.
         }
        * apply sem_equations_n_add_n; auto.
      + intro; apply transient_states_closed_add; auto.
        * eapply memory_closed_rec_state_closed; eauto;
            apply msem_node_memory_closed_rec_n in Node as (); eauto.
        * intro Hin; apply SpecInsts in Hin as (); eapply Notin; eauto.

    - destruct xs; try discriminate.
      match goal with
      | H: hd_error ?l = Some x,
           H': hd_error ?l = _ |- _ =>
        rewrite H' in H; inv H; simpl in H'; inv H'
      end.
      assert (forall Mx, sem_equations_n (translate G) bk H M (add_n x Mx Is) M' eqs) as Heqs'
          by now intro; apply sem_equations_n_add_n.
      assert (clock_match bk H (y, ck)) as Cky
          by (eapply Forall_forall; eauto; inv WC; eauto).
      (* pose proof (msem_reset_spec Hord Reset) as Spec. *)
      exists (fun n => Env.add x (if rs n then Mx 0 else Mx n) (Is n)); split;
        intro;
        inversion_clear Reset as [?????? Nodes](* ; *)
        (* destruct (Nodes (if rs n then pred (count rs n) else count rs n)) *)
        (*   as (Mn & Mn' & Node_n & Mmask_n & Mmask'_n), *)
        (*      (Nodes (count rs 0)) *)
        (*     as (M0 & M0' & Node_0 & Mmask_0 & Mmask'_0) *).
      + destruct (rs n) eqn: Hrst.
        *{ destruct (Nodes (if rs 0 then pred (count rs 0) else count rs 0))
             as (M0 & M0' & Node_0 & Mmask_0 & Mmask'_0).
           destruct (Nodes (count rs n)) as (Mn & Mn' & Node_n & Mmask_n & Mmask'_n).
           assert (Env.find x (Env.add x (Mx 0) (Is n)) = Some (Mx 0))
             by apply Env.gss.
           specialize (Var n); specialize (Hr n); specialize (Cky n); simpl in Cky.
           specialize (Heqs' (fun n => Mx 0) n).
           rewrite Hrst in Hr.
           destruct (ys n) eqn: E'; try discriminate.
           do 2 (econstructor; eauto using sem_equation).
           - eapply Son; eauto.
             destruct Cky as [[]|(?&?&?)]; auto.
             assert (present c = absent) by sem_det; discriminate.
           - simpl; rewrite Mmask_0.
             + eapply msem_node_initial_state; eauto.
             + simpl; cases.
           - econstructor; eauto.
             + discriminate.
             + apply IHnode in Node_n.
               specialize (Node_n n).
               rewrite 2 mask_transparent, <-Mmask'_n in Node_n; auto.


                 simpl in *.
                 destruct (rs 0); simpl in *.  admit.
                 SearchAbout count. admit.
         }
        *{ destruct (Nodes (count rs n)) as (Mn & Mn' & Node_n & Mmask_n & Mmask'_n).
           apply IHnode in Node_n.
           specialize (Node_n n); specialize (Mmask_n n); specialize (Mmask'_n n).
           rewrite 2 mask_transparent, <-Mmask_n, <-Mmask'_n in Node_n; auto.
           specialize (Var n); specialize (Hr n); specialize (Cky n); simpl in Cky.
           specialize (Heqs' Mx n).
           assert (Env.find x (Env.add x (Mx n) (Is n)) = Some (Mx n))
             by apply Env.gss.
           destruct (ys n) eqn: E'.
           - do 2 (econstructor; eauto using sem_equation).
             + apply Son_abs1; auto.
               destruct Cky as [[]|(c &?&?)]; auto.
               assert (present c = absent) by sem_det; discriminate.
             + simpl; eexists; split; eauto; reflexivity.
             + econstructor; eauto.
               discriminate.
           - rewrite Hrst in Hr.
             do 2 (econstructor; eauto using sem_equation).
             + change true with (negb false).
               eapply Son_abs2; eauto.
               destruct Cky as [[]|(?&?&?)]; auto.
               assert (present c = absent) by sem_det; discriminate.
             + simpl; eexists; split; eauto; reflexivity.
             + econstructor; eauto.
               discriminate.
         }
      + apply transient_states_closed_add; auto.
        * apply memory_closed_rec_state_closed; auto.
          rewrite Mmask_0, Mmask_n; auto.
          specialize (Spec n); destruct (rs n);
            apply msem_node_memory_closed_rec_n in Node_n as ();
            apply msem_node_memory_closed_rec_n in Node_0 as (); auto.
        * intro Hin; apply SpecInsts in Hin as (); eapply Notin; eauto.

          destruct (rs n) eqn: E.
        *{ specialize (Heqs' (fun n => Mx 0) n).
           assert (Env.find x (Env.add x (Mx 0) (Is n)) = Some (Mx 0))
             by apply Env.gss.
           constructor; auto; [|constructor; auto].
           - destruct (ys n); try discriminate.
             econstructor; eauto.
             + eapply Son; eauto.
               destruct Cky as [[]|(?&?&?)]; auto.
               assert (present c = absent) by sem_det; discriminate.
             + simpl; rewrite Mmask_0; auto.
             eapply msem_node_initial_state; eauto.
           - eapply SEqCall with (Is := Mx 0); eauto.
             + congruence.
             + eapply sem_block_equal_memory; eauto; reflexivity.   (* TODO: fix rewriting here? *)
         }
        *{ specialize (Heqs' Mx n).
           assert (Env.find x (Env.add x (Mx n) (Is n)) = Some (Mx n))
             by apply Env.gss.
           destruct (ys n) eqn: E'.
           - do 2 (econstructor; eauto using sem_equation).
             + apply Son_abs1; auto.
               destruct Cky as [[]|(c &?&?)]; auto.
               assert (present c = absent) by sem_det; discriminate.
             + simpl; eexists; split; eauto; reflexivity.
             + econstructor; eauto.
               discriminate.
           - do 2 (econstructor; eauto using sem_equation).
             + change true with (negb false).
               eapply Son_abs2; eauto.
               destruct Cky as [[]|(?&?&?)]; auto.
               assert (present c = absent) by sem_det; discriminate.
             + simpl; eexists; split; eauto; reflexivity.
             + econstructor; eauto.
               discriminate.
         }
      + apply transient_states_closed_add; auto.
        * apply memory_closed_rec_state_closed; auto.
          rewrite Mmask_0, Mmask_n; auto.
          specialize (Spec n); destruct (rs n);
            apply msem_node_memory_closed_rec_n in Node_n as ();
            apply msem_node_memory_closed_rec_n in Node_0 as (); auto.
        * intro Hin; apply SpecInsts in Hin as (); eapply Notin; eauto.

    - do 3 (econstructor; auto).
      destruct Mfby as (?&?& Spec).
      specialize (Spec n); destruct (find_val x (M n)) eqn: E; try contradiction.
      specialize (Var n); specialize (Arg n).
      pose proof Arg as Arg'.
      destruct (ls n); destruct Spec as (?& Hxs); rewrite Hxs in Var; inv Arg';
        econstructor; eauto; simpl; auto.
  Qed.

  Lemma not_Is_defined_not_Is_state_in_eqs:
    forall x eqs,
      ~ Is_defined_in_eqs x eqs ->
      (forall k, ~ Is_state_in x k (translate_eqns eqs)).
  Proof.
    unfold translate_eqns, concatMap.
    induction eqs as [|eq]; simpl; intros Notin k Hin.
    - inv Hin.
    - apply Exists_app' in Hin as [Hin|].
      + destruct eq; simpl in Hin.
        * inversion_clear Hin as [?? Hin'|?? Hin']; inv Hin'.
        *{ destruct i; try destruct o; inversion_clear Hin as [?? Hin'|?? Hin'].
           - inv Hin'; apply Notin; do 3 constructor; auto.
           - inversion_clear Hin' as [?? Hin|?? Hin]; inv Hin;
               apply Notin; do 3 constructor; auto.
           - inv Hin'; apply Notin; do 3 constructor; auto.
           - inv Hin'.
         }
        * inversion_clear Hin as [?? Hin'|?? Hin']; inv Hin'.
      + eapply IHeqs; eauto.
        eapply NL.IsD.not_Is_defined_in_cons in Notin as []; auto.
  Qed.

  Lemma Nodup_defs_translate_eqns:
    forall eq eqs G bk H M M',
      msem_equation G bk H M M' eq ->
      NoDup_defs (eq :: eqs) ->
      translate_eqn_nodup_states eq (translate_eqns eqs).
  Proof.
    destruct eq; inversion_clear 1; inversion_clear 1; econstructor; eauto.
    - apply not_Is_defined_not_Is_state_in_eqs.
      assert (In x i) by (now apply hd_error_Some_In); auto.
    - apply not_Is_defined_not_Is_state_in_eqs.
      assert (In x i) by (now apply hd_error_Some_In); auto.
  Qed.

  Lemma gather_insts_Is_state_in_translate_eqns:
    forall eqs x,
      InMembers x (gather_insts eqs) ->
      exists k, Is_state_in x k (translate_eqns eqs).
  Proof.
    unfold gather_insts, translate_eqns, concatMap.
    induction eqs as [|[]]; simpl; try contradiction; intros ** Hin.
    - edestruct IHeqs; eauto; eexists; right; eauto.
    - destruct i; simpl in *; auto.
      destruct o.
      + destruct Hin; subst.
        * exists 1; apply Exists_app'; left; right; left; constructor.
        * edestruct IHeqs; eauto; eexists; apply Exists_app; eauto.
      + destruct Hin; subst.
        * exists 1; apply Exists_app'; left; left; constructor.
        * edestruct IHeqs; eauto; eexists; apply Exists_app; eauto.
    - edestruct IHeqs; eauto; eexists; right; eauto.
  Qed.

  Corollary equations_correctness:
    forall G bk H M M' eqs vars,
      (forall f xss M M' yss,
          msem_node G f xss M M' yss ->
          sem_block_n (translate G) f M xss yss M') ->
      Ordered_nodes G ->
      Forall (wc_equation G vars) eqs ->
      Forall (clock_match bk H) vars ->
      NoDup_defs eqs ->
      Forall (msem_equation G bk H M M') eqs ->
      exists Is, sem_equations_n (translate G) bk H M Is M' (translate_eqns eqs)
            /\ forall n, transient_states_closed (translate G) (gather_insts eqs) (Is n).
  Proof.
    intros ** WC ?? Heqs.
    unfold translate_eqns, concatMap.
    induction eqs as [|eq eqs IHeqs]; simpl; inv WC.
    - exists (fun n => Env.empty state); split; constructor.
    - apply Forall_cons2 in Heqs as [Heq Heqs].
      apply IHeqs in Heqs as (?&?&?); auto.
      + unfold gather_insts, concatMap; simpl.
        eapply equation_correctness; eauto.
        * eapply Nodup_defs_translate_eqns; eauto.
        * apply gather_insts_Is_state_in_translate_eqns.
      + eapply NoDup_defs_cons; eauto.
  Qed.

  Lemma clock_of_correctness:
    forall xss bk,
      ExprSem.clock_of xss bk ->
      forall n, clock_of (xss n) (bk n).
  Proof. auto. Qed.

  Lemma same_clock_correctness:
    forall xss,
      ExprSem.same_clock xss ->
      forall n, same_clock (xss n).
  Proof. auto. Qed.
  Hint Resolve clock_of_correctness same_clock_correctness.

  Lemma not_Is_node_in_not_Is_block_in:
    forall eqs f,
      ~ Is_node_in f eqs ->
      ~ Is_block_in f (translate_eqns eqs).
  Proof.
    unfold translate_eqns, concatMap.
    induction eqs as [|eq]; simpl; intros ** Hnin Hin.
    - inv Hin.
    - apply not_Is_node_in_cons in Hnin as (Hnineq & Hnin).
      apply IHeqs in Hnin.
      destruct eq; simpl in *.
      + inversion_clear Hin as [?? E|?? Hins]; try inv E; auto.
      + destruct i; auto.
        destruct o as [|]; inversion_clear Hin as [?? E|?? Hins]; auto.
        * inv E; apply Hnineq; constructor.
        * inversion_clear Hins as [?? E|?? Hins']; auto.
          inv E; apply Hnineq; constructor.
        * inv E; apply Hnineq; constructor.
      + inversion_clear Hin as [?? E|?? Hins]; try inv E; auto.
  Qed.

  Theorem correctness:
    forall G f xss M M' yss,
      Ordered_nodes G ->
      wc_global G ->
      msem_node G f xss M M' yss ->
      sem_block_n (translate G) f M xss yss M'.
  Proof.
    induction G as [|node ? IH].
    inversion 3;
      match goal with Hf: find_node _ [] = _ |- _ => inversion Hf end.
    intros ** Hord WC Hsem n.
    assert (Hsem' := Hsem).
    inversion_clear Hsem' as [???????? Clock Hfind Ins Outs ???? Heqs Closed Closed'].
    pose proof (find_node_not_Is_node_in _ _ _ Hord Hfind) as Hnini.
    pose proof Hord; inversion_clear Hord as [|??? NodeIn].
    pose proof Hfind as Hfind'.
    simpl in Hfind.
    assert (Ordered_blocks (translate_node node :: translate G))
      by (change (translate_node node :: translate G) with (translate (node :: G));
          apply Ordered_nodes_blocks; auto).
    inversion WC as [|??? (?&?&?& WCeqs)]; subst.
    destruct (ident_eqb node.(n_name) f) eqn:Hnf.
    - inversion Hfind; subst n0.
      apply find_node_translate in Hfind' as (?&?&?&?); subst.
      eapply msem_equations_cons in Heqs; eauto.
      pose proof (NoDup_defs_node node).
      apply msem_node_memory_closed_rec_n in Hsem as (); auto.
      eapply equations_correctness in Heqs as (I & Heqs &?); eauto.
      + econstructor; eauto.
        * specialize (Ins n); destruct node; simpl in *.
          rewrite map_fst_idty; eauto.
        * specialize (Outs n); destruct node; simpl in *.
          rewrite map_fst_idty; eauto.
        * apply sem_equations_cons; eauto.
          apply not_Is_node_in_not_Is_block_in; auto.
        * apply memory_closed_rec_state_closed; auto.
        * eapply transient_states_closed_find_block_other, transient_states_closed_cons; eauto.
          simpl; rewrite gather_eqs_snd_spec; auto.
        * apply memory_closed_rec_state_closed; auto.
      + rewrite idck_app, Forall_app; split.
        * eapply sem_clocked_vars_clock_match; eauto.
          rewrite map_fst_idck; eauto.
        *{ apply Forall_forall; intros (x, ck) ?.
           rewrite idck_app in WCeqs.
           eapply clock_match_eqs with (eqs := node.(n_eqs)); eauto.
           - rewrite <-idck_app, NoDupMembers_idck.
             apply n_nodup.
           - eapply msem_sem_equations; eauto.
           - rewrite map_fst_idck.
             apply n_defd.
         }
    - assert (n_name node <> f) by now apply ident_eqb_neq.
      eapply msem_node_cons, IH in Hsem; eauto.
      apply sem_block_cons2; auto using Ordered_blocks.
  Qed.

  Section DostepCoind.

    Variable R: program -> ident -> stream (list value) -> stream (list value) -> state -> nat -> Prop.

    Hypothesis Step:
      forall P b xss yss Sn n,
        R P b xss yss Sn n ->
        (n = 0 -> initial_state P b Sn)
        /\ exists S', sem_block P b Sn (xss n) (yss n) S'
                /\ R P b xss yss S' (S n).

    Lemma dostep_coind:
      forall P b xss yss S n,
        R P b xss yss S n ->
        dostep P b xss yss S n.
    Proof.
      cofix COFIX; intros ** HR.
      apply Step in HR as (?&?&?&?).
      econstructor; eauto.
    Qed.

  End DostepCoind.

  (* Theorem correctness_dostep: *)
  (*   forall n G f xss M M' yss, *)
  (*     Ordered_nodes G -> *)
  (*     wc_global G -> *)
  (*     msem_node G f xss M M' yss -> *)
  (*     exists S, dostep (translate G) f xss yss S n. *)
  (* Proof. *)
  (*   induction n.  *)
  (*   generalize 0. *)
  (*   cofix COFIX; intros ** Sem. *)
  (*   econstructor. *)
  (*   - intro; subst; eapply msem_node_initial_state; eauto. *)
  (*   - apply correctness; eauto. *)
  (*   - SearchAbout msem_node. eapply COFIX.  SearchAbout initial_state. *)
  (* Theorem correctness_dostep: *)
  (*   forall G f xss M M' yss, *)
  (*     Ordered_nodes G -> *)
  (*     wc_global G -> *)
  (*     msem_node G f xss M M' yss -> *)
  (*     dostep (translate G) f xss yss (M 0) 0. *)
  (* Proof. *)
  (*   (* intros; apply dostep_coind with (R := fun P b xss yss S n => *) *)
  (*   (*                                         P = translate G *) *)
  (*   (*                                         /\ S = M n  *) *)
  (*   (*                                         /\ msem_node G b xss M M' yss); auto. *) *)
  (*   (* intros ** (?&?& Sem); subst. *) *)
  (*   (* split. *) *)
  (*   (* - intro; subst; eapply msem_node_initial_state; eauto. *) *)
  (*   (* - pose proof Sem. apply correctness in Sem; auto. *) *)
  (*   (*   exists (M' n); intuition. intros ** (?&?). intuition. *) *)
  (*   (*   exists (M' n); intuition. *) *)
  (*   generalize 0. *)
  (*   cofix COFIX; intros ** Sem. *)
  (*   econstructor. *)
  (*   - intro; subst; eapply msem_node_initial_state; eauto. *)
  (*   - apply correctness; eauto. *)
  (*   - assert (M' n = M (S n)) as -> by admit. *)
  (*     eapply COFIX; eauto. *)
  (* Qed. *)

End CORRECTNESS.

Module CorrectnessFun
       (Ids      : IDS)
       (Op       : OPERATORS)
       (OpAux    : OPERATORS_AUX       Op)
       (Clks     : CLOCKS          Ids)
       (ExprSyn  : NLEXPRSYNTAX        Op)
       (Str      : STREAM              Op OpAux)
       (ExprSem  : NLEXPRSEMANTICS Ids Op OpAux Clks ExprSyn Str)
       (NL       : NLUSTRE         Ids Op OpAux Clks ExprSyn Str ExprSem)
       (SB       : SYBLOC          Ids Op OpAux Clks ExprSyn Str ExprSem NL.Syn NL.IsF)
       (Trans    : TRANSLATION     Ids Op       Clks ExprSyn             NL.Syn SB.Syn NL.Mem)
<: CORRECTNESS Ids Op OpAux Clks ExprSyn Str ExprSem NL SB Trans.
  Include CORRECTNESS Ids Op OpAux Clks ExprSyn Str ExprSem NL SB Trans.
End CorrectnessFun.
