Require Import List.

Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.Clocks.
Require Import Velus.RMemory.
Require Import Velus.NLustre.
Require Import Velus.Obc.

(** * Correspondence between dataflow and imperative memories *)

Module Type MEMORYCORRES
       (Ids         : IDS)
       (Op          : OPERATORS)
       (OpAux       : OPERATORS_AUX Op)
       (Import Clks : CLOCKS Ids)
       (Import DF   : NLUSTRE Ids Op OpAux Clks)
       (Import MP   : OBC Ids Op OpAux).
(**

  [Memory_Corres] relates a dataflow [D.memory] with an object [heap]
  at an instant [n]. Morally, we are saying that taking a snapshot of
  the memory at time [n] gives [heap].

 *)

  Definition memories := stream (memory Op.val).

  Inductive Memory_Corres (G: global) : ident -> memory Op.val -> heap -> Prop :=
    MemC:
      forall f M menv n,
        find_node f G = Some n ->
        Forall (Memory_Corres_eq G M menv) n.(n_eqs) ->
        Memory_Corres G f M menv

  with Memory_Corres_eq (G: global) : memory Op.val -> heap -> equation -> Prop :=
       | MemC_EqDef:
           forall M menv x ck ce,
             Memory_Corres_eq G M menv (EqDef x ck ce)
       | MemC_EqApp:
           forall M menv x xs ck f le r,
             hd_error xs = Some x ->
             (forall Mo, sub_inst x M Mo ->
                    exists omenv, sub_inst x menv omenv
                             /\ Memory_Corres G f Mo omenv) ->
               Memory_Corres_eq G M menv (EqApp xs ck f le r)
       | MemC_EqFby:
           forall M menv x ck v0 le,
           (forall v, mfind_mem x M = Some v ->
                 mfind_mem x menv = Some v) ->
           Memory_Corres_eq G M menv (EqFby x ck v0 le).

  (** ** Induction principle for [Memory_Corres] and [Memory_Corres_eq] *)

  Section Memory_Corres_mult.
    Variable G: global.
    Variable P: ident -> memory Op.val -> heap -> Prop.
    Variable P_eq: memory Op.val -> heap -> equation -> Prop.

    Hypothesis MemCCase:
      forall f M menv n,
        find_node f G = Some n ->
        Forall (Memory_Corres_eq G M menv) n.(n_eqs) ->
        Forall (P_eq M menv) n.(n_eqs) ->
        P f M menv.

    Hypothesis MemC_EqDefCase:
      forall M menv x ck ce,
        P_eq M menv (EqDef x ck ce).

    Hypothesis MemC_EqAppCase:
      forall M menv x xs ck f le r,
        hd_error xs = Some x ->
        (forall Mo, sub_inst x M Mo ->
               exists omenv, sub_inst x menv omenv
                        /\ Memory_Corres G f Mo omenv
                        /\ P f Mo omenv) ->
        P_eq M menv (EqApp xs ck f le r).

    Hypothesis MemC_EqFbyCase:
      forall M menv x ck v0 le,
        (forall v, mfind_mem x M = Some v ->
              mfind_mem x menv = Some v) ->
        P_eq M menv (EqFby x ck v0 le).

    Fixpoint Memory_Corres_mult
             (f    : ident)
             (M    : memory Op.val)
             (menv : heap)
             (Hmc  : Memory_Corres G f M menv)
             {struct Hmc}
      : P f M menv
    with Memory_Corres_eq_mult
           (M     : memory Op.val)
           (menv  : heap)
           (eq    : equation)
           (Hmceq : Memory_Corres_eq G M menv eq)
           {struct Hmceq} : P_eq M menv eq.
    Proof.
      - destruct Hmc.
        eapply MemCCase; eauto.
        induction H0; auto.
      - destruct Hmceq; eauto.
        eapply MemC_EqAppCase; eauto.
        intros Mo Find; destruct (H0 Mo Find) as (?&?&?); eauto.
    Qed.

  End Memory_Corres_mult.

  (** ** Global environment management *)

  Lemma Memory_Corres_eq_node_tl:
    forall n G eq M menv,
      Ordered_nodes (n :: G) ->
      ~Is_node_in_eq n.(n_name) eq ->
      (Memory_Corres_eq (n :: G) M menv eq
       <-> Memory_Corres_eq G M menv eq).
  Proof.
    intros ** Hord Hini.
    split; intro Hmc; revert M menv eq Hmc Hini.
    - induction 1 as [???? Hfind ? IH | |????????? Hfind |]
                       using Memory_Corres_eq_mult
                     with (P := fun f M menv =>
                                  n.(n_name) <> f ->
                                  Memory_Corres G f M menv);
        intro HH; try solve [ constructor(auto) | intuition].

      + (* Case: Memory_Corres G n f M menv *)
        simpl in Hfind.
        apply ident_eqb_neq in HH.
        rewrite HH in Hfind.
        econstructor; eauto.
        apply find_node_later_not_Is_node_in with (2:=Hfind) in Hord.
        simpl in Hord; clear Hfind.
        apply Is_node_in_Forall in Hord.
        apply Forall_Forall with (1:=Hord) in IH.
        apply Forall_impl with (2:=IH).
        intuition.

      + (* Case: Memory_Corres_eq G n M menv (EqApp xs ck f le) *)
        assert (n_name n <> f)
          by (intro; subst; apply HH; auto using Is_node_in_eq).

        econstructor; eauto.
        intros; edestruct Hfind as (?&?&?&?); eauto.

    - induction 1 as [ ???? Hfind ? IH | |????????? Hfind |]
                       using Memory_Corres_eq_mult
                     with (P:=fun f M menv=>
                                n.(n_name) <> f ->
                                Memory_Corres (n :: G) f M menv);
      intro HH; try solve [ constructor; auto | intuition].
      + apply find_node_later_not_Is_node_in with (2:=Hfind) in Hord.
        rewrite <-find_node_tl with (1:=HH) in Hfind.
        econstructor; eauto.
        apply Is_node_in_Forall in Hord.
        apply Forall_Forall with (1:=Hord) in IH.
        apply Forall_impl with (2:=IH).
        intuition.

      + assert (n_name n <> f)
          by (intro; subst; apply HH; auto using Is_node_in_eq).
        econstructor; eauto.
        intros Mo Hmfind.
        edestruct Hfind as (?&?&?&?); eauto.
  Qed.

  Lemma Memory_Corres_eqs_node_tl:
    forall n G eqs M menv,
      Ordered_nodes (n :: G) ->
      ~Is_node_in n.(n_name) eqs ->
      (Forall (Memory_Corres_eq (n :: G) M menv) eqs
       <-> Forall (Memory_Corres_eq G M menv) eqs).
  Proof.
    induction eqs as [|eq eqs IH]; [now intuition|].
    intros ** Hord Hnini.
    apply not_Is_node_in_cons in Hnini.
    destruct Hnini as [Hnini Hninis].
    split;
      intro HH; apply Forall_cons2 in HH; destruct HH as [HH HHs];
      apply Forall_cons;
      (apply Memory_Corres_eq_node_tl with (1:=Hord) (2:=Hnini) (3:=HH)
       || apply IH with (1:=Hord) (2:=Hninis) (3:=HHs)).
  Qed.

  Lemma Memory_Corres_node_tl:
    forall f n G M menv,
      Ordered_nodes (n :: G) ->
      n.(n_name) <> f ->
      (Memory_Corres (n :: G) f M menv <-> Memory_Corres G f M menv).
  Proof.
    intros ** Hord Hnf.
    split;
      inversion_clear 1;
      econstructor;
      repeat progress
             match goal with
             | Hf: find_node ?f (_ :: ?G) = Some _ |- _ =>
               rewrite find_node_tl with (1:=Hnf) in Hf
             | |- find_node ?f (_ :: ?G) = Some _ =>
               rewrite find_node_tl with (1:=Hnf)
             | Hf: find_node ?f ?G = Some _ |- find_node ?f ?G = Some _ =>
               exact Hf
             | H:Forall (Memory_Corres_eq _ _ _) _
               |- Forall (Memory_Corres_eq _ _ _) _ =>
               apply Memory_Corres_eqs_node_tl with (1:=Hord) (3:=H)
             | Hf: find_node ?f ?G = Some _ |- ~Is_node_in _ _ =>
               apply find_node_later_not_Is_node_in with (1:=Hord) (2:=Hf)
             end.
  Qed.

  (** ** Memory management *)

  Lemma Is_memory_in_Memory_Corres_eqs:
    forall G M menv x eqs,
      Is_defined_in_eqs x eqs ->
      ~Is_variable_in_eqs x eqs ->
      Forall (Memory_Corres_eq G M menv) eqs ->
      (forall v, mfind_mem x M = Some v ->
            mfind_mem x menv = Some v).
  Proof.
    induction eqs as [|eq eqs IH]; [now inversion 1|].
    intros Hidi Hnvi Hmc ms.
    apply Is_defined_in_cons in Hidi.
    apply not_Is_variable_in_cons in Hnvi.
    destruct Hnvi as [Hnvi Hnvis].
    inversion_clear Hmc as [|? ? Hmceq Hmceqs].
    destruct Hidi as [Himeqs|[Himeq Himeqs]];
      [|now apply IH with (1:=Himeqs) (2:=Hnvis) (3:=Hmceqs)].
    destruct eq;
      inversion Himeqs; subst;
      try (exfalso; apply Hnvi; now constructor).
    inversion_clear Hmceq; auto.
  Qed.

  Lemma Memory_Corres_eqs_add_mem:
    forall G M menv y v eqs,
      mfind_mem y M = Some v ->
      Forall (Memory_Corres_eq G M menv) eqs ->
      Forall (Memory_Corres_eq G M (madd_mem y v menv)) eqs.
  Proof.
    induction eqs as [|eq eqs IH]; [now auto|].
    intros Hmfind Hmc.

    assert (Memory_Corres_eq G M menv eq
            /\ Forall (Memory_Corres_eq G M menv) eqs)
      as (Hmc0 & ?) by now apply Forall_cons2.
    clear Hmc.

    apply Forall_cons; [|eapply IH; eauto].
    destruct eq.
    - (* Case: eq ~ EqDef *)
      now constructor.
    - (* Case: eq ~ EqApp *)
      inversion_clear Hmc0 as [|? ? x ? ? ? ? Hsome Hmc|].
      econstructor; eauto.
    - (* Case: eq ~ EqFby *)
      constructor.
      intros ms' Hmfind'.
      destruct (ident_eq_dec i y) as [He|Hne].
      + subst i.
        rewrite Hmfind in Hmfind'.
        injection Hmfind'; intro; subst v.
        now rewrite mfind_mem_gss.
      + erewrite mfind_mem_gso; auto.
        inversion_clear Hmc0 as [| |? ? ? ? ? ? Hmc].
        now eapply Hmc.
  Qed.

  (* Unfortunately, a similar lemma to Memory_Corres_eqs_add_mem but for add_obj
   does not seem to hold without extra conditions:

     Lemma Memory_Corres_eqs_add_obj:
       forall G n M menv y Mo g omenv eqs,
         mfind_inst y M = Some Mo
         -> Memory_Corres G n g Mo omenv
         -> Memory_Corres_eqs G n M menv eqs
         -> Memory_Corres_eqs G n M (add_obj y omenv menv) eqs.

   Consider the equations:
      [ x = f y; x = g y; ... ]
   It is possible for this system to have an m-semantics if both f and g have
   the same input/output behaviour, but also possible for the memory structures
   of f and g to differ from one another. In this case, we end up having as
   hypothesis
        Memory_Corres G n g Mo omenv
   and the goal
        Memory_Corres G n f Mo omenv *)

  Lemma Memory_Corres_eqs_add_obj:
    forall G M menv eqs y omenv,
      Forall (Memory_Corres_eq G M menv) eqs ->
      ~Is_defined_in_eqs y eqs ->
      Forall (Memory_Corres_eq G M (madd_obj y omenv menv)) eqs.
  Proof.
    induction eqs as [|eq eqs IH]; [now constructor|].
    intros y omenv Hmce Hniii.

    assert (Memory_Corres_eq G M menv eq
            /\ Forall (Memory_Corres_eq G M menv) eqs)
      as (Hmc0 & ?) by now apply Forall_cons2.
    clear Hmce.

    assert (  ~ Is_defined_in_eq y eq
            /\ ~ Is_defined_in_eqs y eqs)
      as (Hniii0 & Hniii1)
        by now apply not_Is_defined_in_cons.

    apply Forall_cons; [|now eapply IH].

    destruct eq.
    - (* Case: EqDef *)
      now constructor.
    - (* Case: EqApp *)
      inversion_clear Hmc0 as [|???????? Hsome Hfindo |].
      econstructor; eauto.

      intros Mo Hmfind.
      destruct (ident_eq_dec x y) as [Hxy|Hnxy].
      + subst x. exfalso; apply Hniii0; constructor.
        destruct i; simpl in *; try discriminate.
        left. now injection Hsome.
      + edestruct Hfindo as [omenv' [Hfindo' Hmc]]; eauto.
        exists omenv'.
        split; eauto.
        unfold sub_inst.
        now rewrite mfind_inst_gso.
    - constructor.
      intros ms Hmfind.
      rewrite mfind_mem_add_inst.
      now (inv Hmc0; eauto).
  Qed.

  Lemma Memory_Corres_unchanged:
    forall G f n ls Ms ys menv,
      msem_node G f ls Ms ys ->
      absent_list (ls n) ->
      Memory_Corres G f (Ms n) menv ->
      Memory_Corres G f (Ms (S n)) menv.
  Proof.
    intros ** Hmsem Habs Corres.
    revert dependent menv. revert Habs.
    induction Hmsem as [|
                        ??? y ??????? Hsome Hmfind Hsem |
                        ??? y ?????????? Hsome Hmfind Hsem ? Hvar |
                        ????????? Hsem ? Hfby|
                        ????? IH|
                        ?????? n' ? Hfind Hxss ???? Heqs IH]
                         using msem_node_mult
      with (P_equation := fun bk H M eq =>
                            forall menv,
                              rhs_absent_instant (bk n) (restr H n) eq ->
                              Memory_Corres_eq G (M n) menv eq ->
                              Memory_Corres_eq G (M (S n)) menv eq)
           (P_reset := fun f r xss M yss =>
                         forall menv,
                           absent_list (xss n) ->
                           r (S n) = false ->
                           Memory_Corres G f (M n) menv ->
                           Memory_Corres G f (M (S n)) menv).

    - (* Case: EqDef *)
      inversion_clear 2; constructor; assumption.

    (* Case: EqApp *)
    - intros ** Hrhsa Hmceq.
      econstructor; eauto.
      intros Mo Hmfind'.
      unfold sub_inst_n in Hmfind; unfold sub_inst in Hmfind'.
      rewrite Hmfind in Hmfind'; inv Hmfind'.

      inversion_clear Hmceq as [|? ? x ? ? ? ? ? Hsome' Hmc'|].
      assert (Some x = Some y) as Hxy by now rewrite Hsome, <-Hsome'.
      inv Hxy.

      edestruct Hmc' as [omenv [Hfindo Hmc]]; eauto.
      exists omenv.
      split; [exact Hfindo|].
      apply IHHmsem; auto.
      inv Hrhsa.

      assert (ls n = vs) as ->
        by (specialize (Hsem n); simpl in Hsem; sem_det); auto.

    (* Case: EqReset *)
    - intros ** Hrhsa Hmceq.
      econstructor; eauto.
      intros Mo Hmfind'.
      unfold sub_inst_n in Hmfind; unfold sub_inst in Hmfind'.
      rewrite Hmfind in Hmfind'; inv Hmfind'.

      inversion_clear Hmceq as [|? ? x ? ? ? ? ? Hsome' Hmc'|].
      assert (Some x = Some y) as Hxy by now rewrite Hsome, <-Hsome'.
      inv Hxy.

      edestruct Hmc' as [omenv [Hfindo Hmc]]; eauto.
      exists omenv.
      split; [exact Hfindo|].
      inv Hrhsa.
      apply IHHmsem; auto.
      + assert (ls n = vs) as -> by (specialize (Hsem n); simpl in *; sem_det);
          auto.
      + unfold reset_of.
        unfold sem_avar, lift in Hvar; specialize (Hvar (S n)).
        (* assert (ys (S n) = OpAux.absent) as -> by sem_det; auto. *)
        admit.

     (* Case: EqFby *)
    - intros ** Hrhsa Hmceq.
      constructor.
      intros ms0 Hmfind0.
      inversion_clear Hfby as [????? Hms0 Hy].
      specialize (Hy n).
      destruct (mfind_mem x (M n)) eqn: Hmfind; try contradiction.
      inversion_clear Hmceq as [| |? ? ? ? ? ? Hmenv].
      apply Hmenv.
      rewrite <-Hmfind0.
      inv Hrhsa.
      unfold sem_laexp, lift in Hsem; specialize (Hsem n).
      assert (ls n = OpAux.absent) as Hls by sem_det.
      rewrite Hls in Hy; destruct Hy as [HfindS Hxs].
      now rewrite HfindS.

    (* Case: Reset *)
    - intros ** Hsem E Hmc.
      destruct (IH (count r n)) as (? & Mn & ? & ? & Hxn & ? & HMn & IHn).
      (* unfold masked in Hmaskn. *)
      rewrite <-HMn in Hmc; auto.
      apply IHn in Hmc.
      * rewrite <-HMn; auto.
        simpl; rewrite E; auto.
      * rewrite Hxn; auto.
      (* destruct (r (S n)) eqn: E. *)
      (* + destruct (IH (count r n)) as (Mn & ? & Hmaskn & IHn). *)
      (*   destruct (IH (count r (S n))) as (MSn & ? & HmaskSn & IHSn). *)
      (*   unfold memory_mask in Hmaskn, HmaskSn. *)
      (*   rewrite <-Hmaskn in Hmc; auto. *)
      (*   rewrite <-HmaskSn; auto. *)
      (*   apply IHSn. *)
      (*   * apply absent_list_mask; auto. *)
      (*     apply all_absent_spec. *)
      (*   * admit. *)
      (* + destruct (IH (count r n)) as (Mn & ? & Hmaskn & IHn). *)
      (*   unfold memory_mask in Hmaskn. *)
      (*   rewrite <-Hmaskn in Hmc; auto. *)
      (*   apply IHn in Hmc. *)
      (*   * rewrite <-Hmaskn; auto. *)
      (*     simpl; rewrite E; auto. *)
      (*   * apply absent_list_mask; auto. *)
      (*     apply all_absent_spec. *)

    (* Case: Node *)
    - intros ** Hmc.
      inversion_clear Hmc as [? ? ? ?  Hfind' Hmceqs].
      rewrite Hfind' in Hfind; inv Hfind.

      assert (0 < length (xss n)).
      {
        unfold sem_vars, lift in Hxss.
        specialize (Hxss n).
        apply Forall2_length in Hxss.
        rewrite map_length in Hxss.
        rewrite <-Hxss.
        apply n'.(n_ingt0).
      }

      assert (absent_list (xss n) ->
              Forall (rhs_absent_instant (bk n) (restr H n)) n'.(n_eqs))
        as Habs'
        by (eapply subrate_property_eqns; eauto).

      apply Habs' in Habs.
      apply Forall_Forall with (1:=Habs) in IH.
      apply Forall_Forall with (1:=Hmceqs) in IH.
      clear Habs Hmceqs.
      econstructor; eauto.
      apply Forall_impl with (2:=IH); clear IH.
      intros eq HH.
      destruct HH as [? [? ?]]; auto.
   Qed.

End MEMORYCORRES.

Module MemoryCorresFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Clks  : CLOCKS Ids)
       (DF    : NLUSTRE Ids Op OpAux Clks)
       (MP    : OBC Ids Op OpAux)
       <: MEMORYCORRES Ids Op OpAux Clks DF MP.
  Include MEMORYCORRES Ids Op OpAux Clks DF MP.
End MemoryCorresFun.
