Require Import List.
Import List.ListNotations.
Open Scope list_scope.
Require Import Coq.Sorting.Permutation.
Require Import Setoid.
Require Import Morphisms.

Require Import Coq.FSets.FMapPositive.
Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.Clocks.
Require Import Velus.NLustre.NLExprSyntax.
Require Import Velus.NLustre.NLSyntax.
Require Import Velus.NLustre.Ordered.
Require Import Velus.NLustre.Stream.
Require Import Velus.NLustre.NLExprSemantics.

(** * The NLustre semantics *)

(**

  We provide a "standard" dataflow semantics relating an environment
  of streams to a stream of outputs.

 *)

Module Type NLSEMANTICS
       (Import Ids     : IDS)
       (Import Op      : OPERATORS)
       (Import OpAux   : OPERATORS_AUX       Op)
       (Import Clks    : CLOCKS          Ids)
       (Import ExprSyn : NLEXPRSYNTAX        Op)
       (Import Syn     : NLSYNTAX        Ids Op       Clks ExprSyn)
       (Import Str     : STREAM              Op OpAux)
       (Import Ord     : ORDERED         Ids Op       Clks ExprSyn Syn)
       (Import ExprSem : NLEXPRSEMANTICS Ids Op OpAux Clks ExprSyn      Str).

  (** ** Time-dependent semantics *)

  Fixpoint hold (v0: val) (xs: stream value) (n: nat) : val :=
    match n with
    | 0 => v0
    | S m => match xs m with
            | absent => hold v0 xs m
            | present hv => hv
            end
    end.

  Definition fby (v0: val) (xs: stream value) : stream value :=
    fun n =>
      match xs n with
      | absent => absent
      | _ => present (hold v0 xs n)
      end.

  Section NodeSemantics.

    Variable G: global.

    Inductive sem_equation: stream bool -> history -> equation -> Prop :=
    | SEqDef:
        forall bk H x xs ck ce,
          sem_var H x xs ->
          sem_caexp bk H ck ce xs ->
          sem_equation bk H (EqDef x ck ce)
    | SEqApp:
        forall bk H x ck f arg ls xs,
          sem_laexps bk H ck arg ls ->
          sem_vars H x xs ->
          sem_node f ls xs ->
          sem_equation bk H (EqApp x ck f arg None)
    | SEqReset:
        forall bk H x ck f arg y ck_r ys ls xs,
          sem_laexps bk H ck arg ls ->
          sem_vars H x xs ->
          sem_var H y ys ->
          sem_reset f (reset_of ys) ls xs ->
          sem_equation bk H (EqApp x ck f arg (Some (y, ck_r)))
    | SEqFby:
        forall bk H x ls xs c0 ck le,
          sem_laexp bk H ck le ls ->
          sem_var H x xs ->
          xs = fby (sem_const c0) ls ->
          sem_equation bk H (EqFby x ck c0 le)

    with sem_reset: ident -> stream bool -> stream (list value) -> stream (list value) -> Prop :=
         | SReset:
             forall f r xss yss,
               (forall k, sem_node f
                              (mask (all_absent (xss 0)) k r xss)
                              (mask (all_absent (yss 0)) k r yss)) ->
               sem_reset f r xss yss

    with sem_node: ident -> stream (list value) -> stream (list value) -> Prop :=
         | SNode:
             forall bk H f xss yss n,
               clock_of xss bk ->
               find_node f G = Some n ->
               sem_vars H (map fst n.(n_in)) xss ->
               sem_vars H (map fst n.(n_out)) yss ->
               (* XXX: This should be obtained through well-clocking: *)
               (*  * tuples are synchronised: *)
               same_clock xss ->
               same_clock yss ->
               (*  * output clock matches input clock *)
               (forall n, absent_list (xss n) <-> absent_list (yss n)) ->
               (* XXX: END *)
               Forall (sem_equation bk H) n.(n_eqs) ->
               sem_node f xss yss.

    Definition sem_nodes : Prop :=
      Forall (fun no => exists xs ys, sem_node no.(n_name) xs ys) G.

  End NodeSemantics.

  (** ** Induction principle for [sem_node] and [sem_equation] *)

  (** The automagically-generated induction principle is not strong
enough: it does not support the internal fixpoint introduced by
[Forall] *)

  Section sem_node_mult.
    Variable G: global.

    Variable P_equation: stream bool -> history -> equation -> Prop.
    Variable P_reset: ident -> stream bool -> stream (list value) -> stream (list value) -> Prop.
    Variable P_node: ident -> stream (list value) -> stream (list value) -> Prop.

    Hypothesis EqDefCase:
      forall bk H x xs ck ce,
        sem_var H x xs ->
        sem_caexp bk H ck ce xs ->
        P_equation bk H (EqDef x ck ce).

    Hypothesis EqAppCase:
      forall bk H x ck f arg ls xs,
        sem_laexps bk H ck arg ls ->
        sem_vars H x xs ->
        sem_node G f ls xs ->
        P_node f ls xs ->
        P_equation bk H (EqApp x ck f arg None).

    Hypothesis EqResetCase:
      forall bk H x ck f arg y ck_r ys ls xs,
        sem_laexps bk H ck arg ls ->
        sem_vars H x xs ->
        sem_var H y ys ->
        sem_reset G f (reset_of ys) ls xs ->
        P_reset f (reset_of ys) ls xs ->
        P_equation bk H (EqApp x ck f arg (Some (y, ck_r))).

    Hypothesis EqFbyCase:
      forall bk H x ls xs c0 ck le,
        sem_laexp bk H ck le ls ->
        sem_var H x xs ->
        xs = fby (sem_const c0) ls ->
        P_equation bk H (EqFby x ck c0 le).

    Hypothesis ResetCase:
      forall f r xss yss,
        (forall k, sem_node G f
                       (mask (all_absent (xss 0)) k r xss)
                       (mask (all_absent (yss 0)) k r yss)
              /\ P_node f
                       (mask (all_absent (xss 0)) k r xss)
                       (mask (all_absent (yss 0)) k r yss)) ->
        P_reset f r xss yss.

    Hypothesis NodeCase:
      forall bk H f xss yss n,
        clock_of xss bk ->
        find_node f G = Some n ->
        sem_vars H (map fst n.(n_in)) xss ->
        sem_vars H (map fst n.(n_out)) yss ->
        (* XXX: This should be obtained through well-clocking: *)
        (*  * tuples are synchronised: *)
        same_clock xss ->
        same_clock yss ->
        (*  * output clock matches input clock *)
        (forall n, absent_list (xss n) <-> absent_list (yss n)) ->
        (* XXX: END *)
        Forall (sem_equation G bk H) n.(n_eqs) ->
        Forall (P_equation bk H) n.(n_eqs) ->
        P_node f xss yss.

    Fixpoint sem_equation_mult
            (b: stream bool) (H: history) (e: equation)
            (Sem: sem_equation G b H e) {struct Sem}
      : P_equation b H e
    with sem_reset_mult
           (f: ident) (r: stream bool)
           (xss oss: stream (list value))
           (Sem: sem_reset G f r xss oss) {struct Sem}
         : P_reset f r xss oss
    with sem_node_mult
           (f: ident) (xss oss: stream (list value))
           (Sem: sem_node G f xss oss) {struct Sem}
         : P_node f xss oss.
    Proof.
      - destruct Sem; eauto.
      - destruct Sem as [???? Sem]; eauto.
      - destruct Sem; eauto.
        eapply NodeCase; eauto.
        induction H7; auto.
    Qed.

    Combined Scheme sem_equation_node_ind from
             sem_equation_mult, sem_node_mult, sem_reset_mult.

  End sem_node_mult.

  Lemma hold_abs:
    forall n c xs,
      xs n = absent ->
      hold c xs n = hold c xs (S n).
  Proof.
    destruct n; intros ** E; simpl; now rewrite E.
  Qed.

  Lemma hold_pres:
    forall v n c xs,
      xs n = present v ->
      v = hold c xs (S n).
  Proof.
    destruct n; intros ** E; simpl; now rewrite E.
  Qed.

  (* Ltac assert_const_length xss := *)
  (*   match goal with *)
  (*     H: sem_vars _ _ _ xss |- _ => *)
  (*     let H' := fresh in *)
  (*     let k := fresh in *)
  (*     let k' := fresh in *)
  (*     assert (wf_streams xss) *)
  (*       by (intros k k'; pose proof H as H'; *)
  (*           unfold sem_vars, lift in *; *)
  (*           specialize (H k); specialize (H' k'); *)
  (*           apply Forall2_length in H; apply Forall2_length in H'; *)
  (*           now rewrite H in H') *)
  (*   end. *)

  Lemma sem_node_wf:
    forall G f xss yss,
      sem_node G f xss yss ->
      wf_streams xss /\ wf_streams yss.
  Proof.
    intros ** Sem; split; inv Sem;
      assert_const_length xss; assert_const_length yss; auto.
  Qed.

  Lemma sem_EqApp_gt0:
    forall G bk H xs ck f es r,
      sem_equation G bk H (EqApp xs ck f es r) ->
      0 < length xs.
  Proof.
    inversion_clear 1 as [|????????? Vars Node|???????????? Vars ? Rst|];
      [|inversion_clear Rst as [???? Node]; pose proof Node as Node'; specialize (Node 0)];
      inversion_clear Node as [????????? Out];
      specialize (Out 0); specialize (Vars 0); simpl in *;
        apply Forall2_length in Out; apply Forall2_length in Vars;
          [|rewrite mask_length in Out];
          try (rewrite <-Out in Vars; rewrite Vars, map_length; apply n_outgt0).
    eapply wf_streams_mask.
    intro k; specialize (Node' k); apply sem_node_wf in Node' as (); eauto.
  Qed.

  (** ** Properties of the [global] environment *)

  Lemma sem_node_cons:
    forall node G f xs ys,
      Ordered_nodes (node::G)
      -> sem_node (node::G) f xs ys
      -> node.(n_name) <> f
      -> sem_node G f xs ys.
  Proof.
    intros node G f xs ys Hord Hsem Hnf.
    revert Hnf.
    induction Hsem as [
                     | bk H x ck f lae ls xs Hlae Hvars Hnode IH
                     | bk H x ck f lae y ck_r ys ls xs Hlae Hvars Hvar Hnode IH
                     |
                     |
                     | bk H f xs ys n Hbk Hf ? ? ? ? ? Heqs IH ]
                        using sem_node_mult
      with (P_equation := fun bk H eq => ~Is_node_in_eq node.(n_name) eq
                                      -> sem_equation G bk H eq)
           (P_reset := fun f r xss yss => node.(n_name) <> f ->
                                       sem_reset G f r xss yss).
    - econstructor; eassumption.
    - intro Hnin.
      eapply @SEqApp with (1:=Hlae) (2:=Hvars).
      apply IH. intro Hnf. apply Hnin. rewrite Hnf. constructor.
    - intro Hnin.
      eapply SEqReset; eauto.
      apply IH. intro Hnf. apply Hnin. rewrite Hnf. constructor.
    - intro; eapply SEqFby; eassumption.
    - constructor; intro k.
      specialize (H k); destruct H; auto.
    - intro.
      rewrite find_node_tl with (1:=Hnf) in Hf.
      eapply SNode; eauto.
      assert (Forall (fun eq => ~ Is_node_in_eq (n_name node) eq) (n_eqs n))
        by (eapply Is_node_in_Forall; try eassumption;
            eapply find_node_later_not_Is_node_in; try eassumption).
      clear Heqs; induction n.(n_eqs); inv IH; inv H5; eauto.
  Qed.

  Lemma find_node_find_again:
    forall G f n g,
      Ordered_nodes G
      -> find_node f G = Some n
      -> Is_node_in g n.(n_eqs)
      -> Exists (fun nd => g = nd.(n_name)) G.
  Proof.
    intros G f n g Hord Hfind Hini.
    apply find_node_split in Hfind.
    destruct Hfind as [bG [aG Hfind]].
    rewrite Hfind in *.
    clear Hfind.
    apply Ordered_nodes_append in Hord.
    apply Exists_app.
    constructor 2.
    inversion_clear Hord as [|? ? ? HH H0]; clear H0.
    apply HH in Hini; clear HH.
    intuition.
  Qed.

  Lemma sem_node_cons2:
    forall nd G f xs ys,
      Ordered_nodes G
      -> sem_node G f xs ys
      -> Forall (fun nd' : node => n_name nd <> n_name nd') G
      -> sem_node (nd::G) f xs ys.
  Proof.
    Hint Constructors sem_equation.
    intros nd G f xs ys Hord Hsem Hnin.
    assert (Hnin':=Hnin).
    revert Hnin'.
    induction Hsem as [
       | bk H x ? f lae ls xs Hlae Hvars Hnode IH
       | bk H x f lae y ck_r ys ls xs Hlae Hvars Hvar Hnode IH
       |
       |
       | bk H f xs ys n Hbk Hfind Hxs Hys ? ? ? Heqs IH]
          using sem_node_mult
        with (P_equation := fun bk H eq =>
                     ~Is_node_in_eq nd.(n_name) eq
                     -> sem_equation (nd::G) bk H eq)
             (P_reset := fun f r xss yss => sem_reset (nd::G) f r xss yss);
      try eauto; try intro HH.
    - constructor; intro k; specialize (H k); destruct H; auto.
    - clear HH.
      assert (nd.(n_name) <> f) as Hnf.
      { intro Hnf.
        rewrite Hnf in *.
        pose proof Hfind as Hfind'.
        apply find_node_split in Hfind.
        destruct Hfind as [bG [aG Hge]].
        rewrite Hge in Hnin.
        apply Forall_app in Hnin.
        destruct Hnin as [? Hfg].
        inversion_clear Hfg.
        match goal with H:f<>_ |- False => apply H end.
        erewrite find_node_name; eauto.
      }
      apply find_node_other with (2:=Hfind) in Hnf.
      econstructor; eauto.
      clear Heqs Hxs Hys.
      rename IH into Heqs.
      assert (forall g, Is_node_in g n.(n_eqs)
                   -> Exists (fun nd=> g = nd.(n_name)) G)
        as Hniex by
            (intros g Hini;
             eapply find_node_find_again with (1:=Hord) (2:=Hfind) in Hini; eauto).
      assert (Forall
                (fun eq=> forall g,
                     Is_node_in_eq g eq
                     -> Exists (fun nd=> g = nd.(n_name)) G) n.(n_eqs)) as HH.
      {
        clear Hfind Heqs Hnf.
        induction n.(n_eqs) as [|eq eqs IH]; [now constructor|].
        constructor.
        - intros g Hini.
          apply Hniex.
          constructor 1; apply Hini.
        - apply IH.
          intros g Hini; apply Hniex.
          constructor 2; apply Hini.
      }
      apply Forall_Forall with (1:=HH) in Heqs.
      apply Forall_impl with (2:=Heqs).
      intros eq IH.
      destruct IH as [Hsem IH1].
      apply IH1.
      intro Hini.
      apply Hsem in Hini.
      apply Forall_Exists with (1:=Hnin) in Hini.
      apply Exists_exists in Hini.
      destruct Hini as [nd' [Hin [Hneq Heq]]].
      intuition.
  Qed.


  Lemma Forall_sem_equation_global_tl:
    forall bk nd G H eqs,
      Ordered_nodes (nd::G)
      -> ~ Is_node_in nd.(n_name) eqs
      -> Forall (sem_equation (nd::G) bk H) eqs
      -> Forall (sem_equation G bk H) eqs.
  Proof.
    intros bk nd G H eqs Hord.
    induction eqs as [|eq eqs IH]; [trivial|].
    intros Hnini Hsem.
    apply Forall_cons2 in Hsem; destruct Hsem as [Hseq Hseqs].
    apply IH in Hseqs.
    2:(apply not_Is_node_in_cons in Hnini;
        destruct Hnini; assumption).
    apply Forall_cons with (2:=Hseqs).
    inversion Hseq as [|? ? ? ? ? ? ? Hsem Hvars Hnode
                          |? ? ? ? ? ? ? ? ? ? Hsem Hvars Hvar ? Hreset|]; subst.
    - econstructor; eassumption.
    - apply not_Is_node_in_cons in Hnini.
      destruct Hnini as [Hninieq Hnini].
      assert (nd.(n_name) <> f) as Hnf
          by (intro HH; apply Hninieq; rewrite HH; constructor).
      econstructor; eauto.
      eapply sem_node_cons; eauto.
    - apply not_Is_node_in_cons in Hnini.
      destruct Hnini as [Hninieq Hnini].
      assert (nd.(n_name) <> f) as Hnf
          by (intro HH; apply Hninieq; rewrite HH; constructor).
      econstructor; eauto.
      inversion_clear Hreset as [???? Hnode].
      constructor; intro k; specialize (Hnode k); eauto using sem_node_cons.
    - econstructor; eauto.
  Qed.


  (* Lemma subrate_clock: *)
  (*   forall R ck, *)
  (*     sem_clock_instant false R ck false. *)
  (* Proof. *)
  (*   Hint Constructors sem_clock_instant. *)
  (*   intros R ck. *)
  (*   induction ck; auto. *)
  (*   constructor; auto. *)
  (*   admit. *)
  (* Qed. *)

  (* XXX: Similarly, instead of [rhs_absent_instant] and friends, we
should prove that all the semantic rules taken at [base = false] yield
an absent value *)

  Lemma sem_equations_permutation:
    forall eqs eqs' G bk H,
      Forall (sem_equation G bk H) eqs ->
      Permutation eqs eqs' ->
      Forall (sem_equation G bk H) eqs'.
  Proof.
    intros eqs eqs' G bk H Hsem Hperm.
    induction Hperm as [|eq eqs eqs' Hperm IH|eq0 eq1 eqs|]; auto.
    - inv Hsem; auto.
    - inversion_clear Hsem as [|? ? ? Heqs'].
      inv Heqs'; auto.
  Qed.

  (** Morphisms properties *)

  Add Parametric Morphism G f: (sem_node G f)
      with signature eq_str ==> eq_str ==> Basics.impl
        as sem_node_eq_str.
  Proof.
    intros ** E1 ? ? E2 Node.
    inv Node.
    econstructor; eauto; intro; try rewrite <-E1; try rewrite <-E2; auto.
  Qed.

  Add Parametric Morphism G f: (sem_reset G f)
      with signature eq_str ==> eq_str ==> eq_str ==> Basics.impl
        as sem_reset_eq_str.
  Proof.
    intros ** E1 ? ? E2 ? ? E3 Res.
    inversion_clear Res as [? ? ? ? Node].
    constructor; intro k.

    specialize (Node k). now rewrite <-E1, <-2 E2, <-2 E3.
  Qed.

End NLSEMANTICS.

Module NLSemanticsFun
       (Ids     : IDS)
       (Op      : OPERATORS)
       (OpAux   : OPERATORS_AUX       Op)
       (Clks    : CLOCKS          Ids)
       (ExprSyn : NLEXPRSYNTAX        Op)
       (Syn     : NLSYNTAX        Ids Op       Clks ExprSyn)
       (Str     : STREAM              Op OpAux)
       (Ord     : ORDERED         Ids Op       Clks ExprSyn Syn)
       (ExprSem : NLEXPRSEMANTICS Ids Op OpAux Clks ExprSyn      Str)
<: NLSEMANTICS Ids Op OpAux Clks ExprSyn Syn Str Ord ExprSem.
  Include NLSEMANTICS Ids Op OpAux Clks ExprSyn Syn Str Ord ExprSem.
End NLSemanticsFun.
