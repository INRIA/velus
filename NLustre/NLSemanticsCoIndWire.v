Require Import List.
Import List.ListNotations.
Open Scope list_scope.
Require Import Coq.Sorting.Permutation.
Require Import Setoid.

Require Import Coq.FSets.FMapPositive.
Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.Clocks.
Require Import Velus.NLustre.NLSyntax.
Require Import Velus.NLustre.NLSemanticsCommon.
Require Import Velus.NLustre.Ordered.
Require Import Velus.NLustre.Streams.

(** * The NLustre semantics *)

(**

  We provide a "standard" dataflow semantics relating an environment
  of streams to a stream of outputs.

 *)

Module Type NLSEMANTICSCOINDWIRE
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op)
       (Import Clks  : CLOCKS    Ids)
       (Import Syn   : NLSYNTAX  Ids Op Clks)
       (Import Comm  : NLSEMANTICSCOMMON Ids Op OpAux Clks Syn)
       (Import Ord   : ORDERED   Ids Op Clks Syn).

  CoFixpoint fby (rs: Stream bool) (c: val) (xs: Stream value) : Stream value :=
    match xs with
    | absent ::: xs => absent ::: fby (tl rs) c xs
    | present x ::: xs => present c ::: fby1 (tl rs) x c xs
    end
  with fby1 (rs: Stream bool) (v c: val) (xs: Stream value) : Stream value :=
         match rs, xs with
         | false ::: rs, absent ::: xs => absent ::: fby1 rs v c xs
         | true ::: rs, absent ::: xs => absent ::: fby rs c xs
         | false ::: rs, present x ::: xs => present v ::: fby1 rs x c xs
         | true ::: rs, present x ::: xs => present c ::: fby1 rs x c xs
         end.

  (* CoInductive fby1 *)
  (*   : Stream bool -> val -> val -> Stream value -> Stream value -> Prop := *)
  (* | Fby1ANR: *)
  (*     forall rs v c xs ys, *)
  (*       fby1 rs v c xs ys -> *)
  (*       fby1 (false ::: rs) v c (absent ::: xs) (absent ::: ys) *)
  (* | Fby1AR: *)
  (*     forall rs v c xs ys, *)
  (*       fby rs c xs ys -> *)
  (*       fby1 (true ::: rs) v c (absent ::: xs) (absent ::: ys) *)
  (* | Fby1PNR: *)
  (*     forall rs v x c xs ys, *)
  (*       fby1 rs x c xs ys -> *)
  (*       fby1 (false ::: rs) v c (present x ::: xs) (present v ::: ys) *)
  (* | Fby1PR: *)
  (*     forall rs v x c xs ys, *)
  (*       fby1 rs x c xs ys -> *)
  (*       fby1 (true ::: rs) v c (present x ::: xs) (present c ::: ys) *)

  (* with fby: Stream bool -> val -> Stream value -> Stream value -> Prop := *)
  (* | FbyA: *)
  (*     forall r rs c xs ys, *)
  (*       fby rs c xs ys -> *)
  (*       fby (r ::: rs) c (absent ::: xs) (absent ::: ys) *)
  (* | FbyP: *)
  (*     forall r rs x c xs ys, *)
  (*       fby1 rs x c xs ys -> *)
  (*       fby (r ::: rs) c (present x ::: xs) (present c ::: ys). *)

  CoFixpoint merge_reset (rs rs' : Stream bool) : Stream bool :=
    match rs, rs' with
      r ::: rs, r' ::: rs' => r || r' ::: merge_reset rs rs'
    end.

  Section NodeSemantics.

    Variable G: global.

    Inductive sem_equation: history -> Stream bool -> Stream bool -> equation -> Prop :=
    | SeqDef:
        forall H b r x ck e es,
          sem_cexp H b e es ->
          sem_var H x es ->
          sem_equation H b r (EqDef x ck e)
    | SeqApp:
        forall H b r ys ck f es ess oss,
          Forall2 (sem_lexp H b) es ess ->
          sem_node r f ess oss ->
          Forall2 (sem_var H) ys oss ->
          sem_equation H b r (EqApp ys ck f es None)
    | SeqReset:
        forall H b r ys ck f es x rs ess oss,
          Forall2 (sem_lexp H b) es ess ->
          sem_var H x rs ->
          sem_node (merge_reset r (reset_of rs)) f ess oss ->
          Forall2 (sem_var H) ys oss ->
          sem_equation H b r (EqApp ys ck f es (Some x))
    | SeqFby:
        forall H b r x ck c0 e es os,
          sem_lexp H b e es ->
          os = fby r (sem_const c0) es ->
          sem_var H x os ->
          sem_equation H b r (EqFby x ck c0 e)

    with sem_node: Stream bool -> ident -> list (Stream value) -> list (Stream value) -> Prop :=
         | SNode:
             forall H r f n xss oss,
               find_node f G = Some n ->
               Forall2 (sem_var H) (idents n.(n_in)) xss ->
               Forall2 (sem_var H) (idents n.(n_out)) oss ->
               Forall (sem_equation H (clocks_of xss) r) n.(n_eqs) ->
               sem_node r f xss oss.

  End NodeSemantics.

  Section SemInd.

    Variable G: global.

    Variable P_equation: history -> Stream bool -> Stream bool -> equation -> Prop.
    Variable P_node: Stream bool -> ident -> list (Stream value) -> list (Stream value) -> Prop.

    Hypothesis EqDefCase:
      forall H b r x ck e es,
        sem_cexp H b e es ->
        sem_var H x es ->
        P_equation H b r (EqDef x ck e).

    Hypothesis EqAppCase:
      forall H b r ys ck f es ess oss,
        Forall2 (sem_lexp H b) es ess ->
        sem_node G r f ess oss ->
        Forall2 (sem_var H) ys oss ->
        P_node r f ess oss ->
        P_equation H b r (EqApp ys ck f es None).

    Hypothesis EqResetCase:
      forall H b r ys ck f es x rs ess oss,
        Forall2 (sem_lexp H b) es ess ->
        sem_node G (merge_reset r (reset_of rs)) f ess oss ->
        sem_var H x rs ->
        Forall2 (sem_var H) ys oss ->
        P_node (merge_reset r (reset_of rs)) f ess oss ->
        P_equation H b r (EqApp ys ck f es (Some x)).

    Hypothesis EqFbyCase:
      forall H b r x ck c0 e es os,
        sem_lexp H b e es ->
        os = fby r (sem_const c0) es ->
        sem_var H x os ->
        P_equation H b r (EqFby x ck c0 e).

    Hypothesis NodeCase:
      forall H r f n xss oss,
        find_node f G = Some n ->
        Forall2 (sem_var H) (idents n.(n_in)) xss ->
        Forall2 (sem_var H) (idents n.(n_out)) oss ->
        Forall (sem_equation G H (clocks_of xss) r) n.(n_eqs) ->
        Forall (P_equation H (clocks_of xss) r) n.(n_eqs) ->
        P_node r f xss oss.

    Fixpoint sem_equation_mult
             (H: history) (b r: Stream bool) (e: equation)
             (Sem: sem_equation G H b r e) {struct Sem}
      : P_equation H b r e
    with sem_node_mult
           (r: Stream bool) (f: ident) (xss oss: list (Stream value))
           (Sem: sem_node G r f xss oss) {struct Sem}
         : P_node r f xss oss.
    Proof.
      - destruct Sem; eauto.
      - destruct Sem; eauto.
        eapply NodeCase; eauto.
        induction H3; auto.
    Qed.

    Combined Scheme sem_equation_node_ind from sem_equation_mult, sem_node_mult.

  End SemInd.

  Add Parametric Morphism : merge_reset
      with signature @EqSt bool ==> @EqSt bool ==> @EqSt bool
        as merge_reset_EqSt.
  Proof.
    cofix Cofix.
    intros r1 r1' Er1 r2 r2' Er2.
    unfold_St r1; unfold_St r1'; unfold_St r2; unfold_St r2'.
    constructor; inv Er1; inv Er2; simpl in *; auto.
    now subst.
  Qed.

  CoFixpoint wire_fby1_EqSt_fix (v c: val)
           (rs rs': Stream bool) (Ers: rs ≡ rs')
           (xs xs': Stream value) (Exs: xs ≡ xs') :
    fby1 rs v c xs ≡ fby1 rs' v c xs'
  with wire_fby_EqSt_fix (c: val)
                     (rs rs': Stream bool) (Ers: rs ≡ rs')
                     (xs xs': Stream value) (Exs: xs ≡ xs') :
         fby rs c xs ≡ fby rs' c xs'.
  Proof.
    - unfold_Stv rs; unfold_Stv rs'; unfold_Stv xs; unfold_Stv xs';
        constructor; inv Exs; inv Ers; simpl in *; try discriminate; auto.
      + inv H; apply wire_fby1_EqSt_fix; auto.
      + inv H; apply wire_fby1_EqSt_fix; auto.
    - unfold_Stv xs; unfold_Stv xs'; unfold_St rs; unfold_St rs';
        constructor; inv Exs; inv Ers; simpl in *; try discriminate; auto.
      inv H; apply wire_fby1_EqSt_fix; auto.
  Qed.

  Add Parametric Morphism : fby
      with signature @EqSt bool ==> eq ==> @EqSt value ==> @EqSt value
        as wire_fby_EqSt.
  Proof. intros; apply wire_fby_EqSt_fix; auto. Qed.

  Fixpoint wire_sem_equation_morph_fix
           (G: global) (H: history)
           (b b': Stream bool) (Eb: b ≡ b')
           (r r': Stream bool) (Er: r ≡ r')
           (e: equation)
           (Sem: sem_equation G H b r e) {struct Sem} :
    sem_equation G H b' r' e
  with wire_sem_node_morph_fix
         (G: global)
         (r r': Stream bool) (Er: r ≡ r')
         (f: ident)
         (xss xss': list (Stream value)) (Exss: EqSts value xss xss')
         (yss yss': list (Stream value)) (Eyss: EqSts value yss yss')
         (Sem: sem_node G r f xss yss) {struct Sem} :
    sem_node G r' f xss' yss'.
  Proof.
    - induction Sem.
      + econstructor; eauto.
        now rewrite <-Eb.
      + econstructor; eauto.
        * apply Forall2_impl_In with (P:=sem_lexp H b); eauto.
          intros; now rewrite <-Eb.
        * eapply wire_sem_node_morph_fix; eauto; reflexivity.
      + econstructor; eauto.
        * apply Forall2_impl_In with (P:=sem_lexp H b); eauto.
          intros; now rewrite <-Eb.
        * eapply wire_sem_node_morph_fix; eauto; try reflexivity.
          rewrite <-Er; reflexivity.
      + econstructor; eauto.
        * rewrite <-Eb; eauto.
        * subst.
          eapply sem_var_EqSt; eauto.
          now rewrite <-Er.
    - induction Sem.
      econstructor; eauto.
      + instantiate (1:=H).
        now rewrite <-Exss.
      + now rewrite <-Eyss.
      + apply Forall_impl with (P:=sem_equation G H (clocks_of xss) r); auto.
        apply wire_sem_equation_morph_fix; auto.
        now rewrite Exss.
  Admitted.

  Add Parametric Morphism G H : (sem_equation G H)
      with signature @EqSt bool ==> @EqSt bool ==> eq ==> Basics.impl
        as wire_sem_equation_morph.
  Proof.
    unfold Basics.impl; apply wire_sem_equation_morph_fix.
  Qed.

  Add Parametric Morphism G : (sem_node G)
      with signature @EqSt bool ==> eq ==> @EqSts value ==> @EqSts value ==> Basics.impl
        as wire_sem_node_morph.
  Proof.
    unfold Basics.impl; apply wire_sem_node_morph_fix.
  Qed.

End NLSEMANTICSCOINDWIRE.

(* Module NLSemanticsCoIndWireFun *)
(*        (Ids   : IDS) *)
(*        (Op    : OPERATORS) *)
(*        (OpAux : OPERATORS_AUX Op) *)
(*        (Clks  : CLOCKS    Ids) *)
(*        (Syn   : NLSYNTAX  Ids Op Clks) *)
(*        (Ord   : ORDERED   Ids Op Clks Syn) *)
(*        <: NLSEMANTICSCOINDWIRE Ids Op OpAux Clks Syn Ord. *)
(*   Include NLSEMANTICSCOINDWIRE Ids Op OpAux Clks Syn Ord. *)
(* End NLSemanticsCoIndWireFun. *)
