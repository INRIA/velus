Require Import List.
Import List.ListNotations.
Open Scope list_scope.
Require Import Coq.Sorting.Permutation.

Require Import Coq.FSets.FMapPositive.
Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.Clocks.
Require Import Velus.NLustre.NLSyntax.
Require Import Velus.NLustre.NLSemanticsCommon.
Require Import Velus.NLustre.Ordered.
Require Import Streams.

(** * The NLustre semantics *)

(**

  We provide a "standard" dataflow semantics relating an environment
  of streams to a stream of outputs.

 *)

Module Type NLSEMANTICSCOINDREC
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op)
       (Import Clks  : CLOCKS    Ids)
       (Import Syn   : NLSYNTAX  Ids Op Clks)
       (Import Comm  : NLSEMANTICSCOMMON Ids Op OpAux Clks Syn)
       (Import Ord   : ORDERED   Ids Op Clks Syn).

  CoInductive fby1
    : val -> val -> Stream value -> Stream value -> Prop :=
  | Fby1A:
      forall v c xs ys,
        fby1 v c xs ys ->
        fby1 v c (absent ::: xs) (absent ::: ys)
  | Fby1P:
      forall v x c xs ys,
        fby1 x c xs ys ->
        fby1 v c (present x ::: xs) (present v ::: ys)

  with fby: val -> Stream value -> Stream value -> Prop :=
  | FbyA:
      forall c xs ys,
        fby c xs ys ->
        fby c (absent ::: xs) (absent ::: ys)
  | FbyP:
      forall x c xs ys,
        fby1 x c xs ys ->
        fby c (present x ::: xs) (present c ::: ys).

  Definition reset_of : Stream value -> Stream value :=
    map (fun x => match x with
               | present x => if (x ==b true_val) then present x else present false_val
               | _ => present false_val
               end).

  CoInductive true_s : Stream value -> Stream value -> Prop :=
   | true_s_A:
      forall xs ts,
        true_s xs ts ->
        true_s (absent ::: xs) (absent ::: ts)
   | true_s_P:
      forall x xs ts,
        true_s xs ts ->
        true_s (present x ::: xs) (present true_val ::: ts).

  CoFixpoint true_s' (ss: Stream value) : Stream value :=
    match ss with
    | absent    ::: ss => absent ::: true_s' ss
    | present _ ::: ss => present true_val ::: true_s' ss
    end.

  CoInductive once : Stream value -> Stream value -> Prop :=
  | once_A:
      forall bs ys,
        once bs ys ->
        once (absent ::: bs) (absent ::: ys)
  | once_PF:
      forall bs ys,
        once bs ys ->
        once (present false_val ::: bs) (present false_val ::: ys)
  | once_PT:
      forall bs ts,
        true_s bs ts ->
        once (present true_val ::: bs) ts.

  CoFixpoint once' (ss: Stream value) : Stream value :=
    match ss with
    | absent ::: ss => absent ::: once' ss
    | present s ::: ss =>
      present s :::
      if s ==b true_val then
        true_s' ss
      else
        once' ss
    end.

  CoInductive switch : Stream value -> Stream value -> Stream value -> Stream value -> Prop :=
  | switch_A:
      forall bs xs ys zs,
        switch bs xs ys zs ->
        switch (absent ::: bs) (absent ::: xs) ys (absent ::: zs)
  | switch_PF:
      forall bs x xs ys zs,
        switch bs xs ys zs ->
        switch (present false_val ::: bs) (present x ::: xs) ys (present x ::: zs)
  | switch_PT:
      forall bs x xs ys,
        switch (present true_val ::: bs) (present x ::: xs) ys ys.

  Definition pre_ini (v0: val) (xs: Stream value) : Stream value :=
    match xs with
      x ::: xs => present v0 ::: xs
    end.

  Section NodeSemantics.

    Variable G: global.

    Inductive sem_equation: history -> Stream bool -> equation -> Prop :=
    | SeqDef:
        forall H b x ck e es,
          sem_cexp H b e es ->
          sem_var H x es ->
          sem_equation H b (EqDef x ck e)
    | SeqApp:
        forall H b ys ck f es ess oss,
          Forall2 (sem_lexp H b) es ess ->
          sem_node f ess oss ->
          Forall2 (sem_var H) ys oss ->
          sem_equation H b (EqApp ys ck f es None)
    | SeqReset:
        forall H b ys ck f es x xs ess oss,
          Forall2 (sem_lexp H b) es ess ->
          sem_var H x xs ->
          sem_reset f (reset_of xs) ess oss ->
          Forall2 (sem_var H) ys oss ->
          sem_equation H b (EqApp ys ck f es (Some x))
    | SeqFby:
        forall H b x ck c0 e es os,
          sem_lexp H b e es ->
          fby (sem_const c0) es os ->
          sem_var H x os ->
          sem_equation H b (EqFby x ck c0 e)

    with sem_reset: ident -> Stream value -> list (Stream value) -> list (Stream value) -> Prop :=
         | SReset:
             forall f r once_r r' xss xss' yss rst oss,
               sem_node f xss yss ->
               once_r = once' r ->
               Forall2 (fun xs xs' => when true xs once_r xs') xss xss' ->
               when true r once_r r' ->
               sem_reset f (pre_ini false_val r') xss' rst ->
               Forall3 (switch r) yss rst oss ->
               sem_reset f r xss oss

    with sem_node: ident -> list (Stream value) -> list (Stream value) -> Prop :=
         | SNode:
             forall H f n xss oss,
               find_node f G = Some n ->
               Forall2 (sem_var H) (idents n.(n_in)) xss ->
               Forall2 (sem_var H) (idents n.(n_out)) oss ->
               Forall (sem_equation H (clocks_of xss)) n.(n_eqs) ->
               sem_node f xss oss.

  End NodeSemantics.

  Section SemInd.

    Variable G: global.

    Variable P_equation: history -> Stream bool -> equation -> Prop.
    Variable P_reset: ident -> Stream value -> list (Stream value) -> list (Stream value) -> Prop.
    Variable P_node: ident -> list (Stream value) -> list (Stream value) -> Prop.

    Hypothesis EqDefCase:
      forall H b x ck e es,
        sem_cexp H b e es ->
        sem_var H x es ->
        P_equation H b (EqDef x ck e).

    Hypothesis EqAppCase:
      forall H b ys ck f es ess oss,
        Forall2 (sem_lexp H b) es ess ->
        sem_node G f ess oss ->
        Forall2 (sem_var H) ys oss ->
        P_node f ess oss ->
        P_equation H b (EqApp ys ck f es None).

    Hypothesis EqResetCase:
      forall H b ys ck f es x xs ess oss,
        Forall2 (sem_lexp H b) es ess ->
        sem_var H x xs ->
        sem_reset G f (reset_of xs) ess oss ->
        Forall2 (sem_var H) ys oss ->
        P_reset f (reset_of xs) ess oss ->
        P_equation H b (EqApp ys ck f es (Some x)).

    Hypothesis EqFbyCase:
      forall H b x ck c0 e es os,
        sem_lexp H b e es ->
        fby (sem_const c0) es os ->
        sem_var H x os ->
        P_equation H b (EqFby x ck c0 e).

    Hypothesis ResetCase:
      forall f r once_r r' xss xss' yss rst oss,
        sem_node G f xss yss ->
        once_r = once' r ->
        Forall2 (fun xs xs' => when true xs once_r xs') xss xss' ->
        when true r once_r r' ->
        sem_reset G f (pre_ini false_val r') xss' rst ->
        Forall3 (switch r) yss rst oss ->
        P_node f xss yss ->
        P_reset f (pre_ini false_val r') xss' rst ->
        P_reset f r xss oss.

    Hypothesis NodeCase:
      forall H f n xss oss,
        find_node f G = Some n ->
        Forall2 (sem_var H) (idents n.(n_in)) xss ->
        Forall2 (sem_var H) (idents n.(n_out)) oss ->
        Forall (sem_equation G H (clocks_of xss)) n.(n_eqs) ->
        Forall (P_equation H (clocks_of xss)) n.(n_eqs) ->
        P_node f xss oss.

    Fixpoint sem_equation_mult
             (H: history) (b: Stream bool) (e: equation)
             (Sem: sem_equation G H b e) {struct Sem}
      : P_equation H b e
    with sem_reset_mult
           (f: ident) (r: Stream value) (xss oss: list (Stream value))
           (Sem: sem_reset G f r xss oss) {struct Sem}
         : P_reset f r xss oss
    with sem_node_mult
           (f: ident) (xss oss: list (Stream value))
           (Sem: sem_node G f xss oss) {struct Sem}
         : P_node f xss oss.
    Proof.
      - destruct Sem; eauto.
      - destruct Sem; eauto.
      - destruct Sem; eauto.
        eapply NodeCase; eauto.
        induction H3; auto.
    Qed.

    Combined Scheme sem_equation_node_ind from sem_equation_mult, sem_node_mult, sem_reset_mult.

  End SemInd.

End NLSEMANTICSCOINDREC.

(* Module NLSemanticsCoIndRecFun *)
(*        (Ids   : IDS) *)
(*        (Op    : OPERATORS) *)
(*        (OpAux : OPERATORS_AUX Op) *)
(*        (Clks  : CLOCKS    Ids) *)
(*        (Syn   : NLSYNTAX  Ids Op Clks) *)
(*        (Ord   : ORDERED   Ids Op Clks Syn) *)
(*        <: NLSEMANTICSCOINDREC Ids Op OpAux Clks Syn Ord. *)
(*   Include NLSEMANTICSCOINDREC Ids Op OpAux Clks Syn Ord. *)
(* End NLSemanticsCoIndRecFun. *)
