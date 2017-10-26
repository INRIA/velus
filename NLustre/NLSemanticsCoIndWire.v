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

Module Type NLSEMANTICSCOINDWIRE
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op)
       (Import Clks  : CLOCKS    Ids)
       (Import Syn   : NLSYNTAX  Ids Op Clks)
       (Import Comm  : NLSEMANTICSCOMMON Ids Op OpAux Clks Syn)
       (Import Ord   : ORDERED   Ids Op Clks Syn).

  CoFixpoint fby1 (rs: Stream bool) (v c: val) (xs: Stream value) : Stream value :=
    match rs, xs with
    | false ::: rs, absent ::: xs => absent ::: fby1 rs v c xs
    | true ::: rs, absent ::: xs => absent ::: fby rs c xs
    | false ::: rs, present x ::: xs => present v ::: fby1 rs x c xs
    | true ::: rs, present x ::: xs => present c ::: fby1 rs x c xs
    end

  with fby (rs: Stream bool) (c: val) (xs: Stream value) : Stream value :=
         match xs with
         | absent ::: xs => absent ::: fby (tl rs) c xs
         | present x ::: xs => present c ::: fby1 (tl rs) x c xs
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
