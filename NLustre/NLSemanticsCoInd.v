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

Module Type NLSEMANTICSCOIND
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op)
       (Import Clks  : CLOCKS    Ids)
       (Import Syn   : NLSYNTAX  Ids Op Clks)
       (Import Comm  : NLSEMANTICSCOMMON Ids Op OpAux Clks Syn)
       (Import Ord   : ORDERED   Ids Op Clks Syn).

  CoFixpoint fby1 (v c: val) (xs: Stream value) : Stream value :=
    match xs with
    | absent ::: xs => absent ::: fby1 v c xs
    | present x ::: xs => present v ::: fby1 x c xs
    end.

  CoFixpoint fby (c: val) (xs: Stream value) : Stream value :=
    match xs with
    | absent ::: xs => absent ::: fby c xs
    | present x ::: xs => present c ::: fby1 x c xs
    end.

  (* CoInductive fby1' *)
  (*   : val -> val -> Stream value -> Stream value -> Prop := *)
  (* | Fby1A: *)
  (*     forall v c xs ys, *)
  (*       fby1' v c xs ys -> *)
  (*       fby1' v c (absent ::: xs) (absent ::: ys) *)
  (* | Fby1P: *)
  (*     forall v x c xs ys, *)
  (*       fby1' x c xs ys -> *)
  (*       fby1' v c (present x ::: xs) (present v ::: ys). *)

  (* CoInductive fby': val -> Stream value -> Stream value -> Prop := *)
  (* | FbyA: *)
  (*     forall c xs ys, *)
  (*       fby' c xs ys -> *)
  (*       fby' c (absent ::: xs) (absent ::: ys) *)
  (* | FbyP: *)
  (*     forall x c xs ys, *)
  (*       fby1' x c xs ys -> *)
  (*       fby' c (present x ::: xs) (present c ::: ys). *)

  (* Fact fby1_spec: *)
  (*   forall xs ys v c, ys = fby1 v c xs <-> fby1' v c xs ys. *)
  (* Proof.  *)
  (*   split. *)
  (*   - revert xs ys v c; cofix H; intros. *)
  (*     subst. *)
  (*     rewrite unfold_Stream. *)
  (*     destruct xs as [[|w]]; simpl; constructor; auto. *)
  (*   - intros. *)
  (*     rewrite unfold_Stream. *)
  (*     inv H; simpl. *)

  (*     revert xs ys v c; cofix H; intros. *)

  (* Fact foo: *)
  (*   forall xs ys c, ys = fby c xs <-> fby' c xs ys. *)
  (* Proof. *)
  (*   split. *)
  (*   - revert xs ys k; cofix H; intros. *)
  (*     subst. *)
  (*     rewrite unfold_Stream. *)
  (*     destruct xs as [[|v]]; simpl; constructor; auto. *)

  (*   cofix. *)
  (*   destruct xs. *)
  (*   rewrite unfold_Stream. *)
  (*   simpl. *)

  (* CoFixpoint cut (bs: Stream bool) (xs: Stream value) : Stream value := *)
  (*   match bs, xs with *)
  (*     b ::: bs', x ::: xs' => if b then xs else absent ::: cut bs' xs' *)
  (*   end. *)

  (* CoFixpoint cut_bool (bs: Stream bool) : Stream bool := *)
  (*   match bs with *)
  (*     b ::: bs => false ::: if b then bs else cut_bool bs *)
  (*   end. *)

  (* CoFixpoint switch (bs: Stream bool) (xs ys: Stream value) : Stream value := *)
  (*   match bs, xs, ys with *)
  (*     b ::: bs', x ::: xs', y ::: ys' => if b then ys else x ::: switch bs' xs' ys' *)
  (*   end.  *)

  CoFixpoint mask {A} (opaque: A) (n: nat) (rs: Stream bool) (xs: Stream A) : Stream A :=
    match n, rs, xs with
    | 0,  false ::: rs, x ::: xs =>
      x ::: mask opaque 0 rs xs
    | 0, true ::: _, _ ::: _ =>
      Streams.const opaque
    | S 0, true ::: rs, x ::: xs =>
      x ::: mask opaque 0 rs xs
    | S n, false ::: rs, x ::: xs =>
      opaque ::: mask opaque (S n) rs xs
    | S n, true ::: rs, x ::: xs =>
      opaque ::: mask opaque n rs xs
    end.

  Definition mask_v := mask absent.
  Definition mask_b := mask false.

  Fixpoint take {A} (n: nat) (s: Stream A) : list A :=
    match n with
    | O => nil
    | S n => hd s :: take n (tl s)
    end.

  Fixpoint drop {A} (n: nat) (s: Stream A) {struct n} : Stream A :=
    match n with
    | 0 => s
    | S n => drop n (tl s)
    end.

  Definition r :=
    false ::: false ::: false ::: true ::: false ::: false ::: false ::: false ::: false ::: true ::: false ::: false ::: false ::: true ::: Streams.const false.

  Notation "⊥" := (absent) (at level 50).
  Notation "⇑" := (present true_val).
  Notation "⇓" := (present false_val).


  CoFixpoint x := ⇓ ::: ⇑ ::: x.

  Eval simpl in (take 16 r, take 16 x,
                 take 16 (mask_v 0 r x),
                 take 16 (mask_v 1 r x),
                 take 16 (mask_v 2 r x),
                 take 16 (mask_v 3 r x),
                 take 16 (mask_v 4 r x)).

  CoFixpoint flatten_masks (bs: Stream bool) (xss: Stream (Stream value)) : Stream value :=
    let xss := if hd bs then tl xss else xss in
    hd (hd xss) ::: flatten_masks (tl bs) (map (@tl value) xss).

  CoFixpoint masks_from (n: nat) (rs: Stream bool) (xs: Stream value) : Stream (Stream value) :=
    mask_v n rs xs ::: masks_from (n + 1) rs xs.

  Definition masks := masks_from 0.

  Eval simpl in take 16 (flatten_masks r (masks r x)).

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
          os = fby (sem_const c0) es ->
          sem_var H x os ->
          sem_equation H b (EqFby x ck c0 e)

    with sem_reset: ident -> Stream bool -> list (Stream value) -> list (Stream value) -> Prop :=
         | SReset:
             forall f r xss yss,
               (forall n, sem_node f (List.map (mask_v n r) xss) (List.map (mask_v n r) yss)) ->
               sem_reset f r xss yss

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
    Variable P_reset: ident -> Stream bool -> list (Stream value) -> list (Stream value) -> Prop.
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
        os = fby (sem_const c0) es ->
        sem_var H x os ->
        P_equation H b (EqFby x ck c0 e).

    Hypothesis ResetCase:
      forall f r xss yss,
        (forall n, sem_node G f (List.map (mask_v n r) xss) (List.map (mask_v n r) yss)) ->
        (forall n, P_node f (List.map (mask_v n r) xss) (List.map (mask_v n r) yss)) ->
        P_reset f r xss yss.

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
           (f: ident) (r: Stream bool) (xss oss: list (Stream value))
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

End NLSEMANTICSCOIND.

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
