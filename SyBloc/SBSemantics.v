Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Require Import Setoid.
Require Import Morphisms.

Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.Clocks.
Require Import Velus.RMemory.
Require Import Velus.NLustre.NLExprSyntax.
Require Import Velus.SyBloc.SBSyntax.
Require Import Velus.NLustre.NLExprSemantics.
Require Import Velus.NLustre.Stream.

Module Type SBSEMANTICS
       (Import Ids     : IDS)
       (Import Op      : OPERATORS)
       (Import OpAux   : OPERATORS_AUX       Op)
       (Import Clks    : CLOCKS          Ids)
       (Import ExprSyn : NLEXPRSYNTAX        Op)
       (Import Syn     : SBSYNTAX        Ids Op Clks ExprSyn)
       (Import Str     : STREAM              Op OpAux)
       (Import ExprSem : NLEXPRSEMANTICS Ids Op OpAux Clks ExprSyn Str).

  Record mvalue :=
    Mvalue { content_i: val;
             reset_i: bool
           }.

  Record mvalues :=
    Mvalues { content: stream val;
              reset: stream bool
            }.

  Definition memory := RMemory.memory mvalue.
  Definition memories := RMemory.memory mvalues.

  Inductive reset_regs: stream bool -> memories -> Prop :=
    reset_regs_intro:
      forall M rs,
        (forall x mvs,
            find_val x M = Some mvs ->
            forall n, rs n = true -> mvs.(reset) n = true) ->
        (forall x M',
            sub_inst x M M' ->
            reset_regs rs M') ->
        reset_regs rs M.

  Inductive mfby: ident -> val -> stream value -> memories -> stream value -> Prop :=
    mfby_intro:
      forall x mvs v0 ls M xs,
        find_val x M = Some mvs ->
        mvs.(content) 0 = v0 ->
        (forall n, match ls n with
              | absent =>
                mvs.(content) (S n) = (if mvs.(reset) (S n) then v0 else mvs.(content) n)
                /\ xs n = absent
              | present v =>
                mvs.(content) (S n) = (if mvs.(reset) (S n) then v0 else v)
                /\ xs n = present (mvs.(content) n)
              end) ->
        mfby x v0 ls M xs.

  Section BlockSemantics.

    Variable P: program.

    Inductive sem_equation: stream bool -> history -> memories -> equation -> Prop :=
    | SEqDef:
        forall bk H M x xs ck ce,
          sem_var H x xs ->
          sem_caexp bk H ck ce xs ->
          sem_equation bk H M (EqDef x ck ce)
    | SEqFby:
        forall bk H M x ck c0 e xs ls,
          sem_var H x xs ->
          sem_laexp bk H ck e ls ->
          mfby x (sem_const c0) ls M xs ->
          sem_equation bk H M (EqFby x ck c0 e)
    | SEqReset:
        forall bk H M ck b i r rs M',
          sem_var H r rs ->
          sub_inst i M M' ->
          reset_regs (reset_of rs) M' ->
          sem_equation bk H M (EqReset ck b i r)
    | SEqCall:
        forall bk H M ys M' ck b i es ess oss,
          sem_laexps bk H ck es ess ->
          sub_inst i M M' ->
          sem_block b M' ess oss ->
          sem_vars H ys oss ->
          sem_equation bk H M (EqCall ys ck b i es)

    with sem_block: ident -> memories -> stream (list value) -> stream (list value) -> Prop :=
           SBlock:
             forall b bl P' M H xss yss bk,
               clock_of xss bk ->
               find_block b P = Some (bl, P') ->
               sem_vars H (map fst bl.(b_in)) xss ->
               sem_vars H (map fst bl.(b_out)) yss ->
               same_clock xss ->
               same_clock yss ->
               (forall n, absent_list (xss n) <-> absent_list (yss n)) ->
               Forall (sem_equation bk H M) bl.(b_eqs) ->
               sem_block b M xss yss.

  End BlockSemantics.

  Section sem_block_mult.
    Variable P: program.

    Variable P_equation: stream bool -> history -> memories -> equation -> Prop.
    Variable P_block: ident -> memories -> stream (list value) -> stream (list value) -> Prop.

    Hypothesis EqDefCase:
      forall bk H M x xs ck ce,
        sem_var H x xs ->
        sem_caexp bk H ck ce xs ->
        P_equation bk H M (EqDef x ck ce).

    Hypothesis EqFbyCase:
      forall bk H M x ck c0 e xs ls,
        sem_var H x xs ->
        sem_laexp bk H ck e ls ->
        mfby x (sem_const c0) ls M xs ->
        P_equation bk H M (EqFby x ck c0 e).

    Hypothesis EqResetCase:
      forall bk H M ck b i r rs M',
        sem_var H r rs ->
        sub_inst i M M' ->
        reset_regs (reset_of rs) M' ->
        P_equation bk H M (EqReset ck b i r).

    Hypothesis EqCallCase:
      forall bk H M ys M' ck b i es ess oss,
        sem_laexps bk H ck es ess ->
        sub_inst i M M' ->
        sem_block P b M' ess oss ->
        sem_vars H ys oss ->
        P_block b M' ess oss ->
        P_equation bk H M (EqCall ys ck b i es).

    Hypothesis BlockCase:
      forall b bl P' M H xss yss bk,
        clock_of xss bk ->
        find_block b P = Some (bl, P') ->
        sem_vars H (map fst bl.(b_in)) xss ->
        sem_vars H (map fst bl.(b_out)) yss ->
        same_clock xss ->
        same_clock yss ->
        (forall n, absent_list (xss n) <-> absent_list (yss n)) ->
        Forall (sem_equation P bk H M) bl.(b_eqs) ->
        Forall (P_equation bk H M) bl.(b_eqs) ->
        P_block b M xss yss.

    Fixpoint sem_equation_mult
            (b: stream bool) (H: history) (M: memories) (e: equation)
            (Sem: sem_equation P b H M e) {struct Sem}
      : P_equation b H M e
    with sem_block_mult
           (f: ident) (M: memories) (xss oss: stream (list value))
           (Sem: sem_block P f M xss oss) {struct Sem}
         : P_block f M xss oss.
    Proof.
      - destruct Sem; eauto.
      - destruct Sem.
        eapply BlockCase; eauto.
        match goal with H: Forall _ _ |- _ => induction H; auto end.
    Qed.

    Combined Scheme sem_equation_block_ind from
             sem_equation_mult, sem_block_mult.

  End sem_block_mult.

  (** Morphisms properties *)

  Add Parametric Morphism P b M: (sem_block P b M)
      with signature eq_str ==> eq_str ==> Basics.impl
        as sem_node_eq_str.
  Proof.
    intros ** E1 ? ? E2 Block.
    inv Block.
    econstructor; eauto; intro; try rewrite <-E1; try rewrite <-E2; auto.
  Qed.

  Lemma sem_block_wf:
    forall P f M xss yss,
      sem_block P f M xss yss ->
      wf_streams xss /\ wf_streams yss.
  Proof.
    intros ** Sem; split; inv Sem;
      assert_const_length xss; assert_const_length yss; auto.
  Qed.

End SBSEMANTICS.
