From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Coq Require Import Streams.
From Coq Require Import Sorting.Permutation.

From Coq Require Import FSets.FMapPositive.
From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Lustre.LSyntax.
From Velus Require Import Streams.

(** * Lustre semantics *)

Module Type LSEMANTICS
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Op)
       (Import Str   : STREAMS       Op OpAux)
       (Import Syn   : LSYNTAX   Ids Op).

  Definition history := Env.t (Stream value).

  CoInductive fby1
    : val -> Stream value -> Stream value -> Stream value -> Prop :=
  | Fby1A:
      forall v xs ys rs,
        fby1 v xs ys rs ->
        fby1 v (absent ::: xs) (absent ::: ys) (absent ::: rs)
  | Fby1P:
      forall v w s xs ys rs,
        fby1 s xs ys rs ->
        fby1 v (present w ::: xs) (present s ::: ys) (present v ::: rs).

  CoInductive fby: Stream value -> Stream value -> Stream value -> Prop :=
  | FbyA:
      forall xs ys rs,
        fby xs ys rs ->
        fby (absent ::: xs) (absent ::: ys) (absent ::: rs)
  | FbyP:
      forall x y xs ys rs,
        fby1 y xs ys rs ->
        fby (present x ::: xs) (present y ::: ys) (present x ::: rs).


  CoFixpoint sclocksof (ss: list (Stream value)) : Stream bool :=
    existsb (fun s=> hd s <>b absent) ss ::: sclocksof (List.map (@tl value) ss).

  (* TODO: Use everywhere, esp. in LustreElab.v *)
  (* TODO: replace idents with (list ident) *)
  Definition idents xs := List.map (@fst ident (type * clock)) xs.

  Inductive sem_var: history -> ident -> Stream value -> Prop :=
    sem_var_intro:
      forall H x xs xs',
        Env.find x H = Some xs' ->
        xs ≡ xs' ->
        sem_var H x xs.

  CoInductive reset_of: Stream value -> Stream bool -> Prop :=
    reset_of_intro:
      forall v vs b bs,
        reset_of vs bs ->
        value_to_bool v = Some b ->
        reset_of (v ::: vs) (b ::: bs).

  Section NodeSemantics.

    Variable G : global.

    Inductive sem_exp
      : history -> Stream bool -> exp -> list (Stream value) -> Prop :=
    | Sconst:
        forall H b c,
          sem_exp H b (Econst c) [const b c]

    | Svar:
        forall H b x s ann,
          sem_var H x s ->
          sem_exp H b (Evar x ann) [s]

    | Sunop:
        forall H b e op ty s o ann,
          sem_exp H b e [s] ->
          typeof e = [ty] ->
          lift1 op ty s o ->
          sem_exp H b (Eunop op e ann) [o]

    | Sbinop:
        forall H b e1 e2 op ty1 ty2 s1 s2 o ann,
          sem_exp H b e1 [s1] ->
          sem_exp H b e2 [s2] ->
          typeof e1 = [ty1] ->
          typeof e2 = [ty2] ->
          lift2 op ty1 ty2 s1 s2 o ->
          sem_exp H b (Ebinop op e1 e2 ann) [o]

    | Sfby:
        forall H b e0s es anns s0ss sss os,
          Forall2 (sem_exp H b) e0s s0ss ->
          Forall2 (sem_exp H b) es sss ->
          Forall3 fby (concat s0ss) (concat sss) os ->
          sem_exp H b (Efby e0s es anns) os

    | Swhen:
        forall H b x s k es lann ss os,
          Forall2 (sem_exp H b) es ss ->
          sem_var H x s ->
          Forall2 (when k s) (concat ss) os ->
          sem_exp H b (Ewhen es x k lann) os

    | Smerge:
        forall H b x s ets efs lann ts fs os,
          sem_var H x s ->
          Forall2 (sem_exp H b) ets ts ->
          Forall2 (sem_exp H b) efs fs ->
          Forall3 (merge s) (concat ts) (concat fs) os ->
          sem_exp H b (Emerge x ets efs lann) os

    | Site:
        forall H b e s ets efs lann ts fs os,
          sem_exp H b e [s] ->
          Forall2 (sem_exp H b) ets ts ->
          Forall2 (sem_exp H b) efs fs ->
          Forall3 (ite s) (concat ts) (concat fs) os ->
          sem_exp H b (Eite e ets efs lann) os

    | Sapp:
        forall H b f es lann ss os,
          Forall2 (sem_exp H b) es ss ->
          sem_node f (concat ss) os ->
          sem_exp H b (Eapp f es None lann) os

    | Sreset:
        forall H b f es r lann ss os rs bs,
          Forall2 (sem_exp H b) es ss ->
          sem_exp H b r [rs] ->
          reset_of rs bs ->
          (forall k, sem_node f (List.map (mask k bs) (concat ss)) (List.map (mask k bs) os)) ->
          sem_exp H b (Eapp f es (Some r) lann) os

    with sem_equation: history -> Stream bool -> equation -> Prop :=
           Seq:
             forall H b xs es ss,
               Forall2 (sem_exp H b) es ss ->
               Forall2 (sem_var H) xs (concat ss) ->
               sem_equation H b (xs, es)

    with sem_node: ident -> list (Stream value) -> list (Stream value) -> Prop :=
           Snode:
             forall f ss os n H b,
               find_node f G = Some n ->
               Forall2 (sem_var H) (idents n.(n_in)) ss ->
               Forall2 (sem_var H) (idents n.(n_out)) os ->
               Forall (sem_equation H b) n.(n_eqs) ->
               b = sclocksof ss ->
               sem_node f ss os.

  End NodeSemantics.

  Definition sem_nodes (G: global) : Prop :=
    Forall (fun n => exists xs ys, sem_node G n.(n_name) xs ys) G.

  (* TODO: tidy up file *)

  (** Custom induction schemes *)

  Section sem_exp_ind2.
    Variable G : global.

    Variable P_exp : history -> Stream bool -> exp -> list (Stream value) -> Prop.
    Variable P_equation : history -> Stream bool -> equation -> Prop.
    Variable P_node : ident -> list (Stream value) -> list (Stream value) -> Prop.

    Hypothesis ConstCase:
      forall H b c,
        P_exp H b (Econst c) [const b c].

    Hypothesis VarCase:
      forall H b x s ann,
        sem_var H x s ->
        P_exp H b (Evar x ann) [s].

    Hypothesis UnopCase:
      forall H b e op ty s o ann,
        sem_exp G H b e [s] ->
        P_exp H b e [s] ->
        typeof e = [ty] ->
        lift1 op ty s o ->
        P_exp H b (Eunop op e ann) [o].

    Hypothesis BinopCase:
      forall H b e1 e2 op ty1 ty2 s1 s2 o ann,
        sem_exp G H b e1 [s1] ->
        P_exp H b e1 [s1] ->
        sem_exp G H b e2 [s2] ->
        P_exp H b e2 [s2] ->
        typeof e1 = [ty1] ->
        typeof e2 = [ty2] ->
        lift2 op ty1 ty2 s1 s2 o ->
        P_exp H b (Ebinop op e1 e2 ann) [o].

    Hypothesis FbyCase:
      forall H b e0s es anns s0ss sss os,
        Forall2 (sem_exp G H b) e0s s0ss ->
        Forall2 (P_exp H b) e0s s0ss ->
        Forall2 (sem_exp G H b) es sss ->
        Forall2 (P_exp H b) es sss ->
        Forall3 fby (concat s0ss) (concat sss) os ->
        P_exp H b (Efby e0s es anns) os.

    Hypothesis WhenCase:
      forall H b x s k es lann ss os,
        Forall2 (sem_exp G H b) es ss ->
        Forall2 (P_exp H b) es ss ->
        sem_var H x s ->
        Forall2 (when k s) (concat ss) os ->
        P_exp H b (Ewhen es x k lann) os.

    Hypothesis MergeCase:
      forall H b x s ets efs lann ts fs os,
        sem_var H x s ->
        Forall2 (sem_exp G H b) ets ts ->
        Forall2 (P_exp H b) ets ts ->
        Forall2 (sem_exp G H b) efs fs ->
        Forall2 (P_exp H b) efs fs ->
        Forall3 (merge s) (concat ts) (concat fs) os ->
        P_exp H b (Emerge x ets efs lann) os.

    Hypothesis IteCase:
      forall H b e s ets efs lann ts fs os,
        sem_exp G H b e [s] ->
        P_exp H b e [s] ->
        Forall2 (sem_exp G H b) ets ts ->
        Forall2 (P_exp H b) ets ts ->
        Forall2 (sem_exp G H b) efs fs ->
        Forall2 (P_exp H b) efs fs ->
        Forall3 (ite s) (concat ts) (concat fs) os ->
        P_exp H b (Eite e ets efs lann) os.

    Hypothesis AppCase:
      forall H b f es lann ss os,
        Forall2 (sem_exp G H b) es ss ->
        Forall2 (P_exp H b) es ss ->
        sem_node G f (concat ss) os ->
        P_node f (concat ss) os ->
        P_exp H b (Eapp f es None lann) os.

    Hypothesis ResetCase:
      forall H b f es r lann ss os rs bs,
        Forall2 (sem_exp G H b) es ss ->
        Forall2 (P_exp H b) es ss ->
        sem_exp G H b r [rs] ->
        P_exp H b r [rs] ->
        reset_of rs bs ->
        (forall k, sem_node G f (List.map (mask k bs) (concat ss)) (List.map (mask k bs) os)
              /\ P_node f (List.map (mask k bs) (concat ss)) (List.map (mask k bs) os)) ->
        P_exp H b (Eapp f es (Some r) lann) os.

    Hypothesis Equation:
      forall H b xs es ss,
        Forall2 (sem_exp G H b) es ss ->
        Forall2 (P_exp H b) es ss ->
        Forall2 (sem_var H) xs (concat ss) ->
        P_equation H b (xs, es).

    Hypothesis Node:
      forall f ss os n H b,
        find_node f G = Some n ->
        Forall2 (sem_var H) (idents n.(n_in)) ss ->
        Forall2 (sem_var H) (idents n.(n_out)) os ->
        Forall (sem_equation G H b) n.(n_eqs) ->
        Forall (P_equation H b) n.(n_eqs) ->
        b = sclocksof ss ->
        P_node f ss os.

    Local Ltac SolveForall :=
      match goal with
      | H: Forall ?P1 ?l |- Forall ?P2 ?l =>
        induction H; auto
      | H: Forall2 ?P1 ?l1 ?l2 |- Forall2 ?P2 ?l1 ?l2 =>
        induction H; auto
      | _ => idtac
      end.

    Fixpoint sem_exp_ind2
             (H: history) (b: Stream bool) (e: exp) (ss: list (Stream value))
             (Sem: sem_exp G H b e ss)
             {struct Sem}
      : P_exp H b e ss
    with sem_equation_ind2
           (H: history) (b: Stream bool) (e: equation)
           (Sem: sem_equation G H b e)
           {struct Sem}
         : P_equation H b e
    with sem_node_ind2
           (f: ident) (ss os: list (Stream value))
           (Sem: sem_node G f ss os)
           {struct Sem}
         : P_node f ss os.
    Proof.
      - destruct Sem; eauto.
        + eapply FbyCase; eauto; clear H2; SolveForall.
        + eapply WhenCase; eauto; clear H2; SolveForall.
        + eapply MergeCase; eauto; clear H3; SolveForall.
        + eapply IteCase; eauto; clear H2; SolveForall.
        + eapply AppCase; eauto; clear H1; SolveForall.
        + eapply ResetCase; eauto; clear H2; SolveForall.
      - destruct Sem.
        eapply Equation with (ss:=ss); eauto; clear H1; SolveForall.
      - destruct Sem.
        eapply Node; eauto.
        SolveForall.
    Qed.

  End sem_exp_ind2.

End LSEMANTICS.

Module LSemanticsFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Str   : STREAMS       Op OpAux)
       (Syn   : LSYNTAX   Ids Op)
<: LSEMANTICS Ids Op OpAux Str Syn.
  Include LSEMANTICS Ids Op OpAux Str Syn.
End LSemanticsFun.
