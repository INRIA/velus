Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.Clocks.
Require Import Velus.RMemory.

Require Import Velus.NLustre.NLExprSyntax.
Require Import Velus.NLustre.Stream.
Require Import Velus.NLustre.NLExprSemantics.
Require Import Velus.SyBloc.SBSyntax.
Require Import Velus.SyBloc.SBSemantics.

Require Import Velus.Obc.ObcSyntax.
Require Import Velus.Obc.ObcSemantics.

Require Import Velus.SyBlocToObc.Translation.

Require Import List.
Import List.ListNotations.
Require Import Setoid.

(* Open Scope positive. *)
Open Scope nat.
Open Scope list.

Module Type CORRECTNESS
       (Import Ids     : IDS)
       (Import Op      : OPERATORS)
       (Import OpAux   : OPERATORS_AUX       Op)
       (Import Clks    : CLOCKS          Ids)
       (Import ExprSyn : NLEXPRSYNTAX        Op)
       (Import SynSB   : SBSYNTAX        Ids Op       Clks ExprSyn)
       (Import Str     : STREAM              Op OpAux)
       (Import ExprSem : NLEXPRSEMANTICS Ids Op OpAux Clks ExprSyn              Str)
       (Import SemSB   : SBSEMANTICS     Ids Op OpAux Clks ExprSyn SynSB        Str ExprSem)
       (Import SynObc  : OBCSYNTAX       Ids Op OpAux)
       (Import SemObc  : OBCSEMANTICS    Ids Op OpAux                    SynObc)
       (Import Trans   : TRANSLATION     Ids Op OpAux Clks ExprSyn SynSB SynObc).

  Inductive Memory_Corres (P: SynSB.program) : ident -> state -> menv -> Prop :=
    MemC:
      forall b S me bl P',
        find_block b P = Some (bl, P') ->
        Forall (Memory_Corres_eq P S me) bl.(b_eqs) ->
        Memory_Corres P b S me

  with Memory_Corres_eq (P: SynSB.program) : state -> menv -> equation -> Prop :=
       | MemC_EqDef:
           forall S me x ck ce,
             Memory_Corres_eq P S me (EqDef x ck ce)
       | MemC_EqNext:
           forall S me x ck le,
             (forall v, find_val x S = Some v ->
                   find_val x me = Some v) ->
             Memory_Corres_eq P S me (EqNext x ck le)
       | MemC_EqReset:
           forall S me s ck b,
             (forall Ss, sub_inst s S Ss ->
                    exists me', sub_inst s me me') ->
               Memory_Corres_eq P S me (EqReset s ck b)
       | MemC_EqCall:
           forall S me s xs ck rst b les,
             (forall Ss, sub_inst s S Ss ->
                    exists me', sub_inst s me me'
                           /\ Memory_Corres P b Ss me') ->
               Memory_Corres_eq P S me (EqCall s xs ck rst b les).

  Definition equiv_env (in_domain: ident -> Prop) (R: env) (mems: PS.t) (ve: venv) (me: menv) : Prop :=
    forall x c,
      in_domain x ->
      sem_var_instant R x (present c) ->
      if PS.mem x mems
      then find_val x me = Some c
      else Env.find x ve = Some c.
