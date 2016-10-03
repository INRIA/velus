Require Import Rustre.Common.
Require Import Rustre.Operators.
Require Import Rustre.Dataflow.Syntax.

Require Import List.
Import List.ListNotations.
Open Scope list_scope.

(** * CoreDF typing *)

(** 

  Typing judgements for CoreDF and resulting properties.
  Classify CoreDF programs which are statically well-formed.

 *)

Module Type TYPING
       (Import Ids : IDS)
       (Import Op  : OPERATORS)
       (Import Syn : SYNTAX Ids Op).

  (** ** Clocks *)

  Section WellTyped.

    Variable G    : global.
    Variable vars : list (ident * type).

    Inductive wt_clock : clock -> Prop :=
    | wt_Cbase:
        wt_clock Cbase
    | wt_Con: forall ck x b,
        In (x, bool_type) vars ->
        wt_clock ck ->
        wt_clock (Con ck x b).

    Inductive wt_lexp : lexp -> Prop :=
    | wt_Econst: forall c,
        wt_lexp (Econst c)
    | wt_Evar: forall x ty,
        In (x, ty) vars ->
        wt_lexp (Evar x ty)
    | wt_Ewhen: forall e x b,
        In (x, bool_type) vars ->
        wt_lexp e ->
        wt_lexp (Ewhen e x b)
    | wt_Eunop: forall op e ty,
        type_unop op (typeof e) = Some ty ->
        wt_lexp e ->
        wt_lexp (Eunop op e ty)
    | wt_Ebinop: forall op e1 e2 ty,
        type_binop op (typeof e1) (typeof e2) = Some ty ->
        wt_lexp e1 ->
        wt_lexp e2 ->
        wt_lexp (Ebinop op e1 e2 ty).

    Fixpoint typeofc (ce: cexp): type :=
      match ce with
      | Emerge x t f => typeofc t
      | Eite e t f   => typeofc t
      | Eexp e       => typeof e
      end.

    Inductive wt_cexp : cexp -> Prop :=
    | wt_Emerge: forall x t f,
        In (x, bool_type) vars ->
        typeofc t = typeofc f ->
        wt_cexp t ->
        wt_cexp f ->
        wt_cexp (Emerge x t f)
    | wt_Eite: forall e t f,
        wt_lexp e ->
        typeof e = bool_type ->
        typeofc t = typeofc f ->
        wt_cexp (Eite e t f)
    | wt_Eexp: forall e,
        wt_lexp e ->
        wt_cexp (Eexp e).

    Inductive wt_equation : equation -> Prop :=
    | wt_EqDef: forall x ck e,
        In (x, typeofc e) vars ->
        wt_clock ck ->
        wt_cexp e ->
        wt_equation (EqDef x ck e)
    | wt_EqApp: forall n x ck f es,
        find_node f G = Some n ->
        In (x, snd n.(n_out)) vars ->
        Forall2 (fun e xt => typeof e = snd xt) es n.(n_in) ->
        wt_clock ck ->
        Forall wt_lexp es ->
        wt_equation (EqApp x ck f es)
    | wt_EqFby: forall x ck c0 e,
        In (x, type_const c0) vars ->
        typeof e = type_const c0 ->
        wt_clock ck ->
        wt_lexp e ->
        wt_equation (EqFby x ck c0 e).

  End WellTyped.

  Definition wt_node (G: global) (n: node) : Prop
    := Forall (wt_equation G (n.(n_in) ++ n.(n_vars) ++ [n.(n_out)])) n.(n_eqs).

  (* TODO: replace Welldef_global; except for the Is_well_sch component.
           Notably, typing arguments replace the ~Is_node_in and
           Is_node_in/find_node components. The no duplicate names
           component is replicated exactly. *)
  Inductive wt_global : global -> Prop :=
  | wtg_nil:
      wt_global []
  | wtg_cons: forall n ns,
      wt_global ns ->
      wt_node ns n ->
      Forall (fun n'=> n.(n_name) <> n'.(n_name)) ns ->
      wt_global (n::ns).

End TYPING.

Module TypingFun
       (Import Ids : IDS)
       (Import Op  : OPERATORS)
       (Import Syn : SYNTAX Ids Op) <: TYPING Ids Op Syn.
  Include TYPING Ids Op Syn.
End TypingFun.

