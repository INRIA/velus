Require Import Rustre.Common.
Require Import Rustre.Operators.
Require Import PArith.
Require Import Coq.Sorting.Permutation.

Require Import List.
Import List.ListNotations.
Open Scope list_scope.

(** * The CoreDF dataflow language *)

Module Type SYNTAX
       (Import Ids : IDS)
       (Import Op  : OPERATORS).
  (** ** Clocks *)

  Inductive clock : Type :=
  | Cbase : clock                            (* base clock *)
  | Con   : clock -> ident -> bool -> clock. (* subclock *)

  (** ** Expressions *)

  Inductive lexp : Type :=
  | Econst : const -> lexp
  | Evar   : ident -> type -> lexp
  | Ewhen  : lexp -> ident -> bool -> lexp
  | Eunop  : unop -> lexp -> type -> lexp
  | Ebinop : binop -> lexp -> lexp -> type -> lexp.

  Definition lexps := list lexp.

  Implicit Type le: lexp.
  Implicit Type les: lexps.

  (** ** Control expressions *)

  Inductive cexp : Type :=
  | Emerge : ident -> cexp -> cexp -> cexp
  | Eite   : lexp -> cexp -> cexp -> cexp
  | Eexp   : lexp -> cexp.

  Implicit Type ce: cexp.

  (** ** Equations *)

  (* TODO: Why aren't the two others typed? *)
  Inductive equation : Type :=
  | EqDef : ident -> clock -> cexp -> equation
  | EqApp : idents -> clock -> ident -> lexps -> equation
  | EqFby : ident -> clock -> const -> lexp -> equation.

  Implicit Type eqn: equation.

  (** ** Node *)

  Fixpoint typeof (le: lexp): type :=
    match le with
    | Econst c => type_const c
    | Evar _ ty
    | Eunop _ _ ty
    | Ebinop _ _ _ ty => ty
    | Ewhen e _ _ => typeof e
    end.

  Definition var_defined (eq: equation) : idents :=
    match eq with
    | EqDef x _ _ => [x]
    | EqApp x _ _ _ => x
    | EqFby x _ _ _ => [x]
    end.

  Definition vars_defined (eqs: list equation) : idents :=
    concatMap var_defined eqs.

  Definition is_fby (eq: equation) : bool :=
    match eq with
    | EqFby _ _ _ _ => true
    | _ => false
    end.

  Definition is_app (eq: equation) : bool :=
    match eq with
    | EqApp _ _ _ _ => true
    | _ => false
    end.

  Definition is_def (eq: equation) : bool :=
    match eq with
    | EqDef _ _ _ => true
    | _ => false
    end.

  Record node : Type :=
    mk_node {
        n_name : ident;
        n_in   : list (ident * type);
        n_out  : list (ident * type);
        n_vars : list (ident * type);
        n_eqs  : list equation;

        n_ingt0 : 0 < length n_in;
        n_outgt0 : 0 < length n_out;
        n_defd  : Permutation (vars_defined n_eqs)
                              (map fst (n_vars ++ n_out));
        n_vout  : forall out, In out (map fst n_out) ->
                         ~ In out (vars_defined (filter is_fby n_eqs));
        n_nodup : NoDupMembers (n_in ++ n_vars ++ n_out);
        n_good  : Forall NotReserved (n_in ++ n_vars ++ n_out)
      }.

  (** ** Program *)

  Definition global := list node.

  Implicit Type G: global.

  (* definition is needed in signature *)
  Definition find_node (f : ident) : global -> option node :=
    List.find (fun n=> ident_eqb n.(n_name) f).

  (** Structural properties *)

  Lemma is_filtered_eqs:
    forall eqs,
      Permutation
        (filter is_def eqs ++ filter is_app eqs ++ filter is_fby eqs)
        eqs.
  Proof.
    induction eqs as [|eq eqs]; auto.
    destruct eq; simpl.
    - now apply Permutation_cons.
    - rewrite <-Permutation_cons_app.
      apply Permutation_cons; reflexivity.
      now symmetry.
    - symmetry.
      rewrite <-Permutation_app_assoc.
      apply Permutation_cons_app.
      rewrite Permutation_app_assoc.
      now symmetry.
  Qed.

  Lemma NoDup_var_defined_n_eqs:
    forall n,
      NoDup (vars_defined n.(n_eqs)).
  Proof.
    intro n.
    rewrite n.(n_defd).
    apply fst_NoDupMembers.
    apply (NoDupMembers_app_r _ _ n.(n_nodup)).
  Qed.

End SYNTAX.

Module SyntaxFun
       (Import Ids : IDS)
       (Import Op  : OPERATORS) <: SYNTAX Ids Op.
  Include SYNTAX Ids Op.
End SyntaxFun.
