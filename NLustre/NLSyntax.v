Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.NLustre.NLExprSyntax.
Require Import Velus.Clocks.
Require Import PArith.
Require Import Coq.Sorting.Permutation.

Require Import List.
Import List.ListNotations.
Open Scope list_scope.

(** * The NLustre dataflow language *)

Module Type NLSYNTAX
       (Import Ids     : IDS)
       (Import Op      : OPERATORS)
       (Import Clks    : CLOCKS          Ids)
       (Import ExprSyn : NLEXPRSYNTAX Op).

  (** ** Equations *)

  Inductive equation : Type :=
  | EqDef : ident -> clock -> cexp -> equation
  | EqApp : idents -> clock -> ident -> lexps -> option (ident * clock) -> equation
  | EqFby : ident -> clock -> const -> lexp -> equation.

  Implicit Type eqn: equation.

  (** ** Node *)

  (* XXX: [var_defined] is redundant with [defined_eq], except that it
  works on lists rather than finite sets. *)
  Definition var_defined (eq: equation) : idents :=
    match eq with
    | EqDef x _ _ => [x]
    | EqApp x _ _ _ _ => x
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
    | EqApp _ _ _ _ _ => true
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
        n_in   : list (ident * (type * clock));
        n_out  : list (ident * (type * clock));
        n_vars : list (ident * (type * clock));
        n_eqs  : list equation;

        n_ingt0 : 0 < length n_in;
        n_outgt0 : 0 < length n_out;
        n_defd  : Permutation (vars_defined n_eqs)
                              (map fst (n_vars ++ n_out));
        n_vout  : forall out, In out (map fst n_out) ->
                         ~ In out (vars_defined (filter is_fby n_eqs));
        n_nodup : NoDupMembers (n_in ++ n_vars ++ n_out);
        n_good  : Forall ValidId (n_in ++ n_vars ++ n_out)
                  /\ Forall valid (vars_defined (filter is_app n_eqs))
                  /\ valid n_name
      }.

  (** ** Program *)

  Definition global := list node.

  Implicit Type G: global.

  Definition find_node (f : ident) : global -> option node :=
    List.find (fun n=> ident_eqb n.(n_name) f).

  (** Structural properties *)

  Lemma find_node_name:
    forall G f n,
      find_node f G = Some n ->
      n.(n_name) = f.
  Proof.
    unfold find_node.
    induction G as [|m]; intros; try discriminate.
    simpl in H.
    destruct (ident_eqb (n_name m) f) eqn: E; auto.
    apply ident_eqb_eq; inv H; auto.
  Qed.

  Lemma find_node_other:
    forall f node G node',
      node.(n_name) <> f ->
      (find_node f (node::G) = Some node'
       <-> find_node f G = Some node').
  Proof.
    intros f node G node' Hnf.
    apply BinPos.Pos.eqb_neq in Hnf.
    simpl.
    unfold ident_eqb.
    rewrite Hnf.
    reflexivity.
  Qed.

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

  Lemma vars_defined_EqApp:
    forall xs ck f es r eqs,
      vars_defined (EqApp xs ck f es r :: eqs) = xs ++ vars_defined eqs.
  Proof.
    unfold vars_defined.
    intros. rewrite concatMap_cons.
    reflexivity.
  Qed.

  Lemma n_eqsgt0:
    forall n, 0 < length n.(n_eqs).
  Proof.
    intro.
    pose proof (n_defd n) as Defd.
    pose proof (n_outgt0 n) as Out.
    unfold vars_defined in Defd.
    apply Permutation_length in Defd.
    rewrite concatMap_length, map_length, app_length in Defd.
    destruct (n_eqs n); simpl in *; omega.
  Qed.

  (* XXX: computationally, the following [gather_*] are useless: they
     are only used to simplify the proofs. See [gather_eqs_fst_spec]
     and [gather_eqs_snd_spec]. *)
  Definition gather_mem (eqs: list equation): idents :=
    concatMap (fun eq => match eq with
                      | EqDef _ _ _
                      | EqApp _ _ _ _ _ => []
                      | EqFby x _ _ _ => [x]
                      end) eqs.

  Definition gather_insts (eqs: list equation): list (ident * ident) :=
    concatMap (fun eq => match eq with
                      | EqDef _ _ _
                      | EqFby _ _ _ _ => []
                      | EqApp i _ f _ _ =>
                        match i with
                        | [] => []
                        | i :: _ => [(i,f)]
                        end
                      end) eqs.

  Definition gather_app_vars (eqs: list equation): idents :=
    concatMap (fun eq => match eq with
                      | EqDef _ _ _
                      | EqFby _ _ _ _ => []
                      | EqApp xs _ _ _ _ => tl xs
                      end) eqs.
End NLSYNTAX.

Module NLSyntaxFun
       (Ids     : IDS)
       (Op      : OPERATORS)
       (Clks    : CLOCKS          Ids)
       (ExprSyn : NLEXPRSYNTAX Op)
       <: NLSYNTAX Ids Op Clks ExprSyn.
  Include NLSYNTAX Ids Op Clks ExprSyn.
End NLSyntaxFun.
