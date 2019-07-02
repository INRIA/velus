From Velus Require Import Common.
From Velus Require Import Operators.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import Clocks.
From Coq Require Import PArith.
From Coq Require Import Omega.
From Coq Require Import Sorting.Permutation.

From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

(** * The NLustre dataflow language *)

Module Type NLSYNTAX
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import CESyn : CESYNTAX Op).

  (** ** Equations *)

  Inductive equation : Type :=
  | EqDef : ident -> clock -> cexp -> equation
  | EqApp : idents -> clock -> ident -> exps -> option ident -> equation
  | EqFby : ident -> clock -> const -> exp -> equation.

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
    flat_map var_defined eqs.

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
                  (* /\ Forall valid (vars_defined (filter is_app n_eqs)) *)
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

  Lemma find_node_In:
    forall G f n,
      find_node f G = Some n ->
      n.(n_name) = f /\ In n G.
  Proof.
    induction G as [|n G IH]. now inversion 1.
    simpl. intros f n' Fn'.
    destruct (ident_eqb n.(n_name) f) eqn:Efn.
    - inv Fn'. apply ident_eqb_eq in Efn; auto.
    - apply IH in Fn'; tauto.
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

  Lemma is_filtered_vars_defined:
    forall eqs,
      Permutation
        (vars_defined (filter is_def eqs) ++ vars_defined (filter is_app eqs) ++ vars_defined (filter is_fby eqs))
        (vars_defined eqs).
  Proof.
    simpl.
    induction eqs as [|[] eqs]; simpl; auto.
    - rewrite Permutation_app_comm, 2 Permutation_app_assoc.
      apply Permutation_app_head.
      rewrite <-Permutation_app_assoc, Permutation_app_comm; auto.
    - symmetry.
      rewrite <-Permutation_app_assoc.
      apply Permutation_cons_app.
      symmetry.
      rewrite Permutation_app_assoc; auto.
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

  Lemma n_eqsgt0:
    forall n, 0 < length n.(n_eqs).
  Proof.
    intro.
    pose proof (n_defd n) as Defd.
    pose proof (n_outgt0 n) as Out.
    unfold vars_defined in Defd.
    apply Permutation_length in Defd.
    rewrite flat_map_length, map_length, app_length in Defd.
    destruct (n_eqs n); simpl in *; omega.
  Qed.

  (* XXX: computationally, the following [gather_*] are useless: they
     are only used to simplify the proofs. See [gather_eqs_fst_spec]
     and [gather_eqs_snd_spec]. *)
  Definition gather_mem_eq (eq: equation): idents :=
    match eq with
    | EqDef _ _ _
    | EqApp _ _ _ _ _ => []
    | EqFby x _ _ _ => [x]
    end.

  Definition gather_inst_eq (eq: equation): list (ident * ident) :=
    match eq with
    | EqDef _ _ _
    | EqFby _ _ _ _ => []
    | EqApp i _ f _ _ =>
      match i with
      | [] => []
      | i :: _ => [(i,f)]
      end
    end.

  Definition gather_app_vars_eq (eq: equation): idents :=
    match eq with
    | EqDef _ _ _
    | EqFby _ _ _ _ => []
    | EqApp xs _ _ _ _ => tl xs
    end.

  Definition gather_mems := flat_map gather_mem_eq.
  Definition gather_insts := flat_map gather_inst_eq.
  Definition gather_app_vars := flat_map gather_app_vars_eq.

  (** Basic syntactical properties *)

  Lemma In_gather_mems_cons:
    forall eq eqs x,
      In x (gather_mems (eq :: eqs))
      <-> (In x (gather_mem_eq eq) \/ In x (gather_mems eqs)).
  Proof.
    destruct eq; simpl; split; intuition.
  Qed.

  Lemma In_gather_insts_cons:
    forall eq eqs x,
      InMembers x (gather_insts (eq :: eqs))
      <-> (InMembers x (gather_inst_eq eq) \/ InMembers x (gather_insts eqs)).
  Proof.
    destruct eq; simpl; try now intuition.
    destruct i.
    - setoid_rewrite app_nil_l. intuition.
    - now setoid_rewrite InMembers_app.
  Qed.

  Lemma In_gather_mems_dec:
    forall x eqs,
      { In x (gather_mems eqs) } + { ~In x (gather_mems eqs) }.
  Proof.
    induction eqs as [|eq eqs IH].
    now right; inversion 1.
    destruct eq; simpl; auto.
    destruct (ident_eq_dec x i).
    now subst; auto.
    destruct IH. auto.
    right. inversion 1; auto.
  Qed.

  Lemma In_gather_insts_dec:
    forall i eqs,
      { InMembers i (gather_insts eqs) } + { ~InMembers i (gather_insts eqs) }.
  Proof.
    induction eqs as [|eq eqs IH].
    now right; inversion 1.
    destruct eq; simpl; auto.
    destruct i0 as [|i'].
    now destruct IH; auto.
    destruct (ident_eq_dec i' i).
    subst; simpl; auto.
    destruct IH.
    now left; rewrite InMembers_app; auto.
    right; rewrite NotInMembers_app.
    split; auto. inversion 1; auto.
  Qed.

End NLSYNTAX.

Module NLSyntaxFun
       (Ids     : IDS)
       (Op      : OPERATORS)
       (CESyn   : CESYNTAX Op)
       <: NLSYNTAX Ids Op CESyn.
  Include NLSYNTAX Ids Op CESyn.
End NLSyntaxFun.
