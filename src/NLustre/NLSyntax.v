From Velus Require Import Common.
From Velus Require Import CommonProgram.
From Velus Require Import Operators.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import Clocks.
From Coq Require Import PArith.
From Coq Require Import Sorting.Permutation.

From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

(** * The NLustre dataflow language *)

Module Type NLSYNTAX
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks   : CLOCKS        Ids Op OpAux)
       (Import CESyn : CESYNTAX      Ids Op OpAux Cks).

  (** ** Equations *)

  Inductive equation : Type :=
  | EqDef : ident -> clock -> cexp -> equation
  | EqApp : list ident -> clock -> ident -> list exp -> list (ident * clock) -> equation
  | EqFby : ident -> clock -> const -> exp -> list (ident * clock) -> equation.

  (** ** Node *)

  Definition var_defined (eq: equation) : list ident :=
    match eq with
    | EqDef x _ _ => [x]
    | EqApp x _ _ _ _ => x
    | EqFby x _ _ _ _ => [x]
    end.

  Definition vars_defined (eqs: list equation) : list ident :=
    flat_map var_defined eqs.

  Definition is_fby (eq: equation) : bool :=
    match eq with
    | EqFby _ _ _ _ _ => true
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
        n_name   : ident;                                (* name *)
        n_in     : list (ident * (type * clock));  (* inputs *)
        n_out    : list (ident * (type * clock));  (* outputs *)
        n_vars   : list (ident * (type * clock));  (* local variables *)
        n_eqs    : list equation;                        (* equations *)

        n_ingt0  : 0 < length n_in;
        n_outgt0 : 0 < length n_out;
        n_defd   : Permutation (vars_defined n_eqs)
                               (map fst (n_vars ++ n_out));
        n_vout   : forall out, In out (map fst n_out) ->
                          ~ In out (vars_defined (filter is_fby n_eqs));
        n_nodup  : NoDupMembers (n_in ++ n_vars ++ n_out);
        n_good   : Forall (AtomOrGensym (PSP.of_list gensym_prefs)) (map fst (n_in ++ n_vars ++ n_out)) /\ atom n_name
      }.

  Instance node_unit: ProgramUnit node :=
    { name := n_name; }.

  (** ** Program *)

  Record global := Global {
                       enums : list (ident * nat);
                       nodes : list node
                     }.

  Program Instance global_program: Program node global :=
    { units := nodes;
      update := fun g => Global g.(enums) }.

  Definition find_node (f: ident) (G: global) :=
    option_map fst (find_unit f G).

  (** Structural properties *)

  Lemma find_node_now:
    forall f n G enums,
      n.(n_name) = f ->
      find_node f (Global enums (n::G)) = Some n.
  Proof.
    intros * Heq; subst.
    unfold find_node, find_unit; simpl.
    destruct (ident_eq_dec _ _); simpl; congruence.
  Qed.

  Lemma find_node_other:
    forall f node G node' enums,
      node.(n_name) <> f ->
      (find_node f (Global enums (node::G)) = Some node'
       <-> find_node f (Global enums G)  = Some node').
  Proof.
    unfold find_node, option_map; intros ???? enums ?.
    erewrite find_unit_other with (p' := Global enums G);
      simpl; eauto; try reflexivity.
    unfold equiv_program; reflexivity.
  Qed.

  Lemma find_node_In:
    forall G f n,
      find_node f G = Some n ->
      n.(n_name) = f /\ In n G.(nodes).
  Proof.
    unfold find_node, option_map; intros * Find.
    apply option_map_inv in Find as ((?&?) & Find & E); inv E.
    apply find_unit_In in Find; auto.
  Qed.

  Lemma find_node_Exists:
    forall f enums G, find_node f (Global enums G) <> None <-> List.Exists (fun n=> f = n.(n_name)) G.
  Proof.
    unfold find_node; intros.
    rewrite option_map_None.
    rewrite find_unit_Exists; reflexivity.
  Qed.

  Lemma find_node_split:
    forall f G node,
      find_node f G = Some node ->
      exists bG aG,
        G.(nodes) = bG ++ node :: aG.
  Proof.
    unfold find_node; intros * Find.
    apply option_map_inv in Find as ((?&?) & Find & E); inv E.
    apply find_unit_spec in Find as (?& us & E &?).
    unfold units, global_program in *.
    rewrite E; eauto.
  Qed.

  Lemma Forall_not_find_node_None:
    forall G f enums,
      Forall (fun n => ~(f = n.(n_name))) G <-> find_node f (Global enums G) = None.
  Proof.
    unfold find_node; intros.
    rewrite option_map_None, find_unit_None; reflexivity.
  Qed.

  Lemma find_node_enums_cons:
    forall ns enums e f,
      find_node f (Global (e :: enums) ns) = find_node f (Global enums ns).
  Proof.
    unfold find_node; simpl.
    induction ns; simpl; auto.
    intros.
    remember (find_unit f _) as F eqn: E; symmetry in E.
    remember (find_unit f (Global enums0 _)) as F' eqn: E'; symmetry in E'.
    rewrite find_unit_cons in E; simpl; eauto.
    rewrite find_unit_cons in E'; simpl; eauto.
    destruct E as [(?&?)|(?&?)], E' as [(?&?)|(?&?)]; subst; simpl; auto; contradiction.
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
    destruct (n_eqs n); simpl in *; lia.
  Qed.

  (* XXX: computationally, the following [gather_*] are useless: they
     are only used to simplify the proofs. See [gather_eqs_fst_spec]
     and [gather_eqs_snd_spec]. *)
  Definition gather_mem_eq (eq: equation): list (ident * type) :=
    match eq with
    | EqDef _ _ _
    | EqApp _ _ _ _ _ => []
    | EqFby x _ _ e _ => [(x, typeof e)]
    end.

  Definition gather_inst_eq (eq: equation): list (ident * ident) :=
    match eq with
    | EqDef _ _ _
    | EqFby _ _ _ _ _ => []
    | EqApp i _ f _ _ =>
      match i with
      | [] => []
      | i :: _ => [(i,f)]
      end
    end.

  Definition gather_app_vars_eq (eq: equation): list ident :=
    match eq with
    | EqDef _ _ _
    | EqFby _ _ _ _ _ => []
    | EqApp xs _ _ _ _ => tl xs
    end.

  Definition gather_mems := flat_map gather_mem_eq.
  Definition gather_insts := flat_map gather_inst_eq.
  Definition gather_app_vars := flat_map gather_app_vars_eq.

  (** Basic syntactical properties *)

  (* Lemma In_gather_mems_cons: *)
  (*   forall eq eqs x, *)
  (*     In x (gather_mems (eq :: eqs)) *)
  (*     <-> (In x (gather_mem_eq eq) \/ In x (gather_mems eqs)). *)
  (* Proof. *)
  (*   destruct eq; simpl; split; intuition. *)
  (* Qed. *)

  (* Lemma In_gather_insts_cons: *)
  (*   forall eq eqs x, *)
  (*     InMembers x (gather_insts (eq :: eqs)) *)
  (*     <-> (InMembers x (gather_inst_eq eq) \/ InMembers x (gather_insts eqs)). *)
  (* Proof. *)
  (*   destruct eq; simpl; try now intuition. *)
  (*   destruct l. *)
  (*   - setoid_rewrite app_nil_l. intuition. *)
  (*   - now setoid_rewrite InMembers_app. *)
  (* Qed. *)

  (* Lemma In_gather_mems_dec: *)
  (*   forall x eqs, *)
  (*     { In x (gather_mems eqs) } + { ~In x (gather_mems eqs) }. *)
  (* Proof. *)
  (*   induction eqs as [|eq eqs IH]. *)
  (*   now right; inversion 1. *)
  (*   destruct eq; simpl; auto. *)
  (*   destruct (ident_eq_dec x i). *)
  (*   now subst; auto. *)
  (*   destruct IH. auto. *)
  (*   right. inversion 1; auto. *)
  (* Qed. *)

  (* Lemma In_gather_insts_dec: *)
  (*   forall i eqs, *)
  (*     { InMembers i (gather_insts eqs) } + { ~InMembers i (gather_insts eqs) }. *)
  (* Proof. *)
  (*   induction eqs as [|eq eqs IH]. *)
  (*   now right; inversion 1. *)
  (*   destruct eq; simpl; auto. *)
  (*   destruct l as [|i']. *)
  (*   now destruct IH; auto. *)
  (*   destruct (ident_eq_dec i' i). *)
  (*   subst; simpl; auto. *)
  (*   destruct IH. *)
  (*   now left; rewrite InMembers_app; auto. *)
  (*   right; rewrite NotInMembers_app. *)
  (*   split; auto. inversion 1; auto. *)
  (* Qed. *)

  Lemma node_in_not_nil:
    forall n,
      n.(n_in) <> [].
  Proof.
    intros n E; pose proof (n_ingt0 n) as H.
    rewrite E in H; simpl in H; lia.
  Qed.

  Lemma node_out_not_nil:
    forall n,
      n.(n_out) <> [].
  Proof.
    intros n E; pose proof (n_outgt0 n) as H.
    rewrite E in H; simpl in H; lia.
  Qed.

  Lemma InMembers_gather_mems_In_vars_defined:
    forall eqs x,
      InMembers x (gather_mems eqs) -> In x (vars_defined eqs).
  Proof.
    induction eqs as [|[]]; simpl; auto; intros * Hin.
    - apply in_app; auto.
    - intuition.
  Qed.

  Lemma n_nodup_gather_mems:
    forall n,
      NoDup (gather_mems (n_eqs n)).
  Proof.
    intro.
    pose proof (NoDup_var_defined_n_eqs n) as Hnodup.
    unfold gather_mems, vars_defined in *.
    induction (n_eqs n) as [|[]]; simpl in *; intros; auto.
    - constructor.
    - inv Hnodup; auto.
    - rewrite Permutation_app_comm in Hnodup; apply NoDup_app_weaken in Hnodup; auto.
    - inv Hnodup; constructor; auto.
      apply NotInMembers_NotIn; auto.
      intros Hin; apply InMembers_gather_mems_In_vars_defined in Hin; contradiction.
  Qed.

End NLSYNTAX.

Module NLSyntaxFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks   : CLOCKS        Ids Op OpAux)
       (CESyn : CESYNTAX      Ids Op OpAux Cks)
       <: NLSYNTAX Ids Op OpAux Cks CESyn.
  Include NLSYNTAX Ids Op OpAux Cks CESyn.
End NLSyntaxFun.
