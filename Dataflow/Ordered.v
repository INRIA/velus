Require Import PArith.
Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Require Import Rustre.Common.
Require Import Rustre.Dataflow.Syntax.

(** * Ordering of nodes *)

(** 

The compilation of a whole program is only correct if that program satisfies
the [Ordered_nodes] predicate, which states that a node may only call nodes
that were defined earlier.

Remark: [Ordered_nodes] is implied by [Welldef_global].

 *)

Module Type ORDERED
       (Op : OPERATORS)
       (Import Syn : SYNTAX Op).

  Inductive Is_node_in_eq : ident -> equation -> Prop :=
  | INI: forall x ck f e ty, Is_node_in_eq f (EqApp x ck f e ty).

  (* definition is needed in signature *)
  Definition Is_node_in (f: ident) (eqs: list equation) : Prop :=
    List.Exists (Is_node_in_eq f) eqs.

  Inductive Ordered_nodes : global -> Prop :=
  | ONnil: Ordered_nodes nil
  | ONcons:
      forall nd nds,
        Ordered_nodes nds
        -> (forall f, Is_node_in f nd.(n_eqs) ->
                f <> nd.(n_name)
                /\ List.Exists (fun n=> f = n.(n_name)) nds)
        -> List.Forall (fun nd'=> nd.(n_name) <> nd'.(n_name)) nds
        -> Ordered_nodes (nd::nds).

  (** ** Properties of [Is_node_in] *)

  Section Is_node_Properties.

    Axiom not_Is_node_in_cons:
      forall n eq eqs,
        ~ Is_node_in n (eq::eqs) <-> ~Is_node_in_eq n eq /\ ~Is_node_in n eqs.

    Axiom Is_node_in_Forall:
      forall n eqs,
        ~Is_node_in n eqs <-> List.Forall (fun eq=>~Is_node_in_eq n eq) eqs.

    Axiom find_node_Exists:
      forall f G, find_node f G <> None <-> List.Exists (fun n=> f = n.(n_name)) G.

    Axiom find_node_tl:
      forall f node G,
        node.(n_name) <> f
        -> find_node f (node::G) = find_node f G.

    Axiom find_node_split:
      forall f G node,
        find_node f G = Some node
        -> exists bG aG,
          G = bG ++ node :: aG.

  End Is_node_Properties.

  (** ** Properties of [Ordered_nodes] *)

  Section Ordered_nodes_Properties.

    Axiom Ordered_nodes_append:
      forall G G',
        Ordered_nodes (G ++ G')
        -> Ordered_nodes G'.

    Axiom find_node_later_not_Is_node_in:
      forall f nd G nd',
        Ordered_nodes (nd::G)
        -> find_node f G = Some nd'
        -> ~Is_node_in nd.(n_name) nd'.(n_eqs).

    Axiom find_node_not_Is_node_in:
      forall f nd G,
        Ordered_nodes G
        -> find_node f G = Some nd
        -> ~Is_node_in nd.(n_name) nd.(n_eqs).

  End Ordered_nodes_Properties.

End ORDERED.

Module OrderedFun'
       (Op : OPERATORS)
       (Import Syn : SYNTAX Op).

  Inductive Is_node_in_eq : ident -> equation -> Prop :=
  | INI: forall x ck f e ty, Is_node_in_eq f (EqApp x ck f e ty).

  Definition Is_node_in (f: ident) (eqs: list equation) : Prop :=
    List.Exists (Is_node_in_eq f) eqs.

  Inductive Ordered_nodes : global -> Prop :=
  | ONnil: Ordered_nodes nil
  | ONcons:
      forall nd nds,
        Ordered_nodes nds
        -> (forall f, Is_node_in f nd.(n_eqs) ->
                f <> nd.(n_name)
                /\ List.Exists (fun n=> f = n.(n_name)) nds)
        -> List.Forall (fun nd'=> nd.(n_name) <> nd'.(n_name)) nds
        -> Ordered_nodes (nd::nds).


  (** ** Properties of [Is_node_in] *)

  Section Is_node_Properties.

    Lemma not_Is_node_in_cons:
      forall n eq eqs,
        ~ Is_node_in n (eq::eqs) <-> ~Is_node_in_eq n eq /\ ~Is_node_in n eqs.
    Proof.
      intros n eq eqs.
      split; intro HH.
      - split; intro; apply HH; unfold Is_node_in; intuition.
      - destruct HH; inversion_clear 1; intuition.
    Qed.

    Lemma Is_node_in_Forall:
      forall n eqs,
        ~Is_node_in n eqs <-> List.Forall (fun eq=>~Is_node_in_eq n eq) eqs.
    Proof.
      induction eqs as [|eq eqs IH];
      [split; [now constructor|now inversion 2]|].
      split; intro HH.
      - apply not_Is_node_in_cons in HH.
        destruct HH as [Heq Heqs].
        constructor; [exact Heq|apply IH with (1:=Heqs)].
      - apply not_Is_node_in_cons.
        inversion_clear HH as [|? ? Heq Heqs].
        apply IH in Heqs.
        intuition.
    Qed.

    Lemma find_node_Exists:
      forall f G, find_node f G <> None <-> List.Exists (fun n=> f = n.(n_name)) G.
    Proof.
      induction G as [|node G IH].
      - split; intro Hfn.
        exfalso; apply Hfn; reflexivity.
        apply List.Exists_nil in Hfn; contradiction.
      - destruct (ident_eq_dec node.(n_name) f) as [He|Hne]; simpl.
        + assert (He' := He); apply BinPos.Pos.eqb_eq in He'.
          unfold ident_eqb; rewrite He'.
          split; intro HH; [clear HH|discriminate 1].
          constructor.
          symmetry; exact He.
        + assert (Hne' := Hne); apply BinPos.Pos.eqb_neq in Hne'.
          unfold ident_eqb; rewrite Hne'.
          split; intro HH; [ apply IH in HH; constructor 2; exact HH |].
          apply List.Exists_cons in HH.
          destruct HH as [HH|HH]; [symmetry in HH; contradiction|].
          apply IH; exact HH.
    Qed.

    Lemma find_node_tl:
      forall f node G,
        node.(n_name) <> f
        -> find_node f (node::G) = find_node f G.
    Proof.
      intros f node G Hnf.
      unfold find_node.
      unfold List.find at 1.
      apply Pos.eqb_neq in Hnf.
      unfold ident_eqb.
      rewrite Hnf.
      reflexivity.
    Qed.

    Lemma find_node_split:
      forall f G node,
        find_node f G = Some node
        -> exists bG aG,
          G = bG ++ node :: aG.
    Proof.
      induction G as [|nd G IH]; [unfold find_node, List.find; discriminate|].
      intro nd'.
      intro Hfind.
      unfold find_node in Hfind; simpl in Hfind.
      destruct (ident_eqb (n_name nd) f) eqn:Heq.
      - injection Hfind; intro He; rewrite <-He in *; clear Hfind He.
        exists []; exists G; reflexivity.
      - apply IH in Hfind.
        destruct Hfind as [bG [aG Hfind]].
        exists (nd::bG); exists aG; rewrite Hfind; reflexivity.
    Qed.


    (* Lemma find_node_name: *)
    (*   forall f G fnode, *)
    (*     find_node f G = Some fnode -> fnode.(n_name) = f. *)
    (* Proof. *)
    (*   induction G as [|node G IH]; [now inversion 1|]. *)
    (*   destruct node as [name input output eqs]. *)
    (*   destruct (ident_eqb name f) eqn:Hfn; *)
    (*     assert (Hfn':=Hfn); *)
    (*     [apply Pos.eqb_eq in Hfn'; rewrite Hfn' in *|apply Pos.eqb_neq in Hfn']; *)
    (*     simpl; rewrite Hfn. *)
    (*   - injection 1; intro Heq; rewrite <-Heq; reflexivity. *)
    (*   - intros fnode Hfnode. *)
    (*     apply IH with (1:=Hfnode). *)
    (* Qed. *)

  End Is_node_Properties.

  (** ** Properties of [Ordered_nodes] *)

  Section Ordered_nodes_Properties.

    Lemma Ordered_nodes_append:
      forall G G',
        Ordered_nodes (G ++ G')
        -> Ordered_nodes G'.
    Proof.
      induction G as [|nd G IH]; [intuition|].
      intros G' HnGG.
      apply IH; inversion_clear HnGG; assumption.
    Qed.


    (* Lemma Ordered_nodes_cons_find_node_None: *)
    (*   forall node G, *)
    (*     Ordered_nodes (node::G) *)
    (*     -> find_node node.(n_name) G = None. *)
    (* Proof. *)
    (*   intros node G Hord. *)
    (*   inversion_clear Hord as [|? ? Hord' H0 Hfa]; clear H0. *)
    (*   induction G as [|eq G IH]; [trivial|]. *)
    (*   simpl. *)
    (*   destruct (ident_eqb eq.(n_name) node.(n_name)) eqn:Heq; *)
    (*     apply Forall_cons2 in Hfa; *)
    (*     destruct Hfa as [Hneq H0]. *)
    (*   - apply Peqb_true_eq in Heq. *)
    (*     rewrite Heq in Hneq. *)
    (*     exfalso; apply Hneq; reflexivity. *)
    (*   - apply IH; inversion_clear Hord'; assumption. *)
    (* Qed. *)

    (* Lemma find_node_later_names_not_eq: *)
    (*   forall f nd G nd', *)
    (*     Ordered_nodes (nd::G) *)
    (*     -> find_node f (G) = Some nd' *)
    (*     -> f <> nd.(n_name). *)
    (* Proof. *)
    (*   intros f nd G nd' Hord Hfind. *)
    (*   pose proof (Ordered_nodes_cons_find_node_None _ _ Hord) as Hnone. *)
    (*   intro Heq. *)
    (*   rewrite Heq, Hnone in Hfind. *)
    (*   discriminate. *)
    (* Qed. *)

    Lemma find_node_later_not_Is_node_in:
      forall f nd G nd',
        Ordered_nodes (nd::G)
        -> find_node f G = Some nd'
        -> ~Is_node_in nd.(n_name) nd'.(n_eqs).
    Proof.
      intros f nd G nd' Hord Hfind Hini.
      apply find_node_split in Hfind.
      destruct Hfind as [bG [aG HG]].
      rewrite HG in Hord.
      inversion_clear Hord as [|? ? Hord' H0 Hnin]; clear H0.
      apply Ordered_nodes_append in Hord'.
      inversion_clear Hord' as [| ? ? Hord Heqs Hnin'].
      apply Heqs in Hini.
      destruct Hini as [H0 HH]; clear H0.
      rewrite Forall_app in Hnin.
      destruct Hnin as [H0 Hnin]; clear H0.
      inversion_clear Hnin as [|? ? H0 HH']; clear H0.
      apply List.Exists_exists in HH.
      destruct HH as [node [HaG Heq]].
      rewrite List.Forall_forall in HH'.
      apply HH' in HaG.
      contradiction.
    Qed.

    Lemma find_node_not_Is_node_in:
      forall f nd G,
        Ordered_nodes G
        -> find_node f G = Some nd
        -> ~Is_node_in nd.(n_name) nd.(n_eqs).
    Proof.
      intros f nd G Hord Hfind.
      apply find_node_split in Hfind.
      destruct Hfind as [bG [aG HG]].
      rewrite HG in Hord.
      apply Ordered_nodes_append in Hord.
      inversion_clear Hord as [|? ? Hord' Heqs Hnin].
      intro Hini.
      apply Heqs in Hini.
      destruct Hini as [HH H0]; clear H0.
      apply HH; reflexivity.
    Qed.

  End Ordered_nodes_Properties.

End OrderedFun'.
Module OrderedFun <: ORDERED := OrderedFun'.
