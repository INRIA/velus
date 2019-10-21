(* *********************************************************************)
(*                                                                     *)
(*                 The Vélus verified Lustre compiler                  *)
(*                                                                     *)
(*             (c) 2019 Inria Paris (see the AUTHORS file)             *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

From Coq Require Import PArith.
From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Velus Require Import Common.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import NLustre.NLSyntax.

(** * Ordering of nodes *)

(**

The compilation of a whole program is only correct if that program satisfies
the [Ordered_nodes] predicate, which states that a node may only call nodes
that were defined earlier.

Remark: [Ordered_nodes] is implied by [Welldef_global].

 *)

Module Type NLORDERED
       (Ids            : IDS)
       (Op             : OPERATORS)
       (Import CESyn   : CESYNTAX Op)
       (Import Syn     : NLSYNTAX Ids Op CESyn).

  Inductive Is_node_in_eq : ident -> equation -> Prop :=
  | INI: forall x ck f e r, Is_node_in_eq f (EqApp x ck f e r).

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
        -> List.Forall (fun nd'=> nd.(n_name) <> nd'.(n_name))%type nds
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

    Lemma Not_Is_node_in_self:
      forall n G,
        Ordered_nodes (n :: G) ->
        ~Is_node_in n.(n_name) n.(n_eqs).
    Proof.
      intros n G. inversion_clear 1 as [|??? HH].
      intro Ini. apply HH in Ini. intuition.
    Qed.

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

    Lemma find_node_not_Is_node_in_eq:
      forall G f g n,
        Ordered_nodes G ->
        Forall (fun n' => ~(g = n'.(n_name))) G ->
        find_node f G = Some n ->
        Forall (fun eq => ~ Is_node_in_eq g eq) n.(n_eqs).
    Proof.
      induction G as [|n' G IH]. now inversion 2.
      intros f g n OG NG Ff.
      inv OG. apply Forall_cons2 in NG as (nG & NG).
      simpl in Ff.
      destruct (ident_eqb n'.(n_name) f); [|now eapply IH; eauto].
      inv Ff. apply Forall_forall.
      intros eq Ie Inie. destruct eq; [inv Inie| |inv Inie].
      assert (Is_node_in g n.(n_eqs)) as Ini by (apply Exists_exists; eauto).
      take (forall f, Is_node_in f n.(n_eqs) -> _) and apply it in Ini as (? & NNG).
      apply Forall_Exists with (1:=NG) in NNG.
      now apply Exists_exists in NNG as (? & ? & ? & ?).
    Qed.

  End Ordered_nodes_Properties.

End NLORDERED.

Module NLOrderedFun
       (Ids    : IDS)
       (Op     : OPERATORS)
       (CESyn  : CESYNTAX Op)
       (Syn    : NLSYNTAX Ids Op CESyn)
       <: NLORDERED Ids Op CESyn Syn.
  Include NLORDERED Ids Op CESyn Syn.
End NLOrderedFun.
