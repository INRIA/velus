From Coq Require Import PArith.
From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Velus Require Import Common.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Lustre.LSyntax.

(** * Ordering of Lustre nodes *)

(**

The compilation of a whole program is only correct if that program satisfies
the [Ordered_nodes] predicate, which states that a node may only call nodes
that were defined earlier.

 *)

Module Type LORDERED
       (Ids         : IDS)
       (Op          : OPERATORS)
       (Import Syn  : LSYNTAX Ids Op).

  Inductive Is_node_in_exp : ident -> exp -> Prop :=
  | INEunop: forall f op e a,
      Is_node_in_exp f e -> Is_node_in_exp f (Eunop op e a)
  | INEbinop: forall f op e1 e2 a,
      Is_node_in_exp f e1 \/ Is_node_in_exp f e2 ->
      Is_node_in_exp f (Ebinop op e1 e2 a)
  | INEfby: forall f le1 le2 la,
      Exists (Is_node_in_exp f) le1 \/ Exists (Is_node_in_exp f) le2 ->
      Is_node_in_exp f (Efby le1 le2 la)
  | INEwhen: forall f le x b la,
      Exists (Is_node_in_exp f) le ->
      Is_node_in_exp f (Ewhen le x b la)
  | INEmerge: forall f x le1 le2 la,
      Exists (Is_node_in_exp f) le1 \/ Exists (Is_node_in_exp f) le2 ->
      Is_node_in_exp f (Emerge x le1 le2 la)
  | INEite: forall f e le1 le2 la,
      Is_node_in_exp f e
      \/ Exists (Is_node_in_exp f) le1
      \/ Exists (Is_node_in_exp f) le2 ->
      Is_node_in_exp f (Eite e le1 le2 la)
  | INEapp1: forall f g le a,
      Exists (Is_node_in_exp f) le ->
      Is_node_in_exp f (Eapp g le a)
  | INEapp2: forall f le a, Is_node_in_exp f (Eapp f le a).

  Definition Is_node_in_eq (f: ident) (eq: equation) : Prop :=
    List.Exists (Is_node_in_exp f) (snd eq).

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

End LORDERED.

Module LOrderedFun
       (Ids  : IDS)
       (Op   : OPERATORS)
       (Syn  : LSYNTAX Ids Op)
       <: LORDERED Ids Op Syn.
  Include LORDERED Ids Op Syn.
End LOrderedFun.

