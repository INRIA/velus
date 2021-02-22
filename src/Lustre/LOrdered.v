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
  | INEarrow: forall f le1 le2 la,
      Exists (Is_node_in_exp f) le1 \/ Exists (Is_node_in_exp f) le2 ->
      Is_node_in_exp f (Earrow le1 le2 la)
  (* | INEpre: forall f le1 la, *)
  (*     Exists (Is_node_in_exp f) le1 -> *)
  (*     Is_node_in_exp f (Epre le1 la) *)
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
      Is_node_in_exp f (Eapp g le None a)
  | INEapp2: forall f le r a, Is_node_in_exp f (Eapp f le r a)
  | INEapp3: forall f g le e a,
      Exists (Is_node_in_exp f) (e :: le) ->
      Is_node_in_exp f (Eapp g le (Some e) a).

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

    Lemma Is_node_in_Exists: forall n eqs,
        Is_node_in n eqs <-> List.Exists (Is_node_in_eq n) eqs.
    Proof.
      intros.
      induction eqs as [|eq eqs IH].
      - split; intro Hisin; inv Hisin.
      - split; intro Hisin.
        + inv Hisin.
          * constructor; auto.
          * apply Exists_cons_tl; auto.
        + inv Hisin.
          * constructor; auto.
          * apply Exists_cons_tl; auto.
    Qed.

    Lemma Is_node_in_Forall:
      forall n eqs,
        ~Is_node_in n eqs <-> List.Forall (fun eq=>~Is_node_in_eq n eq) eqs.
    Proof.
      intros n eqs.
      rewrite Is_node_in_Exists. symmetry. apply Forall_Exists_neg.
    Qed.

    Lemma Is_node_in_app: forall n eqs1 eqs2,
        Is_node_in n (eqs1++eqs2) <-> (Is_node_in n eqs1 \/ Is_node_in n eqs2).
    Proof.
      intros n eqs1 eqs2.
      unfold Is_node_in.
      apply Exists_app'.
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

  (** Actually, any wt or wc program is also ordered :)
      We can use the wl predicates + hypothesis that there is no duplication in the node names *)

  Lemma wl_exp_Is_node_in_exp : forall G e f,
      wl_exp G e ->
      Is_node_in_exp f e ->
      In f (map n_name G).
  Proof.
    intros * Hwl Hisin.
    Local Ltac Forall_Exists :=
      match goal with
      | Hex : Exists _ ?es, Hwl : Forall (wl_exp ?G) ?Es, H: Forall (fun _ => _) ?es |- _ =>
        eapply Forall_Forall in H; [|eapply Hwl]; clear Hwl;
        eapply Forall_Exists, Exists_exists in H as [? [_ [[? ?] ?]]]; eauto
      end.
    induction e using exp_ind2; inv Hwl; inv Hisin.
    - (* unop *) auto.
    - (* binop *) destruct H1; auto.
    - (* fby *) destruct H3; Forall_Exists.
    - (* arrow *) destruct H3; Forall_Exists.
    - (* when *) Forall_Exists.
    - (* merge *) destruct H3; Forall_Exists.
    - (* ite *) destruct H3 as [?|[?|?]]; auto; Forall_Exists.
    - (* app *) Forall_Exists.
    - assert (find_node f0 G <> None) as Hfind.
      { intro contra. congruence. }
      apply find_node_Exists, Exists_exists in Hfind as [? [Hin Hname]].
      rewrite in_map_iff; eauto.
    - (* app (reset) *)
      assert (find_node f0 G <> None) as Hfind.
      { intro contra. congruence. }
      apply find_node_Exists, Exists_exists in Hfind as [? [Hin Hname]].
      rewrite in_map_iff; eauto.
    - inv H3; auto. Forall_Exists.
  Qed.

  Lemma wl_equation_Is_node_in_eq : forall G eq f,
      wl_equation G eq ->
      Is_node_in_eq f eq ->
      In f (map n_name G).
  Proof.
    intros ? [xs es] * Hwl Hisin.
    destruct Hwl as [Hwl _].
    unfold Is_node_in_eq in Hisin.
    eapply Forall_Exists in Hisin; eauto.
    eapply Exists_exists in Hisin as [? [_ [? ?]]].
    eapply wl_exp_Is_node_in_exp; eauto.
  Qed.

  Lemma wl_node_Is_node_in : forall G n f,
      wl_node G n ->
      Is_node_in f (n_eqs n) ->
      In f (map n_name G).
  Proof.
    intros * Hwl Hisin.
    unfold wl_node in Hwl.
    unfold Is_node_in in Hisin.
    eapply Forall_Exists in Hisin; eauto.
    eapply Exists_exists in Hisin as [? [_ [? ?]]].
    eapply wl_equation_Is_node_in_eq; eauto.
  Qed.

  Lemma wl_global_Ordered_nodes : forall G,
      NoDup (List.map n_name G) ->
      wl_global G ->
      Ordered_nodes G.
  Proof.
    induction G; intros Hnd Hwl; inv Hnd; inv Hwl;
      constructor; auto.
    - intros f Hisin.
      eapply wl_node_Is_node_in in Hisin; eauto.
      split.
      + intro contra; subst. contradiction.
      + apply in_map_iff in Hisin as [? [? ?]].
        rewrite Exists_exists; eauto.
    - apply Forall_forall; intros ? Hin contra.
      rewrite in_map_iff in H1.
      apply H1; eauto.
  Qed.

End LORDERED.

Module LOrderedFun
       (Ids  : IDS)
       (Op   : OPERATORS)
       (Syn  : LSYNTAX Ids Op)
       <: LORDERED Ids Op Syn.
  Include LORDERED Ids Op Syn.
End LOrderedFun.
