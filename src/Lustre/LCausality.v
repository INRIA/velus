From Coq Require Import String.
From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.
From Coq Require Import Permutation.
From Coq Require Import Setoid Morphisms.

From compcert Require Import common.Errors.

From Velus Require Import Common Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import AcyGraph.
From Velus Require Import Lustre.StaticEnv.
From Velus Require Import Lustre.LSyntax.

(** * Lustre causality *)

Module Type LCAUSALITY
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks : CLOCKS Ids Op OpAux)
       (Import Senv : STATICENV Ids Op OpAux Cks)
       (Import Syn : LSYNTAX Ids Op OpAux Cks Senv).

  (** ** Causality definition *)

  (** Variables that appear in the nth stream of an expression, to the left of fbys. *)
  Inductive Is_free_left (Γ : static_env) (cx : ident) : nat -> exp -> Prop :=
  | IFLvar : forall x a,
      HasCaus Γ x cx ->
      Is_free_left Γ cx 0 (Evar x a)
  | IFLlast : forall x a,
      HasLastCaus Γ x cx ->
      Is_free_left Γ cx 0 (Elast x a)
  | IFLunop : forall op e a,
      Is_free_left Γ cx 0 e ->
      Is_free_left Γ cx 0 (Eunop op e a)
  | IFLbinop : forall op e1 e2 a,
      Is_free_left Γ cx 0 e1
      \/ Is_free_left Γ cx 0 e2 ->
      Is_free_left Γ cx 0 (Ebinop op e1 e2 a)
  | IFLfby : forall e0s es a k,
      Is_free_left_list Γ cx k e0s ->
      Is_free_left Γ cx k (Efby e0s es a)
  | IFLarrow : forall e0s es a k,
      Is_free_left_list Γ cx k e0s
      \/ Is_free_left_list Γ cx k es ->
      Is_free_left Γ cx k (Earrow e0s es a)
  | IFLwhen : forall es x b a k,
      (k < length (fst a) /\ HasCaus Γ x cx)
      \/ Is_free_left_list Γ cx k es ->
      Is_free_left Γ cx k (Ewhen es x b a)
  | IFLmerge : forall x es ty a k,
      (k < length (fst a) /\ HasCaus Γ x cx)
      \/ Exists (fun es => Is_free_left_list Γ cx k (snd es)) es ->
      Is_free_left Γ cx k (Emerge (x, ty) es a)
  | IFLcase : forall e es d a k,
      (k < length (fst a) /\ Is_free_left Γ cx 0 e)
      \/ Exists (fun es => Is_free_left_list Γ cx k (snd es)) es
      \/ (exists d0, d = Some d0 /\ Is_free_left_list Γ cx k d0) ->
      Is_free_left Γ cx k (Ecase e es d a)
  | IFLapp : forall f es er a k,
      k < length a ->
      (exists k', Exists (Is_free_left Γ cx k') es)
      \/ (Exists (Is_free_left Γ cx 0) er) ->
      Is_free_left Γ cx k (Eapp f es er a)

  with Is_free_left_list (Γ : static_env) (cx : ident) : nat -> list exp -> Prop :=
  | IFLLnow : forall k e es,
      k < numstreams e ->
      Is_free_left Γ cx k e ->
      Is_free_left_list Γ cx k (e::es)
  | IFLLlater : forall k e es,
      k >= numstreams e ->
      Is_free_left_list Γ cx (k - numstreams e) es ->
      Is_free_left_list Γ cx k (e::es).

  Local Hint Constructors Is_free_left Is_free_left_list : lcaus.

  Definition idcaus {A B} (l : list (ident * (A * B * ident))) : list (ident * ident) :=
    map (fun '(x, (_, _, cx)) => (x, cx)) l.

  Fact idcaus_app {A B} : forall (l1 l2 : list (ident * (A * B * ident))),
      idcaus (l1 ++ l2) = idcaus l1 ++ idcaus l2.
  Proof. apply map_app. Qed.

  Fact map_fst_idcaus {A B} : forall (l1 : list (ident * (A * B * ident))),
      map fst (idcaus l1) = map fst l1.
  Proof.
    induction l1 as [|(?&(?&?)&?)]; intros; simpl; f_equal; auto.
  Qed.

  Global Hint Unfold idcaus : list.

  Lemma NoDupMembers_idcaus {A B} : forall (xs : list (ident * (A * B * ident))),
      NoDupMembers (idcaus xs) <-> NoDupMembers xs.
  Proof.
    intros *.
    now rewrite fst_NoDupMembers, map_fst_idcaus, <-fst_NoDupMembers.
  Qed.

  Fact idcaus_of_senv_inout : forall xs,
      idcaus_of_senv (senv_of_inout xs) = idcaus xs.
  Proof.
    intros *. unfold idcaus_of_senv, senv_of_inout, idcaus.
    erewrite map_map, map_ext, map_filter_nil, app_nil_r. reflexivity.
    - simpl_Forall. auto.
    - intros; destruct_conjs; auto.
  Qed.

  Inductive Is_defined_in_scope {A} (Pdef : static_env -> A -> Prop) Γ : scope A -> Prop :=
  | DefScope : forall locs blks,
      Pdef (Γ++senv_of_locs locs) blks ->
      Is_defined_in_scope Pdef Γ (Scope locs blks).

  Inductive Is_defined_in Γ (cx : ident) : block -> Prop :=
  | DefEq : forall x xs es,
      In x xs ->
      HasCaus Γ x cx ->
      Is_defined_in Γ cx (Beq (xs, es))
  | DefReset : forall blocks er,
      Exists (Is_defined_in Γ cx) blocks ->
      Is_defined_in Γ cx (Breset blocks er)
  | DefSwitch : forall ec branches,
      Exists (fun blks => Is_defined_in_scope (fun Γ => Exists (Is_defined_in Γ cx)) Γ (snd blks)) branches ->
      Is_defined_in Γ cx (Bswitch ec branches)
  | DefAuto : forall ini states ck,
      Exists (fun blks => Is_defined_in_scope (fun Γ blks => Exists (Is_defined_in Γ cx) (fst blks)) Γ (snd blks)) states ->
      Is_defined_in Γ cx (Bauto ck ini states)
  | DefLocal : forall scope,
      Is_defined_in_scope (fun Γ => Exists (Is_defined_in Γ cx)) Γ scope ->
      Is_defined_in Γ cx (Blocal scope).

  Inductive Is_last_in_scope {A} (Plast : A -> Prop) (cx : ident) : scope A -> Prop :=
  | LastScope1 : forall locs blks,
      Plast blks ->
      Is_last_in_scope Plast cx (Scope locs blks)
  | LastScope2 : forall locs blks x ty ck cx' e,
      In (x, (ty, ck, cx', Some (e, cx))) locs ->
      Is_last_in_scope Plast cx (Scope locs blks).

  Inductive Is_last_in (cx : ident) : block -> Prop :=
  | LastReset : forall blocks er,
      Exists (Is_last_in cx) blocks ->
      Is_last_in cx (Breset blocks er)
  | LastSwitch : forall ec branches,
      Exists (fun blks => Is_last_in_scope (Exists (Is_last_in cx)) cx (snd blks)) branches ->
      Is_last_in cx (Bswitch ec branches)
  | LastAuto : forall ini states ck,
      Exists (fun blks => Is_last_in_scope (fun blks => Exists (Is_last_in cx) (fst blks)) cx (snd blks)) states ->
      Is_last_in cx (Bauto ck ini states)
  | LastLocal : forall scope,
      Is_last_in_scope (Exists (Is_last_in cx)) cx scope ->
      Is_last_in cx (Blocal scope).

  Inductive depends_on_scope {A} (P_dep : _ -> _ -> _ -> _ -> Prop) Γ (cx cy : ident) : scope A -> Prop :=
  | DepOnScope1 : forall locs blks Γ',
      Γ' = Γ ++ senv_of_locs locs ->
      P_dep Γ' cx cy blks ->
      depends_on_scope P_dep Γ cx cy (Scope locs blks)
  | DepOnScope2 : forall locs blks Γ',
      Γ' = Γ ++ senv_of_locs locs ->
      Exists (fun '(_, (_, ck, _, o)) =>
                match o with
                | None => False
                | Some (e, cx') => cx' = cx /\ Is_free_left Γ' cy 0 e
                end) locs ->
      depends_on_scope P_dep Γ cx cy (Scope locs blks).

  Inductive depends_on Γ (cx cy : ident) : block -> Prop :=
  | DepOnEq : forall xs es k x,
      nth_error xs k = Some x ->
      HasCaus Γ x cx ->
      Is_free_left_list Γ cy k es ->
      depends_on Γ cx cy (Beq (xs, es))

  | DepOnReset1 : forall blocks er,
      Exists (depends_on Γ cx cy) blocks ->
      depends_on Γ cx cy (Breset blocks er)
  | DepOnReset2 : forall blocks er,
      Is_defined_in Γ cx (Breset blocks er) \/ Is_last_in cx (Breset blocks er) ->
      Is_free_left Γ cy 0 er ->
      depends_on Γ cx cy (Breset blocks er)

  | DepOnSwitch1 : forall ec branches,
      Exists (fun blks => depends_on_scope (fun Γ cx cy => Exists (depends_on Γ cx cy)) Γ cx cy (snd blks)) branches ->
      depends_on Γ cx cy (Bswitch ec branches)
  | DepOnSwitch2 : forall ec branches,
      Is_defined_in Γ cx (Bswitch ec branches) \/ Is_last_in cx (Bswitch ec branches) ->
      Is_free_left Γ cy 0 ec ->
      depends_on Γ cx cy (Bswitch ec branches)

  | DepOnAuto1 : forall ini states ck,
      Exists (fun blks => depends_on_scope (fun Γ cx cy blks => Exists (depends_on Γ cx cy) (fst blks)) Γ cx cy (snd blks)) states ->
      depends_on Γ cx cy (Bauto ck ini states)
  | DepOnAuto2 : forall ini oth states ck y,
      Is_defined_in Γ cx (Bauto ck (ini, oth) states) \/ Is_last_in cx (Bauto ck (ini, oth) states) ->
      Is_free_in_clock y ck ->
      HasCaus Γ y cy ->
      depends_on Γ cx cy (Bauto ck (ini, oth) states)
  | DepOnAuto3 : forall ini oth states ck,
      Is_defined_in Γ cx (Bauto ck (ini, oth) states) \/ Is_last_in cx (Bauto ck (ini, oth) states) ->
      Exists (fun '(e, _) => Is_free_left Γ cy 0 e) ini ->
      depends_on Γ cx cy (Bauto ck (ini, oth) states)

  | DepOnLocal : forall scope,
      depends_on_scope (fun Γ cx cy => Exists (depends_on Γ cx cy)) Γ cx cy scope ->
      depends_on Γ cx cy (Blocal scope).

  Section incl.
    Fact Is_free_left_list_incl' : forall Γ Γ' es,
      Forall (fun e => forall cx k, Is_free_left Γ cx k e -> Is_free_left Γ' cx k e) es ->
      forall cx k, Is_free_left_list Γ cx k es ->
              Is_free_left_list Γ' cx k es.
    Proof.
      intros * Hf * Hex.
      induction Hex; inv Hf; [left|right]; auto.
    Qed.

    Lemma Is_free_left_incl : forall Γ Γ' e,
        (forall x cx, HasCaus Γ x cx -> HasCaus Γ' x cx) ->
        (forall x cx, HasLastCaus Γ x cx -> HasLastCaus Γ' x cx) ->
        forall cx k, Is_free_left Γ cx k e ->
                Is_free_left Γ' cx k e.
    Proof.
      intros * Hc1 Hc2.
      induction e using exp_ind2; intros * Hfree; inv Hfree; constructor;
        repeat (match goal with
                | H: _ \/ _ |- _ \/ _ => destruct H; [left|right]
                | H: _ /\ _ |- _ /\ _ => destruct H; split; auto
                | H: Exists _ _ |- Exists _ _ => solve_Exists; simpl_Forall
                | H: exists _, Exists _ _ |- _ => destruct H as (x&?); exists x
                | H : exists _, _ /\ _ |- exists _, _ /\ _ => destruct H as (x&?&?); subst; esplit; split
                | H: Is_free_left_list _ _ _ _ |- _ => eapply Is_free_left_list_incl' in H; eauto
                end);
        eauto using Is_free_left.
    Qed.

    Lemma Is_defined_in_incl : forall blk Γ Γ',
        (forall x cx, HasCaus Γ x cx -> HasCaus Γ' x cx) ->
        forall cx, Is_defined_in Γ cx blk -> Is_defined_in Γ' cx blk.
    Proof.
      induction blk using block_ind2; intros * Hc * Hdef; inv Hdef;
        econstructor; eauto using Is_defined_in;
        solve_Exists; simpl_Forall; eauto.
      - destruct s.
        inv H1. econstructor; eauto. solve_Exists; simpl_Forall.
        eapply H; [|eauto]. intros *. rewrite 2 HasCaus_app. intros [|]; auto.
      - destruct s as [?(?&?)].
        inv H1. econstructor; eauto. solve_Exists; simpl_Forall.
        eapply H; [|eauto]. intros *. rewrite 2 HasCaus_app. intros [|]; auto.
      - inv H1. constructor.
        solve_Exists; simpl_Forall.
        eapply H; [|eauto].
        intros *. rewrite 2 HasCaus_app. intros [|]; auto.
    Qed.

    Fact depends_on_scope_incl {A} (P_dep : _ -> _ -> _ -> A -> Prop) : forall locs blks Γ Γ',
        (forall x cx, HasCaus Γ x cx -> HasCaus Γ' x cx) ->
        (forall x cx, HasLastCaus Γ x cx -> HasLastCaus Γ' x cx) ->
        (forall Γ Γ' cx cy,
            (forall x cx, HasCaus Γ x cx -> HasCaus Γ' x cx) ->
            (forall x cx, HasLastCaus Γ x cx -> HasLastCaus Γ' x cx) ->
            P_dep Γ cx cy blks -> P_dep Γ' cx cy blks) ->
        forall cx cy, depends_on_scope P_dep Γ cx cy (Scope locs blks) ->
                 depends_on_scope P_dep Γ' cx cy (Scope locs blks).
    Proof.
      intros * Hca Hla Hp * Hdep. inv Hdep.
      - eapply DepOnScope1; eauto.
        eapply Hp in H2; eauto; intros *.
        rewrite 2 HasCaus_app; intros [|]; eauto.
        rewrite 2 HasLastCaus_app; intros [|]; eauto.
      - eapply DepOnScope2; eauto.
        solve_Exists. destruct o as [(?&?)|]; auto. destruct_conjs.
        split; auto.
        eapply Is_free_left_incl in H0; eauto; intros *.
        rewrite 2 HasCaus_app; intros [|]; eauto.
        rewrite 2 HasLastCaus_app; intros [|]; eauto.
    Qed.

    Lemma depends_on_incl : forall blk Γ Γ',
        (forall x cx, HasCaus Γ x cx -> HasCaus Γ' x cx) ->
        (forall x cx, HasLastCaus Γ x cx -> HasLastCaus Γ' x cx) ->
        forall cx cy, depends_on Γ cx cy blk -> depends_on Γ' cx cy blk.
    Proof.
      induction blk using block_ind2; intros * Hc1 Hc2 * Hdep; inv Hdep.
      - (* equation *)
        econstructor; eauto.
        eapply Is_free_left_list_incl'; eauto. simpl_Forall; eauto using Is_free_left_incl.
      - (* reset *)
        econstructor. solve_Exists. simpl_Forall; eauto.
      - eapply DepOnReset2; eauto using Is_free_left_incl.
        solve_Exists. destruct H2; eauto using Is_defined_in_incl.
      - (* switch *)
        econstructor. solve_Exists.
        destruct s. eapply depends_on_scope_incl; eauto.
        intros; solve_Exists; simpl_Forall; eauto.
      - eapply DepOnSwitch2; eauto using Is_free_left_incl.
          destruct H2; eauto using Is_defined_in_incl.
      - (* automaton *)
        econstructor. solve_Exists.
        destruct s as [?(?&?)]. eapply depends_on_scope_incl; eauto.
        intros; solve_Exists; simpl_Forall; eauto.
      - eapply DepOnAuto2; solve_Exists; eauto. destruct H3; eauto using Is_defined_in_incl.
      - eapply DepOnAuto3; solve_Exists; eauto using Is_free_left_incl.
        destruct H2; eauto using Is_defined_in_incl.
      - (* local *)
        constructor. eapply depends_on_scope_incl; eauto.
        intros; solve_Exists; simpl_Forall; eauto.
    Qed.
  End incl.

  Definition idcaus_of_scope {A} f_idcaus (s : scope A) :=
    let 'Scope locs blks := s in
    idcaus_of_senv (senv_of_locs locs) ++ f_idcaus blks.

  Fixpoint idcaus_of_locals blk :=
    match blk with
    | Beq _ => []
    | Breset blocks _ => flat_map idcaus_of_locals blocks
    | Bswitch _ branches => flat_map (fun '(_, s) => idcaus_of_scope (flat_map idcaus_of_locals) s) branches
    | Bauto _ _ states => flat_map (fun '(_, s) => idcaus_of_scope (fun '(blks, _) => flat_map idcaus_of_locals blks) s) states
    | Blocal s => idcaus_of_scope (flat_map idcaus_of_locals) s
    end.

  Global Hint Unfold idcaus_of_locals : list.

  Definition graph_of_node {PSyn prefs v a} (n : @node PSyn prefs) (g : AcyGraph v a) : Prop :=
    PS.Equal (vertices g)
             (PSP.of_list (map snd (idcaus (n_in n ++ n_out n) ++ idcaus_of_locals (n_block n))))
    /\ (forall cx cy, depends_on (senv_of_inout (n_in n ++ n_out n)) cx cy (n_block n) ->
                is_arc g cy cx).

  Definition node_causal {PSyn prefs} (n : @node PSyn prefs) :=
    NoDup (map snd (idcaus (n_in n ++ n_out n) ++ idcaus_of_locals (n_block n))) /\
    exists v a (g : AcyGraph v a), graph_of_node n g.

  (* Some properties *)

  Lemma node_causal_NoDup {PSyn prefs} : forall (nd : @node PSyn prefs),
      node_causal nd ->
      NoDup (map snd (idcaus (n_in nd ++ n_out nd))).
  Proof.
    intros * (Hnd&_). rewrite map_app in Hnd.
    now apply NoDup_app_l in Hnd.
  Qed.

  Fact Is_free_left_list_length' Γ : forall es x k,
      Forall (fun e => forall x k, Is_free_left Γ x k e -> k < Datatypes.length (annot e)) es ->
      Is_free_left_list Γ x k es ->
      k < length (annots es).
  Proof.
    induction es; intros * Hf Hfree; inv Hfree; simpl;
      rewrite app_length, length_annot_numstreams.
    - (* now ! *)
      apply PeanoNat.Nat.lt_lt_add_r; auto.
    - (* later *)
      inv Hf.
      specialize (IHes _ _ H4 H3).
      apply PeanoNat.Nat.lt_sub_lt_add_l in IHes; auto.
  Qed.

  Lemma Is_free_left_length {PSyn prefs} (G: @global PSyn prefs) Γ : forall e x k,
      wl_exp G e ->
      Is_free_left Γ x k e ->
      k < length (annot e).
  Proof.
    Local Ltac solve_forall2 Ha H :=
      setoid_rewrite <- Ha;
      eapply Is_free_left_list_length'; eauto;
      eapply Forall_Forall in H; eauto;
      clear - H;
      eapply Forall_impl; eauto; intros ? [? ?] ? ? ?; eauto.

    induction e using exp_ind2; intros * Hwl Hfree; inv Hfree; inv Hwl; simpl; auto.
    - (* fby *)
      solve_forall2 H8 H.
    - (* arrow *)
      destruct H3 as [?|?]; auto. solve_forall2 H8 H. solve_forall2 H9 H0.
    - (* when *)
      rewrite map_length. destruct H2 as [[? ?]|?]; auto.
      solve_forall2 H7 H.
    - (* merge *)
      rewrite map_length. destruct H2 as [[? ?]|?]; auto.
      eapply Forall_Forall in H; eauto. eapply Forall_Forall in H6; eauto. clear H7 H.
      eapply Forall_Exists in H0; eauto. eapply Exists_exists in H0 as (?&?&((?&IH)&Wl)&?).
      solve_forall2 H0 IH.
    - (* case *)
      rewrite map_length. destruct H3 as [[? ?]|[Hex|(?&?&Hex)]]; subst; simpl in *; auto.
      + eapply Exists_exists in Hex as (?&Hin&Hex); subst.
        rewrite Forall_forall in *; eauto. specialize (H10 _ Hin). erewrite <-H11; eauto.
        eapply Is_free_left_list_length'; eauto.
        eapply Forall_impl_In in H; eauto; simpl. intros; simpl. eapply H2; eauto.
        eapply Forall_forall in H10; eauto.
      + specialize (H13 _ eq_refl). specialize (H12 _ eq_refl).
        solve_forall2 H13 H0.
  Qed.

  Corollary Is_free_left_list_length {PSyn prefs} (G: @global PSyn prefs) Γ : forall es x k,
      Forall (wl_exp G) es ->
      Is_free_left_list Γ x k es ->
      k < length (annots es).
  Proof.
    intros * Hwl Hfree.
    eapply Is_free_left_list_length'; eauto.
    eapply Forall_impl; eauto. intros.
    eapply Is_free_left_length; eauto.
  Qed.

  Lemma Is_free_left_list_Exists Γ : forall es x k,
      Is_free_left_list Γ x k es ->
      exists k', Exists (Is_free_left Γ x k') es.
  Proof.
    induction es; intros * Hfree; inv Hfree.
    - exists k. left; auto.
    - specialize (IHes _ _ H3) as [k' ?].
      exists k'. right; auto.
  Qed.

  Lemma Is_free_left_In_snd Γ : forall e x k,
      Is_free_left Γ x k e ->
      exists y, HasCaus Γ y x \/ HasLastCaus Γ y x.
  Proof.
    induction e using exp_ind2; intros * Hfree; inv Hfree.
    - (* var *) eauto.
    - (* last *) eauto.
    - (* unop *)
      eauto.
    - (* binop *)
      destruct H1; eauto.
    - (* fby *)
      rewrite Forall_forall in *.
      eapply Is_free_left_list_Exists in H3 as (?&Hex).
      simpl_Exists; eauto.
    - (* arrow *)
      rewrite Forall_forall in *.
      destruct H3 as [Hex|Hex].
      1,2:(eapply Is_free_left_list_Exists in Hex as (?&Hex);
           simpl_Exists; eauto).
    - (* when *)
      rewrite Forall_forall in *.
      destruct H2 as [(_&Hin)|Hex]; eauto.
      + eapply Is_free_left_list_Exists in Hex as (?&Hex).
        simpl_Exists; eauto.
    - (* merge *)
      repeat setoid_rewrite Forall_forall in H.
      destruct H2 as [(_&Hin)|Hex]; eauto.
      + eapply Exists_exists in Hex as (?&?&Hex).
        eapply Is_free_left_list_Exists in Hex as (?&Hex).
        simpl_Exists; eauto.
    - (* case *)
      rewrite Forall_forall in *.
      destruct H3 as [(_&Hin)|[Hex|(?&?&Hex)]]; subst; simpl in *; eauto.
      + eapply Exists_exists in Hex as (?&Hin&Hex); subst.
        eapply Is_free_left_list_Exists in Hex as (?&Hex).
        simpl_Exists.
        eapply H, Forall_forall in Hin; eauto.
      + rewrite Forall_forall in *.
        eapply Is_free_left_list_Exists in Hex as (?&Hex).
        simpl_Exists; eauto.
    - (* app *)
      rewrite Forall_forall in *.
      destruct H7 as [(?&Hex)|Hex]; simpl_Exists; eauto.
  Qed.

  Corollary Is_free_left_list_In_snd Γ : forall es x k,
      Is_free_left_list Γ x k es ->
      exists y, HasCaus Γ y x \/ HasLastCaus Γ y x.
  Proof.
    intros * Hfree.
    eapply Is_free_left_list_Exists in Hfree as (?&Hex).
    eapply Exists_exists in Hex as (?&_&Hfree).
    eapply Is_free_left_In_snd in Hfree; eauto.
  Qed.

  Local Hint Constructors Is_defined_in : lcaus.

  Lemma Is_defined_in_Is_defined_in : forall x cx blk Γ,
      HasCaus Γ x cx ->
      Syn.Is_defined_in x blk ->
      Is_defined_in Γ cx blk.
  Proof.
    induction blk using block_ind2; intros * Hin Hdep; inv Hdep; eauto with lcaus.
    1-4:simpl_Exists; simpl_Forall; econstructor; solve_Exists.
    - destruct s. inv H1; constructor.
      solve_Exists. simpl_Forall. eapply H; eauto.
      apply HasCaus_app; auto.
    - destruct s as [?(?&?)]. inv H1; constructor.
      solve_Exists. simpl_Forall. eapply H; eauto.
      apply HasCaus_app; auto.
    - inv H1. constructor.
      solve_Exists. simpl_Forall. eapply H; eauto.
      apply HasCaus_app; auto.
  Qed.

  (** ** Causality check *)

  Section collect_free.

    Variable cenv cenvl : Env.t ident.

    Definition assemble_brs_free_left_list {A} pss (tys : list A) :=
      List.fold_left (fun ps1 ps2 => List.map (fun '(ps1, ps2) => PS.union ps1 ps2) (List.combine ps1 ps2))
                     pss (List.map (fun _ => PS.empty) tys).

    Definition collect_free_var cenv (x : ident) : ident :=
      or_default xH (Env.find x cenv).

    Fixpoint collect_free_clock (ck : clock) : PS.t :=
      match ck with
      | Cbase => PS.empty
      | Con ck x _ => PS.add (collect_free_var cenv x) (collect_free_clock ck)
      end.

    Fixpoint collect_free_left (e : exp) {struct e} : list PS.t :=
      let collect_free_left_list (es : list exp) := flat_map collect_free_left es in
      match e with
      | Econst _ | Eenum _ _ => [PS.empty]
      | Evar x _ => [PS.singleton (collect_free_var cenv x)]
      | Elast x _ => [PS.singleton (collect_free_var cenvl x)]
      | Eunop _ e _ => (collect_free_left e)
      | Ebinop _ e1 e2 _ =>
        let ps1 := collect_free_left e1 in
        let ps2 := collect_free_left e2 in
        List.map (fun '(ps1, ps2) => PS.union ps1 ps2) (List.combine ps1 ps2)
      | Efby e0s _ _ =>
        collect_free_left_list e0s
      | Earrow e0s es _ =>
        let ps1 := collect_free_left_list e0s in
        let ps2 := collect_free_left_list es in
        List.map (fun '(ps1, ps2) => PS.union ps1 ps2) (List.combine ps1 ps2)
      | Ewhen es x _ _ =>
        let cx := collect_free_var cenv x in
        List.map (fun ps => PS.add cx ps) (collect_free_left_list es)
      | Emerge (x, _) es (tys, _) =>
        let ps := assemble_brs_free_left_list (List.map (fun es => collect_free_left_list (snd es)) es) tys in
        List.map (PS.add (collect_free_var cenv x)) ps
      | Ecase e es d (tys, _) =>
        let ps0 := collect_free_left e in
        let psd := or_default_with (List.map (fun _ => PS.empty) tys) collect_free_left_list d in
        let ps1 := assemble_brs_free_left_list (psd::List.map (fun es => collect_free_left_list (snd es)) es) tys in
        List.map (PS.union (nth 0 ps0 PS.empty)) ps1
      | Eapp _ es er a =>
        let ps := PSUnion (collect_free_left_list er ++ collect_free_left_list es) in
        List.map (fun _ => ps) a
      end.

    Definition collect_free_left_list (es : list exp) :=
      flat_map collect_free_left es.

  End collect_free.

  Definition unions_fuse envs := List.fold_left (Env.union_fuse PS.union) envs (@Env.empty _).

  Definition collect_depends_scope {A} (f_coll : _ -> _ -> A -> Env.t PS.t) (cenv cenvl : Env.t ident) (s : scope A) :=
    let 'Scope locs blks := s in
    let cenv' := Env.union cenv (Env.from_list (map (fun '(x, (_, _, cx, _)) => (x, cx)) locs)) in
    let cenvl' := Env.union cenvl (Env.from_list (map_filter (fun '(x, (_, _, _, o)) => option_map (fun '(_, cx) => (x, cx)) o) locs)) in
    let deps1 := f_coll cenv' cenvl' blks in
    let deps2 := Env.from_list
                   (map_filter (fun '(_, (_, ck, _, o)) =>
                                  option_map (fun '(e, cx) => (cx, nth 0 (collect_free_left cenv' cenvl' e) PS.empty)) o) locs) in
    Env.union_fuse PS.union deps1 deps2.

  Fixpoint collect_depends_on (cenv cenvl : Env.t ident) (d : block) : Env.t PS.t :=
    match d with
    | Beq (xs, es) =>
      Env.from_list
        (List.combine
           (List.map (collect_free_var cenv) xs)
           (collect_free_left_list cenv cenvl es))
    | Breset blocks er =>
      let pr := collect_free_left cenv cenvl er in
      Env.map (fun ps => PS.union (nth 0 pr PS.empty) ps)
              (unions_fuse (map (collect_depends_on cenv cenvl) blocks))
    | Bswitch ec branches =>
      let pc := collect_free_left cenv cenvl ec in
      Env.map (fun ps => PS.union (nth 0 pc PS.empty) ps)
              (unions_fuse (map (fun blks =>
                                   collect_depends_scope
                                     (fun cenv cenvl blks => unions_fuse (map (collect_depends_on cenv cenvl) blks)) cenv cenvl (snd blks)) branches))
    | Bauto ck (ini, oth) states =>
        let pc1 := PSUnion (map (fun '(e, _) => nth 0 (collect_free_left cenv cenvl e) PS.empty) ini) in
        let pc2 := collect_free_clock cenv ck in
        let pc := PS.union pc1 pc2 in
        Env.map (fun ps => PS.union pc ps)
                (unions_fuse (map (fun blks =>
                                     collect_depends_scope
                                       (fun cenv cenvl blks => unions_fuse (map (collect_depends_on cenv cenvl) (fst blks)))
                                       cenv cenvl (snd blks)) states))
    | Blocal scope =>
        collect_depends_scope (fun cenv' cenvl' blks => unions_fuse (map (collect_depends_on cenv' cenvl') blks))
                              cenv cenvl scope
    end.

  Definition build_graph {PSyn prefs} (n : @node PSyn prefs) : Env.t PS.t :=
    let vo := collect_depends_on
                (Env.from_list (idcaus (n_in n ++ n_out n)))
                (@Env.empty _)
                (n_block n) in
    Env.union_fuse PS.union vo (Env.from_list (map (fun '(_, (_, _, cx)) => (cx, PS.empty)) (n_in n))).

  Definition check_node_causality {PSyn prefs} (n : @node PSyn prefs) : res unit :=
    if check_nodup (map snd (idcaus (n_in n ++ n_out n) ++ idcaus_of_locals (n_block n))) then
      match build_acyclic_graph (Env.map PSP.to_list (build_graph n)) with
      | OK _ => OK tt
      | Error msg => Error (MSG "Node " :: (CTX (n_name n)) :: MSG " : " :: msg)
      end
    else Error (MSG "Node " :: (CTX (n_name n)) :: MSG " has duplicated causality annotations" :: nil).

  Definition check_causality {PSyn prefs} (G : @global PSyn prefs) :=
    mmap check_node_causality (nodes G).

  Fact collect_free_left_list_length' cenv cenv' : forall es,
      Forall (fun e => length (collect_free_left cenv cenv' e) = length (annot e)) es ->
      length (collect_free_left_list cenv cenv' es) = length (annots es).
  Proof.
    induction es; intros * Hf; inv Hf; simpl; auto.
    repeat rewrite app_length. f_equal; auto.
  Qed.

  Fact assemble_brs_free_left_list_length {A} : forall pss (tys : list A),
      Forall (fun ps => length ps = length tys) pss ->
      length (assemble_brs_free_left_list pss tys) = length tys.
  Proof.
    unfold assemble_brs_free_left_list.
    intros * Hlen.
    assert (Forall (fun ps => Datatypes.length ps = Datatypes.length (map (fun _ => PS.empty) tys)) pss) as Hlen'.
    { eapply Forall_impl; [|eauto]; intros.
      rewrite map_length; auto. } clear Hlen.
    replace (Datatypes.length tys) with (Datatypes.length (map (fun _ => PS.empty) tys))
      by (rewrite map_length; auto).
    revert Hlen'. generalize (map (fun _ => PS.empty) tys). clear tys.
    induction pss; intros; inv Hlen'; simpl; auto.
    rewrite IHpss; eauto.
    - rewrite map_length, combine_length, H1. apply Nat.min_id.
    - eapply Forall_impl; [|eauto].
      intros ? Heq.
      rewrite map_length, combine_length, Heq, H1.
      symmetry. apply Nat.min_id.
  Qed.

  Lemma collect_free_left_length {PSyn prefs} : forall (G: @global PSyn prefs) cenv cenv' e,
      wl_exp G e ->
      length (collect_free_left cenv cenv' e) = length (annot e).
  Proof.
    Local Ltac solve_forall H :=
      eapply Forall_Forall in H; eauto;
      clear - H;
      eapply Forall_impl; eauto; intros ? [? ?]; auto.

    induction e using exp_ind2; intros Hwl; inv Hwl; simpl; try reflexivity.
    - (* unop *)
      destruct a as (?&?).
      rewrite <- length_annot_numstreams in H4. rewrite IHe; auto.
    - (* binop *)
      destruct a as (?&?).
      rewrite <- length_annot_numstreams in H6, H7.
      rewrite map_length, combine_length, IHe1, IHe2, H6, H7; auto.
    - (* fby *)
      setoid_rewrite collect_free_left_list_length'; auto.
      solve_forall H.
    - (* arrow *)
      rewrite map_length, combine_length.
      setoid_rewrite collect_free_left_list_length'.
      rewrite H7, H8. apply PeanoNat.Nat.min_id.
      solve_forall H. solve_forall H0.
    - (* when *)
      rewrite map_length, map_length.
      setoid_rewrite collect_free_left_list_length'; auto.
      solve_forall H.
    - (* merge *)
      destruct x. rewrite map_length, assemble_brs_free_left_list_length, map_length; auto.
      rewrite Forall_map.
      rewrite Forall_forall in *; intros.
      erewrite <- H6; eauto.
      setoid_rewrite collect_free_left_list_length'; eauto.
      specialize (H _ H0). specialize (H5 _ H0).
      solve_forall H.
    - (* case *)
      rewrite map_length, assemble_brs_free_left_list_length, map_length; auto.
      constructor.
      + destruct d; simpl in *. 2:now rewrite map_length.
        erewrite <-H12; eauto. eapply collect_free_left_list_length'.
        eapply Forall_impl_In; [|eapply H0]; intros.
        eapply Forall_forall in H11; eauto.
      + rewrite Forall_map.
        rewrite Forall_forall in *; intros.
        erewrite <-H10; eauto.
        specialize (H _ H1); simpl in H. specialize (H9 _ H1).
        eapply collect_free_left_list_length'.
        eapply Forall_impl_In; [|eauto]. intros ? Hin ?.
        eapply Forall_forall in H; eauto.
    - (* app *) rewrite map_length; auto.
  Qed.

  Corollary collect_free_left_list_length {PSyn prefs} : forall (G: @global PSyn prefs) cenv cenv' es,
      Forall (wl_exp G) es ->
      length (collect_free_left_list cenv cenv' es) = length (annots es).
  Proof.
    intros * Hwl.
    eapply collect_free_left_list_length'.
    eapply Forall_impl; eauto. intros ? ?.
    eapply collect_free_left_length; eauto.
  Qed.

  Section collect_free_spec.

    Variable Γ : static_env.
    Variable cenv' cenvl' : Env.t ident.

    Hypothesis Heq : forall x cx, Env.find x cenv' = Some cx <-> HasCaus Γ x cx.
    Hypothesis Heql : forall x cx, Env.find x cenvl' = Some cx <-> HasLastCaus Γ x cx.

    Lemma collect_free_var_correct : forall x cx,
        InMembers x Γ ->
        collect_free_var cenv' x = cx ->
        HasCaus Γ x cx.
    Proof.
      intros * Hinm Hcoll.
      unfold collect_free_var in Hcoll. rewrite <-Heq.
      assert (exists cx, HasCaus Γ x cx) as (?&Hhas).
      { apply InMembers_In in Hinm; simpl_In. destruct Hinm.
        esplit. econstructor; eauto. }
      rewrite <-Heq in Hhas. setoid_rewrite Hhas in Hcoll; simpl in *; subst; auto.
    Qed.

    Hypothesis Hnd1 : NoDupMembers Γ.

    Lemma collect_free_var_complete : forall x cx,
        HasCaus Γ x cx ->
        collect_free_var cenv' x = cx.
    Proof.
      intros * Hin.
      unfold collect_free_var. apply Heq in Hin.
      setoid_rewrite Hin. reflexivity.
    Qed.

    Lemma collect_free_last_complete : forall x cx,
        HasLastCaus Γ x cx ->
        collect_free_var cenvl' x = cx.
    Proof.
      intros * Hin.
      unfold collect_free_var. apply Heql in Hin.
      setoid_rewrite Hin. reflexivity.
    Qed.

    Lemma collect_free_left_list_spec' {PSyn prefs} : forall (G: @global PSyn prefs) es x k,
        Forall (wl_exp G) es ->
        Forall (wx_exp Γ) es ->
        Forall (fun e => forall k, wl_exp G e -> wx_exp Γ e ->
                           Is_free_left Γ x k e ->
                           PS.In x (nth k (collect_free_left cenv' cenvl' e) PS.empty)) es ->
        Is_free_left_list Γ x k es ->
        PS.In x (List.nth k (collect_free_left_list cenv' cenvl' es) PS.empty).
    Proof.
      induction es; intros * Hwl Hwx Hf Hfree; inv Hwl; inv Hwx; inv Hf. inv Hfree. simpl.
      assert (length (collect_free_left cenv' cenvl' a) = numstreams a) as Hlen.
      { erewrite collect_free_left_length, length_annot_numstreams; eauto. }
      inv Hfree.
      * rewrite app_nth1. apply H5; eauto. congruence.
      * rewrite app_nth2. apply IHes; eauto. 1,2:congruence.
    Qed.

    Lemma psunion_collect_free_list_spec' {PSyn prefs} : forall (G: @global PSyn prefs) es x,
        Forall (wl_exp G) es ->
        Forall (wx_exp Γ) es ->
        Forall (fun e => forall k, wl_exp G e ->
                           wx_exp Γ e->
                           Is_free_left Γ x k e ->
                           PS.In x (nth k (collect_free_left cenv' cenvl' e) PS.empty)) es ->
        (exists k', Exists (Is_free_left Γ x k') es) ->
        PS.In x (PSUnion (collect_free_left_list cenv' cenvl' es)).
    Proof.
      induction es; intros * Hwl Hwx Hf (?&Hex); inv Hwl; inv Hwx; inv Hf. inv Hex. simpl.
      rewrite PSUnion_In_app.
      inv Hex; auto.
      + assert (Hk:=H0).
        eapply Is_free_left_length in Hk; eauto; erewrite <- collect_free_left_length in Hk; eauto.
        apply H5 in H0; auto.
        left. eapply In_In_PSUnion; eauto.
        eapply nth_In; eauto.
      + right. apply IHes; eauto.
    Qed.

    Fact ps_In_k_lt : forall x l k,
        PS.In x (nth k l PS.empty) ->
        k < length l.
    Proof.
      induction l; intros * Hin; simpl in *.
      - exfalso. eapply not_In_empty. destruct k; eauto.
      - destruct k; eauto.
        + apply PeanoNat.Nat.lt_0_succ.
        + apply Lt.lt_n_S; auto.
    Qed.

    Lemma Exists_Exists_Is_free {PSyn prefs} : forall (G: @global PSyn prefs) es x k,
      Forall (wl_exp G) es ->
      Forall (fun e => numstreams e = 1) es ->
      Exists (Is_free_left Γ x k) es ->
      Exists (Is_free_left Γ x 0) es.
    Proof.
      intros * Wl Num Free.
      simpl_Exists; simpl_Forall.
      assert (k = 0) as Hk'; subst; eauto.
      take (Is_free_left _ _ _ _) and eapply Is_free_left_length in it; eauto. 2:solve_Exists.
      rewrite length_annot_numstreams, Num in it.
      apply PeanoNat.Nat.lt_1_r; auto.
    Qed.
    Local Hint Resolve Exists_Exists_Is_free : lcaus.

    Fact assemble_brs_free_left_list_spec: forall x k pss (tys : list type),
        Forall (fun ps => length ps = length tys) pss ->
        Exists (fun ps => PS.In x (List.nth k ps PS.empty)) pss ->
        PS.In x (List.nth k (assemble_brs_free_left_list pss tys) PS.empty).
    Proof.
      unfold assemble_brs_free_left_list.
      intros * Hlen.
      assert (forall base : list PS.t,
                 Forall (fun ps => length ps = length base) pss ->
                 PS.In x
                       (nth k (fold_left (fun ps1 ps2 : list PS.t => map (fun '(ps0, ps3) => PS.union ps0 ps3)
                                                                      (combine ps1 ps2)) pss base) PS.empty) <->
                 Exists (fun ps : list PS.t => PS.In x (nth k ps PS.empty)) pss \/ PS.In x (nth k base PS.empty)).
      { clear Hlen tys. intros * Hlen; split; revert base Hlen.
        - induction pss; simpl; intros; inv Hlen; auto.
          apply IHpss in H as [H|H]; auto.
          2:{ clear - H2 H3. eapply Forall_impl; [|eauto].
              intros ? Heq. now rewrite map_length, combine_length, Heq, H2, Nat.min_id. }
          rewrite map_nth' with (d':=(PS.empty, PS.empty)) in H.
          2:{ eapply ps_In_k_lt in H; rewrite map_length in H; auto. }
          rewrite combine_nth in H; auto.
          apply PS.union_spec in H as [H|H]; auto.
        - induction pss; simpl; intros; inv Hlen; auto.
          + destruct H; auto.
            inv H.
          + eapply IHpss; eauto.
            1:{ clear - H2 H3. eapply Forall_impl; [|eauto].
                intros ? Heq. now rewrite map_length, combine_length, Heq, H2, Nat.min_id. }
            rewrite map_nth' with (d':=(PS.empty, PS.empty)).
            2:{ rewrite combine_length.
                destruct H. inv H.
                - apply ps_In_k_lt in H1. now rewrite <-H2, Nat.min_id.
                - simpl_Exists; simpl_Forall. apply ps_In_k_lt in H1.
                  now rewrite H2, Nat.min_id, <-H3.
                - apply ps_In_k_lt in H. now rewrite H2, Nat.min_id.
            }
            rewrite combine_nth; auto.
            rewrite PS.union_spec; auto.
            destruct H; auto.
            inv H; auto.
      }
      intros Hex. rewrite H; eauto.
      simpl_Forall. now rewrite map_length.
    Qed.

    Fact collect_free_left_spec {PSyn prefs}: forall (G: @global PSyn prefs) x e k,
        wl_exp G e ->
        wx_exp Γ e ->
        Is_free_left Γ x k e ->
        PS.In x (List.nth k (collect_free_left cenv' cenvl' e) PS.empty).
    Proof with eauto with lcaus.
      induction e using exp_ind2;
        (intros * Hwl Hwx Hfree;
         specialize (Is_free_left_length G Γ _ _ _ Hwl Hfree) as Hlen1;
         specialize (collect_free_left_length G cenv' cenvl' _ Hwl) as Hlen2;
         try destruct a as [ty [ck name]];
         inv Hwl; inv Hwx; inv Hfree; simpl in *;
         try rewrite <- length_annot_numstreams in *; idtac).
      - (* var *)
        apply PSF.singleton_2; auto.
        eapply collect_free_var_complete; eauto.
      - (* last *)
        apply PSF.singleton_2; auto.
        eapply collect_free_last_complete; eauto.
      - (* unop *)
        eapply IHe; eauto.
      - (* binop *)
        erewrite <- collect_free_left_length with (cenv:=cenv') (cenv':=cenvl') in H6, H7; eauto.
        repeat singleton_length.
        destruct H2 as [?|?].
        * apply PSF.union_2. eapply IHe1 in H; eauto.
        * apply PSF.union_3. eapply IHe2 in H; eauto.
      - (* fby *)
        erewrite <- collect_free_left_list_length with (cenv:=cenv') (cenv':=cenvl') in H7, H8; eauto.
        eapply collect_free_left_list_spec'; eauto.
      - (* arrow *)
        erewrite <- collect_free_left_list_length in H7, H8; eauto.
        erewrite map_nth' with (d':=(PS.empty, PS.empty)).
        2:(erewrite <- map_length, Hlen2; eauto).
        rewrite combine_nth. 2:setoid_rewrite H7; setoid_rewrite H8; auto.
        repeat rewrite PS.union_spec.
        destruct H5; [left|right]; eapply collect_free_left_list_spec'; eauto.
      - (* when *)
        erewrite <- collect_free_left_list_length with (cenv:=cenv') (cenv':=cenvl') in H6; eauto.
        erewrite map_nth' with (d':=PS.empty).
        2:(erewrite <- map_length, Hlen2; eapply Hlen1; eauto).
        destruct H4 as [(_&?)|?]; subst.
        * apply PSF.add_1; auto.
          eapply collect_free_var_complete; eauto.
        * apply PSF.add_2. eapply collect_free_left_list_spec'; eauto.
      - (* merge *)
        assert (Forall (fun ps : list PS.t => Datatypes.length ps = Datatypes.length tys)
                       (map (fun es0 => flat_map (collect_free_left cenv' cenvl') (snd es0)) es)) as Hlen'.
        { clear - H5 H6. rewrite Forall_map, Forall_forall in *; intros.
          erewrite <- H6; eauto.
          eapply collect_free_left_list_length; eauto. }
        erewrite map_nth' with (d':=PS.empty).
        2:(erewrite <- map_length, Hlen2; eauto).
        apply PSF.add_iff.
        destruct H3 as [(_&?)|Hfree]; subst; eauto using collect_free_var_complete.
        right.
        apply assemble_brs_free_left_list_spec; auto. solve_Exists. simpl_Forall.
        eapply collect_free_left_list_spec'; eauto.
      - (* case *)
        assert (Forall (fun ps : list PS.t => Datatypes.length ps = Datatypes.length tys)
                       (or_default_with (map (fun _ : type => PS.empty) tys)
                                        (fun es0 : list exp => flat_map (collect_free_left cenv' cenvl') es0) d ::
                                        map (fun es0 => flat_map (collect_free_left cenv' cenvl') (snd es0)) es)) as Hlen'.
        { constructor.
          - destruct d; simpl in *. 2:now rewrite map_length.
            erewrite <-H12; eauto.
            eapply collect_free_left_list_length; eauto.
          - rewrite Forall_map, Forall_forall in *; intros.
            erewrite <- H10; eauto.
            eapply collect_free_left_list_length; eauto. }
        erewrite map_nth' with (d':=PS.empty).
        2:(erewrite <- map_length, Hlen2; eauto).
        apply PS.union_spec.
        destruct H3 as [(_&Hfree)|[Hfree|(?&?&Hfree)]]; subst; simpl in *.
        2,3:right; apply assemble_brs_free_left_list_spec; auto.
        * left. apply IHe; auto.
        * right. solve_Exists. simpl_Forall.
          eapply collect_free_left_list_spec'; eauto.
        * left. eapply collect_free_left_list_spec'; eauto.
      - (* app *)
        erewrite map_nth'; eauto. 2:exact (Tenum (xH, 0), Cbase).
        rewrite PSUnion_In_app.
        destruct H15.
        * right. eapply psunion_collect_free_list_spec'; eauto.
        * left. eapply psunion_collect_free_list_spec'; eauto.
    Qed.

    Corollary collect_free_left_list_spec {PSyn prefs} : forall (G: @global PSyn prefs) es x k,
        Forall (wl_exp G) es ->
        Forall (wx_exp Γ) es ->
        Is_free_left_list Γ x k es ->
        PS.In x (List.nth k (collect_free_left_list cenv' cenvl' es) PS.empty).
    Proof.
      intros * Hwl Hwx.
      eapply collect_free_left_list_spec'; eauto.
      eapply Forall_impl; eauto; intros.
      eapply collect_free_left_spec; eauto.
    Qed.

  End collect_free_spec.

  Lemma unions_fuse_PS_In : forall x envs,
      Env.In x (unions_fuse envs) <-> Exists (Env.In x) envs.
  Proof.
    intros x envs.
    unfold unions_fuse.
    replace envs with (rev (rev envs)); auto using rev_involutive.
    rewrite fold_right_rev_left, <-Exists_rev.
    induction (rev envs); split; intros * Hin; simpl in *.
    - apply Env.Props.P.F.empty_in_iff in Hin; inv Hin.
    - inv Hin.
    - apply Env.union_fuse_In in Hin as [Hin|Hin]; auto.
      right. apply IHl; auto.
    - apply Env.union_fuse_In.
      inv Hin; auto.
      left. apply IHl; auto.
  Qed.

  Fact equiv_env_local {A} : forall Γ locs cenv',
      NoDupMembers locs ->
      (forall x, InMembers x locs -> ~In x (map fst Γ)) ->
      (forall x cx, Env.find x cenv' = Some cx <-> HasCaus Γ x cx) ->
      (forall x cx, Env.find x (Env.union cenv' (Env.from_list (map (fun '(x1, (_, _, cx1, _)) => (x1, cx1)) locs))) = Some cx
               <-> HasCaus (Γ ++ @senv_of_locs A locs) x cx).
  Proof.
    intros * Hnd1 Hnd2 Heq *. rewrite HasCaus_app. split; intros Hin.
    - apply Env.union_find4 in Hin as [|Hin].
      + left. eapply Heq; eauto.
      + apply Env.from_list_find_In in Hin. simpl_In.
        right. econstructor. solve_In. eauto.
    - destruct Hin as [Hin|Hin].
      + apply Env.union_find2. apply Heq; auto.
        rewrite <-Env.Props.P.F.not_find_in_iff, Env.In_from_list.
        intros Hinm. apply InMembers_In in Hinm as (?&?); simpl_In.
        eapply Hnd2; eauto using In_InMembers. inv Hin; solve_In.
      + apply Env.union_find3'. inv Hin. simpl_In.
        apply Env.find_In_from_list. solve_In. apply nodupmembers_map; auto. intros; destruct_conjs; auto.
  Qed.

  Lemma collect_depends_scope_dom {A} P_vd P_nd (P_wl: A -> _) P_wx f_coll P_def P_last
        {PSyn prefs} (G: @global PSyn prefs) :
    forall locs blks xs Γ cenv' cenvl' cx,
      NoDupMembers Γ ->
      (forall x cx, Env.find x cenv' = Some cx <-> HasCaus Γ x cx) ->
      incl xs (map fst Γ) ->
      VarsDefinedScope P_vd (Scope locs blks) xs ->
      NoDupScope P_nd (map fst Γ) (Scope locs blks) ->
      wl_scope P_wl G (Scope locs blks) ->
      wx_scope P_wx Γ (Scope locs blks) ->
      (forall Γ xs cenv' cenvl',
          NoDupMembers Γ ->
          (forall x cx, Env.find x cenv' = Some cx <-> HasCaus Γ x cx) ->
          incl xs (map fst Γ) ->
          P_vd blks xs ->
          P_nd (map fst Γ) blks ->
          P_wl blks ->
          P_wx Γ blks ->
          Env.In cx (f_coll cenv' cenvl' blks) <-> P_def Γ blks \/ P_last blks) ->
      Env.In cx (collect_depends_scope f_coll cenv' cenvl' (Scope locs blks))
      <-> Is_defined_in_scope P_def Γ (Scope locs blks) \/ Is_last_in_scope P_last cx (Scope locs blks).
  Proof.
    intros * Hnd Hca Hincl Hvd Hndloc Hwl Hwx Hp.
    inv Hvd. inv Hndloc. inv Hwl. inv Hwx.
    assert (NoDupMembers (Γ ++ senv_of_locs locs)) as Hnd'.
    { apply NoDupMembers_app; auto.
      - apply nodupmembers_map; auto. intros; destruct_conjs; auto.
      - intros * Hin Hinm2. apply InMembers_senv_of_locs in Hinm2.
        eapply H5; eauto. now rewrite <-fst_InMembers.
    }
    simpl. rewrite Env.union_fuse_In, Hp; eauto.
    2:now apply equiv_env_local.
    2:{ rewrite map_app, map_fst_senv_of_locs.
        apply incl_appl'; auto. }
    2:now rewrite map_app, map_fst_senv_of_locs.
    split; intros Hin; simpl in *.
    - destruct Hin as [[Hin|Hin]|Hin]; subst.
      + left. now constructor.
      + right. now constructor.
      + apply Env.In_from_list, InMembers_In in Hin as (?&Hin).
        simpl_In. right. eapply LastScope2; eauto.
    - destruct Hin as [Hin|Hin]; inv Hin; auto.
      right. eapply Env.In_from_list, In_InMembers. solve_In. reflexivity.
  Qed.

  Lemma collect_depends_on_dom {PSyn prefs} (G: @global PSyn prefs) : forall blk xs Γ cenv' cenvl',
      NoDupMembers Γ ->
      (forall x cx, Env.find x cenv' = Some cx <-> HasCaus Γ x cx) ->
      VarsDefined blk xs ->
      incl xs (map fst Γ) ->
      NoDupLocals (map fst Γ) blk ->
      wl_block G blk ->
      wx_block Γ blk ->
      forall cx, Env.In cx (collect_depends_on cenv' cenvl' blk) <-> Is_defined_in Γ cx blk \/ Is_last_in cx blk.
  Proof.
    Opaque collect_depends_scope.
    induction blk using block_ind2; intros * Hnd Heq Hvars Hincl Hndloc Hwl Hwx cx;
      inv Hvars; inv Hndloc; inv Hwl; inv Hwx; simpl.
    - (* equation *)
      destruct eq; simpl.
      rewrite Env.In_from_list, fst_InMembers, combine_map_fst'.
      2:{ inv H0. erewrite map_length, collect_free_left_list_length; eauto. }
      split; intros Hin.
      + simpl_In. left. econstructor; eauto.
        eapply collect_free_var_correct; eauto.
        destruct H2.
        eapply fst_InMembers; eauto.
      + destruct Hin as [Hin|Hin]; inv Hin.
        eapply collect_free_var_complete in H4; eauto.
        solve_In.
    - (* reset *)
      rewrite Env.Props.P.F.map_in_iff, unions_fuse_PS_In.
      split; intros Hin.
      + simpl_Exists. simpl_Forall. inv_VarsDefined.
        edestruct H as ([|]&_); eauto; [|left|right].
        1:{ etransitivity; eauto using incl_concat. }
        1,2:constructor; solve_Exists.
      + destruct Hin as [Hin|Hin]; inv Hin; solve_Exists; simpl_Forall; inv_VarsDefined.
        1,2:eapply H; eauto.
        1,2:etransitivity; eauto using incl_concat.
    - (* switch *)
      erewrite Env.Props.P.F.map_in_iff, unions_fuse_PS_In, Exists_map,
        Exists_Exists_iff with (Q:=fun s => Is_defined_in_scope _ _ (snd s) \/ Is_last_in_scope _ _ (snd s)).
      1:{ split; [intros Hdef|intros [Hdef|Hdef]; inv Hdef]; solve_Exists.
          destruct Hdef; [left|right]; constructor; solve_Exists. }
      intros * Hin; simpl_Forall.
      destruct s. eapply collect_depends_scope_dom; eauto.
      intros. rewrite unions_fuse_PS_In.
      split; [intros * Hex| intros * [Hex|Hex]]; solve_Exists; inv_VarsDefined; simpl_Forall.
      + eapply H in Hex as [|]; eauto; [left|right|]; solve_Exists.
        etransitivity; eauto. rewrite <-H16; eauto using incl_concat.
      + solve_Exists. eapply H; eauto.
        etransitivity; eauto. rewrite <-H16; eauto using incl_concat.
      + solve_Exists. eapply H; eauto.
        etransitivity; eauto. rewrite <-H16; eauto using incl_concat.
    - (* automaton *)
      erewrite Env.Props.P.F.map_in_iff, unions_fuse_PS_In, Exists_map,
        Exists_Exists_iff with (Q:=fun s => Is_defined_in_scope _ _ (snd s) \/ Is_last_in_scope _ _ (snd s)).
      1:{ split; [intros Hdef|intros [Hdef|Hdef]; inv Hdef]; solve_Exists.
          destruct Hdef; [left|right]; constructor; solve_Exists. }
      intros * Hin; simpl_Forall.
      destruct s as [?(?&?)]. eapply collect_depends_scope_dom; eauto.
      intros. rewrite unions_fuse_PS_In.
      split; [intros * Hex| intros * [Hex|Hex]]; solve_Exists; inv_VarsDefined; simpl_Forall.
      + eapply H in Hex as [|]; eauto; [left|right|]; solve_Exists.
        etransitivity; eauto. rewrite <-H19; eauto using incl_concat.
      + solve_Exists. eapply H; eauto.
        etransitivity; eauto. rewrite <-H19; eauto using incl_concat.
      + solve_Exists. eapply H; eauto.
        etransitivity; eauto. rewrite <-H19; eauto using incl_concat.
    - (* locals *)
      erewrite collect_depends_scope_dom; eauto.
      + split; intros [Hdef|Hdef]; eauto using Is_defined_in, Is_last_in;
          inv Hdef; eauto.
      + intros. rewrite unions_fuse_PS_In.
        split; [intros * Hex| intros * [Hex|Hex]]; solve_Exists; inv_VarsDefined; simpl_Forall.
        * eapply H in Hex as [|]; eauto; [left|right|]; solve_Exists.
          etransitivity; eauto. rewrite <-H11; eauto using incl_concat.
        * solve_Exists. eapply H; eauto.
          etransitivity; eauto. rewrite <-H11; eauto using incl_concat.
        * solve_Exists. eapply H; eauto.
          etransitivity; eauto. rewrite <-H11; eauto using incl_concat.
  Qed.

  Corollary flat_map_collect_depends_on_dom {PSyn prefs} (G: @global PSyn prefs) : forall blks Γ cenv' cenvl' xs,
      NoDupMembers Γ ->
      (forall x cx, Env.find x cenv' = Some cx <-> HasCaus Γ x cx) ->
      Forall2 VarsDefined blks xs ->
      incl (concat xs) (map fst Γ) ->
      Forall (NoDupLocals (map fst Γ)) blks ->
      Forall (wl_block G) blks ->
      Forall (wx_block Γ) blks ->
      forall cx, Env.In cx (unions_fuse (map (collect_depends_on cenv' cenvl') blks)) <->
              Exists (Is_defined_in Γ cx) blks \/ Exists (Is_last_in cx) blks.
  Proof.
    intros * Hnd Heq Hvd Hincl Hndl Hwl Hwx ?.
    split; intros Hin.
    - eapply unions_fuse_PS_In in Hin. simpl_Exists. simpl_Forall. inv_VarsDefined.
      eapply collect_depends_on_dom in Hin as [|]; eauto; [left|right|]. 1,2:solve_Exists.
      etransitivity; eauto using incl_concat.
    - eapply unions_fuse_PS_In.
      destruct Hin; solve_Exists; simpl_Forall; inv_VarsDefined.
      1,2:eapply collect_depends_on_dom; eauto.
      1,2:etransitivity; eauto using incl_concat.
  Qed.

  Lemma unions_fuse_Subset : forall x envs e ps,
      In e envs ->
      Env.find x e = Some ps ->
      exists ps', Env.find x (unions_fuse envs) = Some ps' /\ PS.Subset ps ps'.
  Proof.
    intros x envs.
    unfold unions_fuse.
    replace envs with (rev (rev envs)); auto using rev_involutive.
    setoid_rewrite fold_right_rev_left. setoid_rewrite <-In_rev.
    induction (rev envs); intros * Hin Hfind; simpl in *. inv Hin.
    rewrite Env.union_fuse_spec. inv Hin.
    - rewrite Hfind.
      destruct (Env.find _ _); do 2 esplit; eauto. 2:reflexivity.
      apply PSP.union_subset_2.
    - eapply IHl in H as (?&Hfind'&Hsub); eauto.
      rewrite Hfind'.
      destruct (Env.find x a); do 2 esplit; eauto.
      etransitivity; eauto. apply PSP.union_subset_1.
  Qed.

  Lemma collect_free_var_nodup: forall xs cenv',
      Forall (fun x => Env.In x cenv') xs ->
      NoDup xs ->
      NoDup (map snd (Env.elements cenv')) ->
      NoDup (map (collect_free_var cenv') xs).
  Proof.
    induction xs; intros * Hf Hxs Hcenv'; inv Hf; inv Hxs; simpl.
    - constructor.
    - destruct H1 as (?&Hfind).
      unfold collect_free_var, Env.MapsTo in *. rewrite Hfind; simpl.
      constructor; eauto.
      contradict H3.
      simpl_In.
      eapply Forall_forall in H2 as (?&Hfind'); eauto. unfold Env.MapsTo in *.
      rewrite Hfind' in Hfind; simpl in Hfind; subst.
      eapply Env.NoDup_snd_elements with (x1:=a) (x2:=x0) in Hcenv'; eauto; subst; auto.
  Qed.

  Fact NoDup_locals_inv : forall blks blk xs,
      In blk blks ->
      NoDup (map snd (xs ++ flat_map idcaus_of_locals blks)) ->
      NoDup (map snd (xs ++ idcaus_of_locals blk)).
  Proof.
    intros * Hin Hnd.
    repeat rewrite map_app in *.
    eapply nodup_app_map_flat_map; eauto.
  Qed.

  Fact NoDup_locals_inv2 {A B} (f_idcaus : B -> list (ident * ident)) : forall (brs : list (A * B)) k blks xs,
      In (k, blks) brs ->
      NoDup (map snd (xs ++ flat_map (fun '(_, blks) => f_idcaus blks) brs)) ->
      NoDup (map snd (xs ++ f_idcaus blks)).
  Proof.
    intros * Hin Hnd.
    repeat rewrite map_app in *.
    eapply nodup_app_map_flat_map with (ys:=map snd brs); eauto. solve_In.
    erewrite flat_map_concat_map, map_map, <-flat_map_concat_map, flat_map_ext; eauto.
    intros; destruct_conjs; auto.
  Qed.

  Fact map_fst_map_filter : forall (locs : list (ident * (type * clock * ident * option _))),
      map fst (map_filter (fun '(x0, (_, _, _, o)) => option_map (fun '(_, cx) => (x0, cx)) o) locs) =
      map_filter (fun '(x0, (_, _, o)) => option_map (fun _ : exp * ident => x0) o) locs.
  Proof.
    intros.
    erewrite map_map_filter, map_filter_ext; eauto.
    intros; destruct_conjs. destruct o as [(?&?)|]; auto.
  Qed.

  Fact equiv_env_last_local {A} : forall Γ locs cenv',
      NoDupMembers locs ->
      (forall x, InMembers x locs -> ~In x (map fst Γ)) ->
      (forall x cx, Env.find x cenv' = Some cx <-> HasLastCaus Γ x cx) ->
      (forall x cx, Env.find x (Env.union cenv' (Env.from_list (map_filter (fun '(x2, (_, _, _, o)) => option_map (fun '(_, cx0) => (x2, cx0)) o) locs))) = Some cx
               <-> HasLastCaus (Γ ++ @senv_of_locs A locs) x cx).
  Proof.
    intros * Hnd1 Hnd2 Heq *. rewrite HasLastCaus_app. split; intros Hin.
    - apply Env.union_find4 in Hin as [|Hin].
      + left. eapply Heq; eauto.
      + apply Env.from_list_find_In in Hin. simpl_In.
        right. econstructor. solve_In. simpl. eauto.
    - destruct Hin as [Hin|Hin].
      + apply Env.union_find2. apply Heq; auto.
        rewrite <-Env.Props.P.F.not_find_in_iff, Env.In_from_list.
        intros Hinm. apply InMembers_In in Hinm as (?&?); simpl_In.
        eapply Hnd2; eauto using In_InMembers. inv Hin; solve_In.
      + apply Env.union_find3'. inv Hin. simpl_In. subst.
        apply Env.find_In_from_list. solve_In. apply nodupmembers_map_filter; auto.
        intros; destruct_conjs; auto. destruct o as [(?&?)|]; simpl; auto.
  Qed.

  Fact collect_free_clock_spec : forall Γ cenv x cx ck,
      (forall x cx, Env.find x cenv = Some cx <-> HasCaus Γ x cx) ->
      Is_free_in_clock x ck ->
      HasCaus Γ x cx ->
      PS.In cx (collect_free_clock cenv ck).
  Proof.
    induction ck; intros * Href Hfree Hcaus; inv Hfree; simpl; eauto using PSF.add_2.
    eapply PSF.add_1, collect_free_var_complete; eauto.
  Qed.

  Lemma collect_depends_scope_spec {A} f_idcaus P_vd P_nd P_wl P_wx P_dep f_dep {PSyn prefs} (G: @global PSyn prefs) :
    forall x y locs (blks: A) xs Γ cenv' cenvl',
      NoDupMembers Γ ->
      (forall x cx, Env.find x cenv' = Some cx <-> HasCaus Γ x cx) ->
      (forall x cx, Env.find x cenvl' = Some cx <-> HasLastCaus Γ x cx) ->
      NoDup (map snd (Env.elements cenv' ++ Env.elements cenvl' ++ idcaus_of_scope f_idcaus (Scope locs blks))) ->
      VarsDefinedScope P_vd (Scope locs blks) xs ->
      NoDup xs ->
      Forall (fun x => Env.In x cenv') xs ->
      NoDupScope P_nd (map fst Γ) (Scope locs blks) ->
      wl_scope P_wl G (Scope locs blks) ->
      wx_scope P_wx Γ (Scope locs blks) ->
      depends_on_scope P_dep Γ x y (Scope locs blks) ->
      (forall xs Γ cenv' cenvl',
          NoDupMembers Γ ->
          (forall x cx, Env.find x cenv' = Some cx <-> HasCaus Γ x cx) ->
          (forall x cx, Env.find x cenvl' = Some cx <-> HasLastCaus Γ x cx) ->
          NoDup (map snd (Env.elements cenv' ++ Env.elements cenvl' ++ f_idcaus blks)) ->
          P_vd blks xs ->
          NoDup xs ->
          Forall (fun x => Env.In x cenv') xs ->
          P_nd (map fst Γ) blks ->
          P_wl blks ->
          P_wx Γ blks ->
          P_dep Γ x y blks ->
          exists s, Env.MapsTo x s (f_dep cenv' cenvl' blks) /\ PS.In y s) ->
      exists s, Env.MapsTo x s (collect_depends_scope f_dep cenv' cenvl' (Scope locs blks)) /\ PS.In y s.
  Proof.
    Transparent collect_depends_scope.
    intros * Hnd1 Henv Henvl Hnd4 Hvars Hndvars Hvarsenv Hndl Hwl Hwx Hdep Hind;
      simpl; inv Hvars; inv Hndl; inv Hwl; inv Hwx; inv Hdep.

    - (* sub-blocks *)
      simpl_Exists. inv_VarsDefined. take (P_dep _ _ _ _) and rename it into Hdep.
      eapply Hind with (xs:=xs ++ map fst locs) in Hdep as (?&Hfind&Hpsin); eauto.
      + unfold Env.MapsTo. rewrite Env.union_fuse_spec, Hfind.
        destruct (Env.find x (Env.from_list _)).
        1,2:repeat esplit; try reflexivity. 2:eauto.
        eapply PSF.union_iff. left; eauto.
      + apply NoDupMembers_app; auto.
        * apply nodupmembers_map; auto. intros; destruct_conjs; auto.
        * intros * Hin1 Hin2. rewrite InMembers_senv_of_locs in Hin2.
          eapply H5; eauto using In_InMembers. now rewrite <-fst_InMembers.
      + eapply equiv_env_local; eauto.
      + eapply equiv_env_last_local; eauto.
      + rewrite 2 Env.elements_union, 2 Env.elements_from_list.
        * clear - Hnd4. rewrite app_assoc.
          eapply Permutation_NoDup in Hnd4; eauto. simpl_app.
          repeat rewrite map_map; simpl. apply Permutation_app_head. symmetry.
          rewrite Permutation_swap. apply Permutation_app_head.
          unfold idcaus_of_senv. erewrite map_app, 2 map_map, map_ext, map_filter_map, map_filter_ext, <-app_assoc. reflexivity.
          1,2:intros; destruct_conjs; auto. destruct o as [(?&?)|]; simpl; auto.
        * apply nodupmembers_map_filter; auto.
          intros; destruct_conjs. destruct o as [(?&?)|]; simpl; auto.
        * apply nodupmembers_map; auto. intros; destruct_conjs; auto.
        * intros * Hin1 Hin2. rewrite Env.In_from_list in Hin2. inv Hin1. apply Henvl in H; inv H.
          rewrite fst_InMembers in Hin2. simpl_In.
          eapply H5; eauto using In_InMembers. solve_In.
        * intros * Hin1 Hin2. rewrite Env.In_from_list in Hin2. inv Hin1. apply Henv in H; inv H.
          rewrite fst_InMembers in Hin2. simpl_In.
          eapply H5; eauto using In_InMembers. solve_In.
      + apply NoDup_app'; auto.
        * now eapply fst_NoDupMembers.
        * eapply Forall_forall; intros ? Hin1 Hin2. simpl_Forall.
          inv Hvarsenv. eapply Henv in H. inv H.
          eapply H5. apply fst_InMembers; eauto. solve_In.
      + eapply Forall_forall; intros.
        rewrite Env.union_In.
        apply in_app_or in H as [Hin'|Hin']; [|right]; eauto.
        * simpl_Forall; auto.
        * apply Env.In_from_list, fst_InMembers. erewrite map_map, map_ext; eauto. intros; destruct_conjs; auto.
      + rewrite map_app, map_fst_senv_of_locs; auto.

    - (* last *)
      simpl_Exists. destruct o as [(?&?)|]. 2:take False and inv it.
      destruct_conjs; subst.
      eapply collect_free_left_spec in H0.
      + remember (map_filter (fun '(_, (_, _, _, o)) => option_map (fun '(_, cx) => (cx, _)) _) _) as l.
        assert (exists s, Env.find x (Env.from_list l) = Some s /\ PS.In y s) as (?&Hfind&Hps).
        { repeat esplit; eauto. subst.
          apply Env.find_In_from_list.
          2:{ clear - Hnd4. simpl_app. unfold idcaus_of_senv in Hnd4. simpl_app.
              apply NoDup_app_r, NoDup_app_r, NoDup_app_r, NoDup_app_l in Hnd4.
              rewrite fst_NoDupMembers. rewrite map_map_filter, map_filter_map in Hnd4.
              erewrite map_map_filter, map_filter_ext; eauto.
              intros; destruct_conjs. destruct o as [(?&?)|]; simpl in *; auto.
          }
          eapply map_filter_In. eauto. simpl. reflexivity.
        }
        unfold Env.MapsTo. rewrite Env.union_fuse_spec, Hfind.
        destruct (Env.find _ (f_dep _ _ _)); subst; eauto.
        repeat esplit; eauto.
        rewrite PSF.union_iff; auto.
      + eapply equiv_env_local; eauto.
      + eapply equiv_env_last_local; eauto.
      + simpl_Forall; eauto.
      + simpl_Forall; eauto.
  Qed.

  Lemma collect_depends_on_spec {PSyn prefs} : forall (G: @global PSyn prefs) x y blk xs Γ cenv' cenvl',
      NoDupMembers Γ ->
      (forall x cx, Env.find x cenv' = Some cx <-> HasCaus Γ x cx) ->
      (forall x cx, Env.find x cenvl' = Some cx <-> HasLastCaus Γ x cx) ->
      NoDup (map snd (Env.elements cenv' ++ Env.elements cenvl' ++ idcaus_of_locals blk)) ->
      VarsDefined blk xs ->
      NoDup xs ->
      Forall (fun x => Env.In x cenv') xs ->
      NoDupLocals (map fst Γ) blk ->
      wl_block G blk ->
      wx_block Γ blk ->
      depends_on Γ x y blk ->
      exists s, Env.MapsTo x s (collect_depends_on cenv' cenvl' blk) /\ PS.In y s.
  Proof.
    Opaque collect_depends_scope.
    induction blk using block_ind2; intros * Hnd1 Henv Henvl Hnd4 Hvars Hndvars Hvarsenv Hndl Hwl Hwx Hdep;
      simpl; inv Hvars; inv Hndl; inv Hwl; inv Hwx; inv Hdep.

    - (* equation *)
      inv H0. inv H2.
      eapply collect_free_left_list_spec in H4; eauto.
      repeat esplit; eauto.
      erewrite <-collect_free_left_list_length in H5; eauto.
      apply Env.find_In_from_list.
      2:{ rewrite fst_NoDupMembers, combine_map_fst'; eauto.
          2:rewrite map_length; eauto.
          eapply collect_free_var_nodup; eauto.
          solve_NoDup_app.
      }
      erewrite In_combine_nth_error.
      repeat esplit; eauto.
      + erewrite map_nth_error; eauto.
        erewrite collect_free_var_complete; eauto with senv.
      + eapply nth_error_nth'.
        erewrite <-H5. eapply nth_error_Some; intro; congruence.

    - (* reset block (sub-blocks) *)
      simpl_Exists. simpl_Forall. inv_VarsDefined.
      eapply H with (cenv':=cenv') (cenvl':=cenvl') in Hdef as (?&?&?); eauto.
      2:{ rewrite app_assoc in *. eapply NoDup_locals_inv; eauto. }
      2:eapply NoDup_concat; eauto.
      2:{ eapply Forall_incl; eauto.
          eapply incl_concat; eauto. }
      eapply unions_fuse_Subset in H0 as (?&Hfind&Hsub). 2:eapply in_map_iff; eauto.
      repeat esplit.
      + unfold Env.MapsTo. now rewrite Env.Props.P.F.map_o, Hfind.
      + eapply PSF.union_iff; eauto.
    - (* reset block (reset expr) *)
      clear H.
      eapply collect_depends_on_dom, Env.map_2, unions_fuse_PS_In, Exists_exists in H7 as (?&Hin1&(?&Hfind2)); eauto.
      2,4,5,6:econstructor; eauto.
      2:{ intros ? Hin. eapply Forall_forall in Hvarsenv; eauto.
          inv Hvarsenv. eapply Henv in H0. inv H0. solve_In. }
      eapply unions_fuse_Subset in Hfind2 as (?&Hfind&Hsub); eauto.
      repeat esplit.
      + unfold Env.MapsTo. now erewrite Env.Props.P.F.map_o, Hfind.
      + eapply collect_free_left_spec in H10; eauto.
        eapply PSF.union_iff; eauto.

    - (* switch (sub-blocks) *)
      setoid_rewrite Env.Props.P.F.map_mapsto_iff.
      simpl_Exists. destruct s. simpl_Forall.
      eapply collect_depends_scope_spec in H1 as (?&Hfind&Hpsin); eauto.
      + eapply unions_fuse_Subset in Hfind as (?&Hfind&Hsub).
        unfold Env.MapsTo. rewrite Hfind; simpl. 2:solve_In.
        do 2 esplit; eauto.
        now apply PSF.union_3, Hsub.
      + rewrite app_assoc, map_app in *.
        eapply nodup_app_map_flat_map; eauto. eapply in_map_iff with (f:=snd); do 2 esplit; eauto. auto.
        erewrite flat_map_concat_map, map_map with (l:=branches), map_ext with (l:=branches), <-flat_map_concat_map; eauto.
        intros; destruct_conjs; auto.
      + intros; simpl in *. simpl_Exists. inv_VarsDefined. simpl_Forall.
        eapply H with (xs:=xs1) in H17 as (?&Hinc&Hpsin); eauto.
        * eapply unions_fuse_Subset in Hinc as (?&Hfind&Hsub). 2:eapply in_map_iff; eauto.
          unfold Env.MapsTo.
          repeat esplit; try reflexivity. eauto.
          now apply Hsub.
        * rewrite app_assoc in *. eapply NoDup_locals_inv; eauto.
        * eapply NoDup_concat; eauto. now take (Permutation _ _) and rewrite it.
        * take (Permutation _ _) and rewrite <-it in H16. apply Forall_concat in H16.
          simpl_Forall; auto.
    - (* switch (condition) *)
      clear H.
      eapply collect_depends_on_dom, Env.map_2, unions_fuse_PS_In, Exists_exists in H9 as (?&Hin1&(?&Hfind2)); eauto.
      2,4,5,6:econstructor; eauto.
      2:{ intros ? Hin. eapply Forall_forall in Hvarsenv; eauto.
          inv Hvarsenv. eapply Henv in H0. inv H0. solve_In. }
      eapply unions_fuse_Subset in Hfind2 as (?&Hfind&Hsub); eauto.
      repeat esplit.
      + unfold Env.MapsTo. now erewrite Env.Props.P.F.map_o, Hfind.
      + eapply collect_free_left_spec in H10; eauto.
        eapply PSF.union_iff; eauto.

    - (* automaton (sub-blocks) *)
      simpl_Exists. destruct s as [?(?&?)]. simpl_Forall.
      eapply collect_depends_scope_spec in H1 as (?&Hfind&Hpsin); eauto.
      + eapply unions_fuse_Subset in Hfind as (?&Hfind&Hsub).
        unfold Env.MapsTo. rewrite Env.Props.P.F.map_o, Hfind; simpl. 2:solve_In.
        do 2 esplit; eauto.
        now apply PSF.union_3, Hsub.
      + rewrite app_assoc, map_app in *.
        eapply nodup_app_map_flat_map; eauto. eapply in_map_iff with (f:=snd); do 2 esplit; eauto. auto.
        erewrite flat_map_concat_map, map_map with (l:=states), map_ext with (l:=states), <-flat_map_concat_map; eauto.
        intros; destruct_conjs; auto.
      + intros; simpl in *. simpl_Exists. inv_VarsDefined. simpl_Forall.
        eapply H with (xs:=xs1) in H21 as (?&Hinc&Hpsin); eauto.
        * eapply unions_fuse_Subset in Hinc as (?&Hfind&Hsub). 2:eapply in_map_iff; eauto.
          unfold Env.MapsTo.
          repeat esplit; try reflexivity. eauto.
          now apply Hsub.
        * rewrite app_assoc in *. eapply NoDup_locals_inv; eauto.
        * eapply NoDup_concat; eauto. now take (Permutation _ _) and rewrite it.
        * take (Permutation _ _) and rewrite <-it in H17. apply Forall_concat in H17.
          simpl_Forall; auto.
    - (* automaton (clock) *)
      clear H.
      eapply collect_depends_on_dom, Env.map_2, unions_fuse_PS_In, Exists_exists in H9 as (?&Hin1&(?&Hfind2)); eauto.
      2,4,5,6:econstructor; eauto.
      2:{ intros ? Hin. eapply Forall_forall in Hvarsenv; eauto.
          inv Hvarsenv. eapply Henv in H0. inv H0. solve_In. }
      eapply unions_fuse_Subset in Hfind2 as (?&Hfind&Hsub); eauto.
      repeat esplit.
      + unfold Env.MapsTo. now erewrite Env.Props.P.F.map_o, Hfind.
      + eapply collect_free_clock_spec in H15; eauto.
        repeat esplit; eauto. rewrite 2 PSF.union_iff; eauto.
    - (* automaton (initial state) *)
      clear H.
      eapply collect_depends_on_dom, Env.map_2, unions_fuse_PS_In, Exists_exists in H3 as (?&Hin1&(?&Hfind2)); eauto.
      2,4,5,6:econstructor; eauto.
      2:{ intros ? Hin. eapply Forall_forall in Hvarsenv; eauto.
          inv Hvarsenv. eapply Henv in H0. inv H0. solve_In. }
      eapply unions_fuse_Subset in Hfind2 as (?&Hfind&Hsub); eauto.
      repeat esplit.
      + unfold Env.MapsTo. now erewrite Env.Props.P.F.map_o, Hfind.
      + simpl_Exists; simpl_Forall.
        eapply collect_free_left_spec in H15; eauto.
        repeat esplit; eauto. rewrite 2 PSF.union_iff; left; left; eauto.
        eapply In_In_PSUnion; eauto. solve_In.

    - (* local block *)
      eapply collect_depends_scope_spec; eauto.
      intros; simpl in *. simpl_Exists. inv_VarsDefined. simpl_Forall.
      take (depends_on _ _ _ _) and rename it into Hdep.
      eapply H with (xs:=xs1) in Hdep as (?&Hinc&Hpsin); eauto.
      + eapply unions_fuse_Subset in Hinc as (?&Hfind&Hsub). 2:eapply in_map_iff; eauto.
        unfold Env.MapsTo.
        repeat esplit; try reflexivity. eauto.
        now apply Hsub.
      + rewrite app_assoc in *. eapply NoDup_locals_inv; eauto.
      + eapply NoDup_concat; eauto. now take (Permutation _ _) and rewrite it.
      + take (Permutation _ _) and rewrite <-it in H11. apply Forall_concat in H11.
        simpl_Forall; auto.
  Qed.

  Local Hint Constructors Is_defined_in : lcaus.

  Fact Is_free_in_clock_In Γ : forall x ck,
      wx_clock Γ ck ->
      Is_free_in_clock x ck ->
      IsVar Γ x.
  Proof.
    induction ck; intros * Hwx Hf; inv Hwx; inv Hf; auto.
  Qed.

  Lemma Is_free_left_In Γ Γ' : forall e k x cx,
      NoDup (map snd (idcaus_of_senv Γ)) ->
      HasCaus Γ x cx \/ HasLastCaus Γ x cx ->
      wx_exp Γ' e ->
      Is_free_left Γ cx k e ->
      IsVar Γ' x.
  Proof with simpl_Exists; simpl_Forall; eauto.
    induction e using exp_ind2; intros * Hnd Hin Hwx Hfree; inv Hwx; inv Hfree; eauto.
    - destruct Hin; [|exfalso; eauto using NoDup_HasCaus_HasLastCaus].
      eapply HasCaus_snd_det in H; eauto; subst; auto.
    - destruct Hin; [exfalso; eauto using NoDup_HasCaus_HasLastCaus|].
      eapply HasLastCaus_snd_det in H; eauto; subst; auto with senv.
    - destruct H2; eauto.
    - eapply Is_free_left_list_Exists in H4 as (?&Hfree)...
    - destruct H4 as [H4|H4].
      + eapply Is_free_left_list_Exists in H4 as (?&Hfree)...
      + eapply Is_free_left_list_Exists in H4 as (?&Hfree)...
    - destruct H3 as [(_&?)|H4].
      + destruct Hin; [|exfalso; eauto using NoDup_HasCaus_HasLastCaus].
        eapply HasCaus_snd_det in H1; eauto; subst; auto.
      + eapply Is_free_left_list_Exists in H4 as (?&Hfree)...
    - destruct H3 as [(_&?)|Hfree].
      + destruct Hin; [|exfalso; eauto using NoDup_HasCaus_HasLastCaus].
        eapply HasCaus_snd_det in H1; eauto; subst; auto.
      + simpl_Exists. eapply Is_free_left_list_Exists in Hfree as (?&Hfree)...
    - destruct H3 as [(_&?)|[Hfree|Hfree]]; eauto.
      + simpl_Exists. eapply Is_free_left_list_Exists in Hfree as (?&Hfree)...
      + destruct Hfree as (?&?&Hfree); subst.
        eapply Is_free_left_list_Exists in Hfree as (?&Hfree); eapply Exists_exists in Hfree as (?&?&Hfree).
        specialize (H7 _ eq_refl). simpl in *.
        simpl_Forall; eauto.
    - destruct H9 as [(?&Hfree)|Hfree]...
  Qed.

  Lemma depends_scope_In {A} f_idcaus P_nd P_wx P_dep : forall locs (blks: A) Γ Γ' cy x cx,
      NoDup (map snd (idcaus_of_senv Γ ++ idcaus_of_scope f_idcaus (Scope locs blks))) ->
      HasCaus Γ x cx \/ HasLastCaus Γ x cx ->
      NoDupScope P_nd (map fst Γ) (Scope locs blks) ->
      wx_scope P_wx Γ' (Scope locs blks) ->
      depends_on_scope P_dep Γ cy cx (Scope locs blks) ->
      (forall Γ Γ',
          NoDup (map snd (idcaus_of_senv Γ ++ f_idcaus blks)) ->
          HasCaus Γ x cx \/ HasLastCaus Γ x cx ->
          P_nd (map fst Γ) blks ->
          P_wx Γ' blks ->
          P_dep Γ cy cx blks ->
          IsVar Γ' x) ->
      IsVar Γ' x.
  Proof.
    intros * Hnd Hin Hnd2 Hwx Hdep Hind; inv Hwx; inv Hdep; inv Hnd2; simpl in *.
    - (* sub-blocks *)
      eapply Hind with (Γ':=Γ' ++ _) in H2; eauto.
      + apply IsVar_app in H2 as [|]; auto. exfalso.
        inv H. rewrite InMembers_senv_of_locs in H0.
        eapply H7; eauto.
        destruct Hin as [Hin|Hin]; inv Hin; solve_In.
      + now rewrite idcaus_of_senv_app, <-app_assoc.
      + rewrite HasCaus_app, HasLastCaus_app.
        destruct Hin; auto.
      + rewrite map_app, map_fst_senv_of_locs; auto.

    - (* last *)
      simpl_Exists; simpl_Forall. destruct o; destruct_conjs; simpl in *; try (take False and inv it); subst.
      eapply Is_free_left_In in H0 as Hin'. 4:eauto.
      + eapply IsVar_app in Hin' as [|]; eauto. exfalso.
        inv H. rewrite InMembers_senv_of_locs in H2.
        eapply H7; eauto.
        destruct Hin as [Hin|Hin]; inv Hin; solve_In.
      + clear - Hnd.
        rewrite app_assoc, map_app in Hnd. apply NoDup_app_l in Hnd.
        rewrite idcaus_of_senv_app; auto.
      + rewrite HasCaus_app, HasLastCaus_app. destruct Hin; auto.
  Qed.

  Lemma depends_on_In : forall blk Γ Γ' cy x cx,
      NoDup (map snd (idcaus_of_senv Γ ++ idcaus_of_locals blk)) ->
      HasCaus Γ x cx \/ HasLastCaus Γ x cx ->
      NoDupLocals (map fst Γ) blk ->
      wx_block Γ' blk ->
      depends_on Γ cy cx blk ->
      IsVar Γ' x.
  Proof.
    induction blk using block_ind2; intros * Hnd Hin Hnd2 Hwx Hdep; inv Hwx; inv Hdep; inv Hnd2; simpl in *.
    - (* equation *)
      rewrite app_nil_r in Hnd.
      eapply Is_free_left_list_Exists in H3 as (?&Hfree). simpl_Exists. simpl_Forall.
      eapply Is_free_left_In in Hfree; eauto.

    - (* reset *)
      simpl_Exists; simpl_Forall.
      eapply H; eauto.
      + eapply NoDup_locals_inv; eauto.
    - rewrite map_app in Hnd.
      eapply Is_free_left_In in H5; eauto using NoDup_app_l.

    - (* switch *)
      rename H1 into Hdef. simpl_Exists. simpl_Forall.
      destruct s. eapply depends_scope_In; eauto.
      + rewrite map_app in *.
        eapply nodup_app_map_flat_map; eauto. eapply in_map_iff with (f:=snd); do 2 esplit; eauto. auto.
        erewrite flat_map_concat_map, map_map with (l:=branches), map_ext with (l:=branches), <-flat_map_concat_map; eauto.
        intros; destruct_conjs; auto.
      + intros; simpl in *. simpl_Exists. simpl_Forall.
        eapply H; eauto.
        rewrite map_app in *. eapply nodup_app_map_flat_map; eauto.
    - rewrite map_app in Hnd.
      eapply Is_free_left_In in H3; eauto using NoDup_app_l.

    - (* automaton *)
      simpl_Exists. simpl_Forall.
      destruct s as [?(?&?)]. eapply depends_scope_In; eauto.
      + rewrite map_app in *.
        eapply nodup_app_map_flat_map; eauto. eapply in_map_iff with (f:=snd); do 2 esplit; eauto. auto.
        erewrite flat_map_concat_map, map_map with (l:=states), map_ext with (l:=states), <-flat_map_concat_map; eauto.
        intros; destruct_conjs; auto.
      + intros; simpl in *. simpl_Exists. simpl_Forall.
        eapply H; eauto.
        rewrite map_app in *. eapply nodup_app_map_flat_map; eauto.
    - rewrite map_app in Hnd.
      simpl_Exists. simpl_Forall.
      eapply Is_free_in_clock_In in H9; eauto.
      assert (x = y); subst; auto.
      destruct Hin.
      + eapply HasCaus_snd_det; eauto using NoDup_app_l.
      + exfalso. eapply NoDup_HasCaus_HasLastCaus; eauto using NoDup_app_l.
    - rewrite map_app in Hnd.
      simpl_Exists. simpl_Forall.
      eapply Is_free_left_In in H9; eauto using NoDup_app_l.

    - (* local *)
      eapply depends_scope_In; eauto.
      intros; simpl in *. simpl_Exists. simpl_Forall.
      eapply H; eauto.
      rewrite map_app in *. eapply nodup_app_map_flat_map; eauto.
  Qed.

  Lemma In_Is_defined_in : forall x cx blk xs Γ,
      VarsDefined blk xs ->
      In x xs ->
      HasCaus Γ x cx ->
      incl xs (map fst Γ) ->
      Is_defined_in Γ cx blk.
  Proof.
    induction blk using block_ind2; intros * Hvars Hin Henv Hincl2; simpl in *; inv Hvars.
    - (* equation *)
      destruct eq. econstructor; eauto.
    - (* reset *)
      constructor. apply in_concat in Hin as (?&?&?). inv_VarsDefined.
      solve_Exists. simpl_Forall.
      eapply H; eauto. etransitivity; [|eauto]. apply incl_concat; auto.
    - (* switch *)
      constructor.
      inv H4; simpl in *; try congruence. inv H. clear H1 H6. left.
      inv H0; destruct_conjs; subst.
      assert (In x (concat x1)) as Hin'.
      { take (Permutation (concat _) _) and rewrite it; auto using in_or_app. }
      constructor.
      apply in_concat in Hin' as (?&?&?). inv_VarsDefined.
      solve_Exists. simpl_Forall.
      eapply H5; eauto.
      + apply HasCaus_app; auto.
      + etransitivity; [eapply incl_concat; eauto|].
        rewrite H1. erewrite map_app, map_fst_senv_of_locs.
        apply incl_appl'; auto.
    - (* automaton *)
      constructor.
      inv H5; simpl in *; try congruence. inv H. clear H1 H6. left.
      inv H0; destruct_conjs; subst.
      assert (In x (concat x1)) as Hin'.
      { take (Permutation (concat _) _) and rewrite it; auto using in_or_app. }
      constructor.
      apply in_concat in Hin' as (?&?&?). inv_VarsDefined.
      solve_Exists. simpl_Forall.
      eapply H5; eauto.
      + apply HasCaus_app; auto.
      + etransitivity; [eapply incl_concat; eauto|].
        rewrite H1. erewrite map_app, map_fst_senv_of_locs.
        apply incl_appl'; auto.
    - (* locals *)
      inv H1; destruct_conjs.
      assert (In x (concat x0)) as Hin'.
      { take (Permutation _ _) and rewrite it; auto using in_or_app. }
      apply in_concat in Hin' as (?&?&?). inv_VarsDefined.
      do 2 constructor. solve_Exists. simpl_Forall.
      eapply H; eauto.
      + apply HasCaus_app; auto.
      + etransitivity; [eapply incl_concat; eauto|].
        rewrite H1. erewrite map_app, map_fst_senv_of_locs.
        apply incl_appl'; auto.
  Qed.

  Lemma Is_defined_in_restrict : forall x blk xs cenv cenv',
      NoDupLocals (map fst cenv) blk ->
      VarsDefined blk xs ->
      (forall x, In x xs -> ~InMembers x cenv) ->
      Is_defined_in (cenv ++ cenv') x blk ->
      Is_defined_in cenv' x blk.
  Proof.
    induction blk using block_ind2; intros * Hndloc Hvars Hnin Hdef; inv Hndloc; inv Hvars; inv Hdef.
    - (* equation *)
      econstructor; eauto.
      eapply HasCaus_app in H1 as [Hin|Hin]; auto.
      exfalso. inv Hin.
      eapply Hnin, In_InMembers; eauto.
    - (* reset *)
      constructor. solve_Exists. inv_VarsDefined. simpl_Forall.
      eapply H with (xs:=xs); eauto.
      intros ??. eapply Hnin. eapply in_concat' in H0; eauto.
    - (* switch *)
      constructor. solve_Exists. simpl_Forall.
      inv H1. inv H5. inv H2. constructor. solve_Exists. inv_VarsDefined. simpl_Forall.
      eapply H; eauto.
      3:rewrite app_assoc; eauto.
      + eapply NoDupLocals_incl; [|eauto]. solve_incl_app.
      + intros ? Hin'. eapply in_concat' in Hin'; eauto.
        rewrite H2 in Hin'. apply in_app_or in Hin' as [?|?]; eauto.
        rewrite fst_InMembers. rewrite <-fst_InMembers in H1. eauto.
    - (* automaton *)
      constructor. solve_Exists. simpl_Forall.
      inv H1. inv H6. inv H2. constructor. solve_Exists. inv_VarsDefined. simpl_Forall.
      eapply H; eauto.
      3:rewrite app_assoc; eauto.
      + eapply NoDupLocals_incl; [|eauto]. solve_incl_app.
      + intros ? Hin'. eapply in_concat' in Hin'; eauto.
        rewrite H2 in Hin'. apply in_app_or in Hin' as [?|?]; eauto.
        rewrite fst_InMembers. rewrite <-fst_InMembers in H1. eauto.
    - (* locals *)
      inv H2. inv H1. inv H3.
      do 2 constructor. solve_Exists. inv_VarsDefined. simpl_Forall.
      eapply H with (xs:=xs0); eauto.
      3:rewrite app_assoc; eauto.
      + eapply NoDupLocals_incl; [|eauto]. solve_incl_app.
      + intros ? Hin'. eapply in_concat' in Hin'; eauto.
        rewrite H2 in Hin'. apply in_app_or in Hin' as [?|?]; eauto.
        rewrite fst_InMembers. rewrite <-fst_InMembers in H0. eauto.
  Qed.

  Global Hint Constructors Is_defined_in Is_defined_in_scope Is_last_in Is_last_in_scope : lcaus.
  Global Hint Constructors depends_on : lcaus.

  Lemma depends_scope_def_last {A} P_dep P_def P_last cy cx : forall locs (blk: A) Γ,
      depends_on_scope P_dep Γ cy cx (Scope locs blk) ->
      (forall Γ, P_dep Γ cy cx blk -> P_def Γ blk \/ P_last blk) ->
      Is_defined_in_scope P_def Γ (Scope locs blk)
      \/ Is_last_in_scope P_last cy (Scope locs blk).
  Proof.
    intros * Hdep Hind; inv Hdep.
    - edestruct Hind; eauto with lcaus.
    - simpl_Exists. destruct o as [(?&?)|]; inv H2; eauto with lcaus.
  Qed.

  Lemma depends_on_def_last cy cx : forall blk Γ,
      depends_on Γ cy cx blk ->
      Is_defined_in Γ cy blk \/ Is_last_in cy blk.
  Proof.
    induction blk using block_ind2; intros * Hdep; inv Hdep; auto.
    - (* equation *)
      left. econstructor; eauto using nth_error_In.
    - (* reset *)
      simpl_Exists; simpl_Forall.
      edestruct H; eauto; [left|right]; econstructor; solve_Exists.
    - (* switch *)
      simpl_Exists. destruct s.
      eapply depends_scope_def_last in H1 as [|].
      + left. econstructor. solve_Exists.
      + right. econstructor. solve_Exists.
      + intros * Hex; simpl_Exists. simpl_Forall.
        edestruct H; eauto; [left|right]; solve_Exists.
    - (* automaton *)
      simpl_Exists. destruct s as [?(?&?)].
      eapply depends_scope_def_last in H1 as [|].
      + left. econstructor. solve_Exists.
      + right. econstructor. solve_Exists.
      + intros * Hex; simpl_Exists. simpl_Forall.
        edestruct H; eauto; [left|right]; solve_Exists.
    - (* local *)
      eapply depends_scope_def_last in H1 as [|].
      + left. econstructor. solve_Exists.
      + right. econstructor. solve_Exists.
      + intros * Hex; simpl_Exists. simpl_Forall.
        edestruct H; eauto; [left|right]; solve_Exists.
  Qed.

  Lemma idcaus_of_scope_def_last {A} P_vd P_nd f_idcaus P_def P_last :
    forall cy locs (blks: A) xs Γ,
      VarsDefinedScope P_vd (Scope locs blks) xs ->
      NoDupScope P_nd xs (Scope locs blks) ->
      In cy (map snd (idcaus_of_scope f_idcaus (Scope locs blks))) ->
      (forall xs Γ,
          P_vd blks xs ->
          P_nd xs blks ->
          In cy (map snd (f_idcaus blks)) ->
          P_def Γ blks \/ P_last blks) ->
      (forall xs Γ y,
          P_vd blks xs ->
          P_nd xs blks ->
          In y xs ->
          HasCaus Γ y cy ->
          P_def Γ blks) ->
      Is_defined_in_scope P_def Γ (Scope locs blks) \/ Is_last_in_scope P_last cy (Scope locs blks).
  Proof.
    intros * Hvd Hnd Hin Hind Hdef; inv Hvd; inv Hnd; simpl in *.
    unfold idcaus_of_senv in Hin. repeat rewrite map_app, in_app_iff in Hin.
    destruct Hin as [[Hin|Hin]|Hin]; simpl_In; eauto.
    - left. constructor. eapply Hdef; eauto.
      + apply in_or_app, or_intror. solve_In.
      + apply HasCaus_app, or_intror. econstructor; solve_In. auto.
    - right. eapply LastScope2; eauto.
    - edestruct Hind; eauto with lcaus. solve_In.
  Qed.

  Lemma idcaus_of_locals_def_last : forall cy blk xs Γ,
      VarsDefined blk xs ->
      NoDupLocals xs blk ->
      In cy (map snd (idcaus_of_locals blk)) ->
      Is_defined_in Γ cy blk \/ Is_last_in cy blk.
  Proof.
    Opaque idcaus_of_scope.
    induction blk using block_ind2; intros * Hvd Hnd Hin; inv Hvd; inv Hnd; simpl_In.
    - (* equation *)
      inv Hin0.
    - (* reset *)
      inv_VarsDefined. simpl_Forall.
      edestruct H as [|]; solve_In; eauto using NoDupLocals_incl, incl_concat;
        [left|right]; constructor; solve_Exists.
    - (* switch *)
      inv_VarsDefined. simpl_Forall.
      destruct s. eapply idcaus_of_scope_def_last with (P_last:=Exists _) in H4 as [|]; eauto.
      + left; econstructor. solve_Exists.
      + right; econstructor. solve_Exists.
      + solve_In; eauto.
      + intros; simpl in *. destruct_conjs. simpl_In.
        inv_VarsDefined; simpl_Forall.
        edestruct H; eauto. 3:left; solve_Exists. 3:right; solve_Exists.
        * eapply NoDupLocals_incl; [|eauto]. rewrite <-H6; eauto using incl_concat.
        * solve_In.
      + intros; destruct_conjs. rewrite <-H7 in H5; apply in_concat in H5 as (?&?&?).
        inv_VarsDefined. solve_Exists. simpl_Forall.
        eapply Is_defined_in_Is_defined_in, VarsDefined_Is_defined; eauto.
        eapply NoDupLocals_incl; eauto. rewrite <-H7; eauto using incl_concat.
    - (* automaton *)
      inv_VarsDefined. simpl_Forall.
      destruct s as [?(?&?)]. eapply idcaus_of_scope_def_last in H5 as [|]; eauto.
      + left; econstructor. solve_Exists.
      + right; econstructor. solve_Exists.
      + solve_In; eauto.
      + intros; simpl in *. destruct_conjs. simpl_In.
        inv_VarsDefined; simpl_Forall.
        edestruct H; eauto. 3:left; solve_Exists. 3:right; solve_Exists.
        * eapply NoDupLocals_incl; [|eauto]. rewrite <-H6; eauto using incl_concat.
        * solve_In.
      + intros; destruct_conjs. rewrite <-H7 in H3; apply in_concat in H3 as (?&?&?).
        inv_VarsDefined. solve_Exists. simpl_Forall.
        eapply Is_defined_in_Is_defined_in, VarsDefined_Is_defined; eauto.
        eapply NoDupLocals_incl; eauto. rewrite <-H7; eauto using incl_concat.
    - (* local *)
      eapply idcaus_of_scope_def_last in H1 as [|]; eauto with lcaus.
      + solve_In; eauto.
      + intros; simpl in *. destruct_conjs. simpl_In.
        inv_VarsDefined; simpl_Forall.
        edestruct H; eauto. 3:left; solve_Exists. 3:right; solve_Exists.
        * eapply NoDupLocals_incl; [|eauto]. rewrite <-H5; eauto using incl_concat.
        * solve_In.
      + intros; destruct_conjs. rewrite <-H6 in H4; apply in_concat in H4 as (?&?&?).
        inv_VarsDefined. solve_Exists. simpl_Forall.
        eapply Is_defined_in_Is_defined_in, VarsDefined_Is_defined; eauto.
        eapply NoDupLocals_incl; eauto. rewrite <-H6; eauto using incl_concat.
  Qed.

  Lemma idcaus_of_scope_def_last' {A} P_vd P_nd f_idcaus P_def P_last :
    forall cy locs (blks: A) xs Γ,
      VarsDefinedScope P_vd (Scope locs blks) xs ->
      NoDupScope P_nd xs (Scope locs blks) ->
      Is_defined_in_scope P_def Γ (Scope locs blks) \/ Is_last_in_scope P_last cy (Scope locs blks) ->
      (forall xs Γ,
          P_vd blks xs ->
          P_nd xs blks ->
          P_def Γ blks \/ P_last blks ->
          In cy (map snd (idcaus_of_senv Γ ++ f_idcaus blks))) ->
      In cy (map snd (idcaus_of_senv Γ ++ idcaus_of_scope f_idcaus (Scope locs blks))).
  Proof.
    Transparent idcaus_of_scope.
    intros * Hvd Hnd Hin Hind (* Hdef *); inv Hvd; inv Hnd; simpl in *.
    repeat rewrite map_app, in_app_iff.
    destruct Hin as [Hin|Hin]; inv Hin.
    - eapply Hind in H2; eauto. rewrite idcaus_of_senv_app, 2 map_app, 2 in_app_iff in H2.
      destruct H2 as [[|]|]; eauto.
    - eapply Hind with (Γ:=Γ) in H2; eauto. rewrite map_app, in_app_iff in H2.
      destruct H2 as [|]; eauto.
    - right; left. unfold idcaus_of_senv. rewrite map_app, in_app_iff; right. solve_In; auto.
  Qed.

  Lemma idcaus_of_locals_def_last' : forall cy blk xs Γ,
      VarsDefined blk xs ->
      NoDupLocals xs blk ->
      Is_defined_in Γ cy blk \/ Is_last_in cy blk ->
      In cy (map snd (idcaus_of_senv Γ ++ idcaus_of_locals blk)).
  Proof.
    induction blk using block_ind2; intros * Hvd Hnd Hdef; inv Hvd; inv Hnd; simpl.
    - (* equation *)
      destruct Hdef as [Hdef|Hdef]; inv Hdef.
      rewrite app_nil_r. inv H1.
      unfold idcaus_of_senv. simpl_app. apply in_or_app, or_introl. solve_In.
    - (* reset *)
      assert (Exists (fun blk => Is_defined_in Γ cy blk \/ Is_last_in cy blk) blocks) as Hex.
      { destruct Hdef as [Hdef|Hdef]; inv Hdef; solve_Exists. }
      simpl_Exists. inv_VarsDefined. simpl_Forall.
      eapply H in Hex; eauto using NoDupLocals_incl, incl_concat.
      simpl_app. eapply incl_appr'; [|eauto]. intros ??; solve_In.
    - (* switch *)
      assert (Exists (fun '(_, blks) => Is_defined_in_scope (fun Γ blks => Exists (Is_defined_in Γ cy) blks) Γ blks
                                     \/ Is_last_in_scope (fun blks => Exists (Is_last_in cy) blks) cy blks) branches) as Hex.
      { destruct Hdef as [Hdef|Hdef]; inv Hdef; solve_Exists. }
      simpl_Exists. inv_VarsDefined. simpl_Forall.
      destruct s. eapply idcaus_of_scope_def_last' in H4; eauto.
      + rewrite map_app, in_app_iff in *. destruct H4; auto. right. solve_In.
      + intros; simpl in *; destruct_conjs.
        assert (Exists (fun blk => Is_defined_in Γ0 cy blk \/ Is_last_in cy blk) l0) as Hdef'.
        { destruct H5; solve_Exists. }
        simpl_Exists. inv_VarsDefined. simpl_Forall.
        eapply H in Hdef'; eauto.
        * rewrite map_app, in_app_iff in *. destruct Hdef'; auto. right. solve_In.
        * eapply NoDupLocals_incl; [|eauto]. rewrite <-H6; eauto using incl_concat.
    - (* automaton *)
      assert (Exists (fun '(_, blks) => Is_defined_in_scope (fun Γ '(blks, _) => Exists (Is_defined_in Γ cy) blks) Γ blks
                                     \/ Is_last_in_scope (fun '(blks, _) => Exists (Is_last_in cy) blks) cy blks) states) as Hex.
      { destruct Hdef as [Hdef|Hdef]; inv Hdef; solve_Exists; [left|right].
        1,2:inv H1; eauto with lcaus; constructor; solve_Exists.
      }
      simpl_Exists. simpl_Forall.
      destruct s as [?(?&?)]. eapply idcaus_of_scope_def_last' in H5; eauto.
      + rewrite map_app, in_app_iff in *. destruct H5; auto. right. solve_In.
      + intros; simpl in *; destruct_conjs.
        assert (Exists (fun blk => Is_defined_in Γ0 cy blk \/ Is_last_in cy blk) l1) as Hdef'.
        { destruct H3; solve_Exists. }
        simpl_Exists. inv_VarsDefined. simpl_Forall.
        eapply H in Hdef'; eauto.
        * rewrite map_app, in_app_iff in *. destruct Hdef'; auto. right. solve_In.
        * eapply NoDupLocals_incl; [|eauto]. rewrite <-H6; eauto using incl_concat.
    - (* local *)
      eapply idcaus_of_scope_def_last'; eauto.
      + destruct Hdef as [Hdef|Hdef]; inv Hdef; eauto.
      + intros; simpl in *; destruct_conjs.
        assert (Exists (fun blk => Is_defined_in Γ0 cy blk \/ Is_last_in cy blk) blocks) as Hdef'.
        { destruct H4; solve_Exists. }
        simpl_Exists. inv_VarsDefined. simpl_Forall.
        eapply H in Hdef'; eauto.
        * rewrite map_app, in_app_iff in *. destruct Hdef'; auto. right. solve_In.
        * eapply NoDupLocals_incl; [|eauto]. rewrite <-H5; eauto using incl_concat.
  Qed.

  Lemma build_graph_dom {PSyn prefs} : forall (G: @global PSyn prefs) n,
      wl_node G n ->
      wx_node n ->
      Env.dom (build_graph n) (map snd (idcaus (n_in n ++ n_out n) ++ idcaus_of_locals (n_block n))).
  Proof.
    intros * Hwl Hwx. unfold idents, build_graph.
    eapply Env.dom_intro. intros x.
    rewrite Env.union_fuse_In, Env.In_from_list, fst_InMembers.
    rewrite or_comm. simpl_app.
    erewrite 2 map_map, map_ext, in_app_iff. apply or_iff_compat_l.
    2:intros (?&(?&?)&?); auto.
    pose proof (n_defd n) as (xs&Hdef&Hperm).
    pose proof (n_nodup n) as (Hnd&Hndl).
    erewrite collect_depends_on_dom with (xs:=xs); eauto.
    2:{ apply nodupmembers_map, n_nodup. intros; destruct_conjs; auto. }
    3,4:rewrite map_fst_senv_of_inout.
    3:rewrite Hperm; solve_incl_app. 3:apply node_NoDupLocals.
    2:{ intros *. erewrite <-map_app. split; intros Hin.
        - apply Env.from_list_find_In in Hin. simpl_In.
          econstructor. solve_In. reflexivity.
        - inv Hin. simpl_In.
          apply Env.find_In_from_list. solve_In.
          apply nodupmembers_map, n_nodup. intros; destruct_conjs; auto.
    }
    rewrite in_app_iff.
    split; [intros Hdl|intros [Hin|Hin]].
    - assert (Is_defined_in (senv_of_inout (n_out n)) x (n_block n) \/ Is_last_in x (n_block n)) as Hdl'.
      { destruct Hdl; auto. left.
        unfold senv_of_inout in *. rewrite map_app in H.
        eapply Is_defined_in_restrict in H; eauto.
        - eapply NoDupLocals_incl; [|eauto].
          erewrite map_map, map_ext, map_app. apply incl_appl, incl_refl.
          intros; destruct_conjs; auto.
        - intros ? Hin1 Hin2. eapply NoDupMembers_app_InMembers in Hnd; eauto.
          eapply Hnd. rewrite fst_InMembers, <-Hperm; eauto.
          rewrite fst_InMembers in Hin2. simpl_In; eauto using In_InMembers.
      }
      eapply idcaus_of_locals_def_last' in Hdl'; eauto.
      2:{ eapply NoDupLocals_incl; [|eauto]. rewrite Hperm. solve_incl_app. }
      rewrite map_app, in_app_iff in Hdl'. destruct Hdl'; auto. left.
      unfold idcaus_of_senv, senv_of_inout in H. simpl_app.
      apply in_app_iff in H as [|]; solve_In. congruence.
    - simpl_In.
      left. eapply Is_defined_in_Is_defined_in.
      econstructor. solve_In; eauto using in_or_app. 1,2:auto.
      eapply VarsDefined_Is_defined in Hdef; eauto.
      + eapply NoDupLocals_incl; [|eauto]. rewrite Hperm. solve_incl_app.
      + rewrite Hperm. solve_In.
    - eapply idcaus_of_locals_def_last; eauto.
      eapply NoDupLocals_incl; [|eauto]. rewrite Hperm. solve_incl_app.
  Qed.

  Lemma build_graph_find {PSyn prefs} : forall (G: @global PSyn prefs) n x y,
      wl_node G n ->
      wx_node n ->
      NoDup (map snd (idcaus (n_in n ++ n_out n) ++ idcaus_of_locals (n_block n))) ->
      depends_on (senv_of_inout (n_in n ++ n_out n)) x y (n_block n) ->
      exists ys, (Env.find x (build_graph n)) = Some ys /\ PS.In y ys.
  Proof.
    intros * Hwl Hwx Hndcaus Hdep.
    specialize (build_graph_dom G n Hwl) as Hdom.
    eapply Env.dom_use with (x:=x) in Hdom; eauto.
    rewrite Env.In_find in Hdom. symmetry in Hdom.
    assert (NoDupMembers (idcaus (n_in n ++ n_out n))) as Hnd.
    { pose proof (n_nodup n) as (Hnd&_).
      now rewrite NoDupMembers_idcaus.
    }
    pose proof (n_defd n) as (?&Hdef&Hperm).
    assert (forall x1 cx,
               Env.find x1 (Env.from_list (idcaus (n_in n ++ n_out n))) = Some cx
               <-> HasCaus (senv_of_inout (n_in n ++ n_out n)) x1 cx
           ) as Hequiv.
    { split; intros Hin.
      - apply Env.from_list_find_In in Hin. simpl_In.
        econstructor. solve_In; eauto. reflexivity.
      - inv Hin. apply Env.find_In_from_list; auto.
        solve_In. }
    eapply collect_depends_on_spec with
      (cenv':= Env.from_list (idcaus (n_in n ++ n_out n)))
      (cenvl':=Env.empty _)
      in Hdep as (?&Hx&Hy); eauto with datatypes.
    - assert (In x (map snd (idcaus (n_in n ++ n_out n) ++ idcaus_of_locals (n_block n)))) as Hin'.
      { rewrite Hdom. unfold build_graph.
        rewrite Env.union_fuse_spec, Hx.
        destruct (Env.find x (Env.from_list _)); eauto. }
      apply Hdom in Hin' as (?&Hfind). clear Hdom.
      eexists; split; eauto.
      unfold build_graph in Hfind.
      rewrite Env.union_fuse_spec, Hx in Hfind.
      destruct (Env.find _ _); inv Hfind; auto using PSF.union_2.
    - apply nodupmembers_map, n_nodup. intros; destruct_conjs; auto.
    - setoid_rewrite Env.gempty. split; intros; try congruence.
      inv H; simpl_In; auto.
    - rewrite Env.elements_from_list; auto.
    - rewrite Hperm. rewrite NoDupMembers_idcaus in Hnd.
      eapply fst_NoDupMembers, NoDupMembers_app_r; eauto.
    - rewrite Hperm. eapply Forall_forall; intros.
      rewrite Env.In_from_list, fst_InMembers, map_fst_idcaus, map_app.
      apply in_or_app; auto.
    - rewrite map_fst_senv_of_inout; apply node_NoDupLocals.
  Qed.

  (** We prove that the [check_node_causality] function only succeeds if
      the node is indeed causal.
      This is a simple consequence of [build_graph_find] and [build_acyclic_graph_spec].
   *)
  Lemma check_node_causality_correct {PSyn prefs} : forall (G: @global PSyn prefs) n,
      wl_node G n ->
      wx_node n ->
      check_node_causality n = OK tt ->
      node_causal n.
  Proof.
    intros * Hwl Hwx Hcheck.
    unfold check_node_causality in Hcheck.
    destruct (check_nodup _) eqn:NoDup; inv Hcheck.
    destruct (build_acyclic_graph _) eqn:Build; inv H0.
    eapply check_nodup_correct in NoDup.
    eapply build_acyclic_graph_spec in Build as (a&(Hv&Ha)&Graph).

    split; auto.
    exists t. exists a. exists Graph. split.
    - intros x. rewrite <- Hv.
      apply build_graph_dom in Hwl; auto.
      rewrite Env.Props.P.F.map_in_iff, (Hwl x), <- ps_from_list_ps_of_list, ps_from_list_In.
      reflexivity.
    - intros x y Hdep.
      apply Ha.
      eapply build_graph_find in Hwl as (ys & Find & In); eauto.
      exists (PSP.to_list ys).
      rewrite Env.Props.P.F.map_o, Find; split; auto.
      apply In_PS_elements; auto.
  Qed.

  Corollary check_causality_correct {PSyn prefs} : forall (G: @global PSyn prefs) tts,
      wl_global G ->
      wx_global G ->
      check_causality G = OK tts ->
      Forall node_causal (nodes G).
  Proof.
    unfold wl_global, wx_global, CommonTyping.wt_program, CommonProgram.units, check_causality; simpl.
    intros G.
    induction (nodes G); intros * Hwl Hwx Hcheck; auto.
    inv Hwl. inv Hwx.
    unfold check_causality in Hcheck; simpl in Hcheck.
    apply bind_inversion in Hcheck as [? [? Hcheck]].
    constructor.
    + destruct x. destruct H1. eapply check_node_causality_correct in H; eauto.
    + apply bind_inversion in Hcheck as [? [? Hcheck]]; eauto.
  Qed.

  (** ** Induction lemmas over a causal node *)

  Section exp_causal_ind.
    Context {PSyn : block -> Prop}.
    Context {prefs : PS.t}.
    Variable G : @global PSyn prefs.

    Variable Γ : static_env.

    Variable P_var : ident -> Prop.
    Variable P_exp : exp -> nat -> Prop.

    Inductive P_exps : list exp -> nat -> Prop :=
    | P_exps_now e es k :
        k < numstreams e ->
        P_exp e k ->
        P_exps (e::es) k
    | P_exps_later e es k :
        k >= numstreams e ->
        P_exps es (k-numstreams e) ->
        P_exps (e::es) k.

    Lemma Pexp_Pexps : forall es k,
        Forall (fun e => forall k, k < numstreams e
                           -> (forall x, Is_free_left Γ x k e -> P_var x)
                           -> P_exp e k) es ->
        (forall x, Is_free_left_list Γ x k es -> P_var x) ->
        k < length (annots es) ->
        P_exps es k.
    Proof.
      induction es; intros * Hf Hfree Hk; inv Hf; simpl in *. inv Hk.
      destruct (Nat.ltb k (numstreams a)) eqn:Hltb.
      - rewrite PeanoNat.Nat.ltb_lt in Hltb.
        constructor; eauto with lcaus.
      - eapply PeanoNat.Nat.ltb_ge in Hltb.
        eapply P_exps_later; eauto.
        eapply IHes; eauto with lcaus.
        rewrite app_length, length_annot_numstreams in Hk.
        lia.
    Qed.

    Hypothesis EconstCase : forall c,
        P_exp (Econst c) 0.

    Hypothesis EenumCase : forall k ty,
        P_exp (Eenum k ty) 0.

    Hypothesis EvarCase : forall x cx ann,
        HasCaus Γ x cx ->
        P_var cx ->
        P_exp (Evar x ann) 0.

    Hypothesis ElastCase : forall x cx ann,
        HasLastCaus Γ x cx ->
        P_var cx ->
        P_exp (Elast x ann) 0.

    Hypothesis EunopCase : forall op e1 ann,
        P_exp e1 0 ->
        P_exp (Eunop op e1 ann) 0.

    Hypothesis EbinopCase : forall op e1 e2 ann,
        P_exp e1 0 ->
        P_exp e2 0 ->
        P_exp (Ebinop op e1 e2 ann) 0.

    (* We're reasoning on causality, so we only get the hypothesis on the lhs *)
    Hypothesis EfbyCase : forall e0s es ann k,
        k < length ann ->
        P_exps e0s k ->
        P_exp (Efby e0s es ann) k.

    Hypothesis EarrowCase : forall e0s es ann k,
        k < length ann ->
        P_exps e0s k ->
        P_exps es k ->
        P_exp (Earrow e0s es ann) k.

    Hypothesis EwhenCase : forall es x cx b ann k,
        k < length (fst ann) ->
        P_exps es k ->
        HasCaus Γ x cx ->
        P_var cx ->
        P_exp (Ewhen es x b ann) k.

    Hypothesis EmergeCase : forall x cx tx es ann k,
        k < length (fst ann) ->
        HasCaus Γ x cx ->
        P_var cx ->
        Forall (fun es => P_exps (snd es) k) es ->
        P_exp (Emerge (x, tx) es ann) k.

    Hypothesis EcaseCase : forall e es d ann k,
        k < length (fst ann) ->
        P_exp e 0 ->
        Forall (fun es => P_exps (snd es) k) es ->
        LiftO True (fun d => P_exps d k) d ->
        P_exp (Ecase e es d ann) k.

    Hypothesis EappCase : forall f es er ann k,
        k < length ann ->
        (forall k, k < length (annots es) -> P_exps es k) ->
        (forall k, k < length (annots er) -> P_exps er k) ->
        P_exp (Eapp f es er ann) k.

    (* Exp-level induction *)
    Fixpoint exp_causal_ind e {struct e} : forall k,
        wl_exp G e ->
        wx_exp Γ e ->
        (forall x, Is_free_left Γ x k e -> P_var x) ->
        k < numstreams e ->
        P_exp e k.
    Proof with eauto with senv lcaus.
      Local Ltac solve_forall' es :=
        match goal with
        | Hwl: Forall (wl_exp _) es, Hwx: Forall (wx_exp _) es, Hind : forall e k, wl_exp _ e -> _ |- _ =>
          clear - Hind Hwl Hwx;
          induction es; inv Hwl; inv Hwx; constructor; auto
        end.

      intros * Hwl Hwx Hfree Hnum; destruct e; inv Hwl; inv Hwx; simpl in *.
      - (* const *)
        rewrite PeanoNat.Nat.lt_1_r in Hnum; subst.
        apply EconstCase.
      - (* enum *)
        rewrite PeanoNat.Nat.lt_1_r in Hnum; subst.
        apply EenumCase.
      - (* var *)
        rewrite PeanoNat.Nat.lt_1_r in Hnum; subst.
        inv H0. apply InMembers_In in H as (?&?).
        eapply EvarCase, Hfree...
      - (* last *)
        rewrite PeanoNat.Nat.lt_1_r in Hnum; subst.
        inv H0. destruct (causl_last e) eqn:Hfind; try congruence.
        eapply ElastCase, Hfree...
      - (* unop *)
        rewrite PeanoNat.Nat.lt_1_r in Hnum; subst.
        apply EunopCase.
        eapply exp_causal_ind... rewrite H4; auto.
      - (* binop *)
        rewrite PeanoNat.Nat.lt_1_r in Hnum; subst.
        apply EbinopCase.
        1,2:eapply exp_causal_ind... rewrite H6; auto. rewrite H7; auto.
      - (* fby *)
        eapply EfbyCase; eauto.
        + eapply Pexp_Pexps... 2:congruence.
          solve_forall' l.
      - (* arrow *)
        eapply EarrowCase; eauto.
        1,2:eapply Pexp_Pexps; auto with lcaus; try congruence.
        solve_forall' l. solve_forall' l0.
      - (* when *)
        inv H1. apply InMembers_In in H as (?&?).
        eapply EwhenCase... 2:eapply Hfree...
        eapply Pexp_Pexps... 2:congruence.
        solve_forall' l.
      - (* merge *)
        inv H1. apply InMembers_In in H as (?&?).
        eapply EmergeCase... eapply Hfree...
        assert (forall x, Exists (fun es => Is_free_left_list Γ x k (snd es)) l -> P_var x) as Hfree' by auto with lcaus.
        clear Hfree H3.
        induction l; inv H4; inv H5; inv H7; constructor; auto.
        eapply Pexp_Pexps; eauto. 2:congruence.
        clear - exp_causal_ind H2 H5.
        destruct a. induction l; inv H2; inv H5; constructor; auto.
      - (* case *)
        apply EcaseCase; eauto.
        + eapply exp_causal_ind... rewrite H4; auto.
        + assert (forall x, Exists (fun es => Is_free_left_list Γ x k (snd es)) l -> P_var x) as Hfree' by auto with lcaus.
          clear Hfree H5.
          induction l; inv H7; inv H8; inv H12; constructor; auto.
          eapply Pexp_Pexps; eauto. 2:congruence.
          clear - exp_causal_ind H1 H8.
          destruct a. induction l; inv H1; inv H8; constructor; auto.
        + destruct o; simpl in *; auto.
          specialize (H9 _ eq_refl). specialize (H10 _ eq_refl). specialize (H13 _ eq_refl).
          eapply Pexp_Pexps; eauto. 3:congruence. 2:intros; eapply Hfree; constructor; eauto.
          clear Hfree H10.
          induction l0; inv H9; inv H13; constructor; auto.
      - (* app *)
        apply EappCase; auto.
        + intros k' Hk'. eapply Pexp_Pexps; eauto.
          * solve_forall' l.
          * intros ? Hfree'. eapply Hfree.
            constructor; eauto.
            eapply Is_free_left_list_Exists in Hfree' as [? ?]; eauto.
        + intros k' Hk'. eapply Pexp_Pexps; eauto.
          * solve_forall' l0.
          * intros ? Hfree'. eapply Hfree.
            constructor; eauto.
            eapply Is_free_left_list_Exists in Hfree' as [? ?]; eauto.
            right. solve_Exists. simpl_Forall.
            rewrite <-length_annot_numstreams in H6.
            take (Is_free_left _ _ _ _) and rename it into Hfree1.
            assert (Hfree2:=Hfree1). eapply Is_free_left_length in Hfree1; eauto.
            rewrite H6 in Hfree1. destruct x0; auto. lia.
    Qed.

  End exp_causal_ind.

  (** More flexible induction principle *)
  Section node_causal_ind.
    Context {PSyn : block -> Prop}.
    Context {prefs : PS.t}.
    Variable n : @node PSyn prefs.

    Variable P_vars : list ident -> Prop.

    Lemma causal_ind {v a} : forall (g : AcyGraph v a),
        graph_of_node n g ->
        (forall xs ys, Permutation xs ys -> P_vars xs -> P_vars ys) ->
        P_vars [] ->
        (forall x xs,
            In x (map snd (idcaus (n_in n ++ n_out n))) \/ In x (map snd (idcaus_of_locals (n_block n))) ->
            P_vars xs ->
            (forall y, depends_on (senv_of_inout (n_in n ++ n_out n)) x y (n_block n) -> In y xs) ->
            P_vars (x::xs)) ->
        P_vars (PS.elements (vertices g)).
    Proof.
      intros * [Hv Ha] Hperm Hnil Hdep.
      specialize (has_TopoOrder g) as (xs'&Heq&Hpre).
      eapply Hperm. rewrite Heq, Permutation_PS_elements_of_list. reflexivity.
      eapply TopoOrder_NoDup; eauto.
      assert (incl xs' (map snd (idcaus (n_in n ++ n_out n)) ++ map snd (idcaus_of_locals (n_block n)))) as Hincl.
      { rewrite Hv in Heq.
        repeat rewrite <- ps_from_list_ps_of_list in Heq.
        intros ? Hin. rewrite <- ps_from_list_In in *.
        unfold idents in *.
        now rewrite <- Heq, map_app in Hin. }
      clear Heq.
      induction xs'; auto.
      apply incl_cons' in Hincl as (Hin&Hincl). inversion_clear Hpre as [|?? (?&?&Hin') Hpre'].
      eapply Hdep; eauto.
      - repeat rewrite in_app_iff in Hin. destruct Hin as [|]; auto.
      - intros * Hdep'. eapply Hin'. left.
        eapply Ha; eauto.
    Qed.

    Corollary node_causal_ind :
        node_causal n ->
        (forall xs ys, Permutation xs ys -> P_vars xs -> P_vars ys) ->
        P_vars [] ->
        (forall x xs,
            In x (map snd (idcaus (n_in n ++ n_out n))) \/ In x (map snd (idcaus_of_locals (n_block n))) ->
            P_vars xs ->
            (forall y, depends_on (senv_of_inout (n_in n ++ n_out n)) x y (n_block n) -> In y xs) ->
            P_vars (x::xs)) ->
        P_vars (map snd (idcaus (n_in n ++ n_out n) ++ idcaus_of_locals (n_block n))).
    Proof.
      intros * (Hnd&?&?&g&Hcaus) Hperm Hnil Hdep.
      assert (Hvars:=Hcaus). eapply causal_ind in Hvars; eauto.
      destruct Hcaus as (Heq&_).
      eapply Hperm; [|eauto].
      rewrite Heq, Permutation_PS_elements_of_list; auto.
    Qed.
  End node_causal_ind.

End LCAUSALITY.

Module LCausalityFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks   : CLOCKS Ids Op OpAux)
       (Senv  : STATICENV Ids Op OpAux Cks)
       (Syn   : LSYNTAX Ids Op OpAux Cks Senv)
       <: LCAUSALITY Ids Op OpAux Cks Senv Syn.
  Include LCAUSALITY Ids Op OpAux Cks Senv Syn.
End LCausalityFun.
