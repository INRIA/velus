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
From Velus Require Import Lustre.LSyntax.

(** * Lustre causality *)

Module Type LCAUSALITY
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks : CLOCKS Ids Op OpAux)
       (Import Syn : LSYNTAX Ids Op OpAux Cks).

  (** ** Causality definition *)

  (** Variables that appear in the nth stream of an expression, to the left of fbys. *)
  Inductive Is_free_left (cenv : list (ident * ident)) (cx : ident) : nat -> exp -> Prop :=
  | IFLvar : forall x a,
      In (x, cx) cenv ->
      Is_free_left cenv cx 0 (Evar x a)
  | IFLunop : forall op e a,
      Is_free_left cenv cx 0 e ->
      Is_free_left cenv cx 0 (Eunop op e a)
  | IFLbinop : forall op e1 e2 a,
      Is_free_left cenv cx 0 e1
      \/ Is_free_left cenv cx 0 e2 ->
      Is_free_left cenv cx 0 (Ebinop op e1 e2 a)
  | IFLfby : forall e0s es a k,
      Is_free_left_list cenv cx k e0s ->
      Is_free_left cenv cx k (Efby e0s es a)
  | IFLarrow : forall e0s es a k,
      Is_free_left_list cenv cx k e0s
      \/ Is_free_left_list cenv cx k es ->
      Is_free_left cenv cx k (Earrow e0s es a)
  | IFLwhen : forall es x b a k,
      (k < length (fst a) /\ In (x, cx) cenv)
      \/ Is_free_left_list cenv cx k es ->
      Is_free_left cenv cx k (Ewhen es x b a)
  | IFLmerge : forall x es ty a k,
      (k < length (fst a) /\ In (x, cx) cenv)
      \/ Exists (fun es => Is_free_left_list cenv cx k (snd es)) es ->
      Is_free_left cenv cx k (Emerge (x, ty) es a)
  | IFLcase : forall e es d a k,
      (k < length (fst a) /\ Is_free_left cenv cx 0 e)
      \/ Exists (fun es => Is_free_left_list cenv cx k (snd es)) es
      \/ (exists d0, d = Some d0 /\ Is_free_left_list cenv cx k d0) ->
      Is_free_left cenv cx k (Ecase e es d a)
  | IFLapp : forall f es er a k,
      k < length a ->
      (exists k', Exists (Is_free_left cenv cx k') es)
      \/ (Exists (Is_free_left cenv cx 0) er) ->
      Is_free_left cenv cx k (Eapp f es er a)

  with Is_free_left_list (cenv : list (ident * ident)) (cx : ident) : nat -> list exp -> Prop :=
  | IFLLnow : forall k e es,
      k < numstreams e ->
      Is_free_left cenv cx k e ->
      Is_free_left_list cenv cx k (e::es)
  | IFLLlater : forall k e es,
      k >= numstreams e ->
      Is_free_left_list cenv cx (k - numstreams e) es ->
      Is_free_left_list cenv cx k (e::es).

  Hint Constructors Is_free_left Is_free_left_list.

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

  Lemma InMembers_idcaus {A B} : forall x (xs : list (ident * (A * B * ident))),
      InMembers x (idcaus xs) <-> InMembers x xs.
  Proof.
    intros *.
    now rewrite fst_InMembers, map_fst_idcaus, <-fst_InMembers.
  Qed.

  Lemma NoDupMembers_idcaus {A B} : forall (xs : list (ident * (A * B * ident))),
      NoDupMembers (idcaus xs) <-> NoDupMembers xs.
  Proof.
    intros *.
    now rewrite fst_NoDupMembers, map_fst_idcaus, <-fst_NoDupMembers.
  Qed.

  Inductive Is_defined_in cenv (cx : ident) : block -> Prop :=
  | DefEq : forall x xs es,
      In x xs ->
      In (x, cx) cenv ->
      Is_defined_in cenv cx (Beq (xs, es))
  | DefReset : forall blocks er,
      Exists (Is_defined_in cenv cx) blocks ->
      Is_defined_in cenv cx (Breset blocks er)
  | DefSwitch : forall ec branches,
      Exists (fun blks => Exists (Is_defined_in cenv cx) (snd blks)) branches ->
      Is_defined_in cenv cx (Bswitch ec branches)
  | DefLocal : forall locs blocks,
      Exists (Is_defined_in (cenv ++ idcaus locs) cx) blocks ->
      Is_defined_in cenv cx (Blocal locs blocks).

  Inductive depends_on cenv (cx cy : ident) : block -> Prop :=
  | DepOnEq : forall xs es,
      (exists k x, nth_error xs k = Some x /\ In (x, cx) cenv /\ Is_free_left_list cenv cy k es) ->
      depends_on cenv cx cy (Beq (xs, es))

  | DepOnSwitch1 : forall ec branches,
      Exists (fun blks => Exists (depends_on cenv cx cy) (snd blks)) branches ->
      depends_on cenv cx cy (Bswitch ec branches)
  | DepOnSwitch2 : forall ec branches,
      Exists (fun blks => Exists (Is_defined_in cenv cx) (snd blks)) branches ->
      Is_free_left cenv cy 0 ec ->
      depends_on cenv cx cy (Bswitch ec branches)

  | DepOnReset1 : forall blocks er,
      Exists (depends_on cenv cx cy) blocks ->
      depends_on cenv cx cy (Breset blocks er)
  | DepOnReset2 : forall blocks er,
      Exists (Is_defined_in cenv cx) blocks ->
      Is_free_left cenv cy 0 er ->
      depends_on cenv cx cy (Breset blocks er)

  | DepOnLocal : forall locs blks,
      Exists (depends_on (cenv++idcaus locs) cx cy) blks ->
      depends_on cenv cx cy (Blocal locs blks).

  Definition graph_of_node {PSyn prefs v a} (n : @node PSyn prefs) (g : AcyGraph v a) : Prop :=
    PS.Equal (vertices g) (PSP.of_list (map snd (idcaus (n_in n ++ n_out n ++ locals (n_block n))))) /\
    (forall cx cy, depends_on (idcaus (n_in n ++ n_out n)) cx cy (n_block n) -> is_arc g cy cx).

  Definition node_causal {PSyn prefs} (n : @node PSyn prefs) :=
    NoDup (map snd (idcaus (n_in n ++ n_out n ++ locals (n_block n)))) /\
    exists v a (g : AcyGraph v a), graph_of_node n g.

  (* Some properties *)

  Lemma node_causal_NoDup {PSyn prefs} : forall (nd : @node PSyn prefs),
      node_causal nd ->
      NoDup (map snd (idcaus (n_in nd ++ n_out nd))).
  Proof.
    intros * (Hnd&_).
    unfold idcaus in *. rewrite app_assoc, map_app, map_app in Hnd.
    now apply NoDup_app_l in Hnd.
  Qed.

  Fact Is_free_left_list_length' cenv : forall es x k,
      Forall (fun e => forall x k, Is_free_left cenv x k e -> k < Datatypes.length (annot e)) es ->
      Is_free_left_list cenv x k es ->
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

  Lemma Is_free_left_length {PSyn prefs} (G: @global PSyn prefs) cenv : forall e x k,
      wl_exp G e ->
      Is_free_left cenv x k e ->
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

  Corollary Is_free_left_list_length {PSyn prefs} (G: @global PSyn prefs) cenv : forall es x k,
      Forall (wl_exp G) es ->
      Is_free_left_list cenv x k es ->
      k < length (annots es).
  Proof.
    intros * Hwl Hfree.
    eapply Is_free_left_list_length'; eauto.
    eapply Forall_impl; eauto. intros.
    eapply Is_free_left_length; eauto.
  Qed.

  Lemma Is_free_left_list_Exists cenv : forall es x k,
      Is_free_left_list cenv x k es ->
      exists k', Exists (Is_free_left cenv x k') es.
  Proof.
    induction es; intros * Hfree; inv Hfree.
    - exists k. left; auto.
    - specialize (IHes _ _ H3) as [k' ?].
      exists k'. right; auto.
  Qed.

  Lemma Is_free_left_In_snd cenv : forall e x k,
      Is_free_left cenv x k e ->
      In x (map snd cenv).
  Proof.
    induction e using exp_ind2; intros * Hfree; inv Hfree.
    - (* var *)
      eapply in_map_iff. exists (x, x0); eauto.
    - (* unop *)
      eauto.
    - (* binop *)
      destruct H1; eauto.
    - (* fby *)
      rewrite Forall_forall in *.
      eapply Is_free_left_list_Exists in H3 as (?&Hex).
      eapply Exists_exists in Hex as (?&?&?); eauto.
    - (* arrow *)
      rewrite Forall_forall in *.
      destruct H3 as [Hex|Hex].
      1,2:(eapply Is_free_left_list_Exists in Hex as (?&Hex);
           eapply Exists_exists in Hex as (?&?&?); eauto).
    - (* when *)
      rewrite Forall_forall in *.
      destruct H2 as [(_&Hin)|Hex].
      + eapply in_map_iff. exists (x, x0); eauto.
      + eapply Is_free_left_list_Exists in Hex as (?&Hex).
        eapply Exists_exists in Hex as (?&?&?); eauto.
    - (* merge *)
      repeat setoid_rewrite Forall_forall in H.
      destruct H2 as [(_&Hin)|Hex].
      + eapply in_map_iff. exists (x1, x0); eauto.
      + eapply Exists_exists in Hex as (?&?&Hex).
        eapply Is_free_left_list_Exists in Hex as (?&Hex).
        eapply Exists_exists in Hex as (?&?&?); eauto.
    - (* case *)
      rewrite Forall_forall in *.
      destruct H3 as [(_&Hin)|[Hex|(?&?&Hex)]]; subst; simpl in *; eauto.
      + eapply Exists_exists in Hex as (?&Hin&Hex); subst.
        eapply Is_free_left_list_Exists in Hex as (?&Hex).
        eapply Exists_exists in Hex as (?&?&?); eauto.
        eapply H, Forall_forall in Hin; eauto.
      + rewrite Forall_forall in *.
        eapply Is_free_left_list_Exists in Hex as (?&Hex).
        eapply Exists_exists in Hex as (?&?&?); eauto.
    - (* app *)
      rewrite Forall_forall in *.
      destruct H7 as [(?&Hex)|Hex].
      + eapply Exists_exists in Hex as (?&?&?); eauto.
      + eapply Exists_exists in Hex as (?&?&?); eauto.
  Qed.

  Corollary Is_free_left_list_In_snd cenv : forall es x k,
      Is_free_left_list cenv x k es ->
      In x (map snd cenv).
  Proof.
    intros * Hfree.
    eapply Is_free_left_list_Exists in Hfree as (?&Hex).
    eapply Exists_exists in Hex as (?&_&Hfree).
    eapply Is_free_left_In_snd in Hfree; eauto.
  Qed.

  Hint Constructors Is_defined_in.

  Lemma depends_on_Is_defined_in : forall blk env cy cx,
      depends_on env cx cy blk ->
      Is_defined_in env cx blk.
  Proof.
    induction blk using block_ind2; intros * Hdep; inv Hdep; eauto.
    - (* equation *)
      destruct H0 as (?&?&Hnth&Hin&_).
      econstructor; eauto.
      eapply nth_error_In; eauto.
    - (* reset *)
      eapply Exists_exists in H1 as (?&?&?).
      repeat (take (Forall _ _) and eapply Forall_forall in it; eauto).
      econstructor. eapply Exists_exists; eauto.
    - (* switch *)
      do 2 (eapply Exists_exists in H1 as (?&?&H1)).
      repeat (take (Forall _ _) and eapply Forall_forall in it; eauto).
      econstructor. repeat (eapply Exists_exists; do 2 esplit; eauto).
    - (* local *)
      eapply Exists_exists in H1 as (?&?&?).
      repeat (take (Forall _ _) and eapply Forall_forall in it; eauto).
      econstructor. eapply Exists_exists; eauto.
  Qed.

  (** ** Causality check *)

  Section collect_free.

    Variable (cenv : Env.t ident).

    Definition assemble_brs_free_left_list {A} pss (tys : list A) :=
      List.fold_left (fun ps1 ps2 => List.map (fun '(ps1, ps2) => PS.union ps1 ps2) (List.combine ps1 ps2))
                     pss (List.map (fun _ => PS.empty) tys).

    Definition collect_free_var (x : ident) : ident :=
      or_default xH (Env.find x cenv).

    Fixpoint collect_free_left (e : exp) {struct e} : list PS.t :=
      let collect_free_left_list (es : list exp) := flat_map collect_free_left es in
      match e with
      | Econst _ | Eenum _ _ => [PS.empty]
      | Evar x _ => [PS.singleton (collect_free_var x)]
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
        let cx := collect_free_var x in
        List.map (fun ps => PS.add cx ps) (collect_free_left_list es)
      | Emerge (x, _) es (tys, _) =>
        let ps := assemble_brs_free_left_list (List.map (fun es => collect_free_left_list (snd es)) es) tys in
        List.map (PS.add (collect_free_var x)) ps
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

  Fixpoint collect_depends_on (cenv : Env.t ident) (d : block) : Env.t PS.t :=
    match d with
    | Beq (xs, es) =>
      Env.from_list
        (List.combine
           (List.map (collect_free_var cenv) xs)
           (collect_free_left_list cenv es))
    | Breset blocks er =>
      let pr := collect_free_left cenv er in
      Env.map (fun ps => PS.union (nth 0 pr PS.empty) ps)
              (unions_fuse (map (collect_depends_on cenv) blocks))
    | Bswitch ec branches =>
      let pc := collect_free_left cenv ec in
      Env.map (fun ps => PS.union (nth 0 pc PS.empty) ps)
              (unions_fuse (map (fun blks => unions_fuse (map (collect_depends_on cenv) (snd blks))) branches))
    | Blocal locs blocks =>
      let cenv' := Env.union cenv (Env.from_list (idcaus locs)) in
      unions_fuse (map (collect_depends_on cenv') blocks)
    end.

  Definition build_graph {PSyn prefs} (n : @node PSyn prefs) : Env.t PS.t :=
    let vo := collect_depends_on (Env.from_list (idcaus (n_in n ++ n_out n))) (n_block n) in
    Env.union_fuse PS.union vo (Env.from_list (map (fun '(_, (_, _, cx)) => (cx, PS.empty)) (n_in n))).

  (* Open Scope error_monad_scope. *)

  Definition check_node_causality {PSyn prefs} (n : @node PSyn prefs) : res unit :=
    if check_nodup (map snd (idcaus (n_in n ++ n_out n ++ locals (n_block n)))) then
      match build_acyclic_graph (Env.map PSP.to_list (build_graph n)) with
      | OK _ => OK tt
      | Error msg => Error (MSG "Node " :: (CTX (n_name n)) :: MSG " : " :: msg)
      end
    else Error (MSG "Node " :: (CTX (n_name n)) :: MSG " has duplicated causality annotations" :: nil).

  Definition check_causality {PSyn prefs} (G : @global PSyn prefs) :=
    mmap check_node_causality (nodes G).

  Fact collect_free_left_list_length' cenv : forall es,
      Forall (fun e => length (collect_free_left cenv e) = length (annot e)) es ->
      length (collect_free_left_list cenv es) = length (annots es).
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

  Lemma collect_free_left_length {PSyn prefs} : forall (G: @global PSyn prefs) cenv e,
      wl_exp G e ->
      length (collect_free_left cenv e) = length (annot e).
  Proof.
    Local Ltac solve_forall H :=
      eapply Forall_Forall in H; eauto;
      clear - H;
      eapply Forall_impl; eauto; intros ? [? ?]; auto.

    induction e using exp_ind2; intros Hwl; inv Hwl; simpl.
    - (* const *) reflexivity.
    - (* enum *) reflexivity.
    - (* var *)
      destruct a as (?&?); reflexivity.
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

  Corollary collect_free_left_list_length {PSyn prefs} : forall (G: @global PSyn prefs) cenv es,
      Forall (wl_exp G) es ->
      length (collect_free_left_list cenv es) = length (annots es).
  Proof.
    intros * Hwl.
    eapply collect_free_left_list_length'.
    eapply Forall_impl; eauto. intros ? ?.
    eapply collect_free_left_length; eauto.
  Qed.

  Section collect_free_spec.

    Variable cenv : list (ident * ident).
    Variable cenv' : Env.t ident.

    Hypothesis Heq : Env.Equiv eq cenv' (Env.from_list cenv).

    Lemma collect_free_var_correct : forall x cx,
        InMembers x cenv ->
        collect_free_var cenv' x = cx ->
        In (x, cx) cenv.
    Proof.
      intros * Hinm Hcoll.
      unfold collect_free_var in Hcoll. rewrite Heq in Hcoll.
      eapply Env.In_from_list in Hinm as (cx'&Hfind).
      rewrite Hfind in Hcoll; simpl in *; subst.
      eapply Env.from_list_find_In in Hfind; auto.
    Qed.

    Hypothesis Hnd : NoDupMembers cenv.

    Lemma collect_free_var_complete : forall x cx,
        In (x, cx) cenv ->
        collect_free_var cenv' x = cx.
    Proof.
      intros * Hin.
      unfold collect_free_var. rewrite Heq.
      erewrite Env.find_In_from_list; eauto.
      reflexivity.
    Qed.

    Lemma collect_free_left_list_spec' {PSyn prefs} : forall (G: @global PSyn prefs) es x k,
        Forall (wl_exp G) es ->
        Forall (wx_exp (map fst cenv)) es ->
        Forall (fun e => forall k, wl_exp G e -> wx_exp (map fst cenv) e ->
                           PS.In x (nth k (collect_free_left cenv' e) PS.empty)
                           <-> Is_free_left cenv x k e) es ->
        PS.In x (List.nth k (collect_free_left_list cenv' es) PS.empty) <->
        Is_free_left_list cenv x k es.
    Proof.
      induction es; intros * Hwl Hwx Hf; inv Hwl; inv Hwx; inv Hf.
      - split; intros H.
        + exfalso. eapply not_In_empty. simpl in H; destruct k; eauto.
        + inv H.
      - assert (length (collect_free_left cenv' a) = numstreams a) as Hlen.
        { erewrite collect_free_left_length, length_annot_numstreams; eauto. }
        split; intros H; simpl in *.
        + destruct (Compare_dec.dec_lt k (numstreams a)).
          * left; eauto.
            rewrite app_nth1, H5 in H; eauto. congruence.
          * apply Compare_dec.not_lt in H0.
            right; eauto.
            rewrite app_nth2, IHes in H; eauto. 1,2:congruence.
        + inv H.
          * rewrite app_nth1, H5; eauto. congruence.
          * rewrite app_nth2, IHes; eauto. 1,2:congruence.
    Qed.

    Lemma psunion_collect_free_list_spec' {PSyn prefs} : forall (G: @global PSyn prefs) es x,
        Forall (wl_exp G) es ->
        Forall (wx_exp (map fst cenv)) es ->
        Forall (fun e => forall k, wl_exp G e ->
                           wx_exp (map fst cenv) e ->
                           PS.In x (nth k (collect_free_left cenv' e) PS.empty)
                           <-> Is_free_left cenv x k e) es ->
        PS.In x (PSUnion (collect_free_left_list cenv' es)) <->
        (exists k', Exists (Is_free_left cenv x k') es).
    Proof.
      induction es; intros * Hwl Hwx Hf; inv Hwl; inv Hwx; inv Hf; split; intros H; simpl in *.
      - exfalso.
        rewrite PSUnion_nil in H. apply not_In_empty in H; auto.
      - destruct H as (?&Hex). inv Hex.
      - rewrite PSUnion_In_app in H.
        destruct H as [H|H].
        + apply PSUnion_In_In in H as (?&?&?).
          eapply In_nth in H as (?&?&Hnth).
          rewrite <- Hnth, H5 in H0; eauto.
        + rewrite IHes in H; eauto.
          destruct H as (k'&Hex); eauto.
      - rewrite PSUnion_In_app.
        destruct H as (?&Hex). inv Hex; auto.
        + assert (Hk:=H0).
          eapply Is_free_left_length in Hk; eauto; erewrite <- collect_free_left_length in Hk; eauto.
          apply H5 in H0; auto.
          left. eapply In_In_PSUnion; eauto.
          eapply nth_In; eauto.
        + right. rewrite IHes; eauto.
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
      Exists (Is_free_left cenv x k) es ->
      Exists (Is_free_left cenv x 0) es.
    Proof.
      intros * Wl Num Free.
      eapply Exists_exists in Free as (?&In&Ex). eapply Exists_exists; do 2 esplit; eauto.
      assert (k = 0) as Hk'; subst; eauto.
      eapply Is_free_left_length in Ex. 2:eapply Forall_forall in Wl; eauto.
      eapply Forall_forall in Num; eauto. rewrite length_annot_numstreams, Num in Ex.
      apply PeanoNat.Nat.lt_1_r; auto.
    Qed.
    Hint Resolve Exists_Exists_Is_free.

    Fact assemble_brs_free_left_list_spec: forall x k pss (tys : list type),
        Forall (fun ps => length ps = length tys) pss ->
        PS.In x (List.nth k (assemble_brs_free_left_list pss tys) PS.empty) <->
        Exists (fun ps => PS.In x (List.nth k ps PS.empty)) pss.
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
                - eapply Exists_exists in H1 as (?&Hin&?).
                  eapply Forall_forall in H3; eauto. apply ps_In_k_lt in H.
                  now rewrite H2, Nat.min_id, <-H3.
                - apply ps_In_k_lt in H. now rewrite H2, Nat.min_id.
            }
            rewrite combine_nth; auto.
            rewrite PS.union_spec; auto.
            destruct H; auto.
            inv H; auto.
      }
      rewrite H.
      - split; intros Hin; auto.
        destruct Hin as [?|Hin]; auto.
        exfalso.
        assert (k < length tys) as Hlen'.
        { eapply ps_In_k_lt in Hin; rewrite map_length in Hin; auto. }
        rewrite map_nth' with (d':=OpAux.bool_velus_type) in Hin; eauto.
        eapply not_In_empty; eauto.
      - eapply Forall_impl; [|eauto].
        intros. rewrite map_length; auto.
    Qed.

    Fact collect_free_left_spec {PSyn prefs}: forall (G: @global PSyn prefs) x e k,
        wl_exp G e ->
        wx_exp (map fst cenv) e ->
        PS.In x (List.nth k (collect_free_left cenv' e) PS.empty) <->
        Is_free_left cenv x k e.
    Proof.
      induction e using exp_ind2;
        (intros * Hwl Hwx;
         specialize (Is_free_left_length G cenv _ x k Hwl) as Hlen1;
         specialize (collect_free_left_length _ cenv' _ Hwl) as Hlen2;
         try destruct a as [ty [ck name]];
         inv Hwl; inv Hwx; simpl in *;
         try rewrite <- length_annot_numstreams in *; idtac).
      - (* const *)
        split; intros.
        + exfalso. eapply not_In_empty. repeat (destruct k; eauto).
        + inv H.
      - (* enum *)
        split; intros.
        + exfalso. eapply not_In_empty. repeat (destruct k0; eauto).
        + inv H.
      - (* var *)
        split; intros.
        + simpl in H. destruct k. 2:exfalso; eapply not_In_empty; destruct k; eauto.
          apply PSF.singleton_1 in H; subst. constructor.
          eapply collect_free_var_correct; auto. eapply fst_InMembers; eauto.
        + inv H; simpl. apply PSF.singleton_2; auto.
          eapply collect_free_var_complete; eauto.
      - (* unop *)
        rewrite IHe; eauto.
        split; intros.
        + assert (Hk:=H). eapply Is_free_left_length in Hk; eauto.
          rewrite H4 in Hk. apply PeanoNat.Nat.lt_1_r in Hk; subst; auto.
        + inv H. auto.
      - (* binop *)
        erewrite <- collect_free_left_length with (cenv0:=cenv') in H6, H7; eauto.
        repeat singleton_length.
        split; intros H.
        + destruct k; [|destruct k]. 2,3:destruct (not_In_empty _ H).
          apply PSF.union_1 in H as [?|?]; constructor.
          * left. rewrite <- IHe1; eauto.
          * right. rewrite <- IHe2; eauto.
        + inv H. destruct H3 as [?|?].
          * apply PSF.union_2. rewrite <- IHe1 in H; eauto.
          * apply PSF.union_3. rewrite <- IHe2 in H; eauto.
      - (* fby *)
        split; intros.
        + specialize (ps_In_k_lt _ _ _ H1) as Hk.
          eapply collect_free_left_list_spec' in H1; eauto.
        + erewrite <- collect_free_left_list_length with (cenv0:=cenv') in H7, H8; eauto.
          eapply collect_free_left_list_spec'; eauto.
          inv H1; auto.
      - (* arrow *)
        split; intros.
        + specialize (ps_In_k_lt _ _ _ H1) as Hk. rewrite map_length in Hk.
          erewrite map_nth' with (d':=(PS.empty, PS.empty)) in H1; eauto.
          rewrite combine_nth in H1.
          2:(repeat setoid_rewrite collect_free_left_list_length; eauto; rewrite H7, H8; auto).
          repeat rewrite PS.union_spec in H1. destruct H1 as [Hin|Hin]; eapply collect_free_left_list_spec' in Hin; eauto.
        + erewrite <- collect_free_left_list_length in H7, H8; eauto.
          erewrite map_nth' with (d':=(PS.empty, PS.empty)).
          2:(erewrite <- map_length, Hlen2; eauto).
          rewrite combine_nth. 2:setoid_rewrite H7; setoid_rewrite H8; auto.
          repeat rewrite PS.union_spec. repeat setoid_rewrite collect_free_left_list_spec'; eauto.
          inv H1. destruct H10; auto.
      - (* when *)
        split; intros.
        + specialize (ps_In_k_lt _ _ _ H0) as Hk. rewrite map_length in Hk.
          erewrite map_nth' with (d':=PS.empty) in H0; eauto.
          constructor.
          apply PS.add_spec in H0 as [?|?]; subst; simpl.
          * left; split; auto.
            setoid_rewrite collect_free_left_list_length in Hk; eauto.
            congruence.
            eapply collect_free_var_correct; eauto. eapply fst_InMembers; eauto.
          * right. erewrite <- collect_free_left_list_spec'; eauto.
        + erewrite <- collect_free_left_list_length with (cenv0:=cenv') in H6; eauto.
          erewrite map_nth' with (d':=PS.empty).
          2:(erewrite <- map_length, Hlen2; eapply Hlen1; eauto).
          inv H0. destruct H5 as [(_&?)|?]; subst.
          * apply PSF.add_1; auto.
            apply collect_free_var_complete; auto.
          * apply PSF.add_2. eapply collect_free_left_list_spec'; eauto.
      - (* merge *)
        assert (Forall (fun ps : list PS.t => Datatypes.length ps = Datatypes.length tys)
                       (map (fun es0 => flat_map (collect_free_left cenv') (snd es0)) es)) as Hlen'.
        { clear - H5 H6. rewrite Forall_map, Forall_forall in *; intros.
          erewrite <- H6; eauto.
          eapply collect_free_left_list_length; eauto. }
        split; intros.
        + specialize (ps_In_k_lt _ _ _ H0) as Hk. rewrite map_length in Hk.
          erewrite map_nth' with (d':=PS.empty) in H0; eauto.
          apply PSF.add_iff in H0 as [?|Hfree]; subst.
          * rewrite map_length in Hlen2; rewrite Hlen2, map_length in Hk; auto.
            constructor; left. split; auto.
            eapply collect_free_var_correct; eauto. eapply fst_InMembers; eauto.
          * rewrite assemble_brs_free_left_list_spec in Hfree; auto.
            constructor; right.
            rewrite Exists_map in Hfree. eapply Exists_exists in Hfree as (?&Hin&Hfree).
            eapply Exists_exists; repeat esplit; eauto.
            eapply Forall_forall in H; eauto. eapply Forall_forall in H5; eauto. eapply Forall_forall in H8; eauto.
            eapply collect_free_left_list_spec'; eauto.
        + erewrite map_nth' with (d':=PS.empty).
          2:(erewrite <- map_length, Hlen2; eauto).
          apply PSF.add_iff.
          inv H0. destruct H7 as [(_&?)|Hfree]; subst; auto using collect_free_var_complete.
          right.
          rewrite assemble_brs_free_left_list_spec, Exists_map; auto.
          eapply Exists_exists in Hfree as (?&Hin&Hfree).
          eapply Exists_exists; repeat esplit; eauto.
          eapply Forall_forall in H; eauto. eapply Forall_forall in H5; eauto. eapply Forall_forall in H8; eauto.
          eapply collect_free_left_list_spec'; eauto.
      - (* case *)
        (* assert (Datatypes.length (flat_map (collect_free_left cenv') d) = Datatypes.length ty) as Hlend. *)
        (* { setoid_rewrite collect_free_left_list_length; eauto. } *)
        assert (Forall (fun ps : list PS.t => Datatypes.length ps = Datatypes.length tys)
                       (or_default_with (map (fun _ : type => PS.empty) tys) (fun es0 : list exp => flat_map (collect_free_left cenv') es0) d ::
                                        map (fun es0 => flat_map (collect_free_left cenv') (snd es0)) es)) as Hlen'.
        { constructor.
          - destruct d; simpl in *. 2:now rewrite map_length.
            erewrite <-H12; eauto.
            eapply collect_free_left_list_length; eauto.
          - rewrite Forall_map, Forall_forall in *; intros.
            erewrite <- H10; eauto.
            eapply collect_free_left_list_length; eauto. }
        split; intros.
        + specialize (ps_In_k_lt _ _ _ H1) as Hk. rewrite map_length in Hk.
          erewrite map_nth' with (d':=PS.empty) in H1; eauto.
          apply PS.union_spec in H1 as [Hfree|Hfree].
          2:rewrite assemble_brs_free_left_list_spec in Hfree; auto; inv Hfree.
          * constructor. left. rewrite <-IHe; auto. split; auto.
            rewrite map_length in Hlen2; rewrite Hlen2, map_length in Hk; auto.
          * destruct d; simpl in *.
            -- constructor; right; right. do 2 esplit; eauto.
               eapply collect_free_left_list_spec'; eauto.
            -- exfalso. rewrite map_nth' with (d':=bool_velus_type) in H2. eapply not_In_empty; eauto.
               rewrite assemble_brs_free_left_list_length in Hk; auto.
          * constructor; right; left.
            rewrite Exists_map in H2. eapply Exists_exists in H2 as ((?&?)&Hin&Hfree).
            eapply Exists_exists; repeat esplit; eauto.
            eapply Forall_forall in H; eauto. eapply Forall_forall in H9; eauto. eapply Forall_forall in H14; eauto.
            eapply collect_free_left_list_spec'; eauto.
        + erewrite map_nth' with (d':=PS.empty).
          2:(erewrite <- map_length, Hlen2; eauto).
          apply PS.union_spec.
          inv H1. destruct H8 as [(_&Hfree)|[Hfree|(?&?&Hfree)]]; subst; simpl in *.
          2,3:right; rewrite assemble_brs_free_left_list_spec; auto.
          * left. rewrite IHe; auto.
          * right. rewrite Exists_map; auto.
            eapply Exists_exists in Hfree as (?&Hin&Hfree); subst.
            eapply Exists_exists; repeat esplit; eauto.
            eapply Forall_forall in H; eauto. eapply Forall_forall in H9; eauto. eapply Forall_forall in H14; eauto.
            eapply collect_free_left_list_spec'; eauto.
          * left. eapply collect_free_left_list_spec'; eauto.
      - (* app *)
        split; intros.
        + assert (Hk:=H1). eapply ps_In_k_lt in Hk. rewrite map_length in Hk.
          erewrite map_nth' in H1; eauto. 2:exact (Tenum (xH, 0), Cbase).
          constructor; auto.
          apply PSUnion_In_app in H1 as [?|?].
          * right. eapply psunion_collect_free_list_spec' in H1 as (k'&Ex); eauto.
          * left. erewrite <- psunion_collect_free_list_spec'; eauto.
        + inv H1. erewrite map_nth'; eauto. 2:exact (Tenum (xH, 0), Cbase).
          rewrite PSUnion_In_app.
          destruct H16.
          * right. eapply psunion_collect_free_list_spec'; eauto.
          * left. eapply psunion_collect_free_list_spec'; eauto.
    Qed.

    Corollary collect_free_left_list_spec {PSyn prefs} : forall (G: @global PSyn prefs) es x k,
        Forall (wl_exp G) es ->
        Forall (wx_exp (map fst cenv)) es ->
        PS.In x (List.nth k (collect_free_left_list cenv' es) PS.empty) <->
        Is_free_left_list cenv x k es.
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

  Lemma collect_depends_on_dom {PSyn prefs} (G: @global PSyn prefs) : forall blk cenv cenv',
      NoDupMembers cenv ->
      Env.Equiv eq cenv' (Env.from_list cenv) ->
      NoDupLocals (map fst cenv) blk ->
      wl_block G blk ->
      wx_block (map fst cenv) blk ->
      forall cx, Env.In cx (collect_depends_on cenv' blk) <-> Is_defined_in cenv cx blk.
  Proof.
    induction blk using block_ind2; intros * Hnd Heq Hndloc Hwl Hwx cx;
      inv Hndloc; inv Hwl; inv Hwx; simpl.
    - (* equation *)
      destruct eq; simpl.
      rewrite Env.In_from_list, fst_InMembers, combine_map_fst'.
      2:{ inv H0. erewrite map_length, collect_free_left_list_length; eauto. }
      split; intros Hin.
      + eapply in_map_iff in Hin as (?&?&?). econstructor; eauto.
        eapply collect_free_var_correct; eauto.
        destruct H2.
        eapply fst_InMembers; eauto.
      + inv Hin.
        eapply in_map_iff. do 2 esplit; eauto.
        eapply collect_free_var_complete; eauto.
    - (* reset *)
      rewrite Env.Props.P.F.map_in_iff, unions_fuse_PS_In.
      split; intros Hin.
      + constructor.
        eapply Exists_exists in Hin as (?&Hin1&Hin2); subst.
        eapply in_map_iff in Hin1 as (?&?&Hin1); subst.
        rewrite Forall_forall in *.
        eapply Exists_exists; do 2 esplit; eauto. eapply H; eauto.
      + inv Hin. eapply Exists_exists in H1 as (?&Hin1&Hin2).
        eapply Exists_exists. setoid_rewrite in_map_iff.
        do 2 esplit; eauto.
        rewrite Forall_forall in *.
        eapply H; eauto.
    - (* switch *)
      rewrite Env.Props.P.F.map_in_iff, unions_fuse_PS_In.
      split; intros Hin.
      + constructor.
        eapply Exists_exists in Hin as (?&Hin1&Hin2); subst. eapply in_map_iff in Hin1 as (?&?&Hin1); subst.
        rewrite unions_fuse_PS_In in Hin2.
        eapply Exists_exists in Hin2 as (?&Hin2&Hin3); subst. eapply in_map_iff in Hin2 as (?&?&Hin2); subst.
        do 2 (eapply Exists_exists; do 2 esplit; eauto).
        repeat (take (Forall _ _) and eapply Forall_forall in it; eauto). eapply it; eauto.
      + inv Hin. eapply Exists_exists in H1 as (?&Hin1&Hin2). eapply Exists_exists in Hin2 as (?&Hin2&Hin3).
        eapply Exists_exists. setoid_rewrite in_map_iff.
        do 2 esplit. repeat esplit; eauto. rewrite unions_fuse_PS_In.
        eapply Exists_exists. setoid_rewrite in_map_iff.
        do 2 esplit. repeat esplit; eauto.
        repeat (take (Forall _ _) and eapply Forall_forall in it; eauto). eapply it; eauto.
    - (* locals *)
      assert (NoDupMembers (cenv ++ idcaus locs)) as Hnd'.
      { apply NoDupMembers_app; auto.
        - rewrite NoDupMembers_idcaus; auto.
        - intros * Hin. contradict Hin.
          rewrite fst_InMembers. apply H5.
          rewrite fst_InMembers, map_fst_idcaus, <-fst_InMembers in Hin; auto.
      }
      assert (Env.Equiv eq (Env.union cenv' (Env.from_list (idcaus locs)))
                        (Env.from_list (cenv ++ idcaus locs))) as Hequiv.
      { rewrite Heq. unfold Env.union, Env.from_list.
        rewrite <-Env.adds'_app.
        eapply Env.adds'_Perm; eauto using Env.NoDupMembers_elements.
        apply Env.elements_from_list.
        rewrite NoDupMembers_idcaus; auto.
      }
      split; intros Hin.
      + constructor.
        eapply unions_fuse_PS_In, Exists_exists in Hin as (?&Hin1&Hin2); subst.
        eapply in_map_iff in Hin1 as (?&?&Hin1); subst.
        rewrite Forall_forall in *.
        eapply Exists_exists; do 2 esplit; eauto. eapply H; eauto.
        * rewrite map_app, map_fst_idcaus; eauto.
        * rewrite map_app, map_fst_idcaus; eauto.
      + inv Hin. eapply Exists_exists in H3 as (?&Hin1&Hin2).
        eapply unions_fuse_PS_In, Exists_exists. setoid_rewrite in_map_iff.
        do 2 esplit; eauto.
        rewrite Forall_forall in *.
        eapply H; eauto.
        * rewrite map_app, map_fst_idcaus; eauto.
        * rewrite map_app, map_fst_idcaus; eauto.
  Qed.

  Corollary flat_map_collect_depends_on_dom {PSyn prefs} (G: @global PSyn prefs) : forall blks cenv cenv',
      NoDupMembers cenv ->
      Env.Equiv eq cenv' (Env.from_list cenv) ->
      Forall (NoDupLocals (map fst cenv)) blks ->
      Forall (wl_block G) blks ->
      Forall (wx_block (map fst cenv)) blks ->
      forall cx, Env.In cx (unions_fuse (map (collect_depends_on cenv') blks)) <-> Exists (Is_defined_in cenv cx) blks.
  Proof.
    intros * Hnd Heq Hndl Hwl Hwx ?.
    split; intros Hin.
    - eapply unions_fuse_PS_In, Exists_exists in Hin as (?&Hin1&Hin2); subst.
        eapply in_map_iff in Hin1 as (?&?&Hin1); subst.
        rewrite Forall_forall in *.
        eapply Exists_exists; do 2 esplit; eauto. eapply collect_depends_on_dom; eauto.
    - eapply Exists_exists in Hin as (?&Hin1&Hin2).
      eapply unions_fuse_PS_In, Exists_exists. setoid_rewrite in_map_iff.
      do 2 esplit; eauto.
      rewrite Forall_forall in *.
      eapply collect_depends_on_dom; eauto.
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
      apply in_map_iff in H3 as (?&?&Hin).
      eapply Forall_forall in H2 as (?&Hfind'); eauto. rewrite Hfind' in H; simpl in H; subst.
      eapply Env.NoDup_snd_elements with (x1:=a) (x2:=x0) in Hcenv'; eauto; subst; auto.
  Qed.

  Lemma collect_depends_on_spec {PSyn prefs} : forall (G: @global PSyn prefs) x y blk xs cenv cenv',
      NoDupMembers cenv ->
      Env.Equiv eq cenv' (Env.from_list cenv) ->
      NoDup (map snd ((Env.elements cenv') ++ (idcaus (locals blk)))) ->
      VarsDefined blk xs ->
      NoDup xs ->
      Forall (fun x => Env.In x cenv') xs ->
      NoDupLocals (map fst cenv) blk ->
      wl_block G blk ->
      wx_block (map fst cenv) blk ->
      depends_on cenv x y blk ->
      exists s, Env.MapsTo x s (collect_depends_on cenv' blk) /\ PS.In y s.
  Proof.
    induction blk using block_ind2; intros * Hnd Henv Hnd2 Hvars Hndvars Hvarsenv Hndl Hwl Hwx Hdep;
      simpl; inv Hvars; inv Hndl; inv Hwl; inv Hwx; inv Hdep.
    - (* equation *)
      inv H0. inv H2. destruct H1 as (?&?&Hx&Hin&Hy).
      eapply collect_free_left_list_spec in Hy; eauto.
      repeat esplit; eauto.
      erewrite <-collect_free_left_list_length in H3; eauto.
      apply Env.find_In_from_list.
      2:{ rewrite fst_NoDupMembers, combine_map_fst'; eauto.
          2:rewrite map_length; eauto.
          eapply collect_free_var_nodup; eauto.
          rewrite map_app in Hnd2. apply NoDup_app_l in Hnd2; auto.
      }
      erewrite In_combine_nth_error.
      repeat esplit; eauto.
      + erewrite map_nth_error; eauto.
        erewrite collect_free_var_complete; eauto.
      + eapply nth_error_nth'.
        erewrite <-H3. eapply nth_error_Some; intro; congruence.
    - (* reset block (sub-blocks) *)
      rewrite Forall_forall in *.
      eapply Exists_exists in H1 as (?&Hin&Hdep).
      eapply Forall2_ignore2, Forall_forall in H3 as (xs'&?&?); eauto.
      eapply H with (xs:=xs') in Hdep as (?&?&?); eauto.
      2:{ clear - Hin Hnd2. simpl in *.
          rewrite map_app in *. apply NoDup_app'; auto.
          - apply NoDup_app_l in Hnd2; auto.
          - apply NoDup_app_r in Hnd2.
            rewrite flat_map_concat_map in Hnd2.
            induction blocks; simpl in *; inv Hin.
            1,2:rewrite idcaus_app, map_app in Hnd2; eauto using NoDup_app_l, NoDup_app_r.
          - eapply Forall_forall; intros.
            eapply NoDup_app_In in Hnd2; eauto.
            contradict Hnd2.
            eapply incl_map; eauto. eapply incl_map.
            intros ??. eapply in_flat_map; eauto. }
      2:eapply NoDup_concat; eauto.
      2:{ eapply Forall_incl. rewrite Forall_forall; eauto.
          eapply incl_concat; eauto. }
      eapply unions_fuse_Subset in H3 as (?&Hfind&Hsub). 2:eapply in_map_iff; eauto.
      repeat esplit.
      + unfold Env.MapsTo. now rewrite Env.Props.P.F.map_o, Hfind.
      + eapply PSF.union_iff; eauto.
    - (* reset block (reset expr) *)
      clear H.
      eapply flat_map_collect_depends_on_dom, unions_fuse_PS_In, Exists_exists in H7 as (?&Hin1&(?&Hfind2)); eauto.
      eapply unions_fuse_Subset in Hfind2 as (?&Hfind&Hsub); eauto.
      repeat esplit.
      + unfold Env.MapsTo. now erewrite Env.Props.P.F.map_o, Hfind.
      + eapply collect_free_left_spec in H10; eauto.
        eapply PSF.union_iff; eauto.
    - (* switch (sub-blocks) *)
      setoid_rewrite Env.Props.P.F.map_mapsto_iff.
      eapply Exists_exists in H1 as (?&Hin1&Hdep). eapply Exists_exists in Hdep as (?&Hin2&Hdep).
      repeat (take (Forall _ branches) and eapply Forall_forall in it; eauto).
      repeat (take (Forall _ (snd x0)) and eapply Forall_forall in it; eauto).
      destruct it3 as (?&Hvars&Hperm). eapply Forall2_ignore2, Forall_forall in Hvars as (?&Hin3&Hvars); [|eauto].
      eapply it4 in Hdep as (?&Hfind&?); eauto.
      2:{ simpl_app. unfold idcaus in *; rewrite map_map in *.
          do 2 (eapply nodup_app_map_flat_map in Hnd2; eauto). }
      2:{ rewrite <-Hperm in Hndvars. eapply NoDup_concat; eauto. }
      2:{ rewrite <-Hperm in Hvarsenv. eapply Forall_incl, incl_concat; eauto. }
      eapply unions_fuse_Subset in Hfind as (?&Hfind&Hsub1). 2:eapply in_map_iff; eauto.
      eapply unions_fuse_Subset in Hfind as (?&Hfind&Hsub2).
      2:eapply in_map_iff with (f:=fun x => unions_fuse (map (collect_depends_on cenv') (snd x))); repeat esplit; eauto.
      repeat esplit; eauto.
      eapply PSF.union_iff; eauto.
    - (* switch (condition) *)
      clear H.
      setoid_rewrite Env.Props.P.F.map_mapsto_iff.
      eapply Exists_exists in H9 as ((?&?)&Hin1&Hex).
      assert (Env.In x (unions_fuse (map (fun blks : enumtag * list block => unions_fuse (map (collect_depends_on cenv') (snd blks))) branches))) as (?&Hmap).
      { repeat (take (Forall _ branches) and eapply Forall_forall in it; eauto).
        eapply unions_fuse_PS_In, Exists_exists. do 2 esplit.
        2:eapply flat_map_collect_depends_on_dom; eauto.
        eapply in_map_iff; eauto.
      }
      eapply collect_free_left_spec in H12; eauto.
      repeat esplit; eauto. eapply PSF.union_iff; left; eauto.
    - (* local block *)
      eapply Exists_exists in H5 as (?&Hin&Hdep).
      eapply Forall2_ignore2, Forall_forall in H2 as (xs'&?&?); eauto.
      rewrite Forall_forall in *.
      eapply H with (xs:=xs') in Hdep as (?&Hinc&Hpsin); eauto.
      + eapply unions_fuse_Subset in Hinc as (?&Hfind&Hsub). 2:eapply in_map_iff; eauto.
        repeat esplit.
        * unfold Env.MapsTo. now erewrite Hfind.
        * eauto.
      + apply NoDupMembers_app; auto.
        rewrite NoDupMembers_idcaus; auto.
        intros * Hin'. contradict Hin'.
        rewrite fst_InMembers. apply H7.
        rewrite fst_InMembers, map_fst_idcaus, <-fst_InMembers in Hin'; auto.
      + rewrite Henv. unfold Env.union, Env.from_list.
        rewrite <-Env.adds'_app.
        eapply Env.adds'_Perm; eauto using Env.NoDupMembers_elements.
        apply Env.elements_from_list.
        rewrite NoDupMembers_idcaus; auto.
      + rewrite Env.elements_union.
        { clear - H6 Hin Hnd2. simpl in *. rewrite idcaus_app, app_assoc, map_app in Hnd2.
          rewrite map_app. rewrite Env.elements_from_list. apply NoDup_app'; auto.
          - apply NoDup_app_l in Hnd2; auto.
          - apply NoDup_app_r in Hnd2.
            rewrite flat_map_concat_map in Hnd2.
            induction blocks; simpl in *; inv Hin.
            1,2:rewrite idcaus_app, map_app in Hnd2; eauto using NoDup_app_l, NoDup_app_r.
          - eapply Forall_forall; intros.
            eapply NoDup_app_In in Hnd2; eauto.
            contradict Hnd2.
            eapply incl_map; eauto. eapply incl_map.
            intros ??. eapply in_flat_map; eauto.
          - rewrite NoDupMembers_idcaus; eauto. }
        * intros ? Hin'. rewrite Henv, Env.In_from_list in Hin'.
          rewrite Env.In_from_list, InMembers_idcaus.
          contradict Hin'. rewrite fst_InMembers; eauto.
      + eapply NoDup_concat; eauto.
        rewrite <-H4. apply NoDup_app'; auto.
        * now eapply fst_NoDupMembers.
        * eapply Forall_forall; intros ? Hin1 Hin2.
          eapply Hvarsenv in Hin2. rewrite Henv, Env.In_from_list in Hin2.
          apply fst_InMembers, H7 in Hin2; auto. apply fst_InMembers; auto.
      + eapply Forall_forall; intros.
        assert (In x1 (concat xs0)) as Hin' by (eapply incl_concat; eauto).
        rewrite Env.union_In.
        rewrite <-H4 in Hin'. apply in_app_or in Hin' as [Hin'|Hin']; [right|]; eauto.
        apply Env.In_from_list, fst_InMembers. now rewrite map_fst_idcaus.
      + rewrite map_app, map_fst_idcaus; eauto.
      + rewrite map_app, map_fst_idcaus; eauto.
  Qed.

  Hint Constructors Is_defined_in.

  Lemma Is_defined_in_Is_defined_in : forall x cx blk cenv,
      (* NoDup (map snd (cenv ++ idcaus (locals blk))) -> *)
      In (x, cx) cenv ->
      Syn.Is_defined_in x blk ->
      Is_defined_in cenv cx blk.
  Proof.
    induction blk using block_ind2; intros * Hin Hdef; inv Hdef.
    + (* equation *)
      econstructor; eauto.
    + (* reset *)
      apply Exists_exists in H1 as (?&?&Hdef).
      repeat (take (Forall _ _) and eapply Forall_forall in it; eauto).
      constructor. apply Exists_exists; do 2 esplit; eauto.
    + (* switch *)
      rename H1 into Hdef. do 2 (apply Exists_exists in Hdef as (?&?&Hdef)).
      repeat (take (Forall _ _) and eapply Forall_forall in it; eauto).
      constructor. do 2 (apply Exists_exists; do 2 esplit; eauto).
    + (* local *)
      apply Exists_exists in H2 as (?&?&Hdef).
      repeat (take (Forall _ _) and eapply Forall_forall in it; eauto).
      constructor. apply Exists_exists; do 2 esplit; eauto.
      eapply it; eauto using in_or_app.
  Qed.

  Lemma Is_free_left_In env cenv : forall e k x cx,
      NoDup (map snd cenv) ->
      In (x, cx) cenv ->
      wx_exp env e ->
      Is_free_left cenv cx k e ->
      In x env.
  Proof.
    induction e using exp_ind2; intros * Hnd Hin Hwx Hfree; inv Hwx; inv Hfree; eauto.
    - eapply NoDup_snd_det in Hin; eauto; subst; auto.
    - destruct H2; eauto.
    - eapply Is_free_left_list_Exists in H4 as (?&Hfree). eapply Exists_exists in Hfree as (?&?&?).
      repeat (take (Forall _ e0s) and eapply Forall_forall in it; eauto).
    - destruct H4 as [H4|H4].
      + eapply Is_free_left_list_Exists in H4 as (?&Hfree). eapply Exists_exists in Hfree as (?&?&?).
        repeat (take (Forall _ e0s) and eapply Forall_forall in it; eauto).
      + eapply Is_free_left_list_Exists in H4 as (?&Hfree). eapply Exists_exists in Hfree as (?&?&?).
        repeat (take (Forall _ es) and eapply Forall_forall in it; eauto).
    - destruct H3 as [(_&?)|H4].
      + eapply NoDup_snd_det in Hin; eauto; subst; auto.
      + eapply Is_free_left_list_Exists in H4 as (?&Hfree). eapply Exists_exists in Hfree as (?&?&?).
        repeat (take (Forall _ es) and eapply Forall_forall in it; eauto).
    - destruct H3 as [(_&?)|Hfree].
      + eapply NoDup_snd_det in Hin; eauto; subst; auto.
      + eapply Exists_exists in Hfree as (?&?&Hfree);
          eapply Is_free_left_list_Exists in Hfree as (?&Hfree); eapply Exists_exists in Hfree as (?&?&Hfree).
        repeat (take (Forall _ _) and eapply Forall_forall in it; eauto).
    - destruct H3 as [(_&?)|[Hfree|Hfree]]; eauto.
      + eapply Exists_exists in Hfree as (?&?&Hfree);
          eapply Is_free_left_list_Exists in Hfree as (?&Hfree); eapply Exists_exists in Hfree as (?&?&Hfree).
        repeat (take (Forall _ _) and eapply Forall_forall in it; eauto).
      + destruct Hfree as (?&?&Hfree); subst.
        eapply Is_free_left_list_Exists in Hfree as (?&Hfree); eapply Exists_exists in Hfree as (?&?&Hfree).
        specialize (H7 _ eq_refl). simpl in *.
        repeat (take (Forall _ x0) and eapply Forall_forall in it; eauto).
    - destruct H9 as [(?&Hfree)|Hfree]; eapply Exists_exists in Hfree as (?&?&Hfree).
      + repeat (take (Forall _ es) and eapply Forall_forall in it; eauto).
      + repeat (take (Forall _ er) and eapply Forall_forall in it; eauto).
  Qed.

  Lemma depends_on_In : forall blk env cenv cy x cx,
      NoDup (map snd (cenv ++ idcaus (locals blk))) ->
      In (x, cx) cenv ->
      NoDupLocals (map fst cenv) blk ->
      (* ~InMembers x (locals blk) -> *)
      wx_block env blk ->
      depends_on cenv cy cx blk ->
      In x env.
  Proof.
    induction blk using block_ind2; intros * Hnd Hin (* Hnin  *) Hnd2 Hwx Hdep; inv Hwx; inv Hdep; inv Hnd2; simpl in *.
    - (* equation *)
      destruct H0 as (?&?&?&?&Hfree). destruct H1. rewrite map_app in Hnd.
      eapply Is_free_left_list_Exists in Hfree as (?&Hfree). eapply Exists_exists in Hfree as (?&?&?).
      eapply Is_free_left_In in H4; eauto using NoDup_app_l.
      eapply Forall_forall in H1; eauto.
    - (* reset *)
      eapply Exists_exists in H1 as (?&?&?).
      repeat (take (Forall _ _) and eapply Forall_forall in it; eauto).
      eapply it; eauto.
      + clear - Hnd H0.
        unfold idcaus in *. rewrite map_app, map_map in *.
        eapply nodup_app_map_flat_map; eauto.
    - rewrite map_app in Hnd.
      eapply Is_free_left_In in H5; eauto using NoDup_app_l.
    - (* switch *)
      rename H1 into Hdef. do 2 (eapply Exists_exists in Hdef as (?&?&Hdef)).
      repeat (take (Forall _ _) and eapply Forall_forall in it; eauto).
      eapply it; eauto.
      + clear - Hnd H0 H1.
        unfold idcaus in *. rewrite map_app, map_map in *.
        do 2 (eapply nodup_app_map_flat_map; eauto). eapply in_map_iff; eauto.
        rewrite flat_map_concat_map in *. rewrite map_map; auto.
    - rewrite map_app in Hnd.
      eapply Is_free_left_In in H5; eauto using NoDup_app_l.
    - (* local *)
      eapply Exists_exists in H1 as (?&?&?).
      repeat (take (Forall _ _) and eapply Forall_forall in it; eauto).
      eapply it with (cenv:=cenv++idcaus locs), in_app_iff in it1 as [|]; eauto using in_or_app.
      + exfalso. eapply H7. eapply fst_InMembers; eauto. eapply in_map_iff; do 2 esplit; eauto; auto.
      + rewrite idcaus_app, app_assoc in Hnd. clear - Hnd H0.
        unfold idcaus in *. rewrite map_app, map_map in *.
        eapply nodup_app_map_flat_map; eauto.
      + rewrite map_app, map_fst_idcaus; auto.
  Qed.

  Fact In_Is_defined_in_helper : forall x cx cenv blocks xs0,
      In x (concat xs0 ++ map fst (flat_map locals blocks)) ->
      In (x, cx) (cenv ++ idcaus (flat_map locals blocks)) ->
      Forall2 VarsDefined blocks xs0 ->
      Exists (fun blk => In (x, cx) (cenv ++ idcaus (locals blk)) /\ exists xs, In xs xs0 /\ VarsDefined blk xs /\ In x (xs ++ map fst (locals blk))) blocks.
  Proof.
    intros * Hin Henv Hvars.
    induction Hvars; simpl in *. inv Hin.
    rewrite idcaus_app, Permutation_swap, 2 in_app_iff in Henv.
    destruct Henv as [Henv|[Henv|Henv]].
    + left. repeat esplit; eauto.
      1,2:apply in_or_app; auto.
      right. apply in_map_iff in Henv as ((?&(?&?)&?)&Heq&?); inv Heq.
      eapply in_map_iff. now do 2 eexists; eauto.
    + rewrite map_app, <-app_assoc in Hin. repeat rewrite in_app_iff in Hin.
      destruct Hin as [Hin|[Hin|[Hin|Hin]]].
      1,3:left; repeat esplit; eauto using in_or_app.
      1,2:right; eapply Exists_exists in IHHvars as (?&?&?&?&?&?&?); eauto using in_or_app.
      1,2:eapply Exists_exists; repeat esplit; eauto.
    + right. eapply Exists_exists in IHHvars as (?&?&?&?&?&?&?); eauto.
      eapply Exists_exists. repeat esplit; eauto.
      1,2:apply in_or_app; auto.
      right. apply in_map_iff in Henv as ((?&(?&?)&?)&Heq&?); inv Heq.
      eapply in_map_iff. now do 2 eexists; eauto.
  Qed.

  Lemma In_Is_defined_in : forall x cx blk xs cenv cenv',
      VarsDefined blk xs ->
      In x (xs ++ map fst (locals blk)) ->
      In (x, cx) (cenv ++ idcaus (locals blk)) ->
      incl xs (map fst cenv) ->
      incl cenv cenv' ->
      Is_defined_in cenv' cx blk.
  Proof.
    induction blk using block_ind2; intros * Hvars Hin Henv Hincl1 Hincl2; simpl in *; inv Hvars.
    - (* equation *)
      rewrite app_nil_r in *.
      destruct eq. econstructor; eauto.
    - (* reset *)
      constructor.
      eapply In_Is_defined_in_helper in H3 as Hin'; eauto.
      eapply Exists_exists in Hin' as (?&?&Hin1&?&Hxs&Hvars&Hin2).
      eapply Forall_forall in H; eauto.
      eapply Exists_exists; eauto. do 2 eexists; eauto.
      eapply H; eauto. etransitivity; [|eauto]. apply incl_concat; auto.
    - (* switch *)
      constructor.
      assert (Exists (fun blk => In (x, cx) (cenv ++ idcaus (flat_map locals (snd blk)))
                              /\ exists ys, Forall2 VarsDefined (snd blk) ys /\ Permutation (concat ys) xs
                                      /\ In x (xs ++ map fst (flat_map locals (snd blk)))
                     ) branches) as Hex.
      { clear H.
        apply in_app_iff in Henv as [Henv|Henv].
        - inv H4; try congruence; simpl in *. destruct H as (?&Hvars&Hperm).
          rewrite map_app in Hin. repeat rewrite in_app_iff in Hin.
          destruct Hin as [Hin|[Hin|Hin]].
          1,2:left; repeat esplit; eauto using in_or_app.
          right.
          eapply in_map_iff in Hin as (?&?&Hin); subst.
          eapply in_flat_map in Hin as (?&Hin1&Hin2).
          eapply Forall_forall in H0 as (?&?&?); eauto.
          eapply Exists_exists. repeat esplit; eauto using in_or_app.
          apply in_or_app, or_intror, in_map_iff; eauto.
        - eapply in_map_iff in Henv as ((?&(?&?)&?)&Heq&Henv); inv Heq.
          eapply in_flat_map in Henv as (?&Hbrs&Henv).
          eapply Forall_forall in H4 as (?&?&?); eauto.
          eapply Exists_exists; repeat esplit; eauto using in_or_app.
          1,2:eapply in_or_app, or_intror, in_map_iff; repeat esplit; eauto; auto. } clear H4.
      eapply Exists_exists in Hex as (?&?&?&?&?&?&?).
      eapply In_Is_defined_in_helper, Exists_exists in H1 as (?&?&?&?&?&?&?); eauto. 2:rewrite H4; auto.
      do 2 (eapply Exists_exists; do 2 esplit; eauto).
      repeat (eapply Forall_forall in H; eauto). eapply H; eauto.
      etransitivity; [|eauto]. rewrite <-H4. eapply incl_concat; eauto.
    - (* locals *)
      rewrite map_app, app_assoc, (Permutation_app_comm xs), H4 in Hin.
      rewrite idcaus_app, app_assoc in Henv.
      eapply In_Is_defined_in_helper in H2 as Hin'; eauto.
      constructor.
      eapply Exists_exists in Hin' as (?&?&Hin1&?&Hxs&Hvars&Hin2).
      eapply Forall_forall in H; eauto.
      eapply Exists_exists; eauto. do 2 eexists; eauto.
      eapply H; eauto.
      + etransitivity; [eapply incl_concat; eauto|].
        rewrite <-H4. rewrite map_app, map_fst_idcaus, Permutation_app_comm.
        apply incl_app; [apply incl_appl|apply incl_appr, incl_refl]; auto.
      + apply incl_app; [apply incl_appl|apply incl_appr, incl_refl]; auto.
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
      eapply in_app_or in H1 as [Hin|Hin]; auto.
      exfalso.
      eapply Hnin, In_InMembers; eauto.
    - (* reset *)
      eapply Exists_exists in H1 as (?&Hin&Hex).
      constructor. eapply Exists_exists; eauto. do 2 eexists; eauto.
      eapply Forall2_ignore2, Forall_forall in H4 as (?&Hin'&Hvars); eauto.
      eapply Forall_forall in H2; eauto.
      eapply Forall_forall in H; eauto. eapply H with (xs:=x1); eauto.
      intros ??. eapply Hnin. eapply in_concat' in H0; eauto.
    - (* switch *)
      eapply Exists_exists in H1 as (?&Hin1&Hex). eapply Exists_exists in Hex as (?&Hin2&Hex).
      constructor. do 2 (eapply Exists_exists; eauto; do 2 esplit; eauto).
      repeat (take (Forall _ branches) and eapply Forall_forall in it; eauto). destruct it0 as (?&?&Hperm).
      eapply Forall2_ignore2, Forall_forall in H as (?&?&?); eauto.
      repeat (take (Forall _ (snd x0)) and eapply Forall_forall in it; eauto).
      eapply it0; eauto.
      intros ? Hin. eapply Hnin. rewrite <-Hperm.
      eapply incl_concat; eauto.
    - (* locals *)
      erewrite <-app_assoc in H1. eapply Exists_exists in H1 as (?&Hin&Hex).
      constructor. eapply Exists_exists; eauto. do 2 eexists; eauto.
      eapply Forall2_ignore2, Forall_forall in H3 as (?&Hin'&Hvars); eauto.
      eapply Forall_forall in H2; eauto.
      eapply Forall_forall in H; eauto. eapply H with (xs:=x1); eauto.
      1:eapply NoDupLocals_incl; eauto; solve_incl_app.
      intros ??. eapply in_concat' in H0; eauto. rewrite <-H7 in H0.
      apply in_app_or in H0 as [?|?]; eauto.
      rewrite fst_InMembers. rewrite <-fst_InMembers in H0. eauto.
  Qed.

  Lemma Is_defined_in_In : forall cx blk xs cenv,
      VarsDefined blk xs ->
      incl xs (map fst cenv) ->
      Is_defined_in cenv cx blk ->
      In cx (map snd (cenv ++ idcaus (locals blk))).
  Proof.
    induction blk using block_ind2; intros * Hvars Hincl1 Hdef; simpl in *; inv Hvars; inv Hdef.
    - (* equation *)
      rewrite app_nil_r in *.
      eapply in_map_iff. now do 2 esplit; eauto.
    - (* reset *)
      eapply Exists_exists in H1 as (?&Hin&Hdef).
      eapply Forall2_ignore2, Forall_forall in H3 as (?&?&Hvars); eauto.
      eapply Forall_forall in H; eauto. eapply H with (xs:=x0) in Hdef; eauto.
      2:etransitivity; eauto using incl_concat.
      rewrite map_app, in_app_iff in *. destruct Hdef; auto.
      right. eapply incl_map; eauto. eapply incl_map.
      intros ??. eapply in_flat_map; eauto.
    - (* switch *)
      eapply Exists_exists in H1 as (?&Hin1&Hex). eapply Exists_exists in Hex as (?&Hin2&Hex).
      repeat (take (Forall _ branches) and eapply Forall_forall in it; eauto). destruct it0 as (?&?&Hperm).
      eapply Forall2_ignore2, Forall_forall in H as (?&?&?); eauto.
      repeat (take (Forall _ (snd x)) and eapply Forall_forall in it; eauto).
      eapply it in Hex; eauto. 2:etransitivity; [|eauto]; rewrite <-Hperm; eapply incl_concat; eauto.
      unfold idcaus in *. repeat rewrite map_app in *. rewrite map_map in *.
      eapply in_app_map_flat_map, in_app_map_flat_map; eauto.
    - (* locals *)
      eapply Exists_exists in H1 as (?&Hin&Hdef); eauto.
      eapply Forall2_ignore2, Forall_forall in H2 as (?&?&Hvars); eauto.
      eapply Forall_forall in H; eauto. eapply H with (xs:=x0) in Hdef; eauto.
      2:{ etransitivity; eauto using incl_concat.
          rewrite <-H4. rewrite map_app, map_fst_idcaus, Permutation_app_comm.
          eapply incl_app; [apply incl_appl|apply incl_appr, incl_refl]; auto.
      }
      rewrite idcaus_app.
      repeat rewrite map_app in *.
      rewrite app_assoc.
      rewrite in_app_iff in *. destruct Hdef; auto.
      right. eapply incl_map; eauto. eapply incl_map.
      intros ??. eapply in_flat_map; eauto.
  Qed.

  Lemma build_graph_dom {PSyn prefs} : forall (G: @global PSyn prefs) n,
      wl_node G n ->
      wx_node n ->
      Env.dom (build_graph n) (map snd (idcaus (n_in n ++ n_out n ++ locals (n_block n)))).
  Proof.
    intros * Hwl Hwx. unfold idents, build_graph.
    eapply Env.dom_intro. intros x.
    rewrite Env.union_fuse_In, Env.In_from_list, fst_InMembers.
    rewrite (idcaus_app _ (_ ++ _)), (* (map_app fst),  *)(map_app snd), in_app_iff, or_comm.
    unfold idcaus at 2. erewrite 2 map_map, map_ext. apply or_iff_compat_l.
    2:intros (?&(?&?)&?); auto.
    erewrite collect_depends_on_dom; eauto. 4:erewrite map_fst_idcaus; eauto.
    3:reflexivity.
    2:{ eapply fst_NoDupMembers. rewrite map_fst_idcaus. apply node_NoDup. }
    2:apply node_NoDupLocals.
    2:now rewrite map_fst_idcaus; auto.
    pose proof (n_defd n) as (?&Hdef&Hperm).
    split; intros Hin.
    - rewrite idcaus_app. eapply Is_defined_in_In; eauto.
      + rewrite Hperm, map_fst_idcaus. reflexivity.
      + rewrite idcaus_app in Hin. eapply Is_defined_in_restrict; eauto.
        * eapply NoDupLocals_incl, node_NoDupLocals.
          rewrite map_fst_idcaus. solve_incl_app.
        * pose proof (n_nodup n) as (Hnd&_).
          intros ? Hin'. rewrite Hperm, <-map_fst_idcaus in Hin'.
          eapply NoDupMembers_app_InMembers_l. 2:rewrite fst_InMembers; eauto.
          now rewrite <-idcaus_app, NoDupMembers_idcaus.
    - eapply in_map_iff in Hin as ((?&?)&?&Hin); subst. rewrite idcaus_app in Hin.
      eapply In_Is_defined_in; eauto.
      1,2:rewrite Hperm.
      + rewrite <-map_app, <-map_fst_idcaus, idcaus_app.
        eapply in_map_iff. now do 2 esplit; eauto.
      + rewrite map_fst_idcaus. reflexivity.
      + rewrite idcaus_app. solve_incl_app.
  Qed.

  (* Lemma collect_depends_on_NoDup : forall cenv cenv' blk, *)
  (*     Env.Equiv eq cenv' (Env.from_list cenv) -> *)
  (*     Permutation (map fst (collect_depends_on cenv' blk)) (map snd (cenv ++ idcaus (locals blk))). *)
  (* Proof. *)
  (*   induction blk using block_ind2; intros * Henv; simpl. *)
  (* Qed. *)

  Lemma build_graph_find {PSyn prefs} : forall (G: @global PSyn prefs) n x y,
      wl_node G n ->
      wx_node n ->
      NoDup (map snd (idcaus (n_in n ++ n_out n ++ locals (n_block n)))) ->
      depends_on (idcaus (n_in n ++ n_out n)) x y (n_block n) ->
      exists ys, (Env.find x (build_graph n)) = Some ys /\ PS.In y ys.
  Proof.
    intros * Hwl Hwx Hndcaus Hdep.
    specialize (build_graph_dom G n Hwl) as Hdom.
    eapply Env.dom_use with (x0:=x) in Hdom; eauto.
    rewrite Env.In_find in Hdom. symmetry in Hdom.
    assert (NoDupMembers (idcaus (n_in n ++ n_out n))) as Hnd.
    { pose proof (n_nodup n) as (Hnd&_).
      now rewrite NoDupMembers_idcaus.
    }
    pose proof (n_defd n) as (?&Hdef&Hperm).
    eapply collect_depends_on_spec in Hdep as (?&Hx&Hy); eauto. 2:reflexivity.
    - assert (In x (map snd (idcaus (n_in n ++ n_out n ++ locals (n_block n))))) as Hin'.
      { rewrite app_assoc, idcaus_app. eapply Is_defined_in_In; eauto.
        - rewrite Hperm, map_fst_idcaus. solve_incl_app.
        - eapply collect_depends_on_dom; eauto.
          + reflexivity.
          + rewrite map_fst_idcaus. eapply node_NoDupLocals.
          + now rewrite map_fst_idcaus.
          + esplit; eauto.
      }
      apply Hdom in Hin' as (?&Hfind). clear Hdom.
      eexists; split; eauto.
      unfold build_graph in Hfind.
      rewrite Env.union_fuse_spec, Hx in Hfind.
      destruct (Env.find _ _); inv Hfind; auto using PSF.union_2.
    - rewrite Env.elements_from_list.
      2:rewrite fst_NoDupMembers, map_fst_idcaus; apply node_NoDup.
      now rewrite <-idcaus_app, <-app_assoc.
    - rewrite Hperm. rewrite NoDupMembers_idcaus in Hnd.
      eapply fst_NoDupMembers, NoDupMembers_app_r; eauto.
    - rewrite Hperm. eapply Forall_forall; intros.
      rewrite Env.In_from_list, fst_InMembers, map_fst_idcaus, map_app.
      apply in_or_app; auto.
    - rewrite map_fst_idcaus; apply node_NoDupLocals.
    - now rewrite map_fst_idcaus.
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

    Variable cenv : list (ident * ident).

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
                           -> (forall x, Is_free_left cenv x k e -> P_var x)
                           -> P_exp e k) es ->
        (forall x, Is_free_left_list cenv x k es -> P_var x) ->
        k < length (annots es) ->
        P_exps es k.
    Proof.
      induction es; intros * Hf Hfree Hk; inv Hf; simpl in *. inv Hk.
      destruct (Nat.ltb k (numstreams a)) eqn:Hltb.
      - rewrite PeanoNat.Nat.ltb_lt in Hltb.
        constructor; eauto.
      - eapply PeanoNat.Nat.ltb_ge in Hltb.
        eapply P_exps_later; eauto.
        eapply IHes; eauto.
        rewrite app_length, length_annot_numstreams in Hk.
        apply PeanoNat.Nat.sub_add in Hltb.
        rewrite PeanoNat.Nat.add_comm in Hltb.
        rewrite <- Hltb, <- PeanoNat.Nat.add_lt_mono_l in Hk; auto.
    Qed.

    Hypothesis EconstCase : forall c,
        P_exp (Econst c) 0.

    Hypothesis EenumCase : forall k ty,
        P_exp (Eenum k ty) 0.

    Hypothesis EvarCase : forall x cx ann,
        In (x, cx) cenv ->
        P_var cx ->
        P_exp (Evar x ann) 0.

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
        In (x, cx) cenv ->
        P_var cx ->
        P_exp (Ewhen es x b ann) k.

    Hypothesis EmergeCase : forall x cx tx es ann k,
        k < length (fst ann) ->
        In (x, cx) cenv ->
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
        wx_exp (map fst cenv) e ->
        (forall x, Is_free_left cenv x k e -> P_var x) ->
        k < numstreams e ->
        P_exp e k.
    Proof.
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
        eapply in_map_iff in H0 as ((x&cx)&?&?); subst.
        eapply EvarCase, Hfree; eauto.
      - (* unop *)
        rewrite PeanoNat.Nat.lt_1_r in Hnum; subst.
        apply EunopCase.
        eapply exp_causal_ind; eauto. rewrite H4; auto.
      - (* binop *)
        rewrite PeanoNat.Nat.lt_1_r in Hnum; subst.
        apply EbinopCase.
        1,2:eapply exp_causal_ind; eauto. rewrite H6; auto. rewrite H7; auto.
      - (* fby *)
        eapply EfbyCase; eauto.
        + eapply Pexp_Pexps; eauto. 2:congruence.
          solve_forall' l.
      - (* arrow *)
        eapply EarrowCase; eauto.
        1,2:eapply Pexp_Pexps; eauto; try congruence.
        solve_forall' l. solve_forall' l0.
      - (* when *)
        apply in_map_iff in H1 as ((x&cx)&?&?); subst.
        eapply EwhenCase; eauto.
        eapply Pexp_Pexps; eauto. 2:congruence.
        solve_forall' l.
      - (* merge *)
        apply in_map_iff in H1 as ((?&?)&?&?); subst.
        eapply EmergeCase; eauto.
        assert (forall x, Exists (fun es => Is_free_left_list cenv x k (snd es)) l -> P_var x) as Hfree' by auto.
        clear Hfree H3.
        induction l; inv H4; inv H5; inv H7; constructor; auto.
        eapply Pexp_Pexps; eauto. 2:congruence.
        clear - exp_causal_ind H2 H5.
        destruct a. induction l; inv H2; inv H5; constructor; auto.
      - (* case *)
        apply EcaseCase; eauto.
        + eapply exp_causal_ind; eauto. rewrite H4; auto.
        + assert (forall x, Exists (fun es => Is_free_left_list cenv x k (snd es)) l -> P_var x) as Hfree' by auto.
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
            right; eapply Exists_exists in H as (?&Hin&Hfree1).
            eapply Exists_exists. do 2 esplit; eauto.
            eapply Forall_forall in H6; eauto. rewrite <-length_annot_numstreams in H6.
            assert (Hfree2:=Hfree1). eapply Is_free_left_length in Hfree1; eauto. 2:rewrite Forall_forall in *; eauto.
            rewrite H6 in Hfree1. destruct x0; auto. lia.
    Qed.

  End exp_causal_ind.

  (** More flexible induction principle *)
  Section node_causal_ind.
    Context {PSyn : block -> Prop}.
    Context {prefs : PS.t}.
    Variable n : @node PSyn prefs.

    Variable P_vars : list ident -> Prop.

    (* We can "follow" the [TopOrder] extracted from an [AcyGraph]. *)
    (* This gives us an order over the variables of the node *)
    Lemma TopoOrder_inv {v a} : forall cenv (g : AcyGraph v a) blk x xs,
        (forall x y, depends_on cenv x y blk -> is_arc g y x) ->
        TopoOrder g (x::xs) ->
        (forall y, depends_on cenv x y blk -> In y xs).
    Proof.
      intros * Hdep Hpref Hin Hdep'.
      inversion_clear Hpref as [|?? (?&?&Harc) ?].
      eapply Harc. left. eapply Hdep; eauto.
    Qed.

    Lemma causal_ind {v a} : forall (g : AcyGraph v a),
        graph_of_node n g ->
        (forall xs ys, Permutation xs ys -> P_vars xs -> P_vars ys) ->
        P_vars [] ->
        (forall x xs, In x (map snd (idcaus (n_in n ++ n_out n ++ locals (n_block n)))) ->
                 P_vars xs ->
                 (forall y, depends_on (idcaus (n_in n ++ n_out n)) x y (n_block n) -> In y xs) ->
                 P_vars (x::xs)) ->
        P_vars (PS.elements (vertices g)).
    Proof.
      intros * [Hv Ha] Hperm Hnil Hdep.
      specialize (has_TopoOrder g) as (xs'&Heq&Hpre).
      eapply Hperm. rewrite Heq, Permutation_PS_elements_of_list. reflexivity.
      eapply TopoOrder_NoDup; eauto.
      (* rewrite Heq <- PS_For_all_Forall, <- ps_from_list_ps_of_list, PS_For_all_Forall'. *)
      assert (incl xs' (map snd (idcaus (n_in n ++ n_out n ++ locals (n_block n))))) as Hincl.
      { rewrite Hv in Heq.
        repeat rewrite <- ps_from_list_ps_of_list in Heq.
        intros ? Hin. rewrite <- ps_from_list_In in *.
        unfold idents in *.
        now rewrite <- Heq in Hin. }
      clear Heq.
      induction xs'; auto.
      apply incl_cons' in Hincl as (Hin&Hincl). inversion_clear Hpre as [|?? (?&?&Hin') Hpre'].
      eapply Hdep; eauto.
      intros * Hdep'. eapply Hin'. left.
      eapply Ha; eauto.
    Qed.

    Corollary node_causal_ind :
        node_causal n ->
        (forall xs ys, Permutation xs ys -> P_vars xs -> P_vars ys) ->
        P_vars [] ->
        (forall x xs, In x (map snd (idcaus (n_in n ++ n_out n ++ locals (n_block n)))) ->
                 P_vars xs ->
                 (forall y, depends_on (idcaus (n_in n ++ n_out n)) x y (n_block n) -> In y xs) ->
                 P_vars (x::xs)) ->
        P_vars (map snd (idcaus (n_in n ++ n_out n ++ locals (n_block n)))).
    Proof.
      intros * (Hnd&?&?&g&Hcaus) Hperm Hnil Hdep.
      assert (Hvars:=Hcaus). eapply causal_ind in Hvars; eauto.
      destruct Hcaus as (Heq&_).
      eapply Hperm; [|eauto].
      rewrite Heq, Permutation_PS_elements_of_list; auto. (*  reflexivity. *)
    Qed.
  End node_causal_ind.

End LCAUSALITY.

Module LCausalityFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks   : CLOCKS Ids Op OpAux)
       (Syn   : LSYNTAX Ids Op OpAux Cks)
       <: LCAUSALITY Ids Op OpAux Cks Syn.
  Include LCAUSALITY Ids Op OpAux Cks Syn.
End LCausalityFun.
