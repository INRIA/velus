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
  Inductive Is_free_left (x : ident) : nat -> exp -> Prop :=
  | IFLvar : forall a,
      Is_free_left x 0 (Evar x a)
  | IFLunop : forall op e a,
      Is_free_left x 0 e ->
      Is_free_left x 0 (Eunop op e a)
  | IFLbinop : forall op e1 e2 a,
      Is_free_left x 0 e1
      \/ Is_free_left x 0 e2 ->
      Is_free_left x 0 (Ebinop op e1 e2 a)
  | IFLfby : forall e0s es er a k,
      Is_free_left_list x k e0s
      \/ (k < length a /\ Exists (Is_free_left x 0) er) ->
      Is_free_left x k (Efby e0s es er a)
  | IFLarrow : forall e0s es er a k,
      Is_free_left_list x k e0s
      \/ Is_free_left_list x k es
      \/ (k < length a /\ Exists (Is_free_left x 0) er) ->
      Is_free_left x k (Earrow e0s es er a)
  | IFLwhen : forall es y b a k,
      (k < length (fst a) /\ x = y)
      \/ Is_free_left_list x k es ->
      Is_free_left x k (Ewhen es y b a)
  | IFLmerge : forall es y ty a k,
      (k < length (fst a) /\ x = y)
      \/ Exists (Is_free_left_list x k) es ->
      Is_free_left x k (Emerge (y, ty) es a)
  | IFLcase : forall e es d a k,
      (k < length (fst a) /\ Is_free_left x 0 e)
      \/ Exists (fun oes => exists es, oes = Some es /\ Is_free_left_list x k es) es
      \/ Is_free_left_list x k d ->
      Is_free_left x k (Ecase e es d a)
  | IFLapp : forall f es er a k,
      k < length a ->
      (exists k', Exists (Is_free_left x k') es)
      \/ (Exists (Is_free_left x 0) er) ->
      Is_free_left x k (Eapp f es er a)

  with Is_free_left_list (x : ident) : nat -> list exp -> Prop :=
  | IFLLnow : forall k e es,
      k < numstreams e ->
      Is_free_left x k e ->
      Is_free_left_list x k (e::es)
  | IFLLlater : forall k e es,
      k >= numstreams e ->
      Is_free_left_list x (k - numstreams e) es ->
      Is_free_left_list x k (e::es).

  Hint Constructors Is_free_left Is_free_left_list.

  Definition depends_on (eqs : list equation) (x : ident) (y : ident) :=
    Exists (fun '(xs, es) => exists k,
                nth_error xs k = Some x /\
                Is_free_left_list y k es) eqs.

  Definition depends_on_ck vars (eqs : list equation) (x : ident) (y : ident) :=
    depends_on eqs x y \/ (exists ck, In (x, ck) vars /\ Is_free_in_clock y ck).

  Definition graph_of_eqs {v a} vars eqs (g : AcyGraph v a) : Prop :=
    PS.Equal (vertices g) (PSP.of_list (map fst vars)) /\
    (forall x y, depends_on_ck vars eqs x y -> is_arc g y x).

  Definition graph_of_node {prefs v a} (n : @node prefs) (g : AcyGraph v a) : Prop :=
    graph_of_eqs (idck (n_in n ++ n_vars n ++ n_out n)) (n_eqs n) g.

  Definition node_causal {prefs} (n : @node prefs) :=
    exists {v a} (g : AcyGraph v a), graph_of_node n g.

  Instance graph_of_eqs_Proper {v a} :
    Proper (@Permutation _ ==> @Permutation _ ==> @eq (AcyGraph v a) ==> @Basics.impl)
           graph_of_eqs.
  Proof.
    intros vars vars' Hp1 eqs eqs' Hp2 ? xs ? (Hv&Ha); subst.
    split; auto.
    - rewrite <- ps_from_list_ps_of_list in *.
      rewrite <- Hp1; auto.
    - intros * Hdep. apply Ha.
      destruct Hdep as [?|(ck&?&?)].
      + left. unfold depends_on in *.
        rewrite Hp2; auto.
      + right. exists ck; split; auto.
        rewrite Hp1; auto.
  Qed.

  Fact Is_free_left_list_length' : forall es x k,
      Forall (fun e => forall x k, Is_free_left x k e -> k < Datatypes.length (annot e)) es ->
      Is_free_left_list x k es ->
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

  Lemma Is_free_left_length {prefs} : forall (G: @global prefs) e x k,
      wl_exp G e ->
      Is_free_left x k e ->
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
      destruct H4 as [?|(?&?)]; auto. solve_forall2 H11 H.
    - (* arrow *)
      destruct H4 as [?|[?|(?&?)]]; auto. solve_forall2 H11 H. solve_forall2 H12 H0.
    - (* when *)
      rewrite map_length. destruct H2 as [[? ?]|?]; auto.
      solve_forall2 H7 H.
    - (* merge *)
      rewrite map_length. destruct H2 as [[? ?]|?]; auto.
      eapply Forall_Forall in H; eauto. eapply Forall_Forall in H6; eauto. clear H7 H.
      eapply Forall_Exists in H0; eauto. eapply Exists_exists in H0 as (?&?&((?&IH)&Wl)&?).
      solve_forall2 H0 IH.
    - (* case *)
      rewrite map_length. destruct H3 as [[? ?]|[?|?]]; auto.
      + rewrite Forall_forall in *.
        eapply Exists_exists in H1 as (?&Hin&(?&?&?)); subst.
        specialize (H _ Hin); simpl in H. erewrite <- H11; eauto.
        eapply Is_free_left_list_length'; eauto.
        eapply Forall_impl_In in H; eauto; simpl. intros; simpl. eapply H3; eauto.
        eapply Forall_forall in H10; eauto.
      + solve_forall2 H13 H0.
  Qed.

  Corollary Is_free_left_list_length {prefs} : forall (G: @global prefs) es x k,
      Forall (wl_exp G) es ->
      Is_free_left_list x k es ->
      k < length (annots es).
  Proof.
    intros * Hwl Hfree.
    eapply Is_free_left_list_length'; eauto.
    eapply Forall_impl; eauto. intros.
    eapply Is_free_left_length; eauto.
  Qed.

  Lemma Is_free_left_list_Exists : forall es x k,
      Is_free_left_list x k es ->
      exists k', Exists (Is_free_left x k') es.
  Proof.
    induction es; intros * Hfree; inv Hfree.
    - exists k. left; auto.
    - specialize (IHes _ _ H3) as [k' ?].
      exists k'. right; auto.
  Qed.

  (** ** Causality check *)

  Definition assemble_brs_free_left_list {A} pss (tys : list A) :=
    List.fold_left (fun ps1 ps2 => List.map (fun '(ps1, ps2) => PS.union ps1 ps2) (List.combine ps1 ps2))
                   pss (List.map (fun _ => PS.empty) tys).

  Fixpoint collect_free_left (e : exp) {struct e} : list PS.t :=
    let collect_free_left_list (es : list exp) := flat_map collect_free_left es in
    match e with
    | Econst _ | Eenum _ _ => [PS.empty]
    | Evar id (_, (ck, _)) => [PS.singleton id]
    | Eunop _ e (_, (ck, _)) => (collect_free_left e)
    | Ebinop _ e1 e2 (_, (ck, _)) =>
      let ps1 := collect_free_left e1 in
      let ps2 := collect_free_left e2 in
      List.map (fun '(ps1, ps2) => PS.union ps1 ps2) (List.combine ps1 ps2)
    | Efby e0s _ er _ =>
      let psr := PSUnion (collect_free_left_list er) in
      List.map (PS.union psr) (collect_free_left_list e0s)
    | Earrow e0s es er _ =>
      let ps1 := collect_free_left_list e0s in
      let ps2 := collect_free_left_list es in
      let psr := PSUnion (collect_free_left_list er) in
      List.map (fun '(ps1, ps2) => PS.union psr (PS.union ps1 ps2)) (List.combine ps1 ps2)
    | Ewhen es id _ _ =>
      List.map (fun ps => PS.add id ps) (collect_free_left_list es)
    | Emerge (id, _) es (tys, _) =>
      let ps := assemble_brs_free_left_list (List.map collect_free_left_list es) tys in
      List.map (PS.add id) ps
    | Ecase e es d (tys, _) =>
      let ps0 := collect_free_left e in
      let psd := collect_free_left_list d in
      let ps1 := assemble_brs_free_left_list (psd::(List.map (or_default_with psd collect_free_left_list) es)) tys in
      List.map (PS.union (nth 0 ps0 PS.empty)) ps1
    | Eapp _ es er a =>
      let ps := PSUnion (collect_free_left_list er ++ collect_free_left_list es) in
      List.map (fun _ => ps) a
    end.

  Definition collect_free_left_list (es : list exp) :=
    flat_map collect_free_left es.

  Fixpoint collect_free_clock (ck : clock) : PS.t :=
    match ck with
    | Cbase => PS.empty
    | Con ck x _ => (PS.add x (collect_free_clock ck))
    end.

  Definition build_graph {prefs} (n : @node prefs) : Env.t PS.t :=
    let vo := flat_map (fun '(xs, es) =>
                                 let frees := collect_free_left_list es in
                                 List.combine xs frees) (n_eqs n) in
    let env := Env.from_list (vo ++ (map (fun '(x, _) => (x, PS.empty)) (n_in n))) in
    Env.mapi (fun x deps =>
                match List.find (fun xtc => (fst xtc =? x)%positive)
                                (n_in n ++ n_vars n ++ n_out n)
                with
                | Some (_, (_, ck)) => PS.union deps (collect_free_clock ck)
                | None => deps
                end) env.

  Open Scope error_monad_scope.

  Definition check_node_causality {prefs} (n : @node prefs) : res unit :=
    match build_acyclic_graph (Env.map PSP.to_list (build_graph n)) with
    | OK _ => OK tt
    | Error msg => Error (MSG "Node " :: (CTX (n_name n)) :: MSG " : " :: msg)
    end.

  Definition check_causality {prefs} (G : @global prefs) :=
    mmap check_node_causality (nodes G).

  Fact collect_free_left_list_length' : forall es,
      Forall (fun e => length (collect_free_left e) = length (annot e)) es ->
      length (collect_free_left_list es) = length (annots es).
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

  Lemma collect_free_left_length {prefs} : forall (G: @global prefs) e,
      wl_exp G e ->
      length (collect_free_left e) = length (annot e).
  Proof.
    Local Ltac solve_forall H :=
      eapply Forall_Forall in H; eauto;
      clear - H;
      eapply Forall_impl; eauto; intros ? [? ?]; auto.

    induction e using exp_ind2; intros Hwl; inv Hwl; simpl.
    - (* const *) reflexivity.
    - (* enum *) reflexivity.
    - (* var *)
      destruct a as (?&?&?); reflexivity.
    - (* unop *)
      destruct a as (?&?&?).
      rewrite <- length_annot_numstreams in H4. rewrite IHe; auto.
    - (* binop *)
      destruct a as (?&?&?).
      rewrite <- length_annot_numstreams in H6, H7.
      rewrite map_length, combine_length, IHe1, IHe2, H6, H7; auto.
    - (* fby *)
      rewrite map_length.
      setoid_rewrite collect_free_left_list_length'; auto.
      solve_forall H.
    - (* arrow *)
      rewrite map_length, combine_length.
      setoid_rewrite collect_free_left_list_length'.
      rewrite H10, H11. apply PeanoNat.Nat.min_id.
      solve_forall H. solve_forall H0.
    - (* when *)
      destruct nck. rewrite map_length, map_length.
      setoid_rewrite collect_free_left_list_length'; auto.
      solve_forall H.
    - (* merge *)
      destruct x, nck. rewrite map_length, assemble_brs_free_left_list_length, map_length; auto.
      rewrite Forall_map.
      rewrite Forall_forall in *; intros.
      erewrite <- H6; eauto.
      setoid_rewrite collect_free_left_list_length'; eauto.
      specialize (H _ H0). specialize (H5 _ H0).
      solve_forall H.
    - (* case *)
      destruct nck. rewrite map_length, assemble_brs_free_left_list_length, map_length; auto.
      constructor.
      + rewrite <-H12. eapply collect_free_left_list_length'.
        eapply Forall_impl_In; [|eapply H0]; intros.
        eapply Forall_forall in H11; eauto.
      + rewrite Forall_map.
        rewrite Forall_forall in *; intros.
        destruct x; simpl in *.
        * erewrite <-H10; eauto.
          specialize (H _ H1); simpl in H.
          eapply collect_free_left_list_length'.
          eapply Forall_impl_In; [|eauto]. intros ? Hin ?.
          eapply Forall_forall in H9; eauto.
        * rewrite <-H12. eapply collect_free_left_list_length'.
          eapply Forall_forall; eauto.
    - (* app *) rewrite map_length; auto.
  Qed.

  Corollary collect_free_left_list_length {prefs} : forall (G: @global prefs) es,
      Forall (wl_exp G) es ->
      length (collect_free_left_list es) = length (annots es).
  Proof.
    intros * Hwl.
    eapply collect_free_left_list_length'.
    eapply Forall_impl; eauto. intros ? ?.
    eapply collect_free_left_length; eauto.
  Qed.

  Lemma collect_free_left_list_spec' {prefs} : forall (G: @global prefs) es x k,
      Forall (wl_exp G) es ->
      Forall (fun e => forall k, wl_exp G e -> PS.In x (nth k (collect_free_left e) PS.empty)
                                               <-> Is_free_left x k e) es ->
      PS.In x (List.nth k (collect_free_left_list es) PS.empty) <->
      Is_free_left_list x k es.
  Proof.
    induction es; intros * Hwl Hf; inv Hwl; inv Hf.
    - split; intros H.
      + exfalso. eapply not_In_empty. simpl in H; destruct k; eauto.
      + inv H.
    - assert (length (collect_free_left a) = numstreams a) as Hlen.
      { erewrite collect_free_left_length, length_annot_numstreams; eauto. }
      split; intros H; simpl in *.
      + destruct (Compare_dec.dec_lt k (numstreams a)).
        * left; eauto.
          rewrite app_nth1, H3 in H; eauto. congruence.
        * apply Compare_dec.not_lt in H0.
          right; eauto.
          rewrite app_nth2, IHes in H; eauto. 1,2:congruence.
      + inv H.
        * rewrite app_nth1, H3; eauto. congruence.
        * rewrite app_nth2, IHes; eauto. 1,2:congruence.
  Qed.

  Lemma psunion_collect_free_list_spec' {prefs} : forall (G: @global prefs) es x,
      Forall (wl_exp G) es ->
      Forall (fun e => forall k, wl_exp G e -> PS.In x (nth k (collect_free_left e) PS.empty)
                                               <-> Is_free_left x k e) es ->
      PS.In x (PSUnion (collect_free_left_list es)) <->
      (exists k', Exists (Is_free_left x k') es).
  Proof.
    induction es; intros * Hwl Hf; inv Hwl; inv Hf; split; intros H; simpl in *.
    - exfalso.
      rewrite PSUnion_nil in H. apply not_In_empty in H; auto.
    - destruct H as (?&Hex). inv Hex.
    - rewrite PSUnion_In_app in H.
      destruct H as [H|H].
      + apply PSUnion_In_In in H as (?&?&?).
        eapply In_nth in H as (?&?&Hnth).
        rewrite <- Hnth, H3 in H0; eauto.
      + rewrite IHes in H; eauto.
        destruct H as (k'&Hex); eauto.
    - rewrite PSUnion_In_app.
      destruct H as (?&Hex). inv Hex; auto.
      + assert (Hk:=H0).
        eapply Is_free_left_length in Hk; eauto; erewrite <- collect_free_left_length in Hk; eauto.
        apply H3 in H0; auto.
        left. eapply In_In_PSUnion; eauto.
        eapply nth_In; auto.
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

  Lemma Exists_Exists_Is_free {prefs} : forall (G: @global prefs) es x k,
    Forall (wl_exp G) es ->
    Forall (fun e => numstreams e = 1) es ->
    Exists (Is_free_left x k) es ->
    Exists (Is_free_left x 0) es.
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

  Fact collect_free_left_spec {prefs}: forall (G: @global prefs) x e k,
      wl_exp G e ->
      PS.In x (List.nth k (collect_free_left e) PS.empty) <->
      Is_free_left x k e.
  Proof.
    induction e using exp_ind2;
      (intros * Hwl;
       specialize (Is_free_left_length G _ x k Hwl) as Hlen1;
       specialize (collect_free_left_length _ _ Hwl) as Hlen2;
       try destruct a as [ty [ck name]];
       inv Hwl; simpl in *;
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
      + inv H; simpl. apply PSF.singleton_2; auto.
    - (* unop *)
      rewrite IHe; eauto.
      split; intros.
      + assert (Hk:=H). eapply Is_free_left_length in Hk; eauto.
        rewrite H4 in Hk. apply PeanoNat.Nat.lt_1_r in Hk; subst; auto.
      + inv H. auto.
    - (* binop *)
      erewrite <- collect_free_left_length in H6, H7; eauto.
      repeat singleton_length.
      split; intros H.
      + destruct k; [|destruct k]. 2,3:destruct (not_In_empty _ H).
        apply PSF.union_1 in H as [?|?]; constructor.
        * left. rewrite <- IHe1; eauto.
        * right. rewrite <- IHe2; eauto.
      + inv H. destruct H2 as [?|?].
        * apply PSF.union_2. rewrite <- IHe1 in H; eauto.
        * apply PSF.union_3. rewrite <- IHe2 in H; eauto.
    - (* fby *)
      split; intros.
      + specialize (ps_In_k_lt _ _ _ H2) as Hk. rewrite map_length in Hk.
        erewrite map_nth' with (d':=PS.empty) in H2; eauto.
        erewrite PS.union_spec, collect_free_left_list_spec' in H2; eauto.
        constructor. destruct H2; auto.
        right. setoid_rewrite <- Hlen2. rewrite map_length. split; auto.
        eapply psunion_collect_free_list_spec' in H2 as (k'&Ex); eauto.
      + erewrite <- collect_free_left_list_length in H10, H11; eauto.
        erewrite map_nth' with (d':=PS.empty).
        2:(erewrite <- map_length, Hlen2; eauto).
        erewrite PS.union_spec, collect_free_left_list_spec'; eauto.
        inv H2. destruct H5 as [?|(?&?)]; auto.
        left. eapply psunion_collect_free_list_spec'; eauto.
    - (* arrow *)
      split; intros.
      + specialize (ps_In_k_lt _ _ _ H2) as Hk. rewrite map_length in Hk.
        erewrite map_nth' with (d':=(PS.empty, PS.empty)) in H2; eauto.
        rewrite combine_nth in H2.
        2:(repeat erewrite collect_free_left_list_length; eauto; rewrite H10, H11; auto).
        repeat rewrite PS.union_spec in H2. do 2 erewrite collect_free_left_list_spec' in H2; eauto.
        destruct H2 as [?|[?|?]]; auto.
        constructor. repeat right. setoid_rewrite <- Hlen2. rewrite map_length. split; auto.
        eapply psunion_collect_free_list_spec' in H2 as (k'&Ex); eauto.
      + erewrite <- collect_free_left_list_length in H10, H11; eauto.
        erewrite map_nth' with (d':=(PS.empty, PS.empty)).
        2:(erewrite <- map_length, Hlen2; eauto).
        rewrite combine_nth. 2:setoid_rewrite H10; setoid_rewrite H11; auto.
        repeat rewrite PS.union_spec. repeat erewrite collect_free_left_list_spec'; eauto.
        inv H2. destruct H5 as [?|[?|(?&?)]]; auto.
        left. eapply psunion_collect_free_list_spec'; eauto.
    - (* when *)
      split; intros.
      + specialize (ps_In_k_lt _ _ _ H0) as Hk. rewrite map_length in Hk.
        erewrite map_nth' with (d':=PS.empty) in H0; eauto.
        constructor.
        apply PS.add_spec in H0 as [?|?]; subst; simpl.
        * left; split; auto.
          erewrite collect_free_left_list_length in Hk; eauto.
          congruence.
        * right. erewrite <- collect_free_left_list_spec'; eauto.
      + erewrite <- collect_free_left_list_length in H7; eauto.
        erewrite map_nth' with (d':=PS.empty).
        2:(erewrite <- map_length, Hlen2; eapply Hlen1; eauto).
        inv H0. destruct H4 as [(_&?)|?]; subst.
        * apply PSF.add_1; auto.
        * apply PSF.add_2. erewrite collect_free_left_list_spec'; eauto.
    - (* merge *)
      destruct x0.
      assert (Forall (fun ps : list PS.t => Datatypes.length ps = Datatypes.length ty)
                     (map (fun es0 => flat_map collect_free_left es0) es)) as Hlen'.
      { clear - H6 H7. rewrite Forall_map, Forall_forall in *; intros.
        erewrite <- H7; eauto.
        eapply collect_free_left_list_length; eauto. }
      split; intros.
      + specialize (ps_In_k_lt _ _ _ H0) as Hk. rewrite map_length in Hk.
        erewrite map_nth' with (d':=PS.empty) in H0; eauto.
        apply PSF.add_iff in H0 as [?|Hfree]; subst.
        * rewrite map_length in Hlen2; rewrite Hlen2, map_length in Hk; auto.
        * rewrite assemble_brs_free_left_list_spec in Hfree; auto.
          constructor; right.
          rewrite Exists_map in Hfree. eapply Exists_exists in Hfree as (?&Hin&Hfree).
          eapply Exists_exists; repeat esplit; eauto.
          eapply Forall_forall in H; eauto. eapply Forall_forall in H6; eauto.
          eapply collect_free_left_list_spec'; eauto.
      + erewrite map_nth' with (d':=PS.empty).
        2:(erewrite <- map_length, Hlen2; eauto).
        apply PSF.add_iff.
        inv H0. destruct H3 as [(_&?)|Hfree]; subst; auto.
        right.
        rewrite assemble_brs_free_left_list_spec, Exists_map; auto.
        eapply Exists_exists in Hfree as (?&Hin&Hfree).
        eapply Exists_exists; repeat esplit; eauto.
        eapply Forall_forall in H; eauto. eapply Forall_forall in H6; eauto.
        eapply collect_free_left_list_spec'; eauto.
    - (* case *)
      assert (Datatypes.length (flat_map collect_free_left d) = Datatypes.length ty) as Hlend.
      { erewrite collect_free_left_list_length; eauto. }
      assert (Forall (fun ps : list PS.t => Datatypes.length ps = Datatypes.length ty)
                     (map (or_default_with (flat_map collect_free_left d) (fun es0 => flat_map collect_free_left es0)) es)) as Hlen'.
      { clear - H10 H11 Hlend. rewrite Forall_map, Forall_forall in *; intros.
        destruct x; simpl in *; eauto.
        erewrite <- H11; eauto.
        eapply collect_free_left_list_length; eauto. }
      split; intros.
      + specialize (ps_In_k_lt _ _ _ H1) as Hk. rewrite map_length in Hk.
        erewrite map_nth' with (d':=PS.empty) in H1; eauto.
        apply PS.union_spec in H1 as [Hfree|Hfree].
        * constructor. left. rewrite <-IHe; auto. split; auto.
          rewrite map_length in Hlen2; rewrite Hlen2, map_length in Hk; auto.
        * rewrite assemble_brs_free_left_list_spec in Hfree; auto.
          constructor; right. inv Hfree; [right|]. 1:eapply collect_free_left_list_spec'; eauto.
          rewrite Exists_map in H2. eapply Exists_exists in H2 as (?&Hin&Hfree).
          destruct x0; [left|right]. 2:eapply collect_free_left_list_spec'; eauto.
          eapply Exists_exists; repeat esplit; eauto.
          eapply Forall_forall in H; eauto; simpl in *.
          eapply collect_free_left_list_spec'; eauto.
      + erewrite map_nth' with (d':=PS.empty).
        2:(erewrite <- map_length, Hlen2; eauto).
        apply PS.union_spec.
        inv H1. destruct H4 as [(_&Hfree)|[Hfree|Hfree]].
        2,3:right; rewrite assemble_brs_free_left_list_spec; auto.
        * left. rewrite IHe; auto.
        * right. rewrite Exists_map; auto.
          eapply Exists_exists in Hfree as (?&Hin&(?&?&Hfree)); subst.
          eapply Exists_exists; repeat esplit; eauto.
          eapply Forall_forall in H; eauto.
          eapply collect_free_left_list_spec'; eauto.
        * left. eapply collect_free_left_list_spec'; eauto.
    - (* app *)
      split; intros.
      + assert (Hk:=H1). eapply ps_In_k_lt in Hk. rewrite map_length in Hk.
        erewrite map_nth' in H1; eauto. 2:exact (Tenum (xH, 0), (Cbase, None)).
        constructor; auto.
        apply PSUnion_In_app in H1 as [?|?].
        * right. eapply psunion_collect_free_list_spec' in H1 as (k'&Ex); eauto.
        * left. erewrite <- psunion_collect_free_list_spec'; eauto.
      + inv H1. erewrite map_nth'; eauto. 2:exact (Tenum (xH, 0), (Cbase, None)).
        rewrite PSUnion_In_app.
        destruct H14.
        * right. erewrite psunion_collect_free_list_spec'; eauto.
        * left. eapply psunion_collect_free_list_spec'; eauto.
  Qed.

  Corollary collect_free_left_list_spec {prefs} : forall (G: @global prefs) es x k,
      Forall (wl_exp G) es ->
      PS.In x (List.nth k (collect_free_left_list es) PS.empty) <->
      Is_free_left_list x k es.
  Proof.
    intros * Hwl.
    eapply collect_free_left_list_spec'; eauto.
    eapply Forall_impl; eauto; intros.
    eapply collect_free_left_spec; eauto.
  Qed.

  Hint Constructors Is_free_in_clock.

  Lemma collect_free_clock_spec : forall ck x,
      PS.In x (collect_free_clock ck) <->
      Is_free_in_clock x ck.
  Proof.
    induction ck; intros x; simpl; (split; [intros H|intros H; inv H]).
    - exfalso. apply not_In_empty in H; auto.
    - apply PSF.add_iff in H as [?|?]; subst; auto.
      right. rewrite <- IHck; auto.
    - apply PSF.add_1; auto.
    - apply PSF.add_2. rewrite IHck; auto.
  Qed.

  Fact wl_node_vars_defined {prefs} : forall (G: @global prefs) n,
      wl_node G n ->
      map fst (flat_map (fun '(xs, es) => combine xs (collect_free_left_list es)) (n_eqs n)) =
      vars_defined (n_eqs n).
  Proof.
    intros * Hwl.
    induction Hwl; simpl; auto.
    destruct x as [xs es].
    rewrite map_app, IHHwl. f_equal; auto; simpl.
    apply combine_map_fst'; auto.
    inv H. erewrite collect_free_left_list_length; eauto.
  Qed.

  Lemma build_graph_dom {prefs} : forall (G: @global prefs) n,
      wl_node G n ->
      Env.dom (build_graph n) (idents (n_in n ++ n_vars n ++ n_out n)).
  Proof.
    intros * Hwl. unfold idents, build_graph.
    eapply Env.dom_intro. intros x.
    rewrite Env.Props.P.F.mapi_in_iff.
    rewrite Env.In_from_list, fst_InMembers.
    repeat rewrite map_app. repeat rewrite map_map.
    rewrite Permutation_app_comm.
    erewrite map_ext with (g:=fst). 2:intros (?&?&?); auto.
    setoid_rewrite wl_node_vars_defined; eauto.
    rewrite n_defd, map_app. reflexivity.
  Qed.

  Corollary build_graph_Perm {prefs} : forall (G: @global prefs) n,
      wl_node G n ->
      Permutation (map fst (Env.elements (build_graph n))) (idents (n_in n ++ n_vars n ++ n_out n)).
  Proof.
    intros * Hwl.
    specialize (build_graph_dom _ _ Hwl) as Hdom1.
    specialize (Env.dom_elements (build_graph n)) as Hdom2.
    eapply Env.dom_Perm in Hdom1; eauto.
    - rewrite <- fst_NoDupMembers. apply Env.NoDupMembers_elements.
    - apply node_NoDup.
  Qed.

  Lemma build_graph_find {prefs} : forall (G: @global prefs) n x y,
      wl_node G n ->
      depends_on_ck (idck (n_in n ++ n_vars n ++ n_out n)) (n_eqs n) x y ->
      exists ys, (Env.find x (build_graph n)) = Some ys /\ PS.In y ys.
  Proof.
    intros * Hwl Hdep.
    specialize (build_graph_dom G n Hwl) as Hdom.
    eapply Env.dom_use with (x0:=x) in Hdom.
    rewrite Env.In_find in Hdom. symmetry in Hdom.
    destruct Hdep as [Hdep|(ck&Hin&Hfree)].
    - apply Exists_exists in Hdep as ((xs&es)&Hin&k&Hnth&Hfree).
      assert (In x (map fst (n_in n ++ n_vars n ++ n_out n))) as Hin'.
      { rewrite map_app. apply in_or_app; right.
        rewrite <- n_defd. unfold vars_defined.
        rewrite flat_map_concat_map. eapply in_concat'; eauto; subst.
        + eapply nth_error_In; eauto.
        + eapply in_map_iff. exists (xs, es); auto.
      }
      apply Hdom in Hin' as (?&Hfind). clear Hdom.
      eexists; split; eauto.
      unfold build_graph in Hfind.
      rewrite FMapPositive.PositiveMap.gmapi in Hfind.
      apply option_map_inv_Some in Hfind as (?&Hfind&?).
      erewrite Env.find_In_from_list with (v:=List.nth k (collect_free_left_list es) PS.empty) in Hfind.
      + eapply Forall_forall in Hwl; eauto. inv Hwl.
        inv Hfind. destruct find as [(?&?&?)|]. apply PSF.union_2.
        1,2:eapply collect_free_left_list_spec; eauto.
      + apply in_or_app; left. rewrite in_flat_map.
        eexists; split; eauto; simpl.
        assert (Datatypes.length xs = Datatypes.length (collect_free_left_list es)) as Hlen.
      { eapply Forall_forall in Hwl; eauto. inv Hwl.
        erewrite collect_free_left_list_length; eauto. }
      assert (k < Datatypes.length xs) by (apply nth_error_Some, not_None_is_Some; eauto).
      eapply (nth_error_nth _ _ _ xH) in Hnth as <-.
      rewrite <- combine_nth; auto.
      eapply nth_In. rewrite combine_length, <- Hlen, PeanoNat.Nat.min_id; auto.
      + rewrite fst_NoDupMembers, map_app.
        erewrite wl_node_vars_defined; eauto.
        rewrite map_map. erewrite map_ext with (g:=fst). 2:intros (?&?&?); auto.
        rewrite Permutation_app_comm, n_defd, <- map_app.
        apply node_NoDup.
    - apply In_idck_exists in Hin as (ty&Hin).
      assert (In x (map fst (n_in n ++ n_vars n ++ n_out n))) as Hin'.
      { rewrite in_map_iff. exists (x, (ty, ck)); split; auto. }
      apply Hdom in Hin' as (?&Hfind).
      eexists; split; eauto.
      unfold build_graph in Hfind.
      rewrite FMapPositive.PositiveMap.gmapi in Hfind.
      apply option_map_inv_Some in Hfind as (?&Hfind&?).
      erewrite find_some' in H; eauto; simpl in *; subst.
      2:apply fst_NoDupMembers, node_NoDup.
      apply PSF.union_3. rewrite collect_free_clock_spec; auto.
  Qed.

  (** We prove that the [check_node_causality] function only succeeds if
      the node is indeed causal.
      This is a simple consequence of [build_graph_find] and [build_acyclic_graph_spec].
   *)
  Lemma check_node_causality_correct {prefs} : forall (G: @global prefs) n,
      wl_node G n ->
      check_node_causality n = OK tt ->
      node_causal n.
  Proof.
    intros * Hwl Hcheck.
    unfold check_node_causality in Hcheck.
    destruct (build_acyclic_graph _) eqn:Build; inv Hcheck.
    eapply build_acyclic_graph_spec in Build as (a&(Hv&Ha)&Graph).

    exists t. exists a. exists Graph. split.
    - intros x. rewrite <- Hv.
      apply build_graph_dom in Hwl.
      rewrite Env.Props.P.F.map_in_iff, (Hwl x), <- ps_from_list_ps_of_list, ps_from_list_In, map_fst_idck.
      reflexivity.
    - intros x y Hdep.
      apply Ha.
      eapply build_graph_find in Hwl as (ys & Find & In); eauto.
      exists (PSP.to_list ys).
      rewrite Env.Props.P.F.map_o, Find; split; auto.
      apply In_PS_elements; auto.
  Qed.

  Corollary check_causality_correct {prefs} : forall (G: @global prefs) tts,
      wl_global G ->
      check_causality G = OK tts ->
      Forall node_causal (nodes G).
  Proof.
    unfold wl_global, CommonTyping.wt_program, CommonProgram.units, check_causality; simpl.
    intros G.
    induction (nodes G); intros * Hwl Hcheck; auto.
    inv Hwl.
    unfold check_causality in Hcheck; simpl in Hcheck.
    apply bind_inversion in Hcheck as [? [? Hcheck]].
    constructor.
    + destruct x. destruct H1. eapply check_node_causality_correct in H; eauto.
    + apply bind_inversion in Hcheck as [? [? Hcheck]]; eauto.
  Qed.

  (** ** Induction tactic over a causal set of equations *)

  (** We can "follow" the [TopOrder] extracted from an [AcyGraph].
      This gives us an order over the variables of the node *)
  Lemma TopoOrder_inv {v a} : forall (g : AcyGraph v a) eqs x xs,
      (forall x y, depends_on eqs x y -> is_arc g y x) ->
      TopoOrder g (x::xs) ->
      In x (vars_defined eqs) ->
      Exists (fun '(xs', es) =>
                exists k, k < length xs' /\ nth k xs' xH = x /\
                          (forall y, Is_free_left_list y k es -> In y xs))
             eqs.
  Proof.
    intros * Hdep Hpref Hin.
    inversion_clear Hpref as [|?? (?&?&?) ?].
    unfold vars_defined in Hin.
    apply in_flat_map in Hin as [[xs' es] [Hin Hin']]; simpl in Hin'.
    eapply Exists_exists. exists (xs', es); split; eauto.
    apply In_nth with (d:=xH) in Hin' as [k [Hlen Hnth]].
    exists k. repeat split; auto.
    eapply nth_error_nth' with (d:=xH) in Hlen; subst x.
    intros y' Hfree.
    apply H1. left. apply Hdep. unfold depends_on.
    eapply Exists_exists. exists (xs', es); split; eauto.
  Qed.

  Section causal_ind.
    Context {prefs : PS.t}.
    Variable G : @global prefs.
    Variable n : @node prefs.

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
                                   -> (forall x, Is_free_left x k e -> P_var x)
                                   -> P_exp e k) es ->
        (forall x, Is_free_left_list x k es -> P_var x) ->
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

    Hypothesis EvarCase : forall x ann,
        P_var x ->
        P_exp (Evar x ann) 0.

    Hypothesis EunopCase : forall op e1 ann,
        P_exp e1 0 ->
        P_exp (Eunop op e1 ann) 0.

    Hypothesis EbinopCase : forall op e1 e2 ann,
        P_exp e1 0 ->
        P_exp e2 0 ->
        P_exp (Ebinop op e1 e2 ann) 0.

    (* We're reasoning on causality, so we only get the hypothesis on the lhs *)
    Hypothesis EfbyCase : forall e0s es er ann k,
        k < length ann ->
        P_exps e0s k ->
        (forall k, k < length (annots er) -> P_exps er k) ->
        P_exp (Efby e0s es er ann) k.

    Hypothesis EarrowCase : forall e0s es er ann k,
        k < length ann ->
        P_exps e0s k ->
        P_exps es k ->
        (forall k, k < length (annots er) -> P_exps er k) ->
        P_exp (Earrow e0s es er ann) k.

    Hypothesis EwhenCase : forall es x b ann k,
        k < length (fst ann) ->
        P_exps es k ->
        P_var x ->
        P_exp (Ewhen es x b ann) k.

    Hypothesis EmergeCase : forall x tx es ann k,
        k < length (fst ann) ->
        P_var x ->
        Forall (fun es => P_exps es k) es ->
        P_exp (Emerge (x, tx) es ann) k.

    Hypothesis EcaseCase : forall e es d ann k,
        k < length (fst ann) ->
        P_exp e 0 ->
        Forall (LiftO (P_exps d k) (fun es => P_exps es k)) es ->
        P_exp (Ecase e es d ann) k.

    Hypothesis EappCase : forall f es er ann k,
        k < length ann ->
        (forall k, k < length (annots es) -> P_exps es k) ->
        (forall k, k < length (annots er) -> P_exps er k) ->
        P_exp (Eapp f es er ann) k.

    (* Exp-level induction *)
    Fixpoint exp_causal_ind e {struct e} : forall k,
        wl_exp G e ->
        (forall x, Is_free_left x k e -> P_var x) ->
        k < numstreams e ->
        P_exp e k.
    Proof.
      Ltac solve_forall es :=
        match goal with
        | H: Forall (wl_exp _) es, Hind : forall e k, wl_exp _ e -> _ |- _ =>
          clear - Hind H;
          induction es; inv H; constructor; auto
        end.

      intros * Hwl Hfree Hnum; destruct e; inv Hwl; simpl in *.
      - (* const *)
        rewrite PeanoNat.Nat.lt_1_r in Hnum; subst.
        apply EconstCase.
      - (* enum *)
        rewrite PeanoNat.Nat.lt_1_r in Hnum; subst.
        apply EenumCase.
      - (* var *)
        rewrite PeanoNat.Nat.lt_1_r in Hnum; subst.
        apply EvarCase, Hfree. constructor.
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
          solve_forall l.
        + intros ? Len. eapply Pexp_Pexps; eauto.
          solve_forall l1.
          intros ? Free. eapply Hfree. constructor.
          right; split; auto.
          eapply Is_free_left_list_Exists in Free as (?&Ex); eauto.
      - (* arrow *)
        eapply EarrowCase; eauto.
        1,2:eapply Pexp_Pexps; eauto; try congruence.
        solve_forall l. solve_forall l0.
        intros ? Len. eapply Pexp_Pexps; eauto.
        solve_forall l1.
        intros ? Free. eapply Hfree. constructor.
        right; right; split; auto.
        eapply Is_free_left_list_Exists in Free as (?&Ex); eauto.
      - (* when *)
        apply EwhenCase; eauto.
        eapply Pexp_Pexps; eauto. 2:congruence.
        solve_forall l.
      - (* merge *)
        destruct p.
        apply EmergeCase; eauto.
        assert (forall x, Exists (fun es => Is_free_left_list x k es) l -> P_var x) as Hfree' by auto.
        clear Hfree H3.
        induction l; inv H4; inv H5; constructor; auto.
        eapply Pexp_Pexps; eauto. 2:congruence.
        solve_forall a.
      - (* case *)
        apply EcaseCase; eauto.
        + eapply exp_causal_ind; eauto. rewrite H4; auto.
        + assert (forall x, Exists (fun oes => exists es0 : list exp, oes = Some es0 /\ Is_free_left_list x k es0) l \/
                       Is_free_left_list x k l0 -> P_var x) as Hfree' by auto.
          clear Hfree H5.
          induction l as [|[|]]; constructor; simpl; auto.
          * eapply Pexp_Pexps; eauto.
            -- specialize (H7 _ (in_eq _ _)).
               clear - H7 exp_causal_ind. solve_forall l.
            -- intros. eapply Hfree'. left; left; eauto.
            -- rewrite H8; eauto with datatypes.
          * eapply IHl; eauto; intros; eauto with datatypes.
            eapply Hfree'. destruct H; auto.
          * eapply Pexp_Pexps; eauto. 2:congruence.
            clear - H9 exp_causal_ind. solve_forall l0.
          * eapply IHl; eauto; intros; eauto with datatypes.
            eapply Hfree'. destruct H; auto.
      - (* app *)
        apply EappCase; auto.
        + intros k' Hk'. eapply Pexp_Pexps; eauto.
          * solve_forall l.
          * intros ? Hfree'. eapply Hfree.
            constructor; eauto.
            eapply Is_free_left_list_Exists in Hfree' as [? ?]; eauto.
        + intros k' Hk'. eapply Pexp_Pexps; eauto.
          * solve_forall l0.
          * intros ? Hfree'. eapply Hfree.
            constructor; eauto.
            eapply Is_free_left_list_Exists in Hfree' as [? ?]; eauto.
    Qed.

    Hypothesis EqVars: forall xs es k,
        k < length xs ->
        In (xs, es) (n_eqs n) ->
        P_exps es k ->
        P_var (nth k xs xH).

    Hypothesis Inputs :
      Forall P_var (idents (n_in n)).

    Lemma causal_ind {v a} : forall (g : AcyGraph v a),
        Forall (wl_equation G) (n_eqs n) ->
        graph_of_node n g ->
        Forall P_var (PS.elements (vertices g)).
    Proof.
      intros * Hwl [Hv Ha].
      specialize (has_TopoOrder g) as (xs'&Heq&Hpre).
      rewrite Heq, <- PS_For_all_Forall, <- ps_from_list_ps_of_list, PS_For_all_Forall'.
      assert (incl xs' (idents (n_in n) ++ vars_defined (n_eqs n))) as Hincl.
      { rewrite Hv in Heq.
        repeat rewrite <- ps_from_list_ps_of_list in Heq.
        intros ? Hin. rewrite <- ps_from_list_In in *.
        rewrite <- Heq, map_fst_idck, map_app in Hin.
        rewrite n_defd. assumption. }
      clear Heq.
      induction xs'; auto.
      apply incl_cons' in Hincl as [HIn Hincl].
      assert (Forall P_var xs') as Hxs by (inv Hpre; auto).
      constructor; auto.
      apply in_app_or in HIn as [HIn|HIn].
      - (* a is in the inputs *)
        eapply Forall_forall; [|eauto]. apply Inputs.
      - (* a is in the lhs of an equation *)
        eapply TopoOrder_inv in Hpre; eauto.
        apply Exists_exists in Hpre as [(?&?) (?&k&Hk&Hnth&Hfree)]; subst.
        eapply EqVars; eauto.
        eapply Forall_forall in Hwl; eauto. inv Hwl.
        eapply Pexp_Pexps; eauto. 3:rewrite <- H1; auto.
        + eapply Forall_impl; eauto. intros.
          eapply exp_causal_ind; eauto.
        + intros. eapply Forall_forall in Hxs; eauto.
        + intros * Hdep.
          apply Ha. left; auto.
    Qed.

    Corollary node_causal_ind :
        wl_node G n ->
        node_causal n ->
        Forall P_var (map fst (n_in n ++ n_vars n ++ n_out n)).
    Proof.
      intros * Hwl (?&?&g&Hcaus).
      assert (Hvars:=Hcaus). eapply causal_ind in Hvars; eauto.
      destruct Hcaus as (Heq&_).
      rewrite <- PS_For_all_Forall in Hvars.
      rewrite <- PS_For_all_Forall', ps_from_list_ps_of_list, <- map_fst_idck, <- Heq; auto.
    Qed.

    (** Bonus : now that the induction is done, the property is true for
        any exp or equation *)
    Fact exp_causal_ind' : forall e,
        wl_node G n ->
        node_causal n ->

        wl_exp G e ->
        forall k,
          (forall x, Is_free_left x k e -> In x (idents (n_in n ++ n_vars n ++ n_out n))) ->
          (* wt_exp G (...) e is enough *)
          k < numstreams e ->
          P_exp e k.
    Proof.
      intros * Hwl Hcaus Hwl' ? Hfree Hk.
      eapply exp_causal_ind; eauto.
      intros.
      eapply node_causal_ind, Forall_forall in Hcaus; eauto.
    Qed.

  End causal_ind.

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
