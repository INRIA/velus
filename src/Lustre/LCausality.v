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
From Velus Require Import CheckGraph.
From Velus Require Import Lustre.LSyntax.

(** * Lustre causality *)

Module Type LCAUSALITY
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (Import Syn : LSYNTAX Ids Op).

  (** ** Causality definition *)

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
  | IFLfby : forall e0s es a k,
      Is_free_left_list x k e0s ->
      Is_free_left x k (Efby e0s es a)
  | IFLarrow : forall e0s es a k,
      Is_free_left_list x k e0s
      \/ Is_free_left_list x k es ->
      Is_free_left x k (Earrow e0s es a)
  | IFLwhen : forall es y b a k,
      (k < length (fst a) /\ x = y)
      \/ Is_free_left_list x k es ->
      Is_free_left x k (Ewhen es y b a)
  | IFLmerge : forall ets efs y a k,
      (k < length (fst a) /\ x = y)
      \/ Is_free_left_list x k ets
      \/ Is_free_left_list x k efs ->
      Is_free_left x k (Emerge y ets efs a)
  | IFLite : forall e ets efs a k,
      (k < length (fst a) /\ Is_free_left x 0 e)
      \/ Is_free_left_list x k ets
      \/ Is_free_left_list x k efs->
      Is_free_left x k (Eite e ets efs a)
  | IFLapp : forall f es a k,
      k < length a ->
      (exists k', Exists (Is_free_left x k') es) ->
      Is_free_left x k (Eapp f es None a)
  | IFLreset : forall f es r a k,
      k < length a ->
      (exists k', Exists (Is_free_left x k') es)
      \/ Is_free_left x 0 r ->
      Is_free_left x k (Eapp f es (Some r) a)

  with Is_free_left_list (x : ident) : nat -> list exp -> Prop :=
  | IFLLnow : forall k e es,
      k < numstreams e ->
      Is_free_left x k e ->
      Is_free_left_list x k (e::es)
  | IFLLlater : forall k e es,
      k >= numstreams e ->
      Is_free_left_list x (k-numstreams e) es ->
      Is_free_left_list x k (e::es).

  Hint Constructors Is_free_left Is_free_left_list.

  Definition depends_on (eqs : list equation) (x : ident) (y : ident) :=
    Exists (fun '(xs, es) => exists k, k < length xs /\
                               nth k xs xH = x /\
                               Is_free_left_list y k es) eqs.

  Inductive Is_causal (eqs : list equation) : list ident -> Prop :=
  | ICnil: Is_causal eqs []
  | ICcons: forall x xs,
      Is_causal eqs xs ->
      (forall y, depends_on eqs x y -> In y xs) ->
      Is_causal eqs (x::xs).
  Hint Constructors Is_causal.

  Definition node_causal (n : node) :=
    exists xs, Permutation xs (map fst (n_in n ++ n_vars n ++ n_out n))
          /\ Is_causal (n_eqs n) xs.

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

  Lemma Is_free_left_length : forall G e x k,
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
    - (* fby *) solve_forall2 H8 H.
    - (* arrow *)
      destruct H3. solve_forall2 H8 H. solve_forall2 H9 H0.
    - (* when *)
      rewrite map_length. destruct H2 as [[? ?]|?]; auto.
      solve_forall2 H7 H.
    - (* merge *)
      rewrite map_length. destruct H3 as [[? ?]|[?|?]]; auto.
      solve_forall2 H9 H. solve_forall2 H10 H0.
    - (* ite *)
      rewrite map_length. destruct H3 as [[? ?]|[?|?]]; auto.
      solve_forall2 H11 H. solve_forall2 H12 H0.
  Qed.

  Corollary Is_free_left_list_length : forall G es x k,
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

  Instance Is_causal_Proper:
    Proper (@Permutation equation ==> @eq (list ident) ==> iff)
           Is_causal.
  Proof.
    intros eqs eqs' Hperm ? xs Heq; subst.
    split; intros Hcaus; induction Hcaus; auto.
    - constructor; auto.
      intros y Hdep. apply H.
      unfold depends_on in *. rewrite Hperm; auto.
    - constructor; auto.
      intros y Hdep. apply H.
      unfold depends_on in *. rewrite <- Hperm; auto.
  Qed.

  Instance vars_defined_Proper:
    Proper (@Permutation equation ==> @Permutation ident)
           vars_defined.
  Proof.
    intros eqs eqs' Hperm; subst.
    unfold vars_defined. rewrite Hperm. reflexivity.
  Qed.

  Fact vars_defined_app : forall eqs1 eqs2,
      vars_defined (eqs1++eqs2) = vars_defined eqs1 ++ vars_defined eqs2.
  Proof.
    intros.
    unfold vars_defined. rewrite flat_map_app; auto.
  Qed.

  (** ** Causality check *)

  Fixpoint collect_free_left (e : exp) {struct e} : list PS.t :=
    let collect_free_left_list (es : list exp) := flat_map collect_free_left es in
    match e with
    | Econst _ => [PS.empty]
    | Evar id (_, (ck, _)) => [PS.singleton id]
    | Eunop _ e (_, (ck, _)) => (collect_free_left e)
    | Ebinop _ e1 e2 (_, (ck, _)) =>
      let ps1 := collect_free_left e1 in
      let ps2 := collect_free_left e2 in
      List.map (fun '(ps1, ps2) => PS.union ps1 ps2) (List.combine ps1 ps2)
    | Efby e0s _ _ => (collect_free_left_list e0s)
    | Earrow e0s es _ =>
      let ps1 := collect_free_left_list e0s in
      let ps2 := collect_free_left_list es in
      List.map (fun '(ps1, ps2) => PS.union ps1 ps2) (List.combine ps1 ps2)
    | Ewhen es id _ (_, (ck, _)) =>
      List.map (fun ps => PS.add id ps) (collect_free_left_list es)
    | Emerge id ets efs (_, (ck, _)) =>
      let ps1 := collect_free_left_list ets in
      let ps2 := collect_free_left_list efs in
      List.map (fun '(ps1, ps2) => PS.add id (PS.union ps1 ps2)) (List.combine ps1 ps2)
    | Eite e ets efs (_, (ck, _)) =>
      let ps0 := collect_free_left e in
      let ps1 := collect_free_left_list ets in
      let ps2 := collect_free_left_list efs in
      List.map (fun '(ps1, ps2) => PS.union (List.hd PS.empty ps0) (PS.union ps1 ps2)) (List.combine ps1 ps2)
    | Eapp _ es None a =>
      let ps := PSUnion (collect_free_left_list es) in
      List.map (fun _ => ps) a
    | Eapp _ es (Some r) a =>
      let ps := PSUnion (collect_free_left r ++ collect_free_left_list es) in
      List.map (fun _ => ps) a
    end.

  Definition collect_free_left_list (es : list exp) :=
    flat_map collect_free_left es.

  Definition build_graph (n : node) : Env.t (list positive) :=
    Env.from_list (flat_map (fun '(xs, es) =>
                               let frees := collect_free_left_list es in
                               List.combine xs (List.map PSP.to_list frees)) (n_eqs n)
                            ++ (map (fun '(x, _) => (x, [])) (n_in n))).

  Definition check_node_causality (n : node) :=
    if check_graph (build_graph n)
    then Errors.OK tt
    else Errors.Error (MSG "Causality error in node '" :: CTX (n_name n) :: msg "'").

  Definition check_causality (G : global) :=
    mmap check_node_causality G.

  Fact collect_free_left_list_length' : forall es,
      Forall (fun e => length (collect_free_left e) = length (annot e)) es ->
      length (collect_free_left_list es) = length (annots es).
  Proof.
    induction es; intros * Hf; inv Hf; simpl; auto.
    repeat rewrite app_length. f_equal; auto.
  Qed.

  Lemma collect_free_left_length : forall G e,
      wl_exp G e ->
      length (collect_free_left e) = length (annot e).
  Proof.
    Local Ltac solve_forall H :=
      eapply Forall_Forall in H; eauto;
      clear - H;
      eapply Forall_impl; eauto; intros ? [? ?]; auto.

    induction e using exp_ind2; intros Hwl; inv Hwl; simpl.
    - (* const *) reflexivity.
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
      setoid_rewrite collect_free_left_list_length'; auto.
      solve_forall H.
    - (* arrow *)
      rewrite map_length, combine_length.
      setoid_rewrite collect_free_left_list_length'.
      rewrite H7, H8. apply PeanoNat.Nat.min_id.
      solve_forall H. solve_forall H0.
    - (* when *)
      destruct nck. rewrite map_length, map_length.
      setoid_rewrite collect_free_left_list_length'; auto.
      solve_forall H.
    - (* merge *)
      destruct nck. rewrite map_length, map_length, combine_length.
      setoid_rewrite collect_free_left_list_length'.
      rewrite H8, H9. apply PeanoNat.Nat.min_id.
      solve_forall H. solve_forall H0.
    - (* ite *)
      destruct nck. rewrite map_length, map_length, combine_length.
      setoid_rewrite collect_free_left_list_length'.
      rewrite H10, H11. apply PeanoNat.Nat.min_id.
      solve_forall H. solve_forall H0.
    - (* app *) rewrite map_length; auto.
    - (* app (reset) *) rewrite map_length; auto.
  Qed.

  Corollary collect_free_left_list_length : forall G es,
      Forall (wl_exp G) es ->
      length (collect_free_left_list es) = length (annots es).
  Proof.
    intros * Hwl.
    eapply collect_free_left_list_length'.
    eapply Forall_impl; eauto. intros ? ?.
    eapply collect_free_left_length; eauto.
  Qed.

  Fact wl_node_vars_defined : forall G n,
      wl_node G n ->
      map fst (flat_map (fun '(xs, es) => combine xs (map PSP.to_list (collect_free_left_list es))) (n_eqs n)) =
      vars_defined (n_eqs n).
  Proof.
    intros * Hwl.
    induction Hwl; simpl; auto.
    destruct x as [xs es].
    rewrite map_app, IHHwl. f_equal; auto; simpl.
    apply combine_map_fst'; auto.
    inv H. erewrite map_length, collect_free_left_list_length; eauto.
  Qed.

  Lemma build_graph_dom : forall G n,
      wl_node G n ->
      Env.dom (build_graph n) (map fst (n_in n ++ n_vars n ++ n_out n)).
  Proof.
    intros * Hwl. unfold build_graph.
    eapply Env.dom_Permutation.
    2:{ eapply Env.dom_from_list_map_fst; eauto.
        rewrite fst_NoDupMembers, map_app.
        setoid_rewrite wl_node_vars_defined; eauto. rewrite n_defd.
        replace (map fst (map (fun '(x, _) => (x, [])) (n_in n))) with (map fst (n_in n)).
        rewrite Permutation_app_comm.
        rewrite <- map_app. apply node_NoDup.
        rewrite map_map. eapply map_ext; intros [? ?]; auto.
    }
    repeat rewrite map_app. setoid_rewrite wl_node_vars_defined; eauto.
    rewrite (Permutation_app_comm (map _ (n_vars n))), n_defd, map_app, Permutation_app_comm, (Permutation_app_comm (map _ (n_out _))).
    eapply Permutation_app_head.
    replace (map fst (map (fun '(x, _) => (x, [])) (n_in n))) with (map fst (n_in n)); auto.
    rewrite map_map. eapply map_ext; intros [? ?]; auto.
  Qed.

  Corollary build_graph_Perm : forall G n,
      wl_node G n ->
      Permutation (map fst (Env.elements (build_graph n))) (map fst (n_in n ++ n_vars n ++ n_out n)).
  Proof.
    intros * Hwl.
    specialize (build_graph_dom _ _ Hwl) as Hdom1.
    specialize (Env.dom_elements (build_graph n)) as Hdom2.
    eapply Env.dom_Perm in Hdom1; eauto.
    - rewrite <- fst_NoDupMembers. apply Env.NoDupMembers_elements.
    - apply node_NoDup.
  Qed.

  Lemma build_graph_find' : forall G n,
      wl_node G n ->
      Forall (fun x => forall k xs es,
                  In (xs, es) (n_eqs n) ->
                  k < List.length xs ->
                  nth k xs xH = x ->
                  Env.find x (build_graph n) = Some (List.nth k (map PSP.to_list (collect_free_left_list es)) []))
             (map fst (n_in n ++ n_vars n ++ n_out n)).
  Proof.
    intros * Hwl.
    rewrite Forall_forall.
    intros ? Hx ? ? ? Heq Hk Hnth.
    unfold build_graph.
    eapply Env.find_In_from_list.
    2:{ rewrite fst_NoDupMembers, map_app.
        setoid_rewrite wl_node_vars_defined; eauto. rewrite n_defd.
        replace (map fst (map (fun '(x, _) => (x, [])) (n_in n))) with (map fst (n_in n)).
        rewrite Permutation_app_comm.
        rewrite <- map_app. apply node_NoDup.
        rewrite map_map. eapply map_ext; intros [? ?]; auto.
    }
    rewrite in_app_iff; left.
    rewrite in_flat_map. exists (xs, es); split; auto.
    assert (Datatypes.length xs = Datatypes.length (map PSP.to_list (collect_free_left_list es))) as Hlen.
    { eapply Forall_forall in Hwl; eauto. inv Hwl.
      erewrite map_length, collect_free_left_list_length; eauto. }
    rewrite <- Hnth, <- combine_nth; auto.
    eapply nth_In. rewrite combine_length, <- Hlen, PeanoNat.Nat.min_id; auto.
  Qed.

  Corollary collect_free_left_list_complete' : forall G es x k,
      Forall (wl_exp G) es ->
      Forall (fun e => forall x k, Is_free_left x k e -> PS.In x (List.nth k (collect_free_left e) PS.empty)) es ->
      Is_free_left_list x k es ->
      PS.In x (List.nth k (collect_free_left_list es) PS.empty).
  Proof.
    induction es; intros * Hwl Hf Hfree; inv Hwl; inv Hf. inv Hfree.
    assert (length (collect_free_left a) = numstreams a) as Hlen.
    { erewrite collect_free_left_length, length_annot_numstreams; eauto. }
    inv Hfree; simpl.
    - rewrite app_nth1; eauto. congruence.
    - rewrite app_nth2; eauto.
      + eapply IHes; eauto. congruence.
      + congruence.
  Qed.

  Fact collect_free_left_complete : forall G e x k,
      wl_exp G e ->
      Is_free_left x k e ->
      PS.In x (List.nth k (collect_free_left e) PS.empty).
  Proof.
    Ltac solve_forall3 Hfree H :=
      eapply collect_free_left_list_complete' in Hfree; eauto;
      eapply Forall_Forall in H; eauto; eapply Forall_impl; eauto; intros ? [? ?] ? ? ?; auto.

    induction e using exp_ind2;
      (intros * Hwl Hfree;
       assert (Hk := Hfree); eapply Is_free_left_length in Hk; eauto;
       try destruct a as [ty [ck name]];
       inv Hfree; inv Hwl; simpl in *;
       try rewrite <- length_annot_numstreams in *).
    - (* var *)
      apply PSF.singleton_2; auto.
    - (* unop *) eauto.
    - (* binop *)
      erewrite <- collect_free_left_length in H7, H8; eauto.
      erewrite map_nth' with (d':=(PS.empty, PS.empty)).
      2:(rewrite combine_length; rewrite H7, H8, PeanoNat.Nat.min_id; eauto).
      rewrite combine_nth. 2:congruence.
      rewrite PS.union_spec. destruct H1; eauto.
    - (* fby *)
      eapply collect_free_left_list_complete'; eauto.
      solve_forall3 H3 H.
    - (* arrow *)
      erewrite <- collect_free_left_list_length in H8, H9; eauto.
      erewrite map_nth' with (d':=(PS.empty, PS.empty)).
      2:(rewrite combine_length; setoid_rewrite H8; setoid_rewrite H9; rewrite PeanoNat.Nat.min_id; eauto).
      rewrite combine_nth. 2:setoid_rewrite H8; setoid_rewrite H9; auto.
      rewrite PS.union_spec.
      destruct H3 as [Hfree|Hfree]. solve_forall3 Hfree H. solve_forall3 Hfree H0.
    - (* when *)
      rewrite map_length in Hk. erewrite <- collect_free_left_list_length in H8; eauto.
      erewrite map_nth' with (d':=PS.empty). 2:setoid_rewrite H8; auto.
      rewrite PS.add_spec. destruct H2 as [[? ?]|Hfree]; auto.
      solve_forall3 Hfree H.
    - (* merge *)
      rewrite map_length in Hk. erewrite <- collect_free_left_list_length in H10, H11; eauto.
      erewrite map_nth' with (d':=(PS.empty,PS.empty)).
      2:(rewrite combine_length; setoid_rewrite H10; setoid_rewrite H11; rewrite PeanoNat.Nat.min_id; eauto).
      rewrite combine_nth. 2:setoid_rewrite H10; setoid_rewrite H11; auto.
      rewrite PS.add_spec, PS.union_spec.
      destruct H3 as [[? ?]|[Hfree|Hfree]]; auto. solve_forall3 Hfree H. solve_forall3 Hfree H0.
    - (* ite *)
      rewrite map_length in Hk. erewrite <- collect_free_left_list_length in H12, H13; eauto.
      erewrite map_nth' with (d':=(PS.empty,PS.empty)).
      2:(rewrite combine_length; setoid_rewrite H12; setoid_rewrite H13; rewrite PeanoNat.Nat.min_id; eauto).
      rewrite combine_nth. 2:setoid_rewrite H12; setoid_rewrite H13; auto.
      rewrite PS.union_spec, PS.union_spec.
      destruct H3 as [[? ?]|[Hfree|Hfree]]; auto. 2:solve_forall3 Hfree H. 2:solve_forall3 Hfree H0.
      left. eapply IHe in H2; eauto.
      destruct (collect_free_left e); auto.
    - (* app *)
      erewrite map_nth'; eauto. 2:exact (Op.bool_type, (Cbase, None)).
      destruct H7 as [k' Hex]. apply Exists_exists in Hex as [e [Hin Hfree]].
      eapply Forall_forall in H0; eauto. eapply Forall_forall in H5; eauto.
      specialize (H0 _ _ H5 Hfree).
      eapply In_In_PSUnion; eauto.
      rewrite flat_map_concat_map. eapply incl_concat_map; eauto.
      eapply nth_In. erewrite collect_free_left_length; eauto.
      eapply Is_free_left_length in Hfree; eauto.
    - (* app (reset) *)
      erewrite map_nth'; eauto. 2:exact (Op.bool_type, (Cbase, None)).
      rewrite PSUnion_In_app.
      destruct H7 as [[k' Hex]|Hex].
      + right. apply Exists_exists in Hex as [e [Hin Hfree]].
        eapply Forall_forall in H0; eauto. eapply Forall_forall in H8; eauto.
        specialize (H0 _ _ H8 Hfree).
        eapply In_In_PSUnion; eauto.
        rewrite flat_map_concat_map. eapply incl_concat_map; eauto.
        eapply nth_In. erewrite collect_free_left_length; eauto.
        eapply Is_free_left_length in Hfree; eauto.
      + left. assert (Hfree:=Hex). eapply H in Hex; eauto.
        eapply In_In_PSUnion; eauto.
        eapply nth_In. erewrite collect_free_left_length; eauto.
        eapply Is_free_left_length; eauto.
  Qed.

  Corollary collect_free_left_list_complete : forall G es x k,
      Forall (wl_exp G) es ->
      Is_free_left_list x k es ->
      PS.In x (List.nth k (collect_free_left_list es) PS.empty).
  Proof.
    intros * Hwl Hfree.
    eapply collect_free_left_list_complete'; eauto.
    eapply Forall_impl; eauto; intros.
    eapply collect_free_left_complete; eauto.
  Qed.

  Lemma build_graph_find : forall G n,
      wl_node G n ->
      Forall (fun x => forall y ys,
                  depends_on (n_eqs n) x y ->
                  (Env.find x (build_graph n)) = Some ys ->
                  In y ys) (map fst (n_in n ++ n_vars n ++ n_out n)).
  Proof.
    intros * Hwl.
    specialize (build_graph_find' _ _ Hwl) as Hfind'.
    eapply Forall_impl; eauto; clear Hfind'.
    intros ? Hfind ? ? Hdep Hfind'; simpl in *.
    unfold depends_on in Hdep.
    apply Exists_exists in Hdep as [[? ?] [Hin [k [Hk [Hnth Hfree]]]]].
    specialize (Hfind _ _ _ Hin Hk Hnth).
    rewrite Hfind in Hfind'. inv Hfind'.
    eapply Forall_forall in Hwl; eauto. inv Hwl.
    eapply collect_free_left_list_complete in Hfree; eauto.
    erewrite map_nth' with (d':=PS.empty). 2:erewrite collect_free_left_list_length, <- H0; eauto.
    rewrite In_PS_elements; auto.
  Qed.

  Fact WellOrdered_Is_causal : forall graph eqs xs,
      Forall (fun x => forall y ys,
                  depends_on eqs x y ->
                  (Env.find x graph) = Some ys ->
                  In y ys) xs ->
      WellOrdered graph xs ->
      Is_causal eqs xs.
  Proof.
    intros * Hconn Hord.
    induction xs; inv Hord; inv Hconn; constructor; auto.
  Qed.

  Lemma check_node_causality_correct : forall G n,
      wl_node G n ->
      check_node_causality n = OK tt ->
      node_causal n.
  Proof.
    intros * Hwl Hcheck.
    unfold check_node_causality in Hcheck.
    destruct (check_graph _) eqn:Hcheck'; inv Hcheck.
    eapply check_graph_spec in Hcheck' as [xs [Hperm Hord]].
    assert (Permutation xs (map fst (n_in n ++ n_vars n ++ n_out n))) as Hperm'.
    { rewrite <- Hperm. eapply build_graph_Perm; eauto. }
    exists xs. split; auto.
    eapply WellOrdered_Is_causal; eauto.
    rewrite Hperm'.
    eapply build_graph_find; eauto.
  Qed.

  Corollary check_causality_correct : forall G tts,
      wl_global G ->
      check_causality G = OK tts ->
      Forall node_causal G.
  Proof.
    induction G; intros * Hwl Hcheck; auto.
    inv Hwl.
    unfold check_causality in Hcheck; simpl in Hcheck.
    apply bind_inversion in Hcheck as [? [? Hcheck]].
    constructor.
    + destruct x. eapply check_node_causality_correct in H; eauto.
    + apply bind_inversion in Hcheck as [? [? Hcheck]]; eauto.
  Qed.

  (** *** Consequence of causality.
      We can "follow the trail" of variables *)

  Lemma Is_causal_inv : forall eqs x xs,
      Is_causal eqs (x::xs) ->
      In x (vars_defined eqs) ->
      Exists (fun '(xs', es) =>
                exists k, k < length xs' /\ nth k xs' xH = x /\
                     (forall y, Is_free_left_list y k es -> In y xs)
             ) eqs.
  Proof.
    intros * Hcaus Hin.
    inv Hcaus.
    unfold vars_defined in Hin.
    apply in_flat_map in Hin as [[xs' es] [Hin Hin']]; simpl in Hin'.
    eapply Exists_exists. exists (xs', es); split; eauto.
    apply In_nth with (d:=xH) in Hin' as [k [Hlen Hnth]].
    exists k. repeat split; auto.
    intros y Hfree.
    apply H2. unfold depends_on.
    eapply Exists_exists. exists (xs', es); split; eauto.
  Qed.

  (** ** Induction tactic over a causal set of equations *)

  Section causal_ind.
    Variable G : global.
    Variable n : node.

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
        Forall (fun e => forall k, k < numstreams e -> (forall x, Is_free_left x k e -> P_var x) -> P_exp e k) es ->
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
    Hypothesis EfbyCase : forall e0s es ann k,
        k < length ann ->
        P_exps e0s k ->
        P_exp (Efby e0s es ann) k.

    Hypothesis EarrowCase : forall e0s es ann k,
        k < length ann ->
        P_exps e0s k ->
        P_exps es k ->
        P_exp (Earrow e0s es ann) k.

    Hypothesis EwhenCase : forall es x b ann k,
        k < length (fst ann) ->
        P_exps es k ->
        P_var x ->
        P_exp (Ewhen es x b ann) k.

    Hypothesis EmergeCase : forall x ets efs ann k,
        k < length (fst ann) ->
        P_var x ->
        P_exps ets k ->
        P_exps efs k ->
        P_exp (Emerge x ets efs ann) k.

    Hypothesis EiteCase : forall e ets efs ann k,
        k < length (fst ann) ->
        P_exp e 0 ->
        P_exps ets k ->
        P_exps efs k ->
        P_exp (Eite e ets efs ann) k.

    Hypothesis EappCase : forall f es ann k,
        k < length ann ->
        (forall k, k < length (annots es) -> P_exps es k) ->
        P_exp (Eapp f es None ann) k.

    Hypothesis EappResetCase : forall f es er ann k,
        k < length ann ->
        (forall k, k < length (annots es) -> P_exps es k) ->
        P_exp er 0 ->
        P_exp (Eapp f es (Some er) ann) k.

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

      intros * Hwl Hfree Hnum; destruct e; try destruct o; inv Hwl; simpl in *.
      - (* const *)
        rewrite PeanoNat.Nat.lt_1_r in Hnum; subst.
        apply EconstCase.
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
        apply EfbyCase; eauto.
        eapply Pexp_Pexps; eauto. 2:congruence.
        solve_forall l.
      - (* arrow *)
        apply EarrowCase; eauto.
        1,2:eapply Pexp_Pexps; eauto. 2,4:congruence.
        solve_forall l. solve_forall l0.
      - (* when *)
        apply EwhenCase; eauto.
        eapply Pexp_Pexps; eauto. 2:congruence.
        solve_forall l.
      - (* merge *)
        apply EmergeCase; eauto.
        1,2:eapply Pexp_Pexps; eauto. 2,4:congruence.
        solve_forall l. solve_forall l0.
      - (* ite *)
        apply EiteCase; eauto.
        eapply exp_causal_ind; eauto. rewrite H7; auto.
        1,2:eapply Pexp_Pexps; eauto. 2,4:congruence.
        solve_forall l. solve_forall l0.
      - (* app (reset) *)
        apply EappResetCase; auto.
        + intros k' Hk'. eapply Pexp_Pexps; eauto.
          * solve_forall l.
          * intros ? Hfree'. eapply Hfree.
            constructor; eauto.
            eapply Is_free_left_list_Exists in Hfree' as [? ?]; eauto.
        + eapply exp_causal_ind; eauto.
          rewrite H6; auto.
      - (* app *)
        apply EappCase; auto.
        intros k' Hk'. eapply Pexp_Pexps; eauto.
        + solve_forall l.
        + intros ? Hfree'. eapply Hfree.
          constructor; eauto.
          eapply Is_free_left_list_Exists; eauto.
    Qed.

    Hypothesis EqVars: forall xs es k,
        k < length xs ->
        In (xs, es) (n_eqs n) ->
        P_exps es k ->
        P_var (nth k xs xH).

    Hypothesis Inputs :
      Forall P_var (map fst (n_in n)).

    Lemma causal_ind : forall xs,
        Forall (wl_equation G) (n_eqs n) ->
        incl xs (map fst (n_in n) ++ vars_defined (n_eqs n)) ->
        Is_causal (n_eqs n) xs ->
        Forall P_var xs.
    Proof.
      intros * Hwl Hincl Hcaus.
      induction xs; auto.
      apply incl_cons' in Hincl as [HIn Hincl].
      assert (Forall P_var xs) as Hxs by (inv Hcaus; auto).
      constructor; auto.
      apply in_app_or in HIn as [HIn|HIn].
      - (* a is in the inputs *)
        eapply Forall_forall; [|eauto]. apply Inputs.
      - (* a is in the lhs of an equation *)
        eapply Is_causal_inv in Hcaus; eauto.
        apply Exists_exists in Hcaus as [[xs' es] (?&k&Hk&Hnth&Hfree)]; subst.
        eapply EqVars; eauto.
        eapply Forall_forall in Hwl; eauto. inv Hwl.
        eapply Pexp_Pexps; eauto. 3:rewrite <- H1; auto.
        + eapply Forall_impl; eauto. intros.
          eapply exp_causal_ind; eauto.
        + intros. eapply Forall_forall in Hxs; eauto.
    Qed.

    Corollary node_causal_ind :
        wl_node G n ->
        node_causal n ->
        Forall P_var (map fst (n_in n ++ n_vars n ++ n_out n)).
    Proof.
      intros * Hwl Hcaus.
      destruct Hcaus as [xs [Hperm Hcaus]].
      eapply causal_ind in Hcaus; eauto.
      - rewrite <- Hperm; auto.
      - rewrite n_defd, <- map_app, Hperm. reflexivity.
    Qed.

    (** Bonus : now that the induction is done, this is true for any exp or equation *)

    Fact exp_causal_ind' : forall e,
        wl_node G n ->
        node_causal n ->

        wl_exp G e ->
        forall k,
          (forall x, Is_free_left x k e -> In x (map fst (n_in n ++ n_vars n ++ n_out n))) ->
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

Module LCausality
       (Ids  : IDS)
       (Op   : OPERATORS)
       (Syn  : LSYNTAX Ids Op)
       <: LCAUSALITY Ids Op Syn.
  Include LCAUSALITY Ids Op Syn.
End LCausality.
