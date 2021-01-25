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

  Definition depends_on_ck vars (eqs : list equation) (x : ident) (y : ident) :=
    depends_on eqs x y \/ (exists ck, In (x, ck) vars /\ Is_free_in_clock y ck).

  Definition graph_of_eqs {v a} vars eqs (g : AcyGraph v a) : Prop :=
    PS.Equal (vertices g) (PSP.of_list (map fst vars)) /\
    (forall x y, depends_on_ck vars eqs x y -> is_arc g y x).

  Definition graph_of_node {v a} (n : node) (g : AcyGraph v a) : Prop :=
    graph_of_eqs (idck (n_in n ++ n_vars n ++ n_out n)) (n_eqs n) g.

  Definition node_causal (n : node) :=
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

  Fixpoint collect_free_clock (ck : clock) : PS.t :=
    match ck with
    | Cbase => PS.empty
    | Con ck x _ => (PS.add x (collect_free_clock ck))
    end.

  Definition build_graph (n : node) : Env.t PS.t :=
    let vo := flat_map (fun '(xs, es) =>
                                 let frees := collect_free_left_list es in
                                 List.combine xs frees) (n_eqs n) in
    let env := Env.from_list (vo ++ (map (fun '(x, (_, ck)) => (x, PS.empty)) (n_in n))) in
    Env.mapi (fun x deps => match List.find (fun '(x', _) => (x' =? x)%positive) (n_in n ++ n_vars n ++ n_out n) with
                         | Some (_, (_, ck)) => PS.union deps (collect_free_clock ck)
                         | None => deps
                         end) env.

  Open Scope error_monad_scope.

  Definition check_node_causality (n : node) : res unit :=
    match build_acyclic_graph (build_graph n) with
    | OK _ => OK tt
    | Error msg => Error (MSG "Node " :: (CTX (n_name n)) :: MSG " : " :: msg)
    end.

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

  Lemma collect_free_left_list_spec' : forall G es x k,
      Forall (wl_exp G) es ->
      Forall (fun e => forall k, wl_exp G e -> PS.In x (nth k (collect_free_left e) PS.empty) <-> Is_free_left x k e) es ->
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

  Lemma psunion_collect_free_list_spec' : forall G es x,
      Forall (wl_exp G) es ->
      Forall (fun e => forall k, wl_exp G e -> PS.In x (nth k (collect_free_left e) PS.empty) <-> Is_free_left x k e) es ->
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

  Fact collect_free_left_spec: forall G x e k,
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
      rewrite collect_free_left_list_spec'; eauto.
      split; intros; auto.
      inv H1; auto.
    - (* arrow *)
      split; intros.
      + specialize (ps_In_k_lt _ _ _ H1) as Hk. rewrite map_length in Hk.
        erewrite map_nth' with (d':=(PS.empty, PS.empty)) in H1; eauto.
        rewrite combine_nth in H1.
        2:(repeat erewrite collect_free_left_list_length; eauto; rewrite H7, H8; auto).
        rewrite PS.union_spec in H1. do 2 rewrite collect_free_left_list_spec' in H1; eauto.
      + erewrite <- collect_free_left_list_length in H7, H8; eauto.
        erewrite map_nth' with (d':=(PS.empty, PS.empty)).
        2:(erewrite <- map_length, Hlen2; eauto).
        rewrite combine_nth. 2:setoid_rewrite H7; setoid_rewrite H8; auto.
        rewrite PS.union_spec. repeat rewrite collect_free_left_list_spec'; eauto.
        inv H1; auto.
    - (* when *)
      split; intros.
      + specialize (ps_In_k_lt _ _ _ H0) as Hk. rewrite map_length in Hk.
        erewrite map_nth' with (d':=PS.empty) in H0; eauto.
        constructor.
        apply PS.add_spec in H0 as [?|?]; subst; simpl.
        * left; split; auto.
          erewrite collect_free_left_list_length in Hk; eauto.
          congruence.
        * right. rewrite <- collect_free_left_list_spec'; eauto.
      + erewrite <- collect_free_left_list_length in H7; eauto.
        erewrite map_nth' with (d':=PS.empty).
        2:(erewrite <- map_length, Hlen2; eapply Hlen1; eauto).
        inv H0. destruct H4 as [(_&?)|?]; subst.
        * apply PSF.add_1; auto.
        * apply PSF.add_2. erewrite collect_free_left_list_spec'; eauto.
    - (* merge *)
      split; intros.
      + specialize (ps_In_k_lt _ _ _ H1) as Hk. rewrite map_length in Hk.
        erewrite map_nth' with (d':=(PS.empty, PS.empty)) in H1; eauto.
        rewrite combine_nth in H1.
        2:(repeat erewrite collect_free_left_list_length; eauto; rewrite H9, H10; auto).
        rewrite PSF.add_iff, PS.union_spec in H1. do 2 rewrite collect_free_left_list_spec' in H1; eauto.
        constructor.
        destruct H1 as [?|?]; subst; auto.
        left; split; auto.
        erewrite <- map_length, Hlen2, map_length in Hk; auto.
      + erewrite <- collect_free_left_list_length in H9, H10; eauto.
        erewrite map_nth' with (d':=(PS.empty, PS.empty)).
        2:(erewrite <- map_length, Hlen2; eauto).
        rewrite combine_nth. 2:setoid_rewrite H9; setoid_rewrite H10; auto.
        rewrite PSF.add_iff, PS.union_spec. repeat rewrite collect_free_left_list_spec'; eauto.
        inv H1; auto. destruct H4 as [(_&?)|?]; auto.
    - (* ite *)
      split; intros.
      + specialize (ps_In_k_lt _ _ _ H1) as Hk. rewrite map_length in Hk.
        erewrite map_nth' with (d':=(PS.empty, PS.empty)) in H1; eauto.
        rewrite combine_nth in H1.
        2:(repeat erewrite collect_free_left_list_length; eauto; rewrite H11, H12; auto).
        repeat rewrite PS.union_spec in H1. do 2 rewrite collect_free_left_list_spec' in H1; eauto.
        constructor.
        destruct H1 as [?|?]; subst; auto.
        left; split; auto.
        erewrite <- map_length, Hlen2, map_length in Hk; auto.
        rewrite <- IHe; eauto. destruct (collect_free_left _); auto.
      + erewrite <- collect_free_left_list_length in H11, H12; eauto.
        erewrite map_nth' with (d':=(PS.empty, PS.empty)).
        2:(erewrite <- map_length, Hlen2; eauto).
        rewrite combine_nth. 2:setoid_rewrite H11; setoid_rewrite H12; auto.
        repeat rewrite PS.union_spec. repeat rewrite collect_free_left_list_spec'; eauto.
        inv H1; auto. destruct H4 as [(_&?)|?]; auto.
        left. rewrite <- IHe in H1; eauto.
        destruct (collect_free_left _); auto.
    - (* app *)
      split; intros.
      + assert (Hk:=H1). eapply ps_In_k_lt in Hk. rewrite map_length in Hk.
        erewrite map_nth' in H1; eauto. 2:exact (Op.bool_type, (Cbase, None)).
        constructor; auto.
        rewrite <- psunion_collect_free_list_spec'; eauto.
      + inv H1. erewrite map_nth'; eauto. 2:exact (Op.bool_type, (Cbase, None)).
        rewrite psunion_collect_free_list_spec'; eauto.
    - (* app (reset) *)
      split; intros.
      + assert (Hk:=H1). eapply ps_In_k_lt in Hk. rewrite map_length in Hk.
        erewrite map_nth' in H1; eauto. 2:exact (Op.bool_type, (Cbase, None)).
        constructor; auto.
        apply PSUnion_In_app in H1 as [?|?].
        * right. rewrite <- H; eauto.
          erewrite <- collect_free_left_length in H8; eauto.
          singleton_length. unfold PSUnion in H1; simpl in H1; auto.
        * left. rewrite <- psunion_collect_free_list_spec'; eauto.
      + inv H1. erewrite map_nth'; eauto. 2:exact (Op.bool_type, (Cbase, None)).
        rewrite PSUnion_In_app.
        destruct H14.
        * right. rewrite psunion_collect_free_list_spec'; eauto.
        * left. rewrite <- H in H1; eauto.
          eapply In_In_PSUnion; eauto.
          eapply nth_In. erewrite collect_free_left_length, H8; eauto.
  Qed.

  Corollary collect_free_left_list_spec : forall G es x k,
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

  Fact wl_node_vars_defined : forall G n,
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

  Lemma build_graph_dom : forall G n,
      wl_node G n ->
      Env.dom (build_graph n) (map fst (n_in n ++ n_vars n ++ n_out n)).
  Proof.
    intros * Hwl. unfold build_graph.
    eapply Env.dom_intro. intros x.
    rewrite Env.Props.P.F.mapi_in_iff.
    rewrite Env.In_from_list, fst_InMembers.
    repeat rewrite map_app. repeat rewrite map_map.
    rewrite Permutation_app_comm.
    erewrite map_ext with (g:=fst). 2:intros (?&?&?); auto.
    setoid_rewrite wl_node_vars_defined; eauto.
    rewrite n_defd, map_app. reflexivity.
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

  Fact find_some' : forall {A} (xs : list (ident * A)) x v ,
      NoDupMembers xs ->
      In (x, v) xs ->
      find (fun '(x', _) => (x' =? x)%positive) xs = Some (x, v).
  Proof.
    induction xs; intros * Hndup Hin; inv Hin; inv Hndup; simpl.
    - rewrite Pos.eqb_refl. reflexivity.
    - destruct (ident_eq_dec a0 x); subst.
      + apply In_InMembers in H. contradiction.
      + eapply Pos.eqb_neq in n. rewrite n; auto.
  Qed.

  Lemma build_graph_find : forall G n x y,
      wl_node G n ->
      depends_on_ck (idck (n_in n ++ n_vars n ++ n_out n)) (n_eqs n) x y ->
      exists ys, (Env.find x (build_graph n)) = Some ys /\ PS.In y ys.
  Proof.
    intros * Hwl Hdep.
    specialize (build_graph_dom G n Hwl) as Hdom.
    eapply Env.dom_use with (x0:=x) in Hdom.
    rewrite Env.In_find in Hdom. symmetry in Hdom.
    destruct Hdep as [Hdep|(ck&Hin&Hfree)].
    - apply Exists_exists in Hdep as ((xs&es)&Hin&k&Hk&Hnth&Hfree).
      assert (In x (map fst (n_in n ++ n_vars n ++ n_out n))) as Hin'.
      { rewrite map_app. apply in_or_app; right.
        rewrite <- n_defd. unfold vars_defined.
        rewrite flat_map_concat_map. eapply in_concat'; eauto; subst.
        + eapply nth_In; eauto.
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
      rewrite <- Hnth, <- combine_nth; auto.
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

  Lemma check_node_causality_correct : forall G n,
      wl_node G n ->
      check_node_causality n = OK tt ->
      node_causal n.
  Proof.
    intros * Hwl Hcheck.
    unfold check_node_causality in Hcheck.
    destruct (build_acyclic_graph _); inv Hcheck.
    destruct s as (v&a&g&(Hv&Ha)); simpl in *.
    exists v. exists a. exists g. split.
    - intros x. rewrite <- Hv.
      apply build_graph_dom in Hwl.
      rewrite (Hwl x), <- ps_from_list_ps_of_list, ps_from_list_In, map_fst_idck.
      reflexivity.
    - intros x y Hdep.
      apply Ha.
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

  Lemma Prefix_inv {v a} : forall (g : AcyGraph v a) eqs x xs,
      (forall x y, depends_on eqs x y -> is_arc g y x) ->
      Prefix g (x::xs) ->
      In x (vars_defined eqs) ->
      Exists (fun '(xs', es) =>
                exists k, k < length xs' /\ nth k xs' xH = x /\
                     (forall y, Is_free_left_list y k es -> In y xs)
             ) eqs.
  Proof.
    intros * Hdep Hpref Hin.
    inversion_clear Hpref as [|?? (?&?&?) ?].
    unfold vars_defined in Hin.
    apply in_flat_map in Hin as [[xs' es] [Hin Hin']]; simpl in Hin'.
    eapply Exists_exists. exists (xs', es); split; eauto.
    apply In_nth with (d:=xH) in Hin' as [k [Hlen Hnth]].
    exists k. repeat split; auto.
    intros y' Hfree.
    apply H1. left. apply Hdep. unfold depends_on.
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

    Lemma causal_ind {v a} : forall (g : AcyGraph v a),
        Forall (wl_equation G) (n_eqs n) ->
        graph_of_node n g ->
        Forall P_var (PS.elements (vertices g)).
    Proof.
      intros * Hwl [Hv Ha].
      specialize (has_Prefix g) as (xs'&Heq&Hpre).
      rewrite Heq, <- PS_For_all_Forall, <- ps_from_list_ps_of_list, PS_For_all_Forall'.
      assert (incl xs' (map fst (n_in n) ++ vars_defined (n_eqs n))) as Hincl.
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
        eapply Prefix_inv in Hpre; eauto.
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

  (** We can give a slightly stricter graph : there are arcs between two variables
      only and only if there is actually a dependency in the node *)
  Section strict_graph.

    Definition graph_of_eqs_strict {v a} vars eqs (g : AcyGraph v a) : Prop :=
      PS.Equal (vertices g) (PSP.of_list (map fst vars)) /\
      (forall x y, depends_on_ck vars eqs x y <-> is_arc g y x).

    (** Decidability of depends_on *)
    Fixpoint depends_on_eqb x y xs es n :=
      match n with
      | O => false
      | S n => orb (andb (ident_eqb x (nth n xs xH)) (PS.mem y (nth n (collect_free_left_list es) PS.empty)))
                  (depends_on_eqb x y xs es n)
      end.

    Fact lt_S_n_inv : forall m n,
        m < S n ->
        m = n \/ m < n.
    Proof.
      induction m; intros * Hlt.
      - destruct n; auto.
        right. apply PeanoNat.Nat.lt_0_succ.
      - apply Lt.lt_S_n in Hlt.
        assert (0 < n) as Hn0.
        { destruct n; auto. inv Hlt. apply PeanoNat.Nat.lt_0_succ. }
        rewrite Lt.S_pred_pos with (n:=n) in Hlt; auto.
        specialize (IHm _ Hlt) as [?|?]; subst.
        + left. rewrite <- Lt.S_pred_pos; auto.
        + right. rewrite PeanoNat.Nat.lt_succ_lt_pred; auto.
    Qed.

    Fact depends_on_eqb_spec : forall G x y xs es n,
        wl_equation G (xs, es) ->
        depends_on_eqb x y xs es n = true <->
        exists k, k < n /\ nth k xs xH = x /\ Is_free_left_list y k es.
    Proof.
      induction n; intros Hwl; simpl;
        (split; [intros Hdep|intros (k&Hn&Hnth&Hfree)]).
      - inv Hdep.
      - exfalso. apply OrdersEx.Nat_as_OT.nlt_0_r in Hn; auto.
      - rewrite Bool.orb_true_iff, Bool.andb_true_iff in Hdep.
        destruct Hdep as [(?&?)|?].
        + rewrite ident_eqb_eq in H.
          rewrite <- PSF.mem_iff, collect_free_left_list_spec in H0; eauto.
          inv Hwl; eauto.
        + apply IHn in H as (?&?&?&?); auto.
          exists x0. repeat split; auto.
      - rewrite Bool.orb_true_iff, Bool.andb_true_iff, IHn; auto.
        destruct (lt_S_n_inv _ _ Hn); subst.
        + left. rewrite ident_eqb_eq, <- PSF.mem_iff.
          split; auto.
          rewrite collect_free_left_list_spec; auto. inv Hwl; eauto.
        + right. exists k. repeat split; auto.
    Qed.

    Lemma Is_free_in_clock_dec : forall x ck,
        {Is_free_in_clock x ck} + {~Is_free_in_clock x ck}.
    Proof.
      induction ck; intros.
      - right. intro contra. inv contra.
      - destruct IHck.
        + left. right; auto.
        + destruct (ident_eq_dec x i); subst; auto.
          right. intro contra.
          inv contra; auto.
    Qed.

    Lemma depends_on_dec : forall G eqs,
        Forall (wl_equation G) eqs ->
        forall x y, {depends_on eqs x y} + {~depends_on eqs x y}.
    Proof.
      intros * Hwl *.
      unfold depends_on. eapply Exists_dec_In.
      intros (xs&es) Hin.
      eapply Forall_forall in Hwl; eauto.
      destruct (depends_on_eqb x y xs es (length xs)) eqn:Hdep.
      - left. rewrite depends_on_eqb_spec in Hdep; eauto.
      - right.
        intro contra. rewrite <- depends_on_eqb_spec in contra; eauto.
        congruence.
    Qed.

    Lemma in_map_fst {A B} : forall (l : list (A * B)) x,
        (forall (x y : A), {x = y} + {x <> y}) ->
        In x (map fst l) ->
        { y | In (x, y) l }.
    Proof.
      induction l as [|(?&?) ?]; intros * Hdec Hin; simpl in *.
      - inv Hin.
      - destruct (Hdec a x); subst; auto.
        + exists b; auto.
        + specialize (IHl x Hdec).
          destruct IHl as (?&?); eauto.
          inv Hin; auto. congruence.
    Qed.

    Corollary depends_on_ck_dec : forall G vars eqs,
        NoDupMembers vars ->
        Forall (wl_equation G) eqs ->
        forall x y, {depends_on_ck vars eqs x y} + {~depends_on_ck vars eqs x y}.
    Proof.
      intros * Hnd Hwl ??.
      destruct (depends_on_dec _ _ Hwl x y).
      - left. left. assumption.
      - destruct (in_dec ident_eq_dec x (map fst vars)).
        + apply in_map_fst in i as (ck&?). 2:apply ident_eq_dec.
          destruct (Is_free_in_clock_dec y ck).
          * left. right; eauto.
          * right. intro contra.
            inv contra; auto. destruct H as (?&Hin&?).
            eapply NoDupMembers_det in i; eauto; subst. eauto.
        + right. intro contra.
          inv contra; auto. destruct H as (?&Hin&?).
          eapply In_InMembers, fst_InMembers in Hin; eauto.
    Qed.

    Lemma graph_of_eqs_graph_of_eqs_strict : forall {v a} G vars eqs (g : AcyGraph v a),
        NoDupMembers vars ->
        Forall (wl_equation G) eqs ->
        graph_of_eqs vars eqs g ->
        exists a' (g' : AcyGraph v a'), graph_of_eqs_strict vars eqs g'.
    Proof.
      intros * Hnd Hwl (Hv&Ha).
      specialize (depends_on_ck_dec _ vars _ Hnd Hwl) as Hdec.

      (* First, we can produce a new arc_set with all the useless arcs removed *)
      remember (Env.mapi (fun x => PS.filter (fun y => if Hdec y x then true else false)) a) as a'.

      (* We can build an AcyGraph out of it *)
      assert (exists a'', (forall x y, has_arc a'' x y <-> has_arc a' x y) /\ AcyGraph v a'') as (a''&Heq&g'').
      { eapply subset_AcyGraph with (a':=a'); eauto.
        subst. intros x y (?&Hmap&Hin).
        apply Env.Props.P.F.mapi_inv in Hmap as (s&?&?&?&?); subst.
        apply PSF.filter_1 in Hin. 2:intros ???; subst; auto.
        exists s. auto.
      }
      exists a''. exists g''.

      (* Every necessary arc is inside a'' *)
      assert (forall x y, depends_on_ck vars eqs y x -> has_arc a'' x y) as Ha1.
      { intros * Hdep. rewrite Heq; subst.
        specialize (Ha _ _ Hdep) as (s&Hmap&Hin).
        eapply Env.mapi_1 in Hmap as (?&?&Hmap); subst.
        eexists; split; eauto; simpl.
        apply PSF.filter_3; auto. 1:intros ???; subst; auto.
        rewrite H. destruct Hdec; auto.
      }

      (* Every unnecessary arc has been removed from a'' *)
      assert (forall x y, has_arc a'' x y -> depends_on_ck vars eqs y x) as Ha2.
      { intros * Ha''. rewrite Heq in Ha''; subst.
        destruct Ha'' as (?&Hmap&Hin).
        apply Env.Props.P.F.mapi_inv in Hmap as (?&?&?&?&?); subst.
        apply PSF.filter_2 in Hin. 2:intros ???; subst; auto.
        destruct Hdec; auto. congruence.
      }

      split; auto. unfold is_arc.
      intros *; split; auto.
    Qed.

  End strict_graph.

End LCAUSALITY.

Module LCausalityFun
       (Ids  : IDS)
       (Op   : OPERATORS)
       (Syn  : LSYNTAX Ids Op)
       <: LCAUSALITY Ids Op Syn.
  Include LCAUSALITY Ids Op Syn.
End LCausalityFun.
