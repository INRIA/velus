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

(**
  Causality judgement over a Lustre program
  *)

Module Type LCAUSALITY
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (Import Syn : LSYNTAX Ids Op).

  Inductive Is_free_left (x : ident) : exp -> Prop :=
  | IFLvar : forall a,
      Is_free_left x (Evar x a)
  | IFLunop : forall op e a,
      Is_free_left x e ->
      Is_free_left x (Eunop op e a)
  | IFLbinop : forall op e1 e2 a,
      Is_free_left x e1
      \/ Is_free_left x e2 ->
      Is_free_left x (Ebinop op e1 e2 a)
  | IFLfby : forall e0s es a,
      Exists (Is_free_left x) e0s ->
      Is_free_left x (Efby e0s es a)
  | IFLwhen : forall es y b a,
      x = y
      \/ Exists (Is_free_left x) es ->
      Is_free_left x (Ewhen es y b a)
  | IFLmerge : forall ets efs y a,
      x = y
      \/ Exists (Is_free_left x) ets
      \/ Exists (Is_free_left x) efs ->
      Is_free_left x (Emerge y ets efs a)
  | IFLite : forall e ets efs a,
      Is_free_left x e
      \/ Exists (Is_free_left x) ets
      \/ Exists (Is_free_left x) efs ->
      Is_free_left x (Eite e ets efs a)
  | IFLapp : forall f es a,
      Exists (Is_free_left x) es ->
      Is_free_left x (Eapp f es None a)
  | IFLreset : forall f es r a,
      Exists (Is_free_left x) (r :: es) ->
      Is_free_left x (Eapp f es (Some r) a).

  Inductive Is_causal (inputs : list ident) : list equation -> Prop :=
  | ICnil:
      Is_causal inputs []
  | ICcons: forall eq eqs,
      Is_causal inputs eqs ->
      (forall x, Exists (Is_free_left x) (snd eq) ->
            In x (vars_defined eqs) \/ In x inputs) ->
      Is_causal inputs (eq :: eqs).
  Hint Constructors Is_causal.

  (* TODO: link with check_graph_spec *)
  Definition node_causal (n : node) :=
    exists eqs, Permutation (n_eqs n) eqs
           /\ Is_causal (map fst (n_in n)) eqs.

  Instance Is_causal_Proper:
    Proper (@Permutation ident ==> @eq (list equation) ==> iff)
           Is_causal.
  Proof.
    intros xs xs' Hperm eqs eqs' Heq; subst.
    split; intros Hcaus; induction Hcaus; auto.
    - constructor; auto.
      intros x Hex. apply H in Hex as [?|Hex]; auto.
      right. rewrite <- Hperm; auto.
    - constructor; auto.
      intros x Hex. apply H in Hex as [?|Hex]; auto.
      right. rewrite Hperm; auto.
  Qed.

  Lemma Is_causal_incl : forall ins1 ins2 eqs,
      incl ins1 ins2 ->
      Is_causal ins1 eqs ->
      Is_causal ins2 eqs.
  Proof.
    induction eqs; intros Hincl Hcaus; inv Hcaus; auto.
    constructor; auto.
    intros ? Hex. apply H2 in Hex as [?|Hex]; auto.
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

  Lemma Is_causal_app1 : forall eqs eqs' ins,
      Is_causal ins (eqs ++ eqs') ->
      Is_causal (ins++vars_defined eqs') eqs.
  Proof.
    induction eqs; intros * Hcaus; simpl in *.
    - constructor.
    - inv Hcaus. eapply IHeqs in H1. constructor; auto.
      intros x Hex. apply H2 in Hex.
      rewrite vars_defined_app in Hex. rewrite in_app_iff in *.
      destruct Hex as [[?|?]|?]; auto.
  Qed.

  Lemma Is_causal_app2 : forall eqs eqs' ins,
      Is_causal ins eqs' ->
      Is_causal (ins++vars_defined eqs') eqs ->
      Is_causal ins (eqs ++ eqs').
  Proof.
    induction eqs; intros * Hcaus1 Hcaus2; simpl in *.
    - auto.
    - inv Hcaus2.
      constructor; auto.
      intros x Hex. apply H2 in Hex.
      rewrite vars_defined_app. rewrite in_app_iff in *.
      destruct Hex as [?|[?|?]]; auto.
  Qed.

  Lemma Is_causal_app : forall ins eqs1 eqs2,
      Is_causal ins eqs1 ->
      Is_causal ins eqs2 ->
      Is_causal ins (eqs1 ++ eqs2).
  Proof.
    intros * Hcaus1 Hcaus2.
    eapply Is_causal_app2; eauto.
    eapply Is_causal_incl; eauto.
    apply incl_appl, incl_refl.
  Qed.

  Lemma Forall_Is_causal : forall inputs eqs,
      Forall (fun '(_, es) => forall x, Exists (Is_free_left x) es -> In x inputs) eqs ->
      Is_causal inputs eqs.
  Proof.
    induction eqs; intros Hf; auto.
    inv Hf. constructor; auto.
    destruct a. intros x Hex; eauto.
  Qed.

  Lemma Is_causal_move_to_input : forall inputs eqs xs,
      Is_causal inputs eqs ->
      Is_causal (xs++inputs) (remove_member (list_eq_dec ident_eq_dec) xs eqs).
  Proof.
    induction eqs; intros * Hcaus; simpl in *; auto.
    destruct a as [xs' es']; simpl.
    destruct (list_eq_dec _ _ _); subst.
    - inv Hcaus; eauto.
    - inv Hcaus.
      constructor; simpl in *; auto.
      intros ? Hex. apply H2 in Hex.
      rewrite in_app_iff.
      destruct Hex as [Hin|?]; auto.
        unfold vars_defined in *. rewrite in_flat_map in *.
        destruct Hin as [[xs'' es''] [Hin1 Hin2]]; simpl in *.
        destruct (list_eq_dec ident_eq_dec xs xs''); subst; auto.
        left. exists (xs'', es''); split; auto.
        eapply remove_member_neq_In; auto.
  Qed.

  Corollary Is_causal_moves_to_input : forall inputs eqs xs,
      Is_causal inputs eqs ->
      Is_causal (xs++inputs) (remove_members (list_eq_dec ident_eq_dec) (map (fun x => [x]) xs) eqs).
  Proof.
    intros * Hcaus.
    unfold remove_members.
    rewrite <- fold_left_rev_right. eapply Is_causal_incl with (ins1 := (rev xs) ++ inputs).
    rewrite <- Permutation_rev; reflexivity.
    rewrite <- map_rev.
    remember (rev xs) as xs'. clear Heqxs'.
    induction xs'; simpl; auto.
    rewrite cons_is_app. eapply Is_causal_move_to_input; eauto.
  Qed.

  (** ** Causality check *)

  Fixpoint collect_free_left m (e : exp) : list ident :=
    let collect_free_lefts := flat_map (collect_free_left m) in
    match e with
    | Econst _ => []
    | Evar id (_, (ck, _)) => [m id]
    | Eunop _ e (_, (ck, _)) => (collect_free_left m e)
    | Ebinop _ e1 e2 (_, (ck, _)) => (collect_free_left m e1)++(collect_free_left m e2)
    | Efby e0s es anns =>
      (collect_free_lefts e0s)
    | Ewhen es id _ (_, (ck, _)) =>
      (m id)::(collect_free_lefts es)
    | Emerge id ets efs (_, (ck, _)) =>
      (m id)::(collect_free_lefts ets)++(collect_free_lefts efs)
    | Eite e ets efs (_, (ck, _)) =>
      (collect_free_left m e)++(collect_free_lefts ets)++(collect_free_lefts efs)
    | Eapp _ es None _ =>
      collect_free_lefts es
    | Eapp _ es (Some r) _ =>
      (collect_free_lefts es)++(collect_free_left m r)
    end.

  Definition collect_free_lefts m (es : list exp) : list positive :=
    (flat_map (collect_free_left m) es).

  Definition build_var_map' (eqs: list equation) : Env.t ident :=
    Env.adds' (flat_map (fun eq => match (fst eq) with
                                | [] => []
                                | hd::tl => map (fun x => (x, hd)) tl
                                end) eqs)
              (@Env.empty ident).

  Definition build_var_map (eqs : list equation) : (ident -> ident) :=
    fun x => match Env.find x (build_var_map' eqs) with
          | Some y => y
          | None => x
          end.

  Definition build_graph (n : node) : Env.t (list positive) :=
    let varmap := build_var_map (n_eqs n) in
    Env.from_list ((map_filter (fun eq =>
                                  let frees := collect_free_lefts varmap (snd eq) in
                                  match (fst eq) with
                                  | [] => None
                                  | hd::_ => Some (hd, frees)
                                  end) (n_eqs n))
                     ++(map (fun '(x, _) => (x, [])) (n_in n))).
    (* let inputenv := Env.adds (map fst (n_in n)) (map (fun _ => []) (n_in n)) (@Env.empty (list ident)) in *)
    (* fold_left (fun env eq => *)
    (*              let frees := collect_free_lefts varmap (snd eq) in *)
    (*              match (fst eq) with *)
    (*              | [] => env *)
    (*              | hd::_ => Env.add hd frees env *)
    (*              end) (n_eqs n) inputenv. *)

  Definition check_node_causality (n : node) :=
    if check_graph (build_graph n)
    then Errors.OK tt
    else Errors.Error (MSG "Causality error in node '" :: CTX (n_name n) :: msg "'").

  Definition check_causality (G : global) :=
    mmap check_node_causality G.

  Fact build_var_map_InMembers {B} : forall eqs (ins : list (ident * B)) x m,
      InMembers
        x (map_filter
             (fun eq : list ident * list exp =>
                match fst eq with
                | [] => None
                | hd :: _ => Some (hd, collect_free_lefts m (snd eq))
                end) eqs ++ List.map (fun '(x0, _) => (x0, [])) ins) ->
      In x (vars_defined eqs ++ map fst ins).
  Proof.
    intros * Hin.
    rewrite fst_InMembers, in_map_iff in Hin.
    destruct Hin as [[? ?] [? Hin]]; subst; simpl.
    rewrite in_app_iff in *. destruct Hin as [Hin|Hin].
    + left. eapply map_filter_In' in Hin as [[? ?] [? ?]]; simpl in *.
      destruct l0; inv H0.
      unfold vars_defined. rewrite in_flat_map. exists (i::l0, l1); simpl; auto.
    + right. rewrite in_map_iff in *. destruct Hin as [[x ?] [Hs Hin]]; inv Hs.
      exists (i, b); auto.
  Qed.


  Fact build_var_map_NoDupMembers {B} : forall eqs (ins : list (ident * B)) m,
      NoDup (vars_defined eqs ++ map fst ins) ->
      NoDupMembers
        (map_filter
           (fun eq : list ident * list exp =>
              match fst eq with
              | [] => None
              | hd :: _ => Some (hd, collect_free_lefts m (snd eq))
              end) eqs ++ List.map (fun '(x0, _) => (x0, [])) ins).
  Proof.
    induction eqs; intros * Hnd; simpl in *.
    + rewrite fst_NoDupMembers, map_map.
      erewrite map_ext; eauto. intros [? ?]; auto.
    + destruct a as [xs es]; simpl in *.
      rewrite <- app_assoc in Hnd.
      destruct xs; simpl; auto.
      constructor; auto.
      2:apply NoDup_app_r in Hnd; eauto.
      inv Hnd. apply not_In_app in H1 as [_ Hnin].
      intros Hin.
      eapply build_var_map_InMembers in Hin; auto.
  Qed.

  Lemma build_graph_dom : forall n xs,
      Forall2 (fun x eq => exists tl, fst eq = x::tl) xs (n_eqs n) ->
      Env.dom (build_graph n) (xs++(map fst (n_in n))).
  Proof.
    intros n. unfold build_graph.
    generalize (build_var_map (n_eqs n)) as map.
    specialize (in_vars_defined_NoDup n) as Hndup.
    destruct n; simpl in *; clear - n_nodup0 Hndup.
    assert (List.map fst (List.map (fun '(x, _) => (x, (@nil positive))) n_in0) = List.map fst n_in0) as Hfst.
    { rewrite map_map. apply map_ext.
      intros [? ?]; auto. }
    induction n_eqs0; intros * Hf; simpl in *.
    - inv Hf; simpl.
      eapply Env.dom_from_list_map_fst; auto.
      eapply NoDupMembers_app_l in n_nodup0.
      rewrite fst_NoDupMembers in n_nodup0. rewrite fst_NoDupMembers, Hfst; auto.
    - inv Hf. destruct H2 as [tl ?]. rewrite H; simpl.
      unfold Env.from_list in *. rewrite Env.adds'_cons.
      2:{ rewrite Permutation_swap, H in Hndup; simpl in Hndup.
          intro contra.
          eapply build_var_map_InMembers in contra.
          inv Hndup. apply not_In_app in H2 as [_ Hnin].
          apply Hnin. rewrite Permutation_app_comm; auto. }
      apply Env.dom_add_cons; auto.
      eapply IHn_eqs0; eauto.
      + unfold anon_in_eqs in n_nodup0; simpl in n_nodup0.
        rewrite (Permutation_app_comm (anon_in_eq _)) in n_nodup0.
        repeat rewrite app_assoc in *. apply NoDupMembers_app_l in n_nodup0; auto.
      + rewrite Permutation_swap in Hndup. apply NoDup_app_r in Hndup; auto.
  Qed.

  Lemma build_graph_find' : forall n x xs es,
      In (x::xs, es) (n_eqs n) ->
      Env.find x (build_graph n) = Some (collect_free_lefts (build_var_map (n_eqs n)) es).
  Proof.
    intros * Hin.
    unfold build_graph.
    eapply Env.find_In_from_list.
    2:{ clear - n.
        specialize (in_vars_defined_NoDup n) as Hndup.
        remember (n_in n) as ins. remember (n_eqs n) as eqs. clear - Hndup.
        rewrite Permutation_app_comm in Hndup.
        eapply build_var_map_NoDupMembers; eauto. }
    rewrite in_app_iff. left.
    eapply map_filter_In; eauto.
  Qed.

  Fact collect_free_left_complete : forall m e x,
      Is_free_left x e ->
      In (m x) (collect_free_left m e).
  Proof.
    induction e using exp_ind2; intros * Hfree; inv Hfree; simpl;
      try destruct a as [ty [ck name]];
      simpl; repeat rewrite in_app_iff.
    Local Ltac Forall_Exists_Exists H :=
        eapply Forall_Exists in H; [|eauto];
        rewrite in_flat_map';
        eapply Exists_Exists; [|eauto]; intros ? [? ?]; auto.
    - (* var *)
      left; auto.
    - (* unop *) auto.
    - (* binop *) destruct H0; auto.
    - (* fby *)
      Forall_Exists_Exists H2.
    - (* when *)
      destruct H1 as [Hex|Hex].
      + inv Hex. left; auto.
      + right. Forall_Exists_Exists Hex.
    - (* merge *)
      destruct H2 as [Hex|[Hex|Hex]].
      + inv Hex. left; auto.
      + right; left. Forall_Exists_Exists Hex.
      + right; right. Forall_Exists_Exists Hex.
    - (* ite *)
      destruct H2 as [Hex|[Hex|Hex]]; auto.
      + right; left. Forall_Exists_Exists Hex.
      + right; right. Forall_Exists_Exists Hex.
    - (* app *)
      Forall_Exists_Exists H2.
    - (* app (reset) *)
      inv H2; auto.
      left. Forall_Exists_Exists H3.
  Qed.

  Corollary collect_free_lefts_complete : forall m es x,
      Exists (Is_free_left x) es ->
      In (m x) (collect_free_lefts m es).
  Proof.
    intros * Hex.
    unfold collect_free_lefts. rewrite in_flat_map.
    eapply Exists_exists in Hex as [e [Hin Hfree]].
    exists e; split; auto.
    eapply collect_free_left_complete in Hfree; eauto.
  Qed.

  Lemma build_graph_find : forall n,
      Forall (fun '(xs, es) => forall x tl used,
                  xs = x::tl ->
                  Env.find x (build_graph n) = Some used ->
                  (forall x, Exists (Is_free_left x) es -> In (build_var_map (n_eqs n) x) used))
        ((map (fun '(x, _) => ([x], [])) (n_in n))++n_eqs n).
  Proof.
    intros n.
    apply Forall_app; split.
    - rewrite Forall_map.
      eapply Forall_forall. intros [? [? ?]] Hin * Heq Hfind ? Hex. inv Hex.
    - eapply Forall_forall. intros [? ?] Hin * ? Hfind ? Heqx; subst.
      eapply build_graph_find' in Hin.
      rewrite Hin in Hfind. inv Hfind.
      eapply collect_free_lefts_complete; eauto.
  Qed.

  Fact build_var_map_incl1 : forall eqs,
      forall x y, Env.find x (build_var_map' eqs) = Some y ->
             Exists (fun eq => In x (fst eq) /\ In y (fst eq)) eqs.
  Proof.
    induction eqs; intros * Hfind;
      unfold build_var_map' in Hfind; simpl in *.
    - rewrite Env.gempty in Hfind; congruence.
    - destruct a as [[|? xs] es]; simpl in Hfind. 1:right; eauto.
      rewrite <- Env.adds'_app in Hfind.
      eapply Env.find_adds'_In in Hfind as [Hin|Hfind]; eauto.
      + right. apply in_flat_map in Hin as [[xs' es'] [Hin1 Hin2]]; simpl.
        eapply Exists_exists. exists (xs', es'); split; auto; simpl in *.
        destruct xs'. inv Hin2.
        apply in_map_iff in Hin2 as [? [Hs Hin]]; inv Hs.
        simpl; auto.
      + eapply Env.find_adds'_In in Hfind as [Hin|Hfind].
        * left.
          apply in_map_iff in Hin as [? [Hs Hin]]; inv Hs.
          simpl; auto.
        * rewrite Env.gempty in Hfind; congruence.
  Qed.

  Lemma NoDup_vars_defined : forall eqs xs1 xs2 es1 es2 x,
      NoDup (vars_defined eqs) ->
      In (xs1, es1) eqs ->
      In (xs2, es2) eqs ->
      In x xs1 ->
      In x xs2 ->
      xs1 = xs2.
  Proof.
    induction eqs; intros * Hnd Hin1 Hin2 Hin3 Hin4.
    - inv Hin1.
    - inv Hin1; inv Hin2; auto; simpl in *. 2-3:exfalso.
      + inv H; auto.
      + eapply NoDup_app_In in Hnd; eauto.
        eapply Hnd. unfold vars_defined. rewrite in_flat_map. exists (xs2, es2); auto.
      + eapply NoDup_app_In in Hnd; eauto.
        eapply Hnd. unfold vars_defined. rewrite in_flat_map. exists (xs1, es1); auto.
      + eapply IHeqs; eauto. apply NoDup_app_r in Hnd; auto.
  Qed.

  Lemma build_var_map_incl2 : forall eqs,
      NoDup (vars_defined eqs) ->
      Forall (fun eq => forall x, In x (fst eq) <-> In (build_var_map eqs x) (fst eq)) eqs.
  Proof.
    intros eqs Hndup. unfold build_var_map.
    specialize (build_var_map_incl1 eqs) as Hf.
    eapply Forall_forall. intros [? ?] Hin1 ?; split; intros Hin2; simpl in *.
    - destruct (Env.find x _) eqn:Hfind; auto.
      eapply Hf, Exists_exists in Hfind as [[xs es] [Hi [Hi1 Hi2]]]; simpl in *.
      eapply NoDup_vars_defined in Hin2; eauto. inv Hin2; auto.
    - destruct (Env.find x _) eqn:Hfind; auto.
      eapply Hf, Exists_exists in Hfind as [[xs es] [Hi [Hi1 Hi2]]]; simpl in *.
      eapply NoDup_vars_defined in Hin2; eauto. inv Hin2; auto.
  Qed.

  Corollary build_var_map_vars_defined : forall eqs x,
      NoDup (vars_defined eqs) ->
      In x (vars_defined eqs) <-> In (build_var_map eqs x) (vars_defined eqs).
  Proof.
    intros * Hndup.
    eapply build_var_map_incl2 in Hndup.
    unfold vars_defined. repeat rewrite in_flat_map.
    split; intros [eq [Hin1 Hin2]];
      exists eq; split; auto;
      eapply Forall_forall in Hin1; eauto; simpl in Hin1.
    - rewrite <- Hin1; auto.
    - rewrite Hin1; auto.
  Qed.

  Fact build_var_map_id : forall eqs x,
      ~In x (vars_defined eqs) ->
      (build_var_map eqs x) = x.
  Proof.
    intros * Hnin.
    unfold build_var_map, build_var_map'.
    rewrite Env.gsso', Env.gempty; auto.
    rewrite fst_InMembers.
    intro contra; apply Hnin; clear Hnin.
    apply in_map_iff in contra as [[x' y] [? Hin]]; simpl in *; subst.
    unfold vars_defined.
    rewrite in_flat_map in *. destruct Hin as [[xs es] [Hin1 Hin2]].
    exists (xs, es); split; simpl in *; auto.
    destruct xs. inv Hin2.
    apply in_map_iff in Hin2 as [? [Hs ?]]; inv Hs.
    right; auto.
  Qed.

  Lemma build_var_map_incl : forall n,
      Forall (fun eq => forall x, In (build_var_map (n_eqs n) x) (fst eq) -> In x (fst eq))
             (n_eqs n ++ map (fun '(x, _) => ([x], [])) (n_in n)).
  Proof.
    intros n.
    specialize (in_vars_defined_NoDup n) as Hndup.
    eapply Forall_app; split.
    - apply NoDup_app_r in Hndup; auto.
      eapply build_var_map_incl2 in Hndup.
      eapply Forall_impl; eauto. intros; simpl in *. rewrite H; auto.
    - rewrite Forall_map. eapply Forall_forall. intros [? [? ?]] Hin ? Hin'; simpl in *.
      destruct Hin' as [Hin'|?]; auto.
      rewrite build_var_map_id in Hin'; auto.
      intro contra; subst.
      rewrite build_var_map_vars_defined in contra. 2:apply NoDup_app_r in Hndup; auto.
      eapply NoDup_app_In in Hndup; eauto.
      rewrite in_map_iff. eexists; split; eauto. auto.
  Qed.

  Fact m_vars_defined : forall m x eqs,
      Forall (fun eq => forall x, In (m x) (fst eq) -> In x (fst eq)) eqs ->
      In (m x) (vars_defined eqs) ->
      In x (vars_defined eqs).
  Proof.
    induction eqs; intros Hf Hin; simpl in *; try inv Hin.
    rewrite in_app_iff in *.
    inv Hf.
    destruct Hin as [Hin|?]; auto.
  Qed.

  Fact WellOrdered_Is_causal : forall graph m eqs xs,
      Forall2 (fun x equ => exists tl, fst equ = x::tl) xs eqs ->
      Forall (fun eq => forall x, In (m x) (fst eq) -> In x (fst eq)) eqs ->
      Forall (fun '(xs, es) => forall hd tl used,
                  xs = hd::tl ->
                  Env.find hd graph = Some used ->
                  (forall x, Exists (Is_free_left x) es -> In (m x) used)
             ) eqs ->
      WellOrdered graph xs ->
      Is_causal [] eqs.
  Proof.
    induction eqs; intros * Heq Hm Hf Hord; simpl in *; auto.
    destruct a as [xs' es]; simpl in *.
    inv Heq. inv Hm. inv Hf. inv Hord.
    constructor; simpl in *; eauto.
    intros ? Hex. left.
    destruct H2 as [tl ?]; subst.
    specialize (H5 _ _ _ eq_refl H7).
    apply H5, H8 in Hex.
    clear - Hex H3 H4.
    assert (In (m x0) (vars_defined eqs)) as Hin.
    { eapply Forall2_forall2 in H3 as [Hlen ?].
      eapply In_nth with (d:=x0) in Hex as [n [Hn Hnth]].
      specialize (H _ ([], []) _ _ _ Hn Hnth eq_refl) as [tl' Hnth2].
      setoid_rewrite Hlen in Hn. specialize (@nth_In _ n eqs ([], []) Hn) as Hin.
      destruct (nth n eqs _) as [xs' es']; simpl in Hnth2.
      unfold vars_defined. rewrite in_flat_map. exists (xs', es'); subst; simpl; split; auto. }
    eapply m_vars_defined; eauto.
  Qed.

End LCAUSALITY.

Module LCausality
       (Ids  : IDS)
       (Op   : OPERATORS)
       (Syn  : LSYNTAX Ids Op)
       <: LCAUSALITY Ids Op Syn.
  Include LCAUSALITY Ids Op Syn.
End LCausality.
