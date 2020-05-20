From Coq Require Import List Sorting.Permutation.
Import List.ListNotations.
Open Scope list_scope.

Require Import Omega.

From Velus Require Import Common Ident.
From Velus Require Import Operators.
From Velus Require Import Lustre.LSyntax Lustre.LOrdered Lustre.LTyping.
From Velus Require Import Lustre.Normalization.Fresh Lustre.Normalization.Normalization.

Local Set Warnings "-masking-absolute-name".
Module Type SPECIFICATION
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Import Syn : LSYNTAX Ids Op)
       (Import Norm : NORMALIZATION Ids Op OpAux Syn).

  Import Fresh Fresh.Fresh Facts Tactics.

  (** ** Specification of a normalized node *)

  Inductive normalized_lexp : exp -> Prop :=
  | normalized_Econst : forall c, normalized_lexp (Econst c)
  | normalized_Evar : forall x ty cl, normalized_lexp (Evar x (ty, cl))
  | normalized_Eunop : forall op e1 ty cl,
      normalized_lexp e1 ->
      normalized_lexp (Eunop op e1 (ty, cl))
  | normalized_Ebinop : forall op e1 e2 ty cl,
      normalized_lexp e1 ->
      normalized_lexp e2 ->
      normalized_lexp (Ebinop op e1 e2 (ty, cl))
  | normalized_Ewhen : forall e x b ty cl,
      normalized_lexp e ->
      normalized_lexp (Ewhen [e] x b ([ty], cl)).

  Inductive normalized_cexp : exp -> Prop :=
  | normalized_Emerge : forall x et ef ty cl,
      normalized_cexp et ->
      normalized_cexp ef ->
      normalized_cexp (Emerge x [et] [ef] ([ty], cl))
  | normalized_Eite : forall e et ef ty cl,
      normalized_lexp e ->
      normalized_cexp et ->
      normalized_cexp ef ->
      normalized_cexp (Eite e [et] [ef] ([ty], cl))
  | normalized_lexp_cexp : forall e,
      normalized_lexp e ->
      normalized_cexp e.

  Inductive is_constant : exp -> Prop :=
  | constant_Econst : forall c,
      is_constant (Econst c)
  | constant_Ewhen : forall e x b ty cl,
      is_constant e ->
      is_constant (Ewhen [e] x b ([ty], cl)).

  Inductive normalized_equation : PS.t -> equation -> Prop :=
  | normalized_eq_Eapp : forall out xs f es lann,
      Forall normalized_lexp es ->
      normalized_equation out (xs, [Eapp f es None lann])
  | normalized_eq_Eapp_reset : forall out xs f es x ty cl lann,
      Forall normalized_lexp es ->
      normalized_equation out (xs, [Eapp f es (Some (Evar x (ty, cl))) lann])
  | normalized_eq_Efby : forall out x e0 e ann,
      ~PS.In x out ->
      is_constant e0 ->
      normalized_lexp e ->
      normalized_equation out ([x], [Efby [e0] [e] [ann]])
  | normalized_eq_cexp : forall out x e,
      normalized_cexp e ->
      normalized_equation out ([x], [e]).

  Definition normalized_node (n : node) :=
    Forall (normalized_equation (ps_from_list (List.map fst (n_out n)))) (n_eqs n).

  Definition normalized_global (G : global) := Forall normalized_node G.

  Hint Constructors is_constant normalized_lexp normalized_cexp normalized_equation.

  (** A few initial properties *)

  Fact constant_normalized_lexp : forall e,
      is_constant e ->
      normalized_lexp e.
  Proof.
    intros e Hconst.
    induction Hconst; auto.
  Qed.

  Fact is_constant_numstreams : forall e,
      is_constant e ->
      numstreams e = 1.
  Proof.
    intros e Hconst; induction Hconst; reflexivity.
  Qed.

  Fact normalized_lexp_numstreams : forall e,
      normalized_lexp e ->
      numstreams e = 1.
  Proof.
    induction e; intros Hnorm; inv Hnorm; reflexivity.
  Qed.

  Fact normalized_cexp_numstreams : forall e,
      normalized_cexp e ->
      numstreams e = 1.
  Proof.
    induction e; intros Hnorm; inv Hnorm;
      try apply normalized_lexp_numstreams in H; auto.
  Qed.

  (** ** Propagation of the weak_valid_after property *)

  Fact idents_for_anns_weak_valid : forall anns ids st st' out,
      idents_for_anns anns st = (ids, st') ->
      weak_valid_after st out ->
      weak_valid_after st' out.
  Proof.
    induction anns; intros ids st st' out Hids Hval;
      simpl in *; repeat inv_bind; auto.
    destruct a as [? [? ?]]. repeat inv_bind; eauto.
  Qed.
  Local Hint Resolve idents_for_anns_weak_valid.

  Fact idents_for_anns'_weak_valid : forall anns ids st st' out,
      idents_for_anns' anns st = (ids, st') ->
      weak_valid_after st out ->
      weak_valid_after st' out.
  Proof.
    induction anns; intros ids st st' out Hids Hval;
      simpl in *; repeat inv_bind; auto.
    destruct a as [? [? ?]]. destruct o; repeat inv_bind; [destruct x|]; eauto.
  Qed.
  Local Hint Resolve idents_for_anns'_weak_valid.

  Fact init_var_for_clock_weak_valid : forall nck id st st' out,
      init_var_for_clock nck st = (id, st') ->
      weak_valid_after st out ->
      weak_valid_after st' out.
  Proof.
    intros nck id st st' out Hinit Hval;
      unfold init_var_for_clock in Hinit.
    destruct find in Hinit.
    - destruct p; inv Hinit; auto.
    - destruct fresh_ident eqn:Hfresh.
      inv Hinit; eauto.
  Qed.
  Local Hint Resolve init_var_for_clock_weak_valid.

  Fact fby_iteexp_weak_valid : forall e0 e a e' eqs' st st' out,
      fby_iteexp e0 e a st = (e', eqs', st') ->
      weak_valid_after st out ->
      weak_valid_after st' out.
  Proof.
    intros e0 e [ty cl] e' eqs' st st' out Hfby Hval;
      unfold fby_iteexp in Hfby.
    destruct (Norm.is_constant e0); repeat inv_bind; eauto.
  Qed.
  Local Hint Resolve fby_iteexp_weak_valid.

  Fact normalize_fby_weak_valid : forall e0s es anns es' eqs' st st' out,
      normalize_fby e0s es anns st = (es', eqs', st') ->
      weak_valid_after st out ->
      weak_valid_after st' out.
  Proof.
    intros e0s es anns es' eqs' st st' out Hfby Hval;
      unfold normalize_fby in Hfby; repeat inv_bind.
    eapply map_bind2_weak_valid in H; eauto.
    eapply Forall_forall; intros [[? ?] [? ?]] Hin ? ? ? ? Hfby Hval'.
    eapply fby_iteexp_weak_valid in Hval'; eauto.
  Qed.
  Local Hint Resolve normalize_fby_weak_valid.

  Fact normalize_reset_weak_valid : forall e e' eqs' st st' out,
      normalize_reset e st = (e', eqs', st') ->
      weak_valid_after st out ->
      weak_valid_after st' out.
  Proof.
    intros e e' eqs' st st' out Hnorm Hval.
    specialize (normalize_reset_spec e) as [[? [? [? Hspec]]]|Hspec]; subst;
      rewrite Hspec in Hnorm; clear Hspec; repeat inv_bind; auto.
    destruct hd as [? [? ?]]. repeat inv_bind; eauto.
  Qed.

  Local Ltac solve_weak_valid :=
    match goal with
    | H : map_bind2 _ _ _ = (_, _, ?st) |- weak_valid_after ?st _ =>
      eapply map_bind2_weak_valid in H; eauto; solve_forall
    | H : normalize_fby _ _ _ _ = (_, _, ?st) |- weak_valid_after ?st _ =>
      eapply normalize_fby_weak_valid; eauto
    | H : normalize_reset _ _ = (_, _, ?st) |- weak_valid_after ?st _ =>
      eapply normalize_reset_weak_valid; eauto
    | H : idents_for_anns _ _ = (_, ?st) |- weak_valid_after ?st _ =>
      eapply idents_for_anns_weak_valid; eauto
    | H : idents_for_anns' _ _ = (_, ?st) |- weak_valid_after ?st _ =>
      eapply idents_for_anns'_weak_valid; eauto
    end.

  Fact normalize_exp_weak_valid : forall e is_control es' eqs' st st' out,
      normalize_exp is_control e st = (es', eqs', st') ->
      weak_valid_after st out ->
      weak_valid_after st' out.
  Proof with eauto.
    induction e using exp_ind2; intros is_control es' eqs' st st' out Hnorm Hval;
      simpl in *; repeat inv_bind...
    - (* fby *) repeat solve_weak_valid.
    - (* when *)
      destruct a; repeat inv_bind. repeat solve_weak_valid.
    - (* merge *)
      destruct a; repeat inv_bind.
      destruct is_control; repeat inv_bind; repeat solve_weak_valid.
    - (* ite *)
      destruct a; repeat inv_bind.
      destruct is_control; repeat inv_bind; repeat solve_weak_valid.
    - (* app *)
      destruct ro; repeat inv_bind; repeat solve_weak_valid.
      eapply H; eauto. repeat solve_weak_valid.
  Qed.
  Local Hint Resolve normalize_exp_weak_valid.

  Corollary normalize_exps_weak_valid : forall es es' eqs' st st' out,
      normalize_exps es st = (es', eqs', st') ->
      weak_valid_after st out ->
      weak_valid_after st' out.
  Proof with eauto.
    intros es es' eqs' st st' out Hnorm Hval.
    unfold normalize_exps in Hnorm; repeat inv_bind.
    eapply map_bind2_weak_valid in H; eauto.
    eapply Forall_forall; intros ? Hin ? ? ? ? Hnorm Hval'; eauto.
  Qed.
  Local Hint Resolve normalize_exps_weak_valid.

  Fact normalize_rhs_weak_valid : forall e keep_fby es' eqs' st st' out,
      normalize_rhs keep_fby e st = (es', eqs', st') ->
      weak_valid_after st out ->
      weak_valid_after st' out.
  Proof with eauto.
    destruct e; intros keep_fby es' eqs' st st' out Hnorm Hval;
      unfold normalize_rhs in Hnorm; eauto.
    - (* fby *) destruct keep_fby; eauto.
      repeat inv_bind. repeat solve_weak_valid.
    - (* app *)
      destruct o; repeat inv_bind; repeat solve_weak_valid.
      eapply normalize_exps_weak_valid; eauto.
  Qed.
  Hint Resolve normalize_rhs_weak_valid.

  Corollary normalize_rhss_weak_valid : forall es keep_fby es' eqs' st st' out,
      normalize_rhss keep_fby es st = (es', eqs', st') ->
      weak_valid_after st out ->
      weak_valid_after st' out.
  Proof with eauto.
    intros es keep_fby es' eqs' st st' out Hnorm Hval.
    unfold normalize_rhss in Hnorm; repeat inv_bind.
    eapply map_bind2_weak_valid in H; eauto.
    eapply Forall_forall; intros ? Hin ? ? ? ? Hnorm Hval'; eauto.
  Qed.
  Local Hint Resolve normalize_rhss_weak_valid.

  Fact normalize_equation_weak_valid : forall e to_cut eqs' st st' out,
      normalize_equation to_cut e st = (eqs', st') ->
      weak_valid_after st out ->
      weak_valid_after st' out.
  Proof with eauto.
    intros [xs es] to_cut eqs' st st' out Hnorm Hval;
      unfold normalize_equation in Hnorm; repeat inv_bind; eauto.
  Qed.
  Hint Resolve normalize_equation_weak_valid.

  (** ** Additional properties *)

  Fact idents_for_anns_weak_valid_nIn : forall anns ids st st' out,
      idents_for_anns anns st = (ids, st') ->
      weak_valid_after st out ->
      Forall (fun id => ~PS.In id out) (map fst ids).
  Proof.
    induction anns; intros ids st st' out Hids Hval;
      simpl in *; [|destruct a as [? [? ?]]]; repeat inv_bind; simpl; auto.
    constructor; eauto.
    eapply fresh_ident_weak_valid_nIn; eauto.
  Qed.

  (** ** After normalization, equations and expressions are normalized *)

  Fact normalized_lexp_hd_default : forall es,
      Forall normalized_lexp es ->
      normalized_lexp (hd_default es).
  Proof.
    intros es Hf.
    destruct es; simpl.
    - constructor.
    - inv Hf; auto.
  Qed.

  Fact map_bind2_normalized_lexp {A A2} :
    forall (k : A -> FreshAnn ((list exp) * A2)) a es' a2s st st',
      map_bind2 k a st = (es', a2s, st') ->
      Forall (fun a => forall es' a2s st st',
                  k a st = (es', a2s, st') ->
                  Forall normalized_lexp es') a ->
      Forall normalized_lexp (concat es').
  Proof.
    intros k a eqs' a2s st st' Hmap Hf.
    apply map_bind2_values in Hmap.
    induction Hmap; simpl in *.
    - constructor.
    - destruct H as [? [? H]]. inv Hf.
      rewrite Forall_app.
      split; eauto.
  Qed.

  Fact map_bind2_normalized_cexp {A A2} :
    forall (k : A -> FreshAnn ((list exp) * A2)) a es' a2s st st',
      map_bind2 k a st = (es', a2s, st') ->
      Forall (fun a => forall es' a2s st st',
                  k a st = (es', a2s, st') ->
                  Forall normalized_cexp es') a ->
      Forall normalized_cexp (concat es').
  Proof.
    intros k a eqs' a2s st st' Hmap Hf.
    apply map_bind2_values in Hmap.
    induction Hmap; simpl in *.
    - constructor.
    - destruct H as [? [? H]]. inv Hf.
      rewrite Forall_app.
      split; eauto.
  Qed.

  Fact add_whens_is_constant : forall ty cl e,
      is_constant e ->
      is_constant (add_whens e ty cl).
  Proof.
    induction cl; intros e Hcons; simpl.
    - assumption.
    - constructor. eauto.
  Qed.

  Fact add_whens_normalized_lexp : forall ty cl e,
      normalized_lexp e ->
      normalized_lexp (add_whens e ty cl).
  Proof.
    induction cl; intros e Hadd; simpl in Hadd.
    - assumption.
    - constructor. eauto.
  Qed.

  Hint Resolve in_combine_l in_combine_r.
  Hint Resolve normalized_lexp_hd_default.

  Fact is_constant_is_constant : forall e,
      Norm.is_constant e = true <->
      is_constant e.
  Proof with eauto.
    intros e. split; intros Hconst.
    - induction e using exp_ind2; simpl in Hconst; try congruence.
      + constructor.
      + repeat (destruct es; try congruence).
        inv H; inv H3.
        destruct a.
        repeat (destruct l; try congruence).
        constructor...
    - induction Hconst...
  Qed.

  Lemma normalize_exp_normalized_lexp : forall e es' eqs' st st',
      normalize_exp false e st = (es', eqs', st') ->
      Forall normalized_lexp es'.
  Proof with eauto.
    induction e using exp_ind2; intros es' eqs' st st' Hnorm;
      simpl in Hnorm; repeat inv_bind; repeat constructor.
    - (* var *)
      destruct a...
    - (* unop *)
      destruct a...
    - (* binop *)
      destruct a. constructor...
    - (* fby *)
      repeat rewrite_Forall_forall.
      repeat simpl_In. destruct a0...
    - (* when *)
      destruct a. repeat inv_bind.
      apply map_bind2_normalized_lexp in H0...
      repeat rewrite_Forall_forall.
      repeat simpl_In...
    - (* merge *)
      destruct a. repeat inv_bind.
      repeat rewrite_Forall_forall.
      repeat simpl_In. destruct a...
    - (* ite *)
      destruct a. repeat inv_bind.
      repeat rewrite_Forall_forall.
      repeat simpl_In. destruct a...
    - (* app *)
      repeat rewrite_Forall_forall.
      repeat simpl_In. destruct a0...
  Qed.
  Hint Resolve normalize_exp_normalized_lexp.

  Corollary normalize_exps_normalized_lexp: forall es es' eqs' st st',
      normalize_exps es st = (es', eqs', st') ->
      Forall normalized_lexp es'.
  Proof.
    intros es es' eqs' st st' Hnorm.
    unfold normalize_exps in Hnorm. repeat inv_bind.
    apply map_bind2_normalized_lexp in H; auto.
    rewrite Forall_forall; intros; eauto.
  Qed.
  Hint Resolve normalize_exps_normalized_lexp.

  Lemma normalize_exp_normalized_cexp : forall e es' eqs' st st',
      normalize_exp true e st = (es', eqs', st') ->
      Forall normalized_cexp es'.
  Proof with eauto.
    induction e using exp_ind2; intros es' eqs' st st' Hnorm;
      simpl in Hnorm; repeat inv_bind; repeat constructor.
    - (* var *)
      destruct a...
    - (* unop *)
      destruct a...
    - (* binop *)
      destruct a. constructor...
    - (* fby *)
      solve_forall.
      repeat simpl_In. destruct a0...
    - (* when *)
      destruct a. repeat inv_bind.
      apply map_bind2_normalized_lexp in H0; solve_forall.
      repeat rewrite_Forall_forall.
      repeat simpl_In...
    - (* merge *)
      destruct a. repeat inv_bind.
      apply map_bind2_normalized_cexp in H1; solve_forall.
      apply map_bind2_normalized_cexp in H2; solve_forall.
      repeat rewrite_Forall_forall.
      repeat simpl_In...
    - (* ite *)
      destruct a. repeat inv_bind.
      apply normalize_exp_normalized_lexp in H1.
      apply map_bind2_normalized_cexp in H2; solve_forall.
      apply map_bind2_normalized_cexp in H3; solve_forall.
      repeat rewrite_Forall_forall.
      repeat simpl_In.
      constructor...
      apply normalized_lexp_hd_default. solve_forall.
    - (* app *)
      solve_forall.
      repeat simpl_In. destruct a0...
  Qed.

  Fact init_var_for_clock_normalized_eq : forall cl id eqs' out st st',
      weak_valid_after st out ->
      init_var_for_clock cl st = (id, eqs', st') ->
      Forall (normalized_equation out) eqs'.
  Proof.
    intros cl id eqs' out st st' Hvalid Hinit.
    unfold init_var_for_clock in Hinit.
    destruct (find _ _).
    - destruct p. inv Hinit. constructor.
    - destruct (fresh_ident _ _) eqn:Hfresh. inv Hinit.
      repeat constructor.
      + eapply fresh_ident_weak_valid_nIn in Hfresh; eauto.
      + apply add_whens_is_constant. auto.
      + apply add_whens_normalized_lexp. auto.
  Qed.

  Fact fby_iteexp_normalized_eq : forall e0 e a e' eqs' out st st',
      weak_valid_after st out ->
      normalized_lexp e ->
      fby_iteexp e0 e a st = (e', eqs', st') ->
      Forall (normalized_equation out) eqs'.
  Proof.
    intros e0 e [ty cl] e' eqs' out st st' Hvalid He Hfby.
    unfold fby_iteexp in Hfby.
    destruct (Norm.is_constant e0); repeat inv_bind; constructor.
    - assert (weak_valid_after x1 out) as Hvalid' by eauto.
      constructor; auto.
      + eapply fresh_ident_weak_valid_nIn in H0; eauto.
      + eapply add_whens_is_constant; eauto.
    - eapply init_var_for_clock_normalized_eq in H; eauto.
  Qed.

  Fact map_bind2_normalized_eq {A A1} :
    forall (k : A -> FreshAnn (A1 * (list equation))) a out a1s eqs' st st',
      map_bind2 k a st = (a1s, eqs', st') ->
      weak_valid_after st out ->
      (forall a a1s eqs' st st', k a st = (a1s, eqs', st') ->
                            weak_valid_after st out ->
                            weak_valid_after st' out) ->
      Forall (fun a => forall a1s eqs' st st',
                  k a st = (a1s, eqs', st') ->
                  weak_valid_after st out ->
                  Forall (normalized_equation out) eqs') a ->
      Forall (normalized_equation out) (concat eqs').
  Proof.
    induction a; intros out a1s eqs' st st' Hmap Hlt Hfollows Hf;
      simpl in *; repeat inv_bind.
    - constructor.
    - inv Hf. simpl.
      rewrite Forall_app; eauto.
  Qed.

  Fact normalize_fby_normalized_eq : forall e0s es anns es' eqs' out st st',
      weak_valid_after st out ->
      Forall normalized_lexp es ->
      normalize_fby e0s es anns st = (es', eqs', st') ->
      Forall (normalized_equation out) eqs'.
  Proof with eauto.
    intros e0s es anns es' eqs' out st st' Hval Hf Hnorm.
    unfold normalize_fby in Hnorm.
    repeat inv_bind.
    - eapply map_bind2_normalized_eq...
      + intros. destruct a as [[e0 e] [ty cl]]...
      + rewrite Forall_forall; intros.
        destruct x as [[e0 e] [ty cl]].
        eapply fby_iteexp_normalized_eq in H1...
        rewrite Forall_forall in Hf...
  Qed.

  Lemma normalize_exp_normalized_eq : forall e is_control es' eqs' out st st',
      weak_valid_after st out ->
      normalize_exp is_control e st = (es', eqs', st') ->
      Forall (normalized_equation out) eqs'.
  Proof with eauto.
    induction e using exp_ind2; intros is_control es' eqs' out st st' Hval Hnorm;
      simpl in Hnorm; repeat inv_bind; repeat constructor; eauto.
    - (* binop *)
      apply Forall_app. split...
    - (* fby *)
      assert (weak_valid_after x1 out) as Hvalid1 by solve_weak_valid.
      assert (weak_valid_after x4 out) as Hvalid2 by solve_weak_valid.
      assert (weak_valid_after x7 out) as Hvalid3 by solve_weak_valid.
      repeat rewrite Forall_app. repeat split.
      + apply map_bind2_normalized_lexp in H1; [| solve_forall].
        apply map_bind2_normalized_lexp in H2; [| solve_forall].
        clear H H0.
        unfold normalize_fby in H3; repeat inv_bind. apply map_bind2_values in H.
        repeat rewrite_Forall_forall.
        repeat simpl_In.
        apply In_nth with (d:=(hd_default [])) in H6; destruct H6 as [n [? ?]].
        replace (length x5) in H6.
        specialize (H3 (e, e, a0) (hd_default []) [] _ _ _ _ H6 eq_refl eq_refl eq_refl). destruct H3 as [? [? H3]].
        destruct (nth n _) as [[e0 e'] [ty cl]] eqn:Hnth.
        unfold fby_iteexp in H3.
        destruct (Norm.is_constant e0) eqn:Hisconst; repeat inv_bind.
        * simpl in *. rewrite <- H9. repeat constructor.
          -- intro contra.
             eapply idents_for_anns_weak_valid_nIn in H4...
             rewrite Forall_forall in H4. apply H4 in contra; auto.
             rewrite in_map_iff. exists (i, a0); auto.
          -- rewrite is_constant_is_constant in Hisconst...
          -- eapply nth_In in H6; rewrite Hnth in H6...
        * simpl. rewrite <- H11. repeat constructor.
          eapply nth_In in H6; rewrite Hnth in H6...
      + eapply map_bind2_normalized_eq in H1... solve_forall.
      + eapply map_bind2_normalized_eq in H2...
        * eapply map_bind2_st_follows in H1; solve_forall.
      + eapply normalize_fby_normalized_eq in H3; eauto.
        eapply map_bind2_normalized_lexp; eauto. solve_forall.
    - (* when *)
      destruct a. repeat inv_bind.
      eapply map_bind2_normalized_eq in H0; eauto. solve_forall.
    - (* merge *)
      destruct a; destruct is_control; repeat inv_bind;
        repeat rewrite Forall_app; repeat split.
      1,2,4,5: (eapply map_bind2_normalized_eq; eauto; solve_forall).
      1,2: solve_weak_valid.
      rewrite Forall_forall; intros [? ?] Hin. rewrite map_map in Hin; simpl in Hin.
      repeat simpl_In.
      constructor. constructor.
      + eapply map_bind2_normalized_cexp in H1; eauto; solve_forall.
        rewrite Forall_forall in H1...
        eapply normalize_exp_normalized_cexp...
      + eapply map_bind2_normalized_cexp in H2; eauto; solve_forall.
        rewrite Forall_forall in H2...
        eapply normalize_exp_normalized_cexp...
    - (* ite *)
      destruct a; destruct is_control; repeat inv_bind;
        repeat rewrite Forall_app; repeat split.
      1,5: (eapply IHe; eauto).
      1,2,4,5: (eapply map_bind2_normalized_eq; eauto; solve_forall).
      1,2: solve_weak_valid.
      rewrite Forall_forall; intros [? ?] Hin. rewrite map_map in Hin; simpl in Hin.
      repeat simpl_In.
      constructor. constructor.
      + eapply normalized_lexp_hd_default.
        eapply normalize_exp_normalized_lexp...
      + eapply map_bind2_normalized_cexp in H2; eauto; solve_forall.
        rewrite Forall_forall in H2...
        eapply normalize_exp_normalized_cexp...
      + eapply map_bind2_normalized_cexp in H3; eauto; solve_forall.
        rewrite Forall_forall in H3...
        eapply normalize_exp_normalized_cexp...
    - (* app *)
      eapply map_bind2_normalized_lexp in H1; eauto; solve_forall.
      destruct ro; repeat inv_bind.
      + specialize (normalize_reset_spec (hd_default x)) as [[? [? [? Hspec]]]|Hspec]; subst;
          rewrite Hspec in H4; clear Hspec; repeat inv_bind.
        * destruct x3...
        * destruct (hd _) as [? [? ?]]; simpl in *; repeat inv_bind...
      + constructor...
    - (* app (auxiliary equations) *)
      rewrite Forall_app. split.
      + destruct ro; repeat inv_bind;
        eapply map_bind2_normalized_eq in H1; eauto; solve_forall.
      + destruct ro; repeat inv_bind; try constructor;
        eapply Forall_app. split.
        * eapply H in H2... solve_weak_valid.
        * specialize (normalize_reset_spec (hd_default x)) as [[? [? [? Hspec]]]|Hspec]; subst;
          rewrite Hspec in H4; clear Hspec; repeat inv_bind...
          destruct (hd _) as [? [? ?]]; simpl in *; repeat inv_bind.
          repeat constructor. apply normalized_lexp_hd_default...
  Qed.
  Local Hint Resolve normalize_exp_normalized_eq.

  Corollary normalize_exps_normalized_eq : forall es es' eqs' out st st',
      weak_valid_after st out ->
      normalize_exps es st = (es', eqs', st') ->
      Forall (normalized_equation out) eqs'.
  Proof.
    intros es es' eqs' out st st' Hval Hnorm.
    unfold normalize_exps in Hnorm. repeat inv_bind.
    eapply map_bind2_normalized_eq in H; eauto.
    solve_forall.
  Qed.
  Local Hint Resolve normalize_exps_normalized_eq.

  (* Intermediary predicate for normalized rhs *)
  Inductive normalized_rhs : bool -> exp -> Prop :=
  | normalized_rhs_Eapp : forall f es lann keep_fby,
      Forall normalized_lexp es ->
      normalized_rhs keep_fby (Eapp f es None lann)
  | normalized_rhs_Eapp_reset : forall f es x ty cl lann keep_fby,
      Forall normalized_lexp es ->
      normalized_rhs keep_fby (Eapp f es (Some (Evar x (ty, cl))) lann)
  | normalized_rhs_Efby : forall e0 e ann,
      is_constant e0 ->
      normalized_lexp e ->
      normalized_rhs true (Efby [e0] [e] [ann])
  | normalized_rhs_cexp : forall e keep_fby,
      normalized_cexp e ->
      normalized_rhs keep_fby e.
  Hint Constructors normalized_rhs.

  Fact normalized_equation_normalized_rhs : forall xs es to_cut,
      normalized_equation to_cut (xs, es) ->
      Forall (normalized_rhs (negb (existsb (fun x => PS.mem x to_cut) xs))) es.
  Proof with eauto.
    intros xs es to_cut Hnormed.
    inv Hnormed...
    constructor; [| constructor].
    simpl.
    apply PSE.mem_3 in H1. rewrite H1; simpl...
  Qed.

  Fact normalize_rhs_normalized_rhs : forall e keep_fby es' eqs' st st',
      normalize_rhs keep_fby e st = (es', eqs', st') ->
      Forall (normalized_rhs keep_fby) es'.
  Proof with eauto.
    intros e keep_fby es' eqs' st st' Hnorm.
    destruct e; unfold normalize_rhs in Hnorm;
      try (apply normalize_exp_normalized_cexp in Hnorm; solve_forall; auto).
    - (* fby *)
      destruct keep_fby; try (apply normalize_exp_normalized_cexp in Hnorm; solve_forall; auto).
      repeat inv_bind.
      apply normalize_exps_normalized_lexp in H.
      apply normalize_exps_normalized_lexp in H0.
      unfold normalize_fby in H1. repeat inv_bind.
      eapply map_bind2_values, Forall3_ignore3 in H1.
      repeat rewrite_Forall_forall.
      apply In_nth with (d:=(hd_default [])) in H3; destruct H3 as [n [Hn Hnth]].
      replace (length es') in Hn.
      specialize (H2 (x5, x5, (bool_type, (Cbase, None))) (hd_default []) _ _ _ Hn eq_refl eq_refl) as [? [? [? H2]]].
      destruct (nth n (combine _ _) _) as [[e0 e] [ty cl]] eqn:Hnth'.
      unfold fby_iteexp in H2.
      destruct (Norm.is_constant e0) eqn:Hisconst; repeat inv_bind; simpl in *.
      + rewrite <- H4. repeat constructor.
        * rewrite is_constant_is_constant in Hisconst...
        * eapply nth_In in Hn. rewrite Hnth' in Hn...
      + rewrite <- H6. repeat constructor.
        eapply nth_In in Hn. rewrite Hnth' in Hn...
    - (* app *)
      destruct o; repeat inv_bind...
      specialize (normalize_reset_spec (hd_default x4)) as [[? [[? ?] [? Hspec]]]|Hspec]; subst;
        rewrite Hspec in H1; clear Hspec; repeat inv_bind...
      destruct (hd _) as [? [ty cl]]; simpl in H1. repeat inv_bind...
  Qed.

  Corollary normalize_rhss_normalized_rhs : forall es keep_fby es' eqs' st st',
      normalize_rhss keep_fby es st = (es', eqs', st') ->
      Forall (normalized_rhs keep_fby) es'.
  Proof with eauto.
    intros es keep_fby es' eqs' st st' Hnorm.
    unfold normalize_rhss in Hnorm. repeat inv_bind.
    eapply map_bind2_values in H.
    induction H; simpl; try constructor.
    apply Forall_app. split; auto.
    destruct H as [? [? H]].
    eapply normalize_rhs_normalized_rhs; eauto.
  Qed.

  Fact normalize_rhs_normalized_eq : forall e keep_fby es' eqs' out st st',
      weak_valid_after st out ->
      normalize_rhs keep_fby e st = (es', eqs', st') ->
      Forall (normalized_equation out) eqs'.
  Proof with eauto.
    intros e keep_fby es' eqs' out st st' Hval Hnorm.
    destruct e; unfold normalize_rhs in Hnorm;
      try (eapply normalize_exp_normalized_eq in Hnorm; eauto).
    - (* fby *)
      destruct keep_fby; try (eapply normalize_exp_normalized_eq in Hnorm; eauto).
      simpl in Hnorm. repeat inv_bind.
      repeat rewrite Forall_app. repeat split...
      + eapply normalize_fby_normalized_eq in H1; eauto.
    - (* app *)
      repeat inv_bind...
      destruct o; repeat inv_bind; repeat rewrite Forall_app; repeat split...
      specialize (normalize_reset_spec (hd_default x4)) as [[? [? [? Hspec]]]|Hspec]; subst;
        rewrite Hspec in H1; clear Hspec; repeat inv_bind; eauto.
      + destruct (hd _ _) as [? [? ?]]; simpl in H1.
        repeat inv_bind. repeat constructor.
        apply normalized_lexp_hd_default...
  Qed.
  Hint Resolve normalize_rhs_normalized_eq.

  Corollary normalize_rhss_normalized_eq : forall es keep_fby es' eqs' out st st',
      weak_valid_after st out ->
      normalize_rhss keep_fby es st = (es', eqs', st') ->
      Forall (normalized_equation out) eqs'.
  Proof.
    intros es keep_fby es' eqs' out st st' Hvalid Hnorm.
    unfold normalize_rhss in Hnorm; repeat inv_bind.
    eapply map_bind2_normalized_eq in H; eauto.
    rewrite Forall_forall; intros; eauto.
  Qed.
  Hint Resolve normalize_rhss_normalized_eq.

  Lemma normalize_equation_normalized_eq : forall G eq to_cut eqs' out st st',
      weak_valid_after st out ->
      wl_equation G eq ->
      normalize_equation to_cut eq st = (eqs', st') ->
      PS.Subset out to_cut ->
      Forall (normalized_equation out) eqs'.
  Proof with eauto.
    intros G [xs es] to_cut eqs' out st st' Hval Hwl Hnorm Hincl.
    unfold normalize_equation in Hnorm.
    repeat inv_bind.
    remember (negb (existsb (fun x => PS.mem x to_cut) xs)) as keep_fby.
    assert (keep_fby = true -> Forall (fun x => ~PS.In x out) xs) as Hin.
    { intro Hkeep; subst.
      rewrite Bool.negb_true_iff in Hkeep. rewrite existsb_Forall in Hkeep.
      rewrite forallb_Forall in Hkeep. solve_forall.
      rewrite Bool.negb_true_iff in H0. apply PSE.mem_4 in H0.
      intro contra. apply Hincl in contra. contradiction.
    }
    clear Heqkeep_fby.
    rewrite Forall_app. split.
    - assert (length xs = length (annots x)) as Hlen.
      { destruct Hwl as [Hwl1 Hwl2].
        eapply normalize_rhss_annots_length in H...
        congruence. } clear Hwl.
      eapply normalize_rhss_normalized_rhs in H; eauto.
      revert xs Hin Hlen.
      induction H; intros xs Hin Hlen; constructor.
      + inv H...
        * destruct xs; simpl in *; try omega.
          constructor...
          specialize (Hin eq_refl). inv Hin. auto.
        * simpl in Hlen. rewrite app_length in Hlen.
          rewrite length_annot_numstreams in Hlen.
          specialize (normalized_cexp_numstreams _ H1) as Hlen'.
          rewrite Hlen' in *. simpl.
          destruct xs... simpl in Hlen. omega.
      + eapply IHForall.
        * intro Hkeep. apply Hin in Hkeep.
          apply Forall_skipn...
        * rewrite skipn_length.
          rewrite Hlen. simpl. rewrite app_length.
          rewrite length_annot_numstreams. omega.
    - eapply normalize_rhss_normalized_eq in H; eauto.
  Qed.

  Corollary normalize_equations_normalized_eq : forall G eqs to_cut eqs' out st st',
      weak_valid_after st out ->
      Forall (wl_equation G) eqs ->
      normalize_equations to_cut eqs st = (eqs', st') ->
      PS.Subset out to_cut ->
      Forall (normalized_equation out) eqs'.
  Proof.
    induction eqs; intros to_cut eqs' out st st' Hval Hwl Hnorm Hincl;
      simpl in Hnorm; repeat inv_bind; auto.
    inv Hwl. apply Forall_app; split.
    - eapply normalize_equation_normalized_eq; eauto.
    - eapply IHeqs in H0; eauto.
  Qed.

  (** ** No anonymous names in a normalized node *)

  Fact is_constant_no_fresh : forall e,
      is_constant e ->
      fresh_in e = [].
  Proof with eauto.
    intros e Hconst.
    induction Hconst; simpl...
    rewrite IHHconst...
  Qed.

  Fact normalized_lexp_no_fresh : forall e,
      normalized_lexp e ->
      fresh_in e = [].
  Proof with eauto.
    intros e Hnormed.
    induction Hnormed; simpl...
    - (* binop *)
      rewrite IHHnormed1. rewrite IHHnormed2. reflexivity.
    - (* when *)
      rewrite IHHnormed. reflexivity.
  Qed.

  Fact normalized_cexp_no_fresh : forall e,
      normalized_cexp e ->
      fresh_in e = [].
  Proof with eauto.
    intros e Hnormed.
    induction Hnormed; simpl...
    - (* merge *)
      rewrite IHHnormed1. rewrite IHHnormed2. reflexivity.
    - (* ite *)
      rewrite IHHnormed1. rewrite IHHnormed2.
      rewrite normalized_lexp_no_fresh...
    - (* lexp *)
      eapply normalized_lexp_no_fresh...
  Qed.

  Corollary normalize_exp_no_fresh : forall e is_control es' eqs' st st',
      normalize_exp is_control e st = (es', eqs', st') ->
      fresh_ins es' = [].
  Proof.
    intros e is_control es' eqs' st st' Hnorm.
    unfold fresh_ins. rewrite concat_eq_nil, Forall_map.
    destruct is_control.
    - apply normalize_exp_normalized_cexp in Hnorm.
      eapply Forall_impl; eauto. intros. apply normalized_cexp_no_fresh; auto.
    - apply normalize_exp_normalized_lexp in Hnorm.
      eapply Forall_impl; eauto. intros. apply normalized_lexp_no_fresh; auto.
  Qed.

  Corollary normalize_exps_no_fresh : forall es es' eqs' st st',
      normalize_exps es st = (es', eqs', st') ->
      fresh_ins es' = [].
  Proof.
    induction es; intros es' eqs' st st' Hnorm;
      unfold fresh_ins;
      unfold normalize_exps in Hnorm; simpl in *; repeat inv_bind; auto.
    simpl. rewrite map_app, concat_app.
    eapply normalize_exp_no_fresh in H.
    unfold fresh_ins in H, IHes; rewrite H; simpl.
    eapply IHes.
    unfold normalize_exps; inv_bind.
    repeat eexists; eauto. inv_bind; eauto.
  Qed.

  Fact normalized_equation_no_anon_in_eq : forall to_cut e,
      normalized_equation to_cut e ->
      anon_in_eq e = [].
  Proof with eauto.
    intros to_cut e Hnormed.
    induction Hnormed; unfold anon_in_eq, anon_ins; simpl; repeat rewrite app_nil_r.
    - (* app *)
      unfold fresh_ins. rewrite concat_eq_nil, Forall_map.
      solve_forall. eapply normalized_lexp_no_fresh...
    - (* app (reset) *)
      unfold fresh_ins. rewrite concat_eq_nil, Forall_map.
      solve_forall. eapply normalized_lexp_no_fresh...
    - (* fby *)
      rewrite is_constant_no_fresh...
      rewrite normalized_lexp_no_fresh...
    - (* cexp *)
      specialize (anon_in_fresh_in e) as Hincl.
      rewrite normalized_cexp_no_fresh in Hincl...
      apply incl_nil...
  Qed.

  Lemma normalized_equations_no_anon : forall to_cut eqs,
      Forall (normalized_equation to_cut) eqs ->
      anon_in_eqs eqs = [].
  Proof.
    intros to_cut eqs Hnormed.
    unfold anon_in_eqs.
    rewrite concat_eq_nil, Forall_map.
    solve_forall. eapply normalized_equation_no_anon_in_eq; eauto.
  Qed.

  Corollary normalize_equations_no_anon : forall G eqs to_cut eqs' out st st',
      weak_valid_after st out ->
      Forall (wl_equation G) eqs ->
      normalize_equations to_cut eqs st = (eqs', st') ->
      PS.Subset out to_cut ->
      anon_in_eqs eqs' = [].
  Proof.
    intros G eqs to_cut eqs' out st st' Hval Hwl Hnorm Hsub.
    eapply normalized_equations_no_anon.
    eapply normalize_equations_normalized_eq; eauto.
  Qed.

End SPECIFICATION.

Module SpecificationFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Syn : LSYNTAX Ids Op)
       (Norm : NORMALIZATION Ids Op OpAux Syn)
       <: SPECIFICATION Ids Op OpAux Syn Norm.
  Include SPECIFICATION Ids Op OpAux Syn Norm.
End SpecificationFun.
