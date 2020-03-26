From Coq Require Import List.

From Velus Require Import Common Ident.
From Velus Require Import Operators Environment.
From Velus Require Import CoindStreams.
From Velus Require Import Lustre.LSyntax Lustre.LOrdered Lustre.LTyping Lustre.LSemantics.
From Velus Require Import Lustre.Normalization.Fresh Lustre.Normalization.Normalization.

(** * Correctness of the Normalization *)

Local Set Warnings "-masking-absolute-name".
Module Type CORRECTNESS
       (Import Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Str : COINDSTREAMS Op OpAux)
       (Import Syn : LSYNTAX Ids Op)
       (Import Typ : LTYPING Ids Op Syn)
       (Lord : LORDERED Ids Op Syn)
       (Import Sem : LSEMANTICS Ids Op OpAux Syn Lord Str)
       (Import Norm : NORMALIZATION Ids Op OpAux Syn Typ).
  Import List.

  Ltac singleton_length :=
    simpl in *;
    match goal with
    | H : length ?x = 1 |- _ =>
      destruct x; simpl in H; try congruence;
      destruct x; simpl in H; try congruence;
      simpl in *; clear H
    end.

  Fact map_bind2_wt_exp {A A2 B} :
    forall G vars (k : A -> Fresh (list exp * A2) B) a es' a2s st st',
      map_bind2 k a st = (es', a2s, st') ->
      Forall (fun a => forall es' a2s st st',
                  k a st = (es', a2s, st') ->
                  Forall (wt_exp G vars) es') a ->
      Forall (wt_exp G vars) (concat es').
  Proof.
    intros G vars k a es' a2s st st' Hmap Hf.
    apply map_bind2_values in Hmap.
    induction Hmap; inv Hf.
    - constructor.
    - simpl. apply Forall_app.
      destruct H as [? [? H]].
      split; eauto.
  Qed.

  (** ** Preservation of good typing
      TODO is this necessary ? *)

  Fact idents_for_anns_wt : forall G vars anns ids st st',
      idents_for_anns anns st = (ids, st') ->
      Forall (fun '(ty, cl) => wt_nclock vars cl) anns ->
      Forall (wt_exp G (vars++(idty ids))) (map (fun '(x, ann) => Evar x ann) ids).
  Proof.
    induction anns; intros ids st st' Hidents Hf;
      simpl in *; repeat inv_bind.
    - constructor.
    - inv Hf. destruct a as [ty cl].
      specialize (IHanns x1 _ _ H0 H4).
      econstructor; eauto.
      + repeat constructor; simpl; auto.
        * apply in_or_app. right. constructor; auto.
        * eapply wt_nclock_incl; eauto.
          apply incl_appl. reflexivity.
      + eapply Forall_impl; [| eauto].
        intros. eapply wt_exp_incl; eauto.
        apply incl_app.
        * apply incl_appl. reflexivity.
        * apply incl_appr. apply incl_tl. reflexivity.
  Qed.

  Fact st_follows_incl {A1 A2 A3} : forall (st st' : fresh_st ((A1 * A2) * A3)),
      fresh_st_follows st st' ->
      incl (idty (idty (snd st))) (idty (idty (snd st'))).
  Proof.
    intros st st' [Hincl _].
    unfold incl in *. intros [id data] Hin.
    unfold idty in *.
    rewrite in_map_iff in *. destruct Hin as [x [H Hin]]; subst. inv H.
    exists x. split; auto.
    rewrite in_map_iff in *. destruct Hin as [x' [H Hin]]; subst.
    exists x'. eauto.
  Qed.

  Hint Constructors wt_exp.
  Fact normalize_exp_wt : forall G vars e is_control es' eqs' st st',
      wt_exp G vars e ->
      normalize_exp is_control e st = (es', eqs', st') ->
      Forall (wt_exp G (vars++(idty (idty (snd st'))))) es'. (* non mauvais invariant *)
  Proof.
    intros G vars e is_control es' eqs' st st' Hwt;
      revert is_control eqs' es' st st'.
    induction Hwt using wt_exp_ind2;
      intros is_control eqs' es' st st' Hnorm; simpl in *.
    - (* const *)
      repeat inv_bind; eauto.
    - (* var *)
      repeat inv_bind.
      repeat constructor.
      + apply in_or_app; auto.
      + eapply wt_nclock_incl; eauto.
        apply incl_appl. apply incl_refl.
    - (* unop *)
      repeat inv_bind.
      specialize (IHHwt _ _ _ _ _ H2).
      repeat constructor.
      specialize (normalize_exp_length _ _ _ _ _ _ _ _ Hwt H2) as Hlen.
      rewrite <- numstreams_length_typeof in Hlen.
      replace (typeof e) in *.
      singleton_length.
      inv IHHwt. econstructor; eauto.
      eapply normalize_exp_typeof in Hwt; eauto.
      simpl in *; rewrite app_nil_r in Hwt; rewrite Hwt; auto.
      eapply wt_nclock_incl; eauto.
      apply incl_appl; apply incl_refl.
    - (* binop *)
      repeat inv_bind.
      specialize (IHHwt1 _ _ _ _ _ H3).
      specialize (IHHwt2 _ _ _ _ _ H4).
      repeat constructor.
      specialize (normalize_exp_length _ _ _ _ _ _ _ _ Hwt1 H3) as Hlen1.
      specialize (normalize_exp_length _ _ _ _ _ _ _ _ Hwt2 H4) as Hlen2.
      rewrite <- numstreams_length_typeof in Hlen1.
      rewrite <- numstreams_length_typeof in Hlen2.
      replace (typeof e1) in *.
      replace (typeof e2) in *.
      repeat singleton_length.
      eapply normalize_exp_typeof in Hwt1; eauto.
      eapply normalize_exp_typeof in Hwt2; eauto.
      inv IHHwt1. inv IHHwt2. inv H8. inv H10.
      econstructor; eauto;
        simpl in *; rewrite app_nil_r in *;
          try rewrite Hwt1; try rewrite Hwt2; auto.
      + eapply wt_exp_incl; eauto.
        apply incl_app.
        * apply incl_appl; reflexivity.
        * apply incl_appr. eapply st_follows_incl; eauto.
      + eapply wt_nclock_incl; [| eauto].
        apply incl_appl; reflexivity.
    - (* fby *)
      repeat inv_bind.
      admit.
    - (* when *)
      repeat inv_bind.
      specialize (map_bind2_normalize_exp_length _ _ _ _ _ _ _ _ H H1) as Hlength.
      specialize (map_bind2_normalize_exp_typeof _ _ _ _ _ _ _ _ H H1) as Htypeof.
      admit.
  Admitted.

  Fact map_bind2_wt_eq {A A1 B} :
    forall G vars (k : A -> Fresh (A1 * list equation) B) a a1s eqs' st st',
      map_bind2 k a st = (a1s, eqs', st') ->
      Forall (fun a => forall a1 eqs' st st',
                  k a st = (a1, eqs', st') ->
                  Forall (wt_equation G vars) eqs') a ->
      Forall (wt_equation G vars) (concat eqs').
  Proof.
    intros G vars k a a1s eqs' st st' Hmap Hf.
    apply map_bind2_values in Hmap.
    induction Hmap; inv Hf.
    - constructor.
    - simpl. apply Forall_app.
      destruct H as [? [? H]].
      split; eauto.
  Qed.

  (* Fact normalize_fby_wt_eq : forall G vars e0s es anns es' eqs' st st', *)
  (*     normalize_fby e0s es anns st = (es', eqs', st') -> *)
  (*     Forall (wt_equation G vars) eqs'. *)
  (* Proof. *)
  (*   intros G vars e0s es anns es' eqs' st st' Hnorm. *)
  (*   unfold normalize_fby in Hnorm. repeat inv_bind. *)
  (*   eapply map_bind2_wt_eq; eauto. *)
  (*   rewrite Forall_forall; intros. destruct x as [[e0 e] [ty cl]]. *)
  (*   specialize (fby_iteexp_spec e0 e ty cl) as [[c [? Hfby]]|Hfby]; subst; rewrite Hfby in H1; clear Hfby; *)
  (*     repeat inv_bind. *)
  (*   - constructor. *)
  (*   - repeat constructor; simpl in *. *)
  (* Admitted. *)

  Fact normalize_exp_wt_eq : forall G vars e is_control es' eqs' st st',
      wt_exp G vars e ->
      normalize_exp is_control e st = (es', eqs', st') ->
      Forall (wt_equation G vars (* FIXME *)) eqs'.
  Proof.
    induction e using exp_ind2; intros is_control es' eqs' st st' Hwt Hnorm;
      inv Hwt; simpl in Hnorm; repeat inv_bind.
    - (* const *) constructor.
    - (* var *) constructor.
    - (* unop *) eauto.
    - (* binop *)
      rewrite Forall_app.
      split; eauto.
    - (* fby *)
      repeat rewrite Forall_app.
      repeat split; eauto;
        try (eapply map_bind2_wt_eq; eauto;
             rewrite Forall_forall in *;
             intros; eauto).
      admit. admit.
    - (* when *)
      eapply map_bind2_wt_eq; eauto.
      rewrite Forall_forall in *; intros; eauto.
    - (* merge *)
      destruct is_control; repeat inv_bind.
      + (* exp *)
        apply Forall_app; split;
          (eapply map_bind2_wt_eq; eauto;
           rewrite Forall_forall in *; intros; eauto).
      + (* control *)
        repeat rewrite Forall_app.
        repeat split;
          try (eapply map_bind2_wt_eq; eauto;
               rewrite Forall_forall in *; intros; eauto).
        admit.
  Admitted.
End CORRECTNESS.

Module CorrectnessFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Op)
       (Str : COINDSTREAMS Op OpAux)
       (Syn : LSYNTAX Ids Op)
       (Typ : LTYPING Ids Op Syn)
       (Lord : LORDERED Ids Op Syn)
       (Sem : LSEMANTICS Ids Op OpAux Syn Lord Str)
       (Norm : NORMALIZATION Ids Op OpAux Syn Typ)
       <: CORRECTNESS Ids Op OpAux Str Syn Typ Lord Sem Norm.
  Include CORRECTNESS Ids Op OpAux Str Syn Typ Lord Sem Norm.
End CorrectnessFun.
