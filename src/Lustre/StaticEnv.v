From Velus Require Import Common.
From Velus Require Import Operators.
From Velus Require Import Clocks.

From Coq Require Import Morphisms.

From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

(** * Static environment for analysis of Lustre programs *)

Module Type STATICENV
       (Import Ids  : IDS)
       (Import Op   : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks  : CLOCKS Ids Op OpAux).

  Record annotation :=
    { typ : type;
      clo : clock;
      causl : ident;
      causl_last : option ident;
    }.

  Definition ann_with_clock (ann : annotation) (ck : clock) :=
    Build_annotation ann.(typ) ck ann.(causl) ann.(causl_last).

  Definition static_env := list (ident * annotation).

  Inductive IsVar : static_env -> ident -> Prop :=
  | IsVarC : forall senv x,
      InMembers x senv ->
      IsVar senv x.

  Inductive HasType : static_env -> ident -> type -> Prop :=
  | HasTypeC : forall senv x ty e,
      In (x, e) senv ->
      e.(typ) = ty ->
      HasType senv x ty.

  Inductive HasClock : static_env -> ident -> clock -> Prop :=
  | HasClockC : forall senv x ck e,
      In (x, e) senv ->
      e.(clo) = ck ->
      HasClock senv x ck.

  Inductive HasCaus : static_env -> ident -> ident -> Prop :=
  | HasCausC : forall senv x cx e,
      In (x, e) senv ->
      e.(causl) = cx ->
      HasCaus senv x cx.

  Inductive IsLast : static_env -> ident -> Prop :=
  | IsLastC : forall senv x e,
      In (x, e) senv ->
      e.(causl_last) <> None ->
      IsLast senv x.

  Inductive HasLastCaus : static_env -> ident -> ident -> Prop :=
  | HasLastCausC : forall senv x cx e,
      In (x, e) senv ->
      e.(causl_last) = Some cx ->
      HasLastCaus senv x cx.

  Global Hint Constructors IsVar HasType HasClock HasCaus IsLast HasLastCaus : senv.

  Global Instance IsVar_proper:
    Proper (@Permutation.Permutation _ ==> @eq _ ==> iff) IsVar.
  Proof.
    intros ?? Hperm ???; subst; split; intros Hin; inv Hin;
      (rewrite Hperm in * || rewrite <-Hperm in * ); auto with senv.
  Qed.

  Global Instance HasType_proper:
    Proper (@Permutation.Permutation _ ==> @eq _ ==> @eq _ ==> iff) HasType.
  Proof.
    intros ?? Hperm ??????; subst; split; intros Hin; inv Hin;
      (rewrite Hperm in * || rewrite <-Hperm in * ); eauto with senv.
  Qed.

  Global Instance HasClock_proper:
    Proper (@Permutation.Permutation _ ==> @eq _ ==> @eq _ ==> iff) HasClock.
  Proof.
    intros ?? Hperm ??????; subst; split; intros Hin; inv Hin;
      (rewrite Hperm in * || rewrite <-Hperm in * ); eauto with senv.
  Qed.

  Global Instance HasCaus_proper:
    Proper (@Permutation.Permutation _ ==> @eq _ ==> @eq _ ==> iff) HasCaus.
  Proof.
    intros ?? Hperm ??????; subst; split; intros Hin; inv Hin;
      (rewrite Hperm in * || rewrite <-Hperm in * ); eauto with senv.
  Qed.

  Global Instance IsLast_proper:
    Proper (@Permutation.Permutation _ ==> @eq _ ==> iff) IsLast.
  Proof.
    intros ?? Hperm ???; subst; split; intros Hin; inv Hin;
      (rewrite Hperm in * || rewrite <-Hperm in * ); eauto with senv.
  Qed.

  Global Instance HasLastCaus_proper:
    Proper (@Permutation.Permutation _ ==> @eq _ ==> @eq _ ==> iff) HasLastCaus.
  Proof.
    intros ?? Hperm ??????; subst; split; intros Hin; inv Hin;
      (rewrite Hperm in * || rewrite <-Hperm in * ); eauto with senv.
  Qed.

  Lemma IsVar_incl : forall senv1 senv2 x,
      incl senv1 senv2 ->
      IsVar senv1 x ->
      IsVar senv2 x.
  Proof.
    intros * Hincl Hv. inv Hv.
    eauto using InMembers_incl with senv.
  Qed.

  Lemma HasType_incl : forall senv1 senv2 x ty,
      incl senv1 senv2 ->
      HasType senv1 x ty ->
      HasType senv2 x ty.
  Proof.
    intros * Hincl Hv. inv Hv. eauto with senv.
  Qed.

  Lemma HasClock_incl : forall senv1 senv2 x ck,
      incl senv1 senv2 ->
      HasClock senv1 x ck ->
      HasClock senv2 x ck.
  Proof.
    intros * Hincl Hv. inv Hv. eauto with senv.
  Qed.

  Lemma HasCaus_incl : forall senv1 senv2 x cx,
      incl senv1 senv2 ->
      HasCaus senv1 x cx ->
      HasCaus senv2 x cx.
  Proof.
    intros * Hincl Hv. inv Hv. eauto with senv.
  Qed.

  Lemma IsLast_incl : forall senv1 senv2 x,
      incl senv1 senv2 ->
      IsLast senv1 x ->
      IsLast senv2 x.
  Proof.
    intros * Hincl Hv. inv Hv.
    eauto using InMembers_incl with senv.
  Qed.

  Lemma HasLastCaus_incl : forall senv1 senv2 x cx,
      incl senv1 senv2 ->
      HasLastCaus senv1 x cx ->
      HasLastCaus senv2 x cx.
  Proof.
    intros * Hincl Hv. inv Hv. eauto with senv.
  Qed.

  Global Hint Resolve IsVar_incl HasType_incl HasClock_incl HasCaus_incl IsLast_incl HasLastCaus_incl : senv.

  Lemma HasType_IsVar : forall env x ty,
      HasType env x ty ->
      IsVar env x.
  Proof.
    intros * Hhas. inv Hhas; eauto using In_InMembers with senv.
  Qed.

  Lemma HasClock_IsVar : forall env x ck,
      HasClock env x ck ->
      IsVar env x.
  Proof.
    intros * Hhas. inv Hhas; eauto using In_InMembers with senv.
  Qed.

  Lemma IsLast_IsVar : forall env x,
      IsLast env x ->
      IsVar env x.
  Proof.
    intros * His. inv His; eauto using In_InMembers with senv.
  Qed.

  Global Hint Resolve HasType_IsVar HasClock_IsVar IsLast_IsVar : senv.

  Fact IsVar_app : forall env1 env2 x,
      IsVar (env1 ++ env2) x <-> IsVar env1 x \/ IsVar env2 x.
  Proof.
    split; intros * Hv.
    - inv Hv. apply InMembers_app in H as [|]; auto with senv.
    - destruct Hv as [Hv|Hv]; inv Hv.
      1,2:constructor; apply InMembers_app; auto.
  Qed.

  Fact IsLast_app : forall env1 env2 x,
      IsLast (env1 ++ env2) x <-> IsLast env1 x \/ IsLast env2 x.
  Proof.
    split; intros * Hv.
    - inv Hv. apply in_app_iff in H as [|]; eauto with senv.
    - destruct Hv as [Hv|Hv]; inv Hv.
      1,2:econstructor; try eapply in_app_iff; eauto.
  Qed.

  Fact HasType_app : forall env1 env2 x cx,
      HasType (env1 ++ env2) x cx <-> HasType env1 x cx \/ HasType env2 x cx.
  Proof.
    split; intros * Hv.
    - inv Hv. apply in_app_iff in H as [|]; eauto with senv.
    - destruct Hv as [Hv|Hv]; inv Hv.
      1,2:econstructor; try eapply in_app_iff; eauto.
  Qed.

  Fact HasClock_app : forall env1 env2 x cx,
      HasClock (env1 ++ env2) x cx <-> HasClock env1 x cx \/ HasClock env2 x cx.
  Proof.
    split; intros * Hv.
    - inv Hv. apply in_app_iff in H as [|]; eauto with senv.
    - destruct Hv as [Hv|Hv]; inv Hv.
      1,2:econstructor; try eapply in_app_iff; eauto.
  Qed.

  Fact HasCaus_app : forall env1 env2 x cx,
      HasCaus (env1 ++ env2) x cx <-> HasCaus env1 x cx \/ HasCaus env2 x cx.
  Proof.
    split; intros * Hv.
    - inv Hv. apply in_app_iff in H as [|]; eauto with senv.
    - destruct Hv as [Hv|Hv]; inv Hv.
      1,2:econstructor; try eapply in_app_iff; eauto.
  Qed.

  Fact HasLastCaus_app : forall env1 env2 x cx,
      HasLastCaus (env1 ++ env2) x cx <-> HasLastCaus env1 x cx \/ HasLastCaus env2 x cx.
  Proof.
    split; intros * Hv.
    - inv Hv. apply in_app_iff in H as [|]; eauto with senv.
    - destruct Hv as [Hv|Hv]; inv Hv.
      1,2:econstructor; try eapply in_app_iff; eauto.
  Qed.

  Definition senv_of_tyck (l : list (ident * (type * clock))) : static_env :=
    List.map (fun '(x, (ty, ck)) => (x, Build_annotation ty ck xH None)) l.

  Definition senv_of_inout (l : list (ident * (type * clock * ident))) : static_env :=
    List.map (fun '(x, (ty, ck, cx)) => (x, Build_annotation ty ck cx None)) l.

  Definition senv_of_locs {A} (l : list (ident * (type * clock * ident * option (A * ident)))) : static_env :=
    List.map (fun '(x, (ty, ck, cx, o)) => (x, Build_annotation ty ck cx (option_map snd o))) l.

  Global Hint Unfold senv_of_inout senv_of_locs : list.

  Lemma map_fst_senv_of_tyck : forall l,
      map fst (senv_of_tyck l) = map fst l.
  Proof.
    intros *. unfold senv_of_tyck.
    erewrite map_map, map_ext; auto. intros; destruct_conjs; auto.
  Qed.

  Lemma map_fst_senv_of_inout : forall l,
      map fst (senv_of_inout l) = map fst l.
  Proof.
    intros *. unfold senv_of_inout.
    erewrite map_map, map_ext; auto. intros; destruct_conjs; auto.
  Qed.

  Lemma map_fst_senv_of_locs {A} : forall l,
      map fst (@senv_of_locs A l) = map fst l.
  Proof.
    intros *. unfold senv_of_locs.
    erewrite map_map, map_ext; auto. intros; destruct_conjs; auto.
  Qed.

  Lemma InMembers_senv_of_locs {A} : forall x locs,
      InMembers x (@senv_of_locs A locs) <-> InMembers x locs.
  Proof.
    intros *. symmetry.
    symmetry. now rewrite fst_InMembers, map_fst_senv_of_locs, <-fst_InMembers.
  Qed.

  Lemma NoDupMembers_senv_of_locs {A} : forall locs,
      NoDupMembers (@senv_of_locs A locs) <-> NoDupMembers locs.
  Proof.
    intros *. now rewrite fst_NoDupMembers, map_fst_senv_of_locs, <-fst_NoDupMembers.
  Qed.

  Definition idty (env : static_env) : list (ident * type) :=
    map (fun '(x, entry) => (x, entry.(typ))) env.

  Definition idck (env : static_env) : list (ident * clock) :=
    map (fun '(x, entry) => (x, entry.(clo))) env.

  Global Hint Unfold idty idck : list.

  Definition idcaus_of_senv (env : static_env) : list (ident * ident) :=
    map (fun '(x, e) => (x, e.(causl))) env
    ++ map_filter (fun '(x, e) => option_map (fun cx => (x, cx)) e.(causl_last)) env.

  Import Permutation.

  Fact idcaus_of_senv_app : forall Γ1 Γ2,
      Permutation (idcaus_of_senv (Γ1 ++ Γ2))
                  (idcaus_of_senv Γ1 ++ idcaus_of_senv Γ2).
  Proof.
    intros.
    unfold idcaus_of_senv. simpl_app.
    apply Permutation_app_head, Permutation_swap.
  Qed.

  Fact idcaus_of_senv_In : forall Γ x cx,
      (HasCaus Γ x cx \/ HasLastCaus Γ x cx)
      <-> In (x, cx) (idcaus_of_senv Γ).
  Proof.
    intros *. unfold idcaus_of_senv. rewrite in_app_iff.
    split; (intros [|]; [left|right]).
    - inv H. solve_In.
    - inv H. solve_In. simpl. rewrite H1; simpl; auto.
    - simpl_In. econstructor; solve_In; eauto.
    - simpl_In. econstructor; solve_In; eauto.
  Qed.

  Fact HasCaus_snd_det Γ : forall x1 x2 cx,
      NoDup (map snd (idcaus_of_senv Γ)) ->
      HasCaus Γ x1 cx ->
      HasCaus Γ x2 cx ->
      x1 = x2.
  Proof.
    intros * Hnd Hc1 Hc2.
    unfold idcaus_of_senv in *. rewrite map_app in Hnd. apply NoDup_app_l in Hnd.
    inv Hc1. inv Hc2.
    eapply NoDup_snd_det in Hnd; eauto. 2:solve_In.
    clear H0; solve_In. congruence.
  Qed.

  Fact HasLastCaus_snd_det Γ : forall x1 x2 cx,
      NoDup (map snd (idcaus_of_senv Γ)) ->
      HasLastCaus Γ x1 cx ->
      HasLastCaus Γ x2 cx ->
      x1 = x2.
  Proof.
    intros * Hnd Hc1 Hc2.
    unfold idcaus_of_senv in *. rewrite map_app in Hnd. apply NoDup_app_r in Hnd.
    inv Hc1. inv Hc2.
    eapply NoDup_snd_det in Hnd; eauto. 2:solve_In; simpl; rewrite H2; simpl; eauto.
    clear H1; solve_In. simpl; rewrite H0; simpl; auto.
  Qed.

  Fact NoDup_HasCaus_HasLastCaus Γ : forall x1 x2 cx,
      NoDup (map snd (idcaus_of_senv Γ)) ->
      HasCaus Γ x1 cx ->
      HasLastCaus Γ x2 cx ->
      False.
  Proof.
    intros * Hnd Hc1 Hc2.
    unfold idcaus_of_senv in *. rewrite map_app in Hnd.
    inv Hc1. inv Hc2. eapply NoDup_app_In in Hnd. eapply Hnd.
    - solve_In. rewrite H1; simpl; auto.
    - clear H0. solve_In.
  Qed.

  Lemma senv_of_tyck_NoLast : forall Γ,
    forall x, ~IsLast (senv_of_tyck Γ) x.
  Proof.
    intros * Hl. inv Hl. simpl_In. auto.
  Qed.

  Lemma senv_of_inout_NoLast : forall Γ,
    forall x, ~IsLast (senv_of_inout Γ) x.
  Proof.
    intros * Hl. inv Hl. simpl_In. auto.
  Qed.

  Lemma NoLast_app : forall Γ1 Γ2,
      (forall x, ~IsLast (Γ1 ++ Γ2) x)
      <-> (forall x, ~IsLast Γ1 x) /\ (forall x, ~IsLast Γ2 x).
  Proof.
    intros *. setoid_rewrite IsLast_app.
    split; intros. split; intros ? Hl.
    1,2:eapply H; eauto.
    destruct H as (H1&H2). intros [|]; [eapply H1|eapply H2]; eauto.
  Qed.

  (* Notations *)

  (* Notation "Γ ⊢ x" := (IsVar Γ x) (at level 50). *)
  (* Notation "Γ ⊢ x : ty" := (HasType Γ x ty) (at level 50). *)
  (* Notation "Γ ⊢ x : ck" := (HasClock Γ x ck) (at level 50). *)
  (* Notation "Γ ⊢ x : cx" := (HasCaus Γ x cx) (at level 50). *)
  (* Notation "Γ ⊢ 'last' x" := (IsLast Γ x) (at level 50). *)
  (* Notation "Γ ⊢ 'last' x : cx" := (HasLastCaus Γ x cx) (at level 50). *)

End STATICENV.

Module StaticEnvFun
       (Ids      : IDS)
       (Op       : OPERATORS)
       (OpAux    : OPERATORS_AUX Ids Op)
       (Cks      : CLOCKS Ids Op OpAux) <: STATICENV Ids Op OpAux Cks.
  Include STATICENV Ids Op OpAux Cks.
End StaticEnvFun.
