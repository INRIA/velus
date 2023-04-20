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

  Definition ann_with_caus (ann : annotation) (cx : ident) :=
    Build_annotation ann.(typ) ann.(clo) cx ann.(causl_last).

  Definition static_env := list (ident * annotation).

  Inductive IsVar : static_env -> ident -> Prop :=
  | IsVarC : forall senv x,
      InMembers x senv ->
      IsVar senv x.

  Lemma IsVar_fst : forall Γ x,
      IsVar Γ x <-> In x (map fst Γ).
  Proof.
    split.
    - intros []. now rewrite <-fst_InMembers.
    - intros. constructor. now rewrite fst_InMembers.
  Qed.

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

  Lemma IsVar_In : forall Γ x,
      IsVar Γ x ->
      In x (map fst Γ).
  Proof.
    intros * Hv.
    inv Hv.
    now apply fst_InMembers.
  Qed.

  Lemma IsVar_incl_fst : forall senv1 senv2,
      (forall x, IsVar senv1 x -> IsVar senv2 x) ->
      incl (map fst senv1) (map fst senv2).
  Proof.
    intros * Hincl ? Hin. simpl_In.
    assert (IsVar senv1 a) as Hv by (econstructor; solve_In).
    apply Hincl in Hv. inv Hv. solve_In.
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

  Fact IsVar_concat : forall env1 env2 x,
      In env1 env2 ->
      IsVar env1 x ->
      IsVar (concat env2) x.
  Proof.
    intros * Hin Hv. inv Hv.
    eapply InMembers_In in H as (?&?).
    econstructor. eapply In_InMembers; eauto using in_concat'.
  Qed.
  Global Hint Resolve IsVar_concat : senv.

  Fact IsVar_concat' : forall env2 x,
      IsVar (concat env2) x ->
      exists env1, In env1 env2 /\ IsVar env1 x.
  Proof.
    intros * Hv. inv Hv.
    eapply InMembers_In in H as (?&In). apply in_concat in In as (?&?&?).
    do 2 esplit; eauto. econstructor; eauto using In_InMembers.
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

  Global Hint Rewrite IsLast_app HasType_app HasClock_app HasCaus_app HasLastCaus_app : list.

  Definition senv_of_tyck (l : list (ident * (type * clock))) : static_env :=
    List.map (fun '(x, (ty, ck)) => (x, Build_annotation ty ck xH None)) l.

  Definition senv_of_ins (l : list (ident * (type * clock * ident))) : static_env :=
    List.map (fun '(x, (ty, ck, cx)) => (x, Build_annotation ty ck cx None)) l.

  Definition senv_of_decls (l : list (ident * (type * clock * ident * option ident))) : static_env :=
    List.map (fun '(x, (ty, ck, cx, o)) => (x, Build_annotation ty ck cx o)) l.

  Global Hint Unfold senv_of_ins senv_of_decls : list.

  Lemma senv_of_decls_app : forall xs ys,
      senv_of_decls (xs ++ ys) = senv_of_decls xs ++ senv_of_decls ys.
  Proof.
    intros. apply map_app.
  Qed.

  Lemma map_fst_senv_of_tyck : forall l,
      map fst (senv_of_tyck l) = map fst l.
  Proof.
    intros *. unfold senv_of_tyck.
    erewrite map_map, map_ext; auto. intros; destruct_conjs; auto.
  Qed.

  Lemma map_fst_senv_of_ins : forall l,
      map fst (senv_of_ins l) = map fst l.
  Proof.
    intros *. unfold senv_of_ins.
    erewrite map_map, map_ext; auto. intros; destruct_conjs; auto.
  Qed.

  Lemma map_fst_senv_of_decls : forall l,
      map fst (senv_of_decls l) = map fst l.
  Proof.
    intros *. unfold senv_of_decls.
    erewrite map_map, map_ext; auto. intros; destruct_conjs; auto.
  Qed.

  Global Hint Rewrite -> map_fst_senv_of_tyck.
  Global Hint Rewrite -> map_fst_senv_of_ins.
  Global Hint Rewrite -> @map_fst_senv_of_decls.

  Lemma InMembers_senv_of_decls : forall x locs,
      InMembers x (senv_of_decls locs) <-> InMembers x locs.
  Proof.
    intros *. symmetry.
    symmetry. autorewrite with list. now rewrite map_fst_senv_of_decls.
  Qed.

  Global Hint Rewrite -> InMembers_senv_of_decls : list.

  Lemma NoDupMembers_senv_of_decls : forall locs,
      NoDupMembers (senv_of_decls locs) <-> NoDupMembers locs.
  Proof.
    intros *. now rewrite fst_NoDupMembers, map_fst_senv_of_decls, <-fst_NoDupMembers.
  Qed.

  Lemma IsVar_senv_of_decls : forall x locs,
      IsVar (senv_of_decls locs) x <-> InMembers x locs.
  Proof.
    split; intros * Hiv; [inv Hiv|constructor]; autorewrite with list in *; auto.
  Qed.

  Global Hint Rewrite -> @IsVar_senv_of_decls.

  Lemma IsLast_senv_of_decls : forall x locs,
      IsLast (senv_of_decls locs) x -> InMembers x locs.
  Proof.
    intros * Hiv; inv Hiv; solve_In.
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

  Lemma senv_of_ins_NoLast : forall Γ,
    forall x, ~IsLast (senv_of_ins Γ) x.
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

  Lemma senv_HasType :
    forall l x ty ck i,
      In (x,(ty,ck,i)) l ->
      HasType (senv_of_ins l) x ty.
  Proof.
    intros * Hin.
    unfold senv_of_ins.
    econstructor; eauto.
    apply in_map_iff.
    exists (x,(ty,ck,i)); auto. auto.
  Qed.

  Lemma senv_HasClock :
    forall l x ty ck i,
      In (x,(ty,ck,i)) l ->
      HasClock (senv_of_ins l) x ck.
  Proof.
    intros * Hin.
    unfold senv_of_ins.
    econstructor; eauto.
    apply in_map_iff.
    exists (x,(ty,ck,i)); auto. auto.
  Qed.

  Lemma In_HasType :
    forall x l, In x (List.map fst l) ->
           exists ty, HasType (senv_of_ins l) x ty.
  Proof.
    unfold senv_of_ins.
    intros * Hin.
    apply in_map_iff in Hin as ((?&(ty,?)&?)&?&?); simpl in *; subst.
    exists ty.
    econstructor.
    rewrite in_map_iff.
    esplit; split; now eauto.
    reflexivity.
  Qed.

  Lemma HasType_det :
    forall Γ x ty1 ty2,
      NoDupMembers Γ ->
      HasType Γ x ty1 ->
      HasType Γ x ty2 ->
      ty1 = ty2.
  Proof.
    intros * ND C1 C2; inv C1; inv C2.
    eapply NoDupMembers_det with (t := e) in ND; eauto.
    now subst.
  Qed.

  Lemma HasClock_det :
    forall Γ x ck1 ck2,
      NoDupMembers Γ ->
      HasClock Γ x ck1 ->
      HasClock Γ x ck2 ->
      ck1 = ck2.
  Proof.
    intros * ND C1 C2; inv C1; inv C2.
    eapply NoDupMembers_det with (t := e) in ND; eauto.
    now subst.
  Qed.

  Global Hint Rewrite map_fst_senv_of_ins : list.

End STATICENV.

Module StaticEnvFun
       (Ids      : IDS)
       (Op       : OPERATORS)
       (OpAux    : OPERATORS_AUX Ids Op)
       (Cks      : CLOCKS Ids Op OpAux) <: STATICENV Ids Op OpAux Cks.
  Include STATICENV Ids Op OpAux Cks.
End StaticEnvFun.
