From Velus Require Import Common.
From Velus Require Import CommonTyping.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import Stc.StcSyntax.
From Velus Require Import CoreExpr.CETyping.

From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Coq Require Import Morphisms.

(** * Stc typing *)

(**

  Typing judgements for Stc and resulting properties.

 *)

Module Type STCTYPING
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks   : CLOCKS    Ids Op OpAux)
       (Import CESyn : CESYNTAX  Ids Op OpAux Cks)
       (Import Syn   : STCSYNTAX Ids Op OpAux Cks CESyn)
       (Import CETyp : CETYPING  Ids Op OpAux Cks CESyn).

  Inductive wt_trconstr {prefs} (P: @program prefs) (Γ: list (ident * (type * bool))): trconstr -> Prop :=
  | wt_TcDef:
      forall x ck e,
        In (x, (typeofr e, false)) Γ ->
        wt_clock P.(types) Γ ck ->
        wt_rhs P.(types) P.(externs) Γ e ->
        wt_trconstr P Γ (TcDef ck x e)
  | wt_TcResetState:
      forall x ckr ty islast c0,
        In (x, (ty, islast)) Γ ->
        wt_const P.(types) c0 ty ->
        wt_clock P.(types) Γ ckr ->
        wt_trconstr P Γ (TcReset ckr (ResState x ty c0))
  | wt_TcUpdateLast:
      forall x ck ckrs e,
        In (x, (typeofc e, true)) Γ ->
        wt_clock P.(types) Γ ck ->
        wt_cexp P.(types) Γ e ->
        wt_trconstr P Γ (TcUpdate ck ckrs (UpdLast x e))
  | wt_TcUpdateNext:
      forall x ck ckrs e,
        In (x, (typeof e, false)) Γ ->
        wt_clock P.(types) Γ ck ->
        wt_exp P.(types) Γ e ->
        wt_trconstr P Γ (TcUpdate ck ckrs (UpdNext x e))
  | wt_TcResetInst:
      forall s ck f i P',
        find_system f P = Some (s, P') ->
        wt_clock P.(types) Γ ck ->
        wt_trconstr P Γ (TcReset ck (ResInst i f))
  | wt_TcCall:
      forall s xs ck rst f es i P',
        find_system f P = Some (s, P') ->
        Forall2 (fun x '(_, (t, _)) => In (x, (t, false)) Γ) xs s.(s_out) ->
        Forall2 (fun e '(_, (t, _)) => typeof e = t) es s.(s_in) ->
        wt_clock P.(types) Γ ck ->
        Forall (wt_exp P.(types) Γ) es ->
        wt_trconstr P Γ (TcUpdate ck rst (UpdInst i xs f es)).

  Definition wt_states {prefs} (P: @program prefs) : list (ident * (const * type * clock)) -> Prop :=
    Forall (fun '(_, (c, t, _)) => wt_const P.(types) c t).

  Definition wt_system {prefs} (P: @program prefs) (s: @system prefs) : Prop :=
        Forall (wt_trconstr P
                  (map (fun '(x, (ty, ck)) => (x, (ty, false))) (s.(s_in) ++ s.(s_vars) ++ s.(s_out))
                     ++ map (fun '(x, (_, ty, _)) => (x, (ty, true))) s.(s_lasts)
                     ++ map (fun '(x, (_, ty, _)) => (x, (ty, false))) s.(s_nexts)))
               s.(s_tcs)
        /\ wt_states P (s.(s_lasts) ++ s.(s_nexts))
        /\ forall x ty,
            In (x, ty) (idfst (s_in s ++ s_vars s ++ s_out s) ++ idsnd (idfst (s_lasts s ++ s_nexts s))) ->
            wt_type P.(types) ty.

  Definition wt_program {prefs} := CommonTyping.wt_program (@wt_system prefs).

  Global Hint Constructors wt_clock wt_trconstr : stctyping.

  Global Instance wt_trconstr_Proper {prefs} :
    Proper (@eq (@program prefs) ==> @Permutation.Permutation _
                ==> @eq trconstr ==> iff)
           wt_trconstr.
  Proof.
    intros G1 G2 HG env1 env2 Henv eq1 eq2 Heq.
    subst.
    split; intro WTtc.
    - inv WTtc; rewrite Henv in *; econstructor; eauto;
        match goal with H:Forall2 _ ?x ?y |- Forall2 _ ?x ?y =>
                        apply Forall2_impl_In with (2:=H) end;
        intros ? (?&(?&?)); rewrite Henv in *; auto.
    - inv WTtc; rewrite <-Henv in *; econstructor; eauto;
          match goal with H:Forall2 _ ?x ?y |- Forall2 _ ?x ?y =>
                          apply Forall2_impl_In with (2:=H) end;
          intros ? (?&(?&?)); rewrite Henv in *; auto.
  Qed.

  Lemma wt_trconstr_incl {prefs} (P: @program prefs) : forall Γ Γ' tr,
      incl Γ Γ' ->
      wt_trconstr P Γ tr ->
      wt_trconstr P Γ' tr.
  Proof.
    intros * Incl Wt. inv Wt; econstructor; eauto with stctyping.
    1,2:simpl_Forall; eauto with stctyping.
  Qed.

  Fact s_lasts_of_mems_of_states {prefs} (P: @program prefs) : forall s,
      wt_system P s ->
      incl (lasts_of (s_tcs s)) (mems_of_states (s_lasts s)).
  Proof.
    intros ? (Wt1&_&_) ? L.
    induction Wt1; simpl in *. inv L.
    destruct x; auto. destruct u; auto.
    inv L; auto. inv H.
    take (In _ _) and rewrite ? in_app_iff in it. destruct it as [|[|]]; simpl_In.
    unfold mems_of_states. solve_In.
  Qed.

  Corollary s_lasts_of_mems_of_states_iff {prefs} (P: @program prefs) : forall s,
      wt_system P s ->
      forall x ty, In (x, ty) (lasts_of (s_tcs s)) <-> In (x, ty) (mems_of_states (s_lasts s)).
  Proof.
    intros * Wts. unfold mems_of_states in *.
    split; intros.
    - eapply s_lasts_of_mems_of_states; eauto.
    - assert (InMembers x (lasts_of (s_tcs s))).
      { rewrite fst_InMembers, <-s_lasts_in_tcs. solve_In. }
      simpl_In.
      assert (t = ty); subst; auto.
      destruct Wts as (Wt1&_&_).
      induction Wt1; simpl in *. inv Hin.
      destruct x0; auto. destruct u; auto.
      inv Hin; auto. inv H0. inv H.
      take (In _ _) and rewrite ? in_app_iff in it. destruct it as [|[|]]; simpl_In.
      pose proof (s_nodup s) as ND. apply NoDup_app_r, NoDup_app_r, NoDup_app_r, NoDup_app_l, fst_NoDupMembers in ND.
      eapply NoDupMembers_det in Hin0; eauto. now inv Hin0.
  Qed.

  Fact s_nexts_of_mems_of_states {prefs} (P: @program prefs) : forall s,
      wt_system P s ->
      incl (nexts_of (s_tcs s)) (mems_of_states (s_nexts s)).
  Proof.
    intros ? (Wt1&_&_) [] L.
    assert (~InMembers i (s_in s ++ s_vars s ++ s_out s)) as Nin.
    { apply In_InMembers, fst_InMembers in L.
      rewrite <-s_nexts_in_tcs in L. rewrite fst_InMembers, ? map_app.
      pose proof (s_nodup s) as ND. intros ?.
      rewrite 2 app_assoc, <-app_assoc with (l:=map fst (s_in _)) in ND.
      eapply NoDup_app_In in ND; eauto using in_or_app.
    }
    induction Wt1; simpl in *. inv L.
    destruct x; auto. destruct u; auto.
    inv L; auto. inv H.
    take (In _ _) and rewrite ? in_app_iff in it. destruct it as [|[|]]; simpl_In.
    - exfalso. eapply Nin. solve_In.
    - unfold mems_of_states. solve_In.
  Qed.

  Corollary s_nexts_of_mems_of_states_iff {prefs} (P: @program prefs) : forall s,
      wt_system P s ->
      forall x ty, In (x, ty) (nexts_of (s_tcs s)) <-> In (x, ty) (mems_of_states (s_nexts s)).
  Proof.
    intros * Wts. unfold mems_of_states in *.
    split; intros.
    - eapply s_nexts_of_mems_of_states; eauto.
    - assert (InMembers x (nexts_of (s_tcs s))).
      { rewrite fst_InMembers, <-s_nexts_in_tcs. solve_In. }
      assert (~InMembers x (s_in s ++ s_vars s ++ s_out s)) as Nin.
      { apply fst_InMembers in H0. rewrite <-s_nexts_in_tcs in H0.
        rewrite fst_InMembers, ? map_app.
        pose proof (s_nodup s) as ND. intros ?.
        rewrite 2 app_assoc, <-app_assoc with (l:=map fst (s_in _)) in ND.
        eapply NoDup_app_In in ND; eauto using in_or_app.
      }
      simpl_In.
      assert (t = ty); subst; auto.
      destruct Wts as (Wt1&_&_).
      induction Wt1; simpl in *. inv Hin.
      destruct x0; auto. destruct u; auto.
      inv Hin; auto. inv H0. inv H.
      take (In _ _) and rewrite ? in_app_iff in it. destruct it as [|[|]]; simpl_In.
      1:{ exfalso. eapply Nin. solve_In. }
      pose proof (s_nodup s) as ND. apply NoDup_app_r, NoDup_app_r, NoDup_app_r, NoDup_app_r, fst_NoDupMembers in ND.
      eapply NoDupMembers_det in Hin0; eauto. now inv Hin0.
  Qed.

End STCTYPING.

Module StcTypingFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks   : CLOCKS    Ids Op OpAux)
       (CESyn : CESYNTAX  Ids Op OpAux Cks)
       (Syn   : STCSYNTAX Ids Op OpAux Cks CESyn)
       (CETyp : CETYPING  Ids Op OpAux Cks CESyn)
       <: STCTYPING Ids Op OpAux Cks CESyn Syn CETyp.
  Include STCTYPING Ids Op OpAux Cks CESyn Syn CETyp.
End StcTypingFun.
