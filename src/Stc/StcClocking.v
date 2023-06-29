From Coq Require Import FSets.FMapPositive.
From Velus Require Import Common.
From Velus Require Import CommonProgram.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import Stc.StcSyntax.
From Velus Require Import CoreExpr.CEClocking.
From Velus Require Import Stc.StcOrdered.
From Velus Require Import CoreExpr.CEIsFree.
From Velus Require Import Stc.StcIsFree.

From Coq Require Import List.
From Coq Require Import Morphisms.
From Coq Require Import Permutation.

(** * Well clocked programs *)

(**

This family of predicates states that a program is well-clocked
wrt. its clock annotations.

 *)

Module Type STCCLOCKING
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks   : CLOCKS        Ids Op OpAux)
       (Import CESyn : CESYNTAX      Ids Op OpAux Cks)
       (Import Syn   : STCSYNTAX     Ids Op OpAux Cks CESyn)
       (Import Ord   : STCORDERED    Ids Op OpAux Cks CESyn Syn)
       (Import CEClo : CECLOCKING    Ids Op OpAux Cks CESyn).

  Inductive wc_trconstr {prefs} (P: @program prefs) (Γ: list (ident * (clock * bool))): trconstr -> Prop :=
  | CTcDef:
      forall x ck e,
        In (x, (ck, false)) Γ ->
        wc_rhs Γ e ck ->
        wc_trconstr P Γ (TcDef ck x e)
  | CTcResetState:
      forall x ck islast ckr ty c0,
        In (x, (ck, islast)) Γ ->
        wc_clock (idfst Γ) ckr ->
        wc_trconstr P Γ (TcReset ckr (ResState x ty c0))
  | CTcUpdateLast:
      forall ck ckrs x e,
        In (x, (ck, true)) Γ ->
        wc_cexp Γ e ck ->
        wc_trconstr P Γ (TcUpdate ck ckrs (UpdLast x e))
  | CTcUpdateNext:
      forall x ck ckrs e,
        In (x, (ck, false)) Γ ->
        wc_exp Γ e ck ->
        wc_trconstr P Γ (TcUpdate ck ckrs (UpdNext x e))
  | CTcResetInst:
      forall ck i f,
        wc_clock (idfst Γ) ck ->
        wc_trconstr P Γ (TcReset ck (ResInst i f))
  | CTcApp:
      forall ck ckrs i xs f es s P' sub,
        find_system f P = Some (s, P') ->
        Forall2 (fun '(x, (_, xck)) le =>
                   SameVar (sub x) le
                   /\ exists lck, wc_exp Γ le lck
                            /\ instck ck sub xck = Some lck)
                s.(s_in) es ->
        Forall2 (fun '(y, (_, yck)) x =>
                   sub y = Some x
                   /\ exists xck, In (x, (xck, false)) Γ
                            /\ instck ck sub yck = Some xck)
                s.(s_out) xs ->
        wc_trconstr P Γ (TcUpdate ck ckrs (UpdInst i xs f es)).

  Definition wc_system {prefs} (P: @program prefs) (s: @system prefs) : Prop :=
    wc_env (idsnd (s.(s_in))) /\
    wc_env (idsnd (s.(s_in) ++ s.(s_out))) /\
    wc_env (idsnd (s.(s_in) ++ s.(s_vars) ++ s.(s_out)) ++ idsnd s.(s_lasts) ++ idsnd s.(s_nexts)) /\
    Forall (wc_trconstr P
              (map (fun '(x, (_, ck)) => (x, (ck, false))) (s.(s_in) ++ s.(s_vars) ++ s.(s_out))
                 ++ map (fun '(x, (_, _, ck)) => (x, (ck, true))) s.(s_lasts)
                 ++ map (fun '(x, (_, _, ck)) => (x, (ck, false))) s.(s_nexts)))
           s.(s_tcs).

  Definition wc_program {prefs} (P: @program prefs) :=
    Forall' (fun P' => wc_system (Program P.(types) P.(externs) P')) P.(systems).

  Inductive Has_clock_tc: clock -> trconstr -> Prop :=
  | HcTcDef:
      forall ck x e,
        Has_clock_tc ck (TcDef ck x e)
  | HcTcReset:
      forall ckr rsconstr,
        Has_clock_tc ckr (TcReset ckr rsconstr)
  | HcTcUpdate:
      forall ck ckrs updconstr,
        Has_clock_tc ck (TcUpdate ck ckrs updconstr).

  Global Hint Constructors wc_clock wc_exp wc_cexp wc_trconstr : stcclocking.
  Global Hint Unfold wc_env wc_system : stcclocking.

  Global Instance wc_trconstr_Proper {prefs}:
    Proper (@eq (@program prefs) ==> @Permutation _ ==> @eq trconstr ==> iff)
           wc_trconstr.
  Proof with eauto with stcclocking.
    intros ??? env1 env2 Henv eq1 eq2 Htc; subst.
    split; intro WTtc; inv WTtc; econstructor...
    all:simpl_Forall; destruct_conjs; repeat (esplit; eauto).
    all:unfold idfst; rewrite ?Henv; eauto; rewrite <-?Henv; eauto.
  Qed.

  Lemma wc_trconstr_incl {prefs} (P: @program prefs) : forall Γ Γ' tr,
      incl Γ Γ' ->
      wc_trconstr P Γ tr ->
      wc_trconstr P Γ' tr.
  Proof.
    intros * Incl Wc. inv Wc; econstructor; eauto with stcclocking.
    1,2:simpl_Forall; eauto with stcclocking.
  Qed.

  Lemma wc_program_app_weaken {prefs}:
    forall (P P' : list (@system prefs)) enums externs,
      wc_program (Program enums externs (P' ++ P)) ->
      wc_program (Program enums externs P).
  Proof.
    induction P'; auto.
    inversion_clear 1; auto.
  Qed.

  Lemma wc_find_system {prefs}:
    forall (P: @program prefs) f b P',
      wc_program P ->
      find_system f P = Some (b, P') ->
      wc_system P' b.
  Proof.
    intros [] * WCG Hfind.
    assert (types0 = types P')
      by (apply find_unit_equiv_program in Hfind; specialize (Hfind nil); inv Hfind; auto).
    assert (externs0 = externs P')
      by (apply find_unit_equiv_program in Hfind; specialize (Hfind nil); inv Hfind; auto).
    apply find_unit_spec in Hfind as (?&?&?&?); simpl in *; subst.
    apply wc_program_app_weaken in WCG.
    inversion_clear WCG; destruct P'; auto.
  Qed.

  Lemma wc_trconstr_program_cons {prefs}:
    forall vars b (P: list (@system prefs)) tc enums externs,
      Ordered_systems (Program enums externs (b :: P)) ->
      wc_trconstr (Program enums externs P) vars tc ->
      wc_trconstr (Program enums externs (b :: P)) vars tc.
  Proof.
    intros * OnG WCnG.
    inversion_clear OnG as [|?? []].
    inversion_clear WCnG as [| | | | |????????? Find]; eauto with stcclocking.
    econstructor; eauto.
    rewrite find_system_other; eauto.
    intro; subst.
    apply find_unit_In in Find as (?& Hin).
    eapply Forall_forall in Hin; eauto; simpl in *; congruence.
  Qed.

  Lemma wc_trconstr_program_app {prefs}:
    forall vars (P' P: list (@system prefs)) tc enums externs,
      Ordered_systems (Program enums externs (P' ++ P)) ->
      wc_trconstr (Program enums externs P) vars tc ->
      wc_trconstr (Program enums externs (P' ++ P)) vars tc.
  Proof.
    induction P'; auto.
    simpl. intros * OG WCtc.
    eapply wc_trconstr_program_cons in OG; eauto.
    inv OG. auto.
  Qed.

  Lemma wc_find_system' {prefs}:
    forall (P: @program prefs) f b P',
      Ordered_systems P ->
      wc_program P ->
      find_system f P = Some (b, P') ->
      wc_system P b.
  Proof.
    intros [] * OG WCG Hfind.
    induction systems0 as [|b' P IH]; try discriminate.
    eapply find_unit_cons in Hfind as [[E Hfind]|[E Hfind]]; simpl; eauto.
    - inv Hfind. inversion WCG as [|?? (WCi & WCo & WCv & WCtcs) WCG']; subst.
      constructor; repeat (try split; auto).
      simpl_Forall.
      apply wc_trconstr_program_cons; auto.
    - assert (OG' := OG).
      inversion_clear OG as [|?? [] OG''].
      inversion_clear WCG as [|??? WCG'].
      specialize (IH OG'' WCG' Hfind).
      destruct IH as (WCi & WCo & WCv & WCtcs).
      repeat (try split; auto).
      simpl_Forall.
      apply wc_trconstr_program_cons; auto.
  Qed.

  (** Properties *)

  Section Well_clocked.

    (** We work under a (valid) clocking environment *)
    Context {prefs : PS.t}.
    Variable P : @program prefs.
    Variable Γ : list (ident * (clock * bool)).
    Variable Hnd : NoDupMembers Γ.
    Variable Hwc : wc_env (idfst Γ).

    Fact wc_clock_not_Is_free_in_clock : forall x ck islast,
        wc_clock (idfst Γ) ck ->
        In (x, (ck, islast)) Γ ->
        ~ Is_free_in_clock x ck.
    Proof.
      intros * Wc In Free.
      apply Is_free_in_clock_self_or_parent in Free as (ck' & b & [Hck|Hck]).
      - subst.
        apply wc_clock_sub with (1:=Hwc) in Wc. simpl_In.
        eapply NoDupMembers_det in In; eauto. inv In.
        eapply clock_no_loops; eauto.
      - apply wc_clock_parent with (1:=Hwc) (2:=Hck) in Wc.
        apply wc_clock_sub with (1:=Hwc) in Wc. simpl_In.
        eapply NoDupMembers_det in Hin; eauto. inv Hin.
        apply clock_parent_parent' in Hck.
        eapply clock_parent_not_refl; eauto.
    Qed.

    Corollary wc_TcDef_not_Is_free_in_clock:
      forall x ce ck,
        wc_trconstr P Γ (TcDef ck x ce) ->
        ~ Is_free_in_clock x ck.
    Proof.
      intros * Hwctr Hfree.
      inversion_clear Hwctr as [??? Hin| | | | |].
      eapply wc_env_var in Hwc as Hclock. 2:solve_In.
      eapply wc_clock_not_Is_free_in_clock; eauto.
    Qed.

    Lemma wc_TcUpdateLast_not_Is_free_in_clock:
      forall ck ckrs x e,
        wc_trconstr P Γ (TcUpdate ck ckrs (UpdLast x e)) ->
        ~ Is_free_in_clock x ck.
    Proof.
      intros * Hwctr Hfree.
      inversion_clear Hwctr as [| |???? Hin He| | |].
      eapply wc_env_var in Hwc as Hclock. 2:solve_In.
      eapply wc_clock_not_Is_free_in_clock; eauto.
    Qed.

    Lemma wc_TcUpdateNext_not_Is_free_in_clock:
      forall ck ckrs x e,
        wc_trconstr P Γ (TcUpdate ck ckrs (UpdNext x e)) ->
        ~ Is_free_in_clock x ck.
    Proof.
      intros * Hwctr Hfree.
      inversion_clear Hwctr as [| |???? Hin He| | |].
      eapply wc_env_var in Hwc as Hclock. 2:solve_In.
      eapply wc_clock_not_Is_free_in_clock; eauto.
    Qed.

    Corollary wc_TcUpdateInst_not_Is_free_in_clock:
      forall ck ckrs s xs f es,
        wc_trconstr P Γ (TcUpdate ck ckrs (UpdInst s xs f es)) ->
        forall x, In x xs -> ~ Is_free_in_clock x ck.
    Proof.
      intros * Hwctr ? Hin Hfree.
      inversion_clear Hwctr as [| | | | |?????? b P' sub Hfind Hisub Hosub].
      match goal with H:List.In x xs |- _ => rename H into Hin end.
      destruct (Forall2_in_right _ _ _ _ Hosub Hin) as ((?&(?&?)) & Ho & Hxtc & xck & Hxck & Hxi).
      eapply wc_env_var in Hwc as Hclock. 2:solve_In.
      apply Is_free_in_clock_self_or_parent in Hfree.
      apply instck_parent in Hxi.
      destruct Hxi as [Hxi|Hxi]; destruct Hfree as (ck' & bb & [Hck|Hck]).
      - subst ck xck.
        apply wc_clock_sub with (1:=Hwc) in Hclock. simpl_In.
        eapply NoDupMembers_det in Hxck as Hloop; eauto. inv Hloop.
        eapply clock_no_loops; eauto.
      - subst ck.
        apply wc_clock_parent with (1:=Hwc) (2:=Hck) in Hclock.
        apply wc_clock_sub with (1:=Hwc) in Hclock. simpl_In.
        eapply NoDupMembers_det in Hxck as Hloop; eauto. inv Hloop.
        apply clock_parent_parent' in Hck.
        apply clock_parent_not_refl with (1:=Hck).
      - subst ck.
        apply wc_clock_parent with (1:=Hwc) (2:=Hxi) in Hclock.
        apply clock_parent_parent' in Hxi.
        apply wc_clock_sub with (1:=Hwc) in Hclock. simpl_In.
        eapply NoDupMembers_det in Hxck as Hloop; eauto. inv Hloop.
        apply clock_parent_not_refl with (1:=Hxi).
      - apply wc_clock_parent with (1:=Hwc) (2:=Hxi) in Hclock.
        apply wc_clock_parent with (1:=Hwc) (2:=Hck) in Hclock.
        apply wc_clock_sub with (1:=Hwc) in Hclock. simpl_In.
        eapply NoDupMembers_det in Hxck as Hloop; eauto. inv Hloop.
        apply clock_parent_parent' in Hck.
        apply clock_parent_trans with (1:=Hck) in Hxi.
        apply clock_parent_not_refl with (1:=Hxi).
    Qed.

  End Well_clocked.

End STCCLOCKING.

Module StcClockingFun
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks   : CLOCKS        Ids Op OpAux)
       (Import CESyn : CESYNTAX      Ids Op OpAux Cks)
       (Import Syn   : STCSYNTAX     Ids Op OpAux Cks CESyn)
       (Import Ord   : STCORDERED    Ids Op OpAux Cks CESyn Syn)
       (Import CEClo : CECLOCKING    Ids Op OpAux Cks CESyn)
  <: STCCLOCKING Ids Op OpAux Cks CESyn Syn Ord CEClo.
  Include STCCLOCKING Ids Op OpAux Cks CESyn Syn Ord CEClo.
End StcClockingFun.

Module Type STCCLOCKFREE
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks   : CLOCKS    Ids Op OpAux)
       (Import CESyn : CESYNTAX  Ids Op OpAux Cks)
       (Import Syn   : STCSYNTAX Ids Op OpAux Cks CESyn)
       (Import Ord   : STCORDERED    Ids Op OpAux Cks CESyn Syn)
       (Import CEClo : CECLOCKING    Ids Op OpAux Cks CESyn)
       (Import Clo   : STCCLOCKING   Ids Op OpAux Cks CESyn Syn Ord CEClo)
       (Import CEIsF : CEISFREE  Ids Op OpAux Cks CESyn)
       (Import Free  : STCISFREE Ids Op OpAux Cks CESyn Syn CEIsF).

  (** ** Last variables that appear in a wc constraint are declared as last *)

  Lemma Is_free_last_wc_exp : forall Γ e ck x,
      wc_exp Γ e ck ->
      CEIsF.Is_free_in_exp (FunctionalEnvironment.Last x) e ->
      exists ck, In (x, (ck, true)) Γ.
  Proof.
    induction e; intros * Wc F; inv Wc; inv F; eauto.
    take (_ \/ _) and destruct it; eauto.
  Qed.

  Lemma Is_free_last_wc_cexp : forall Γ e ck x,
      wc_cexp Γ e ck ->
      CEIsF.Is_free_in_cexp (FunctionalEnvironment.Last x) e ->
      exists ck, In (x, (ck, true)) Γ.
  Proof.
    induction e using cexp_ind2'; intros * Wc F; inv Wc; inv F; eauto using Is_free_last_wc_exp.
    - take (Forall2 _ _ _) and eapply Forall2_ignore1 in it.
      simpl_Exists; simpl_Forall; eauto.
    - simpl_Exists; subst; simpl_Forall; eauto.
  Qed.

  Lemma Is_free_last_wc_trconstr {prefs} : forall (P: @program prefs) Γ tc x,
      wc_trconstr P Γ tc ->
      Is_free_in_tc (FunctionalEnvironment.Last x) tc ->
      exists ck, In (x, (ck, true)) Γ.
  Proof.
    intros * Wc F; inv Wc; inv F.
    - (* def *)
      take (Is_free_in_arhs _ _ _) and inv it.
      take (wc_rhs _ _ _) and inv it; take (Is_free_in_rhs _ _) and inv it.
      + simpl_Exists. simpl_Forall. eauto using Is_free_last_wc_exp.
      + eauto using Is_free_last_wc_cexp.
    - (* upd last *)
      take (Is_free_in_acexp _ _ _) and inv it; eauto using Is_free_last_wc_cexp.
    - (* upd next *)
      take (Is_free_in_aexp _ _ _) and inv it; eauto using Is_free_last_wc_exp.
    - (* call *)
      apply Forall2_ignore1 in H0.
      take (Is_free_in_aexps _ _ _) and inv it.
      simpl_Exists. simpl_Forall. eauto using Is_free_last_wc_exp.
  Qed.

End STCCLOCKFREE.

Module StcClockFreeFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks   : CLOCKS    Ids Op OpAux)
       (CESyn : CESYNTAX  Ids Op OpAux Cks)
       (Syn   : STCSYNTAX Ids Op OpAux Cks CESyn)
       (Ord   : STCORDERED    Ids Op OpAux Cks CESyn Syn)
       (CEClo : CECLOCKING    Ids Op OpAux Cks CESyn)
       (Clo   : STCCLOCKING   Ids Op OpAux Cks CESyn Syn Ord CEClo)
       (CEIsF : CEISFREE  Ids Op OpAux Cks CESyn)
       (Free  : STCISFREE Ids Op OpAux Cks CESyn Syn CEIsF)
<: STCCLOCKFREE Ids Op OpAux Cks CESyn Syn Ord CEClo Clo CEIsF Free.
  Include STCCLOCKFREE Ids Op OpAux Cks CESyn Syn Ord CEClo Clo CEIsF Free.
End StcClockFreeFun.
