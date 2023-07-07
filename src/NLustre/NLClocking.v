From Coq Require Import FSets.FMapPositive.
From Velus Require Import Common.
From Velus Require Import CommonProgram.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import FunctionalEnvironment.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import NLustre.Memories.
From Velus Require Import NLustre.IsDefined.
From Velus Require Import NLustre.NLOrdered.
From Velus Require Import CoreExpr.CEClocking.

From Coq Require Import List.
From Coq Require Import Morphisms.
From Coq Require Import Permutation.

(** * Well clocked programs *)

(**

This family of predicates states that a program is well-clocked
wrt. its clock annotations.

 *)

Module Type NLCLOCKING
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX  Ids Op)
       (Import Cks   : CLOCKS         Ids Op OpAux)
       (Import CESyn : CESYNTAX       Ids Op OpAux Cks)
       (Import Syn   : NLSYNTAX   Ids Op OpAux Cks CESyn)
       (Import Ord   : NLORDERED  Ids Op OpAux Cks CESyn Syn)
       (Import Mem   : MEMORIES   Ids Op OpAux Cks CESyn Syn)
       (Import IsD   : ISDEFINED  Ids Op OpAux Cks CESyn Syn Mem)
       (Import CEClo : CECLOCKING Ids Op OpAux Cks CESyn).

  Inductive wc_equation (G: global) (Γ: list (ident * (clock * bool))): equation -> Prop :=
  | CEqDef:
      forall x ck islast ce,
        In (x, (ck, islast)) Γ ->
        wc_rhs Γ ce ck ->
        wc_equation G Γ (EqDef x ck ce)
  | CEqLast:
      forall x ty ck c0 xrs,
        In (x, (ck, true)) Γ ->
        Forall (fun '(x, ck) => exists islast, In (x, (ck, islast)) Γ) xrs ->
        wc_equation G Γ (EqLast x ty ck c0 xrs)
  | CEqApp:
      forall xs ck f les xrs n sub,
        find_node f G = Some n ->
        Forall2 (fun '(x, (_, xck)) le =>
                   SameVar (sub x) le
                   /\ exists lck, wc_exp Γ le lck
                            /\ instck ck sub xck = Some lck)
                n.(n_in) les ->
        Forall2 (fun '(y, (_, yck)) x =>
                   sub y = Some x
                   /\ exists xck islast, In (x, (xck, islast)) Γ
                            /\ instck ck sub yck = Some xck)
                n.(n_out) xs ->
        Forall (fun '(x, ck) => exists islast, In (x, (ck, islast)) Γ) xrs ->
        wc_equation G Γ (EqApp xs ck f les xrs)
  | CEqFby:
      forall x ck v0 le xrs,
        In (x, (ck, false)) Γ ->
        wc_exp Γ le ck ->
        Forall (fun '(x, ck) => exists islast, In (x, (ck, islast)) Γ) xrs ->
        wc_equation G Γ (EqFby x ck v0 le xrs).

  Definition wc_node (G: global) (n: node) : Prop :=
    wc_env (idsnd (n.(n_in))) /\
    wc_env (idsnd (n.(n_in) ++ n.(n_out))) /\
    wc_env (idsnd (n.(n_in) ++ idfst n.(n_vars) ++ n.(n_out))) /\
    Forall (wc_equation G (map (fun '(x, (_, ck)) => (x, (ck, false))) (n.(n_in) ++ n.(n_out))
                                ++ map (fun '(x, (_, ck, islast)) => (x, (ck, islast))) n.(n_vars)))
              n.(n_eqs).

  Definition wc_global (G: global) :=
    Forall' (fun ns => wc_node (Global G.(types) G.(externs) ns)) G.(nodes).

  Inductive Has_clock_eq: clock -> equation -> Prop :=
  | HcEqDef: forall x ck ce,
      Has_clock_eq ck (EqDef x ck ce)
  | HcEqLast: forall x ty ck c0 r,
      Has_clock_eq ck (EqLast x ty ck c0 r)
  | HcEqApp: forall x f ck les r,
      Has_clock_eq ck (EqApp x ck f les r)
  | HcEqFby: forall x v0 ck le r,
      Has_clock_eq ck (EqFby x ck v0 le r).

  Global Hint Constructors wc_clock wc_exp wc_cexp wc_equation Has_clock_eq : nlclocking.
  Global Hint Unfold wc_env wc_node : nlclocking.
  Global Hint Resolve Forall_nil : datatypes.

  Global Instance wc_equation_Proper:
    Proper (@eq global ==> @Permutation _ ==> @eq equation ==> iff)
           wc_equation.
  Proof.
    intros G1 G2 Hg env1 env2 Henv eq1 eq2 Heq; subst.
    split; intro WTeq; inv WTeq; econstructor; eauto;
      simpl_Forall; destruct_conjs; repeat esplit; eauto.
    all:try rewrite Henv; eauto.
    all:try rewrite <-Henv; eauto.
  Qed.

  Lemma wc_global_app_weaken:
    forall G G' enums externs,
      wc_global (Global enums externs (G' ++ G)) ->
      wc_global (Global enums externs G).
  Proof.
    induction G'; auto.
    inversion_clear 1. auto.
  Qed.

  Lemma wc_find_node:
    forall G f node enums externs,
      wc_global (Global enums externs G) ->
      find_node f (Global enums externs G) = Some node ->
      exists G'' G',
        G = G'' ++ node :: G'
        /\ wc_node (Global enums externs G') node.
  Proof.
    intros * WCG Hfind.
    apply find_node_split in Hfind as (G'' & G' & HG); simpl in HG.
    rewrite HG in *.
    apply wc_global_app_weaken in WCG.
    inversion_clear WCG. eauto.
  Qed.

  Lemma wc_equation_global_cons:
    forall Ω nd G eq types externs,
      Ordered_nodes (Global types externs (nd :: G)) ->
      wc_equation (Global types externs G) Ω eq ->
      wc_equation (Global types externs (nd :: G)) Ω eq.
  Proof.
    intros * OnG WCnG.
    inversion_clear OnG as [|? ? [? HndG] OG].
    inversion_clear WCnG; eauto using wc_equation.
    econstructor; eauto.
    unfold find_node, option_map, find_unit; simpl.
    destruct (ident_eq_dec (n_name nd) f); auto.
    assert (find_node f (Global types0 externs0 G) <> None) as Hfind by congruence.
    apply find_node_Exists in Hfind.
    apply decidable_Exists_not_Forall in Hfind.
    - subst; contradiction.
    - auto using decidable_eq_ident.
  Qed.

  Lemma wc_equation_global_app:
    forall Ω G' G eq types externs,
      Ordered_nodes (Global types externs (G' ++ G)) ->
      wc_equation (Global types externs G) Ω eq ->
      wc_equation (Global types externs (G' ++ G)) Ω eq.
  Proof.
    induction G'; auto.
    simpl. intros * OG WCeq.
    eapply wc_equation_global_cons in OG; eauto.
    inv OG. auto.
  Qed.

  (** Properties *)

  Section Well_clocked.

    (** We work under a (valid) clocking environment *)
    Variable G : global.
    Variable Γ : list (ident * (clock * bool)).
    Variable Hnd : NoDupMembers Γ.
    Variable Hwc : wc_env (idfst Γ).

    Lemma wc_equation_not_Is_free_in_clock:
      forall eq x ck,
        wc_equation G Γ eq
        -> Is_defined_in_eq (Var x) eq
        -> Has_clock_eq ck eq
        -> ~Is_free_in_clock x ck.
    Proof.
      intros eq x' ck' Hwce Hdef Hhasck Hfree.
      assert (NoDupMembers (idfst Γ)) as ND' by (now apply NoDupMembers_idfst).
      inversion Hwce
        as [x ck islast e Hcv Hexp Heq|
           |xs ck f e r n sub Hfind Hisub Hosub Heq
           |x ck v' e r Hcv Hexp Hr]; subst;
        inv Hdef; inv Hhasck.
      - (* Def *)
        eapply wc_env_var in Hwc as Hclock; [|solve_In].
        eapply Is_free_in_clock_parent in Hfree as Hpar; eauto. 2:solve_In.
        eapply clock_parent_not_refl; eauto.
      - (* App *)
        rename x' into x.
        match goal with H:List.In x xs |- _ => rename H into Hin end.
        destruct (Forall2_in_right _ _ _ _ Hosub Hin)
          as ((?&?&?) & Ho & (Hxeq & xck & ? & Hxck & Hxi)).
        eapply wc_env_var in Hwc as Hclock; [|solve_In].
        apply Is_free_in_clock_self_or_parent in Hfree.
        apply instck_parent in Hxi.
        destruct Hxi as [Hxi|Hxi]; destruct Hfree as (ck' & b & [Hck|Hck]); subst.
        + apply wc_clock_sub with (1:=Hwc) in Hclock.
          eapply clock_no_loops, NoDupMembers_det; eauto. clear Hclock; solve_In.
        + apply wc_clock_parent with (1:=Hwc) (2:=Hck) in Hclock.
          apply wc_clock_sub with (1:=Hwc) in Hclock.
          eapply NoDupMembers_det in Hclock; auto. 2:clear Hclock; solve_In.
          subst. apply clock_parent_parent' in Hck.
          apply clock_parent_not_refl with (1:=Hck).
        + apply wc_clock_parent with (1:=Hwc) (2:=Hxi) in Hclock.
          apply clock_parent_parent' in Hxi.
          apply wc_clock_sub with (1:=Hwc) in Hclock.
          eapply NoDupMembers_det in Hclock; auto. 2:clear Hclock; solve_In.
          subst. apply clock_parent_not_refl with (1:=Hxi).
        + apply wc_clock_parent with (1:=Hwc) (2:=Hxi) in Hclock.
          apply wc_clock_parent with (1:=Hwc) (2:=Hck) in Hclock.
          apply wc_clock_sub with (1:=Hwc) in Hclock.
          eapply NoDupMembers_det in Hclock; auto. 2:clear Hclock; solve_In.
          subst. apply clock_parent_parent' in Hck.
          apply clock_parent_trans with (1:=Hck) in Hxi.
          apply clock_parent_not_refl with (1:=Hxi).
      - eapply wc_env_var in Hwc as Hclock; [|solve_In].
        eapply Is_free_in_clock_parent in Hfree as Hpar; eauto. 2:solve_In.
        eapply clock_parent_not_refl; eauto.
    Qed.

    Corollary wc_EqDef_not_Is_free_in_clock:
      forall x ce ck,
        wc_equation G Γ (EqDef x ck ce)
        -> ~Is_free_in_clock x ck.
    Proof.
      intros x ce ck Hwce Hwt.
      eapply wc_equation_not_Is_free_in_clock; eauto with nldef nlclocking.
    Qed.

    Corollary wc_EqApp_not_Is_free_in_clock:
      forall xs f le r ck,
        wc_equation G Γ (EqApp xs ck f le r)
        -> forall x, List.In x xs -> ~Is_free_in_clock x ck.
    Proof.
      intros x f le ck Hwce Hwt y Hinx.
      eapply wc_equation_not_Is_free_in_clock; eauto with nldef nlclocking.
    Qed.

    Corollary wc_EqFby_not_Is_free_in_clock:
      forall x v0 le ck r,
        wc_equation G Γ (EqFby x ck v0 le r)
        -> ~Is_free_in_clock x ck.
    Proof.
      intros x v0 le ck Hwce Hwt.
      eapply wc_equation_not_Is_free_in_clock; eauto with nldef nlclocking.
    Qed.

  End Well_clocked.

  Lemma global_iface_eq_wc_eq : forall G1 G2 vars eq,
      global_iface_eq G1 G2 ->
      wc_equation G1 vars eq ->
      wc_equation G2 vars eq.
  Proof.
    intros * Heq Hwc.
    destruct Heq as (Henums&Hexterns&Heq).
    inv Hwc. 1,2,4:econstructor; eauto; try congruence.
    specialize (Heq f). rewrite H in Heq. inv Heq.
    destruct H5 as (?&?&?).
    symmetry in H4. eapply CEqApp with (sub:=sub); eauto; try congruence.
  Qed.

  Section incl.
    Variable (G : global).
    Variable (Γ Γ' : list (ident * (clock * bool))).
    Hypothesis Hincl : incl Γ Γ'.

    Lemma wc_equation_incl : forall equ,
        wc_equation G Γ equ ->
        wc_equation G Γ' equ.
    Proof.
      intros * Hwc; inv Hwc; econstructor; simpl_Forall; eauto with nlclocking.
      1,2:simpl_Forall; destruct_conjs; eauto 6 with nlclocking.
    Qed.

  End incl.

End NLCLOCKING.

Module NLClockingFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX  Ids Op)
       (Cks   : CLOCKS         Ids Op OpAux)
       (CESyn : CESYNTAX       Ids Op OpAux Cks)
       (Syn   : NLSYNTAX   Ids Op OpAux Cks CESyn)
       (Ord   : NLORDERED  Ids Op OpAux Cks CESyn Syn)
       (Mem   : MEMORIES   Ids Op OpAux Cks CESyn Syn)
       (IsD   : ISDEFINED  Ids Op OpAux Cks CESyn Syn Mem)
       (CEClo : CECLOCKING Ids Op OpAux Cks CESyn)
  <: NLCLOCKING Ids Op OpAux Cks CESyn Syn Ord Mem IsD CEClo.
  Include NLCLOCKING Ids Op OpAux Cks CESyn Syn Ord Mem IsD CEClo.
End NLClockingFun.
