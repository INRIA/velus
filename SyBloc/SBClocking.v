Require Import Coq.FSets.FMapPositive.
Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.Clocks.
Require Import Velus.CoreExpr.CESyntax.
Require Import Velus.SyBloc.SBSyntax.
Require Import Velus.CoreExpr.CEClocking.
Require Import Velus.SyBloc.SBIsLast.
Require Import Velus.SyBloc.SBIsVariable.
Require Import Velus.SyBloc.SBIsDefined.

Require Import List.

(** * Well clocked programs *)

(**

This family of predicates states that a program is well-clocked
wrt. its clock annotations.

 *)

Module Type SBCLOCKING
       (Import Ids     : IDS)
       (Import Op      : OPERATORS)
       (Import Clks    : CLOCKS         Ids)
       (Import CESyn : CESYNTAX       Op)
       (Import Syn     : SBSYNTAX       Ids Op Clks CESyn)
       (Import Last    : SBISLAST       Ids Op Clks CESyn Syn)
       (Import Var     : SBISVARIABLE   Ids Op Clks CESyn Syn)
       (Import Def     : SBISDEFINED    Ids Op Clks CESyn Syn Var Last)
       (Import CEClo : CECLOCKING Ids Op Clks CESyn).


  Inductive wc_equation (vars: list (ident * clock)): equation -> Prop :=
  | CEqDef:
      forall x ck e,
        In (x, ck) vars ->
        wc_cexp vars e ck ->
        wc_equation vars (EqDef x ck e)
  | CEqFby:
      forall x ck e,
        In (x, ck) vars ->
        wc_lexp vars e ck ->
        wc_equation vars (EqNext x ck e)
  | CEqReset:
      forall s ck f,
        wc_clock vars ck ->
        wc_equation vars (EqReset s ck f)
  | CEqApp:
      forall s xs ck rst f es,
        Forall (fun x => In (x, ck) vars) xs ->
        Forall (fun e => wc_lexp vars e ck) es ->
        wc_equation vars (EqCall s xs ck rst f es).

  Definition wc_block (b: block) : Prop :=
    wc_env (idck (b.(b_in))) /\
    wc_env (idck (b.(b_in) ++ b.(b_out))) /\
    wc_env (idck (b.(b_in) ++ b.(b_vars) ++ b.(b_out)) ++ idck b.(b_lasts)) /\
    Forall (wc_equation (idck (b.(b_in) ++ b.(b_vars) ++ b.(b_out)) ++ idck b.(b_lasts)))
           b.(b_eqs).

  Inductive wc_program : program -> Prop :=
  | wc_global_nil:
      wc_program nil
  | wc_global_cons:
      forall b bs,
      wc_program bs ->
      wc_block b ->
      wc_program (b :: bs).

  Inductive Has_clock_eq: clock -> equation -> Prop :=
  | HcEqDef:
      forall x ck e,
        Has_clock_eq ck (EqDef x ck e)
  | HcEqNext:
      forall x ck e,
        Has_clock_eq ck (EqNext x ck e)
  | HcEqReset:
      forall s ck f,
      Has_clock_eq ck (EqReset s ck f)
  | HcEqCall:
      forall s xs ck rst f es,
      Has_clock_eq ck (EqCall s xs ck rst f es).

  Hint Constructors wc_clock wc_lexp wc_cexp wc_equation wc_program.
  Hint Unfold wc_env wc_block.
  Hint Resolve Forall_nil.

  Require Import Morphisms.
  Import Permutation.

  Instance wc_equation_Proper:
    Proper (@Permutation (ident * clock) ==> @eq equation ==> iff)
           wc_equation.
  Proof.
    intros env1 env2 Henv eq1 eq2 Heq; subst.
    split; intro WTeq.
    - inv WTeq; try rewrite Henv in *; eauto.
      constructor; now setoid_rewrite <-Henv.
    - inv WTeq; try rewrite <-Henv in *; eauto with nlclocking.
      constructor; now setoid_rewrite Henv.
  Qed.

  Lemma wc_program_app_weaken:
    forall P P',
      wc_program (P' ++ P) ->
      wc_program P.
  Proof.
    induction P'; auto.
    inversion_clear 1; auto.
  Qed.

  Lemma wc_find_block:
    forall P f b P',
      wc_program P ->
      find_block f P = Some (b, P') ->
      wc_block b.
  Proof.
    intros ** WCG Hfind.
    apply find_block_app in Hfind as (?&?&?); subst.
    apply wc_program_app_weaken in WCG.
    inversion_clear WCG; auto.
  Qed.

  (* Lemma wc_equation_global_cons: *)
  (*   forall vars nd G eq, *)
  (*     Ordered_nodes (nd :: G) -> *)
  (*     wc_equation G vars eq -> *)
  (*     wc_equation (nd :: G) vars eq. *)
  (* Proof. *)
  (*   intros ** OnG WCnG. *)
  (*   inversion_clear OnG as [|? ? OG ? HndG]. *)
  (*   inversion_clear WCnG; eauto using wc_equation. *)
  (*   econstructor; eauto. *)
  (*   simpl. destruct (ident_eqb nd.(n_name) f) eqn:Hf; auto. *)
  (*   apply ident_eqb_eq in Hf. *)
  (*   rewrite Hf in *. *)
  (*   assert (find_node f G <> None) as Hfind by congruence. *)
  (*   apply find_node_Exists in Hfind. *)
  (*   apply decidable_Exists_not_Forall in Hfind. *)
  (*   - contradiction. *)
  (*   - auto using decidable_eq_ident. *)
  (* Qed. *)

  (* Lemma wc_equation_global_app: *)
  (*   forall vars G' G eq, *)
  (*     Ordered_nodes (G' ++ G) -> *)
  (*     wc_equation G vars eq -> *)
  (*     wc_equation (G' ++ G) vars eq. *)
  (* Proof. *)
  (*   induction G'; auto. *)
  (*   simpl. intros ** OG WCeq. *)
  (*   eapply wc_equation_global_cons in OG; eauto. *)
  (*   inv OG. auto. *)
  (* Qed. *)

  (* Lemma wc_find_node': *)
  (*   forall G f node, *)
  (*     Ordered_nodes G -> *)
  (*     wc_global G -> *)
  (*     find_node f G = Some node -> *)
  (*     wc_node G node. *)
  (* Proof. *)
  (*   intros ** OG WCG Hfind. *)
  (*   induction G as [|n' G IH]. discriminate. *)
  (*   simpl in *. *)
  (*   destruct (ident_eqb n'.(n_name) f) eqn:Heq. *)
  (*   - inv Hfind. inversion_clear WCG as [|? ? WCG' (WCi & WCo & WCv & WCeqs)]. *)
  (*     constructor; repeat (try split; auto). *)
  (*     apply Forall_impl_In with (2:=WCeqs). *)
  (*     intros. apply wc_equation_global_cons; auto. *)
  (*   - assert (OG' := OG). *)
  (*     inversion_clear OG as [|? ? OG'' ? ?]. *)
  (*     inversion_clear WCG as [|? ? WCG']. *)
  (*     specialize (IH OG'' WCG' Hfind). *)
  (*     destruct IH as (WCi & WCo & WCv & WCeqs). *)
  (*     repeat (try split; auto). *)
  (*     apply Forall_impl_In with (2:=WCeqs). *)
  (*     intros. apply wc_equation_global_cons; auto. *)
  (* Qed. *)

  (** Properties *)

  Section Well_clocked.

    (** We work under a (valid) clocking environment *)
    Variable vars : list (ident * clock).
    Variable Hnd : NoDupMembers vars.
    Variable Hwc : wc_env vars.

    Lemma wc_equation_not_Is_free_in_clock:
      forall eq x ck,
        wc_equation vars eq ->
        Is_defined_in_eq x eq ->
        Has_clock_eq ck eq ->
        ~ Is_free_in_clock x ck.
    Proof.
      intros eq x' ck' Hwce Hdef Hhasck Hfree.
      inversion Hwce as [??? Hin|??? Hin| |?????? Hvars Hexps];
        clear Hwce; subst; inv Hdef; inv Hhasck.
      - pose proof (wc_env_var _ _ _ Hwc Hin) as Hclock.
        apply Is_free_in_clock_self_or_parent in Hfree as (ck' & b & [Hck|Hck]).
        + subst.
          apply wc_clock_sub with (1:=Hwc) in Hclock.
          eapply NoDupMembers_det with (2 := Hin) in Hclock; eauto.
          eapply clock_no_loops; eauto.
        + apply wc_clock_parent with (1:=Hwc) (2:=Hck) in Hclock.
          apply wc_clock_sub with (1:=Hwc) in Hclock.
          eapply NoDupMembers_det with (2 := Hin) in Hclock; eauto; subst.
          apply clock_parent_parent' in Hck.
          eapply clock_parent_not_refl; eauto.
      - pose proof (wc_env_var _ _ _ Hwc Hin) as Hclock.
        apply Is_free_in_clock_self_or_parent in Hfree as (ck' & b & [Hck|Hck]).
        + subst.
          apply wc_clock_sub with (1:=Hwc) in Hclock.
          eapply NoDupMembers_det with (2 := Hin) in Hclock; eauto.
          eapply clock_no_loops; eauto.
        + apply wc_clock_parent with (1:=Hwc) (2:=Hck) in Hclock.
          apply wc_clock_sub with (1:=Hwc) in Hclock.
           eapply NoDupMembers_det with (2 := Hin) in Hclock; eauto; subst.
          apply clock_parent_parent' in Hck.
          eapply clock_parent_not_refl; eauto.
      - rename x' into x.
        match goal with H:In x xs |- _ => rename H into Hin end.
        eapply Forall_forall in Hin; eauto.
        pose proof (wc_env_var _ _ _ Hwc Hin) as Hclock.
        apply Is_free_in_clock_self_or_parent in Hfree as (ck' & b & [Hck|Hck]).
        + subst.
          apply wc_clock_sub with (1:=Hwc) in Hclock.
          eapply NoDupMembers_det with (2 := Hin) in Hclock; eauto.
          eapply clock_no_loops; eauto.
        + apply wc_clock_parent with (1:=Hwc) (2:=Hck) in Hclock.
          apply wc_clock_sub with (1:=Hwc) in Hclock.
          eapply NoDupMembers_det with (2 := Hin) in Hclock; eauto; subst.
          apply clock_parent_parent' in Hck.
          eapply clock_parent_not_refl; eauto.
    Qed.

    Corollary wc_EqDef_not_Is_free_in_clock:
      forall x ce ck,
        wc_equation vars (EqDef x ck ce) ->
        ~ Is_free_in_clock x ck.
    Proof.
      intros; eapply wc_equation_not_Is_free_in_clock;
        eauto using Has_clock_eq, Is_defined_in_eq.
    Qed.

    Corollary wc_EqNext_not_Is_free_in_clock:
      forall x le ck,
        wc_equation vars (EqNext x ck le) ->
        ~ Is_free_in_clock x ck.
    Proof.
      intros; eapply wc_equation_not_Is_free_in_clock;
        eauto using Has_clock_eq, Is_defined_in_eq.
    Qed.

    Corollary wc_EqCall_not_Is_free_in_clock:
      forall s xs rst f es ck,
        wc_equation vars (EqCall s xs ck rst f es) ->
        forall x, In x xs -> ~ Is_free_in_clock x ck.
    Proof.
      intros; eapply wc_equation_not_Is_free_in_clock;
        eauto using Is_defined_in_eq, Has_clock_eq.
    Qed.

  End Well_clocked.

End SBCLOCKING.

Module SBClockingFun
       (Import Ids     : IDS)
       (Import Op      : OPERATORS)
       (Import Clks    : CLOCKS         Ids)
       (Import CESyn : CESYNTAX       Op)
       (Import Syn     : SBSYNTAX       Ids Op Clks CESyn)
       (Import Last    : SBISLAST       Ids Op Clks CESyn Syn)
       (Import Var     : SBISVARIABLE   Ids Op Clks CESyn Syn)
       (Import Def     : SBISDEFINED    Ids Op Clks CESyn Syn Var Last)
       (Import CEClo : CECLOCKING Ids Op Clks CESyn)
  <: SBCLOCKING Ids Op Clks CESyn Syn Last Var Def CEClo.
  Include SBCLOCKING Ids Op Clks CESyn Syn Last Var Def CEClo.
End SBClockingFun.