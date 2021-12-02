From Velus Require Import Common.
From Velus Require Import CommonProgram.
From Velus Require Import CommonTyping.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import NLustre.NLSyntax.
From Velus Require Import NLustre.NLOrdered.
From Velus Require Import CoreExpr.CETyping.

From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Coq Require Import Morphisms.

(** * NLustre typing *)

(**

  Typing judgements for NLustre and resulting properties.
  Classify NLustre programs which are statically well-formed.

 *)

Module Type NLTYPING
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks   : CLOCKS    Ids Op OpAux)
       (Import CESyn : CESYNTAX  Ids Op OpAux Cks)
       (Import Syn   : NLSYNTAX  Ids Op OpAux Cks CESyn)
       (Import Ord   : NLORDERED Ids Op OpAux Cks CESyn Syn)
       (Import CETyp : CETYPING  Ids Op OpAux Cks CESyn).

  Inductive wt_equation (G: global) (Γ: list (ident * type)):
    equation -> Prop :=
  | wt_EqDef: forall x ck e,
      In (x, typeofc e) Γ ->
      wt_clock G.(enums) Γ ck ->
      wt_cexp G.(enums) Γ e ->
      wt_equation G Γ (EqDef x ck e)
  | wt_EqApp: forall n xs ck f es xrs,
      find_node f G = Some n ->
      Forall2 (fun x '(_, (t, _)) => In (x, t) Γ) xs n.(n_out) ->
      Forall2 (fun e '(_, (t, _)) => typeof e = t) es n.(n_in) ->
      wt_clock G.(enums) Γ ck ->
      Forall (wt_exp G.(enums) Γ) es ->
      Forall (fun xr => In (bool_id, 2) G.(enums) /\ In (xr, OpAux.bool_velus_type) Γ) (map fst xrs) ->
      Forall (wt_clock G.(enums) Γ) (map snd xrs) ->
      wt_equation G Γ (EqApp xs ck f es xrs)
  | wt_EqFby: forall x ck c0 e xrs,
      In (x, typeof e) Γ ->
      wt_const G.(enums) c0 (typeof e) ->
      wt_clock G.(enums) Γ ck ->
      wt_exp G.(enums) Γ e ->
      Forall (fun xr => In (bool_id, 2) G.(enums) /\ In (xr, OpAux.bool_velus_type) Γ) (map fst xrs) ->
      Forall (wt_clock G.(enums) Γ) (map snd xrs) ->
      wt_equation G Γ (EqFby x ck c0 e xrs).

  Definition wt_node (G: global) (n: node) : Prop
    := Forall (wt_equation G (idty (n.(n_in) ++ n.(n_vars) ++ n.(n_out))))
              n.(n_eqs)
       /\ forall x tn,
          In (x, Tenum tn) (idty (n.(n_in) ++ n.(n_vars) ++ n.(n_out))) ->
          In tn G.(enums)
          /\ 0 < snd tn.

  (* TODO: replace Welldef_global; except for the Is_well_sch component.
           Notably, typing arguments replace the ~Is_node_in and
           Is_node_in/find_node components. The no duplicate names
           component is replicated exactly. *)

  Definition wt_global :=
    wt_program wt_node.

  Hint Constructors wt_clock wt_exp wt_cexp wt_equation : nltyping.

  Global Instance wt_equation_Proper:
    Proper (@eq global ==> @Permutation.Permutation (ident * type)
                ==> @eq equation ==> iff)
           wt_equation.
  Proof.
    intros G1 G2 HG env1 env2 Henv eq1 eq2 Heq.
    rewrite Heq, HG.
    split; intro WTeq.
    - inv WTeq; rewrite Henv in *; eauto;
        econstructor; eauto;
          match goal with
          | H:Forall2 _ ?x ?y |- Forall2 _ ?x ?y =>
            apply Forall2_impl_In with (2:=H)
          | H:Forall _ ?x |- Forall _ ?x =>
            apply Forall_impl_In with (2:=H) end.
      intros ? (?&(?&?)); rewrite Henv in *; auto.
      1-4:intros; rewrite Henv in *; auto.
    - inv WTeq; rewrite <-Henv in *; eauto;
        econstructor; eauto;
          match goal with
          | H:Forall2 _ ?x ?y |- Forall2 _ ?x ?y =>
            apply Forall2_impl_In with (2:=H)
          | H:Forall _ ?x |- Forall _ ?x =>
            apply Forall_impl_In with (2:=H) end.
      intros ? (?&(?&?)); rewrite Henv in *; auto.
      1-4:intros; rewrite Henv in *; auto.
  Qed.

  Lemma wt_global_Ordered_nodes:
    forall G,
      wt_global G ->
      Ordered_nodes G.
  Proof.
    intros; eapply wt_program_Ordered_program; eauto.
    intros * (WT&?) Hni.
    eapply Forall_Exists, Exists_exists in Hni as (eq & Hin & WTeq & Hni); eauto.
    apply not_None_is_Some.
    inv Hni; inv WTeq;
      take (find_node _ _ = _) and apply option_map_inv in it as ((?&?)&?&?);
      eauto.
  Qed.

  Lemma wt_equation_enums_cons:
    forall ns enums e Γ eq,
      wt_equation (Global enums ns) Γ eq ->
      wt_equation (Global (e :: enums) ns) Γ eq.
  Proof.
    induction 1; eauto using wt_equation, wt_clock_enums_cons, wt_cexp_enums_cons, wt_exp_enums_cons.
    - econstructor; eauto using wt_clock_enums_cons.
      + now rewrite find_node_enums_cons.
      + eapply Forall_impl; [|eauto]; eauto using wt_exp_enums_cons.
      + eapply Forall_impl; [|eauto]; intros ? (?&?); simpl in *; eauto using wt_exp_enums_cons.
      + eapply Forall_impl; [|eauto]; eauto using wt_clock_enums_cons.
    - econstructor; eauto using wt_clock_enums_cons, wt_exp_enums_cons.
      + simpl in *. inv H0; constructor; auto using in_cons.
      + eapply Forall_impl; [|eauto]; intros ? (?&?); simpl in *; eauto using wt_exp_enums_cons.
      + eapply Forall_impl; [|eauto]; eauto using wt_clock_enums_cons.
  Qed.

  Corollary wt_node_enums_cons:
    forall ns enums e n,
      wt_node (Global enums ns) n ->
      wt_node (Global (e :: enums) ns) n.
  Proof.
    unfold wt_node; intros * (WT & Enums); split.
    - apply Forall_forall; intros;
        take (Forall _ _) and eapply Forall_forall in it; eauto.
      now apply wt_equation_enums_cons.
    - intros * Hin; apply Enums in Hin as (?&?); split; auto.
      now right.
  Qed.

  Corollary wt_global_enums_cons:
    forall enums ns e,
      wt_global (Global enums ns) ->
      wt_global (Global (e :: enums) ns).
  Proof.
    unfold wt_global, wt_program.
    induction ns; simpl; intros * WT; inv WT; constructor.
    - take (_ /\ _) and destruct it as (WT & ?); split; auto.
      now apply wt_node_enums_cons.
    - apply IHns; auto.
  Qed.

  Section incl.
    Variable (G : global).
    Variable (vars vars' : list (ident * type)).
    Hypothesis Hincl : incl vars vars'.

    Fact wt_clock_incl : forall ck,
      wt_clock G.(enums) vars ck ->
      wt_clock G.(enums) vars' ck.
    Proof.
      intros * Hwt.
      induction Hwt.
      - constructor.
      - constructor; auto.
    Qed.
    Local Hint Resolve wt_clock_incl.

    Lemma wt_exp_incl : forall e,
        wt_exp G.(enums) vars e ->
        wt_exp G.(enums) vars' e.
    Proof.
      induction e; intros Hwt; inv Hwt; econstructor; eauto.
    Qed.
    Local Hint Resolve wt_exp_incl.

    Lemma wt_cexp_incl : forall e,
        wt_cexp G.(enums) vars e ->
        wt_cexp G.(enums) vars' e.
    Proof.
      induction e using cexp_ind2'; intros Hwt; inv Hwt; econstructor; eauto.
      - eapply Forall_impl_In; [|eapply H7]; intros.
        eapply Forall_forall in H; eauto.
      - intros. eapply Forall_forall in H; eauto.
        simpl in *; eauto.
    Qed.
    Local Hint Resolve wt_cexp_incl.

    Lemma wt_equation_incl : forall equ,
        wt_equation G vars equ ->
        wt_equation G vars' equ.
    Proof.
      intros [| |] Hwt; inv Hwt; econstructor; eauto.
      - eapply Forall2_impl_In; eauto. intros ? (?&?&?); eauto.
      - eapply Forall_impl; [|eauto]; eauto.
      - eapply Forall_impl; [|eauto]; intros ? (?&?); eauto.
      - eapply Forall_impl; [|eauto]; eauto.
      - eapply Forall_impl; [|eauto]; intros ? (?&?); eauto.
      - eapply Forall_impl; [|eauto]; eauto.
    Qed.

  End incl.

  Lemma global_iface_eq_wt_eq : forall G1 G2 vars eq,
      global_iface_eq G1 G2 ->
      wt_equation G1 vars eq ->
      wt_equation G2 vars eq.
  Proof.
    intros * Heq Hwt.
    destruct Heq as (Henums&Heq).
    inv Hwt; try constructor; eauto; try congruence.
    2:eapply Forall_impl; eauto; intros; congruence.
    specialize (Heq f). rewrite H in Heq. inv Heq.
    destruct H8 as (?&?&?).
    symmetry in H7. econstructor; eauto; try congruence.
    eapply Forall_impl; eauto; intros; congruence.
  Qed.

End NLTYPING.

Module NLTypingFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX  Ids Op)
       (Cks   : CLOCKS     Ids Op OpAux)
       (CESyn : CESYNTAX   Ids Op OpAux Cks)
       (Syn   : NLSYNTAX   Ids Op OpAux Cks CESyn)
       (Ord   : NLORDERED  Ids Op OpAux Cks CESyn Syn)
       (CETyp : CETYPING   Ids Op OpAux Cks CESyn)
       <: NLTYPING Ids Op OpAux Cks CESyn Syn Ord CETyp.
  Include NLTYPING Ids Op OpAux Cks CESyn Syn Ord CETyp.
End NLTypingFun.
