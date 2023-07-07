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

  Inductive wt_equation (G: global) (Γ: list (ident * (type * bool))): equation -> Prop :=
  | wt_EqDef: forall x ck e islast,
      In (x, (typeofr e, islast)) Γ ->
      wt_clock G.(types) Γ ck ->
      wt_rhs G.(types) G.(externs) Γ e ->
      wt_equation G Γ (EqDef x ck e)
  | wt_EqLast: forall x ty ck c0 xrs,
      In (x, (ty, true)) Γ ->
      wt_clock G.(types) Γ ck ->
      wt_const G.(types) c0 ty ->
      Forall (fun '(xr, ckr) => In bool_velus_type G.(types) /\ In (xr, OpAux.bool_velus_type) (idfst Γ)
                            /\ wt_clock G.(types) Γ ckr) xrs ->
      wt_equation G Γ (EqLast x ty ck c0 xrs)
  | wt_EqApp: forall n xs ck f es xrs,
      find_node f G = Some n ->
      Forall2 (fun x '(_, (t, _)) => In (x, (t, false)) Γ) xs n.(n_out) ->
      Forall2 (fun e '(_, (t, _)) => typeof e = t) es n.(n_in) ->
      wt_clock G.(types) Γ ck ->
      Forall (wt_exp G.(types) Γ) es ->
      Forall (fun '(xr, ckr) => In bool_velus_type G.(types) /\ In (xr, OpAux.bool_velus_type) (idfst Γ)
                            /\ wt_clock G.(types) Γ ckr) xrs ->
      Forall (wt_clock G.(types) Γ) (map snd xrs) ->
      wt_equation G Γ (EqApp xs ck f es xrs)
  | wt_EqFby: forall x ck c0 e xrs,
      In (x, (typeof e, false)) Γ ->
      wt_clock G.(types) Γ ck ->
      wt_const G.(types) c0 (typeof e) ->
      wt_exp G.(types) Γ e ->
      Forall (fun '(xr, ckr) => In bool_velus_type G.(types) /\ In (xr, OpAux.bool_velus_type) (idfst Γ)
                            /\ wt_clock G.(types) Γ ckr) xrs ->
      wt_equation G Γ (EqFby x ck c0 e xrs).

  Definition wt_node (G: global) (n: node) : Prop
    := Forall (wt_equation G (map (fun '(x, (ty, _)) => (x, (ty, false))) (n.(n_in) ++ n.(n_out))
                                ++ map (fun '(x, (ty, _, islast)) => (x, (ty, islast))) n.(n_vars)))
         n.(n_eqs)
       /\ forall x ty,
          In (x, ty) (idfst (n.(n_in) ++ idfst n.(n_vars) ++ n.(n_out))) -> wt_type G.(types) ty.

  Definition wt_global :=
    wt_program wt_node.

  Global Hint Constructors wt_clock wt_exp wt_cexp wt_equation : nltyping.

  Global Instance wt_equation_Proper:
    Proper (@eq global ==> @Permutation.Permutation _
                ==> @eq equation ==> iff)
           wt_equation.
  Proof.
    intros G1 G2 HG env1 env2 Henv eq1 eq2 Heq.
    rewrite Heq, HG.
    split; intro WTeq; inv WTeq; econstructor; eauto.
    all:simpl_Forall; destruct_conjs; repeat split.
    all:try rewrite Henv; eauto.
    all:try rewrite <-Henv; eauto.
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

  Section incl.
    Variable (G : global).
    Variable (vars vars' : list (ident * (type * bool))).
    Hypothesis Hincl : incl vars vars'.

    Lemma wt_equation_incl : forall equ,
        wt_equation G vars equ ->
        wt_equation G vars' equ.
    Proof.
      intros * Hwt; inv Hwt;
        econstructor; simpl_Forall; destruct_conjs; repeat split; eauto with nltyping.
      all:try eapply incl_map; eauto.
      simpl_Forall; eauto.
    Qed.

  End incl.

  Lemma global_iface_eq_wt_eq : forall G1 G2 vars eq,
      global_iface_eq G1 G2 ->
      wt_equation G1 vars eq ->
      wt_equation G2 vars eq.
  Proof.
    intros * Heq Hwt.
    destruct Heq as (Henums&Htypes&Heq).
    inv Hwt.
    3:(specialize (Heq f); rewrite H in Heq; inv Heq;
       take (node_iface_eq _ _) and destruct it as (?&?&?)).
    all:try econstructor; eauto; try congruence.
    all:simpl_Forall; destruct_conjs; repeat split; eauto; try congruence.
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
