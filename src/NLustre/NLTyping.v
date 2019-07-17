From Velus Require Import Common.
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
       (Import CESyn : CESYNTAX      Op)
       (Import Syn   : NLSYNTAX  Ids Op CESyn)
       (Import Ord   : NLORDERED Ids Op CESyn Syn)
       (Import CETyp : CETYPING  Ids Op CESyn).

  Inductive wt_equation (G: global) (vars: list (ident * type)): equation -> Prop :=
  | wt_EqDef: forall x ck e,
      In (x, typeofc e) vars ->
      wt_clock vars ck ->
      wt_cexp vars e ->
      wt_equation G vars (EqDef x ck e)
  | wt_EqApp: forall n xs ck f es,
      find_node f G = Some n ->
      Forall2 (fun x xt => In (x, dty xt) vars) xs n.(n_out) ->
      Forall2 (fun e xt => typeof e = dty xt) es n.(n_in) ->
      wt_clock vars ck ->
      Forall (wt_exp vars) es ->
      wt_equation G vars (EqApp xs ck f es None)
  | wt_EqReset: forall n xs ck f es r,
      find_node f G = Some n ->
      Forall2 (fun x xt => In (x, dty xt) vars) xs n.(n_out) ->
      Forall2 (fun e xt => typeof e = dty xt) es n.(n_in) ->
      wt_clock vars ck ->
      Forall (wt_exp vars) es ->
      In (r, bool_type) vars ->
      wt_equation G vars (EqApp xs ck f es (Some r))
  | wt_EqFby: forall x ck c0 e,
      In (x, type_const c0) vars ->
      typeof e = type_const c0 ->
      wt_clock vars ck ->
      wt_exp vars e ->
      wt_equation G vars (EqFby x ck c0 e).

  Definition wt_node (G: global) (n: node) : Prop
    := Forall (wt_equation G (idty (n.(n_in) ++ n.(n_vars) ++ n.(n_out))))
              n.(n_eqs).

  (* TODO: replace Welldef_global; except for the Is_well_sch component.
           Notably, typing arguments replace the ~Is_node_in and
           Is_node_in/find_node components. The no duplicate names
           component is replicated exactly. *)
  Inductive wt_global : global -> Prop :=
  | wtg_nil:
      wt_global []
  | wtg_cons: forall n ns,
      wt_global ns ->
      wt_node ns n ->
      Forall (fun n'=> n.(n_name) <> n'.(n_name))%type ns ->
      wt_global (n::ns).

  Hint Constructors wt_clock wt_exp wt_cexp wt_equation wt_global : nltyping.

  Lemma wt_global_NoDup:
    forall g,
      wt_global g ->
      NoDup (map n_name g).
  Proof.
    induction g; eauto using NoDup.
    intro WTg. simpl. constructor.
    2:apply IHg; now inv WTg.
    intro Hin.
    inversion_clear WTg as [|? ? ? WTn Hn].
    change (Forall (fun n' => (fun i=> a.(n_name) <> i :> ident) n'.(n_name)) g)
      in Hn.
    apply Forall_map in Hn.
    apply Forall_forall with (1:=Hn) in Hin.
    now contradiction Hin.
  Qed.

  Instance wt_equation_Proper:
    Proper (@eq global ==> @Permutation.Permutation (ident * type)
                ==> @eq equation ==> iff)
           wt_equation.
  Proof.
    intros G1 G2 HG env1 env2 Henv eq1 eq2 Heq.
    rewrite Heq, HG.
    split; intro WTeq.
    - inv WTeq; rewrite Henv in *; eauto;
        econstructor; eauto;
          match goal with H:Forall2 _ ?x ?y |- Forall2 _ ?x ?y =>
                          apply Forall2_impl_In with (2:=H) end;
          intros; rewrite Henv in *; auto.
    - inv WTeq; rewrite <-Henv in *; eauto;
        econstructor; eauto;
          match goal with H:Forall2 _ ?x ?y |- Forall2 _ ?x ?y =>
                          apply Forall2_impl_In with (2:=H) end;
          intros; rewrite Henv in *; auto.
  Qed.

  Lemma wt_global_Ordered_nodes:
    forall G,
      wt_global G ->
      Ordered_nodes G.
  Proof.
    induction G as [|n G]; intros * WT; auto using Ordered_nodes.
    inv WT.
    constructor; auto.
    intros *  Hni.
    eapply Forall_Exists, Exists_exists in Hni as (eq & Hin & WTeq & Hni); eauto.
    inv Hni; inv WTeq;
      assert (Exists (fun n' => f = n_name n') G) as Hn
        by (apply find_node_Exists, not_None_is_Some; eauto);
      split; auto; intro; subst;
        eapply Forall_Exists, Exists_exists in Hn as (?&?&?&?); eauto;
          contradiction.
  Qed.

End NLTYPING.

Module NLTypingFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (CESyn : CESYNTAX       Op)
       (Syn   : NLSYNTAX   Ids Op CESyn)
       (Ord   : NLORDERED  Ids Op CESyn Syn)
       (CETyp : CETYPING   Ids Op CESyn)
       <: NLTYPING Ids Op CESyn Syn Ord CETyp.
  Include NLTYPING Ids Op CESyn Syn Ord CETyp.
End NLTypingFun.
