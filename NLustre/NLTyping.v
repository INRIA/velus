Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.Clocks.
Require Import Velus.CoreExpr.CESyntax.
Require Import Velus.NLustre.NLSyntax.
Require Import Velus.CoreExpr.CETyping.

Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Require Import Morphisms.

(** * NLustre typing *)

(**

  Typing judgements for NLustre and resulting properties.
  Classify NLustre programs which are statically well-formed.

 *)

Module Type NLTYPING
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import Clks  : CLOCKS   Ids)
       (Import CESyn : CESYNTAX     Op)
       (Import Syn   : NLSYNTAX Ids Op Clks CESyn)
       (Import CETyp : CETYPING Ids Op Clks CESyn).

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
      Forall (wt_lexp vars) es ->
      NoDup xs ->
      wt_equation G vars (EqApp xs ck f es None)
  | wt_EqReset: forall n xs ck f es r,
      find_node f G = Some n ->
      Forall2 (fun x xt => In (x, dty xt) vars) xs n.(n_out) ->
      Forall2 (fun e xt => typeof e = dty xt) es n.(n_in) ->
      wt_clock vars ck ->
      Forall (wt_lexp vars) es ->
      NoDup xs ->
      In (r, bool_type) vars ->
      wt_equation G vars (EqApp xs ck f es (Some r))
  | wt_EqFby: forall x ck c0 e,
      In (x, type_const c0) vars ->
      typeof e = type_const c0 ->
      wt_clock vars ck ->
      wt_lexp vars e ->
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
      Forall (fun n'=> n.(n_name) <> n'.(n_name)) ns ->
      wt_global (n::ns).

  Hint Constructors wt_clock wt_lexp wt_cexp wt_equation wt_global : nltyping.

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
    change (Forall (fun n' => (fun i=> a.(n_name) <> i) n'.(n_name)) g) in Hn.
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

End NLTYPING.

Module NLTypingFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (Clks  : CLOCKS   Ids)
       (CESyn : CESYNTAX     Op)
       (Syn   : NLSYNTAX Ids Op Clks CESyn)
       (CETyp : CETYPING Ids Op Clks CESyn)
       <: NLTYPING Ids Op Clks CESyn Syn CETyp.
  Include NLTYPING Ids Op Clks CESyn Syn CETyp.
End NLTypingFun.
