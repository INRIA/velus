Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.Clocks.
Require Import Velus.CoreExpr.CESyntax.
Require Import Velus.SyBloc.SBSyntax.
Require Import Velus.CoreExpr.CETyping.

Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Require Import Morphisms.

(** * SyBloc typing *)

(**

  Typing judgements for SyBloc and resulting properties.

 *)

Module Type SBTYPING
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import Clks  : CLOCKS   Ids)
       (Import CESyn : CESYNTAX     Op)
       (Import Syn   : SBSYNTAX Ids Op Clks CESyn)
       (Import CETyp : CETYPING Ids Op Clks CESyn).

  Inductive wt_equation (P: program) (vars: list (ident * type)) (lasts: list (ident * type)): equation -> Prop :=
  | wt_EqDef:
      forall x ck e,
        In (x, typeofc e) vars ->
        wt_clock (vars ++ lasts) ck ->
        wt_cexp (vars ++ lasts) e ->
        wt_equation P vars lasts (EqDef x ck e)
  | wt_EqNext:
      forall x ck e,
        In (x, typeof e) lasts ->
        wt_clock (vars ++ lasts) ck ->
        wt_lexp (vars ++ lasts) e ->
        wt_equation P vars lasts (EqNext x ck e)
  | wt_EqReset:
      forall s ck f b P',
        find_block f P = Some (b, P') ->
        wt_clock (vars ++ lasts) ck ->
        wt_equation P vars lasts (EqReset s ck f)
  | wt_EqCall:
      forall s xs ck rst f es b P',
        find_block f P = Some (b, P') ->
        Forall2 (fun x xt => In (x, dty xt) vars) xs b.(b_out) ->
        Forall2 (fun e xt => typeof e = dty xt) es b.(b_in) ->
        wt_clock (vars ++ lasts) ck ->
        Forall (wt_lexp (vars ++ lasts)) es ->
        wt_equation P vars lasts (EqCall s xs ck rst f es).

  Definition wt_block (P: program) (b: block) : Prop :=
    Forall (wt_equation P (idty (b.(b_in) ++ b.(b_vars) ++ b.(b_out)))
                        (map (fun x => (fst x, type_const (fst (snd x)))) b.(b_lasts)))
           b.(b_eqs).

  (* TODO: replace Welldef_global; except for the Is_well_sch component.
           Notably, typing arguments replace the ~Is_node_in and
           Is_node_in/find_node components. The no duplicate names
           component is replicated exactly. *)
  Inductive wt_program : program -> Prop :=
  | wtg_nil:
      wt_program []
  | wtg_cons:
      forall b P,
        wt_program P ->
        wt_block P b ->
        Forall (fun b' => b.(b_name) <> b'.(b_name)) P ->
        wt_program (b :: P).

  Hint Constructors wt_clock wt_lexp wt_cexp wt_equation wt_program.

  Lemma wt_program_NoDup:
    forall P,
      wt_program P ->
      NoDup (map b_name P).
  Proof.
    induction P; eauto using NoDup.
    intro WTg. simpl. constructor.
    2:apply IHP; now inv WTg.
    intro Hin.
    inversion_clear WTg as [|? ? ? WTn Hn].
    change (Forall (fun b' => (fun i => a.(b_name) <> i) b'.(b_name)) P) in Hn.
    apply Forall_map in Hn.
    apply Forall_forall with (1:=Hn) in Hin.
    now contradiction Hin.
  Qed.

  Instance wt_equation_Proper:
    Proper (@eq program ==> @Permutation.Permutation (ident * type)
                ==> @Permutation.Permutation (ident * type)
                ==> @eq equation ==> iff)
           wt_equation.
  Proof.
    intros G1 G2 HG env1 env2 Henv lasts1 lasts2 Hlasts eq1 eq2 Heq.
    subst.
    split; intro WTeq.
    - inv WTeq; rewrite Henv, Hlasts in *; econstructor; eauto;
        match goal with H:Forall2 _ ?x ?y |- Forall2 _ ?x ?y =>
                        apply Forall2_impl_In with (2:=H) end;
        intros; rewrite Henv in *; auto.
    - inv WTeq; rewrite <-Henv, <-Hlasts in *; econstructor; eauto;
          match goal with H:Forall2 _ ?x ?y |- Forall2 _ ?x ?y =>
                          apply Forall2_impl_In with (2:=H) end;
          intros; rewrite Henv in *; auto.
  Qed.

End SBTYPING.

Module SBTypingFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (Clks  : CLOCKS   Ids)
       (CESyn : CESYNTAX     Op)
       (Syn   : SBSYNTAX Ids Op Clks CESyn)
       (CETyp : CETYPING Ids Op Clks CESyn)
       <: SBTYPING Ids Op Clks CESyn Syn CETyp.
  Include SBTYPING Ids Op Clks CESyn Syn CETyp.
End SBTypingFun.
