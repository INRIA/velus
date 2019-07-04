From Velus Require Import Common.
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
       (Import CESyn : CESYNTAX      Op)
       (Import Syn   : STCSYNTAX Ids Op CESyn)
       (Import CETyp : CETYPING  Ids Op CESyn).

  Inductive wt_trconstr (P: program) (vars: list (ident * type)) (lasts: list (ident * type)): trconstr -> Prop :=
  | wt_TcDef:
      forall x ck e,
        In (x, typeofc e) vars ->
        wt_clock (vars ++ lasts) ck ->
        wt_cexp (vars ++ lasts) e ->
        wt_trconstr P vars lasts (TcDef x ck e)
  | wt_TcNext:
      forall x ck e,
        In (x, typeof e) lasts ->
        wt_clock (vars ++ lasts) ck ->
        wt_exp (vars ++ lasts) e ->
        wt_trconstr P vars lasts (TcNext x ck e)
  | wt_TcReset:
      forall s ck f i P',
        find_system f P = Some (s, P') ->
        wt_clock (vars ++ lasts) ck ->
        wt_trconstr P vars lasts (TcReset i ck f)
  | wt_TcCall:
      forall s xs ck rst f es i P',
        find_system f P = Some (s, P') ->
        Forall2 (fun x xt => In (x, dty xt) vars) xs s.(s_out) ->
        Forall2 (fun e xt => typeof e = dty xt) es s.(s_in) ->
        wt_clock (vars ++ lasts) ck ->
        Forall (wt_exp (vars ++ lasts)) es ->
        wt_trconstr P vars lasts (TcCall i xs ck rst f es).

  Definition wt_system (P: program) (s: system) : Prop :=
    Forall (wt_trconstr P (idty (s.(s_in) ++ s.(s_vars) ++ s.(s_out)))
                        (map (fun x => (fst x, type_const (fst (snd x)))) s.(s_lasts)))
           s.(s_tcs).

  (* TODO: replace Welldef_global; except for the Is_well_sch component.
           Notably, typing arguments replace the ~Is_node_in and
           Is_node_in/find_node components. The no duplicate names
           component is replicated exactly. *)
  Inductive wt_program : program -> Prop :=
  | wtg_nil:
      wt_program []
  | wtg_cons:
      forall s P,
        wt_program P ->
        wt_system P s ->
        Forall (fun s' => s.(s_name) <> s'.(s_name))%type P ->
        wt_program (s :: P).

  Hint Constructors wt_clock wt_exp wt_cexp wt_trconstr wt_program.

  Lemma wt_program_NoDup:
    forall P,
      wt_program P ->
      NoDup (map s_name P).
  Proof.
    induction P; eauto using NoDup.
    intro WTg. simpl. constructor.
    2:apply IHP; now inv WTg.
    intro Hin.
    inversion_clear WTg as [|? ? ? WTn Hn].
    change (Forall (fun b' => (fun i => a.(s_name) <> i :> ident) b'.(s_name)) P) in Hn.
    apply Forall_map in Hn.
    apply Forall_forall with (1:=Hn) in Hin.
    now contradiction Hin.
  Qed.

  Instance wt_trconstr_Proper:
    Proper (@eq program ==> @Permutation.Permutation (ident * type)
                ==> @Permutation.Permutation (ident * type)
                ==> @eq trconstr ==> iff)
           wt_trconstr.
  Proof.
    intros G1 G2 HG env1 env2 Henv lasts1 lasts2 Hlasts eq1 eq2 Heq.
    subst.
    split; intro WTtc.
    - inv WTtc; rewrite Henv, Hlasts in *; econstructor; eauto;
        match goal with H:Forall2 _ ?x ?y |- Forall2 _ ?x ?y =>
                        apply Forall2_impl_In with (2:=H) end;
        intros; rewrite Henv in *; auto.
    - inv WTtc; rewrite <-Henv, <-Hlasts in *; econstructor; eauto;
          match goal with H:Forall2 _ ?x ?y |- Forall2 _ ?x ?y =>
                          apply Forall2_impl_In with (2:=H) end;
          intros; rewrite Henv in *; auto.
  Qed.

End STCTYPING.

Module StcTypingFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (CESyn : CESYNTAX     Op)
       (Syn   : STCSYNTAX Ids Op CESyn)
       (CETyp : CETYPING Ids Op CESyn)
       <: STCTYPING Ids Op CESyn Syn CETyp.
  Include STCTYPING Ids Op CESyn Syn CETyp.
End StcTypingFun.
