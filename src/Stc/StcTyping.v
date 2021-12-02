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

  Inductive wt_trconstr (P: program) (Γv: list (ident * type)) (Γm: list (ident * type)): trconstr -> Prop :=
  | wt_TcDef:
      forall x ck e,
        In (x, typeofc e) Γv ->
        wt_clock P.(enums) (Γv ++ Γm) ck ->
        wt_cexp P.(enums) (Γv ++ Γm) e ->
        wt_trconstr P Γv Γm (TcDef x ck e)
  | wt_TcResetConst:
      forall x ckr ty c0,
        In (x, ty) Γm ->
        wt_const P.(enums) c0 ty ->
        wt_clock P.(enums) (Γv ++ Γm) ckr ->
        wt_trconstr P Γv Γm (TcReset x ckr ty c0)
  | wt_TcNext:
      forall x ck ckrs e,
        In (x, typeof e) Γm ->
        wt_clock P.(enums) (Γv ++ Γm) ck ->
        wt_exp P.(enums) (Γv ++ Γm) e ->
        wt_trconstr P Γv Γm (TcNext x ck ckrs e)
  | wt_TcIReset:
      forall s ck f i P',
        find_system f P = Some (s, P') ->
        wt_clock P.(enums) (Γv ++ Γm) ck ->
        wt_trconstr P Γv Γm (TcInstReset i ck f)
  | wt_TcCall:
      forall s xs ck rst f es i P',
        find_system f P = Some (s, P') ->
        Forall2 (fun x '(_, (t, _)) => In (x, t) Γv) xs s.(s_out) ->
        Forall2 (fun e '(_, (t, _)) => typeof e = t) es s.(s_in) ->
        wt_clock P.(enums) (Γv ++ Γm) ck ->
        Forall (wt_exp P.(enums) (Γv ++ Γm)) es ->
        wt_trconstr P Γv Γm (TcStep i xs ck rst f es).

  Definition wt_nexts (P: program) : list (ident * (const * type * clock)) -> Prop :=
    Forall (fun '(_, (c, t, _)) => wt_const P.(enums) c t).

  Definition wt_system (P: program) (s: system) : Prop :=
        Forall (wt_trconstr P (idty (s.(s_in) ++ s.(s_vars) ++ s.(s_out)))
                            (mems_of_nexts s.(s_nexts)))
               s.(s_tcs)
        /\ wt_nexts P s.(s_nexts)
        /\ forall x tn,
            In (x, Tenum tn) (idty (s_in s ++ s_vars s ++ s_out s)) ->
            In tn P.(enums)
            /\ 0 < snd tn.

  Definition wt_program := CommonTyping.wt_program wt_system.

  Hint Constructors wt_clock wt_exp wt_cexp wt_trconstr.

  Global Instance wt_trconstr_Proper:
    Proper (@eq program ==> @Permutation.Permutation (ident * type)
                ==> @Permutation.Permutation (ident * type)
                ==> @eq trconstr ==> iff)
           wt_trconstr.
  Proof.
    intros G1 G2 HG env1 env2 Henv resets1 resets2 Hresets eq1 eq2 Heq.
    subst.
    split; intro WTtc.
    - inv WTtc; rewrite Henv, Hresets in *; econstructor; eauto;
        match goal with H:Forall2 _ ?x ?y |- Forall2 _ ?x ?y =>
                        apply Forall2_impl_In with (2:=H) end;
        intros ? (?&(?&?)); rewrite Henv in *; auto.
    - inv WTtc; rewrite <-Henv, <-Hresets in *; econstructor; eauto;
          match goal with H:Forall2 _ ?x ?y |- Forall2 _ ?x ?y =>
                          apply Forall2_impl_In with (2:=H) end;
          intros ? (?&(?&?)); rewrite Henv in *; auto.
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
