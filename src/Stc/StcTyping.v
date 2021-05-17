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

  Inductive wt_trconstr (P: program) (vars: list (ident * type)) (resets: list (ident * type)): trconstr -> Prop :=
  | wt_TcDef:
      forall x ck e,
        In (x, typeofc e) vars ->
        wt_clock (vars ++ resets) ck ->
        wt_cexp (vars ++ resets) e ->
        wt_trconstr P vars resets (TcDef x ck e)
  | wt_TcReset:
      forall x ckr c0,
        In (x, type_const c0) resets ->
        wt_clock (vars ++ resets) ckr ->
        wt_trconstr P vars resets (TcReset x ckr c0)
  | wt_TcNext:
      forall x ck ckrs e,
        In (x, typeof e) resets ->
        wt_clock (vars ++ resets) ck ->
        wt_exp (vars ++ resets) e ->
        wt_trconstr P vars resets (TcNext x ck ckrs e)
  | wt_TcIReset:
      forall s ck f i P',
        find_system f P = Some (s, P') ->
        wt_clock (vars ++ resets) ck ->
        wt_trconstr P vars resets (TcInstReset i ck f)
  | wt_TcStep:
      forall s xs ck ckrs f es i P',
        find_system f P = Some (s, P') ->
        Forall2 (fun x '(_, (t, _)) => In (x, t) vars) xs s.(s_out) ->
        Forall2 (fun e '(_, (t, _)) => typeof e = t) es s.(s_in) ->
        wt_clock (vars ++ resets) ck ->
        Forall (wt_exp (vars ++ resets)) es ->
        wt_trconstr P vars resets (TcStep i xs ck ckrs f es).

  Definition wt_system (P: program) (s: system) : Prop :=
    Forall (wt_trconstr P (idty (s.(s_in) ++ s.(s_vars) ++ s.(s_out)))
                        (map (fun x => (fst x, type_const (fst (snd x)))) s.(s_nexts)))
           s.(s_tcs).

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

  Instance wt_trconstr_Proper:
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
       (CESyn : CESYNTAX     Op)
       (Syn   : STCSYNTAX Ids Op CESyn)
       (CETyp : CETYPING Ids Op CESyn)
       <: STCTYPING Ids Op CESyn Syn CETyp.
  Include STCTYPING Ids Op CESyn Syn CETyp.
End StcTypingFun.
