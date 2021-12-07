From Velus Require Import Common.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import CoreExpr.CESyntax.

From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Coq Require Import Morphisms.

Module Type CETYPING
       (Import Ids  : IDS)
       (Import Op   : OPERATORS)
       (Import OpAux: OPERATORS_AUX Ids Op)
       (Import Cks  : CLOCKS        Ids Op OpAux)
       (Import Syn  : CESYNTAX      Ids Op OpAux Cks).

  (** ** Clocks *)

  Section WellTyped.

    Variable enums : list (ident * nat).
    Variable Γ : list (ident * type).

    Inductive wt_clock : clock -> Prop :=
    | wt_Cbase:
        wt_clock Cbase
    | wt_Con: forall ck x tn c,
        In (x, Tenum tn) Γ ->
        In tn enums ->
        c < snd tn ->
        wt_clock ck ->
        wt_clock (Con ck x (Tenum tn, c)).

    Inductive wt_exp : exp -> Prop :=
    | wt_Econst: forall c,
        wt_exp (Econst c)
    | wt_Eenum: forall x tn,
        In tn enums ->
        x < snd tn ->
        wt_exp (Eenum x (Tenum tn))
    | wt_Evar: forall x ty,
        In (x, ty) Γ ->
        wt_exp (Evar x ty)
    | wt_Ewhen: forall e x b tn,
        In (x, Tenum tn) Γ ->
        In tn enums ->
        b < snd tn ->
        wt_exp e ->
        wt_exp (Ewhen e x b)
    | wt_Eunop: forall op e ty,
        type_unop op (typeof e) = Some ty ->
        wt_exp e ->
        wt_exp (Eunop op e ty)
    | wt_Ebinop: forall op e1 e2 ty,
        type_binop op (typeof e1) (typeof e2) = Some ty ->
        wt_exp e1 ->
        wt_exp e2 ->
        wt_exp (Ebinop op e1 e2 ty).

    Inductive wt_cexp : cexp -> Prop :=
    | wt_Emerge: forall x l ty tn,
        In (x, Tenum tn) Γ ->
        In tn enums ->
        snd tn = length l ->
        Forall (fun e => typeofc e = ty) l ->
        Forall wt_cexp l ->
        wt_cexp (Emerge (x, Tenum tn) l ty)
    | wt_Ecase: forall e l d tn,
        wt_exp e ->
        typeof e = Tenum tn ->
        In tn enums ->
        snd tn = length l ->
        (forall e, In (Some e) l -> typeofc e = typeofc d) ->
        wt_cexp d ->
        (forall e, In (Some e) l -> wt_cexp e) ->
        wt_cexp (Ecase e l d)
    | wt_Eexp: forall e,
        wt_exp e ->
        wt_cexp (Eexp e).

  End WellTyped.

  Global Hint Constructors wt_clock : typing ltyping nltyping stctyping.
  Global Hint Constructors wt_exp wt_cexp : nltyping stctyping.

  Lemma wt_clock_add:
    forall x v enums Γ ck,
      ~InMembers x Γ ->
      wt_clock enums Γ ck ->
      wt_clock enums ((x, v) :: Γ) ck.
  Proof.
    induction ck; auto with nltyping.
    inversion 2.
    eauto with nltyping datatypes.
  Qed.

  Global Instance wt_clock_Proper:
    Proper (@Permutation.Permutation (ident * nat) ==>
            @Permutation.Permutation (ident * type) ==>
            @eq clock ==> iff)
           wt_clock.
  Proof.
    intros enums' enums Henums env' env Henv ck' ck Hck.
    rewrite Hck; clear Hck ck'.
    induction ck.
    - split; auto with nltyping.
    - destruct IHck.
      split; inversion_clear 1; econstructor;
        try rewrite Henv in *;
        try rewrite Henums in *;
        eauto.
  Qed.

  Global Instance wt_exp_Proper:
    Proper (@Permutation.Permutation (ident * nat) ==>
            @Permutation.Permutation (ident * type) ==>
            @eq exp ==> iff)
           wt_exp.
  Proof.
    intros enums' enums Henums env' env Henv e' e He.
    rewrite He; clear He.
    induction e; try destruct IHe;
      try destruct IHe1, IHe2;
      split; auto;
        inversion_clear 1;
        ((rewrite Henv in *; try rewrite Henums in *)
        || (rewrite <-Henv in *; try rewrite <-Henums in *) || idtac);
         eauto with nltyping.
          - econstructor; eauto.
            now rewrite <-Henums.
          - econstructor; eauto.
            now rewrite Henums.
  Qed.

  Global Instance wt_exp_pointwise_Proper:
    Proper (@Permutation.Permutation (ident * nat) ==>
            @Permutation.Permutation (ident * type) ==>
            pointwise_relation exp iff)
           wt_exp.
  Proof.
    intros enums' enums Henums env' env Henv e.
    now rewrite Henv, Henums.
  Qed.

  Global Instance wt_cexp_Proper:
    Proper (@Permutation.Permutation (ident * nat) ==>
            @Permutation.Permutation (ident * type) ==>
            @eq cexp ==> iff)
           wt_cexp.
  Proof.
    intros enums' enums Henums env' env Henv e' e He.
    rewrite He; clear He.
    induction e using cexp_ind2'; try destruct IHe1, IHe2;
      split; inversion_clear 1; try rewrite Henv in *; try rewrite Henums in *;
        econstructor; eauto; try rewrite Henv in *; try rewrite Henums in *; eauto.
    - apply Forall_forall; intros * Hin.
      do 3 (take (Forall _ _) and eapply Forall_forall in it; eauto).
      apply it; auto.
    - apply Forall_forall; intros * Hin.
      do 3 (take (Forall _ _) and eapply Forall_forall in it; eauto).
      apply it; auto.
    - now apply IHe.
    - intros * Hin.
      take (Forall _ _) and eapply Forall_forall in it; eauto.
      apply it; auto.
    - now apply IHe.
    - intros * Hin.
      take (Forall _ _) and eapply Forall_forall in it; eauto.
      apply it; auto.
  Qed.

  Lemma wt_clock_enums_cons:
    forall enums e Γ ck,
      wt_clock enums Γ ck ->
      wt_clock (e :: enums) Γ ck.
  Proof.
    induction 1; eauto using wt_clock.
    econstructor; eauto.
    now right.
  Qed.

  Lemma wt_exp_enums_cons:
    forall enums e Γ ex,
      wt_exp enums Γ ex ->
      wt_exp (e :: enums) Γ ex.
  Proof.
    induction 1; eauto using wt_exp.
    - constructor; auto.
      now right.
    - econstructor; eauto.
      now right.
  Qed.

  Lemma wt_cexp_enums_cons:
    forall enums e Γ ce,
      wt_cexp enums Γ ce ->
      wt_cexp (e :: enums) Γ ce.
  Proof.
    induction ce using cexp_ind2'; intros * WT; inv WT;
      eauto using wt_cexp, wt_exp_enums_cons.
    - econstructor; eauto.
      + now right.
      + apply Forall_forall; intros.
        repeat take (Forall _ _) and eapply Forall_forall in it; eauto.
    - econstructor; eauto using wt_exp_enums_cons.
      + now right.
      + intros.
        take (Forall _ _) and eapply Forall_forall in it; eauto; simpl in it; auto.
  Qed.

End CETYPING.

Module CETypingFun
       (Ids  : IDS)
       (Op   : OPERATORS)
       (OpAux: OPERATORS_AUX Ids Op)
       (Cks  : CLOCKS        Ids Op OpAux)
       (Syn  : CESYNTAX      Ids Op OpAux Cks)
       <: CETYPING Ids Op OpAux Cks Syn.
  Include CETYPING Ids Op OpAux Cks Syn.
End CETypingFun.
