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

    Variable types : list type.
    Variable externs : list (ident * (list ctype * ctype)).
    Variable Γ : list (ident * (type * bool)).

    Inductive wt_clock : clock -> Prop :=
    | wt_Cbase:
        wt_clock Cbase
    | wt_Con: forall ck x tx tn islast c,
        In (x, (Tenum tx tn, islast)) Γ ->
        In (Tenum tx tn) types ->
        c < length tn ->
        wt_clock ck ->
        wt_clock (Con ck x (Tenum tx tn, c)).

    Inductive wt_exp : exp -> Prop :=
    | wt_Econst: forall c,
        wt_exp (Econst c)
    | wt_Eenum: forall x tx tn,
        In (Tenum tx tn) types ->
        x < length tn ->
        wt_exp (Eenum x (Tenum tx tn))
    | wt_Evar: forall x ty islast,
        In (x, (ty, islast)) Γ ->
        wt_exp (Evar x ty)
    | wt_Elast: forall x ty,
        In (x, (ty, true)) Γ ->
        wt_exp (Elast x ty)
    | wt_Ewhen: forall e x b tx tn islast,
        In (x, (Tenum tx tn, islast)) Γ ->
        In (Tenum tx tn) types ->
        b < length tn ->
        wt_exp e ->
        wt_exp (Ewhen e (x, Tenum tx tn) b)
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
    | wt_Emerge: forall x l ty tx tn islast,
        In (x, (Tenum tx tn, islast)) Γ ->
        In (Tenum tx tn) types ->
        length tn = length l ->
        Forall (fun e => typeofc e = ty) l ->
        Forall wt_cexp l ->
        wt_cexp (Emerge (x, Tenum tx tn) l ty)
    | wt_Ecase: forall e l d tx tn,
        wt_exp e ->
        typeof e = Tenum tx tn ->
        In (Tenum tx tn) types ->
        length tn = length l ->
        (forall e, In (Some e) l -> typeofc e = typeofc d) ->
        wt_cexp d ->
        (forall e, In (Some e) l -> wt_cexp e) ->
        wt_cexp (Ecase e l d)
    | wt_Eexp: forall e,
        wt_exp e ->
        wt_cexp (Eexp e).

    Inductive wt_rhs : rhs -> Prop :=
    | wt_Eextcall: forall f es tyout tyins,
        Forall wt_exp es ->
        Forall2 (fun e ty => typeof e = Tprimitive ty) es tyins ->
        In (f, (tyins, tyout)) externs ->
        wt_rhs (Eextcall f es tyout)
    | wt_Ecexp: forall e,
        wt_cexp e ->
        wt_rhs (Ecexp e).

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
    Proper (@Permutation.Permutation type ==>
            @Permutation.Permutation _ ==>
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
    Proper (@Permutation.Permutation type ==>
            @Permutation.Permutation _ ==>
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
    Proper (@Permutation.Permutation type ==>
            @Permutation.Permutation _ ==>
            pointwise_relation exp iff)
           wt_exp.
  Proof.
    intros enums' enums Henums env' env Henv e.
    now rewrite Henv, Henums.
  Qed.

  Global Instance wt_cexp_Proper:
    Proper (@Permutation.Permutation type ==>
            @Permutation.Permutation _ ==>
            @eq cexp ==> iff)
           wt_cexp.
  Proof.
    intros enums' enums Henums env' env Henv e' e He.
    rewrite He; clear He.
    induction e using cexp_ind2'; try destruct IHe1, IHe2;
      split; inversion_clear 1; try rewrite Henv in *; try rewrite Henums in *;
        econstructor; eauto; try rewrite Henv in *; try rewrite Henums in *; eauto.
    - simpl_Forall. apply H; auto.
    - simpl_Forall. apply H; auto.
    - now apply IHe.
    - intros * Hin.
      simpl_Forall. apply H; auto.
    - now apply IHe.
    - intros * Hin.
      simpl_Forall. apply H; auto.
  Qed.

  Global Instance wt_rhs_Proper:
    Proper (@Permutation.Permutation _ ==>
            @Permutation.Permutation _ ==>
            @Permutation.Permutation _ ==>
            @eq _ ==> iff)
           wt_rhs.
  Proof.
    intros types' types Htypes externs' externs Hexterns env' env Henv e' e ?; subst.
    destruct e; split; intros Hwt; inv Hwt; econstructor; eauto; simpl_Forall.
    all:try rewrite Htypes, Henv; auto.
    all:try rewrite <-Htypes, <-Henv; auto.
    all:try rewrite Hexterns; auto; try rewrite <-Hexterns; auto.
  Qed.

  Section incl.
    Variable (types : list type).
    Variable (vars vars' : list (ident * (type * bool))).
    Hypothesis Hincl : incl vars vars'.

    Fact wt_clock_incl : forall ck,
      wt_clock types vars ck ->
      wt_clock types vars' ck.
    Proof.
      intros * Hwt.
      induction Hwt.
      - constructor.
      - econstructor; eauto.
    Qed.

    Lemma wt_exp_incl : forall e,
        wt_exp types vars e ->
        wt_exp types vars' e.
    Proof.
      induction e; intros Hwt; inv Hwt; econstructor; eauto.
    Qed.

    Lemma wt_cexp_incl : forall e,
        wt_cexp types vars e ->
        wt_cexp types vars' e.
    Proof.
      induction e using cexp_ind2'; intros Hwt; inv Hwt; econstructor; eauto using wt_exp_incl.
      - simpl_Forall; eauto.
      - intros. eapply Forall_forall in H; eauto.
        simpl in *; eauto.
    Qed.

    Lemma wt_rhs_incl externs : forall e,
        wt_rhs types externs vars e ->
        wt_rhs types externs vars' e.
    Proof.
      intros * Wt; inv Wt; econstructor; simpl_Forall; eauto using wt_exp_incl, wt_cexp_incl.
    Qed.

  End incl.
  Global Hint Resolve wt_clock_incl wt_exp_incl wt_cexp_incl wt_rhs_incl : nltyping stctyping.

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
