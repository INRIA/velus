From Coq Require Import FSets.FMapPositive.
From Velus Require Import Common.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import Environment.

From Coq Require Import List.
From Coq Require Import Morphisms.
From Coq Require Import Permutation.

(** * Well clocked expressions *)

Module Type CECLOCKING
       (Import Ids  : IDS)
       (Import Op   : OPERATORS)
       (Import OpAux: OPERATORS_AUX Ids Op)
       (Import Cks  : CLOCKS        Ids Op OpAux)
       (Import Syn  : CESYNTAX      Ids Op OpAux Cks).

  Inductive SameVar : option ident -> exp -> Prop :=
  | SVNone: forall e,
      SameVar None e
  | SVSome: forall x ty,
      SameVar (Some x) (Evar x ty).

  Section WellClocked.

    Variable Γ : list (ident * (clock * bool)).

    Inductive wc_exp : exp -> clock -> Prop :=
    | Cconst:
        forall c,
          wc_exp (Econst c) Cbase
    | Cenum:
        forall x ty,
          wc_exp (Eenum x ty) Cbase
    | Cvar:
        forall x ck islast ty,
          In (x, (ck, islast)) Γ ->
          wc_exp (Evar x ty) ck
    | Clast:
      forall x ck ty,
        In (x, (ck, true)) Γ ->
        wc_exp (Elast x ty) ck
    | Cwhen:
        forall e x tx t b ck islast,
          wc_exp e ck ->
          In (x, (ck, islast)) Γ ->
          wc_exp (Ewhen e (x, tx) b) (Con ck x (t, b))
    | Cunop:
        forall op e ck ty,
          wc_exp e ck ->
          wc_exp (Eunop op e ty) ck
    | Cbinop:
        forall op e1 e2 ck ty,
          wc_exp e1 ck ->
          wc_exp e2 ck ->
          wc_exp (Ebinop op e1 e2 ty) ck.

    Inductive wc_cexp : cexp -> clock -> Prop :=
    | Cmerge:
        forall x tx l ty ck islast,
          In (x, (ck, islast)) Γ ->
          l <> nil ->
          Forall2 (fun i e => wc_cexp e (Con ck x (tx, i))) (seq 0 (length l)) l ->
          wc_cexp (Emerge (x, tx) l ty) ck
    | Ccase:
        forall c l d ck,
          wc_exp c ck ->
          l <> nil ->
          wc_cexp d ck ->
          (forall e, In (Some e) l -> wc_cexp e ck) ->
          wc_cexp (Ecase c l d) ck
    | Cexp:
        forall e ck,
          wc_exp e ck ->
          wc_cexp (Eexp e) ck.

    Inductive wc_rhs : rhs -> clock -> Prop :=
    | Cextcall:
        forall f es ty ck,
          Forall (fun e => wc_exp e ck) es ->
          wc_rhs (Eextcall f es ty) ck
    | Ccexp:
        forall e ck,
          wc_cexp e ck ->
          wc_rhs (Ecexp e) ck.

  End WellClocked.

  (** ** Basic properties of clocking *)

  Lemma wc_clock_exp:
    forall vars le ck,
      wc_env (idfst vars) ->
      wc_exp vars le ck ->
      wc_clock (idfst vars) ck.
  Proof.
    induction le as [| | | |le IH| |] (* using exp_ind2 *).
    - inversion_clear 2; now constructor.
    - inversion_clear 2; now constructor.
    - intros ck Hwc; inversion_clear 1 as [| |? ? ? Hcv| | | |].
      eapply wc_env_var; eauto. solve_In.
    - intros ck Hwc; inversion_clear 1 as [| | |? ? ? Hcv| | |].
      eapply wc_env_var; eauto. solve_In.
    - intros ck Hwc.
      inversion_clear 1 as [| | | |?????? ck' Hle Hcv | |].
      constructor; auto. solve_In.
    - intros ck Hwc; inversion_clear 1; auto.
    - intros ck Hwc; inversion_clear 1; auto.
  Qed.

  Lemma wc_clock_cexp:
    forall vars ce ck,
      wc_env (idfst vars) ->
      wc_cexp vars ce ck ->
      wc_clock (idfst vars) ck.
  Proof.
    induction ce as [? ces ? IHces|? ces ? IHces|] using cexp_ind2'.
    - intros ck Hwc.
      inversion_clear 1 as [?????? Hcv ? Hcs| |].
      destruct ces as [|e]; try contradiction.
      inversion_clear Hcs as [|???? Hc]; inversion_clear IHces as [|?? IHce].
      apply IHce with (1:=Hwc) in Hc.
      inversion_clear Hc; assumption.
    - intros ck Hwc; inversion_clear 1; auto.
    - intros ck Hwc; inversion_clear 1 as [| |? ? Hck].
      apply wc_clock_exp with (1:=Hwc) (2:=Hck).
  Qed.

  Global Hint Constructors wc_clock wc_exp wc_cexp : nlclocking.
  Global Hint Resolve Forall_nil : nlclocking.

  Global Instance wc_exp_Proper:
    Proper (@Permutation _ ==> @eq exp ==> @eq clock ==> iff)
           wc_exp.
  Proof.
    intros env' env Henv e' e He ck' ck Hck.
    rewrite He, Hck; clear He Hck e' ck'.
    revert ck.
    induction e; split; inversion_clear 1; econstructor; eauto.
    all:try rewrite Henv; eauto.
    all:try rewrite <-Henv; eauto.
    all:repeat (take (forall ck, _ <-> _) and try apply it; clear it; auto).
  Qed.

  Global Instance wc_cexp_Proper:
    Proper (@Permutation _ ==> @eq cexp ==> @eq clock ==> iff)
           wc_cexp.
  Proof.
    intros env' env Henv e' e He ck' ck Hck.
    rewrite He, Hck; clear He Hck e' ck'.
    revert ck.
    induction e using cexp_ind2'; split; inversion_clear 1; econstructor; eauto.
    all:try rewrite Henv; eauto.
    all:try rewrite <-Henv; eauto.
    all:intros; simpl_Forall.
    all:repeat (take (forall ck, _ <-> _) and try apply it; clear it; auto).
  Qed.

  Global Instance wc_rhs_Proper:
    Proper (@Permutation.Permutation (ident * _) ==>
            @eq _ ==> @eq _ ==> iff)
           wc_rhs.
  Proof.
    intros env' env Henv e' e ? ck' ck ?; subst.
    destruct e; split; intros Hwc; inv Hwc; econstructor; eauto; simpl_Forall.
    all:try rewrite Henv; auto.
    all:try rewrite <-Henv; auto.
  Qed.

  Section incl.
    Variable (Γ Γ' : list (ident * (clock * bool))).
    Hypothesis Hincl : incl Γ Γ'.

    Fact wc_clock_incl : forall ck,
        wc_clock (idfst Γ) ck ->
        wc_clock (idfst Γ') ck.
    Proof.
      intros * Hwc.
      induction Hwc.
      - constructor.
      - constructor; auto.
        eapply incl_map; eauto.
    Qed.

    Lemma wc_exp_incl : forall e ck,
        wc_exp Γ e ck ->
        wc_exp Γ' e ck.
    Proof.
      induction e; intros * Hwc; inv Hwc; econstructor; eauto.
    Qed.

    Lemma wc_cexp_incl : forall e ck,
        wc_cexp Γ e ck ->
        wc_cexp Γ' e ck.
    Proof.
      induction e using cexp_ind2'; intros * Hwc; inv Hwc; econstructor; eauto using wc_exp_incl.
      - simpl_Forall. eauto.
      - intros. eapply Forall_forall in H; eauto.
        simpl in *; eauto.
    Qed.

    Lemma wc_rhs_incl : forall e ck,
        wc_rhs Γ e ck ->
        wc_rhs Γ' e ck.
    Proof.
      intros * Hwc; inv Hwc; econstructor; simpl_Forall; eauto using wc_exp_incl, wc_cexp_incl.
    Qed.

  End incl.

  Global Hint Resolve wc_clock_incl wc_exp_incl wc_cexp_incl wc_rhs_incl : nlclocking stcclocking.

End CECLOCKING.

Module CEClockingFun
       (Ids  : IDS)
       (Op   : OPERATORS)
       (OpAux: OPERATORS_AUX Ids Op)
       (Cks  : CLOCKS        Ids Op OpAux)
       (Syn  : CESYNTAX      Ids Op OpAux Cks)
  <: CECLOCKING Ids Op OpAux Cks Syn.
  Include CECLOCKING Ids Op OpAux Cks Syn.
End CEClockingFun.
