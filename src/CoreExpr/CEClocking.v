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

    Variable vars : list (ident * clock).

    Inductive wc_exp : exp -> clock -> Prop :=
    | Cconst:
        forall c,
          wc_exp (Econst c) Cbase
    | Cenum:
        forall x ty,
          wc_exp (Eenum x ty) Cbase
    | Cvar:
        forall x ck ty,
          In (x, ck) vars ->
          wc_exp (Evar x ty) ck
    | Cwhen:
        forall e x t b ck,
          wc_exp e ck ->
          In (x, ck) vars ->
          wc_exp (Ewhen e x b) (Con ck x (t, b))
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
        forall x tx l ty ck,
          In (x, ck) vars ->
          l <> nil ->
          Forall2 (fun i e => wc_cexp e (Con ck x (tx, i))) (seq 0 (length l)) l ->
          wc_cexp (Emerge (x, tx) l ty) ck
    | Ccase:
        forall c l ty ck,
          wc_exp c ck ->
          l <> nil ->
          Forall (fun e => wc_cexp e ck) l ->
          wc_cexp (Ecase c l ty) ck
    | Cexp:
        forall e ck,
          wc_exp e ck ->
          wc_cexp (Eexp e) ck.

  End WellClocked.

  (** ** Basic properties of clocking *)

  Lemma wc_clock_exp:
    forall vars le ck,
      wc_env vars ->
      wc_exp vars le ck ->
      wc_clock vars ck.
  Proof.
    induction le as [| | |le IH| |] (* using exp_ind2 *).
    - inversion_clear 2; now constructor.
    - inversion_clear 2; now constructor.
    - intros ck Hwc; inversion_clear 1 as [| |? ? ? Hcv| | |].
      apply wc_env_var with (1:=Hwc) (2:=Hcv).
    - intros ck Hwc.
      inversion_clear 1 as [| | |???? ck' Hle Hcv | |].
      constructor; [now apply IH with (1:=Hwc) (2:=Hle)|assumption].
    - intros ck Hwc; inversion_clear 1; auto.
    - intros ck Hwc; inversion_clear 1; auto.
  Qed.

  Lemma wc_clock_cexp:
    forall vars ce ck,
      wc_env vars ->
      wc_cexp vars ce ck ->
      wc_clock vars ck.
  Proof.
    induction ce as [? ces ? IHces|? ces ? IHces|] using cexp_ind2.
    - intros ck Hwc.
      inversion_clear 1 as [????? Hcv ? Hcs| |].
      destruct ces as [|e]; try contradiction.
      inversion_clear Hcs as [|???? Hc]; inversion_clear IHces as [|?? IHce].
      apply IHce with (1:=Hwc) in Hc.
      inversion_clear Hc; assumption.
    - intros ck Hwc.
      inversion_clear 1 as [|???? Hcv ? Hcs|].
      destruct ces as [|e]; try contradiction.
      inversion_clear Hcs as [|?? Hc]; inversion_clear IHces as [|?? IHce].
      apply IHce with (1:=Hwc) in Hc; auto.
    - intros ck Hwc; inversion_clear 1 as [| |? ? Hck].
      apply wc_clock_exp with (1:=Hwc) (2:=Hck).
  Qed.

  Hint Constructors wc_clock wc_exp wc_cexp : nlclocking.
  Hint Resolve Forall_nil : nlclocking.

  Instance wc_exp_Proper:
    Proper (@Permutation (ident * clock) ==> @eq exp ==> @eq clock ==> iff)
           wc_exp.
  Proof.
    intros env' env Henv e' e He ck' ck Hck.
    rewrite He, Hck; clear He Hck e' ck'.
    revert ck.
    induction e;
      split; auto with nlclocking;
        inversion_clear 1;
        (rewrite Henv in * || rewrite <-Henv in * || idtac);
        try edestruct IHe;
        try edestruct IHe1, IHe2;
        auto with nlclocking.
  Qed.

  Instance wc_cexp_Proper:
    Proper (@Permutation (ident * clock) ==> @eq cexp ==> @eq clock ==> iff)
           wc_cexp.
  Proof.
    intros env' env Henv e' e He ck' ck Hck.
    rewrite He, Hck; clear He Hck e' ck'.
    revert ck.
    induction e using cexp_ind2;
      split; inversion_clear 1;
        try (
        (rewrite Henv in * || rewrite <-Henv in *);
         constructor; auto;
         now (rewrite <-IHe1 || rewrite IHe1
              || rewrite <-IHe2 || rewrite IHe2)).
        - rewrite Henv in *.
          constructor; auto.
          take (_ <> nil) and clear it.
          revert dependent l; intro.
          generalize 0.
          induction l; simpl; intros * IH H; auto.
          inv H; inversion_clear IH as [|?? H'].
          constructor; auto.
          apply H'; auto.
        - rewrite <-Henv in *.
          constructor; auto.
          take (_ <> nil) and clear it.
          revert dependent l; intro.
          generalize 0.
          induction l; simpl; intros * IH H; auto.
          inv H; inversion_clear IH as [|?? H'].
          constructor; auto.
          apply H'; auto.
        - rewrite Henv in *.
          constructor; auto.
          eapply Forall_impl_In; [|eauto]. intros.
          eapply Forall_forall in H; eauto. apply H; auto.
        - rewrite <-Henv in *.
          constructor; auto.
          eapply Forall_impl_In; [|eauto]. intros.
          eapply Forall_forall in H; eauto. apply H; auto.
  Qed.

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
