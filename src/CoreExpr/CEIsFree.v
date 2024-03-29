From Velus Require Import Common.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import CoreExpr.CESyntax.
From Coq Require Import List.

(** * Free variables *)

(**

The predicate [Is_free x t : Prop] states that the variable [x] is
used in the term [t].
 *)

Module Type CEISFREE
       (Ids         : IDS)
       (Op          : OPERATORS)
       (OpAux       : OPERATORS_AUX Ids Op)
       (Import Cks  : CLOCKS        Ids Op OpAux)
       (Import Syn  : CESYNTAX      Ids Op OpAux Cks).

  (* Warning: induction scheme is not strong enough. *)
  Inductive Is_free_in_exp : ident -> exp -> Prop :=
  | FreeEvar: forall x ty, Is_free_in_exp x (Evar x ty)
  | FreeEwhen1: forall e c cv x,
      Is_free_in_exp x e ->
      Is_free_in_exp x (Ewhen e c cv)
  | FreeEwhen2: forall e c tx cv,
      Is_free_in_exp c (Ewhen e (c, tx) cv)
  | FreeEunop : forall c op e ty,
      Is_free_in_exp c e -> Is_free_in_exp c (Eunop op e ty)
  | FreeEbinop : forall c op e1 e2 ty,
      Is_free_in_exp c e1 \/ Is_free_in_exp c e2 -> Is_free_in_exp c (Ebinop op e1 e2 ty).

  Inductive Is_free_in_aexp : ident -> clock -> exp -> Prop :=
  | freeAexp1: forall ck e x,
      Is_free_in_exp x e  ->
      Is_free_in_aexp x ck e
  | freeAexp2: forall ck e x,
      Is_free_in_clock x ck ->
      Is_free_in_aexp x ck e.

  Inductive Is_free_in_aexps : ident -> clock -> list exp -> Prop :=
  | freeAexps1: forall ck les x,
      Exists (Is_free_in_exp x) les ->
      Is_free_in_aexps x ck les
  | freeAexps2: forall ck les x,
      Is_free_in_clock x ck ->
      Is_free_in_aexps x ck les.

  Inductive Is_free_in_cexp : ident -> cexp -> Prop :=
  | FreeEmerge_cond: forall i ti l ty,
      Is_free_in_cexp i (Emerge (i, ti) l ty)
  | FreeEmerge_branches: forall i l ty x,
      Exists (Is_free_in_cexp x) l ->
      Is_free_in_cexp x (Emerge i l ty)
  | FreeEcase_cond: forall x b l ty,
      Is_free_in_exp x b ->
      Is_free_in_cexp x (Ecase b l ty)
  | FreeEcase_branches: forall x b l d,
      Exists (fun os => exists e, os = Some e /\ Is_free_in_cexp x e) l ->
      Is_free_in_cexp x (Ecase b l d)
  | FreeEcase_default : forall x b l d,
      Is_free_in_cexp x d ->
      Is_free_in_cexp x (Ecase b l d)
  | FreeEexp: forall e x,
      Is_free_in_exp x e ->
      Is_free_in_cexp x (Eexp e).

  Inductive Is_free_in_rhs : ident -> rhs -> Prop :=
  | FreeEextcall: forall x f es ty,
      Exists (Is_free_in_exp x) es ->
      Is_free_in_rhs x (Eextcall f es ty)
  | FreeEcexp: forall x e,
      Is_free_in_cexp x e ->
      Is_free_in_rhs x (Ecexp e).

  Inductive Is_free_in_arhs : ident -> clock -> rhs -> Prop :=
  | FreeArhs1 : forall ck ce x,
      Is_free_in_rhs x ce ->
      Is_free_in_arhs x ck ce
  | FreeArhs2 : forall ck ce x,
      Is_free_in_clock x ck ->
      Is_free_in_arhs x ck ce.

  Global Hint Constructors Is_free_in_clock Is_free_in_exp
       Is_free_in_aexp Is_free_in_aexps Is_free_in_cexp
       Is_free_in_rhs Is_free_in_arhs: nlfree stcfree.

  (** * Decision procedure *)

  Lemma Is_free_in_clock_disj:
    forall y ck x c, Is_free_in_clock y (Con ck x c)
                     <-> y = x \/ Is_free_in_clock y ck.
  Proof.
    intros y ck x c; split; intro HH.
    inversion_clear HH; auto.
    destruct HH as [HH|HH]; subst; auto with nlfree.
  Qed.

  Lemma Is_free_in_when_disj:
    forall y e x tx c, Is_free_in_exp y (Ewhen e (x, tx) c)
                  <-> y = x \/ Is_free_in_exp y e.
  Proof.
    intros y e x c; split; intro HH.
    inversion_clear HH; auto.
    destruct HH as [HH|HH]; subst; auto with nlfree.
  Qed.

  Fixpoint free_in_clock_dec (ck : clock) (T: PS.t)
    : { S | forall x, PS.In x S <-> (Is_free_in_clock x ck \/ PS.In x T) }.
    refine (
        match ck with
        | Cbase => exist _ T _
        | Con ck' x c =>
          match free_in_clock_dec ck' T with
          | exist _ S' HF => exist _ (PS.add x S') _
          end
        end).
    - intro x; split; intro HH; auto.
      destruct HH as [HH|HH]; [inversion HH|exact HH].
    - intro y; split; intro HH.
      + apply PS.add_spec in HH as [|HH]; subst; auto with nlfree.
        apply HF in HH as [|]; auto with nlfree.
      + rewrite Is_free_in_clock_disj in HH.
        apply or_assoc in HH. rewrite PS.add_spec.
        destruct HH as [HH|HH]; subst; auto.
        right. apply HF; auto.
  Defined.

  Fixpoint free_in_clock (ck : clock) (fvs: PS.t) : PS.t :=
    match ck with
    | Cbase => fvs
    | Con ck' x _ => free_in_clock ck' (PS.add x fvs)
    end.

  Fixpoint free_in_exp (e: exp) (fvs: PS.t) : PS.t :=
    match e with
    | Econst _ => fvs
    | Eenum _ _ => fvs
    | Evar x _ => PS.add x fvs
    | Ewhen e (x, _) _ => free_in_exp e (PS.add x fvs)
    | Eunop _ e _ => free_in_exp e fvs
    | Ebinop _ e1 e2 _ => free_in_exp e2 (free_in_exp e1 fvs)
    end.

  Definition free_in_aexp (ck: clock)(le : exp) (fvs : PS.t) : PS.t :=
    free_in_exp le (free_in_clock ck fvs).

  Definition free_in_aexps (ck: clock) (es : list exp) (fvs : PS.t) : PS.t :=
    fold_left (fun fvs e => free_in_exp e fvs) es (free_in_clock ck fvs).

  Fixpoint free_in_cexp (ce: cexp) (fvs: PS.t) : PS.t :=
    match ce with
    | Emerge (i, _) l _ => fold_left (fun fvs e => free_in_cexp e fvs) l (PS.add i fvs)
    | Ecase b l d       =>
      free_in_cexp d (fold_left (fun fvs => or_default_with fvs (fun e => free_in_cexp e fvs)) l (free_in_exp b fvs))
    | Eexp e            => free_in_exp e fvs
    end.

  Definition free_in_rhs (e: rhs) (fvs: PS.t) : PS.t :=
    match e with
    | Eextcall f es ty => fold_left (fun fvs e => free_in_exp e fvs) es fvs
    | Ecexp e => free_in_cexp e fvs
    end.

  Definition free_in_arhs (ck: clock) (e: rhs) (fvs: PS.t) : PS.t :=
    free_in_rhs e (free_in_clock ck fvs).

  (** * Specification lemmas *)

  Lemma free_in_clock_spec:
    forall x ck m, PS.In x (free_in_clock ck m)
                   <-> Is_free_in_clock x ck \/ PS.In x m.
  Proof.
    induction ck.
    - split; [intros|intros [Hck|]]; auto.
      inv Hck.
    - split; intro H0.
      + apply IHck in H0; destruct H0 as [H0|H0]; auto with nlfree.
        apply PS.add_spec in H0 as [|]; subst; auto with nlfree.
      + apply IHck. rewrite PS.add_spec.
        destruct H0 as [H0|H0]; inversion H0; subst; auto.
  Qed.

  Corollary free_in_clock_spec':
    forall x ck, PS.In x (free_in_clock ck PS.empty)
                 <-> Is_free_in_clock x ck.
  Proof.
    intros.
    rewrite (free_in_clock_spec x ck PS.empty).
    split; [intros [HH|HH]|intro HH]; intuition.
  Qed.

  Lemma free_in_exp_spec:
    forall x e m, PS.In x (free_in_exp e m)
                  <-> Is_free_in_exp x e \/ PS.In x m.
  Proof.
    intro x; induction e using exp_ind; destruct_conjs;
      try now intro m; (split;
                        [
                          intro H0; try apply IHe in H0
                        | intro H0; try apply IHe
                       ]);
      try destruct H0 as [H0|H0];
      try apply free_in_clock_spec in H0;
      try inversion H0; subst;
        try apply PS.add_spec;
        solve [
            auto with nlfree
          | right; apply free_in_clock_spec; auto
          | apply PS.add_spec in H1; destruct H1; subst; auto with nlfree
          | right; apply PS.add_spec; auto ].
    intro m.
    split; intro HH.
    - simpl in HH.
      apply IHe2 in HH.
      destruct HH as [HH|HH]; [now intuition|].
      apply IHe1 in HH. intuition.
    - simpl.
      destruct HH as [HH|HH].
      + inversion_clear HH as [| | | |? ? ? ? ? Hf].
        apply IHe2.
        destruct Hf as [HH|HH]; auto.
        right. apply IHe1; auto.
      + apply IHe2; right; apply IHe1; auto.
  Qed.

  Lemma free_in_exp_spec':
    forall x e, PS.In x (free_in_exp e PS.empty)
                <-> Is_free_in_exp x e.
  Proof.
    setoid_rewrite (free_in_exp_spec _ _ PS.empty); intuition.
  Qed.

  Lemma free_in_aexp_spec:
    forall x ck e m, PS.In x (free_in_aexp ck e m)
                     <-> Is_free_in_aexp x ck e \/ PS.In x m.
  Proof.
    destruct e; split; intros;
      repeat
        (match goal with
         | H:_ \/ _ |- _ => destruct H as [H|H]
         | H:PS.In _ (free_in_aexp _ _ _) |- _ => apply free_in_exp_spec in H
         | H:PS.In _ (free_in_clock _ _) |- _ => apply free_in_clock_spec in H
         | |- PS.In _ (free_in_aexp _ _ _) => apply free_in_exp_spec
         | H:Is_free_in_aexp _ _ _ |- _ => inversion_clear H
         | |- context[PS.In _ (free_in_clock _ _)] => rewrite free_in_clock_spec
         end); auto with nlfree.
  Qed.

  Lemma free_in_aexp_spec':
    forall x ck e, PS.In x (free_in_aexp ck e PS.empty)
                   <-> Is_free_in_aexp x ck e.
  Proof.
    setoid_rewrite (free_in_aexp_spec _ _ _ PS.empty); intuition.
  Qed.

  Lemma free_in_fold_left_exp_spec : forall x l m,
      PS.In x (fold_left (fun fvs e => free_in_exp e fvs) l m) <->
      Exists (Is_free_in_exp x) l \/ PS.In x m.
  Proof.
    intros x l. induction l; intro m; simpl.
    - split; [intros|intros [Hex|]]; auto. inv Hex.
    - rewrite IHl. rewrite free_in_exp_spec.
      split; intros [H | H]; auto.
      + destruct H as [H | H]; auto with datatypes.
      + inversion_clear H; auto.
  Qed.

  Lemma free_in_aexps_spec:
    forall x ck e m, PS.In x (free_in_aexps ck e m)
                     <-> Is_free_in_aexps x ck e \/ PS.In x m.
  Proof.
    intros x c l m. unfold free_in_aexps.
    rewrite free_in_fold_left_exp_spec.
    rewrite free_in_clock_spec.
    split; intros [H | H]; auto; inversion H; auto with nlfree.
  Qed.

  Lemma free_in_aexps_spec':
    forall x ck l, PS.In x (free_in_aexps ck l PS.empty)
                   <-> Is_free_in_aexps x ck l.
  Proof.
    setoid_rewrite (free_in_aexps_spec _ _ _ PS.empty); intuition.
  Qed.

  Ltac destruct_Is_free :=
    repeat match goal with
           | H: _ \/ _ |- _ =>
             destruct H

           | H: Is_free_in_cexp _ (Emerge _ _ _) |- _ =>
             inversion H; subst; clear H

           | H: Is_free_in_cexp _ (Ecase _ _ _) |- _ =>
             inversion H; subst; clear H

           | H: Is_free_in_cexp _ (Eexp _) |- _ =>
             inversion H; subst; clear H

           | IHe: context[PS.In _ (free_in_cexp ?e _)],
                  H:PS.In _ (free_in_cexp ?e _) |- _ =>
             apply IHe in H

           | H: PS.In _ (free_in_exp _ _) |- _ =>
             apply free_in_exp_spec in H

           | H: PS.In _ (PS.add _ _) |- _ =>
             apply PS.add_spec in H
           end.

  Lemma In_fold_left_free_in_cexp_aux:
    forall l x m,
      Forall (fun e =>
                forall x m,
                  PS.In x (free_in_cexp e m) <-> PS.In x (free_in_cexp e PS.empty) \/ PS.In x m) l ->
      PS.In x (fold_left (fun fvs e => free_in_cexp e fvs) l m) <->
      (PS.In x (fold_left (fun fvs e => free_in_cexp e fvs) l PS.empty)
       \/ PS.In x m).
  Proof.
    induction l as [|e]; simpl; inversion_clear 1 as [|?? He].
    - rewrite PSF.empty_iff; tauto.
    - rewrite IHl; auto.
      rewrite (IHl _ (free_in_cexp e PS.empty)); auto.
      rewrite He, or_assoc; reflexivity.
  Qed.

  Lemma In_fold_left_or_default_free_in_cexp_aux:
    forall l x m,
      Forall
        (or_default_with True
           (fun e : cexp =>
            forall (x : positive) (m : PS.t),
            PS.In x (free_in_cexp e m) <-> PS.In x (free_in_cexp e PS.empty) \/ PS.In x m)) l ->
      PS.In x (fold_left (fun fvs => or_default_with fvs (fun e0 : cexp => free_in_cexp e0 fvs)) l m) <->
      (PS.In x (fold_left (fun fvs => or_default_with fvs (fun e0 : cexp => free_in_cexp e0 fvs)) l PS.empty)
       \/ PS.In x m).
  Proof.
    induction l as [|e]; simpl; inversion_clear 1 as [|?? He].
    - rewrite PSF.empty_iff; tauto.
    - rewrite IHl; auto.
      symmetry; rewrite IHl; auto.
      destruct e; simpl in *.
      + symmetry; rewrite He; tauto.
      + rewrite PSF.empty_iff. tauto.
  Qed.

  Lemma In_free_in_cexp:
    forall e x m,
      PS.In x (free_in_cexp e m) <-> PS.In x (free_in_cexp e PS.empty) \/ PS.In x m.
  Proof.
    induction e using cexp_ind2'; simpl; intros.
    - destruct x as (x, _); rewrite In_fold_left_free_in_cexp_aux; auto.
      rewrite (In_fold_left_free_in_cexp_aux _ _ (PS.add x PS.empty)); auto.
      rewrite ? PS.add_spec, ? or_assoc, PSF.empty_iff; tauto.
    - rewrite IHe, In_fold_left_or_default_free_in_cexp_aux, free_in_exp_spec; auto.
      symmetry. rewrite IHe, In_fold_left_or_default_free_in_cexp_aux; auto.
      rewrite free_in_exp_spec. repeat rewrite PSF.empty_iff. tauto.
    - rewrite 2 free_in_exp_spec, PSF.empty_iff; tauto.
  Qed.

  Corollary In_fold_left_free_in_cexp:
    forall l x m,
      PS.In x (fold_left (fun fvs e => free_in_cexp e fvs) l m) <->
      (PS.In x (fold_left (fun fvs e => free_in_cexp e fvs) l PS.empty)
       \/ PS.In x m).
  Proof.
    intros; apply In_fold_left_free_in_cexp_aux.
    apply Forall_forall; intros; apply In_free_in_cexp.
  Qed.

  Corollary In_fold_left_or_default_free_in_cexp:
    forall l x m,
      PS.In x (fold_left (fun fvs => or_default_with fvs (fun e0 : cexp => free_in_cexp e0 fvs)) l m) <->
      (PS.In x (fold_left (fun fvs => or_default_with fvs (fun e0 : cexp => free_in_cexp e0 fvs)) l PS.empty)
       \/ PS.In x m).
  Proof.
    intros; apply In_fold_left_or_default_free_in_cexp_aux.
    apply Forall_forall; intros. destruct x0; simpl; auto. apply In_free_in_cexp.
  Qed.

  Lemma free_in_cexp_spec:
    forall e x m, PS.In x (free_in_cexp e m)
                  <-> Is_free_in_cexp x e \/ PS.In x m.
  Proof with auto with nlfree.
    induction e using cexp_ind2';
      intros; simpl; split; intro H0;
        destruct_Is_free;
        subst; auto;
          try rewrite IHe2, IHe1;
          try rewrite free_in_exp_spec;
          auto with nlfree.
    - induction l as [|e]; destruct x; simpl in *.
      + apply PS.add_spec in H0 as []; subst...
      + apply In_fold_left_free_in_cexp in H0 as [|Hin].
        * inv H.
          destruct IHl as [Free|]; auto.
          -- apply In_fold_left_free_in_cexp; auto.
          -- inv Free; left; constructor.
             right; auto.
        * apply In_free_in_cexp in Hin as [Hin|Hin].
          -- inversion_clear H as [|?? He].
             apply He in Hin.
             rewrite PSF.empty_iff in Hin; destruct Hin; try contradiction.
             left; constructor; left; auto.
          -- apply PS.add_spec in Hin as []; subst...
    - induction l as [|e]; simpl in *.
      + apply PS.add_spec; auto.
      + apply In_fold_left_free_in_cexp.
        inversion_clear H as [|?? He Hl].
        apply IHl, In_fold_left_free_in_cexp in Hl as [|Hin]; auto.
        rewrite In_free_in_cexp; auto.
    - simpl_Exists. simpl_Forall.
      apply In_split in Hin as (l1 & l2 & E); subst.
      rewrite fold_left_app; simpl.
      rewrite 2 In_fold_left_free_in_cexp, In_free_in_cexp, H; auto.
    - destruct x. apply In_fold_left_free_in_cexp.
      right; apply PSF.add_2; auto.
    - apply In_fold_left_or_default_free_in_cexp in H0 as [Hin|].
      + left. apply FreeEcase_branches.
        induction l as [|e']; simpl in *; inv H. apply not_In_empty in Hin; inv Hin.
        apply In_fold_left_or_default_free_in_cexp in Hin as [|Hin].
        * right. eapply IHl; eauto.
        * destruct e'; simpl in *; try (solve [inv Hin]).
          left. repeat esplit; eauto. apply H2 in Hin as [|Hin]; auto.
          apply not_In_empty in Hin; inv Hin.
      + apply free_in_exp_spec in H0 as []...
    - rewrite In_free_in_cexp, In_fold_left_or_default_free_in_cexp. do 2 right.
      apply free_in_exp_spec; auto.
    - rewrite In_free_in_cexp, In_fold_left_or_default_free_in_cexp. right; left.
      induction l as [|e']; simpl in *.
      + inv H3.
      + rewrite In_fold_left_or_default_free_in_cexp. inv H; inv H3; eauto.
        right. destruct H0 as (?&?&?); subst; simpl in *. eapply H2; eauto.
    - rewrite In_free_in_cexp. left. apply IHe; auto.
    - rewrite In_free_in_cexp, In_fold_left_or_default_free_in_cexp, free_in_exp_spec. auto.
  Qed.

  Lemma free_in_cexp_spec':
    forall x e, PS.In x (free_in_cexp e PS.empty)
                <-> Is_free_in_cexp x e.
  Proof.
    setoid_rewrite (free_in_cexp_spec _ _ PS.empty); intuition.
  Qed.

  Lemma free_in_rhs_spec:
    forall e x m, PS.In x (free_in_rhs e m)
                  <-> Is_free_in_rhs x e \/ PS.In x m.
  Proof.
    intros [] *; simpl.
    - rewrite free_in_fold_left_exp_spec.
      split; intros []; auto; left; auto using Is_free_in_rhs.
      now inv H.
    - rewrite free_in_cexp_spec.
      split; intros []; auto; left; auto using Is_free_in_rhs.
      now inv H.
  Qed.

  Lemma free_in_arhs_spec:
    forall x ck e m, PS.In x (free_in_arhs ck e m)
                     <-> Is_free_in_arhs x ck e \/ PS.In x m.
  Proof.
    unfold free_in_arhs.
    intros *; rewrite free_in_rhs_spec, free_in_clock_spec.
    split; intros; intuition; auto using Is_free_in_arhs.
    inv H0; auto.
  Qed.

End CEISFREE.

Module CEIsFreeFun
       (Ids  : IDS)
       (Op   : OPERATORS)
       (OpAux: OPERATORS_AUX Ids Op)
       (Cks  : CLOCKS        Ids Op OpAux)
       (Syn  : CESYNTAX      Ids Op OpAux Cks)
       <: CEISFREE Ids Op OpAux Cks Syn.
  Include CEISFREE Ids Op OpAux Cks Syn.
End CEIsFreeFun.
