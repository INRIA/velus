From Velus Require Import Common.
From Velus Require Import FunctionalEnvironment.
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
  Inductive Is_free_in_exp : var_last -> exp -> Prop :=
  | FreeEvar: forall x ty, Is_free_in_exp (Var x) (Evar x ty)
  | FreeElast: forall x ty, Is_free_in_exp (Last x) (Elast x ty)
  | FreeEwhen1: forall e c cv x,
      Is_free_in_exp x e ->
      Is_free_in_exp x (Ewhen e c cv)
  | FreeEwhen2: forall e c tx cv,
      Is_free_in_exp (Var c) (Ewhen e (c, tx) cv)
  | FreeEunop : forall c op e ty,
      Is_free_in_exp c e -> Is_free_in_exp c (Eunop op e ty)
  | FreeEbinop : forall c op e1 e2 ty,
      Is_free_in_exp c e1 \/ Is_free_in_exp c e2 -> Is_free_in_exp c (Ebinop op e1 e2 ty).

  Inductive Is_free_in_aexp : var_last -> clock -> exp -> Prop :=
  | freeAexp1: forall ck e x,
      Is_free_in_exp x e  ->
      Is_free_in_aexp x ck e
  | freeAexp2: forall ck e x,
      Is_free_in_clock x ck ->
      Is_free_in_aexp (Var x) ck e.

  Inductive Is_free_in_aexps : var_last -> clock -> list exp -> Prop :=
  | freeAexps1: forall ck les x,
      Exists (Is_free_in_exp x) les ->
      Is_free_in_aexps x ck les
  | freeAexps2: forall ck les x,
      Is_free_in_clock x ck ->
      Is_free_in_aexps (Var x) ck les.

  Inductive Is_free_in_cexp : var_last -> cexp -> Prop :=
  | FreeEmerge_cond: forall i ti l ty,
      Is_free_in_cexp (Var i) (Emerge (i, ti) l ty)
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

  Inductive Is_free_in_acexp : var_last -> clock -> cexp -> Prop :=
  | freeAcexp1: forall ck e x,
      Is_free_in_cexp x e  ->
      Is_free_in_acexp x ck e
  | freeAcexp2: forall ck e x,
      Is_free_in_clock x ck ->
      Is_free_in_acexp (Var x) ck e.

  Inductive Is_free_in_rhs : var_last -> rhs -> Prop :=
  | FreeEextcall: forall x f es ty,
      Exists (Is_free_in_exp x) es ->
      Is_free_in_rhs x (Eextcall f es ty)
  | FreeEcexp: forall x e,
      Is_free_in_cexp x e ->
      Is_free_in_rhs x (Ecexp e).

  Inductive Is_free_in_arhs : var_last -> clock -> rhs -> Prop :=
  | FreeArhs1 : forall ck ce x,
      Is_free_in_rhs x ce ->
      Is_free_in_arhs x ck ce
  | FreeArhs2 : forall ck ce x,
      Is_free_in_clock x ck ->
      Is_free_in_arhs (Var x) ck ce.

  Global Hint Constructors Is_free_in_clock Is_free_in_exp
       Is_free_in_aexp Is_free_in_aexps
       Is_free_in_cexp Is_free_in_acexp
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
                  <-> y = Var x \/ Is_free_in_exp y e.
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

  Fixpoint free_in_exp (e: exp) (fvs: (PS.t * PS.t)) : (PS.t * PS.t) :=
    match e with
    | Econst _ => fvs
    | Eenum _ _ => fvs
    | Evar x _ => (PS.add x (fst fvs), snd fvs)
    | Elast x _ => (fst fvs, PS.add x (snd fvs))
    | Ewhen e (x, _) _ => free_in_exp e (PS.add x (fst fvs), snd fvs)
    | Eunop _ e _ => free_in_exp e fvs
    | Ebinop _ e1 e2 _ => free_in_exp e2 (free_in_exp e1 fvs)
    end.

  Definition free_in_aexp (ck: clock)(le : exp) (fvs : (PS.t * PS.t)) : (PS.t * PS.t) :=
    free_in_exp le (free_in_clock ck (fst fvs), snd fvs).

  Definition free_in_aexps (ck: clock) (es : list exp) (fvs : (PS.t * PS.t)) : (PS.t * PS.t) :=
    fold_left (fun fvs e => free_in_exp e fvs) es (free_in_clock ck (fst fvs), snd fvs).

  Fixpoint free_in_cexp (ce: cexp) (fvs: (PS.t * PS.t)) : (PS.t * PS.t) :=
    match ce with
    | Emerge (i, _) l _ => fold_left (fun fvs e => free_in_cexp e fvs) l (PS.add i (fst fvs), snd fvs)
    | Ecase b l d       =>
      free_in_cexp d (fold_left (fun fvs => or_default_with fvs (fun e => free_in_cexp e fvs)) l (free_in_exp b fvs))
    | Eexp e            => free_in_exp e fvs
    end.

  Definition free_in_acexp (ck: clock)(le : cexp) (fvs : (PS.t * PS.t)) : (PS.t * PS.t) :=
    free_in_cexp le (free_in_clock ck (fst fvs), snd fvs).

  Definition free_in_rhs (e: rhs) (fvs: (PS.t * PS.t)) : (PS.t * PS.t) :=
    match e with
    | Eextcall f es ty => fold_left (fun fvs e => free_in_exp e fvs) es fvs
    | Ecexp e => free_in_cexp e fvs
    end.

  Definition free_in_arhs (ck: clock) (e: rhs) (fvs: (PS.t * PS.t)) : (PS.t * PS.t) :=
    free_in_rhs e (free_in_clock ck (fst fvs), snd fvs).

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
    split; [intros [HH|HH]|intro HH]; auto with *.
  Qed.

  Lemma free_in_exp_spec1:
    forall x e m, PS.In x (fst (free_in_exp e m))
             <-> Is_free_in_exp (Var x) e \/ PS.In x (fst m).
  Proof.
    induction e; intros; destruct_conjs; simpl;
      repeat ((rewrite PS.add_spec||take (forall m, _ <-> _) and rewrite it; clear it); simpl);
      (split; [intros|intros [F|]; [inv F|]]);
      repeat (take (_ \/ _) and destruct it; subst); auto with nlfree.
  Qed.

  Corollary free_in_exp_spec1':
    forall x e, PS.In x (fst (free_in_exp e (PS.empty, PS.empty)))
           <-> Is_free_in_exp (Var x) e.
  Proof.
    intros.
    setoid_rewrite (free_in_exp_spec1 _ _ (PS.empty, PS.empty)).
    split.
    - intros [ H | H ]; [ assumption | inversion H ].
    - auto.
  Qed.

  Lemma free_in_exp_spec2:
    forall x e m, PS.In x (snd (free_in_exp e m))
             <-> Is_free_in_exp (Last x) e \/ PS.In x (snd m).
  Proof.
    induction e; intros; destruct_conjs; simpl;
      repeat ((rewrite PS.add_spec||take (forall m, _ <-> _) and rewrite it; clear it); simpl);
      (split; [intros|intros [F|]; [inv F|]]);
      repeat (take (_ \/ _) and destruct it; subst); auto with nlfree.
  Qed.

  Corollary free_in_exp_spec2':
    forall x e, PS.In x (snd (free_in_exp e (PS.empty, PS.empty)))
           <-> Is_free_in_exp (Last x) e.
  Proof.
    intros.
    setoid_rewrite (free_in_exp_spec2 _ _ (PS.empty, PS.empty)).
    split.
    - intros [ H | H ]; [ assumption | inversion H ].
    - auto.
  Qed.

  Lemma free_in_aexp_spec1:
    forall x ck e m, PS.In x (fst (free_in_aexp ck e m))
                <-> Is_free_in_aexp (Var x) ck e \/ PS.In x (fst m).
  Proof.
    intros. unfold free_in_aexp.
    rewrite free_in_exp_spec1; simpl; rewrite free_in_clock_spec.
    split; [intros|intros [F|]; [inv F|]];
      repeat (take (_ \/ _) and destruct it); auto with nlfree.
  Qed.

  Lemma free_in_aexp_spec2:
    forall x ck e m, PS.In x (snd (free_in_aexp ck e m))
                <-> Is_free_in_aexp (Last x) ck e \/ PS.In x (snd m).
  Proof.
    intros. unfold free_in_aexp.
    rewrite free_in_exp_spec2; simpl.
    split; [intros|intros [F|]; [inv F|]];
      repeat (take (_ \/ _) and destruct it); auto with nlfree.
  Qed.

  Lemma fold_left_spec1 {A} f In : forall (l : list A) (m: PS.t * PS.t) x,
      Forall (fun e => forall m x, PS.In x (fst (f m e)) <-> In x e \/ PS.In x (fst m)) l ->
      PS.In x (fst (fold_left f l m)) <-> Exists (In x) l \/ PS.In x (fst m).
  Proof.
    induction l; intros * F; inv F; simpl.
    - split; [intros|intros [Ex|]]; auto. inv Ex.
    - rewrite IHl, H1, Exists_cons; auto.
      intuition.
  Qed.

  Corollary free_in_fold_left_exp_spec1 : forall x l m,
      PS.In x (fst (fold_left (fun fvs e => free_in_exp e fvs) l m)) <->
      Exists (Is_free_in_exp (Var x)) l \/ PS.In x (fst m).
  Proof.
    intros.
    erewrite fold_left_spec1 with (In:=fun x => Is_free_in_exp (Var x)); [reflexivity|].
    simpl_Forall. apply free_in_exp_spec1.
  Qed.

  Lemma fold_left_spec2 {A} f In : forall (l : list A) (m: PS.t * PS.t) x,
      Forall (fun e => forall m x, PS.In x (snd (f m e)) <-> In x e \/ PS.In x (snd m)) l ->
      PS.In x (snd (fold_left f l m)) <-> Exists (In x) l \/ PS.In x (snd m).
  Proof.
    induction l; intros * F; inv F; simpl.
    - split; [intros|intros [Ex|]]; auto. inv Ex.
    - rewrite IHl, H1, Exists_cons; auto.
      intuition.
  Qed.

  Lemma free_in_fold_left_exp_spec2 : forall x l m,
      PS.In x (snd (fold_left (fun fvs e => free_in_exp e fvs) l m)) <->
      Exists (Is_free_in_exp (Last x)) l \/ PS.In x (snd m).
  Proof.
    intros.
    erewrite fold_left_spec2 with (In:=fun x => Is_free_in_exp (Last x)); [reflexivity|].
    simpl_Forall. apply free_in_exp_spec2.
  Qed.

  Lemma free_in_aexps_spec1:
    forall x ck e m, PS.In x (fst (free_in_aexps ck e m))
                <-> Is_free_in_aexps (Var x) ck e \/ PS.In x (fst m).
  Proof.
    intros x c l m. unfold free_in_aexps.
    rewrite free_in_fold_left_exp_spec1. simpl.
    rewrite free_in_clock_spec.
    split; intros [H | H]; auto; inversion H; auto with nlfree.
  Qed.

  Lemma free_in_aexps_spec2:
    forall x ck e m, PS.In x (snd (free_in_aexps ck e m))
                <-> Is_free_in_aexps (Last x) ck e \/ PS.In x (snd m).
  Proof.
    intros x c l m. unfold free_in_aexps.
    rewrite free_in_fold_left_exp_spec2. simpl.
    split; intros [H | H]; auto; inversion H; auto with nlfree.
  Qed.

  Lemma free_in_cexp_spec1:
    forall e x m, PS.In x (fst (free_in_cexp e m))
             <-> Is_free_in_cexp (Var x) e \/ PS.In x (fst m).
  Proof with auto with nlfree.
    induction e using cexp_ind2'; intros; destruct_conjs.
    - rewrite fold_left_spec1 with (In:=fun x => Is_free_in_cexp (Var x)).
      2:{ simpl_Forall. now rewrite H. }
      simpl. rewrite PS.add_spec.
      split; intros; repeat (take (_ \/ _) and destruct it; subst); auto with nlfree.
      take (Is_free_in_cexp _ _) and inv it; auto.
    - rewrite IHe, fold_left_spec1 with (In:=fun x o => exists e, o = Some e /\ Is_free_in_cexp (Var x) e), free_in_exp_spec1.
      2:{ simpl_Forall. destruct x0; simpl in *.
          - rewrite H. split; intros; repeat (take (_ \/ _) and destruct it; destruct_conjs); eauto.
            take (Some _ = Some _) and inv it. auto.
          - split; intros; repeat (take (_ \/ _) and destruct it; destruct_conjs); eauto.
            take (None = Some _) and inv it. }
      split; intros; repeat (take (_ \/ _) and destruct it; subst); auto with nlfree.
      take (Is_free_in_cexp _ _) and inv it; auto.
    - rewrite free_in_exp_spec1.
      split; intros; repeat (take (_ \/ _) and destruct it; subst); auto with nlfree.
      take (Is_free_in_cexp _ _) and inv it; auto.
  Qed.

  Lemma free_in_cexp_spec2:
    forall e x m, PS.In x (snd (free_in_cexp e m))
             <-> Is_free_in_cexp (Last x) e \/ PS.In x (snd m).
  Proof with auto with nlfree.
    induction e using cexp_ind2'; intros; destruct_conjs.
    - rewrite fold_left_spec2 with (In:=fun x => Is_free_in_cexp (Last x)).
      2:{ simpl_Forall. now rewrite H. }
      split; intros; repeat (take (_ \/ _) and destruct it; subst); auto with nlfree.
      take (Is_free_in_cexp _ _) and inv it; auto.
    - rewrite IHe, fold_left_spec2 with (In:=fun x o => exists e, o = Some e /\ Is_free_in_cexp (Last x) e), free_in_exp_spec2.
      2:{ simpl_Forall. destruct x0; simpl in *.
          - rewrite H. split; intros; repeat (take (_ \/ _) and destruct it; destruct_conjs); eauto.
            take (Some _ = Some _) and inv it. auto.
          - split; intros; repeat (take (_ \/ _) and destruct it; destruct_conjs); eauto.
            take (None = Some _) and inv it. }
      split; intros; repeat (take (_ \/ _) and destruct it; subst); auto with nlfree.
      take (Is_free_in_cexp _ _) and inv it; auto.
    - rewrite free_in_exp_spec2.
      split; intros; repeat (take (_ \/ _) and destruct it; subst); auto with nlfree.
      take (Is_free_in_cexp _ _) and inv it; auto.
  Qed.

  Lemma free_in_acexp_spec1:
    forall x ck e m, PS.In x (fst (free_in_acexp ck e m))
                <-> Is_free_in_acexp (Var x) ck e \/ PS.In x (fst m).
  Proof.
    intros. unfold free_in_acexp.
    rewrite free_in_cexp_spec1; simpl; rewrite free_in_clock_spec.
    split; [intros|intros [F|]; [inv F|]];
      repeat (take (_ \/ _) and destruct it); auto with nlfree.
  Qed.

  Lemma free_in_acexp_spec2:
    forall x ck e m, PS.In x (snd (free_in_acexp ck e m))
                <-> Is_free_in_acexp (Last x) ck e \/ PS.In x (snd m).
  Proof.
    intros. unfold free_in_acexp.
    rewrite free_in_cexp_spec2; simpl.
    split; [intros|intros [F|]; [inv F|]];
      repeat (take (_ \/ _) and destruct it); auto with nlfree.
  Qed.

  Lemma free_in_rhs_spec1:
    forall e x m, PS.In x (fst (free_in_rhs e m))
             <-> Is_free_in_rhs (Var x) e \/ PS.In x (fst m).
  Proof.
    intros [] *; simpl.
    - rewrite free_in_fold_left_exp_spec1.
      split; intros []; auto; left; auto using Is_free_in_rhs.
      now inv H.
    - rewrite free_in_cexp_spec1.
      split; intros []; auto; left; auto using Is_free_in_rhs.
      now inv H.
  Qed.

  Lemma free_in_arhs_spec1:
    forall x ck e m, PS.In x (fst (free_in_arhs ck e m))
                <-> Is_free_in_arhs (Var x) ck e \/ PS.In x (fst m).
  Proof.
    unfold free_in_arhs.
    intros *; simpl. rewrite free_in_rhs_spec1; simpl. rewrite free_in_clock_spec.
    split; intros; repeat (take (_ \/ _) and destruct it); auto with nlfree.
    inv H; auto.
  Qed.

  Lemma free_in_rhs_spec2:
    forall e x m, PS.In x (snd (free_in_rhs e m))
             <-> Is_free_in_rhs (Last x) e \/ PS.In x (snd m).
  Proof.
    intros [] *; simpl.
    - rewrite free_in_fold_left_exp_spec2.
      split; intros []; auto; left; auto using Is_free_in_rhs.
      now inv H.
    - rewrite free_in_cexp_spec2.
      split; intros []; auto; left; auto using Is_free_in_rhs.
      now inv H.
  Qed.

  Lemma free_in_arhs_spec2:
    forall x ck e m, PS.In x (snd (free_in_arhs ck e m))
                <-> Is_free_in_arhs (Last x) ck e \/ PS.In x (snd m).
  Proof.
    unfold free_in_arhs.
    intros *; simpl. rewrite free_in_rhs_spec2; simpl.
    split; intros; repeat (take (_ \/ _) and destruct it); auto with nlfree.
    inv H; auto.
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
