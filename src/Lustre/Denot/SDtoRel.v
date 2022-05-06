From Coq Require Import BinPos List.
From Cpo Require Import Cpo_def Cpo_streams_type Systems.

From Velus Require Import Common Ident Operators Clocks CoindStreams.
From Velus Require Import Lustre.StaticEnv Lustre.LSyntax Lustre.LOrdered Lustre.LSemantics Lustre.LTyping.

Close Scope equiv_scope. (* conflicting notation "==" *)

Require Import Cpo_ext.
Require Import SDfuns.
Require Import Denot.

(* TODO: déjà dans Vélus *)
Lemma eq_EqSt:
  forall {A}, inclusion (Stream A) eq (@EqSt A).
Proof.
  intros ? xs xs' E.
  now rewrite E.
Qed.

(* TODO: move *)
(* remember with [Streams.EqSt] instead of [eq] *)
Tactic Notation "remember_st" constr(s) "as" ident(x) :=
  let Hx := fresh "H"x in
  remember s as x eqn:Hx;
  apply symmetry, eq_EqSt in Hx.

(* TODO: move *)
Ltac revert_all :=
  repeat match goal with
         | H:_ |- _ => revert H
         end.

(* TODO: move *)
Section Stream_DS.

  (** we can build a [Stream] from a [DS] if it is always productive,
      i.e. it is not bot at some point. *)

  Context {A B : Type}.
  Variable f : A -> B.

  Definition S_of_DS (s : DS A) : infinite s -> Streams.Stream B.
    revert s.
    cofix Cof; intros * Hinf.
    inversion Hinf as [ Hc Hi ].
    specialize (Cof (rem s) Hi).
    apply uncons in Hc as [v].
    exact (Streams.Cons (f v) Cof).
  Defined.

  Lemma _S_of_DS_eq :
    forall (s : DS A) (Hs : infinite s)
      t (Ht : infinite t),
      s == t ->
      S_of_DS s Hs ≡ S_of_DS t Ht.
  Proof.
    cofix Cof; intros * Heq.
    destruct Hs as [Hcs Hs].
    destruct Ht as [Hct Ht].
    rewrite Streams.unfold_Stream; simpl.
    destruct (uncons Hct) as (?&? & Ht').
    constructor; simpl; destruct (uncons Hcs) as (?&?& Hs').
    - apply decomp_eqCon in Ht'.
      apply decomp_eqCon in Hs'.
      rewrite Ht', Hs' in Heq.
      now rewrite (Con_hd_simpl Heq).
    - apply Cof, rem_eq_compat, Heq.
  Qed.

  Lemma __S_of_DS_eq :
    forall (s : DS A) Hs t (Heq : s == t),
      S_of_DS s Hs ≡ S_of_DS t ((proj1 (infinite_morph Heq) Hs)).
  Proof.
    intros.
    now apply _S_of_DS_eq.
  Qed.

  Lemma S_of_DS_eq :
    forall (s : DS A) Hs t (Heq : s == t),
    exists Ht,
      S_of_DS s Hs ≡ S_of_DS t Ht.
  Proof.
    esplit.
    apply (__S_of_DS_eq _ Hs _ Heq).
  Qed.

  Lemma S_of_DS_Cons :
    forall xs xsi x t,
      S_of_DS xs xsi ≡ Streams.Cons x t ->
      exists x' xs',
        xs == cons x' xs'
        /\ f x' = x
        /\ exists H, S_of_DS xs' H ≡ t.
  Proof.
    intros * Heq.
    apply infinite_decomp in xsi as H.
    destruct H as (x' & xs' & Hxs & Hinf).
    destruct (S_of_DS_eq _ xsi _ Hxs) as [inf' Heq2].
    exists x', xs'. split; auto.
    rewrite Heq2 in Heq. clear - Heq.
    setoid_rewrite Streams.unfold_Stream in Heq.
    simpl in Heq.
    destruct inf', (uncons i) as (?&?& Hdec).
    apply decompCon_eq in Hdec.
    inversion Hdec. subst.
    inversion Heq as [? H]; simpl in *.
    edestruct (S_of_DS_eq _ inf') as [inf'' Heq3].
    { rewrite rem_cons. reflexivity. }
    rewrite Heq3 in H.
    split; eauto.
  Qed.

  Lemma const_DS_const :
    forall v Hi, Streams.const (f v) ≡ S_of_DS (DS_const v) Hi.
  Proof.
    intros.
    remember_st (Streams.const (f v)) as sl.
    remember_st (S_of_DS (DS_const v) Hi) as sr.
    revert_all.
    cofix Cof; intros.
    destruct sl, sr.
    apply S_of_DS_Cons in Hsr as (x & tx & Hxs & Hxvx & itx & Eqx).
    rewrite DS_const_eq in Hxs.
    apply Con_eq_simpl in Hxs as [? Heq].
    inversion Hsl; simpl in *.
    constructor; simpl; subst; auto.
    eapply Cof; eauto.
    now rewrite <- Eqx, (ex_proj2 (S_of_DS_eq _ _ _ (symmetry Heq))).
  Qed.

End Stream_DS.

(* TODO : move section, des trucs ont changé *)
(** ** Expressing safety properties *)
Section DS_Forall.

  Variable A : Type.
  Variable P : A -> Prop.

  CoInductive DSForall : DS A -> Prop :=
  | Forall_Eps : forall s, DSForall s -> DSForall (Eps s)
  | Forall_Con : forall x s, P x -> DSForall s -> DSForall (Con x s).

  Lemma DSForall_pred : forall s, DSForall s -> DSForall (pred s).
  Proof.
    intros s Hf.
    destruct s; simpl; inversion Hf; auto.
  Qed.

  Lemma DSForall_tl : forall x s, DSForall (Con x s) -> DSForall s.
  Proof.
    now inversion 1.
  Qed.

  Lemma DSForall_Con_hd : forall s x xs, DSForall s -> s == Con x xs -> P x.
  Proof.
    intros * Hf Heq.
    assert (isCon s) as Hcon by (rewrite Heq; auto).
    induction Hcon; inversion Hf; subst.
    - rewrite <- eqEps in Heq.
      apply IHHcon; auto.
    - apply Con_hd_simpl in Heq.
      now subst.
  Qed.

  Lemma DSForall_Oeq : forall x y, x == y -> DSForall x -> DSForall y.
  Proof.
    cofix Cof.
    intros x y Heq Hf.
    destruct y; constructor.
    - rewrite <- eqEps in Heq. exact (Cof _ _ Heq Hf).
    - exact (DSForall_Con_hd _ _ _ Hf Heq).
    - apply decomp_eq in Heq as (t & (k & Hp) & Ht).
      apply (Cof t); auto.
      clear - Hp Hf.
      revert dependent x.
      induction k; simpl; intros; subst.
      + inversion Hf; auto.
      + apply (IHk (pred x)); auto using DSForall_pred.
  Qed.

  Global Add Parametric Morphism : (DSForall)
         with signature (@Oeq (DS A)) ==> iff as DSForall_Oeq_mor.
  Proof.
    split; [|symmetry in H]; apply DSForall_Oeq; assumption.
  Qed.

  Lemma DSForall_bot : DSForall (DS_bot A).
  Proof.
    cofix Cof.
    rewrite DS_bot_eq.
    constructor; apply Cof.
  Qed.

  Lemma DSForall_eps : forall s, DSForall (Eps s) -> DSForall s.
    inversion 1; assumption.
  Defined.

  (* unprovable induction proinciple *)
  Lemma DSForall_ind :
    (forall s, DSForall (rem s) -> DSForall s) ->
    forall s, DSForall s.
  Abort.

  (* valid induction principle, though not very useful *)
  Lemma DSForall_ind :
    (forall s, DSForall (first s) -> DSForall (first (rem s))) ->
    forall s, DSForall (first s) -> DSForall s.
  Proof.
    intro Hfr.
    cofix Cof.
    intros s Hh.
    destruct s; constructor.
    - rewrite DS_inv in Hh. simpl in Hh.
      apply DSForall_eps in Hh.
      apply Cof, Hh.
    - rewrite DS_inv in Hh. simpl in Hh.
      now inversion Hh.
    - specialize (Hfr (Con a s) Hh).
      setoid_rewrite DS_inv in Hfr at 2. simpl in Hfr.
      rewrite <- DS_inv in Hfr.
      apply Cof, Hfr.
  Qed.

  (** Admissibility predicate needed by [fixp_ind]  *)
  Lemma DSForall_admissible : admissible DSForall.
  Proof.
    intros f Hf.
    simpl. unfold DS_lub. generalize 1 as m.
    revert dependent f.
    cofix Cof.
    intros.
    rewrite DS_lubn_inv.
    destruct (fCon f (S m)).
    - destruct s as (?&?&?&?& Hplus).
      constructor; auto.
      + specialize (Hplus O). rewrite plus_O_n in Hplus.
        specialize (Hf x1).
        rewrite Hplus in Hf.
        now inversion Hf.
      + apply Cof.
        intro n.
        specialize (Hplus n).
        specialize (Hf (n + x1)).
        rewrite Hplus in Hf.
        now inversion Hf.
    - constructor.
      apply Cof.
      intro n.
      specialize (Hf (n)).
      unfold cpred, pred. simpl.
      destruct (f n) eqn:Hfn.
      + setoid_rewrite Hfn. now inversion Hf.
      + now do 2 setoid_rewrite Hfn.
  Qed.

  (** More general admissibility  *)
  Lemma DSForall_admissible2 :
    forall B (f : DS B -C-> DS A),
      admissible (fun s => DSForall (f s)).
  Proof.
    intros ?? seq Hseq.
    setoid_rewrite lub_comp_eq; auto.
    now apply DSForall_admissible.
  Qed.

  (** Induction principle for simple streams defined with [FIXP] *)
  Lemma DSForall_FIXP :
    forall (F : DS A -C-> DS A),
      (forall s, DSForall s -> DSForall (F s)) ->
      DSForall (FIXP (DS A) F).
  Proof.
    intros.
    rewrite FIXP_fixp.
    apply fixp_ind; simpl; auto.
    apply DSForall_admissible.
    apply DSForall_bot.
  Qed.

End DS_Forall.


Module Type SDTOREL
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks   : CLOCKS        Ids Op OpAux)
       (Import Senv  : STATICENV     Ids Op OpAux Cks)
       (Import Syn   : LSYNTAX       Ids Op OpAux Cks Senv)
       (* (Import Typ   : LTYPING       Ids Op OpAux Cks Senv Syn) *)
       (Import Lord  : LORDERED      Ids Op OpAux Cks Senv Syn)
       (Import Str   : COINDSTREAMS  Ids Op OpAux Cks)
       (Import Sem   : LSEMANTICS Ids Op OpAux Cks Senv Syn Lord Str)
       (Import Den   : LDENOT     Ids Op OpAux Cks Senv Syn Lord Str).

(* vérification des prédicats sémantiques  *)
Section oks.

Definition sval_of_sampl : sampl value -> svalue :=
  fun v => match v with
        | pres v => present v
        | abs => absent
        | err e => absent
        end.
Definition S_of_DSv := S_of_DS sval_of_sampl.

Definition safe_val : sampl value -> Prop :=
  fun v => match v with
        | err _ => False
        | _ => True
        end.
Definition safe_DS : DS (sampl value) -> Prop := DSForall _ safe_val.

Lemma ok_fby1 :
  forall v (xs ys : DS (sampl value)),
    let rs := SDfuns.fby1 (Some v) xs ys in
    forall (xsi : infinite xs)
      (ysi : infinite ys)
      (rsi : infinite rs), (* obligé ? *)
      safe_DS xs ->
      safe_DS ys ->
      safe_DS rs ->
      fby1 v (S_of_DSv xs xsi) (S_of_DSv ys ysi) (S_of_DSv rs rsi).
Proof.
  intros.
  remember_st (S_of_DSv xs xsi) as xs'.
  remember_st (S_of_DSv ys ysi) as ys'.
  remember_st (S_of_DSv rs rsi) as rs'.
  revert_all.
  cofix Cof; intros * Sx Sy Sr ? Eqx ? Eqy ? Eqr.
  destruct xs' as [vx xs'], ys' as [vy ys'], rs' as [vr rs'].
  apply S_of_DS_Cons in Eqx as (x & tx & Hxs & Hxvx & itx & Eqx).
  apply S_of_DS_Cons in Eqy as (y & ty & Hys & Hyvy & ity & Eqy).
  apply S_of_DS_Cons in Eqr as (r & tr & Hrs & Hrvr & itr & Eqr).
  subst rs.
  rewrite Hxs, Hys, fby1_eq in Hrs.
  destruct x, y; simpl in *; subst.
  all: try apply Con_eq_simpl in Hrs as [? Heq]; subst; simpl.
  (* error cases *)
  all: rewrite Hxs, Hys in *.
  all: rewrite fby1_eq, ?fby1AP_eq in Sr, rsi.
  all: try (exfalso; inv Sx; inv Sy; assumption).
  all: apply DSForall_tl in Sx, Sy, Sr.
  2,3: rewrite DS_const_eq in Sr; inv Sr; now exfalso.
  all: constructor; rewrite fby1AP_eq in Heq.
  all: rewrite (ex_proj2 (S_of_DS_eq _ _ _ _ (symmetry Heq))) in Eqr; eauto.
Qed.

Lemma ok_fby :
  forall (xs ys : DS (sampl value)),
    let rs := SDfuns.fby xs ys in
    forall (xsi : infinite xs)
      (ysi : infinite ys)
      (rsi : infinite rs), (* obligé ?*)
      safe_DS xs ->
      safe_DS ys ->
      safe_DS rs ->
      fby (S_of_DSv xs xsi) (S_of_DSv ys ysi) (S_of_DSv rs rsi).
Proof.
  intros.
  remember_st (S_of_DSv xs xsi) as xs'.
  remember_st (S_of_DSv ys ysi) as ys'.
  remember_st (S_of_DSv rs rsi) as rs'.
  revert_all.
  cofix Cof; intros * Sx Sy Sr ? Eqx ? Eqy ? Eqr.
  destruct xs' as [vx xs'], ys' as [vy ys'], rs' as [vr rs'].
  apply S_of_DS_Cons in Eqx as (x & tx & Hxs & Hxvx & itx & Eqx).
  apply S_of_DS_Cons in Eqy as (y & ty & Hys & Hyvy & ity & Eqy).
  apply S_of_DS_Cons in Eqr as (r & tr & Hrs & Hrvr & itr & Eqr).
  subst rs.
  rewrite Hxs, Hys, fby_eq in Hrs.
  destruct x, y; simpl in *; subst.
  all: try apply Con_eq_simpl in Hrs as [? Heq]; subst; simpl.
  (* error cases *)
  all: rewrite Hxs, Hys in *.
  all: rewrite fby_eq, ?fbyA_eq, ?fby1AP_eq in Sr, rsi.
  all: try (exfalso; inv Sx; inv Sy; assumption).
  all: apply DSForall_tl in Sx, Sy, Sr.
  2,3: rewrite DS_const_eq in Sr; inv Sr; now exfalso.
  all: constructor; rewrite ?fbyA_eq, ?fby1AP_eq in Heq.
  all: rewrite (ex_proj2 (S_of_DS_eq _ _ _ _ (symmetry Heq))) in Eqr; eauto.
  rewrite <- Eqr, <- Eqx, <- Eqy.
  apply ok_fby1; auto.
Qed.

End oks.

End SDTOREL.
