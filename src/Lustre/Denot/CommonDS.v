From Coq Require Import Streams.
From Velus Require Import Common.
From Velus Require Import Lustre.Denot.Cpo.

(** * General facts about Denotational streams *)

(* lemme déjà présent dans Velus.CoindStreams mais on n'a pas envie
   d'instancier un module pour ça... *)
Lemma eq_EqSt:
  forall {A}, inclusion (Stream A) eq (@EqSt A).
Proof.
  intros ? xs xs' E.
  now rewrite E.
Qed.

(* remember with [Streams.EqSt] instead of [eq] *)
Tactic Notation "remember_st" constr(s) "as" ident(x) :=
  let Hx := fresh "H"x in
  remember s as x eqn:Hx;
  apply symmetry, eq_EqSt in Hx.

(* remember with [@Oeq (DS _)] instead of [eq] *)
Tactic Notation "remember_ds" uconstr(s) "as" ident(x) :=
  let Hx := fresh "H"x in
  remember s as x eqn:Hx;
  apply Oeq_refl_eq in Hx.

Ltac revert_all :=
  repeat match goal with
         | H:_ |- _ => revert H
         end.


(** ** Conversion to/from Coq Streams *)
Section Stream_DS.

  (** we can build a [Stream] from a [DS] if it is always productive,
      i.e. it is not bot at some point. *)

  Context {A B : Type}.
  Variable f : A -> B.

  Definition S_of_DS (s : DS A) : infinite s -> Stream B.
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
    rewrite unfold_Stream; simpl.
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
    setoid_rewrite unfold_Stream in Heq.
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

  Lemma S_of_DS_cons :
    forall u U Inf,
      S_of_DS (Cpo_streams_type.cons u U) Inf
        ≡ f u ⋅ (S_of_DS U (cons_infinite _ _ _ Inf)).
  Proof.
    intros.
    destruct Inf as [Hc Inf].
    constructor; simpl; destruct (uncons Hc) as (u' & U' & Hu);
      apply decompCon_eq in Hu; inv Hu; auto.
    apply _S_of_DS_eq.
    now rewrite rem_cons.
  Qed.

  Lemma const_DS_const :
    forall v Hi, const (f v) ≡ S_of_DS (DS_const v) Hi.
  Proof.
    intros.
    remember_st (const (f v)) as sl.
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


  (** The other way is simpler *)

  CoFixpoint DS_of_S (s : Stream A) : DS A :=
    match s with
    | Streams.Cons a s => CONS a (DS_of_S s)
    end.

  Global Add Parametric Morphism : DS_of_S
         with signature @EqSt A ==> @Oeq (DS A)
           as DS_of_S_morph.
  Proof.
    clear; intros.
    apply DS_bisimulation_allin1
      with (R := fun U V => exists x y, x ≡ y
                                /\ U == DS_of_S x
                                /\ V == DS_of_S y).
    3: eauto 5.
    { clear.
      intros * (x & y & Hxy & Hu & Hv) Eq1 Eq2.
      exists x,y. eauto. }
    clear.
    intros U V Hc ([] & [] & Hxy & Hu & Hv).
    rewrite DS_inv in Hu, Hv; simpl in *.
    setoid_rewrite Hu.
    setoid_rewrite Hv.
    inv Hxy; simpl in *; subst.
    rewrite 2 first_cons, 2 rem_cons.
    split; auto; eauto.
  Qed.

  Lemma DS_of_S_const :
    forall (c : A),
      DS_of_S (Streams.const c) == DS_const c.
  Proof.
    split; revert_all; cofix H; intros.
    - rewrite (unfold_Stream (Streams.const c)), (DS_inv (DS_of_S _)); simpl.
      rewrite DS_const_eq.
      econstructor; eauto using decompCon.
      eapply H; eauto.
    - rewrite (unfold_Stream (Streams.const c)), (DS_inv (DS_of_S _)); simpl.
      rewrite DS_const_eq.
      econstructor; eauto using decompCon.
      eapply H; eauto.
  Qed.

  Lemma DS_of_S_inf : forall s, infinite (DS_of_S s).
    cofix Cof.
    destruct s; constructor.
    - rewrite DS_inv; simpl; auto.
    - rewrite (DS_inv (DS_of_S (a ⋅ s))); simpl.
      rewrite rem_cons; apply Cof.
  Qed.

End Stream_DS.

Lemma DS_of_S_of_DS :
  forall A (s : DS A) H,
    DS_of_S (S_of_DS id s H) == s.
Proof.
  clear; intros.
  apply DS_bisimulation_allin1
    with (R := fun U V => exists H, U == DS_of_S (S_of_DS id V H)); eauto 2.
  { intros * [Inf Eq1] Eq2 Eq3.
    exists (proj1 (infinite_morph Eq3) Inf).
    rewrite <- Eq2, Eq1.
    apply DS_of_S_morph, _S_of_DS_eq, Eq3. }
  clear.
  intros U V Hc (Inf & Hu).
  apply infinite_decomp in Inf as HH.
  destruct HH as (v & V' & Hv & Inf').
  destruct (S_of_DS_eq id V Inf _ Hv) as [Inf2 Hsv].
  rewrite Hsv, S_of_DS_cons in Hu.
  setoid_rewrite Hu.
  rewrite (DS_inv (DS_of_S _)); simpl.
  split. { now rewrite Hv, 2 first_cons. }
  rewrite rem_cons.
  exists (rem_infinite _ _ Inf).
  apply DS_of_S_morph, _S_of_DS_eq.
  now rewrite Hv, rem_cons.
Qed.

(** ** Expressing safety properties *)
Section DS_Forall.

  Context {A : Type}.
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
      generalize dependent x.
      induction k; simpl; intros; subst.
      + inversion Hf; auto.
      + apply (IHk (pred x)); auto using DSForall_pred.
  Qed.

  Global Add Parametric Morphism : (DSForall)
         with signature (@Oeq (DS A)) ==> iff as DSForall_Oeq_mor.
  Proof.
    split; [|symmetry in H]; apply DSForall_Oeq; assumption.
  Qed.

  Lemma DSForall_le : forall x y, x <= y -> DSForall y -> DSForall x.
  Proof.
    cofix Cof; destruct x; intros ? Le Hf; constructor;
      inversion Le as [|???? HH]; eauto 2.
    all: apply decomp_eqCon in HH; rewrite HH in *; inv Hf; eauto 2.
  Qed.

  Lemma DSForall_bot : DSForall (DS_bot A).
  Proof.
    cofix Cof.
    rewrite DS_bot_eq.
    constructor; apply Cof.
  Qed.

  Lemma DSForall_const :
    forall c, P c -> DSForall (DS_const c).
  Proof.
    cofix Cof; intros.
    rewrite DS_inv; simpl.
    constructor; auto.
  Qed.

  Lemma DSForall_all :
    (forall x, P x) -> forall xs, DSForall xs.
  Proof.
    cofix Cof; intros; destruct xs; constructor; eauto.
  Qed.

  Lemma DSForall_eps : forall s, DSForall (Eps s) -> DSForall s.
    inversion 1; assumption.
  Defined.

  Lemma DSForall_rem : forall s, DSForall s -> DSForall (rem s).
  Proof.
    unfold rem, Rem, DSCase; simpl.
    cofix Cof; intros.
    destruct s; inv H; rewrite DScase_inv; auto.
    constructor; auto.
  Qed.

  Lemma DSForall_nrem : forall s n, DSForall s -> DSForall (nrem n s).
  Proof.
    induction n; intros; auto.
    rewrite nrem_S, nrem_rem.
    apply DSForall_rem; auto.
  Qed.

  (* unprovable induction principle *)
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
    generalize dependent f.
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

  (** More general admissibility *)
  Lemma DSForall_admissible2 :
    forall D (f : D -C-> DS A),
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

  Lemma DSForall_app :
    forall u v,
      DSForall u ->
      DSForall v ->
      DSForall (app u v).
  Proof.
    intros.
    remember_ds (app u v) as t.
    revert_all.
    cofix Cof; intros * Fu Fv t Ht.
    destruct t; constructor.
    - rewrite <- eqEps in *.
      now eapply Cof with (u := u) (v := v).
    - apply symmetry, app_cons_elim in Ht as (?& Hu &?).
      rewrite Hu in Fu; now inv Fu.
    - apply symmetry, app_cons_elim in Ht as (?& ? & Ht).
      now rewrite Ht.
  Qed.

  Lemma DSForall_take : forall n xs, DSForall xs -> DSForall (take n xs).
  Proof.
    induction n; intros * Hf; rewrite take_eq.
    apply DSForall_bot.
    apply DSForall_app; auto using DSForall_rem.
  Qed.

End DS_Forall.

Lemma DSForall_map :
  forall {A B} (f : A -> B) P s,
    DSForall (fun x => P (f x)) s -> DSForall P (MAP f s).
Proof.
  clear; intros.
  remember (MAP f s) as fs. apply Oeq_refl_eq in Heqfs.
  generalize dependent s. revert fs.
  cofix Cof; intros * H Hfs.
  destruct fs.
  - constructor.
      apply Cof with s; auto. now rewrite eqEps.
  - apply symmetry, map_eq_cons_elim in Hfs as (?&? & Hs &?&?); subst.
    rewrite Hs in *; inv H.
    constructor; auto.
    apply Cof with (rem s); rewrite Hs, rem_cons; auto.
Qed.

Lemma DSForall_impl :
  forall A (P Q : A -> Prop) (s : DS A),
    (forall x : A, P x -> Q x) ->
    DSForall P s ->
    DSForall Q s.
Proof.
  intros ???.
  cofix Cof.
  destruct s; intros Pq Hf; inv Hf; constructor; cases.
Qed.

Lemma DSForall_and :
  forall A (P Q : A -> Prop) (u : DS A),
    DSForall P u ->
    DSForall Q u ->
    DSForall (fun x => P x /\ Q x) u.
Proof.
  cofix Cof; intros * Hp Hq.
  destruct u; inv Hp; inv Hq; constructor; auto.
Qed.

Lemma DSForall_forall :
  forall {A T} (P : T -> A -> Prop) (s : DS A),
    (forall x, DSForall (P x) s)
    <-> DSForall (fun s => forall x, P x s) s.
Proof.
  split; revert s; cofix Cof; intros * Hf.
  - destruct s; constructor; eauto using DSForall_tl.
    + setoid_rewrite <- eqEps in Hf; eauto.
    + intro x. specialize (Hf x). now inv Hf.
  - destruct s; constructor; eauto using DSForall_tl.
    + setoid_rewrite <- eqEps in Hf; eauto.
    + inv Hf; auto.
Qed.

(** Admissibility with dependent predicate on elements of the stream *)
Lemma DSForall_admissible3 :
  forall (D:cpo) (A T : Type) (P : T -> A -> Prop) (f : T -> D -C-> DS A),
    @admissible D (fun s => forall x, DSForall (P x) (f x s)).
Proof.
  intros ?????? Hf ?.
  setoid_rewrite lub_comp_eq; auto.
  apply DSForall_admissible; intro.
  apply Hf.
Qed.

Lemma DSForall_zip :
  forall {A B C},
  forall (P : A -> Prop) (Q : B -> Prop) (R : C -> Prop),
  forall op xs ys,
    (forall x y, P x -> Q y -> R (op x y)) ->
    DSForall P xs ->
    DSForall Q ys ->
    DSForall R (ZIP op xs ys).
Proof.
  intros * PQ Hp Hq.
  remember (ZIP _ _ _) as t eqn:Ht. apply Oeq_refl_eq in Ht.
  revert Hp Hq Ht.
  revert xs ys t.
  cofix Cof; intros.
  destruct t.
  - constructor; rewrite <- eqEps in Ht; eauto.
  - apply symmetry, zip_uncons in Ht as (?&?&?&?& Hx & Hy & Ht &?).
    rewrite Hx, Hy in *; inv Hp; inv Hq.
    constructor; eauto.
Qed.

Lemma DSForall_zip3 :
  forall {A B C D},
  forall (P : A -> Prop) (Q : B -> Prop) (R : C -> Prop) (S : D -> Prop),
  forall op xs ys zs,
    (forall x y z, P x -> Q y -> R z -> S (op x y z)) ->
    DSForall P xs ->
    DSForall Q ys ->
    DSForall R zs ->
    DSForall S (ZIP3 op xs ys zs).
Proof.
  intros.
  rewrite zip3_eq.
  eapply DSForall_zip with (P := fun f => forall x, R x -> S (f x)); eauto.
  eapply DSForall_zip; eauto.
Qed.
