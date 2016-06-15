Require Import CommonSem.

Definition state := (menv * venv)%type.

(* =stmt_eval= *)
Inductive stmt_eval: state -> stmt -> state -> Prop :=
| Iassign: forall me ve x e v,
    exp_eval me ve e v ->
    stmt_eval (me, ve) (Assign x e) (me, PM.add x v ve)
| Iassignst: forall me ve x e v,
    exp_eval me ve e v ->
    stmt_eval (me, ve) (AssignSt x e) (madd_mem x v me, ve)
| Icomp: forall me1 ve1 s1 me2 ve2 s2 me3 ve3,
    stmt_eval (me1, ve1) s1 (me2, ve2) ->
    stmt_eval (me2, ve2) s2 (me3, ve3) ->
    stmt_eval (me1, ve1) (Comp s1 s2) (me3, ve3)
| Iskip_comp: forall me ve s me' ve',
    stmt_eval (me, ve) s (me', ve') ->
    stmt_eval (me, ve) (Comp Skip s) (me', ve')
| Iskip: forall st,
    stmt_eval st Skip st.


Inductive cont :=
| Kstop: cont
| Kseq: stmt -> cont -> cont.

(* =stmt_eval= *)
Inductive stmt_eval_cont: state * stmt * cont -> state * stmt * cont -> Prop :=
| Iassign_cont: forall me ve x e v ve' k,
    exp_eval me ve e v ->
    PM.add x v ve = ve' ->
    stmt_eval_cont ((me, ve), Assign x e, k) ((me, ve'), Skip, k)
| Iassignst_cont: forall me ve x e v me' k,
    exp_eval me ve e v ->
    madd_mem x v me = me' ->
    stmt_eval_cont ((me, ve), AssignSt x e, k) ((me', ve), Skip, k)
| Icomp_cont: forall st s1 s2 k,
    stmt_eval_cont (st, Comp s1 s2, k) (st, s1, Kseq s2 k)
| Iskip_comp_cont: forall st s k,
    stmt_eval_cont (st, Skip, Kseq s k) (st, s, k).

Section SEQUENCES.
  Set Implicit Arguments.

  Variable A: Type. 
  Variable R: A -> A -> Prop. 

  Inductive star: A -> A -> Prop :=
  | star_refl: forall a,
      star a a
  | star_step: forall a b c,
      R a b -> star b c -> star a c.

  Lemma star_one:
    forall (a b: A), R a b -> star a b.
  Proof.
    intros. econstructor; eauto. constructor.
  Qed.

  Lemma star_trans:
    forall (a b: A), star a b -> forall c, star b c -> star a c.
  Proof.
    induction 1; intros. auto. econstructor; eauto.
  Qed.

End SEQUENCES.

Definition terminates (S: state) (s: stmt) (S': state) : Prop :=
  star stmt_eval_cont (S, s, Kstop) (S', Skip, Kstop).

Hint Constructors stmt_eval_cont.

Theorem to_cont:
  forall S s S',
    stmt_eval S s S' ->
    forall k, star stmt_eval_cont (S, s, k) (S', Skip, k).
Proof.
  induction 1; intro.
  - apply star_one; eauto.
  - apply star_one; eauto.
  - eapply star_trans.
    + apply star_one; eauto.
    + eapply star_trans; eauto.
      eapply star_trans; eauto.
      apply star_one; eauto.
  - eapply star_trans.
    + apply star_one; eauto.
    + eapply star_trans; eauto.
      eapply star_one; eauto.
  - apply star_refl.
Qed.


Inductive keval: cont -> state -> state -> Prop :=
| KE_stop: forall S,
    keval Kstop S S
| KE_seq: forall s k S S' S'',
    stmt_eval S s S' ->
    keval k S' S'' ->
    keval (Kseq s k) S S''.

Inductive skeval: state * stmt * cont -> state -> Prop :=
  ske_intro: forall s k S S' S'',
      stmt_eval S s S' ->
      keval k S' S'' ->
      skeval (S, s, k) S''.

Require Import Coq.Program.Equality.

Hint Constructors stmt_eval.

Lemma stmt_eval_cont_skeval:
  forall S s k S' s' k',
    stmt_eval_cont (S, s, k) (S', s', k') ->
    forall S'',
      skeval (S', s', k') S'' ->
      skeval (S, s, k) S''.
Proof.
  intros until k'. intro STEP. dependent induction STEP; intros.
  - inv H0. inv H5. econstructor; eauto; auto.
  - inv H0. inv H5. econstructor; eauto; auto.
  - inv H. inv H5. econstructor; eauto. destruct S', S'1, S'0. econstructor; eauto.
  - inv H. econstructor; eauto. econstructor; eauto.
Qed.

Lemma stmt_eval_cont_skeval':
  forall S s k S' s' k' S'',
    star stmt_eval_cont (S, s, k) (S', s', k') ->
    skeval (S', s', k') S'' ->
    skeval (S, s, k) S''.
Proof.
  intros; dependent induction H; auto.
  destruct b as [[S1 s1] k1].
  eapply stmt_eval_cont_skeval; eauto.
Qed.

Hint Constructors keval.

Theorem from_cont:
  forall S s S',
  terminates S s S' -> stmt_eval S s S'.
Proof.
  unfold terminates; intros.
  assert (SKEV: skeval (S, s, Kstop) S').
  - eapply stmt_eval_cont_skeval'; eauto.
    econstructor; eauto. 
  - inv SKEV. inv H5; auto.
Qed.
