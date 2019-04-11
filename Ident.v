Require Import Velus.Common.
Require Import String.
Require Import Ascii.
Require Import List.
Import List.ListNotations.

Open Scope bool_scope.

Axiom pos_to_str: ident -> string.
Axiom pos_of_str: string -> ident.

Axiom pos_to_str_injective:
  forall x x',
    pos_to_str x = pos_to_str x' ->
    x = x'.
Axiom pos_of_str_injective:
  forall x x',
    pos_of_str x = pos_of_str x' ->
    x = x'.
Axiom pos_to_str_not_empty:
  forall x, pos_to_str x <> ("")%string.
Axiom pos_to_str_equiv:
  forall s, pos_to_str (pos_of_str s) = s.
Axiom pos_of_str_equiv:
  forall x, pos_of_str (pos_to_str x) = x.

Fixpoint In_str (x: ascii) (s: string): Prop :=
  match s with
  | EmptyString => False
  | String x' s => x' = x \/ In_str x s
  end.

Scheme Equality for ascii.
Fixpoint mem_str (x: ascii) (s: string): bool :=
  match s with
  | EmptyString => false
  | String x' s => (ascii_beq x' x || mem_str x s)%bool
  end.

Lemma mem_In_str:
  forall x s,
    In_str x s <-> mem_str x s = true.
Proof.
  induction s; simpl.
  - split; auto.
    intro; discriminate.
  - split; intro H.
    + rewrite Bool.orb_true_iff; destruct H.
      * left; now apply internal_ascii_dec_lb.
      * right; now apply IHs.
    + rewrite Bool.orb_true_iff in H; destruct H.
      * left; now apply internal_ascii_dec_bl.
      * right; now apply IHs.
Qed.

Lemma not_mem_In_str:
  forall x s,
    ~In_str x s <-> mem_str x s = false.
Proof.
  induction s; simpl.
  - split; auto.
  - split; intro H.
    + rewrite Bool.orb_false_iff; apply Decidable.not_or in H; destruct H; split.
      * apply Bool.not_true_is_false; intro E.
        apply internal_ascii_dec_bl in E.
        contradiction.
      * now apply IHs.
    + rewrite Bool.orb_false_iff in H; destruct H; intros [E|E].
      * apply Bool.not_true_iff_false in H; apply H.
        now apply internal_ascii_dec_lb.
      * now apply IHs.
Qed.

Lemma In_str_eq:
  forall x s,
    In_str x (String x s).
Proof.
  simpl; now left.
Qed.

Lemma In_str_app:
  forall x s1 s2,
    In_str x (s1 ++ s2)%string <-> In_str x s1 \/ In_str x s2.
Proof.
  induction s1; split; simpl; intro H.
  - now right.
  - destruct H; auto; contradiction.
  - destruct H.
    + now repeat left.
    + rewrite IHs1 in H; destruct H.
      * now left; right.
      * now repeat right.
  - rewrite IHs1; destruct H as [[|]|].
    + now left.
    + now right; left.
    + now repeat right.
Qed.

Lemma not_in_str_cons:
  forall x x' s,
    ~ In_str x (String x' s) <-> x <> x' /\ ~ In_str x s.
Proof.
  split; intro H.
  - simpl in H; split; intro E; apply H; auto.
  - simpl; intros [|]; destruct H; auto.
Qed.

Lemma append_assoc:
  forall s s' s'',
    (s ++ s' ++ s'' = (s ++ s') ++ s'')%string.
Proof.
  induction s; auto; intros; simpl.
  f_equal; auto.
Qed.

Definition sep: ascii := "$"%char.

Lemma append_sep_injectivity:
  forall x pre1 pre2 post1 post2,
    ~ In_str x pre1 ->
    ~ In_str x pre2 ->
    (pre1 ++ (String x post1) = pre2 ++ (String x post2))%string ->
    pre1 = pre2 /\ post1 = post2.
Proof.
  induction pre1; intros pre2 post1 post2 Hin1 Hin2 Heq.
  - assert (pre2 = ""%string).
    { destruct pre2; trivial; []. exfalso. simpl in Heq. inv Heq. apply Hin2. now left. }
    subst. simpl in Heq. inv Heq. now split.
  - destruct pre2.
    + exfalso. apply Hin1. inv Heq. now left.
    + simpl in Heq. inv Heq. rewrite not_in_str_cons in *.
      destruct (IHpre1 pre2 post1 post2); try tauto. subst. now split.
Qed.

Lemma append_eq_empty:
  forall s s', (s ++ s' = "" -> s = "" /\ s' = "")%string.
Proof.
  induction s; simpl; intros; auto.
  discriminate.
Qed.

Lemma append_same_last:
  forall pre1 post1 pre2 x,
    (pre1 ++ post1 = pre2 ++ String x "")%string ->
    (post1 <> "")%string ->
    exists post1',
      (post1 = post1' ++ String x "")%string.
Proof.
  induction pre1; simpl; intros ** E H; eauto.
  destruct pre2; simpl in *.
  - inv E; apply append_eq_empty in H2; destruct H2; contradiction.
  - inv E; eauto.
Qed.

Lemma append_string:
  forall s x s', (s ++ String x s' = (s ++ String x "") ++ s')%string.
Proof.
  induction s; simpl; auto; intros.
  now f_equal.
Qed.

Lemma append_injectivity_left:
  forall pre1 pre2 post,
    (pre1 ++ post = pre2 ++ post)%string ->
    pre1 = pre2.
Proof.
  induction pre1, pre2; simpl; intros ** E; auto.
  - exfalso.
    revert dependent pre2; revert a.
    induction post; intros; try discriminate.
    inversion E; subst a0.
    destruct pre2; simpl in *.
    + apply (IHpost a ""%string); now simpl.
    + rewrite append_string in H1; eauto.
  - exfalso.
    clear IHpre1.
    revert dependent pre1; revert a.
    induction post; intros; try discriminate.
    inversion E; subst a0.
    destruct pre1; simpl in *.
    + apply (IHpost a ""%string); now simpl.
    + rewrite append_string in H1; eauto.
  - inv E; f_equal; eauto.
Qed.

Module Export Ids <: IDS.
  Definition self := pos_of_str "self".
  Definition out := pos_of_str "out".
  Definition main_id: ident := pos_of_str "main".
  Definition fun_id: ident  := pos_of_str "fun".
  Definition sync_id: ident := pos_of_str "sync".
  Definition main_sync_id: ident := pos_of_str "main_sync".

  Definition step := pos_of_str "step".
  Definition reset := pos_of_str "reset".

  Definition reserved : idents := [ self; out ].

  Definition methods  : idents := [ step; reset ].

  (* The following identifier is (provably) never used in practice. *)
  Definition default : ident := pos_of_str "$$$$".

  Lemma reserved_nodup: NoDup reserved.
  Proof.
    constructor.
    - inversion_clear 1 as [E|Hin].
      + unfold out, self in E.
        apply pos_of_str_injective in E.
        discriminate.
      + contradict Hin.
    - repeat constructor; auto.
  Qed.

  Lemma methods_nodup: NoDup methods.
  Proof.
    constructor.
    - inversion_clear 1 as [E|Hin].
      + unfold reset, step in E.
        apply pos_of_str_injective in E.
        discriminate.
      + contradict Hin.
    - repeat constructor; auto.
  Qed.

  Lemma reset_not_step:
    reset <> step.
  Proof.
    pose proof methods_nodup as Hndup.
    unfold methods in Hndup.
    inversion_clear Hndup.
    intro Hrs. rewrite Hrs in *.
    intuition.
  Qed.

  Lemma fun_not_out: fun_id <> out.
  Proof.
    intro E; unfold fun_id, out in E.
    apply pos_of_str_injective in E.
    discriminate.
  Qed.

  Definition NotReserved {typ: Type} (xty: ident * typ) : Prop :=
    ~In (fst xty) reserved.

  Definition prefix (pre id: ident) :=
    pos_of_str (pos_to_str pre ++ (String sep (pos_to_str id))).

  Definition valid (x: ident) := ~In_str sep (pos_to_str x).

  Inductive prefixed: ident -> Prop :=
    prefixed_intro: forall pref id,
      prefixed (prefix pref id).

   Definition ValidId {typ: Type} (xty: ident * typ) : Prop :=
    NotReserved xty /\ valid (fst xty).

  Lemma In_sep_prefix:
    forall pre id,
      In_str sep (pos_to_str (prefix pre id)).
  Proof.
    intros.
    unfold prefix.
    rewrite pos_to_str_equiv, In_str_app; right.
    apply In_str_eq.
  Qed.

  Lemma valid_not_prefixed:
    forall x, valid x -> ~prefixed x.
  Proof.
    intros ** V H.
    inv H.
    apply V, In_sep_prefix.
  Qed.

  Definition prefix_fun (c f: ident): ident :=
    prefix fun_id (prefix c f).
  Definition prefix_out (o f: ident): ident :=
    prefix out (prefix o f).

  Lemma prefix_injective:
    forall pref id pref' id',
      valid pref ->
      valid pref' ->
      prefix pref id = prefix pref' id' ->
      pref = pref' /\ id = id'.
  Proof.
    unfold prefix.
    intros ** H.
    apply pos_of_str_injective in H.
    apply append_sep_injectivity in H; auto.
    destruct H as [E1 E2].
    apply pos_to_str_injective in E1;
      apply pos_to_str_injective in E2; auto.
  Qed.

  Remark fun_id_valid: valid fun_id.
  Proof.
    unfold fun_id, valid, sep.
    rewrite pos_to_str_equiv.
    intro.
    simpl in H.
    destruct H as [|[|[|]]]; discriminate || auto.
  Qed.

  Lemma prefix_fun_injective:
    forall c c' f f',
      valid c ->
      valid c' ->
      prefix_fun c f = prefix_fun c' f' ->
      c = c' /\ f = f'.
  Proof.
    unfold prefix_fun.
    intros ** Eq.
    pose proof fun_id_valid.
    apply prefix_injective in Eq; auto; destruct Eq as [E Eq]; clear E.
    now apply prefix_injective.
  Qed.

  Remark out_valid: valid out.
  Proof.
    unfold out, valid, sep.
    rewrite pos_to_str_equiv.
    intro.
    simpl in H.
    destruct H as [|[|[|]]]; discriminate || auto.
  Qed.

  Lemma prefix_out_injective:
    forall c c' f f',
      valid c ->
      valid c' ->
      prefix_out c f = prefix_out c' f' ->
      c = c' /\ f = f'.
  Proof.
    unfold prefix_out.
    intros ** Eq.
    pose proof out_valid.
    apply prefix_injective in Eq; auto; destruct Eq as [E Eq]; clear E.
    now apply prefix_injective.
  Qed.

  Inductive prefixed_fun: ident -> Prop :=
    prefixed_fun_intro: forall c f, prefixed_fun (prefix_fun c f).

  Lemma prefixed_fun_prefixed:
    forall x, prefixed_fun x -> prefixed x.
  Proof.
    inversion 1; unfold prefix_fun; constructor.
    (* apply fun_id_valid. *)
  Qed.

  Lemma prefix_fun_not_out:
    forall c f c' f', prefix_fun c f <> prefix_out c' f'.
  Proof.
    unfold prefix_fun, prefix_out.
    intros ** E.
    pose proof fun_id_valid; pose proof out_valid.
    apply prefix_injective in E; auto; destruct E as [E]; contradict E.
    apply fun_not_out.
  Qed.

  Definition glob_id (id: ident): ident :=
    pos_of_str ((pos_to_str id) ++ String sep EmptyString)%string.

  Lemma last_det:
    forall s s' a b,
      (s ++ String a EmptyString = s' ++ String b EmptyString)%string ->
      a = b.
  Proof.
    induction s, s'; simpl; intros.
    - inv H; auto.
    - inv H.
      destruct s'; simpl in *; discriminate.
    - inv H.
      destruct s; simpl in *; discriminate.
    - inv H.
      eapply IHs; eauto.
  Qed.

  Lemma main_not_glob:
    forall x, glob_id x <> main_id.
  Proof.
    unfold glob_id, main_id.
    intros * H.
    apply pos_of_str_injective in H.
    change "main"%string with ("mai" ++ "n")%string in H.
    apply last_det in H.
    inv H.
  Qed.

  Lemma sync_not_glob:
    forall x, glob_id x <> sync_id.
  Proof.
    unfold glob_id, sync_id.
    intros * H.
    apply pos_of_str_injective in H.
    change "sync"%string with ("syn" ++ "c")%string in H.
    apply last_det in H.
    inv H.
  Qed.

  Lemma main_sync_not_glob:
    forall x, glob_id x <> main_sync_id.
  Proof.
    unfold glob_id, main_sync_id.
    intros * H.
    apply pos_of_str_injective in H.
    change "main_sync"%string with ("main_syn" ++ "c")%string in H.
    apply last_det in H.
    inv H.
  Qed.

  Lemma self_not_glob:
    forall x, glob_id x <> self.
  Proof.
    unfold glob_id, self.
    intros * H.
    apply pos_of_str_injective in H.
    change "self"%string with ("sel" ++ "f")%string in H.
    apply last_det in H.
    inv H.
  Qed.

  Lemma glob_id_injective:
    forall x x',
      valid x ->
      valid x' ->
      glob_id x = glob_id x' ->
      x = x'.
  Proof.
    unfold glob_id.
    intros ** H.
    apply pos_of_str_injective in H.
    apply append_sep_injectivity in H; auto; destruct H.
    now apply pos_to_str_injective.
  Qed.

  Lemma glob_id_not_prefixed:
    forall x,
      valid x ->
      ~ prefixed (glob_id x).
  Proof.
    intros ** V H.
    inversion H as [? ? E].
    unfold prefix, glob_id in E.
    apply pos_of_str_injective in E.
    apply append_sep_injectivity in E; auto.
    - destruct E as [? E]; contradict E.
      apply pos_to_str_not_empty.
    - intro Hin.
      pose proof E as E'.
      apply append_same_last in E'.
      + destruct E' as [post E'].
        rewrite E', append_assoc in E.
        apply append_injectivity_left in E.
        apply V.
        rewrite <-E, In_str_app.
        now left.
      + intro; discriminate.
  Qed.

  Remark self_valid: valid self.
  Proof.
    unfold self, valid, sep.
    rewrite pos_to_str_equiv.
    intro.
    simpl in H.
    destruct H as [|[|[|[|]]]]; discriminate || auto.
  Qed.

  Lemma self_not_prefixed: ~ prefixed self.
  Proof.
    intro H.
    inversion H as [? ? E].
    unfold prefix, self in E.
    apply pos_of_str_injective in E.
    apply self_valid; unfold self; rewrite pos_to_str_equiv.
    rewrite <- E, In_str_app; right; apply In_str_eq.
  Qed.

  Lemma out_not_prefixed: ~ prefixed out.
  Proof.
    intro H.
    inversion H as [? ? E].
    unfold prefix, out in E.
    apply pos_of_str_injective in E.
    apply out_valid; unfold out; rewrite pos_to_str_equiv.
    rewrite <- E, In_str_app; right; apply In_str_eq.
  Qed.

  Remark sync_id_valid: valid sync_id.
  Proof.
    unfold sync_id, valid, sep.
    rewrite pos_to_str_equiv.
    intro.
    simpl in H.
    destruct H as [|[|[|[|]]]]; discriminate || auto.
  Qed.

  Lemma sync_not_prefixed: ~ prefixed sync_id.
  Proof.
    intro H.
    inversion H as [? ? E].
    unfold prefix, sync_id in E.
    apply pos_of_str_injective in E.
    apply sync_id_valid; unfold sync_id; rewrite pos_to_str_equiv.
    rewrite <- E, In_str_app; right; apply In_str_eq.
  Qed.

 End Ids.