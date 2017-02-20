Require Import Velus.Common.
Require Import String.
Require Import Ascii.
Require Import List.
Import List.ListNotations.

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
  forall x, pos_to_str (pos_of_str x) = x.

Fixpoint In_str (x: ascii) (s: string): Prop :=
  match s with
  | EmptyString => False
  | String x' s => x' = x \/ In_str x s
  end.

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

Axiom pos_to_str_valid:
  forall x, ~ In_str "$" (pos_to_str x).

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

  Lemma fun_not_out: fun_id <> out.
  Proof.
    intro E; unfold fun_id, out in E.
    apply pos_of_str_injective in E.
    discriminate.    
  Qed.
  
  Definition NotReserved {typ: Type} (xty: ident * typ) : Prop :=
    ~In (fst xty) reserved.
End Ids.

Definition prefix (pre id: ident) :=
  pos_of_str (pos_to_str pre ++ (String "$" (pos_to_str id))).

Definition prefix_fun (c f: ident): ident :=
  prefix fun_id (prefix c f).
Definition prefix_out (o f: ident): ident :=
  prefix out (prefix o f).
  
Lemma prefix_injective:
  forall pref id pref' id',
    prefix pref id = prefix pref' id' ->
    pref = pref' /\ id = id'.
Proof.
  unfold prefix.
  intros ** H.
  apply pos_of_str_injective in H.
  apply append_sep_injectivity in H;
    try apply pos_to_str_valid.
  destruct H as [H1 H2].
  apply pos_to_str_injective in H1;
    apply pos_to_str_injective in H2; auto.
Qed.

Lemma prefix_fun_injective: 
 forall c c' f f',
   prefix_fun c f = prefix_fun c' f' -> c = c' /\ f = f'.
Proof.
  unfold prefix_fun.
  intros ** Eq.
  apply prefix_injective in Eq; destruct Eq as [E Eq]; clear E.
  now apply prefix_injective.
Qed.

Lemma prefix_out_injective: 
 forall c c' f f',
   prefix_out c f = prefix_out c' f' -> c = c' /\ f = f'.
Proof.
  unfold prefix_out.
  intros ** Eq.
  apply prefix_injective in Eq; destruct Eq as [E Eq]; clear E.
  now apply prefix_injective.
Qed.

Inductive prefixed: ident -> Prop :=
  prefixed_intro: forall pref id, prefixed (prefix pref id).

Inductive prefixed_fun: ident -> Prop :=
  prefixed_fun_intro: forall c f, prefixed_fun (prefix_fun c f).

Lemma prefixed_fun_prefixed:
  forall x, prefixed_fun x -> prefixed x.
Proof.
  inversion 1; unfold prefix_fun; constructor.
Qed.

Lemma prefix_fun_not_out:
  forall c f c' f', prefix_fun c f <> prefix_out c' f'.
Proof.
  unfold prefix_fun, prefix_out.
  intros ** E.
  apply prefix_injective in E; destruct E as [E]; contradict E.
  apply fun_not_out.  
Qed.

Definition glob_id (id: ident): ident :=
  pos_of_str ((pos_to_str id) ++ "$")%string.

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
    glob_id x = glob_id x' ->
    x = x'.
Proof.
  unfold glob_id.
  intros ** H.
  apply pos_of_str_injective in H.
  apply append_sep_injectivity in H; destruct H;
    try apply pos_to_str_valid.
  now apply pos_to_str_injective.
Qed.

Lemma glob_id_not_prefixed:
  forall x, ~ prefixed (glob_id x).
Proof.
  intros ** H.
  inversion H as [? ? E].
  unfold prefix, glob_id in E.
  apply pos_of_str_injective in E.
  apply append_sep_injectivity in E; try apply pos_to_str_valid; auto.
  destruct E as [? E]; contradict E.
  apply pos_to_str_not_empty. 
Qed.

Lemma self_not_prefixed: ~ prefixed self.
Proof.
  intro H.
  inversion H as [? ? E].
  unfold prefix, self in E.
  apply pos_of_str_injective in E.
  assert (In_str "$" "self") as Hin
      by (rewrite <- E, In_str_app; right; apply In_str_eq).
  destruct Hin as [|[|[|[|]]]]; try discriminate.
  contradiction.
Qed.

Lemma sync_not_prefixed: ~ prefixed sync_id.
Proof.
  intro H.
  inversion H as [? ? E].
  unfold prefix, sync_id in E.
  apply pos_of_str_injective in E.
  assert (In_str "$" "sync") as Hin
      by (rewrite <- E, In_str_app; right; apply In_str_eq).
  destruct Hin as [|[|[|[|]]]]; try discriminate.
  contradiction.
Qed.
  
