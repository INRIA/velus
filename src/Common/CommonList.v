From Coq Require Import List.
From Coq Require Import Lists.SetoidList.
From Coq Require Import Permutation.
From Coq Require Import Decidable.
From Coq Require Import Relations.
From Coq Require Import Morphisms.
From Coq Require Import Classes.EquivDec.
From Coq Require Import Omega.

From Velus Require Import CommonTactics.

Import List.ListNotations.
Open Scope list_scope.

Section Extra.

  Context {A: Type}.

  Lemma List_shift_first:
    forall ll (x : A) lr,
      ll ++ (x :: lr) = (ll ++ [x]) ++ lr.
  Proof.
    induction ll as [|? ? IH]; [auto|intros].
    rewrite <- app_comm_cons.
    rewrite IH.
    now do 2 rewrite app_comm_cons.
  Qed.

  Lemma in_app:
    forall (x: A) (l1 l2: list A), In x (l1 ++ l2) <-> In x l1 \/ In x l2.
  Proof.
    intros. split; intro. apply in_app_or. auto. apply in_or_app. auto.
  Qed.

  Corollary in_app_weak :
    forall (x : A) l l',
      In x l -> In x (l ++ l').
  Proof.
    intros. apply in_app; auto.
  Qed.

  Lemma in_app_comm :
    forall (a : A) (l1 l2 : list A), In a (l1 ++ l2) <-> In a (l2 ++ l1).
  Proof.
    intros; split; intro Hin; apply in_app_or in Hin;
      apply in_or_app; tauto.
  Qed.

  Lemma app_last_app:
    forall xs xs' (x: A),
      (xs ++ [x]) ++ xs' = xs ++ x :: xs'.
  Proof.
    induction xs; simpl; auto.
    intros; f_equal; apply IHxs.
  Qed.

  Lemma cons_is_app:
    forall (x: A) xs,
      x :: xs = [x] ++ xs.
  Proof.
    destruct xs; simpl; auto.
  Qed.

  Remark Forall_hd:
    forall (A : Type) (P : A -> Prop) (x : A) (l : list A),
      Forall P (x :: l) -> P x.
  Proof.
    intros * HF. inv HF. auto.
  Qed.

  Remark Forall_tl:
    forall (A : Type) (P : A -> Prop) (x : A) (l : list A),
      Forall P (x :: l) -> Forall P l.
  Proof.
    intros * HF. inv HF. auto.
  Qed.

  Remark Forall_hd_tl:
    forall (A : Type) (P : A -> Prop) (x : A) (l : list A),
      Forall P (x :: l) -> P x /\ Forall P l.
  Proof.
    intros * HF. inv HF. auto.
  Qed.

  (* should be in standard lib... *)
  Lemma not_in_cons (x a : A) (l : list A):
    ~ In x (a :: l) <-> x <> a /\ ~ In x l.
  Proof.
    split.
    - intro Notin.
      split.
      + intro Eq.
        apply Notin.
        rewrite Eq.
        apply in_eq.
      + intro In.
        apply Notin.
        apply in_cons; auto.
    - intros [Neq Notin] In.
      apply in_inv in In.
      destruct In.
      + apply Neq; auto.
      + apply Notin; auto.
  Qed.

  Lemma fold_left_map:
    forall {B C} (l: list A) (f: C -> B -> C) (g: A -> B) a,
      fold_left f (map g l) a = fold_left (fun a x => f a (g x)) l a.
  Proof.
    induction l; simpl; auto.
  Qed.

  Lemma fold_left_map_fst:
    forall {B C} f xs (acc : C),
      fold_left (fun acc xy => f acc (fst xy)) xs acc
      = fold_left f (map (@fst A B) xs) acc.
  Proof.
    induction xs; auto.
    simpl. now setoid_rewrite IHxs.
  Qed.

  Remark not_In2_app:
    forall (x: A) l1 l2,
      ~ In x l2 ->
      In x (l1 ++ l2) ->
      In x l1.
  Proof.
    intros * HnIn Hin.
    induction l1.
    - contradiction.
    - rewrite <-app_comm_cons in Hin.
      inversion Hin; subst.
      + apply in_eq.
      + right; now apply IHl1.
  Qed.

  Lemma not_In_app:
    forall xs ys (x : A),
      ~In x (xs ++ ys) <-> (~In x xs /\ ~In x ys).
  Proof.
    setoid_rewrite in_app.
    split; [intro HH|intros (HH1 & HH2) [HH3|HH4]]; auto using Decidable.not_or.
  Qed.

  Lemma partition_switch:
    forall f g,
      (forall x:A, f x = g x) ->
      forall xs, partition f xs = partition g xs.
  Proof.
    intros * Hfg xs.
    induction xs as [|x xs]; auto. simpl.
    specialize (Hfg x). symmetry in Hfg. rewrite Hfg, IHxs.
    reflexivity.
  Qed.

  Lemma filter_app:
    forall (p:A->bool) xs ys,
      filter p xs ++ filter p ys = filter p (xs ++ ys).
  Proof.
    induction xs as [|x xs]; intro ys; auto.
    simpl; destruct (p x); simpl; rewrite IHxs; auto.
  Qed.

  Remark split_map:
    forall {B C} (xs: list C) (l: list A) (l': list B) f f',
      split (map (fun x => (f x, f' x)) xs) = (l, l') ->
      l = map f xs /\ l' = map f' xs.
  Proof.
    induction xs; simpl.
    - inversion_clear 3; auto.
    - intros ws ys f f' Split.
      destruct (split (map (fun x : C => (f x, f' x)) xs)) as (g, d) eqn: E.
      inv Split.
      edestruct IHxs as [G D]; eauto; rewrite <-G, <-D; auto.
  Qed.

  Remark In_singleton:
    forall (y x: A),
      In y [x] <-> y = x.
  Proof.
    split; intro H.
    - simpl in H; destruct H; auto.
      contradiction.
    - subst x; apply in_eq.
  Qed.

  Lemma In_weaken_cons:
    forall {A} (y x:A) xs,
      In x (y::xs) ->
      x <> y ->
      In x xs.
  Proof.
    intros * Hin Hnxy.
    inv Hin; congruence.
  Qed.

  Lemma in_filter:
    forall f x (l: list A), In x (filter f l) -> In x l.
  Proof.
    intros f x.
    induction l as [ | i l IHl ]; eauto.
    simpl; destruct (f i); eauto.
    intro H; inv H; auto.
  Qed.

  Lemma Forall_not_In_singleton:
    forall (x: A) ys,
      ~ In x ys ->
      Forall (fun y => ~ In y [x]) ys.
  Proof.
    induction ys; auto; simpl; intros; constructor; auto; intros [|]; auto.
  Qed.

  Global Add Parametric Morphism {A} : (@length A)
      with signature @Permutation.Permutation A ==> eq
        as length_permutation.
  Proof.
    intros. now apply Permutation.Permutation_length.
  Qed.

  Lemma split_last:
    forall {B} (x: A * B) xs,
      split (xs ++ [x]) =
      let (g, d) := split xs in
      (g ++ [fst x], d ++ [snd x]).
  Proof.
    destruct x as [a b].
    induction xs as [|(a', b')]; auto.
    simpl.
    destruct (split xs) as [g d].
    rewrite IHxs; auto.
  Qed.

  Lemma nth_seq:
    forall {A} n' n (xs: list A) x,
      n' < length xs - n ->
      nth n' (seq n (length xs - n)) x = n' + n.
  Proof.
    intros; rewrite seq_nth; try omega.
  Qed.

  Lemma seq_cons:
    forall k m,
      m < k ->
      seq m (k - m) = m :: seq (S m) (k - S m).
  Proof.
    induction k; intros * E; simpl.
    - omega.
    - destruct m; simpl.
      + now rewrite Nat.sub_0_r.
      + rewrite <- 2 seq_shift.
        rewrite IHk; auto.
        omega.
  Qed.

  Lemma length_hd_error:
    forall (l: list A),
      0 < length l ->
      exists x, hd_error l = Some x.
  Proof.
    induction l; simpl; intros * L; try omega.
    econstructor; eauto.
  Qed.

  Fact hd_error_Some_In:
    forall (xs: list A) x,
      hd_error xs = Some x ->
      In x xs.
  Proof.
    induction xs; simpl; try discriminate.
    inversion 1; auto.
  Qed.

  Fact hd_error_Some_hd:
    forall d (xs: list A) x,
      hd_error xs = Some x ->
      hd d xs = x.
  Proof.
    destruct xs; simpl; intros; try discriminate.
    now inv H.
  Qed.

  Lemma hd_error_In:
    forall xs (x : A),
      hd_error xs = Some x -> In x xs.
  Proof.
    intros * Hxs. destruct xs; inv Hxs. now constructor.
  Qed.

  Lemma split_map_fst {B} : forall (l : list (A * B)),
      fst (split l) = map fst l.
  Proof.
    intros l.
    induction l; simpl.
    - reflexivity.
    - destruct a; simpl.
      destruct (split l); simpl in *.
      f_equal. auto.
  Qed.

  Lemma split_map_snd {B} : forall (l : list (A * B)),
      snd (split l) = map snd l.
  Proof.
    intros l.
    induction l; simpl.
    - reflexivity.
    - destruct a; simpl.
      destruct (split l); simpl in *.
      f_equal. auto.
  Qed.

  Lemma map_ext_in' {B C} : forall (f : A -> C) (g : B -> C) l1 l2,
      length l1 = length l2 ->
      (forall a b, In (a, b) (combine l1 l2) -> f a = g b) ->
      map f l1 = map g l2.
  Proof.
    induction l1; intros l2 Hlen Hin;
      destruct l2; simpl in *; try congruence.
    inv Hlen.
    apply IHl1 in H0; auto.
    f_equal; auto.
  Qed.
End Extra.

Section find.

  Context {A: Type} (f: A -> bool).

  Lemma find_Exists:
    forall xs,
      find f xs <> None <-> Exists (fun x => f x = true) xs.
  Proof.
    induction xs as [|x xs IH].
    - rewrite Exists_nil. intuition.
    - destruct (f x) eqn:Hfx; simpl; rewrite Hfx.
      + split; intro HH; auto with datatypes. discriminate.
      + split; intro HH.
        now apply IH in HH; auto.
        apply IH. inversion_clear HH as [? ? Hfx'|]; auto.
        rewrite Hfx' in Hfx; inversion Hfx.
  Qed.

  Lemma find_split:
    forall xs x,
      find f xs = Some x ->
      exists bxs axs, xs = bxs ++ x :: axs.
  Proof.
    induction xs as [|x xs IH]. discriminate.
    simpl. destruct (f x).
    - inversion_clear 1. now exists nil, xs.
    - intros y Hf. apply IH in Hf.
      destruct Hf as (bxs & axs & Hf).
      rewrite Hf. now exists (x::bxs), axs.
  Qed.

  Lemma find_weak_spec:
    forall (xs: list A),
      find f xs = None ->
      Forall (fun x => f x = false) xs.
  Proof.
    induction xs as [|x xs IH]; simpl; auto.
    intro Hfind.
    destruct (f x) eqn:Hpx; try inv Hfind; auto.
  Qed.
End find.

Section split.
  Context {A B : Type}.

  Lemma split_fst_snd : forall (xs : list (A * B)),
      split xs = (map fst xs, map snd xs).
  Proof.
    induction xs; simpl; auto.
    destruct a. rewrite IHxs; auto.
  Qed.

  Corollary combine_fst_snd : forall (xs : list (A * B)),
      xs = combine (map fst xs) (map snd xs).
  Proof.
    intros xs.
    specialize (split_combine xs) as Hcomb.
    rewrite split_fst_snd in Hcomb; auto.
  Qed.
End split.

Section Map.

  Context {A B: Type}.
  Variable f: A -> B.

  Remark map_cons':
    forall l y ys,
      map f l = y :: ys ->
      exists x xs, l = x :: xs /\ y = f x /\ ys = map f xs.
  Proof.
    destruct l; simpl; intros * H.
    - contradict H. apply nil_cons.
    - exists a, l. inversion H; auto.
  Qed.

  Remark map_app':
    forall l1 l l2,
      map f l = l1 ++ l2 ->
      exists k1 k2, l = k1 ++ k2 /\ l1 = map f k1 /\ l2 = map f k2.
  Proof.
    induction l1; simpl; intros * H.
    - exists [], l; auto.
    - apply map_cons' in H.
      destruct H as (x & xs & Happ & Hl & Hr).
      symmetry in Hr. apply IHl1 in Hr.
      destruct Hr as (k1 & k2 & Hl1 & Hl2 & Hl3).
      exists (x :: k1), k2; simpl; repeat split; auto. congruence.
      f_equal; auto.
  Qed.

  Remark map_inj: forall xs ys,
      (forall x y, f x = f y -> x = y) ->
      map f xs = map f ys -> xs = ys.
  (* XXX: Is that not defined already?! *)
  Proof.
  intros ? ? Hinj ?.
  generalize dependent ys; generalize dependent xs.
  induction xs as [| x xs IHxs];
    intro ys; destruct ys as [ | y ys ]; try discriminate; simpl; auto.
  intro Heq; inv Heq.
  assert (x = y) by now apply Hinj.
  assert (xs = ys) by now apply IHxs.
  now congruence.
  Qed.

  Lemma map_nth':
    forall (l : list A) (d: B) (d' : A) (n : nat),
      n < length l ->
      nth n (List.map f l) d = f (nth n l d').
  Proof.
    induction l, n; simpl; intros * H; try omega; auto.
    apply IHl; omega.
  Qed.

End Map.

Section Incl.

  Context {A: Type}.

  Lemma incl_cons':
    forall (x: A) xs ys,
      incl (x :: xs) ys -> In x ys /\ incl xs ys.
  Proof.
    unfold incl; intuition.
  Qed.

  Lemma incl_tl': forall (x : A) xs ys,
      incl xs ys -> incl (x::xs) (x::ys).
  Proof.
    intros x xs ys Hincl.
    eapply incl_cons.
    + left; auto.
    + apply incl_tl; auto.
  Qed.

  Lemma incl_nil:
    forall (xs: list A),
      incl xs [] -> xs = [].
  Proof.
    intros xs H.
    induction xs; auto.
    unfold incl in H.
    specialize (H a (in_eq a xs)).
    contradict H.
  Qed.

  Lemma incl_nil': forall (xs : list A),
      incl [] xs.
  Proof. intros xs x Hin; inv Hin. Qed.

  Lemma Forall_incl:
    forall (l l': list A) P,
      Forall P l ->
      incl l' l ->
      Forall P l'.
  Proof.
    intros * H Incl.
    apply Forall_forall; intros * Hin.
    apply Incl in Hin.
    eapply Forall_forall in H; eauto.
  Qed.

  Lemma incl_map {B} : forall (l l' : list A) (f : A -> B),
      incl l l' -> incl (map f l) (map f l').
  Proof.
    intros l l' f Hincl.
    unfold incl in *.
    intros a Hin. rewrite in_map_iff in *.
    destruct Hin as [? [? Hin]]; subst.
    exists x. split; auto.
  Qed.

  Lemma incl_appl' : forall (l n m : list A),
      incl n m ->
      incl (n ++ l) (m ++ l).
  Proof.
    intros l n m Hincl.
    intros x Hin.
    rewrite in_app_iff in *.
    destruct Hin as [Hin|Hin]; auto.
  Qed.

  Lemma incl_appr' : forall (l n m : list A),
      incl n m ->
      incl (l ++ n) (l ++ m).
  Proof.
    intros l n m Hincl.
    intros x Hin.
    rewrite in_app_iff in *.
    destruct Hin as [Hin|Hin]; auto.
  Qed.

  Lemma incl_filter : forall (f : A -> bool) xs ys,
      incl xs ys ->
      incl (filter f xs) (filter f ys).
  Proof.
    induction xs; intros * Hincl.
    - simpl. apply incl_nil'.
    - apply incl_cons' in Hincl as [Hin Hincl].
      apply IHxs in Hincl. simpl.
      destruct (f a) eqn:Hf; auto.
      apply incl_cons; auto.
      apply filter_In; auto.
  Qed.

  Lemma incl_concat_map {B} : forall (f : A -> list B) x xs,
      In x xs ->
      incl (f x) (concat (map f xs)).
  Proof.
    induction xs; intros Hin; inv Hin; simpl.
    - apply incl_appl, incl_refl.
    - apply IHxs in H.
      apply incl_appr, H.
  Qed.

  Global Instance incl_refl : Reflexive (@incl A).
  Proof. unfold Reflexive. intros. apply incl_refl. Qed.

  Global Instance incl_trans : Transitive (@incl A).
  Proof. unfold Transitive. intros. eapply incl_tran; eauto. Qed.

End Incl.

Section Nodup.

  Context {A: Type}.

  Lemma NoDup_cons':
    forall (x:A) xs,
      NoDup (x::xs) <-> ~In x xs /\ NoDup xs.
  Proof.
    split; intro HH.
    - inversion_clear HH. intuition.
    - destruct HH. constructor; auto.
  Qed.

  Lemma NoDup_map_inv {B} (f: A -> B) l : NoDup (map f l) -> NoDup l.
  Proof.
    induction l; simpl; inversion_clear 1; subst; constructor; auto.
    intro H. now apply (in_map f) in H.
  Qed.

  Lemma NoDup_app_weaken:
    forall (xs: list A) ys,
      NoDup (xs ++ ys) ->
      NoDup xs.
  Proof.
    Hint Constructors NoDup.
    intros * Hndup.
    induction xs as [|x xs]; auto.
    inversion_clear Hndup as [|? ? Hnin Hndup'].
    apply IHxs in Hndup'.
    constructor; auto.
    intro Hin. apply Hnin.
    apply in_or_app; now left.
  Qed.

  Lemma NoDup_app_l : forall (xs : list A) ys,
      NoDup (xs ++ ys) ->
      NoDup xs.
  Proof. exact NoDup_app_weaken. Qed.

  Lemma NoDup_app_r : forall (xs : list A) ys,
      NoDup (xs ++ ys) ->
      NoDup ys.
  Proof.
    intros ws xs H.
    rewrite Permutation_app_comm in H.
    apply NoDup_app_l in H; auto.
  Qed.

  Lemma NoDup_app_cons:
    forall ws (x: A) xs,
      NoDup (ws ++ x :: xs)
      <-> ~In x (ws ++ xs) /\ NoDup (ws ++ xs).
  Proof.
    induction ws; simpl; split; intros * Nodup.
    - inv Nodup; auto.
    - destruct Nodup; auto.
    - inversion Nodup as [|? ? Notin Nodup']; clear Nodup; subst.
      split.
      + intro H; destruct H.
        * subst; apply Notin.
          apply in_app; right; apply in_eq.
        * apply NoDup_remove_2 in Nodup'.
          contradiction.
      + constructor.
        * intro Hin; apply Notin.
          apply in_app_or in Hin.
          destruct Hin; apply in_app; auto.
          right; now apply in_cons.
        * now apply NoDup_remove_1 in Nodup'.
    - destruct Nodup as [Notin Nodup].
      inversion Nodup as [|? ? Notin' Nodup']; clear Nodup; subst.
      constructor.
      + intro Hin.
        apply in_app_or in Hin.
        destruct Hin; apply Notin', in_app; auto.
        simpl in H; destruct H; auto.
        subst; contradict Notin; now left.
      + rewrite IHws; split; auto.
  Qed.

  Lemma NoDup_app_In:
    forall (x: A) xs ws,
      NoDup (xs ++ ws) ->
      In x xs ->
      ~In x ws.
  Proof.
    induction ws as [|w ws IH]; auto.
    intros Nodup Hin H.
    destruct H; subst.
    - apply NoDup_app_cons in Nodup.
      destruct Nodup as (Notin & ?).
      apply Notin. apply in_app. now left.
    - apply NoDup_remove_1 in Nodup.
      apply IH; auto.
  Qed.

  Lemma NoDup_app':
    forall (xs ws: list A),
      NoDup xs ->
      NoDup ws ->
      Forall (fun x => ~ In x ws) xs ->
      NoDup (xs ++ ws).
  Proof.
    induction xs as [|x]; auto.
    intros * Nodupxs Nodupws Hin.
    inv Hin; inv Nodupxs.
    rewrite <-app_comm_cons.
    constructor; auto.
    intro H.
    apply not_In_app in H; auto.
  Qed.

  Lemma NoDup_app'_iff:
    forall (xs ws: list A),
      NoDup (xs ++ ws) <->
       (NoDup xs
      /\ NoDup ws
      /\ Forall (fun x => ~ In x ws) xs).
  Proof.
  split.
  - induction xs; auto.
    rewrite <- app_comm_cons.
    intro H.
    inv H.
    destruct IHxs as [Hxs [Hws Hall]]; trivial; [].
    repeat split.
    + constructor; intuition.
    + assumption.
    + constructor; intuition.
  - intros H; decompose record H;
      now apply NoDup_app'.
  Qed.

  Lemma NoDup_swap:
    forall (x y z: list A),
      NoDup (x ++ y ++ z) <->
      NoDup (y ++ x ++ z).
  Proof.
    induction x; simpl; try reflexivity.
    split; intros * Nodup.
    - inversion_clear Nodup as [|?? Notin]; apply NoDup_app_cons; split.
      + intro Hin; apply Notin; rewrite 2 in_app.
        apply in_app in Hin as [?|Hin]; [|apply in_app in Hin as [|]]; auto.
      + now apply IHx.
    - apply NoDup_app_cons in Nodup as (Notin &?).
      constructor.
      + intro Hin; apply Notin; rewrite 2 in_app.
        apply in_app in Hin as [?|Hin]; [|apply in_app in Hin as [|]]; auto.
      + now apply IHx.
  Qed.

  Lemma nodup_filter:
    forall f (l: list A),
      NoDup l -> NoDup (filter f l).
  Proof.
    intro f. induction l as [ | x l IHl ]; simpl; auto.
    intro Hnodup. inversion_clear Hnodup as [ | ? ? Hnin_x Hnodup_l ].
    destruct (f x); auto.
    constructor; auto.
    intro; eapply Hnin_x, in_filter; eauto.
  Qed.

End Nodup.

Lemma concat_length:
  forall {A} (l: list (list A)),
    length (concat l) = fold_left (fun s x => s + length x) l 0.
Proof.
  induction l; simpl; auto.
  rewrite app_length.
  rewrite IHl.
  clear.
  replace (length a) with (length a + 0) at 2; try omega.
  generalize 0 as n; generalize (length a) as k.
  induction l; simpl; intros; auto.
  rewrite IHl, plus_assoc; auto.
Qed.

Section ConcatMap.

  Context {A B: Type}.

  Lemma flat_map_length:
    forall l (f : A -> list B),
      length (flat_map f l) = fold_left (fun s x => s + length (f x)) l 0.
  Proof.
    intros. rewrite flat_map_concat_map.
    rewrite concat_length, fold_left_map; auto.
  Qed.

  Lemma length_flat_map:
    forall (f: B -> list A) x xs,
      length (flat_map f (x :: xs)) = length (f x) + length (flat_map f xs).
  Proof.
    intros. setoid_rewrite flat_map_concat_map.
    simpl. now rewrite app_length.
  Qed.

  Lemma flat_map_app:
    forall (f : A -> list B) xs ys,
      flat_map f xs ++ flat_map f ys = flat_map f (xs ++ ys).
  Proof.
    induction xs; auto.
    simpl. intros; now rewrite <-app_assoc, IHxs.
  Qed.

  Lemma Permutation_cons_1:
    forall {A} (x : A) xs ys,
      Permutation (x::xs) ys
      <-> exists zs, Permutation xs zs /\ Permutation ys (x::zs).
  Proof.
    destruct xs as [|x' xs], ys as [|y' ys].
    - split; intro HH.
      + symmetry in HH; apply Permutation_nil in HH; discriminate.
      + destruct HH as (zs & Hzs & Hxzs).
        apply Permutation_nil in Hxzs; discriminate.
    - split; intro HH.
      + apply Permutation_length_1_inv in HH. inv HH; eauto.
      + destruct HH as (zs & Hzs & Hxzs).
        apply Permutation_nil in Hzs; subst.
        symmetry in Hxzs; apply Permutation_length_1_inv in Hxzs.
        now inv Hxzs.
    - split; intro HH.
      + symmetry in HH; apply Permutation_nil in HH; discriminate.
      + destruct HH as (zs & Hzs & Hxzs).
        apply Permutation_nil in Hxzs; discriminate.
    - split; intro HH.
      + setoid_rewrite <-HH. eauto.
      + destruct HH as (zs & Hzs & Hxzs).
        rewrite <-Hzs in Hxzs. clear Hzs.
        now rewrite <-Hxzs.
  Qed.

  Lemma flat_map_ExistsIn:
    forall (f : A -> list B) xs y ys,
      flat_map f xs = y :: ys ->
      exists x ys', In x xs /\ f x = y :: ys'.
  Proof.
    induction xs as [|x xs IH]; [now inversion 1|].
    simpl; intros * Hcm.
    destruct (f x) as [|x' ys'] eqn:Hfx; simpl in Hcm.
    - apply IH in Hcm.
      destruct Hcm as (x' & ys' & Hin & Hfx').
      repeat eexists; eauto.
    - exists x. exists ys'.
      split; auto with datatypes.
      rewrite Hfx. now inv Hcm.
  Qed.

  Lemma In_flat_map:
    forall (f : A -> list B) xss v,
      In v (flat_map f xss) ->
      exists xs,
        In xs xss /\ In v (f xs).
  Proof.
    induction xss as [|xs xss IH]. now inversion 1.
    simpl; intros v Hin.
    apply in_app in Hin.
    destruct Hin as [Hin|Hin].
    now eauto with datatypes.
    apply IH in Hin.
    destruct Hin as (xs' & Hin & Hinf).
    eauto with datatypes.
  Qed.

  Fact in_flat_map' : forall (f : A -> list B) (l : list A) (y : B),
      In y (flat_map f l) <-> Exists (fun x => In y (f x)) l.
  Proof.
    intros *.
    rewrite Exists_exists, in_flat_map.
    split; intros [x [? ?]]; exists x; auto.
  Qed.

  Remark in_concat_cons:
    forall l' (l: list A) x xs,
      In x l ->
      In (xs :: l) l' ->
      In x (concat l').
  Proof.
    induction l' as [|y]; simpl; intros * Hin Hin'.
    - contradiction.
    - destruct Hin' as [E|Hin'].
      + subst y.
        apply in_app; left; now apply in_cons.
      + apply in_app; right.
        eapply IHl'; eauto.
  Qed.

  Remark in_concat':
    forall l' (l: list A) x,
      In x l ->
      In l l' ->
      In x (concat l').
  Proof.
    induction l' as [|y]; simpl; intros * Hin Hin'.
    - contradiction.
    - destruct Hin' as [E|Hin'].
      + subst y.
        apply in_app; now left.
      + apply in_app; right.
        eapply IHl'; eauto.
  Qed.

  Lemma in_concat:
    forall (ls : list (list A)) (y : A),
      In y (concat ls) <-> (exists l : list A, In y l /\ In l ls).
  Proof.
  split.
  - induction ls as [|l ls]; [ firstorder | ].
    intro H. simpl in H. apply in_app in H.
    destruct H;
      [
      | edestruct IHls as (ys & ? & ?) ; auto ];
      firstorder.
  - intro H; decompose record H;
      eapply in_concat'; eauto.
  Qed.

  Lemma concat_Forall :
    forall (l' : list (list A)) (l : list A) (P : A -> Prop),
      Forall P (concat l') ->
      In l l' ->
      Forall P l.
  Proof.
    intros * Hp Hinl.
    apply Forall_forall. intros x Hinx.
    eapply Forall_forall; eauto.
    apply in_concat. eauto.
  Qed.

  Lemma Forall_concat : forall (l : list (list A)) P,
      Forall (fun l => Forall P l) l -> Forall P (concat l).
  Proof.
    intros l P Hf.
    rewrite Forall_forall in *.
    intros x Hin.
    apply in_concat in Hin.
    destruct Hin as [l' [Hin1 Hin2]].
    specialize (Hf _ Hin2).
    rewrite Forall_forall in Hf. auto.
  Qed.

  Lemma concat_length_1 : forall (f : A -> list B) (l : list A),
      Forall (fun x => length (f x) = 1) l ->
      length (concat (map f l)) = length l.
  Proof.
    induction l; intros Hf; simpl; auto.
    inv Hf.
    rewrite app_length.
    rewrite H1; simpl.
    f_equal; auto.
  Qed.

  Lemma concat_length_eq : forall (l1 : list (list A)) (l2 : list (list B)),
      Forall2 (fun l1 l2 => length l1 = length l2) l1 l2 ->
      length (concat l1) = length (concat l2).
  Proof.
    intros l1 l2 Hf.
    induction Hf; simpl.
    - reflexivity.
    - repeat rewrite app_length. f_equal; auto.
  Qed.

  Lemma concat_length_map_nth : forall (f : A -> list B) (l : list A) n da db,
      n < length l ->
      Forall (fun x => length (f x) = 1) l ->
      f (nth n l da) = [nth n (concat (map f l)) db].
  Proof.
    intros f l.
    induction l; intros n da db Hlen Hf; inv Hf; simpl.
    - simpl in Hlen. omega.
    - destruct n; auto.
      + destruct (f a); simpl in *; try congruence.
        destruct l0; simpl in *; try congruence.
      + destruct (f a); simpl in *; try congruence.
        destruct l0; simpl in *; try congruence.
        eapply IHl; eauto. omega.
  Qed.

  Fact concat_map_singl1 : forall (l : list A),
    (concat (map (fun x => [x]) l)) = l.
  Proof.
    induction l; simpl; auto.
    f_equal. assumption.
  Qed.

  Fact concat_map_singl2 : forall (l : list (list A)),
    (concat (concat (List.map (fun x => List.map (fun x => [x]) x) l))) = (concat l).
  Proof.
    induction l; simpl; auto.
    rewrite concat_app.
    rewrite IHl; clear IHl.
    f_equal. apply concat_map_singl1.
  Qed.

  Lemma concat_eq_nil : forall (l : list (list A)),
      concat l = [] <-> Forall (fun l => l = nil) l.
  Proof.
    intros l.
    split; intro H.
    - induction l; auto.
      simpl in *. apply app_eq_nil in H as [H1 H2].
      constructor; auto.
    - induction l; auto.
      simpl. inv H. auto.
  Qed.

End ConcatMap.

Section FoldLeft2.

  Context {A B C : Type}.

  Variable (f : A -> B -> C -> A).

  Fixpoint fold_left2 (xs : list B) (ys : list C) (a : A) : A :=
    match xs, ys with
    | x::xs', y::ys' => fold_left2 xs' ys' (f a x y)
    | _, _ => a
    end.


End FoldLeft2.

Section Permutation.

  Context {A: Type}.

  Lemma Permutation_incl1:
    forall (ws: list A) xs ys,
      Permutation xs ys ->
      (incl xs ws <-> incl ys ws).
  Proof.
    intros * Hperm.
    induction Hperm.
    - reflexivity.
    - split; intro HH.
      + apply incl_cons' in HH.
        destruct HH as [Hin Hincl].
        apply IHHperm in Hincl.
        apply incl_cons; auto.
      + apply incl_cons' in HH.
        destruct HH as [Hin Hincl].
        apply IHHperm in Hincl.
        apply incl_cons; auto.
    - split; intro HH.
      + apply incl_cons' in HH.
        destruct HH as (Hiny & HH).
        apply incl_cons' in HH.
        destruct HH as (Hinx & Hincl).
        repeat (apply incl_cons; auto).
      + apply incl_cons' in HH.
        destruct HH as (Hinx & HH).
        apply incl_cons' in HH.
        destruct HH as (Hiny & Hincl).
        repeat (apply incl_cons; auto).
    - now rewrite IHHperm1, IHHperm2.
  Qed.

  Global Instance Permutation_incl_Proper:
    Proper (@Permutation A ==> @Permutation A ==> iff) (@incl A).
  Proof.
    intros xs ys Hperm xs' ys' Hperm'.
    induction Hperm'; try rewrite (Permutation_incl1 _ _ _ Hperm).
    - reflexivity.
    - split; intro HH.
      + intros y Hin.
        apply HH in Hin.
        inversion_clear Hin as [|Hin'].
        now subst; constructor.
        rewrite Hperm' in Hin'.
        constructor 2; auto.
      + intros y Hin.
        apply HH in Hin.
        inversion_clear Hin as [|Hin'].
        now subst; constructor.
        rewrite <-Hperm' in Hin'.
        constructor 2; auto.
    - split; intro HH.
      + intros z Hin. apply HH in Hin. now rewrite perm_swap.
      + intros z Hin. apply HH in Hin. now rewrite perm_swap.
    - rewrite (Permutation_incl1 _ _ _ Hperm) in IHHperm'1.
      rewrite (Permutation_incl1 _ _ _ Hperm) in IHHperm'2.
      now rewrite IHHperm'1, IHHperm'2.
  Qed.

  Global Instance NoDup_Permutation_Proper:
    Proper (Permutation (A:=A) ==> iff) (@NoDup A).
  Proof.
    intros xs ys Hperm.
    induction Hperm.
    - now intuition.
    - rewrite 2 NoDup_cons', IHHperm, Hperm.
      reflexivity.
    - split; inversion_clear 1 as [|? ? Hnin Hndup];
        inversion_clear Hndup as [|? ? Hnin' Hndup'];
        (constructor; [|constructor]); auto; intro Hnin3;
          apply Hnin.
      + inversion Hnin3; [|contradiction].
        subst. now constructor.
      + now constructor 2.
      + inversion Hnin3; [|contradiction].
        subst. now constructor.
      + now constructor 2.
    - now rewrite IHHperm1, IHHperm2.
  Qed.

  Lemma Permutation_app_assoc:
    forall (ws: list A) xs ys,
      Permutation ((ws ++ xs) ++ ys) (ws ++ xs ++ ys).
  Proof.
    intros.
    induction ws.
    reflexivity.
    now apply Permutation_cons.
  Qed.

  Global Instance Permutation_app_Proper2 (xs: list A):
    Proper (Permutation (A:=A) ==> Permutation (A:=A))
           (app (A:=A) xs).
  Proof.
    intros ys ws Hperm.
    now apply Permutation_app_head.
  Qed.

  Global Instance Permutation_app_Proper3:
    Proper (Permutation (A:=A) ==> (@eq (list A)) ==> Permutation (A:=A))
           (app (A:=A)).
  Proof.
    intros xs ys Hperm ws1 ws2 Heq.
    rewrite Heq.
    rewrite (Permutation_app_comm xs), (Permutation_app_comm ys).
    now apply Permutation_app_head.
  Qed.

  Global Instance Permutation_concat_Proper:
    Proper (Permutation (A:=list A) ==> Permutation (A:=A))
           (@concat A).
  Proof.
  intros xs ys Hperm. induction Hperm.
  - reflexivity.
  - simpl. now rewrite IHHperm.
  - simpl. do 2 rewrite app_assoc. now rewrite (Permutation_app_comm x y).
  - now transitivity (concat l').
  Qed.

  Lemma Permutation_rev_append:
    forall {A} (xs zs : list A),
      Permutation (rev_append zs xs) (zs ++ xs).
  Proof.
    setoid_rewrite rev_append_rev.
    symmetry. apply Permutation_app_tail, Permutation_rev.
  Qed.

  Definition notb (f: A -> bool) (x: A) := negb (f x).

  Lemma filter_notb_app:
    forall (p: A -> bool) xs,
      Permutation (filter p xs ++ filter (notb p) xs) xs.
  Proof.
    induction xs as [|x xs]; auto.
    unfold notb, negb in *. simpl. destruct (p x); simpl.
    now rewrite IHxs.
    rewrite <-Permutation_middle. now rewrite IHxs.
  Qed.

  Global Instance Permutation_filter_Proper (p:A->bool):
    Proper (@Permutation A ==> @Permutation A) (filter p).
  Proof.
    Hint Constructors Permutation.
    intros xs ys Hperm.
    induction Hperm; simpl; auto.
    - destruct (p x); auto.
    - destruct (p x); destruct (p y); auto.
    - now rewrite IHHperm1, IHHperm2.
  Qed.

  Lemma permutation_partition:
    forall p (l: list A),
      Permutation l (fst (partition p l) ++ snd (partition p l)).
  Proof.
    induction l as [|x l].
    now constructor.
    simpl.
    destruct (p x).
    - rewrite (surjective_pairing (partition _ _)).
      now simpl; apply Permutation_cons.
    - rewrite (surjective_pairing (partition _ _)).
      now simpl; apply Permutation_cons_app.
  Qed.

  Lemma fst_partition_filter:
    forall P (xs: list A),
      Permutation (fst (partition P xs)) (filter P xs).
  Proof.
    induction xs as [|x xs]; auto.
    simpl; rewrite (surjective_pairing (partition P xs)).
    destruct (P x); auto.
    now apply Permutation_cons.
  Qed.

  Lemma snd_partition_filter:
    forall P (xs: list A),
      Permutation (snd (partition P xs)) (filter (fun x => negb (P x)) xs).
  Proof.
    induction xs as [|x xs]; auto.
    simpl; rewrite (surjective_pairing (partition P xs)).
    destruct (P x); auto.
    now apply Permutation_cons.
  Qed.

  Global Instance Permutation_map_Proper {B}:
    Proper ((@eq (A -> B)) ==> Permutation (A:=A) ==> (Permutation (A:=B)))
           (@map A B).
  Proof.
    intros f g Heq xs ys Hperm.
    subst. now rewrite Hperm.
  Qed.

  Lemma Permutation_swap:
    forall (xs ys zs: list A),
      Permutation (xs ++ ys ++ zs) (ys ++ xs ++ zs).
  Proof.
    induction xs; simpl; intros; auto.
    rewrite cons_is_app, <-app_last_app, 3 app_assoc.
    apply Permutation_app_tail.
    rewrite Permutation_app_comm, <-app_assoc; auto.
  Qed.

End Permutation.

Section Pointwise.

  Context {A: Type}.

  Global Instance pointwise_filter_Proper:
    Proper (pointwise_relation A eq ==> @eq (list A) ==> @eq (list A))
           (@filter A).
  Proof.
    intros f g Heq ys xs Hperm. subst.
    induction xs as [|x xs]; auto.
    simpl. now rewrite Heq, IHxs.
  Qed.

  Global Instance pointwise_partition_Proper:
    Proper (pointwise_relation A eq ==> @eq (list A) ==> @eq (list A * list A))
           (@partition A).
  Proof.
    intros f g Heq ys xs Hperm. subst.
    induction xs as [|x xs]; auto.
    simpl. now rewrite Heq, IHxs.
  Qed.

  Global Instance Forall_Permutation_Proper:
    Proper (pointwise_relation A iff ==> Permutation (A:=A) ==> iff) (@Forall A).
  Proof.
    intros P Q HPQ xs ys Hperm.
    assert (forall ws, Forall P ws <-> Forall Q ws) as Hsame
        by (induction ws as [|w ws]; split; inversion_clear 1;
          auto; constructor; try (rewrite HPQ || rewrite <-HPQ); intuition).
    induction Hperm.
    - split; auto.
    - split; inversion_clear 1.
      + constructor; try rewrite <-HPQ; intuition.
      + constructor; try rewrite HPQ; intuition.
    - split; intro;
        repeat match goal with H:Forall _ (_::_) |- _ => inversion_clear H end;

        repeat constructor; try (rewrite HPQ || rewrite <-HPQ); auto;
          now apply Hsame.
    - now rewrite IHHperm1, <-IHHperm2, Hsame.
  Qed.

  Global Instance Exists_Permutation_Proper:
    Proper (pointwise_relation A iff ==> Permutation (A:=A) ==> iff) (@Exists A).
  Proof.
    intros P Q HPQ xs ys Hperm.
  assert (forall ws, Exists P ws <-> Exists Q ws) as Hsame.
    - induction ws as [|w ws]; split; inversion_clear 1.
      + constructor; now rewrite <-HPQ.
      + constructor 2; intuition.
      + constructor; now rewrite HPQ.
      + constructor 2; intuition.
    - induction Hperm.
      + now setoid_rewrite Exists_nil.
      + setoid_rewrite Exists_cons.
        now rewrite IHHperm, HPQ.
      + repeat setoid_rewrite Exists_cons.
        rewrite Hsame, HPQ. intuition.
      + now rewrite IHHperm1, <-Hsame, IHHperm2.
  Qed.

  Global Instance Permutation_map_Proper2 {A B}:
    Proper (pointwise_relation A eq ==> Permutation.Permutation (A:=A)
                               ==> (Permutation.Permutation (A:=B)))
           (@map A B).
  Proof.
    intros f g Heq xs ys Hperm. induction Hperm; auto.
    - simpl. now rewrite Heq, IHHperm.
    - simpl. rewrite perm_swap.
      simpl. repeat rewrite Heq.
      repeat apply perm_skip.
      induction l; auto. simpl. now rewrite Heq, IHl.
    - now rewrite IHHperm1, Hperm2.
  Qed.

  Global Instance Permutation_flat_map_Proper :
    forall A B f,
      Proper (Permutation (A:=A) ==> Permutation (A:=B))
             (flat_map (A:=A) (B:=B) f).
  Proof.
    intros * l l' Perm. now rewrite 2 flat_map_concat_map, Perm.
  Qed.

End Pointwise.

Section ForallExists.

  Context {A: Type}.

  Lemma Forall_map:
    forall {B} P (f: A -> B) xs,
      Forall P (map f xs) <-> Forall (fun x => P (f x)) xs.
  Proof.
    intros.
    induction xs; split; simpl; inversion 1; intuition.
  Qed.

  Variable P: A -> Prop.

  Lemma Forall_cons2:
    forall x l,
      Forall P (x :: l) <-> P x /\ Forall P l.
  Proof. intros; split; inversion_clear 1; auto. Qed.

  Lemma Forall_app:
    forall ll rr,
      Forall P (ll ++ rr) <-> (Forall P ll /\ Forall P rr).
  Proof.
    intros.
    induction ll as [|x ll IH]; [intuition|].
    rewrite Forall_cons2.
    rewrite and_assoc.
    rewrite <-IH.
    rewrite <-List.app_comm_cons.
    now rewrite Forall_cons2.
  Qed.

  Lemma Exists_app:
    forall ll rr,
      Exists P rr ->
      Exists P (ll ++ rr).
  Proof.
    intros * Hex.
    induction ll as [|x ll IH]; [intuition|].
    rewrite <-List.app_comm_cons.
    constructor 2.
    exact IH.
  Qed.

  Lemma Exists_app':
    forall (l l': list A),
      Exists P (l ++ l') <-> Exists P l \/ Exists P l'.
  Proof.
    split.
    - induction l; simpl; auto.
      inversion_clear 1 as [|?? E]; intuition.
    - intros [E|E].
      + induction l; simpl; inv E; auto.
      + induction l; simpl; auto.
  Qed.

  Lemma Forall_Forall:
    forall Q xs,
      Forall P xs -> Forall Q xs -> Forall (fun x=>P x /\ Q x) xs.
  Proof.
    induction xs as [|x xs IH]; [now constructor|].
    intros HPs HQs.
    inversion_clear HPs as [|? ? HP HPs'].
    inversion_clear HQs as [|? ? HQ HQs'].
    intuition.
  Qed.

  Lemma Forall_Exists:
    forall Q xs,
      Forall P xs ->
      Exists Q xs ->
      Exists (fun x=>P x /\ Q x) xs.
  Proof.
    induction xs as [|x xs IH]; [now inversion 2|].
    intros Ha He.
    inversion_clear Ha.
    inversion_clear He; auto.
  Qed.

  Lemma decidable_Exists:
    forall xs,
      (forall x, In x xs -> decidable (P x)) ->
      decidable (Exists P xs).
  Proof.
    intros * Hdec.
    induction xs as [|x xs].
    - right. now intro HH; apply Exists_nil in HH.
    - destruct (Hdec x) as [Hx|Hx].
      + now constructor.
      + destruct IHxs as [Hxs|Hxs];
          try (now left; constructor).
        intros y Hin.
        apply Hdec. now constructor 2.
      + destruct IHxs as [Hxs|Hxs].
        * intros y Hin.
          apply Hdec. now constructor 2.
        * left. now constructor 2.
        * right. intro HH.
          apply Exists_cons in HH.
          intuition.
  Qed.

  Lemma decidable_Exists_not_Forall:
    forall xs,
      (forall x, In x xs -> decidable (P x)) ->
      (Exists P xs <-> ~Forall (fun x => ~(P x)) xs).
  Proof.
    induction xs as [|x xs]; intro Hdec.
    - split; intro HH.
      + now apply Exists_nil in HH.
      + apply Exists_nil. now apply HH.
    - split; intro HH.
      + inversion_clear 1 as [|? ? HnP Hfa].
        inversion_clear HH as [|? ? Hex]; auto.
        apply IHxs in Hex; auto.
        intros y Hin. apply Hdec. intuition.
      + destruct (Hdec x) as [Hx|Hx]; auto. now intuition.
        right. apply IHxs; intuition.
  Qed.

  Lemma Exists_map:
    forall {B} P (f : A -> B) xs,
      Exists P (map f xs) <-> Exists (fun x => P (f x)) xs.
  Proof.
    induction xs as [|x xs IH]; simpl; split; intro HH; inv HH; auto;
      now constructor 2; apply IH.
  Qed.

  Lemma Exists_Exists:
    forall (Q : A -> Prop) xs,
    (forall x, P x -> Q x) ->
    Exists P xs -> Exists Q xs.
  Proof.
    intros * Himpl Hex.
    rewrite Exists_exists in *. destruct Hex as [? [Hin HP]].
    exists x; auto.
  Qed.

  Lemma Permutation_Forall:
    forall l l',
      Permutation l l' ->
      Forall P l ->
      Forall P l'.
  Proof.
    induction 1; inversion 1; auto.
    match goal with H:Forall _ (_ :: _) |- _ => inversion H end.
    repeat constructor; auto.
  Qed.

  Lemma Forall_app_weaken:
    forall xs ys,
      Forall P (xs ++ ys) ->
      Forall P ys.
  Proof.
    intros * HH. apply Forall_app in HH. intuition.
  Qed.

  Lemma Forall_impl_In :
    forall (Q : A -> Prop) l,
      (forall a, In a l -> P a -> Q a) ->
      Forall P l -> Forall Q l.
  Proof.
    induction l; auto.
    intros H HP.
    inversion_clear HP.
    auto using in_eq, in_cons.
  Qed.

  Lemma Forall_Forall':
    forall (Q : A -> Prop) (xs : list A),
      Forall P xs /\ Forall Q xs <-> Forall (fun x : A => P x /\ Q x) xs.
  Proof.
    split.
    - intros [? ?]; now apply Forall_Forall.
    - intro HForall.
      induction xs as [|x xs]; split; auto; inv HForall; constructor; tauto.
  Qed.

  Lemma Forall_singl:
    forall (x : A),
      Forall P [x] -> P x.
  Proof.
    intros * Hf. inversion Hf; auto.
  Qed.

  Lemma Forall_not_In_app:
    forall (zs xs ys: list A),
      Forall (fun z => ~ In z xs) zs ->
      Forall (fun z => ~ In z ys) zs ->
      Forall (fun z => ~ In z (xs ++ ys)) zs.
  Proof.
    induction zs; auto; intros * Hxs Hys; inv Hxs; inv Hys.
    constructor; auto.
    intro H; apply not_In_app in H; auto.
  Qed.

  Lemma Exists_concat : forall xs,
      Exists P (concat xs) <-> Exists (Exists P) xs.
  Proof.
    intros xs. split; intro H.
    - rewrite Exists_exists in *.
      destruct H as [x [Hin H]].
      rewrite in_concat in Hin. destruct Hin as [l [Hin1 Hin2]].
      exists l. split; auto.
      rewrite Exists_exists. exists x; auto.
    - rewrite Exists_exists in *.
      destruct H as [l [Hin1 H]].
      rewrite Exists_exists in H. destruct H as [x [Hin2 H]].
      exists x. split; auto. rewrite in_concat. exists l; auto.
  Qed.

  Lemma Exists_concat_nth : forall xs n d,
      n < length xs ->
      Exists P (nth n xs d) -> Exists P (concat xs).
  Proof.
    intros xs n d Hlen Hex.
    apply nth_In with (d:=d) in Hlen.
    rewrite Exists_concat.
    rewrite Exists_exists.
    exists (nth n xs d); auto.
  Qed.

  Lemma Exists_concat_nth' : forall xs d,
      Exists P (concat xs) ->
      exists n, (n < length xs /\ Exists P (nth n xs d)).
  Proof.
    intros xs d Hex.
    rewrite Exists_concat in Hex.
    rewrite Exists_exists in Hex. destruct Hex as [x [Hin Hex]].
    apply In_nth with (d:=d) in Hin. destruct Hin as [n [Hlen Hnth]]; subst.
    exists n. auto.
  Qed.

  Lemma Exists_combine_l {B} : forall xs (ys : list B),
      length xs = length ys ->
      Exists P xs <-> Exists (fun '(x, _) => P x) (combine xs ys).
  Proof.
    induction xs; intros ys Hlen;
      destruct ys; simpl in *; try congruence.
    - split; intros H; inv H.
    - inv Hlen.
      apply IHxs in H0.
      split; intros H.
      + inv H; auto.
        right. rewrite <- H0. assumption.
      + inv H; auto.
        right. rewrite H0. assumption.
  Qed.

  Lemma Exists_combine_r {B} : forall xs (ys : list B),
      length xs = length ys ->
      Exists P xs <-> Exists (fun '(_, x) => P x) (combine ys xs).
  Proof.
    induction xs; intros ys Hlen;
      destruct ys; simpl in *; try congruence.
    - split; intros H; inv H.
    - inv Hlen.
      apply IHxs in H0.
      split; intros H.
      + inv H; auto.
        right. rewrite <- H0. assumption.
      + inv H; auto.
        right. rewrite H0. assumption.
  Qed.

  Lemma Exists_singl : forall (x : A),
      Exists P [x] ->
      P x.
  Proof.
    intros x Hex.
    inv Hex; auto. inv H0.
  Qed.

End ForallExists.

Lemma Forall_iff_insideout:
  forall {A} (P Q : A -> Prop) xs,
    (Forall (fun x => P x <-> Q x) xs) ->
    (Forall P xs <-> Forall Q xs).
Proof.
  induction xs. now intuition.
  intro FA. apply Forall_hd_tl in FA as (FA1 & FA2).
  split; inversion 1; subst; intuition.
Qed.

Section ForallExistsB.

  Context {A: Type}.
  Variable p: A -> bool.

  Lemma Exists_existsb:
    forall xs P,
      (forall x, P x <-> p x = true) ->
      (Exists P xs <-> existsb p xs = true).
  Proof.
    intros * Spec.
    induction xs as [|x xs IH]; simpl.
    - split; inversion 1.
    - rewrite Bool.orb_true_iff, <-IH, <-Spec; split.
      + inversion 1; auto.
      + intros [E|E].
        * left; auto.
        * right; auto.
  Qed.

  Lemma forallb_exists:
    forall (l: list A),
      forallb p l = false <-> (exists x : A, In x l /\ p x = false).
  Proof.
    induction l as [|a]; simpl; split; intro H; try discriminate.
    - destruct H as (? & ? & ?); contradiction.
    - apply Bool.andb_false_iff in H as [H|H].
      + exists a; intuition.
      + apply IHl in H as (x & ? & ?).
        exists x; intuition.
    - destruct H as (? & [] & ?).
      + subst; apply Bool.andb_false_intro1; auto.
      + apply Bool.andb_false_intro2, IHl.
        exists x; intuition.
  Qed.

  Lemma existsb_Forall:
    forall xs,
      existsb p xs = false <->
      forallb (fun x => negb (p x)) xs = true.
  Proof.
    induction xs; simpl. now intuition.
    now rewrite Bool.orb_false_iff, IHxs,
    Bool.andb_true_iff, Bool.negb_true_iff.
  Qed.

  Lemma existsb_Forall_neg:
    forall xs,
      existsb (fun x => negb (p x)) xs = false <->
      forallb p xs = true.
  Proof.
    induction xs; simpl. now intuition.
    now rewrite Bool.orb_false_iff, IHxs,
    Bool.andb_true_iff, Bool.negb_false_iff.
  Qed.

  Lemma forallb_Forall:
    forall xs,
      forallb p xs = true <-> Forall (fun x => p x = true) xs.
  Proof.
    induction xs. now split; auto using Forall_nil.
    simpl. now rewrite Bool.andb_true_iff, IHxs, Forall_cons2.
  Qed.

End ForallExistsB.

(* Induction on a pair of lists of the same length *)
Section list_ind2.
  Context {A B : Type}.
  Variable P : list A -> list B -> Prop.

  Hypothesis Hnil : P nil nil.
  Hypothesis Hcons : forall a l1 b l2,
      P l1 l2 -> P (a::l1) (b::l2).

  Fixpoint list_ind2 l1 l2 : length l1 = length l2 -> P l1 l2.
  Proof.
    destruct l1; destruct l2; intro Hlen; simpl in Hlen; try congruence.
    - apply Hcons. apply list_ind2.
      inv Hlen. reflexivity.
  Qed.
End list_ind2.

Section Combine.

  Context {A B C: Type}.

  Lemma combine_map_fst:
    forall (f: A -> B) xs (ys: list C),
      combine (map f xs) ys = map (fun x=>(f (fst x), snd x)) (combine xs ys).
  Proof.
    induction xs; try constructor.
    destruct ys; try constructor.
    simpl. now rewrite IHxs.
  Qed.

  Lemma combine_map_fst':
    forall (xs : list A) (ys : list B),
      length xs = length ys -> map fst (combine xs ys) = xs.
  Proof.
    intros xs ys Hlen.
    refine (list_ind2 (fun xs ys => _) _ _ xs ys Hlen); simpl.
    - reflexivity.
    - intros a l1 b l2 IHl. f_equal; auto.
  Qed.

  Lemma combine_map_snd:
    forall (f: C -> B) (xs: list A) ys,
      combine xs (map f ys) = map (fun x=>(fst x, f (snd x))) (combine xs ys).
  Proof.
    induction xs; try constructor.
    destruct ys; try constructor.
    simpl. now rewrite IHxs.
  Qed.

  Lemma combine_map_snd':
    forall (xs : list A) (ys : list B),
      length xs = length ys -> map snd (combine xs ys) = ys.
  Proof.
    intros xs ys Hlen.
    refine (list_ind2 (fun xs ys => _) _ _ xs ys Hlen); simpl.
    - reflexivity.
    - intros a l1 b l2 IHl. f_equal; auto.
  Qed.

  Lemma combine_same : forall (xs : list A),
      combine xs xs = map (fun x => (x, x)) xs.
  Proof.
    induction xs; simpl; f_equal; auto.
  Qed.

  Lemma combine_nil_l:
    forall (xs: list B),
      combine (@nil A) xs = [].
  Proof.
    destruct xs; auto.
  Qed.

  Lemma combine_nil_r:
    forall (xs: list A),
      combine xs (@nil B) = [].
  Proof.
    destruct xs; auto.
  Qed.

  Lemma combine_app_l:
    forall (xs xs': list A) (ys: list B),
      combine (xs ++ xs') ys = combine xs (firstn (length xs) ys)
                                       ++ combine xs' (skipn (length xs) ys).
  Proof.
    induction xs as [|x xs IH]; auto.
    intros xs' ys.
    destruct ys; simpl; try rewrite combine_nil_r; auto.
    now simpl; rewrite IH.
  Qed.

  Lemma combine_app_r:
    forall (xs: list A) (ys ys': list B),
      combine xs (ys ++ ys') = combine (firstn (length ys) xs) ys
                                       ++ combine (skipn (length ys) xs) ys'.
  Proof.
    intros xs ys; revert ys xs.
    induction ys as [|y ys IH]; auto.
    intros xs ys'.
    destruct xs; auto.
    now simpl; rewrite IH.
  Qed.

  Lemma NotIn_combine:
    forall (xs: list A) (ys: list B) x y,
      ~In x xs ->
      ~In (x, y) (combine xs ys).
  Proof.
    induction xs as [|x xs IH]. now auto.
    destruct ys as [|y ys]. now auto.
    simpl.
    intros x' y' Hni HH.
    apply Decidable.not_or in Hni.
    destruct Hni as (Hni1 & Hni2).
    destruct HH as [HH|HH].
    apply Hni1; now inv HH.
    apply IH in HH; auto.
  Qed.

  Lemma In_combine_f:
    forall (f1 : A -> B) (f2 : A -> C) xs x1 x2,
      In (x1, x2) (combine (map f1 xs) (map f2 xs)) ->
      exists x,
        In x xs /\ x1 = f1 x /\ x2 = f2 x.
  Proof.
    induction xs. now inversion 1.
    intros x1 x2 Hin.
    inversion_clear Hin.
    - inv H. eauto using in_eq.
    - apply IHxs in H. destruct H as (x & Hin & H1 & H2); subst.
      eauto using in_cons.
  Qed.

  Lemma map_snd_combine:
    forall (l: list A) (l': list B),
      length l = length l' ->
      map (@snd A B) (combine l l') = l'.
  Proof.
    induction l, l'; inversion 1; auto.
    simpl. now rewrite (IHl _ H1).
  Qed.

  Lemma combine_length_l:
    forall (l : list A) (l' : list B),
      length (combine l l') = length l ->
      length l <= length l'.
  Proof.
    intros l l' Hlen.
    rewrite combine_length in Hlen.
    rewrite Nat.min_l_iff in Hlen. omega.
  Qed.

  Lemma combine_length_r:
    forall (l : list A) (l' : list B),
      length (combine l l') = length l' ->
      length l >= length l'.
  Proof.
    intros l l' Hlen.
    rewrite combine_length in Hlen.
    rewrite Nat.min_r_iff in Hlen. omega.
  Qed.

  Lemma combine_nth_l:
    forall (l : list A) (l': list B) n d1 d2,
      length l <= length l' ->
      exists d, nth n (combine l l') (d1, d2) = (nth n l d1, d).
  Proof.
    induction l, l'; intros n d1 d2 Hlen; simpl in *.
    + exists d2. destruct n; auto.
    + exists d2. destruct n; auto.
    + omega.
    + destruct n.
      * exists b; auto.
      * apply IHl. omega.
  Qed.

  Lemma combine_nth_r:
    forall (l : list A) (l': list B) n d1 d2,
      length l >= length l' ->
      exists d, nth n (combine l l') (d1, d2) = (d, nth n l' d2).
  Proof.
    induction l, l'; intros n d1 d2 Hlen; simpl in *.
    + exists d1. destruct n; auto.
    + omega.
    + exists d1. destruct n; auto.
    + destruct n.
      * exists a; auto.
      * apply IHl. omega.
  Qed.

  Lemma in_combine_nodup :
    forall {A B} xs ys (x : A) (y : B) y',
      NoDup xs ->
      In (x, y) (combine xs ys) ->
      In (x, y') (combine xs ys) ->
      y = y'.
  Proof.
    induction xs. inversion 2. intros * Hdup Hin Hin'.
    destruct ys. inv Hin. inv Hin; inv Hin'; try congruence.
    - inv H. inv Hdup. now take (In _ _) and apply in_combine_l in it.
    - inv H0. inv Hdup. now take (In _ _) and apply in_combine_l in it.
    - inv Hdup. eauto.
  Qed.

End Combine.

Lemma In_combine_f_left:
  forall {A B} (f1 : A -> B) xs x x1,
    In (x1, x) (combine (map f1 xs) xs) ->
    In x xs /\ x1 = f1 x.
Proof.
  intros A B f1 xs x x1 Hin.
  rewrite <-map_id with (l:=xs) in Hin at 2.
  apply In_combine_f in Hin.
  destruct Hin as (x' & Hin & H1 & H2); subst; auto.
Qed.

Lemma In_combine_f_right:
  forall {A B} (f2 : A -> B) xs x x2,
    In (x, x2) (combine xs (map f2 xs)) ->
    In x xs /\ x2 = f2 x.
Proof.
  intros A B f1 xs x x2 Hin.
  rewrite <-map_id with (l:=xs) in Hin at 1.
  apply In_combine_f in Hin.
  destruct Hin as (x' & Hin & H1 & H2); subst; auto.
Qed.

Lemma combine_map_both:
  forall {A B C D} (f: A -> B) (g: C -> D) xs ys,
    combine (map f xs) (map g ys)
    = map (fun x => (f (fst x), g (snd x))) (combine xs ys).
Proof.
  intros; rewrite combine_map_fst, combine_map_snd, map_map; auto.
Qed.

Section SkipnDropn.

  Context {A : Type}.

  Lemma skipn_app:
    forall (xs: list A) ys n,
      n = length xs ->
      skipn n (xs ++ ys) = ys.
  Proof.
    induction xs as [|x xs IH]; intros * Hn; subst; simpl; auto.
  Qed.

  Lemma skipn_nil:
    forall n,
      skipn n (@nil A) = @nil A.
  Proof.
    induction n; auto.
  Qed.

  Lemma firstn_nil:
    forall n,
      firstn n (@nil A) = @nil A.
  Proof.
    induction n; auto.
  Qed.

  Lemma firstn_app:
    forall (xs: list A) ys n,
      n = length xs ->
      firstn n (xs ++ ys) = xs.
  Proof.
    induction xs; intros ys n Hn; subst; auto.
    simpl; rewrite IHxs; auto.
  Qed.

  Lemma In_skipn:
    forall (xs: list A) n x,
      In x (skipn n xs) ->
      In x xs.
  Proof.
    induction xs; try setoid_rewrite skipn_nil.
    now inversion 1.
    intros * Hin.
    destruct n; auto.
    apply IHxs in Hin.
    auto with datatypes.
  Qed.

  Lemma In_firstn:
    forall (xs: list A) n x,
      In x (firstn n xs) ->
      In x xs.
  Proof.
    induction xs; try setoid_rewrite firstn_nil.
    now inversion 1.
    intros * Hin.
    destruct n; inversion Hin; subst; eauto with datatypes.
  Qed.

  Lemma Forall_skipn:
    forall P (xs: list A) n,
      Forall P xs ->
      Forall P (skipn n xs).
  Proof.
    induction xs as [|x xs IH].
    setoid_rewrite skipn_nil; auto.
    intros n Hfa.
    induction n; auto.
    inversion_clear Hfa.
    now apply IH.
  Qed.

  Lemma skipn_cons:
    forall n (xs: list A) x,
      n > 0 ->
      skipn n (x :: xs) = skipn(n - 1) xs.
  Proof.
    induction n; simpl; intros * H.
    - omega.
    - now rewrite Nat.sub_0_r.
  Qed.

  Lemma skipn_length:
    forall n (l: list A),
      length (skipn n l) = length l - n.
  Proof.
    induction n; intros; simpl.
    - omega.
    - destruct l; simpl; auto.
  Qed.

  Lemma nth_skipn:
    forall (xs: list A) n' n x_d,
      nth n' (skipn n xs) x_d = nth (n' + n) xs x_d.
  Proof.
    induction xs; intros; simpl.
    - rewrite skipn_nil; simpl; destruct (n' + n); destruct n'; auto.
    - destruct n; simpl.
      + now rewrite <-plus_n_O.
      + destruct n'; simpl; rewrite IHxs; auto.
        now rewrite Plus.plus_Snm_nSm.
  Qed.

  Lemma nth_firstn_1: forall (xs: list A) n' n x_d,
      n' < n ->
      nth n' (firstn n xs) x_d = nth n' xs x_d.
  Proof.
    induction xs; intros; simpl.
    - destruct n'; destruct n; auto.
    - destruct n'; destruct n; auto; try omega.
      simpl. apply IHxs. omega.
  Qed.

End SkipnDropn.

Section AppLength.
  Context {A B : Type}.

  Lemma app_length_impl :
    forall (l1 l'1 : list A) (l2 l'2 : list B),
      length l'1 = length l'2 ->
      length (l'1 ++ l1) = length (l'2 ++ l2) ->
      length l1 = length l2.
  Proof.
    intros * Hl Hlapp.
    rewrite 2 app_length in Hlapp.
    omega.
  Qed.

  Lemma length_app :
    forall (l : list A) (l1 l2 : list B),
      (length l = length (l1 ++ l2)) ->
      (exists l1' l2', l = l1' ++ l2'
                  /\ length l1' = length l1
                  /\ length l2' = length l2).
  Proof.
    intros.
    rewrite app_length in H.
    exists (firstn (length l1) l),(skipn (length l1) l). split; [|split].
    - symmetry. apply firstn_skipn.
    - rewrite firstn_length. apply Min.min_l. omega.
    - apply app_length_impl with (l'1 := firstn (length l1) l) (l'2 := l1).
      rewrite firstn_length. apply Min.min_l. omega.
      rewrite firstn_skipn. now rewrite app_length.
  Qed.

  Lemma app_length_inv1 :
    forall (l1 l1' l2 l2' : list A),
      l1 ++ l2 = l1' ++ l2' ->
      length l1 = length l1' ->
      l1 = l1'.
  Proof.
    intros * Happ Hlen.
    apply f_equal with (f := firstn (length l1)) in Happ.
    rewrite Hlen in Happ at 2.
    do 2 rewrite firstn_app in Happ; auto.
  Qed.

  Lemma app_length_inv2:
    forall (l1 l1' l2 l2' : list A),
      l1 ++ l2 = l1' ++ l2' ->
      length l1 = length l1' ->
      l2 = l2'.
  Proof.
    intros * Happ Hlen.
    apply f_equal with (f := skipn (length l1)) in Happ.
    rewrite Hlen, skipn_app, skipn_app in Happ; auto.
  Qed.
End AppLength.

Section Forall2.

  Context {A B C : Type}.

  Open Scope bool_scope.

  Fixpoint forall2b (f : A -> B -> bool) l1 l2 :=
    match l1, l2 with
    | nil, nil => true
    | e1 :: l1, e2 :: l2 => f e1 e2 && forall2b f l1 l2
    | _, _ => false
    end.

  Lemma forall2b_Forall2:
    forall (p : A -> B -> bool) (xs : list A) (ys : list B),
      forall2b p xs ys = true <-> Forall2 (fun x y => p x y = true) xs ys.
  Proof.
    split; intros * FA.
    - revert xs ys FA. induction xs, ys; simpl in *; auto; try discriminate.
      rewrite Bool.andb_true_iff. intros (FA1 & FA2).
      apply IHxs in FA2. auto.
    - induction FA; auto. simpl; apply Bool.andb_true_iff; auto.
  Qed.

  Lemma Forall2_forall2_eq:
    forall (eq_A: A -> A -> Prop) (eq_B: B -> B -> Prop)
      (eq_A_refl: reflexive A eq_A)
      (eq_B_refl: reflexive B eq_B)
      (P: A -> B -> Prop)
      (P_compat: Proper (eq_A ==> eq_B ==> Basics.impl) P)
      (l1: list A) (l2: list B),
      Forall2 P l1 l2
      <-> length l1 = length l2
        /\ forall a b n x1 x2,
          n < length l1 ->
          eq_A (nth n l1 a) x1 ->
          eq_B (nth n l2 b) x2 ->
          P x1 x2.
  Proof.
    intros. revert l2; induction l1; intro.
    - split; intro H.
      + inv H. split; simpl; auto.
        intros; omega.
      + destruct H as [H _]. destruct l2; try discriminate; auto.
    - split; intro H.
      + inversion_clear H as [|? ? ? ? ? H'].
        rewrite IHl1 in H'; destruct H' as (? & IH).
        split; simpl; auto.
        intros; destruct n.
        * eapply P_compat; eauto.
        * eapply IH; eauto; omega.
      + destruct H as [Hlen H].
        destruct l2; simpl in Hlen; try discriminate.
        constructor.
        * apply (H a b 0); simpl; auto; try omega.
        * rewrite IHl1; split; try omega.
          intros a' b' **; eapply (H a' b' (S n)); simpl; eauto; omega.
  Qed.

  Lemma Forall2_forall2 :
    forall P l1 l2,
      Forall2 P l1 l2
      <-> length l1 = length l2
          /\ forall (a : A) (b : B) n x1 x2,
          n < length l1 ->
          nth n l1 a = x1 ->
          nth n l2 b = x2 ->
          P x1 x2.
  Proof.
    intros P l1. induction l1; intro l2.
    * split; intro H.
    + inversion_clear H. split; simpl; auto. intros. omega.
    + destruct H as [H _]. destruct l2; try discriminate. constructor.
      * split; intro H.
    + inversion_clear H. rewrite IHl1 in H1. destruct H1. split; simpl; auto.
      intros. destruct n; subst; trivial. eapply H1; eauto. omega.
    + destruct H as [Hlen H].
      destruct l2; simpl in Hlen; try discriminate. constructor.
      apply (H a b 0); trivial; simpl; try omega.
      rewrite IHl1. split; try omega.
      intros. eapply (H a0 b0 (S n)); simpl; eauto. simpl; omega.
  Qed.

  Lemma Forall2_ignore2:
    forall {A B} (P : A -> B -> Prop) xs ys,
      Forall2 P xs ys ->
      Forall (fun x => exists y, In y ys /\ P x y) xs.
  Proof.
    induction 1; auto.
    constructor; eauto with datatypes.
    apply Forall_impl_In with (2:=IHForall2).
    intros a Ia (b & Ib & Pb). eauto with datatypes.
  Qed.

  Lemma Forall2_ignore2': forall (P : A -> Prop) xs (ys : list B),
      length xs = length ys ->
      Forall P xs ->
      Forall2 (fun x _ => P x) xs ys.
  Proof.
    induction xs; intros * Hlen Hf; inv Hf;
      destruct ys; simpl in *; try congruence;
        constructor; auto.
  Qed.

  Lemma Forall2_ignore1:
    forall {A B} (P : A -> B -> Prop) xs ys,
      Forall2 P xs ys ->
      Forall (fun y => exists x, In x xs /\ P x y) ys.
  Proof.
    induction 1; auto.
    constructor; eauto with datatypes.
    apply Forall_impl_In with (2:=IHForall2).
    intros a Ia (b & Ib & Pb). eauto with datatypes.
  Qed.

  Lemma Forall2_ignore1': forall (P : B -> Prop) (xs : list A) ys,
      length ys = length xs ->
      Forall P ys ->
      Forall2 (fun _ y => P y) xs ys.
  Proof.
    intros P xs ys; revert xs.
    induction ys; intros * Hlen Hf; inv Hf;
      destruct xs; simpl in *; try congruence;
        constructor; auto.
  Qed.

  Lemma Forall2_cons':
    forall P (x : A) (y : B) l l',
      (P x y /\ Forall2 P l l') <-> Forall2 P (x::l) (y::l').
  Proof.
    split. now intuition.
    inversion 1; auto.
  Qed.

  Lemma Forall2_det : forall (R : A -> B -> Prop),
      (forall x y1 y2, R x y1 -> R x y2 -> y1 = y2) ->
      forall xs ys1 ys2, Forall2 R xs ys1 -> Forall2 R xs ys2 -> ys1 = ys2.
  Proof.
    intros R HR xs. induction xs as [| x xs]; intros ys1 ys2 Hall1 Hall2.
    - inversion Hall1. inversion Hall2; reflexivity.
    - inversion Hall1. inversion Hall2. f_equal; eauto.
  Qed.

  Remark Forall2_hd:
    forall (A B : Type) (P : A -> B -> Prop)
      (x : A) (l : list A) (x' : B) (l' : list B),
      Forall2 P (x :: l) (x' :: l') -> P x x'.
  Proof.
    intros * HF. inv HF. auto.
  Qed.

  Remark Forall2_tl:
    forall (A B : Type) (P : A -> B -> Prop)
      (x : A) (l : list A) (x' : B) (l' : list B),
      Forall2 P (x :: l) (x' :: l') -> Forall2 P l l'.
  Proof.
    intros * HF. inv HF. auto.
  Qed.

  Lemma Forall2_combine:
    forall P (xs: list A) (ys: list B),
      Forall2 P xs ys -> Forall (fun x => P (fst x) (snd x)) (combine xs ys).
  Proof.
    intros P xs ys Hfa2.
    induction Hfa2; now constructor.
  Qed.

  Lemma Forall2_combine':
    forall P (xs : list A) (ys : list B),
      Forall2 (fun x y => P (x, y)) xs ys -> Forall P (combine xs ys).
  Proof.
    intros P xs ys Hfa2.
    induction Hfa2; now constructor.
  Qed.

  Lemma Forall2_combine_ll: forall P (xs : list A) (ys : list B) (zs : list C),
      Forall2 P xs ys ->
      length zs = length xs ->
      Forall2 (fun '(_, x) y => P x y) (combine zs xs) ys.
  Proof.
    intros P xs ys zs Hf. revert zs.
    induction Hf; intros zs Hlen; simpl in *.
    - destruct zs; simpl in *; try congruence.
      constructor.
    - destruct zs; simpl in *; try congruence.
      constructor; auto.
  Qed.

  Lemma Forall2_combine_lr: forall P (xs : list A) (ys : list B) (zs : list C),
      Forall2 P xs ys ->
      length zs = length xs ->
      Forall2 (fun '(x, _) y => P x y) (combine xs zs) ys.
  Proof.
    intros P xs ys zs Hf. revert zs.
    induction Hf; intros zs Hlen; simpl in *.
    - destruct zs; simpl in *; try congruence.
      constructor.
    - destruct zs; simpl in *; try congruence.
      constructor; auto.
  Qed.

  Lemma Forall2_same:
    forall P (xs: list A),
      Forall (fun x => P x x) xs <-> Forall2 P xs xs.
  Proof.
    induction xs as [|x xs IH]; split; auto;
      inversion_clear 1; destruct IH; auto.
  Qed.

  Lemma Forall2_eq_refl:
    forall (x: list A), Forall2 eq x x.
  Proof.
    induction x; auto.
  Qed.

  Lemma Forall2_in_left:
    forall P (xs: list A) (ys: list B) x,
      Forall2 P xs ys ->
      In x xs ->
      exists y, In y ys /\ P x y.
  Proof.
    induction 1; simpl. contradiction.
    destruct 1 as [Heq|Hin].
    now subst; exists y; auto.
    apply IHForall2 in Hin. destruct Hin as (y' & Hin & HP).
    eauto.
  Qed.

  Lemma Forall2_in_right:
    forall P (xs: list A) (ys: list B) y,
      Forall2 P xs ys ->
      In y ys ->
      exists x, In x xs /\ P x y.
  Proof.
    induction 1; simpl. contradiction.
    destruct 1 as [Heq|Hin].
    now subst; exists x; auto.
    apply IHForall2 in Hin. destruct Hin as (y' & Hin & HP).
    eauto.
  Qed.

  Lemma Forall2_chain_In':
    forall {C} P Q (xs: list A) (ys: list B) (zs: list C) x z,
      Forall2 P xs ys ->
      Forall2 Q ys zs ->
      In (x, z) (combine xs zs) ->
      exists y, P x y /\ Q y z /\ In (x, y) (combine xs ys)
                               /\ In (y, z) (combine ys zs).
  Proof.
    induction xs as [|x xs IH]; simpl. now intuition.
    intros ys zs x' z HP HQ Hin.
    destruct ys as [|y ys]. now inversion HP.
    destruct zs as [|z' zs]. now inversion HQ.
    inversion_clear HP. inversion_clear HQ.
    inversion_clear Hin as [Hin'|Hin'].
    - inv Hin'. exists y; repeat split; simpl; auto with datatypes.
    - match goal with Hp:Forall2 P _ _, Hq:Forall2 Q _ _ |- _ =>
        destruct (IH _ _ _ _ Hp Hq Hin') as (y' & HP & HQ & Hin1 & Hin2) end.
      exists y'. repeat split; simpl; auto with datatypes.
  Qed.

  Lemma Forall2_chain_In:
    forall {C} P Q (xs: list A) (ys: list B) (zs: list C) x z,
      Forall2 P xs ys ->
      Forall2 Q ys zs ->
      In (x, z) (combine xs zs) ->
      exists y, P x y /\ Q y z.
  Proof.
    intros * HP HQ Hin.
    destruct (Forall2_chain_In' _ _ _ _ _ _ _ HP HQ Hin)
      as (y & Hp & Hq & Hin1 & Hin2).
    eauto.
  Qed.

  Lemma all_In_Forall2:
    forall (P: A -> B -> Prop) xs vs,
      length xs = length vs ->
      (forall x v, In (x, v) (combine xs vs) -> P x v) ->
      Forall2 P xs vs.
  Proof.
    induction xs as [|x xs IH]; destruct vs as [|v vs];
      auto; try now inversion 1.
    inversion 1. intro Hc. constructor.
    - apply Hc. simpl. auto.
    - apply IH; auto.
      intros * Hin. apply Hc. now right.
  Qed.

  Lemma Forall2_impl_In:
    forall (P Q: A -> B -> Prop) (l1: list A) (l2: list B),
      (forall (a: A) (b: B), In a l1 -> In b l2 -> P a b -> Q a b) ->
      Forall2 P l1 l2 ->
      Forall2 Q l1 l2.
  Proof.
    intros * HPQ HfaP.
    induction HfaP; auto.
    apply Forall2_cons;
      auto using in_eq, in_cons.
  Qed.

  Global Instance Forall2_Proper:
    Proper (pointwise_relation A (pointwise_relation B iff)
                               ==> eq ==> eq ==> iff) (@Forall2 A B).
  Proof.
    intros P Q HPQ ? xs Pxs ? ys Pys; subst.
    split; intro FA; apply Forall2_impl_In with (2:=FA);
      intros * Ixs Iys HH; now apply HPQ in HH.
  Qed.

  Lemma Forall2_swap_args:
    forall (P: A -> B -> Prop) (xs: list A) (ys: list B),
      Forall2 P xs ys <-> Forall2 (fun y x => P x y) ys xs.
  Proof.
    split; intro HH; induction HH; auto.
  Qed.

  Lemma Forall2_Forall2:
    forall (P1: A -> B -> Prop) P2 xs ys,
      Forall2 P1 xs ys ->
      Forall2 P2 xs ys ->
      Forall2 (fun x y => P1 x y /\ P2 x y) xs ys.
  Proof.
    intros * Hfa1 Hfa2.
    induction Hfa1 as [|x y xs ys H1 Hfa1 IH]; auto.
    inversion_clear Hfa2. auto.
  Qed.

  Lemma Forall2_length :
    forall (P : A -> B -> Prop) l1 l2,
      Forall2 P l1 l2 -> length l1 = length l2.
  Proof.
    induction l1, l2; intros * Hall; inversion Hall; clear Hall; subst; simpl; auto.
  Qed.

  Lemma Forall2_forall:
    forall (P: A -> B -> Prop) xs ys,
      ((forall x y, In (x, y) (combine xs ys) -> P x y)
       /\ length xs = length ys)
      <->
      Forall2 P xs ys.
  Proof.
    split.
    - intros * (Hin & Hlen).
      apply Forall2_forall2.
      split; auto.
      intros x y n x' y' Hnl Hn1 Hn2.
      apply Hin.
      subst x' y'. rewrite <-combine_nth with (1:=Hlen).
      apply nth_In.
      now rewrite combine_length, <-Hlen, Min.min_idempotent.
    - intros H; split.
      + intros * Hin.
        apply Forall2_combine in H.
        eapply Forall_forall in Hin; eauto.
        auto.
      + eapply Forall2_length; eauto.
  Qed.

  Lemma Forall2_eq:
    forall (xs: list A) ys,
      Forall2 eq xs ys <-> xs = ys.
  Proof.
    split; intro HH.
    - induction HH; subst; auto.
    - subst. induction ys; auto.
  Qed.

  Lemma Forall2_In:
    forall x v xs vs (P : A -> B -> Prop) ,
      In (x, v) (combine xs vs) ->
      Forall2 P xs vs ->
      P x v.
  Proof.
    intros x v xs vs P Hin HP.
    apply Forall2_combine in HP.
    rewrite Forall_forall in HP.
    now apply HP in Hin.
  Qed.

  Lemma Forall2_left_cons:
    forall P (x:A) xs (ys : list B),
      Forall2 P (x::xs) ys ->
      exists y ys', ys = y::ys' /\ P x y /\ Forall2 P xs ys'.
  Proof.
    inversion_clear 1; eauto.
  Qed.

  Lemma Forall2_right_cons:
    forall P (xs: list A) (y: B) ys,
      Forall2 P xs (y::ys) ->
      exists x xs', xs = x::xs' /\ P x y /\ Forall2 P xs' ys.
  Proof.
    inversion_clear 1; eauto.
  Qed.

  Lemma Forall2_Forall2_exists:
    forall {C} P Q (xs: list A) (ys: list B),
      Forall2 (fun x y=> exists z, P x z /\ Q y z) xs ys ->
      exists (zs: list C), Forall2 P xs zs /\ Forall2 Q ys zs.
  Proof.
    intros * Hfa.
    induction Hfa; eauto.
    destruct IHHfa as (zs & HPs & HQs).
    destruct H as (z & HP & HQ).
    exists (z::zs); eauto.
  Qed.

  Lemma Forall2_map_1:
    forall {C} P (f: A -> C) (xs: list A) (ys: list B),
      Forall2 P (map f xs) ys <-> Forall2 (fun x=>P (f x)) xs ys.
  Proof.
    induction xs as [|x xs]; destruct ys as [|y ys];
      try (now split; inversion 1; constructor).
    split; intro HH.
    - inversion_clear HH.
      apply Forall2_cons; auto.
      apply IHxs; auto.
    - inversion_clear HH.
      apply Forall2_cons; auto.
      apply IHxs; auto.
  Qed.

  Lemma Forall2_in_left_combine:
    forall (l: list A) (l': list B) P x,
      Forall2 P l l' ->
      In x l ->
      exists y, In (x, y) (combine l l') /\ P x y.
  Proof.
    induction 1; inversion_clear 1.
    - subst; exists y; simpl; intuition.
    - simpl; destruct IHForall2; auto.
      eexists; intuition; eauto.
  Qed.

  Lemma Forall2_app_split :
    forall (P : A -> B -> Prop)  l1 l1' l2 l2',
      Forall2 P (l1 ++ l2) (l1' ++ l2') ->
      length l1 = length l1' ->
      Forall2 P l1 l1' /\ Forall2 P l2 l2'.
  Proof.
    induction l1, l1'; simpl; intros * Hf Hzero; eauto; inv Hzero.
    inv Hf. apply IHl1 in H5; eauto. split; try econstructor; tauto.
  Qed.

  Lemma Forall2_Permutation_1 : forall (P : A -> B -> Prop) l1 l1' l2,
      Permutation l1 l1' ->
      Forall2 P l1 l2 ->
      exists l2', Permutation l2 l2' /\ Forall2 P l1' l2'.
  Proof.
    intros P l1 l1' l2 Hperm Hf. revert l2 Hf.
    induction Hperm; intros l2 Hf.
    - inv Hf. exists []; auto.
    - inv Hf.
      apply IHHperm in H3 as [l2' [Hperm' Hf']].
      exists (y::l2'). split; auto.
    - inv Hf. inv H3.
      exists (y1::y0::l'0). split; auto.
      repeat constructor.
    - eapply IHHperm1 in Hf. destruct Hf as [l2' [Hperm' Hf']].
      eapply IHHperm2 in Hf'. destruct Hf' as [l2'' [Hperm'' Hf'']].
      exists l2''. split; auto. etransitivity; eauto.
  Qed.


  Lemma Forall2_const_map :
    forall (P : A -> B -> Prop) (e : A) (l : list C) (l' : list B),
      Forall (fun y => P e y) l' ->
      length l = length l' ->
      Forall2 (fun x y => P x y) (map (fun _ => e) l) l'.
  Proof.
    intros * Hf Hlen.
    apply Forall2_forall; split; [| now rewrite map_length].
    intros * Hin. revert dependent l'.
    induction l; intros. inv Hin.
    destruct l'; inv Hlen. simpl in Hin.
    destruct Hin; inv Hf; try inv H; eauto.
  Qed.

  Lemma Forall2_singl : forall (P : A -> B -> Prop) x y,
      Forall2 P [x] [y] -> P x y.
  Proof.
    intros * Hf. inversion Hf; auto.
  Qed.
End Forall2.

Hint Resolve (proj2 (Forall2_eq _ _)).

Lemma Forall2_trans_ex:
  forall {A B C} (P: A -> B -> Prop) Q xs ys (zs: list C),
    Forall2 P xs ys ->
    Forall2 Q ys zs ->
    Forall2 (fun x z => exists y, In y ys /\ P x y /\ Q y z) xs zs.
Proof.
  intros * HPs HQs'.
  revert zs HQs'.
  induction HPs. now inversion 1; auto.
  inversion_clear 1 as [|? ? ? zs' HQ HQs].
  apply IHHPs in HQs.
  constructor; eauto with datatypes.
  eapply Forall2_impl_In  with (2:=HQs).
  intros ? ? ? ? (? & ? & ? & ?).
  eauto with datatypes.
Qed.

Lemma Forall2_map_2:
  forall {A B C} P (f: B -> C) (xs: list A) (ys: list B),
    Forall2 P xs (map f ys) <-> Forall2 (fun x y=>P x (f y)) xs ys.
Proof.
  intros.
  now rewrite Forall2_swap_args, Forall2_map_1, Forall2_swap_args.
Qed.

(* Show a predicate of two lists by "folding right" progressively. *)
Lemma forall2_right:
  forall {A B : Type} (P : list A -> list B -> Prop),
    P [] [] ->
    (forall x y xs' ys',
        P xs' ys' ->
        P (x::xs') (y::ys')) ->
    forall xs ys,
      length xs = length ys ->
      P xs ys.
Proof.
  intros A B P Pnil HH.
  induction xs, ys; auto; discriminate.
Qed.

Fact nth_concat2 {A B} : forall (x1 : A) (x2 : B) l1 l2 a b n,
    length l1 = length l2 ->
    Forall2 (fun l1 l2 => length l1 = length l2) l1 l2 ->
    n < length (concat l1) ->
    x1 = nth n (concat l1) a ->
    x2 = nth n (concat l2) b ->
    exists n', exists n'', (n' < length l1 /\
                  n'' < length (nth n' l1 [a]) /\
                  x1 = nth n'' (nth n' l1 [a]) a /\
                  x2 = nth n'' (nth n' l2 [b]) b).
Proof.
  intros x1 x2 l1 l2 a b n Hlen1 Hlen2.
  generalize dependent n.
  induction Hlen2; intros n Hlen3 Hnth1 Hnth2; simpl in *.
  - inversion Hlen3.
  - inv Hlen1. specialize (IHHlen2 H1).
    destruct (n <? length x) eqn:Hnx.
    + (* the element is in the first sublist *)
      rewrite Nat.ltb_lt in Hnx.
      exists 0. exists n.
      repeat split; auto.
      * apply Nat.lt_0_succ.
      * apply app_nth1; auto.
      * apply app_nth1; rewrite <- H; auto.
    + (* the element is in the rest of the sublist *)
      rewrite Nat.ltb_ge in Hnx.
      rewrite app_length in Hlen3.
      assert (n - length x < length (concat l)) as Hlen3' by omega.
      specialize (IHHlen2 (n - length x) Hlen3' (* (app_nth2 _ _ _ Hnx') (app_nth2 _ _ _ Hny') *)).
      assert (n >= length x) as Hnx' by omega; assert (n >= length y) as Hny' by omega.
      rewrite H in IHHlen2 at 2.
      specialize (IHHlen2 (app_nth2 _ _ _ Hnx') (app_nth2 _ _ _ Hny')) as [n' [n'' [Hlen' [Hlen'' [Hnth1 Hnth2]]]]].
      exists (S n'). exists n''. repeat split; auto. omega.
Qed.

Lemma Forall2_concat {A B} : forall (P : A -> B -> Prop) l1 l2,
    Forall2 (fun l1 l2 => Forall2 P l1 l2) l1 l2 ->
    Forall2 P (concat l1) (concat l2).
Proof.
  intros P l1 l2 Hforall.
  rewrite Forall2_forall2 in Hforall; destruct Hforall as [Hlen Hforall].
  rewrite Forall2_forall2.
  assert (Forall2 (fun l1 l2 => length l1 = length l2) l1 l2) as Hlen'.
  { rewrite Forall2_forall2.
      split; auto.
      intros a b n x1 x2 Hlen2 Hnth1 Hnth2.
      specialize (Hforall a b n x1 x2 Hlen2 Hnth1 Hnth2).
      rewrite Forall2_forall2 in Hforall; destruct Hforall as [Hlen3 _]; auto. }
  assert (length (concat l1) = length (concat l2)) as Hlenconcat.
  { clear Hlen Hforall.
    induction Hlen'; simpl; auto.
    repeat rewrite app_length. rewrite H. rewrite IHHlen'. reflexivity. }
  split; auto.
  intros a b n x1 x2 Hlen2 Hnth1 Hnth2; subst.
  specialize (nth_In _ a Hlen2) as Hin1.
  specialize (nth_concat2 _ _ _ _ a b n Hlen Hlen' Hlen2 eq_refl eq_refl)
    as [n' [n'' [Hlenn1 [Hlenn2 [Hnth1 Hnth2]]]]].
  specialize (Hforall [a] [b] n' _ _ Hlenn1 eq_refl eq_refl).
  rewrite Forall2_forall2 in Hforall; destruct Hforall as [Hlen3 Hforall].
  specialize (Hforall a b n'' _ _ Hlenn2 eq_refl eq_refl).
  rewrite <- Hnth1 in Hforall. rewrite <- Hnth2 in Hforall.
  assumption.
Qed.

Section Forall3.

  Context {A B C : Type}.
  Variable R : A -> B -> C -> Prop.

  Inductive Forall3 : list A -> list B -> list C -> Prop :=
  | Forall3_nil : Forall3 [] [] []
  | Forall3_cons : forall (x : A) (y : B) (z: C)
                          (l0 : list A) (l1 : list B) (l2 : list C),
      R x y z ->
      Forall3 l0 l1 l2 ->
      Forall3 (x :: l0) (y :: l1) (z :: l2).

  Lemma Forall3_length :
    forall (l1 : list A) (l2 : list B) (l3 : list C),
      Forall3 l1 l2 l3 ->
      length l1 = length l2
      /\ length l2 = length l3.
  Proof.
    induction 1. tauto. simpl. omega.
  Qed.

  Lemma Forall3_in_right:
    forall (xs : list A)
      (ys : list B) (zs : list C) (z : C),
      Forall3 xs ys zs ->
      In z zs -> exists (x : A) (y : B), In x xs /\ In y ys /\ R x y z.
  Proof.
    induction 1; simpl. contradiction.
    destruct 1 as [Heq|Hin].
    now subst; exists x, y; auto.
    apply IHForall3 in Hin. destruct Hin as (x' & y' & Hin & Hin' & HP).
    exists x', y'. eauto.
  Qed.

  Remark Forall3_tl:
    forall (x : A)
      (y : B) (z : C) (l0 : list A) (l1 : list B) (l2 : list C),
      Forall3 (x :: l0) (y :: l1) (z :: l2) -> Forall3 l0 l1 l2.
  Proof.
    intros * HF. inv HF. auto.
  Qed.

  Fixpoint forall3b (f : A -> B -> C -> bool) l1 l2 l3 :=
    match l1, l2, l3 with
    | nil, nil, nil => true
    | e1 :: l1, e2 :: l2, e3 :: l3 => andb (f e1 e2 e3) (forall3b f l1 l2 l3)
    | _, _, _ => false
    end.

  Lemma Forall3_ignore23:
    forall xs ys zs,
      Forall3 xs ys zs ->
      Forall (fun x => exists y z, R x y z) xs.
  Proof.
    induction 1; eauto.
  Qed.

  Lemma Forall3_ignore13:
    forall xs ys zs,
      Forall3 xs ys zs ->
      Forall (fun y => exists x z, R x y z) ys.
  Proof.
    induction 1; eauto.
  Qed.

  Lemma Forall3_ignore12:
    forall xs ys zs,
      Forall3 xs ys zs ->
      Forall (fun z => exists x y, R x y z) zs.
  Proof.
    induction 1; eauto.
  Qed.

  Lemma Forall3_ignore3:
    forall xs ys zs,
      Forall3 xs ys zs ->
      Forall2 (fun x y => exists z, R x y z) xs ys.
  Proof.
    induction 1; eauto.
  Qed.
End Forall3.

Lemma Forall3_forall3 {A B C}:
  forall P l1 l2 l3,
    Forall3 P l1 l2 l3
    <-> length l1 = length l2
      /\ length l1 = length l3
      /\ forall (a : A) (b : B) (c : C) n x1 x2 x3,
          n < length l1 ->
          nth n l1 a = x1 ->
          nth n l2 b = x2 ->
          nth n l3 c = x3 ->
          P x1 x2 x3.
Proof.
  intros P l1. induction l1; intros l2 l3.
  - split; intro H.
    + inv H. repeat split; simpl; auto. intros. omega.
    + destruct H as [H1 [H2 _]]. destruct l2; destruct l3; try discriminate. constructor.
  - split; intro H.
    + inv H. rewrite IHl1 in H5. destruct H5 as [? [? ?]]. repeat split; simpl; auto.
      intros. destruct n; subst; trivial. eapply H1; eauto. omega.
    + destruct H as [Hlen2 [Hlen3 H]].
      destruct l2; destruct l3; simpl in Hlen2; simpl in Hlen3; try discriminate. constructor.
      apply (H a b c 0); trivial; simpl; try omega.
      rewrite IHl1. repeat split; try omega.
      intros. eapply (H a0 b0 c0 (S n)); simpl; eauto. omega.
Qed.

Lemma forall3b_Forall3:
  forall {A B C} (p : A -> B -> C -> bool) xs ys zs,
    (forall3b p xs ys zs = true) <-> (Forall3 (fun x y z => p x y z = true) xs ys zs).
Proof.
  split.
  - revert xs ys zs.
    induction xs, ys, zs; simpl; try discriminate; eauto using Forall3_nil.
    rewrite Bool.andb_true_iff.
    intros (? & ?); eauto using Forall3_cons.
  - induction 1; auto. simpl.
    apply Bool.andb_true_iff; split; auto.
Qed.

Lemma Forall3_impl_In:
  forall {A B C} (P Q : A -> B -> C -> Prop) xs ys zs,
    (forall x y z, In x xs -> In y ys -> In z zs -> P x y z -> Q x y z) ->
    Forall3 P xs ys zs -> Forall3 Q xs ys zs.
Proof.
  intros * PQ FA. induction FA; constructor; auto with datatypes.
Qed.


Lemma Forall3_Forall3 {A B C}: forall (P Q : A -> B -> C -> Prop) xs ys zs,
    Forall3 P xs ys zs ->
    Forall3 Q xs ys zs ->
    Forall3 (fun x y z => P x y z /\ Q x y z) xs ys zs.
Proof.
  intros * Hf1 Hf2.
  induction Hf1; inv Hf2; constructor; auto.
Qed.

Lemma Forall3_combine'1 {A B C} : forall (P : (A * B) -> C -> Prop) xs ys zs,
    Forall3 (fun x y z => P (x, y) z) xs ys zs ->
    Forall2 P (combine xs ys) zs.
Proof.
  intros * Hf.
  induction Hf; simpl; constructor; auto.
Qed.

Lemma Forall3_ignore1' {A B C} : forall P (xs : list A) (ys : list B) (zs : list C),
    length xs = length ys ->
    Forall2 P ys zs ->
    Forall3 (fun _ y z => P y z) xs ys zs.
Proof.
  intros * Hlen Hf. revert xs Hlen.
  induction Hf; intros; destruct xs; simpl in *; try congruence; constructor; auto.
Qed.

Lemma Forall3_ignore2' {A B C} : forall P (xs : list A) (ys : list B) (zs : list C),
    length ys = length xs ->
    Forall2 P xs zs ->
    Forall3 (fun x _ z => P x z) xs ys zs.
Proof.
  intros * Hlen Hf. revert ys Hlen.
  induction Hf; intros; destruct ys; simpl in *; try congruence; constructor; auto.
Qed.

Lemma Forall3_ignore3' {A B C} : forall P (xs : list A) (ys : list B) (zs : list C),
    length zs = length xs ->
    Forall2 P xs ys ->
    Forall3 (fun x y _ => P x y) xs ys zs.
Proof.
  intros * Hlen Hf. revert zs Hlen.
  induction Hf; intros; destruct zs; simpl in *; try congruence; constructor; auto.
Qed.

Global Instance Forall3_Proper' {A B C}:
  Proper (pointwise_relation A (pointwise_relation B (pointwise_relation C Basics.impl))
                             ==> eq ==> eq ==> eq ==> Basics.impl) (@Forall3 A B C).
Proof.
  intros P Q HPQ ? xs Pxs ? ys Pys ? zs Pzs; subst.
  intro FA; apply Forall3_impl_In with (2:=FA);
    intros * Ixs Iys Izs HH; now apply HPQ in HH.
Qed.

Global Instance Forall3_Proper {A B C}:
  Proper (pointwise_relation A (pointwise_relation B (pointwise_relation C iff))
                             ==> eq ==> eq ==> eq ==> iff) (@Forall3 A B C).
Proof.
  intros P Q HPQ ? xs Pxs ? ys Pys ? zs Pzs; subst.
  split. now rewrite HPQ. now rewrite <-HPQ.
Qed.

Section InMembers.
  Context {A B: Type}.

  Fixpoint InMembers (a:A) (l:list (A * B)) : Prop :=
    match l with
    | nil => False
    | (a', _) :: m => a' = a \/ InMembers a m
    end.

  Inductive NoDupMembers: list (A * B) -> Prop :=
  | NoDupMembers_nil:
      NoDupMembers nil
  | NoDupMembers_cons: forall a b l,
      ~ InMembers a l ->
      NoDupMembers l ->
      NoDupMembers ((a, b)::l).

  Lemma inmembers_eq:
    forall a b l, InMembers a ((a, b) :: l).
  Proof.
    intros. constructor. reflexivity.
  Qed.

  Lemma inmembers_cons:
    forall a a' l, InMembers a l -> InMembers a (a' :: l).
  Proof.
    intros. destruct a'. simpl. intuition.
  Qed.

  Lemma In_InMembers:
    forall a b xs,
      In (a, b) xs -> InMembers a xs.
  Proof.
    intros * Hin.
    induction xs as [|x xs IH]; inversion_clear Hin; subst.
    - simpl. left. reflexivity.
    - simpl. destruct x. right. intuition.
  Qed.

  Lemma InMembers_In:
    forall a xs,
      InMembers a xs -> exists b, In (a, b) xs.
  Proof.
    intros * Hin.
    induction xs as [|x xs IH]; simpl in Hin.
    - contradiction.
    - simpl. destruct x. destruct Hin; subst.
      + exists b; now left.
      + destruct (IH H) as (b' & HH); auto.
        exists b'; now right.
  Qed.

  Lemma nodupmembers_cons:
    forall id ty xs,
      NoDupMembers ((id, ty) :: xs) <->
      ~InMembers id xs /\ NoDupMembers xs.
  Proof.
    split.
    - inversion_clear 1. auto.
    - destruct 1 as [Hnin Hndup].
      constructor; auto.
  Qed.

  Lemma NotInMembers_NotIn:
    forall a b xs, ~ InMembers a xs -> ~ In (a, b) xs.
  Proof.
    intros * Hnim Hin.
    apply In_InMembers in Hin.
    intuition.
  Qed.

  Lemma NotIn_NotInMembers:
    forall a xs, (forall b, ~ In (a, b) xs) -> ~ InMembers a xs.
  Proof.
    intros * Notin Hin.
    apply InMembers_In in Hin as (?&?).
    eapply Notin; eauto.
  Qed.

  Lemma NotInMembers_cons:
    forall xs x y,
      ~InMembers y (x::xs) <-> ~InMembers y xs /\ y <> fst x.
  Proof.
    induction xs as [|x' xs IH]; split; intro Hnin.
    - split.
      + inversion 1.
      + intro Eq; apply Hnin.
        destruct x; simpl in *; now left.
    - destruct x; simpl. destruct Hnin as [? Diff].
      intro Hin; apply Diff.
      destruct Hin; try contradiction; auto.
    - split.
      + intro HH. apply Hnin.
        destruct x, x'.
        right. inversion HH; auto.
      + intro HH. apply Hnin.
        destruct x, x'.
        simpl in *; now left.
    - rewrite IH in Hnin; destruct Hnin as ((Hnin & Hx') & Hx).
      destruct x, x'; simpl in *.
      intro Hin; destruct Hin as [|[|]].
      + now apply Hx.
      + now apply Hx'.
      + now apply Hnin.
  Qed.

  Lemma InMembers_app:
    forall y ws xs,
      InMembers y (ws ++ xs) <-> (InMembers y ws) \/ (InMembers y xs).
  Proof.
    induction ws as [|y' ws IH].
    - now intuition.
    - destruct y' as [y' yv]. simpl.
      split; intro HH; destruct HH as [HH|HH].
      + intuition.
      + apply IH in HH. intuition.
      + destruct HH as [HH|HH].
        * intuition.
        * right. apply IH. intuition.
      + right. apply IH. intuition.
  Qed.

  Global Instance InMembers_Permutation_Proper:
    Proper (eq ==> (@Permutation (A*B)) ==> iff) InMembers.
  Proof.
    intros x y Heq xs ys Hperm.
    rewrite Heq. clear Heq x.
    split; intro Hinm.
    - apply InMembers_In in Hinm.
      destruct Hinm as [b Hinm].
      apply Permutation_in with (2:=Hinm) in Hperm.
      apply In_InMembers with (1:=Hperm).
    - apply InMembers_In in Hinm.
      destruct Hinm as [b Hinm].
      symmetry in Hperm.
      apply Permutation_in with (2:=Hinm) in Hperm.
      apply In_InMembers with (1:=Hperm).
  Qed.

  Lemma NotInMembers_app:
    forall y ws xs,
      ~InMembers y (ws ++ xs) <-> (~InMembers y xs /\ ~InMembers y ws).
  Proof.
    destruct ws; repeat split.
    - assumption.
    - inversion 1.
    - destruct 1. assumption.
    - intro HH. apply H.
      apply InMembers_app. auto.
    - intro. apply H.
      apply InMembers_app. auto.
    - destruct 1 as [H1 H2].
      intro H. apply InMembers_app in H. intuition.
  Qed.

  Lemma InMembers_dec:
    forall (x : A) (xs : list (A * B)),
      (forall (x y: A), {x = y} + {x <> y}) ->
      { InMembers x xs } + { ~InMembers x xs }.
  Proof.
    intros * Hdec.
    induction xs as [|(y, yv) xs]; auto.
    simpl.
    destruct IHxs.
    now intuition.
    destruct (Hdec y x) as [Heq|Hne]; auto.
    right. destruct 1; auto.
  Qed.

  Lemma inmembers_skipn:
    forall x (xs: list (A * B)) n,
      InMembers x (skipn n xs) ->
      InMembers x xs.
  Proof.
    induction xs as [|(y, yv) xs IH]; intros n Hin.
    now rewrite skipn_nil in Hin; inversion Hin.
    destruct n.
    now destruct Hin; subst; auto using inmembers_eq, inmembers_cons.
    apply IH in Hin; auto using inmembers_cons.
  Qed.

  Lemma inmembers_firstn:
    forall x (xs: list (A * B)) n,
      InMembers x (firstn n xs) ->
      InMembers x xs.
  Proof.
    induction xs as [|(y, yv) xs IH]; intros n Hin.
    now rewrite firstn_nil in Hin; inversion Hin.
    destruct n.
    now destruct Hin; subst; auto using inmembers_eq, inmembers_cons.
    destruct Hin as [|Hin]; subst; auto using inmembers_eq.
    apply IH in Hin; auto using inmembers_cons.
  Qed.

  Lemma InMembers_skipn_firstn:
    forall x (xs: list (A * B)) n,
      InMembers x (skipn n xs) ->
      NoDupMembers xs ->
      ~InMembers x (firstn n xs).
  Proof.
    induction xs as [|y xs IH]; intros * Hs Hnd Hf.
    now rewrite skipn_nil in Hs; inversion Hs.
    destruct n; simpl; auto.
    destruct y as (ya, yb).
    apply nodupmembers_cons in Hnd.
    destruct Hnd as [Hnin Hnd].
    simpl in *.
    destruct Hf as [Hf|Hf].
    - subst. eauto using inmembers_skipn.
    - apply IH with (1:=Hs) (2:=Hnd) (3:=Hf).
  Qed.

  Lemma InMembers_firstn_skipn:
    forall (xs: list (A * B)) n x,
      InMembers x (firstn n xs) ->
      NoDupMembers xs ->
      ~InMembers x (skipn n xs).
  Proof.
    induction xs as [|(ya, yb) xs IH]; intros n x Him Hnd.
    now rewrite firstn_nil in Him; inversion Him.
    destruct n; auto.
    simpl in *.
    inversion_clear Hnd as [|? ? ? Hnim Hnd'].
    destruct Him; subst;
      eauto using inmembers_skipn.
  Qed.

  Lemma NoDupMembers_NoDup:
    forall xs, NoDupMembers xs -> NoDup xs.
  Proof.
    induction xs as [|x xs IH]; [now constructor|].
    intro Hndm.
    inversion_clear Hndm.
    constructor; [|now apply IH].
    apply NotInMembers_NotIn. assumption.
  Qed.

  Lemma NoDupMembers_app_cons:
    forall ws x y xs,
      NoDupMembers (ws ++ (x, y) :: xs)
      <-> ~InMembers x (ws ++ xs) /\ NoDupMembers (ws ++ xs).
  Proof.
    induction ws as [|w ws IH]; repeat split.
    - apply nodupmembers_cons in H. intuition.
    - apply nodupmembers_cons in H. intuition.
    - destruct 1 as [HH1 HH2].
      apply nodupmembers_cons. intuition.
    - destruct w as [w ww].
      simpl in H. apply nodupmembers_cons in H.
      destruct H as [H1 H2].
      apply IH in H2.
      destruct H2 as [H2 H3].
      intro HH. destruct HH as [HH|HH].
      + subst. apply H1.
        apply InMembers_app. right.
        now constructor.
      + apply H2. assumption.
    - destruct w as [w ww].
      simpl in *. apply nodupmembers_cons in H.
      destruct H as [H1 H2].
      apply IH in H2.
      apply nodupmembers_cons.
      destruct H2 as [H2 H3].
      apply NotInMembers_app in H1.
      destruct H1 as [H1 H4].
      apply NotInMembers_cons in H1.
      split; try apply NotInMembers_app; intuition.
    - destruct 1 as [H1 H2].
      destruct w as [w ww].
      simpl in H2. apply nodupmembers_cons in H2.
      destruct H2 as [H2 H3].
      simpl. apply nodupmembers_cons.
      split.
      + intro HH. apply H2.
        apply InMembers_app.
        apply InMembers_app in HH.
        destruct HH as [HH|HH]; [now auto|].
        destruct HH as [HH|HH]; [|now auto].
        exfalso; apply H1. subst.
        now constructor.
      + apply IH.
        split; [|assumption].
        intro HH. apply H1.
        constructor 2. assumption.
  Qed.

  Lemma NoDupMembers_remove_1:
    forall ws x xs,
      NoDupMembers (ws ++ x :: xs) -> NoDupMembers (ws ++ xs).
  Proof.
    intros * HH.
    destruct x. apply NoDupMembers_app_cons in HH. intuition.
  Qed.

  Lemma NoDupMembers_app_r:
    forall ws xs,
      NoDupMembers (ws ++ xs) -> NoDupMembers xs.
  Proof.
    induction ws as [|w ws IH]; auto.
    intros xs H.
    apply IH.
    rewrite <-app_comm_cons in H.
    destruct w; rewrite nodupmembers_cons in H; tauto.
  Qed.

  Global Instance NoDupMembers_Permutation_Proper:
    Proper (Permutation (A:=A * B) ==> iff) NoDupMembers.
  Proof.
    intros xs ys Hperm.
    induction Hperm.
    - now intuition.
    - destruct x as [x y].
      rewrite 2 nodupmembers_cons, IHHperm, Hperm.
      reflexivity.
    - split; intro HH.
      + inversion HH as [|a b l' Hninm Hndup]. clear HH. subst.
        destruct x as [x y].
        inversion Hndup as [|c d l' Hinm' Hndup']. clear Hndup. subst.
        econstructor.
        * intro Hinm. apply Hinm'.
          inversion_clear Hinm; subst; auto.
          exfalso; apply Hninm. now constructor.
        * constructor; auto. intro Hinm.
          apply Hninm. now constructor 2.
      + inversion HH as [|a b l' Hninm Hndup]. clear HH. subst.
        destruct y as [x y].
        inversion Hndup as [|c d l' Hinm' Hndup']. clear Hndup. subst.
        econstructor.
        * intro Hinm. apply Hinm'.
          inversion_clear Hinm; subst; auto.
          exfalso; apply Hninm. now constructor.
        * constructor; auto. intro Hinm.
          apply Hninm. now constructor 2.
    - now rewrite IHHperm1.
  Qed.

  Lemma NoDupMembers_app_l:
    forall ws xs,
      NoDupMembers (ws ++ xs) -> NoDupMembers ws.
  Proof.
    intros * Hndup.
    rewrite Permutation_app_comm in Hndup.
    apply NoDupMembers_app_r with (1:=Hndup).
  Qed.

  Lemma NoDupMembers_app_InMembers:
    forall x xs ws,
      NoDupMembers (xs ++ ws) ->
      InMembers x xs ->
      ~InMembers x ws.
  Proof.
    induction ws as [|w ws IH]; auto.
    intros Nodup Hin H.
    destruct w; simpl in H.
    destruct H.
    - apply NoDupMembers_app_cons in Nodup.
      destruct Nodup as (Notin & ?).
      apply NotInMembers_app in Notin.
      subst.
      destruct Notin as (? & Notin); now apply Notin.
    - apply NoDupMembers_remove_1 in Nodup.
      apply IH; auto.
  Qed.

  Lemma NoDupMembers_app_InMembers_l:
    forall x xs ws,
      NoDupMembers (xs ++ ws) ->
      InMembers x ws ->
      ~InMembers x xs.
  Proof.
    intros * Hdup Hin.
    eapply NoDupMembers_app_InMembers; eauto.
    now rewrite (Permutation_app_comm _ xs).
  Qed.

  Lemma NoDupMembers_det:
    forall x t t' xs,
      NoDupMembers xs ->
      In (x, t) xs ->
      In (x, t') xs ->
      t = t'.
  Proof.
    induction xs; intros H Hin Hin'.
    - contradict Hin.
    - inversion Hin; inversion Hin'; subst.
      + inversion H1; auto.
      + inversion H; subst.
        inversion Hin'.
        * inversion H0; auto.
        * exfalso. apply H3. eapply In_InMembers; eauto.
      + inversion H; subst.
        inversion Hin.
        * inversion H1; auto.
        * exfalso. apply H3. eapply In_InMembers; eauto.
      + apply IHxs; auto.
        destruct a; rewrite nodupmembers_cons in H; tauto.
  Qed.

  Lemma NoDupMembers_firstn:
    forall (xs: list (A * B)) n,
      NoDupMembers xs ->
      NoDupMembers (firstn n xs).
  Proof.
    induction xs as [|x xs IH]. now setoid_rewrite firstn_nil; auto.
    intros n Hndup.
    destruct n; simpl; auto using NoDupMembers_nil.
    inversion_clear Hndup as [|? ? ? Hni Hnd].
    apply IH with (n:=n) in Hnd.
    eauto using NoDupMembers, inmembers_firstn.
  Qed.

  Lemma InMembers_neq:
    forall x y xs,
      InMembers x xs ->
      ~ InMembers y xs ->
      x <> y.
  Proof.
    intros * Hx Hy; intro xy. subst.
    now apply Hy.
  Qed.

  Remark fst_InMembers:
    forall x xs,
      InMembers x xs <-> In x (map (@fst A B) xs).
  Proof.
    induction xs; simpl; intuition.
  Qed.

  Remark fst_NoDupMembers:
    forall xs,
      NoDupMembers xs <-> NoDup (map (@fst A B) xs).
  Proof.
    induction xs as [|(x,y)].
    - split; constructor.
    - simpl; split; inversion 1.
      + inversion H as [|? ? ? Notin ? Heq]; subst.
        constructor.
        * now rewrite <-fst_InMembers.
        * now apply IHxs.
      + constructor.
        * now rewrite fst_InMembers.
        * now apply IHxs.
  Qed.

  Lemma InMembers_In_combine:
    forall x (xs: list A) (ys: list B),
      InMembers x (combine xs ys) ->
      In x xs.
  Proof.
    induction xs as [|x' xs]; auto.
    destruct ys; [contradiction|].
    destruct 1 as [Heq|Hin].
    now subst; constructor.
    constructor 2; apply IHxs with (1:=Hin).
  Qed.

  Lemma In_InMembers_combine:
    forall x (xs: list A) (ys: list B),
      length xs = length ys ->
      (In x xs <-> InMembers x (combine xs ys)).
  Proof.
    intros x xs ys Hlen.
    split; [|now apply InMembers_In_combine].
    revert x xs ys Hlen.
    induction xs as [|x' xs]; auto.
    intros ys Hlen Hin.
    destruct ys; [discriminate|].
    inversion Hin; subst; [now left|right].
    apply IHxs; auto.
  Qed.

  Lemma NoDup_NoDupMembers_combine:
    forall (xs: list A) (ys: list B),
    NoDup xs -> NoDupMembers (combine xs ys).
  Proof.
    induction xs as [|x xs]; [now intros; constructor|].
    intros ys Hndup.
    destruct ys; simpl; constructor.
    - inversion_clear Hndup.
      intro Hin. apply InMembers_In_combine in Hin.
      contradiction.
    - apply IHxs; auto. now inversion Hndup.
  Qed.

  Lemma NoDupMembers_combine_NoDup:
    forall (xs: list A) (ys: list B),
      length xs = length ys ->
      NoDupMembers (combine xs ys) -> NoDup xs.
  Proof.
    induction xs as [|x xs]; intros; auto using NoDup_nil.
    destruct ys as [|y ys]; [inv H|].
    simpl in *. injection H. intros Hlen.
    inv H0. constructor; eauto.
    rewrite <-In_InMembers_combine in H3; auto.
  Qed.

  Remark InMembers_snd_In:
    forall {C} y l,
      InMembers y (map (@snd C (A * B)) l) ->
      exists x z, In (x, (y, z)) l.
  Proof.
    induction l as [|(x', (y', z'))]; simpl; intros * Hin.
    - contradiction.
    - destruct Hin as [|Hin].
      + subst y'; exists x', z'; now left.
      + apply IHl in Hin; destruct Hin as (x & z & Hin).
        exists x, z; now right.
  Qed.

  Remark In_InMembers_snd:
    forall {C} x y z l,
      In (x, (y, z)) l ->
      InMembers y (map (@snd C (A * B)) l).
  Proof.
    induction l as [|(x', (y', z'))]; simpl; intros * Hin; auto.
    destruct Hin as [Eq|Hin].
    - inv Eq; now left.
    - right; auto.
  Qed.

  Lemma NoDupMembers_app:
    forall (ws xs : list (A * B)),
      NoDupMembers ws ->
      NoDupMembers xs ->
      (forall x, InMembers x ws -> ~InMembers x xs) ->
      NoDupMembers (ws ++ xs).
  Proof.
    intros * Hndws Hndxs Hnin.
    induction ws as [|w ws IH]; auto.
    destruct w as (wn & wv).
    inv Hndws.
    simpl; apply NoDupMembers_cons; auto using inmembers_cons.
    apply NotInMembers_app.
    split; auto using Hnin, inmembers_eq.
  Qed.

  Lemma NoDup_NoDupA:
    forall (xs: list A),
      NoDup xs <-> SetoidList.NoDupA eq xs.
  Proof.
    induction xs.
    - split; intro HH; auto using NoDup_nil.
    - destruct IHxs.
      split; intro HH; inv HH; constructor; auto.
      + rewrite SetoidList.InA_alt.
        destruct 1 as (y &  Heq & Hin).
        subst; auto.
      + match goal with H:~SetoidList.InA _ _ _ |- _
                        => rename H into Hsl end.
        rewrite SetoidList.InA_alt in Hsl.
        intro Hin. apply Hsl.
        exists a; split; auto.
  Qed.

  Lemma NoDup_skipn:
    forall (xs: list A) n,
      NoDup xs -> NoDup (skipn n xs).
  Proof.
    induction xs.
    now setoid_rewrite skipn_nil.
    destruct n; simpl.
    now intuition.
    inversion 1; auto.
  Qed.

  Lemma NoDupMembers_skipn:
    forall (xs: list (A * B)) n,
      NoDupMembers xs -> NoDupMembers (skipn n xs).
  Proof.
    induction xs.
    now setoid_rewrite skipn_nil.
    destruct n; simpl.
    now intuition.
    inversion 1; auto.
  Qed.

  Lemma InMembers_Forall:
    forall P (xs : list (A * B)) x,
      Forall P (map (@fst A B) xs) ->
      InMembers x xs ->
      P x.
  Proof.
    intros * Hfa Him.
    apply fst_InMembers in Him.
    apply Forall_forall with (1:=Hfa) (2:=Him).
  Qed.

  Lemma NoDupMembers_app':
    forall (xs ys : list (A * B)),
      NoDupMembers (xs++ys) ->
      NoDupMembers xs /\ NoDupMembers ys.
  Proof.
    intros xs ys Hndup.
    split.
    - apply NoDupMembers_app_l in Hndup; auto.
    - apply NoDupMembers_app_r in Hndup; auto.
  Qed.

  Lemma InMembers_incl : forall x (xs ys : list (A * B)),
      incl xs ys ->
      InMembers x xs ->
      InMembers x ys.
  Proof.
    intros * Hincl Hin.
    rewrite fst_InMembers in *.
    eapply incl_map in Hincl; eauto.
  Qed.

  Fact incl_NoDup_In : forall (l1 l2 : list (A * B)) x y,
      incl l1 l2 ->
      NoDupMembers l2 ->
      InMembers x l1 ->
      In (x, y) l2 ->
      In (x, y) l1.
  Proof.
    intros * Hincl Hndup Hinm Hin.
    apply InMembers_In in Hinm as [? Hin'].
    assert (x0 = y); subst; auto.
    eapply Hincl in Hin'.
    eapply NoDupMembers_det in Hndup; eauto.
  Qed.

End InMembers.

Section OptionLists.

  Context {A : Type}.

  Fixpoint LiftO (d : Prop) (P : A -> Prop) (x : option A) : Prop :=
    match x with None => d | Some x => P x end.

  Fixpoint Ino (a : A) (l : list (option A)) : Prop :=
    match l with
    | [] => False
    | b :: m => LiftO False (eq a) b \/ Ino a m
    end.

  (* Fixpoint Ino (a : A) (l : list (option A)) : Prop := *)
  (*   match l with *)
  (*   | [] => False *)
  (*   | Some b :: m => b = a \/ Ino a m *)
  (*   | None :: m => Ino a m *)
  (*   end. *)

  Inductive NoDupo : list (option A) -> Prop :=
    NoDupo_nil : NoDupo []
  | NoDupo_conss : forall x l, ~ Ino x l -> NoDupo l -> NoDupo (Some x :: l)
  | NoDupo_consn : forall l, NoDupo l -> NoDupo (None :: l).

  Definition assert_singleton (xs : option (list A)) : option A :=
    match xs with Some [x] => Some x | _ => None end.

  Lemma assert_singleton_spec:
    forall e (v : A),
      assert_singleton e = Some v ->
      e = Some [v].
  Proof.
    intros * AS. destruct e; inv AS.
    repeat match goal with
           | H: (match ?l with _ => _ end) = Some _ |- _ => destruct l
           | H: Some _ = Some _ |- _ => inv H
           end; try discriminate; auto.
  Qed.

  Lemma Ino_In :
    forall (x : A) xs, Ino x xs <-> In (Some x) xs.
  Proof.
    split; intro H; induction xs as [| e]; auto.
    - destruct e; inv H; simpl in *; subst; auto. tauto.
    - destruct e; inversion H as [Heq|]; try inv Heq;
        simpl in *; intuition.
  Qed.

  Lemma ino_app_iff :
    forall (l l' : list (option A)) (a : A),
      Ino a (l ++ l') <-> Ino a l \/ Ino a l'.
  Proof.
    setoid_rewrite Ino_In. auto using in_app_iff.
  Qed.

  Lemma ino_dec:
    forall (x : A) xos,
      (forall x y : A, {x = y} + {x <> y}) ->
      Ino x xos \/ ~Ino x xos.
  Proof.
    intros * H; rewrite Ino_In. eapply ListDec.In_decidable.
    intros y z. destruct y as [a|], z as [b|]; try (right; congruence).
    destruct (H a b); [left|right]; congruence.
    now left.
  Qed.

  Lemma NoDupo_app':
    forall (xs ws : list (option A)),
      NoDupo xs ->
      NoDupo ws ->
      (forall x : A, Ino x xs -> ~ Ino x ws) ->
      NoDupo (xs ++ ws).
  Proof.
    induction xs as [|[]]; intros * D1 D2 Hino; simpl; auto.
    - constructor. inv D1. rewrite Ino_In in *. rewrite in_app.
      intros []; auto. specialize (Hino a).
      apply Hino; simpl; rewrite Ino_In in *; auto.
      inv D1. apply IHxs; auto. intros. apply Hino. now right.
    - inv D1. constructor. apply IHxs; auto. intros. apply Hino. now right.
  Qed.

  Lemma Ino_Forall:
    forall (x : A) (xs : list (option A)) (P : option A -> Prop),
      Forall P xs -> Ino x xs -> P (Some x).
  Proof.
    intros * Hforall Hin.
    induction xs as [|a]; inversion Hin; inversion Hforall; subst; auto.
    destruct a; simpl in *; subst; tauto.
  Qed.

  Lemma NoDupo_NoDup: forall (xs : list A),
      NoDupo (map Some xs) <-> NoDup xs.
  Proof.
    induction xs; split; intro H; inv H; simpl; constructor.
    - rewrite Ino_In, in_map_iff in H2.
      intro contra; apply H2. exists a; auto.
    - rewrite <- IHxs; auto.
    - rewrite Ino_In, in_map_iff.
      intros [x [Heq contra]]; inv Heq; auto.
    - rewrite IHxs; auto.
  Qed.

End OptionLists.

Ltac app_NoDupMembers_det :=
  match goal with
  | H: NoDupMembers ?xs,
         H1: In (?x, ?t1) ?xs,
             H2: In (?x, ?t2) ?xs |- _ =>
      assert (t1 = t2) by (eapply NoDupMembers_det; eauto); subst t2; clear H2
    end.

(* List equality modulo duplicates *)

Definition same_elements {A} : relation (list A) :=
  fun xs ys => forall x, In x xs <-> In x ys.

Lemma same_elements_refl {A} : reflexive _ (@same_elements A).
Proof. now intros xs x. Qed.

Lemma same_elements_sym {A} : symmetric _ (@same_elements A).
Proof. now intro. Qed.

Lemma same_elements_trans {A} : transitive _ (@same_elements A).
Proof. firstorder. Qed.

Add Parametric Relation {A} : (list A) same_elements
    reflexivity proved by same_elements_refl
    symmetry proved by same_elements_sym
    transitivity proved by same_elements_trans
      as same_relation_rel.

Section Nub.
  Context {A : Type} (DA : forall x y : A, {x = y} + {x <> y}).

  Fixpoint nub (xs : list A) : list A :=
    match xs with
    | [] => []
    | x::xs => if in_dec DA x xs then nub xs else x :: nub xs end.

  Lemma In_nub:
    forall xs x,
      In x xs <-> In x (nub xs).
  Proof.
    induction xs as [|x xs IH]. now intuition.
    simpl. intro y. destruct (in_dec DA x xs); split; intro HH.
    - now destruct HH as [|HH]; subst; apply IH.
    - apply IH in HH; auto.
    - destruct HH as [|HH]; subst. now constructor.
      apply IH in HH. now constructor 2.
    - inv HH; auto. take (In y (nub xs)) and apply IH in it; auto.
  Qed.

  Lemma nub_same_elements:
    forall xs, same_elements (nub xs) xs.
  Proof. intros xs x; symmetry. now apply In_nub. Qed.

  Lemma NoDup_nub:
    forall xs, NoDup (nub xs).
  Proof.
    induction xs as [|x xs IH]; simpl; auto using NoDup_nil.
    destruct (in_dec DA x xs) as [HH|HH]; auto.
    rewrite In_nub in HH. now constructor.
  Qed.

  Lemma uniquify_list:
    forall (xs : list A), exists ys, (forall x, In x xs <-> In x ys) /\ NoDup ys.
  Proof.
    intro xs. exists (nub xs).
    split; [|now apply NoDup_nub].
    now setoid_rewrite <-In_nub.
  Qed.

End Nub.

Add Parametric Morphism {A} : (@List.In A)
    with signature (eq ==> same_elements ==> iff)
      as In_same_elements.
Proof.
  intros x xs ys S. now split; intro HH; apply S in HH.
Qed.

(** Tactics wellfoundedness and termination *)

Section LL.

  Context {A : Type}.

  Definition ll (ls1 ls2 : list A) :=
    length ls1 < length ls2.

  Lemma ll_wf':
    forall ls, Acc ll ls.
  Proof.
    intro ls. assert (length ls <= length ls) as Hlen; auto.
    revert Hlen. generalize (length ls) at 2.
    intro len; revert ls.
    unfold ll. induction len; intros ls Hlen; constructor;
                 try apply Le.le_n_0_eq in Hlen; intuition.
  Defined.

  Theorem ll_wf:
    well_founded ll.
  Proof.
    red; eauto using ll_wf'.
  Defined.

End LL.

Section ListSuffix.

  Context {A : Type}.

  Definition ltsuffix (ls1 ls2 : list A) :=
    exists ls1', ls2 = ls1' ++ ls1 /\ ls1' <> nil.

  Lemma ltsuffix_wf:
    well_founded ltsuffix.
  Proof.
    apply Wf_nat.well_founded_lt_compat with (f:=@length A).
    destruct 1 as (x' & H1 & H2).
    subst y. rewrite app_length.
    assert (length x' <> 0) as H3; try omega.
    now rewrite length_zero_iff_nil.
  Qed.

End ListSuffix.

Section Wf_Prod.

  Context {A B : Type}
          (R1 : A -> A -> Prop)
          (R2 : B -> B -> Prop).

  Hypothesis R1_wf : well_founded R1.
  Hypothesis R2_wf : well_founded R2.

  Definition rr xx yy :=
    R1 (fst xx) (fst yy) /\ R2 (snd xx) (snd yy).

  Lemma rr_wf: well_founded rr.
  Proof.
    unfold rr.
    intros (x', y').
    specialize (R1_wf x').
    specialize (R2_wf y').
    revert y' R2_wf.
    elim R1_wf. clear x' R1_wf.
    intros x' Hx HHx y' R2_wf.
    elim R2_wf. clear y' R2_wf.
    intros y' Hy HHy.
    constructor.
    intros (x, y) (HR1 & HR2).
    auto.
  Qed.

End Wf_Prod.

Section Ltsuffix2.

  Context {A B : Type}.

  Definition ltsuffix2 := rr (@ltsuffix A) (@ltsuffix B).

  Lemma ltsuffix2_wf : well_founded ltsuffix2.
  Proof rr_wf (@ltsuffix A) (@ltsuffix B) ltsuffix_wf ltsuffix_wf.

End Ltsuffix2.

Set Implicit Arguments.

Section Well_founded_FixPoint.

  Variable A : Type.
  Variable R : A -> A -> Prop.

  Hypothesis Rwf : well_founded R.

  Variable F : forall x:A, (forall y:A, R y x -> Prop) -> Prop.

  Local Notation Fix_F := (@Fix_F A R (fun _ => Prop) F).
  Local Notation Acc := (@Acc A R).

  Definition PFix (x:A) := Fix_F (Rwf x).

  Hypothesis
    F_ext :
    forall (x:A) (f g:forall y:A, R y x -> Prop),
      (forall (y:A) (p:R y x), f y p <-> g y p) -> (F f <-> F g).

  Lemma Fix_F_inv : forall (x:A) (r s:Acc x), Fix_F r <-> Fix_F s.
  Proof.
    intro x; induction (Rwf x); intros.
    rewrite <- (Fix_F_eq (fun _ => Prop) F r);
      rewrite <- (Fix_F_eq (fun _ => Prop) F s); intros.
    apply F_ext; auto.
  Qed.

  Lemma PFix_eq : forall x:A, PFix x <-> F (fun (y:A) (p:R y x) => PFix y).
  Proof.
    intro x; unfold PFix.
    rewrite <- Fix_F_eq.
    apply F_ext; intros.
    apply Fix_F_inv.
  Qed.

End Well_founded_FixPoint.

Unset Implicit Arguments.

Lemma eqlistA_eq_eq {A}:
  relation_equivalence (SetoidList.eqlistA (@eq A)) (eq).
Proof.
  intros xs1 xs2. now split; rewrite SetoidList.eqlistA_altdef, Forall2_eq.
Qed.

(** Tactics for inductions on lists *)

Ltac induction_list_tac e I l H :=
  match type of e with
    list ?A =>
    let Eq := fresh in
    let Eql := H in
    remember e as l eqn:Eq;
      assert (exists l', e = l' ++ l) as Eql by (exists (@nil A); simpl; auto);
      clear Eq; move Eql at top; induction l as I;
      [clear Eql|
       match goal with
         IH: (exists l', e = l' ++ ?l'') -> ?P,
             EQ: (exists l', e = l' ++ ?x::?xs) |- _ =>
         let l' := fresh l in
         let E := fresh in
         destruct EQ as [l' Eql];
           rewrite <-app_last_app in Eql;
           assert (exists l', e = l' ++ xs) as E by (exists (l' ++ [x]); auto);
           specialize (IH E); clear E
       end]
  end.

(* Tactic Notation "induction_list" constr(E) "as" simple_intropattern(I) "with" ident(l) "eq:" ident(H) := *)
(*   induction_list_tac E I l H. *)
Tactic Notation "induction_list" constr(E) "as" simple_intropattern(I) "with" ident(l) :=
  let H := fresh "H" l in
  induction_list_tac E I l H.
Tactic Notation "induction_list" constr(E) "as" simple_intropattern(I) :=
  let l := fresh "l" in
  induction_list E as I with l.
Tactic Notation "induction_list" constr(E) :=
  induction_list E as [|].
(* Tactic Notation "induction_list" constr(E) "with" ident(l) "eq:" ident(H) := *)
(*   induction_list E as [|] with l eq:H. *)
(* Tactic Notation "induction_list" constr(E) "as" simple_intropattern(I) "eq:" ident(H) := *)
(*   let l := fresh "l" in *)
(*   induction_list E as I with l eq:H. *)
Tactic Notation "induction_list" constr(E) "with" ident(l) :=
  induction_list E as [|] with l.
(* Tactic Notation "induction_list" constr(E) "eq:" ident(H) := *)
(*   let l := fresh "l" in *)
(*   induction_list E as [|] with l eq:H. *)

Tactic Notation "induction_list" ident(E) "as" simple_intropattern(I) "with" ident(l) :=
  let H := fresh "H" l in
  induction_list_tac E I l H.

(* Pos.min and Pos.max with fold *)
Section minmax.
  Fact min_fold_le : forall l x0,
    ((fold_right Pos.min x0 l) <= x0)%positive.
  Proof.
    induction l; intros x0; simpl in *.
    - apply Pos.le_refl.
    - etransitivity. apply Pos.le_min_r. auto.
  Qed.

  Fact min_fold_in : forall x l x0,
      List.In x l ->
      ((fold_right Pos.min x0 l) <= x)%positive.
  Proof.
    intros x l.
    induction l; intros x0 Hin; simpl in Hin.
    - inversion Hin.
    - destruct Hin as [?|Hin]; subst; simpl.
      + apply Pos.le_min_l.
      + etransitivity. apply Pos.le_min_r. auto.
  Qed.

  Fact min_fold_eq : forall x1 x2 l,
      Pos.le x1 x2 ->
      Pos.le (fold_right Pos.min x1 l) (fold_right Pos.min x2 l).
  Proof.
    induction l; intro Hle; simpl in *.
    - assumption.
    - apply Pos.min_le_compat_l; auto.
  Qed.

  Fact max_fold_ge : forall l x0,
      (x0 <= (fold_left Pos.max l x0))%positive.
  Proof.
    induction l; intros x0; simpl in *.
    - apply Pos.le_refl.
    - eapply Pos.le_trans.
      2: apply IHl.
      apply Pos.le_max_l.
  Qed.

  Fact max_fold_in : forall x l x0,
      List.In x l ->
      (x <= (fold_left Pos.max l x0))%positive.
  Proof.
    intros x l.
    induction l; intros x0 Hin; simpl in Hin.
    - inversion Hin.
    - destruct Hin as [?|Hin]; subst; simpl.
      + eapply Pos.le_trans.
        2: eapply max_fold_ge.
        apply Pos.le_max_r.
      + apply IHl; eauto.
  Qed.
End minmax.

Ltac singleton_length :=
  simpl in *;
  let Hsingl := fresh "Hsingl" in
  match goal with
  | H : length ?x = 1 |- _ =>
    destruct x eqn:Hsingl; simpl in *; try congruence
  end;
  let Hsingl := fresh "Hsingl" in
  match goal with
  | H : S (length ?x) = 1 |- _ =>
    destruct x eqn:Hsingl; simpl in *; try congruence;
    clear H; repeat rewrite app_nil_r in *
  end;
  subst.

Lemma Forall_concat' {A} : forall P (l : (list (list A))),
    Forall (fun x => length x = 1) l ->
    Forall P (concat l) ->
    Forall (Forall P) l.
Proof.
  induction l; intros Hlen Hf; [constructor|].
  - simpl in Hf. inv Hlen.
    apply Forall_app in Hf as [Hf1 Hf2].
    singleton_length.
    inv Hf1. repeat constructor; auto.
Qed.

Lemma Forall2_eq_concat2 {A} : forall (l1 : (list A)) (l2 : (list (list A))),
    Forall (fun x => length x = 1) l2 ->
    Forall2 eq l1 (concat l2) ->
    Forall2 (fun x y => [x] = y) l1 l2.
Proof.
  intros l1 l2; revert l1. induction l2; intros * Hlen Heq.
  - simpl in Heq. inv Heq. constructor.
  - inv Hlen. singleton_length. inv Heq.
    constructor; auto.
Qed.

Section map_filter.
  Context {A B : Type}.

  Variable (f : A -> option B).

  Fixpoint map_filter (ls : list A) : list B :=
    match ls with
    | [] => []
    | a::tl =>
      match f a with
      | Some b => b::(map_filter tl)
      | None => map_filter tl
      end
    end.

  Lemma map_filter_app : forall xs ys,
      map_filter (xs ++ ys) = map_filter xs ++ map_filter ys.
  Proof.
    induction xs; simpl; auto.
    intros ys.
    destruct (f a); eauto.
    rewrite <- app_comm_cons.
    f_equal; eauto.
  Qed.

  Lemma map_filter_In : forall x y xs,
      In x xs ->
      f x = Some y ->
      In y (map_filter xs).
  Proof.
    induction xs; intros Hin Hf; simpl; inv Hin.
    - rewrite Hf. left; auto.
    - destruct (f a); [right|]; auto.
  Qed.

  Lemma map_filter_In' : forall y xs,
      In y (map_filter xs) ->
      exists x, In x xs /\ f x = Some y.
  Proof.
    induction xs; intros Hin; simpl in *.
    - inv Hin.
    - destruct (f a) eqn:Hf.
      + simpl in Hin; destruct Hin as [Hin|Hin]; subst.
        * exists a; auto.
        * eapply IHxs in Hin as [x [Hin Hf']].
          exists x; auto.
      + eapply IHxs in Hin as [x [Hin Hf']].
        exists x; auto.
  Qed.
End map_filter.


Global Instance Permutation_map_filter_Proper {A B}:
  Proper ((@eq (A -> option B)) ==> Permutation (A:=A) ==> (Permutation (A:=B)))
         (@map_filter A B).
Proof.
  intros f g Heq l1 l2 Hperm; subst.
  induction Hperm; simpl; auto.
  - destruct (g x); auto.
  - destruct (g x), (g y); auto.
    apply perm_swap.
  - etransitivity; eauto.
Qed.

Section remove_member.
  Context {A B : Type}.
  Variable (eq_dec : forall x y : A, {x = y} + {x <> y}).

  Fixpoint remove_member (y : A) (xs : list (A * B)) : (list (A * B)) :=
    match xs with
    | [] => []
    | (x1, x2)::tl => if eq_dec y x1 then remove_member y tl
                    else (x1, x2)::remove_member y tl
    end.

  Lemma remove_member_incl : forall x xs,
      incl (remove_member x xs) xs.
  Proof.
    induction xs as [|[x1 x2] xs]; simpl.
    - apply incl_refl.
    - destruct (eq_dec x x1); subst.
      + apply incl_tl, IHxs.
      + apply incl_tl', IHxs.
  Qed.

  Lemma remove_member_nIn : forall x xs,
      ~InMembers x (remove_member x xs).
  Proof.
    induction xs as [|[x1 x2] xs]; simpl.
    - intro f; inv f.
    - destruct (eq_dec x x1); auto.
      intros [contra|contra]; congruence.
  Qed.

  Lemma remove_member_nIn_idem : forall x xs,
      ~InMembers x xs ->
      remove_member x xs = xs.
  Proof.
    induction xs as [|[x1 x2] xs]; intros Hnin; simpl; auto.
    destruct (eq_dec x x1); subst.
    - exfalso. apply Hnin.
      constructor; auto.
    - f_equal. apply IHxs.
      intro contra. apply Hnin. right; auto.
  Qed.

  Lemma remove_member_Perm : forall x y xs,
      NoDupMembers xs ->
      In (x, y) xs ->
      Permutation ((x, y)::(remove_member x xs)) xs.
  Proof.
    induction xs as [|[x1 x2] xs]; intros Hndup Hin; simpl.
    - inv Hin.
    - inv Hndup. inv Hin.
      + inv H. destruct eq_dec; subst; try congruence.
        apply perm_skip. rewrite remove_member_nIn_idem; auto.
      + specialize (IHxs H3 H).
        destruct eq_dec; subst; try congruence.
        * exfalso. apply In_InMembers in H; auto.
        * rewrite perm_swap. apply perm_skip; auto.
  Qed.

  Lemma remove_member_NoDupMembers : forall x xs,
      NoDupMembers xs ->
      NoDupMembers (remove_member x xs).
  Proof.
    induction xs as [|[x1 x2] xs]; intros Hndup; simpl; auto.
    inv Hndup.
    destruct (eq_dec x x1); subst; auto.
    constructor; auto.
    intro contra. apply H1.
    apply InMembers_In in contra as [y contra].
    apply In_InMembers with (b:=y).
    specialize (remove_member_incl x xs) as Hincl. apply Hincl; auto.
  Qed.

  Lemma remove_member_neq_In : forall x xs x' y',
      x' <> x ->
      In (x', y') xs ->
      In (x', y') (remove_member x xs).
  Proof.
    induction xs as [|[x1 y1] xs]; intros x' y' Hneq Hin; simpl.
    - inv Hin.
    - inv Hin.
      + inv H.
        destruct (eq_dec x x'); try congruence. left; auto.
      + specialize (IHxs _ _ Hneq H).
        destruct (eq_dec x x1); eauto.
        right; eauto.
  Qed.
End remove_member.
