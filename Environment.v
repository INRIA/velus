Require Import Coq.FSets.FMapPositive.
Require Import Coq.FSets.FMapFacts.
Require Import Coq.ZArith.ZArith.

Module Env.

  Include PositiveMap.
  Include PositiveMapAdditionalFacts.
  Module Props := FMapFacts.OrdProperties PositiveMap.

  Section Extra.

    Context {A: Type}.

    Definition adds (xs: list positive) (vs : list A) (m : t A) :=
      fold_right (fun (xv: positive * A) env =>
                    let (x , v) := xv in
                    add x v env) m (combine xs vs).

    Lemma add_comm:
      forall x y a b (m: t A),
        x <> y ->
        add x a (add y b m) = add y b (add x a m).
    Proof.
      induction x, y, m; simpl; intro Neq;
        ((f_equal; apply IHx; intro Eq; apply Neq; now inversion Eq) || now contradict Neq).
    Qed.

    Lemma in_dec:
      forall x (m: t A),
        In x m \/ ~In x m.
    Proof.
      intros; destruct (Props.P.F.In_dec m x); auto.
    Qed.

    Remark option_map_map:
      forall {A B C} (f: A -> B) (g: B -> C) o,
        option_map g (option_map f o) = option_map (fun x => g (f x)) o.
    Proof. now destruct o. Qed.

    Lemma xmapi_xmapi:
      forall {B C} (f: A -> B) (g: B -> C) (m: t A) x,
        xmapi (fun _ => g) (xmapi (fun _ => f) m x) x =
        xmapi (fun _ (x : A) => g (f x)) m x.
    Proof.
      induction m; intro; simpl; auto.
      f_equal; auto.
      apply option_map_map.
    Qed.

    Lemma map_map:
      forall {B C} (f: A -> B) (g: B -> C) (m: t A),
        map g (map f m) = map (fun x => g (f x)) m.
    Proof.
      unfold map, mapi; intros.
      apply xmapi_xmapi.
    Qed.

    Lemma find_gsso:
      forall x y xs (vs: list A) m,
        x <> y ->
        find x (adds (y :: xs) vs m) = find x (adds xs (tl vs) m).
    Proof.
      intros ** Hneq.
      unfold adds.
      destruct vs.
      - destruct xs; reflexivity.
      - simpl; rewrite gso; auto.
    Qed.

    Lemma find_gsss:
      forall x a xs (vs: list A) m,
        find x (adds (x :: xs) (a :: vs) m) = Some a.
    Proof.
      intros; unfold adds; apply gss.
    Qed.

    Lemma find_In_gsso:
      forall x xs (vs: list A) m,
        ~ List.In x xs ->
        find x (adds xs vs m) = find x m.
    Proof.
      intros ** Hin.
      revert vs; induction xs; intro; simpl; auto.
      rewrite find_gsso.
      - apply IHxs; intuition.
      - intro; apply Hin; now left.
    Qed.

    Lemma find_gssn:
      forall d1 (d2: A) n m xs vs x,
        n < length xs ->
        length xs = length vs ->
        NoDup xs ->
        nth n xs d1 = x ->
        find x (adds xs vs m) = Some (nth n vs d2).
    Proof.
      intros ** Hlen Hleq Hndup Hnth.
      unfold adds.
      remember (combine xs vs) as xvs eqn:Hxvs.
      assert (xs = fst (split xvs)) as Hxs
          by (now subst xvs; rewrite combine_split with (1:=Hleq)).
      assert (vs = snd (split xvs)) as Hvs
          by (now subst xvs; rewrite combine_split with (1:=Hleq)).
      subst xs vs.
      clear Hleq. revert n Hlen Hnth.
      induction xvs as [|xv xvs]; intros n Hlen Hnth.
      now inversion Hlen.
      simpl. destruct xv as [x' v'].
      simpl in *; destruct (split xvs); simpl in *.
      inversion_clear Hndup as [|? ? Hnin Hndup'].
      destruct n.
      - subst. now rewrite gss.
      - injection Hxvs; intro; subst.
        rewrite gso.
        + rewrite (IHxvs Hndup' eq_refl n); auto with arith.
        + pose proof (nth_In l d1 (Lt.lt_S_n _ _ Hlen)) as Hin.
          intro Hnth. rewrite Hnth in Hin. contradiction.
    Qed.

    Lemma NotIn_find_adds:
      forall x xs (o: option A) vs m,
        ~ List.In x xs ->
        find x m = o ->
        find x (adds xs vs m) = o.
    Proof.
      induction xs as [|xty xs]; auto.
      intros v vs S Hnin Hfind.
      apply Decidable.not_or in Hnin as [Hnin Hneq].
      rewrite find_gsso; auto.
    Qed.

    Lemma adds_cons_cons:
      forall xs x (a: A) vs m,
        ~ List.In x xs ->
        adds (x :: xs) (a :: vs) m = adds xs vs (add x a m).
    Proof.
      unfold adds.
      induction xs as [|x']; intros ** NotIn; simpl; auto.
      destruct vs as [|v']; simpl; auto.
      rewrite <-IHxs.
      - simpl.
        rewrite add_comm; auto.
        intro Eq.
        apply NotIn; subst.
        apply in_eq.
      - apply Decidable.not_or in NotIn as []; auto.
    Qed.

    Lemma adds_comm:
      forall xs x y (a b: A) vs m,
        ~ List.In x xs ->
        ~ List.In y xs ->
        x <> y ->
        adds (x :: y :: xs) (a :: b :: vs) m = adds (y :: x :: xs) (b :: a :: vs) m.
    Proof.
      intros.
      repeat rewrite adds_cons_cons; auto.
      - rewrite add_comm; auto.
      - intros []; contradiction.
      - intros [|]; congruence.
    Qed.

    Lemma adds_nil_nil:
      forall e,
        adds List.nil List.nil e = e.
    Proof. unfold adds; simpl; auto. Qed.

    Lemma In_find:
      forall x (s: t A),
        In x s <-> (exists v, find x s = Some v).
    Proof.
      setoid_rewrite Props.P.F.in_find_iff; reflexivity.
    Qed.

    Lemma elements_In:
      forall x (a: A) m,
        List.In (x, a) (elements m) -> In x m.
    Proof.
      intros ** Hin.
      apply elements_complete in Hin.
      apply In_find; eauto.
    Qed.

  End Extra.

End Env.
