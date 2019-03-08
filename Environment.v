Require Import Coq.FSets.FMapPositive.
Require Import Coq.FSets.FMapFacts.
Require Import Coq.ZArith.ZArith.

Module Env.

  Include PositiveMap.
  Include PositiveMapAdditionalFacts.
  Module Props := FMapFacts.OrdProperties PositiveMap.

  Section Extra.

    Context {A: Type}.

    Definition adds' (xs: list (positive * A)) (m: t A) :=
      fold_right (fun (xv: positive * A) env =>
                    let (x , v) := xv in
                    add x v env) m xs.

    Definition adds (xs: list positive) (vs : list A) (m : t A) :=
      adds' (combine xs vs) m.

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

    Lemma find_gsso':
      forall x y a xvs m,
        x <> y ->
        find x (adds' ((y, a) :: xvs) m) = find x (adds' xvs m).
    Proof.
      intros; simpl; rewrite gso; auto.
    Qed.

    Lemma find_gsso:
      forall x y xs (vs: list A) m,
        x <> y ->
        find x (adds (y :: xs) vs m) = find x (adds xs (tl vs) m).
    Proof.
      intros ** Hneq.
      unfold adds.
      destruct vs; simpl.
      - destruct xs; reflexivity.
      - rewrite gso; auto.
    Qed.

    Lemma find_gsss':
      forall x a xvs m,
        find x (adds' ((x, a) :: xvs) m) = Some a.
    Proof.
      intros; apply gss.
    Qed.

    Lemma find_gsss:
      forall x a xs (vs: list A) m,
        find x (adds (x :: xs) (a :: vs) m) = Some a.
    Proof.
      intros; unfold adds; apply gss.
    Qed.

    Lemma find_In_gsso':
      forall x xvs m,
        (forall a, ~ List.In (x, a) xvs) ->
        find x (adds' xvs m) = find x m.
    Proof.
      intros ** Hin.
      induction xvs as [|(y, a)]; simpl; auto.
      rewrite gso.
      - apply IHxvs; intros ??; eapply Hin; right; eauto.
      - intro; subst; eapply Hin; constructor; eauto.
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

    Lemma In_find_adds':
      forall x a xvs m,
        NoDup (List.map (@fst _ A) xvs) ->
        List.In (x, a) xvs ->
        find x (adds' xvs m) = Some a.
    Proof.
      unfold adds'.
      induction xvs as [|(y, b)]; simpl; try contradiction.
      inversion_clear 1 as [|?? Notin]; inversion_clear 1 as [E|]; simpl.
      - inversion E; subst; now rewrite gss.
      - rewrite gso; auto.
        intro; subst; apply Notin.
        eapply in_map_iff; exists (y, a); auto.
    Qed.

    Lemma In_find_adds:
      forall x a xs vs m,
        NoDup xs ->
        List.In (x, a) (combine xs vs) ->
        find x (adds xs vs m) = Some a.
    Proof.
      unfold adds.
      induction xs as [|x'], vs as [|v']; simpl; try contradiction.
      inversion_clear 1 as [|?? Notin]; inversion_clear 1 as [E|]; simpl.
      - inversion E; subst; now rewrite gss.
      - rewrite gso; auto.
        intro; subst; apply Notin.
        eapply in_combine_l; eauto.
    Qed.

    Lemma adds_nil_nil':
      forall e,
        adds' List.nil e = e.
    Proof. simpl; auto. Qed.

    Lemma adds_nil_nil:
      forall e,
        adds List.nil List.nil e = e.
    Proof. simpl; auto. Qed.

    Lemma adds_nil_l:
      forall e vs,
        adds List.nil vs e = e.
    Proof. simpl; auto. Qed.

    Lemma adds_nil_r:
      forall e xs,
        adds xs List.nil e = e.
    Proof.
      unfold adds; destruct xs; simpl; auto.
    Qed.

    Lemma find_adds_In':
      forall x a xvs m,
        NoDup (List.map (@fst _ A) xvs) ->
        find x m = None ->
        find x (adds' xvs m) = Some a ->
        List.In (x, a) xvs.
    Proof.
      unfold adds'.
      induction xvs as [|(y, b)]; simpl; try congruence.
      inversion_clear 1; intros ** Find.
      destruct (Pos.eq_dec x y).
      - subst; rewrite gss in Find; inversion Find; auto.
      - rewrite gso in Find; auto.
        right; eauto.
    Qed.

    Lemma find_adds_In_spec':
      forall x a xvs m,
        NoDup (List.map (@fst _ A) xvs) ->
        find x (adds' xvs m) = Some a ->
        List.In (x, a) xvs
        \/ ((forall a, ~ List.In (x, a) xvs)
           /\ find x m = Some a).
    Proof.
      unfold adds'.
      induction xvs as [|(y, c)]; simpl; auto.
      inversion_clear 1; intros ** Find.
      destruct (Pos.eq_dec x y).
      - subst; rewrite gss in Find; inversion Find; auto.
      - rewrite gso in Find; auto.
        edestruct IHxvs; eauto.
        right; intuition; eauto.
        congruence.
    Qed.

    Lemma find_adds_In:
      forall x v xs vs m,
        NoDup xs ->
        find x m = None ->
        find x (adds xs vs m) = Some v ->
        List.In (x, v) (combine xs vs).
    Proof.
      unfold adds.
      induction xs as [|x'], vs as [|v']; simpl; try congruence.
      inversion_clear 1; intros ** Find.
      destruct (Pos.eq_dec x x').
      - subst; rewrite gss in Find; inversion Find; auto.
      - rewrite gso in Find; auto.
        right; eauto.
    Qed.

    Lemma find_adds_In_spec:
      forall x v xs vs m,
        NoDup xs ->
        find x (adds xs vs m) = Some v ->
        List.In (x, v) (combine xs vs)
        \/ ((forall v, ~ List.In (x, v) (combine xs vs))
           /\ find x m = Some v).
    Proof.
      unfold adds.
      induction xs as [|x'], vs as [|v']; simpl; auto.
      inversion_clear 1; intros ** Find.
      destruct (Pos.eq_dec x x').
      - subst; rewrite gss in Find; inversion Find; auto.
      - rewrite gso in Find; auto.
        edestruct IHxs; eauto.
        right; intuition; eauto.
        congruence.
    Qed.

    Lemma NotIn_find_adds':
      forall x xvs (o: option A) m,
        (forall a, ~ List.In (x, a) xvs) ->
        find x m = o ->
        find x (adds' xvs m) = o.
    Proof.
      induction xvs as [|(y, a)]; auto.
      intros ** Hnin Hfind.
      rewrite find_gsso'.
      - apply IHxvs; auto.
        intros ??; eapply Hnin; right; eauto.
      - intro; subst; eapply Hnin; constructor; eauto.
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

    Lemma adds_cons_cons':
      forall xvs x (a: A) m,
        (forall a, ~ List.In (x, a) xvs) ->
        adds' ((x, a) :: xvs) m = adds' xvs (add x a m).
    Proof.
      unfold adds'.
      induction xvs as [|(y, b)]; intros ** NotIn; simpl; auto.
      rewrite <-IHxvs.
      - simpl.
        rewrite add_comm; auto.
        intro; subst; eapply NotIn; constructor; eauto.
      - intros ??; eapply NotIn; right; eauto.
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

    Lemma adds_comm':
      forall xvs x y (a b: A) m,
        (forall a, ~ List.In (x, a) xvs) ->
        (forall b, ~ List.In (y, b) xvs) ->
        x <> y ->
        adds' ((x, a) :: (y, b) :: xvs) m = adds' ((y, b) :: (x, a) :: xvs) m.
    Proof.
      intros ** NotInx NotIny ?.
      repeat rewrite adds_cons_cons'; auto.
      - rewrite add_comm; auto.
      - intros ? [E|?]; try inversion E; try contradiction.
        eapply NotIny; eauto.
      - intros ? [|?]; try congruence.
        eapply NotInx; eauto.
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

    Lemma adds_add_comm':
      forall xvs x (a: A) m,
        (forall a, ~ List.In (x, a) xvs) ->
        add x a (adds' xvs m) = adds' xvs (add x a m).
    Proof.
      induction xvs as [|(y, b)]; simpl; auto.
      intros ** Nin; rewrite <-IHxvs.
      - apply add_comm.
        intro; subst.
        eapply Nin; left; eauto.
      - intros ** Hin.
        eapply Nin; eauto.
    Qed.

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

    Lemma Equiv_empty:
      forall m eq,
        (forall x, find x m = None) ->
        Equiv eq m (empty A).
    Proof.
      intros ** Spec.
      constructor.
      - setoid_rewrite Props.P.F.empty_in_iff; setoid_rewrite In_find.
        split; try contradiction.
        intros (?& ?); congruence.
      - setoid_rewrite Props.P.F.empty_mapsto_iff; contradiction.
    Qed.

  End Extra.

End Env.
