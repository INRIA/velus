From Coq Require Import FSets.FMapPositive.
From Coq Require Import FSets.FMapFacts.
From Coq Require Import ZArith.ZArith.

From Velus Require Import Common.

Module Env.

  Include PositiveMap.
  Include PositiveMapAdditionalFacts.
  Module Props := FMapFacts.OrdProperties PositiveMap.

  Section Extra.

    Context {A: Type}.

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

    (* fold_left is preferred over fold_right when used in executable code,
       when fold_right is easier to work with in proofs *)
    Definition adds_with {B} (f: B -> A) (xs: list (positive * B)) (m: t A) : t A :=
      fold_left (fun env (xv: positive * B) =>
                   let (x, v) := xv in
                   add x (f v) env) xs m.

    Definition from_list_with {B} (f: B -> A) (xs: list (positive * B)) : t A :=
      adds_with f xs (@empty A).

    Definition adds' (xs: list (positive * A)) (m: t A) : t A :=
      fold_left (fun env (xv: positive * A) =>
                   let (x , v) := xv in
                   add x v env) xs m.

    Definition from_list (xs: list (positive * A)) : t A :=
      adds' xs (@empty A).

    Definition adds_opt (xs: list positive) (vos : list (option A)) (e : t A) : t A :=
      fold_right (fun (xvo: positive * option A) env =>
                    match xvo with
                    | (x, Some v) => add x v env
                    | _ => env end) e (combine xs vos).

    Definition updates (xs: list positive) (vos : list (option A)) (m : t A) : t A :=
      fold_right (fun (xvo: positive * option A) env =>
                    match xvo with
                    | (x, Some v) => add x v env
                    | (x, None) => remove x env
                    end) m (combine xs vos).

    Definition adds (xs: list positive) (vs : list A) (m : t A) : t A :=
      adds' (combine xs vs) m.

    Lemma adds'_is_adds_with_identity:
      forall xs m,
        adds' xs m = adds_with (fun x => x) xs m.
    Proof. reflexivity. Qed.

    Section AddsWith.

      Context {B: Type}.
      Variable f: B -> A.

      Lemma adds_with_app:
        forall xs ys s,
          adds_with f ys (adds_with f xs s) = adds_with f (xs ++ ys) s.
      Proof.
        induction xs as [|x xs IH]; auto.
        now setoid_rewrite IH.
      Qed.

      Lemma find_adds_with_spec:
        forall x xvs s,
          (InMembers x xvs ->
           forall s', find x (adds_with f xvs s) = find x (adds_with f xvs s'))
          /\ (~ InMembers x xvs ->
             find x (adds_with f xvs s) = find x s).
      Proof.
        induction xvs as [|(x', v')].
        - intuition; destruct H; contradiction.
        - split.
          + simpl; intros [?|Hin].
            *{ subst.
               destruct (InMembers_dec x xvs) as [|Notin]; try apply Pos.eq_dec.
               - intros; eapply IHxvs; auto.
               - intro.
                 pose proof Notin as Notin'.
                 eapply IHxvs in Notin; rewrite Notin.
                 eapply IHxvs in Notin'; rewrite Notin'.
                 now rewrite 2 gss.
             }
            * intros; eapply IHxvs; auto.
          + rewrite NotInMembers_cons; simpl; intros (Notin &?).
            eapply IHxvs in Notin; rewrite Notin.
            apply gso; auto.
      Qed.

      Lemma gsso_with:
      forall x xvs m,
        ~ InMembers x xvs ->
        find x (adds_with f xvs m) = find x m.
      Proof. apply find_adds_with_spec. Qed.

      Lemma find_adds_with_spec_Some:
        forall xvs x a m,
          find x (adds_with f xvs m) = Some a ->
          (exists b, List.In (x, b) xvs /\ f b = a)
          \/ (~ InMembers x xvs /\ find x m = Some a).
      Proof.
        induction xvs as [|(x', v') xs IH]; simpl. now intuition.
        intros * Hfind. apply IH in Hfind as [(?&?&?)|(Hnim & Hfind)]; eauto.
        destruct (Pos.eq_dec x' x).
        - subst. rewrite gss in Hfind.
          injection Hfind. intro; subst; eauto.
        - rewrite gso in Hfind; intuition.
      Qed.

      Lemma find_gsso_with:
        forall xvs x y a m,
          x <> y ->
          find x (adds_with f ((y, a) :: xvs) m) = find x (adds_with f xvs m).
      Proof.
        intros; simpl.
        destruct (InMembers_dec x xvs) as [|Notin]; try apply Pos.eq_dec.
        - now apply find_adds_with_spec.
        - rewrite 2 gsso_with; auto.
          now apply gso.
      Qed.

      Lemma find_gsss_with:
      forall x a xvs m,
        ~ InMembers x xvs ->
        find x (adds_with f ((x, a) :: xvs) m) = Some (f a).
      Proof.
        intros; simpl.
        rewrite (proj2 (find_adds_with_spec _ _ _)); auto.
        apply gss.
      Qed.

      Lemma In_find_adds_with:
        forall x a xvs m,
          NoDupMembers xvs ->
          List.In (x, a) xvs ->
          find x (adds_with f xvs m) = Some (f a).
      Proof.
        induction xvs as [|(y, b)]; simpl; try contradiction.
        inversion_clear 1 as [|?? Notin]; inversion_clear 1 as [E|]; simpl; auto.
        inv E. rewrite gsso_with, gss; auto.
      Qed.

      Lemma adds_with_cons:
        forall xvs x b m,
          ~ InMembers x xvs ->
          adds_with f ((x, b) :: xvs) m = add x (f b) (adds_with f xvs m).
      Proof.
        unfold adds_with.
        induction xvs as [|(y, b')]; intros * NotIn; simpl; auto.
        rewrite NotInMembers_cons in NotIn. destruct NotIn.
        rewrite <-IHxvs; auto. simpl.
        rewrite add_comm; auto.
      Qed.

    End AddsWith.

    Lemma adds'_app:
      forall xs ys s,
        adds' ys (adds' xs s) = adds' (xs ++ ys) s.
    Proof.
      intros; setoid_rewrite adds'_is_adds_with_identity;
        rewrite (adds'_is_adds_with_identity xs).
      apply adds_with_app.
    Qed.

    Lemma gsso':
      forall x xvs m,
        ~ InMembers x xvs ->
        find x (adds' xvs m) = find x m.
    Proof.
      setoid_rewrite adds'_is_adds_with_identity.
      apply gsso_with.
    Qed.

    Corollary gsso:
      forall x xs (vs: list A) m,
        ~ List.In x xs ->
        find x (adds xs vs m) = find x m.
    Proof.
      intros; unfold adds.
      apply gsso'.
      intros * Hin; apply InMembers_In_combine in Hin; auto.
    Qed.

    Lemma from_list_find_In:
      forall xvs x a,
        find x (from_list xvs) = Some a ->
        List.In (x, a) xvs.
    Proof.
      unfold from_list. setoid_rewrite adds'_is_adds_with_identity.
      intros * Find; apply find_adds_with_spec_Some in Find as [(?&?&?)|(?& Find)]; subst; auto.
      rewrite gempty in Find; discriminate.
    Qed.

    Lemma find_gsso':
      forall xvs x y a m,
        x <> y ->
        find x (adds' ((y, a) :: xvs) m) = find x (adds' xvs m).
    Proof.
      intros; setoid_rewrite adds'_is_adds_with_identity.
      apply find_gsso_with; auto.
    Qed.

    Corollary find_gsso:
      forall x y xs (vs: list A) m,
        x <> y ->
        find x (adds (y :: xs) vs m) = find x (adds xs (tl vs) m).
    Proof.
      intros * Hneq.
      unfold adds.
      destruct vs.
      - destruct xs; reflexivity.
      - simpl combine; now apply find_gsso'.
    Qed.

    Lemma find_gsss':
      forall x a xvs m,
        ~ InMembers x xvs ->
        find x (adds' ((x, a) :: xvs) m) = Some a.
    Proof.
      intros; setoid_rewrite adds'_is_adds_with_identity.
      apply find_gsss_with; auto.
    Qed.

    Corollary find_gsss:
      forall x a xs (vs: list A) m,
        ~ List.In x xs ->
        find x (adds (x :: xs) (a :: vs) m) = Some a.
    Proof.
      intros; unfold adds; simpl combine; apply find_gsss'.
      intros Hin; apply InMembers_In_combine in Hin; auto.
    Qed.

    Lemma In_find_adds':
      forall x a xvs m,
        NoDupMembers xvs ->
        List.In (x, a) xvs ->
        find x (adds' xvs m) = Some a.
    Proof.
      intros; rewrite adds'_is_adds_with_identity.
      erewrite In_find_adds_with; eauto.
    Qed.

    Corollary In_find_adds:
      forall x a xs vs m,
        NoDup xs ->
        List.In (x, a) (combine xs vs) ->
        find x (adds xs vs m) = Some a.
    Proof.
      unfold adds; intros.
      apply In_find_adds'; auto.
      apply NoDup_NoDupMembers_combine; auto.
    Qed.

    Lemma In_adds_spec':
      forall x xvs (m: t A),
        In x (adds' xvs m) <-> (InMembers x xvs \/ In x m).
    Proof.
      induction xvs as [|(x', v')]; simpl.
      - firstorder.
      - intro; rewrite IHxvs, Props.P.F.add_in_iff.
        intuition.
    Qed.

    Corollary In_adds_spec:
      forall x xs vs (m: t A),
        length xs = length vs ->
        (In x (adds xs vs m) <-> (List.In x xs \/ In x m)).
    Proof.
      unfold adds; intros.
      rewrite In_adds_spec', <-In_InMembers_combine; auto; intuition.
    Qed.

    (* Lemma adds_nil_nil': *)
    (*   forall e, *)
    (*     adds' List.nil e = e. *)
    (* Proof. simpl; auto. Qed. *)

    Lemma adds_opt_nil_nil:
      forall e,
        adds_opt List.nil List.nil e = e.
    Proof. simpl; auto. Qed.

    Lemma adds_nil_nil:
      forall e,
        adds List.nil List.nil e = e.
    Proof. simpl; auto. Qed.

    Lemma adds_nil_l:
      forall e vs,
        adds List.nil vs e = e.
    Proof. simpl; auto. Qed.

    Lemma updates_nil_l:
      forall e vs,
        updates List.nil vs e = e.
    Proof. simpl; auto. Qed.

    (* Lemma adds_nil_r: *)
    (*   forall e xs, *)
    (*     adds xs List.nil e = e. *)
    (* Proof. *)
    (*   unfold adds; destruct xs; simpl; auto. *)
    (* Qed. *)

    (* Lemma find_adds_In': *)
    (*   forall x a xvs m, *)
    (*     NoDupMembers xvs -> *)
    (*     find x m = None -> *)
    (*     find x (adds' xvs m) = Some a -> *)
    (*     List.In (x, a) xvs. *)
    (* Proof. *)
    (*   induction xvs as [|(y, b)]. *)
    (*   - simpl; congruence. *)
    (*   - inversion_clear 1; intros * Find. *)
    (*     destruct (Pos.eq_dec x y). *)
    (*     + subst; simpl in *; rewrite gsso', gss in Find; auto; inv Find; auto. *)
    (*     + rewrite find_gsso' in Find; auto. *)
    (*       simpl; eauto. *)
    (* Qed. *)

    (* Lemma find_adds_In: *)
    (*   forall x v xs vs m, *)
    (*     NoDup xs -> *)
    (*     find x m = None -> *)
    (*     find x (adds xs vs m) = Some v -> *)
    (*     List.In (x, v) (combine xs vs). *)
    (* Proof. *)
    (*   unfold adds. *)
    (*   intros; eapply find_adds_In'. *)
    (*   induction xs as [|x'], vs as [|v']; simpl; try congruence. *)
    (*   inversion_clear 1; intros * Find. *)
    (*   destruct (Pos.eq_dec x x'). *)
    (*   - subst; rewrite gss in Find; inversion Find; auto. *)
    (*   - rewrite gso in Find; auto. *)
    (*     right; eauto. *)
    (* Qed. *)

    (* Lemma find_adds_In_spec: *)
    (*   forall x v xs vs m, *)
    (*     NoDup xs -> *)
    (*     find x (adds xs vs m) = Some v -> *)
    (*     List.In (x, v) (combine xs vs) *)
    (*     \/ ((forall v, ~ List.In (x, v) (combine xs vs)) *)
    (*        /\ find x m = Some v). *)
    (* Proof. *)
    (*   unfold adds. *)
    (*   induction xs as [|x'], vs as [|v']; simpl; auto. *)
    (*   inversion_clear 1; intros * Find. *)
    (*   destruct (Pos.eq_dec x x'). *)
    (*   - subst; rewrite gss in Find; inversion Find; auto. *)
    (*   - rewrite gso in Find; auto. *)
    (*     edestruct IHxs; eauto. *)
    (*     right; intuition; eauto. *)
    (*     congruence. *)
    (* Qed. *)

    Lemma adds'_cons:
      forall xvs x (a: A) m,
        ~ InMembers x xvs ->
        adds' ((x, a) :: xvs) m = add x a (adds' xvs m).
    Proof.
      setoid_rewrite adds'_is_adds_with_identity.
      intros; apply adds_with_cons; auto.
    Qed.

    Corollary adds_cons_cons:
      forall xs x (a: A) vs m,
        ~ List.In x xs ->
        adds (x :: xs) (a :: vs) m = add x a (adds xs vs m).
    Proof.
      unfold adds; intros.
      simpl combine; eapply adds'_cons.
      intros * Hin; apply InMembers_In_combine in Hin; auto.
    Qed.

    (* Lemma adds_comm': *)
    (*   forall xvs x y (a b: A) m, *)
    (*     (forall a, ~ List.In (x, a) xvs) -> *)
    (*     (forall b, ~ List.In (y, b) xvs) -> *)
    (*     x <> y -> *)
    (*     adds' ((x, a) :: (y, b) :: xvs) m = adds' ((y, b) :: (x, a) :: xvs) m. *)
    (* Proof. *)
    (*   intros * NotInx NotIny ?. *)
    (*   repeat rewrite adds_cons_cons'; auto. *)
    (*   - rewrite add_comm; auto. *)
    (*   - intros ? [E|?]; try inversion E; try contradiction. *)
    (*     eapply NotIny; eauto. *)
    (*   - intros ? [|?]; try congruence. *)
    (*     eapply NotInx; eauto. *)
    (* Qed. *)

    (* Lemma adds_comm: *)
    (*   forall xs x y (a b: A) vs m, *)
    (*     ~ List.In x xs -> *)
    (*     ~ List.In y xs -> *)
    (*     x <> y -> *)
    (*     adds (x :: y :: xs) (a :: b :: vs) m = adds (y :: x :: xs) (b :: a :: vs) m. *)
    (* Proof. *)
    (*   intros. *)
    (*   repeat rewrite adds_cons_cons; auto. *)
    (*   - rewrite add_comm; auto. *)
    (*   - intros []; contradiction. *)
    (*   - intros [|]; congruence. *)
    (* Qed. *)

    (* Lemma adds_add_comm': *)
    (*   forall xvs x (a: A) m, *)
    (*     (forall a, ~ List.In (x, a) xvs) -> *)
    (*     add x a (adds' xvs m) = adds' xvs (add x a m). *)
    (* Proof. *)
    (*   induction xvs as [|(y, b)]; simpl; auto. *)
    (*   intros * Nin; rewrite <-IHxvs. *)
    (*   - apply add_comm. *)
    (*     intro; subst. *)
    (*     eapply Nin; left; eauto. *)
    (*   - intros * Hin. *)
    (*     eapply Nin; eauto. *)
    (* Qed. *)

    Lemma In_find:
      forall x (s: t A),
        In x s <-> (exists v, find x s = Some v).
    Proof.
      setoid_rewrite Props.P.F.in_find_iff; reflexivity.
    Qed.

    Corollary find_In:
      forall x (s: t A) v,
        find x s = Some v ->
        In x s.
    Proof.
      intros; rewrite In_find; eauto.
    Qed.

    Lemma elements_In:
      forall x (a: A) m,
        List.In (x, a) (elements m) -> In x m.
    Proof.
      intros * Hin.
      apply elements_complete in Hin.
      apply In_find; eauto.
    Qed.

    Lemma Env_equiv_orel {R : relation A} :
      forall S T, Env.Equiv R S T <-> (forall x, (orel R) (Env.find x S) (Env.find x T)).
    Proof.
      split; [intros (I & M)|intros LR].
      - intros x.
        destruct (Env.find x S) as [v|] eqn:FS.
        + pose proof (Env.find_2 _ _ FS) as MS.
          apply find_In, I in FS.
          rewrite In_find in FS; destruct FS as (v' & FT).
          pose proof (Env.find_2 _ _ FT) as MT.
          specialize (M _ _ _ MS MT).
          right; eauto.
        + apply Env.Props.P.F.not_find_in_iff in FS.
          assert (~Env.In x T) as FT
              by (intro HH; apply I in HH; auto).
          apply Env.Props.P.F.not_find_in_iff in FT as ->.
          now left.
      - split.
        + intro x. specialize (LR x) as [(LR1 & LR2)|(v1 & v2 & LR1 & LR2 & LR3)].
          * apply Env.Props.P.F.not_find_in_iff in LR1.
            apply Env.Props.P.F.not_find_in_iff in LR2.
            intuition.
          * apply find_In in LR1.
            apply find_In in LR2.
            intuition.
        + intros x v v' MS MT.
          apply find_1 in MS.
          apply find_1 in MT.
          specialize (LR x) as [(LR1 & LR2)|(v1 & v2 & LR1 & LR2 & LR3)].
          * rewrite MS in LR1; discriminate.
          * rewrite MS in LR1. rewrite MT in LR2.
            now inv LR1; inv LR2.
    Qed.

    Lemma NoDupMembers_NoDupA:
      forall {A} (xs: list (positive * A)),
        NoDupMembers xs <-> SetoidList.NoDupA (@eq_key A) xs.
    Proof.
      induction xs as [|[x y] xs IH].
      - split; intro HH; auto using NoDupMembers_nil.
      - destruct IH.
        split; intro HH; inv HH; constructor; auto.
        + rewrite SetoidList.InA_alt.
          destruct 1 as (xy & Heq & Hin).
          unfold eq_key, E.eq in Heq.
          simpl in Heq.
          apply H3, fst_InMembers.
          rewrite Heq.
          auto using in_map.
        + match goal with H:~SetoidList.InA _ _ _ |- _
                          => rename H into Hsl end.
          rewrite SetoidList.InA_alt in Hsl.
          intro Hin. apply Hsl.
          apply InMembers_In in Hin.
          destruct Hin as (w, Hin).
          exists (x, w); split; auto.
          reflexivity.
    Qed.

    Lemma InA_map_fst:
      forall {A} x xs y,
        SetoidList.InA eq x (List.map (@fst positive A) xs)
        <-> SetoidList.InA (@eq_key A) (x, y) xs.
    Proof.
      induction xs as [|(i, a) xs IH]; simpl; split; try (now inversion 1).
      - inversion 1 as [|? ? HH]; subst. now constructor.
        apply (IH y) in HH. inv H; now constructor 2.
      - inversion 1 as [|? ? HH]; subst. now constructor.
        apply IH in HH. inv H; now constructor 2.
    Qed.

    Lemma NoDupA_map_fst:
      forall {A} xs,
        SetoidList.NoDupA eq (List.map (@fst positive A) xs)
        <-> SetoidList.NoDupA (@eq_key A) xs.
    Proof.
      induction xs as [|(i, a) xs IH]; simpl.
      - split; inversion 1; auto.
      - split; inversion 1 as [|? ? Hni Hnd];
          subst; constructor; try (apply IH; auto).
        + rewrite InA_map_fst in Hni; eassumption.
        + rewrite InA_map_fst; eassumption.
    Qed.

    Lemma NoDupMembers_elements:
      forall m,
        NoDupMembers (@elements A m).
    Proof.
      intros.
      apply NoDupMembers_NoDupA.
      apply elements_3w.
    Qed.

    Lemma elements_add:
      forall x (v: A) m,
        ~ In x m ->
        Permutation.Permutation (elements (add x v m)) ((x,v) :: elements m).
    Proof.
      intros * Hin.
      apply Permutation.NoDup_Permutation.
      - apply NoDupMembers_NoDup, NoDupMembers_elements.
      - constructor.
        2:now apply NoDupMembers_NoDup, NoDupMembers_elements.
        intro Hele.
        apply elements_complete in Hele.
        apply Hin; apply In_find; eauto.
      - destruct x0 as (x', v'). split; intro HH.
        + apply elements_complete in HH.
          destruct (Pos.eq_dec x' x).
      * subst.
        rewrite gss in HH.
        injection HH; intro; subst.
        now constructor.
      * rewrite gso in HH; auto.
        constructor 2.
        apply elements_correct with (1:=HH).
        + apply in_inv in HH.
          destruct HH as [He|Hin'].
          * inv He. apply elements_correct, gss.
          * apply elements_correct.
        destruct (Pos.eq_dec x' x).
        2:now rewrite gso; auto using elements_complete.
        subst.
        contradiction Hin.
        apply elements_complete in Hin'.
        apply In_find; eauto.
    Qed.

    Lemma In_Members:
      forall x (m : t A),
        In x m <-> InMembers x (elements m).
    Proof.
      split; intro HH.
      - rewrite In_find in HH.
        destruct HH as (v & HH).
        apply In_InMembers with (b:=v).
        now apply elements_correct.
      - apply InMembers_In in HH.
        destruct HH as (v & HH).
        rewrite In_find.
        eauto using elements_complete.
    Qed.

    Lemma Equiv_empty:
      forall m eq,
        (forall x, find x m = None) ->
        Equiv eq m (empty A).
    Proof.
      intros * Spec.
      constructor.
      - setoid_rewrite Props.P.F.empty_in_iff; setoid_rewrite In_find.
        split; try contradiction.
        intros (?& ?); congruence.
      - setoid_rewrite Props.P.F.empty_mapsto_iff; contradiction.
    Qed.

    Lemma find_adds_opt_spec_Some:
      forall xs vs x a m,
        length xs = length vs ->
        find x (adds_opt xs vs m) = Some a ->
        List.In (x, Some a) (combine xs vs)
        \/ find x m = Some a.
    Proof.
      unfold adds_opt.
      induction xs as [|x'], vs as [|v']; simpl; auto; try discriminate.
      intros * Length Find; inv Length.
      destruct v'.
      - destruct (Pos.eq_dec x x') as [|].
        + subst; rewrite gss in Find; inv Find; auto.
        + rewrite gso in Find; auto.
          apply IHxs in Find as [|()]; auto.
      - apply IHxs in Find as [|]; auto.
    Qed.

    Lemma find_gsso_opt:
      forall x x' xs (vs: list (option A)) S,
        x <> x' ->
        find x (adds_opt (x' :: xs) vs S) = find x (adds_opt xs (tl vs) S).
    Proof.
      intros * Hneq.
      unfold adds_opt.
      destruct vs. now destruct xs; auto.
      destruct o; simpl; auto.
      now rewrite gso; auto.
    Qed.

    Lemma find_gsss_opt:
      forall x v xs (vs: list (option A)) S,
        find x (adds_opt (x :: xs) (Some v :: vs) S) = Some v.
    Proof.
      intros. unfold adds_opt. apply gss.
    Qed.

    Lemma find_In_gsso_opt:
      forall x ys (vs: list (option A)) env,
        ~ List.In x ys ->
        find x (adds_opt ys vs env) = find x env.
    Proof.
      intros x ys vs env Hin.
      revert vs; induction ys; intro vs; simpl; auto.
      rewrite find_gsso_opt.
      - apply IHys. intuition.
      - intro. apply Hin. now left.
  Qed.

    Lemma adds_opt_cons_cons:
      forall xs x (v: A) vs e,
        adds_opt (x :: xs) (Some v :: vs) e = add x v (adds_opt xs vs e).
    Proof.
      induction xs as [|x']; intros; simpl; auto.
    Qed.

  Lemma adds_opt_cons_cons':
    forall xs x (v: A) vs e,
      ~ List.In x xs ->
      adds_opt (x :: xs) (Some v :: vs) e = adds_opt xs vs (add x v e).
  Proof.
    unfold adds_opt.
    induction xs as [|x']; intros * NotIn; simpl; auto.
    destruct vs as [|v']; simpl; auto.
    rewrite <-IHxs; auto.
    - simpl. destruct v'; auto.
      rewrite add_comm; auto.
      intro; subst; apply NotIn; constructor; auto.
    - intro; apply NotIn; right; auto.
  Qed.

  Lemma adds_opt_cons_cons_None:
    forall xs x (vs: list (option A)) e,
      adds_opt (x :: xs) (None :: vs) e = adds_opt xs vs e.
  Proof. auto. Qed.

  Lemma In_adds_opt_In:
    forall xs vos x,
      In x (adds_opt xs vos (empty _)) ->
      List.In x xs.
  Proof.
    intros xs.
    setoid_rewrite Props.P.F.in_find_iff.
    induction xs as [|y xs' IH].
    - intros vos x; unfold adds_opt.
      destruct vos; simpl; rewrite gempty; intuition.
    - intros vos x.
      destruct vos as [|vo vos].
      + now unfold adds_opt; simpl; rewrite gempty; intuition.
      + destruct (Pos.eq_dec x y).
        *{ subst; destruct vo.
           - now rewrite find_gsss_opt; intuition.
           - now rewrite adds_opt_cons_cons_None; intro HH; apply IH in HH; constructor 2.
         }
        * rewrite find_gsso_opt; auto.
          intro HH; apply IH in HH.
          now constructor 2.
  Qed.

  Lemma updates_is_adds:
    forall xs vs (m: t A),
      NoDup xs ->
      updates xs (List.map (@Some A) vs) m = adds xs vs m.
  Proof.
    unfold updates, adds; intros * Hndp.
    revert vs.
    induction xs, vs; simpl; inversion_clear Hndp as [|?? Notin]; auto.
    rewrite IHxs, <-adds'_cons; simpl; auto.
    intro; eapply Notin, InMembers_In_combine; eauto.
  Qed.

  Lemma adds_opt_is_adds:
    forall xs vs (m: t A),
      NoDup xs ->
      adds_opt xs (List.map (@Some A) vs) m = adds xs vs m.
  Proof.
    unfold adds_opt, adds; intros * Hndp.
    revert vs.
    induction xs, vs; simpl; inversion_clear Hndp as [|?? Notin]; auto.
    rewrite IHxs, <-adds'_cons; simpl; auto.
    intro; eapply Notin, InMembers_In_combine; eauto.
  Qed.

  Lemma find_guso:
      forall x x' xs (vs: list (option A)) m,
        x <> x' ->
        find x (updates (x' :: xs) vs m) = find x (updates xs (tl vs) m).
    Proof.
      intros * Hneq.
      unfold updates.
      destruct vs. now destruct xs; auto.
      destruct o; simpl.
      + now rewrite gso; auto.
      + now rewrite gro; auto.
    Qed.

    Lemma find_guss:
      forall x v xs (vs: list (option A)) m,
        find x (updates (x :: xs) (Some v :: vs) m) = Some v.
    Proof.
      intros; unfold updates; apply gss.
    Qed.

    Lemma find_gurs:
      forall x xs (vs: list (option A)) m,
        find x (updates (x :: xs) (None :: vs) m) = None.
    Proof.
      intros; unfold updates; apply grs.
    Qed.

    Lemma updates_cons_cons_None:
      forall x xs (vos : list (option A)) m,
        updates (x :: xs) (None :: vos) m = remove x (updates xs vos m).
    Proof. now unfold updates. Qed.

    Lemma find_In_guso:
      forall x ys (vs: list (option A)) env,
        ~ List.In x ys ->
        find x (updates ys vs env) = find x env.
    Proof.
      intros x ys vs env Hin.
      revert vs; induction ys; intro vs; simpl; auto.
      rewrite find_guso.
      - apply IHys. intuition.
      - intro. apply Hin. now left.
    Qed.

    Lemma updates_cons_cons:
      forall xs x (vo: option A) vs e,
        updates (x :: xs) (vo :: vs) e =
        (match vo with None => remove x | Some v => add x v end)
          (updates xs vs e).
    Proof.
      induction xs as [|x']; intros; destruct vo; simpl; auto.
    Qed.

    Lemma add_not_Leaf:
      forall x v S, add x v S <> Leaf A.
    Proof.
      induction x; simpl; destruct S; inversion 1.
    Qed.

    Lemma add_remove_comm:
      forall x x' (v: A) m,
        x <> x' ->
        remove x' (add x v m) = add x v (remove x' m).
    Proof.
      Local Ltac AddRemoveDestructCases :=
        repeat progress
               match goal with
               | |- context [ match ?e with _ => _ end ] =>
                 let Heq := fresh "Heq" in
                 destruct e eqn:Heq
               | H:context [ match ?e with _ => _ end ] |- _ =>
                 let Heq := fresh "Heq" in
                 destruct e eqn:Heq
               | H:Node _ _ _ = Node _ _ _ |- _ => inversion_clear H; subst
               | H:add _ _ _ = Leaf _ |- _ => now apply add_not_Leaf in H
               end; f_equal; auto; try discriminate.

      induction x, x', m; simpl; intro Neq;
        (try now contradiction Neq);
        (try assert (x <> x') as Hnx by (now intro Heq; apply Neq; subst));
        (try rewrite IHx; auto);
        (try rewrite rleaf);
        AddRemoveDestructCases.
    Qed.

    Lemma remove_comm:
      forall x x' (m : t A),
        remove x (remove x' m) = remove x' (remove x m).
    Proof.
      induction x, x', m; auto;
        destruct m1, o, m2; simpl;
          try rewrite IHx; try rewrite rleaf;
            repeat progress
           match goal with
           | H1:remove ?x1 ?n = Leaf A
             |- context[remove ?x1 (remove ?x2 ?n)]
             => (rewrite IHx || rewrite <-IHx); rewrite H1, rleaf
           | H1:remove ?x1 ?n = Node ?l1 ?o1 ?r1,
                H2:remove ?x2 ?n = Node ?l2 ?o2 ?r2
             |- context[remove ?x1 (remove ?x2 ?n)]
             => (rewrite IHx || rewrite <-IHx); rewrite H1; clear H1
           | H1: remove ?x1 ?n1 = Node ?l ?o ?r
             |- context[Node ?l ?o ?r] => rewrite <-H1
           | |- context[match remove ?x (Node ?l ?o ?r) with _ => _ end]
             => let Heq := fresh "Heq" in
                destruct (remove x (Node l o r)) eqn:Heq
           end; f_equal; try rewrite rleaf; auto.
    Qed.

    Lemma updates_cons_cons':
    forall xs x (vo: option A) vs e,
      ~ List.In x xs ->
      updates (x :: xs) (vo :: vs) e =
      updates xs vs
              (match vo with None => remove x | Some v => add x v end e).
    Proof.
      unfold updates.
      destruct vo as [v|].
      - induction xs as [|x']; intros * NotIn; simpl; auto.
        destruct vs as [|v']; simpl; auto.
        rewrite <-IHxs; auto.
        + simpl. destruct v'.
          * rewrite add_comm; auto.
            intro; subst; apply NotIn; constructor; auto.
          * rewrite add_remove_comm; auto.
            intro; subst; apply NotIn; constructor; auto.
        + intro; apply NotIn; right; auto.
      - induction xs as [|x']; intros * NotIn; simpl; auto.
        destruct vs as [|v']; simpl; auto.
        rewrite <-IHxs; auto.
        + simpl. destruct v'.
          * rewrite add_remove_comm; auto.
            intro; subst; apply NotIn; constructor; auto.
          * rewrite remove_comm; auto.
        + intro; apply NotIn; right; auto.
    Qed.

    Lemma updates_mono:
      forall x (env: t A) ys rvos,
        In x env ->
        Forall (fun x => ~(x = None)) rvos ->
        In x (updates ys rvos env).
    Proof.
      induction ys; destruct rvos; auto.
      intros Hin Hnone; inversion_clear Hnone.
      unfold updates; destruct o; simpl.
      - apply Props.P.F.add_in_iff; eauto.
      - congruence.
    Qed.

  End Extra.

End Env.
