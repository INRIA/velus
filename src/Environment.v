From Coq Require Import FSets.FMapPositive.
From Coq Require Import FSets.FMapFacts.
From Coq Require Import ZArith.ZArith.
From Coq Require Import Classes.EquivDec.

From Velus Require Import Common.CommonTactics.
From Velus Require Import Common.CommonList.
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
      forall {B C} (f: ident -> A -> B) (g: ident -> B -> C) (m: t A) x,
        xmapi g (xmapi f m x) x =
        xmapi (fun x (v : A) => g x (f x v)) m x.
    Proof.
      induction m; intro; simpl; auto.
      f_equal; auto.
      apply option_map_map.
    Qed.

    Lemma mapi_mapi:
      forall {B C} (f: positive -> A -> B) (g: positive -> B -> C) (m: t A),
        mapi g (mapi f m) = mapi (fun x v => g x (f x v)) m.
    Proof.
      unfold mapi; intros.
      apply xmapi_xmapi.
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

    Lemma adds_opt_nil_nil:
      forall e,
        adds_opt List.nil List.nil e = e.
    Proof. simpl; auto. Qed.

    Lemma adds_opt_nil_l:
      forall e vs,
        adds_opt List.nil vs e = e.
    Proof. simpl; auto. Qed.

    Lemma adds_nil_nil:
      forall e,
        adds List.nil List.nil e = e.
    Proof. simpl; auto. Qed.

    Lemma adds_nil_l:
      forall e vs,
        adds List.nil vs e = e.
    Proof. simpl; auto. Qed.

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

    Lemma find_In_from_list:
      forall x (v : A) xs,
        List.In (x, v) xs ->
        NoDupMembers xs ->
        find x (from_list xs) = Some v.
    Proof.
      induction xs as [|(x', v') xs IH]. now inversion 1.
      intros Ix ND. unfold from_list. inv Ix; inv ND.
      - take ((_, _) = (_, _)) and inv it.
        rewrite adds'_cons, Env.gss; auto.
      - rewrite find_gsso'. now apply IH; auto.
        take (List.In _ _) and apply In_InMembers in it.
        intro; subst; auto.
    Qed.

    Lemma In_from_list:
      forall x (xs : list (ident * A)),
        In x (from_list xs) <-> InMembers x xs.
    Proof.
      unfold from_list. setoid_rewrite In_adds_spec'.
      split; intro HH; auto.
      destruct HH as [|HH]; auto.
      now apply Props.P.F.empty_in_iff in HH.
    Qed.

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

    Lemma Equiv_orel {R : relation A} :
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
          rewrite FT. constructor; auto.
        + apply Env.Props.P.F.not_find_in_iff in FS.
          assert (~Env.In x T) as FT
              by (intro HH; apply I in HH; auto).
          apply Env.Props.P.F.not_find_in_iff in FT as ->.
          now left.
      - split.
        + intro x. specialize (LR x).
          inversion LR as [LR1 LR2|??? LR1 LR2]; symmetry in LR1, LR2.
          * apply Env.Props.P.F.not_find_in_iff in LR1.
            apply Env.Props.P.F.not_find_in_iff in LR2.
            intuition.
          * apply find_In in LR1.
            apply find_In in LR2.
            intuition.
        + intros x v v' MS MT.
          apply find_1 in MS.
          apply find_1 in MT.
          specialize (LR x).
          inversion LR as [LR1 LR2|??? LR1 LR2]; symmetry in LR1, LR2.
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

    Lemma adds_opt_mono:
      forall x (env: t A) ys rvos,
        In x env ->
        Forall (fun x => ~(x = None)) rvos ->
        In x (adds_opt ys rvos env).
    Proof.
      induction ys; destruct rvos; auto.
      intros Hin Hnone; inversion_clear Hnone.
      destruct o; simpl.
      - apply Props.P.F.add_in_iff; eauto.
      - congruence.
    Qed.

    Global Instance find_Proper (R : relation A) `{Equivalence A R}:
      Proper (eq ==> Env.Equiv R ==> orel R) (@Env.find A).
    Proof.
      intros x y Hxy E1 E2 (EE1 & EE2); subst.
      destruct (Env.find y E1) eqn:Hx1; destruct (Env.find y E2) eqn:Hx2.
      - repeat (match goal with [ H:Env.find _ _ = Some _ |- _ ] =>
                                apply Env.find_2 in H end).
        specialize (EE2 _ _ _ Hx1 Hx2).
        setoid_rewrite EE2; reflexivity.
      - apply find_In in Hx1. apply Env.Props.P.F.not_find_in_iff in Hx2.
        exfalso; apply Hx2. now apply EE1.
      - apply Env.Props.P.F.not_find_in_iff in Hx1. apply find_In in Hx2.
        exfalso; apply Hx1. now apply EE1.
      - reflexivity.
    Qed.

    Global Instance find_eq_Proper:
      Proper (eq ==> Env.Equiv eq ==> eq) (@Env.find A).
    Proof.
      intros x y Hxy E1 E2 EE; subst.
      apply orel_eq. rewrite EE. reflexivity.
    Qed.

    Lemma omap_find:
      forall xs (env : Env.t A),
        Forall (fun x => Env.In x env) xs ->
        exists vs, omap (fun x => Env.find x env) xs = Some vs
              /\ Forall2 (fun x v => Env.find x env = Some v) xs vs.
    Proof.
      induction xs as [|x xs IH]; simpl; eauto.
      inversion_clear 1 as [|?? Dx Dxs].
      rewrite In_find in Dx. destruct Dx as (v & Fx).
      rewrite Fx. apply IH in Dxs as (vs & -> & HH). eauto.
    Qed.

  End Extra.

  (** Equivalence of Environments *)

  Section Equiv.

    Context {A} (R : relation A).

    Lemma find_Some_orel `{Reflexive _ R} :
      forall env x v,
        find x env = Some v ->
        orel R (find x env) (Some v).
    Proof.
      now intros * ->.
    Qed.

    Lemma orel_find_Some:
      forall env x v,
        orel R (find x env) (Some v) ->
        exists v', R v' v /\ find x env = Some v'.
    Proof.
      intros * Fx. inv Fx; eauto.
    Qed.

    Global Add Parametric Morphism `{Equivalence _ R} : (@In A)
        with signature (eq ==> Equiv R ==> iff)
          as In_Equiv.
    Proof.
      intros x env1 env2 EE. setoid_rewrite In_find.
      split; intros (v, Fx); apply find_Some_orel in Fx; auto.
      - rewrite EE in Fx. apply orel_find_Some in Fx as (? & ? & ?); eauto.
      - rewrite <-EE in Fx. apply orel_find_Some in Fx as (? & ? & ?); eauto.
    Qed.

    Global Instance Equiv_Reflexive `{Reflexive A R} : Reflexive (Equiv R).
    Proof.
      intro env. apply Equiv_orel. reflexivity.
    Qed.

    Global Instance Equiv_Transitive `{Transitive A R} :
      Transitive (Equiv R).
    Proof.
      intros env1 env2 env3.
      setoid_rewrite Equiv_orel.
      intros E12 E23 x. specialize (E12 x); specialize (E23 x).
      inv E12; inv E23; auto; try match goal with H1:_ = find x ?env,
                      H2:_ = find x ?env |- _ => rewrite <- H1 in H2 end;
      try discriminate.
      take (Some _ = Some _) and inversion it; subst.
      constructor. transitivity sy; auto.
    Qed.

    Global Instance Equiv_Symmetric `{Symmetric _ R} : Symmetric (Equiv R).
    Proof.
      intros env1 env2. setoid_rewrite Equiv_orel.
      intros E x. specialize (E x). inv E; auto.
      constructor; auto.
    Qed.

    Global Add Parametric Relation `{Equivalence _ R} : (t A) (Equiv R)
        reflexivity proved by Equiv_Reflexive
        symmetry proved by Equiv_Symmetric
        transitivity proved by Equiv_Transitive
      as Equivalence_Equiv.

    Global Add Parametric Morphism `{Equivalence _ R} : (Equiv R)
        with signature (Equiv R ==> Equiv R ==> iff)
          as Equiv_Equiv.
    Proof.
      intros env1 env2 E12 env3 env4 E34.
      repeat rewrite Env.Equiv_orel in *.
      setoid_rewrite E12. setoid_rewrite E34.
      reflexivity.
    Qed.

    Lemma add_remove:
      forall env x (v : A),
        Env.find x env = Some v ->
        Env.Equal env (Env.add x v (Env.remove x env)).
    Proof.
      intros env x v Fx. intro y.
      destruct (ident_eq_dec y x); subst.
      now rewrite Fx, Env.gss.
      rewrite Env.gso, Env.gro; auto.
    Qed.

    Lemma Equal_add_both:
      forall x (v : A) env1 env2,
        Env.Equal env1 env2 ->
        Env.Equal (Env.add x v env1) (Env.add x v env2).
    Proof.
      intros * EE y. rewrite EE.
      destruct (ident_eq_dec y x); auto.
    Qed.

  End Equiv.


  Existing Instance Equivalence_Equiv.

  (** Refinement of Environments *)

  (* TODO: shift to Environment and update Obc/Equiv.v.
           note: argument order changed. *)
  Section EnvRefines.

    Import Relation_Definitions Basics.

    Context {A : Type}
            (R : relation A).

    Definition refines (env1 env2 : Env.t A) : Prop :=
      forall x v, Env.find x env1 = Some v ->
             exists v', R v v' /\ Env.find x env2 = Some v'.

    Global Typeclasses Opaque refines.

    Lemma refines_empty:
      forall env, refines (empty A) env.
    Proof.
      intros env x v Hfind. now rewrite gempty in Hfind.
    Qed.

    Lemma refines_refl `{Reflexive _ R} : reflexive _ refines.
    Proof.
      intros env x v ->; eauto.
    Qed.

    Lemma refines_trans `{Transitive _ R} : transitive _ refines.
    Proof.
      intros env1 env2 env3 H1 H2 x v Hfind.
      apply H1 in Hfind as (? & ? & Hfind).
      apply H2 in Hfind as (? & ? & ->).
      eauto.
    Qed.

    (* [env_refines] is a [PreOrder] *)
    Global Add Parametric Relation `{Reflexive _ R} `{Transitive _ R}
      : _ refines
        reflexivity proved by refines_refl
        transitivity proved by refines_trans
          as env_refines_preorder.

    Global Add Parametric Morphism `{Reflexive _ R} `{Transitive _ R} : refines
        with signature (refines --> refines ++> impl)
          as refines_refines1.
    Proof.
      intros env2 env1 ER12 env3 env4 ER34 ER13.
      transitivity env2; auto.
      transitivity env3; auto.
    Qed.

    Global Add Parametric Morphism `{Reflexive _ R} `{Transitive _ R} : refines
        with signature (refines ++> refines --> flip impl)
          as refines_refines2.
    Proof.
      intros env1 env2 ER12 env4 env3 ER34 ER23.
      transitivity env2; auto. transitivity env3; auto.
    Qed.

    Lemma refines_add `{Reflexive _ R} :
      forall env x v,
        ~ In x env ->
        refines env (add x v env).
    Proof.
      intros env x v nI x' v' Fx'.
      destruct (ident_eq_dec x x').
      - subst. apply find_In in Fx'. exfalso; auto.
      - rewrite gso; eauto.
    Qed.

    Lemma refines_add_both:
      forall env1 env2 x v1 v2,
        refines env1 env2 ->
        R v1 v2 ->
        refines (add x v1 env1) (add x v2 env2).
    Proof.
      intros env1 env2 x v1 v2 Henv Rv y yv Hfind.
      destruct (ident_eq_dec x y).
      - subst; rewrite gss in *; inv Hfind; eauto.
      - rewrite gso in *; auto.
    Qed.

    Global Add Morphism (@In A)
        with signature (eq ==> refines ++> impl)
          as In_refines.
    Proof.
      setoid_rewrite In_find.
      intros x E1 E2 ER12 (v & Fx).
      apply ER12 in Fx as (v' & ? & ?); eauto.
    Qed.

    Global Add Morphism (@In A)
        with signature (eq ==> refines --> flip impl)
          as In_refines_flip.
    Proof.
      setoid_rewrite In_find.
      intros x E1 E2 ER12 (v & Fx).
      apply ER12 in Fx as (v' & ? & ?); eauto.
    Qed.

    Global Instance refines_Proper `{Reflexive _ R} `{Transitive _ R} :
      Proper (flip refines ==> refines ==> impl) refines.
    Proof.
      intros m1 m1' Henv1 m2 m2' Henv2.
      intros Henv x v Hfind.
      apply Henv1 in Hfind as (? & ? & Hfind).
      apply Henv in Hfind as (? & ? & Hfind).
      apply Henv2 in Hfind as (? & ? & Hfind).
      eauto.
    Qed.

    Global Instance add_refines_Proper `{Reflexive _ R}:
      Proper (@eq ident ==> @eq A ==> refines ==> refines) (@add A).
    Proof.
      intros x y Hxy vx vy Hv m1 m2 Henv.
      subst. now apply refines_add_both.
    Qed.

    Lemma Equiv_refines' `{Symmetric _ R}:
      forall env1 env2,
        Equiv R env1 env2 ->
        refines env1 env2.
    Proof.
      intros env1 env2 E x v Fx.
      rewrite Equiv_orel in E. specialize (E x).
      rewrite Fx in E. symmetry in E.
      apply orel_find_Some in E as (v' & Rvv & ->).
      symmetry in Rvv. eauto.
    Qed.

    Lemma Equiv_refines `{Equivalence _ R}:
      forall env1 env2,
        Equiv R env1 env2 <-> (refines env1 env2 /\ refines env2 env1).
    Proof.
      split; intro E.
      - split; apply Equiv_refines'; auto.
        now symmetry in E.
      - destruct E as (E1 & E2). split.
        + split; intro Ik.
          * now rewrite E1 in Ik.
          * now rewrite E2 in Ik.
        + intros * M1 M2.
          apply Env.find_1 in M1. apply Env.find_1 in M2.
          apply E1 in M1 as (v & Rv & F2).
          rewrite F2 in M2. now inv M2.
    Qed.

    (* TODO: Use to simplify Env.Equal lemmas... *)
    Global Add Parametric Morphism `{Equivalence _ R} : refines
        with signature (Equiv R ==> Equiv R ==> iff)
          as refines_Equiv.
    Proof.
      intros mA mA' EA mB mB' EB.
      apply Equiv_refines in EA as (EA1 & EA2).
      apply Equiv_refines in EB as (EB1 & EB2).
      split; intro ER.
      - transitivity mA; auto. transitivity mB; auto.
      - transitivity mA'; auto. transitivity mB'; auto.
    Qed.

    Global Add Parametric Morphism `{Equivalence _ R} : refines
        with signature (Equiv R ==> Equiv R ==> flip impl)
          as refines_Equiv_flip_impl.
    Proof.
      intros mA mA' EA mB mB' EB EAB.
      apply Equiv_refines in EA as (EA1 & EA2).
      apply Equiv_refines in EB as (EB1 & EB2).
      transitivity mA'; auto. transitivity mB'; auto.
    Qed.

    Global Instance equiv_refines `{Equivalence _ R} :
      PartialOrder (Equiv R) refines.
    Proof.
      intros env1 env2.
      constructor.
      - intro E. red; unfold predicate_intersection; simpl.
        setoid_rewrite E. split; reflexivity.
      - intros (E1 & E2). apply Equiv_refines. auto.
    Qed.

    Lemma refines_add_right `{Reflexive _ R} `{Transitive _ R}:
      forall env1 env2 x v,
        refines env1 env2 ->
        ~ In x env1 ->
        refines env1 (add x v env2).
    Proof.
      intros. setoid_rewrite refines_add at 1; eauto.
      apply refines_add_both; auto.
    Qed.

    Lemma refines_remove `{Reflexive _ R}:
      forall env x,
        refines (remove x env) env.
    Proof.
      intros env x y v Fx.
      destruct (ident_eq_dec x y).
      - now subst; rewrite grs in *.
      - rewrite gro in *; eauto.
    Qed.

    Lemma refines_remove_both:
      forall env1 env2 x,
        refines env1 env2 ->
        refines (remove x env1) (remove x env2).
    Proof.
      intros env1 env2 x Henv y v Hfind.
      destruct (ident_eq_dec x y).
      - now subst; rewrite grs in *.
      - rewrite gro in *; auto.
    Qed.

    Lemma refines_add_remove:
      forall env1 env2 x v,
        refines env1 env2 ->
        refines (remove x env1) (add x v env2).
    Proof.
      intros env1 env2 x v Henv y vy Hfind.
      destruct (ident_eq_dec x y).
      - now subst; rewrite grs in Hfind.
      - rewrite gro in Hfind; auto.
        rewrite gso; auto.
    Qed.

    Lemma find_add:
      forall {x v} {env : t A},
        find x env = Some v ->
        Equal env (add x v env).
    Proof.
      intros x v env Fx.
      rewrite Props.P.F.Equal_Equiv, Equiv_orel.
      intro y. destruct (ident_eq_dec y x) as [|Nyx]; subst.
      - now rewrite gss, Fx.
      - rewrite gso; eauto.
    Qed.

    Lemma refines_orel_find `{Reflexive _ R} `{Transitive _ R}:
      forall env1 env2 x,
        refines env1 env2 ->
        In x env1 ->
        orel R (find x env1) (find x env2).
    Proof.
      intros * ER Ix.
      rewrite In_find in Ix. destruct Ix as (v & Fx1).
      specialize (ER _ _ Fx1) as (v' & Rvv & Fx2).
      now rewrite Fx1, Fx2, Rvv.
    Qed.

    Lemma refines_find_add_left `{Reflexive _ R}:
      forall x v env,
        find x env = Some v ->
        refines (add x v env) env.
    Proof.
      intros * Fx.
      intros y v' Fy.
      destruct (ident_eq_dec y x) as [|Nyx].
      - subst. rewrite gss in Fy. inv Fy; eauto.
      - rewrite gso in Fy; eauto.
    Qed.

    Lemma refines_find_add_right `{Reflexive _ R}:
      forall x v env,
        find x env = Some v ->
        refines env (add x v env).
    Proof.
      intros * Fx. intros y v' Fy.
      destruct (ident_eq_dec y x) as [|Nyx].
      - subst. rewrite gss. rewrite Fx in Fy. inv Fy; eauto.
      - rewrite gso; eauto.
    Qed.

    Lemma refines_add_left `{Reflexive _ R} `{Transitive _ R}:
      forall x v1 v2 env1 env2,
        refines env1 env2 ->
        find x env2 = Some v2 ->
        R v1 v2 ->
        refines (add x v1 env1) env2.
    Proof.
      intros * R12 MT Rvv.
      apply refines_find_add_left in MT. setoid_rewrite <-MT.
      auto using refines_add_both.
    Qed.

  End EnvRefines.

  Existing Instance env_refines_preorder.
  Existing Instance Equivalence_Equiv.

  Hint Immediate refines_empty.
  Hint Extern 4 (refines _ (add ?x _ _) (add ?x _ _)) => apply refines_add.

  Lemma Equal_Equiv {A}:
    relation_equivalence Equal (Equiv (@eq A)).
  Proof.
    split; intro HH; now apply Props.P.F.Equal_Equiv in HH.
  Qed.

  Add Parametric Morphism {A}: (@Equiv A)
      with signature (subrelation ==> eq ==> eq ==> impl)
        as Equiv_subrelation.
  Proof.
    intros R1 R2 SR env1 env2 ER.
    split. now apply ER.
    destruct ER as (? & ?); eauto.
  Qed.

  Global Instance subrelation_Equiv {A} (R1 R2 : relation A):
    subrelation R1 R2 ->
    subrelation (Equiv R1) (Equiv R2).
  Proof.
    intros SR env1 env2 EE.
    now rewrite SR in EE.
  Qed.

  Global Instance Equal_subrelation_Equiv {A} (R : relation A) `{Reflexive _ R}:
    subrelation Equal (Equiv R).
  Proof.
    rewrite Equal_Equiv.
    apply eq_subrelation in H.
    typeclasses eauto.
  Qed.

  Global Instance Equiv_subrelation_Equal {A}:
    subrelation (Equiv (@eq A)) Equal.
  Proof.
    now rewrite Equal_Equiv.
  Qed.

  Global Instance refines_Equal_Proper {A}:
    Proper (@Equal A ==> @Equal A ==> iff) (refines eq).
  Proof.
    rewrite Equal_Equiv.
    typeclasses eauto.
  Qed.

  Section RefinesAdds.
    Context {V : Type}.

    Fact refines_adds' : forall (xs : list (ident * V)) H H',
        refines eq H H' ->
        refines eq (adds' xs H) (adds' xs H').
    Proof.
      induction xs; intros H H' Href; simpl.
      - assumption.
      - destruct a.
        eapply IHxs.
        apply refines_add_both; auto.
    Qed.

    Lemma refines_adds : forall ids (vs : list V) H,
        Forall (fun id => ~In id H) ids ->
        refines eq H (adds ids vs H).
    Proof.
      induction ids; intros vs H Hnin; inv Hnin.
      - unfold adds. reflexivity.
      - unfold adds in *.
        destruct vs; simpl.
        + reflexivity.
        + etransitivity.
          * apply IHids; auto.
          * eapply refines_adds'.
            apply refines_add; auto.
    Qed.
  End RefinesAdds.

  Lemma In_add1 {A : Type}:
    forall x (v : A) env,
      In x (add x v env).
  Proof.
    setoid_rewrite In_find. setoid_rewrite gss. eauto.
  Qed.

  Lemma In_add2 {A : Type}:
    forall x y (v : A) env,
      In y env ->
      In y (add x v env).
  Proof.
    intros x y v env0 Iy.
    destruct (ident_eq_dec y x); [subst; auto using In_add1|].
    apply In_find. rewrite gso; auto.
  Qed.

  Hint Immediate In_add1.
  Hint Extern 4 (In ?x (add ?y ?v ?env)) => apply In_add2.
  Hint Extern 4 (refines _ ?x ?x) => reflexivity.
  Hint Immediate eq_Transitive.

  Section EnvDom.

    Context { V : Type }.

    Definition dom (env : Env.t V) (dom : list ident) :=
      forall x, Env.In x env <-> List.In x dom.

    Lemma dom_use:
      forall {env xs},
        dom env xs ->
        forall x, Env.In x env <-> List.In x xs.
    Proof. auto. Qed.

    Lemma dom_intro:
      forall env xs,
        (forall x, Env.In x env <-> List.In x xs) ->
        dom env xs.
    Proof. auto. Qed.

    Lemma dom_add_cons:
      forall env xs x v,
        dom env xs ->
        dom (add x v env) (x :: xs).
    Proof.
      intros evn xs x v ED y.
      split; intro HH.
      - apply Props.P.F.add_in_iff in HH as [HH|HH]; subst.
        now constructor. apply ED in HH. now constructor 2.
      - inv HH; auto. take (List.In _ xs) and apply ED in it; auto.
    Qed.

    Lemma dom_empty:
      dom (empty V) List.nil.
    Proof.
      intro. split; inversion 1.
      now apply Props.P.F.empty_in_iff in H.
    Qed.

    Import Permutation.

    Global Add Parametric Morphism (E : relation V) `{Equivalence _ E} : dom
        with signature (Equiv E ==> @Permutation ident ==> iff)
          as dom_Equiv_Permutation.
    Proof.
      intros env1 env2 EE xs1 xs2 Pxs. unfold dom.
      setoid_rewrite EE.
      induction Pxs; split; intro HH;
        try (setoid_rewrite <-HH || setoid_rewrite HH);
        try setoid_rewrite Pxs; try reflexivity.
      - now setoid_rewrite (perm_swap x).
      - now setoid_rewrite (perm_swap x).
      - now setoid_rewrite Pxs1; setoid_rewrite Pxs2.
      - now setoid_rewrite Pxs1; setoid_rewrite Pxs2.
    Qed.

    Corollary dom_Permutation : forall d l1 l2,
        Permutation l1 l2 ->
        dom d l1 <-> dom d l2.
    Proof.
      intros d l1 l2 Hperm.
      apply dom_Equiv_Permutation with (E:=eq); auto.
      reflexivity.
    Qed.

    Lemma dom_equal_empty:
      forall M, dom M List.nil <-> Equal M (empty V).
    Proof.
      intros. unfold dom. split; intro HH.
      - intro x. rewrite gempty.
        apply Props.P.F.not_find_in_iff.
        rewrite HH. auto.
      - intros x. setoid_rewrite HH.
        split; [intro Ix|now inversion 1].
        now apply Props.P.F.empty_in_iff in Ix.
    Qed.

    Lemma dom_from_list_map_fst:
      forall (xs : list (ident * V)) ys,
        NoDupMembers xs ->
        ys = List.map fst xs ->
        dom (from_list xs) ys.
    Proof.
      intros * ND HH; subst.
      induction xs as [|(x, v) xs IH].
      now apply dom_empty.
      inv ND; take (NoDupMembers _) and specialize (IH it).
      unfold dom in *. simpl.
      setoid_rewrite In_from_list.
      setoid_rewrite In_from_list in IH.
      intro y; split; intro HH.
      - inv HH; auto. take (InMembers _ _) and apply IH in it; auto.
      - destruct HH as [HH|HH]; subst. now constructor.
        apply fst_InMembers in HH. now constructor 2.
    Qed.

    Global Opaque dom.
  End EnvDom.

  Hint Extern 4 (dom ?env (?xs ++ nil)) => rewrite app_nil_r.
  Hint Immediate dom_empty.

  Add Parametric Morphism {A} (R: relation A) `{Equivalence _ R} : (@add A)
      with signature (eq ==> R ==> Equiv R ==> Equiv R)
        as add_Equiv.
  Proof.
    setoid_rewrite Equiv_orel.
    intros x v1 v2 Rvv env1 env2 EE y.
    destruct (ident_eq_dec x y).
    - subst. setoid_rewrite gss. now constructor.
    - setoid_rewrite gso; auto.
  Qed.

  Add Parametric Morphism {A} : (@dom A)
      with signature (eq ==> same_elements ==> iff)
        as dom_same_elements.
  Proof.
    intros env xs ys S.
    split; intro HH; apply Env.dom_intro; intro y;
      apply Env.dom_use with (x:=y) in HH; rewrite HH.
    now apply S. now symmetry; apply S.
  Qed.

  Lemma uniquify_dom:
    forall {A} (env : Env.t A) xs,
      dom env xs ->
      exists ys, dom env ys /\ NoDup ys.
  Proof.
    intros * Dxs.
    exists (nub ident_eq_dec xs).
    split; [|now apply NoDup_nub].
    now setoid_rewrite nub_same_elements.
  Qed.

  Lemma find_not_In_dom:
    forall {A} (H : Env.t A) xs x,
      dom H xs ->
      ~List.In x xs ->
      find x H = None.
  Proof.
    intros * DH NI.
    apply dom_use with (x0:=x) in DH.
    rewrite <-DH in NI.
    rewrite Props.P.F.in_find_iff in NI.
    now apply None_eq_dne in NI.
  Qed.

  Lemma dom_cons_remove:
    forall {A} (env : @t A) x xs,
      dom env xs ->
      dom (remove x env) (filter (nequiv_decb x) xs).
  Proof.
    intros * D. apply dom_intro. intros y.
    apply dom_use with (x0:=y) in D.
    destruct (ident_eq_dec y x); subst.
    - setoid_rewrite In_find. rewrite grs, filter_In.
      split; [intros (? & ?); discriminate|intros (? & HH)].
      now rewrite nequiv_decb_refl in HH.
    - rewrite Props.P.F.remove_in_iff, D, filter_In.
      split; intros (H1 & H2); split; auto.
      now apply nequiv_decb_true.
  Qed.

  Section DomAdds.

    Context { V : Type }.

    Fact dom_adds' : forall (xs : list (ident * V)) H d,
        dom H d ->
        dom (adds' xs H) ((List.map fst xs)++d).
    Proof.
      induction xs; intros H d Hdom.
      - simpl. assumption.
      - destruct a; simpl.
        apply dom_add_cons with (x:=i) (v0:=v) in Hdom.
        apply IHxs in Hdom.
        erewrite dom_Permutation; [eauto|].
        apply Permutation.Permutation_middle.
    Qed.

    Lemma dom_adds : forall ids (vs : list V) H d,
        length ids = length vs ->
        dom H d ->
        dom (adds ids vs H) (ids++d).
    Proof.
      intros.
      unfold adds.
      apply dom_adds' with (xs:=(combine ids vs)) in H1.
      rewrite combine_map_fst' in H1; auto.
    Qed.

    Lemma adds_MapsTo : forall ids (vs : list V) H n d d',
        length ids = length vs ->
        n < length ids ->
        NoDup ids ->
        Env.MapsTo (nth n ids d) (nth n vs d') (Env.adds ids vs H).
    Proof.
      induction ids; intros vs H n d d' Hlen Hn Hndup.
      - unfold adds; simpl in *; try omega.
      - destruct vs; simpl in *; try congruence.
        inv Hndup.
        destruct n.
        + unfold MapsTo in *.
          apply find_gsss; auto.
        + eapply IHids; eauto.
          omega.
    Qed.
  End DomAdds.

  Section EnvDomUpperBound.

    Context { V : Type }.

    Definition dom_ub (env : t V) (dom : list ident) :=
      forall x, In x env -> List.In x dom.

    Lemma dom_ub_use:
      forall {env xs},
        dom_ub env xs ->
        forall x, In x env -> List.In x xs.
    Proof. auto. Qed.

    Lemma dom_ub_intro:
      forall env xs,
        (forall x, In x env -> List.In x xs) ->
        dom_ub env xs.
    Proof. auto. Qed.

    Lemma dom_dom_ub:
    forall H d,
      Env.dom H d ->
      dom_ub H d.
    Proof.
      intros * DH.
      apply dom_ub_intro. intros x Ix.
      now apply dom_use with (1:=DH) in Ix.
    Qed.

    Lemma dom_ub_empty:
      forall d, dom_ub (empty V) d.
    Proof.
      intro d. apply dom_ub_intro.
      intros x Ix. now apply Env.Props.P.F.empty_in_iff in Ix.
    Qed.

    Lemma dom_ub_app:
      forall H xs ys,
        dom_ub H xs ->
        dom_ub H (xs ++ ys).
    Proof.
      intros H xs ys DH x Ix.
      apply DH in Ix. apply in_or_app. auto.
    Qed.

    Global Opaque dom_ub.
  End EnvDomUpperBound.

  Lemma refines_dom_ub_dom:
    forall {A R} (H H' : Env.t A) d,
      refines R H H' ->
      dom H d ->
      dom_ub H' d ->
      dom H' d.
  Proof.
    intros A R H H' d HH DH DH'.
    apply dom_intro. intro x.
    split; intro Ix.
    now eapply dom_ub_use with (1:=DH') in Ix.
    now apply dom_use with (1:=DH) in Ix; rewrite HH in Ix.
  Qed.

  Lemma dom_ub_cons:
    forall {V} x xs (env: t V),
      dom_ub env xs ->
      dom_ub env (x::xs).
  Proof.
    intros * DU.
    apply dom_ub_intro. intros y Iy.
    apply DU in Iy. now constructor 2.
  Qed.

  Lemma dom_ub_add:
    forall {V} x v xs (env: t V),
      dom_ub env xs ->
      dom_ub (add x v env) (x::xs).
  Proof.
    intros * DU.
    apply Env.dom_ub_intro. intros y Iy.
    apply Env.Props.P.F.add_in_iff in Iy as [Iy|Iy].
    now subst; constructor.
    apply DU in Iy. now constructor 2.
  Qed.

  Lemma dom_Forall_not_In:
    forall {A} (H : Env.t A) xs ys,
      dom H xs ->
      Forall (fun x => ~List.In x xs) ys ->
      forall y, List.In y ys -> ~(In y H).
  Proof.
    intros * DH FA y Iy Ey.
    apply Env.dom_use with (1:=DH) in Ey.
    rewrite Forall_forall in FA.
    apply FA in Iy. auto.
  Qed.

  Section EnvDomLowerBound.

    Context { V : Type }.

    Definition dom_lb (env : t V) (dom : list ident) :=
      forall x, List.In x dom -> In x env.

    Lemma dom_lb_cons : forall (env : t V) (id : ident) (xs : list ident),
        dom_lb env (id::xs) <-> (In id env /\ dom_lb env xs).
    Proof.
      intros env id xs.
      unfold dom_lb in *.
      split.
      - intro H. split.
        + apply H. constructor; auto.
        + intros x Hin. apply H. right; auto.
      - intros [H1 H2] x HIn.
        destruct HIn; subst; auto.
    Qed.

    Lemma dom_lb_use:
      forall {env xs},
        dom_lb env xs ->
        forall x, List.In x xs -> In x env.
    Proof. auto. Qed.

    Lemma dom_lb_intro:
      forall env xs,
        (forall x, List.In x xs -> In x env) ->
        dom_lb env xs.
    Proof. auto. Qed.

    Lemma dom_dom_lb:
    forall H d,
      dom H d ->
      dom_lb H d.
    Proof.
      intros * DH.
      apply dom_lb_intro. intros x Ix.
      now apply Env.dom_use with (1:=DH) in Ix.
    Qed.

    Lemma dom_lb_nil:
      forall E, dom_lb E nil.
    Proof.
      intro E. apply dom_lb_intro. now inversion 1.
    Qed.

    Lemma dom_lb_add_cons:
      forall x xs v H,
        dom_lb H xs ->
        dom_lb (add x v H) (x :: xs).
    Proof.
      intros x xs v H DH y Iy.
      inv Iy; auto using In_add1, In_add2.
    Qed.

    Lemma dom_lb_app:
      forall H xs ys,
        dom_lb H (xs ++ ys) ->
        dom_lb H xs.
    Proof.
      intros H xs ys DH x Ix.
      apply DH, in_or_app. auto.
    Qed.

    Global Opaque dom_lb.
  End EnvDomLowerBound.

  Hint Resolve dom_lb_nil.

  Lemma dom_lb_ub_dom:
    forall {A} (H : t A) d,
      dom_lb H d ->
      dom_ub H d ->
      dom H d.
  Proof.
    intros * Min Max.
    apply dom_intro; intro x.
    split; intros Ix.
    now apply dom_ub_use with (1:=Max) in Ix.
    now apply dom_lb_use with (1:=Min) in Ix.
  Qed.

  Hint Resolve dom_lb_ub_dom.

  Section EnvRestrict.
    Context {V : Type}.

    Definition restrict (H : Env.t V) (xs : list ident) : Env.t V :=
      List.fold_right (fun id H' => match (Env.find id H) with
                                 | None => H'
                                 | Some v => add id v H'
                                 end) (empty V) xs.

    Lemma restrict_dom_ub : forall xs (H : Env.t V),
        dom_ub (restrict H xs) xs.
    Proof.
      induction xs; intro H; simpl.
      - apply dom_ub_empty.
      - destruct (find a H); simpl.
        + apply dom_ub_add; auto.
        + apply dom_ub_cons; auto.
    Qed.

    Lemma restrict_refines : forall R xs (H : Env.t V),
        Reflexive R ->
        Transitive R ->
        refines R (restrict H xs) H.
    Proof.
      induction xs; intros H Hrefl Htrans; simpl.
      - apply refines_empty.
      - destruct (find a H) eqn:Hfind; simpl.
        + eapply refines_add_left; eauto.
        + eauto.
    Qed.

    Lemma dom_lb_restrict_dom : forall xs (H : Env.t V),
        dom_lb H xs ->
        dom (restrict H xs) xs.
    Proof.
      induction xs; intros H Hdom; simpl.
      - apply dom_empty.
      - rewrite dom_lb_cons in Hdom; destruct Hdom.
        rewrite In_find in H0. destruct H0 as [v H0].
        rewrite H0.
        apply dom_add_cons. auto.
    Qed.

    Lemma restrict_find : forall xs (H : Env.t V) id v,
        List.In id xs ->
        find id H = Some v ->
        find id (restrict H xs) = Some v.
    Proof.
      induction xs; intros H id v HIn Hfind; simpl; inv HIn.
      - rewrite Hfind. apply gss.
      - eapply IHxs in H0; eauto.
        destruct (find a H) eqn:Hfind2; auto.
        destruct (Pos.eqb a id) eqn:Heq.
        + rewrite Pos.eqb_eq in Heq; subst.
          rewrite Hfind in Hfind2. inv Hfind2.
          apply gss.
        + rewrite Pos.eqb_neq in Heq.
          rewrite <- H0. apply gso. auto.
    Qed.
  End EnvRestrict.

  (** Notations *)

  Module Notations.
    Notation "e1 ≈ e2" :=  (Equal e1 e2)
                             (at level 70, no associativity) : env_scope.

    Notation "e1 ≈⟨ R ⟩ e2" :=  (Equiv R e1 e2)
                                  (at level 70, no associativity,
                                   format "e1  '[' ≈⟨ R ⟩ ']'  e2") : env_scope.

    Notation "e1 ⊑⟨ ee ⟩ e2" := (refines ee e1 e2)
                                  (at level 70, no associativity,
                                   format "e1  '[' ⊑⟨ ee ⟩ ']'  e2") : env_scope.
    Notation "e1 ⊑ e2" := (refines eq e1 e2)
                            (at level 70, no associativity) : env_scope.

  End Notations.

End Env.

Open Scope env_scope.
