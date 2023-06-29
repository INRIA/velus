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

    Lemma mapi_elements {B} (f : _ -> A -> B) : forall m,
        Env.elements (Env.mapi f m) = List.map (fun '(x, y) => (x, f x y)) (Env.elements m).
    Proof.
      intros m.
      unfold elements, mapi. generalize xH as i.
      induction m; intros; simpl in *; auto.
      destruct o; simpl in *.
      1,2:repeat rewrite map_app; simpl; f_equal; auto.
    Qed.

    Lemma map_map:
      forall {B C} (f: A -> B) (g: B -> C) (m: t A),
        map g (map f m) = map (fun x => g (f x)) m.
    Proof.
      unfold map, mapi; intros.
      apply xmapi_xmapi.
    Qed.

    Fact xmapi_ext : forall {B} (f g : positive -> A -> B) (m : t A) p,
        (forall p x, f p x = g p x) ->
        xmapi f m p = xmapi g m p.
    Proof.
      induction m; intros p Heq; simpl; auto.
      f_equal; auto.
      destruct o; simpl; f_equal; auto.
    Qed.

    Lemma map_ext: forall {B} (f g : A -> B) (m: t A),
        (forall x, f x = g x) ->
        map f m = map g m.
    Proof.
      intros * Heq.
      unfold map, mapi in *.
      eapply xmapi_ext; intuition.
    Qed.

    Lemma map_Equiv {B} {Ra: A -> A -> Prop} {Rb: B -> B -> Prop} : forall (f : A -> B) (m1 m2: t A),
        (forall x y, Ra x y -> Rb (f x) (f y)) ->
        Env.Equiv Ra m1 m2 ->
        Env.Equiv Rb (Env.map f m1) (Env.map f m2).
    Proof.
      intros * Hf (HIn&Hfind).
      split.
      - intros. now rewrite 2 Props.P.F.map_in_iff.
      - unfold MapsTo in *. intros * Hfind1 Hfind2.
        rewrite Props.P.F.map_o in *.
        destruct (Env.find k m1) eqn:Hfind1'; inv Hfind1.
        destruct (Env.find k m2) eqn:Hfind2'; inv Hfind2.
        eapply Hf; eauto.
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

    Lemma find_adds'_In:
      forall x y xvs (m: t A),
        find x (adds' xvs m) = Some y -> (List.In (x, y) xvs \/ find x m = Some y).
    Proof.
      induction xvs as [|(x', v')]; simpl.
      - firstorder.
      - intros. apply IHxvs in H.
        destruct H as [H|H]; auto.
        destruct (PositiveMap.E.eq_dec x x'); subst.
        + rewrite PositiveMap.gss in H. inv H; auto.
        + rewrite PositiveMap.gso in H; auto.
    Qed.

    Lemma find_adds'_nIn: forall x xvs (m : t A),
        find x (adds' xvs m) = None <-> (not (InMembers x xvs) /\ find x m = None).
    Proof.
      induction xvs; intros *; simpl;
        (split; [intros Hfind|intros (Hnin&Hfind)]); auto.
      - destruct a as (?&?).
        apply IHxvs in Hfind as (Hfind&Hnin).
        destruct (PositiveMap.E.eq_dec p x); subst.
        + rewrite Env.gss in Hnin. congruence.
        + rewrite Env.gso in Hnin; auto.
          split; auto. intros [?|?]; auto.
      - destruct a as (?&?).
        rewrite IHxvs; split.
        + intro contra; auto.
        + rewrite Env.gso; auto.
    Qed.

    Lemma find_gsss'_irrelevant:
      forall x a xvs m1 m2,
        InMembers x xvs ->
        find x (adds' xvs m1) = Some a ->
        find x (adds' xvs m2) = Some a.
    Proof.
      induction xvs as [|(?&?)]; intros * Hin Hfind; simpl in *.
      - inv Hin.
      - destruct Hin, (ident_eq_dec k x), (InMembers_dec x xvs ident_eq_dec);
          try congruence; subst; eauto.
        setoid_rewrite find_gsss' in Hfind; eauto.
        setoid_rewrite find_gsss'; eauto.
    Qed.

    Corollary find_gsss'_empty:
      forall x a xvs m,
        find x (adds' xvs (Env.empty _)) = Some a ->
        find x (adds' xvs m) = Some a.
    Proof.
      intros * Hfind.
      eapply find_gsss'_irrelevant; eauto.
      eapply find_adds'_In in Hfind as [Hin|Hin].
      + eapply In_InMembers; eauto.
      + rewrite PositiveMap.gempty in Hin. congruence.
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

    Lemma adds_cons:
      forall xs vs x (a: A) m,
        adds (x :: xs) (a :: vs) m = adds xs vs (add x a m).
    Proof.
      intros *.
      unfold adds; simpl. reflexivity.
    Qed.

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

    Fact from_list_find_iff : forall xs x (y : A),
        NoDupMembers xs ->
        Env.find x (from_list xs) = Some y <-> List.In (x, y) xs.
    Proof.
      intros * ND; split; intros; eauto using from_list_find_In, find_In_from_list.
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

    Lemma NoDup_snd_elements : forall env x1 x2 (y : A),
        NoDup (List.map snd (elements env)) ->
        find x1 env = Some y ->
        find x2 env = Some y ->
        x1 = x2.
    Proof.
      intros * Hnd Hfind1 Hfind2.
      apply elements_correct in Hfind1.
      apply elements_correct in Hfind2.
      eapply NoDup_snd_det; eauto.
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

    Lemma elements_adds:
      forall xs m,
        NoDupMembers (elements m++xs) ->
        Permutation.Permutation (elements (adds' xs m)) (elements m++xs).
    Proof.
      induction xs as [|[k a] xs]; intros m Hndup; simpl.
      - rewrite app_nil_r. reflexivity.
      - specialize (IHxs (add k a m)).
        rewrite elements_add in IHxs.
        2: { rewrite <- Permutation.Permutation_middle in Hndup.
             inv Hndup. apply NotInMembers_app in H1 as [_ H1].
             rewrite In_Members; auto. }
        rewrite <- Permutation.Permutation_middle in *.
        apply IHxs in Hndup.
        etransitivity; eauto.
    Qed.

    Corollary elements_from_list: forall xs,
        NoDupMembers xs ->
        Permutation.Permutation (elements (from_list xs)) xs.
    Proof.
      intros * Hnd. unfold from_list.
      rewrite elements_adds. 1,2:rewrite Props.P.elements_empty; auto.
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

    Lemma elements_from_list_incl : forall xs,
        incl (elements (from_list xs)) xs.
    Proof.
      intros xs [? ?] Hin.
      apply PositiveMap.elements_complete, from_list_find_In in Hin; auto.
    Qed.

    Lemma find_env_from_list':
      forall x (v: A) xs s,
        find x (adds' xs s) = Some v
        -> List.In (x, v) xs \/ (~InMembers x xs /\ find x s = Some v).
    Proof.
      induction xs as [|(x', v') xs IH]; simpl. now intuition.
      intros s Hfind. apply IH in Hfind as [|(Hnim & Hfind)]; auto.
      destruct (ident_eq_dec x' x).
      + subst. rewrite Env.gss in Hfind.
        injection Hfind. intro; subst; auto.
      + rewrite Env.gso in Hfind; intuition.
    Qed.

    Lemma adds_from_list : forall xs ys (env : t A) x y,
        find x (adds xs ys env) = Some y ->
        find x (from_list (combine xs ys)) = Some y \/ find x env = Some y.
    Proof.
      intros * Find.
      unfold from_list, adds in *.
      apply find_adds'_In in Find as Find'. destruct Find' as [In|]; auto.
      left. erewrite find_gsss'_irrelevant; eauto using In_InMembers.
    Qed.

  End Extra.

  Fact from_list_rev : forall xs,
      NoDupMembers xs ->
      NoDup (List.map snd xs) ->
      forall x y, Env.find x (from_list xs) = Some y
             <-> Env.find y (from_list (List.map (fun x => (snd x, fst x)) xs)) = Some x.
  Proof.
    intros * ND1 ND2 *.
    rewrite ? from_list_find_iff; auto.
    2:now rewrite fst_NoDupMembers, List.map_map.
    split; intros In; [solve_In|simpl_In; auto].
  Qed.

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
      try discriminate; auto with datatypes.
      take (Some _ = Some _) and inversion it; subst.
      constructor. transitivity sy; auto.
    Qed.

    Global Instance Equiv_Symmetric `{Symmetric _ R} : Symmetric (Equiv R).
    Proof.
      intros env1 env2. setoid_rewrite Equiv_orel.
      intros E x. specialize (E x). inv E; auto with datatypes.
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


  Global Existing Instance Equivalence_Equiv.

  (** Refinement of Environments *)

  Section EnvRefines.

    Import Relation_Definitions Basics.

    Context {A : Type}
            (R : relation A).

    Definition refines (env1 env2 : Env.t A) : Prop :=
      forall x v, Env.find x env1 = Some v ->
             exists v', R v v' /\ Env.find x env2 = Some v'.

    Typeclasses Opaque refines.

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
      - rewrite gso; eauto with datatypes.
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

    Lemma refines_elements : forall env1 env2,
        refines env1 env2 ->
        incl (List.map fst (elements env1)) (List.map fst (elements env2)).
    Proof.
      intros * Href ? Hin.
      rewrite <-fst_InMembers, <-In_Members in *.
      eapply In_refines; eauto.
    Qed.

  End EnvRefines.

  Global Existing Instance env_refines_preorder.
  Global Existing Instance Equivalence_Equiv.

  Global Hint Immediate refines_empty : env.
  Global Hint Extern 4 (refines _ (add ?x _ _) (add ?x _ _)) => apply refines_add : env.
  Global Hint Resolve refines_refl refines_trans refines_add refines_add_both refines_add_right
         refines_remove refines_remove_both refines_add_remove refines_orel_find
         refines_find_add_left refines_find_add_right refines_add_left refines_elements : env.

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
    Variable (R : V -> V -> Prop).

    Hypothesis R_refl : Reflexive R.
    Hypothesis R_trans : Transitive R.

    Fact refines_adds'_aux : forall (xs : list (ident * V)) H H',
        refines R H H' ->
        refines R (adds' xs H) (adds' xs H').
    Proof.
      induction xs; intros H H' Href; simpl.
      - assumption.
      - destruct a.
        eapply IHxs.
        apply refines_add_both; auto.
    Qed.

    Lemma refines_adds' : forall (xs : list (ident * V)) H,
        Forall (fun id => ~In id H) (List.map fst xs) ->
        refines R H (adds' xs H).
    Proof.
      induction xs as [|(?&?)]; intros * Hnin; inv Hnin; simpl.
      - eapply refines_refl; eauto.
      - eapply refines_trans. eauto.
        + eapply IHxs; eauto.
        + eapply refines_adds'_aux.
          eapply refines_add; auto.
    Qed.

    Corollary refines_adds : forall ids (vs : list V) H,
        Forall (fun id => ~In id H) ids ->
        refines R H (adds ids vs H).
    Proof.
      intros * Hf.
      unfold adds. eapply refines_adds'.
      revert vs.
      induction Hf; intros [|]; simpl; auto.
    Qed.

    Lemma refines_adds_opt:
      forall {A} xs m1 m2 (vos1 vos2 : list (option A)),
        refines eq m2 m1 ->
        Forall2 (fun vo1 vo2 => forall v, vo2 = Some v -> vo1 = Some v) vos1 vos2 ->
        NoDup xs ->
        Forall (fun x => ~Env.In x m2) xs ->
        refines eq (Env.adds_opt xs vos2 m2) (Env.adds_opt xs vos1 m1).
    Proof.
      induction xs as [|x xs]; induction 2 as [|vo1 vo2 vos1 vos2 Hvo Hvos]; auto.
      inversion_clear 1 as [|? ? Hnxs Hndup].
      rewrite Forall_cons2; intros (? & Hnin).
      destruct vo1, vo2.
      - specialize (Hvo a0 eq_refl); inv Hvo.
        setoid_rewrite Env.adds_opt_cons_cons.
        auto using Env.refines_add_both.
      - setoid_rewrite Env.adds_opt_cons_cons'; auto.
        setoid_rewrite Env.adds_opt_cons_cons_None.
        apply IHxs; auto.
        apply Env.refines_add_right; auto using eq_Transitive.
      - now specialize (Hvo a eq_refl).
      - setoid_rewrite Env.adds_opt_cons_cons_None; auto.
    Qed.
  End RefinesAdds.

  Global Hint Resolve refines_adds' refines_adds refines_adds_opt : env.

  Lemma refines_map : forall {V1 V2} {eq1 : V1 -> V1 -> Prop} {eq2 : V2 -> V2 -> Prop} (f : V1 -> V2) H1 H2,
      (forall x y, eq1 x y -> eq2 (f x) (f y)) ->
      Env.refines eq1 H1 H2 ->
      Env.refines eq2 (map f H1) (map f H2).
  Proof.
    intros * Hf Href ?? Hfind1.
    rewrite Props.P.F.map_o in *.
    eapply option_map_inv in Hfind1 as (?&Hfind1&?); subst.
    eapply Href in Hfind1 as (?&?&Hfind1); subst.
    rewrite Hfind1; simpl. exists (f x1).
    split; auto.
  Qed.

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

  Global Hint Immediate In_add1 : env.
  Global Hint Extern 4 (In ?x (add ?y ?v ?env)) => apply In_add2 : env.
  Global Hint Extern 4 (refines _ ?x ?x) => reflexivity : env.
  Global Hint Immediate eq_Transitive : env.

  Lemma adds_opt_mono {A: Type}:
    forall x (env: t A) ys rvos,
      In x env ->
      In x (adds_opt ys rvos env).
  Proof.
    induction ys as [|y]; destruct rvos; auto.
    intros Hin.
    destruct o.
    - rewrite adds_opt_cons_cons.
      apply In_add2; auto.
    - rewrite adds_opt_cons_cons_None; auto.
  Qed.

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
      - inv HH; auto with env. take (List.In _ xs) and apply ED in it; auto with env.
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

    Lemma dom_elements: forall (e : t V),
        dom e (List.map fst (elements e)).
    Proof.
      intros * x; rewrite Props.P.F.elements_in_iff; split.
      - intros [v Hin]. rewrite InA_alt in Hin. destruct Hin as [[x' v'] [Heq Hin]].
        rewrite in_map_iff. exists (x', v'); simpl; split; auto.
        inv Heq; simpl in *. inv H; auto.
      - intro Hin. apply in_map_iff in Hin as [[x' v'] [? Hin]]; simpl; subst.
        exists v'; simpl. apply In_InA; auto. apply Props.P.eqke_equiv.
    Qed.

    Lemma dom_Perm : forall e xs ys,
        NoDup xs ->
        NoDup ys ->
        dom e xs ->
        dom e ys ->
        Permutation xs ys.
    Proof.
      intros * Hnd1 Hnd2 Hdom1 Hdom2.
      unfold dom in *.
      apply NoDup_Permutation; auto.
      intros x.
      rewrite <- Hdom1, <- Hdom2. reflexivity.
    Qed.

    Global Opaque dom.
  End EnvDom.

  Global Hint Extern 4 (dom ?env (?xs ++ nil)) => rewrite app_nil_r : env.
  Global Hint Immediate dom_empty : env.

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

  Add Parametric Morphism {A} : (@adds' A)
      with signature (eq ==> Equiv eq ==> Equiv eq)
        as adds'_Equiv.
  Proof.
    intros xs; induction xs as [|(?&?)]; intros * Heq; simpl; auto.
    apply IHxs. rewrite Heq. reflexivity.
  Qed.

  Import Permutation.

  Lemma adds'_Perm {A} : forall (xs ys : list (ident * A)) m,
      NoDupMembers xs ->
      Permutation xs ys ->
      Env.Equiv eq (adds' xs m) (adds' ys m).
  Proof.
    intros * Hnd Hperm. revert m.
    induction Hperm; intros *; simpl; eauto.
    - reflexivity.
    - inv Hnd. apply IHHperm; auto.
    - inv Hnd. inv H2.
      apply adds'_Equiv; auto.
      rewrite add_comm. reflexivity.
      contradict H1; subst.
      left; auto.
    - etransitivity; eauto.
      eapply IHHperm2.
      now rewrite <-Hperm1.
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
    apply dom_use with (x:=x) in DH.
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
    apply dom_use with (x:=y) in D.
    destruct (ident_eq_dec y x); subst.
    - setoid_rewrite In_find. rewrite grs, filter_In.
      split; [intros (? & ?); discriminate|intros (? & HH)].
      now rewrite nequiv_decb_refl in HH.
    - rewrite Props.P.F.remove_in_iff, D, filter_In.
      split; intros (H1 & H2); split; auto.
      now apply nequiv_decb_true.
  Qed.

  Lemma dom_map : forall {V1 V2} (f : V1 -> V2) xs H,
      dom (Env.map f H) xs <-> dom H xs.
  Proof.
    intros *; split; intros Hdom;
      eapply dom_intro; intros x.
    1,2:erewrite <-dom_use; eauto.
    1,2:erewrite Props.P.F.map_in_iff; reflexivity.
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
        apply dom_add_cons with (x:=i) (v:=v) in Hdom.
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
      - unfold adds; simpl in *; try lia.
      - destruct vs; simpl in *; try congruence.
        inv Hndup.
        destruct n.
        + unfold MapsTo in *.
          apply find_gsss; auto.
        + eapply IHids; eauto.
          lia.
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

    Lemma dom_ub_incl: forall H xs ys,
        incl xs ys ->
        dom_ub H xs ->
        dom_ub H ys.
    Proof.
      intros * Hincl Hd ? Hin.
      eapply Hincl, Hd; eauto.
    Qed.

    Corollary dom_ub_app:
      forall H xs ys,
        dom_ub H xs ->
        dom_ub H (xs ++ ys).
    Proof.
      intros * DH.
      eapply dom_ub_incl; eauto.
      eapply incl_appl, incl_refl; auto.
    Qed.

    Global Add Parametric Morphism (E : relation V) `{Equivalence _ E} : dom_ub
        with signature (Equiv E ==> @Permutation ident ==> iff)
          as dom_ub_Equiv_Permutation.
    Proof.
      intros env1 env2 EE xs1 xs2 Pxs. unfold dom_ub.
      setoid_rewrite EE.
      split; intros ?? HH;
        (rewrite Pxs||rewrite <-Pxs); eauto.
    Qed.

    Global Opaque dom_ub.
  End EnvDomUpperBound.

  Lemma dom_ub_map : forall {V1 V2} (f : V1 -> V2) xs H,
      dom_ub (Env.map f H) xs <-> dom_ub H xs.
  Proof.
    intros *; split; intros Hdom;
      eapply dom_ub_intro; intros x Hin.
    1,2:eapply dom_ub_use; [eauto|].
    1,2:erewrite Props.P.F.map_in_iff in *; auto.
  Qed.

  Lemma dom_ub_refines: forall {A R} (H H' : Env.t A) d,
      refines R H H' ->
      dom_ub H' d ->
      dom_ub H d.
  Proof.
    intros * Href Hdom.
    apply dom_ub_intro; intros * Hin.
    eapply dom_ub_use in Hdom; eauto.
    eapply In_refines; eauto.
  Qed.

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

    Lemma dom_lb_incl: forall H xs ys,
        incl xs ys ->
        dom_lb H ys ->
        dom_lb H xs.
    Proof.
      intros * Hincl Hlb ? Hin; auto.
    Qed.

    Lemma dom_lb_app:
      forall H xs ys,
        dom_lb H (xs ++ ys) ->
        dom_lb H xs.
    Proof.
      intros H xs ys DH x Ix.
      apply DH, in_or_app. auto.
    Qed.

    Lemma dom_lb_refines:
      forall R H H' xs,
        Env.refines R H H' ->
        dom_lb H xs ->
        dom_lb H' xs.
    Proof.
      intros * Href Hdom ? Hin.
      eapply In_refines; eauto.
    Qed.

    Lemma dom_lb_map:
      forall f H xs,
        dom_lb H xs <->
        dom_lb (map f H) xs.
    Proof.
      intros *; split; intros * Hdom ? Hin.
      - apply Props.P.F.map_in_iff; auto.
      - erewrite <-Props.P.F.map_in_iff; eauto.
    Qed.

    Lemma dom_lb_app': forall H xs ys,
        dom_lb H xs ->
        dom_lb H ys ->
        dom_lb H (xs ++ ys).
    Proof.
      intros * Hd1 Hd2 ? Hin.
      apply in_app_or in Hin as [Hin|Hin]; auto.
    Qed.

    Corollary dom_lb_concat: forall H xss,
        Forall (dom_lb H) xss ->
        dom_lb H (concat xss).
    Proof.
      intros * Hf.
      induction Hf; simpl; auto using dom_lb_nil, dom_lb_app'.
    Qed.

    Global Opaque dom_lb.
  End EnvDomLowerBound.

  Global Hint Resolve dom_lb_nil : env.

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
  Global Hint Resolve dom_lb_ub_dom : env.

  Lemma adds'_dom_ub : forall {A} (H : t A) d xs,
      dom_ub H d ->
      dom_ub (Env.adds' xs H) (d ++ List.map fst xs).
  Proof.
    intros * Hdom.
    apply dom_ub_intro; intros ? Hin.
    apply In_adds_spec' in Hin as [|].
    - apply in_or_app, or_intror. now apply fst_InMembers.
    - eapply dom_ub_use with (x:=x) in Hdom; eauto using in_or_app.
  Qed.

  Section adds_opt'.
    Import List.ListNotations.
    Definition adds_opt' {A : Type} (xos: list (option positive))
               (vs : list A) (e : Env.t A) : Env.t A :=
      fold_right (fun (xov: option positive * A) env =>
                    match xov with
                    | (Some x, v) => Env.add x v env
                    | _ => env end) e (combine xos vs).

    Lemma find_adds_opt'_spec_Some:
      forall {A} xs vs x (a : A) m,
        length xs = length vs ->
        Env.find x (adds_opt' xs vs m) = Some a ->
        List.In (Some x, a) (combine xs vs)
        \/ Env.find x m = Some a.
    Proof.
      unfold adds_opt'.
      induction xs as [|x'], vs as [|v']; simpl; auto; try discriminate.
      intros * Length Find; inv Length.
      destruct x'.
      - destruct (Pos.eq_dec x p) as [|].
        + subst; rewrite Env.gss in Find; inv Find; auto.
        + rewrite Env.gso in Find; auto.
          apply IHxs in Find as [|()]; auto.
      - apply IHxs in Find as [|]; auto.
    Qed.

    Lemma find_gsso_opt':
      forall {A}x x' xs (vs: list A) S,
        Some x <> x' ->
        Env.find x (adds_opt' (x' :: xs) vs S) =
        Env.find x (adds_opt' xs (tl vs) S).
    Proof.
      intros * Hneq.
      unfold adds_opt'.
      destruct vs. now destruct xs; auto.
      destruct x'; simpl; auto.
      rewrite Env.gso; auto. intro. apply Hneq. congruence.
    Qed.

    Lemma find_gsss_opt':
      forall {A} x v xs (vs: list A) S,
        Env.find x (adds_opt' (Some x :: xs) (v :: vs) S) = Some v.
    Proof.
      intros. unfold adds_opt'. apply Env.gss.
    Qed.

    Lemma find_In_gsso_opt':
      forall {A} x ys (vs: list A) env,
        ~ Ino x ys ->
        Env.find x (adds_opt' ys vs env) = Env.find x env.
    Proof.
      intros ? x ys vs env Hin.
      revert vs; induction ys; intro vs; simpl; auto.
      rewrite find_gsso_opt'.
      - apply IHys. rewrite Ino_In in *. intuition.
      - intro. apply Hin. rewrite Ino_In. now left.
    Qed.

    Lemma adds_opt'_cons_Some:
      forall {A} xs x (v: A) vs e,
        adds_opt' (Some x :: xs) (v :: vs) e =
        Env.add x v (adds_opt' xs vs e).
    Proof.
      induction xs as [|x']; intros; simpl; auto.
    Qed.

    Lemma adds_opt'_cons_None:
      forall {A} xs (v : A) vs e,
        adds_opt' (None :: xs) (v :: vs) e = adds_opt' xs vs e.
    Proof. auto. Qed.

    Lemma adds_opt'_app :
      forall {A} xs (vs : list A) xs' vs' m,
        length xs = length vs ->
        adds_opt' (xs ++ xs') (vs ++ vs') m
        = adds_opt' xs vs (adds_opt' xs' vs' m).
    Proof.
      induction xs as [|x xs IH]; simpl; intros * Hlen.
      - symmetry in Hlen. apply length_zero_iff_nil in Hlen. subst. auto.
      - destruct vs as [| v vs]; simpl in Hlen; inv Hlen.
        destruct x; simpl.
        + do 2 rewrite adds_opt'_cons_Some.
             rewrite IH; auto.
        + do 2 rewrite adds_opt'_cons_None.
          rewrite IH; auto.
    Qed.

    Lemma adds_opt'_nil:
      forall {A} vs (e : Env.t A),
        adds_opt' [] vs e = e.
    Proof. auto. Qed.

    Lemma adds_opt'_nil':
      forall {A} xs (e : Env.t A),
        adds_opt' xs [] e = e.
    Proof.
      unfold adds_opt'.
      setoid_rewrite combine_nil_r. simpl. auto.
    Qed.

    Lemma adds_opt'_None:
      forall {A B} xs vs (e : Env.t A),
        adds_opt' (List.map (fun _ : B => None) xs) vs e = e.
    Proof.
      induction xs; simpl. now setoid_rewrite adds_opt'_nil.
      destruct vs. now setoid_rewrite adds_opt'_nil'.
      setoid_rewrite adds_opt'_cons_None. auto.
    Qed.

    Lemma find_adds_opt'_disj:
      forall {A} (x : ident) xs xs' vs vs' (e : Env.t A),
        (forall x, Ino x xs -> ~ Ino x xs') ->
        Ino x xs ->
        Env.find x (adds_opt' xs vs e)
        = Env.find x (adds_opt' xs vs (adds_opt' xs' vs' e)).
    Proof.
      intros * Hino Hin.
      revert dependent x. revert vs. induction xs; intros; inv Hin.
      destruct a as [p|]; take (LiftO _ _ _) and inv it. destruct vs.
      do 2 rewrite adds_opt'_nil'.
         specialize (Hino p). simpl in Hino.
         specialize (Hino (or_introl (eq_refl p))).
         now rewrite find_In_gsso_opt'.
         now rewrite 2 find_gsss_opt'.
         destruct a as [p|], vs.
         + eapply IHxs with (vs := []) in H; eauto.
           2: intros; apply Hino; now right.
           now rewrite 2 adds_opt'_nil' in *.
         + destruct (decidable_eq_ident x p). subst.
           now rewrite 2 find_gsss_opt'.
           rewrite 2 find_gsso_opt'; simpl. 2-3: intro Heq; inv Heq; auto.
           apply IHxs; auto. intros. apply Hino. now right.
         + eapply IHxs with (vs := []) in H; eauto.
           2: intros; apply Hino; now right.
           now rewrite 2 adds_opt'_nil' in *.
         + rewrite 2 adds_opt'_cons_None; auto.
           apply IHxs; auto. intros. apply Hino. now right.
    Qed.

    Lemma find_permute_adds_opt':
      forall {A} (x : ident) xs xs' vs vs' (e : Env.t A),
        (forall x, Ino x xs -> ~ Ino x xs') ->
        Env.find x (adds_opt' xs vs (adds_opt' xs' vs' e))
        = Env.find x (adds_opt' xs' vs' (adds_opt' xs vs e)).
    Proof.
      intros * Hino.
      destruct (ino_dec x xs (ident_eq_dec)) as [Hin|Hin].
      - erewrite <- find_adds_opt'_disj; eauto.
        apply Hino in Hin. setoid_rewrite find_In_gsso_opt' at 2; auto.
      - rewrite find_In_gsso_opt'; auto.
        destruct (ino_dec x xs' (ident_eq_dec)) as [Hin'|Hin'].
        erewrite <- find_adds_opt'_disj; eauto. intros ?? HH.
        now apply Hino in HH.
        rewrite 3 find_In_gsso_opt'; auto.
    Qed.

    Lemma find_adds_opt'_ino:
      forall {A} (x : ident) xs vs (e : Env.t A),
        length xs = length vs ->
        Ino x xs ->
        Env.find x (adds_opt' xs vs e)
        = Env.find x (adds_opt' xs vs (Env.empty A)).
    Proof.
      induction xs. inversion 2. intros * Hlen Hino.
      destruct vs. inv Hlen. apply Ino_In in Hino. inv Hino.
      - now rewrite 2 find_gsss_opt'.
      - destruct a as [p|]. destruct (ident_eq_dec x p).
        subst. now rewrite 2 find_gsss_opt'.
        rewrite 2 find_gsso_opt'; try (intro HH; inv HH; auto).
        simpl. apply IHxs; auto. now apply Ino_In.
        rewrite 2 adds_opt'_cons_None. apply IHxs; auto. now apply Ino_In.
    Qed.

    Lemma In_find_adds_opt':
      forall {A} (x : ident) (v : A) xs vs m,
        NoDupo xs ->
        List.In (Some x, v) (combine xs vs) ->
        Env.find x (adds_opt' xs vs m) = Some v.
    Proof.
      induction xs. inversion 2.
      intros * Hdupo Hino. destruct vs. rewrite combine_nil_r in Hino.
      inv Hino. inv Hino. inv H. now rewrite find_gsss_opt'.
      destruct a as [p|]; inv Hdupo; try rewrite adds_opt'.
      destruct (Pos.eq_dec x p). subst.
      + now apply in_combine_l, Ino_In in H.
      + rewrite find_gsso_opt'; auto. congruence.
      + rewrite adds_opt'_cons_None; eauto.
    Qed.

    Lemma adds_opt'_adds: forall {A} xs (vs : list A) m,
        NoDup xs ->
        length xs = length vs ->
        Equal (adds_opt' (List.map Some xs) vs m) (adds xs vs m).
    Proof.
      induction xs; intros * Hndup Hlen; simpl; destruct vs; simpl in *; try congruence.
      - rewrite adds_opt'_nil, adds_nil_l. reflexivity.
      - inv Hndup. rewrite adds_cons_cons, adds_opt'_cons_Some; auto.
        apply Equal_add_both; eauto.
    Qed.

    Lemma adds_opt'_ignore: forall {A} xs1 xs2 (vs1 vs2 : list A) m,
        length xs1 = length vs1 ->
        length xs2 = length vs2 ->
        (forall x, Ino x xs2 -> Ino x xs1) ->
        Env.Equal (adds_opt' xs1 vs1 (adds_opt' xs2 vs2 m)) (adds_opt' xs1 vs1 m).
    Proof.
      intros * Hlen1 Hlen2 Hincl x. specialize (Hincl x). revert xs1 xs2 vs1 vs2 Hlen1 Hlen2 Hincl.
      induction xs1; intros; destruct vs1; simpl in *; try congruence.
      - repeat rewrite adds_opt'_nil.
        eapply find_In_gsso_opt'; eauto.
      - destruct a.
        + repeat rewrite adds_opt'_cons_Some.
          destruct (ident_eqb x p) eqn:Heq.
          * rewrite ident_eqb_eq in Heq; subst.
            repeat rewrite PositiveMap.gss. reflexivity.
          * rewrite ident_eqb_neq in Heq.
            repeat rewrite PositiveMap.gso; auto.
            eapply IHxs1; eauto.
            intros Hino. apply Hincl in Hino. destruct Hino as [Hino|?]; auto. congruence.
        + repeat rewrite adds_opt'_cons_None.
          apply IHxs1; auto.
          intros Hino. apply Hincl in Hino. destruct Hino as [Hino|?]; auto. inv Hino.
    Qed.

    Lemma adds_opt'_refines:  forall {A} xs1 (vs : list A) m,
        length xs1 = length vs ->
        Forall (fun x => forall id, x = Some id -> ~In id m) xs1 ->
        Env.refines eq m (adds_opt' xs1 vs m).
    Proof.
      induction xs1; intros * Hlen Hnin;
        destruct vs; simpl in *; try congruence.
      - repeat rewrite adds_opt'_nil. reflexivity.
      - inv Hnin. inv Hlen.
        specialize (IHxs1 _ _ H0 H2).
        destruct a.
        + specialize (H1 k eq_refl); subst.
          rewrite adds_opt'_cons_Some.
          intros ? ? Hfind. specialize (IHxs1 _ _ Hfind) as (v'&?&Hfind'); subst.
          exists v'. split; auto.
          destruct (Pos.eq_dec k x); subst.
          * exfalso. eapply find_In in Hfind; auto.
          * rewrite PositiveMap.gso; auto.
        + rewrite adds_opt'_cons_None; auto.
    Qed.

    Lemma adds_opt'_dom :  forall {A} ys xs (vs : list A) m,
        length ys = length vs ->
        Env.dom m xs ->
        Env.dom (adds_opt' ys vs m) (xs ++ map_filter id ys).
    Proof.
      induction ys; intros * Hlen Hdom;
        destruct vs; simpl in *; try congruence.
      - rewrite adds_opt'_nil, app_nil_r. assumption.
      - inv Hlen.
        specialize (IHys _ _ _ H0 Hdom).
        destruct a; simpl in *.
        + rewrite adds_opt'_cons_Some.
          rewrite dom_Permutation. apply dom_add_cons; eauto.
          erewrite <- Permutation.Permutation_middle; reflexivity.
        + rewrite adds_opt'_cons_None; eauto.
    Qed.
  End adds_opt'.

  Section union.
    Context {A : Type}.

    (** Union of two environments *)
    Definition union (m1 : t A) (m2 : t A) :=
      adds' (elements m2) m1.

    Lemma union_find_None : forall m1 m2 x,
        find x (union m1 m2) = None <->
        find x m1 = None /\ find x m2 = None.
    Proof.
      intros *. split; [intros Hf|intros (Hf1&Hf2)]; unfold union in *.
      - apply find_adds'_nIn in Hf as [? ?].
        split; auto.
        rewrite <- Props.P.F.not_find_in_iff. intro contra; apply H.
        apply In_Members; auto.
      - rewrite find_adds'_nIn. split; auto.
        intros contra. rewrite <- In_Members, In_find in contra.
        destruct contra. congruence.
    Qed.

    Variable R : A -> A -> Prop.
    Hypothesis Hequiv: Equivalence R.

    Lemma union_find1 : forall m1 m2 x y,
        find x m1 = Some y ->
        find x m2 = Some y ->
        find x (union m1 m2) = Some y.
    Proof.
      intros * Hf1 Hf2.
      eapply In_find_adds'; eauto.
      + apply NoDupMembers_elements.
      + apply PositiveMap.elements_correct; auto.
    Qed.

    Lemma union_find1' : forall m1 m2 x y1 y2,
        find x m1 = Some y1 ->
        find x m2 = Some y2 ->
        find x (union m1 m2) = Some y2.
    Proof.
      intros * Hf1 Hf2.
      eapply In_find_adds'; eauto.
      + apply NoDupMembers_elements.
      + apply PositiveMap.elements_correct; auto.
    Qed.

    Lemma union_find2 : forall m1 m2 x y,
        find x m1 = Some y ->
        find x m2 = None ->
        find x (union m1 m2) = Some y.
    Proof.
      intros * Hf1 Hf2.
      unfold union.
      rewrite gsso'; eauto.
      intro contra.
      rewrite <- In_Members in contra.
      rewrite <- Props.P.F.not_find_in_iff in Hf2; auto.
    Qed.

    Lemma union_find3 : forall m1 m2 x y,
        find x m1 = None ->
        find x m2 = Some y ->
        find x (union m1 m2) = Some y.
    Proof.
      intros * Hf1 Hf2.
      eapply In_find_adds'; eauto.
      + apply NoDupMembers_elements.
      + apply PositiveMap.elements_correct; auto.
    Qed.

    Corollary union_find3' : forall m1 m2 x y,
        find x m2 = Some y ->
        find x (union m1 m2) = Some y.
    Proof.
      intros * Hfind2.
      destruct (find x m1) eqn:Hfind1.
      - eapply union_find1'; eauto.
      - eapply union_find3; eauto.
    Qed.

    Lemma union_find4 : forall m1 m2 x y,
        find x (union m1 m2) = Some y ->
        find x m1 = Some y \/ find x m2 = Some y.
    Proof.
      intros * Hf.
      eapply find_adds'_In in Hf as [?|?]; eauto.
      eapply PositiveMap.elements_complete in H; eauto.
    Qed.

    Lemma union_find4' : forall m1 m2 x y,
        find x (union m1 m2) = Some y ->
        (find x m1 = Some y /\ find x m2 = None) \/ find x m2 = Some y.
    Proof.
      intros * Hfind.
      destruct (find x m2) eqn:Hfind2.
      - erewrite union_find3' in Hfind; eauto.
      - left; split; auto. destruct (find x m1) eqn:Hfind1.
        + erewrite union_find2 in Hfind; eauto.
        + symmetry. rewrite <-Hfind.
          eapply union_find_None; eauto.
    Qed.

    Lemma union_refines1 : forall m m',
        refines R m m' ->
        refines R m (union m m').
    Proof.
      intros * Href ? ? Hfind.
      specialize (Href _ _ Hfind) as (v'&?&?); subst.
      exists v'. split; auto.
      eapply union_find1'; eauto.
    Qed.

    Lemma union_refines2 : forall m m1 m2,
        refines R m m1 ->
        refines R m m2 ->
        refines R m (union m1 m2).
    Proof.
      intros * Href1 Href2 ? ? Hfind.
      specialize (Href1 _ _ Hfind) as (v1&?&?); subst.
      specialize (Href2 _ _ Hfind) as (v2&?&?); subst.
      exists v2. split; auto.
      eapply union_find1'; eauto.
    Qed.

    Lemma union_dom' : forall m1 m2 xs ys zs,
        dom m1 (xs ++ ys) ->
        dom m2 (xs ++ zs) ->
        dom (union m1 m2) (xs ++ ys ++ zs).
    Proof.
      intros * Hd1 Hd2.
      eapply dom_intro. intros x; split; intros.
      - apply In_find in H as (v&Hfind).
        apply union_find4 in Hfind as [Hf|Hf];
          (eapply find_In, dom_use in Hf; [|eauto]).
        1,2:repeat rewrite in_app_iff in *; destruct Hf; auto.
      - unfold union. rewrite In_adds_spec'.
        rewrite <- In_Members.
        repeat rewrite in_app_iff in H. destruct H as [H|[H|H]].
        + right. erewrite dom_use; [|eauto]. rewrite in_app_iff; auto.
        + right. erewrite dom_use; [|eauto]. rewrite in_app_iff; auto.
        + left. erewrite dom_use; [|eauto]. rewrite in_app_iff; auto.
    Qed.

    Fact dom_In_nIn : forall (m m' : t A) xs ys x,
        dom m xs ->
        dom m' (xs ++ ys) ->
        In x m' ->
        ~In x m ->
        (~List.In x xs /\ List.In x ys).
    Proof.
      intros * Hd1 Hd2 Hin Hnin.
      erewrite dom_use in Hin; [|eauto].
      erewrite dom_use in Hnin; [|eauto].
      split; auto.
      apply in_app_iff in Hin as [?|?]; auto.
      exfalso; auto.
    Qed.

    Lemma union_refines3 : forall m m1 m2 xs ys zs,
        NoDup (ys ++ zs) ->
        dom m xs ->
        dom m1 (xs ++ ys) ->
        dom m2 (xs ++ zs) ->
        refines R m m1 ->
        refines R m m2 ->
        refines R m1 (union m1 m2).
    Proof.
      intros * Hnd Hd Hd1 Hd2 Hr1 Hr2 ? ? Hfind.
      destruct (Env.find x m) eqn:Hfind'.
      - specialize (Hr1 _ _ Hfind') as (?&?&Hfind''); subst.
        rewrite Hfind'' in Hfind. inv Hfind.
        specialize (Hr2 _ _ Hfind') as (v2&?&?); subst.
        exists v2. split. 2:eapply union_find1'; eauto.
        etransitivity; eauto. symmetry; auto.
      - (* x ∈ zs /\ x ∉ xs *)
        eapply dom_In_nIn in Hd1 as (Hnin&Hin); eauto.
        2:apply find_In in Hfind; eauto.
        2:erewrite <- Props.P.F.not_find_in_iff in Hfind'; eauto.
        eapply NoDup_app_In in Hnd; eauto.
        exists v. split; try reflexivity. eapply union_find2; eauto.
        eapply find_not_In_dom; eauto.
        intro contra. apply in_app_iff in contra as [?|?]; auto.
    Qed.

    Lemma union_refines4 : forall m m1 m2 xs ys zs,
        NoDup (ys ++ zs) ->
        dom m xs ->
        dom m1 (xs ++ ys) ->
        dom m2 (xs ++ zs) ->
        refines R m m1 ->
        refines R m m2 ->
        refines R m2 (union m1 m2).
    Proof.
      intros * Hnd Hd Hd1 Hd2 Hr1 Hr2 ? ? Hfind.
      destruct (Env.find x m) eqn:Hfind'.
      - specialize (Hr2 _ _ Hfind') as (?&?&Hfind''); subst.
        rewrite Hfind'' in Hfind. inv Hfind.
        specialize (Hr1 _ _ Hfind') as (?&?&?); subst.
        exists v. split. 2:eapply union_find1'; eauto.
        reflexivity.
      - (* x ∈ ys /\ x ∉ xs *)
        eapply dom_In_nIn in Hd2 as (Hnin&Hin); eauto.
        2:apply find_In in Hfind; eauto.
        2:erewrite <- Props.P.F.not_find_in_iff in Hfind'; eauto.
        rewrite Permutation.Permutation_app_comm in Hnd. eapply NoDup_app_In in Hnd; eauto.
        exists v. split; try reflexivity. eapply union_find3; eauto.
        eapply find_not_In_dom; eauto.
        intro contra. apply in_app_iff in contra as [?|?]; auto.
    Qed.

    Lemma union_refines4' : forall m1 m2,
        refines R m2 (union m1 m2).
    Proof.
      intros * ?? Hfind.
      eapply union_find3' in Hfind; eauto.
      do 2 esplit; eauto. reflexivity.
    Qed.

    Lemma union_In : forall x e1 e2,
        In x (union e1 e2) <-> In x e1 \/ In x e2.
    Proof.
      intros *.
      repeat rewrite In_find.
      destruct (find x e1) eqn:Hf1, (find x e2) eqn:Hf2, (find x (union e1 e2)) eqn:Hf;
        (split; [intros (?&Heq); inv Heq|intros [(?&Heq)|(?&Heq)]; inv Heq]); eauto.
      1-5:exfalso.
      1-4:eapply union_find_None in Hf as (?&?); congruence.
      assert (find x (union e1 e2) = None); try congruence.
      rewrite union_find_None; auto.
    Qed.

    Corollary union_dom : forall m1 m2 xs ys,
        dom m1 xs ->
        dom m2 ys ->
        dom (union m1 m2) (xs ++ ys).
    Proof.
      intros * Hd1 Hd2.
      eapply dom_intro; intros.
      eapply Env.dom_use in Hd1. eapply Env.dom_use in Hd2.
      now rewrite union_In, in_app_iff, Hd1, Hd2.
    Qed.

    Lemma union_dom_lb : forall m1 m2 xs ys,
        dom_lb m1 xs ->
        dom_lb m2 ys ->
        dom_lb (union m1 m2) (xs ++ ys).
    Proof.
      intros * Hd1 Hd2.
      eapply dom_lb_intro; intros ? Hin.
      rewrite union_In.
      apply in_app_iff in Hin as [Hin|Hin]; [left|right].
      1,2:eapply Env.dom_lb_use; eauto.
    Qed.

    Lemma union_dom_lb2 : forall m1 m2 xs,
        dom_lb m2 xs ->
        dom_lb (union m1 m2) xs.
    Proof.
      intros * Hd1.
      eapply dom_lb_intro; intros ? Hin.
      rewrite union_In.
      right. eapply Env.dom_lb_use; eauto.
    Qed.

    Lemma union_dom_ub : forall m1 m2 xs,
        dom_ub m1 xs ->
        dom_ub m2 xs ->
        dom_ub (union m1 m2) xs.
    Proof.
      intros * Hd1 Hd2.
      eapply dom_ub_intro; intros ? Hin.
      rewrite union_In in Hin.
      destruct Hin as [Hin|Hin].
      1,2:eapply Env.dom_ub_use; [|eauto]; eauto.
    Qed.

    Lemma union_dom_ub_app : forall m1 m2 xs ys,
        dom_ub m1 xs ->
        dom_ub m2 ys ->
        dom_ub (union m1 m2) (xs ++ ys).
    Proof.
      intros * Hd1 Hd2.
      eapply dom_ub_intro; intros ? Hin.
      rewrite union_In in Hin. apply in_app_iff.
      destruct Hin as [Hin|Hin]; [left|right].
      1,2:eapply Env.dom_ub_use; eauto.
    Qed.

    Corollary union_mem : forall x e1 e2,
        mem x (union e1 e2) = mem x e1 || mem x e2.
    Proof.
      intros *.
      destruct (mem _ _) eqn:Hmem; symmetry.
      - rewrite Bool.orb_true_iff.
        repeat rewrite <-Props.P.F.mem_in_iff in *.
        apply union_In; auto.
      - rewrite Bool.orb_false_iff.
        repeat rewrite <-Props.P.F.not_mem_in_iff in *.
        apply Decidable.not_or. rewrite <-union_In; auto.
    Qed.

    Lemma elements_union : forall e1 e2,
        (forall x, Env.In x e1 -> ~Env.In x e2) ->
        Permutation.Permutation (elements (union e1 e2)) (elements e1 ++ elements e2).
    Proof.
      intros * Hnd. eapply elements_adds; eauto.
      eapply NoDupMembers_app; eauto using NoDupMembers_elements.
      intros * Hin. eapply In_Members, Hnd in Hin.
      contradict Hin. eapply In_Members; eauto.
    Qed.

    Definition unions (envs : list (Env.t A)) :=
      List.fold_left union envs (Env.empty _).
  End union.

  Add Parametric Morphism {A} (R : A -> A -> Prop) : union
      with signature Env.Equiv R ==> Env.Equiv R ==> Env.Equiv R
        as union_Equiv.
  Proof.
    intros * (Hk1&Hv1) * (Hk2&Hv2).
    constructor; intros *.
    - now rewrite 2 union_In, Hk1, Hk2.
    - intros Hfind1 Hfind2; unfold MapsTo in *.
      destruct (Env.find k x0) eqn:Hfind3.
      + erewrite union_find3' in Hfind1; eauto. inv Hfind1.
        eapply Hv2; eauto.
        assert (In k x0) as Hin by (econstructor; eauto).
        apply Hk2 in Hin as (?&Hfind4). unfold MapsTo in *.
        erewrite union_find3' in Hfind2; eauto.
        congruence.
      + destruct (Env.find k x) eqn:Hfind4.
        * erewrite union_find2 in Hfind1; eauto. inv Hfind1.
          eapply Hv1; eauto.
          assert (~In k x0) as Hnin by (intros (?&?); congruence).
          rewrite Hk2 in Hnin.
          assert (find k y0 = None) as Hfind5.
          { destruct (find k y0) eqn:Hfind; auto.
            contradict Hnin. econstructor; eauto. }
          assert (In k x) as Hin by (econstructor; eauto).
          apply Hk1 in Hin as (?&Hfind6). unfold MapsTo in *.
          erewrite union_find2 in Hfind2; eauto.
          congruence.
        * assert (find k (union x x0) = None); try congruence.
          eapply union_find_None; eauto.
  Qed.

  Section union_fuse.
    Context {A : Type}.

    Variable fuse : A -> A -> A.

    Definition union_fuse (m1 m2 : t A) :=
      Env.fold (fun x a1 m2 => add x (or_default_with a1 (fuse a1) (Env.find x m2)) m2) m1 m2.

    Lemma union_fuse_spec : forall m1 m2 x,
        find x (union_fuse m1 m2) =
        match (find x m1), (find x m2) with
        | Some y1, Some y2 => Some (fuse y1 y2)
        | Some y1, None => Some y1
        | None, Some y2 => Some y2
        | None, None => None
        end.
    Proof.
      intros *. unfold union_fuse. revert x.
      eapply Props.P.fold_rec.
      - intros ? Hemp ?.
        destruct (find x m) eqn:Hfind1.
        + exfalso. apply Hemp in Hfind1; auto.
        + destruct (find x m2); auto.
      - intros * Hfind1 Hnin Hadd Hrec ?.
        rewrite Hadd.
        destruct (ident_eq_dec x k); subst.
        + rewrite 2 Env.gss; simpl.
          rewrite Hrec; clear Hrec.
          destruct (find k m') eqn:Hfind2.
          { exfalso. apply Hnin. econstructor; eauto. }
          destruct (find k m2); simpl; auto.
        + repeat rewrite Env.gso; simpl; auto.
    Qed.

    Corollary union_fuse_In : forall m1 m2 x,
        In x (union_fuse m1 m2) <-> In x m1 \/ In x m2.
    Proof.
      intros *. repeat rewrite Props.P.F.in_find_iff.
      rewrite union_fuse_spec.
      destruct (find x m1), (find x m2); simpl.
      1-4:(split; [intros| intros [|]]; try congruence).
      1,2:left; congruence. right; congruence.
    Qed.

  End union_fuse.

  Section find_pred.
    Context {V : Type}.
    Variable P : key -> V -> bool.

    (** Find a key / value pair that respects P in the environment *)
    Definition find_pred (m : Env.t V) : option (key * V) :=
      fold (fun k v acc => if P k v then Some (k, v) else acc) m None.

    Lemma find_pred_spec : forall m k v,
        find_pred m = Some (k, v) ->
        MapsTo k v m /\ P k v = true.
    Proof.
      intros *. unfold find_pred.
      apply Props.P.fold_rec.
      - intros * _ contra. inv contra.
      - intros * Hmaps Hnin Hadd Hrec Heq.
        unfold MapsTo, Props.P.Add in *. rewrite Hadd; clear Hadd.
        destruct (P k0 e) eqn:Hpk; subst.
        + inv Heq.
          rewrite Env.gss; auto.
        + specialize (Hrec eq_refl) as (Hfind&Hp).
          split; auto.
          rewrite Env.gso; auto.
          intro contra; subst.
          apply find_In in Hfind. contradiction.
    Qed.
  End find_pred.

  (** Notations *)

  Declare Scope env_scope.

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
