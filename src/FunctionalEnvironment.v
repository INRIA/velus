From Velus Require Import Common.CommonTactics.
From Velus Require Import Common.
From Velus Require Import Operators.

From Coq Require Import Setoid Morphisms.
From Coq Require Import Classes.RelationClasses.
Import Relation_Definitions.

Module FEnv.

  Class fenv_key (A : Type) :=
    { fenv_key_eqdec : EqDec A eq }.

  Global Instance ident_fenv_key : fenv_key ident :=
    {| fenv_key_eqdec := EqDec_instance_0 |}.

  (** Encoding environment as "partial" functions. *)
  Section FEnv.
    Context {K : Type} `{K_key : fenv_key K}.
    Local Instance: EqDec K eq := { equiv_dec := fenv_key_eqdec }.

    Definition t A := K -> option A.

    Definition empty A : t A := fun _ => None.

    Section In.
      Context {A : Type}.

      Definition In x (env : t A) :=
        exists v, env x = Some v.

      Lemma find_In : forall env x v,
          env x = Some v -> In x env.
      Proof.
        intros * Find. esplit; eauto.
      Qed.

      Lemma not_find_In : forall env x,
          ~In x env <-> env x = None.
      Proof.
        unfold In; split.
        - intros Hnin.
          destruct (env x) eqn:Hfind; auto.
          exfalso; eauto.
        - intros Hnone (?&Hfind). congruence.
      Qed.
    End In.

    (** Environment equivalence *)
    Section Equiv.
      Context {A : Type} (R : relation A).

      Definition Equiv (env1 env2 : t A) : Prop :=
        forall x, (orel R) (env1 x) (env2 x).

      Global Instance Equiv_Reflexive `{Reflexive A R} : Reflexive Equiv.
      Proof.
        intro env. unfold Equiv. reflexivity.
      Qed.

      Global Instance Equiv_Transitive `{Transitive A R} :
        Transitive Equiv.
      Proof.
        unfold Equiv.
        intros env1 env2 env3 E12 E23 x.
        etransitivity; eauto.
      Qed.

      Global Instance Equiv_Symmetric `{Symmetric _ R} : Symmetric Equiv.
      Proof.
        unfold Equiv.
        intros env1 env2 E x.
        now symmetry.
      Qed.

      Global Add Parametric Relation `{Equivalence _ R} : (t A) Equiv
             reflexivity proved by Equiv_Reflexive
             symmetry proved by Equiv_Symmetric
             transitivity proved by Equiv_Transitive
             as Equivalence_Equiv.

      Global Add Parametric Morphism : In
             with signature (eq --> Equiv --> iff)
               as Equiv_In.
      Proof.
        intros * ? * Heq.
        split; intros (?&Hfind); subst;
          specialize (Heq x); rewrite Hfind in Heq; inv Heq;
          esplit; eauto.
      Qed.
    End Equiv.

    Global Existing Instance Equivalence_Equiv.

    (** Environment inclusion *)
    Section refines.
      Context {A : Type} (R : relation A).

      Definition refines (env1 env2 : t A) : Prop :=
        forall x v, env1 x = Some v ->
               exists v', R v v' /\ env2 x = Some v'.

      Global Add Parametric Morphism `{Equivalence _ R} : refines
             with signature (Equiv R ==> Equiv R ==> Basics.impl)
               as refines_Equiv.
      Proof.
        intros mA mA' EA mB mB' EB Href ?? Hfind.
        specialize (EA x). rewrite Hfind in EA; inv EA.
        symmetry in H0. apply Href in H0 as (?&HR&Hfind').
        specialize (EB x). rewrite Hfind' in EB; inv EB.
        do 2 esplit; eauto.
        etransitivity; [|eauto].
        symmetry. etransitivity; [|eauto]. now symmetry.
      Qed.

      Lemma In_refines : forall env1 env2,
          refines env1 env2 ->
          forall x, In x env1 -> In x env2.
      Proof.
        intros * Href * (?&?).
        apply Href in H as (?&?&?).
        esplit; eauto.
      Qed.

      Lemma refines_None : forall m1 m2 x,
          refines m1 m2 ->
          m2 x = None ->
          m1 x = None.
      Proof.
        intros * Href Hm2.
        rewrite <-not_find_In in *. contradict Hm2.
        eapply In_refines; eauto.
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

      Global Add Parametric Relation `{Reflexive _ R} `{Transitive _ R}
        : _ refines
             reflexivity proved by refines_refl
             transitivity proved by refines_trans
             as env_refines_preorder.

    End refines.

    (** Domain of environments *)

    Section dom.
      Context {A : Type}.

      Definition dom (env : t A) (xs : list K) :=
        forall x, In x env <-> List.In x xs.
    End dom.

    Section dom_ub.
      Context {A : Type}.

      Definition dom_ub (env : t A) (xs : list K) :=
        forall x, In x env -> List.In x xs.

      Lemma dom_ub_incl : forall env xs1 xs2,
          List.incl xs1 xs2 ->
          dom_ub env xs1 ->
          dom_ub env xs2.
      Proof.
        intros * Hsub Hdom ? Hin; auto.
      Qed.

      Lemma dom_ub_refines {R} : forall env1 env2 xs,
          refines R env2 env1 ->
          dom_ub env1 xs ->
          dom_ub env2 xs.
      Proof.
        intros * Href Hdom ? Hin; eauto using In_refines.
      Qed.

      Lemma dom_dom_ub: forall H d,
          dom H d ->
          dom_ub H d.
      Proof.
        intros * DH ?. apply DH.
      Qed.
    End dom_ub.

    Section dom_lb.
      Context {A : Type}.

      Definition dom_lb (env : t A) (xs : list K) :=
        forall x, List.In x xs -> In x env.

      Lemma dom_lb_incl : forall env xs1 xs2,
          List.incl xs2 xs1 ->
          dom_lb env xs1 ->
          dom_lb env xs2.
      Proof.
        intros * Hsub Hdom ? Hin; auto.
      Qed.

      Lemma dom_lb_refines {R} : forall env1 env2 xs,
          refines R env1 env2 ->
          dom_lb env1 xs ->
          dom_lb env2 xs.
      Proof.
        intros * Href Hdom ? Hin; eauto using In_refines.
      Qed.

      Lemma dom_dom_lb: forall H d,
          dom H d ->
          dom_lb H d.
      Proof.
        intros * DH ?. apply DH.
      Qed.
    End dom_lb.

    Section restrict.
      Context {A : Type}.

      Definition restrict (env : t A) (xs : list K) : t A :=
        fun x => if List.existsb (fun y => y ==b x) xs then env x else None.

      Lemma restrict_find : forall env xs x v,
          List.In x xs ->
          env x = Some v ->
          (restrict env xs) x = Some v.
      Proof.
        unfold restrict.
        intros * Hin Hfind.
        replace (List.existsb _ _) with true; auto.
        symmetry. apply List.existsb_exists.
        do 2 esplit; eauto. apply equiv_decb_refl.
      Qed.

      Lemma restrict_find_inv : forall env xs x v,
          (restrict env xs) x = Some v ->
          List.In x xs /\ env x = Some v.
      Proof.
        unfold restrict.
        intros * Hfind.
        cases_eqn Eq; try congruence.
        apply List.existsb_exists in Eq. simpl_Exists.
        rewrite equiv_decb_equiv in H0. now inv H0.
      Qed.

      Corollary restrict_find_None1 : forall env xs x,
          ~List.In x xs ->
          (restrict env xs) x = None.
      Proof.
        intros * Hnin.
        destruct (restrict _ _ _) eqn:Hres; auto.
        apply restrict_find_inv in Hres as (?&_); congruence.
      Qed.

      Corollary restrict_find_None2 : forall env xs x,
          env x = None ->
          (restrict env xs) x = None.
      Proof.
        intros * Hnin.
        destruct (restrict _ _ _) eqn:Hres; auto.
        apply restrict_find_inv in Hres as (_&?); congruence.
      Qed.

      Lemma restrict_find_None_inv : forall env xs x,
          (restrict env xs) x = None ->
          env x = None \/ ~List.In x xs.
      Proof.
        unfold restrict.
        intros * Hnin. cases_eqn Heq; auto.
        right. intro contra.
        apply existsb_Forall, forallb_Forall in Heq. simpl_Forall.
        rewrite equiv_decb_refl in Heq. inv Heq.
      Qed.

      Lemma restrict_refines : forall R xs (env : t A),
          Reflexive R ->
          refines R (restrict env xs) env.
      Proof.
        intros * Hrefl ?? Hfind.
        apply restrict_find_inv in Hfind as (?&?).
        do 2 esplit; eauto.
      Qed.

      Lemma restrict_refines' : forall R xs env1 env2,
          refines R env1 env2 ->
          refines R (restrict env1 xs) (restrict env2 xs).
      Proof.
        intros * Href ?? Hfind.
        apply restrict_find_inv in Hfind as (Hin&Hfind). apply Href in Hfind as (?&Heq&Hfind).
        do 2 esplit; eauto using restrict_find.
      Qed.

      Lemma incl_restrict_refines R `{Reflexive _ R} : forall xs ys (env : t A),
          List.incl xs ys ->
          refines R (restrict env xs) (restrict env ys).
      Proof.
        intros * Hincl ? v Hfind.
        exists v. split; auto.
        apply restrict_find_inv in Hfind as (?&?).
        apply restrict_find; auto.
      Qed.

      Lemma restrict_In : forall xs env x,
          In x (restrict env xs) <-> In x env /\ List.In x xs.
      Proof.
        split; [intros (?&Hfind)|intros ((?&Henv)&Hfind)].
        - apply restrict_find_inv in Hfind as (?&?).
          split; auto. econstructor; eauto.
        - econstructor; eauto using restrict_find.
      Qed.

      Corollary restrict_dom_ub : forall env xs,
          dom_ub (restrict env xs) xs.
      Proof.
        intros * ? Hin.
        now apply restrict_In in Hin as (?&?).
      Qed.

      Lemma restrict_Equiv : forall R xs env1 env2,
          Equiv R env1 env2 ->
          Equiv R (restrict env1 xs) (restrict env2 xs).
      Proof.
        unfold restrict.
        intros * Heq.
        intros x. specialize (Heq x). inv Heq.
        1,2:cases; constructor; auto.
      Qed.
    End restrict.

    (** Add an association to an environment *)
    Section add.
      Context {A : Type}.

      Definition add x v (env : t A) :=
        fun y => if (y ==b x) then Some v else env y.

      Lemma gss : forall x v env,
          (add x v env) x = Some v.
      Proof.
        unfold add.
        intros. now rewrite equiv_decb_refl.
      Qed.

      Lemma gso : forall x v env y,
          y <> x ->
          (add x v env) y = env y.
      Proof.
        unfold add.
        intros * Hneq. cases_eqn Eq.
        rewrite equiv_decb_equiv in Eq. inv Eq. congruence.
      Qed.

      Lemma add_In : forall env x v y,
          In y (add x v env) <-> x = y \/ In y env.
      Proof.
        unfold add.
        split; [intros (?&Hfind)|intros [?|(?&Hfind)]]; subst; cases_eqn Eq.
        - rewrite equiv_decb_equiv in Eq. inv Eq; auto.
        - right. econstructor; eauto.
        - econstructor. rewrite equiv_decb_refl. reflexivity.
        - destruct (y ==b x) eqn:Heq; econstructor; rewrite Heq; eauto.
      Qed.

      Lemma add_refines R `{Reflexive _ R} : forall env x v,
          ~In x env ->
          refines R env (add x v env).
      Proof.
        unfold add.
        intros * Hnin ?? Hfind.
        cases_eqn Eq; eauto. rewrite equiv_decb_equiv in Eq; inv Eq.
        exfalso. apply Hnin. econstructor; eauto.
      Qed.

      Lemma add_dom : forall env x v xs,
          dom env xs ->
          dom (add x v env) (x::xs).
      Proof.
        intros * Hdom y. specialize (Hdom y).
        now rewrite add_In, Hdom.
      Qed.

      Lemma add_dom_ub : forall env x v xs,
          dom_ub env xs ->
          dom_ub (add x v env) (x::xs).
      Proof.
        intros * Hdom y. specialize (Hdom y).
        rewrite add_In. intros [|]; subst; auto with datatypes.
      Qed.

      Lemma add_dom_lb : forall env x v xs,
          dom_lb env xs ->
          dom_lb (add x v env) (x::xs).
      Proof.
        intros * Hdom y. specialize (Hdom y).
        rewrite add_In. intros [|]; subst; auto.
      Qed.

    End add.

    (** Union of environments *)
    Section union.
      Context {A : Type}.

      (** The union prioritises the new (right) environment *)
      Definition union (env1 env2 : t A) :=
        fun x => match env2 x with
                 | Some v => Some v
                 | None => env1 x
                 end.

      Lemma union1 : forall env1 env2 x v,
          env1 x = Some v ->
          env2 x = Some v ->
          (union env1 env2) x = Some v.
      Proof.
        intros * Hfind1 Hfind2.
        unfold union. now rewrite Hfind2.
      Qed.

      Lemma union2 : forall env1 env2 x v,
          env1 x = Some v ->
          env2 x = None ->
          (union env1 env2) x = Some v.
      Proof.
        intros * Hfind1 Hfind2.
        unfold union. now rewrite Hfind2.
      Qed.

      Lemma union3 : forall env1 env2 x v,
          env1 x = None ->
          env2 x = Some v ->
          (union env1 env2) x = Some v.
      Proof.
        intros * Hfind1 Hfind2.
        unfold union. now rewrite Hfind2.
      Qed.

      Fact union3' : forall env1 env2 x v,
          env2 x = Some v ->
          (union env1 env2) x = Some v.
      Proof.
        intros * Hfind1.
        unfold union. now rewrite Hfind1.
      Qed.

      Lemma union4 : forall env1 env2 x v,
          (union env1 env2) x = Some v ->
          env1 x = Some v \/ env2 x = Some v.
      Proof.
        intros * Hfind.
        unfold union in *.
        destruct (env2 x); auto.
      Qed.

      Corollary union_None : forall env1 env2 x,
          (union env1 env2) x = None <-> env1 x = None /\ env2 x = None.
      Proof.
        unfold union; intros.
        split; [intros|intros (?&?)]; cases.
      Qed.

      Fact union4' : forall env1 env2 x v,
          (union env1 env2) x = Some v ->
          env2 x = Some v \/ (env1 x = Some v /\ env2 x = None).
      Proof.
        intros * Hfind.
        unfold union in *.
        destruct (env2 x); auto.
      Qed.

      Lemma union_In : forall env1 env2 x,
          In x (union env1 env2) <-> In x env1 \/ In x env2.
      Proof.
        split; [intros (?&Hfind)|intros [(?&?)|(?&Hfind2)]].
        - apply union4 in Hfind as [|]; [left|right]; econstructor; eauto.
        - destruct (env2 x) eqn:Hfind1;
            econstructor; eauto using union2, union3'.
        - econstructor; eauto using union3'.
      Qed.

      Add Parametric Morphism (R : A -> A -> Prop) : union
          with signature Equiv R ==> Equiv R ==> Equiv R
            as union_Equiv.
      Proof.
        intros * Heq1 * Heq2 ?.
        specialize (Heq1 x1); specialize (Heq2 x1).
        unfold union.
        inv Heq1; inv Heq2; constructor; auto.
      Qed.

      Lemma union_dom_ub : forall env1 env2 xs,
          dom_ub env1 xs ->
          dom_ub env2 xs ->
          dom_ub (union env1 env2) xs.
      Proof.
        intros * Hdom1 Hdom2 ?.
        rewrite union_In.
        intros [|]; auto.
      Qed.

      Lemma union_dom_lb : forall env1 env2 xs1 xs2,
          dom_lb env1 xs1 ->
          dom_lb env2 xs2 ->
          dom_lb (union env1 env2) (xs1 ++ xs2).
      Proof.
        intros * Hdom1 Hdom2 ?.
        rewrite List.in_app_iff, union_In.
        intros [|]; auto.
      Qed.

      Lemma union_dom_lb1 : forall env1 env2 xs,
          dom_lb env1 xs ->
          dom_lb (union env1 env2) xs.
      Proof.
        intros * Hdom1 ?.
        rewrite union_In; auto.
      Qed.

      Lemma union_dom_lb2 : forall env1 env2 xs,
          dom_lb env2 xs ->
          dom_lb (union env1 env2) xs.
      Proof.
        intros * Hdom2 ?.
        rewrite union_In; auto.
      Qed.

      Lemma union_refines1 R `{Reflexive _ R} : forall m1 m1' m2,
          refines R m1 m1' ->
          refines R (union m1 m2) (union m1' m2).
      Proof.
        intros * Href ?? Hfind.
        apply union4' in Hfind as [Hsome|(Hsome&Hnone)].
        - eauto using union3'.
        - apply Href in Hsome as (?&Hr&Hsome).
          eauto using union2.
      Qed.

      Lemma union_refines4' R `{Reflexive _ R} : forall m1 m2,
          refines R m2 (union m1 m2).
      Proof.
        intros * ?? Hfind.
        eapply union3' in Hfind; eauto.
      Qed.

      Lemma union_refines_inv R `{Reflexive _ R} : forall m1 m2 m',
          refines R (union m1 m2) m' ->
          (forall x, In x m1 -> ~In x m2) ->
          exists m2', Equiv R (union m1 m2') m'
                 /\ refines R m2 m2'
                 /\ (forall x, In x m2' <-> In x m' /\ ~In x m1).
      Proof.
        intros * Href Hnd.
        exists (fun x => match m1 x with Some v => None | None => m' x end).
        split; [|split].
        - unfold union. intros ?; simpl.
          destruct (m1 x) eqn:Hm1; auto.
          + assert (union m1 m2 x = Some a) as Hunion.
            { apply union2; auto. apply not_find_In.
              intro contra. eapply Hnd; eauto. econstructor; eauto. }
            apply Href in Hunion as (?&HR&Hm').
            rewrite Hm'. constructor; auto.
          + destruct (m' x); reflexivity.
        - intros ?? Hm2.
          assert (union m1 m2 x = Some v) as Hunion.
          { unfold union. now rewrite Hm2. }
          apply Href in Hunion as (?&HR&Hm').
          do 2 esplit; eauto.
          replace (m1 x) with (@None A); simpl; auto.
          symmetry. apply not_find_In. intro contra.
          eapply Hnd; eauto. econstructor; eauto.
        - split; [intros (?&Hin)|intros ((?&Hin)&Hnin)]; unfold In in *.
          + destruct (m1 x); try congruence.
            split; eauto. intros contra; destruct_conjs; congruence.
          + destruct (m1 x); [exfalso; eauto|eauto].
      Qed.

      Lemma union_assoc R `{Reflexive _ R} : forall m1 m2 m3,
          Equiv R (union m1 (union m2 m3)) (union (union m1 m2) m3).
      Proof.
        intros * ?. unfold union.
        cases_eqn Heq; try congruence; try reflexivity.
        1,2:inv Heq; reflexivity.
      Qed.
    End union.

    (** Mapping on an environment *)
    Section map.
      Context {A B : Type}.

      Definition map (f : A -> B) (env : t A) :=
        fun x => option_map f (env x).

      Lemma map_in_iff f : forall x env,
          In x (map f env) <-> In x env.
      Proof.
        intros.
        unfold In, map.
        split; intros (?&Heq); inv_equalities; eauto.
        rewrite Heq; simpl; eauto.
      Qed.

      Lemma dom_map f : forall env xs,
          dom (map f env) xs <-> dom env xs.
      Proof.
        intros. unfold dom.
        now setoid_rewrite map_in_iff.
      Qed.

      Lemma dom_ub_map f : forall env xs,
          dom_ub (map f env) xs <-> dom_ub env xs.
      Proof.
        intros. unfold dom_ub.
        now setoid_rewrite map_in_iff.
      Qed.

      Lemma dom_lb_map f : forall env xs,
          dom_lb (map f env) xs <-> dom_lb env xs.
      Proof.
        intros. unfold dom_lb.
        now setoid_rewrite map_in_iff.
      Qed.

      Lemma map_Equiv (R1 : relation A) (R2 : relation B) f : forall env1 env2,
          (forall x y, R1 x y -> R2 (f x) (f y)) ->
          Equiv R1 env1 env2 ->
          Equiv R2 (map f env1) (map f env2).
      Proof.
        unfold map.
        intros * Hrel Heq x.
        specialize (Heq x); inv Heq; constructor; auto.
      Qed.

      Lemma refines_map (R1 : relation A) (R2 : relation B) f : forall env1 env2,
          (forall x y, R1 x y -> R2 (f x) (f y)) ->
          refines R1 env1 env2 ->
          refines R2 (map f env1) (map f env2).
      Proof.
        unfold map.
        intros * Hrel Href ?? Hfind.
        inv_equalities. apply Href in Hf as (?&?&Hfind).
        rewrite Hfind. eauto.
      Qed.

      Lemma restrict_map R `{Reflexive _ R} f : forall env xs,
          Equiv R (restrict (map f env) xs) (map f (restrict env xs)).
      Proof.
        unfold restrict, map.
        intros * ?. cases; simpl; reflexivity.
      Qed.

      Lemma union_map R `{Reflexive _ R} f : forall env1 env2,
          Equiv R (map f (union env1 env2)) (union (map f env1) (map f env2)).
      Proof.
        unfold union, map.
        intros * ?. destruct (env2 _); simpl; reflexivity.
      Qed.
    End map.

    Lemma map_map {A B C} R `{Reflexive _ R} : forall env (f1 : A -> B) (f2 : B -> C),
        Equiv R (map f2 (map f1 env)) (map (fun x => f2 (f1 x)) env).
    Proof.
      intros * ?. unfold map.
      destruct (env x); simpl; reflexivity.
    Qed.

    Section mapi.
      Context {A B : Type}.

      Definition mapi (f : K -> A -> B) (env : t A) :=
        fun x => option_map (f x) (env x).

      Lemma mapi_in_iff f : forall x env,
          In x (mapi f env) <-> In x env.
      Proof.
        intros.
        unfold In, mapi.
        split; intros (?&Heq); inv_equalities; eauto.
        rewrite Heq; simpl; eauto.
      Qed.
    End mapi.

    Section of_list.
      Context {A : Type}.

      Definition of_list (l : list (K * A)) : t A :=
        fun x => option_map snd (List.find (fun y => x ==b fst y) l).

      Lemma of_list_find_In : forall l x a,
          (of_list l) x = Some a ->
          List.In (x, a) l.
      Proof.
        unfold of_list; intros. inv_equalities.
        apply List.find_some in Hf as (Hin&Heq).
        rewrite equiv_decb_equiv in Heq. now inv Heq.
      Qed.

      Fact find_some' : forall {A} (xs : list (K * A)) x v ,
          NoDupMembers xs ->
          List.In (x, v) xs ->
          List.find (fun xtc => x ==b fst xtc) xs = Some (x, v).
      Proof.
        induction xs; intros * Hndup Hin; inv Hin; inv Hndup; simpl.
        - now rewrite equiv_decb_refl.
        - cases_eqn Eq.
          rewrite equiv_decb_equiv in Eq. inv Eq.
          apply In_InMembers in H. contradiction.
      Qed.

      Lemma of_list_In_find : forall l x a,
          NoDupMembers l ->
          List.In (x, a) l ->
          (of_list l) x = Some a.
      Proof.
        unfold of_list; intros.
        erewrite find_some'; eauto. auto.
      Qed.

      Lemma of_list_In : forall l x,
          In x (of_list l) <-> InMembers x l.
      Proof.
        unfold of_list.
        split; [intros (?&Hfind)|intros Hin].
        - inv_equalities. apply List.find_some in Hf as (In&Eq).
          rewrite equiv_decb_equiv in Eq; inv Eq; eauto using In_InMembers.
        - apply InMembers_In in Hin as (?&Hin).
          destruct (List.find (fun y => x ==b fst y) l) eqn:Hass.
          + esplit; eauto. now rewrite Hass.
          + exfalso. eapply List.find_none in Hass; [|eauto].
            rewrite equiv_decb_refl in Hass; inv Hass.
      Qed.

      Lemma of_list_None : forall l x,
          (of_list l) x = None <-> ~InMembers x l.
      Proof.
        intros.
        split; intros H.
        - intros contra. apply of_list_In in contra as (?&?); congruence.
        - destruct (of_list _ _) eqn:Hofl; auto.
          apply of_list_find_In, In_InMembers in Hofl. congruence.
      Qed.

    End of_list.

  End FEnv.
End FEnv.

(** Hints *)

Global Hint Resolve FEnv.refines_refl : fenv.
Global Hint Unfold FEnv.map FEnv.mapi : fenv.

(** Simplification tactic *)

Ltac simpl_fenv :=
  autounfold with fenv in *;
  inv_equalities.

(** Notations *)

Declare Scope fenv_scope.
Infix "+" := FEnv.union (left associativity, at level 50) : fenv_scope.
Delimit Scope fenv_scope with fenv.
