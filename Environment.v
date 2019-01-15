Require Import Velus.Common.

Require Import List.
Require Import Coq.Structures.OrderedType.
Require Import Coq.Structures.OrderedTypeEx.

Module POTB := PositiveOrderedTypeBits.

Import List.ListNotations.

Set Implicit Arguments.

Definition t (A: Type) := list (ident * A).

Section Global.

  Variable A B: Type.

  Definition empty : t A := [].

  Fixpoint find (x: ident) (e: t A) : option A :=
    match e with
    | [] => None
    | (y, a) :: e' =>
      match POTB.compare x y with
      | LT _ => None
      | EQ _ => Some a
      | GT _ => find x e'
      end
    end.

  Definition mem (x: ident) (e: t A) : bool :=
    match find x e with
    | Some _ => true
    | None => false
    end.

  Fixpoint add (x: ident) (a: A) (e: t A) : t A :=
    match e with
    | [] => [(x, a)]
    | (y, b) :: e' =>
      match POTB.compare x y with
      | LT _ => (x, a) :: e
      | EQ _ => (x, a) :: e'
      | GT _ => (y, b) :: add x a e'
      end
    end.

  Definition map (f: A -> B) (e: t A) : t B :=
    List.map (fun (xa: ident * A) =>
                let (x, a) := xa in
                (x, f a))
             e.

  Definition mapi (f: ident -> A -> B) (e: t A) : t B :=
    List.map (fun (xa: ident * A) =>
                let (x, a) := xa in
                (x, f x a))
             e.

  (* Function eqb (cmp: A -> A -> bool) (e e' : t A) {struct e} : bool := *)
  (*   match e, e' with *)
  (*   | [], [] => true *)
  (*   | (x, a) :: e, (x', a') :: e' => *)
  (*     match POTB.compare x x' with *)
  (*      | EQ _ => cmp a a' && eq cmp e e' *)
  (*      | _ => false *)
  (*     end *)
  (*  | _, _ => false *)
  (* end. *)

  Definition eq (e e' : t A) : Prop := forall x, find x e = find x e'.

  Lemma eq_refl: reflexive _ eq.
  Proof.
    intros ?; unfold eq; reflexivity.
  Qed.

  Lemma eq_symm: symmetric _ eq.
  Proof.
    intros ? ?; unfold eq; auto.
  Qed.

  Lemma eq_trans: transitive _ eq.
  Proof.
    intros ? ? ?; unfold eq; intros E1 E2 e.
    now rewrite E1, E2.
  Qed.

  Add Parametric Relation : (t A)  eq
      reflexivity proved by eq_refl
      symmetry proved by eq_symm
      transitivity proved by eq_trans
        as Eq_eq.

  Fact compare_eq:
    forall x,
    exists H, POTB.compare x x = EQ H.
  Proof.
    intros; destruct (POTB.compare x x) as [|Eq|];
      try (now exfalso; eapply POTB.bits_lt_antirefl; eauto).
    exists Eq; auto.
  Qed.

  Theorem gss:
    forall x a e,
      find x (add x a e) = Some a.
  Proof.
    induction e as [|[y]]; simpl.
    - destruct (compare_eq x) as [? E]; now rewrite E.
    - destruct (POTB.compare x y) eqn: Cmp; simpl.
      + destruct (compare_eq x) as [? E]; now rewrite E.
      + destruct (compare_eq x) as [? E]; now rewrite E.
      + now rewrite Cmp.
  Qed.

  Corollary gss':
    forall x y a e,
      ident_eqb x y = true ->
      find x (add y a e) = Some a.
  Proof.
    intros ** E; rewrite ident_eqb_eq in E; subst; apply gss.
  Qed.

  Theorem gso:
    forall x y a e,
      x <> y ->
      find x (add y a e) = find x e.
  Proof.
    induction e as [|[z]]; intros Neq; simpl.
    - destruct (POTB.compare x y); simpl; auto.
      now contradict Neq.
    - destruct (POTB.compare y z) eqn: Eyz, (POTB.compare x z) eqn: Exz, (POTB.compare x y) eqn: Exy;
        simpl; try rewrite Exy; try rewrite Exz; auto;
          try (now contradict Neq);
          try repeat match goal with
                H: POTB.eq ?a ?b |- _ =>
                assert (a = b); auto; subst b;
                  exfalso; apply (POTB.bits_lt_antirefl a);
                    etransitivity; eauto
              end.
      exfalso; apply (POTB.bits_lt_antirefl x);
        do 2 (etransitivity; eauto).
  Qed.

  Corollary gso':
    forall x y a e,
      ident_eqb x y = false ->
      find x (add y a e) = find x e.
  Proof.
    intros ** E; rewrite ident_eqb_neq in E; now apply gso.
  Qed.

  Lemma find_cons_eq:
    forall x a e,
      find x ((x, a) :: e) = Some a.
  Proof.
    intros; simpl.
    destruct (compare_eq x) as [? E]; now rewrite E.
  Qed.

  Lemma find_cons_lt:
    forall x y a e,
      POTB.lt x y ->
      find x ((y, a) :: e) = None.
  Proof.
    intros ** E; simpl.
    destruct (POTB.compare x y) eqn: Exy; auto.
    - assert (x = y); auto; subst; contradict E; apply POTB.bits_lt_antirefl.
    - exfalso; apply (POTB.bits_lt_antirefl x);
        do 2 (etransitivity; eauto).
  Qed.

  Theorem find_in:
    forall x a e,
      find x e = Some a ->
      In (x, a) e.
  Proof.
    induction e as [|(y, b)]; simpl.
    - intro; discriminate.
    - intro H; destruct (POTB.compare x y); try discriminate.
      + assert (x = y); auto; inv H; auto.
      + right; auto.
  Qed.

  Definition add_list (xvs: list (ident * A)) (e: t A) :=
    fold_right (fun (xv: ident * A) env =>
                  let (x , v) := xv in
                  add x v env) e xvs.

  Definition adds xs (vs : list A) :=
    add_list (combine xs vs).

  Definition from_list (xvs: list (ident * A)) :=
    add_list xvs empty.

  Lemma add_comm:
    forall x x' (v v': A) m,
      x <> x' ->
      add x v (add x' v' m) = add x' v' (add x v m).
  Proof.
    Ltac aux :=
      try match goal with
          (* | H: POTB.lt ?x' ?y, H': POTB.lt ?y ?x, H'': POTB.lt ?x ?x' |- _ => *)
          (*   let E := fresh in *)
          (*   assert (POTB.lt x' x) by (now transitivity y); *)
          (*   assert (POTB.lt x' x') as E by (now transitivity x); *)
          (*   apply POTB.lt_not_eq in E; exfalso; apply E; reflexivity *)
          | H: POTB.lt ?x ?x', H': POTB.eq ?x' ?x |- _ =>
            apply POTB.lt_not_eq in H; symmetry in H'; contradiction
          | H: POTB.lt ?x ?x', H': POTB.eq ?x ?x' |- _ =>
            apply POTB.lt_not_eq in H; contradiction
          | H: POTB.lt ?x ?x', H': POTB.lt ?x' ?x |- _ =>
            let E := fresh in
            assert (POTB.lt x x) as E by (now transitivity x');
            apply POTB.lt_not_eq in E; exfalso; apply E; reflexivity
          | H: POTB.lt ?x ?x', H': POTB.lt ?x' ?y, H'': POTB.eq ?x ?y |- _ =>
            let E := fresh in
            assert (POTB.lt x y) as E by (now transitivity x');
            apply POTB.lt_not_eq in E; contradiction
          | H: POTB.lt ?x ?x', H': POTB.lt ?x' ?y, H'': POTB.eq ?y ?x |- _ =>
            let E := fresh in
            assert (POTB.lt x y) as E by (now transitivity x');
            apply POTB.lt_not_eq in E; symmetry in H''; contradiction
          | H: ?x <> ?x', H': POTB.eq ?x' ?y, H'': POTB.eq ?x ?y |- _ =>
            exfalso; apply H; now rewrite H', H''
          | H: ?x <> ?x', H': POTB.eq ?x' ?x |- _ =>
            exfalso; apply H; now rewrite H'
          | H: POTB.eq ?x' ?y, H': POTB.lt ?y ?x, H'': POTB.lt ?x ?x' |- _ =>
            rewrite H in H'';
            let E := fresh in
            assert (POTB.lt x x) as E by (now transitivity y);
            apply POTB.lt_not_eq in E; exfalso; apply E; reflexivity
           end; try contradiction; auto.

    intros ** Neq.
    revert dependent x; revert v v' x'; induction m as [|(y, w)]; simpl; intros.
    - destruct (POTB.compare x x'), (POTB.compare x' x); aux.
    - destruct (POTB.compare x' y) eqn: E, (POTB.compare x y) eqn: E'; simpl;
        try rewrite E; try rewrite E'; try (f_equal; auto);
          try destruct (POTB.compare x x'); try destruct (POTB.compare x' x); aux.
      + assert (POTB.lt x' x) by (now transitivity y);
          assert (POTB.lt x' x') as E'' by (now transitivity x);
          apply POTB.lt_not_eq in E''; exfalso; apply E''; reflexivity.
      + assert (POTB.lt y x) by (now transitivity x');
          assert (POTB.lt y y) as E'' by (now transitivity x);
          apply POTB.lt_not_eq in E''; exfalso; apply E''; reflexivity.
  Qed.

  Lemma add_list_cons_cons:
    forall x (v: A) xvs e,
      ~ InMembers x xvs ->
      add_list ((x, v) :: xvs) e = add_list xvs (add x v e).
  Proof.
    unfold add_list.
    induction xvs as [|(x', v')]; intros ** NotIn; simpl; auto.
    rewrite <-IHxvs.
    - simpl.
      rewrite add_comm; auto.
      intro Eq.
      apply NotIn; subst.
      now constructor.
    - apply NotInMembers_cons in NotIn; tauto.
  Qed.

  Lemma adds_cons_cons:
    forall xs x (v: A) vs e,
      ~ In x xs ->
      adds (x :: xs) (v :: vs) e = adds xs vs (add x v e).
  Proof.
    unfold adds; intros ** NotIn.
    apply add_list_cons_cons.
    intro; eapply NotIn, InMembers_In_combine; eauto.
  Qed.

  Lemma find_gsso:
    forall x x' xs (vs: list A) S,
      x <> x' ->
      find x (adds (x' :: xs) vs S) = find x (adds xs (tl vs) S).
  Proof.
    intros ** Hneq.
    unfold adds.
    destruct vs. destruct xs; reflexivity.
    simpl. rewrite gso; auto.
  Qed.

  Lemma not_In_find_adds:
    forall x xs (v: option A) vs S,
      ~In x xs ->
      find x S = v ->
      find x (adds xs vs S) = v.
  Proof.
    induction xs as [|xty xs]; auto.
    intros v vs S Hnin Hfind.
    apply not_in_cons in Hnin.
    destruct Hnin as [Hnin Hneq].
    rewrite find_gsso; auto.
  Qed.

  Lemma In_find_add_list:
    forall x v xvs S,
      NoDupMembers xvs ->
      In (x, v) xvs ->
      find x (add_list xvs S) = Some v.
  Proof.
    induction xvs as [|(x', v') xvs]; try contradiction.
    inversion_clear 1; inversion_clear 1 as [E|]; simpl.
    - inv E; now rewrite gss.
    - rewrite gso; auto.
      eapply InMembers_neq; eauto.
      eapply In_InMembers; eauto.
  Qed.

  Lemma In_find_add_list':
    forall x v xvs S,
      NoDupMembers xvs ->
      find x S = None ->
      find x (add_list xvs S) = Some v ->
      In (x, v) xvs.
  Proof.
    induction xvs as [|(x', v') xvs]; simpl.
    - intros ** ->; discriminate.
    - inversion_clear 1; intros ** Find.
      destruct (ident_eq_dec x x').
      + subst; rewrite gss in Find; inv Find; auto.
      + rewrite gso in Find; auto.
        right; eauto.
  Qed.

  Add Parametric Morphism x v: (add x v)
      with signature eq ==> eq
        as add_eq.
  Proof.
    unfold eq; intros ** y.
    destruct (ident_eq_dec x y).
    - subst; now rewrite 2 gss.
    - rewrite 2 gso; auto.
  Qed.

  Add Parametric Morphism xvs: (add_list xvs)
      with signature eq ==> eq
        as add_list_eq.
  Proof.
    unfold add_list.
    induction xvs as [|(y, a)]; intros ** E x; simpl; auto.
    erewrite add_eq.
    Focus 2.
    apply IHxvs; eauto.
    auto.
  Qed.

  Lemma add_ps_from_list_cons:
    forall xvs x v,
      eq (add x v (from_list xvs))
         (from_list ((x, v) :: xvs)).
  Proof.
    intros; unfold from_list; reflexivity.
  Qed.

End Global.

Theorem find_map:
  forall (A B: Type) (x: ident) (e: t A) (f: A -> B),
    find x (map f e) = option_map f (find x e).
Proof.
  induction e as [|[y]]; simpl; intros; auto.
  destruct (POTB.compare x y); auto.
Qed.

Theorem find_mapi:
  forall (A B: Type) (x: ident) (e: t A) (f: ident -> A -> B),
    find x (mapi f e) = option_map (f x) (find x e).
Proof.
  induction e as [|[y]]; simpl; intros; auto.
  destruct (POTB.compare x y); auto.
  assert (x = y); auto; subst; auto.
Qed.
