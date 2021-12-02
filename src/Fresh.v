From Coq Require Import List Sorting.Permutation.
Import List.ListNotations.
Open Scope list_scope.
From Coq Require Import Classes.RelationClasses.
From Coq Require Import Setoid Morphisms.

From Velus Require Import Common.
From Velus Require Import Environment.

(** * Fresh name generation *)

(** The fresh monad (with memory) : generates new names and keeps
    a record of each name generated along with some information

    The file is structured as such:

    - a signature FRESHKERNEL, which exposes the kernel features of the monad
    - a functor FreshKernel which implements the previous signature,
      and contains some gruesome definitions details that we prefer to hide
    - a functor Fresh that includes FreshKernel and also offers some additional lemmas.
      This module should be instanciated using an IDS module that contains, among other things,
      the gensym function used for name generation
 *)
Module Type FRESHKERNEL
       (Import Ids : IDS).

  (** The Monad manipulates a state, which exposes a list of the identifiers generated
      by the monad, paired with some data *)
  Section st.
    Parameter fresh_st : Type -> Type.
    Context {B : Type}.
    Parameter st_anns : fresh_st B -> list (ident * B).
    Definition st_ids (st : fresh_st B) := map fst (st_anns st).
  End st.

  Definition Fresh (A B : Type) : Type := fresh_st B -> A * fresh_st B.

  (** The state can be deemed as "valid".
      [st_valid_after st prefix aft] means that the state only contains
      identifier prefixed by [prefix] and that are distinct from the ones in [aft].
      This properties also ensures that all ids in the state are distinct *)
  Section validity.
    Context {B : Type}.
    Parameter st_valid_after : fresh_st B -> ident -> PS.t -> Prop.
    Conjecture st_valid_NoDup : forall st prefix aft,
        st_valid_after st prefix aft ->
        NoDup (st_ids st++PSP.to_list aft).
    Conjecture st_valid_PSeq : forall st prefix aft1 aft2,
        PS.eq aft1 aft2 ->
        st_valid_after st prefix aft1 ->
        st_valid_after st prefix aft2.
    Conjecture st_valid_prefixed : forall st prefix aft,
        st_valid_after st prefix aft ->
        Forall (fun x => exists n hint, x = gensym prefix hint n) (st_ids st).
  End validity.

  (** [st_follows] forms an inclusion relation over the contents of the states.
      We show below that every primimitive Fresh operation produces a new state
      that follows the previous one *)
  Section follows.
    Context {B : Type}.
    Parameter st_follows : fresh_st B -> fresh_st B -> Prop.
    Conjecture st_follows_refl : Reflexive st_follows.
    Conjecture st_follows_trans : Transitive st_follows.
    Conjecture st_follows_incl : forall st st',
        st_follows st st' ->
        incl (st_anns st) (st_anns st').
  End follows.

  (** The initial state is empty.
      An empty state is valid under a few assumption :
      - the [prefix] used for generating must be different from the ones used previously.
      - in the case of [st_valid_reuse], the reusable and non-reusable idents must be distinct
      When initializing *)
  Section init.
    Context {B : Type}.
    Parameter init_st : fresh_st B.
    Conjecture init_st_anns : st_anns init_st = [].
    Conjecture init_st_valid : forall prefix aft aftprefs,
        ~PS.In prefix aftprefs ->
        PS.For_all (AtomOrGensym aftprefs) aft ->
        st_valid_after init_st prefix aft.
  End init.

  (** The central function for fresh identifier generation,
      [fresh_ident prefix hint d] generates a new identifier prefixed by [prefix] and
      associated with data [d] in the new state.
      If a value is passed for [hint], it will show up in the generated identifier.
      [fresh_ident prefix d] preserves validity as long as [prefix] is the correct one *)
  Section fresh_ident.
    Context {B : Type}.
    Parameter fresh_ident : ident -> option ident -> B -> Fresh ident B.

    Conjecture fresh_ident_anns : forall pref hint b id st st',
        fresh_ident pref hint b st = (id, st') ->
        st_anns st' = (id, b)::(st_anns st).

    Conjecture fresh_ident_st_valid : forall pref hint b id st st' aft,
        fresh_ident pref hint b st = (id, st') ->
        st_valid_after st pref aft ->
        st_valid_after st' pref aft.
    Conjecture fresh_ident_st_follows : forall pref hint b id st st',
        fresh_ident pref hint b st = (id, st') ->
        st_follows st st'.

    Conjecture fresh_ident_prefixed : forall pref hint b id st st',
        fresh_ident pref hint b st = (id, st') ->
        exists n hint, id = gensym pref hint n.
  End fresh_ident.

  (** Generate some fresh identifiers for alpha-renaming purposes.
      Also rename inside the provided annotations using the rename function passed.
      Returns the pairs with new idents and transformed annots, as well as the substitution itself.
      Depending on the value of the flag `save`, the generated identifiers can be saved in the state or not
   *)
  Section fresh_idents_rename.
    Context {B : Type}.

    Parameter fresh_idents_rename : ident -> list (ident * B) -> (Env.t ident -> B -> B) -> Fresh (list (ident * B) * Env.t ident) B.

    Conjecture fresh_idents_rename_ids : forall pref ids frename ids' sub st st',
        NoDupMembers ids ->
        fresh_idents_rename pref ids frename st = ((ids', sub), st') ->
        ids' = map (fun '(x, ann) => (or_default x (Env.find x sub), frename sub ann)) ids.

    Conjecture fresh_idents_rename_sub1 : forall pref ids frename ids' sub st st' x,
        fresh_idents_rename pref ids frename st = ((ids', sub), st') ->
        Env.In x sub -> InMembers x ids.

    Conjecture fresh_idents_rename_sub2 : forall pref ids frename ids' sub st st' x,
        fresh_idents_rename pref ids frename st = ((ids', sub), st') ->
        InMembers x ids <-> exists y n, Env.MapsTo x y sub /\ y = gensym pref (Some x) n.

    Conjecture fresh_idents_rename_sub_NoDup : forall pref ids frename ids' sub st st',
        NoDupMembers ids ->
        fresh_idents_rename pref ids frename st = ((ids', sub), st') ->
        NoDup (map snd (Env.elements sub)).

    Conjecture fresh_idents_rename_sub_nIn : forall prefs aft pref ids frename ids' sub st st' x y,
        st_valid_after st prefs aft ->
        fresh_idents_rename pref ids frename st = ((ids', sub), st') ->
        Env.MapsTo x y sub -> ~In y (st_ids st).

    Conjecture fresh_idents_rename_anns : forall pref ids frename ids' sub st st',
        fresh_idents_rename pref ids frename st = ((ids', sub), st') ->
        st_anns st' = ids'++st_anns st.

    Conjecture fresh_idents_rename_st_valid : forall pref ids frename ids' sub st st' aft,
        fresh_idents_rename pref ids frename st = ((ids', sub), st') ->
        st_valid_after st pref aft ->
        st_valid_after st' pref aft.
    Conjecture fresh_idents_rename_st_follows : forall pref ids frename ids' sub st st',
        fresh_idents_rename pref ids frename st = ((ids', sub), st') ->
        st_follows st st'.
  End fresh_idents_rename.

  Section ret.
    Context {A B : Type}.
    Parameter ret : A -> Fresh A B.
    Conjecture ret_spec : forall a st,
        ret a st = (a, st).
  End ret.

  Section bind.
    Context {A A' B : Type}.
    Parameter bind : Fresh A B -> (A -> Fresh A' B) -> Fresh A' B.
    Conjecture bind_spec : forall (x : Fresh A B) (k : A -> Fresh A' B) st a' st'',
        (bind x k) st = (a', st'') <->
        exists a, exists st', (x st = (a, st') /\ k a st' = (a', st'')).
  End bind.

  Section bind2.
    Context {A1 A2 A' B : Type}.
    Parameter bind2 : Fresh (A1 * A2) B -> (A1 -> A2 -> Fresh A' B) -> Fresh A' B.
    Conjecture bind2_spec : forall (x : Fresh (A1 * A2) B) (k : A1 -> A2 -> Fresh A' B) st a' st'',
        (bind2 x k) st = (a', st'') <->
        exists a1, exists a2, exists st', (x st = ((a1, a2), st') /\ k a1 a2 st' = (a', st'')).
  End bind2.
End FRESHKERNEL.

Module FreshKernel(Import Ids : IDS) : FRESHKERNEL(Ids).
  Section st.
    Definition fresh_st (B : Type) : Type := (ident * list (ident * B)).
    Context {B : Type}.
    Definition st_anns (st : fresh_st B) := snd st.
    Definition st_ids (st : fresh_st B) := map fst (st_anns st).
  End st.

  Definition Fresh (A B : Type) : Type := fresh_st B -> A * fresh_st B.

  Section ret.
    Context {A B : Type}.
    Definition ret (a : A) : Fresh A B := fun st => (a, st).

    Fact ret_spec : forall a st,
        ret a st = (a, st).
    Proof.
      intros a st. reflexivity.
    Qed.
  End ret.

  Section validity.
    Context {B : Type}.
    (** The state is valid if the next ident is greater than all generated idents,
        and if there is no duplicates in generated idents *)
    Definition st_valid_after (st : fresh_st B) (pref : ident) (aft : PS.t) : Prop :=
      let '(n, l) := st in
      NoDupMembers l /\
      Forall (fun id => exists x hint, id = gensym pref hint x /\ Pos.lt x n) (map fst l) /\
      exists prefs,
        ~PS.In pref prefs /\
        PS.For_all (AtomOrGensym prefs) aft.

    Fact AtomOrGensym_gensym_injective : forall prefs pref hint x,
        AtomOrGensym prefs (gensym pref hint x) ->
        PS.In pref prefs.
    Proof.
      intros * [Hat|(?&?&?&?&Hgen)].
      - exfalso. eapply gensym_not_atom; eauto.
      - eapply gensym_injective in Hgen as (?&?); subst; auto.
    Qed.

    Fact st_valid_NoDup : forall st pref aft,
        st_valid_after st pref aft ->
        NoDup (st_ids st++PSP.to_list aft).
    Proof.
      intros [n l] pref aft (Hnd&Hpre&?&Hnpre&Hatg).
      apply NoDup_app'; simpl.
      - apply fst_NoDupMembers; auto.
      - apply PS_elements_NoDup.
      - eapply Forall_impl; [|eauto].
        intros ? (?&?&Hgen&_); subst.
        rewrite In_PS_elements; simpl.
        intro contra. apply Hatg in contra.
        eapply AtomOrGensym_gensym_injective in contra.
        contradiction.
    Qed.

    Fact st_valid_PSeq : forall st pref aft1 aft2,
        PS.eq aft1 aft2 ->
        st_valid_after st pref aft1 ->
        st_valid_after st pref aft2.
    Proof.
      intros [n l] * Heq (?&?&?&?&?).
      repeat (constructor; auto).
      exists x. rewrite <- Heq; auto.
    Qed.

    Fact st_valid_prefixed : forall st pref aft,
        st_valid_after st pref aft ->
        Forall (fun x => exists n hint, x = gensym pref hint n) (st_ids st).
    Proof.
      intros (?&?) * (?&?&?); auto.
      eapply Forall_impl; [|eauto].
      intros ? (?&?&Hgen&_); subst; eauto.
    Qed.
  End validity.

  Section follows.
    Context {B : Type}.

    Definition st_follows (st st' : fresh_st B) :=
      incl (snd st) (snd st').

    Fact st_follows_refl : Reflexive st_follows.
    Proof. intros st. unfold st_follows. reflexivity. Qed.

    Fact st_follows_trans : Transitive st_follows.
    Proof.
      unfold Transitive. intros.
      unfold st_follows in *.
      etransitivity; eauto.
    Qed.

    Fact st_follows_incl : forall st st',
        st_follows st st' ->
        incl (st_anns st) (st_anns st').
    Proof. intuition. Qed.
  End follows.

  Section init.
    Context {B : Type}.

    Definition init_st : fresh_st B := (xH, []).

    Fact init_st_anns : st_anns init_st = [].
    Proof. intros. reflexivity.
    Qed.

    Fact init_st_valid : forall pref aft aftprefs,
        ~PS.In pref aftprefs ->
        PS.For_all (AtomOrGensym aftprefs) aft ->
        st_valid_after init_st pref aft.
    Proof.
      intros * Hnin Hprefs.
      unfold init_st.
      repeat (constructor; simpl; eauto).
    Qed.
  End init.

  Section fresh_ident.
    Context {B : Type}.

    Definition fresh_ident pref hint (b : B) : Fresh ident B :=
      fun '(n, l) =>
        let id := gensym pref hint n in
        (id, (Pos.succ n, (id, b)::l)).

    Fact fresh_ident_anns : forall pref hint b id st st',
        fresh_ident pref hint b st = (id, st') ->
        st_anns st' = (id, b)::(st_anns st).
    Proof.
      intros.
      destruct st. inv H.
      reflexivity.
    Qed.

    Fact fresh_ident_st_valid :
      forall pref hint (b : B) id st st' aft,
        fresh_ident pref hint b st = (id, st') ->
        st_valid_after st pref aft ->
        st_valid_after st' pref aft.
    Proof.
      intros ???? [n l] [n' l'] aft Hfresh (Hv1&Hv2&aftprefs&Hv3&Hv4).
      simpl in Hfresh; inv Hfresh.
      repeat split; simpl; auto. 3:exists aftprefs; split; auto. 1,2:constructor; auto.
      - rewrite fst_InMembers.
        intro Hin. eapply Forall_forall in Hv2 as (?&?&Heq&?); eauto.
        apply gensym_injective in Heq as (_&?); subst.
        eapply Pos.lt_irrefl; eauto.
      - repeat esplit; eauto.
        apply Pos.lt_succ_diag_r.
      - eapply Forall_impl; [|eauto].
        intros ? (?&?&?&?); subst.
        repeat esplit; eauto.
        etransitivity; eauto. apply Pos.lt_succ_diag_r.
    Qed.

    Fact fresh_ident_st_follows :
      forall pref hint (b : B) id st st',
        fresh_ident pref hint b st = (id, st') ->
        st_follows st st'.
    Proof.
      intros ???? [n l] [n' l'] Hfresh.
      simpl in *; inv Hfresh; simpl.
      unfold st_follows in *; simpl in *.
      apply incl_tl. reflexivity.
    Qed.

    Fact fresh_ident_prefixed : forall pref hint b id st st',
        fresh_ident pref hint b st = (id, st') ->
        exists x hint, id = gensym pref hint x.
    Proof.
      intros ???? (?&?) ? Hfresh. inv Hfresh; eauto.
    Qed.
  End fresh_ident.

  Section fresh_idents_rename.
    Context {B : Type}.

    Definition fresh_idents_rename pref (ids : list (ident * B)) (frename : _ -> B -> B) st :=
      let '(n, l) := st in
      let (iids, n) := List.fold_left (fun '(l, n) '(x, ann) =>
                                         let id := gensym pref (Some x) n in
                                         (((x, id), ann)::l, Pos.succ n))
                                      ids (nil, n) in
      let sub := Env.from_list (map fst iids) in
      let ids := map (fun '((_, x), ann) => (x, frename sub ann)) (List.rev iids) in
      ((ids, sub), (n, ids++l)).

    Fact fi_right_le pref : forall (ids : list (ident * B)) ids' n n',
        fold_right (fun x y => (let '(l, n) := y in fun '(x0, ann) => ((x0, gensym pref (Some x0) n, ann) :: l, Pos.succ n)) x) ([], n) ids = (ids', n') ->
        Pos.le n n'.
    Proof.
      induction ids as [|(?&?)]; intros * Hfold; simpl in *.
      - inv Hfold. reflexivity.
      - cases_eqn Hfold. inv Hfold.
        eapply IHids in Hfold0. lia.
    Qed.

    Fact fi_fold_left_values pref : forall (ids : list (ident * B)) iids n n',
        fold_left (fun '(l, n) '(x, ann) => ((x, gensym pref (Some x) n, ann) :: l, Pos.succ n)) ids ([], n) = (iids, n') ->
        Forall2 (fun '(x, ann) '((x1, x2), ann1) => x1 = x /\ ann1 = ann /\ exists n1, x2 = gensym pref (Some x) n1 /\ Pos.le n n1 /\ Pos.lt n1 n') ids (List.rev iids).
    Proof.
      intros * Hfold.
      rewrite Forall2_rev, rev_involutive.
      rewrite <-(rev_involutive ids), fold_right_rev_left in Hfold.
      revert iids n n' Hfold.
      generalize (rev ids) as ids'. clear ids.
      induction ids'; intros * Hfold; simpl in *.
      - inv Hfold; auto.
      - cases_eqn Hfold. inv Hfold.
        repeat (econstructor; eauto using Pos.lt_succ_diag_r, fi_right_le).
        eapply IHids' in Hfold0.
        eapply Forall2_impl_In; [|eauto]; intros (?&?) ((?&?)&?) _ _ (?&?&?&?&?&?).
        repeat esplit; eauto. lia.
    Qed.

    Fact fi_left_le pref : forall (ids : list (ident * B)) ids0 iids n n',
        fold_left (fun '(l, n) '(x, ann) => ((x, gensym pref (Some x) n, ann) :: l, Pos.succ n)) ids (ids0, n) = (iids, n') ->
        Pos.le n n'.
    Proof.
      induction ids as [|(?&?)]; intros * Hfold; simpl in *.
      - inv Hfold. reflexivity.
      - eapply IHids in Hfold. lia.
    Qed.

    Fact fi_NoDup pref : forall (ids : list (ident * B)) ids' n n',
        fold_left (fun '(l, n) '(x, ann) => ((x, gensym pref (Some x) n, ann) :: l, Pos.succ n)) ids ([], n) = (ids', n') ->
        NoDup (map (fun '(_, x, _) => x) ids').
    Proof.
      intros (* ids ids' n n' *) * Hfold.
      assert (NoDup (map (fun '(_, x, _) => x) ids') /\
              Forall (fun '(_, x, _) => exists n1 hint, x = gensym pref hint n1 /\ Pos.lt n1 n') ids') as (?&?); auto.
      rewrite <-(rev_involutive ids), fold_right_rev_left in Hfold.
      revert ids' n n' Hfold. generalize (rev ids) as ids'; clear ids.
      induction ids'; intros * Hfold; simpl in *.
      - inv Hfold. repeat constructor.
      - cases_eqn Hfold. inv Hfold.
        specialize (IHids' _ _ _ Hfold0) as (Hnd&Hf).
        repeat constructor; auto.
        + intro contra. eapply in_map_iff in contra as (((?&?)&?)&?&?); subst.
          eapply Forall_forall in Hf; eauto. destruct Hf as (?&?&Hgen&?).
          eapply gensym_injective in Hgen as (?&?); subst. lia.
        + repeat esplit; eauto. lia.
        + eapply Forall_impl; [|eauto]; intros ((?&?)&?) (?&?&?&?); subst.
          repeat esplit; eauto. lia.
    Qed.

    Fact fi_map_fst : forall pref (ids : list (ident * B)) iids n n',
        Forall2 (fun '(x, ann) '((x1, x2), ann1) => x1 = x /\ ann1 = ann /\ exists n1, x2 = gensym pref (Some x) n1 /\ Pos.le n n1 /\ Pos.lt n1 n') ids iids ->
        map fst (map fst iids) = map fst ids.
    Proof.
      intros * Hf.
      induction Hf as [|(?&?) ((?&?)&?) ?? (?&?&_)]; subst; simpl; auto.
    Qed.

    Lemma fresh_idents_rename_ids : forall pref ids frename ids' sub st st',
        NoDupMembers ids ->
        fresh_idents_rename pref ids frename st = ((ids', sub), st') ->
        ids' = map (fun '(x, ann) => (or_default x (Env.find x sub), frename sub ann)) ids.
    Proof.
      unfold fresh_idents_rename.
      intros * Hnd Hfresh. destruct st.
      destruct fold_left eqn:Hfold. inv Hfresh.
      eapply fi_fold_left_values in Hfold.
      assert (Forall (fun '(x, x') => Env.find x (Env.from_list (map fst l0)) = Some x') (map fst (rev l0))) as Hfind.
      { rewrite <-Permutation_rev.
        eapply Forall_forall; intros (?&?) Hin.
        eapply Env.find_In_from_list; eauto.
        erewrite fst_NoDupMembers, (Permutation_rev l0), fi_map_fst; eauto.
        now rewrite <-fst_NoDupMembers.
      }
      clear Hnd.
      induction Hfold as [|(?&?) ((?&?)&?) ?? (?&?&_)]; auto; subst; simpl in *; inv Hfind.
      f_equal; auto.
      rewrite H1; simpl. reflexivity.
    Qed.

    Lemma fresh_idents_rename_sub1 : forall pref ids frename ids' sub st st' x,
        fresh_idents_rename pref ids frename st = ((ids', sub), st') ->
        Env.In x sub -> InMembers x ids.
    Proof.
      unfold fresh_idents_rename.
      intros * Hfresh Hmap. destruct st.
      destruct fold_left eqn:Hfold. inv Hfresh.
      rewrite Permutation_rev.
      rewrite <-(rev_involutive ids), fold_right_rev_left in Hfold.
      destruct (InMembers_dec x (rev ids) ident_eq_dec); eauto.
      exfalso. eapply n; clear n.
      eapply Env.In_from_list in Hmap.
      clear l. revert l0 i i0 Hfold Hmap. generalize (rev ids) as ids'. clear ids.
      induction ids' as [|(?&?)]; intros * Hfold Hmap; simpl in *.
      - inv Hfold. inv Hmap.
      - cases_eqn Hfold. inv Hfold.
        specialize (IHids' _ _ _ Hfold0).
        inv Hmap; auto.
    Qed.

    Lemma fresh_idents_rename_sub2 : forall pref ids frename ids' sub st st' x,
        fresh_idents_rename pref ids frename st = ((ids', sub), st') ->
        InMembers x ids <-> exists y n, Env.MapsTo x y sub /\ y = gensym pref (Some x) n.
    Proof.
      unfold fresh_idents_rename.
      intros * Hfresh. destruct st.
      destruct fold_left eqn:Hfold. inv Hfresh.
      rewrite Permutation_rev.
      rewrite <-(rev_involutive ids), fold_right_rev_left in Hfold.
      clear l. revert l0 i i0 Hfold. generalize (rev ids) as ids'. clear ids.
      induction ids'; intros * Hfold; simpl in *.
      - inv Hfold. split; [intros []|intros (?&?&Hemp&_)]; simpl in *.
        unfold Env.from_list in *; simpl in *.
        eapply Env.Props.P.F.empty_mapsto_iff in Hemp; eauto.
      - cases_eqn Hfold. inv Hfold.
        specialize (IHids' _ _ _ Hfold0). rewrite IHids'.
        split; [intros [|(?&?&Hmap&Hgen)]|intros (?&?&Hmap&Hgen)];
          subst; unfold Env.MapsTo, Env.from_list in *; simpl.
        + destruct (InMembers_dec x ids' ident_eq_dec).
          * eapply IHids' in i0 as (?&?&?&?); subst.
            repeat esplit; eauto using Env.find_gsss'_empty.
          * repeat esplit; eauto.
            setoid_rewrite Env.find_gsss'; eauto.
            { contradict n. clear - Hfold0 n.
              revert i i1 l n Hfold0.
              induction ids' as [|(?&?)]; intros * Hin Hfold0; simpl in *.
              - inv Hfold0. inv Hin.
              - cases_eqn Hfold. inv Hfold0. inv Hin; eauto.
            }
        + repeat esplit; eauto.
          eapply Env.find_gsss'_empty; eauto.
        + destruct (ident_eq_dec i2 x); auto. right.
          setoid_rewrite Env.find_gsso' in Hmap; eauto.
    Qed.

    Lemma fresh_idents_rename_sub_NoDup : forall pref ids frename ids' sub st st',
        NoDupMembers ids ->
        fresh_idents_rename pref ids frename st = ((ids', sub), st') ->
        NoDup (map snd (Env.elements sub)).
    Proof.
      unfold fresh_idents_rename.
      intros * Hnd Hfresh.
      assert (Hfresh':=Hfresh). eapply fresh_idents_rename_ids in Hfresh'; eauto.
      destruct st, fold_left eqn:Hfold. inv Hfresh.
      rewrite Env.elements_from_list.
      - eapply fi_NoDup in Hfold.
        erewrite map_map, map_ext; eauto. intros ((?&?)&?); auto.
      - eapply fi_fold_left_values, fi_map_fst in Hfold.
        rewrite fst_NoDupMembers, (Permutation_rev l0).
        setoid_rewrite Hfold. apply fst_NoDupMembers; auto.
    Qed.

    Lemma fresh_idents_rename_sub_nIn prefs aft : forall pref ids frename ids' sub st st' x y,
        st_valid_after st prefs aft ->
        fresh_idents_rename pref ids frename st = ((ids', sub), st') ->
        Env.MapsTo x y sub -> ~In y (st_ids st).
    Proof.
      unfold fresh_idents_rename.
      intros * Hvalid Hfresh Hmaps Hin. destruct st, Hvalid as (_&?&_).
      destruct fold_left eqn:Hfold. inv Hfresh.
      eapply Env.from_list_find_In, in_map_iff in Hmaps as ((?&?)&Heq&Hin'); simpl in *; subst.
      eapply fi_fold_left_values, Forall2_ignore1 in Hfold. rewrite <-Permutation_rev in Hfold.
      eapply Forall_forall in Hfold as ((?&?)&?&Heq); eauto; simpl in *. destruct Heq as (?&?&?&Hgen&Hlt&Hge); subst.
      eapply Forall_forall in H as (?&?&Hgen&Hlt'); eauto.
      eapply gensym_injective in Hgen as (?&?); subst. lia.
    Qed.

    Lemma fresh_idents_rename_anns : forall pref ids frename ids' sub st st',
        fresh_idents_rename pref ids frename st = ((ids', sub), st') ->
        st_anns st' = ids'++st_anns st.
    Proof.
      unfold fresh_idents_rename.
      intros * Hfresh. destruct st.
      cases_eqn Hfold.
    Qed.

    Lemma fresh_idents_rename_st_valid : forall pref ids frename ids' sub st st' aft,
        fresh_idents_rename pref ids frename st = ((ids', sub), st') ->
        st_valid_after st pref aft ->
        st_valid_after st' pref aft.
    Proof.
      unfold fresh_idents_rename.
      intros ????? (?&?) (?&?) ? Hfresh (Hv1&Hv2&Hv3).
      destruct fold_left eqn:Hfold. inv Hfresh.
      repeat (split; auto).
      - apply NoDupMembers_app; auto.
        + rewrite fst_NoDupMembers, map_map; simpl.
          eapply fi_NoDup in Hfold; eauto.
          erewrite <-Permutation_rev, map_ext; eauto. intros ((?&?)&?); auto.
        + intros ? Hinm1 Hinm2.
          eapply fst_InMembers in Hinm2. eapply Forall_forall in Hv2 as (?&?&?&Hlt); eauto; subst.
          rewrite fst_InMembers, map_map in Hinm1. eapply in_map_iff in Hinm1 as (((?&?)&?)&?&?); simpl in *; subst.
          eapply fi_fold_left_values, Forall2_ignore1, Forall_forall in Hfold as ((?&?)&?&Hfold); eauto; simpl in *.
          destruct Hfold as (?&?&?&?&?&?); subst.
          eapply gensym_injective in H3 as (?&?); subst. lia.
      - rewrite map_app. apply Forall_app; split; auto.
        + eapply fi_fold_left_values in Hfold. clear - Hfold.
          induction Hfold as [|(?&?) ((?&?)&?) ?? (?&?&?&?&?&?)];
            auto; subst; simpl in *; constructor; eauto.
        + eapply Forall_impl; [|eauto]; intros ? (?&?&?&?).
          repeat (esplit; eauto).
          eapply Pos.lt_le_trans; eauto using fi_left_le.
    Qed.

    Lemma fresh_idents_rename_st_follows : forall pref ids frename ids' sub st st',
        fresh_idents_rename pref ids frename st = ((ids', sub), st') ->
        st_follows st st'.
    Proof.
      unfold fresh_idents_rename, st_follows.
      intros ????? (?&?) (?&?) Hfresh.
      cases_eqn Hfold; inv Hfresh.
      apply incl_appr, incl_refl.
    Qed.
  End fresh_idents_rename.

  Section bind.
    Context {A A' B : Type}.

    Definition bind (x : Fresh A B) (k : A -> Fresh A' B) : Fresh A' B :=
      fun st => let '(a, st') := x st in k a st'.

    Lemma bind_spec : forall (x : Fresh A B) (k : A -> Fresh A' B) st a' st'',
        (bind x k) st = (a', st'') <->
        exists a, exists st', (x st = (a, st') /\ k a st' = (a', st'')).
    Proof.
      intros x k st a' st''. split; intros.
      - unfold bind in H.
        destruct (x st) as [a st']. exists a. exists st'.
        split; auto.
      - destruct H as [a [st' [H1 H2]]]. unfold bind.
        rewrite H1. assumption.
    Qed.
  End bind.

  Section bind2.
    Context {A1 A2 A' B : Type}.

    Definition bind2 (x: Fresh (A1 * A2) B) (k: A1 -> A2 -> Fresh A' B) : Fresh A' B :=
      fun n => let '((a1, a2), n') := x n in k a1 a2 n'.

    Lemma bind2_spec : forall (x : Fresh (A1 * A2) B) (k : A1 -> A2 -> Fresh A' B) st a' st'',
        (bind2 x k) st = (a', st'') <->
        exists a1, exists a2, exists st', (x st = ((a1, a2), st') /\ k a1 a2 st' = (a', st'')).
    Proof.
      intros x k st a' st''. split; intros.
      - unfold bind2 in H.
        destruct (x st) as [[a1 a2] st']. exists a1. exists a2. exists st'.
        split; auto.
      - destruct H as [a1 [a2 [st' [H1 H2]]]]. unfold bind2.
        rewrite H1. assumption.
    Qed.
  End bind2.
End FreshKernel.

Module Fresh(Ids : IDS).
  Module Ker := FreshKernel(Ids).
  Include Ker.

  Section Instances.
    Context {B : Type}.
    Global Instance st_follows_Reflexive : Reflexive (@st_follows B) := st_follows_refl.
    Global Instance st_follows_Transitive : Transitive (@st_follows B) := st_follows_trans.

    Global Instance st_valid_after_Proper :
      Proper (@eq (@fresh_st B) ==> @eq ident ==> PS.Equal ==> @Basics.impl)
             st_valid_after.
    Proof.
      intros ? ? ? ? ? ? ? ? Heq Hfresh; subst.
      eapply st_valid_PSeq; eauto.
    Qed.
  End Instances.

  Module Facts.

    Section st.
      Context {B : Type}.

      Fact st_anns_ids_In : forall (st : fresh_st B) id,
          (exists b, In (id, b) (st_anns st)) <-> In id (st_ids st).
      Proof.
        intros.
        split; intros.
        - destruct H as [b H].
          unfold st_ids. rewrite in_map_iff.
          exists (id, b); auto.
        - unfold st_ids in H. rewrite in_map_iff in H.
          destruct H as [[? b] [? H]]; simpl in *; subst.
          exists b. assumption.
      Qed.
    End st.

    Fact contradict_AtomOrGensym : forall pref prefs hint n,
        ~PS.In pref prefs ->
        ~Ids.AtomOrGensym prefs (Ids.gensym pref hint n).
    Proof.
      intros * Hnin [Hat|(?&?&?&?&Hgen)].
      - eapply Ids.gensym_not_atom; eauto.
      - eapply Ids.gensym_injective in Hgen as (?&?); subst; eauto.
    Qed.

    Section st_valid_after.
      Context {B : Type}.

      Fact st_valid_after_NoDupMembers {C} : forall (st : fresh_st B) pref (vars : list (ident * C)),
          NoDupMembers vars ->
          st_valid_after st pref (PSP.of_list (map fst vars)) ->
          NoDup (map fst vars ++ st_ids st).
      Proof.
        intros * Hndup Hvalid.
        eapply st_valid_NoDup in Hvalid.
        rewrite ps_of_list_ps_to_list_Perm in Hvalid. 2:rewrite <- fst_NoDupMembers; auto.
        unfold st_ids in Hvalid.
        rewrite Permutation_app_comm; auto.
      Qed.

      Fact st_valid_after_AtomOrGensym_nIn : forall pref prefs aft (st : fresh_st B) x,
          ~PS.In pref prefs ->
          st_valid_after st pref aft ->
          Ids.AtomOrGensym prefs x ->
          ~In x (st_ids st).
      Proof.
        intros * Hnin Hst Hat Hin.
        eapply st_valid_prefixed, Forall_forall in Hst as (?&?&?); eauto; subst.
        eapply contradict_AtomOrGensym in Hat; eauto.
      Qed.
    End st_valid_after.

    Section fresh_ident.
      Context {B : Type}.

      Fact fresh_ident_In : forall pref hint (b : B) id st st',
          fresh_ident pref hint b st = (id, st') ->
          In (id, b) (st_anns st').
      Proof.
        intros. apply fresh_ident_anns in H.
        rewrite H. constructor. reflexivity.
      Qed.

      Corollary fresh_ident_Inids : forall pref hint (b : B) id st st',
          fresh_ident pref hint b st = (id, st') ->
          In id (st_ids st').
      Proof.
        intros * Hfresh.
        apply fresh_ident_In in Hfresh.
        unfold st_ids. rewrite in_map_iff.
        exists (id, b); auto.
      Qed.

      Fact fresh_ident_vars_perm : forall pref hint (b : B) id st st',
          fresh_ident pref hint b st = (id, st') ->
          Permutation (id::(st_ids st)) (st_ids st').
      Proof.
        intros. apply fresh_ident_anns in H.
        unfold st_ids in *. rewrite H.
        reflexivity.
      Qed.

      Fact fresh_ident_nIn : forall pref hint (b : B) id st st' aft,
          st_valid_after st pref aft ->
          fresh_ident pref hint b st = (id, st') ->
          ~List.In id (st_ids st).
      Proof.
        intros * Hvalid Hfresh.
        eapply fresh_ident_st_valid in Hvalid; eauto.
        apply st_valid_NoDup in Hvalid. apply NoDup_app_weaken in Hvalid.
        apply fresh_ident_vars_perm in Hfresh.
        unfold st_ids in *.
        rewrite <- Hfresh in Hvalid. inv Hvalid.
        assumption.
      Qed.

      Fact fresh_ident_nIn' : forall pref hint (b : B) id st st' aft,
          st_valid_after st pref aft ->
          fresh_ident pref hint b st = (id, st') ->
          ~PS.In id aft.
      Proof.
        intros * Hvalid Hfresh.
        eapply fresh_ident_st_valid in Hvalid; eauto.
        apply st_valid_NoDup in Hvalid.
        apply fresh_ident_vars_perm in Hfresh.
        unfold st_ids in *.
        rewrite <- Hfresh in Hvalid. inv Hvalid.
        intro contra. apply H1, in_or_app, or_intror, In_PS_elements; auto.
      Qed.

      Fact fresh_ident_nIn'' : forall pref hint (b : B) id st st' aft,
          st_valid_after st pref (PSP.of_list aft) ->
          fresh_ident pref hint b st = (id, st') ->
          ~In id (aft ++ st_ids st).
      Proof.
        intros * Hvalid Hfresh.
        intro contra.
        apply in_app in contra as [contra|contra].
        - eapply fresh_ident_nIn' in Hfresh; eauto.
          rewrite <- ps_from_list_ps_of_list, ps_from_list_In in Hfresh; auto.
        - eapply fresh_ident_nIn in Hvalid; eauto.
      Qed.

    End fresh_ident.

    Section fresh_idents_rename.
      Context {B : Type}.

      Fact fresh_idents_rename_sub_gensym pref frename : forall (ids: list (ident * B)) st ids' sub st',
          fresh_idents_rename pref ids frename st = ((ids', sub), st') ->
          forall x y, Env.MapsTo x y sub -> exists n, y = Ids.gensym pref (Some x) n.
      Proof.
        intros * Hfresh * Hmap.
        assert (Hin:=Hfresh). eapply fresh_idents_rename_sub1 in Hin. 2:econstructor; eauto.
        eapply fresh_idents_rename_sub2 in Hin as (?&?&Hmap'&?); eauto.
        unfold Env.MapsTo in *. rewrite Hmap in Hmap'; inv Hmap'.
        eauto.
      Qed.
    End fresh_idents_rename.
  End Facts.

  Module Tactics.
    Ltac inv_bind :=
      simpl in *;
      match goal with
      | H : context c [ret _ _] |- _ =>
        rewrite ret_spec in H
      | H : (_, _) = (_, _) |- _ =>
        inv H
      | H : bind _ _ _ = (_, _) |- _ =>
        apply bind_spec in H; destruct H as [? [? [? ?]]]; simpl in *
      | H : bind2 _ _ _ = (_, _) |- _ =>
        apply bind2_spec in H; destruct H as [? [? [? [? ?]]]]; simpl in *
      | |- context c [ret _ _] =>
        rewrite ret_spec
      | |- bind _ _ _ = (_, _) =>
        rewrite bind_spec; repeat esplit
      | |- bind2 _ _ _ = (_, _) =>
        rewrite bind2_spec; repeat esplit
      end.
  End Tactics.

  Module Notations.
    Declare Scope fresh_monad_scope.

    (** [do] notation, inspired by CompCert's error monad *)
    Notation "'do' X <- A ; B" :=
      (bind A (fun X => B))
        (at level 200, X name, A at level 100, B at level 200): fresh_monad_scope.

    Notation "'do' ( X , Y ) <- A ; B" :=
      (bind2 A (fun X Y => B))
        (at level 200, X name, Y name, A at level 100, B at level 200): fresh_monad_scope.
  End Notations.

  Section mmap.
    Import Tactics Notations.
    Open Scope fresh_monad_scope.
    Context {A A1 B : Type}.
    Variable k : A -> Fresh A1 B.

    Fixpoint mmap a :=
      match a with
      | nil => ret nil
      | hd::tl => do a1 <- k hd;
                do a1s <- mmap tl;
                ret (a1::a1s)
      end.

    Fact mmap_values : forall a st a1s st',
        mmap a st = (a1s, st') ->
        Forall2 (fun a a1 => exists st'', exists st''', k a st'' = (a1, st''')) a a1s.
    Proof.
      induction a; intros st a1s st' Hfold; simpl in *; repeat inv_bind.
      - constructor.
      - specialize (IHa _ _ _ H0).
        constructor; eauto.
    Qed.

    Fact mmap_st_valid : forall a a1s st st' pref aft,
        mmap a st = (a1s, st') ->
        Forall (fun a => forall a1 st st',
                    k a st = (a1, st') ->
                    st_valid_after st pref aft ->
                    st_valid_after st' pref aft) a ->
        st_valid_after st pref aft ->
        st_valid_after st' pref aft.
    Proof.
      induction a; intros * Hmap Hforall Hvalid;
        simpl in *; repeat inv_bind; auto.
      inv Hforall. eapply IHa; eauto.
    Qed.

    Fact mmap_st_follows : forall a a1s st st',
        mmap a st = (a1s, st') ->
        Forall (fun a => forall a1 st st', k a st = (a1, st') -> st_follows st st') a ->
        st_follows st st'.
    Proof.
      induction a; intros * Hmap Hforall;
        simpl in *; repeat inv_bind; auto.
      - reflexivity.
      - inv Hforall.
        etransitivity; eauto.
    Qed.

    Fact mmap_length : forall a1s a2s st st',
        mmap a1s st = (a2s, st') ->
        length a2s = length a1s.
    Proof.
      induction a1s; intros * Hmap; repeat inv_bind; simpl in *; auto.
      f_equal; eauto.
    Qed.
  End mmap.

  Section mmap2.
    Import Tactics Notations.
    Open Scope fresh_monad_scope.
    Context {A A1 A2 B : Type}.
    Variable k : A -> Fresh (A1 * A2) B.

    Fixpoint mmap2 a :=
      match a with
      | nil => ret (nil, nil)
      | hd::tl => do (a1, a2) <- k hd;
                do (a1s, a2s) <- mmap2 tl;
                ret (a1::a1s, a2::a2s)
      end.

    Fact mmap2_values : forall a st a1s a2s st',
        mmap2 a st = (a1s, a2s, st') ->
        Forall3 (fun a a1 a2 => exists st'', exists st''', k a st'' = (a1, a2, st''')) a a1s a2s.
    Proof.
      induction a; intros st a1s a2s st' Hfold; simpl in *; repeat inv_bind.
      - constructor.
      - specialize (IHa _ _ _ _ H0).
        constructor; eauto.
    Qed.

    Fact mmap2_st_valid : forall a a1s a2s st st' pref aft,
        mmap2 a st = (a1s, a2s, st') ->
        Forall (fun a => forall a1 a2 st st',
                    k a st = (a1, a2, st') ->
                    st_valid_after st pref aft ->
                    st_valid_after st' pref aft) a ->
        st_valid_after st pref aft ->
        st_valid_after st' pref aft.
    Proof.
      induction a; intros * Hmap Hforall Hvalid;
        simpl in *; repeat inv_bind; auto.
      inv Hforall. eapply IHa; eauto.
    Qed.

    Fact mmap2_st_follows : forall a a1s a2s st st',
        mmap2 a st = (a1s, a2s, st') ->
        Forall (fun a => forall a1 a2 st st', k a st = (a1, a2, st') -> st_follows st st') a ->
        st_follows st st'.
    Proof.
      induction a; intros a1s a2s st st' Hmap Hforall;
        simpl in *; repeat inv_bind; auto.
      - reflexivity.
      - inv Hforall.
        etransitivity; eauto.
    Qed.

    Fact mmap2_length_1 : forall a st a1s a2s st',
        mmap2 a st = (a1s, a2s, st') ->
        length a1s = length a.
    Proof.
      induction a; intros * Map; simpl in Map;
        repeat inv_bind; simpl; f_equal; eauto.
    Qed.
  End mmap2.

  Hint Resolve fresh_ident_st_valid.
  Hint Resolve fresh_ident_st_follows.
  Hint Resolve st_follows_incl.
  Hint Resolve mmap2_st_valid.
  Hint Resolve mmap2_st_follows.
End Fresh.
