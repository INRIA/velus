From Coq Require Import String.
From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Coq Require Import RelationClasses.
Import Coq.Relations.Relation_Operators.
From Coq Require Import Arith.Arith.
From Coq Require Import Setoid.

From Velus Require Import Common.
From Velus Require Import Environment.


(** ** Vertices and arcs *)

(** Vertices *)
Definition V_set : Type := PS.t.

(** Arcs *)
Definition A_set : Type := Env.t PS.t.

Definition empty_arc_set : A_set := Env.empty _.

(** There is an arc between x and y in the arc set *)
Definition has_arc (a : A_set) (x y : ident) :=
  exists s, Env.MapsTo x s a /\ PS.In y s.

(** Decision procedure to find if an arc exists *)
Definition has_arcb (a : A_set) (x y : ident) :=
  match (Env.find x a) with
  | Some s => PS.mem y s
  | None => false
  end.

Lemma has_arcb_spec : forall a x y,
    has_arcb a x y = true <-> has_arc a x y.
Proof.
  intros a x y.
  unfold has_arcb, has_arc.
  split; [intros H|intros (?&Hmap&Hin)]; destruct (Env.find _ _) eqn:Hfind.
  - eauto.
  - inv H.
  - rewrite Hmap in Hfind. inv Hfind.
    apply PSF.mem_1; auto.
  - rewrite Hmap in Hfind. inv Hfind.
Qed.

Lemma nhas_arc_empty : forall x y,
    ~has_arc empty_arc_set x y.
Proof.
  intros * (?&Hmap&_).
  rewrite Env.Props.P.F.empty_mapsto_iff in Hmap; auto.
Qed.

(** Add a single arc *)
Definition add_arc (x y : ident) (a : A_set) :=
  match (Env.find x a) with
  | Some s => Env.add x (PS.add y s) a
  | None => Env.add x (PS.singleton y) a
  end.

Lemma add_arc_spec : forall a x y x' y',
    has_arc (add_arc x y a) x' y' <->
    has_arc a x' y' \/
    (x = x' /\ y = y').
Proof.
  intros *. unfold add_arc, has_arc, Env.MapsTo in *.
  split; intros H;
    [(destruct H as (s&Hm&Hin);
      (destruct (ident_eq_dec x x'), (ident_eq_dec y y'); subst;
       destruct (Env.find _ a) eqn:Hfind))
    |(destruct H as [(?&?&?)|(?&?)]; destruct (Env.find x a) eqn:Hfind; subst)].
  1-2:right; auto.
  1-6:left.
  1-2:rewrite Env.gss in Hm; inv Hm.
  3-6:rewrite Env.gso in Hm; eauto.
  3,4:destruct (ident_eq_dec x x'), (ident_eq_dec y y'); subst.
  1-12:try rewrite Env.gss; try rewrite Env.gso; eauto.
  3-8:eexists; split; eauto.
  3,7:apply PSF.add_1; auto.
  4,6:apply PSF.singleton_2; auto.
  - rewrite PSF.add_neq_iff in Hin; eauto.
  - apply PSF.singleton_1 in Hin. contradiction.
  - rewrite H in Hfind. inv Hfind. apply PSF.add_2; auto.
  - rewrite H in Hfind. congruence.
Qed.

Definition has_trans_arc a := clos_trans_n1 _ (has_arc a).

Global Hint Constructors clos_trans_n1 : acygraph.
Global Hint Unfold has_trans_arc : acygraph.

Global Instance has_trans_arc_Transitive : forall a,
    Transitive (has_trans_arc a).
Proof.
  intros ? ??? Ha1 Ha2.
  induction Ha2; eauto with acygraph.
Qed.

Lemma nhas_trans_arc_empty : forall x y,
    ~has_trans_arc empty_arc_set x y.
Proof.
  intros * contra.
  induction contra; eapply nhas_arc_empty; eauto.
Qed.

Fact add_arc_has_trans_arc1 : forall a x y,
    has_trans_arc (add_arc x y a) x y.
Proof.
  left.
  rewrite add_arc_spec; auto.
Qed.

Fact add_arc_has_trans_arc2 : forall a x y x' y',
    has_trans_arc a x' y' ->
    has_trans_arc (add_arc x y a) x' y'.
Proof.
  intros * Ha.
  induction Ha.
  - left. rewrite add_arc_spec; auto.
  - eapply tn1_trans; eauto.
    rewrite add_arc_spec; eauto.
Qed.
Global Hint Resolve add_arc_has_trans_arc1 add_arc_has_trans_arc2 : acygraph.

Lemma add_arc_spec2 : forall a x y x' y',
    has_trans_arc (add_arc x y a) x' y' <->
    has_trans_arc a x' y' \/
    (x = x' /\ y = y') \/
    (x = x' /\ has_trans_arc a y y') \/
    (has_trans_arc a x' x /\ y = y') \/
    (has_trans_arc a x' x /\ has_trans_arc a y y').
Proof.
  intros *; split; intros Ha.
  - induction Ha; try rewrite add_arc_spec in *.
    + destruct H as [?|(?&?)]; subst; auto with acygraph.
    + destruct H as [?|(?&?)];
        destruct IHHa as [?|[(?&?)|[(?&?)|[(?&?)|(?&?)]]]];
        subst; eauto 10 with acygraph.
  - destruct Ha as [?|[(?&?)|[(?&?)|[(?&?)|(?&?)]]]]; subst; eauto with acygraph.
    + etransitivity; eauto with acygraph.
    + etransitivity; eauto with acygraph.
    + repeat (etransitivity; eauto with acygraph).
Qed.

(** ** Acyclic graph *)

(** Transitive, Directed Acyclic Graph *)
Inductive AcyGraph : V_set -> A_set -> Prop :=
| AGempty : AcyGraph PS.empty empty_arc_set
| AGaddv : forall v a x,
    AcyGraph v a ->
    (* ~PS.In x v -> *)
    AcyGraph (PS.add x v) a
| AGadda : forall v a x y,
    AcyGraph v a ->
    x <> y ->
    PS.In x v ->
    PS.In y v ->
    (* ~has_arc a x y -> *)
    ~has_trans_arc a y x ->
    AcyGraph v (add_arc x y a).
Global Hint Constructors AcyGraph : acygraph.

Definition vertices {v a} (g : AcyGraph v a) : V_set := v.
Definition arcs {v a} (g : AcyGraph v a) : A_set := a.

Definition is_vertex {v a} (g : AcyGraph v a) (x : ident) : Prop :=
  PS.In x v.

Definition is_arc {v a} (g : AcyGraph v a) x y : Prop :=
  has_arc a x y.

Lemma nis_arc_Gempty : forall x y,
  ~is_arc AGempty x y.
Proof.
  intros * (?&contra&_).
  rewrite Env.Props.P.F.empty_mapsto_iff in contra; auto.
Qed.

Definition is_trans_arc {v a} (g : AcyGraph v a) x y : Prop :=
  has_trans_arc a x y.

Lemma nis_trans_arc_Gempty : forall x y,
    ~is_trans_arc AGempty x y.
Proof.
  intros * contra; simpl in contra.
  apply nhas_trans_arc_empty in contra; auto.
Qed.

(** ** Major properties of is_arc : transitivity, irreflexivity, asymmetry *)

Global Instance is_trans_arc_Transitive {v a} (g : AcyGraph v a) :
    Transitive (is_trans_arc g).
Proof. eapply has_trans_arc_Transitive; eauto. Qed.

Lemma has_arc_irrefl : forall v a,
    AcyGraph v a ->
    Irreflexive (has_arc a).
Proof.
  fix irrefl 3.
  intros * g. destruct g.
  - intros ? Ha.
    apply nis_arc_Gempty in Ha; auto.
  - specialize (irrefl _ _ g); auto.
  - specialize (irrefl _ _ g).
    intros x' Harc.
    apply add_arc_spec in Harc as [?|(?&?)]; subst.
    + eapply irrefl; eauto.
    + congruence.
Qed.

Global Instance is_arc_Irreflexive {v a} (g : AcyGraph v a) :
    Irreflexive (is_arc g).
Proof. eapply has_arc_irrefl; eauto. Qed.

Global Instance is_trans_arc_Asymmetric {v a} (g : AcyGraph v a) :
    Asymmetric (is_trans_arc g).
Proof.
  revert v a g.
  fix trans 3.
  intros *. destruct g.
  - intros ? ? ? Ha1.
    exfalso. eapply nhas_trans_arc_empty; eauto.
  - specialize (trans _ _ g); auto.
  - specialize (trans _ _ g).
    intros x' y' Harc1 Harc2.
    apply add_arc_spec2 in Harc1; apply add_arc_spec2 in Harc2.
    destruct Harc1 as [?|[(?&?)|[(?&?)|[(?&?)|(?&?)]]]];
      destruct Harc2 as [?|[(?&?)|[(?&?)|[(?&?)|(?&?)]]]]; subst; eauto 10.
    1-7:eapply n0.
    1-7:etransitivity; eauto.
    1,2:etransitivity; eauto.
Qed.

Global Instance is_trans_arc_Irreflexive {v a} (g : AcyGraph v a) :
  Irreflexive (is_trans_arc g).
Proof.
  revert v a g.
  fix irrefl 3.
  intros * x. destruct g.
  - apply nis_trans_arc_Gempty.
  - eapply (irrefl _ _ g).
  - intros contra.
    specialize (irrefl _ _ g).
    apply add_arc_spec2 in contra as [?|[(?&?)|[(?&?)|[(?&?)|(?&?)]]]]; subst; eauto.
    + eapply irrefl; eauto.
    + eapply n0. etransitivity; eauto.
Qed.

Lemma is_arc_is_vertex : forall {v a} (g : AcyGraph v a) x y,
    is_arc g x y ->
    is_vertex g x /\ is_vertex g y.
Proof.
  fix is_arc_is_vertex 3.
  intros * Hisarc.
  destruct g; simpl in *.
  - exfalso. destruct Hisarc as (?&contra&_).
    rewrite Env.Props.P.F.empty_mapsto_iff in contra; auto.
  - specialize (is_arc_is_vertex _ _ g).
    apply is_arc_is_vertex in Hisarc as (Hvx&Hvy).
    split; apply PSF.add_2; auto.
  - specialize (is_arc_is_vertex _ _ g).
    unfold is_arc in Hisarc.
    apply add_arc_spec in Hisarc as [?|(?&?)]; subst; auto.
    apply is_arc_is_vertex in H; auto.
Qed.

Corollary is_trans_arc_is_vertex : forall {v a} (g : AcyGraph v a) x y,
    is_trans_arc g x y ->
    is_vertex g x /\ is_vertex g y.
Proof.
  intros * Ha.
  induction Ha.
  - apply is_arc_is_vertex; auto.
  - destruct IHHa.
    eapply is_arc_is_vertex in H as (_&?).
    eauto.
Qed.

Lemma is_trans_arc_neq : forall {v a} (g : AcyGraph v a) x y,
    is_trans_arc g x y ->
    x <> y.
Proof.
  intros * Ha contra; subst.
  eapply is_trans_arc_Irreflexive; eauto.
Qed.

Local Ltac destruct_conj_disj :=
    match goal with
    | H : _ /\ _ |- _ => destruct H
    | H : _ \/ _ |- _ => destruct H
    end; subst.

(** is_trans_arc is decidable ! *)
Lemma is_trans_arc_dec : forall {v a} (g : AcyGraph v a),
    forall x y, (is_trans_arc g x y) \/ (~ is_trans_arc g x y).
Proof.
  fix is_trans_arc_dec 3.
  intros *. destruct g.
  - right. eapply nis_trans_arc_Gempty.
  - specialize (is_trans_arc_dec _ _ g x y) as [?|?]; auto.
  - specialize (is_trans_arc_dec _ _ g).
    destruct (is_trans_arc_dec x y), (is_trans_arc_dec x x0), (is_trans_arc_dec y0 y),
    (ident_eq_dec y y0), (ident_eq_dec x x0); subst.
    1-32: try solve [left; apply add_arc_spec2; auto 10].
    1-7:(right; intro contra; apply add_arc_spec2 in contra;
         repeat destruct_conj_disj; auto).
Qed.

(** ** Building an acyclic graph *)
(** We can try to build an acyclic graph from any graph
    (defined as a mapping from vertices to their direct predecessors)
    We iterate through the list of vertices, trying to add some that are
    not already in the graph, and which predecessors are all already in the graph.

    This algorithm only succeeds if the graph is indeed acyclic, and produces a witness of that fact.
 *)

From compcert Require Import common.Errors.

Definition add_after (preds : PS.t) (x : ident) (a : A_set) : A_set :=
  PS.fold (fun p a => add_arc p x a) preds a.

Lemma add_after_spec : forall a preds y x' y',
    has_arc (add_after preds y a) x' y' <->
    has_arc a x' y' \/
    (PS.In x' preds /\ y = y').
Proof.
  Local Ltac simpl_ps_add :=
    unfold PSP.Add in *;
    match goal with
    | Hadd: (forall y, PS.In y ?s2 <-> ?p = y \/ PS.In y ?s1), Hin: PS.In ?x ?s1 |- _ =>
      eapply or_intror in Hin; erewrite <- Hadd in Hin
    | Hadd: (forall y, PS.In y ?s2 <-> ?x = y \/ PS.In y ?s1) |- _ =>
      specialize (Hadd x) as (_&?)
    | _ => idtac
  end.
  intros preds a y.
  unfold add_after. apply PSP.fold_rec.
  - intros * Hemp.
    split; auto.
    intros [?|(Hin&?)]; subst; auto.
    destruct (Hemp _ Hin).
  - intros p * Hin Hnin Hadd Hrec *.
    rewrite add_arc_spec.
    split; intros [?|(?&?)]; subst; auto.
    + apply Hrec in H as [?|(?&?)]; subst; auto; unfold PS.Exists.
      repeat simpl_ps_add; eauto 10.
    + repeat simpl_ps_add; eauto 10.
    + rewrite Hrec; auto.
    + destruct (ident_eq_dec p x'); subst; auto.
      specialize (Hrec x' y').
      left. rewrite Hrec; auto.
      right. split; auto.
      apply Hadd in H as [?|?]; auto. congruence.
Qed.

Corollary add_after_has_arc1 : forall a x y x' preds,
    has_arc a x y ->
    has_arc (add_after preds x' a) x y.
Proof.
  intros * Ha.
  rewrite add_after_spec; auto.
Qed.

Corollary add_after_has_arc2 : forall a x y preds,
    PS.In y preds ->
    has_arc (add_after preds x a) y x.
Proof.
  intros * Hin.
  rewrite add_after_spec; auto.
Qed.

Lemma add_after_AcyGraph : forall v a x preds,
    PS.In x v ->
    ~PS.In x preds ->
    PS.For_all (fun x => PS.In x v) preds ->
    PS.For_all (fun p => ~has_trans_arc a x p) preds ->
    AcyGraph v a ->
    AcyGraph v (add_after preds x a) /\
    PS.For_all (fun p => ~has_trans_arc (add_after preds x a) x p) preds.
Proof.
  intros * Hin1 Hnin2 Hpreds Hna Hacy.
  revert Hacy.
  unfold add_after. eapply PSP.fold_rec_nodep.
  - intros * Hacy; split; auto.
  - intros * Hin' Hrec Hacy.
    specialize (Hrec Hacy) as (Hacy'&Hna').
    split; [apply AGadda|]; auto.
    + intro contra; subst; auto.
    + intros ? Hin contra.
      apply Hna' in Hin. apply Hin.
      rewrite add_arc_spec2 in contra. repeat destruct_conj_disj; auto.
      * exfalso; auto.
      * exfalso; auto.
        apply Hna' in Hin'; auto.
Qed.

Definition acgraph_of_graph g v a :=
  (forall x, Env.In x g <-> PS.In x v) /\
  (forall x y, (exists xs, Env.find y g = Some xs /\ In x xs) -> has_arc a x y).

Section Dfs.

  Variable graph : Env.t (list positive).

  Record dfs_state : Type :=
    mk_dfs_state {
        in_progress : PS.t;
        progress_in_graph : forall x, PS.In x in_progress -> Env.In x graph
      }.

  Extraction Inline in_progress.

  Definition empty_dfs_state :=
    {| in_progress := PS.empty;
       progress_in_graph := fun x Hin =>
                              False_ind (Env.In x graph) (not_In_empty x Hin) |}.
  Extraction Inline empty_dfs_state.

  Lemma cardinals_in_progress_le_graph:
    forall a,
      PS.cardinal a.(in_progress) <= Env.cardinal graph.
  Proof.
    intro a.
    rewrite Env.cardinal_1, PS.cardinal_spec.
    rewrite <-(map_length fst).
    pose proof a.(progress_in_graph) as Hag.
    assert (NoDup (PS.elements (in_progress a))) as Hnds
        by (rewrite NoDup_NoDupA; apply PS.elements_spec2w).
    assert (NoDupMembers (Env.elements graph)) as Hndg
        by (apply Env.NoDupMembers_elements).
    apply fst_NoDupMembers in Hndg.
    setoid_rewrite PSF.elements_iff in Hag.
    setoid_rewrite Env.In_Members in Hag.
    setoid_rewrite fst_InMembers in Hag.
    revert Hag Hnds Hndg.
    generalize (map fst (Env.elements graph)) as g.
    generalize (PS.elements a.(in_progress)) as n.
    induction n as [|x n IH]; auto using le_0_n.
    intros g Hin NDn NDg. simpl.
    inversion_clear NDn as [|?? Hnx NDn'].
    assert (In x g) as Hxg by auto.
    apply in_split in Hxg as (g1 & g2 & Hg); subst.
    rewrite <-Permutation.Permutation_middle.
    simpl; apply le_n_S.
    rewrite <-Permutation.Permutation_middle in NDg; inv NDg.
    apply IH; auto.
    intros y Hyi.
    apply (In_weaken_cons x).
    now rewrite Permutation.Permutation_middle; auto.
    intro; subst. apply Hnx.
    apply SetoidList.InA_alt in Hyi as (y & Heq & Hyin).
    subst; auto.
  Qed.

  Definition max_depth_remaining (s : dfs_state) : nat :=
    Env.cardinal graph - PS.cardinal s.(in_progress).

  Definition deeper : dfs_state -> dfs_state -> Prop :=
    ltof _ max_depth_remaining.

  Lemma wf_deeper: well_founded deeper.
  Proof.
    apply well_founded_ltof.
  Defined.

  Lemma add_deeper:
    forall x s P,
      ~ PS.In x (in_progress s) ->
      deeper {| in_progress := PS.add x (in_progress s);
                progress_in_graph := P |} s.
  Proof.
    unfold deeper, ltof, max_depth_remaining.
    intros x s Hprog Hnin.
    pose proof (cardinals_in_progress_le_graph s) as Hag.
    pose proof (cardinals_in_progress_le_graph
                  {| in_progress := PS.add x (in_progress s);
                     progress_in_graph := Hprog |}) as Hbg.
    simpl in *.
    rewrite PSP.add_cardinal_2 with (1:=Hnin) in *.
    lia.
  Qed.

  Definition visited (p : PS.t) (v : PS.t) : Prop :=
    (forall x, PS.In x p -> ~PS.In x v)
    /\ exists a, AcyGraph v a
           /\ (forall x, PS.In x v ->
                   exists zs, Env.find x graph = Some zs
                         /\ (forall y, In y zs -> has_arc a y x)).

  Definition none_visited : { v | visited PS.empty v }.
  Proof.
    exists PS.empty.
    repeat split; auto using not_In_empty.
    exists empty_arc_set.
    repeat split; auto using not_In_empty with acygraph.
    intros * Hin. now apply not_In_empty in Hin.
  Defined.
  Extraction Inline none_visited.

  Section dfs'_loop.
    Variable (inp : PS.t)
      (dfs' : forall x (v : { v | visited inp v }),
          option { v' | visited inp v' & (In_ps [x] v' /\ PS.Subset (proj1_sig v) v') }).

  Program Fixpoint dfs'_loop
             (zs : list positive)
             (v : {v | visited inp v }) {struct zs}
    : option { v' | visited inp v' & (In_ps zs v' /\ PS.Subset (proj1_sig v) v') }  :=
    match zs with
    | [] => Some (sig2_of_sig v _)
    | w::ws =>
        match dfs' w v with
        | None => None
        | Some (exist2 _ _ v' _ _) =>
            match dfs'_loop ws (exist _ v' _) with
            | None => None
            | Some v'' => Some (sig2_weaken2 _ v'')
            end
        end
    end.
  Next Obligation.
    split.
    - now apply In_ps_nil.
    - reflexivity.
  Defined.
  Next Obligation.
    clear Heq_anonymous0.
    split.
    - apply Forall_cons; auto.
      take (PS.Subset _ s) and rewrite <-it.
      take (In_ps [_] v') and now inv it.
    - rewrite <-H0. rewrite <-s1. reflexivity.
  Defined.
  Extraction Inline dfs'_loop.

  End dfs'_loop.

  Definition pre_visited_add:
    forall {inp} x
      (v : { v | visited inp v }),
      ~PS.In x (proj1_sig v) ->
      { v' | visited (PS.add x inp) v' & v' = (proj1_sig v) }.
  Proof.
    intros inp x (v, (Pv1 & Pv2)) Hnxp.
    simpl in *. exists v; split; auto.
    intros y Hyp. apply PS.add_spec in Hyp as [HH|HH]; subst; auto.
  Defined.
  Extraction Inline pre_visited_add.

  Program Definition dfs'
     (s : dfs_state)
     (dfs'' : forall s', deeper s' s ->
                forall x (v : { v | visited s'.(in_progress) v }),
                  option { v' | visited s'.(in_progress) v'
                                & In_ps [x] v' /\ PS.Subset (proj1_sig v) v' })
     (x : positive)
     (v : { v | visited s.(in_progress) v })
    : option { v' | visited s.(in_progress) v'
                    & In_ps [x] v' /\ PS.Subset (proj1_sig v) v' } :=
    match PS.mem x s.(in_progress) with
    | true => None
    | false =>
        match PS.mem x (proj1_sig v) with
        | true => Some (sig2_of_sig v _)
        | false =>
            match (Env.find x graph) with
            | None => None
            | Some zs =>
                let s' := mk_dfs_state (PS.add x s.(in_progress)) _ in
                match (dfs'_loop s'.(in_progress) (dfs'' s' _) zs (exist _ v _)) with
                | None => None
                | Some (exist2 _ _ v' (conj P1 _) _) => Some (exist2 _ _ (PS.add x v') _ _)
                end
            end
        end
    end.
  Next Obligation.
    split; [|reflexivity].
    repeat constructor.
    apply PSF.mem_2; auto.
  Defined.
  Next Obligation.
    apply PSF.add_iff in H as [|Hin]; subst; eauto using Env.find_In, progress_in_graph.
  Defined.
  Next Obligation.
    apply add_deeper, PSE.mem_4; auto.
  Defined.
  Next Obligation.
    simpl.
    take (false = PS.mem x v) and (symmetry in it; apply PSE.mem_4 in it).
    destruct (pre_visited_add x (exist _ v H) it) as (v', V', Qv'); subst; auto.
  Defined.
  Next Obligation.
    simpl in *. clear Heq_anonymous.
    repeat split.
    - intros y Hyin.
      setoid_rewrite PS.add_spec.
      apply not_or'. split; [intro; subst|].
      + clear - Heq_anonymous0 Hyin. eapply PSE.mem_4; eauto.
      + apply P1. now apply PSF.add_2.
    - rename a into P2. rename e into P3.
      exists (add_after (PSP.of_list zs) x wildcard'); split.
      + apply add_after_AcyGraph; auto using PSF.add_1 with acygraph.
        * rewrite ps_of_list_In. intro contra.
          unfold In_ps in *. simpl_Forall.
          eapply P1; eauto using PSF.add_1.
        * intros ? Hin. rewrite ps_of_list_In in Hin.
          apply PSF.add_2. unfold In_ps in *. simpl_Forall. eauto.
        * intros ? _ HasArc.
          eapply is_trans_arc_is_vertex with (g:=P2) in HasArc as (Ver&_); eauto.
          eapply P1 in Ver; eauto using PSF.add_1.
      + intros y Hyin.
        apply PS.add_spec in Hyin as [HH|HH].
        * subst. exists zs; split; auto.
          intros z HH. apply add_after_has_arc2.
          rewrite ps_of_list_In; auto.
        * destruct (P3 _ HH) as (? & ? & ?).
          exists x0. split; eauto using add_after_has_arc1.
  Defined.
  Next Obligation.
    clear Heq_anonymous. simpl in *. split.
    - repeat constructor; auto using PSF.add_1.
    - eapply PSP.subset_add_2; eauto.
  Defined.

  Definition dfs
    : forall x (v : { v | visited PS.empty v }),
      option { v' | visited PS.empty v' &
                    (In_ps [x] v'
                     /\ PS.Subset (proj1_sig v) v') }
    := Fix wf_deeper _ dfs' empty_dfs_state.

End Dfs.

Program Definition build_acyclic_graph (graph : Env.t (list positive)) : res PS.t :=
  bind (Env.fold (fun x _ vo =>
                    bind vo
                         (fun v => match dfs graph x v with
                                | None => Error (msg "Couldn't build acyclic graph")
                                | Some v => OK (sig_of_sig2 v)
                                end))
                         graph (OK (none_visited graph)))
                 (fun v => OK _).

Lemma build_acyclic_graph_spec : forall graph v,
    build_acyclic_graph graph = OK v ->
    exists a, acgraph_of_graph graph v a /\ AcyGraph v a.
Proof.
  unfold build_acyclic_graph.
  intros graph v Hcheck.
  monadInv Hcheck. rename EQ into Hfold.
  rename x into v'.
  rewrite Env.fold_1 in Hfold.
  assert (PS.Equal (proj1_sig v')
                   (ps_adds (map fst (Env.elements graph))
                            (proj1_sig (none_visited graph)))) as Hveq;
    [apply PSP.double_inclusion; split|].
  - destruct v' as (v' & Pv'1 & a & Pv'2 & Pv'3).
    simpl. intros x Hx.
    apply Pv'3 in Hx as (zs & Hx & Hsuc).
    apply Env.elements_correct in Hx.
    apply ps_adds_spec; left.
    solve_In.
  - revert Hfold.
    revert v'.
    generalize (none_visited graph) as acc.
    generalize (Env.elements graph) as xs.
    induction xs as [|x xs IH]; [inversion 1; reflexivity|].
    simpl. intros acc v' (* Hacc *) Hfold.
    destruct (dfs graph (fst x) acc) as [acc'|] eqn:Hacc'; simpl in *.
    + apply IH in Hfold.
      rewrite <-Hfold.
      apply Subset_ps_adds.
      destruct acc' as (acc', Vacc', (H1acc' & H2acc')); simpl in *.
      apply PSP.subset_add_3; auto. now apply In_ps_singleton.
    + clear - Hfold. exfalso.
      induction xs; simpl in *; try congruence.
  - clear Hfold. destruct v' as (v & Pv1 & a & Pv2 & Pv3).
    simpl in *.
    exists a. split; auto.
    constructor; auto.
    + intros x. rewrite Hveq, ps_adds_of_list, ps_of_list_In, Env.In_Members, fst_InMembers.
      reflexivity.
    + intros ?? (?&Find&In).
      specialize (Pv3 y). rewrite Hveq, ps_adds_of_list, ps_of_list_In in Pv3.
      assert (Find':=Find). apply Env.elements_correct in Find'.
      eapply in_map with (f:=fst), Pv3 in Find' as (?&Find'&?).
      setoid_rewrite Find in Find'; inv Find'; eauto.
Qed.

(** ** Extracting a prefix *)
(** In order to build an induction principle over the graph, we need to linearize it.
    We want to extract a Topological Order ([TopoOrder]) from the graph,
    which is simply encoded as a list, with the head variable only depending on the tail ones.
 *)

Definition TopoOrder {v a} (g : AcyGraph v a) (xs : list ident) :=
  Forall' (fun xs x => ~In x xs
                    /\ is_vertex g x
                    /\ (forall y, is_trans_arc g y x -> In y xs)) xs.
Global Hint Unfold TopoOrder : acygraph.

Lemma TopoOrder_weaken : forall {v a} (g : AcyGraph v a) xs,
    TopoOrder g xs ->
    Forall (fun x => forall y, is_trans_arc g y x -> In y xs) xs.
Proof.
  intros * Hpref.
  induction Hpref; auto.
  destruct H as (Hnin&Hv&Ha).
  constructor; intuition.
  eapply Forall_impl; [|eauto].
  intros * ? ? ?. right; auto.
Qed.

Lemma TopoOrder_NoDup : forall {v a} (g : AcyGraph v a) xs,
    TopoOrder g xs ->
    NoDup xs.
Proof.
  intros * Hpref.
  induction Hpref; constructor; auto.
  destruct H; auto.
Qed.

Fact TopoOrder_AGaddv : forall {v a} (g : AcyGraph v a) x xs,
    TopoOrder g xs ->
    TopoOrder (AGaddv v a x g) xs.
Proof.
  induction xs; intros * Hpre; inv Hpre; auto with acygraph datatypes.
  destruct H1 as (?&?&?).
  specialize (IHxs H2).
  repeat constructor; auto.
  apply PSF.add_2; auto.
Qed.

Lemma TopoOrder_insert : forall {v a} (g : AcyGraph v a) xs1 xs2 x,
    is_vertex g x ->
    ~In x (xs1++xs2) ->
    (forall y, is_trans_arc g y x -> In y xs2) ->
    TopoOrder g (xs1 ++ xs2) ->
    TopoOrder g (xs1 ++ x :: xs2).
Proof.
  induction xs1; intros * Hver Hnin Ha Hpre; simpl in *.
  - constructor; repeat split; auto.
  - inversion_clear Hpre as [|?? (Hnin'&Hver'&Ha') Hpre'].
    apply not_or' in Hnin as (Hneq&Hnin).
    apply not_In_app in Hnin' as (Hnin1&Hnin2).
    constructor; repeat split; auto.
    + rewrite not_In_app; simpl; rewrite not_or'; auto.
    + intros * Ha''. specialize (Ha' _ Ha'').
      rewrite in_app_iff in *; simpl.
      destruct Ha'; auto.
    + apply IHxs1; auto.
Qed.

(** x is located before y in l *)
Definition Before (x y : ident) l :=
  Forall' (fun xs x' => x' = y -> In x xs) l.

Lemma Before_middle : forall xs1 xs2 x y,
    x <> y ->
    ~In y xs1 ->
    ~In y xs2 ->
    Before x y (xs1 ++ y :: x :: xs2).
Proof.
  induction xs1; intros * Hneq Hnin1 Hnin2; simpl.
  - constructor; [|constructor].
    + intros _. left; auto.
    + intros contra; subst. congruence.
    + induction xs2; auto with datatypes.
      apply not_in_cons in Hnin2 as (Hneq'&Hnin2).
      constructor; auto.
      intros contra; subst. congruence.
  - apply not_in_cons in Hnin1 as (Hneq'&Hnin1).
    constructor; auto.
    + intros contra; subst. congruence.
    + apply IHxs1; auto.
Qed.

Lemma Before_In : forall xs x y,
    Before x y xs ->
    In y xs ->
    In x xs.
Proof.
  induction xs; intros * Hbef Hin; inv Hbef; inv Hin.
  1,2:right; eauto.
Qed.

Import Permutation.

(** Given a prefix of the form xs1 ++ y :: xs2, we can split xs1
    into two list: xs1l depends on y and xs1r doesnt *)
Fact TopoOrder_Partition_split : forall {v a} (g : AcyGraph v a) xs1 xs2 xs1l xs1r y,
    Partition (fun z => is_trans_arc g y z) xs1 xs1l xs1r ->
    TopoOrder g (xs1 ++ y :: xs2) ->
    TopoOrder g (xs1l ++ y :: xs1r ++ xs2).
Proof.
  induction xs1; intros * Hpart Hpre; inv Hpart; simpl in *.
  - assumption.
  - inversion_clear Hpre as [|?? (Hnin&Hver&Ha) Hf].
    constructor; repeat split; auto.
    + erewrite (Partition_Permutation _ xs1), <- app_assoc, <- Permutation_middle in Hnin; eauto.
    + intros * Ha'. specialize (Ha _ Ha').
      erewrite (Partition_Permutation _ xs1), <- app_assoc, <- Permutation_middle in Ha; eauto.
    + apply IHxs1; auto.
  - inversion_clear Hpre as [|?? (Hnin&Hver&Ha) Hf].
    rewrite cons_is_app, app_assoc.
    apply TopoOrder_insert; auto; try rewrite <- app_assoc, <- cons_is_app.
    + erewrite (Partition_Permutation _ xs1), <- app_assoc, <- Permutation_middle in Hnin; eauto.
    + intros * Ha'. specialize (Ha _ Ha').
      erewrite (Partition_Permutation _ xs1), <- app_assoc in Ha; eauto.
      repeat (rewrite in_app_iff in *; simpl in *; idtac).
      destruct Ha as [Hin|[?|[?|?]]]; subst; auto. 2:congruence.
      exfalso.
      eapply Partition_Forall1, Forall_forall in H1; [|eauto].
      eapply H4; eauto. etransitivity; eauto.
    + apply IHxs1; auto.
Qed.

(* Is there is no arc between y and x, it is possible to reorganize the TopoOrder *)
(* so that x ends up before y *)
Lemma TopoOrder_reorganize : forall {v a} (g : AcyGraph v a) xs x y,
    x <> y ->
    In x xs ->
    In y xs ->
    TopoOrder g xs ->
    ~is_trans_arc g y x ->
    exists xs', Permutation.Permutation xs' xs /\
           TopoOrder g xs' /\
           Before x y xs'.
Proof.
  induction xs; intros * Hneq Hin1 Hin2 Hpref Hna;
    inv Hin1; inv Hin2; inversion_clear Hpref as [|?? (Hnin&Hv&Ha)]; subst.
  - contradiction.
  - clear IHxs.
    apply in_split in H as (xs1&xs2&?); subst.
    (* Partition the xs1.
       No xs1 depends on x (because (xs1 ++ y :: xs2) is a prefix).
       All the xs1l depend on y, and therefore x does not depend on them.
       All the xs1r do not depend on y
       We produce a new list of the form xs1l ++ y :: x :: xs1r ++ xs2
     *)
    assert (exists xs1l xs1r, Partition (fun z => is_trans_arc g y z) xs1 xs1l xs1r) as (xs1l&xs1r&Hpart).
    { eapply dec_Partition, is_trans_arc_dec. }
    exists (xs1l ++ y :: x :: xs1r ++ xs2).
    assert (Permutation xs1 (xs1l ++ xs1r)) as Hperm.
    { eapply Partition_Permutation; eauto. }
    repeat split.
    + repeat rewrite <- Permutation_middle.
      rewrite app_assoc, <- Hperm.
      apply perm_swap.
    + eapply TopoOrder_Partition_split in H0; eauto.
      rewrite cons_is_app, app_assoc.
      apply TopoOrder_insert; try rewrite <- app_assoc, <- cons_is_app; auto.
      * rewrite Hperm, <- app_assoc, <- Permutation_middle in Hnin; auto.
      * intros ? Ha'. specialize (Ha _ Ha').
        rewrite Hperm, <- app_assoc in Ha.
        repeat (rewrite in_app_iff in *; simpl in *; idtac).
        destruct Ha as [?|[?|[?|?]]]; subst; auto. 2:congruence.
        exfalso.
        eapply Partition_Forall1, Forall_forall in Hpart; [|eauto].
        eapply Hna. etransitivity; eauto.
    + assert (~ In y (xs1 ++ xs2)).
      { apply TopoOrder_NoDup in H0.
        rewrite <- Permutation_middle in H0.
        inv H0; auto. }
      rewrite Hperm, <- app_assoc in H.
      apply not_In_app in H as (?&?).
      apply Before_middle; auto.
  - exists (y::xs). repeat split; auto with acygraph datatypes.
    constructor; auto.
    clear - Hnin.
    induction xs; [constructor|].
    apply not_in_cons in Hnin as (Hneq&Hnin).
    constructor; eauto.
    intro contra; subst; congruence.
  - specialize (IHxs _ _ Hneq H H0 H1 Hna) as (xs'&Hperm&Hpre&Hbef).
    exists (a0::xs'); repeat split; auto.
    + repeat constructor; auto.
      2:intros ? Ha'.
      1,2:rewrite Hperm; auto.
    + constructor; auto.
      intros ?; subst.
      rewrite Hperm; auto.
Qed.

Lemma TopoOrder_AGadda : forall {v a} (g : AcyGraph v a) xs x y Hneq Hin1 Hin2 Hna,
    Before x y xs ->
    TopoOrder g xs ->
    TopoOrder (AGadda _ _ x y g Hneq Hin1 Hin2 Hna) xs.
Proof.
  induction xs; intros * Hbef Hpre; auto with acygraph datatypes.
  inv Hbef. inversion_clear Hpre as [|?? (?&?&?) Hf].
  constructor. 2:eapply IHxs; eauto.
  repeat split; auto.
  intros ? Ha.
  apply add_arc_spec2 in Ha as [?|[(?&?)|[(?&?)|[(?&?)|(?&?)]]]]; subst; auto.
  - apply H3 in H5; auto.
    eapply Before_In in H2; eauto.
  - specialize (H1 eq_refl).
    eapply TopoOrder_weaken, Forall_forall in Hf; eauto.
  - specialize (H3 _ H5).
    eapply Before_In in H2; eauto.
    eapply TopoOrder_weaken, Forall_forall in Hf; eauto.
Qed.

(** Every Directed Acyclic Graph has at least one complete TopoOrder *)
Lemma has_TopoOrder {v a} :
  forall g : AcyGraph v a,
  exists xs,
    PS.Equal (vertices g) (PSP.of_list xs)
    /\ TopoOrder g xs.
Proof.
  revert v a.
  fix has_TopoOrder 3.
  intros *.
  destruct g.
  - exists []; simpl. split; auto with acygraph datatypes.
    reflexivity.
  - specialize (has_TopoOrder _ _ g) as (xs&Heq&Hp).
    destruct (PSP.In_dec x v).
    + exists xs; simpl; split; auto.
      * rewrite <- Heq.
        intros ?. setoid_rewrite PSF.add_iff.
        split; [intros [?|?]| intros ?]; subst; auto.
      * apply TopoOrder_AGaddv; auto.
    + exists (x::xs); simpl; split; [|constructor;repeat split].
      * unfold vertices in *.
        rewrite Heq. reflexivity.
      * rewrite Heq, <- ps_from_list_ps_of_list, ps_from_list_In in n; auto.
      * apply PSF.add_1; auto.
      * intros y Hisarc.
        assert (Hneq:=Hisarc). apply is_trans_arc_neq in Hneq.
        apply is_trans_arc_is_vertex in Hisarc as (?&?).
        apply PSF.add_3 in H; auto.
        rewrite <- ps_from_list_ps_of_list in Heq.
        rewrite <- ps_from_list_In, <- Heq; auto.
      * apply TopoOrder_AGaddv; auto.
  - specialize (has_TopoOrder _ _ g) as (xs&Heq&Hp).
    specialize (TopoOrder_reorganize g xs x y) as (xs'&?&Hp'&Hbef); auto.
    + rewrite Heq, <- ps_from_list_ps_of_list, ps_from_list_In in i; auto.
    + rewrite Heq, <- ps_from_list_ps_of_list, ps_from_list_In in i0; auto.
    + exists xs'; split.
      * rewrite <- ps_from_list_ps_of_list, H, ps_from_list_ps_of_list.
        assumption.
      * eapply TopoOrder_AGadda; eauto.
Qed.
