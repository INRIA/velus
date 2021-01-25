From Coq Require Import String.
From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Coq Require Import RelationClasses.

From Velus Require Import Common.
From Velus Require Import Environment.

Import Coq.Relations.Relation_Operators.

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

(** Get the successors of a vertex *)
Definition get_succ (x : ident) (a : A_set) :=
  match (Env.find x a) with
  | Some s => s
  | None => PS.empty
  end.

Lemma get_succ_spec : forall a x y,
    PS.In y (get_succ x a) <->
    has_arc a x y.
Proof.
  intros *.
  unfold get_succ, has_arc, Env.MapsTo.
  split; [intros H|intros (?&Hs&Hin)]; destruct Env.find.
  3,4:inv Hs; auto.
  - eauto.
  - destruct (not_In_empty _ H).
Qed.

(** Get the predecessors of a vertex *)
Definition get_pred (x : ident) (a : A_set) :=
  Env.fold (fun y s acc => if PS.mem x s then (PS.add y acc) else acc) a PS.empty.

Lemma get_pred_spec : forall a x y,
    PS.In x (get_pred y a) <->
    has_arc a x y.
Proof.
  intros *.
  unfold get_pred, has_arc, Env.MapsTo.
  apply Env.Props.P.fold_rec.
  - intros ? Hempty.
    rewrite Env.Empty_alt in Hempty.
    split; [intros H|intros (?&Hfind&_)].
    + destruct (not_In_empty _ H).
    + rewrite Hempty in Hfind. congruence.
  - intros * Hm Hnin Hadd Hrec.
    rewrite Hadd; clear Hadd.
    split; [intros H|intros (?&?&?)];
      destruct (PS.mem _ _) eqn:Hmem; destruct (ident_eq_dec x k); subst.
    + rewrite Env.gss; eauto.
    + rewrite Env.gso; eauto.
      apply PSF.add_3 in H; auto.
      apply Hrec in H as (?&?&?); eauto.
    + exfalso. apply Hrec in H as (?&Hfind&?).
      apply Env.find_In in Hfind; auto.
    + rewrite Env.gso; eauto.
      apply Hrec in H as (?&?&?); eauto.
    + apply PSF.add_1; auto.
    + rewrite Env.gso in H; auto.
      apply PSF.add_2. rewrite Hrec; eauto.
    + exfalso.
      rewrite Env.gss in H; auto. inv H.
      apply PSE.mem_4 in Hmem; auto.
    + rewrite Env.gso in H; auto.
      rewrite Hrec; eauto.
Qed.

Definition has_trans_arc a := clos_trans_n1 _ (has_arc a).
Hint Constructors clos_trans_n1.
Hint Unfold has_trans_arc.

Global Instance has_trans_arc_Transitive : forall a,
    Transitive (has_trans_arc a).
Proof.
  intros ? ??? Ha1 Ha2.
  induction Ha2; eauto.
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
Hint Resolve add_arc_has_trans_arc1 add_arc_has_trans_arc2.

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
    + destruct H as [?|(?&?)]; subst; auto.
    + destruct H as [?|(?&?)];
        destruct IHHa as [?|[(?&?)|[(?&?)|[(?&?)|(?&?)]]]];
        subst; eauto 10.
  - destruct Ha as [?|[(?&?)|[(?&?)|[(?&?)|(?&?)]]]]; subst; eauto.
    + etransitivity; eauto.
    + etransitivity; eauto.
    + etransitivity; eauto.
      etransitivity; eauto.
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
Hint Constructors AcyGraph.

Definition vertices {v a} (g : AcyGraph v a) : V_set := v.
Definition arcs {v a} (g : AcyGraph v a) : A_set := a.

Definition is_vertex {v a} (g : AcyGraph v a) (x : ident) : Prop :=
  PS.In x v.

Lemma is_vertex_spec {v a} : forall (g : AcyGraph v a) x,
    is_vertex g x <-> PS.In x (vertices g).
Proof. reflexivity. Qed.

Definition is_arc {v a} (g : AcyGraph v a) x y : Prop :=
  has_arc a x y.

Lemma is_arc_spec {v a} : forall (g : AcyGraph v a) x y,
    is_arc g x y <-> (has_arc (arcs g) x y).
Proof. reflexivity. Qed.

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

Lemma has_arc_trans : forall a x y z,
    has_arc a x y ->
    has_arc a y z ->
    has_trans_arc a x z.
Proof.
  intros * Ha1 Ha2; eauto.
Qed.

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

Corollary has_arc_asym : forall v a,
    AcyGraph v a ->
    Asymmetric (has_arc a).
Proof.
  intros * g ?? Ha1 Ha2.
  eapply is_trans_arc_Asymmetric with (g0:=g); unfold is_trans_arc; eauto.
Qed.

Global Instance is_arc_Asymmetric {v a} (g : AcyGraph v a) :
    Asymmetric (is_arc g).
Proof. eapply has_arc_asym; eauto. Qed.

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

Definition is_arcb {v a} (g : AcyGraph v a) x y : bool :=
  has_arcb a x y.

Lemma is_arcb_spec {v a} : forall (g : AcyGraph v a) x y,
    is_arcb g x y = true <-> is_arc g x y.
Proof.
  intros *.
  unfold is_arcb. rewrite has_arcb_spec.
  reflexivity.
Qed.

Corollary is_arcb_false_iff {v a} : forall (g : AcyGraph v a) x y,
    is_arcb g x y = false <-> ~is_arc g x y.
Proof.
  intros *.
  rewrite <- is_arcb_spec, Bool.not_true_iff_false.
  reflexivity.
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

(** has_arc is decidable ! *)
Lemma has_arc_dec : forall a,
    forall x y, (has_arc a x y) \/ (~has_arc a x y).
Proof.
  intros *.
  unfold has_arc.
  destruct (Env.find x a) eqn:Hfind.
  - destruct (PS.mem y t) eqn:Hmem; [left|right].
    + apply PSF.mem_2 in Hmem.
      exists t; split; auto.
    + intros (?&Hmap&Hin).
      unfold Env.MapsTo in *. rewrite Hfind in Hmap. inv Hmap.
      apply PSF.mem_1 in Hin. congruence.
  - right. intros (?&Hmap&_).
    unfold Env.MapsTo in *. rewrite Hfind in Hmap. inv Hmap.
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

(** ** Building an acyclic graph
    We can try to build an acyclic graph from any graph
    (defined as a mapping from vertices to their direct predecessors)
    We iterate through the list of vertices, trying to add some that are
    not already in the graph, and which predecessors are all already in the graph *)

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

Fact add_after_has_trans_arc2 : forall a preds y x' y',
    has_trans_arc a x' y' ->
    has_trans_arc (add_after preds y a) x' y'.
Proof.
  intros * Ha.
  induction Ha.
  - left. rewrite add_after_spec; auto.
  - eapply tn1_trans; eauto. rewrite add_after_spec; auto.
Qed.

Lemma add_after_spec2 : forall a preds y x' y',
    has_trans_arc (add_after preds y a) x' y' <->
    has_trans_arc a x' y' \/
    (PS.In x' preds /\ y = y') \/
    (PS.In x' preds /\ has_trans_arc a y y') \/
    (PS.Exists (fun p => has_trans_arc a x' p) preds /\ y = y') \/
    (PS.Exists (fun p => has_trans_arc a x' p) preds /\ has_trans_arc a y y').
Proof.
  intros *; split; intros Ha.
  - induction Ha; rewrite add_after_spec in *.
    + destruct H as [?|(?&?)]; subst; auto.
    + destruct H as [?|(?&?)];
        destruct IHHa as [?|[(?&?)|[(?&?)|[(?&?)|(?&?)]]]];
        subst; eauto 10.
      do 3 right. left. split; auto.
      eexists; eauto.
  - destruct Ha as [?|[(?&?)|[(?&?)|[(?&?)|(?&?)]]]]; subst; eauto.
    + eapply add_after_has_trans_arc2; eauto.
    + left. rewrite add_after_spec; auto.
    + eapply add_after_has_trans_arc2 in H0.
      etransitivity; eauto.
      left. rewrite add_after_spec; eauto.
    + destruct H as (?&Hin&Ha).
      eapply add_after_has_trans_arc2 in Ha.
      etransitivity; eauto.
      left. rewrite add_after_spec; eauto.
    + destruct H as (?&Hin&Ha).
      eapply add_after_has_trans_arc2 in Ha.
      eapply add_after_has_trans_arc2 in H0.
      etransitivity; eauto.
      etransitivity; eauto.
      left. rewrite add_after_spec; eauto.
Qed.

Corollary add_after_has_trans_arc1 : forall a preds x' y',
    PS.In x' preds ->
    has_trans_arc (add_after preds y' a) x' y'.
Proof.
  intros * Hin.
  rewrite add_after_spec2; auto.
Qed.

Corollary add_after_has_trans_arc3 : forall {v a} x y preds,
    AcyGraph v a ->
    ~PS.In y v ->
    has_trans_arc (add_after preds y a) x y ->
    PS.In x preds \/ PS.Exists (fun x' => has_trans_arc a x x') preds.
Proof.
  intros * Hacy Hnin Ha.
  rewrite add_after_spec2 in Ha.
  repeat destruct_conj_disj; auto.
  exfalso.
  eapply is_trans_arc_is_vertex with (g:=Hacy) in H as (?&?); eauto.
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

Corollary add_after_AcyGraph' : forall v a x preds,
    ~PS.In x v ->
    ~PS.In x preds ->
    PS.For_all (fun x => PS.In x v) preds ->
    AcyGraph v a ->
    AcyGraph (PS.add x v) (add_after preds x a).
Proof.
  intros * Hnin1 Hnin2 Hpreds Hacy.
  assert (PS.For_all (fun y => ~has_trans_arc a x y) preds) as Hnpreds.
  { intros ? Hin contra.
    specialize (is_trans_arc_is_vertex Hacy) as (?&?); eauto.
  }
  eapply add_after_AcyGraph; eauto.
  - apply PSF.add_1; auto.
  - intros ? Hin. apply Hpreds in Hin.
    apply PSF.add_2; auto.
Qed.

Definition find_addable (v : V_set) (g : Env.t PS.t) :=
  Env.find_pred (fun k preds =>
                   andb (negb (PS.mem k v))
                        (PS.for_all (fun x => PS.mem x v) preds)) g.

Definition errmsg_of_env {A} (s : Env.t A) :=
  Env.fold (fun x _ a => (CTX x)::(MSG ", ")::a) s nil.

Definition acgraph_of_graph g v a :=
  (forall x, Env.In x g <-> PS.In x v) /\
  (forall x y, (exists xs, Env.find y g = Some xs /\ PS.In x xs) -> has_arc a x y).

Program Fixpoint bacg_aux
        (g0 g : Env.t PS.t)
        (Href : Env.refines eq g g0)
        v (ag : exists a, AcyGraph v a /\ acgraph_of_graph (Env.diff g0 g) v a) {measure (Env.cardinal g)}
  : res { v | exists a, AcyGraph v a /\ acgraph_of_graph g0 v a } :=
  match Env.is_empty g with
    | true => OK (exist _ v _)
    | false =>
      match (find_addable v g) with
      | None => Error (MSG "Cannot build acyclic graph, there is a cycle between the following vars : "::(errmsg_of_env g))
      | Some (x, preds) => bacg_aux g0 (Env.remove x g) _ (PS.add x v) _
      end
  end.
Next Obligation.
  exists ag. split; auto.
  rename Heq_anonymous into Hempty. symmetry in Hempty.
  apply Env.is_empty_2 in Hempty.
  clear bacg_aux. destruct H0 as (Hv&Ha).
  constructor.
  - intros ?.
    rewrite <- Hv.
    rewrite Env.diff_empty; auto. reflexivity.
  - intros * (?&Hfind&?).
    apply Ha. eexists; split; eauto.
    rewrite Env.diff_empty; auto.
Qed.
Next Obligation.
  etransitivity; [|eauto].
  eapply Env.refines_remove; auto.
Qed.
Next Obligation.
  clear bacg_aux.
  rename Heq_anonymous into Hfind. symmetry in Hfind.
  rename Heq_anonymous0 into Hempty. symmetry in Hempty.
  apply Env.find_pred_spec in Hfind as (Hin&Hb).
  apply Bool.andb_true_iff in Hb as (Hnin&Hpreds).
  apply Bool.negb_true_iff, PSE.mem_4 in Hnin.
  rewrite PS.for_all_spec in Hpreds. 2:intros ? ? Heq; rewrite Heq; auto.
  exists (add_after preds x ag). destruct H0 as (Hv&Ha).
  split; [|split].
  - eapply add_after_AcyGraph'; eauto.
    intro contra. apply Hpreds in contra; auto.
  - intros ?.
    rewrite PS.add_spec, <- Hv.
    repeat rewrite Env.diff_In_iff.
    split; [intros (?&Hnin')|intros [?|(?&Hnin')]]; subst.
    + destruct (ident_eq_dec x0 x); auto.
      right; split; auto.
      intros contra. apply Hnin'.
      rewrite Env.Props.P.F.remove_in_iff; auto.
    + split.
      * exists preds. eapply Href in Hin as (?&Heq&?); subst; auto.
      * apply Env.remove_1. reflexivity.
    + split; auto.
      intro contra. apply Hnin'.
      apply Env.Props.P.F.remove_in_iff in contra as (?&?); auto.
  - intros x' y' (?&Hfind&Hin').
    specialize (Ha x' y').
    assert (Hfind':=Hfind). apply Env.diff_remove in Hfind' as [(Hneq&Hfind')|?]; subst.
    + specialize (Ha (ex_intro _ _ (conj Hfind' Hin'))) as Harc.
      apply add_after_has_arc1; auto.
    + apply Env.diff_spec in Hfind as (Hfind&?).
      apply Href in Hin as (?&?&Hin); subst.
      rewrite Hfind in Hin. inv Hin.
      apply add_after_has_arc2; auto.
Qed.
Next Obligation.
  clear Heq_anonymous0.
  rename Heq_anonymous into Hfind. symmetry in Hfind.
  apply Env.find_pred_spec in Hfind as (Hin&_).
  erewrite (@Env.Props.P.cardinal_2 _ _ g).
  - apply PeanoNat.Nat.lt_succ_diag_r.
  - apply Env.remove_1. reflexivity.
  - unfold Env.Props.P.Add. intros ?.
    rewrite <- Env.add_remove; auto. apply Hin.
Qed.

Program Definition build_acyclic_graph (g : Env.t PS.t) : res { v | exists a, AcyGraph v a /\ acgraph_of_graph g v a } :=
  bacg_aux g g _ PS.empty _.
Next Obligation.
  exists empty_arc_set; split; auto.
  split.
  - intros ?.
    split; intros H; exfalso.
    + apply Env.In_find in H as (?&Hfind).
      apply Env.diff_spec in Hfind as (Hmap&Hnin).
      apply Env.find_In in Hmap; auto.
    + apply not_In_empty in H; auto.
  - intros xs ? (?&Hfind&Hin).
    exfalso.
    apply Env.diff_spec in Hfind as (Hmap&Hnin).
    apply Env.find_In in Hmap; auto.
Qed.

(** ** Extracting a prefix
    In order to build an induction principle over the graph, we need to linearize it.
    We want to extract a "prefix" from the graph, which is an order of the vertices
    in which arcs are directed from the tail of the list to the head
 *)

Definition Prefix {v a} (g : AcyGraph v a) (xs : list ident) :=
  ForallTail (fun x xs => ~In x xs /\ is_vertex g x /\ (forall y, is_trans_arc g y x -> In y xs)) xs.
Hint Unfold Prefix.

Lemma Prefix_weaken : forall {v a} (g : AcyGraph v a) xs,
    Prefix g xs ->
    Forall (fun x => forall y, is_trans_arc g y x -> In y xs) xs.
Proof.
  intros * Hpref.
  induction Hpref; auto.
  destruct H as (Hnin&Hv&Ha).
  constructor; intuition.
  eapply Forall_impl; [|eauto].
  intros * ? ? ?. right; auto.
Qed.

Lemma Prefix_nIn : forall {v a} (g : AcyGraph v a) x xs,
    ~In x xs ->
    Prefix g xs ->
    ~Exists (fun y => is_trans_arc g x y) xs.
Proof.
  intros * Hnin Hpre Hex.
  apply Prefix_weaken in Hpre.
  eapply Forall_Exists in Hex; eauto.
  eapply Exists_exists in Hex as (?&_&Ha&Ha').
  specialize (Ha _ Ha'); auto.
Qed.

Lemma Prefix_NoDup : forall {v a} (g : AcyGraph v a) xs,
    Prefix g xs ->
    NoDup xs.
Proof.
  intros * Hpref.
  induction Hpref; constructor; auto.
  destruct H; auto.
Qed.

Fact Prefix_AGaddv : forall {v a} (g : AcyGraph v a) x xs,
    Prefix g xs ->
    Prefix (AGaddv v a x g) xs.
Proof.
  induction xs; intros * Hpre; inv Hpre; auto.
  destruct H1 as (?&?&?).
  specialize (IHxs H2).
  repeat constructor; auto.
  apply PSF.add_2; auto.
Qed.

Lemma Prefix_insert : forall {v a} (g : AcyGraph v a) xs1 xs2 x,
    is_vertex g x ->
    ~In x (xs1++xs2) ->
    (forall y, is_trans_arc g y x -> In y xs2) ->
    Prefix g (xs1 ++ xs2) ->
    Prefix g (xs1 ++ x :: xs2).
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
  ForallTail (fun x' xs => x' = y -> In x xs) l.

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
    + induction xs2; auto.
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
Fact Prefix_Partition_split : forall {v a} (g : AcyGraph v a) xs1 xs2 xs1l xs1r y,
    Partition (fun z => is_trans_arc g y z) xs1 xs1l xs1r ->
    Prefix g (xs1 ++ y :: xs2) ->
    Prefix g (xs1l ++ y :: xs1r ++ xs2).
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
    apply Prefix_insert; auto; try rewrite <- app_assoc, <- cons_is_app.
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

(* Is there is no arc between y and x, it is possible to reorganize the Prefix *)
(* so that x ends up before y *)
Lemma Prefix_reorganize : forall {v a} (g : AcyGraph v a) xs x y,
    x <> y ->
    In x xs ->
    In y xs ->
    Prefix g xs ->
    ~is_trans_arc g y x ->
    exists xs', Permutation.Permutation xs' xs /\
           Prefix g xs' /\
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
    + eapply Prefix_Partition_split in H0; eauto.
      rewrite cons_is_app, app_assoc.
      apply Prefix_insert; try rewrite <- app_assoc, <- cons_is_app; auto.
      * rewrite Hperm, <- app_assoc, <- Permutation_middle in Hnin; auto.
      * intros ? Ha'. specialize (Ha _ Ha').
        rewrite Hperm, <- app_assoc in Ha.
        repeat (rewrite in_app_iff in *; simpl in *; idtac).
        destruct Ha as [?|[?|[?|?]]]; subst; auto. 2:congruence.
        exfalso.
        eapply Partition_Forall1, Forall_forall in Hpart; [|eauto].
        eapply Hna. etransitivity; eauto.
    + assert (~ In y (xs1 ++ xs2)).
      { apply Prefix_NoDup in H0.
        rewrite <- Permutation_middle in H0.
        inv H0; auto. }
      rewrite Hperm, <- app_assoc in H.
      apply not_In_app in H as (?&?).
      apply Before_middle; auto.
  - exists (y::xs). repeat split; auto.
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

Lemma Prefix_AGadda : forall {v a} (g : AcyGraph v a) xs x y Hneq Hin1 Hin2 Hna,
    Before x y xs ->
    Prefix g xs ->
    Prefix (AGadda _ _ x y g Hneq Hin1 Hin2 Hna) xs.
Proof.
  induction xs; intros * Hbef Hpre; auto.
  inv Hbef. inversion_clear Hpre as [|?? (?&?&?) Hf].
  constructor. 2:eapply IHxs; eauto.
  repeat split; auto.
  intros ? Ha.
  apply add_arc_spec2 in Ha as [?|[(?&?)|[(?&?)|[(?&?)|(?&?)]]]]; subst; auto.
  - apply H3 in H5; auto.
    eapply Before_In in H2; eauto.
  - specialize (H1 eq_refl).
    eapply Prefix_weaken, Forall_forall in Hf; eauto.
  - specialize (H3 _ H5).
    eapply Before_In in H2; eauto.
    eapply Prefix_weaken, Forall_forall in Hf; eauto.
Qed.

(** Every Directed Acyclic Graph has at least one complete Prefix *)
Lemma has_Prefix : forall {v a} (g : AcyGraph v a),
    exists xs, (PS.Equal (vertices g) (PSP.of_list xs)) /\
          Prefix g xs.
Proof.
  fix has_Prefix 3.
  intros *.
  destruct g.
  - exists []; simpl. split; auto.
    reflexivity.
  - specialize (has_Prefix _ _ g) as (xs&Heq&Hp).
    destruct (PSP.In_dec x v).
    + exists xs; simpl; split; auto.
      * rewrite <- Heq.
        intros ?. setoid_rewrite PSF.add_iff.
        split; [intros [?|?]| intros ?]; subst; auto.
      * apply Prefix_AGaddv; auto.
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
      * apply Prefix_AGaddv; auto.
  - specialize (has_Prefix _ _ g) as (xs&Heq&Hp).
    specialize (Prefix_reorganize g xs x y) as (xs'&?&Hp'&Hbef); auto.
    + rewrite Heq, <- ps_from_list_ps_of_list, ps_from_list_In in i; auto.
    + rewrite Heq, <- ps_from_list_ps_of_list, ps_from_list_In in i0; auto.
    + exists xs'; split.
      * rewrite <- ps_from_list_ps_of_list, H, ps_from_list_ps_of_list.
        assumption.
      * eapply Prefix_AGadda; eauto.
Qed.

(** ** Inserting into the graph
    When we compile the program, what we do is often add some intermediate vertices
    between a set of predecessors and an existing vertex.
 *)

Definition add_between preds x y a :=
  add_arc x y (add_after preds x a).

Lemma add_between_AcyGraph : forall {v a} (g : AcyGraph v a) x preds succ,
    PS.For_all (is_vertex g) preds ->
    is_vertex g succ ->
    PS.For_all (fun p => is_arc g p succ) preds ->
    ~is_vertex g x ->
    AcyGraph (PS.add x v) (add_between preds x succ a).
Proof.
  intros * Hv1 Hv2 Harcs Hnv.
  unfold add_between.
  assert (~has_trans_arc a succ x) as Hna.
  { intro contra.
    eapply is_trans_arc_is_vertex in contra as (?&?); eauto. }
  apply AGadda. apply add_after_AcyGraph'; auto.
  - intro contra; subst.
    contradiction.
  - apply PSF.add_1; auto.
  - apply PSF.add_2; auto.
  - intro contra.
    apply add_after_spec2 in contra as [?|[(?&?)|[(?&?)|[(?&?)|(?&?)]]]]; subst; auto.
    + eapply Harcs, has_arc_irrefl in H; eauto.
    + eapply is_trans_arc_Irreflexive in H0; eauto.
    + destruct H as (p&Hin&Ha). apply Harcs in Hin.
      eapply is_trans_arc_Asymmetric with (g0:=g) in Ha.
      eapply Ha. left; eauto.
    + eapply is_trans_arc_Irreflexive in H0; eauto.
Qed.

Lemma add_between_spec : forall v a preds x y x' y',
    ~PS.In y preds ->
    ~PS.Exists (fun p => has_arc a y p) preds ->
    AcyGraph v a ->
    has_arc (add_between preds x y a) x' y' <->
    has_arc a x' y' \/
    PS.In x' preds /\ x = y' \/
    x = x' /\ y = y'.
Proof.
  intros * Hnin1 Hnin2 Hg. unfold add_between.
  rewrite add_arc_spec, add_after_spec.
  split; intros; repeat destruct_conj_disj; eauto 10.
Qed.

Fact add_between_has_trans_arc2 : forall v a preds x y x' y',
    ~PS.In y preds ->
    ~PS.Exists (fun p => has_arc a y p) preds ->
    AcyGraph v a ->
    has_trans_arc a x' y' ->
    has_trans_arc (add_between preds x y a) x' y'.
Proof.
  intros * Hnin1 Hnin2 Hg Ha.
  induction Ha.
  - left. rewrite add_between_spec; eauto.
  - eapply tn1_trans; eauto. rewrite add_between_spec; eauto.
Qed.

Lemma add_between_spec2 : forall v a preds x y x' y',
    ~PS.In y preds ->
    ~PS.Exists (fun p => has_trans_arc a y p) preds ->
    AcyGraph v a ->
    has_trans_arc (add_between preds x y a) x' y' <->
    has_trans_arc a x' y' \/
    PS.In x' preds /\ x = y' \/
    PS.In x' preds /\ y = y' \/
    x = x' /\ y = y' \/
    PS.Exists (fun p => has_trans_arc a x' p) preds /\ x = y' \/
    PS.Exists (fun p => has_trans_arc a x' p) preds /\ y = y' \/
    has_trans_arc a x' x /\ y = y' \/
    PS.In x' preds /\ has_trans_arc a x y' \/
    PS.In x' preds /\ has_trans_arc a y y' \/
    x = x' /\ has_trans_arc a y y' \/
    PS.Exists (fun p => has_trans_arc a x' p) preds /\ has_trans_arc a x y' \/
    PS.Exists (fun p => has_trans_arc a x' p) preds /\ has_trans_arc a y y' \/
    has_trans_arc a x' x /\ has_trans_arc a y y'.
Proof.
  intros * Hnin1 Hnin2 Hacy.
  assert (~PS.Exists (fun p => has_arc a y p) preds) as Hnin3.
  { intros (x0&Hin&contra).
    apply Hnin2. exists x0; auto. }
  split; intros; unfold PS.Exists in *.
  - induction H.
    + eapply add_between_spec in H; eauto.
      repeat destruct_conj_disj; eauto 10.
    + clear H0. eapply add_between_spec in H; eauto.
      repeat destruct_conj_disj; eauto 16.
      * exfalso; auto.
      * exfalso; eauto.
  - repeat destruct_conj_disj; eauto 15.
    + eapply add_between_has_trans_arc2; eauto.
    + left. rewrite add_between_spec; eauto.
    + etransitivity. 2:apply add_arc_has_trans_arc1.
      apply add_arc_has_trans_arc2.
      rewrite add_after_spec2; auto.
    + apply add_arc_has_trans_arc1.
    + destruct H as (?&Hin&Ha).
      etransitivity. eapply add_between_has_trans_arc2; eauto.
      left; eapply add_between_spec; eauto.
    + destruct H as (?&Hin&Ha).
      etransitivity. eapply add_between_has_trans_arc2; eauto.
      etransitivity; left; eapply add_between_spec; eauto.
    + etransitivity. eapply add_between_has_trans_arc2; eauto.
      left; eapply add_between_spec; eauto.
    + etransitivity. 2:eapply add_between_has_trans_arc2; eauto.
      left; eapply add_between_spec; eauto.
    + etransitivity. 2:eapply add_between_has_trans_arc2; eauto.
      etransitivity; left; eapply add_between_spec; eauto.
    + etransitivity. 2:eapply add_between_has_trans_arc2; eauto.
      left; eapply add_between_spec; eauto.
    + destruct H as (?&Hin&Ha).
      etransitivity. etransitivity. 1,3:eapply add_between_has_trans_arc2; eauto.
      left; eapply add_between_spec; eauto.
    + destruct H as (?&Hin&Ha).
      etransitivity. etransitivity. 1,3:eapply add_between_has_trans_arc2; eauto.
      etransitivity; left; eapply add_between_spec; eauto.
    + etransitivity. etransitivity. 1,3:eapply add_between_has_trans_arc2; eauto.
      left; eapply add_between_spec; eauto.
Qed.

Section remove_arc.

  Definition remove_arc x y (a : A_set) : A_set :=
    match (Env.find x a) with
    | Some s => Env.add x (PS.remove y s) a
    | None => a
    end.

  Lemma remove_arc_spec : forall a x y x' y' ,
      has_arc (remove_arc x y a) x' y' <-> has_arc a x' y' /\ (x <> x' \/ y <> y').
  Proof.
    intros *. unfold remove_arc, has_arc, Env.MapsTo in *.
    split; intros H;
      [destruct H as (s&Hm&Hin)|destruct H as (?&?)];
      destruct (ident_eq_dec x x'), (ident_eq_dec y y'), (Env.find x a) eqn:Hfind; subst.
    1-16:try rewrite Env.gss in *; eauto.
    1-16:try rewrite Env.gso in *; eauto.
    - exfalso. inv Hm.
      apply PSF.remove_1 in Hin; auto.
    - congruence.
    - split; auto.
      inv Hm. exists t; split; auto.
      apply PSF.remove_3 in Hin; auto.
    - exfalso. destruct H0; auto.
    - destruct H as (?&?&?).
      rewrite Hfind in H. inv H.
      exists (PS.remove y x); split; auto.
      apply PSF.remove_2; auto.
  Qed.

  Fact has_arc_has_trans_arc : forall a a' x y,
      (forall x y, has_arc a x y <-> has_arc a' x y) ->
      has_trans_arc a x y <-> has_trans_arc a' x y.
  Proof.
    intros * Ha; split; intros Hta; induction Hta.
    1,3:left; rewrite Ha in *; auto.
    1,2:eapply tn1_trans; eauto; rewrite Ha in *; auto.
  Qed.

  (* Lemma remove_arc_has_trans_arc1 : forall a x y x' y' , *)
  (*     has_trans_arc (remove_arc x y a) x' y' -> *)
  (*     has_trans_arc a x' y'. *)
  (* Proof. *)
  (*   intros * Ha. *)
  (*   induction Ha. *)
  (*   - left. apply remove_arc_spec in H as (?&?); auto. *)
  (*   - eapply tn1_trans; eauto. *)
  (*     apply remove_arc_spec in H as (?&?); auto. *)
  (* Qed. *)

  (* Lemma remove_arc_AcyGraph : forall {v a} x y, *)
  (*     AcyGraph v a -> *)
  (*     exists a', (forall x' y', has_arc a' x' y' <-> has_arc (remove_arc x y a) x' y') /\ *)
  (*       AcyGraph v a'. *)
  (* Proof. *)
  (*   fix remove_arc_AcyGraph 5. *)
  (*   intros * g. *)
  (*   destruct g. *)
  (*   - exists (Env.empty _); split. *)
  (*     + unfold remove_arc. rewrite Env.gempty. reflexivity. *)
  (*     + constructor. *)
  (*   - specialize (remove_arc_AcyGraph _ _ x y g) as (a'&?&?). *)
  (*     exists a'; split; auto. *)
  (*   - specialize (remove_arc_AcyGraph _ _ x y g) as (a'&?&?). *)
  (*     destruct (Decidable.dec_and _ _ (decidable_eq_ident x x0) (decidable_eq_ident y y0)). *)
  (*     + destruct H5; subst. *)
  (*       exists a'. split; auto. *)
  (*       intros x' y'. repeat rewrite remove_arc_spec, add_arc_spec. *)
  (*       split; [intros Ha|intros (?&?)]. *)
  (*       * apply H3, remove_arc_spec in Ha as (?&?); auto. *)
  (*       * rewrite H3, remove_arc_spec. split; auto. *)
  (*         destruct H5 as [?|(?&?)]; subst; auto. *)
  (*         exfalso. destruct H6; auto. *)
  (*     + exists (add_arc x0 y0 a'). *)
  (*       split. 2:constructor; auto. *)
  (*       * intros x' y'. *)
  (*         rewrite add_arc_spec, H3. *)
  (*         repeat rewrite remove_arc_spec. rewrite add_arc_spec. *)
  (*         split; intros; repeat destruct_conj_disj; eauto 10. *)
  (*         split; [auto|]. *)
  (*         apply Decidable.not_and; auto. apply decidable_eq_ident. *)
  (*       * rewrite has_arc_has_trans_arc; auto. *)
  (*         intros Ha. eapply H2, remove_arc_has_trans_arc1; eauto. *)
  (* Qed. *)

  Lemma subset_AcyGraph : forall v a (g : AcyGraph v a) a',
      (forall x y, has_arc a' x y -> has_arc a x y) ->
      exists a'', (forall x y, has_arc a'' x y <-> has_arc a' x y) /\
        AcyGraph v a''.
  Proof.
    fix subset_AcyGraph 3.
    intros * g * Hsub.
    destruct g.
    - exists (Env.empty _); split; auto.
      intros *. split; intros; exfalso.
      + destruct H as (?&Hmap&?). rewrite Env.Props.P.F.empty_mapsto_iff in Hmap; auto.
      + apply Hsub in H. destruct H as (?&Hmap&?). rewrite Env.Props.P.F.empty_mapsto_iff in Hmap; auto.
    - specialize (subset_AcyGraph _ _ g _ Hsub) as (a''&?&?).
      exists a''; split; auto.
    - assert (forall x0 y0 : ident, has_arc (remove_arc x y a') x0 y0 -> has_arc a x0 y0) as Hsub'.
      { intros * Ha.
        apply remove_arc_spec in Ha as (Ha&Hneq). apply Hsub in Ha.
        apply add_arc_spec in Ha as [Ha|(?&?)]; subst; auto.
        exfalso. destruct Hneq; auto.
      }
      specialize (subset_AcyGraph _ _ g _ Hsub') as (a''&Heq''&Hg'').
      destruct (has_arc_dec a' x y).
      + exists (add_arc x y a''). split; [|constructor]; auto.
        * intros *.
          rewrite add_arc_spec, Heq'', remove_arc_spec.
          split; [intros [(?&?)|(?&?)]|intros ?]; subst; auto.
          destruct (ident_eq_dec x x0), (ident_eq_dec y y0); subst; auto.
        * intro contra.
          apply H2.
          erewrite has_arc_has_trans_arc in contra; [|eauto].
          clear - contra Hsub'.
          induction contra; auto.
          eapply tn1_trans; eauto.
      + exists a''. split; auto.
        intros *.
        rewrite Heq'', remove_arc_spec.
        split; [intros (?&?)| intros ?]; auto.
        split; auto.
        destruct (ident_eq_dec x x0), (ident_eq_dec y y0); subst; auto.
  Qed.

End remove_arc.
