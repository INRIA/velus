From Coq Require Import FSets.FMapPositive.
From Coq Require Import FSets.FMapFacts.
From Coq Require Import List.
From Coq Require Import Sorting.Permutation.
From Coq Require Import ZArith.BinInt.

From Coq Require Import Setoid.
From Coq Require Import Relations RelationPairs.
From Coq Require Import Morphisms.

Import ListNotations.
From Coq Require MSets.MSets.
From Coq Require Export PArith.
From Coq Require Import Classes.EquivDec.

From Velus Require Export Common.CommonTactics.
From Velus Require Export Common.CommonList.
From Velus Require Export Common.CommonStreams.
From Velus Require Export Common.CommonPS.
From Coq Require Export PeanoNat.
From Coq Require Export Lia.

Open Scope list.

(** * Common definitions *)

(** ** Finite sets and finite maps *)

(** These modules are used to manipulate identifiers. *)

Definition ident := positive.

Module PS := Coq.MSets.MSetPositive.PositiveSet.
Module PSP := MSetProperties.WPropertiesOn Pos PS.
Module PSF := MSetFacts.Facts PS.
Module PSE := MSetEqProperties.WEqPropertiesOn Pos PS.
Module PSdec := Coq.MSets.MSetDecide.WDecide PS.

Definition ident_eq_dec := Pos.eq_dec.
Definition ident_eqb := Pos.eqb.

Instance: EqDec ident eq := { equiv_dec := ident_eq_dec }.

Implicit Type i j: ident.

(** ** Properties *)

Lemma not_or':
  forall A B, ~(A \/ B) <-> ~A /\ ~B.
Proof.
  split; intuition.
Qed.

Lemma flip_impl:
  forall {P Q : Prop},
    (P -> Q) ->
    ~Q ->
    ~P.
Proof. intros P Q HPQ HnQ HP. auto. Qed.

Lemma None_eq_dne:
  forall {A} (v : option A),
    ~(v <> None) <-> (v = None).
Proof.
  destruct v; intuition.
  exfalso. apply H; discriminate.
Qed.

(** *** About identifiers **)

Lemma ident_eqb_neq:
  forall x y, ident_eqb x y = false <-> x <> y.
Proof.
  unfold ident_eqb; apply Pos.eqb_neq.
Qed.

Lemma ident_eqb_eq:
  forall x y, ident_eqb x y = true <-> x = y.
Proof.
  unfold ident_eqb; apply Pos.eqb_eq.
Qed.

Lemma ident_eqb_refl:
  forall f, ident_eqb f f = true.
Proof.
  unfold ident_eqb; apply Pos.eqb_refl.
Qed.

Lemma ident_eqb_sym:
  forall x y, ident_eqb x y = ident_eqb y x.
Proof Pos.eqb_sym.

Lemma ident_eq_sym:
  forall (x y: ident), x = y <-> y = x.
Proof.
  now intros; split; subst.
Qed.

Lemma decidable_eq_ident:
  forall (f g: ident),
    Decidable.decidable (f = g).
Proof.
  intros f g.
  unfold Decidable.decidable.
  setoid_rewrite <-ident_eqb_eq.
  destruct (ident_eqb f g); auto.
Qed.

Lemma equiv_decb_negb:
  forall x, (x ==b negb x) = false.
Proof. destruct x; simpl; auto. Qed.

Definition mem_assoc_ident {A} (x: ident): list (ident * A) -> bool :=
  existsb (fun y => ident_eqb (fst y) x).

Lemma mem_assoc_ident_false:
  forall {A} x xs (t: A),
    mem_assoc_ident x xs = false ->
    ~ In (x, t) xs.
Proof.
  intros ** Hin.
  apply Bool.not_true_iff_false in H.
  apply H.
  apply existsb_exists.
  exists (x, t); split; auto.
  apply ident_eqb_refl.
Qed.

Lemma mem_assoc_ident_true:
  forall {A} x xs,
    mem_assoc_ident x xs = true ->
    exists t: A, In (x, t) xs.
Proof.
  intros * Hin.
  unfold mem_assoc_ident in Hin; rewrite existsb_exists in Hin.
  destruct Hin as ((x', t) & ? & E).
  simpl in E; rewrite ident_eqb_eq in E; subst x'.
  eauto.
Qed.

Definition assoc_ident {A} (x: ident) (xs: list (ident * A)): option A :=
  match find (fun y => ident_eqb (fst y) x) xs with
  | Some (_, a) => Some a
  | None => None
  end.

Lemma assoc_ident_true :
  forall {A} (x: ident) (y : A) (xs: list (ident * A)),
    NoDupMembers xs ->
    In (x,y) xs ->
    assoc_ident x xs = Some y.
Proof.
  induction xs as [| a]. inversion 2.
  intros Hdup Hin.
  inv Hdup. unfold assoc_ident. simpl. destruct Hin as [He |].
  - inv He. now rewrite ident_eqb_refl.
  - destruct (ident_eqb a0 x) eqn:Heq; auto. apply ident_eqb_eq in Heq.
    subst. exfalso. eauto using In_InMembers.
Qed.

Lemma assoc_ident_false:
  forall {A} (x: ident) (xs: list (ident * A)),
    ~InMembers x xs ->
    assoc_ident x xs = None.
Proof.
  induction xs as [| a]; auto.
  intro nin. unfold assoc_ident. cases_eqn EE.
  apply find_some in EE as [Hin Eq]. destruct a. subst. simpl in *.
  apply ident_eqb_eq in Eq as ->.
  exfalso. apply nin. destruct Hin as [H|H].
  inv H. tauto. eauto using In_InMembers.
Qed.

Module Type IDS.
  Parameter bool_id : ident.
  Parameter true_id : ident.
  Parameter false_id : ident.

  Parameter self : ident.
  Parameter out  : ident.
  Parameter temp : ident.

  Parameter step  : ident.
  Parameter reset : ident.

  Parameter elab : ident.
  Parameter switch : ident.
  Parameter local : ident.
  Parameter norm1 : ident.
  Parameter norm2 : ident.
  Parameter obc2c : ident.

  (** Incremental prefix sets *)
  Definition elab_prefs := PS.singleton elab.
  Definition switch_prefs := PS.add switch elab_prefs.
  Definition local_prefs := PS.add local switch_prefs.
  Definition norm1_prefs := PS.add norm1 local_prefs.
  Definition norm2_prefs := PS.add norm2 norm1_prefs.

  Definition gensym_prefs := [elab; switch; local; norm1; norm2].
  Conjecture gensym_prefs_NoDup : NoDup gensym_prefs.

  Parameter default : ident.

  Conjecture reset_not_step: reset <> step.

  Parameter atom : ident -> Prop.

  Conjecture self_atom : atom self.
  Conjecture out_atom : atom out.
  Conjecture temp_atom : atom temp.

  Conjecture step_atom : atom step.
  Conjecture reset_atom : atom reset.
  Conjecture elab_atom : atom elab.
  Conjecture switch_atom : atom switch.
  Conjecture local_atom : atom local.
  Conjecture norm1_atom : atom norm1.
  Conjecture norm2_atom : atom norm2.
  Conjecture obc2c_atom : atom obc2c.

  (** *** Name generation by prefixing *)

  Parameter prefix : ident -> ident -> ident.

  Conjecture prefix_not_atom:
    forall pref id,
      ~atom (prefix pref id).

  Conjecture prefix_injective:
    forall pref id pref' id',
      prefix pref id = prefix pref' id' ->
      pref = pref' /\ id = id'.

  (** *** Name generation with fresh identifiers *)

  Parameter gensym : ident -> (option ident) -> ident -> ident.

  Conjecture gensym_not_atom:
    forall pref hint x,
      ~atom (gensym pref hint x).

  Conjecture gensym_injective:
    forall pref hint x pref' hint' x',
      gensym pref hint x = gensym pref' hint' x' ->
      pref = pref' /\ x = x'.

  Definition AtomOrGensym (prefs : PS.t) (id : ident) :=
    atom id \/ PS.Exists (fun pre => exists n hint, id = gensym pre hint n) prefs.

End IDS.

Generalizable Variables A.

Lemma equiv_decb_equiv:
  forall `{EqDec A} (x y : A),
    equiv_decb x y = true <-> equiv x y.
Proof.
  intros.
  split; intro; unfold equiv_decb in *;
    destruct (equiv_dec x y); intuition.
Qed.

Lemma nequiv_decb_false:
  forall {A} `{EqDec A} (x y: A),
    (x <>b y) = false <-> (x ==b y) = true.
Proof.
  unfold nequiv_decb, equiv_decb.
  intros. destruct (equiv_dec x y); intuition.
Qed.

Lemma equiv_decb_refl:
  forall `{EqDec A} (x: A),
    equiv_decb x x = true.
Proof.
  intros. now apply equiv_decb_equiv.
Qed.

Lemma nequiv_decb_refl:
  forall x, (x <>b x) = false.
Proof.
  intro x. unfold nequiv_decb.
  apply Bool.negb_false_iff, equiv_decb_refl.
Qed.

Lemma not_equiv_decb_equiv:
  forall `{EqDec A} (x y: A),
    equiv_decb x y = false <-> ~(equiv x y).
Proof.
  split; intro Hne.
  - unfold equiv_decb in Hne.
    now destruct (equiv_dec x y).
  - unfold equiv_decb.
    destruct (equiv_dec x y); [|reflexivity].
    exfalso; now apply Hne.
Qed.

Lemma nequiv_decb_true:
  forall {A R} `{EqDec A R} (x y : A),
    (x <>b y) = true <-> (x =/= y).
Proof.
  unfold nequiv_decb.
  intros; split; intro HH.
  - destruct (equiv_dec x y) as [E|E]; auto.
    apply equiv_decb_equiv in E.
    now rewrite E in HH.
  - apply Bool.eq_true_not_negb. intro E.
    now rewrite equiv_decb_equiv in E.
Qed.

Lemma not_in_filter_nequiv_decb:
  forall y xs,
    ~In y xs ->
    filter (nequiv_decb y) xs = xs.
Proof.
  induction xs as [|x xs IH]; auto.
  intro Ny. apply not_in_cons in Ny as (Ny1 & Ny2). simpl.
  apply nequiv_decb_true in Ny1 as ->.
  now apply IH in Ny2 as ->.
Qed.

Lemma forall2b_Forall2_equiv_decb:
  forall {A R} `{EqDec A R} (xs ys : list A),
    forall2b equiv_decb xs ys = true ->
    Forall2 R xs ys.
Proof.
  intros * FA. apply forall2b_Forall2 in FA.
  now setoid_rewrite equiv_decb_equiv in FA.
Qed.

Definition equiv_decb3 {A R} `{EqDec A R} (x y z : A) : bool :=
  (x ==b y) && (y ==b z).

Lemma equiv_decb3_equiv:
  forall {A R} `{EqDec A R} x y z,
    (equiv_decb3 x y z = true) <-> (x === y /\ y === z).
Proof.
  unfold equiv_decb3. setoid_rewrite Bool.andb_true_iff.
  split; intros (Exy & Eyz).
  - rewrite equiv_decb_equiv in Exy;
      rewrite equiv_decb_equiv in Eyz; auto.
  - setoid_rewrite equiv_decb_equiv; auto.
Qed.

Lemma forall3b_equiv_decb3:
  forall {A R} `{EqDec A R} xs ys zs,
    forall3b equiv_decb3 xs ys zs = true ->
    Forall2 R xs ys /\ Forall2 R ys zs.
Proof.
  setoid_rewrite forall3b_Forall3.
  setoid_rewrite equiv_decb3_equiv.
  induction 2; intuition.
Qed.

Lemma forallb_forall2b_equiv_decb :
  forall {A R} `{EqDec A R} (xs : list (list A)) (ys : list A),
    forallb (fun xs => forall2b equiv_decb xs ys) xs = true ->
    Forall (fun xs => Forall2 R xs ys) xs.
Proof.
  intros * FA. apply forallb_Forall in FA.
  eapply Forall_impl; [|eauto].
  intros ? FA2.
  eapply forall2b_Forall2_equiv_decb; eauto.
Qed.

(** *** About Coq stdlib *)

Lemma pos_le_plus1:
  forall x, (x <= x + 1)%positive.
Proof.
  intros.
  rewrite Pos.add_1_r.
  apply Pos.lt_eq_cases.
  left; apply Pos.lt_succ_diag_r.
Qed.

Lemma pos_lt_plus1:
  forall x, (x < x + 1)%positive.
Proof.
  intros. rewrite Pos.add_1_r. apply Pos.lt_succ_diag_r.
Qed.

Lemma not_None_is_Some:
  forall A (x : option A), x <> None <-> (exists v, x = Some v).
Proof.
  destruct x; intuition.
  exists a; reflexivity.
  discriminate.
  match goal with H:exists _, _ |- _ => destruct H end; discriminate.
Qed.

(* TODO: Why the hell can't I use <> ?!? *)
Corollary not_None_is_Some_Forall:
  forall {A} (xs: list (option A)),
    Forall (fun (v: option A) => ~ v = None) xs ->
    exists ys, xs = map Some ys.
Proof.
  induction 1 as [|?? E].
    - exists []; simpl; eauto.
    - rewrite not_None_is_Some in E. destruct E as (v, E).
      destruct IHForall as (vs & ?); subst.
      exists (v :: vs); simpl; eauto.
Qed.

Lemma not_Some_is_None:
  forall A (x : option A),  (forall v, x <> Some v) <-> x = None.
Proof.
  destruct x; intuition.
  - exfalso; now apply (H a).
  - discriminate.
  - discriminate.
Qed.

Lemma Nat2Z_inj_pow:
  forall m n,
    Z.of_nat (n ^ m) = Zpower.Zpower_nat (Z.of_nat n) m.
Proof.
  induction m; simpl; intro; auto.
  rewrite Znat.Nat2Z.inj_mul, IHm; auto.
Qed.

Section IsNoneSome.
  Context {A : Type}.

  Fixpoint isNone (o : option A) : bool :=
    match o with None => true | Some _ => false end.

  Fixpoint isSome (o : option A) : bool :=
    match o with None => false | Some _ => true end.

  Lemma isSome_true:
    forall (v : option A), isSome v = true <-> exists v', v = Some v'.
  Proof.
    destruct v; simpl; split; intro; eauto; try discriminate.
    now take (exists v', _) and destruct it.
  Qed.

  Lemma isSome_false:
    forall (v : option A), isSome v = false <-> v = None.
  Proof.
    destruct v; simpl; split; intro; eauto; try discriminate.
  Qed.

End IsNoneSome.

(** Miscellaneous *)

Lemma relation_equivalence_subrelation:
  forall {A} (R1 R2 : relation A),
    relation_equivalence R1 R2 <-> (subrelation R1 R2 /\ subrelation R2 R1).
Proof.
  intros.
  unfold relation_equivalence, predicate_equivalence,
  pointwise_lifting, subrelation. firstorder.
Qed.

(** types and clocks *)

Section TypesAndClocks.

  Context {type clock : Type}.

  (* A Lustre variable is declared with a type and a clock.
     In the abstract syntax, a declaration is represented as a triple:
     (x, (ty, ck)) : ident * (type * clock)

     And nodes include lists of triples for lists of declarations.
     The following definitions and lemmas facilitate working with such
     values. *)

  (* Definition dty (x : ident * (type * clock)) : type := fst (snd x). *)
  (* Definition dck (x : ident * (type * clock)) : clock := snd (snd x). *)

  Definition idty : list (ident * (type * clock)) -> list (ident * type) :=
    map (fun xtc => (fst xtc, fst (snd xtc))).

  Definition idck : list (ident * (type * clock)) -> list (ident * clock) :=
    map (fun xtc => (fst xtc, snd (snd xtc))).

  (* idty *)

  Lemma idty_app:
    forall xs ys,
      idty (xs ++ ys) = idty xs ++ idty ys.
  Proof.
    induction xs; auto.
    simpl; intro; now rewrite IHxs.
  Qed.

  Lemma InMembers_idty:
    forall x xs,
      InMembers x (idty xs) <-> InMembers x xs.
  Proof.
    induction xs as [|x' xs]; split; auto; intro HH;
      destruct x' as (x' & tyck); simpl.
    - rewrite <-IHxs; destruct HH; auto.
    - rewrite IHxs. destruct HH; auto.
  Qed.

  Lemma NoDupMembers_idty:
    forall xs,
      NoDupMembers (idty xs) <-> NoDupMembers xs.
  Proof.
    induction xs as [|x xs]; split; inversion_clear 1;
      eauto using NoDupMembers_nil; destruct x as (x & tyck); simpl in *;
      constructor; try rewrite InMembers_idty in *;
      try rewrite IHxs in *; auto.
  Qed.

  Lemma map_fst_idty:
    forall xs,
      map fst (idty xs) = map fst xs.
  Proof.
    induction xs; simpl; try rewrite IHxs; auto.
  Qed.

  Lemma length_idty:
    forall xs,
      length (idty xs) = length xs.
  Proof.
    induction xs as [|x xs]; auto.
    destruct x; simpl. now rewrite IHxs.
  Qed.

  Lemma In_idty_exists:
    forall x (ty : type) xs,
      In (x, ty) (idty xs) <-> exists (ck: clock), In (x, (ty, ck)) xs.
  Proof.
    induction xs as [|x' xs].
    - split; inversion_clear 1. inv H0.
    - split.
      + inversion_clear 1 as [HH|HH];
          destruct x' as (x' & ty' & ck'); simpl in *.
        * inv HH; eauto.
        * apply IHxs in HH; destruct HH; eauto.
      + destruct 1 as (ck & HH).
        inversion_clear HH as [Hin|Hin].
        * subst; simpl; auto.
        * constructor 2; apply IHxs; eauto.
  Qed.

  Lemma idty_InMembers:
    forall x ty (xs : list (ident * (type * clock))),
      In (x, ty) (idty xs) ->
      InMembers x xs.
  Proof.
    intros * Ix.
    unfold idty in Ix.
    apply in_map_iff in Ix as ((y, (yt, yc)) & Dy & Iy). inv Dy.
    apply In_InMembers with (1:=Iy).
  Qed.

  Global Instance idty_Permutation_Proper:
    Proper (@Permutation (ident * (type * clock))
            ==> @Permutation (ident * type)) idty.
  Proof.
    intros xs ys Hperm.
    unfold idty. rewrite Hperm.
    reflexivity.
  Qed.

  (* idck *)

  Lemma idck_app:
    forall xs ys,
      idck (xs ++ ys) = idck xs ++ idck ys.
  Proof.
    induction xs; auto.
    simpl; intro; now rewrite IHxs.
  Qed.

  Lemma InMembers_idck:
    forall x xs,
      InMembers x (idck xs) <-> InMembers x xs.
  Proof.
    induction xs as [|x' xs]; split; auto; intro HH;
      destruct x' as (x' & tyck); simpl.
    - rewrite <-IHxs; destruct HH; auto.
    - rewrite IHxs. destruct HH; auto.
  Qed.

  Lemma NoDupMembers_idck:
    forall xs,
      NoDupMembers (idck xs) <-> NoDupMembers xs.
  Proof.
    induction xs as [|x xs]; split; inversion_clear 1;
      eauto using NoDupMembers_nil; destruct x as (x & tyck); simpl in *;
      constructor; try rewrite InMembers_idck in *;
      try rewrite IHxs in *; auto.
  Qed.

  Lemma map_fst_idck:
    forall xs,
      map fst (idck xs) = map fst xs.
  Proof.
    induction xs; simpl; try rewrite IHxs; auto.
  Qed.

  Lemma length_idck:
    forall xs,
      length (idck xs) = length xs.
  Proof.
    induction xs as [|x xs]; auto.
    destruct x; simpl. now rewrite IHxs.
  Qed.

  Lemma In_idck_exists:
    forall x (ck : clock) xs,
      In (x, ck) (idck xs) <-> exists (ty: type), In (x, (ty, ck)) xs.
  Proof.
    induction xs as [|x' xs].
    - split; inversion_clear 1. inv H0.
    - split.
      + inversion_clear 1 as [HH|HH];
          destruct x' as (x' & ty' & ck'); simpl in *.
        * inv HH; eauto.
        * apply IHxs in HH; destruct HH; eauto.
      + destruct 1 as (ty & HH).
        inversion_clear HH as [Hin|Hin].
        * subst; simpl; auto.
        * constructor 2; apply IHxs; eauto.
  Qed.

  Global Instance idck_Permutation_Proper:
    Proper (Permutation (A:=(ident * (type * clock)))
            ==> Permutation (A:=(ident * clock))) idck.
  Proof.
    intros xs ys Hperm.
    unfold idck. rewrite Hperm.
    reflexivity.
  Qed.

  Lemma filter_fst_idck:
    forall (xs: list (ident * (type * clock))) P,
      idck (filter (fun x => P (fst x)) xs) = filter (fun x => P (fst x)) (idck xs).
  Proof.
    induction xs; simpl; intros; auto.
    cases; simpl; now rewrite IHxs.
  Qed.

End TypesAndClocks.

Lemma In_of_list_InMembers:
  forall {A} x (xs : list (ident * A)),
    PS.In x (PSP.of_list (map fst xs)) <-> InMembers x xs.
Proof.
  split; intros Hin.
  - apply PSP.of_list_1, SetoidList.InA_alt in Hin as (y & Heq & Hin); subst y.
    now apply fst_InMembers.
  - apply PSP.of_list_1, SetoidList.InA_alt.
    apply fst_InMembers in Hin. eauto.
Qed.

(** Useful functions on lists of options *)

Section OptionLists.

  Context {A B : Type}.

  Definition omap (f : A -> option B) : list A -> option (list B) :=
    fold_right (fun x ys => match f x, ys with
                            | Some y, Some ys => Some (y :: ys)
                            | _, _ => None
                            end) (Some []).

  Definition ofold_right (f : A -> B -> option B) : option B -> list A -> option B :=
    fold_right (fun x acc => match acc with
                          | Some acc => f x acc
                          | None => None
                          end).

  Definition ofold_left (f : B -> A -> option B) : list A -> option B -> option B :=
    fold_left (fun acc x => match acc with
                            | Some acc => f acc x
                            | None => None
                            end).

  Lemma ofold_right_none_none:
    forall (f : A -> B -> option B) xs, ofold_right f None xs = None.
  Proof.
    induction xs; simpl; auto. now rewrite IHxs.
  Qed.

End OptionLists.


Definition or_default {A} (d: A) (o: option A) : A :=
  match o with Some a => a | None => d end.

Definition or_default_with {A B} (d: B) (f: A -> B) (o: option A) : B :=
  match o with Some a => f a | None => d end.

(** Lift relations into the option type *)

Section ORel.

  Context {A : Type}
          (R : relation A).

  Inductive orel : relation (option A) :=
  | Oreln : orel None None
  | Orels : forall sx sy, R sx sy -> orel (Some sx) (Some sy).

  Global Instance orel_refl `{RR : Reflexive A R} : Reflexive orel.
  Proof.
    intro sx.
    destruct sx; constructor; auto.
  Qed.

  Global Instance orel_trans `{RT : Transitive A R} : Transitive orel.
  Proof.
    intros sx sy sz XY YZ.
    inv XY; inv YZ; try discriminate; constructor.
    transitivity sy0; auto.
  Qed.

  Global Instance orel_sym `{RS : Symmetric A R} : Symmetric orel.
  Proof.
    intros sx sy XY. inv XY; constructor; symmetry; auto.
  Qed.

  Global Instance orel_equiv `{Equivalence A R} : Equivalence orel.
  Proof. exact (Build_Equivalence orel orel_refl orel_sym orel_trans).
  Qed.

  Global Instance orel_preord `{PreOrder A R} : PreOrder orel.
  Proof. exact (Build_PreOrder orel orel_refl orel_trans).
  Qed.

  Global Instance orel_Some_Proper: Proper (R ==> orel) Some.
  Proof.
    intros x y Rxy. right. eauto.
  Qed.

  Global Instance orel_Proper `{Symmetric A R} `{Transitive A R} :
    Proper (orel ==> orel ==> iff) orel.
  Proof.
    intros ox1 ox2 ORx oy1 oy2 ORy.
    split; intro HH.
    - symmetry in ORx. transitivity ox1; auto. transitivity oy1; auto.
    - symmetry in ORy. transitivity ox2; auto. transitivity oy2; auto.
  Qed.

  Lemma orel_inversion:
    forall x y, orel (Some x) (Some y) <-> R x y.
  Proof.
    split.
    - now inversion 1.
    - intro Rxy. eauto using orel.
  Qed.

End ORel.

Arguments orel {A}%type R%signature.
Hint Extern 4 (orel _ None None) => now constructor.
Hint Extern 5 (orel _ ?x ?x) => reflexivity.

Lemma orel_eq {A : Type} :
  forall x y, orel (@eq A) x y <-> x = y.
Proof.
  intros x y. destruct x, y; split; intro HH; try discriminate; inv HH; auto.
Qed.

Lemma orel_eq_weaken:
  forall {A} R `{Reflexive A R} (x y : option A),
    x = y -> orel R x y.
Proof.
  now intros A R RR x y Exy; subst.
Qed.

Instance orel_option_map_Proper
         {A B} (RA : relation A) (RB : relation B) `{Equivalence B RB}:
  Proper ((RA ==> RB) ==> orel RA ==> orel RB) (@option_map A B).
Proof.
  intros f' f Ef oa' oa Eoa.
  destruct oa'; destruct oa; simpl; inv Eoa; auto.
  take (RA _ _) and specialize (Ef _ _ it).
  now rewrite Ef.
Qed.

Instance orel_option_map_pointwise_Proper
         {A B} (RA : relation A) (RB : relation B)
         `{Equivalence B RB}:
  Proper (pointwise_relation A RB ==> eq ==> orel RB) (@option_map A B).
Proof.
  intros f' f Hf oa' oa Eoa; subst.
  destruct oa; simpl; [|reflexivity].
  apply orel_inversion.
  rewrite Hf. reflexivity.
Qed.

Instance orel_subrelation {A} (R1 R2 : relation A) `{subrelation A R1 R2}:
  subrelation (orel R1) (orel R2).
Proof.
  intros xo yo Ro.
  destruct xo, yo; inv Ro; constructor; auto.
Qed.

(* Should not be necessary, but rewriting through RelProd is often
   very slow or fails. *)
Lemma orel_pair:
  forall {A B} (RA: relation A) (RB: relation B)
    a1 a2 b1 b2,
    RA a1 a2 ->
    RB b1 b2 ->
    orel (RelationPairs.RelProd RA RB) (Some (a1, b1)) (Some (a2, b2)).
Proof.
  intros until b2. intros Ea Eb.
  constructor; auto.
Qed.

Instance orel_subrelation_Proper {A}:
  Proper (@subrelation A ==> eq ==> eq ==> Basics.impl) orel.
Proof.
  intros R2 R1 HR ox2 ox1 ORx oy2 oy1 ORy HH; subst.
  destruct ox1, oy1; inv HH; auto.
  take (R2 _ _) and apply HR in it. now constructor.
Qed.

Instance orel_equivalence_Proper {A}:
  Proper (@relation_equivalence A ==> eq ==> eq ==> iff) orel.
Proof.
  intros R2 R1 HR ox2 ox1 ORx oy2 oy1 ORy; subst.
  apply relation_equivalence_subrelation in HR as (HR1 & HR2).
  split; intro HH. now setoid_rewrite <-HR1. now setoid_rewrite <-HR2.
Qed.

Instance orel_EqDec {A R} `{EqDec A R} : EqDec (option A) (orel R) :=
  { equiv_dec := fun xo yo =>
                   match xo, yo with
                   | None, None => left _
                   | Some x, Some y => match x == y with
                                      | left _ => left _
                                      | right _ => right _
                                      end
                   | _, _ => right _
                   end }.
Proof.
  - now take (x === y) and rewrite it.
  - intro HH. take (x =/= y) and apply it. unfold equiv in HH.
    now rewrite orel_inversion in HH.
  - inversion 1.
  - inversion 1.
  - reflexivity.
Qed.

(** Lift boolean relations into the option type *)

Section ORelB.
  Context {A : Type}
          (f : A -> A -> bool).

  Definition orelb (x y : option A) :=
    match x, y with
    | None, None => true
    | Some x, Some y => f x y
    | _, _ => false
    end.

  Lemma orelb_orel : forall R x y,
      (forall x y, f x y = true <-> R x y) ->
      orelb x y = true <-> orel R x y.
  Proof.
    intros * Heq.
    destruct x, y; simpl.
    - rewrite Heq; split; intros.
      constructor; auto. inv H; auto.
    - split; intros. 1,2:inv H.
    - split; intros. 1,2:inv H.
    - split; intros. 1,2:constructor.
  Qed.

End ORelB.

(** Lift relations between elements of different types into the option type *)

Section ORel2.

  Context {A B : Type}
          (R : A -> B -> Prop).

  Inductive orel2 : option A -> option B -> Prop :=
  | Orel2n : orel2 None None
  | Orel2s : forall sx sy,
      R sx sy ->
      orel2 (Some sx) (Some sy).

  Lemma orel2_inversion:
    forall x y, orel2 (Some x) (Some y) <-> R x y.
  Proof.
    split.
    - now inversion 1.
    - intro Rxy. eauto using orel2.
  Qed.

End ORel2.

Lemma option_map_inv:
  forall {A B} (f: A -> B) oa b,
    option_map f oa = Some b ->
    exists a, oa = Some a /\ b = f a.
Proof.
  unfold option_map; intros * E.
  cases; inv E; eauto.
Qed.

Lemma option_map_None:
  forall {A B} (f: A -> B) oa,
    option_map f oa = None <-> oa = None.
Proof.
  unfold option_map; intros; cases; intuition; discriminate.
Qed.

(** The option monad *)

(* Do notation, lemmas and tactis for the option monad taken directly
     from CompCert's error_monad_scope (X. Leroy).

     We introduce several operators to facilitate Proper lemmas around the
     orel relation and a notation for improved readability. *)

Definition obind {A B: Type} (f: option A) (g: A -> option B) : option B :=
  match f with
  | Some x => g x
  | None => None
  end.

Definition obind2 {A B C: Type} (f: option (A * B)) (g: A -> B -> option C) : option C :=
  match f with
  | Some (x, y) => g x y
  | None => None
  end.

Notation "'do' X <- A ; B" := (obind A (fun X => B))
                                (at level 200, X ident, A at level 100, B at level 200)
                              : option_monad_scope.

Notation "'do' ( X , Y ) <- A ; B" := (obind2 A (fun X Y => B))
                                        (at level 200, X ident, Y ident, A at level 100, B at level 200)
                                      : option_monad_scope.

Remark obind_inversion:
  forall (A B: Type) (f: option A) (g: A -> option B) (y: B),
    obind f g = Some y ->
    exists x, f = Some x /\ g x = Some y.
Proof.
  intros until y. destruct f; simpl; intros.
  exists a; auto. discriminate.
Qed.

Remark obind2_inversion:
  forall {A B C: Type} (f: option (A*B)) (g: A -> B -> option C) (z: C),
    obind2 f g = Some z ->
    exists x, exists y, f = Some (x, y) /\ g x y = Some z.
Proof.
  intros until z. destruct f; simpl.
  destruct p; simpl; intros. exists a; exists b; auto.
  intros; discriminate.
Qed.

Local Open Scope option_monad_scope.

Remark omap_inversion:
  forall (A B: Type) (f: A -> option B) (l: list A) (l': list B),
    omap f l = Some l' ->
    Forall2 (fun x y => f x = Some y) l l'.
Proof.
  induction l; simpl; intros.
  inversion_clear H. constructor.
  destruct (f a) eqn:Hfa; [|discriminate].
  destruct (omap f l); inversion_clear H.
  constructor; auto.
Qed.

(** The [omonadInv H] tactic below simplifies hypotheses of the form
<<
        H: (do x <- a; b) = OK res
>>
       By definition of the obind operation, both computations [a] and
       [b] must succeed for their composition to succeed.  The tactic
       therefore generates the following hypotheses:

         x: ...
        H1: a = OK x
        H2: b x = OK res
 *)

Ltac omonadInv1 H :=
  match type of H with
  | (Some _ = Some _) =>
    inversion H; clear H; try subst
  | (None = Some _) =>
    discriminate
  | (obind ?F ?G = Some ?X) =>
    let x := fresh "x" in (
      let EQ1 := fresh "EQ" in (
        let EQ2 := fresh "EQ" in (
          destruct (obind_inversion F G H) as (x & EQ1 & EQ2);
          clear H; try (omonadInv1 EQ2))))
  | (obind2 ?F ?G = Some ?X) =>
    let x1 := fresh "x" in (
      let x2 := fresh "x" in (
        let EQ1 := fresh "EQ" in (
          let EQ2 := fresh "EQ" in (
            destruct (obind2_inversion F G H) as (x1 & x2 & EQ1 & EQ2);
            clear H; try (omonadInv1 EQ2)))))
  | (match ?X with left _ => _ | right _ => None end = Some _) =>
    destruct X; [try (omonadInv1 H) | discriminate]
  | (match (negb ?X) with true => _ | false => None end = Some _) =>
    destruct X as [] eqn:?; [discriminate | try (omonadInv1 H)]
  | (match ?X with true => _ | false => None end = Some _) =>
    destruct X as [] eqn:?; [try (omonadInv1 H) | discriminate]
  | (omap ?F ?L = Some ?M) =>
    generalize (omap_inversion F L H); intro
  end.

Ltac omonadInv H :=
  omonadInv1 H ||
             match type of H with
             | (?F _ _ _ _ _ _ _ _ = Some _) =>
               ((progress simpl in H) || unfold F in H); omonadInv1 H
             | (?F _ _ _ _ _ _ _ = Some _) =>
               ((progress simpl in H) || unfold F in H); omonadInv1 H
             | (?F _ _ _ _ _ _ = Some _) =>
               ((progress simpl in H) || unfold F in H); omonadInv1 H
             | (?F _ _ _ _ _ = Some _) =>
               ((progress simpl in H) || unfold F in H); omonadInv1 H
             | (?F _ _ _ _ = Some _) =>
               ((progress simpl in H) || unfold F in H); omonadInv1 H
             | (?F _ _ _ = Some _) =>
               ((progress simpl in H) || unfold F in H); omonadInv1 H
             | (?F _ _ = Some _) =>
               ((progress simpl in H) || unfold F in H); omonadInv1 H
             | (?F _ = Some _) =>
               ((progress simpl in H) || unfold F in H); omonadInv1 H
             end.

(* Reasoning about the option monad *)

Section OptionReasoning.

  Context {A B C : Type}.

  (* Rewriting the first argument (in [orel RA]) induces a reflexivity/Proper
     requirement on the second (higher-order) argument. The simplest
     solution is to declare it [Proper (RA ==> orel RB)]. *)
  Global Add Parametric Morphism
         {RA : relation A} {RB : relation (option B)} `{Reflexive _ RB} : obind
      with signature (orel RA ==> (RA ==> RB) ==> RB)
        as obind_orel_ho.
  Proof.
    intros oa1 oa2 Eoa f1 f2 Ef.
    destruct oa1 as [a1|]; inv Eoa; auto.
    now take (RA _ _) and specialize (Ef _ _ it).
  Qed.

  Global Add Parametric Morphism (RB : relation (option B)) `{Reflexive _ RB} : obind
      with signature (@eq (option A) ==> (pointwise_relation A RB) ==> RB)
        as obind_pointwise.
  Proof.
    intros f g1 g2 PW.
    destruct f; simpl; auto.
  Qed.

  Global Add Parametric Morphism
         (RA : relation A) (RB : relation B) (RC : relation (option C))
         `{Reflexive _ RC} : obind2
      with signature (orel (RA * RB) ==> (RA ==> RB ==> RC) ==> RC)
        as obind2_orel_ho.
  Proof.
    intros oa1 oa2 Eoa f1 f2 Ef.
    destruct oa1 as [(a1, b1)|]; inv Eoa; auto.
    take (A * B)%type and destruct it.
    take ((RA * RB)%signature _ _) and destruct it as (HA & HB).
    specialize (Ef _ _ HA _ _ HB). auto.
  Qed.

  Lemma orel_obind_intro:
    forall (RA: relation A) {RB: relation B}
      {oa1 oa2 : option A} {f1 f2 : A -> option B},
      orel RA oa1 oa2 ->
      (forall a1 a2, oa1 = Some a1 ->
                oa2 = Some a2 ->
                RA a1 a2 ->
                orel RB (f1 a1) (f2 a2)) ->
      orel RB (obind oa1 f1) (obind oa2 f2).
  Proof.
    intros * Ha Hf.
    destruct oa1 as [a1|]; inv Ha; simpl; auto.
  Qed.

  Lemma orel_obind_intro_eq:
    forall {RB: relation B} {oa1 oa2 : option A} {f1 f2 : A -> option B},
      oa1 = oa2 ->
      (forall a, oa1 = Some a ->
            oa2 = Some a ->
            orel RB (f1 a) (f2 a)) ->
      orel RB (obind oa1 f1) (obind oa2 f2).
  Proof.
    intros * Ha Hf.
    apply orel_obind_intro with (RA:=eq); subst; [reflexivity|].
    intros a1 a2 Ha H2.
    destruct oa2; try discriminate.
    repeat match goal with H:Some _ = Some _ |- _ => inv H end; auto.
  Qed.

  Lemma orel_obind_intro_same:
    forall {RB: relation B} {oa : option A} {f1 f2 : A -> option B},
      (forall a, oa = Some a ->
            orel RB (f1 a) (f2 a)) ->
      orel RB (obind oa f1) (obind oa f2).
  Proof.
    intros * Hf.
    apply (orel_obind_intro eq); [reflexivity|].
    intros * a Haa; subst; inversion Haa; subst. auto.
  Qed.

  Lemma orel_obind_inversion
        (RA : relation A) `{Reflexive A RA}
        {RB : relation B} `{Equivalence B RB}
        {g} `{Proper _ (RA ==> orel RB) g} :
    forall f q,
      orel RB (obind f g) (Some q)
      <-> (exists p, orel RA f (Some p) /\ orel RB (g p) (Some q)).
  Proof.
    intros f q; split; [intro HH|intros (p & Hf & Hg)].
    2:now setoid_rewrite Hf.
    inversion HH as [|q' q'' Rq Ms]; subst; clear HH.
    symmetry in Ms. apply obind_inversion in Ms as (p & -> & Hg).
    apply (orel_eq_weaken RB) in Hg.
    setoid_rewrite Rq in Hg. exists p; split; auto.
  Qed.
  Global Arguments orel_obind_inversion RA%signature {_} {RB}%signature {_ _ _}.

  Lemma ofold_right_altdef:
    forall (f : A -> B -> option B) xs acc,
      ofold_right f acc xs = fold_right (fun x acc => obind acc (f x)) acc xs.
  Proof. reflexivity. Qed.

  Lemma ofold_right_cons:
    forall (f : A -> B -> option B) x xs acc,
      ofold_right f acc (x::xs) = obind (ofold_right f acc xs) (f x).
  Proof. reflexivity. Qed.

  Global Instance ofold_right_Proper (RA: relation A) (RB: relation B):
    Proper ((RA ==> RB ==> orel RB)
              ==> orel RB ==> SetoidList.eqlistA RA ==> orel RB) ofold_right.
  Proof.
    intros f1 f2 Ef a1 a2 RBa xs1 xs2 RAxs.
    revert xs2 RAxs; induction xs1; intros xs2; inversion 1; subst; auto.
    inv RAxs. simpl.
    take (SetoidList.eqlistA _ _ _) and specialize (IHxs1 _ it).
    destruct (ofold_right f1 a1 xs1); inv IHxs1; auto.
    now apply Ef.
  Qed.

  Global Instance omap_Proper (RA: relation A):
    Proper ((RA ==> orel RA) ==> SetoidList.eqlistA RA
                           ==> orel (SetoidList.eqlistA RA)) omap.
  Proof.
    intros f' f Ef xs' xs Exs.
    induction Exs; simpl. now constructor.
    take (RA x x') and pose proof (Ef _ _ it) as Efx.
    destruct (f' x); inv Efx; auto.
    destruct (omap f' l); inv IHExs; auto.
    constructor; auto.
  Qed.

  Global Instance omap_Proper_pointwise (RA: relation A):
    Proper (pointwise_relation A (orel RA) ==> eq
                               ==> orel (SetoidList.eqlistA RA)) omap.
  Proof.
    intros f' f Ef xs' xs Exs; subst.
    induction xs. now constructor.
    simpl. specialize (Ef a). destruct (f' a); inv Ef; auto.
    destruct (omap f' xs); inv IHxs; auto.
    constructor. auto.
  Qed.

  Lemma orel_omap:
    forall (f g : A -> option B) xs,
      (forall x, orel eq (f x) (g x)) ->
      orel eq (omap f xs) (omap g xs).
  Proof.
    intros f g xs HH.
    induction xs; simpl. now rewrite orel_inversion.
    specialize (HH a).
    destruct (f a); inv HH; auto.
    destruct (omap f xs); inv IHxs; auto.
  Qed.

  Lemma orel_omap_eqlistA (RB : relation B) :
    forall f g (xs : list A),
      (forall x, orel RB (f x) (g x)) ->
      orel (SetoidList.eqlistA RB) (omap f xs) (omap g xs).
  Proof.
    intros f g xs HH.
    induction xs; simpl. now rewrite orel_inversion.
    specialize (HH a).
    destruct (f a); inv HH; auto.
    destruct (omap f xs); inv IHxs; auto.
    constructor. auto.
  Qed.

  Lemma orel_option_map (RB :relation B):
    forall (f g : A -> B) x,
      (forall x, RB (f x) (g x)) ->
      orel RB (option_map f x) (option_map g x).
  Proof.
    intros f g x HH.
    destruct x; simpl; auto.
    constructor. auto.
  Qed.

  (* Helper lemma for rewriting modulo an equivalence at the head of an [obind]
     on the left-hand side of an [orel].
     Usage [setoid_rewrite (orel_obind_head EQ)].

     Rewriting with [orel RA f f'] in a goal like
     [forall z, orel RB (do x <- f; g x) (Some z)]
     requires showing that [g] is [Reflexive] or [Proper] modulo [RA], where
     [g] may be an abstraction over the non-[None] result of [f] or a
     sequence of [obind]s with nested abstractions. In any case, the
     automatically generated proof obligations often cause [typeclasses eauto]
     to fail or even loop. When the tactic does fail, it is difficult to
     translate the error message and debug trace into the required (often
     adhoc) [Proper] terms. This lemma is a lightweight attempt to solve
     the problem by generating and exposing the required term for interactive
     solution. Note that when rewriting under binders (e.g., [z]), only the
     right-hand side of the [orel] may depend on them (not [f], [f'] or [g]).

     Note: successive rewriting over a nesting of [obind]s modulo the same
     relation requires repeatedly solving the same obligations. E.g., in
     [do x <- f; do y <- g x; do z <- h x y; Some (x, y, z)],
     [Proper (RA ==> orel RA) (fun x => do y <- g x; do z <- h x y; Some (x, y, z))]
     contains an obligation that also appears for a second rewrite
     [Proper (RA ==> orel RA) (fun y => do z <- h x y; Some (x, y, z))]. Is
     this inevitable? *)
  Lemma orel_obind_head
        {RA : relation A} {RB : relation B} `{Equivalence _ RB} {f f'}:
    orel RA f f' ->
    forall g, Proper (RA ==> orel RB) g ->
         forall h, orel RB (obind f g) h <-> orel RB (obind f' g) h.
  Proof.
    intros Eff g h Pg. setoid_rewrite Eff. reflexivity.
  Qed.

  Lemma orel_obind2_head
        {RA : relation A} {RB : relation B} {RC : relation C}
        `{Equivalence _ RC} {f f'}:
    orel (RA * RB) f f' ->
    forall g, Proper (RA ==> RB ==> orel RC) g ->
         forall h, orel RC (obind2 f g) h <-> orel RC (obind2 f' g) h.
  Proof.
    intros Eff g h Pg. setoid_rewrite Eff. reflexivity.
  Qed.

  Fixpoint oconcat (xs : list (option (list A))) : option (list A) :=
    match xs with
    | [] => Some ([])
    | None::_ => None
    | Some x :: xs =>
      do xs' <- oconcat xs;
        Some (x ++ xs')
    end.

  Lemma option_map_inv_Some : forall (f : A -> B) oa b,
      option_map f oa = Some b ->
      exists a, oa = Some a /\ f a = b.
  Proof.
    intros f oa b Hmap.
    unfold option_map in Hmap; destruct oa; try congruence.
    inv Hmap.
    exists a; auto.
  Qed.

  Lemma option_map_inv_None : forall (f : A -> B) oa,
      option_map f oa = None ->
      oa = None.
  Proof.
    intros f oa Hmap.
    unfold option_map in Hmap; destruct oa; try congruence.
  Qed.
End OptionReasoning.

Definition orel_obind_intro_endo {A} {R: relation A}
  := @orel_obind_intro A A R R.

Lemma orel_obind2_intro:
  forall {A B C} (RA: relation A) (RB: relation B) {RC: relation C}
    {oab1 oab2 : option (A * B)} {f1 f2 : A -> B -> option C},
    orel (RA * RB) oab1 oab2 ->
    (forall a1 b1 a2 b2, oab1 = Some (a1, b1) ->
                    oab2 = Some (a2, b2) ->
                    RA a1 a2 ->
                    RB b1 b2 ->
                    orel RC (f1 a1 b1) (f2 a2 b2)) ->
    orel RC (obind2 oab1 f1) (obind2 oab2 f2).
Proof.
  intros * Ha Hf.
  apply (orel_obind_intro (RelProd RA RB)); auto.
  intros (a1, b1) (a2, b2) H1 H2; subst.
  rewrite orel_inversion in Ha. destruct Ha; auto.
Qed.

Ltac split_orel_obinds :=
  repeat intro;
  repeat progress
         (subst*; match goal with
                  | |- orel ?RB (match ?e with _ => _ end) (match ?e with _ => _ end) =>
                    destruct e; split_orel_obinds
                  | H: ?equive ?e1 ?e2
                    |- orel ?RA (match ?e1 with _ => _ end)
                           (match ?e2 with _ => _ end) =>
                    setoid_rewrite H
                  | |- orel ?RB (obind ?oa ?f1) (obind ?oa ?f2) =>
                    eapply orel_obind_intro_same; split_orel_obinds
                  | |- orel ?RB (obind ?oa1 ?f1) (obind ?oa2 ?f2) =>
                    eapply orel_obind_intro; split_orel_obinds
                  | |- orel ?RB (obind2 ?oa1 ?f1) (obind2 ?oa2 ?f2) =>
                    eapply orel_obind2_intro; split_orel_obinds
                  | |- orel ?RB (Some _) (Some _) =>
                    eapply orel_inversion
                  | |- RelProd _ _ _ _ =>
                    eapply pair_compat; split_orel_obinds
                  end; (reflexivity || eassumption || idtac)).

Ltac rewrite_orel_obinds :=
  repeat progress
         (subst; match goal with
                 | [ H:?equiv ?L ?R |- context [ ?L ] ] => setoid_rewrite H
                 end; try reflexivity).

Ltac solve_orel_obinds := split_orel_obinds; repeat rewrite_orel_obinds.

Section check_nodup.

  Definition check_nodup (l : list positive) :=
    Nat.eqb (PS.cardinal (ps_from_list l)) (List.length l).

  Lemma check_nodup_correct : forall l,
      check_nodup l = true ->
      NoDup l.
  Proof.
    intros l Hcheck.
    unfold check_nodup in Hcheck.
    rewrite ps_from_list_ps_of_list, PeanoNat.Nat.eqb_eq, PS.cardinal_spec in Hcheck.
    eapply NoDup_length_incl'; eauto.
    + apply PS_elements_NoDup.
    + intros x Hin.
      rewrite In_PS_elements, PSP.of_list_1, InA_alt in Hin.
      destruct Hin as [? [? ?]]; subst; auto.
  Qed.

End check_nodup.

Section sig2.
  Context {A : Type} {P Q : A -> Prop}.

  Lemma sig2_of_sig:
    forall (s : { s : A | P s }),
      Q (proj1_sig s) ->
      { s | P s & Q s }.
  Proof.
    intros (s, Ps) Qs.
    exact (exist2 _ _ s Ps Qs).
  Defined.
  Extraction Inline sig2_of_sig.

  Lemma sig2_weaken2:
    forall {Q' : A -> Prop},
      (forall s, Q s -> Q' s) ->
      { s : A | P s & Q s } ->
      { s | P s & Q' s }.
  Proof.
    intros * HQQ s.
    destruct s as (s, Ps, Qs).
    apply HQQ in Qs.
    exact (exist2 _ _ s Ps Qs).
  Defined.
  Extraction Inline sig2_weaken2.
End sig2.
