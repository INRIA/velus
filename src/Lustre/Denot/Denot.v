From Coq Require Import BinPos List.

From Velus Require Import Common Ident Operators Clocks CoindStreams.
From Velus Require Import Lustre.StaticEnv Lustre.LSyntax Lustre.LSemantics.

From Velus Require Import Lustre.Denot.Cpo.

Close Scope equiv_scope. (* conflicting notation "==" *)
Import ListNotations.

Require Import Cpo_ext.
Require Import SDfuns.

Module Type LDENOT
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks   : CLOCKS        Ids Op OpAux)
       (Import Senv  : STATICENV     Ids Op OpAux Cks)
       (Import Syn   : LSYNTAX       Ids Op OpAux Cks Senv)
       (Import Str   : COINDSTREAMS  Ids Op OpAux Cks).

Section Nprod.

Fixpoint nprod (n : nat) : cpo :=
  match n with
  | O => DS (sampl value) (* filled with error_Ty *)
  | 1 => DS (sampl value)
  | S n => Dprod (DS (sampl value)) (nprod n)
  end.

Definition nprod_app : forall {n p}, nprod n -C-> nprod p -C-> nprod (n + p).
  induction n as [|[]]; intro p.
  - exact (CURRY _ _ _ (SND _ _ )).
  - destruct p.
    + exact (CTE _ _).
    + exact (PAIR _ _).
  - apply curry.
    exact ((PAIR _ _ @2_ (FST _ _ @_ FST _ _))
             ((IHn p @2_ (SND _ _ @_ FST _ _)) (SND _ _))).
Defined.

(* obtenir le premier élément *)
Definition nprod_fst {n} : nprod n -C-> DS (sampl value) :=
  match n with
  | O => CTE _ _ (DS_const (err error_Ty))
  | 1 => ID _
  | (S n) => FST _ _
  end.

(* jeter le premier élément *)
Definition nprod_skip {n} : nprod (S n) -C-> nprod n :=
  match n with
  | O => CTE _ _ (DS_const (err error_Ty))
  | (S n) => SND _ _
  end.

Lemma nprod_fst_app :
  forall m n (mp : nprod (S m)) (np : nprod n),
    nprod_fst (nprod_app mp np) = nprod_fst mp.
Proof.
  destruct m, n; auto.
Qed.

(* donne le p-ème flot de np ou DS_const (err error_Ty) *)
Fixpoint get_nth (p : nat) {n} : nprod n -C-> DS (sampl value) :=
  match p with
  | O => nprod_fst
  | S p => match n return nprod n -C-> _ with
          | O => CTE _ _ (DS_const (err error_Ty))
          | S _ => get_nth p @_ nprod_skip
          end
  end.

Lemma get_nth_Oeq_compat :
  forall n k (np np' : nprod n),
    np == np' ->
    get_nth k np == get_nth k np'.
Proof.
  induction n; simpl; intros * Heq.
  - destruct k; auto.
  - destruct n, k; auto.
    + unfold get_nth. now rewrite Heq.
    + simpl. autorewrite with cpodb. auto.
Qed.

Global Add Parametric Morphism n k : (get_nth k)
       with signature (@Oeq (nprod n)) ==> (@Oeq (DS (sampl value))) as get_nth_compat_morph.
Proof.
  exact (get_nth_Oeq_compat n k).
Qed.

Lemma get_nth_skip :
  forall {n} (np : nprod (S n)) k,
    get_nth k (nprod_skip np) = get_nth (S k) np.
Proof.
  induction k; auto.
Qed.

Lemma nprod_app_nth1 :
  forall m n (mp : nprod m) (np : nprod n) k,
    k < m ->
    get_nth k (nprod_app mp np) = get_nth k mp.
Proof.
  induction m; intros * Hk.
  - inversion Hk.
  - destruct k; simpl.
    + now setoid_rewrite nprod_fst_app.
    + autorewrite with cpodb.
      rewrite <- (IHm n _ np); auto with arith.
      destruct m; simpl; auto; lia.
Qed.

Lemma nprod_app_nth2 :
  forall m n (mp : nprod m) (np : nprod n) k,
    k >= m ->
    get_nth k (nprod_app mp np) = get_nth (k-m) np.
Proof.
  induction m; intros * Hk.
  - simpl in *. autorewrite with cpodb; repeat f_equal; auto with arith.
  - Opaque nprod_app.
    destruct k; simpl.
    + lia.
    + destruct m, n; auto with arith.
      * destruct k; simpl; now autorewrite with cpodb.
      * rewrite <- (IHm _ (nprod_skip mp)); auto with arith.
      * rewrite <- (IHm _ (nprod_skip mp)); auto with arith.
      * rewrite <- (IHm _ (nprod_skip mp)); auto with arith.
Qed.

(* TODO: !! simplifier
   comme nprod ne concerne que les value, le polymorphisme de F est inutile.
   Donc changer soit le type de F, soit le type de nprod (paramétré par un
   type de flot ??
 *)
Fixpoint lift (F : forall D, DS (sampl D) -C-> DS (sampl D)) {n} {struct n} : nprod n -C-> nprod n :=
  match n with
  | O => ID _
  | S n =>
      match n return nprod n -C-> nprod n -> nprod (S n) -C-> nprod (S n) with
      | O => fun _ => F _
      | S _ => fun fn => PROD_map (F _) fn
      end (@lift F n)
  end.

(* TODO: comment le définir directement ? *)
Definition llift D (F : DS (sampl value) -C-> D -C-> DS (sampl value)) {n} :
  nprod n -C-> D -C-> nprod n.
  induction n as [|[]].
  - apply CTE.
  - apply F.
  - apply curry.
    apply (fcont_comp2 (PAIR _ _)).
    exact ((F @2_ (FST _ _ @_ FST _ _)) (SND _ _)).
    exact ((IHn @2_ (SND _ _ @_ FST _ _)) (SND _ _)).
Defined.

Lemma llift_simpl :
  forall D F n d u U,
    @llift D F (S (S n)) (u, U) d = (F u d, @llift D F (S n) U d).
Proof.
  trivial.
Qed.

Lemma llift_nth :
  forall D F d,
  forall {n} (np : nprod n) k,
    k < n ->
    get_nth k (llift D F np d) = F (get_nth k np) d.
Proof.
  induction n as [|[]]; intros; auto; try lia.
  - destruct k; simpl; auto; lia.
  - destruct np.
    rewrite llift_simpl.
    destruct k; auto.
    rewrite <- get_nth_skip.
    setoid_rewrite <- IHn; auto with arith.
Qed.

Definition lift2
  (F : forall A : Type, DS (sampl A) -C-> DS (sampl A) -C-> DS (sampl A)) {n} :
  nprod n -C-> nprod n -C-> nprod n.
  induction n as [|[]].
  - exact 0. (* ? *)
  - exact (F _).
  - apply curry.
    apply (fcont_comp2 (PAIR _ _)).
    exact ((F _ @2_ (FST _ _ @_ FST _ _ )) (FST _ _ @_ SND _ _ )).
    exact ((IHn @2_ (SND _ _ @_ FST _ _ )) (SND _ _ @_ SND _ _ )).
Defined.

Lemma lift2_simpl :
  forall F n u U v V,
    @lift2 F (S (S n)) (u, U) (v, V) = (F _ u v, @lift2 F (S n) U V).
Proof.
  trivial.
Qed.

Lemma lift2_nth :
  forall (f : forall A, DS (sampl A) -C-> DS (sampl A) -C-> DS (sampl A)),
  forall {n} (np np' : nprod n) k,
    k < n ->
    get_nth k (lift2 f np np') = f _ (get_nth k np) (get_nth k np').
Proof.
  induction n as [|[]]; intros; auto; try lia.
  - destruct k; simpl; auto; lia.
  - destruct np, np'.
    rewrite lift2_simpl.
    destruct k; auto.
    rewrite <- 3 get_nth_skip, <- IHn; auto with arith.
Qed.

Fixpoint nprod_const (c : sampl value) n {struct n} : nprod n :=
  match n with
  | O => DS_const (err error_Ty)
  | S n =>
      match n return nprod n -> nprod (S n) with
      | O => fun _ => DS_const c
      | S m => fun np => (DS_const c, np)
      end (nprod_const c n)
  end.

Lemma get_nth_const :
  forall c n k,
    k < n ->
    get_nth k (nprod_const c n) = DS_const c.
Proof.
  induction n as [|[]]; intros * Hk.
  - inversion Hk.
  - destruct k; auto; lia.
  - destruct k; auto.
    rewrite <- get_nth_skip, IHn; auto with arith.
Qed.

End Nprod.

Section Forall_Nprod.

Variable P : DS (sampl value) -> Prop.

Definition forall_nprod {n} (np : nprod n) : Prop.
  induction n as [|[]]; simpl in *.
  - exact True.
  - exact (P np).
  - exact (P (fst np) /\ IHn (snd np)).
Defined.

Lemma forall_nprod_skip :
  forall {n} (np : nprod (S n)),
    forall_nprod np ->
    forall_nprod (nprod_skip np).
Proof.
  intros * Hnp.
  destruct n.
  - now simpl.
  - destruct Hnp. auto.
Qed.

Lemma forall_nprod_k :
  forall {n} (np : nprod n),
    (forall k, k < n -> P (get_nth k np)) ->
    forall_nprod np.
Proof.
  induction n as [|[]]; intros * Hk.
  - constructor.
  - apply (Hk O); auto.
  - split.
    + apply (Hk O); auto with arith.
    + apply IHn; intros.
      change (snd np) with (nprod_skip np).
      rewrite get_nth_skip; auto with arith.
Qed.

Lemma forall_nprod_k' :
  forall {n} (np : nprod n),
    forall_nprod np ->
    (forall k, k < n -> P (get_nth k np)).
Proof.
  induction n as [|[]]; intros * Hk.
  - lia.
  - intros.
    assert (k = O) by lia; subst.
    now simpl in Hk.
  - intros.
    specialize (IHn (nprod_skip np)).
    setoid_rewrite get_nth_skip in IHn.
    destruct k. { destruct Hk; auto. }
    apply IHn; auto using forall_nprod_skip with arith.
Qed.

Lemma forall_nprod_k_iff :
  forall {n} (np : nprod n),
    forall_nprod np <-> (forall k, k < n -> P (get_nth k np)).
Proof.
  split; auto using forall_nprod_k, forall_nprod_k'.
Qed.

Lemma forall_nprod_app :
  forall {n m} (np : nprod n) (mp : nprod m),
    forall_nprod np ->
    forall_nprod mp ->
    forall_nprod (nprod_app np mp).
Proof.
  intros * Hnp Hmp.
  apply forall_nprod_k.
  intros * Hk.
  destruct (Nat.lt_ge_cases k n).
  - rewrite nprod_app_nth1; auto using forall_nprod_k'.
  - rewrite nprod_app_nth2; auto.
    apply forall_nprod_k'; auto; lia.
Qed.

Lemma app_forall_nprod :
  forall {n m} (np : nprod n) (mp : nprod m),
    forall_nprod (nprod_app np mp) ->
    forall_nprod np
    /\ forall_nprod mp.
Proof.
  setoid_rewrite forall_nprod_k_iff.
  intros * Hf; split; intros k Hk.
  - specialize (Hf k).
    rewrite nprod_app_nth1 in Hf; auto with arith.
  - specialize (Hf (n + k)).
    rewrite nprod_app_nth2, minus_plus in Hf; auto with arith.
Qed.

Lemma forall_nprod_lift2 :
  forall (f : forall A, DS (sampl A) -C-> DS (sampl A) -C-> DS (sampl A)),
    (forall x y, P x -> P y -> P (f _ x y)) ->
    forall {n} (np np' : nprod n),
      forall_nprod np ->
      forall_nprod np' ->
      forall_nprod (lift2 f np np').
Proof.
  intros f Hf.
  induction n as [|[]]; intros * H H'; auto.
  simpl in *; auto.
  destruct np,np',H,H'.
  rewrite lift2_simpl.
  split; simpl in *; auto .
  now apply IHn.
Qed.

Lemma forall_nprod_const :
  forall {n} c,
    P (DS_const c) ->
    forall_nprod (nprod_const c n).
Proof.
  intros.
  apply forall_nprod_k; intros.
  now rewrite get_nth_const.
Qed.

Global Add Parametric Morphism n
  (P_compat:  Morphisms.Proper (Oeq (O := DS (sampl value)) ==> iff) P)
  : (forall_nprod)
    with signature Oeq (O := nprod n) ==> iff
      as forall_nprod_morph.
Proof.
  unfold Morphisms.Proper, Morphisms.respectful, Basics.impl in *.
  intros * Heq.
  rewrite 2 forall_nprod_k_iff.
  split; intros.
  eapply P_compat; rewrite <- ?Heq; auto.
  eapply P_compat; rewrite ?Heq; auto.
Qed.

End Forall_Nprod.

Lemma forall_nprod_impl :
  forall (P Q : DS (sampl value) -> Prop),
    (forall x, P x -> Q x) ->
    forall {n} (np : nprod n),
      forall_nprod P np ->
      forall_nprod Q np.
Proof.
  induction n as [|[]]; intros * Hf; auto.
  - now simpl in *; auto.
  - destruct Hf.
    split; auto.
    now apply IHn.
Qed.

Lemma forall_nprod_and :
  forall (P Q : DS (sampl value) -> Prop),
    forall {n} (np : nprod n),
    forall_nprod P np ->
    forall_nprod Q np ->
    forall_nprod (fun x => P x /\ Q x) np.
Proof.
  induction n as [|[]]; intros * Hp Hq; auto.
  - constructor; auto.
  - inv Hp. inv Hq.
    constructor; auto; now apply IHn.
Qed.

Lemma forall_nprod_llift :
  forall D (F : DS (sampl value) -C-> D -C-> DS (sampl value)) d,
  forall (P Q : DS (sampl value) -> Prop),
    (forall x, Q x -> P (F x d)) ->
    forall {n} (np : nprod n),
      forall_nprod Q np ->
      forall_nprod P (llift _ F np d).
Proof.
  intros D F d ?? Hf.
  induction n as [|[]]; intros * H; auto.
  simpl in *; auto.
  destruct np, H.
  rewrite llift_simpl.
  split; simpl in *; auto .
  now apply IHn.
Qed.

(* TODO: bouger cette section et les précédentes dans un autre fichier *)
Section List_of_nprod.

Fixpoint list_of_nprod {n} (np : nprod n) : list (DS (sampl value)) :=
  match n return nprod n -> _ with
  | O => fun _ => []
  | S m => fun np => nprod_fst np :: match m with
                   | O => []
                   | _ => list_of_nprod (nprod_skip np)
                   end
  end np.

Lemma list_of_nprod_app :
  forall {n m} (np : nprod n) (mp : nprod m),
    list_of_nprod (nprod_app np mp) = list_of_nprod np ++ list_of_nprod mp.
Proof.
  induction n as [|[]]; intros; auto.
  - destruct m; auto.
  - destruct np as (p,np).
    specialize (IHn _ np mp).
    simpl; f_equal; auto.
Qed.

Lemma list_of_nprod_nth :
  forall {n} (np : nprod n) k d,
    k < n ->
    nth k (list_of_nprod np) d = get_nth k np.
Proof.
  induction n as [|[]]; auto; intros * Hk. inv Hk.
  - destruct k as [|[]]; now inv Hk.
  - destruct k; auto.
    apply IHn; auto with arith.
Qed.

Lemma forall_nprod_Forall :
  forall P {n} (np : nprod n),
    forall_nprod P np ->
    Forall P (list_of_nprod np).
Proof.
  induction n as [|[]]; intros * Hf.
  - constructor.
  - constructor; auto.
  - inversion Hf.
    constructor; auto.
    now apply IHn.
Qed.

Lemma Forall_forall_nprod :
  forall P {n} (np : nprod n),
    Forall P (list_of_nprod np) ->
    forall_nprod P np.
Proof.
  induction n as [|[]]; intros * Hf.
  - constructor.
  - inv Hf. auto.
  - inv Hf.
    constructor; auto.
    now apply IHn.
Qed.

Lemma list_of_nprod_length :
  forall {n} (np : nprod n),
    length (list_of_nprod np) = n.
Proof.
  induction n as [|[]]; auto.
  intros []; simpl.
  f_equal. apply IHn.
Qed.

Lemma Forall2_lift2 :
  forall {A} (F : forall A, DS (sampl A) -C-> DS (sampl A) -C-> DS (sampl A))
    (P Q : A -> DS (sampl value) -> Prop),
    (forall a x y, P a x -> P a y -> Q a (F _ x y)) ->
    forall l {n} (l1 l2 : nprod n),
      Forall2 P l (list_of_nprod l1) ->
      Forall2 P l (list_of_nprod l2) ->
      Forall2 Q l (list_of_nprod (lift2 F l1 l2)).
Proof.
  induction l as [|? []]; intros * Hl1 Hl2.
  - simpl_Forall.
    destruct n; simpl in *; auto; congruence.
  - destruct n as [|[]]; simpl in *; simpl_Forall.
    cbn; auto.
  - destruct n as [|[]]; auto.
    inv Hl1; simpl_Forall.
    inv Hl1; simpl_Forall.
    destruct l1 as (s1&l1), l2 as (s2&l2).
    specialize (IHl _ l1 l2).
    rewrite lift2_simpl.
    constructor.
    + inv Hl1. inv Hl2. cbn; auto.
    + inv Hl1. inv Hl2. auto.
Qed.

Lemma Forall2_llift :
  forall {A} D d (F : DS (sampl value) -C-> D -C-> DS (sampl value))
    (P Q : A -> DS (sampl value) -> Prop),
    (forall a x, P a x -> Q a (F x d)) ->
    forall (l : list A) {n} (l1 : nprod n),
      Forall2 P l (list_of_nprod l1) ->
      Forall2 Q l (list_of_nprod (llift _ F l1 d)).
Proof.
  induction l as [|? []]; intros * Hl1.
  - simpl_Forall.
    destruct n; simpl in *; auto; congruence.
  - destruct n as [|[]]; simpl in *; simpl_Forall.
    cbn; auto.
  - destruct n as [|[]]; auto.
    inv Hl1; simpl_Forall.
    inv Hl1; simpl_Forall.
    destruct l1 as (s1&l1).
    specialize (IHl _ l1).
    rewrite llift_simpl.
    constructor.
    + inv Hl1. cbn; auto.
    + inv Hl1. auto.
Qed.

Lemma Forall_llift :
  forall D d (F : DS (sampl value) -C-> D -C-> DS (sampl value))
    (P Q : DS (sampl value) -> Prop),
    (forall x, P x -> Q (F x d)) ->
    forall {n} (np : nprod n),
      Forall P (list_of_nprod np) ->
      Forall Q (list_of_nprod (llift _ F np d)).
Proof.
  intros * HPQ.
  induction n as [|[]]; intros * Hp.
  - simpl_Forall. easy.
  - simpl_Forall. destruct H; subst; try tauto; now apply HPQ.
  - constructor.
    + apply HPQ. now inv Hp.
    + apply IHn; inv Hp; auto.
Qed.

End List_of_nprod.


Section EXP.

Definition SI := fun _ : ident => sampl value.

(* l'opérateur swhen spécialisé aux Velus.Op.value *)
Definition swhenv :=
  let get_tag := fun v => match v with Venum t => Some t | _ => None end in
  @swhen value value enumtag get_tag Nat.eqb.

Definition denot_exp_ (ins : list ident)
  (e : exp) :
  (* (inputs * base clock * env) -> streams *)
  Dprod (Dprod (DS_prod SI) (DS bool)) (DS_prod SI) -C-> nprod (numstreams e).
  epose (denot_var :=
       fun x => if mem_ident x ins
             then PROJ (DS_fam SI) x @_ FST _ _ @_ FST _ _
             else PROJ (DS_fam SI) x @_ SND _ _).
  revert e.
  fix denot_exp 1.
  intro e.
  destruct e eqn:He; simpl (nprod _).
  - (* Econst *)
    apply (sconst (Vscalar (sem_cconst c)) @_ SND _ _ @_ FST _ _).
  - (* Eenum *)
    apply CTE, (DS_const (err error_Ty)).
  - (* Evar *)
    exact (denot_var i).
  - (* Elast *)
    apply CTE, (DS_const (err error_Ty)).
  - (* Eunop *)
    eapply fcont_comp. 2: apply (denot_exp e0).
    destruct (numstreams e0) as [|[]].
    (* pas le bon nombre de flots: *)
    1,3: apply CTE, (DS_const (err error_Ty)).
    destruct (typeof e0) as [|ty []].
    (* pas le bon nombre de flots: *)
    1,3: apply CTE, (DS_const (err error_Ty)).
    exact (sunop (fun v => sem_unop u v ty)).
  - (* Ebinop *)
    apply CTE, (DS_const (err error_Ty)).
  - (* Efby *)
    rename l into e0s.
    rename l0 into es.
    rename l1 into anns.
    clear He.
    (* vérifier le typage *)
    destruct (Nat.eq_dec
                (list_sum (List.map numstreams e0s))
                (list_sum (List.map numstreams es))) as [Heq|].
    destruct (Nat.eq_dec
                (length anns)
                (list_sum (List.map numstreams e0s))
             ) as [->|].
    (* si les tailles ne correspondent pas : *)
    2,3: apply CTE, (nprod_const (err error_Ty) _).
    (* calculer les flots de e0s *)
    assert (Dprod (Dprod (DS_prod SI) (DS bool)) (DS_prod SI) -C-> nprod (list_sum (List.map numstreams e0s))) as s0s.
    { clear Heq.
      induction e0s as [|a].
      + exact (CTE _ _ (DS_const (err error_Ty))).
      + exact ((nprod_app @2_ (denot_exp a)) IHe0s). }
    (* calculer les flots de e0s *)
    assert (Dprod (Dprod (DS_prod SI) (DS bool)) (DS_prod SI) -C-> nprod (list_sum (List.map numstreams es))) as ss.
    { clear Heq.
      induction es as [|a].
      + exact (CTE _ _ (DS_const (err error_Ty))).
      + exact ((nprod_app @2_ (denot_exp a)) IHes). }
    (* calculer les flots de es *)
    rewrite <- Heq in ss.
    exact ((lift2 (@SDfuns.fby) @2_ s0s) ss).
  - (* Earrow *)
    apply CTE, (nprod_const (err error_Ty)).
  - (* Ewhen *)
    rename l into es.
    destruct l0 as (tys,ck).
    destruct (Nat.eq_dec
                (length tys)
                (list_sum (List.map numstreams es))
             ) as [->|].
    2: apply CTE, (nprod_const (err error_Ty) _).
    assert (Dprod (Dprod (DS_prod SI) (DS bool)) (DS_prod SI) -C-> nprod (list_sum (List.map numstreams es))) as ss.
    { clear He.
      induction es as [|a].
      + exact (CTE _ _ (DS_const (err error_Ty))).
      + exact ((nprod_app @2_ (denot_exp a)) IHes). }
    exact ((llift _ (swhenv e0) @2_ ss) (denot_var i)).
  - (* Emerge *)
    apply CTE, (nprod_const (err error_Ty)).
  - (* Ecase *)
    apply CTE, (nprod_const (err error_Ty)).
  - (* Eapp *)
    apply CTE, (nprod_const (err error_Ty)).
Defined.

Definition denot_exp (ins : list ident) (e : exp) :
(* (inputs * base clock * env) -> streams *)
  DS_prod SI -C-> DS bool -C-> DS_prod SI -C-> nprod (numstreams e) :=
  curry (curry (denot_exp_ ins e)).

Ltac forward_apply A :=
  match type of A with
  | ?B -> ?C =>
      assert C; [ apply A |]
  end.

Definition denot_exps_ (ins : list ident) (es : list exp) :
  Dprod (Dprod (DS_prod SI) (DS bool)) (DS_prod SI) -C-> nprod (list_sum (List.map numstreams es)).
  induction es as [|a].
  + exact (CTE _ _ (DS_const (err error_Ty))).
  + exact ((nprod_app @2_ (denot_exp_ ins a)) IHes).
Defined.

Definition denot_exps (ins : list ident) (es : list exp) :
  DS_prod SI -C-> DS bool -C-> DS_prod SI -C-> nprod (list_sum (List.map numstreams es)) :=
  curry (curry (denot_exps_ ins es)).

Lemma denot_exps_eq :
  forall ins e es envI bs env,
    denot_exps ins (e :: es) envI bs env
    = nprod_app (denot_exp ins e envI bs env) (denot_exps ins es envI bs env).
Proof.
  trivial.
Qed.

(* ?????? *)
Definition nprod_add : forall n m : nat, nprod n -> nprod m -> nprod n :=
  fun n m =>
    match Nat.eq_dec n m with
    | left a =>
        eq_rect_r (fun n0 : nat => nprod n0 -> nprod m -> nprod n0)
          (fun mm => lift2 (@fby) mm) a
    | right b => fun (_ : nprod n) (_ : nprod m) => nprod_const abs n
    end.

Definition denot_var ins envI env x : DS (sampl value) :=
  if mem_ident x ins then envI x else env x.

Lemma denot_exp_eq :
  forall ins e envI bs env,
    denot_exp ins e envI bs env =
      match e return nprod (numstreams e) with
      | Econst c => sconst (Vscalar (sem_cconst c)) bs
      | Evar x _ => denot_var ins envI env x
      | Eunop op e an =>
          let se := denot_exp ins e envI bs env in
          match numstreams e as n return nprod n -> nprod 1 with
          | 1 => fun se =>
              match typeof e with
              | [ty] => sunop (fun v => sem_unop op v ty) se
              | _ => DS_const (err error_Ty)
              end
          | _ => fun _ => DS_const (err error_Ty)
          end se
      (* | Ebinop _ _ _ op e1 e2 => *)
      (*     binop (denot_lbinop op) (denot_exp e1 genv env bs) (denot_exp e2 genv env bs) *)
      | Efby e0s es an =>
          let s0s := denot_exps ins e0s envI bs env in
          let ss := denot_exps ins es envI bs env in
          let n := (list_sum (List.map numstreams e0s)) in
          let m := (list_sum (List.map numstreams es)) in
          match Nat.eq_dec n m, Nat.eq_dec (length an) n with
          | left eqm, left eqan =>
              eq_rect_r nprod (lift2 (@SDfuns.fby) s0s (eq_rect_r nprod ss eqm)) eqan
          | _, _ => nprod_const (err error_Ty) _
          end
      (* | Earrow _ e0 e => *)
      (*     lift2 s (@arrow) _ (denot_exp e0 genv env bs) (denot_exp e genv env bs) *)
      (* | Epair _ _ e1 e2 => *)
      (*     PAIR_flat s _ _ (denot_exp e1 genv env bs) (denot_exp e2 genv env bs) *)
      | Ewhen es x k (tys,_) =>
          let ss := denot_exps ins es envI bs env in
          match  Nat.eq_dec (length tys) (list_sum (List.map numstreams es)) with
          | left eqn =>
              eq_rect_r nprod (llift _ (swhenv k) ss (denot_var ins envI env x)) eqn
          | _ => nprod_const (err error_Ty) _
          end
      (* | Emerge _ x vd eT eF => *)
      (*     llift2 s _ (@merge) _ (denot_var s thisd x vd env) *)
      (*       (denot_exp eT genv env bs) (denot_exp eF genv env bs) *)
      (* | Eite _ e eT eF => *)
      (*     llift2 s _ (@ite) _ (denot_exp e genv env bs) *)
      (*       (denot_exp eT genv env bs) (denot_exp eF genv env bs) *)
      (* | Eapp _ _ f fd e => denot_app s gd f fd genv (denot_exp e genv env bs) *)
      (* | Ereset _ _ f fd e er => *)
      (*     reset (denot_app s gd f fd genv) *)
                          (*       (denot_exp er genv env bs) (denot_exp e genv env bs) *)
      | _ => nprod_const (err error_Ty) _
      end.
Proof.
  destruct e; auto; intros envI bs env.
  - (* Evar *)
    unfold denot_exp, denot_exp_, denot_var at 1.
    cases.
  - (* Eunop *)
    unfold denot_exp, denot_exp_ at 1.
    fold (denot_exp_ ins e).
    autorewrite with cpodb using (simpl (fst _); simpl (snd _)).
    generalize (denot_exp_ ins e) as ss.
    generalize (numstreams e) as ne.
    destruct ne as [|[]]; intros; auto.
    destruct (typeof e) as [|? []]; auto.
  - (* Efby*)
    rename l into e0s.
    rename l0 into es.
    rename l1 into a.
    unfold denot_exp, denot_exp_ at 1.
    destruct
      (Nat.eq_dec (list_sum (List.map numstreams e0s)) (list_sum (List.map numstreams es))) as [E1|],
        (Nat.eq_dec (length a) (list_sum (List.map numstreams e0s))) as [E2|]; auto.
    unfold denot_exps.
    (* FIXME: (denot_exps_ e0s) et (denot_exps_ es) apparaissent sous forme déroulée
       à gauche de l'égalité car [denot_exps] n'existait pas encore lors de la définition
       de [denot_exp_]. Coq n'arrive pas à les enrouler avec [fold (denot_exps_ e0s)] et
       [fold (denot_exps_ es)]. On doit l'aider avec la tactique suivante.
     *)
    do 2 match goal with
     | |- context [  (list_rect ?A ?B ?C ?D) ] =>
         change (list_rect A B C D) with (denot_exps_ ins D);
         generalize (denot_exps_ ins D); intro (* pour pouvoir détruire E1 et E2 *)
      end.
    now destruct E1, E2.
  - (* Ewhen *)
    destruct l0 as (tys,?).
    unfold denot_exp, denot_exp_, denot_var at 1.
    (* unfold denot_exp, denot_exp_ at 1. *)
    destruct (Nat.eq_dec _ _) as [E|]; auto.
    unfold denot_exps.
    match goal with
     | |- context [  (list_rect ?A ?B ?C ?D) ] =>
         change (list_rect A B C D) with (denot_exps_ ins D);
         generalize (denot_exps_ ins D); intro (* pour pouvoir détruire E1 et E2 *)
    end.
    unfold eq_rect_r, eq_rect, eq_sym; cases.
Qed.

Global Opaque denot_exp.

End EXP.


Definition denot_equation (ins : list ident) (e : equation) :
  DS_prod SI -C-> DS bool -C-> DS_prod SI -C-> DS_prod SI.
  destruct e as (xs,es).
  (* vérification des tailles *)
  destruct (Nat.eq_dec
              (length xs)
              (list_sum (List.map numstreams es))
           ) as [Heq|].
  2:{ apply curry, curry, Dprodi_DISTR.
      exact (fun _ => CTE _ _ (DS_const (err error_Ty))). }
  pose proof (ss := denot_exps_ ins es).
  apply curry, curry, Dprodi_DISTR.
  intro x.
  destruct (mem_ident x ins).
  (* si x est une entrée *)
  exact (PROJ (DS_fam SI) x @_ FST _ _ @_ FST _ _).
  (* x est un indice dans l'environment des sorties. S'il apparaît dans
     les xs on le met à jour, sinon on regarde dans l'environnement *)
  revert Heq ss.
  generalize (list_sum (List.map numstreams es)) as n; intros.
  (* on ne garde que env et ss (pas les entrées) *)
  eapply fcont_comp2.
  2: exact (SND _ _).
  2: exact ss.
  clear ss.
  apply curry.
  revert dependent n.
  (* TODO: on considère que toutes les sorties sont définies dans
     cette équation. L'alternative est de garder la liste des sorties
     et de faire deux cas lorsque la variable n'appartient pas à xs :
     - si la varible est une sortie : retrouner (env x)
     - sinon, renvoyer error_Ty *)
  induction xs as [| y xs]; intros.
  - exact (CTE _ _ (DS_const (err error_Ty))).
  - destruct (ident_eq_dec x y).
    + exact (nprod_fst @_ SND _ _).
    + eapply fcont_comp.
      * exact (IHxs (length xs) eq_refl).
      * inv Heq.
        exact (PROD_map (ID _) nprod_skip).
Defined.

Section Equation_spec.


(* TODO: bouger cette section, mais où ? *)
Section Mem_nth.

(* retourne l'indice de l'élément dans la liste *)
Fixpoint mem_nth (l : list ident) (x : ident) : option nat :=
  match l with
  | [] => None
  | y :: l =>
      if ident_eq_dec x y then Some O
      else option_map S (mem_nth l x)
  end.

Lemma mem_nth_nth :
  forall l k d,
    NoDup l ->
    k < length l ->
    mem_nth l (nth k l d) = Some k.
Proof.
  induction l; simpl; intros * Hdup Hk. lia.
  destruct k.
  - destruct ident_eq_dec; congruence.
  - inv Hdup. cases; subst.
    + exfalso. auto using nth_In with arith.
    + rewrite IHl; auto with arith.
Qed.

Lemma mem_nth_In :
  forall l x n, mem_nth l x = Some n -> In x l.
Proof.
  induction l as [|y l]; simpl; intros * Hm; try congruence.
  destruct (ident_eq_dec x y); subst; auto.
  apply option_map_inv in Hm as (?&?&?); eauto.
Qed.

Lemma mem_nth_Some :
  forall x l k d,
    mem_nth l x = Some k ->
    k < length l /\ nth k l d = x.
Proof.
  induction l; simpl; intros * Hk; try congruence.
  destruct ident_eq_dec; subst; inv Hk; auto with arith.
  apply option_map_inv in H0 as (?& HH &?); subst.
  edestruct IHl; eauto with arith.
Qed.

Lemma mem_nth_nin :
  forall x xs,
    mem_nth xs x = None ->
    In x xs ->
    False.
Proof.
  intros * Hf Hin.
  induction xs; simpl in *; cases.
  apply option_map_None in Hf.
  firstorder.
Qed.

End Mem_nth.

Lemma denot_equation_eq :
  forall ins xs es envI bs env x,
    denot_equation ins (xs,es) envI bs env x
    = if Nat.eq_dec (length xs) (list_sum (List.map numstreams es))
      then
        if mem_ident x ins then envI x else
         let ss := denot_exps ins es envI bs env in
         match mem_nth xs x with
         | None => DS_const (err error_Ty)
         | Some n => get_nth n ss
         end
       else DS_const (err error_Ty).
Proof.
  intros ????? env ?.
  unfold denot_equation, denot_exps.
  destruct (Nat.eq_dec (length xs) (list_sum (List.map numstreams es))) as [Heq|]; auto.
  (* FIXME: pourquoi faut-il ajouter ça ? *)
  Local Hint Rewrite (Dprodi_DISTR_simpl _ (DS_fam SI)) : cpodb.
  autorewrite with cpodb using (simpl (snd _); simpl (fst _)).
  destruct (mem_ident x ins); auto.
  autorewrite with cpodb using (simpl (snd _); simpl (fst _)).
  generalize (denot_exps_ ins es).
  revert Heq.
  generalize (list_sum (List.map numstreams es)).
  induction xs; intros; simpl; auto.
  destruct (ident_eq_dec x a); auto.
  destruct Heq; simpl.
  autorewrite with cpodb using (simpl (snd _); simpl (fst _)).
  rewrite IHxs with (t := nprod_skip @_ t).
  destruct (mem_nth xs x); auto.
Qed.

Global Opaque denot_equation.

End Equation_spec.

(* (* 1ère version : construction directe de l'environnement en parcourant *)
(*  l'équation *) *)
(*     Definition denot_equation' (e : equation) : *)
(*       DS_prod type_vars -C-> DS bool -C-> DS_prod type_vars. *)
(*       destruct e as (xs,es). *)
(*       (* vérification des tailles *) *)
(*       destruct (Nat.eq_dec *)
(*                   (length xs) *)
(*                   (list_sum (List.map numstreams es)) *)
(*                ) as [Heq|]. *)
(*       (* 2: exact (CTE _ _ 0). (* TODO : error_Ty *) *) *)
(*       2:{ (* TODO: plus joli *) *)
(*         apply curry, Dprodi_DISTR. *)
(*         intro. apply CTE. unfold type_vars. simpl. *)
(*         cases. exact (DS_const (err error_Ty)). exact (DS_const tt). } *)
(*       (* calcul des expressions *) *)
(*       apply curry. *)
(*       assert (Dprod (DS_prod type_vars) (DS bool) -C-> nprod (list_sum (List.map numstreams es))) as ss. *)
(*       { clear Heq. induction es as [|a]; simpl (list_sum _). *)
(*         + exact (CTE _ _ (DS_const tt)). *)
(*         + exact ((nprod_app _ _ @2_ (uncurry (denot_exp a))) IHes). } *)
(*       (* on construit le produit variable par variable *) *)
(*       apply Dprodi_DISTR. *)
(*       intro x. *)
(*       destruct (existsb (ident_eqb x) (List.map fst vars)) eqn:Hx. *)
(*       2:{ unfold DS_fam, type_vars at 2. *)
(*           rewrite Hx. *)
(*           exact (CTE _ _ (DS_const tt)). (* TODO: plutôt error_Ty ? *) *)
(*       } *)
(*       (* si la variable apparaît dans xs on prend la valeur calculée, *)
(*          sinon celle de l'environment *) *)
(*       remember (list_sum (List.map numstreams es)) as n eqn:Hn. clear Hn. *)
(*       revert dependent n. *)
(*       induction xs as [| y xs]; intros. *)
(*       - exact (PROJ _ x @_ FST _ _). *)
(*       - destruct n. inversion Heq. *)
(*         destruct (ident_eqb x y). *)
(*         + (* on prend l'expression *) *)
(*           unfold DS_fam, type_vars at 2. rewrite Hx. *)
(*           eapply fcont_comp. 2: apply ss. *)
(*           destruct n. *)
(*           * exact (ID _). *)
(*           * exact (FST _ _). *)
(*         + (* on passe à la suite *) *)
(*           inversion Heq; subst. *)
(*           eapply IHxs; eauto. *)
(*           eapply fcont_comp. 2: apply ss. *)
(*           destruct (length xs). *)
(*           * exact (CTE _ _ (DS_const tt)). *)
(*           * exact (SND _ _). *)
(*     Defined. *)

Definition denot_block (ins : list ident) (b : block) :
  DS_prod SI -C-> DS bool -C-> DS_prod SI -C-> DS_prod SI :=
  match b with
  | Beq e => denot_equation ins e
  | _ => curry (curry (FST _ _ @_ FST _ _)) (* garder les entrées *)
  end.

Definition denot_node {PSyn prefs} (n : @node PSyn prefs) :
  DS_prod SI -C-> DS bool -C-> DS_prod SI -C-> DS_prod SI :=
  denot_block (List.map fst n.(n_in)) n.(n_block).



Section Temp.

(* TODO: pour l'instant on se restreint aux cas suivants *)
Inductive restr_exp : exp -> Prop :=
| restr_Econst :
  forall c,
    restr_exp (Econst c)
| restr_Evar :
  forall x ann,
    restr_exp (Evar x ann)
| restr_Eunop :
  forall op e ann,
    restr_exp e ->
    restr_exp (Eunop op e ann)
| restr_Efby :
  forall e0s es anns,
    Forall restr_exp e0s ->
    Forall restr_exp es ->
    restr_exp (Efby e0s es anns)
| restr_Ewhen :
  forall es x k anns,
    Forall restr_exp es ->
    restr_exp (Ewhen es x k anns)
(* | restr_Eapp : *)
(*   forall f es ers anns, *)
(*     Forall restr_exp es -> *)
(*     Forall restr_exp ers -> *)
(*     restr_exp (Eapp f es ers anns) *)
.

Inductive restr_block : block -> Prop :=
| restr_Beq :
  forall xs es,
    Forall restr_exp es ->
    restr_block (Beq (xs,es)).

Definition restr_node {PSyn prefs} (nd : @node PSyn prefs) : Prop :=
  restr_block nd.(n_block).

End Temp.

End LDENOT.

Module LDenotFun
  (Ids   : IDS)
  (Op    : OPERATORS)
  (OpAux : OPERATORS_AUX Ids Op)
  (Cks   : CLOCKS        Ids Op OpAux)
  (Senv  : STATICENV     Ids Op OpAux Cks)
  (Syn   : LSYNTAX       Ids Op OpAux Cks Senv)
  (Str   : COINDSTREAMS  Ids Op OpAux Cks)
<: LDENOT Ids Op OpAux Cks Senv Syn Str.
  Include LDENOT Ids Op OpAux Cks Senv Syn Str.
End LDenotFun.
