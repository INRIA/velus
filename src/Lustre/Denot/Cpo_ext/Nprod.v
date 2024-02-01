From Coq Require Import Morphisms List.
From Velus Require Import Common.CommonList.
From Velus.Lustre.Denot.Cpo Require Import Cpo_def Cpo_streams_type.

Import ListNotations.

Require Import Cpo_def_ext.

(** * Extension of the Cpo library *)

(** ** The cpo of n-uplets. *)
Section Nprod.

Context { D : cpo }.

Fixpoint nprod (n : nat) : cpo :=
  match n with
  | O => D
  | 1 => D
  | S n => Dprod D (nprod n)
  end.

(** extract the first element *)
Definition nprod_hd {n} : nprod (S n) -C-> D :=
  match n with
  | O => ID _
  | (S n) => FST _ _
  end.

(** same with default value if n = 0 *)
Definition nprod_hd_def d {n} : nprod n -C-> D :=
  match n with
  | O => CTE _ _ d
  | (S n) => nprod_hd
  end.

(** throw away the first element *)
Definition nprod_tl {n} : nprod (S n) -C-> nprod n :=
  match n with
  | O => ID _
  | (S n) => SND _ _
  end.

(** cons function *)
Definition nprod_cons {n} : D -C-> nprod n -C-> nprod (S n) :=
   match n with
   | O => CTE _ _
   | S _ => PAIR _ _
   end.

Lemma nprod_cons_Oeq_compat :
  forall (d1 d2 : D) n (np1 np2 : nprod n),
    d1 == d2 ->
    np1 == np2 ->
    nprod_cons d1 np1 == nprod_cons d2 np2.
Proof.
  destruct n; auto.
Qed.

Lemma nprod_hd_tl : forall {n} (np : nprod (S n)),
    np = nprod_cons (nprod_hd np) (nprod_tl np).
Proof.
  destruct n; auto.
  destruct np; auto.
Qed.

Lemma nprod_hd_cons : forall x n (np:nprod n),
    nprod_hd (nprod_cons x np) = x.
Proof.
  destruct n; auto.
Qed.

Lemma nprod_tl_cons : forall x n (np : nprod (S n)),
    nprod_tl (nprod_cons x np) = np.
Proof.
  auto.
Qed.

Lemma nprod_hd_bot : forall n, nprod_hd (0 : nprod (S n)) = 0.
Proof.
  destruct n; reflexivity.
Qed.

Lemma nprod_tl_bot : forall n, nprod_tl (0 : nprod (S n)) = 0.
Proof.
  destruct n; reflexivity.
Qed.

Lemma nprod_cons_bot : forall n, nprod_cons 0 (0 : nprod n) = 0.
Proof.
  destruct n; reflexivity.
Qed.

(** nprod concatenation *)
Fixpoint nprod_app {n p} : nprod n -C-> nprod p -C-> nprod (n + p) :=
  match n return nprod n -C-> nprod p -C-> nprod (n+p) with
  | O => curry (SND _ _)
  | S n => curry ((nprod_cons @2_ nprod_hd @_ FST _ _)
                   ((nprod_app @2_ nprod_tl @_ FST _ _) (SND _ _)))
  end.

Lemma nprod_hd_app :
  forall m n (mp : nprod (S m)) (np : nprod n),
    nprod_hd (nprod_app mp np) = nprod_hd mp.
Proof.
  destruct m, n; auto.
Qed.

Lemma nprod_tl_app :
  forall m n (mp : nprod (S (S m))) (np : nprod n),
    nprod_tl (nprod_app mp np) = nprod_app (nprod_tl mp) np.
Proof.
  destruct m, n; auto.
Qed.

(** extract the k-th element if k < n, [d] otherwise *)
Fixpoint get_nth (k : nat) (d : D) {n} : nprod n -C-> D :=
  match n with
  | O => CTE _ _ d
  | _ => match k with
        | O => nprod_hd
        | S k => get_nth k d @_ nprod_tl
        end
  end.

Lemma get_nth_Oeq_compat :
  forall n k d (np np' : nprod n),
    np == np' ->
    get_nth k d np == get_nth k d np'.
Proof.
  induction n; simpl; intros * Heq.
  - destruct k; auto.
  - destruct n, k; auto.
    + unfold get_nth. now rewrite Heq.
    + simpl. autorewrite with cpodb. auto.
    + simpl. autorewrite with cpodb. auto.
Qed.

Global Add Parametric Morphism n k d : (get_nth k d)
       with signature @Oeq (nprod n) ==> @Oeq D as get_nth_compat_morph.
Proof.
  exact (get_nth_Oeq_compat n k d).
Qed.

Lemma get_nth_tl :
  forall {n} (np : nprod (S n)) k d,
    get_nth (S k) d np = get_nth k d (nprod_tl np).
Proof.
  induction k; auto.
Qed.

(** independence wrt. the default value *)
Lemma get_nth_indep :
  forall n (np : nprod n) k d d',
    k < n ->
    get_nth k d np = get_nth k d' np.
Proof.
  induction n; intros * Hk.
  - inversion Hk.
  - destruct k; auto; simpl.
    rewrite fcont_comp_simpl, IHn with (d' := d'); auto with arith.
Qed.

(** condition d'égalité pour les nprod *)
Lemma nprod_eq :
  forall n (np1 np2 : nprod (S n)),
    (forall k d, k < (S n) -> get_nth k d np1 == get_nth k d np2) ->
    np1 == np2.
Proof.
  induction n; simpl; intros * Heq.
  - apply (Heq O np1); auto.
  - destruct np1 as [d1 np1], np2 as [d2 np2].
    apply Dprod_eq_pair.
    + apply (Heq O d1); lia.
    + apply IHn; intros.
      rewrite (Heq (S k) d); auto; lia.
Qed.

Lemma nprod_app_nth1 :
  forall m n (mp : nprod m) (np : nprod n) k d,
    k < m ->
    get_nth k d (nprod_app mp np) = get_nth k d mp.
Proof.
  induction m; intros * Hk.
  - inversion Hk.
  - destruct k; simpl.
    + now unshelve setoid_rewrite nprod_hd_app.
    + autorewrite with cpodb.
      rewrite <- (IHm n _ np); auto with arith.
      destruct m; simpl; auto; lia.
Qed.

Lemma nprod_app_nth2 :
  forall m n (mp : nprod m) (np : nprod n) k d,
    k >= m ->
    get_nth k d (nprod_app mp np) = get_nth (k-m) d np.
Proof.
  induction m; intros * Hk.
  - simpl in *. autorewrite with cpodb; repeat f_equal; auto with arith.
  - destruct k; simpl.
    + lia.
    + destruct m, n; auto with arith.
      * destruct k; simpl; now autorewrite with cpodb.
      * rewrite <- (IHm _ (nprod_tl mp)); auto with arith.
      * rewrite <- (IHm _ (nprod_tl mp)); auto with arith.
      * rewrite <- (IHm _ (nprod_tl mp)); auto with arith.
Qed.

Lemma nprod_app_Oeq_compat :
  forall {n p} (p1 p2 : nprod n) (p3 p4 : nprod p),
    p1 == p2 ->
    p3 == p4 ->
    nprod_app p1 p3 == nprod_app p2 p4.
Proof.
  induction n; auto.
Qed.

Fixpoint nprod_const n : D -C-> nprod n :=
  match n with
  | O => ID _
  | S n => (nprod_cons @2_ ID _) (nprod_const n)
  end.

Lemma get_nth_const :
  forall c n k d,
    k < n ->
    get_nth k d (nprod_const n c) = c.
Proof.
  induction n; intros * Hk.
  - inversion Hk.
  - destruct k; simpl.
    + now setoid_rewrite nprod_hd_cons.
    + destruct n; [|apply IHn]; lia.
Qed.

Lemma get_nth_err :
  forall k d n (np : nprod n),
    (n <= k)%nat ->
    get_nth k d np = d.
Proof.
  induction k; simpl; intros * Hn.
  - inversion Hn; subst. now simpl.
  - destruct n; cbn; auto.
    setoid_rewrite <- get_nth_tl.
    apply IHk; auto with arith.
Qed.


(** A Forall predicate for n-uplets  *)
Section Forall_Nprod.

Variable P : D -> Prop.

Definition forall_nprod {n} (np : nprod n) : Prop.
  induction n as [|[]]; simpl in *.
  - exact True.
  - exact (P np).
  - exact (P (fst np) /\ IHn (snd np)).
Defined.

Lemma forall_nprod_hd :
  forall {n} (np : nprod (S n)),
    forall_nprod np ->
    P (nprod_hd np).
Proof.
  intros * Hf.
  destruct n; auto.
  now inversion Hf.
Qed.

Lemma forall_nprod_tl :
  forall {n} (np : nprod (S n)),
    forall_nprod np ->
    forall_nprod (nprod_tl np).
Proof.
  intros * Hf.
  destruct n.
  - now simpl.
  - now inversion Hf.
Qed.

Lemma forall_nprod_inv :
  forall n (np : nprod (S n)),
    forall_nprod np ->
    P (nprod_hd np) /\ forall_nprod (nprod_tl np).
Proof.
  intros [|[]] ?; simpl; auto.
Qed.

Lemma hd_tl_forall :
  forall {n} (np : nprod (S n)),
    P (nprod_hd np) ->
    forall_nprod (nprod_tl np) ->
    forall_nprod np.
Proof.
  destruct n as [|[]]; intros * Hh Ht; now simpl in *.
Qed.

Lemma forall_nprod_cons :
  forall {n} d (np : nprod n),
    P d ->
    forall_nprod np ->
    forall_nprod (nprod_cons d np).
Proof.
  destruct n; simpl; auto.
Qed.

Lemma forall_nprod_cons_iff :
  forall {n} d (np : nprod n),
    forall_nprod (nprod_cons d np)
    <-> P d /\ forall_nprod np.
Proof.
  split; destruct n; cbn; tauto.
Qed.

Lemma k_forall_nprod :
  forall {n} (np : nprod n),
    (forall k d, k < n -> P (get_nth k d np)) ->
    forall_nprod np.
Proof.
  induction n; intros * Hk; auto; try now simpl.
  apply hd_tl_forall.
  - unshelve eapply (Hk O); auto with arith.
    destruct n; [| destruct np]; auto.
  - apply IHn; intros.
    apply (Hk (S k)); auto with arith.
Qed.

Lemma k_forall_nprod_def :
  forall {n} (np : nprod n) d,
    (forall k, k < n -> P (get_nth k d np)) ->
    forall_nprod np.
Proof.
  induction n; intros * Hk; try now simpl.
  apply hd_tl_forall.
  - apply (Hk O); auto with arith.
  - apply (IHn _ d); intros.
    apply (Hk (S k)); auto with arith.
Qed.

Lemma forall_nprod_k :
  forall {n} (np : nprod n),
    forall_nprod np ->
    (forall k d, k < n -> P (get_nth k d np)).
Proof.
  induction n; intros * Hf * Hk.
  inversion Hk.
  apply forall_nprod_hd in Hf as ?.
  apply forall_nprod_tl in Hf as ?.
  destruct k; auto.
  apply IHn; auto with arith.
Qed.

Lemma forall_nprod_k_def :
  forall {n} (np : nprod n) d,
    P d ->
    forall_nprod np ->
    (forall k, P (get_nth k d np)).
Proof.
  intros * Hp Hf k.
  destruct (Nat.lt_ge_cases k n).
  - apply forall_nprod_k; auto.
  - rewrite get_nth_err; auto.
Qed.

Lemma forall_nprod_k_iff :
  forall {n} (np : nprod n),
    forall_nprod np <-> (forall k d, k < n -> P (get_nth k d np)).
Proof.
  split; auto using forall_nprod_k, k_forall_nprod.
Qed.

Lemma forall_nprod_app :
  forall {n m} (np : nprod n) (mp : nprod m),
    forall_nprod np ->
    forall_nprod mp ->
    forall_nprod (nprod_app np mp).
Proof.
  intros * Hnp Hmp.
  eapply k_forall_nprod.
  intros * Hk.
  destruct (Nat.lt_ge_cases k n).
  - rewrite nprod_app_nth1; auto using forall_nprod_k.
  - rewrite nprod_app_nth2; auto.
    apply forall_nprod_k; auto; lia.
Qed.

Lemma app_forall_nprod :
  forall {n m} (np : nprod n) (mp : nprod m),
    forall_nprod (nprod_app np mp) ->
    forall_nprod np
    /\ forall_nprod mp.
Proof.
  setoid_rewrite forall_nprod_k_iff.
  intros * Hf; split; intros k d Hk.
  - specialize (Hf k d).
    rewrite nprod_app_nth1 in Hf; auto with arith.
  - specialize (Hf (n + k) d).
    rewrite nprod_app_nth2, Nat.add_comm,
      Nat.add_sub in Hf; auto with arith.
    apply Hf; lia.
Qed.

Lemma forall_app_nprod :
  forall {n m} (np : nprod n) (mp : nprod m),
    forall_nprod (nprod_app np mp) <->
      forall_nprod np
      /\ forall_nprod mp.
Proof.
  split; auto using app_forall_nprod.
  intros []; auto using forall_nprod_app.
Qed.

Lemma forall_nprod_const :
  forall {n} c,
    P c ->
    forall_nprod (nprod_const n c).
Proof.
  intros.
  apply k_forall_nprod; intros.
  now rewrite get_nth_const.
Qed.

Global Add Parametric Morphism n
  (P_compat:  Morphisms.Proper (@Oeq D ==> iff) P)
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
  forall (P Q : D -> Prop),
    (forall x, P x -> Q x) ->
    forall {n} (np : nprod n),
      forall_nprod P np ->
      forall_nprod Q np.
Proof.
  intros * PQ * Hf.
  induction n; auto.
  apply forall_nprod_hd in Hf as ?.
  apply forall_nprod_tl in Hf as ?.
  apply hd_tl_forall; auto.
Qed.

Lemma forall_nprod_and :
  forall (P Q : D -> Prop),
    forall {n} (np : nprod n),
    forall_nprod P np ->
    forall_nprod Q np ->
    forall_nprod (fun x => P x /\ Q x) np.
Proof.
  induction n; intros * Hp Hq; auto.
  apply forall_nprod_hd in Hp as ?, Hq as ?.
  apply forall_nprod_tl in Hp as ?, Hq as ?.
  apply hd_tl_forall; auto.
Qed.

Lemma and_forall_nprod :
  forall (P Q : D -> Prop),
  forall {n} (np : nprod n),
    forall_nprod (fun x => P x /\ Q x) np ->
    forall_nprod P np /\ forall_nprod Q np.
Proof.
  induction n; intros * Hpq; auto.
  apply forall_nprod_inv in Hpq as [[] Ht].
  destruct (IHn _ Ht).
  split; apply hd_tl_forall; eauto.
Qed.

Lemma forall_nprod_and_iff :
  forall (P Q : D -> Prop),
  forall {n} (np : nprod n),
    (forall_nprod P np /\ forall_nprod Q np)
    <-> forall_nprod (fun x => P x /\ Q x) np.
Proof.
  split; intros.
  - now apply forall_nprod_and.
  - now apply and_forall_nprod.
Qed.

(* TODO: pas sûr de bien comprendre tout ça... Et peut-être
   que c'est un peu faible avec eq ? *)
Global Instance :
  Proper (pointwise_relation D iff ==>
            forall_relation (fun n : nat => eq ==> iff)) forall_nprod.
Proof.
  intros P Q PQ ??? Heq; subst.
  split; intro Hf.
  { induction a as [|[]]; auto.
    - apply PQ; auto.
    - inversion_clear Hf; split.
      + apply PQ; auto.
      + apply IHa; auto. }
  { induction a as [|[]]; auto.
    - apply PQ; auto.
    - inversion_clear Hf; split.
      + apply PQ; auto.
      + apply IHa; auto. }
Qed.


(** From n-uplets, build lists of length n *)
Section List_of_nprod.

Import ListNotations.

Fixpoint list_of_nprod {n} : nprod n -> list D :=
  match n return nprod n -> _ with
  | 0 => fun _ => []
  | S n => fun np => nprod_hd np :: list_of_nprod (nprod_tl np)
  end.

Lemma list_of_nprod_length :
  forall {n} (np : nprod n),
    length (list_of_nprod np) = n.
Proof.
  induction n; simpl; auto.
Qed.

Lemma list_of_nprod_cons :
  forall {n} d (np : nprod n),
    list_of_nprod (nprod_cons d np) = d :: list_of_nprod np.
Proof.
  destruct n; auto.
Qed.

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
    nth k (list_of_nprod np) d = get_nth k d np.
Proof.
  induction n; destruct k; simpl; intros; auto.
  now rewrite IHn.
Qed.

Lemma list_of_nprod_nth_error :
  forall n (np : nprod n) k d x,
    nth_error (list_of_nprod np) k = Some x ->
    get_nth k d np = x.
Proof.
  intros * Hn.
  apply nth_error_nth with (d := d) in Hn as Hnt.
  now rewrite list_of_nprod_nth in Hnt.
Qed.

Lemma forall_nprod_Forall :
  forall P {n} (np : nprod n),
    forall_nprod P np ->
    Forall P (list_of_nprod np).
Proof.
  induction n; intros * Hf; simpl; auto.
  apply forall_nprod_hd in Hf as ?.
  apply forall_nprod_tl in Hf as ?.
  constructor; auto.
Qed.

Lemma Forall_forall_nprod :
  forall P {n} (np : nprod n),
    Forall P (list_of_nprod np) ->
    forall_nprod P np.
Proof.
  induction n; intros * Hf; try now simpl.
  inversion_clear Hf.
  apply hd_tl_forall; auto.
Qed.

Lemma nprod_forall_Forall :
  forall P {n} (np : nprod n),
    forall_nprod P np <-> Forall P (list_of_nprod np).
Proof.
  split; eauto using forall_nprod_Forall, Forall_forall_nprod.
Qed.

Lemma Forall2_list_of_nprod_inv :
  forall T (P : T -> D -> Prop) n (np : nprod (S n)) x l,
    Forall2 P (x :: l) (list_of_nprod np) <->
      P x (nprod_hd np) /\ Forall2 P l (list_of_nprod (nprod_tl np)).
Proof.
  destruct n; split; intros * Hf;
    inversion_clear Hf; constructor; auto.
Qed.

End List_of_nprod.

End Nprod.

Notation "A [ n ]" := (@nprod A n) (at level 100, only printing, format "A [ n ]").


(** ** Lifting functions over n-uplets *)
Section Lifting.

Context {D1 D2 D3 : cpo}.

Fixpoint lift (F : D1 -C-> D2) {n} : @nprod D1 n -C-> @nprod D2 n :=
  match n with
  | O => F
  | S n => (nprod_cons @2_ F @_ nprod_hd) (lift F @_ nprod_tl)
  end.

Lemma lift_hd :
  forall f n (np : nprod (S n)),
    nprod_hd (lift f np) = f (nprod_hd np).
Proof.
  destruct n; auto.
Qed.

Lemma lift_tl :
  forall f n (np : nprod (S n)),
    nprod_tl (lift f np) = lift f (nprod_tl np).
Proof.
  destruct n; auto.
Qed.

Lemma lift_cons :
  forall f n x (np : nprod n),
    lift f (nprod_cons x np) =
      nprod_cons (f x) (lift f np).
Proof.
  destruct n; auto.
Qed.

Lemma lift_bot :
  forall (f : D1 -C-> D2), f 0 == 0 -> forall n, lift f (0 : nprod n) == 0.
Proof.
  induction n; simpl; auto.
  autorewrite with cpodb.
  setoid_rewrite nprod_hd_bot.
  setoid_rewrite nprod_tl_bot.
  rewrite IHn, H.
  now setoid_rewrite nprod_cons_bot.
Qed.

Lemma lift_app :
  forall f n1 (np1 : nprod n1) n2 (np2 : nprod n2),
    lift f (nprod_app np1 np2) = nprod_app (lift f np1) (lift f np2).
Proof.
  induction n1 as [|[]]; intros; auto.
  - destruct n2; auto.
  - rewrite nprod_hd_tl, nprod_tl_app, (nprod_hd_app _ _ (lift f np1)).
    now rewrite lift_tl, <- IHn1.
Qed.

Lemma nth_lift :
  forall F n (np : nprod n) k d1 d2,
    k < n ->
    get_nth k d2 (lift F np) = F (get_nth k d1 np).
Proof.
  induction n as [|[]]; intros * Hk.
  - inversion Hk.
  - now destruct k; try lia.
  - destruct k; auto.
    rewrite 2 get_nth_tl, lift_tl.
    erewrite IHn; auto; lia.
Qed.

Lemma lift_ext :
  forall (f g : D1 -C-> D2) n (np : nprod n),
    (forall x, f x == g x) ->
    lift f np == lift g np.
Proof.
  induction n; intros * Heq; simpl; auto.
  autorewrite with cpodb.
  now rewrite Heq, IHn.
Qed.

Lemma forall_nprod_lift :
  forall (F : D1 -C-> D2),
  forall (P : D2 -> Prop),
  forall {n} (np : nprod n),
    forall_nprod (fun x => P (F x)) np <->
      forall_nprod P (lift F np).
Proof.
  split.
  - intros * Hf.
    induction n as [|[]]; auto.
    inversion Hf.
    constructor; auto.
    now apply IHn.
  - intros * Hf.
    induction n as [|[]]; auto.
    inversion Hf.
    constructor; auto.
    now apply IHn.
Qed.

Lemma lift_nprod_const :
  forall F c n,
    lift F (nprod_const n c) = nprod_const n (F c).
Proof.
  induction n; auto.
  simpl (nprod_const _ _).
  autorewrite with cpodb.
  now rewrite lift_cons, IHn.
Qed.

Definition llift {A} (F : D1 -C-> A -C-> D2) {n} :
  @nprod D1 n -C-> A -C-> @nprod D2 n.
  (* match n with *)
  (* | O => CTE _ _ *)
  (* | S n => *)
  (*     match n return nprod n -C-> D -C-> nprod n -> nprod (S n) -C-> D -C-> nprod (S n) with *)
  (*     | O => fun _ => F *)
  (*     | S _ => fun fn => curry ((PAIR _ _ @2_ *)
  (*                              ((F @2_ (FST _ _ @_ FST _ _)) (SND _ _))) *)
  (*                             ((fn @2_ (SND _ _ @_ FST _ _)) (SND _ _))) *)
  (*     end (@llift _ F n) *)
  (*        end. *)
  induction n as [|[]].
  - apply F.
  - apply F.
  - apply curry.
    apply (fcont_comp2 (PAIR _ _)).
    exact ((F @2_ (FST _ _ @_ FST _ _)) (SND _ _)).
    exact ((IHn @2_ (SND _ _ @_ FST _ _)) (SND _ _)).
Defined.
Opaque llift.

Lemma llift_simpl :
  forall A F n d u U,
    @llift A F (S (S n)) (u, U) d = (F u d, @llift A F (S n) U d).
Proof.
  trivial.
Qed.

Lemma llift_hd :
  forall A F n d U,
    nprod_hd (@llift A F (S n) U d) = F (nprod_hd U) d.
Proof.
  destruct n; auto.
Qed.

Lemma llift_tl :
  forall A F n d U,
    nprod_tl (@llift A F (S n) U d) = llift F (nprod_tl U) d.
Proof.
  destruct n; auto.
Qed.

Lemma llift_nth :
  forall A (F : D1 -C-> A -C-> D2) a,
  forall {n} (np : nprod n) k d1 d2,
    k < n ->
    get_nth k d2 (llift F np a) = F (get_nth k d1 np) a.
Proof.
  induction n; intros * Hk.
  - inversion Hk.
  - destruct k; simpl.
    + now setoid_rewrite llift_hd.
    + autorewrite with cpodb.
      setoid_rewrite llift_tl; auto with arith.
Qed.

Definition llift_env {A I} (F : A -C-> Dprodi (fun _ : I => D1) -C-> D2) {n} :
  A -C-> Dprodi (fun _ : I => @nprod D1 n) -C-> @nprod D2 n.
  induction n as [|[]].
  - apply F.
  - apply F.
  - apply curry.
    apply (fcont_comp2 (PAIR _ _)).
    + exact ((F @2_ FST _ _) (DMAPi (fun _ => FST _ _) @_ SND _ _)).
    + exact ((IHn @2_ FST _ _) (DMAPi (fun _ => SND _ _) @_ SND _ _)).
Defined.

Definition lift2
  (F : D1 -C-> D2 -C-> D3) {n} :
  @nprod D1 n -C-> @nprod D2 n -C-> @nprod D3 n.
  induction n as [|[]].
  - exact F.
  - exact F.
  - apply curry.
    apply (fcont_comp2 (PAIR _ _)).
    exact ((F @2_ (FST _ _ @_ FST _ _ )) (FST _ _ @_ SND _ _ )).
    exact ((IHn @2_ (SND _ _ @_ FST _ _ )) (SND _ _ @_ SND _ _ )).
Defined.

Lemma lift2_hd :
  forall F n (U V : nprod (S n)),
    nprod_hd (lift2 F U V) = F (nprod_hd U) (nprod_hd V).
Proof.
  destruct n; auto.
Qed.

Lemma lift2_tl :
  forall F n (U V : nprod (S n)),
    nprod_tl (lift2 F U V) = lift2 F (nprod_tl U) (nprod_tl V).
Proof.
  destruct n; auto.
Qed.

Lemma lift2_simpl :
  forall F n u U v V,
    @lift2 F (S (S n)) (u, U) (v, V) = (F u v, @lift2 F (S n) U V).
Proof.
  trivial.
Qed.

Lemma lift2_nth :
  forall (F : D1 -C-> D2 -C-> D3) {n} (np np' : nprod n) k d1 d2 d3,
    k < n ->
    get_nth k d3 (lift2 F np np') = F (get_nth k d1 np) (get_nth k d2 np').
Proof.
  induction n as [|[]]; intros; auto; try lia.
  - destruct k; simpl; auto; lia.
  - destruct np, np'.
    rewrite lift2_simpl.
    destruct k; auto.
    erewrite 3 get_nth_tl, <- IHn; auto with arith.
Qed.

Lemma forall_nprod_lift2 :
  forall (F : D1 -C-> D2 -C-> D3),
  forall (P1 : D1 -> Prop)
    (P2 : D2 -> Prop)
    (P3 : D3 -> Prop),
    (forall x y, P1 x -> P2 y -> P3 (F x y)) ->
    forall {n} (np np' : nprod n),
      forall_nprod P1 np ->
      forall_nprod P2 np' ->
      forall_nprod P3 (lift2 F np np').
Proof.
  intros f P1 P2 P3 Hf.
  induction n as [|[]]; intros * H1 H2; auto.
  - cbn in *; intuition.
  - destruct np, np', H1, H2.
    rewrite lift2_simpl.
    constructor.
    apply Hf; auto.
    apply IHn; auto.
Qed.

Lemma forall_nprod_llift :
  forall A (F : D1 -C-> A -C-> D2) d,
  forall (P : D2 -> Prop)
    (Q : D1 -> Prop),
    (forall x, Q x -> P (F x d)) ->
    forall {n} (np : nprod n),
      forall_nprod Q np ->
      forall_nprod P (llift F np d).
Proof.
  intros A F d ?? Hf.
  induction n as [|[]]; intros * H; auto.
  - cbn in *; intuition.
  - destruct np, H.
    rewrite llift_simpl.
    constructor.
    + simpl in *; auto.
    + apply IHn; auto.
Qed.

(* pas envie d'importer tout Common pour ça... *)
Ltac inv H := inversion H; clear H; subst.
Ltac simpl_Forall :=
  repeat
    (match goal with
     | H: Forall2 _ _ (_ :: _) |- _ => inv H
     end; subst).


Lemma Forall2_lift2 :
  forall A (F : D1 -C-> D2 -C-> D3)
    (P : A -> D1 -> Prop)
    (Q : A -> D2 -> Prop)
    (R : A -> D3 -> Prop),
    (forall a x y, P a x -> Q a y -> R a (F x y)) ->
    forall {n} (l1 l2 : nprod n) l,
      Forall2 P l (list_of_nprod l1) ->
      Forall2 Q l (list_of_nprod l2) ->
      Forall2 R l (list_of_nprod (lift2 F l1 l2)).
Proof.
  intros * PQR.
  induction n; intros * H1 H2.
  - simpl; inversion H1; auto.
  - inv H1. inv H2.
    constructor.
    + rewrite lift2_hd; auto.
    + rewrite lift2_tl; auto.
Qed.

Lemma Forall2_llift :
  forall A B b (F : D1 -C-> B -C-> D2)
    (P : A -> D1 -> Prop)
    (Q : A -> D2 -> Prop),
    (forall a x, P a x -> Q a (F x b)) ->
    forall {n} (l1 : nprod n) (l : list A),
      Forall2 P l (list_of_nprod l1) ->
      Forall2 Q l (list_of_nprod (llift F l1 b)).
Proof.
  intros * PQ.
  induction n; intros * Hf.
  - simpl; inversion Hf; auto.
  - inv Hf; constructor.
    + rewrite llift_hd; auto.
    + rewrite llift_tl; auto.
Qed.

Lemma Forall_llift :
  forall A a (F : D1 -C-> A -C-> D2)
    (P : D1 -> Prop)
    (Q : D2 -> Prop),
    (forall x, P x -> Q (F x a)) ->
    forall {n} (np : nprod n),
      Forall P (list_of_nprod np) ->
      Forall Q (list_of_nprod (llift F np a)).
Proof.
  intros * PQ.
  induction n; intros * Hp; constructor; inv Hp.
  - rewrite llift_hd; auto.
  - rewrite llift_tl; auto.
Qed.

Lemma lift_map :
  forall F n (np : nprod n),
    list_of_nprod (lift F np) = List.map F (list_of_nprod np).
Proof.
  induction n as [|[]]; intros; auto.
  simpl.
  now setoid_rewrite IHn.
Qed.

End Lifting.

Lemma lift_ID :
  forall D n (np : nprod n),
    lift (ID D) np = np.
Proof.
  induction n; simpl; intros; auto.
  autorewrite with cpodb.
  rewrite IHn.
  now setoid_rewrite <- (nprod_hd_tl np).
Qed.

Lemma lift_lift :
  forall D1 D2 D3 (F : D1 -C-> D2) (G : D2 -C-> D3) n (np : nprod n),
    lift G (lift F np) = lift (G @_ F) np.
Proof.
  induction n as [|[]]; intros; simpl; auto.
  autorewrite with cpodb.
  now setoid_rewrite <- IHn.
Qed.


(** ** A kind of List.fold_right for nprod *)
Section Nprod_Foldi.

  Context {I : Type}.
  Context {A B : cpo}.

  Definition nprod_Foldi : forall (l : list I),
      (I -O-> B -C-> A -C-> A) -C-> A -C-> @nprod B (length l) -C-> A.
    induction l as [| i l].
    - apply CTE, CTE.
    - apply curry, curry.
      refine ((ID _ @3_ _) _ _).
      + exact (fcont_ford_shift _ _ _ (ID _) i @_ (FST _ _ @_ FST _ _)).
      + exact (nprod_hd @_ SND _ _).
      + exact ((IHl @3_ FST _ _ @_ FST _ _) (SND _ _ @_ FST _ _) (nprod_tl @_ SND _ _)).
  Defined.

  Lemma Foldi_nil :
    forall F a np, nprod_Foldi [] F a np = a.
  Proof.
    trivial.
  Qed.

  Lemma Foldi_cons : forall i l f a np,
      nprod_Foldi (i :: l) f a np
      = f i (nprod_hd np) (nprod_Foldi l f a (nprod_tl np)).
  Proof.
    trivial.
  Qed.

  Lemma Foldi_fold_right : forall l f a np,
      nprod_Foldi l f a np = fold_right (fun '(i, x) a => f i x a) a (combine l (list_of_nprod np)).
  Proof.
    induction l; intros; auto.
    rewrite Foldi_cons; simpl.
    do 2 f_equal; eauto.
  Qed.

  Lemma forall_nprod_Foldi :
    forall (P : A -> Prop)
      (Q : B -> Prop)
      (l : list I) (d : A) (f : I -O-> B -C-> A -C-> A) np,
      (forall i d1 d2, P d1 -> Q d2 -> P (f i d2 d1)) ->
      P d ->
      forall_nprod Q np ->
      P (nprod_Foldi l f d np).
  Proof.
    induction l; intros * PQ pd Fn; auto.
    rewrite Foldi_cons.
    apply PQ.
    - apply IHl; eauto using forall_nprod_tl.
    - now apply forall_nprod_hd in Fn.
  Qed.

  (** A weak induction principle for nprod_Foldi *)
  Lemma Foldi_rec :
    forall (P : A -> Prop) (F : I -O-> B -C-> A -C-> A) d,
      P d ->
      (forall i d dd, P dd -> P (F i d dd)) ->
      forall l np,
        P (nprod_Foldi l F d np).
  Proof.
    clear.
    intros * Hd HF.
    induction l; intro np; auto.
    rewrite Foldi_cons.
    apply HF, IHl.
  Qed.

End Nprod_Foldi.


(** To characterize stream functions defined with [nprod_Foldi], it may be
    useful to speak independently about heads and tails of streams.
    Tails can be easily accessed with [lift (@REM _) np] while heads needs
    a [is_cons] predicate to be extracted. This is the purpose of [nprod_hds].
 *)
Section Nprod_hds.

  Context {A : Type}.

  Fixpoint nprod_hds {n} : forall (np : @nprod (DS A) n),
      forall_nprod (@is_cons _) np -> list A :=
    match n with
    | O => fun _ _ => []
    | S n => fun _ Inf => projT1 (uncons (forall_nprod_hd _ _ Inf))
                        :: nprod_hds _ (forall_nprod_tl _ _ Inf)
    end.

  Lemma hds_length :
    forall n (np : nprod n) npc,
      length (nprod_hds np npc) = n.
  Proof.
    induction n; simpl; auto.
  Qed.

  Lemma Forall_hds :
    forall (P : A -> Prop) (Q : DS A -> Prop),
      (forall x u U, x == cons u U -> Q x -> P u) ->
      forall n (np : nprod n) Icn,
        Forall Q (list_of_nprod np) ->
        Forall P (nprod_hds np Icn).
  Proof.
    intros * QP.
    induction n; intros * Hf; inversion_clear Hf; constructor; auto.
    destruct (uncons _) as (?&?& Hd); simpl.
    apply decomp_eqCon in Hd.
    eapply QP; eauto.
  Qed.

  Lemma Forall2_hds :
    forall I (P : I -> A -> Prop) (Q : I -> DS A -> Prop),
      (forall i x u U, x == cons u U -> Q i x -> P i u) ->
      forall (l : list I) (np : nprod (length l)) Icn,
      Forall2 Q l (list_of_nprod np) ->
      Forall2 P l (nprod_hds np Icn).
  Proof.
    intros * QP.
    induction l; intros * Hf; inversion_clear Hf; constructor; auto.
    destruct (uncons _) as (?&?& Hd); simpl.
    apply decomp_eqCon in Hd.
    eapply QP; eauto.
  Qed.

End Nprod_hds.


(** ** Matrix operations *)
Section Lift_nprod.

Context {D1 D2 : cpo}.

(** [lift_nprod F np] applies F to each row of the matrix to
   produce a vector of size m.

   F( x11  x12 ... x1n ) → F1
   F( x21  x22 ... x2n ) → F2
   F(  .
   F(  .
   F( xm1  xm2 ... xmn ) → Fm
*)
Definition lift_nprod {n m} :
  (@nprod D1 n -C-> D2) -C-> @nprod (@nprod D1 m) n -C-> @nprod D2 m.
  induction m.
  - apply ID.
  - refine (curry ((nprod_cons @2_ _) _)).
    + exact ((AP _ _ @2_ FST _ _) (lift nprod_hd @_ SND _ _)).
    + exact ((IHm @2_ FST _ _) (lift nprod_tl @_ SND _ _)).
Defined.

Lemma lift_nprod_simpl :
  forall n m F (np : @nprod (@nprod D1 (S m)) n),
    lift_nprod F np = nprod_cons
                        (F (lift nprod_hd np))
                        (lift_nprod F (lift nprod_tl np)).
Proof.
  trivial.
Qed.

Lemma hd_lift_nprod :
  forall n m F (np : @nprod (@nprod D1 (S m)) n),
    nprod_hd (lift_nprod F np) = F (lift nprod_hd np).
Proof.
  intros.
  destruct m; auto.
Qed.

Lemma tl_lift_nprod :
  forall n m F (np : @nprod (@nprod D1 (S m)) n),
    nprod_tl (lift_nprod F np) = lift_nprod F (lift nprod_tl np).
Proof.
  intros.
  destruct m; auto.
Qed.

Lemma lift_nprod_nth :
  forall d1 d2 n F m k (np : @nprod (@nprod D1 m) n),
    k < m ->
    get_nth k d2 (lift_nprod F np) = F (lift (get_nth k d1) np).
Proof.
  induction m as [|[|m]]; intros * Hk; try lia.
  - destruct k; try lia; now cbn.
  - rewrite lift_nprod_simpl.
    destruct k.
    + now setoid_rewrite nprod_hd_cons.
    + setoid_rewrite IHm; auto with arith.
      now rewrite lift_lift.
Qed.

(** If ∀ i, (Q xi1 ∧ Q xi2 ∧ ... ∧ Q xin) implies P (F (xi1, ... xin))
    and Q indeed holds for every element of the matrix, then P holds
    for the result of [lift_nprod] *)
Lemma forall_lift_nprod :
  forall n (F : @nprod D1 n -C-> D2),
  forall (P : D2 -> Prop) (Q : D1 -> Prop),
    (forall x, forall_nprod Q x -> P (F x)) ->
    forall m np,
      forall_nprod (forall_nprod Q) np ->
      @forall_nprod _ P m (lift_nprod F np).
Proof.
  intros * QP.
  induction m; intros * Hq.
  - now simpl.
  - rewrite lift_nprod_simpl.
    apply forall_nprod_cons.
    + eapply QP, forall_nprod_lift, forall_nprod_impl; eauto.
      now apply forall_nprod_hd.
    + eapply IHm, forall_nprod_lift, forall_nprod_impl; eauto.
      now apply forall_nprod_tl.
Qed.

(** If every column of the matrix satisfy the property (Forall2 P l)
    then for all entries of l, P holds with every element in the corresponding
    row of the matrix. Typically, l is a list of type annotations. *)
Lemma Forall2_lift_nprod :
  forall n (F : @nprod D1 n -C-> D2),
  forall A (P : A -> D1 -> Prop) (Q : A -> D2 -> Prop),
    (forall a x, forall_nprod (P a) x -> Q a (F x)) ->
    forall (l : list A) m (np : @nprod (@nprod D1 m) n),
      m = length l ->
      Forall (fun ss => Forall2 P l (list_of_nprod ss)) (list_of_nprod np) ->
      Forall2 Q l (list_of_nprod (lift_nprod F np)).
Proof.
  intros * PQ.
  induction l; intros * ? Hf; subst; constructor.
  - rewrite hd_lift_nprod.
    apply PQ, forall_nprod_lift, Forall_forall_nprod.
    eapply Forall_impl in Hf; eauto.
    intros * HH.
    now inversion_clear HH.
  - rewrite tl_lift_nprod.
    apply IHl; auto.
    rewrite lift_map.
    eapply Forall_map, Forall_impl; eauto.
    intros * HH.
    now inversion_clear HH.
Qed.

(** If (Forall2 Q l) holds for every row of the matrix
    and implies P (F row) then P holds for the resulting vector. *)
Lemma Forall_lift_nprod :
  forall A (l : list A),
  forall (F : @nprod D1 (length l) -C-> D2),
  forall (P : D2 -> Prop) (Q : A -> D1 -> Prop),
    (forall (np : nprod (length l)),
        Forall2 Q l (list_of_nprod np) -> P (F np)) ->
    forall m (np : @nprod (@nprod D1 m) (length l)),
      Forall2 (fun e ss => forall_nprod (Q e) ss) l (list_of_nprod np) ->
      Forall P (list_of_nprod (lift_nprod F np)).
Proof.
  intros * QP.
  induction m; intros * Hf.
  now constructor.
  apply forall_nprod_Forall, hd_tl_forall.
  - rewrite hd_lift_nprod.
    apply QP.
    rewrite lift_map.
    apply Forall2_map_2.
    eapply Forall2_impl_In in Hf; eauto.
    now intros * _ _ HH%forall_nprod_hd.
  - rewrite tl_lift_nprod.
    apply Forall_forall_nprod, IHm.
    rewrite lift_map.
    apply Forall2_map_2.
    eapply Forall2_impl_In in Hf; eauto.
    now intros * _ _ HH%forall_nprod_tl.
Qed.

End Lift_nprod.

Lemma lift_lift_nprod :
  forall D1 D2 D3,
  forall (F : D2 -C-> D3) n m G np,
    lift F (@lift_nprod D1 D2 n m G np)
    = lift_nprod (F @_ G) np.
Proof.
  induction m; intros; auto.
  now rewrite 2 lift_nprod_simpl, <- IHm, lift_cons.
Qed.
