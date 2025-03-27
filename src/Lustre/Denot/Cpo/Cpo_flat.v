Require Export Cpo_def.
Require Export Arith.
Require Export ZArith.
Set Implicit Arguments.

(** * Cpo_flat.v : Flat cpo over a type D *)

Section Flat_cpo.
Variable D : Type.

(** ** Definition *)

CoInductive Dflat : Type := Eps : Dflat -> Dflat | Val : D -> Dflat.

Lemma DF_inv : forall d, d = match d with Eps x => Eps x | Val d => Val d end.
destruct d; auto.
Qed.
Hint Resolve DF_inv : core.

(** ** Removing Eps steps *)

Definition pred d : Dflat := match d with Eps x => x | Val _ => d end.

Fixpoint pred_nth (d:Dflat) (n:nat) {struct n} : Dflat :=
    match n with 0 => d
              |S m => match d with Eps x => pred_nth x m
                                 | Val _ => d
                      end
    end.

Lemma pred_nth_val : forall x n, pred_nth (Val x) n = Val x.
destruct n; simpl; trivial.
Qed.
Hint Resolve pred_nth_val : core.

Lemma pred_nth_Sn_acc : forall n d, pred_nth d (S n) = pred_nth (pred d) n.
destruct d; simpl; auto.
Qed.

Lemma pred_nth_Sn : forall n d, pred_nth d (S n) = pred (pred_nth d n).
induction n; intros; auto.
destruct d.
exact (IHn d).
rewrite pred_nth_val; rewrite pred_nth_val; simpl; trivial.
Qed.

(** ** Order *)
CoInductive DFle : Dflat -> Dflat -> Prop :=
                   DFleEps : forall x y,  DFle x y -> DFle (Eps x) (Eps y)
                |  DFleEpsVal : forall x d,  DFle x (Val d) -> DFle (Eps x) (Val d)
                |  DFleVal : forall d n y, pred_nth y n = Val d -> DFle (Val d) y.

Hint Constructors DFle : core.

Lemma DFle_rec : forall R : Dflat -> Dflat -> Prop,
   (forall x y, R (Eps x) (Eps y) -> R x y) ->
   (forall x d, R (Eps x) (Val d) -> R x (Val d)) ->
   (forall d y, R (Val d) y -> exists n, pred_nth y n = Val d)
   -> forall x y, R x y -> DFle x y.
intros R REps REpsVal RVal; cofix DFle_rec; destruct x; intros.
destruct y; intros.
apply DFleEps; apply DFle_rec; auto.
apply DFleEpsVal; apply DFle_rec; auto.
case (RVal d y H); intros n H1.
apply DFleVal with n; auto.
Qed.

(** *** Properties of the order *)
Lemma DFle_refl : forall x, DFle x x.
cofix DFle_refl; intros.
case x; intros.
apply DFleEps; apply DFle_refl.
apply DFleVal with 0%nat; auto.
Qed.
Hint Resolve DFle_refl : core.

Lemma DFleEps_right : forall x y,  DFle x y -> DFle x (Eps y).
cofix DFleEps_right; intros.
case H; intros.
apply DFleEps; apply DFleEps_right; trivial.
apply DFleEps;trivial.
apply DFleVal with (S n); auto.
Defined.
Hint Resolve DFleEps_right : core.

Lemma DFleEps_left : forall x y,  DFle x y -> DFle (Eps x) y.
cofix DFleEps_left; intros.
case H; intros.
apply DFleEps; apply DFleEps_left; trivial.
apply DFleEpsVal;apply DFleEpsVal;trivial.
destruct n; simpl in H0.
subst y0; apply DFleEpsVal; trivial.
destruct y0; simpl in H0.
apply DFleEps; apply DFleVal with n; auto.
apply DFleEpsVal;rewrite H0; apply DFle_refl.
Qed.

Hint Resolve DFleEps_left : core.

Lemma DFle_pred_left : forall x y, DFle x y -> DFle (pred x) y.
destruct x; destruct y; simpl; intros; trivial.
inversion H; auto.
inversion H; trivial.
Qed.

Lemma DFle_pred_right : forall x y, DFle x y -> DFle x (pred y).
destruct x; destruct y; simpl; intros; trivial.
inversion H; auto.
inversion H; trivial.
destruct n; simpl in H1.
discriminate H1.
apply DFleVal with n; auto.
Qed.

Hint Resolve DFle_pred_left DFle_pred_right : core.

Lemma DFle_pred : forall x y, DFle x y -> DFle (pred x) (pred y).
auto.
Qed.

Hint Resolve DFle_pred : core.

Lemma DFle_pred_nth_left : forall n x y, DFle x y -> DFle (pred_nth x n) y.
induction n; intros.
simpl; auto.
rewrite pred_nth_Sn; auto.
Qed.

Lemma DFle_pred_nth_right : forall n x y,
      DFle x y -> DFle x (pred_nth y n).
induction n; intros.
simpl; auto.
rewrite pred_nth_Sn; auto.
Qed.

Hint Resolve DFle_pred_nth_left DFle_pred_nth_right : core.

Lemma DFleVal_eq : forall x y, DFle (Val x) (Val y) -> x=y.
intros x y H; inversion H.
destruct n; simpl in H1; injection H1; auto.
Qed.
Hint Immediate DFleVal_eq : core.

Lemma DFleVal_sym : forall x y, DFle (Val x) y -> DFle y (Val x).
intros x y H; inversion H.
rewrite <- H1; apply DFle_pred_nth_right; auto.
Qed.


Lemma DFle_trans : forall x y z, DFle x y -> DFle y z -> DFle x z.
cofix DFle_trans; intros x y z H1; case H1; intros.
inversion H0.
apply DFleEps; apply DFle_trans with y0; assumption.
apply DFleEpsVal; apply DFle_trans with y0; assumption.
destruct z.
apply DFleEps; apply DFle_trans with (Val d); trivial.
exact (DFle_pred H0).
apply DFleEpsVal; rewrite <- (DFleVal_eq H0); trivial.
rewrite <- H; apply DFle_pred_nth_left; trivial.
Defined.

(** *** Declaration of the ordered set *)
Definition DF_ord : ord.
exists Dflat DFle; intros; auto.
apply DFle_trans with y; trivial.
Defined.

(** ** Definition of the cpo structure *)

Lemma eq_Eps : forall x:DF_ord, x == Eps x.
intros; apply Ole_antisym; repeat red; auto.
Qed.
Hint Resolve eq_Eps : core.

(** *** Bottom is given by an infinite chain of Eps *)
CoFixpoint DF_bot : DF_ord := Eps DF_bot.

Lemma DF_bot_eq : DF_bot = Eps DF_bot.
transitivity match DF_bot with Eps x => Eps x | Val d => Val d end; auto.
Qed.

Lemma DF_bot_least : forall x:DF_ord, DF_bot <= x.
cofix DF_bot_least; intro x.
rewrite DF_bot_eq; destruct x.
apply DFleEps; apply DF_bot_least.
apply DFleEpsVal; apply DF_bot_least.
Qed.

(** *** More properties of elements in the flat domain *)

Lemma DFle_eq : forall x (y:DF_ord), (Val x:DF_ord) <= y -> (Val x:DF_ord) == y.
intros; apply Ole_antisym; auto.
apply DFleVal_sym; trivial.
Qed.

Lemma DFle_Val_exists_pred :
      forall (x:DF_ord) d, (Val d:DF_ord) <= x -> exists k, pred_nth x k = Val d.
intros x d H; inversion H; eauto.
Qed.

Lemma Val_exists_pred_le :
      forall (x:DF_ord) d, (exists k, pred_nth x k = Val d) -> (Val d:DF_ord) <= x.
destruct 1; intros.
apply DFleVal with x0; trivial.
Qed.
Hint Immediate DFle_Val_exists_pred Val_exists_pred_le : core.

Lemma Val_exists_pred_eq :
      forall (x:DF_ord) d, (exists k, pred_nth x k = Val d) -> (Val d:DF_ord) == x.
intros; apply DFle_eq; auto.
Qed.

(** *** Construction of least upper bounds *)

Definition isEps (x:DF_ord) := match x with Eps _ => True | _ => False end.

Lemma isEps_Eps : forall x:DF_ord, isEps (Eps x).
repeat red; auto.
Qed.

Lemma not_isEpsVal : forall d, ~ (isEps (Val d)).
repeat red; auto.
Qed.
Hint Resolve isEps_Eps not_isEpsVal : core.

Lemma isEps_dec : forall (x:DF_ord) , {d:D|x=Val d}+{isEps x}.
destruct x; auto.
left; exists d; auto.
Defined.

Lemma fVal : forall (c:natO -m> DF_ord) (n:nat),
        {d:D | exists k, k<n /\ c k = Val d} + {forall k, k<n -> isEps (c k)}.
induction n.
right; intros; absurd (k<0); lia.
case IHn; intros.
case s; intros d H; left; exists d.
case H; intros k (H1,H2); exists k; auto with arith.
case (isEps_dec (c n)); intros.
case s; intros d H; left; exists d; exists n; auto with *.
right; intros.
assert (H0:(k<n \/ k=n)%nat); try lia.
case H0; intro; subst; auto with arith.
Defined.

(** *** Flat lubs *)

Definition cpred (c:natO -m> DF_ord) : natO-m>DF_ord.
exists (fun n => pred (c n)); red.
intros x y H; apply DFle_pred.
apply (fmonotonic c); auto.
Defined.

CoFixpoint DF_lubn (c:natO-m> DF_ord) (n:nat) : DF_ord :=
    match fVal c n with inleft (@exist _ _ d _) => Val d
                                |  inright _  => Eps (DF_lubn (cpred c) (S n))
    end.

Lemma DF_lubn_inv : forall (c:natO-m> DF_ord) (n:nat), DF_lubn c n =
     match fVal c n with inleft (@exist _ _ d _) => Val d
                                |  inright _  => Eps (DF_lubn (cpred c) (S n))
    end.
intros; rewrite (DF_inv (DF_lubn c n)).
simpl; case (fVal c n); trivial.
intro s; case s; trivial.
Qed.

Lemma chain_Val_eq : forall (c:natO-m> DF_ord) (n n':nat) d d',
    (Val d : DF_ord) <= c n -> (Val d' : DF_ord) <= c n'  -> d=d'.
intros; assert (c n <= c n' \/ c n' <= c n).
assert (n <= n'\/ n' < n)%nat.
apply Nat.le_gt_cases.
auto with *.
case H1; intro.
assert ((Val d : DF_ord) <= Val d'); auto.
apply Ole_trans with (c n); auto.
apply Ole_trans with (c n'); auto.
apply DFleVal_sym; auto.
assert ((Val d' : DF_ord) <= Val d); auto.
apply Ole_trans with (c n'); auto.
apply Ole_trans with (c n); auto.
apply DFleVal_sym; auto.
symmetry; auto.
Qed.


Lemma pred_lubn_Val : forall (d:D)(n k p:nat) (c:natO-m> DF_ord),
             (n <k+p)%nat -> pred_nth (c n) k = Val d
                                   -> pred_nth (DF_lubn c p) k = Val d.
induction k; intros.
(* Base case *)
rewrite (DF_lubn_inv c p); simpl.
simpl in H0.
case (fVal c p); intros.
case s; intros d' (k,(H1,H2)); auto.
rewrite (@chain_Val_eq c k n d' d); auto.
absurd (isEps (c n)); auto.
rewrite H0; auto.
(* Induction *)
rewrite (DF_lubn_inv c p).
case (fVal c p); intros.
destruct s; auto.
destruct e.
rewrite (@chain_Val_eq c n x0 d x); auto with *.
apply DFleVal with (S k); auto.
rewrite pred_nth_Sn_acc; simpl.
rewrite IHk; auto with arith.
replace (k + S p) with (S k + p)%nat; simpl; auto with arith.
rewrite <- H0; rewrite pred_nth_Sn_acc; trivial.
Qed.

Lemma pred_lubn_Val_inv  : forall (d:D)(k p:nat) (c:natO-m> DF_ord),
             pred_nth (DF_lubn c p) k = Val d
         -> exists n, (n <k+p)%nat /\ pred_nth (c n) k = Val d.
induction k; intros p c;rewrite (DF_lubn_inv c p).
simpl; intro H.
destruct (fVal c p).
destruct s.
injection H; intros; subst; auto.
discriminate H.
destruct (fVal c p).
destruct s.
case e; intros n (H1,H2);  exists n; auto with *.
simpl in H; rewrite H2; injection H; auto.
simpl pred_nth at 1; intros.
case (IHk (S p) (cpred c)); intros; auto.
exists x; auto with *.
rewrite pred_nth_Sn_acc; trivial.
Qed.

Definition DF_lub (c:natO-m> DF_ord) := DF_lubn c 1.

Lemma pred_lub_Val : forall (d:D)(n:nat) (c:natO-m> DF_ord),
             (Val d:DF_ord) <= (c n) -> (Val d:DF_ord) <= DF_lub c.
intros d n c H; case (DFle_Val_exists_pred H); intros k H1.
apply Val_exists_pred_le.
exists (n+k); unfold DF_lub; apply (@pred_lubn_Val d n (n+k) 1); auto with zarith.
pattern n at 2; elim n; intros; auto.
simpl plus;rewrite pred_nth_Sn; rewrite H0; auto.
Qed.

Lemma pred_lub_Val_inv : forall (d:D)(c:natO-m> DF_ord),
            (Val d:DF_ord) <= DF_lub c -> exists n,  (Val d:DF_ord) <= (c n).
intros d c H; case (DFle_Val_exists_pred H); intros k H1.
case (pred_lubn_Val_inv k 1 c H1); intros n (H2,H3).
exists n; apply DFleVal with k; trivial.
Qed.

Lemma DF_lub_upper : forall c:natO-m> DF_ord, forall n, c n <= DF_lub c.
intros; apply DFle_rec
  with (R:= fun x y:DF_ord=>x==c n /\ y==DF_lub c); auto with *.
apply Oeq_trans with (Eps x); auto.
apply Oeq_trans with (Eps y); auto.
apply Oeq_trans with (Eps x); auto.
apply (@DFle_Val_exists_pred y d).
apply Ole_trans with (DF_lub c); auto.
apply pred_lub_Val with n; auto.
Qed.

Lemma DF_lub_least : forall (c:natO-m> DF_ord) a,
                      (forall n, c n <= a) -> DF_lub c <= a.
intros; apply DFle_rec
  with (R:= fun x y:DF_ord=>x==DF_lub c /\ y == a); auto with *.
apply Oeq_trans with (Eps x); auto.
apply Oeq_trans with (Eps y); auto.
apply Oeq_trans with (Eps x); auto.
apply (@DFle_Val_exists_pred y d).
apply Ole_trans with a; auto.
case (@pred_lub_Val_inv  d c); auto.
intros; apply Ole_trans with (c x); auto.
Qed.

(** *** Declaration of the flat cpo *)

Definition DF : cpo.
exists DF_ord DF_bot DF_lub; intros.
apply DF_bot_least.
apply DF_lub_upper.
apply DF_lub_least; trivial.
Defined.

End Flat_cpo.

(** ** Trivial cpo with only the bottom element *)

Inductive DTriv : Type := DTbot : DTriv.

Definition DT_ord : ord.
exists DTriv (fun x y => True); auto.
Defined.

Definition DT : cpo.
exists DT_ord DTbot (fun f : natO-m>DT_ord => DTbot); red; intros; simpl; auto.
Defined.

Lemma DT_eqBot : forall x : DT, x = DTbot.
destruct x; auto.
Qed.
