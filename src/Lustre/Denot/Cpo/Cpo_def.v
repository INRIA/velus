(** * Ccpo.v: Specification and properties of a cpo *)

Require Export Setoid.
Require Export Arith.
Require Export Lia.
Set Implicit Arguments.
Unset Strict Implicit.
Open Scope nat_scope.


(** ** Ordered type *)
Record ord : Type := mk_ord
  { tord:>Type;
     Ole           : tord->tord->Prop;
     Ole_refl    : forall x :tord, Ole x x;
     Ole_trans : forall x y z:tord, Ole x y -> Ole y z -> Ole x z  }.

Global Hint Resolve Ole_refl Ole_trans : core.

Global Hint Extern 2  (@Ole ?X1 ?X2 ?X3 ) => simpl Ole : core.

Declare Scope O_scope.
Bind Scope O_scope with tord.
Delimit Scope O_scope with tord.

Infix "<=" := Ole : O_scope.
Open Scope O_scope.

(** *** Associated equality *)
Definition Oeq (O:ord) (x y : O) := x <= y /\ y <= x.

(** printing == %\ensuremath{\equiv}% #&#8801;# *)
Infix "==" := Oeq (at level 70) : O_scope.

Lemma Ole_refl_eq : forall  (O:ord) (x y:O), x=y -> x <= y.
intros O x y H; rewrite H; auto.
Qed.

Global Hint Resolve Ole_refl_eq : core.

Lemma Ole_antisym : forall (O:ord) (x y:O), x<=y -> y <=x -> x==y.
red; auto.
Qed.
Global Hint Immediate Ole_antisym : core.

Lemma Oeq_refl : forall (O:ord) (x:O), x == x.
red; auto.
Qed.
Global Hint Resolve Oeq_refl : core.

Lemma Oeq_refl_eq : forall (O:ord) (x y:O), x=y -> x == y.
intros O x y H; rewrite H; auto.
Qed.
Global Hint Resolve Oeq_refl_eq : core.

Lemma Oeq_sym : forall (O:ord) (x y:O), x == y -> y == x.
unfold Oeq; intuition.
Qed.

Lemma Oeq_le : forall (O:ord) (x y:O), x == y -> x <= y.
unfold Oeq; intuition.
Qed.

Lemma Oeq_le_sym : forall (O:ord) (x y:O), x == y -> y <= x.
unfold Oeq; intuition.
Qed.

Global Hint Resolve Oeq_le : core.
Global Hint Immediate Oeq_sym Oeq_le_sym : core.

Lemma Oeq_trans : forall (O:ord) (x y z:O), x == y -> y == z -> x == z.
unfold Oeq; split; apply Ole_trans with y; auto.
Qed.
Global Hint Resolve Oeq_trans : core.

(** *** Setoid relations *)

Add Parametric Relation (o:ord) : (tord o) (Oeq (O:=o))
       reflexivity proved by (Oeq_refl (O:=o))
       symmetry proved by (Oeq_sym (O:=o))
       transitivity proved by (Oeq_trans (O:=o)) as Oeq_Relation.

Add Parametric Relation (o:ord) : (tord o) (Ole (o:=o))
       reflexivity proved by (Ole_refl (o:=o))
       transitivity proved by (Ole_trans (o:=o)) as Ole_Relation.

(** printing ==> %\ensuremath\Longrightarrow% #&#8702;# *)
Add Parametric Morphism (o:ord) : (Ole (o:=o))
  with signature (Oeq (O:=o)) ==> (Oeq (O:=o)) ==> iff
  as Ole_eq_compat_iff.
Proof.
split; firstorder.
apply Ole_trans with x; trivial.
apply Ole_trans with x0; trivial.
apply Ole_trans with y; trivial.
apply Ole_trans with y0; trivial.
Qed.

Lemma Ole_eq_compat :
     forall (O : ord) (x1 x2 : O),
       x1 == x2 -> forall x3 x4 : O, x3 == x4 -> x1 <= x3 -> x2 <= x4.
firstorder; apply Ole_trans with x1; trivial.
apply Ole_trans with x3; trivial.
Qed.

Lemma Ole_eq_right : forall (O : ord) (x y z: O),
             x <= y -> y == z -> x <= z.
intros; apply Ole_eq_compat with x y; auto.
Qed.

Lemma Ole_eq_left : forall (O : ord) (x y z: O),
             x == y -> y <= z -> x <= z.
intros; apply Ole_eq_compat with y z; auto.
Qed.

(** *** Dual order *)

(** - Iord x y := y <= x  *)
Definition Iord (O:ord):ord.
exists O (fun x y : O => y <= x); intros; auto.
apply Ole_trans with y; auto.
Defined.

(** *** Order on functions *)

(** - ford f g := forall x, f x <= g x *)
Definition ford (A:Type) (O:ord) : ord.
exists (A->O) (fun f g:A->O => forall x, f x <= g x); intros; auto.
apply Ole_trans with (y x0); auto.
Defined.

(** printing -o> %\ensuremath{\stackrel{o}{\rightarrow}}% *)
Infix "-o>" := ford (right associativity, at level 30) : O_scope .

Lemma ford_le_elim : forall A (O:ord) (f g:A -o> O), f <= g ->forall n, f n <= g n.
auto.
Qed.
Global Hint Immediate ford_le_elim : core.

Lemma ford_le_intro : forall A (O:ord) (f g:A -o> O), (forall n, f n <= g n) -> f <= g.
auto.
Qed.
Global Hint Resolve ford_le_intro : core.

Lemma ford_eq_elim : forall A (O:ord) (f g:A -o> O), f == g ->forall n, f n == g n.
firstorder.
Qed.
Global Hint Immediate ford_eq_elim : core.

Lemma ford_eq_intro : forall A (O:ord) (f g:A -o> O), (forall n, f n == g n) -> f == g.
red; auto.
Qed.
Global Hint Resolve ford_eq_intro : core.

Global Hint Extern 2 (Ole (o:=ford ?X1 ?X2) ?X3 ?X4) => intro : core.

(** ** Monotonicity *)

(** *** Definition and properties *)

Definition monotonic (O1 O2:ord) (f : O1 -> O2) := forall x y, x <= y -> f x <= f y.
Global Hint Unfold monotonic : core.

Definition stable (O1 O2:ord) (f : O1 -> O2) := forall x y, x == y -> f x == f y.
Global Hint Unfold stable : core.

Lemma monotonic_stable : forall (O1 O2 : ord) (f:O1 -> O2),
             monotonic f -> stable f.
unfold monotonic, stable; firstorder.
Qed.
Global Hint Resolve monotonic_stable : core.

(** *** Type of monotonic functions *)

Record fmono (O1 O2:ord) : Type := mk_fmono
            {fmonot :> O1 -> O2; fmonotonic: monotonic fmonot}.
Global Hint Resolve fmonotonic : core.

(** - fmon O1 O2 (f g : fmono O1 O2) := forall x, f x <= g x *)
Definition fmon (O1 O2:ord) : ord.
exists (fmono O1 O2) (fun f g:fmono O1 O2 => forall x, f x <= g x); intros; auto.
apply Ole_trans with (y x0); auto.
Defined.

(** printing -m> %\ensuremath{\stackrel{m}{\rightarrow}}%*)
Infix "-m>" := fmon (at level 30, right associativity) : O_scope.

Lemma fmon_stable : forall (O1 O2:ord) (f:O1 -m> O2), stable f.
intros; apply monotonic_stable; auto.
Qed.
Global Hint Resolve fmon_stable : core.

Lemma fmon_le_elim : forall (O1 O2:ord) (f g:O1 -m> O2), f <= g -> forall n, f n <= g n.
auto.
Qed.
Global Hint Immediate fmon_le_elim : core.

Lemma fmon_le_intro : forall (O1 O2:ord) (f g:O1 -m> O2), (forall n, f n <= g n) -> f <= g.
auto.
Qed.
Global Hint Resolve fmon_le_intro : core.

Lemma fmon_eq_elim : forall (O1 O2:ord) (f g:O1 -m> O2), f == g ->forall n, f n == g n.
firstorder.
Qed.
Global Hint Immediate fmon_eq_elim : core.

Lemma fmon_eq_intro : forall (O1 O2:ord) (f g:O1 -m> O2), (forall n, f n == g n) -> f == g.
red; auto.
Qed.
Global Hint Resolve fmon_eq_intro : core.

Global Hint Extern 2 (Ole (o:=fmon ?X1 ?X2) ?X3 ?X4) => intro : core.

(** *** Monotonicity and dual order *)

(** - [lmon f] uses f as monotonic function over the dual order. *)
Definition Imon : forall O1 O2, (O1 -m> O2) -> Iord O1 -m> Iord O2.
intros O1 O2 f; exists (f: Iord O1 -> Iord O2); red; simpl; intros.
apply (fmonotonic f); auto.
Defined.

Definition Imon2 : forall O1 O2 O3, (O1 -m> O2 -m> O3) -> Iord O1 -m> Iord O2 -m> Iord O3.
intros O1 O2 O3 f; exists (fun (x:Iord O1) => Imon (f x)); red; simpl; intros.
apply (fmonotonic f); auto.
Defined.

(** *** Monotonic functions with 2 arguments *)
Definition le_compat2_mon : forall (O1 O2 O3:ord)(f:O1 -> O2 -> O3),
     (forall (x y:O1) (z t:O2), x<=y -> z <= t -> f x z <= f y t) -> (O1 -m> O2 -m> O3).
intros O1 O2 O3 f Hle; exists (fun (x:O1) => mk_fmono (fun z t => Hle x x z t (Ole_refl x))).
red; intros; intro a; simpl; auto.
Defined.

(** ** Sequences *)
(** *** Order on natural numbers *)

(** - natO n m = n <= m *)
Definition natO : ord.
  exists nat (fun n m : nat => (n <= m)%nat); intros; auto with arith.
    apply Nat.le_trans with y; auto.
Defined.

Definition fnatO_intro : forall (O:ord) (f:nat -> O), (forall n, f n <= f (S n)) -> natO -m> O.
intros; exists f; red; simpl; intros.
elim H0; intros; auto.
apply Ole_trans with (f m); trivial.
Defined.

Lemma fnatO_elim : forall (O:ord) (f:natO -m> O) (n:nat), f n <= f (S n).
intros; apply (fmonotonic f); auto.
Qed.
Global Hint Resolve fnatO_elim : core.


(** - (mseq_lift_left f n) k = f (n+k) *)
Definition mseq_lift_left : forall (O:ord) (f:natO -m> O) (n:nat), natO -m> O.
intros; exists (fun k => f (n+k)%nat); red; intros.
apply (fmonotonic f); auto with arith.
Defined.

Lemma mseq_lift_left_simpl : forall (O:ord) (f:natO -m> O) (n k:nat),
    mseq_lift_left f n  k = f (n+k)%nat.
trivial.
Qed.

Lemma mseq_lift_left_le_compat : forall (O:ord) (f g:natO -m> O) (n:nat),
             f <= g -> mseq_lift_left f n <= mseq_lift_left g n.
intros; intro; simpl; auto.
Qed.
Global Hint Resolve mseq_lift_left_le_compat : core.

Add Parametric Morphism  (o:ord) : (mseq_lift_left (O:=o))
 with signature (Oeq  (O:=natO -m> o)) ==> eq (A:=nat) ==> (Oeq (O:=natO -m> o))
as mseq_lift_left_eq_compat.
intros; apply Ole_antisym; auto.
Qed.
Global Hint Resolve mseq_lift_left_eq_compat : core.

(** - (mseq_lift_right f n) k = f (k+n) *)
Definition mseq_lift_right : forall (O:ord) (f:natO -m> O) (n:nat), natO -m> O.
intros; exists (fun k => f (k+n)%nat); red; intros.
apply (fmonotonic f); auto with arith.
Defined.

Lemma mseq_lift_right_simpl : forall (O:ord) (f:natO -m> O) (n k:nat),
    mseq_lift_right f n  k = f (k+n)%nat.
trivial.
Qed.


Lemma mseq_lift_right_le_compat : forall (O:ord) (f g:natO -m> O) (n:nat),
             f <= g -> mseq_lift_right f n <= mseq_lift_right g n.
intros; intro; simpl; auto.
Qed.
Global Hint Resolve mseq_lift_right_le_compat : core.

Add Parametric Morphism (o:ord) : (mseq_lift_right (O:=o))
   with signature Oeq (O:=natO -m> o) ==> eq (A:=nat) ==> Oeq (O:=natO -m> o)
as mseq_lift_right_eq_compat.
intros; apply Ole_antisym; auto.
Qed.

Lemma mseq_lift_right_left : forall (O:ord) (f:natO -m> O) n,
       mseq_lift_left f n  == mseq_lift_right f n.
intros; apply fmon_eq_intro; unfold mseq_lift_left,mseq_lift_right; simpl; intros.
replace (n0+n)%nat with (n+n0)%nat; auto with arith.
Qed.

(** *** Monotonicity and functions *)
(** -  (ford_app f x) n = f n x *)
Definition ford_app : forall (A:Type)(O1 O2:ord)(f:O1 -m> (A -o> O2))(x:A), O1 -m> O2.
intros; exists (fun n => f n x); intros.
intro n; intros.
assert (f n <= f y); auto.
apply (fmonotonic f); trivial.
Defined.

(** printing <o> %\ensuremath{\stackrel{o}{\diamond}}% *)
Infix "<o>" := ford_app (at level 30, no associativity) : O_scope.

Lemma ford_app_simpl : forall (A:Type)(O1 O2:ord)  (f : O1 -m> A -o> O2) (x:A)(y:O1),
            (f <o> x) y = f y x.
trivial.
Qed.

Lemma ford_app_le_compat : forall (A:Type)(O1 O2:ord) (f g:O1 -m> A -o> O2) (x:A),
             f <= g -> f <o> x  <= g <o> x.
intros; intro; simpl.
apply (H x0).
Qed.
Global Hint Resolve ford_app_le_compat : core.

Add Parametric Morphism (A:Type)(O1 O2:ord) : (ford_app (A:=A) (O1:=O1) (O2:=O2))
   with signature Oeq (O:=O1 -m> (A -o> O2)) ==> eq (A:=A) ==> Oeq (O:=O1 -m> O2)
as ford_app_eq_compat.
intros; apply Ole_antisym; auto.
Qed.

(** - ford_shift f x y == f y x *)
Definition ford_shift : forall (A:Type)(O1 O2:ord)(f:A -o> (O1 -m> O2)), O1 -m> (A -o> O2).
intros; exists (fun x y => f y x); intros.
intros n x H y.
apply (fmonotonic (f y)); trivial.
Defined.

Lemma ford_shift_le_compat : forall (A:Type)(O1 O2:ord) (f g: A -o> (O1 -m> O2)),
             f <= g -> ford_shift f  <= ford_shift g.
intros; intro; simpl; auto.
Qed.
Global Hint Resolve ford_shift_le_compat : core.

Add Parametric Morphism (A:Type)(O1 O2:ord) : (ford_shift (A:=A) (O1:=O1) (O2:=O2))
 with signature Oeq (O:=A -o> (O1 -m> O2)) ==> Oeq (O:=O1 -m> (A -o> O2))
as ford_shift_eq_compat.
intros; apply Ole_antisym; auto.
Qed.


(**  - (fmon_app f x) n = f n x *)

Definition fmon_app : forall (O1 O2 O3:ord)(f:O1 -m> O2 -m> O3)(x:O2), O1 -m> O3.
intros; exists (fun n => f n x); intros.
intro n; intros.
assert (f n <= f y); auto.
apply (fmonotonic f); trivial.
Defined.

(** printing <_> %\ensuremath{\leftrightarroweq}%*)
Infix "<_>" := fmon_app (at level 35, no associativity) : O_scope.

Lemma fmon_app_simpl : forall  (O1 O2 O3:ord)(f:O1 -m> O2 -m> O3)(x:O2)(y:O1),
      (f <_> x)  y = f y x.
trivial.
Qed.

Lemma fmon_app_le_compat : forall (O1 O2 O3:ord) (f g:O1 -m> (O2 -m> O3)) (x y:O2),
             f <= g -> x <= y -> f <_> x  <= g <_> y.
red; intros; simpl; intros; auto.
apply Ole_trans with (f x0 y); auto.
apply (fmonotonic (f x0)); auto.
Qed.
Global Hint Resolve fmon_app_le_compat : core.

Add Parametric Morphism (O1 O2 O3:ord) : (fmon_app (O1:=O1) (O2:=O2) (O3:=O3))
  with signature Oeq (O:=O1 -m> O2 -m> O3) ==> Oeq (O:=O2) ==> Oeq (O:=O1-m>O3)
as fmon_app_eq_compat.
intros; apply Ole_antisym; intros; auto.
Qed.

(** - fmon_id c = c *)
Definition fmon_id :  forall (O:ord), O -m> O.
intros; exists (fun (x:O)=>x).
intro n; auto.
Defined.

Lemma fmon_id_simpl : forall (O:ord) (x:O), fmon_id O x = x.
trivial.
Qed.

(**  - (fmon_cte c) n = c *)
Definition fmon_cte :  forall (O1 O2:ord)(c:O2), O1 -m> O2.
intros; exists (fun (x:O1)=>c).
intro n; auto.
Defined.

Lemma fmon_cte_simpl : forall  (O1 O2:ord)(c:O2)(c:O2) (x:O1), fmon_cte O1 c x = c.
trivial.
Qed.

Definition mseq_cte : forall O:ord, O -> natO -m> O := fmon_cte natO.

Lemma fmon_cte_le_compat : forall (O1 O2:ord) (c1 c2:O2),
             c1 <= c2 -> fmon_cte O1 c1 <= fmon_cte O1 c2.
intros; intro; auto.
Qed.

Add Parametric Morphism (O1 O2:ord) : (fmon_cte O1 (O2:=O2))
       with signature Oeq (O:=O2) ==>  Oeq (O:=O1 -m> O2)
as fmon_cte_eq_compat.
intros; apply Ole_antisym; auto.
Qed.

(** - (fmon_diag h) n = h n n *)
Definition fmon_diag : forall (O1 O2:ord)(h:O1 -m> (O1 -m> O2)), O1 -m> O2.
intros; exists (fun n => h n n).
red; intros.
apply Ole_trans with (h x y); auto.
apply (fmonotonic (h x)); auto.
assert (h x <= h y); auto.
apply (fmonotonic h); trivial.
Defined.

Lemma fmon_diag_le_compat :  forall (O1 O2:ord) (f g:O1 -m> (O1 -m> O2)),
             f <= g -> fmon_diag f <= fmon_diag g.
intros; intro; simpl; auto.
Qed.
Global Hint Resolve fmon_diag_le_compat : core.

Lemma fmon_diag_simpl : forall (O1 O2:ord) (f:O1 -m> (O1 -m> O2)) (x:O1),
             fmon_diag f x = f x x.
trivial.
Qed.

Add Parametric Morphism (O1 O2:ord) : (fmon_diag (O1:=O1) (O2:=O2))
    with signature Oeq (O:=O1 -m> (O1 -m> O2)) ==> Oeq (O:=O1 -m> O2)
as fmon_diag_eq_compat.
intros; apply Ole_antisym; auto.
Qed.

(** - (fmon_shift h) n m = h m n *)
Definition fmon_shift : forall (O1 O2 O3:ord)(h:O1 -m> O2 -m>  O3), O2 -m> O1 -m>  O3.
intros; exists (fun m => h <_> m).
intro n; simpl; intros.
apply (fmonotonic (h x)); trivial.
Defined.

Lemma fmon_shift_simpl : forall (O1 O2 O3:ord)(h:O1 -m> O2 -m>  O3) (x : O2) (y:O1),
      fmon_shift h x y = h y x.
trivial.
Qed.

Lemma fmon_shift_le_compat :  forall (O1 O2 O3:ord) (f g:O1 -m>  O2 -m>  O3),
             f <= g -> fmon_shift f <= fmon_shift g.
intros; intro; simpl; intros.
assert (f x0 <= g x0); auto.
Qed.
Global Hint Resolve fmon_shift_le_compat : core.

Add Parametric Morphism (O1 O2 O3:ord) : (fmon_shift (O1:=O1) (O2:=O2) (O3:=O3))
   with signature Oeq  (O:=O1 -m> O2 -m>  O3) ==> Oeq (O:=O2 -m> O1 -m>  O3)
as fmon_shift_eq_compat.
intros; apply Ole_antisym; auto.
Qed.

Lemma fmon_shift_shift_eq :  forall (O1 O2 O3:ord) (h : O1 -m> O2 -m>  O3),
             fmon_shift (fmon_shift h) == h.
intros; apply fmon_eq_intro; unfold fmon_shift; simpl; auto.
Qed.

(** - (f@g) x = f (g x) *)
Definition fmon_comp : forall O1 O2 O3:ord, (O2 -m> O3) -> (O1 -m> O2) -> O1 -m> O3.
intros O1 O2 O3 f g; exists (fun n => f (g n)); red; intros.
apply (fmonotonic f).
apply (fmonotonic g); auto.
Defined.

(** printing @ %\ensuremath{\stackrel{m}{\circ}}% *)
Infix "@" := fmon_comp (at level 35) : O_scope.

Lemma fmon_comp_simpl : forall (O1 O2 O3:ord) (f :O2 -m> O3) (g:O1 -m> O2) (x:O1),
            (f @ g) x = f (g x).
trivial.
Qed.

(** - (f@2 g) h x = f (g x) (h x) *)
Definition fmon_comp2 :
    forall O1 O2 O3 O4:ord, (O2 -m> O3 -m> O4) -> (O1 -m> O2) -> (O1 -m> O3) -> O1-m>O4.
intros O1 O2 O3 O4 f g h; exists (fun n => f (g n) (h n)); red; intros.
apply Ole_trans with (f (g x) (h y)); auto.
apply (fmonotonic (f (g x))).
apply (fmonotonic h); auto.
apply (fmonotonic f); auto.
apply (fmonotonic g); auto.
Defined.

(** printing @2 %\ensuremath{\stackrel{m}{\circ_2}}% *)
Infix "@2" := fmon_comp2 (at level 70) : O_scope.

Lemma fmon_comp2_simpl :
    forall (O1 O2 O3 O4:ord) (f:O2 -m> O3 -m> O4) (g:O1 -m> O2) (h:O1 -m> O3) (x:O1),
            (f @2 g) h x = f (g x) (h x).
trivial.
Qed.

Add Parametric Morphism (O1 O2 O3:ord) : (fmon_comp (O1:=O1) (O2:=O2) (O3:=O3))
with signature Ole (o:=O2 -m> O3) ++> Ole (o:=O1 -m> O2) ++> Ole (o:=O1 -m> O3)
as fmon_comp_le_compat_morph.
red; intros f1 f2 H g1 g2 H1 x; simpl.
apply Ole_trans with (f2 (g1 x)); auto.
apply (fmonotonic f2); auto.
Qed.

Lemma fmon_comp_le_compat :
      forall (O1 O2 O3:ord) (f1 f2: O2 -m> O3) (g1 g2:O1 -m> O2),
                 f1 <= f2 -> g1<= g2 -> f1 @ g1 <= f2 @ g2.
intros; exact (fmon_comp_le_compat_morph H H0).
Qed.
Global Hint Immediate fmon_comp_le_compat : core.

Add Parametric Morphism (O1 O2 O3:ord) : (fmon_comp (O1:=O1) (O2:=O2) (O3:=O3))
with signature Oeq (O:=O2 -m> O3) ==> Oeq  (O:=O1 -m> O2) ==> Oeq (O:=O1 -m> O3)
as fmon_comp_eq_compat.
intros; apply Ole_antisym; apply fmon_comp_le_compat; auto.
Qed.
Global Hint Immediate fmon_comp_eq_compat : core.


Lemma fmon_comp_monotonic2 :
      forall (O1 O2 O3:ord) (f: O2 -m> O3) (g1 g2:O1 -m> O2),
               g1<= g2 -> f @ g1 <= f @ g2.
auto.
Qed.
Global Hint Resolve fmon_comp_monotonic2 : core.

Lemma fmon_comp_monotonic1 :
      forall (O1 O2 O3:ord) (f1 f2: O2 -m> O3) (g:O1 -m> O2),
               f1<= f2 -> f1 @ g <= f2 @ g.
auto.
Qed.
Global Hint Resolve fmon_comp_monotonic1 : core.

Definition fcomp : forall O1 O2 O3:ord,  (O2 -m> O3) -m> (O1 -m> O2) -m> (O1 -m> O3).
   intros; exists (fun f : O2 -m> O3 =>
                  mk_fmono (fmonot:=fun g : O1 -m> O2 => fmon_comp f g)
                                    (fmon_comp_monotonic2 f)).
red; intros; simpl; intros.
apply H.
Defined.

Lemma fcomp_simpl : forall (O1 O2 O3:ord) (f:O2 -m> O3) (g:O1 -m> O2),
             fcomp O1 O2 O3 f g = f @ g.
trivial.
Qed.

Definition fcomp2  : forall O1 O2 O3 O4:ord,
        (O3 -m> O4) -m> (O1 -m> O2-m>O3) -m> (O1 -m> O2 -m> O4).
intros; exists (fun f : O3 -m> O4 =>
                      fcomp O1 (O2-m> O3) (O2-m>O4) (fcomp O2 O3 O4 f)).
red; intros; simpl; intros.
apply H.
Defined.

Lemma fcomp2_simpl : forall (O1 O2 O3 O4:ord) (f:O3 -m> O4) (g:O1 -m> O2-m>O3) (x:O1)(y:O2),
             fcomp2 O1 O2 O3 O4 f g x y = f (g x y).
trivial.
Qed.

Lemma fmon_le_compat : forall (O1 O2:ord) (f: O1 -m> O2) (x y:O1), x<=y -> f x <= f y.
intros; apply (fmonotonic f); auto.
Qed.
Global Hint Resolve fmon_le_compat : core.

Lemma fmon_le_compat2 : forall (O1 O2 O3:ord) (f: O1 -m> O2 -m> O3) (x y:O1) (z t:O2),
             x<=y -> z <=t -> f x z <= f y t.
intros; apply Ole_trans with (f x t).
apply (fmonotonic (f x)); auto.
apply (fmonotonic f); auto.
Qed.
Global Hint Resolve fmon_le_compat2 : core.

Lemma fmon_cte_comp : forall (O1 O2 O3:ord)(c:O3)(f:O1-m>O2),
              fmon_cte O2 c @ f == fmon_cte O1 c.
intros; apply fmon_eq_intro; intro x; auto.
Qed.

(** ** Basic operators of omega-cpos *)
(** - Constant : $0$
     - lub : limit of monotonic sequences
*)



(** *** Definition of cpos *)
Record cpo : Type := mk_cpo
  {tcpo:>ord; D0 : tcpo; lub: (natO -m> tcpo) -> tcpo;
   Dbot : forall x:tcpo, D0 <= x;
   le_lub : forall (f : natO -m> tcpo) (n:nat), f n <= lub f;
   lub_le : forall (f : natO -m> tcpo) (x:tcpo), (forall n, f n <= x) -> lub f <= x}.

Arguments D0 {c}.
Notation "0" := D0 : O_scope.

Global Hint Resolve Dbot le_lub lub_le : core.

(** *** Least upper bounds *)

Add Parametric Morphism (c:cpo) :  (lub (c:=c))
   with signature Ole (o:=natO -m> c) ++> Ole (o:=c)
as lub_le_compat_morph.
intros f g H; apply lub_le; intros.
apply Ole_trans with (g n); auto.
Qed.
Global Hint Resolve lub_le_compat_morph : core.

Lemma lub_le_compat : forall (D:cpo) (f g:natO -m> D), f <= g -> lub f <= lub g.
intros; apply lub_le; intros.
apply Ole_trans with (g n); auto.
Qed.
Global Hint Resolve lub_le_compat : core.

Definition Lub : forall (D:cpo), (natO -m> D) -m> D.
intro D; exists (fun (f :natO-m>D) => lub f); red; auto.
Defined.

Add Parametric Morphism (c:cpo) : (lub (c:=c))
with signature Oeq (O:=natO -m> c) ==> Oeq (O:=c)
as lub_eq_compat.
intros; apply Ole_antisym; auto.
Qed.
Global Hint Resolve lub_eq_compat : core.

Lemma lub_cte : forall (D:cpo) (c:D), lub (fmon_cte natO c) == c.
intros; apply Ole_antisym; auto.
apply le_lub with (f:=fmon_cte natO c) (n:=O); auto.
Qed.

Global Hint Resolve lub_cte : core.

Lemma lub_lift_right : forall (D:cpo) (f:natO -m> D) n, lub f == lub (mseq_lift_right f n).
intros; apply Ole_antisym; auto.
apply lub_le_compat; intro.
unfold mseq_lift_right; simpl.
apply (fmonotonic f); auto with arith.
Qed.
Global Hint Resolve lub_lift_right : core.

Lemma lub_lift_left : forall (D:cpo) (f:natO -m> D) n, lub f == lub (mseq_lift_left f n).
intros; apply Ole_antisym; auto.
apply lub_le_compat; intro.
unfold mseq_lift_left; simpl.
apply (fmonotonic f); auto with arith.
Qed.
Global Hint Resolve lub_lift_left : core.

Lemma lub_le_lift : forall (D:cpo) (f g:natO -m> D) (n:natO),
        (forall k, n <= k -> f k <= g k) -> lub f <= lub g.
intros; apply lub_le; intros.
apply Ole_trans with (f (n+n0)).
apply (fmonotonic f); simpl; auto with arith.
apply Ole_trans with (g (n+n0)); auto.
apply H; simpl; auto with arith.
Qed.

Lemma lub_eq_lift : forall (D:cpo) (f g:natO -m> D) (n:natO),
        (forall k, n <= k -> f k == g k) -> lub f == lub g.
intros; apply Ole_antisym; apply lub_le_lift with n; intros; auto.
apply Oeq_le_sym; auto.
Qed.

(** - (lub_fun h) x = lub_n (h n x) *)
Definition lub_fun : forall (O:ord) (D:cpo) (h : natO -m> O -m> D), O -m> D.
intros; exists (fun m => lub (h <_> m)).
red; intros.
apply lub_le_compat; simpl; intros.
apply (fmonotonic (h x0)); auto.
Defined.

Lemma lub_fun_eq : forall (O:ord) (D:cpo) (h : natO -m> O -m> D) (x:O),
           lub_fun h x == lub (h <_> x).
auto.
Qed.

Lemma lub_fun_shift :  forall (D:cpo) (h : natO -m> (natO -m>  D)),
             lub_fun h == Lub D @ (fmon_shift h).
intros; apply fmon_eq_intro; unfold lub_fun; simpl; auto.
Qed.

Lemma double_lub_simpl : forall (D:cpo) (h : natO -m> natO -m>  D),
        lub (Lub D @ h) == lub (fmon_diag h).
intros; apply Ole_antisym.
apply lub_le; intros; simpl; apply lub_le; intros.
apply Ole_trans with (h n (n+n0)).
apply (fmonotonic (h n)); auto with arith.
apply Ole_trans with (h (n+n0) (n+n0)).
apply (fmonotonic h); auto with arith.
apply le_lub with (f:=fmon_diag h) (n:=(n + n0)%nat).
apply lub_le_compat.
unfold fmon_diag; simpl; auto.
Qed.

Lemma lub_exch_le : forall (D:cpo) (h : natO -m> (natO -m>  D)),
                    lub (Lub D @ h) <= lub (lub_fun h).
intros; apply lub_le; intros; simpl.
apply lub_le; intros.
apply Ole_trans with (lub (h n)); auto.
apply lub_le_compat; intro.
unfold lub_fun; simpl.
apply le_lub with (f:=h <_> x) (n:=n).
Qed.
Global Hint Resolve lub_exch_le : core.

Lemma lub_exch_eq : forall (D:cpo) (h : natO -m> (natO -m>  D)),
 lub (Lub D @ h) == lub (lub_fun h).
intros; apply Ole_antisym; auto.
Qed.

Global Hint Resolve lub_exch_eq : core.

(** *** Functional cpos *)

Definition fcpo : Type -> cpo -> cpo.
intros A D; exists (ford A D)  (fun x:A => (0:D)) (fun f (x:A) => lub(c:=D) (f <o> x)); intros; auto.
intro x; apply Ole_trans with ((f <o> x) n); auto.
Defined.

(** printing -O-> %\ensuremath{\stackrel{O}{\longleftarrow}}% *)
Infix "-O->" := fcpo (right associativity, at level 30) : O_scope.

Lemma fcpo_lub_simpl : forall A (D:cpo) (h:natO-m> A-O->D)(x:A),
      (lub h) x = lub(c:=D) (h <o> x).
trivial.
Qed.

(** ** Continuity *)

Lemma lub_comp_le :
    forall (D1 D2 : cpo) (f:D1 -m> D2) (h : natO -m> D1),  lub (f @ h) <= f (lub h).
intros; apply lub_le; simpl; intros.
apply (fmonotonic f); auto.
Qed.
Global Hint Resolve lub_comp_le : core.

Lemma lub_comp2_le : forall (D1 D2 D3: cpo) (F:D1 -m> D2-m>D3) (f : natO -m> D1) (g: natO -m> D2),
        lub ((F @2 f) g) <= F (lub f)  (lub g).
intros; apply lub_le; simpl; auto.
Qed.
Global Hint Resolve lub_comp2_le : core.

Definition continuous (D1 D2 : cpo) (f:D1 -m> D2)
                := forall h : natO -m> D1,  f (lub h) <= lub (f @ h).

Lemma continuous_eq_compat : forall (D1 D2 : cpo) (f g:D1 -m> D2),
                 f==g -> continuous f -> continuous g.
red; intros.
apply Ole_trans with (f (lub h)).
assert (g <= f); auto.
rewrite <- H; auto.
Qed.

Add Parametric Morphism (D1 D2 : cpo) : (continuous (D1:=D1) (D2:=D2))
     with signature Oeq (O:=D1 -m> D2) ==> iff
as continuous_eq_compat_iff.
split; intros.
apply continuous_eq_compat with x; trivial.
apply continuous_eq_compat with y; auto.
Qed.

Lemma lub_comp_eq :
    forall (D1 D2 : cpo) (f:D1 -m> D2) (h : natO -m> D1),  continuous f -> f (lub h) == lub (f @ h).
intros; apply Ole_antisym; auto.
Qed.
Global Hint Resolve lub_comp_eq : core.


(** - mon0 x == 0 *)
Definition mon0 (O1:ord) (D2 : cpo) : O1 -m> D2 := fmon_cte O1 (0:D2).

Lemma cont0 : forall {D1 D2 : cpo}, continuous (mon0 D1 D2).
red; simpl; auto.
Qed.

(** - double_app f g n m = f m (g n) *)
Definition double_app (O1 O2 O3 O4: ord) (f:O1 -m> O3 -m> O4) (g:O2 -m> O3)
        : O2 -m> (O1 -m> O4) := (fmon_shift f) @ g.

(** ** Cpo of monotonic functions *)

Definition fmon_cpo : forall (O:ord) (D:cpo), cpo.
intros; exists (fmon O D) (mon0 O D) (lub_fun (O:=O) (D:=D)); auto.
simpl; intros.
apply le_lub with (f:=fmon_app f x) (n:=n); auto.
Defined.

(** printing -M-> %\ensuremath{\stackrel{M}{\longleftarrow}}% *)
Infix "-M->" := fmon_cpo (at level 30, right associativity) : O_scope.

Lemma fmon_lub_simpl : forall (O:ord) (D:cpo) (h:natO-m>O-M->D) (x:O),
             (lub h) x = lub (h <_> x).
trivial.
Qed.

Lemma double_lub_diag : forall (D:cpo) (h:natO-m>natO-M->D),
             lub (lub h) == lub (fmon_diag h).
intros.
intros; apply Ole_antisym.
apply lub_le; intros; simpl; apply lub_le; intros; simpl.
apply Ole_trans with (h (n+n0) (n+n0)); auto with arith.
apply le_lub with (f:=fmon_diag h) (n:=(n + n0)%nat).
apply lub_le_compat.
unfold fmon_diag; simpl; intros.
apply le_lub with (f:=h <_> x) (n:=x).
Qed.



(** *** Continuity *)

Definition continuous2 (D1 D2 D3: cpo) (F:D1 -m> D2 -m> D3)
     := forall (f : natO-m>D1) (g :natO-m>D2), F (lub f) (lub g) <= lub ((F @2 f) g).

Lemma continuous2_app : forall (D1 D2 D3:cpo) (F : D1-m>D2-m>D3),
            continuous2 F -> forall k, continuous (F k).
red; intros.
apply Ole_trans with (F (lub (mseq_cte k))  (lub h)); auto.
apply Ole_trans with (lub ((F @2 (mseq_cte k)) h)); auto.
Qed.

Lemma continuous2_continuous : forall (D1 D2 D3:cpo) (F : D1-m>D2-M->D3),
            continuous2 F -> continuous F.
red; intros; intro k.
apply Ole_trans with (F (lub h) (lub (mseq_cte k)) ); auto.
apply Ole_trans with (lub ((F @2 h) (mseq_cte k))); auto.
Qed.

Lemma continuous2_left : forall (D1 D2 D3:cpo) (F : D1-m>D2-M->D3) (h:natO-m>D1) (x:D2),
            continuous2 F -> F (lub h) x <= lub ((F <_> x) @h).
intros; apply (continuous2_continuous H h x).
Qed.

Lemma continuous2_right : forall (D1 D2 D3:cpo) (F : D1-m>D2-M->D3) (x:D1)(h:natO-m>D2),
            continuous2 F -> F x (lub h) <= lub (F x @h).
intros; apply (continuous2_app H x).
Qed.

Lemma continuous_continuous2 : forall (D1 D2 D3:cpo) (F : D1-m>D2-M->D3),
      (forall k:D1, continuous (F k)) -> continuous F -> continuous2 F.
red; intros.
apply Ole_trans with (lub (F (lub f) @ g)); auto.
apply lub_le; simpl; intros.
apply Ole_trans with (lub ((F <_> (g n))@f)).
apply Ole_trans with (lub (c:=D2 -M-> D3) (F@f) (g n)); auto.
rewrite (lub_lift_right ((F @2 f) g) n).
apply lub_le_compat; simpl; intros.
apply Ole_trans with (F (f x) (g (x+n))); auto with arith.
Qed.

Global Hint Resolve continuous2_app continuous2_continuous continuous_continuous2 : core.

Lemma lub_comp2_eq : forall (D1 D2 D3:cpo) (F : D1 -m> D2 -M-> D3),
      (forall k:D1, continuous (F k)) -> continuous F ->
      forall (f : natO-m>D1) (g :natO-m>D2),
      F (lub f) (lub g) == lub ((F@2 f) g).
intros; apply Ole_antisym; auto.
apply (continuous_continuous2 (F:=F)); trivial.
Qed.

Lemma lub_cont2_comp2_eq : forall (D1 D2 D3:cpo) (F : D1 -m> D2 -M-> D3),
      continuous2 F -> forall (f : natO-m>D1) (g :natO-m>D2), F (lub f) (lub g) == lub ((F@2 f) g).
intros; apply lub_comp2_eq; auto.
intro; apply (continuous2_app H).
Qed.

Lemma continuous_sym : forall (D1 D2:cpo) (F : D1-m> D1 -M-> D2),
      (forall x y, F x y == F y x) -> (forall k:D1, continuous (F k)) -> continuous F.
red; intros; intro k.
apply Ole_trans with (F k (lub h)); auto.
apply Ole_trans with (lub ((F k) @ h)); auto.
Qed.

Lemma continuous2_sym : forall (D1 D2:cpo) (F : D1-m>D1-m>D2),
      (forall x y, F x y == F y x) -> (forall k, continuous (F k)) -> continuous2 F.
intros; apply continuous_continuous2; auto.
apply continuous_sym; auto.
Qed.
Global Hint Resolve continuous2_sym : core.

(** - continuity is preserved by composition *)

Lemma continuous_comp : forall (D1 D2 D3:cpo) (f:D2-m>D3)(g:D1-m>D2),
             continuous f -> continuous g -> continuous (f@g).
red; intros.
rewrite fmon_comp_simpl.
apply Ole_trans with (f (lub (g@h))); auto.
apply Ole_trans with (lub (f@(g@h))); auto.
Qed.
Global Hint Resolve continuous_comp : core.

Lemma continuous2_comp : forall (D1 D2 D3 D4:cpo) (f:D1-m>D2)(g:D2-m>D3-M->D4),
             continuous f -> continuous2 g -> continuous2 (g @ f).
intros; apply continuous_continuous2; auto.
red; intros.
rewrite fmon_comp_simpl.
apply (continuous2_right (F:=g) (f k) h); trivial.
Qed.
Global Hint Resolve continuous2_comp : core.

Lemma continuous2_comp2 : forall (D1 D2 D3 D4:cpo) (f:D3-m>D4)(g:D1-m>D2-M->D3),
             continuous f -> continuous2 g -> continuous2 (fcomp2 D1 D2 D3 D4 f g).
red; intros.
rewrite fcomp2_simpl.
apply Ole_trans with (f (lub ((g@2 f0) g0))); auto.
apply Ole_trans with (lub (f@((g@2 f0) g0))); auto.
Qed.
Global Hint Resolve continuous2_comp2 : core.

(** ** Cpo of continuous functions *)

Lemma cont_lub : forall (D1 D2 : cpo) (f:natO -m> (D1 -m> D2)),
                                        (forall n, continuous (f n)) ->
                                        continuous  (lub (c:=D1-M->D2) f).
red; intros; simpl.
apply Ole_trans with
                        (lub (c:=D2) (Lub D2 @ (fmon_shift (double_app f h)))).
apply lub_le_compat; intro n; simpl.
apply Ole_trans with (lub ((f n) @ h)); auto.
rewrite lub_exch_eq.
apply lub_le_compat; intro n; simpl.
apply lub_le_compat; intro m; simpl; auto.
Qed.

Record fconti (D1 D2:cpo): Type
     := mk_fconti {fcontit : D1 -m> D2; fcontinuous : continuous fcontit}.
Global Hint Resolve fcontinuous : core.

Definition fconti_fun (D1 D2 :cpo) (f:fconti D1 D2) : D1-> D2 :=fun x => fcontit f x.
Coercion fconti_fun : fconti >-> Funclass.

Definition fcont_ord : cpo -> cpo -> ord.
intros D1 D2; exists (fconti D1 D2) (fun (f g: fconti D1 D2) => fcontit f <= fcontit g); intros; auto.
apply Ole_trans with (fcontit y); auto.
Defined.

(** printing -c-> %\ensuremath{\stackrel{c}{\leftarrow}}% *)
Infix "-c>" := fcont_ord (at level 30, right associativity) : O_scope.

Lemma fcont_le_intro : forall (D1 D2:cpo) (f g : D1 -c> D2), (forall x, f x <= g x) -> f <= g.
trivial.
Qed.

Lemma fcont_le_elim : forall (D1 D2:cpo) (f g : D1 -c> D2), f <= g -> forall x, f x <= g x.
trivial.
Qed.

Lemma fcont_eq_intro : forall (D1 D2:cpo) (f g : D1 -c> D2), (forall x, f x == g x) -> f == g.
intros; apply Ole_antisym; apply fcont_le_intro; auto.
Qed.

Lemma fcont_eq_elim : forall (D1 D2:cpo) (f g : D1 -c> D2), f == g -> forall x, f x == g x.
intros; apply Ole_antisym; apply fcont_le_elim; auto.
Qed.

Lemma fcont_monotonic : forall (D1 D2:cpo) (f : D1 -c> D2) (x y : D1),
            x <= y -> f x <= f y.
intros; apply (fmonotonic (fcontit f) H).
Qed.
Global Hint Resolve fcont_monotonic : core.

Lemma fcont_stable : forall (D1 D2:cpo) (f : D1 -c> D2) (x y : D1),
            x == y -> f x == f y.
intros; apply (fmon_stable (fcontit f) H).
Qed.
Global Hint Resolve fcont_monotonic : core.

Definition fcont0 (D1 D2:cpo) : D1 -c> D2 := mk_fconti (@cont0 D1 D2).

Definition Fcontit (D1 D2:cpo) : (D1 -c> D2) -m> D1-m> D2.
exists (fcontit (D1:=D1) (D2:=D2)); auto.
Defined.


Definition fcont_lub (D1 D2:cpo) : (natO -m> D1 -c> D2) -> D1 -c> D2.
intro f; exists (lub (c:=D1-M->D2) (Fcontit D1 D2 @f)).
apply cont_lub; intros; simpl; auto.
Defined.

Definition fcont_cpo : cpo -> cpo -> cpo.
intros D1 D2; exists (fcont_ord D1 D2) (fcont0 D1 D2) (fcont_lub (D1:=D1) (D2:=D2));
simpl; intros; auto.
apply le_lub with (f:=(Fcontit D1 D2 @ f) <_> x) (n:=n).
Defined.
(** printing -C-> %\ensuremath{\stackrel{C}{\longleftarrow}}% *)
Infix "-C->" := fcont_cpo (at level 30, right associativity) : O_scope.

Definition fcont_app (O:ord) (D1 D2:cpo) (f: O -m> D1-c> D2) (x:D1) : O -m> D2
         := Fcontit D1 D2 @ f <_> x.

(** printing <__> %\ensuremath{\Longleftrightarrow}%*)
Infix "<__>" := fcont_app (at level 70) : O_scope.

Lemma fcont_app_simpl : forall (O:ord) (D1 D2:cpo) (f: O -m> D1-c> D2) (x:D1)(y:O),
            (f <__> x) y = f y x.
trivial.
Qed.

Definition ford_fcont_shift (A:Type) (D1 D2:cpo) (f: A -o> (D1-c> D2)) : D1 -c> A -O-> D2.
intros; exists (ford_shift (fun x => Fcontit D1 D2 (f x))).
red; intros; intro x.
simpl.
apply Ole_trans with (lub (fcontit (f x) @ h)); auto.
Defined.

Definition fmon_fcont_shift (O:ord) (D1 D2:cpo) (f: O -m> D1-c> D2) : D1 -c> O -M-> D2.
intros; exists (fmon_shift (Fcontit D1 D2@f)).
red; intros; intro x.
simpl.
rewrite (fcontinuous (f x) h); auto.
Defined.


Lemma fcont_app_continuous :
       forall (O:ord) (D1 D2:cpo) (f: O -m> D1-c> D2) (h:natO-m>D1),
            f <__> (lub h) <= lub (c:=O-M->D2) (fcontit (fmon_fcont_shift f) @ h).
intros; intro x.
rewrite fcont_app_simpl.
rewrite (fcontinuous (f x) h); auto.
Qed.

Lemma fcont_lub_simpl : forall (D1 D2:cpo) (h:natO-m>D1-C->D2)(x:D1),
            lub h x = lub (h <__> x).
trivial.
Qed.

Definition continuous2_cont_app : forall (D1 D2 D3 :cpo) (f:D1-m> D2 -M-> D3),
            (forall k, continuous (f k)) -> D1 -m> (D2 -C-> D3).
intros; exists (fun k => mk_fconti (H k)); red; intros; auto.
Defined.

Lemma continuous2_cont_app_simpl :
forall (D1 D2 D3 :cpo) (f:D1-m> D2 -M-> D3)(H:forall k, continuous (f k))
        (k:D1),  continuous2_cont_app H k = mk_fconti (H k).
trivial.
Qed.

Lemma continuous2_cont : forall (D1 D2 D3 :cpo) (f:D1-m> D2 -M-> D3),
            continuous2 f -> D1 -c> (D2 -C-> D3).
intros; exists (continuous2_cont_app (f:=f) (continuous2_app H)).
red; intros; rewrite continuous2_cont_app_simpl; intro k; simpl.
apply Ole_trans with (lub (c:=D2-M->D3) (f@h) k); auto.
assert (continuous f); auto.
Defined.

Lemma Fcontit_cont : forall D1 D2, continuous (D1:=D1-C->D2) (D2:=D1-M->D2) (Fcontit D1 D2).
red; intros; auto.
Qed.
Global Hint Resolve Fcontit_cont : core.


Definition fcont_comp : forall (D1 D2 D3:cpo), (D2 -c> D3) -> (D1-c> D2) -> D1 -c> D3.
intros D1 D2 D3 f g.
exists (fcontit f @ fcontit g); auto.
Defined.

Infix "@_" := fcont_comp (at level 35) : O_scope.

Lemma fcont_comp_simpl : forall (D1 D2 D3:cpo)(f:D2 -c> D3)(g:D1-c> D2) (x:D1),
       (f @_ g) x = f (g x).
trivial.
Qed.

Lemma fcontit_comp_simpl : forall (D1 D2 D3:cpo)(f:D2 -c> D3)(g:D1-c> D2) (x:D1),
       fcontit (f @_ g) = fcontit f @ fcontit g.
trivial.
Qed.

Lemma fcont_comp_le_compat : forall (D1 D2 D3:cpo) (f g : D2 -c> D3) (k l :D1-c> D2),
      f <= g -> k <= l -> f @_ k <= g @_ l.
intros; apply fcont_le_intro; intro x.
repeat (rewrite fcont_comp_simpl).
apply Ole_trans with (g (k x)); auto.
Qed.
Global Hint Resolve fcont_comp_le_compat : core.

Add Parametric Morphism (D1 D2 D3:cpo) : (fcont_comp (D1:=D1) (D2:=D2) (D3:=D3))
with signature Ole (o:=D2 -c> D3) ++> Ole (o:=D1-c> D2) ++> Ole (o:=D1 -c> D3)
as fcont_comp_le_morph.
intros.
exact (fcont_comp_le_compat H H0).
Qed.

Add Parametric Morphism (D1 D2 D3:cpo) : (fcont_comp (D1:=D1) (D2:=D2) (D3:=D3))
with signature Oeq (O:=D2 -c> D3) ==> Oeq (O:=D1-c> D2) ==> Oeq (O:=D1 -c> D3)
as fcont_comp_eq_compat.
intros.
apply Ole_antisym; auto.
Qed.

Definition fcont_Comp (D1 D2 D3:cpo) : (D2 -C-> D3) -m> (D1-C-> D2) -m> D1 -C-> D3
      := le_compat2_mon (fcont_comp_le_compat (D1:=D1) (D2:=D2) (D3:=D3)).

Lemma fcont_Comp_simpl : forall (D1 D2 D3:cpo) (f:D2 -c> D3) (g:D1-c> D2),
               fcont_Comp D1 D2 D3 f g = f @_ g.
trivial.
Qed.

Lemma fcont_Comp_continuous2 : forall (D1 D2 D3:cpo), continuous2 (fcont_Comp D1 D2 D3).
red; intros.
change ((lub  f) @_ (lub g) <= lub (c:=D1 -C-> D3) ((fcont_Comp D1 D2 D3 @2 f) g)).
apply fcont_le_intro; intro x; rewrite fcont_comp_simpl.
repeat (rewrite fcont_lub_simpl).
rewrite fcont_app_continuous.
rewrite double_lub_diag.
apply lub_le_compat; simpl; auto.
Qed.

Definition fcont_COMP  (D1 D2 D3:cpo) : (D2 -C-> D3) -c> (D1-C-> D2) -C-> D1 -C-> D3
      := continuous2_cont (fcont_Comp_continuous2 (D1:=D1) (D2:=D2) (D3:=D3)).

Lemma fcont_COMP_simpl : forall (D1 D2 D3:cpo) (f: D2 -C-> D3) (g:D1-C-> D2),
	fcont_COMP D1 D2 D3 f g = f @_ g.
trivial.
Qed.

Definition fcont2_COMP  (D1 D2 D3 D4:cpo) : (D3 -C-> D4) -c> (D1-C-> D2-C->D3) -C-> D1 -C-> D2 -C-> D4 :=
   (fcont_COMP D1 (D2-C->D3) (D2 -C-> D4)) @_ (fcont_COMP D2 D3 D4).

Definition fcont2_comp  (D1 D2 D3 D4:cpo) (f:D3 -C-> D4)(F:D1-C-> D2-C->D3) := fcont2_COMP D1 D2 D3 D4 f F.

Infix "@@_" := fcont2_comp (at level 35) : O_scope.

Lemma fcont2_comp_simpl : forall (D1 D2 D3 D4:cpo) (f:D3 -C-> D4)(F:D1-C-> D2-C->D3)(x:D1)(y:D2),
       (f @@_ F) x y = f (F x y).
trivial.
Qed.

Lemma fcont_le_compat2 : forall (D1 D2 D3:cpo) (f : D1-c>D2-C->D3)
    (x y : D1) (z t : D2), x <= y -> z <= t -> f x z <= f y t.
intros; apply Ole_trans with (f y z); unfold fconti_fun; auto.
apply fmon_le_elim.
apply  (fmonotonic (Fcontit D2 D3) (x:=fcontit f x) (y:=fcontit f y)); auto.
Qed.
Global Hint Resolve fcont_le_compat2 : core.

Lemma fcont_eq_compat2 : forall (D1 D2 D3:cpo) (f : D1-c>D2-C->D3)
    (x y : D1) (z t : D2), x == y -> z == t -> f x z == f y t.
intros; apply Ole_antisym; auto.
Qed.
Global Hint Resolve fcont_eq_compat2 : core.

Lemma fcont_continuous : forall (D1 D2 : cpo) (f:D1 -c> D2)(h:natO-m>D1),
            f (lub h) <= lub (fcontit f @ h).
intros; apply (fcontinuous f h).
Qed.
Global Hint Resolve fcont_continuous : core.

Lemma fcont_continuous2 : forall (D1 D2 D3:cpo) (f:D1-c>(D2-C->D3)),
                                             continuous2 (Fcontit D2 D3 @ fcontit f).
intros; apply continuous_continuous2; intros.
change (continuous (fcontit (f k))); auto.
apply (continuous_comp (D1:=D1) (D2:=D2-C->D3) (D3:=D2-M->D3) (f:=Fcontit D2 D3)); auto.
Qed.
Global Hint Resolve fcont_continuous2 : core.

Definition fcont_shift (D1 D2 D3 : cpo) (f:D1-c>D2-C->D3) : D2-c>D1-C->D3.
intros.
apply continuous2_cont with (D1:=D2) (D2:=D1) (D3:=D3)
  (f:=fmon_shift (O1:=D1) (O2:=D2) (O3:=D3) (Fcontit D2 D3 @ fcontit f)).
red; intros; repeat rewrite fmon_shift_simpl.
repeat rewrite fmon_comp_simpl; auto.
change (f (lub g) (lub f0) <= lub ((fmon_shift (Fcontit D2 D3 @ fcontit f) @2 f0) g)).
apply Ole_trans with (1:=fcont_continuous2 f g f0).
apply lub_le_compat; intro n.
repeat rewrite fmon_comp_simpl; auto.
Defined.

Lemma fcont_shift_simpl : forall (D1 D2 D3 : cpo) (f:D1-c>D2-C->D3) (x:D2) (y:D1),
            fcont_shift f x y = f y x.
trivial.
Qed.

Definition fcont_SEQ  (D1 D2 D3:cpo) : (D1-C-> D2) -C-> (D2 -C-> D3) -C-> D1 -C-> D3
      := fcont_shift (fcont_COMP D1 D2 D3).

Lemma fcont_SEQ_simpl : forall (D1 D2 D3:cpo) (f: D1 -C-> D2) (g:D2-C-> D3),
	fcont_SEQ D1 D2 D3 f g = g @_ f.
trivial.
Qed.

Definition fcont_comp2 : forall (D1 D2 D3 D4:cpo),
                (D2 -c> D3 -C->D4) -> (D1-c> D2) -> (D1 -c> D3) -> D1-c>D4.
intros D1 D2 D3 D4 f g h.
exists (((Fcontit D3 D4 @fcontit f) @2 fcontit g) (fcontit h)).
red; intros; simpl.
change (f (g (lub h0)) (h (lub h0)) <= lub (c:=D4) ((Fcontit D3 D4 @ fcontit f @2 fcontit g) (fcontit h) @ h0)).
apply Ole_trans with (f (lub (c:=D2) (fcontit g @ h0)) (lub (c:=D3) (fcontit h @ h0))); auto.
apply (fcont_continuous2 f (fcontit g @ h0) (fcontit h @ h0)).
Defined.

Infix "@2_" := fcont_comp2 (at level 35, right associativity) : O_scope.

Lemma fcont_comp2_simpl : forall (D1 D2 D3 D4:cpo)
                (F:D2 -c> D3 -C->D4) (f:D1-c> D2) (g:D1 -c> D3) (x:D1), (F@2_ f) g x = F (f x) (g x).
trivial.
Qed.

Add Parametric Morphism (D1 D2 D3 D4:cpo) : (fcont_comp2 (D1:=D1) (D2:=D2) (D3:=D3) (D4:=D4))
  with signature Ole (o:=D2 -c> D3 -C->D4) ++>Ole (o:=D1-c> D2) ++> Ole (o:=D1 -c> D3) ++> Ole (o:=D1-c>D4)
as fcont_comp2_le_morph.
intros F G HF f1 f2 Hf g1 g2 Hg x; simpl.
apply Ole_trans with (fcontit (fcontit G (fcontit f1 x)) (fcontit g1 x)).
apply HF.
change (Fcontit D3 D4 (fcontit G (fcontit f1 x)) (fcontit g1 x) <=
              Fcontit D3 D4 (fcontit G (fcontit f2 x)) (fcontit g2 x)).
apply (fmon_le_compat2 (Fcontit D3 D4)); auto.
Qed.

Add Parametric Morphism (D1 D2 D3 D4:cpo) : (fcont_comp2 (D1:=D1) (D2:=D2) (D3:=D3) (D4:=D4))
with signature Oeq (O:=D2 -c> D3 -C->D4) ==> Oeq (O:=D1-c> D2) ==> Oeq (O:=D1 -c> D3) ==> Oeq (O:=D1-c>D4)
as fcont_comp2_eq_compat.
intros F G (HF1,HF2) f1 f2 (Hf1,Hf2) g1 g2 (Hg1,Hg2).
apply Ole_antisym.
exact (fcont_comp2_le_morph HF1 Hf1 Hg1).
exact (fcont_comp2_le_morph HF2 Hf2 Hg2).
Qed.


(** - Identity function is continuous *)

Definition Id : forall O:ord, O-m>O.
intros; exists (fun x:O => x); red; auto.
Defined.

Definition ID : forall D:cpo, D-c>D.
intros; exists (Id D); red; auto.
Defined.

Lemma Id_simpl : forall O x, Id O x = x.
trivial.
Qed.

Lemma ID_simpl : forall D x, ID D x = Id D x.
trivial.
Qed.

Definition AP (D1 D2:cpo) : (D1-C->D2)-c>D1-C->D2:=ID (D1-C->D2).

Lemma AP_simpl : forall (D1 D2:cpo) (f : D1-C->D2) (x:D1), AP D1 D2 f x = f x.
trivial.
Qed.

Definition fcont_comp3 (D1 D2 D3 D4 D5:cpo)
                (F:D2 -c> D3 -C->D4-C->D5)(f:D1-c> D2)(g:D1 -c> D3)(h:D1-c>D4): D1-c>D5
  := (AP D4 D5 @2_ ((F @2_ f) g)) h.

Infix "@3_" := fcont_comp3 (at level 35, right associativity) : O_scope.

Lemma fcont_comp3_simpl : forall (D1 D2 D3 D4 D5:cpo)
                (F:D2 -c> D3 -C->D4-C->D5) (f:D1-c> D2) (g:D1 -c> D3) (h:D1-c>D4) (x:D1),
                (F@3_ f) g h x = F (f x) (g x) (h x).
trivial.
Qed.

(** ** Product of two cpos *)

Definition Oprod : ord -> ord -> ord.
intros O1 O2; exists (O1 * O2)%type (fun (x y:O1*O2) => fst x <= fst y /\ snd x <= snd y); intuition.
apply Ole_trans with a0; trivial.
apply Ole_trans with b0; trivial.
Defined.

Definition Fst (O1 O2 : ord) : Oprod O1 O2 -m> O1.
exists (fst (A:=O1) (B:=O2)); red; simpl; intuition.
Defined.

Definition Snd (O1 O2 : ord) : Oprod O1 O2 -m> O2.
exists (snd (A:=O1) (B:=O2)); red; simpl; intuition.
Defined.

Definition Pairr (O1 O2 : ord) : O1 -> O2 -m> Oprod O1 O2.
intro x; exists (fun y:O2 => (x,y)); red; auto.
Defined.

Definition Pair (O1 O2 : ord) : O1 -m> O2 -m> Oprod O1 O2.
exists (Pairr (O1:=O1) O2); red; auto.
Defined.

Lemma Fst_simpl : forall (O1 O2 : ord) (p:Oprod O1 O2), Fst O1 O2 p = fst p.
trivial.
Qed.

Lemma Snd_simpl : forall (O1 O2 : ord) (p:Oprod O1 O2), Snd O1 O2 p = snd p.
trivial.
Qed.

Lemma Pair_simpl : forall (O1 O2 : ord) (x:O1)(y:O2), Pair O1 O2 x y = (x,y).
trivial.
Qed.


Definition prod0 (D1 D2:cpo) : Oprod D1 D2 := (0: D1,0: D2).
Definition prod_lub (D1 D2:cpo) (f : natO -m> Oprod D1 D2) := (lub (Fst D1 D2@f), lub (Snd D1 D2@f)).

Definition Dprod : cpo -> cpo -> cpo.
intros D1 D2; exists (Oprod D1 D2) (prod0 D1 D2) (prod_lub (D1:=D1) (D2:=D2)); unfold prod_lub; intuition.
apply Ole_trans with (fst (fmonot f n), snd (fmonot f n)); simpl; intuition.
apply le_lub with (f:=Fst D1 D2 @ f) (n:=n).
apply le_lub with (f:=Snd D1 D2 @ f) (n:=n).
apply Ole_trans with (fst x, snd x); simpl; intuition.
apply lub_le; simpl; intros.
case (H n); auto.
apply lub_le; simpl; intros.
case (H n); auto.
Defined.

Lemma Dprod_eq_intro : forall (D1 D2:cpo) (p1 p2: Dprod D1 D2),
             fst p1 == fst p2 -> snd p1 == snd p2 -> p1 == p2.
split; simpl; auto.
Qed.
Global Hint Resolve Dprod_eq_intro : core.

Lemma Dprod_eq_pair : forall (D1 D2:cpo) (x1 y1:D1) (x2 y2:D2),
             x1==y1 -> x2==y2 -> ((x1,x2):Dprod D1 D2) == (y1,y2).
auto.
Qed.
Global Hint Resolve Dprod_eq_pair : core.

Lemma Dprod_eq_elim_fst : forall (D1 D2:cpo) (p1 p2: Dprod D1 D2),
             p1==p2 -> fst p1 == fst p2.
split; case H; simpl; intuition.
Qed.
Global Hint Immediate Dprod_eq_elim_fst : core.

Lemma Dprod_eq_elim_snd : forall (D1 D2:cpo) (p1 p2: Dprod D1 D2),
             p1==p2 -> snd p1 == snd p2.
split; case H; simpl; intuition.
Qed.
Global Hint Immediate Dprod_eq_elim_snd : core.

Definition FST (D1 D2:cpo) : Dprod D1 D2 -c> D1.
intros; exists (Fst D1 D2); red; intros; auto.
Defined.

Definition SND (D1 D2:cpo) : Dprod D1 D2 -c> D2.
intros; exists (Snd D1 D2); red; intros; auto.
Defined.

Lemma Pair_continuous2 : forall (D1 D2:cpo), continuous2 (D3:=Dprod D1 D2) (Pair D1 D2).
red; intros; auto.
Qed.

Definition PAIR (D1 D2:cpo) : D1 -c> D2 -C-> Dprod D1 D2
                := continuous2_cont (Pair_continuous2 (D1:=D1) (D2:=D2)).

Lemma FST_simpl : forall (D1 D2 :cpo) (p:Dprod D1 D2), FST D1 D2 p = Fst D1 D2 p.
trivial.
Qed.

Lemma SND_simpl : forall (D1 D2 :cpo) (p:Dprod D1 D2), SND D1 D2 p = Snd D1 D2 p.
trivial.
Qed.

Lemma PAIR_simpl : forall (D1 D2 :cpo) (p1:D1) (p2:D2), PAIR D1 D2 p1 p2 = Pair D1 D2 p1 p2.
trivial.
Qed.

Lemma FST_PAIR_simpl : forall (D1 D2 :cpo) (p1:D1) (p2:D2),
            FST D1 D2 (PAIR D1 D2 p1 p2) = p1.
trivial.
Qed.

Lemma SND_PAIR_simpl : forall (D1 D2 :cpo) (p1:D1) (p2:D2),
            SND D1 D2 (PAIR D1 D2 p1 p2) = p2.
trivial.
Qed.

Definition Prod_map :  forall (D1 D2 D3 D4:cpo)(f:D1-m>D3)(g:D2-m>D4) ,
      Dprod D1 D2 -m> Dprod D3 D4.
intros; exists (fun p => pair (f (fst p)) (g (snd p))); red; intros.
split; simpl fst; simpl snd; apply fmonotonic.
apply (fmonotonic (Fst D1 D2) H).
apply (fmonotonic (Snd D1 D2) H).
Defined.


Lemma Prod_map_simpl : forall (D1 D2 D3 D4:cpo)(f:D1-m>D3)(g:D2-m>D4) (p:Dprod D1 D2),
      Prod_map f g p =  pair (f (fst p)) (g (snd p)).
trivial.
Qed.

Definition PROD_map :  forall (D1 D2 D3 D4:cpo)(f:D1-c>D3)(g:D2-c>D4) ,
      Dprod D1 D2 -c> Dprod D3 D4.
intros; exists (Prod_map (fcontit f) (fcontit g)); red; intros; rewrite Prod_map_simpl.
split; simpl.
apply Ole_trans with (f (lub (Fst D1 D2 @ h))); trivial.
rewrite (fcont_continuous f).
apply lub_le_compat; intros; intro; simpl; auto.
apply Ole_trans with (g (lub (Snd D1 D2 @ h))); trivial.
rewrite (fcont_continuous g).
apply lub_le_compat; intros; intro; simpl; auto.
Defined.

Lemma PROD_map_simpl :  forall (D1 D2 D3 D4:cpo)(f:D1-c>D3)(g:D2-c>D4)(p:Dprod D1 D2),
      PROD_map f g p = pair (f (fst p)) (g (snd p)).
trivial.
Qed.

Definition curry (D1 D2 D3 : cpo) (f:Dprod D1 D2 -c> D3) : D1 -c> (D2-C->D3) :=
fcont_COMP D1 (D2-C->Dprod D1 D2) (D2-C->D3)
                          (fcont_COMP D2 (Dprod D1 D2) D3 f) (PAIR D1 D2).

Definition Curry : forall (D1 D2 D3 : cpo), (Dprod D1 D2 -c> D3) -m> D1 -c> (D2-C->D3).
       intros; exists (curry (D1:=D1)(D2:=D2)(D3:=D3)); red; intros; auto.
Defined.

Lemma Curry_simpl : forall (D1 D2 D3 : cpo) (f:Dprod D1 D2 -C-> D3) (x:D1) (y:D2),
       Curry D1 D2 D3 f x y = f (x,y).
trivial.
Qed.

Definition CURRY : forall (D1 D2 D3 : cpo), (Dprod D1 D2 -C-> D3) -c> D1 -C-> (D2-C->D3).
       intros; exists (Curry D1 D2 D3); red; intros; auto.
Defined.

Lemma CURRY_simpl : forall (D1 D2 D3 : cpo) (f:Dprod D1 D2 -C-> D3),
       CURRY D1 D2 D3 f = Curry D1 D2 D3 f.
trivial.
Qed.

Definition uncurry (D1 D2 D3 : cpo) (f:D1 -c> (D2-C->D3)) : Dprod D1 D2 -c> D3
      :=  (f @2_ (FST D1 D2)) (SND D1 D2).

Definition Uncurry : forall (D1 D2 D3 : cpo), (D1 -c> (D2-C->D3)) -m> Dprod D1 D2 -c> D3.
       intros; exists (uncurry (D1:=D1)(D2:=D2)(D3:=D3)).
red; intros.
apply fcont_le_intro; intro z; unfold uncurry.
repeat (rewrite fcont_comp2_simpl); auto.
apply (H (FST D1 D2 z) (SND D1 D2 z)).
Defined.

Lemma Uncurry_simpl : forall (D1 D2 D3 : cpo) (f:D1 -c> (D2-C->D3)) (p:Dprod D1 D2),
       Uncurry D1 D2 D3 f p = f (fst p) (snd p).
trivial.
Qed.

Definition UNCURRY : forall (D1 D2 D3 : cpo), (D1 -C-> (D2-C->D3)) -c> Dprod D1 D2 -C-> D3.
       intros; exists (Uncurry D1 D2 D3); red; intros; auto.
Defined.

Lemma UNCURRY_simpl : forall (D1 D2 D3 : cpo)  (f:D1 -c> (D2-C->D3)),
       UNCURRY D1 D2 D3 f = Uncurry D1 D2 D3 f.
trivial.
Qed.

(** ** Indexed product of cpo's *)

Definition Oprodi (I:Type)(O:I->ord) : ord.
intros; exists (forall i:I, O i) (fun p1 p2:forall i:I, O i => forall i:I, p1 i <= p2 i); intros; auto.
apply Ole_trans with (y i); trivial.
Defined.

Lemma Oprodi_eq_intro : forall (I:Type)(O:I->ord) (p q : Oprodi O), (forall i, p i == q i) -> p==q.
intros; apply Ole_antisym; intro i; auto.
Qed.

Lemma Oprodi_eq_elim : forall (I:Type)(O:I->ord) (p q : Oprodi O), p==q -> forall i, p i == q i.
intros; apply Ole_antisym; case H; auto.
Qed.

Definition Proj (I:Type)(O:I->ord) (i:I) : Oprodi O -m> O i.
intros; exists (fun x: Oprodi O=> x i); red; intuition.
Defined.

Lemma Proj_simpl : forall  (I:Type)(O:I->ord) (i:I) (x:Oprodi O),
            Proj O i x = x i.
trivial.
Qed.

Definition Dprodi (I:Type)(D:I->cpo) : cpo.
intros; exists (Oprodi D) (fun i=>(0:D i)) (fun (f : natO -m> Oprodi D) (i:I) => lub (Proj D i @ f));
intros; simpl; intros; auto.
apply le_lub with (f:= Proj (fun x : I => D x) i @ f) (n:=n).
apply lub_le; simpl; intros.
apply (H n i).
Defined.

Lemma Dprodi_lub_simpl : forall (I:Type)(Di:I->cpo)(h:natO-m>Dprodi Di)(i:I),
            lub h i = lub (c:=Di i) (Proj Di i @ h).
trivial.
Qed.

Lemma Dprodi_continuous : forall (D:cpo)(I:Type)(Di:I->cpo)
    (f:D -m> Dprodi Di), (forall i, continuous (Proj Di i @ f)) ->
    continuous f.
red; intros; intro i.
apply Ole_trans with (lub (c:=Di i) ((Proj Di i @ f) @ h)); auto.
exact (H i h).
Qed.

Definition Dprodi_lift : forall (I J:Type)(Di:I->cpo)(f:J->I),
             Dprodi Di -m> Dprodi (fun j => Di (f j)).
intros; exists (fun (p: Dprodi Di) j => p (f j)); red; auto.
Defined.

Lemma Dprodi_lift_simpl : forall (I J:Type)(Di:I->cpo)(f:J->I)(p:Dprodi Di),
             Dprodi_lift Di f p = fun j => p (f j).
trivial.
Qed.

Lemma Dprodi_lift_cont : forall (I J:Type)(Di:I->cpo)(f:J->I),
             continuous (Dprodi_lift Di f).
intros; apply Dprodi_continuous; red; simpl; intros; auto.
Qed.

Definition DLIFTi (I J:Type)(Di:I->cpo)(f:J->I) : Dprodi Di -c> Dprodi (fun j => Di (f j))
             := mk_fconti (Dprodi_lift_cont (Di:=Di) f).

Definition Dmapi : forall (I:Type)(Di Dj:I->cpo)(f:forall i, Di i -m> Dj i),
            Dprodi Di -m> Dprodi Dj.
intros; exists (fun p i => f i (p i)); red; auto.
Defined.

Lemma Dmapi_simpl : forall (I:Type)(Di Dj:I->cpo)(f:forall i, Di i -m> Dj i) (p:Dprodi Di) (i:I),
Dmapi f p i = f i (p i).
trivial.
Qed.

Lemma DMAPi : forall (I:Type)(Di Dj:I->cpo)(f:forall i, Di i -c> Dj i),
            Dprodi Di -c> Dprodi Dj.
intros; exists (Dmapi (fun i => fcontit (f i))).
red; intros; intro i; rewrite Dmapi_simpl.
repeat (rewrite Dprodi_lub_simpl).
apply Ole_trans with (lub (c:=Dj i) (Fcontit (Di i) (Dj i) (f i) @ (Proj (fun x : I => Di x) i @ h))); auto.
Defined.

Lemma DMAPi_simpl : forall (I:Type)(Di Dj:I->cpo)(f:forall i, Di i -c> Dj i) (p:Dprodi Di) (i:I),
DMAPi f p i = f i (p i).
trivial.
Qed.

Lemma Proj_cont : forall (I:Type)(Di:I->cpo) (i:I),
                    continuous (D1:=Dprodi Di) (D2:=Di i) (Proj Di i).
red; intros; simpl; trivial.
Qed.

Definition PROJ (I:Type)(Di:I->cpo) (i:I) : Dprodi Di -c> Di i :=
      mk_fconti (Proj_cont (Di:=Di) i).

Lemma PROJ_simpl : forall (I:Type)(Di:I->cpo) (i:I)(d:Dprodi Di),
               PROJ Di i d = d i.
trivial.
Qed.

(** *** Particular cases with one or two elements *)

Section Product2.

Definition I2 := bool.
Variable DI2 : bool -> cpo.

Definition DP1 := DI2 true.
Definition DP2 := DI2 false.

Definition PI1 : Dprodi DI2 -c> DP1 := PROJ DI2 true.
Definition pi1 (d:Dprodi DI2) := PI1 d.

Definition PI2 : Dprodi DI2 -c> DP2 := PROJ DI2 false.
Definition pi2 (d:Dprodi DI2) := PI2 d.

Definition pair2 (d1:DP1) (d2:DP2) : Dprodi DI2 := bool_rect DI2 d1 d2.

Lemma pair2_le_compat : forall (d1 d'1:DP1) (d2 d'2:DP2), d1 <= d'1 -> d2 <= d'2
            -> pair2 d1 d2 <= pair2 d'1 d'2.
intros; intro b; case b; simpl; auto.
Qed.

Definition Pair2 : DP1 -m> DP2 -m> Dprodi DI2 := le_compat2_mon pair2_le_compat.

Definition PAIR2 : DP1 -c> DP2 -C-> Dprodi DI2.
apply continuous2_cont with (D1:=DP1) (D2:=DP2) (D3:=Dprodi DI2) (f:=Pair2).
red; intros; intro b.
case b; simpl; apply lub_le_compat; auto.
Defined.

Lemma PAIR2_simpl : forall (d1:DP1) (d2:DP2), PAIR2 d1 d2 = Pair2 d1 d2.
trivial.
Qed.

Lemma Pair2_simpl : forall (d1:DP1) (d2:DP2), Pair2 d1 d2 = pair2 d1 d2.
trivial.
Qed.

Lemma pi1_simpl : forall  (d1: DP1) (d2:DP2), pi1 (pair2 d1 d2) = d1.
trivial.
Qed.

Lemma pi2_simpl : forall  (d1: DP1) (d2:DP2), pi2 (pair2 d1 d2) = d2.
trivial.
Qed.

Definition DI2_map (f1 : DP1 -c> DP1) (f2:DP2 -c> DP2)
               : Dprodi DI2 -c> Dprodi DI2 :=
                 DMAPi (bool_rect (fun b:bool => DI2 b -c>DI2 b) f1 f2).

Lemma Dl2_map_eq : forall (f1 : DP1 -c> DP1) (f2:DP2 -c> DP2) (d:Dprodi DI2),
               DI2_map f1 f2 d == pair2 (f1 (pi1 d)) (f2 (pi2 d)).
intros; simpl; apply Oprodi_eq_intro; intro b; case b; trivial.
Qed.
End Product2.
Global Hint Resolve Dl2_map_eq : core.

Section Product1.
Definition I1 := unit.
Variable D : cpo.

Definition DI1 (_:unit) := D.
Definition PI : Dprodi DI1 -c> D := PROJ DI1 tt.
Definition pi (d:Dprodi DI1) := PI d.

Definition pair1 (d:D) : Dprodi DI1 := unit_rect DI1 d.

Definition pair1_simpl : forall (d:D) (x:unit), pair1 d x = d.
destruct x; trivial.
Defined.

Definition Pair1 : D -m> Dprodi DI1.
exists pair1; red; intros; intro d.
repeat (rewrite pair1_simpl);trivial.
Defined.


Lemma Pair1_simpl : forall (d:D), Pair1 d = pair1 d.
trivial.
Qed.

Definition PAIR1 : D -c> Dprodi DI1.
exists Pair1; red; intros; repeat (rewrite Pair1_simpl).
intro d; rewrite pair1_simpl.
rewrite (Dprodi_lub_simpl (Di:=DI1)).
apply lub_le_compat; intros.
intro x; simpl; rewrite pair1_simpl; auto.
Defined.

Lemma pi_simpl : forall  (d:D), pi (pair1 d) = d.
trivial.
Qed.

Definition DI1_map (f : D -c> D)
               : Dprodi DI1 -c> Dprodi DI1 :=
                 DMAPi (fun t:unit => f).

Lemma DI1_map_eq : forall (f : D -c> D) (d:Dprodi DI1),
               DI1_map f d == pair1 (f (pi d)).
intros; simpl; apply Oprodi_eq_intro; intro b; case b; trivial.
Qed.
End Product1.

Global Hint Resolve DI1_map_eq : core.

(** ** Fixpoints *)
Section Fixpoints.
Variable D: cpo.
Variable f : D -m>D.

Hypothesis fcont : continuous f.

Fixpoint iter_ n : D := match n with O => 0 | S m => f (iter_ m) end.

Lemma iter_incr : forall n, iter_ n <= f (iter_ n).
induction n; simpl; auto.
Qed.
Hint Resolve iter_incr : core.

Definition iter : natO -m> D.
exists iter_; red; intros.
induction H; simpl; auto.
apply Ole_trans with (iter_ m); auto.
Defined.

Definition fixp : D := lub iter.

Lemma fixp_le : fixp <= f fixp.
unfold fixp.
apply Ole_trans with (lub (fmon_comp f iter)); auto.
Qed.
Hint Resolve fixp_le : core.

Lemma fixp_eq : fixp == f fixp.
apply Ole_antisym; auto.
unfold fixp.
apply Ole_trans with (1:= fcont iter).
rewrite (lub_lift_left iter (S O)); auto.
Qed.

Lemma fixp_inv : forall g, f g <= g -> fixp <= g.
unfold fixp; intros.
apply lub_le.
induction n; intros; auto.
simpl; apply Ole_trans with (f g); auto.
Qed.

End Fixpoints.
Global Hint Resolve fixp_le fixp_eq fixp_inv : core.

Definition fixp_cte : forall (D:cpo) (d:D), fixp (fmon_cte D d) == d.
intros; apply fixp_eq with (f:=fmon_cte D d); red; intros; auto.
unfold fmon_cte at 1; simpl.
apply le_lub with (f:=fmon_comp (fmon_cte D (O2:=D) d) h) (n:=O); simpl; auto.
Qed.
Global Hint Resolve fixp_cte : core.

Lemma fixp_le_compat : forall (D:cpo) (f g : D-m>D), f<=g -> fixp f <= fixp g.
intros; unfold fixp.
apply lub_le_compat.
intro n; induction n; simpl; auto.
apply Ole_trans with (g (iter_ (D:=D) f n)); auto.
Qed.
Global Hint Resolve fixp_le_compat : core.

Add Parametric Morphism (D:cpo) : (fixp (D:=D))
     with signature Oeq (O:=D-m>D) ==> Oeq (O:=D)
as fixp_eq_compat.
intros; apply Ole_antisym; auto.
Qed.
Global Hint Resolve fixp_eq_compat : core.

Definition Fixp : forall (D:cpo), (D-m>D) -m> D.
intros D; exists (fixp (D:=D)); auto.
Defined.

Lemma Fixp_simpl : forall (D:cpo) (f:D-m>D), Fixp D f = fixp f.
trivial.
Qed.

Definition Iter : forall D:cpo, (D-M->D) -m> (natO -M->D).
intro D; exists (fun (f:D-M->D) => iter (D:=D) f); red; intros.
intro n; induction n; simpl; intros; auto.
apply Ole_trans with (y (iter_ (D:=D) x n)); auto.
Defined.

Lemma IterS_simpl : forall (D:cpo) f n, Iter D f (S n) = f (Iter D f n).
trivial.
Qed.

Lemma iterS_simpl : forall (D:cpo) f n, iter f (S n) = f (iter (D:=D) f n).
trivial.
Qed.

Lemma iter_continuous : forall (D:cpo),
    forall h : natO -m> (D-M->D), (forall n, continuous (h n)) ->
                  iter (lub h) <= lub (Iter D @ h).
red; intros; intro k.
induction k; auto.
rewrite iterS_simpl.
apply Ole_trans with (lub h  (lub (c:=natO -M-> D) (Iter D @ h) k)); auto.
repeat (rewrite fmon_lub_simpl).
apply Ole_trans with
       (lub (c:=D) (lub (c:=natO-M->D) (double_app h ((Iter D @ h) <_> k)))).
apply lub_le_compat; simpl; intros.
apply Ole_trans with (lub ((h x)@((Iter D @ h) <_> k))); auto.
apply Ole_trans
  with (lub (fmon_diag  (double_app h ((Iter D @ h) <_> k)))); auto.
case (double_lub_diag (double_app h ((Iter D @ h) <_> k))); intros L _.
apply Ole_trans with (1:=L); auto.
Qed.

Global Hint Resolve iter_continuous : core.

Lemma iter_continuous_eq : forall (D:cpo),
    forall h : natO -m> (D-M->D), (forall n, continuous (h n)) ->
                  iter (lub h) == lub (Iter D @ h).
intros; apply Ole_antisym; auto.
exact (lub_comp_le (Iter D) h).
Qed.


Lemma fixp_continuous : forall (D:cpo) (h : natO -m> (D-M->D)),
       (forall n, continuous (h n)) -> fixp (lub h) <= lub (Fixp D @ h).
intros; unfold fixp.
rewrite (iter_continuous_eq H).
simpl; rewrite <- lub_exch_eq; auto.
Qed.
Global Hint Resolve fixp_continuous : core.

Lemma fixp_continuous_eq : forall (D:cpo) (h : natO -m> (D -M-> D)),
       (forall n, continuous (h n)) -> fixp (lub h) == lub (Fixp D @ h).
intros; apply Ole_antisym; auto.
exact (lub_comp_le (D1:=D -M-> D) (Fixp D) h).
Qed.

Definition FIXP : forall (D:cpo), (D-C->D) -c> D.
intro D; exists (Fixp D @ (Fcontit D D)).
red; intros.
rewrite fmon_comp_simpl.
rewrite Fixp_simpl.
apply Ole_trans with (fixp (D:=D) (lub (c:=D-M->D) (Fcontit D D@h))); auto.
apply Ole_trans with  (lub (Fixp D @ (Fcontit D D@h))); auto.
apply fixp_continuous; intros.
change (continuous (D1:=D) (D2:=D) (fcontit (h n))); auto.
Defined.

Lemma FIXP_simpl : forall (D:cpo) (f:D-c>D), FIXP D f = Fixp D (fcontit f).
trivial.
Qed.

Lemma FIXP_le_compat : forall (D:cpo) (f g : D-C->D),
            f <= g -> FIXP D f <= FIXP D g.
intros; repeat (rewrite FIXP_simpl); repeat (rewrite Fixp_simpl).
apply fixp_le_compat; auto.
Qed.
Global Hint Resolve FIXP_le_compat : core.

Lemma FIXP_eq_compat : forall (D:cpo) (f g : D-C->D),
            f == g -> FIXP D f == FIXP D g.
intros; apply Ole_antisym; auto.
Qed.
Global Hint Resolve FIXP_eq_compat : core.

Lemma FIXP_eq : forall (D:cpo) (f:D-c>D), FIXP D f == f (FIXP D f).
intros; rewrite FIXP_simpl; rewrite Fixp_simpl.
apply (fixp_eq (f:=fcontit f)).
auto.
Qed.
Global Hint Resolve FIXP_eq : core.

Lemma FIXP_inv : forall (D:cpo) (f:D-c>D)(g : D), f g <= g -> FIXP D f <= g.
intros; rewrite FIXP_simpl; rewrite Fixp_simpl; apply fixp_inv; auto.
Qed.

(** *** Iteration of functional *)
Lemma FIXP_comp_com : forall (D:cpo) (f g:D-c>D),
       g @_ f <= f @_ g-> FIXP D g <= f (FIXP D g).
intros; apply FIXP_inv.
apply Ole_trans with (f (g (FIXP D g))).
apply (fcont_le_elim H (FIXP D g)).
apply fcont_monotonic.
case (FIXP_eq g); trivial.
Qed.

Lemma FIXP_comp : forall (D:cpo) (f g:D-c>D),
       g @_ f <= f @_ g -> f (FIXP D g) <= FIXP D g -> FIXP D (f @_ g) == FIXP D g.
intros; apply Ole_antisym.
(* fix f @_ g <= fix g *)
apply FIXP_inv.
rewrite fcont_comp_simpl.
apply Ole_trans with (f (FIXP D g)); auto.
(* fix g <= fix f @_ g *)
apply FIXP_inv.
assert (g (f (FIXP D (f @_ g))) <= f (g (FIXP D (f @_ g)))).
apply (H (FIXP D (f @_ g))).
case (FIXP_eq (f@_g)); intros.
apply Ole_trans with (2:=H3).
apply Ole_trans with (2:=H1).
apply fcont_monotonic.
apply FIXP_inv.
rewrite fcont_comp_simpl.
apply fcont_monotonic.
apply Ole_trans with (1:=H1); auto.
Qed.

Fixpoint fcont_compn (D:cpo)(f:D-c>D) (n:nat) {struct n} : D-c>D :=
             match n with O => f | S p => fcont_compn f p @_ f end.

Lemma fcont_compn_com : forall (D:cpo)(f:D-c>D) (n:nat),
            f @_ (fcont_compn f n) <= fcont_compn f n @_ f.
induction n; auto.
simpl fcont_compn.
apply Ole_trans with ((f @_ fcont_compn (D:=D) f n) @_ f); auto.
Qed.

Lemma FIXP_compn :
     forall (D:cpo) (f:D-c>D) (n:nat), FIXP D (fcont_compn f n) == FIXP D f.
induction n; auto.
simpl fcont_compn.
apply FIXP_comp.
apply fcont_compn_com.
apply Ole_trans with (fcont_compn (D:=D) f n (FIXP D (fcont_compn (D:=D) f n))); auto.
apply Ole_trans with (FIXP D (fcont_compn (D:=D) f n)); auto.
Qed.

Lemma fixp_double : forall (D:cpo) (f:D-c>D), FIXP D (f @_ f) == FIXP D f.
intros; exact (FIXP_compn f (S O)).
Qed.

Lemma FIXP_proj : forall (I:Type)(DI: I -> cpo) (F:Dprodi DI -c>Dprodi DI) (i:I) (fi : DI i -c> DI i),
                              (forall X : Dprodi DI, F X i == fi (X i)) -> FIXP (Dprodi DI) F i == FIXP (DI i) fi.
intros; apply Ole_antisym.
(* fix F i <= fix fi *)
rewrite FIXP_simpl.
rewrite Fixp_simpl.
unfold fixp.
rewrite Dprodi_lub_simpl.
apply lub_le .
induction n; auto.
rewrite fmon_comp_simpl.
rewrite (iterS_simpl (fcontit F)).
rewrite (Proj_simpl (O:=DI) i).
apply Ole_trans with (fi (iter (D:=Dprodi DI) (fcontit F) n i)).
case (H (iter (D:=Dprodi DI) (fcontit F) n)); trivial.
apply Ole_trans with (fi (FIXP (DI i) fi)); auto.
(* fix fi <= fix F i *)
apply FIXP_inv.
case (H (FIXP (Dprodi DI) F)); intros.
apply Ole_trans with (1:=H1).
case (FIXP_eq F); auto.
Qed.

(** *** Induction principle *)
Definition admissible (D:cpo)(P:D->Type) :=
          forall f : natO -m> D, (forall n, P (f n)) -> P (lub f).

Lemma fixp_ind : forall  (D:cpo)(F:D -m> D)(P:D->Type),
       admissible P -> P 0 -> (forall x, P x -> P (F x)) -> P (fixp F).
intros; unfold fixp.
apply X; intros.
induction n; simpl; auto.
Defined.

(** ** Directed complete partial orders without minimal element *)

Record dcpo : Type := mk_dcpo
  {tdcpo:>ord; dlub: (natO -m> tdcpo) -> tdcpo;
   le_dlub : forall (f : natO -m> tdcpo) (n:nat), f n <= dlub f;
   dlub_le : forall (f : natO -m> tdcpo) (x:tdcpo), (forall n, f n <= x) -> dlub f <= x}.

Global Hint Resolve le_dlub dlub_le : core.

Lemma dlub_le_compat : forall (D:dcpo)(f1 f2 : natO -m> D), f1 <= f2 -> dlub f1 <= dlub f2.
intros; apply dlub_le; intros.
apply Ole_trans with (f2 n); auto.
Qed.
Global Hint Resolve dlub_le_compat : core.

Lemma dlub_eq_compat : forall (D:dcpo)(f1 f2 : natO -m> D), f1 == f2 -> dlub f1 == dlub f2.
intros; apply Ole_antisym; auto.
Qed.
Global Hint Resolve dlub_eq_compat : core.

Lemma dlub_lift_right : forall (D:dcpo) (f:natO-m>D) n, dlub f == dlub (mseq_lift_right f n).
intros; apply Ole_antisym; auto.
apply dlub_le_compat; intro.
unfold mseq_lift_right; simpl.
apply (fmonotonic f); auto with arith.
Qed.
Global Hint Resolve dlub_lift_right : core.

Lemma dlub_cte : forall (D:dcpo) (c:D), dlub (mseq_cte c) == c.
intros; apply Ole_antisym; auto.
apply le_dlub with (f:=fmon_cte natO c) (n:=O); auto.
Qed.


(** *** A cpo is a dcpo *)

Definition cpo_dcpo : cpo -> dcpo.
intro D; exists D (lub (c:=D)); auto.
Defined.

(** ** Setoid type *)

Record setoid : Type := mk_setoid
  {tset:>Type; Seq:tset->tset->Prop; Seq_refl : forall x :tset, Seq x x;
   Seq_sym : forall x y:tset, Seq x y -> Seq y x;
   Seq_trans : forall x y z:tset, Seq x y -> Seq y z -> Seq x z}.

Global Hint Resolve Seq_refl : core.
Global Hint Immediate Seq_sym : core.

(** *** A setoid is an ordered set *)

Definition setoid_ord : setoid -> ord.
intro S; exists S (Seq (s:=S)); auto.
intros; apply Seq_trans with y; trivial.
Defined.

Definition ord_setoid : ord -> setoid.
intro O; exists O (Oeq (O:=O)); auto.
intros; apply Oeq_trans with y; trivial.
Defined.

(** *** A Type is an ordered set and a setoid with Leibniz equality *)

Definition type_ord (X:Type) : ord.
exists X (fun x y:X => x = y); intros; auto.
transitivity y; trivial.
Defined.

Definition type_setoid (X:Type) : setoid.
exists X (fun x y:X => x = y); intros; auto.
transitivity y; trivial.
Defined.

(** *** A setoid is a dcpo *)

Definition lub_eq (S:setoid) (f:natO-m>setoid_ord S) := f O.

Lemma le_lub_eq  : forall (S:setoid) (f:natO-m>setoid_ord S) (n:nat), f n <= lub_eq f.
intros; unfold lub_eq; simpl.
apply Seq_sym; apply (fmonotonic f); simpl; auto with arith.
Qed.

Lemma lub_eq_le  : forall (S:setoid) (f:natO-m>setoid_ord S)(x:setoid_ord S),
                (forall (n:nat), f n <= x) -> lub_eq f <= x.
intros; unfold lub_eq; simpl; intros.
exact (H O).
Qed.

Global Hint Resolve le_lub_eq lub_eq_le : core.

Definition setoid_dcpo : setoid -> dcpo.
intro S; exists (setoid_ord S) (lub_eq (S:=S)); intros; auto.
Defined.

(** Cpo of arrays seen as functions from nat to D with a bound n *)

Definition lek (O:ord) (k:nat) (f g : nat -> O) := forall n, n < k -> f n <= g n.
Global Hint Unfold lek : core.

Lemma lek_refl : forall (O:ord) k (f:nat -> O), lek k f f.
auto.
Qed.
Global Hint Resolve lek_refl : core.

Lemma lek_trans : forall (O:ord) (k:nat) (f g h: nat -> O), lek k f g -> lek k g h -> lek k f h.
red; intros.
apply Ole_trans with (g n); auto.
Qed.

Definition natk_ord : ord -> nat -> ord.
intros O k; exists (nat->O) (lek (O:=O) k); auto.
exact (lek_trans (O:=O) (k:=k)).
Defined.

Definition norm (O:ord) (x:O) (k:nat) (f: natk_ord O k) : natk_ord O k :=
        fun n => if le_lt_dec k n then x else f n.

Lemma norm_simpl_lt : forall (O:ord) (x:O) (k:nat) (f: natk_ord O k) (n:nat),
       n < k -> norm x f n = f n.
unfold norm; intros; case (le_lt_dec k n); auto.
intros; casetype False; lia.
Qed.

Lemma norm_simpl_le : forall (O:ord) (x:O) (k:nat) (f: natk_ord O k) (n:nat),
       (k <= n)%nat -> norm x f n = x.
unfold norm; intros; case (le_lt_dec k n); auto.
intros; casetype False; lia.
Qed.

Definition natk_mon_shift : forall (O1 O2 : ord)(x:O2) (k:nat),
         (O1 -m> natk_ord O2 k) -> natk_ord (O1 -m> O2) k.
intros O1 O2 x k f n; exists (fun (y:O1) => norm x (f y) n).
red; intros.
case (le_lt_dec k n); intro.
repeat rewrite norm_simpl_le; auto.
repeat rewrite norm_simpl_lt; auto.
apply (fmonotonic f H n); trivial.
Defined.

Lemma natk_mon_shift_simpl
     : forall (O1 O2 : ord)(x:O2) (k:nat)(f:O1 -m> natk_ord O2 k) (n:nat) (y:O1),
     natk_mon_shift x f n y = norm x (f y) n.
trivial.
Qed.

Definition natk_shift_mon : forall (O1 O2 : ord)(k:nat),
         (natk_ord (O1 -m> O2) k) -> O1 -m> natk_ord O2 k.
intros O1 O2 k f; exists (fun (y:O1) n => f n y).
red; intros; intros n H1.
apply (fmonotonic (f n)); auto.
Defined.

Lemma natk_shift_mon_simpl
     : forall (O1 O2 : ord)(k:nat)(f:natk_ord (O1 -m> O2) k) (x:O1)(n:nat),
     natk_shift_mon f x n = f n x.
trivial.
Qed.

Definition natk0 (D:cpo) (k:nat) : natk_ord D k := fun n : nat => (0:D).

Definition natklub (D:cpo) (k:nat) (h:natO-m>natk_ord D k) : natk_ord D k :=
                            fun n => lub (natk_mon_shift (0:D) h n).

Lemma natklub_less : forall (D:cpo) (k:nat) (h:natO-m>natk_ord D k) (n:nat),
                       h n <= natklub h.
simpl; red; unfold natklub; intros.
apply Ole_trans with (natk_mon_shift (O1:=natO) (O2:=D) 0 (k:=k) h n0 n); auto.
rewrite natk_mon_shift_simpl.
rewrite norm_simpl_lt; auto.
Qed.

Lemma natklub_least : forall (D:cpo) (k:nat) (h:natO-m>natk_ord D k) (p:natk_ord D k),
                       (forall n:nat, h n <= p) -> natklub h <= p.
simpl; red; unfold natklub; intros.
apply lub_le; intros.
rewrite natk_mon_shift_simpl.
rewrite norm_simpl_lt; auto.
apply (H n0 n H0).
Qed.

Definition Dnatk : forall (D:cpo) (k:nat), cpo.
intros; exists (natk_ord D k) (natk0 D k) (natklub (D:=D) (k:=k)).
unfold natk0; auto.
exact (natklub_less (D:=D) (k:=k)).
exact (natklub_least (D:=D) (k:=k)).
Defined.

Notation "k --> D" := (Dnatk D k) (at level 55, right associativity) : O_scope.

Definition natk_shift_cont : forall (D1 D2 : cpo)(k:nat),
         (k --> (D1-C->D2)) -> D1 -c> (k --> D2).
intros D1 D2 k f; exists (natk_shift_mon (k:=k) (fun n => fcontit (f n))).
red; intros; intros n H.
rewrite (natk_shift_mon_simpl (O1:=D1) (O2:=D2) (k:=k)).
simpl; unfold natklub.
apply Ole_trans with (lub (fcontit (f n) @ h)); auto.
apply lub_le_compat; intro m.
rewrite fmon_comp_simpl.
rewrite natk_mon_shift_simpl.
rewrite norm_simpl_lt; trivial.
Defined.

Lemma natk_shift_cont_simpl
     : forall (D1 D2:cpo)(k:nat)(f:k --> (D1-C->D2)) (n:nat) (x:D1),
     natk_shift_cont f x n = f n x.
trivial.
Qed.

Lemma natklub_simpl : forall (D:cpo) (k:nat) (h:natO -m> (k --> D)) (n:nat),
                    lub h n = lub (natk_mon_shift (0:D) h n).
trivial.
Qed.
