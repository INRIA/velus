Require Export Systems.
Require Export Cpo_nat.
Require Export Arith.
Require Export Euclid.

(** * Sieve.v: Example of Sieve of Eratosthenes *)

(** - sift (cons a s) == cons a (sift (filter (div a) s)) **)


(** ** Preliminaries on divisibility *)

Definition div (n m:nat) := exists q, m = q * n.

Lemma div0 : forall q n r, r=q * n -> r < n -> r = O.
intros; destruct q; auto.
simpl in H.
absurd (n <= r)%nat; try lia.
Qed.

Lemma div0bis : forall q q' n r, q * n = q' * n + r -> r < n -> r = O.
intros; assert (r= (q-q')*n).
assert (0<n).
apply Nat.le_lt_trans with r; auto with arith.
assert (~q * n < q' * n).
red; intro; try lia.
rewrite Nat.mul_sub_distr_r.
rewrite H; lia.
apply div0 with (q-q') n; auto.
Qed.

Definition div_dec : forall n m, {div n m}+ {~ div n m}.
intro; assert ({n=O}+{0<n}).
destruct n; auto with arith.
case H; intros.
subst n.
destruct m; intros.
left; exists O; simpl; auto with arith.
right; intros (q,H1).
absurd (S m = O); try lia.
case (modulo n l m); intros r H1.
assert (Hr:{r=O}+{0<r}).
destruct r; auto with arith.
case Hr; intro.
left; case H1; intros q (H2,H3); exists q; subst; auto with arith.
right; intro H2; case H2; intros q H3; case H1; intros q' (H4,H5).
absurd (r=O); try lia.
apply div0bis with q q' n; auto.
transitivity m; auto.
Qed.

(** ** Definition of the system  *)

(** - o = sift i is recursively defined by:  o = app i Y ;   Y = sift X;  X = fdiv i *)

Definition LI : Type := unit.
Definition i := tt.

Inductive LO : Type := X | Y | o.

Definition D := nat.

Definition SL : LI+LO -> Type := fun i => D.

(** *** Node corresponding to the division *)

Definition fdiv : DS D -c> DS D := DSCASE D D (fun a => FILTER (div a) (div_dec a)).

Lemma fdiv_cons : forall a s, fdiv (cons a s) = filter (div a) (div_dec a) s.
intros; unfold fdiv; rewrite DSCASE_simpl; rewrite DScase_cons; auto.
Qed.

(** *** Definition of the system parameterized by sift *)

Definition Funsift : (DS D -C-> DS D) -m> system SL.
exists (fun fs (x:LO) => match x with X => fdiv @_ PROJ (DS_fam SL) (inl LO i) 
                                                            |  Y => fs @_ PROJ (DS_fam SL) (inr LI X) 
                                                            |  o => (APP D @2_ PROJ (DS_fam SL) (inl LO i))
                                                                                       (PROJ (DS_fam SL) (inr LI Y))
              end).
red; intros f g Hfg; intro x.
case x; auto.
apply (fcont_le_intro (D1:=Dprodi (DS_fam SL)) (D2:=DS D)); intro P; 
repeat rewrite fcont_comp_simpl; auto.
Defined.

Lemma Funsift_simpl : forall fs x, Funsift fs x = match x with X => fdiv @_ PROJ (DS_fam SL) (inl LO i) 
                                                            |  Y => fs @_ PROJ (DS_fam SL) (inr LI X) 
                                                            |  o => (APP D @2_ PROJ (DS_fam SL) (inl LO i))
                                                                                       (PROJ (DS_fam SL) (inr LI Y))
              end.
trivial.
Qed.

Definition FunSift : (DS D -C-> DS D) -c> system SL.
exists Funsift; red; intros; intro x.
rewrite Funsift_simpl.
unfold system; rewrite Dprodi_lub_simpl.
apply (fcont_le_intro (D1:=DS_prod SL) (D2:=DS (inrSL SL x))); intro p.
rewrite fcont_lub_simpl.
case x; repeat rewrite fcont_comp_simpl.
eapply Ole_trans with (y := (Proj (fun x0 : LO => DS_prod SL -C-> DS (inrSL SL x0)) X @ (Funsift @ h) <__>
   p) O); trivial.
rewrite fcont_lub_simpl.
apply lub_le_compat; intro n; auto.
repeat rewrite fcont_comp2_simpl.
apply Ole_trans with (y:= (Proj (fun x0 : LO => DS_prod SL -C-> DS (inrSL SL x0)) o @ (Funsift @ h) <__>
   p) O); trivial.
Defined.

Lemma FunSift_simpl : forall fs x, FunSift fs x = match x with X => fdiv @_ PROJ (DS_fam SL) (inl LO i) 
                                                            |  Y => fs @_ PROJ (DS_fam SL) (inr LI X) 
                                                            |  o => (APP D @2_ PROJ (DS_fam SL) (inl LO i))
                                                                                       (PROJ (DS_fam SL) (inr LI Y))
              end.
trivial.
Qed.

(** - [focus] restrict to the input and output observed *)
Definition focus : (DS_prod (inlSL SL) -C-> DS_prod SL) -c> DS D -C-> DS D := 
     PROJ (DS_fam SL) (inr LI o) @@_ fcont_SEQ (DS D) (DS_prod (inlSL SL)) (DS_prod SL) (PAIR1 (DS D)).

Lemma focus_simpl : forall (f : DS_prod (inlSL SL) -C-> DS_prod SL) (s:DS D), 
    focus f s = f (pair1 s) (inr LI o).
trivial.
Qed.

(** *** Definition and properties of [sift] *)
Definition sift : DS D -C-> DS D := 
               FIXP (DS D -C->DS D) (focus @_ (sol_of_system SL @_ FunSift)).

Lemma sift_eq : sift == focus (sol_of_system SL (FunSift sift)).
exact (FIXP_eq (focus @_ (sol_of_system SL @_ FunSift))).
Qed.
Global Hint Resolve sift_eq : core.

Lemma sift_le_compat : forall x y, x <= y -> sift x <= sift y.
intros; apply fcont_monotonic; auto.
Qed.
Global Hint Resolve sift_le_compat : core.

Lemma sift_eq_compat : forall x y, x == y -> sift x == sift y.
intros; apply fcont_stable; auto.
Qed.
Global Hint Resolve sift_eq_compat : core.

Lemma sol_of_system_i : forall s : DS D, sol_of_system SL (FunSift sift) (pair1 s) (inl LO i) == s.
intro s; exact (Oprodi_eq_elim (sol_of_system_eq (FunSift sift) (pair1 s)) (inl LO i)).
Qed.

Lemma sol_of_system_X : forall s : DS D, 
            sol_of_system SL (FunSift sift) (pair1 s) (inr LI X) == fdiv s.
intro s; apply Oeq_trans with  (1:= Oprodi_eq_elim (sol_of_system_eq (FunSift sift) (pair1 s)) (inr LI X)).
simpl.
rewrite FunSift_simpl.
rewrite fcont_comp_simpl.
apply (fcont_stable fdiv).
exact (sol_of_system_i s).
Qed.

Lemma sol_of_system_Y : forall s : DS D, 
            sol_of_system SL (FunSift sift) (pair1 s) (inr LI Y) == sift (fdiv s).
intro s; apply Oeq_trans with  (1:=Oprodi_eq_elim (sol_of_system_eq (FunSift sift) (pair1 s)) (inr LI Y)).
simpl.
rewrite FunSift_simpl.
rewrite fcont_comp_simpl.
apply (fcont_stable sift).
exact (sol_of_system_X s).
Qed.

Lemma sol_of_system_o : forall s : DS D, 
            sol_of_system SL (FunSift sift) (pair1 s) (inr LI o) == app s (sift (fdiv s)).
intro s; apply Oeq_trans with  (1:=Oprodi_eq_elim (sol_of_system_eq (FunSift sift) (pair1 s)) (inr LI o)).
simpl.
rewrite FunSift_simpl.
rewrite fcont_comp2_simpl.
rewrite APP_simpl.
exact (app_eq_compat (sol_of_system_i s) (sol_of_system_Y s)).
Qed.

Lemma sift_prop : forall a s, sift (cons a s) == cons a (sift (filter (div a) (div_dec a) s)).
intros ; apply Oeq_trans with (1:=fcont_eq_elim sift_eq (cons a s)).
rewrite focus_simpl.
rewrite sol_of_system_o.
rewrite app_cons.
apply cons_eq_compat; trivial.
apply sift_eq_compat.
rewrite fdiv_cons; auto.
Qed.
