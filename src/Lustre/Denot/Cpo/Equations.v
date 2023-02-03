Require Export Arith.
Require Export Lia.

Set Implicit Arguments.

(** * Equations.v: Decision of equations between schemes *)

(** ** Markov rule *)

Definition dec (P:nat->Prop) := forall n, {P n} + {~ P n}.

Record Dec : Type := mk_Dec {prop :> nat -> Prop; is_dec : dec prop}.

Definition PS : Dec -> Dec.
intro P; exists (fun n => P (S n)).
intro n; exact (is_dec P (S n)).
Defined.

Definition ord (P Q:Dec) := forall n, Q n -> exists m, m < n /\ P m.

Lemma ord_eq_compat : forall (P1 P2 Q1 Q2:Dec),
        (forall n, P1 n -> P2 n) -> (forall n, Q2 n -> Q1 n)
     -> ord P1 Q1 -> ord P2 Q2.
red; intros.
case (H1 n); auto.
intros m (H3,H4); exists m; auto.
Qed.

Lemma ord_not_0 : forall P Q : Dec, ord P Q -> ~Q 0.
intros P Q H H1; case (H 0 H1); intros m (H2,H3); casetype False; lia.
Qed.

Lemma ord_0 : forall P Q : Dec, P 0 -> ~Q 0 -> ord P Q.
intros P Q H H1 n; exists 0; destruct n; intuition.
Qed.

(** - first elt of P then Q *)
Definition PP : Dec -> Dec -> Dec.
 intros P Q; exists (fun n => match n with O => P 0 | S p => Q p end).
intro n; case n.
apply (is_dec P 0).
intro p; apply (is_dec Q p).
Defined.


Lemma PP_PS : forall (P:Dec) n, PP P (PS P) n <-> P n.
intros; case n; simpl; intuition.
Qed.

Lemma PS_PP : forall (P Q:Dec) n, PS (PP P Q) n <-> Q n.
unfold PS,PP; simpl; intuition.
Qed.

Lemma ord_PS : forall P : Dec, ~ P 0 -> ord (PS P) P.
intros P H n Qn.
destruct n.
case H; trivial.
exists n; auto.
Qed.

Lemma ord_PP : forall (P Q: Dec), ~ P 0 -> ord Q (PP P Q).
intros P Q H n Qn.
destruct n.
case H; trivial.
exists n; auto.
Qed.

Lemma ord_PS_PS : forall P Q : Dec, ord P Q -> ~P 0 -> ord (PS P) (PS Q).
red; intros.
case (H (S n)); auto.
intros m Hm.
destruct m; intros.
case H0; intuition.
exists m; intuition.
Qed.

Lemma Acc_ord_equiv : forall P Q : Dec, (forall n, P n <-> Q n) -> Acc ord P -> Acc ord Q.
intros; destruct H0; intros.
apply Acc_intro; intros R HR.
apply H0.
apply ord_eq_compat with R Q; intuition.
case (H n); auto.
Qed.

Lemma Acc_ord_0 : forall P : Dec, P 0 -> Acc ord P.
intros; apply Acc_intro; intros Q H1.
case (ord_not_0 H1 H).
Qed.
Global Hint Immediate Acc_ord_0 : core.

Lemma Acc_ord_PP : forall (P Q:Dec), Acc ord Q -> Acc ord (PP P Q).
intros P Q H; generalize P; clear P; elim H; clear Q H.
intros Q AQ APP P.
apply Acc_intro; intros R H1.
case (is_dec R 0); intro.
auto.
apply Acc_ord_equiv with (PP R (PS R)).
exact (PP_PS R).
apply APP.
apply ord_eq_compat with (PS R) (PS (PP P Q)); auto.
apply ord_PS_PS; auto.
Qed.

Lemma Acc_ord_PS : forall (P:Dec), Acc ord (PS P) -> Acc ord P.
intros; apply Acc_ord_equiv with (PP P (PS P)).
exact (PP_PS P).
apply Acc_ord_PP; auto.
Qed.

Lemma Acc_ord : forall (P:Dec), (exists n,P n) -> Acc ord P.
intros P (n,H).
generalize P H; elim n; intros.
auto.
apply Acc_ord_PS; auto.
Qed.

Fixpoint min_acc (P:Dec) (a:Acc ord P) {struct a} : nat :=
             match is_dec P 0 with
                 left _ => 0 | right H => S (min_acc (Acc_inv a (PS P) (ord_PS P H))) end.

Definition minimize (P:Dec) (e:exists n, P n) : nat := min_acc (Acc_ord P e).

Lemma minimize_P : forall (P:Dec) (e:exists n, P n), P (minimize P e).
unfold minimize.
intros; elim (Acc_ord P e) using Acc_inv_dep.
intros Q H H1.
simpl.
case (is_dec Q 0); auto.
intro n; assert (H2:=H1 (PS Q) (ord_PS Q n)); auto.
Qed.

Lemma minimize_min : forall (P:Dec) (e:exists n, P n) (m:nat), m < minimize P e -> ~ P m.
unfold minimize.
intros P e; elim (Acc_ord P e) using Acc_inv_dep.
simpl; intros Q H1 H2 m.
case (is_dec Q 0).
red; intros; lia.
intro n; assert (H3:=H2 (PS Q) (ord_PS Q n)).
destruct m; intros; auto.
assert (H4:m < min_acc (H1 (PS Q) (ord_PS Q n))); try lia.
exact (H3 m H4).
Qed.

Lemma minimize_incr : forall (P Q:Dec)(e:exists n, P n)(f:exists n, Q n),
            (forall n, P n -> Q n) -> minimize Q f <= minimize P e.
intros; assert (~ minimize P e < minimize Q f); try lia.
red; intro; assert (~ Q (minimize P e)).
apply minimize_min with f; trivial.
apply H1; apply H; apply minimize_P.
Qed.

Require Export Cpo_def.

(** ** Definition of terms *)
Section Terms.

Variables F : Type.
Hypothesis decF : forall f g : F, {f=g}+{~f=g}.

Variable Ar : F -> nat.

Record ind (f:F) : Type := mk_ind {val :> nat ; val_less : val < Ar f}.

Inductive term : Type := X | Ap : F -> (nat -> term) -> term.

(* Implicit Arguments Ap []. *)

Inductive le_term : term -> term -> Prop :=
               le_X : forall t : term, le_term X t
           |   le_Ap : forall (f:F) (st1 st2: nat -> term),
                          (forall (i:nat), (i < Ar f) -> le_term (st1 i) (st2 i))
                         -> le_term (Ap f st1) (Ap f st2).
Hint Constructors le_term : core.

Lemma le_term_refl : forall t : term, le_term t t.
induction t; auto.
Qed.

Lemma le_term_trans : forall t1 t2 t3 : term, le_term t1 t2 -> le_term t2 t3 -> le_term t1 t3.
intros t1 t2 t3 H; generalize t3; clear t3; induction H; intros; auto.
inversion H1; auto.
Qed.

Lemma not_le_term_Ap_X : forall f st, ~ le_term (Ap f st) X.
red; intros; inversion H.
Qed.
Hint Resolve not_le_term_Ap_X : core.

Lemma not_le_term_Ap_diff : forall f g st1 st2, ~ f=g -> ~ le_term (Ap f st1) (Ap g st2).
red; intros; inversion H0; auto.
Qed.
Hint Resolve not_le_term_Ap_diff : core.

Lemma not_le_term_Ap_st : forall f st1 st2 (n:nat),
     n < Ar f -> ~ le_term (st1 n) (st2 n) -> ~ le_term (Ap f st1) (Ap f st2).
red; intros; inversion H1; auto.
Qed.

Lemma dec_finite : forall P:nat->Prop, dec P -> forall n,
            {forall i, i < n -> P i} + {exists i, i < n /\ ~P i}.
induction n.
left; intros; casetype False; lia.
case IHn; intro.
case (H n); intro.
left; intros; assert (i < n \/ i = n); try lia; intuition; subst; auto.
right; exists n; auto.
right; case e; intros i H1; exists i; intuition lia.
Defined.

Definition le_term_dec : forall t u, {le_term t u}+{~ le_term t u}.
induction t; auto.
destruct u; auto.
case (decF f f0); intro; auto; subst.
case (dec_finite (P:=fun n => le_term (t n) (t0 n))) with (n:=Ar f0).
red; auto.
auto.
intro; right.
case e; intros i H; apply not_le_term_Ap_st with i; intuition.
Defined.

Definition term_ord : ord.
exists term le_term.
exact le_term_refl.
exact le_term_trans.
Defined.

Fixpoint substX (t u:term_ord) {struct t} : term_ord :=
      match t with X => u | Ap f st => Ap f (fun i => substX (st i) u) end.

Lemma substX_le : forall (t u:term_ord), t <= substX t u.
induction t; simpl; intros; auto.
apply le_Ap; intros; auto.
apply (H i u).
Qed.

(** ** Interpretation of a term in cpo *)
Section InterpTerm.
Variable D : cpo.

Variable Finterp : forall f:F, (Ar f --> D) -c> D.

Fixpoint interp_term (t:term) : D -c> D :=
        match t with X => ID D
                        | Ap f st => Finterp f @_
                                            natk_shift_cont (fun i => interp_term (st i))
        end.

Lemma interp_term_X : forall x:D, interp_term X x=x.
trivial.
Qed.


Lemma interp_term_Ap : forall (f:F) (st : nat -> term) (x:D),
            interp_term (Ap f st) x = Finterp f (fun i => interp_term (st i) x).
trivial.
Qed.

Definition interp_equation (t:term) : D := FIXP D (interp_term t).

Lemma interp_equa_eq : forall (t:term), interp_equation t == interp_term t (interp_equation t).
intro t; exact (FIXP_eq  (interp_term t)).
Qed.

End InterpTerm.
Hint Resolve interp_term_X interp_term_Ap interp_equa_eq : core.

(** ** Construction of the universal domain for terms *)

Definition TU := natO -m> term_ord.

(** *** Order the universal domain *)

Definition TUle (T T' : TU) := forall n, exists m,  n<m /\ T n <= T' m.

Lemma TUle_refl : forall T : TU, TUle T T.
red; intros; exists (S n); auto.
Qed.

Lemma TUle_trans : forall T1 T2 T3 : TU, TUle T1 T2 -> TUle T2 T3 -> TUle T1 T3.
red; intros.
case (H n); intros m (H1,H1').
case (H0 m); intros p (H2,H2'); exists p.
split; try lia.
apply Ole_trans with (T2 m); auto.
Qed.

Definition TU_ord : ord.
exists TU TUle.
exact TUle_refl.
exact TUle_trans.
Defined.

(** *** Cpo structure for the universal domain *)

Definition TU0 : TU_ord := mseq_cte (X:term_ord).

Lemma TU0_less : forall T : TU_ord, TU0 <= T.
intros; simpl; red; intros.
exists (S n); auto.
Qed.

(** - find the smallest m greater than n such that T n <= T' m *)
Definition le_term_next : forall (T T' : TU_ord) (n:nat), Dec.
intros; exists (fun k => n<k /\ le_term (T n) (T' k)).
intro k.
case (le_lt_dec k n); intro.
intuition lia.
case  (le_term_dec (T n) (T' k)); intuition.
Defined.

Definition TUle_next (T T' : TU_ord)  (n:nat)  (p: T <= T'):= minimize (le_term_next T T' n) (p n).

Lemma TUle_next_le_term : forall (T T' : TU_ord) (p: T <= T') (n:nat),
             T n <= T' (TUle_next n p).
intros; unfold TUle_next.
case (minimize_P (le_term_next T T' n) (p n)); auto.
Qed.

Lemma TUle_next_le : forall (T T' : TU_ord) (p: T <= T') (n:nat),
             (n < TUle_next n p)%nat.
intros; unfold TUle_next.
case (minimize_P (le_term_next T T' n) (p n)); auto.
Qed.

Lemma TUle_next_incr : forall (T T' : TU_ord) (p q: T <= T') (n m:nat),
             (n <= m)%nat -> (TUle_next n p <= TUle_next m q)%nat.
intros; unfold TUle_next.
apply minimize_incr.
unfold le_term_next; simpl.
intuition eauto with arith.
apply le_term_trans with (T m); auto.
apply (fmonotonic T); auto.
Qed.

(** *** Definition of lubs in the universal domain *)
(**
     - lub T 0 = T 0 0,
     - lub T i = T i j with T k l <= lub T i for k <= i, l <= i,
     - i <= j, lub T i <= lub T (i+1)
*)

(** - find the apropriate index in T n starting from T 0 k *)
Fixpoint lub_index (T : natO-m>TU_ord) (k:nat) (n:nat) {struct n} : nat :=
             match n with O => k
               | S p => TUle_next (lub_index T k p) (fnatO_elim T p)
             end.

Lemma lub_index_S : forall (T : natO-m>TU_ord) (k:nat) (n:nat),
      lub_index T k (S n) = TUle_next (lub_index T k n) (fnatO_elim T n).
trivial.
Qed.

Lemma lub_index_incr : forall (T : natO-m>TU_ord) (k l:nat) (n:nat),
            (k <= l) % nat -> (lub_index T k n <= lub_index T l n)%nat.
induction n; simpl; intros; auto.
apply TUle_next_incr; auto.
Qed.
Hint Resolve lub_index_incr : core.

Lemma lub_index_le_term_S : forall (T : natO-m>TU_ord) (k:nat) (n:nat),
            T n (lub_index T k n) <= T (S n) (lub_index T k (S n)).
intros; rewrite lub_index_S.
apply TUle_next_le_term.
Qed.
Hint Resolve lub_index_le_term_S : core.

Lemma lub_index_le_term : forall (T : natO-m>TU_ord) (k:nat) (n m:nat),
            (n <= m)%nat -> T n (lub_index T k n) <= T m (lub_index T k m).
intros; elim H; intros; auto.
apply Ole_trans with (T m0 (lub_index T k m0)); auto.
Qed.
Hint Resolve lub_index_le_term : core.

Lemma lub_index_le : forall (T : natO-m>TU_ord) (k:nat) (n:nat),
                          (n+k <= lub_index T k n)%nat.
induction n; simpl; intros; auto with arith.
assert (Hm:=TUle_next_le (fnatO_elim T n) (lub_index T k n)); lia.
Qed.
Hint Resolve lub_index_le : core.

Definition TUlub : (natO-m>TU_ord) -> TU_ord.
intro T; apply (fnatO_intro (f:=fun n => T n (lub_index T n n))).
intro; apply Ole_trans with (T (S n) (lub_index T n (S n))); auto.
apply (fmonotonic (T (S n))).
apply (lub_index_incr T (k:=n) (l:=S n)  (S n)); auto.
Defined.

Lemma TUlub_simpl : forall T n, TUlub T n = T n (lub_index T n n).
trivial.
Qed.

Lemma TUlub_le_term : forall (T : natO-m>TU_ord) (k l n : nat),
    (k <= n)%nat -> (l<=n)%nat -> T k l <= TUlub T n.
intros; rewrite TUlub_simpl.
apply Ole_trans with (T k (lub_index T n k)); auto.
apply (fmonotonic (T k)); auto.
apply Ole_trans with n; auto.
apply Ole_trans with (k+n); auto with arith.
Qed.
Hint Resolve TUlub_le_term : core.

Lemma TUlub_less : forall T : natO-m>TU_ord, forall n, T n <= TUlub T.
intros.
intro m.
exists (S (n+m)); auto with arith.
Qed.

Lemma TUlub_least : forall (T : natO-m>TU_ord) (T':TU_ord),
               (forall n, T n <= T') -> TUlub T <= T'.
intros; intro n; rewrite TUlub_simpl.
case (H n (lub_index T n n)); intros m (H1,H2).
exists m; split; auto.
apply Nat.le_lt_trans with (lub_index T n n); auto.
apply Nat.le_trans with (n+n); auto with arith.
Qed.

(** *** Declaration of the cpo structure *)
Definition DTU : cpo.
exists TU_ord TU0 TUlub.
exact TU0_less.
exact TUlub_less.
exact TUlub_least.
Defined.


(** ** Interpretation of terms in the universal domain *)

Fixpoint maxk (f:nat -> nat) (k:nat) (def:nat) {struct k}: nat :=
       match k with O => def | S p => let m:=maxk f p def in
                                                      let a:= f p in
                                                      if le_lt_dec m a then a else m
       end.

Lemma maxk_le : forall (f:nat -> nat) (k:nat) (def:nat),
      forall p, p < k -> (f p <= maxk f k def)%nat.
induction k; simpl; intros.
absurd (p < 0); auto with arith.
assert (p < k \/ p = k); intuition (try lia); subst;
case (le_lt_dec (maxk f k def) (f k)); intros; auto with arith.
apply Nat.le_trans with (maxk f k def); auto.
Qed.

Lemma maxk_le_def : forall (f:nat -> nat) (k:nat) (def:nat),
     (def<= maxk f k def)%nat.
intros; induction k; simpl; intros; auto.
case (le_lt_dec (maxk f k def) (f k)); intros; auto with arith.
apply Nat.le_trans with (maxk f k def); auto.
Qed.


Definition TUcte (t:term) : DTU := mseq_cte (O:=term_ord) t.

Definition DTUAp : forall (f:F) (ST: Ar f --> DTU), DTU.
intros f ST; exists (fun n => Ap f (fun i => ST i n)).
red; intros.
apply le_Ap; intros.
apply (fmonotonic (ST i) H).
Defined.

Lemma DTUAp_simpl
   : forall (f:F) (ST: Ar f --> DTU)(n:nat), DTUAp ST n = Ap f (fun i => ST i n).
trivial.
Qed.

Definition DTUAp_mon : forall (f:F), (Ar f --> DTU) -m> DTU.
intro f; exists (DTUAp (f:=f)).
red; intros; intro n; simpl.
assert (exists m, n < m /\ forall p, p < Ar f -> x p n <= y p m).
generalize x y H; clear x y H; induction (Ar f); intros.
exists (S n); split; auto with arith; intros; absurd (p < 0); auto with arith.
case (IHn0 x y).
intros p Hp; apply (H p); auto with arith.
intros m (Hm1,Hm2).
case (H n0 (Nat.lt_succ_diag_r n0) n); intros m' (Hm'1,Hm'2).
exists (m+m'); split; auto with arith; intros.
assert (p < n0 \/ p = n0); try lia.
case H1; intros.
apply Ole_trans with (y p m); auto with arith.
subst p; apply Ole_trans with (y n0 m'); auto with arith.
case H0; intros m (H1,H2); exists m; auto.
Defined.

Lemma DTUAp_mon_simpl :
     forall (f:F) (ST: Ar f --> DTU)(n:nat), DTUAp_mon f ST n = Ap f (fun i => ST i n).
trivial.
Qed.

Definition TUAp : forall (f:F), (Ar f --> DTU) -c> DTU.
intro f; exists (DTUAp_mon f).
red; intros.
intro n; rewrite DTUAp_mon_simpl.
change
(exists m : nat,
  n < m /\
  le_term
  (Ap f (fun i : nat => norm 0 (h n) i (lub_index (natk_mon_shift 0 h i) n n)))
  (lub (c:=DTU) (DTUAp_mon f @ h) m)).
pose (m:= maxk (fun i => lub_index (natk_mon_shift 0 h i) n n) (Ar f) (S n)).
assert (S n <= m)%nat.
unfold m; apply maxk_le_def.
exists m; split; auto with arith.
apply le_term_trans with (Ap f (fun i => h n i m)).
apply le_Ap; intros.
rewrite norm_simpl_lt; trivial.
apply (fmonotonic (h n i)).
unfold m; apply (maxk_le (fun i : nat => lub_index (natk_mon_shift 0 h i) n n) (S n) (k:=Ar f) H0); auto.
(* second part of transitivity *)
apply (TUlub_le_term (DTUAp_mon f @ h) (k:=n) (l:=m) (n:=m)); auto with arith.
Qed.

Fixpoint DTUfix (T:term) (n:nat) {struct n}: term_ord
      := match n with O => X | S p => substX (DTUfix T p) T end.

Definition TUfix (T:term) : DTU.
    apply fnatO_intro with (DTUfix T); simpl; intro.
    apply substX_le.
Defined.

Lemma TUfix_simplS : forall  (T:term) n, TUfix T (S n) = substX (TUfix T n) T.
trivial.
Qed.

Lemma TUfix_simpl0 : forall  (T:term) , TUfix T O = X.
trivial.
Qed.

(*
Lemma TUfix_equa
    : forall (T:term), (interp_equation TUAp T : natO-m> term_ord) == TUfix T.
intro; apply fmon_eq_intro.
induction n; intros; auto.
apply Oeq_trans with (interp_term TUAp T (interp_equation TUAp T) (S n)).
apply fmon_eq_elim.
apply (interp_equa_eq TUAp T).
*)

End Terms.
