Require List.
Require Export Cpo_def.
Set Implicit Arguments.


(** * Cpo_streams_type.v: Domain of possibly infinite streams on a type *)

CoInductive DStr (D:Type) : Type
    := Eps : DStr D -> DStr D | Con : D -> DStr D -> DStr D.

Lemma DS_inv  : forall (D:Type) (d:DStr D),
   d = match d with Eps x => Eps x | Con a s => Con a s end.
destruct d; auto.
Qed.
Global Hint Resolve DS_inv : core.

(** - Extraction of a finite list from the n first constructors of a stream *)

Fixpoint DS_to_list (D:Type)(d:DStr D) (n : nat) {struct n}: List.list D :=
 match n with O => List.nil
                 | S p => match d with Eps d' => DS_to_list d' p
                                                 |  Con a d' => List.cons a (DS_to_list d' p)
                               end
 end.

(** ** Removing Eps steps *)
Definition pred (D:Type) d : DStr D := match d with Eps x => x | Con _ _ => d end.

Inductive isCon (D:Type) : DStr D -> Prop :=
            isConEps : forall x, isCon x -> isCon (Eps x)
          | isConCon : forall a s, isCon (Con a s).
Global Hint Constructors isCon : core.

Lemma isCon_pred : forall D (x:DStr D), isCon x -> isCon (pred x).
destruct 1; simpl; auto.
Qed.
Global Hint Resolve isCon_pred : core.

Definition isEps (D:Type) (x:DStr D) := match x with Eps _ => True | _ => False end.

(** Less general than isCon_pred but the result is a subterm of
      the argument (isCon x), used in uncons *)
Lemma isConEps_inv : forall D (x:DStr D), isCon x -> isEps x -> isCon (pred x).
destruct 1; simpl; intros.
assumption.
case H.
Defined.

Lemma isCon_intro : forall D (x:DStr D), isCon (pred x) -> isCon x.
destruct x; auto.
Qed.
Global Hint Resolve isCon_intro : core.

Fixpoint pred_nth D (x:DStr D) (n:nat) {struct n} : DStr D :=
             match n with 0 => x
                              | S m => pred_nth (pred x) m
             end.

Lemma pred_nth_switch : forall D k (x:DStr D), pred_nth (pred x) k = pred (pred_nth x k).
induction k; intros; simpl; auto.
Qed.
Global Hint Resolve pred_nth_switch  : core.

Lemma pred_nthS : forall D k (x:DStr D), pred_nth x (S k) = pred (pred_nth x k).
exact pred_nth_switch.
Qed.
Global Hint Resolve pred_nthS : core.

Lemma pred_nthCon : forall D a (s:DStr D) n, pred_nth (Con a s) n = (Con a s).
induction n; simpl; auto.
Qed.
Global Hint Resolve pred_nthCon : core.

Definition decomp D (a:D) (s x:DStr D) : Prop := exists k, pred_nth x k = Con a s.
Global Hint Unfold decomp : core.

Lemma decomp_isCon : forall D a (s x:DStr D), decomp a s x -> isCon x.
intros D a s x Hd; case Hd; intro k; generalize x; induction k; simpl; intros; auto.
subst x0; auto.
Qed.

Lemma decompCon : forall D a (s:DStr D), decomp a s (Con a s).
exists (0%nat); auto.
Qed.
Global Hint Resolve decompCon : core.

Lemma decompCon_eq :
    forall D a b (s t:DStr D), decomp a s (Con b t) -> Con a s = Con b t.
destruct 1.
transitivity (pred_nth (Con b t) x); auto.
Qed.
Global Hint Immediate decompCon_eq : core.

Lemma decompEps : forall D a (s x:DStr D), decomp a s x -> decomp a s (Eps x).
destruct 1.
exists (S x0); auto.
Qed.
Global Hint Resolve decompEps : core.


Lemma decompEps_pred : forall D a (s x:DStr D), decomp a s x -> decomp a s (pred x).
destruct 1; intros.
exists x0; auto.
transitivity (pred (pred_nth x x0)); auto.
rewrite H; auto.
Qed.

Lemma decompEps_pred_sym : forall D a (s x:DStr D), decomp a s (pred x) -> decomp a s x.
destruct x; simpl; intros; auto.
Qed.

Global Hint Immediate decompEps_pred_sym decompEps_pred : core.

Lemma decomp_ind : forall D a (s:DStr D) (P : DStr D-> Prop),
   (forall x, P x -> decomp a s x -> P (Eps x))
 -> P (Con a s) ->  forall x, decomp a s x -> P x.
intros D a s P HE HC x H; case H; intro n; generalize x H; clear x H.
induction n; simpl; intros.
subst; auto.
destruct x.
assert (decomp a s x); auto.
exact (decompEps_pred H).
simpl in H0; rewrite pred_nthCon in H0.
injection H0; intros; subst; auto.
Qed.

Lemma DStr_match : forall D (x:DStr D), {a:D & {s:DStr D | x = Con a s}}+{isEps x}.
intros D x; case x; simpl; auto; intros a s.
left; exists a; exists s; trivial.
Defined.

Lemma uncons : forall D (x:DStr D), isCon x ->{a:D & {s:DStr D| decomp a s x}}.
intro D. fix uncons 2; intros x ic.
case (DStr_match x); intros.
case s; clear s; intros a (s, eqx); exists a; exists s; subst x; auto.
case (uncons (pred x) (isConEps_inv ic i)); intros a (s,dx).
exists a; exists s; auto.
Defined.

(** ** Definition of the order *)
CoInductive DSle (D:Type) : DStr D -> DStr D -> Prop :=
                   DSleEps : forall x y,  DSle x y -> DSle (Eps x) y
                |  DSleCon : forall a s t y, decomp a t y -> DSle s t -> DSle (Con a s) y.

Global Hint Constructors DSle : core.

(** ** Properties of the order *)

Lemma DSle_pred_eq : forall D (x y:DStr D), forall n, x=pred_nth y n -> DSle x y.
intro D; cofix DSle_pred_eq; intros x y n.
case x; intros.
apply DSleEps; apply (DSle_pred_eq d y (S n)).
replace (pred_nth y (S n)) with (pred (pred_nth y n)).
rewrite <- H; trivial.
rewrite <- pred_nth_switch; auto.
apply DSleCon with d0.
exists n; auto.
auto.
apply (DSle_pred_eq d0 d0 (0%nat)); auto.
Qed.

Lemma DSle_refl : forall D (x:DStr D), DSle x x.
intros; apply (DSle_pred_eq (x:=x) x 0); auto.
Qed.
Global Hint Resolve DSle_refl : core.


Lemma DSle_pred_right  : forall D (x y:DStr D),  DSle x y -> DSle x (pred y).
intro D; cofix DSle_pred_right; intros x y H1; case H1; intros.
apply DSleEps.
apply DSle_pred_right; assumption.
apply DSleCon with t; auto.
Qed.

Lemma DSleEps_right_elim  : forall D (x y:DStr D),  DSle x (Eps y) -> DSle x y.
intros D x y H; exact (DSle_pred_right H).
Qed.

Lemma DSle_pred_right_elim : forall D (x y:DStr D),  DSle x (pred y) -> DSle x y.
cofix DSle_pred_right_elim; destruct x; simpl; intros.
apply DSleEps.
apply DSle_pred_right_elim; inversion H; assumption.
inversion H.
apply DSleCon with t; auto.
Qed.

Lemma DSle_pred_left  : forall D (x y:DStr D),  DSle x y -> DSle (pred x) y.
destruct 1; simpl; intros; trivial.
apply DSleCon with t; auto.
Qed.
Global Hint Resolve DSle_pred_left DSle_pred_right : core.

Lemma DSle_pred : forall D (x y:DStr D),  DSle x y -> DSle (pred x) (pred y).
auto.
Qed.
Global Hint Resolve DSle_pred : core.

Lemma DSle_pred_left_elim  : forall D (x y:DStr D),  DSle (pred x) y -> DSle x y.
intro D; cofix DSle_pred_left_elim; destruct x; simpl; intros; try assumption.
apply DSleEps; trivial.
Qed.

Lemma DSle_decomp : forall D a (s x y:DStr D),
   decomp a s x -> DSle x y -> exists t, decomp a t y /\ DSle s t.
intros D a s x y Hdx; case Hdx; intros k; generalize x; induction k; simpl; intros; auto.
simpl in H; rewrite H in H0; inversion H0.
exists t; auto.
case (IHk (pred x0)); auto.
intros t (Hd,Hle).
exists t; auto.
Qed.

Lemma DSle_trans : forall D (x y z:DStr D), DSle x y -> DSle y z -> DSle x z.
intro D; cofix DSle_trans; intros x y z H1; case H1; intros.
apply DSleEps.
apply DSle_trans with y0; assumption.
case (DSle_decomp H H2); intros u (He,Ht).
apply DSleCon with u; try assumption.
apply DSle_trans with t; trivial.
Qed.

(** *** Defintion of the ordered set *)
Definition DS_ord (D:Type) : ord := mk_ord (DSle_refl (D:=D)) (DSle_trans (D:=D)).

(** *** more Properties *)
Lemma DSleEps_right  : forall (D:Type) (x y : DS_ord D),  x <= y -> x <= Eps y.
intros; apply (DSle_pred_right_elim (x:=x) (Eps y)); auto.
Qed.
Global Hint Resolve DSleEps_right : core.

Lemma DSleEps_left : forall D (x y : DS_ord D),  x <= y -> (Eps x:DS_ord D) <= y.
intros; apply (DSle_pred_left_elim (Eps x) (y:=y)); auto.
Qed.
Global Hint Resolve DSleEps_left : core.

Lemma DSeq_pred : forall D (x:DS_ord D), x == pred x.
intros; apply Ole_antisym.
apply (DSle_pred_right (x:=x) (y:=x)); auto.
apply (DSle_pred_left (x:=x) (y:=x)); auto.
Qed.
Global Hint Resolve DSeq_pred : core.

Lemma pred_nth_eq : forall D n (x:DS_ord D),  x == pred_nth x n.
induction n; simpl; intros; auto.
apply Oeq_trans with (pred x); auto.
Qed.
Global Hint Resolve pred_nth_eq : core.

Lemma DSleCon0 :
     forall D a (s t:DS_ord D),  s <= t ->  (Con a s:DS_ord D) <= Con a t.
intros.
apply (DSleCon (a:=a) (s:=s) (t:=t) (y:=Con a t)); auto.
Qed.
Global Hint Resolve DSleCon0 : core.

Lemma Con_compat :
 forall D a (s t:DS_ord D), s == t ->  (Con a s:DS_ord D) == Con a t.
intros; apply Ole_antisym; auto.
Qed.
Global Hint Resolve Con_compat : core.


Lemma DSleCon_hd : forall (D:Type) a b (s t:DS_ord D),
     (Con a s:DS_ord D) <= Con b t-> a = b.
intros D a b s t H; inversion H.
assert (Con a t0=Con b t); auto.
injection H5; intros; subst; auto.
Qed.

Lemma Con_hd_simpl : forall D a b (s t : DS_ord D),  (Con a s:DS_ord D) == Con b t-> a = b.
intros; apply DSleCon_hd with s t; auto.
Qed.

Lemma DSleCon_tl : forall D a b (s t:DS_ord D), (Con a s:DS_ord D) <= Con b t -> (s:DS_ord D) <= t.
intros D a b s t H; inversion H.
assert (Con a t0=Con b t); auto.
injection H5; intros; subst; auto.
Qed.

Lemma Con_tl_simpl : forall D a b (s t:DS_ord D), (Con a s:DS_ord D) == Con b t -> (s:DS_ord D) == t.
intros; apply Ole_antisym.
apply DSleCon_tl with a b; auto.
apply DSleCon_tl with b a; auto.
Qed.

Lemma eqEps : forall D (x:DS_ord D), x == Eps x.
intros; apply Ole_antisym; auto.
Qed.
Global Hint Resolve eqEps : core.

Lemma decomp_eqCon : forall D a s (x:DS_ord D), decomp a s x -> x == Con a s.
intros D a s x Hdx; case Hdx; intro k; generalize x; induction k; auto.
intros; apply Oeq_trans with (pred x0); auto.
Qed.
Global Hint Immediate decomp_eqCon : core.

Lemma decomp_DSleCon : forall D a s (x:DS_ord D), decomp a s x -> x <= Con a s.
intros; case (decomp_eqCon H); auto.
Qed.

Lemma decomp_DSleCon_sym :
   forall D a s (x:DS_ord D), decomp a s x -> (Con a s:DS_ord D)<=x.
intros; case (decomp_eqCon H); auto.
Qed.
Global Hint Immediate decomp_DSleCon decomp_DSleCon_sym : core.

Lemma DSleCon_exists_decomp :
      forall D (x:DS_ord D) a (s:DS_ord D), (Con a s:DS_ord D) <= x
                   -> exists b, exists t, decomp b t x /\ a = b /\ s <= t.
intros D x a s H; inversion H; eauto.
Qed.

Lemma Con_exists_decompDSle :
      forall D (x:DS_ord D) a (s:DS_ord D),
      (exists t, decomp a t x /\ s <= t) -> (Con a s:DS_ord D) <= x.
intros D x a s (t,(H,H1)).
simpl; apply DSleCon with t; auto.
Qed.
Global Hint Immediate DSleCon_exists_decomp Con_exists_decompDSle : core.

Lemma DSle_isCon : forall D a (s x : DS_ord D), (Con a s : DS_ord D) <= x -> isCon x.
intros D a s x H; case (DSleCon_exists_decomp H); intros b (t,(H1,(H2,H3))); auto.
apply (decomp_isCon H1).
Qed.

Lemma DSle_uncons :
   forall D (x:DS_ord D) a (s:DS_ord D), (Con a s:DS_ord D) <= x
                   -> { t : DS_ord D | decomp a t x /\ s <= t}.
intros; case (@uncons D x); auto.
apply (DSle_isCon H).
intros b (t,Hd).
exists t.
assert ((Con a s : DS_ord D) <= Con b t).
apply Ole_trans with x; auto.
split; auto.
assert (a=b).
apply DSleCon_hd with s t; trivial.
rewrite H1; auto.
apply DSleCon_tl with a b; trivial.
Defined.

Lemma DSle_rec : forall D (R : DStr D -> DStr D -> Prop),
   (forall x y, R (Eps x) y -> R x y) ->
   (forall a s y, R (Con a s) y -> exists t, decomp a t y /\ R s t)
   -> forall x y : DS_ord D, R x y -> x <= y.
intros D R REps RCon; cofix DSle_rec; destruct x; intros.
simpl; apply DSleEps; apply DSle_rec; auto.
case (RCon d x y H); intros u (H1,H2); simpl; apply DSleCon with u; try assumption.
apply DSle_rec; assumption.
Qed.

Lemma isEps_Eps : forall D (x:DS_ord D), isEps (Eps x).
repeat red; auto.
Qed.

Lemma not_isEpsCon : forall D a (s:DS_ord D), ~ isEps (Con a s).
repeat red; auto.
Qed.
Global Hint Resolve isEps_Eps not_isEpsCon : core.

Lemma isCon_le : forall D (x y : DS_ord D), isCon x -> x <= y -> isCon y.
intros D x y H; generalize y; induction H; intros.
inversion_clear H0; auto.
inversion_clear H; auto.
apply decomp_isCon with a t; trivial.
Qed.

Lemma decomp_eq : forall D a (s x:DS_ord D),
     x == Con a s -> exists t, decomp a t x /\ s==t.
intros; assert ((Con a s :DS_ord D) <= x); auto.
inversion_clear H0.
exists t.
assert ((Con a t :DS_ord D) <= Con a s).
apply Ole_trans with x; auto.
split; auto.
split; auto.
apply (DSleCon_tl H0); auto.
Qed.

Lemma DSle_rec_eq : forall D (R : DStr D -> DStr D -> Prop),
   (forall x1 x2 y1 y2:DS_ord D, R x1 y1 -> x1==x2 -> y1==y2 -> R x2 y2) ->
   (forall a s (y:DS_ord D), R (Con a s) y -> exists t, y==Con a t /\ R s t)
   -> forall x y : DS_ord D, R x y -> x <= y.
intros D R Req RCon; cofix DSle_rec_eq; destruct x; intros.
simpl; apply DSleEps; apply DSle_rec_eq.
apply Req with (Eps x) y; auto.
case (RCon d x y H); intros u (H1,H2).
case (decomp_eq H1); intros u' (H4,H5).
simpl; apply DSleCon with u'; try assumption.
apply DSle_rec_eq.
apply Req with x u; auto.
Qed.

Lemma DSeq_rec : forall D (R : DStr D -> DStr D -> Prop),
   (forall x1 x2 y1 y2:DS_ord D, R x1 y1 -> x1==x2 -> y1==y2 -> R x2 y2) ->
   (forall a s (y:DS_ord D), R (Con a s) y -> exists t, y==Con a t /\ R s t)->
   (forall a s (x:DS_ord D), R x (Con a s) -> exists t, x==Con a t /\ R t s)
  -> forall x y : DS_ord D, R x y -> x == y.
intros; apply Ole_antisym.
apply DSle_rec_eq with R; auto; intros.
apply DSle_rec_eq with (R:=fun x y => R y x); intros; trivial.
apply H with y1 x1; auto.
case (H1 a s y0 H3); intros t (H4,H5); exists t; auto.
Qed.


(** ** Bottom is given by an infinite chain of Eps *)
CoFixpoint DS_bot (D:Type) : DS_ord D := Eps (DS_bot D).

Lemma DS_bot_eq (D:Type) : DS_bot D = Eps (DS_bot D).
transitivity match DS_bot D with Eps x => Eps x | Con a s => Con a s end; auto.
apply (DS_inv (DS_bot D)).
Qed.

Lemma DS_bot_least : forall D (x:DS_ord D), DS_bot D <= x.
intro D; cofix DS_bot_least; intro x.
rewrite DS_bot_eq; destruct x.
simpl; apply DSleEps; apply DS_bot_least.
simpl; apply DSleEps; apply DS_bot_least.
Qed.
Global Hint Resolve DS_bot_least : core.


(** ** Construction of least upper bounds *)

Lemma chain_tl : forall D (c:natO-m> DS_ord D), isCon (c O) -> natO -m> DS_ord D.
intros D c H.
assert (H':forall n, isCon (c n)).
intros; apply isCon_le with (c O); auto with arith.
exists (fun n => let (b,r) := uncons (H' n) in let (t,_) := r in t).
intros n m H1; case (uncons (H' n)); intros b (t,hn);
case (uncons (H' m)); intros d (u,hm).
assert ((Con b t : DS_ord D)<=Con d u).
apply Ole_trans with (c n); auto.
apply Ole_trans with (c m); auto.
apply (DSleCon_tl H0).
Defined.

Lemma chain_uncons :
   forall D (c:natO -m> DS_ord D), isCon (c O) ->
      {hd:D & {ctl : natO -m> DS_ord D | forall n, c n == Con hd (ctl n)}}.
intros D c H; case (uncons H); intros hd (tl,H1); exists hd; exists (chain_tl c H); intros.
unfold chain_tl; simpl.
case (uncons (isCon_le H (fmon_le_compat c (Nat.le_0_l n)))); intros.
case s; clear s; intros t H2; auto.
apply Oeq_trans with (Con x t); auto.
assert ((Con hd tl : DS_ord D) <= Con x t).
apply Ole_trans with (c O); auto.
apply Ole_trans with (c n); auto with arith.
assert (hd=x).
apply DSleCon_hd with tl t; trivial.
rewrite H3; apply Con_compat; auto.
Defined.

Lemma fCon : forall D (c:natO -m> DS_ord D) (n:nat),
            {hd: D &
            {tlc:natO -m> DS_ord D|
                 exists m, m < n /\ forall k, c (k+m) == Con hd (tlc k)}}
            + {forall k, k<n -> isEps (c k)}.
induction n.
right; intros; absurd (k<0); lia.
case IHn; clear IHn; intro.
case s; clear s; intros hdc (tlc,H).
left; exists hdc; exists tlc; case H; intro m; exists m; intuition.
case (DStr_match (c n)); intros.
case s; clear s; intros a (s,H); left.
assert (isCon (mseq_lift_left c n O)).
unfold mseq_lift_left; simpl.
replace (n+0) with n; auto with arith; rewrite H; auto.
case (chain_uncons (mseq_lift_left c n) H0); intros hdc (tlc, H1).
exists hdc; exists tlc; exists n; auto; intuition.
unfold mseq_lift_left in H1; simpl in H1.
replace (k+n) with (n+k); auto with arith.
right; intros.
assert (H0:(k<n \/ k=n)%nat); try lia.
case H0; intro; subst; auto with arith.
Defined.

(** ** Lubs on streams *)

Definition cpred D (c:natO -m> DS_ord D) : natO -m> DS_ord D.
exists (fun n => pred (c n)).
intros n m H; simpl; apply DSle_pred; auto.
apply (fmonotonic c H).
Defined.

CoFixpoint DS_lubn D (c:natO -m> DS_ord D) (n:nat) : DS_ord D :=
    match fCon c n with
      inleft (existT _ hd (exist _ tlc _)) => Con hd (DS_lubn tlc 2)
   |  inright _  => Eps (DS_lubn (cpred c) (S n))
    end.

(* XXX: starting at 2 instead of 1 leads to an equivalent stream with
  less Eps elements when c O == DS_bot *)
Definition DS_lub (D:Type) (c:natO -m> DS_ord D) := DS_lubn c 2.

Lemma DS_lubn_inv : forall D (c:natO -m> DS_ord D) (n:nat), DS_lubn c n =
     match fCon c n with
        inleft (existT _ hd (exist _ tlc _)) => Con hd (DS_lub tlc)
     |  inright _  => Eps (DS_lubn (cpred c) (S n))
    end.
intros; rewrite (DS_inv (DS_lubn c n)).
simpl; case (fCon c n); trivial.
destruct s; simpl.
destruct s; trivial.
Qed.

Lemma DS_lubn_pred_nth : forall D a (s:DS_ord D)  n k p (c:natO -m> DS_ord D),
   (n<k+p)%nat -> pred_nth (c n) k = Con a s ->
   exists d:natO -m> DS_ord D,
                 DS_lubn c p == Con a (DS_lub d) /\ (s:DS_ord D) <= d n.
intros D a s n k; pattern k; apply Wf_nat.lt_wf_ind; intros.
rewrite (DS_lubn_inv c p).
case (fCon c p); intros.
case s0; clear s0; intros hd (tlc,(m,(H2,H3))).
assert ((Con a s : DS_ord D) <= Con hd (tlc n)).
apply Ole_trans with (c (n+m)); auto.
rewrite <- H1; apply Ole_trans with (c n); auto with arith.
exists tlc; split; auto.
assert (Heq:=DSleCon_hd H4).
rewrite Heq; apply Con_compat; auto.
apply DSleCon_tl with a hd; auto.
destruct n0; simpl pred_nth in *|-*.
absurd (isEps (c n)); auto.
rewrite H1; auto.
case (H n0) with  (p:=S p) (c:=cpred c); auto; try lia.
intros d (H2,H3); exists d; split; auto.
apply Oeq_trans with (DS_lubn (cpred c) (S p)); auto.
Qed.

Lemma DS_lubn_pred_nth_inv : forall D a (s:DS_ord D) k p (c:natO -m> DS_ord D),
   pred_nth (DS_lubn c p) k = Con a s ->
   exists tlc :natO -m> DS_ord D, s= DS_lub tlc /\ exists m, forall l, c (l+m) == Con a (tlc l).
intros D a s k; pattern k; apply Wf_nat.lt_wf_ind; clear k; intros n IH p c.
rewrite (DS_lubn_inv c p).
case (fCon c p).
intros (hdc,(tlc,(m,(H2,H3)))) H.
exists tlc.
assert (Heq:Con hdc (DS_lub tlc)=Con a s).
transitivity (pred_nth (Con hdc (DS_lub tlc)) n); auto.
injection Heq; auto.
intros; subst; repeat split; auto.
exists m; auto.
destruct n; simpl pred_nth; intros.
discriminate H.
case (IH n) with (p:=S p) (c:=cpred c); auto with arith; clear IH.
intros tlc (H1,(m,H3)).
exists tlc; split; auto.
exists m; intro l; apply Oeq_trans with (cpred c (l + m)); auto.
unfold cpred; simpl; auto.
Qed.

Lemma DS_lubCon_inv : forall D a (s:DS_ord D) (c:natO -m> DS_ord D),
   (DS_lub c == Con a s) ->
   exists tlc :natO -m> DS_ord D,
           s==DS_lub tlc  /\ exists m, forall l, c (l+m) == Con a (tlc l).
intros; case (decomp_eq H); intros t (H1,H2).
case H1; intros k H4.
case (@DS_lubn_pred_nth_inv D a t k 2 c H4); intros tlc (H5,(m,H7)).
exists tlc; split; subst; auto.
exists m; intros.
apply Oeq_trans with (Con a (tlc l)); auto.
Qed.


Lemma DS_lubCon : forall D a s n (c:natO -m> DS_ord D),
   (Con a s :DS_ord D) <= c n ->
   exists d:natO -m> DS_ord D,
             DS_lub c == Con a (DS_lub d)  /\ (s:DS_ord D) <= d n.
intros D a s n c H; inversion_clear H.
case H0; intros k H3.
case (@DS_lubn_pred_nth D a t n (n+k) 2 c); auto; try lia.
pattern n at 2; elim n; intros; simpl; auto.
transitivity (pred (pred_nth (c n) (n0 + k))); auto.
rewrite H; auto.
intros d (H4,H5).
exists d; split; eauto.
Qed.

Lemma DS_lub_upper : forall D (c:natO -m> DS_ord D), forall n, c n <= DS_lub c.
intros; apply DSle_rec_eq
  with (R:= fun x y:DS_ord D =>exists c:natO -m> DS_ord D, x<=c n /\ y==DS_lub c); intuition.
clear c; case H; intros c (H2,H3); exists c; split.
apply Ole_trans with x1; auto.
apply Oeq_trans with y1; auto.
clear c; case H; clear H; intros c (H1,H2).
case (DS_lubCon n c H1); intros d (H3,H4).
assert (H6:(y:DS_ord D)==Con a (DS_lub d)).
apply Oeq_trans with (DS_lub c); trivial.
exists (DS_lub d); split; auto.
exists d; auto.
exists c; auto.
Qed.

Lemma DS_lub_least : forall D (c:natO -m> DS_ord D) x,
                      (forall n, c n <= x) -> DS_lub c <= x.
intros; apply DSle_rec_eq
  with (R:= fun x y: DS_ord D=>exists c, x==DS_lub c /\ forall n, c n <= y); intros.
case H0; intros d (H3,H4); exists d; split; eauto.
case H0; intros d (H3,H4).
assert (H5:(Con a s:DS_ord D) <= DS_lub d); auto.
inversion_clear H5.
case (@DS_lubCon_inv D a s d); auto; intros tlc (H7,(m,H9)).
assert ((Con a (tlc O) :DS_ord D) <= y).
apply Ole_trans with (d (0+m)); auto.
inversion_clear H5.
assert (y==Con a t0); auto.
exists t0; split; auto.
assert (forall l, (Con a (tlc l): DS_ord D) <= Con a t0).
intro; apply Ole_trans with (d (l+m)); auto.
apply Ole_trans with y; auto.
exists tlc; split; auto; intros.
apply DSleCon_tl with a a; auto.
exists c; auto.
Qed.

(** ** Definition of the cpo of streams *)
Definition DS : Type -> cpo.
intro D; exists (DS_ord D) (DS_bot D) (DS_lub (D:=D)); auto.
exact (DS_lub_upper (D:=D)).
exact (DS_lub_least (D:=D)).
Defined.

Lemma DS_lub_inv : forall D (c:natO -m> DS D), lub c =
     match fCon c 2 with
        inleft (existT _ hd (exist _ tlc _)) => Con hd (lub (c:=DS D) tlc)
     |  inright _  => Eps (DS_lubn (cpred c) 3)
    end.
intros D c; exact (DS_lubn_inv c 2).
Qed.

Definition cons D (a : D) (s: DS D) : DS D := Con a s.

Lemma cons_le_compat :
     forall D a b (s t:DS D), a = b -> s <= t ->  cons a s <= cons b t.
intros; simpl; unfold cons; rewrite H; apply DSleCon0; auto.
Qed.
Global Hint Resolve cons_le_compat : core.

Lemma cons_eq_compat :
 forall D a b (s t:DS D), a = b -> s == t ->  cons a s == cons b t.
intros; apply Ole_antisym; auto.
Qed.
Global Hint Resolve cons_eq_compat : core.

Add Parametric Morphism D : (@cons D)
    with signature eq ==> (@Oeq (DS D)) ==> (@Oeq (DS D)) as cons_eq_compat_morph.
  intros; apply cons_eq_compat; auto.
Qed.

Lemma not_le_consBot: forall D a (s:DS D), ~ cons a s <= 0.
intros D a s H.
inversion_clear H.
case H0; intros.
induction x; auto.
simpl in H.
rewrite DS_bot_eq in H.
discriminate H.
Qed.
Global Hint Resolve not_le_consBot : core.


Lemma DSle_intro_cons :
       forall D (x y:DS D), (forall a s, x==cons a s -> cons a s <= y) -> x <= y.
intros; simpl; apply DSle_rec_eq with
    (R:= fun (x y :DS D) => forall a s, x==cons a s -> cons a s <= y); auto; intros.
apply Ole_trans with y1; auto.
apply (H0 a s); auto.
apply Oeq_trans with x2; auto.
assert (cons a s <= y0); eauto.
inversion_clear H1.
exists t; split; intros; auto.
apply Ole_trans with s; auto.
Qed.

Definition is_cons D (x:DS D) := isCon x.

Lemma is_cons_intro : forall D (a:D) (s:DS D), is_cons (cons a s).
red; unfold cons; auto.
Qed.
Global Hint Resolve is_cons_intro : core.

Lemma is_cons_elim : forall D (x:DS D), is_cons x -> exists a, exists s : DS D, x == cons a s.
intros; elim (uncons H); intros a (s,H1).
exists a; exists s.
unfold cons; simpl; auto.
Qed.

Lemma not_is_consBot : forall D, ~ is_cons (0:DS D).
red; intros.
case (is_cons_elim H); intros a (s,Heq).
apply (not_le_consBot (a:=a) (s:=s)); auto.
Qed.
Global Hint Resolve not_is_consBot : core.

Lemma is_cons_le_compat : forall D (x y:DS D), x <= y -> is_cons x -> is_cons y.
intros; unfold is_cons; simpl; apply isCon_le with x; auto.
Qed.

Lemma is_cons_eq_compat : forall D (x y:DS D), x == y -> is_cons x -> is_cons y.
intros; apply is_cons_le_compat with x; auto.
Qed.

Lemma DSle_intro_is_cons : forall D (x y:DS D), (is_cons x -> x <= y) -> x <= y.
intros; apply DSle_intro_cons; intros.
apply Ole_trans with x; auto.
apply H; apply is_cons_eq_compat with (cons a s); auto.
Qed.

Lemma DSeq_intro_is_cons : forall D (x y:DS D),
             (is_cons x -> x <= y) -> (is_cons y -> y <= x) -> x == y.
intros; apply Ole_antisym; apply DSle_intro_is_cons; auto.
Qed.

Add Parametric Morphism D : (@is_cons D)
with signature (@Oeq (DS D)) ==> iff as is_cons_eq_iff.
intros x y; split; intro.
apply is_cons_eq_compat with x; auto.
apply is_cons_eq_compat with y; auto.
Qed.

Add Parametric Morphism D : (@cons D)
with signature eq ==> (@Ole (DS D)) ++> (@Ole (DS D)) as cons_le_morph.
intros; apply (cons_le_compat (D:=D)); trivial.
Qed.

Global Hint Resolve cons_le_morph : core.

(** ** Basic functions *)

Section Simple_functions.

(** *** Build a function F such that F (Con a s) = f a s and F (Eps x) = Eps (F x) *)

Variable D D': Type.
Variable f : D -> DS D -m> DS D'.

CoFixpoint DScase  (s:DS D) : DS D':=
    match s with Eps x => Eps (DScase x) | Con a l => f a l end.

Lemma DScase_inv :
   forall (s:DS D), DScase s = match s with Eps l => Eps (DScase l)  | Con a l =>  f a l end.
intros; rewrite (DS_inv (DScase s)); simpl; auto.
Qed.

Lemma DScaseEps : forall (s:DS D), DScase (Eps s) = Eps (DScase s).
intros; rewrite (DScase_inv (Eps s)); trivial.
Qed.

Lemma DScase_cons : forall a (s:DS D), DScase (cons a s) = f a s.
intros; rewrite (DScase_inv (cons a s)); trivial.
Qed.
Hint Resolve DScaseEps DScase_cons : core.

Lemma DScase_decomp : forall a (s x:DS D), decomp a s x ->  DScase x == f a s.
intros a s x Hd.
pattern x; apply decomp_ind with (3:=Hd); intros; auto.
rewrite DScaseEps; auto.
apply Oeq_trans with (DScase x0); simpl; auto.
Qed.

Lemma DScase_eq_cons : forall a (s x:DS D), x == cons a s -> DScase x == f a s.
intros; elim (decomp_eq H); intros t (H1,H2).
apply Oeq_trans with (f a t).
apply DScase_decomp; auto.
apply (fmon_stable (f a)); auto.
Qed.
Hint Resolve DScase_eq_cons : core.

Lemma DScase_bot : DScase 0 <= 0.
cofix DScase_bot; simpl.
pattern (DS_bot D) at 1; rewrite DS_bot_eq.
rewrite DScaseEps.
apply DSleEps; trivial.
Qed.

Lemma DScase_le_cons : forall a (s x:DS D), cons a s <= x -> f a s <= DScase x.
intros a s x H; inversion H.
apply Ole_trans with (f a t).
apply (fmonotonic (f a)); auto.
case (DScase_decomp H2); auto.
Qed.

Lemma DScase_le_compat : forall (s t:DS D), s <= t -> DScase s <= DScase t.
cofix DScase_le_compat.
intros s t H; rewrite (DScase_inv s); case H; intros.
simpl; apply DSleEps.
apply DScase_le_compat; trivial.
apply Ole_trans with (f a t0); auto.
pattern y; apply decomp_ind with (3:=H0); auto; intros.
rewrite DScaseEps.
apply Ole_trans with (DScase x).
exact H2.
simpl; apply DSleEps_right.
simpl; apply DSle_refl.
Qed.
Hint Resolve DScase_le_compat : core.

Lemma DScase_eq_compat : forall (s t:DS D), s == t -> DScase s == DScase t.
intros; apply Ole_antisym; auto.
Qed.
Hint Resolve DScase_eq_compat : core.

Add Parametric Morphism : DScase
with signature (@Oeq (DS D)) ==> (@Oeq (DS D')) as DScase_eq_compat_morph.
exact DScase_eq_compat.
Qed.

Definition DSCase : DS D -m> DS D'.
exists DScase; red; auto.
Defined.

Lemma DSCase_simpl : forall (s:DS D), DSCase s = DScase s.
trivial.
Qed.

Lemma DScase_decomp_elim : forall a (s:DS D') (x:DS D),
   decomp a s (DScase x) -> exists b, exists t, x==cons b t /\ f b t == Con a s.
intros a s x H; case H; clear H.
intro k; generalize x; clear x; pattern k; apply Wf_nat.lt_wf_ind; intros.
rewrite DScase_inv in H0; destruct x.
destruct n; simpl in H0.
discriminate H0.
case (H n) with (2:=H0); auto.
intros b (t,(H1,H2)).
exists b; exists t; split; auto.
apply Oeq_trans with x; auto.
apply Oeq_sym; apply (eqEps x).
exists d; exists x; split; auto.
rewrite <- H0; simpl; auto.
Qed.

Lemma DScase_eq_cons_elim : forall a (s : DS D') (x:DS D),
   DScase x == cons a s -> exists b, exists t, x==cons b t /\ f b t == cons a s.
intros a s x H; case (decomp_eq H); intros t (H1,H2).
case (DScase_decomp_elim x H1); intros c (u,(H4,H5)).
exists c; exists u; split; auto.
apply Oeq_trans with (cons a t); simpl; auto.
Qed.

Lemma DScase_is_cons : forall (x:DS D), is_cons (DScase x) -> is_cons x.
intros; case (is_cons_elim H); intros a (s,H1).
case (DScase_eq_cons_elim x H1); intros b (t,(H2,H3)).
red; apply DSle_isCon with b t; auto.
Qed.

Lemma is_cons_DScase : (forall a (s:DS D), is_cons (f a s)) -> forall (x:DS D), is_cons x -> is_cons (DScase x).
intros; case (is_cons_elim H0); intros a (s,H1).
apply is_cons_eq_compat with (f a s); auto.
rewrite H1; auto.
Qed.

Hypothesis fcont : forall c, continuous (f c).

Lemma DScase_cont : continuous DSCase.
red; intros; rewrite DSCase_simpl; apply DSle_intro_cons; intros.
case (DScase_eq_cons_elim (a:=a) (s:=s) (lub h)); auto; intros b (t,(H3,H4)).
case (DS_lubCon_inv h H3).
intros tlc (H5,(m,H6)).
apply Ole_trans with (f b t); auto.
apply Ole_trans with (f b (lub (c:=DS D) tlc)); auto.
apply Ole_trans with (lub (f b @ tlc)); auto.
(* simpl; apply (fcont b). *)
rewrite (lub_lift_right (DSCase @ h) m); auto.
apply (lub_le_compat (D:=DS D')).
unfold mseq_lift_right; simpl; intros.
apply DScase_le_cons; unfold cons; auto.
Qed.
Hint Resolve DScase_cont : core.

Lemma DScase_cont_eq : forall (c:natO-m>DS D), DScase (lub c) == lub (DSCase @ c).
intros; apply lub_comp_eq with (f:=DSCase); auto.
Qed.

End Simple_functions.

Global Hint Resolve DScaseEps DScase_cons DScase_le_compat DScase_eq_compat DScase_bot DScase_cont : core.

Definition DSCASE_mon : forall D D', (D-O->(DS D -M-> DS D')) -M-> DS D -M-> DS D'.
intros D D'; exists (DSCase (D:=D)(D':=D')); red; intros f g Hle; intro s.
repeat (rewrite DSCase_simpl).
simpl; apply DSle_intro_cons; intros.
case (DScase_eq_cons_elim f (a:=a) (s:=s0) s); auto; intros b (t,(Hs,Hf)).
assert (DScase g s == g b t).
apply (DScase_eq_cons g Hs).
apply Ole_trans with (f b t); auto.
apply Ole_trans with (g b t); auto.
Defined.

Lemma DSCASE_mon_simpl : forall D D' f s, DSCASE_mon D D' f s = DScase f s.
trivial.
Qed.

Lemma DSCASE_mon_cont : forall D D', continuous (DSCASE_mon D D').
red; intros; intro s; rewrite (DSCASE_mon_simpl (D:=D) (D':=D')).
apply DSle_intro_cons; intros.
case (DScase_eq_cons_elim  (lub h) (a:=a) (s:=s0) s);
         auto; intros b (t,(Hs,Hf)).
rewrite fmon_lub_simpl.
apply Ole_trans with (lub ((h <o> b) <_> t)); auto.
apply (lub_le_compat (D:=DS D')); intro n.
repeat (rewrite fmon_app_simpl); rewrite fmon_comp_simpl.
rewrite DSCASE_mon_simpl.
rewrite (DScase_eq_cons (h n) Hs); auto.
Qed.

Definition DSCASE_cont : forall D D', (D-O->(DS D -C-> DS D')) -m> (DS D -C-> DS D').
intros D D'.
exists (fun f => mk_fconti (DScase_cont (D:=D) (D':=D') (fun a => fcontit (f a)) (fun a => fcontinuous (f a)))).
intros f g Hle; intro s;simpl.
apply DSle_intro_cons; intros.
case (DScase_eq_cons_elim (fun a : D => fcontit (f a)) (a:=a) (s:=s0) s); auto; intros b (t,(Hs,Hf)).
assert (DScase (fun a0 => fcontit (g a0)) s == g b t).
apply (DScase_eq_cons (fun a0 => fcontit (g a0)) Hs).
apply Ole_trans with (f b t); auto.
apply Ole_trans with (g b t); auto.
apply (fcont_le_elim (Hle b)).
Defined.

Lemma DSCASE_cont_simpl : forall D D' f s,
        DSCASE_cont D D' f s = DScase (fun a => fcontit (f a)) s.
trivial.
Qed.

Definition DSCASE : forall D D', (D-O->DS D -C->DS D')-c> DS D -C->DS D'.
intros; exists (DSCASE_cont D D').
red; intros; intro s.
change (DSCASE_cont D D' (lub h) s <= lub (DSCASE_cont D D' @ h) s).
rewrite DSCASE_cont_simpl.
apply DSle_intro_cons; intros.
case (DScase_eq_cons_elim  (fun a : D => fcontit ((lub h) a)) (a:=a) (s:=s0) s); auto; intros b (t,(Hs,Hf)).
rewrite fcont_lub_simpl.
apply Ole_trans with (lub ((h <o> b) <__> t)); auto.
apply (lub_le_compat (D:=DS D')); intro n.
repeat (rewrite fcont_app_simpl).
rewrite fmon_comp_simpl.
rewrite DSCASE_cont_simpl.
rewrite (DScase_eq_cons (fun a0 : D => fcontit (h n a0)) Hs); auto.
Defined.

Lemma DSCASE_simpl : forall D D' f s, DSCASE D D' f s = DScase (fun a => fcontit (f a)) s.
trivial.
Qed.

(** ** Basic functions on streams *)

(** - Cons is continuous *)

Definition Cons (D:Type): D -o> DS D -m> DS D.
intro b; exists (cons b).
red; intros; auto.
Defined.

Lemma Cons_simpl : forall D (a : D) (s : DS D), Cons a s = cons a s.
trivial.
Qed.

Lemma Cons_cont : forall D (a : D), continuous (Cons a).
red; intros D a h.
case (DS_lubCon (a:=a) (s:=h O) O (Cons a @ h)); trivial.
intros d (H1,H2).
case (DS_lubCon_inv (Cons a @ h) H1).
intros tlc (H4,H5).
apply Ole_trans with (cons a (lub (c:=DS D) d)); auto.
case H5; clear H5; intros m H5.
rewrite Cons_simpl; apply cons_le_compat; trivial.
rewrite H4.
assert (forall l : nat, h (l + m) == tlc l).
intro l; simpl; apply Con_tl_simpl with a a.
apply (H5 l).
rewrite (lub_lift_right h m).
apply (lub_le_compat (D:=DS D)  (f:=mseq_lift_right (O:=DS D) h m) (g:=tlc)); intro n; simpl.
case (H n); auto.
Qed.
Global Hint Resolve Cons_cont : core.

Definition CONS D (a : D) : DS D -c> DS D := mk_fconti (Cons_cont a).

Lemma CONS_simpl : forall D (a : D) (s : DS D), CONS a s = cons a s.
trivial.
Qed.

(** - first takes a stream and return the stream with only the first element
        f a s = cons a nil
*)

Definition firstf (D:Type) : D -> DS D -m>DS D:=
fun (d:D) => fmon_cte (DS D) (O2:=DS D) (cons d (0:DS D)).

Lemma firstf_simpl : forall D (a:D) (s:DS D), firstf a s = cons a (0:DS D).
trivial.
Qed.

Lemma firstf_cont : forall D (a:D) c, firstf a (lub c) <= lub (firstf a @ c).
intros; rewrite firstf_simpl.
unfold firstf.
apply Ole_trans with (lub (c:=DS D) (fmon_cte natO (O2:=DS D) (cons a (0 : DS D)))); auto.
Qed.
Global Hint Resolve firstf_cont : core.

Definition First (D:Type) : DS D -m> DS D := DSCase (firstf (D:=D)).

Definition first D (s:DS D) := First D s.

Lemma first_simpl : forall D (s:DS D), first s = DScase (firstf (D:=D)) s.
trivial.
Qed.

Lemma first_le_compat : forall D (s t:DS D), s <= t -> first s <= first t.
unfold first; auto.
Qed.
Global Hint Resolve first_le_compat : core.

Lemma first_eq_compat : forall D (s t:DS D), s == t -> first s == first t.
intros; apply Ole_antisym; auto.
Qed.
Global Hint Resolve first_eq_compat : core.

Lemma first_cons : forall D a (s:DS D), first (cons a s) = cons a (0:DS D).
intros; rewrite first_simpl; intros.
rewrite DScase_cons; trivial.
Qed.

Lemma first_bot : forall D, first (D:=D) 0 <= 0.
intros; rewrite first_simpl; auto.
Qed.

Lemma first_cons_elim : forall D a (s t:DS D),
    first t == cons a s -> exists u, t == cons a u /\ s==(0:DS D).
intros D a s t; rewrite first_simpl; intros.
case (DScase_eq_cons_elim (firstf (D:=D)) t H).
intros b (u,(H1,H2)).
exists u.
assert (b=a).
apply (Con_hd_simpl H2).
assert ((0:DS D) ==s).
apply (Con_tl_simpl H2).
split; auto.
apply Oeq_trans with (1:=H1); auto.
Qed.

Add Parametric Morphism D : (@first D)
with signature (@Oeq (DS D)) ==> (@Oeq (DS D)) as first_eq_compat_morph.
exact (@first_eq_compat D).
Qed.

Add Parametric Morphism D : (@first D)
with signature (@Ole (DS D)) ++> (@Ole (DS D)) as first_le_compat_morph.
exact (@first_le_compat D).
Qed.

Lemma is_cons_first : forall D (s:DS D), is_cons s -> is_cons (first s).
unfold first, First; intros.
rewrite DSCase_simpl; apply is_cons_DScase; auto.
intros; unfold firstf; simpl; auto.
Qed.
Global Hint Resolve is_cons_first : core.

Lemma first_is_cons : forall D (s:DS D), is_cons (first s) -> is_cons s.
unfold first, First; intros.
apply DScase_is_cons with D (firstf (D:=D)); auto.
Qed.
Global Hint Immediate first_is_cons : core.

Lemma first_cont : forall D, continuous (First D).
intro; unfold First; apply DScase_cont; intros.
exact (firstf_cont c).
Qed.
Global Hint Resolve first_cont : core.

Definition FIRST (D:Type) : DS D -c> DS D.
exists (First D); auto.
Defined.

Lemma FIRST_simpl : forall D s, FIRST D s = first s.
trivial.
Qed.

(** - rem returns the stream without the first element *)

Definition remf D (d: D) : DS D -m> DS D := fmon_id (DS D).

Lemma remf_simpl : forall D (a:D) s, remf a s = s.
trivial.
Qed.

Lemma remf_cont : forall D (a:D) s, remf a (lub s) <= lub (remf a @ s).
intros; rewrite remf_simpl; auto.
Qed.
Global Hint Resolve remf_cont : core.

Definition Rem D : DS D -m> DS D := DSCase (remf (D:=D)).
Definition rem D (s:DS D) := Rem D s.

Lemma rem_simpl : forall D (s:DS D), rem s = DScase (remf (D:=D)) s.
trivial.
Qed.

Lemma rem_cons : forall D (a:D) s, rem (cons a s) = s.
intros; rewrite rem_simpl; rewrite DScase_cons; trivial.
Qed.

Lemma rem_bot : forall D, rem (D:=D) 0 <= 0.
intros; rewrite rem_simpl; auto.
Qed.

Lemma rem_le_compat : forall D (s t:DS D), s<=t -> rem s <= rem t.
unfold rem; auto.
Qed.
Global Hint Resolve rem_le_compat : core.

Lemma rem_eq_compat : forall D (s t:DS D), s==t -> rem s == rem t.
intros; apply Ole_antisym; auto.
Qed.
Global Hint Resolve rem_eq_compat : core.

Add Parametric Morphism D : (@rem D)
with signature (@Oeq (DS D)) ==> (@Oeq (DS D)) as rem_eq_compat_morph.
exact (@rem_eq_compat D).
Qed.

Add Parametric Morphism D : (@rem D)
with signature (@Ole (DS D)) ++> (@Ole (DS D)) as rem_le_compat_morph.
exact (@rem_le_compat D).
Qed.

Lemma rem_is_cons : forall D (s:DS D), is_cons (rem s) -> is_cons s.
unfold rem, Rem; intros.
apply DScase_is_cons with D (remf (D:=D)); auto.
Qed.
Global Hint Immediate rem_is_cons : core.

Lemma rem_cont : forall D, continuous (Rem D).
intros; unfold Rem; apply DScase_cont; intros; auto.
exact (remf_cont c).
Qed.
Global Hint Resolve rem_cont : core.

Definition REM (D:Type) : DS D -c> DS D.
intros; exists (Rem D); auto.
Defined.

Lemma REM_simpl : forall D (s:DS D), REM D s = rem s.
trivial.
Qed.

(** - app s t concatenates the first element of s to t *)

Definition appf D (t:DS D) (d: D) : DS D -m>DS D := fmon_cte (DS D) (Cons d t).

Lemma appf_simpl D (t:DS D) : forall a s, appf t a s = cons a t.
trivial.
Qed.

Definition Appf : forall D, DS D -m> D -o> (DS D -m> DS D).
intro D; exists (appf (D:=D)); red; intros; intros a s; repeat (rewrite appf_simpl); auto.
Defined.

Lemma Appf_simpl : forall D t, Appf D t = appf t.
trivial.
Qed.

Lemma appf_cont D (t:DS D) : forall a c, appf t a (lub c) <= lub (appf t a @ c).
intros; rewrite appf_simpl.
unfold appf.
apply Ole_trans with (lub (c:=DS D) (fmon_cte natO (O2:=DS D) (Cons a t))); auto.
Qed.
Global Hint Resolve appf_cont : core.

Lemma appf_cont_par : forall D, continuous (D2:=D -O-> (DS D -M->DS D)) (Appf D).
red; intros.
intros a s.
rewrite (Appf_simpl (D:=D)); rewrite appf_simpl.
apply Ole_trans with (lub (c:=DS D) (Cons a @ h)); auto.
apply (Cons_cont a h).
rewrite fcpo_lub_simpl; rewrite fmon_lub_simpl.
apply lub_le_compat; intro n; auto.
Qed.
Global Hint Resolve appf_cont_par : core.

Definition AppI : forall D, DS D -m> DS D -m> DS D.
intros; exists (fun t =>  DSCase (appf t)); red; intros.
apply (fmonotonic (DSCASE_mon D D) (x:=appf x) (y:=appf y)).
apply (fmonotonic (Appf D) (x:=x) (y:=y)); trivial.
Defined.

Lemma AppI_simpl : forall D s t, AppI D t s = DScase (appf t) s.
trivial.
Qed.

Definition App (D:Type) := fmon_shift (AppI D).

Lemma App_simpl : forall D s t, App D s t = DScase (appf t) s.
trivial.
Qed.

Definition app D s t := App D s t.

Lemma app_simpl : forall D (s t:DS D), app s t = DScase (appf t) s.
trivial.
Qed.

Lemma app_cons : forall D a (s t:DS D), app (cons a s) t = cons a t.
intros; rewrite app_simpl; rewrite DScase_cons; trivial.
Qed.

Lemma app_bot : forall D (s:DS D), app 0 s <= 0.
intros; rewrite app_simpl; auto.
Qed.

Lemma app_mon_left : forall D (s t u : DS D), s <= t -> app s u <= app t u.
intros; repeat (rewrite app_simpl); auto.
Qed.

Lemma app_cons_elim : forall D a (s t u:DS D), app t u == cons a s ->
             exists t', t == cons a t' /\ s == u.
intros D a s t u; rewrite app_simpl; intros.
case (DScase_eq_cons_elim (appf u) t H).
intros b (t',(H1,H2)).
exists t'.
assert (b=a).
apply (Con_hd_simpl H2).
assert (u==s).
apply (Con_tl_simpl H2).
split; auto.
apply Oeq_trans with (1:=H1); auto.
Qed.

Lemma app_mon_right : forall D (s t u : DS D), t <= u -> app s t <= app s u.
intros; apply (fmonotonic (App D s) H); auto.
Qed.

Global Hint Resolve first_cons first_bot app_cons app_bot
                    app_mon_left app_mon_right rem_cons rem_bot : core.

Lemma app_le_compat : forall D (s t u v:DS D), s <= t -> u <= v -> app s u <= app t v.
intros; apply Ole_trans with (app t u); auto.
Qed.
Global Hint Immediate app_le_compat : core.

Lemma app_eq_compat : forall D (s t u v:DS D), s == t -> u == v -> app s u == app t v.
intros; apply Ole_antisym; apply app_le_compat; auto.
Qed.
Global Hint Immediate app_eq_compat : core.

Add Parametric Morphism D : (@app D)
with signature (@Oeq (DS D)) ==> (@Oeq (DS D)) ==> (@Oeq (DS D)) as app_eq_compat_morph.
intros; apply (app_eq_compat H H0); auto.
Qed.

Add Parametric Morphism D : (@app D)
with signature (@Ole (DS D)) ++> (@Ole (DS D)) ++> (@Ole (DS D)) as app_le_compat_morph.
intros; apply (app_le_compat H H0); auto.
Qed.

Lemma is_cons_app : forall D (x y : DS D), is_cons x -> is_cons (app x y).
intros; rewrite app_simpl.
apply is_cons_DScase; simpl; auto.
Qed.
Global Hint Resolve is_cons_app : core.

Lemma app_is_cons : forall D (x y : DS D),  is_cons (app x y) -> is_cons x.
intros D x y; rewrite app_simpl; intros; apply DScase_is_cons with D (appf y); auto.
Qed.

Lemma app_cont : forall D, continuous2 (App D).
intro D; apply continuous_continuous2; intros.
red; intros.
rewrite (App_simpl (D:=D)).
apply Ole_trans with (DScase (lub (c:=D-O->(DS D -M->DS D)) (Appf D @ h)) k).
assert (DSCase (appf (lub (c:=DS D) h)) <=
DSCase (lub (c:=D -O-> (DS D -M-> DS D)) (Appf D @ h))); auto.
apply (fmonotonic (DSCASE_mon D D) (x:=appf (lub h)) (y:=lub (c:=D -O-> DS D -M-> DS D) (Appf D @ h))).
apply (appf_cont_par (D:=D) h).
apply Ole_trans with (lub (c:=DS D -M->DS D) (DSCASE_mon D D @ (Appf D @ h)) k); auto.
apply (DSCASE_mon_cont (Appf D @ h) k).
red; intros; intro k.
rewrite fmon_lub_simpl.
assert (continuous (D1:=DS D) (D2:=DS D) (DSCase (appf k))).
apply DScase_cont; intros.
exact (appf_cont k c).
exact (H h).
Qed.
Global Hint Resolve app_cont : core.

Definition APP (D:Type) : DS D -c> DS D -C-> DS D := continuous2_cont (app_cont (D:=D)).

Lemma APP_simpl : forall D (s t : DS D), APP D s t = app s t.
trivial.
Qed.

(** *** Basic equalities *)
Lemma first_eq_bot : forall D, first (D:=D) 0 == 0.
intros; apply Ole_antisym; auto.
Qed.

Lemma rem_eq_bot : forall D, rem (D:=D) 0 == 0.
auto.
Qed.

Lemma app_eq_bot : forall D (s:DS D), app 0 s == 0.
auto.
Qed.
Global Hint Resolve first_eq_bot rem_eq_bot app_eq_bot : core.

Lemma DSle_app_bot_right_first : forall D (s:DS D), app s 0 <= first s.
intros; apply DSle_intro_cons; intros.
case (app_cons_elim s 0 H); intros b (H1,H2).
apply Ole_trans with (cons a (0:DS D)); auto.
apply Ole_trans with (first (cons a b)); auto.
Qed.

Lemma DSle_first_app_bot_right : forall D (s:DS D), first s <= app s 0.
intros; apply DSle_intro_cons; intros.
case (first_cons_elim s H); intros s' (H1,H2); auto.
Qed.

Lemma app_bot_right_first : forall D (s:DS D), app s 0 == first s.
intros; apply Ole_antisym.
apply DSle_app_bot_right_first.
apply DSle_first_app_bot_right.
Qed.

Lemma DSle_first_app_first : forall D (x y:DS D), first (app x y) <= first x.
intros; apply DSle_intro_cons; intros.
case (first_cons_elim (app x y) H); intros s' (H1,H2).
case (app_cons_elim x y H1); intros x' (H3,H4).
apply Ole_trans with (first (cons a x')); auto.
apply Ole_trans with (cons a (0:DS D)); auto.
Qed.

Lemma DSle_first_first_app : forall D (x y:DS D), first x <= first (app x y).
intros; apply DSle_intro_cons; intros.
case (first_cons_elim x H); intros x' (H1,H2).
apply  Ole_trans with (first (app (cons a x') y)); auto.
apply Ole_trans with (first (cons a y)); auto.
apply Ole_trans with (cons a (0:DS D)); auto.
Qed.

Lemma first_app_first : forall D (x y:DS D), first (app x y)==first x.
intros; apply Ole_antisym.
apply DSle_first_app_first.
apply DSle_first_first_app.
Qed.

Global Hint Resolve app_bot_right_first first_app_first : core.

Lemma DSle_app_first_rem : forall D (x:DS D), app (first x) (rem x) <= x.
intros; apply DSle_intro_cons; intros.
case (app_cons_elim (first x) (rem x) H); intros t (H1,H2).
case (first_cons_elim x H1); intros x' (H3,H4).
apply Ole_trans with (cons a x'); auto.
apply cons_le_compat; auto.
apply Ole_trans with (rem x); auto.
apply Ole_trans with (rem (cons a x')); auto.
Qed.

Lemma DSle_app_first_rem_sym : forall D (x:DS D), x <= app (first x) (rem x).
intros; apply DSle_intro_cons; intros.
apply Ole_trans with (app (first (cons a s)) (rem (cons a s))).
rewrite first_cons; rewrite rem_cons; rewrite app_cons; trivial.
apply Ole_trans with (app (first x) (rem (cons a s))); auto.
Qed.

Lemma app_first_rem : forall D (x:DS D), app (first x) (rem x) == x.
intros; apply Ole_antisym.
apply DSle_app_first_rem.
apply DSle_app_first_rem_sym.
Qed.
Global Hint Resolve app_first_rem : core.

Lemma rem_app : forall D (x y:DS D), is_cons x -> rem (app x y) == y.
intros; case (is_cons_elim H); intros a (s,H1).
rewrite H1.
rewrite app_cons; rewrite rem_cons; trivial.
Qed.
Global Hint Resolve rem_app : core.

Lemma rem_app_le : forall D (x y:DS D), rem (app x y) <= y.
intros; apply DSle_intro_is_cons; intros.
assert (is_cons (app x y)); auto.
assert (is_cons x); auto.
apply app_is_cons with y; trivial.
Qed.
Global Hint Resolve rem_app_le : core.

Lemma is_cons_rem_app : forall D (x y : DS D), is_cons x -> is_cons y -> is_cons (rem (app x y)).
intros; apply is_cons_eq_compat with y; auto.
apply Oeq_sym; auto.
Qed.
Global Hint Resolve is_cons_rem_app : core.

Lemma rem_app_is_cons : forall D (x y : DS D),  is_cons (rem (app x y)) -> is_cons y.
intros; assert (is_cons (app x y)); auto.
assert (is_cons x).
apply app_is_cons with y; trivial.
apply is_cons_eq_compat with (rem (app x y)); auto.
Qed.

Lemma first_first_eq : forall D (s:DS D), first (first s) == first s.
intros; apply Oeq_trans with (first (app (first s) (rem s))); auto.
Qed.
Global Hint Resolve first_first_eq : core.

Lemma app_app_first : forall D (s t : DS D), app (first s) t == app s t.
intros; apply DSeq_intro_is_cons; intros.
assert (is_cons s).
assert (is_cons (first s)); auto.
apply app_is_cons with t; trivial.
case (is_cons_elim H0); intros a (s',H1).
rewrite H1; rewrite first_cons; repeat rewrite app_cons; trivial.
assert (is_cons s).
apply app_is_cons with t; trivial.
case (is_cons_elim H0); intros a (s',H1).
rewrite H1; rewrite first_cons; repeat rewrite app_cons; trivial.
Qed.

(** ** Proof by co-recursion *)
Lemma DS_bisimulation : forall D (R: DS D -> DS D -> Prop),
        (forall x1 x2 y1 y2, R x1 y1 -> x1==x2 -> y1==y2 -> R x2 y2)
   -> (forall (x y:DS D), (is_cons x \/ is_cons y) -> R x y -> first x == first y)
   -> (forall (x y:DS D), (is_cons x \/ is_cons y) -> R x y -> R (rem x) (rem y))
   -> forall x y, R x y -> x == y.
intros; apply (DSeq_rec R); auto; intros.
assert (Hf:=H0 (cons a s) y0 (or_introl (is_cons y0) (is_cons_intro a s)) H3).
assert (Hr:=H1 (cons a s) y0 (or_introl (is_cons y0) (is_cons_intro a s)) H3).
rewrite first_cons in Hf.
case (first_cons_elim (a:=a) (s:=0:DS D) y0); auto; intros x0 (H4,_).
exists x0; split; auto.
apply H with (rem (cons a s)) (rem y0); auto.
apply Oeq_trans with (rem (cons a x0)); auto.
assert (Hf:=H0 x0 (cons a s)  (or_intror (is_cons x0) (is_cons_intro a s)) H3).
assert (Hr:=H1 x0 (cons a s) (or_intror (is_cons x0) (is_cons_intro a s)) H3).
rewrite first_cons in Hf.
case (first_cons_elim (a:=a) (s:=0:DS D) x0); auto; intros y0 (H4,_).
exists y0; split; auto.
apply H with (rem x0) (rem (cons a s)); auto.
apply Oeq_trans with (rem (cons a y0)); auto.
Qed.


Lemma DS_bisimulation2 : forall D (R: DS D -> DS D -> Prop),
        (forall x1 x2 y1 y2, R x1 y1 -> x1==x2 -> y1==y2 -> R x2 y2)
   -> (forall (x y:DS D), (is_cons x \/ is_cons y) -> R x y -> first x == first y)
   -> (forall (x y:DS D), (is_cons (rem x) \/ is_cons (rem y)) -> R x y -> first (rem x) == first (rem y))
   -> (forall (x y:DS D), (is_cons (rem x) \/ is_cons (rem y)) -> R x y -> R (rem (rem x)) (rem (rem y)))
   -> forall x y, R x y -> x == y.
intros;
apply DS_bisimulation
   with (R:= fun x y => R x y \/ ((is_cons x \/ is_cons y)
                                                 -> (first x == first y /\
                                                      R (rem x) (rem y)))); intros.
case H4; clear H4; intros.
left; apply H with x1 y1; trivial.
right; intros.
assert (is_cons x1 \/ is_cons y1).
case H7; clear H7; intro.
left; apply is_cons_eq_compat with x2; auto.
right; apply is_cons_eq_compat with y2; auto.
assert (H9:=H4 H8); clear H4 H7 H8; intuition.
rewrite <- H5; rewrite <- H6; trivial.
apply H with (rem x1) (rem y1); auto.
case H5; clear H5; intros; auto.
case (H5 H4); trivial.
case H5; clear H5; intros; auto.
case (H5 H4); clear H4 H5; intros.
auto.
auto.
Qed.

(** ** Finiteness of streams *)

CoInductive infinite (D:Type) (s: DS D) : Prop :=
      inf_intro : is_cons s -> infinite (rem s) -> infinite s.

Lemma infinite_le_compat :  forall D (s t:DS D), s <= t -> infinite s -> infinite t.
intro D; cofix infinite_le_compat; intros.
case H0; intros.
apply inf_intro.
apply is_cons_le_compat with s; auto.
apply infinite_le_compat with (rem s); auto.
Qed.

Add Parametric Morphism D : (@infinite D)
with signature (@Oeq (DS D)) ==> iff as infinite_morph.
intros x y; split; intros.
apply infinite_le_compat with x; auto.
apply infinite_le_compat with y; auto.
Qed.

Lemma not_infiniteBot : forall D, ~ infinite (0:DS D).
red; intros D H; case H; intros.
apply (not_is_consBot (D:=D)); auto.
Qed.
Global Hint Resolve not_infiniteBot : core.


Inductive finite  (D:Type) (s:DS D) : Prop :=
      fin_bot : s <= 0 -> finite s | fin_cons : finite (rem s) -> finite s.

Lemma finite_mon : forall D (s t:DS D), s <= t -> finite t -> finite s.
intros.
generalize s H.
elim H0; clear s t H H0; intros.
apply fin_bot.
apply Ole_trans with s; auto.
apply fin_cons; auto.
Qed.

Add Parametric Morphism D : (@finite D)
with signature (@Oeq (DS D)) ==> iff as finite_morph.
intros x y; split; intros.
apply finite_mon with x; auto.
apply finite_mon with y; auto.
Qed.

Lemma not_finite_infinite : forall D (s:DS D), finite s -> ~ infinite s.
induction 1; intros; auto.
red; intro; apply (not_infiniteBot (D:=D)).
apply infinite_le_compat with s; auto.
red; intro; apply IHfinite.
case H0; trivial.
Qed.

(** ** Mapping a function on a stream *)

Section MapStream.
Variable D D': Type.
Variable F : D -> D'.

Definition mapf : (DS D -C-> DS D') -m> D -O-> DS D -C-> DS D'.
exists (fun (f : DS D -C-> DS D') (a:D) => CONS (F a) @_ f).
red; intros f g Hle a.
apply (fcont_le_intro (D1:=DS D) (D2:=DS D')); intro s.
repeat rewrite fcont_comp_simpl.
auto.
Defined.

Lemma mapf_simpl : forall f, mapf f = fun a => CONS (F a) @_ f.
trivial.
Qed.

Definition Mapf : (DS D -C-> DS D') -c> D-O-> DS D -C->DS D'.
exists mapf.
red; intros h a.
rewrite mapf_simpl.
rewrite fcpo_lub_simpl.
apply (fcont_le_intro (D1:=DS D) (D2:=DS D')); intro s.
rewrite fcont_lub_simpl.
repeat rewrite fcont_comp_simpl; repeat rewrite fcont_lub_simpl; intros.
rewrite (fcontinuous (CONS (F a)) (h <__> s)).
apply lub_le_compat; intro n; auto.
Defined.

Lemma Mapf_simpl : forall f, Mapf f = fun a => CONS (F a) @_ f.
trivial.
Qed.

Definition MAP : DS D -C-> DS D' := FIXP (DS D-C->DS D') (DSCASE D D' @_ Mapf).

Lemma MAP_eq : MAP == DSCASE D D' (Mapf MAP).
exact (FIXP_eq  (DSCASE D D' @_ Mapf)).
Qed.

Definition map (s: DS D) := MAP s.

Lemma map_eq : forall s:DS D, map s == DScase (fun a => Cons (F a) @ (fcontit MAP)) s.
intros; apply (fcont_eq_elim MAP_eq s).
Qed.

Lemma map_bot : map 0 == 0.
unfold map.
rewrite (fcont_eq_elim MAP_eq 0).
rewrite DSCASE_simpl; auto.
Qed.

Lemma map_eq_cons : forall a s,
            map (cons a s) == cons (F a) (map s).
intros; unfold map at 1.
rewrite (fcont_eq_elim MAP_eq (cons a s)).
rewrite DSCASE_simpl.
rewrite DScase_cons; auto.
Qed.

Lemma map_le_compat : forall s t, s <= t -> map s <= map t.
intros; unfold map; apply (fcont_monotonic MAP); trivial.
Qed.

Lemma map_eq_compat : forall s t, s == t -> map s == map t.
intros; apply (fcont_stable MAP H).
Qed.

Add Parametric Morphism : map
with signature (@Oeq (DS D)) ==> (@Oeq (DS D')) as map_eq_compat_morph_local.
exact map_eq_compat.
Qed.

Lemma is_cons_map : forall (s:DS D), is_cons s -> is_cons (map s).
intros; case (is_cons_elim H); intros a (t,H1).
rewrite H1.
rewrite map_eq_cons; auto.
Qed.
Hint Resolve is_cons_map : core.

Lemma map_is_cons : forall s, is_cons (map s) -> is_cons s.
intros; case (is_cons_elim H); intros a (t,H1).
generalize H1; rewrite map_eq.
intros; apply DScase_is_cons with (f:=fun a0 : D => Cons (F a0) @ fcontit MAP).
rewrite H0; auto.
Qed.
Hint Immediate map_is_cons : core.

End  MapStream.
Global Hint Resolve map_bot map_eq_cons map_le_compat map_eq_compat is_cons_map : core.

Add Parametric Morphism D D' : (@map D D')
with signature eq ==> (@Oeq (DS D)) ==> (@Oeq (DS D')) as map_eq_compat_morph.
exact (@map_eq_compat D D').
Qed.

(** ** Filtering a stream *)

Section FilterStream.
Variable D : Type.
Variable P : D -> Prop.
Variable Pdec : forall x, {P x}+{~ P x}.

Definition filterf : (DS D -C-> DS D) -m> D-O-> DS D -C->DS D.
exists (fun (f : DS D -C-> DS D) a => if Pdec a then CONS a @_ f else f).
red; intros f g Hle a.
case (Pdec a); intros; auto.
apply (fcont_le_intro (D1:=DS D) (D2:=DS D)); intro s.
repeat rewrite fcont_comp_simpl.
auto.
Defined.

Lemma filterf_simpl : forall f, filterf f = fun a => if Pdec a then CONS a @_ f else f.
trivial.
Qed.

Definition Filterf : (DS D -C-> DS D) -c> D-O-> DS D -C->DS D.
exists filterf.
red; intros h a.
rewrite filterf_simpl.
rewrite fcpo_lub_simpl.
apply (fcont_le_intro (D1:=DS D) (D2:=DS D)); intro s.
rewrite fcont_lub_simpl.
case (Pdec a); repeat rewrite fcont_comp_simpl; repeat rewrite fcont_lub_simpl; intros.
rewrite (fcontinuous (CONS a) (h <__> s)).
apply lub_le_compat; intro n.
rewrite fmon_comp_simpl.
repeat rewrite fcont_app_simpl.
rewrite ford_app_simpl.
rewrite fmon_comp_simpl.
rewrite filterf_simpl.
case (Pdec a); intuition.
(* case ~ P a *)
apply lub_le_compat; intro m.
repeat rewrite fcont_app_simpl.
rewrite ford_app_simpl.
rewrite fmon_comp_simpl.
rewrite filterf_simpl.
case (Pdec a); intuition.
Defined.

Lemma Filterf_simpl : forall f, Filterf f = fun a => if Pdec a then CONS a @_ f else f.
trivial.
Qed.

Definition FILTER : DS D -C-> DS D := FIXP (DS D-C->DS D) (DSCASE D D @_ Filterf).

Lemma FILTER_eq : FILTER == DSCASE D D (Filterf FILTER).
exact (FIXP_eq  (DSCASE D D @_ Filterf)).
Qed.

Definition filter (s: DS D) := FILTER s.

Lemma filter_bot : filter 0 == 0.
unfold filter.
rewrite (fcont_eq_elim FILTER_eq 0).
rewrite DSCASE_simpl; auto.
Qed.

Lemma filter_eq_cons : forall a s,
            filter (cons a s) == if Pdec a then cons a (filter s) else filter s.
intros; unfold filter at 1.
rewrite (fcont_eq_elim FILTER_eq (cons a s)).
rewrite DSCASE_simpl.
rewrite DScase_cons.
rewrite Filterf_simpl; case (Pdec a); auto.
Qed.

Lemma filter_le_compat : forall s t, s <= t -> filter s <= filter t.
intros; unfold filter; apply (fcont_monotonic FILTER); trivial.
Qed.

Lemma filter_eq_compat : forall s t, s == t -> filter s == filter t.
intros; apply (fcont_stable FILTER H).
Qed.

End  FilterStream.
Global Hint Resolve filter_bot filter_eq_cons filter_le_compat filter_eq_compat : core.
