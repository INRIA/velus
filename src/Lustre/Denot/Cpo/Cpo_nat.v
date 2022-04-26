Require Export Cpo_streams_type.
Set Implicit Arguments.

(** * Cpo_nat.v: Domains of natural numbers *)

(** ** Definition *)
(** - Natural numbers are a particular case of streams over the trivial type unit *) 

Lemma unit_eq : forall x : unit, x = tt.
destruct x; trivial.
Qed.
Global Hint Resolve unit_eq : core.

Definition DN : cpo := DS unit.

Definition DNS (n : DN) : DN := cons tt n.

(** ** Embedding of usual natural numbers *)

Fixpoint nat2DN (n:nat) : DN := match n with 0 => 0 | S p => DNS (nat2DN p) end.


(** ** Infinite element *)

CoFixpoint DNinf : DN := DNS DNinf.

Lemma DNinf_inv : DNinf = DNS DNinf.
pattern  DNinf at 1; rewrite (DS_inv DNinf); simpl; trivial.
Qed.

Lemma DNleinf : forall n:DN, n <= DNinf.
cofix DNleinf; destruct n.
repeat red; apply DSleEps; apply (DNleinf n).
rewrite DNinf_inv.
case u.
repeat red; apply DSleCon with DNinf.
unfold DNS; auto.
apply (DNleinf n).
Qed.

Global Hint Resolve DNleinf : core.

(** ** Properties of basic operators *)

Lemma DNEps_left : forall x y:DN, x == y -> (Eps x :DN) == y.
intros; apply Oeq_trans with x; auto.
apply Oeq_sym; exact (eqEps x).
Qed.

Lemma DNEps_right : forall x y:DN, x == y -> x == Eps y.
intros; apply Oeq_trans with y; auto.
exact (eqEps y).
Qed.

Global Hint Immediate DNEps_left DNEps_right : core.

Lemma DNS_le_compat : forall (x y:DN) , x<=y -> DNS x <= DNS y.
intros x y H; exact (DSleCon0  (D:=unit) tt H).
Qed.
Global Hint Resolve DNS_le_compat : core.

Lemma DNS_eq_compat : forall (x y:DN) , x==y -> DNS x == DNS y.
intros; apply Ole_antisym;auto.
Qed.
Global Hint Resolve DNS_eq_compat : core.

Add Morphism DNS with signature (@Oeq DN) ==> (@Oeq DN) as DNS_eq_compat_morph.
exact DNS_eq_compat.
Qed.

Lemma DNS_le_simpl : forall x y :DN, DNS x <= DNS y -> x <= y.
intros x y H; exact (DSleCon_tl (D:=unit) H).
Qed.
Global Hint Immediate DNS_le_simpl : core.

Lemma DNS_eq_simpl : forall x y :DN, DNS x == DNS y -> x == y.
intros x y H; exact (Con_tl_simpl (D:=unit) H).
Qed.
Global Hint Immediate DNS_eq_simpl : core.

(** ** Simulation principles *)

Lemma DNle_rec : forall R : DN -> DN -> Prop,
   (forall x1 x2 y1 y2:DN, R x1 y1 -> x1==x2 -> y1==y2 -> R x2 y2) ->
   (forall s (y:DN), R (DNS s) y -> exists t, y== DNS t /\ R s t)
   -> forall x y : DN , R x y -> x <= y.
intros R Req RCons x y Rxy.
apply DSle_rec_eq with (D:=unit) (R:=R) (x:=x); auto.
intro a; rewrite (unit_eq a); intros s y0 H2.
case (RCons s y0 H2); intros t (H3,H4); exists t; auto.
Qed.

Lemma DNeq_rec : forall R : DN -> DN -> Prop,
   (forall x1 x2 y1 y2:DN, R x1 y1 -> x1==x2 -> y1==y2 -> R x2 y2) ->
   (forall s (y:DN), R (DNS s) y -> exists t, y==DNS t /\  R s t)->
   (forall s (x:DN), R x (DNS s) -> exists t, x==DNS t /\ R t s)
  -> forall x y : DN , R x y -> x == y.
intros R Req RCons1 RCons2 x y Rxy; 
      apply DSeq_rec with (D:=unit) (R:=R); auto.
intro a; rewrite (unit_eq a); intros s y0 H2.
case (RCons1 s y0 H2); intros t (H3,H4); exists t; auto.
intro a; rewrite (unit_eq a); intros s y0 H2.
case (RCons2 s y0 H2); intros t (H3,H4); exists t; auto.
Qed.

(** ** More properties on basic functions *)

Lemma DNle_n_Sn  : forall x, x <= DNS x.
intros; apply DNle_rec with (R:= fun x y => y == DNS x); intros; auto.
apply Oeq_trans with y1; auto.
apply Oeq_trans with (DNS x1); auto.
exists (DNS s); auto.
Qed.
Global Hint Resolve DNle_n_Sn : core.

Lemma DNinf_le_intro : forall x, DNS x <= x -> DNinf <= x.
intros; apply DNle_rec with (R:= fun x y => DNS y <= y); intros; auto.
apply Ole_trans with y1; auto.
apply Ole_trans with (DNS y1); auto.
exists y; auto.
Qed.
Global Hint Immediate DNinf_le_intro : core.


Lemma is_cons_S : forall n, is_cons n -> n == DNS (rem n).
intros; case (is_cons_elim H); intro a; case a; intros (t,H1); auto.
apply Oeq_trans with (DNS (rem (cons tt t))).
rewrite rem_cons; auto.
apply DNS_eq_compat.
rewrite H1; trivial.
Qed.

Lemma infinite_S : forall n : DN, DNS n <= n -> infinite n.
cofix infinite_S; intros.
assert (is_cons n).
apply is_cons_le_compat with (DNS n); unfold DNS; auto.
apply inf_intro; trivial.
apply infinite_S.
apply Ole_trans with (rem (DNS n)); auto.
rewrite <- is_cons_S; auto.
unfold DNS; rewrite rem_cons; trivial.
apply (rem_le_compat (D:=unit)); auto.
Qed.

(** ** Addition *)
CoFixpoint add (n m : DN) : DN := 
     match n with (Eps n')   => Eps (add m n')
                       |  (Con _ n')   => DNS (add m n')
     end.

Lemma add_inv : forall (n m : DN), 
   add n m = match n with (Eps n')   => Eps (add m n')
                                     |  (Con _ n')   => DNS (add m n')
   end.
intros; rewrite (DS_inv (add n m)); simpl.
destruct n; trivial.
Qed.

Lemma add_decomp_elim : forall a (s x y:DN), decomp a s (add x y) -> 
            exists t, exists u, s = add t u /\
                (x==DNS u /\ y==t \/ x==t /\ y == DNS u).
intros a s x y H; case H; clear H; intro k; generalize x y; clear x y; 
pattern k; apply Wf_nat.lt_wf_ind; intros.
rewrite add_inv in H0; destruct x.
destruct n; simpl in H0.
discriminate H0.
case (H n) with (2:=H0); auto; intros t (u,(H1,H2)).
exists t; exists u; intuition.
rewrite (unit_eq u); exists y; exists x; intuition.
rewrite (pred_nthCon (D:=unit) tt (add y x)) in H0.
injection H0; auto.
Qed.

Lemma add_eqCons : forall (s x y:DN), add x y == DNS s -> 
            exists t, exists u, s == add t u /\
                (x==DNS u /\ y==t  \/  x == t /\ y == DNS u).
intros s x y H; case (decomp_eq (D:=unit) H); intros v (H1,H2).
case (add_decomp_elim x y H1); intros t (u, (Heq, H4)).
exists t; exists u; intuition.
apply Oeq_trans with v; auto.
apply Oeq_trans with v; auto.
Qed.

Lemma addS : 
     forall x' x, DNS x' <= x 
   -> forall y, (exists s, add x y == DNS s) /\ (exists s, add y x == DNS s).
intros x' x H; inversion_clear H.
case H0; clear H0; intro k; generalize x; clear x; 
pattern k; apply Wf_nat.lt_wf_ind; intros.
rewrite (add_inv x y); destruct x.
destruct n; simpl in H0.
discriminate H0.
assert 
 (forall y : DN,
    (exists s : DN, add x y == DNS s) /\ 
    (exists s : DN, add y x == DNS s)).
intro; apply (H n) with (2:=H0); auto; intros.
split.
case (H2 y); intros (s,H4) (s',H5); exists s'; auto.
rewrite (add_inv y (Eps x)); destruct y.
rewrite (add_inv (Eps x) y).
case (H2 y); intros (s,H4) (s',H5); exists s'; auto.
apply Oeq_trans with (Eps (add y x)); auto.
exists (add (Eps x) y); auto.
split.
exists (add y x); auto.
rewrite (add_inv y (Con u x)); case y; intros.
rewrite (add_inv (Con u x) d).
exists (add d x); auto.
exists (add (Con u x) d); auto.
Qed.

Lemma addS_sym : 
   forall x y v:DN, add x y == DNS v -> exists t', add y x == DNS t'.
intros x y v H; case (add_eqCons x y H); intros t (u,(Heq,[(H1,H2)|(H1,H2)])).
case (addS (x':=u) (x:=x)) with (y:=y); auto.
case (addS (x':=u) (x:=y)) with (y:=x); auto.
Qed.

(** DNSn x n = S^n x *)

Fixpoint DNSn (x:DN) (n:nat) {struct n} :DN := 
   match n with 0 => x | S p => DNSn (DNS x) p end.

Lemma DNSnS : forall n x, DNSn (DNS x) n = DNS (DNSn x n).
induction n; simpl; auto.
Qed.
Global Hint Resolve DNSnS : core.


Lemma DNSn_mon : forall (n:nat) (x y:DN), x<=y -> DNSn x n <= DNSn y n.
induction n; simpl; auto; intros.
apply IHn; auto.
Qed.
Global Hint Resolve DNSn_mon : core.

Lemma DNSn_eq_compat : forall  (n:nat) (x y:DN), x==y -> DNSn x n == DNSn y n.
intros; apply Ole_antisym;auto.
Qed.
Global Hint Resolve DNSn_eq_compat : core.


(** Condition S^l x <= z & y <= S^l t ensuring x+y <= z+t *)
Definition compat (x y z t:DN) := exists l:nat, (DNSn x l <= z /\ y <= DNSn t l).

Lemma compatS : 
   forall x y z t x' y' z' t',
   compat x y z t -> 
      (x==DNS y' /\ y==x' \/ x==x' /\ y==DNS y')
  -> (z==DNS t' /\ t==z' \/ z==z' /\ t==DNS t')
  -> (compat x' y' z' t' \/ compat x' y' t' z' \/ compat y' x' z' t' \/ compat y' x' t' z').
intros x y z t x' y' z' t' (l, (H1,H2)). intros [[]|[]] [[]|[]].
(* case 1 *)
repeat right; exists l; split.
apply DNS_le_simpl.
apply Ole_trans with z; auto.
apply Ole_trans with (DNSn (DNS y') l); auto.
apply Ole_trans with (DNSn x l); auto.
apply Ole_trans with (DNSn t l); auto.
apply Ole_trans with y; auto.
(* case 1 *)
right;right;left; exists (S l); simpl DNSn; split.
apply Ole_trans with z; auto.
apply Ole_trans with (DNSn x l); auto.
apply Ole_trans with y; auto.
apply Ole_trans with (DNSn t l); auto.
(* case 3 : case l = 0 *)
destruct l; simpl DNSn in H1; simpl DNSn in H2.
right;right;left; exists (S 0); simpl DNSn; split.
apply Ole_trans with y; auto.
apply Ole_trans with t; auto.
apply Ole_trans with x; auto.
apply Ole_trans with z; auto.
(* case 3 :  l = S l' *)
right;left; exists l; split; apply DNS_le_simpl.
apply Ole_trans with z; auto.
apply Ole_trans with (DNSn (DNS x) l); auto.
apply Ole_trans with (DNSn (DNS x') l); auto.
apply Ole_trans with y; auto.
apply Ole_trans with (DNSn (DNS t) l); auto.
apply Ole_trans with (DNSn (DNS z') l); auto.
(* Case 4 *)
left; exists l; split.
apply Ole_trans with z; auto.
apply Ole_trans with (DNSn x l); auto.
apply DNS_le_simpl; apply Ole_trans with y; auto.
apply Ole_trans with (DNSn t l); auto.
apply Ole_trans with (DNSn (DNS t') l); auto.
Qed.

Lemma compat_addS : forall n m p q v:DN, 
    (compat n m p q) -> add n m == DNS v -> exists t, add p q == DNS t.
intros n m p q v (l,(H,H0)) H1.
case (add_eqCons n m H1); intros n' (m',(H2,[(H3,H4)|(H3,H4)])).
assert (H5:DNS (DNSn m' l) <= p).
rewrite <- DNSnS.
apply Ole_trans with (DNSn n l); auto.
case (addS H5) with (y:=q); auto.
destruct l; simpl DNSn in H; simpl DNSn in H0.
assert (H5:DNS m' <= q).
apply Ole_trans with m; auto.
case (addS H5) with (y:=p); auto.
assert (H5:DNS (DNSn n l) <= p).
rewrite <- DNSnS; trivial.
case (addS H5) with (y:=q); auto.
Qed.


Lemma add_compat : 
  forall n m p q, 
    (compat n m p q \/ compat n m q p \/ compat m n p q \/ compat m n q p) 
    -> add n m <= add p q.
intros; apply DNle_rec with 
     (R:= fun x y => exists n, exists m, exists p, exists q, 
             x ==  add n m /\ y == add p q /\  
             (compat n m p q \/ compat n m q p \/ compat m n p q \/ compat m n q p)).
(* Compatibility with equality *)
clear H n m p q; intros x1 x2 y1 y2 (n,(m,(p,(q,(H1,(H2,H3)))))).
exists n; exists m; exists p; exists q; split.
apply Oeq_trans with x1; auto.
split; auto.
apply Oeq_trans with y1; auto.
(* Case Cons *)
clear H n m p q; intros s y (n,(m,(p,(q,(H1,(H2,Hc)))))).
assert (H1':add n m == DNS s); auto; clear H1.
case  (add_eqCons n m H1'); intros n' (m', (H4,H5)).
case Hc; clear Hc; intro H3.
(* compat n m p q *)
case (compat_addS H3 H1'); intros w H6.
case  (add_eqCons p q H6); intros p' (q', (H7,H8)).
exists w; split; auto.
apply Oeq_trans with (add p q); auto.
exists n'; exists m'; exists p'; exists q'; split; auto.
split; auto.
apply (compatS H3 H5 H8).
case H3; clear H3; intro H3.
(* compat n m q p *)
case (compat_addS H3 H1'); intros w H6.
case (addS_sym q p H6); clear H6 w; intros w H6.
case  (add_eqCons p q H6); intros p' (q', (H7,H8)).
exists w; split; auto.
apply Oeq_trans with (add p q); auto.
exists n'; exists m'; exists p'; exists q'; split; auto.
split; auto.
case (compatS H3 (x':=n') (y':=m') (z':=p') (t':=q')); intuition.
case (addS_sym n m H1'); intros s' H1.
case H3; clear H3; intro H3.
(* compat m n p q *)
case (compat_addS H3 H1); intros w H6.
case  (add_eqCons p q H6); intros p' (q', (H7,H8)).
exists w; split; auto.
apply Oeq_trans with (add p q); auto.
exists n'; exists m'; exists p'; exists q'; split; auto.
split; auto.
case (compatS H3 (x':=n') (y':=m') (z':=p') (t':=q')); intuition.
(* compat m n q p *)
case (compat_addS H3 H1); intros w H6.
case (addS_sym q p H6); clear H6 w; intros w H6.
case  (add_eqCons p q H6); intros p' (q', (H7,H8)).
exists w; split; auto.
apply Oeq_trans with (add p q); auto.
exists n'; exists m'; exists p'; exists q'; split; auto.
split; auto.
case (compatS H3 (x':=n') (y':=m') (z':=p') (t':=q')); intuition.
(* witness *)
exists n; exists m; exists p; exists q; auto.
Qed.

Lemma add_mon : forall n p m q, n<=p -> m <= q -> add n m <= add p q.
intros; apply add_compat.
left; exists O; simpl DNSn; auto.
Qed.

Global Hint Resolve add_mon : core.

Definition Add : DN -m> DN -m> DN := le_compat2_mon add_mon.

Lemma Add_simpl : forall x y, Add x y = add x y.
trivial.
Qed.

Add Morphism add with signature (@Oeq DN) ==> (@Oeq DN) ==> (@Oeq DN) as add_eq_compat.
intros; apply Ole_antisym; auto.
Qed.

Lemma add_le_sym : forall n m, add n m <= add m n.
intros; apply add_compat.
right; left; exists O; simpl DNSn; auto.
Qed.
Global Hint Resolve add_le_sym : core.

Lemma add_sym : forall n m, add n m == add m n.
intros; apply Ole_antisym; auto.
Qed.


Lemma addS_shift : forall n m, add (DNS n) m == add n (DNS m).
intros; apply Ole_antisym; apply add_compat.
repeat right; exists (S 0); simpl DNSn; auto.
left; exists (S 0); simpl DNSn; auto.
Qed.
Global Hint Resolve addS_shift : core.

Lemma addS_simpl : forall n m, add (DNS n) m == DNS (add n m).
intros; case (addS (x':=n) (x:=DNS n)) with (y:=m); auto; intros (s,H) _.
case (add_eqCons (DNS n) m H); intros t (u,(H1,H2)).
apply Oeq_trans with (DNS s); auto.
apply DNS_eq_compat.
apply Oeq_trans with (add t u); intuition.
apply Oeq_trans with (add u t); auto.
apply add_eq_compat; auto.
apply DNS_eq_simpl; auto.
rewrite <- H2; rewrite H3; auto.
Qed.
Global Hint Resolve addS_simpl : core.

Lemma not_le_S_0 : forall n, ~ (DNS n <= 0).
exact (not_le_consBot (D:=unit) (a:=tt)).
Qed.
Global Hint Resolve not_le_S_0 : core.

(*
Lemma addS_n_0 : forall n m, add DN0 n == DNS m -> n == DNS m.
intros n m H; case (add_eqCons DN0 n H); intros x (y,(H1,[(H2,H3)|(H2,H3)])).
absurd (DNS y <= DN0); auto.
*)

Lemma add_n_0 : forall n, add 0 n == n.
intros; apply DNeq_rec with 
          (R:= fun x y => exists n, x ==  add 0 n /\ y == n).
(* compatibility with equality *)
intros x1 x2 y1 y2 (n0,(H1,H2)) H3 H4.
exists n0; intuition eauto.
(* Case (add 0 n) is S *)
clear n; intros s y  (n0,(H1,H2)).
assert (Ha:add 0 n0 == DNS s); auto.
case (add_eqCons 0 n0 Ha); intros u (v,(He,[(H3,H4)|(H3,H4)])).
absurd (DNS v <= 0); auto.
exists v; intuition.
apply Oeq_trans with n0; auto.
exists v; split; auto.
rewrite H3; auto.
(* Case n is S *)
clear n; intros s x  (n0,(H1,H2)).
assert (Hle:DNS s <= n0); auto.
case (addS Hle 0); intros _ (w,Ha).
case (add_eqCons 0 n0 Ha); intros u (v,(He,[(H3,H4)|(H3,H4)])).
absurd (DNS v <= 0); auto.
exists w; intuition.
apply Oeq_trans with (add 0 n0); auto.
exists v; split.
rewrite H3; auto.
apply DNS_eq_simpl.
apply Oeq_trans with n0; auto.
exists n; auto.
Qed.

(* *** Continuity of addition *)

Lemma add_continuous_right : forall b, continuous (Add b).
red; intros b c.
apply DNle_rec with
     (R:= fun x y => exists b, exists c, x ==  add b (lub c) /\ y == lub (Add b @c)).
(* compatibility with equality *)
intros x1 x2 y1 y2 (b0,(c0,(H1,H2))) H3 H4.
exists b0; exists c0; intuition eauto.
(* Case (add b (lub c)) is S *)
clear b c; intros s y  (b,(c,(H1,H2))).
assert (H1':add b (lub c)==DNS s); auto.
case (add_eqCons b (lub c) H1'); intros u (v,(He,[(H3,H4)|(H3,H4)])).
(* Case b = S u *)
exists (lub (Add v @ c)); split; auto.
apply Oeq_trans with (lub (Add b @ c)); auto.
apply Oeq_trans with  (lub (c:=DN) (Cons tt @ (Add v @ c))).
apply lub_eq_compat; apply fmon_eq_intro; simpl; intros.
apply Oeq_trans with (add (DNS v) (c n)).
apply add_eq_compat; auto.
apply (addS_simpl v (c n)).
apply Oeq_sym; apply (lub_comp_eq (D1:=DN) (D2:=DN) (f:=Cons tt)) with 
        (h:=Add v @ c).
exact (Cons_cont tt).

exists v; exists c; split; auto.
apply Oeq_trans with (add v u); auto.
apply Oeq_trans with (add u v); auto.
apply add_eq_compat; auto.

(* Case lub c = S v *)
case (DS_lubCon_inv c H4); intros tlc (Hl1,(m,Hl3)).
exists (lub (Add b @ tlc)); split.
apply Oeq_trans with (lub (Add b @ c)); auto.
apply Oeq_trans with (lub (c:=DN) (Cons tt @ (Add b @ tlc))).
apply Oeq_trans with (lub (mseq_lift_right (O:=DN) (Add b @ c) m)); auto.
apply lub_eq_compat; apply fmon_eq_intro; unfold mseq_lift_right; simpl; intro.
apply Oeq_trans with (add b (Cons tt (tlc n))).
apply add_eq_compat; auto.
exact (Hl3 n).
apply Oeq_trans with (add (DNS b) (tlc n)).
apply Oeq_sym; exact (addS_shift b (tlc n)).
exact (addS_simpl b (tlc n)).
apply Oeq_sym; 
apply (lub_comp_eq (D1:=DN) (D2:=DN) (f:=Cons tt)) with (h:=(Add b @ tlc)).
exact (Cons_cont tt).

exists b; exists tlc; split; auto.
apply Oeq_trans with (add u v); auto.
apply add_eq_compat; auto.
(* R (add b (lub c)) (lub (Add b @c)) *)
exists b; exists c; auto.
Qed.


Lemma add_continuous2 : continuous2 Add.
apply continuous2_sym.
intros; repeat (rewrite Add_simpl); auto.
intros; apply add_continuous_right.
Qed.

Lemma add_continuous : continuous (D2:=DN-M->DN) Add.
apply continuous2_continuous.
apply add_continuous2.
Qed.

(** ** Length of a stream *)

Definition LENGTH (D:Type) : DS D -c> DN := MAP (fun x:D=>tt).

Definition length (D:Type) (s:DS D) : DN := LENGTH D s.

Lemma length_simpl : forall (D:Type) (s:DS D), length s = map (fun x:D=>tt) s.
trivial.
Qed.

Lemma length_eq_cons : forall D a (s:DS D), length (cons a s) == DNS (length s).
intros; repeat rewrite length_simpl.
exact (map_eq_cons (fun _ : D => tt) a s).
Qed.

Lemma length_nil : forall D, length (0:DS D) == 0.
intro D; exact (map_bot (fun _ : D => tt)).
Qed.

Global Hint Resolve  length_eq_cons length_nil : core.
   
Lemma length_le_compat : forall D (s t : DS D), s <= t -> length s <= length t.
intro D; exact (fcont_monotonic (LENGTH D)).
Qed.
Global Hint Resolve length_le_compat : core.

Lemma length_eq_compat : forall D (s t : DS D), s == t -> length s == length t.
intros; apply Ole_antisym; auto.
Qed.
Global Hint Resolve length_eq_compat : core.

Add Parametric Morphism D : (@length D) with signature (@Oeq (DS D)) ==> (@Oeq DN) as length_morph.
intros; apply length_eq_compat; trivial.
Qed.

Lemma is_cons_length : forall D (s:DS D), is_cons s -> is_cons (length s).
intros; rewrite length_simpl; auto.
Qed.
Global Hint Resolve is_cons_length : core.

Lemma length_is_cons : forall D (s:DS D), is_cons (length s) -> is_cons s.
intros D s; rewrite length_simpl; apply map_is_cons with (F:=fun _:D => tt); auto.
Qed.
Global Hint Immediate length_is_cons : core.

Lemma length_rem : forall D (s:DS D), length (rem s) == rem (length s).
intros; apply (DSeq_intro_is_cons (D:=unit)); intros.
assert (is_cons (rem s)); auto.
assert (is_cons s); auto.
case (is_cons_elim H1); intros a (t,H2).
rewrite H2; rewrite length_eq_cons; unfold DNS; repeat rewrite rem_cons; auto.
assert (is_cons (length s)); auto.
assert (is_cons s); auto.
case (is_cons_elim H1); intros a (t,H2).
rewrite H2; rewrite length_eq_cons; unfold DNS; repeat rewrite rem_cons; auto.
Qed.
Global Hint Resolve length_rem : core.

Lemma infinite_length : forall D (s:DS D), infinite s -> infinite (length s).
intro D; assert (forall (s:DS D), infinite s -> forall n, n == length s -> infinite n).
cofix infinite_length; intros.
case H; intros; apply inf_intro.
rewrite H0; auto.
apply infinite_length with (rem s); auto.
rewrite H0; auto.
intros; apply H with s; auto.
Qed.
Global Hint Resolve infinite_length : core.

Lemma length_infinite : forall D (s:DS D), infinite (length s) -> infinite s.
intro D; assert (forall (n:DN), infinite n -> forall (s:DS D), n == length s -> infinite s).
cofix length_infinite; intros.
case H; intros; apply inf_intro.
assert (is_cons (length s)); auto.
rewrite <- H0; auto.
apply length_infinite with (rem n); auto.
rewrite H0; auto.
intros; apply H with (length s); auto.
Qed.
Global Hint Immediate length_infinite : core.
