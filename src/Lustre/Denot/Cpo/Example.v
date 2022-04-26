Require Export Systems.
Require Export Cpo_nat.

(** * Example.v: example from Kahn's IFIT 74 paper *)

(** ** Definitions of nodes *)

Definition D := nat.

(** - f U V = app U (app V (f (rem U) (rem V))) *)
Definition Funf : (DS D -C-> DS D -C-> DS D) -c> (DS D) -C-> (DS D) -C-> DS D.
apply curry.
apply curry.
pose (F:=FST (DS D -C-> DS D -C-> DS D) (DS D) @_ 
             (FST (Dprod ((DS D) -C->(DS D) -C-> DS D) (DS D)) (DS D))).
pose (U:=SND ((DS D) -C-> (DS D) -C-> DS D) (DS D) @_ 
             (FST (Dprod ((DS D) -C->(DS D) -C-> DS D) (DS D)) (DS D))).
pose (V:=SND (Dprod ((DS D) -C->(DS D) -C-> DS D) (DS D)) (DS D)).
apply (fcont_comp2 (D1:=Dprod (Dprod ((DS D) -C-> (DS D) -C-> DS D) (DS D)) (DS D)) (APP D)).
exact U.
apply (fcont_comp2 (D1:=Dprod (Dprod (DS D -C-> DS D -C-> DS D) (DS D)) (DS D)) (APP D)).
exact V.
exact ((AP (DS D) (DS D -C-> DS D)  @3_ F)(REM D @_ U) (REM D @_  V)).
Defined.

Lemma Funf_eq : forall (f : DS D -C-> DS D -C-> DS D) (U V : DS D),
       Funf f U V == app U (app V (f (rem U) (rem V))).
trivial.
Qed.

Definition f : DS D -C-> DS D -C-> DS D := FIXP _ Funf.

Lemma f_eq : forall (p1 p2:DS D),
            f p1 p2 == app p1 (app p2 (f (rem p1) (rem p2))).
unfold f; intros.
assert (Heq:=FIXP_eq Funf).
assert (Heq1:=fcont_eq_elim Heq p1).
rewrite (fcont_eq_elim Heq1 p2).
auto.
Qed.
Global Hint Resolve f_eq : core.


Lemma first_f_eq : forall (p1 p2:DS D), first (f p1 p2) == first p1.
intros; rewrite f_eq.
rewrite first_app_first; auto.
Qed.
Global Hint Resolve first_f_eq : core.

Lemma rem_f_eq : forall (p1 p2:DS D),
            is_cons p1 -> rem (f p1 p2) == app p2 (f (rem p1) (rem p2)).
intros; rewrite f_eq.
rewrite rem_app; auto.
Qed.
Global Hint Resolve rem_f_eq : core.

Lemma is_cons_f: forall (p1 p2:DS D), is_cons p1 -> is_cons (f p1 p2).
intros; apply is_cons_eq_compat with (app p1 (app p2 (f (rem p1) (rem p2)))); auto.
Qed.

Lemma is_cons_rem_f: forall (p1 p2:DS D), is_cons p1 -> is_cons p2 ->  is_cons (rem (f p1 p2)).
intros; apply is_cons_eq_compat with (rem (app p1 (app p2 (f (rem p1) (rem p2))))); auto.
Qed.

Lemma f_is_cons :  forall (p1 p2:DS D), is_cons (f p1 p2) -> is_cons p1.
 intros; assert (is_cons (app p1 (app p2 (f (rem p1) (rem p2))))).
apply is_cons_eq_compat with (f p1 p2); auto.
apply app_is_cons with (app p2 (f (rem p1) (rem p2))); auto.
Qed.

Lemma rem_f_is_cons :  forall (p1 p2:DS D), is_cons (rem (f p1 p2)) -> is_cons p2.
 intros; assert (is_cons (rem (app p1 (app p2 (f (rem p1) (rem p2)))))).
apply is_cons_eq_compat with (rem (f p1 p2)); auto.
apply app_is_cons with (f (rem p1) (rem p2)); auto.
apply rem_app_is_cons with p1; auto.
Qed.

(** - g1 U = app U g1 (rem (rem U))) *)

Definition Fung1 : (DS D -C-> DS D) -c> DS D -C-> DS D.
apply curry.
apply (fcont_comp2 (D1:=Dprod (DS D -C-> DS D) (DS D)) (APP D)).
apply (SND (DS D -C-> DS D) (DS D)).
apply ((AP (DS D) (DS D) @2_
          (FST (DS D -C-> DS D) (DS D)))
          ((REM D @_ REM D) @_ (SND (DS D -C-> DS D) (DS D)))).
Defined.

Lemma Fung1_eq : forall (g1 : DS D -c> DS D) (p:DS D),
       Fung1 g1 p == app p (g1 (rem (rem p))).
intros; unfold Fung1; unfold curry.
rewrite fcont_COMP_simpl.
rewrite fcont_comp_simpl.
rewrite fcont_COMP_simpl.
rewrite fcont_comp_simpl.
repeat (rewrite fcont_comp2_simpl).
repeat (rewrite fcont_comp_simpl).
rewrite FST_PAIR_simpl.
rewrite SND_PAIR_simpl.
rewrite AP_simpl.
repeat (rewrite APP_simpl); repeat (rewrite REM_simpl).
unfold app; apply (fmon_stable (App D p)).
apply (fcont_stable g1); auto.
Qed.

Lemma Fung1_pair_eq : forall (g1 : DS D -C-> DS D) (p:DS D),
       Fung1 g1 p == app p (g1 (rem (rem p))).
intros; apply (Fung1_eq g1 p).
Qed.

Definition g1 : DS D -c> DS D := FIXP (DS D -C-> DS D) Fung1.

Lemma g1_eq : forall (p:DS D),
            g1 p == app p (g1 (rem (rem p))).
unfold g1; intros.
assert (Heq:=FIXP_eq Fung1).
rewrite (fcont_eq_elim Heq p).
rewrite Fung1_pair_eq; auto.
Qed.
Global Hint Resolve g1_eq : core.

Lemma first_g1_eq : forall (p:DS D), first (g1 p) == first p.
intros; rewrite g1_eq.
rewrite first_app_first; auto.
Qed.

Lemma rem_g1_eq : forall (p:DS D), is_cons p -> rem (g1 p) == g1 (rem (rem p)).
intros; rewrite g1_eq.
rewrite rem_app; auto.
Qed.

Lemma is_cons_g1 : forall (p:DS D), is_cons p -> is_cons (g1 p).
intros; apply is_cons_eq_compat with (app p (g1 (rem (rem p)))); auto.
Qed.
Global Hint Resolve is_cons_g1 : core.

Lemma g1_is_cons : forall (p:DS D), is_cons (g1 p) -> is_cons p.
intros; assert (is_cons (app p (g1 (rem (rem p))))).
apply is_cons_eq_compat with (g1 p); auto.
apply app_is_cons with (g1 (rem (rem p))); auto.
Qed.


(** - g2 U = app (rem U) (g2 (rem (rem U))) *)

Definition Fung2 : (DS D -C-> DS D) -c> DS D -C-> DS D.
apply curry.
apply (fcont_comp2 (D1:=Dprod (DS D -C-> DS D) (DS D)) (APP D)).
apply (REM D @_ (SND (DS D -C-> DS D) (DS D))).
apply ((AP (DS D) (DS D) @2_
          (FST (DS D -C-> DS D) (DS D)))
          ((REM D @_ REM D) @_ (SND (DS D -C-> DS D) (DS D)))).
Defined.

Lemma Fung2_eq : forall (g2 : DS D -c> DS D) (p:DS D),
       Fung2 g2 p == app (rem p) (g2 (rem (rem p))).
intros; unfold Fung2,curry.
rewrite fcont_COMP_simpl.
rewrite fcont_comp_simpl.
rewrite fcont_COMP_simpl.
rewrite fcont_comp_simpl.
repeat (rewrite fcont_comp2_simpl).
repeat (rewrite fcont_comp_simpl).
rewrite FST_PAIR_simpl.
rewrite SND_PAIR_simpl.
rewrite AP_simpl.
repeat (rewrite APP_simpl); repeat (rewrite REM_simpl).
unfold app; apply (fmon_stable (App D (rem p))).
apply (fcont_stable g2); auto.
Qed.

Definition g2 : DS D -c> DS D := FIXP (DS D -C-> DS D) Fung2.

Lemma g2_eq : forall (p:DS D), g2 p == app (rem p) (g2 (rem (rem p))).
unfold g2; intros.
assert (Heq:=FIXP_eq Fung2).
rewrite (fcont_eq_elim Heq p).
rewrite Fung2_eq; auto.
Qed.
Global Hint Resolve g2_eq : core.

Lemma first_g2_eq : forall (p:DS D), first (g2 p) == first (rem p).
intros; rewrite g2_eq.
rewrite first_app_first; auto.
Qed.

Lemma rem_g2_eq : forall (p:DS D), is_cons (rem p) -> rem (g2 p) == g2 (rem (rem p)).
intros; rewrite g2_eq.
rewrite rem_app; auto.
Qed.

Lemma is_cons_g2 : forall (p:DS D), is_cons (rem p) -> is_cons (g2 p).
intros; apply is_cons_eq_compat with (app (rem p) (g2 (rem (rem p)))); auto.
Qed.
Global Hint Resolve is_cons_g2 : core.

Lemma g2_is_cons : forall (p:DS D), is_cons (g2 p) -> is_cons (rem p).
intros; assert (is_cons (app (rem p) (g2 (rem (rem p))))).
apply is_cons_eq_compat with (g2 p); auto.
apply app_is_cons with (g2 (rem (rem p))); auto.
Qed.

(** - h n s = cons n s *)
Definition h (n:nat) : DS D -c> DS D := CONS n.

(** ** Definition of the system *)
Inductive LI : Type := .
Inductive LO : Type := X | Y | Z | T1 | T2.

Definition SL : LI+LO -> Type := fun x => D.

(** - X = f Y Z;   Y = h 0 T1;  Z = h 1 T2;  T1 = g1 X;  T2 = g2 X *)  
Definition sys : system SL := 
    fun x : LO => match x with  
                X   => (f @2_ (PROJ (DS_fam SL) (inr LI Y))) (PROJ (DS_fam SL) (inr LI Z))
             |  Y   =>  h O @_ PROJ (DS_fam SL) (inr LI T1)
             |  Z  =>  h 1 @_ PROJ (DS_fam SL) (inr LI T2) 
             |  T1 => g1 @_ PROJ (DS_fam SL) (inr LI X) 
             |  T2 => g2 @_ PROJ (DS_fam SL) (inr LI X) 
                           end.

(** - The system has no inputs  *)

Definition init : Dprodi (DS_fam (inlSL SL)) := fun i : LI => match i with end.

(** - Equation associated to the system *)

Definition EQN_sys : Dprodi (DS_fam SL) -c> Dprodi (DS_fam SL) 
               := EQN_of_system sys init.

(** - The result is given on the X node *)

Definition result : DS D := sol_of_system SL sys init (inr LI X).

(** ** Properties *)

(** - X == f (h O (g1 X)) (h 1 (g2 X)) *)

Definition  FunX : DS D -c> DS D := (f @2_ (h O @_ g1)) (h 1 @_ g2).

Lemma FunX_simpl : forall (s:DS D), FunX s = f (h O (g1 s)) (h 1 (g2 s)).
trivial.
Qed.

Lemma eqn_sys_FunX : 
     forall p : Dprodi (DS_fam SL),
     fcont_compn EQN_sys 2 p (inr LI X) == FunX (p (inr LI X)).
intros; simpl.
repeat (rewrite fcont_comp_simpl).
unfold EQN_sys at 1.
apply Oeq_trans with
   (eqn_of_system sys init (EQN_sys (EQN_sys p)) (inr LI X)).
trivial.
simpl; unfold FunX.
repeat (rewrite fcont_comp_simpl).
repeat (rewrite fcont_comp2_simpl).
apply (fcont_eq_compat2 (D1:=DS D) (D2:=DS D) (D3:=DS D)).
apply Oeq_trans with (EQN_sys (EQN_sys p)  (inr LI Y)); auto.
apply Oeq_trans with (EQN_sys (EQN_sys p)  (inr LI Z)); auto.
Qed.

Lemma result_eq : result == FIXP (DS D) FunX.
unfold result.
rewrite sol_of_system_simpl.
apply Oeq_trans with (FIXP (Dprodi (DS_fam SL)) (fcont_compn EQN_sys (S (S O))) (inr LI X)).
assert (FIXP (Dprodi (DS_fam SL)) (EQN_of_system sys init) ==
            FIXP (Dprodi (DS_fam SL)) (fcont_compn (D:=Dprodi (DS_fam SL)) EQN_sys 2)); auto.
apply Oeq_sym; apply (FIXP_compn EQN_sys 2).
apply (FIXP_proj (F:= fcont_compn (D:=Dprodi (DS_fam SL)) EQN_sys 2) (i:=inr LI X)).
exact eqn_sys_FunX.
Qed.

Lemma lem1 : forall s:DS D, FunX s == cons O (cons 1 (f (g1 s) (g2 s))).
intros; rewrite FunX_simpl.
apply Oeq_trans with (1:=f_eq (h 0 (g1 s)) (h 1 (g2 s))).
unfold h.
repeat (rewrite CONS_simpl).
repeat (rewrite app_cons); repeat (rewrite first_cons);
  repeat (rewrite rem_cons); repeat (rewrite app_cons);trivial.
Qed.

Lemma R_is_cons : forall s t, t == f (g1 s) (g2 s) -> is_cons s -> is_cons t.
intros; apply is_cons_eq_compat with (f (g1 s) (g2 s)); auto.
assert (is_cons (g1 s)); auto.
apply is_cons_f; auto.
Qed.

Lemma R_is_cons_rem : forall s t, t == f (g1 s) (g2 s) 
            -> is_cons (rem s) -> is_cons (rem t).
intros; apply is_cons_eq_compat with (rem (f (g1 s) (g2 s))); auto.
apply is_cons_rem_f.
assert (is_cons s); auto.
apply is_cons_g2; auto.
Qed.

Lemma R_is_cons_inv : forall s t, t == f (g1 s) (g2 s) -> is_cons t -> is_cons s.
intros; assert (is_cons (f (g1 s) (g2 s))).
apply is_cons_eq_compat with t; auto.
assert (is_cons (g1 s)).
apply f_is_cons with (g2 s); auto.
apply g1_is_cons; trivial.
Qed.

Lemma R_is_cons_rem_inv : forall s t, t == f (g1 s) (g2 s) 
            -> is_cons (rem t) -> is_cons (rem s).
intros; assert (is_cons (rem (f (g1 s) (g2 s)))).
apply is_cons_eq_compat with (rem t); auto.
assert (is_cons (g2 s)).
apply rem_f_is_cons with (g1 s); auto.
apply g2_is_cons; trivial.
Qed.

Lemma lem2 : forall s:DS D, s == f (g1 s) (g2 s).
intros; apply DS_bisimulation2 with (R:= fun s t => t == f (g1 s) (g2 s)); auto; intros.
apply Oeq_trans with y1; auto.
apply Oeq_trans with (f (g1 x1) (g2 x1)); auto.
apply (fcont_eq_compat2 f); apply fcont_stable; trivial.
(* first x == first y *)
rewrite H0; rewrite f_eq.
rewrite first_app_first.
rewrite g1_eq.
rewrite first_app_first; auto.
(* first (rem x) == first (rem y) *)
rewrite H0; rewrite f_eq.
assert (is_cons x).
case H; intros; auto.
apply R_is_cons_inv with y; trivial.
apply rem_is_cons; trivial.
rewrite rem_app; auto.
rewrite first_app_first.
rewrite g2_eq; auto.
(* R (rem (rem x)) (rem (rem y)) *)
rewrite H0.
assert (is_cons (rem x)).
case H; intros; auto.
apply R_is_cons_rem_inv with y; trivial.
assert (is_cons x); auto.
rewrite (f_eq (g1 x) (g2 x)).
rewrite rem_app.
2:auto.
rewrite rem_app.
2:auto.
apply (fcont_eq_compat2 f); simpl.
apply rem_g1_eq; auto.
apply rem_g2_eq; auto.
Qed.

(** - result is an infinite stream alternating 0 and 1 *)
Lemma result_alt : result == cons O (cons 1 result).
apply Oeq_trans with (1:=result_eq).
apply Oeq_trans with (1:=FIXP_eq FunX).
apply Oeq_trans with (1:=lem1 (FIXP (DS D) FunX)).
apply cons_eq_compat; auto.
apply cons_eq_compat; auto.
apply Oeq_trans with (FIXP (DS D) FunX).
apply Oeq_sym; apply lem2.
apply Oeq_sym; apply result_eq.
Qed.

Lemma result_inf : infinite result.
apply length_infinite.
apply infinite_S.
apply Ole_trans with (length (cons O (cons 1 result))).
rewrite length_eq_cons.
apply DNS_le_compat; rewrite (length_eq_cons (D:=D)); auto.
apply length_le_compat; case result_alt; auto.
Qed.


(*

Eval lazy beta delta iota zeta in pred_nth result 3.

(** ** Test by extraction *)


Extraction NoInline DS_bot. 
Extraction "example" DS_to_list result.

Extraction Language Haskell.
Extraction "example" DS_to_list result.

*)
