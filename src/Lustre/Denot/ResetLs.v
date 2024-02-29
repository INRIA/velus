Require Import List.
Require Import Cpo Reset SDfuns CommonDS.
Import ListNotations.

(** An attempt to prove the equivalence between the reset construct
    of Lucid Synchrone and the one of Denot.SDfuns. *)

(* In "Modular Resetting of Synchronous Data-Flow Programs",
   Hamon & Pouzet encode the reset in two functions:

  let whilenot c = o where
    rec o = true -> if c then false else pre o

  let rec reset_up c x =
    let cond = whilenot c in
    merge cond
      (up (x when cond))
      (reset_up (c when not cond) (x when not cond))


  In Lustre (thèse de Lélio p.39), it gives :

  node true_until(r: bool) returns (c: bool)
  let
    c = true -> if r then false else (pre c);
  tel

  node reset_f(x: int; r: bool) returns (y: int)
  var c: bool;
  let
    c = true_until(r);
    y = merge c (f(x when c)) (reset_f((x, r) when not c));
  tel
 *)


(* en Vélus ?? :

   c = if r then false else (true fby c)

   ou bien, pour faire le même premier instant que LS
   (évite une récurrence instantanée dans le reset)

   c = true -> if r then false else (true fby c)
 *)

(* case booléen : if-then-else *)
Definition scaseb {A} := @scase A bool bool Some bool_eq [true;false].


Lemma scaseb_abs :
  forall A rs (xs ys : DS (sampl A)),
    scaseb (cons abs rs) (PAIR _ _ (cons abs xs) (cons abs ys))
    == cons abs (scaseb rs (PAIR _ _ xs ys)).
Proof.
  intros.
  unfold scaseb.
  rewrite scase_eq at 1.
  rewrite 2 Foldi_cons, Foldi_nil.
  repeat (simpl; autorewrite with cpodb).
  rewrite 2 zip3_cons.
  reflexivity.
Qed.

Lemma scaseb_pres :
  forall A r rs x y (xs ys : DS (sampl A)),
    scaseb (cons (pres r) rs) (PAIR _ _ (cons (pres x) xs) (cons (pres y) ys))
    == cons (pres (if r then x else y)) (scaseb rs (PAIR _ _ xs ys)).
Proof.
  intros.
  unfold scaseb.
  rewrite scase_eq at 1.
  rewrite 2 Foldi_cons, Foldi_nil.
  repeat (simpl; autorewrite with cpodb).
  rewrite 2 zip3_cons.
  destruct r; auto.
Qed.

(* Lemma scaseb_cons : *)
(*   forall A r rs x y (xs ys : DS (sampl A)), *)
(*     scaseb (cons r rs) (PAIR _ _ (cons x xs) (cons y ys)) *)
(*     == cons (match r, x, y with *)
(*              | abs, abs, abs => abs *)
(*              | pres true, pres x, pres y => pres x *)
(*              | pres false, pres x, pres y => pres y *)
(*              | err e, _, _ => err e *)
(*              | _, err e, _ => err e *)
(*              | _, _, err e => err e *)
(*              | _, _, _ => err error_Cl *)
(*              end) (scaseb rs (PAIR _ _ xs ys)). *)
(* Proof. *)
(*   intros. *)
(*   unfold scaseb. *)
(*   rewrite scase_eq at 1. *)
(*   rewrite 2 Foldi_cons, Foldi_nil. *)
(*   repeat (simpl; autorewrite with cpodb). *)
(*   rewrite 2 zip3_cons. *)
(*   destruct r as [| [] |]. *)
(*   4:{ simpl. *)
(*       fcase *)
(*   4: reflexivity. *)
(*   destruct r, x, y; try reflexivity. *)
(*   reflexivity. *)
(*   destruct r as [| [] | ]. *)
(*   auto. *)
(*   destruct r; auto. *)
(* Qed. *)


(* TODO: move *)
Lemma sconst_cons :
    forall A (c:A) b bs,
      sconst c (cons b bs) == cons (if b then pres c else abs) (sconst c bs).
Proof.
  intros.
  apply map_eq_cons.
Qed.

Definition safe_DS {A} : DS (sampl A) -> Prop :=
  DSForall (fun v => match v with err _ => False | _ => True end).

(* when/merge booléen *)
Definition swhenb {A} := @swhen A bool bool Some bool_eq.
Definition smergeb {A} := @smerge A bool bool Some bool_eq [true;false].

(* on part d'une fonction de flots *)
Module VERSION2.

Parameter (I A : Type).
Definition SI := fun _ : I => sampl A.
Definition DS_prod := @DS_prod I.

Parameter (f : DS (sampl A) -C-> DS (sampl A)).

(* <= en vrai, si pas d'infinité... *)
Hypothesis AbsF : forall xs, f (cons abs xs) == cons abs (f xs).
Corollary AbsConstF : f (DS_const abs) == DS_const abs.
Proof.
  apply take_Oeq.
  induction n; auto.
  rewrite DS_const_eq, AbsF, 2 (take_eq (S n)), 2 app_cons, 2 rem_cons.
  now rewrite IHn.
Qed.

Hypothesis LpF : forall xs n, f (take n xs) == take n (f xs).

(* TODO: align ??? *)
(* Hypothesis Halign : *)
(*   forall f n, *)
(*     find_node f G = Some n -> *)
(*     let ins := List.map fst (n_in n) in *)
(*     let Γ := senv_of_ins (n_in n) ++ senv_of_decls (n_out n) ++ get_locals (n_block n) in *)
(*     forall envI, *)
(*     wf_env Γ ins envI (bss ins envI) (envG f envI) -> *)
(*     abs_alignLE envI (envG f envI). *)
(* *)

(* environnement où tous les flots sont égaux à l'entrée *)
Definition env1 : DS (sampl A) -c> DS_prod SI :=
  Dprodi_DISTR _ _ _ (fun _ => ID _).

(* f appliqué aux environnements *)
Definition fs : DS_prod SI -C-> DS_prod SI := DMAPi (fun _ => f).

Lemma fs_env1 :
  forall xs o, fs (env1 xs) o = f xs.
Proof.
  reflexivity.
Qed.

Definition true_until : DS (sampl bool) -C-> DS (sampl bool).
  refine (FIXP _ _).
  apply curry.
  refine ((scaseb @2_ SND _ _) _).
  refine ((PAIR _ _ @2_ _) _).
  - (* true *)
    refine (sconst false @_ AC @_ SND _ _).
  - (* false *)
    refine ((fby @2_ sconst true @_ AC @_ SND _ _) _).
    refine ((AP _ _ @2_ FST _ _) (SND _ _)).
Defined.


Lemma test_take_Oeq:
  forall r,
    infinite r ->
    fby (sconst 3 r) (sconst 3 r) == sconst 3 r.
Proof.
  intros r Infr.
  apply take_Oeq; intro n.
  revert dependent r; induction n; intros; auto.
  apply infinite_decomp in Infr as (vr & r' & Hr & Infr).
  rewrite Hr, sconst_cons.
  destruct vr.
  - rewrite fby_eq, fby1AP_eq, 2 (take_eq (S n)), 2 app_cons, 2 rem_cons.
    apply cons_eq_compat; auto.
    rewrite <- IHn; auto.
    clear IHn Hr r.
    revert dependent r'; induction n; intros r Infr; try reflexivity.
    apply infinite_decomp in Infr as (vr & r' & Hr & Infr).
    rewrite Hr, sconst_cons.
    destruct vr.
    + now rewrite fby_eq, fby1_eq, fby1AP_eq.
    + rewrite fby_eq, fbyA_eq, fby1_eq, fby1AP_eq, 2 (take_eq (S n)), 2 app_cons, 2 rem_cons.
      apply cons_eq_compat, IHn; auto.
  - rewrite fby_eq, fbyA_eq, 2 (take_eq (S n)), 2 app_cons, 2 rem_cons.
    apply cons_eq_compat; auto.
Qed.

(* TODO: ça pour tout ?? *)
Arguments PAIR {D1 D2}.

Lemma true_until_eq :
  forall r, true_until r
       == scaseb r (PAIR
                      (sconst false (AC r))
                      (fby (sconst true (AC r)) (true_until r))).
Proof.
  intros.
  unfold true_until at 1.
  rewrite FIXP_eq.
  reflexivity.
Qed.

Lemma true_until_true :
  forall r,
    safe_DS r ->
    true_until (cons (pres true) r) == cons (pres false) (sconst false (AC r)).
Proof.
 intros r Hsafe.
 (* dérouler la tête *)
 rewrite true_until_eq.
 rewrite AC_cons, 2 sconst_cons.
 rewrite fby_eq, scaseb_pres.
 apply cons_eq_compat; auto.
 (* bisim *)
 eapply DS_bisimulation_allin1 with
   (R := fun U V =>
           exists rs,
             safe_DS rs /\
               U == scaseb rs (PAIR
                                 (sconst false (AC rs))
                                 (fby1 (Some false)(sconst true (AC rs)) U))
             /\ V == (sconst false (AC rs))
   ).
 3:{ exists r. split. auto.
     split. 2: auto.
     rewrite true_until_eq at 1.
     rewrite AC_cons, 2 sconst_cons.
     rewrite fby_eq, scaseb_pres.
     rewrite fby1AP_eq.
     auto.
 }
 { intros * ? Eq1 Eq2.
   setoid_rewrite <- Eq1.
   setoid_rewrite <- Eq2.
   eauto. }
 clear.
 intros U V Hc (rs & Hsafe & Hu & Hv).
 edestruct (@is_cons_elim _ rs) as (vr & rs' & Hrs).
 { destruct Hc as [Hc|Hc].
   - rewrite Hu in Hc.
     apply scase_is_cons in Hc as []; now auto.
   - unfold sconst in Hv. rewrite Hv in Hc.
     now apply map_is_cons, AC_is_cons in Hc.
 }
 rewrite Hrs in Hu, Hv, Hsafe.
 inversion_clear Hsafe as [|?? Hvr Hsafe'].
 rewrite AC_cons, sconst_cons in Hv.
 split.
 - (* first *)
   rewrite Hv, first_cons.
   rewrite Hu at 1.
   rewrite AC_cons, 2 sconst_cons.
   rewrite fby1_eq.
   destruct vr; try tauto.
   + rewrite scaseb_abs, first_cons; auto.
   + rewrite scaseb_pres, first_cons.
     destruct a; auto.
 - (* rem *)
   exists rs'; split; auto.
   split.
   2: now rewrite Hv, rem_cons.
   rewrite Hu at 1.
   rewrite AC_cons, 2 sconst_cons.
   rewrite fby1_eq.
   destruct vr; try tauto.
   + rewrite scaseb_abs, rem_cons.
     rewrite AC_cons, 2 sconst_cons in Hu.
     rewrite fby1_eq in Hu.
     rewrite scaseb_abs in Hu.
     rewrite Hu, rem_cons.
     rewrite fby1AP_eq; auto.
   + rewrite scaseb_pres, rem_cons.
     rewrite AC_cons, 2 sconst_cons in Hu.
     rewrite fby1_eq in Hu.
     rewrite scaseb_pres in Hu.
     rewrite Hu, rem_cons.
     rewrite fby1AP_eq.
     now destruct a.
Qed.

Lemma true_until_false :
  forall r,
    safe_DS r ->
    true_until (cons (pres false) r) == cons (pres true) (true_until r).
Proof.
 intros r Hsafe.
 (* dérouler la tête *)
 rewrite true_until_eq.
 rewrite AC_cons, 2 sconst_cons.
 rewrite fby_eq, scaseb_pres.
 apply cons_eq_compat; auto.
 (* bisim ?????*)
Abort.

Lemma true_until_false :
  forall r, true_until (cons (pres false) r) == cons (pres true) (true_until r).
Proof.
  intros.
  rewrite true_until_eq.
  rewrite AC_cons, 2 sconst_cons.
  rewrite fby_eq, scaseb_pres.
  apply cons_eq_compat; auto.
  unfold true_until.
  rewrite FIXP_fixp.
  revert r.
  apply fixp_ind.
  admit.
  admit.
  intros ftrue_until Hf r.
  autorewrite with cpodb.
  simpl.
  autorewrite with cpodb.
  simpl.
  repeat change (?a, ?b) with (PAIR a b).
  setoid_rewrite <- Hf at 2.
  rewrite AC_cons, 2 sconst_cons.
  rewrite fby_eq.
  rewrite (scaseb_pres _ false _ false true).
  rewrite fby1AP_eq.
Abort. (* pas tout à fait exact *)


(* TODO: redéfinir true_until en co-inductif et comparer les principes
   de raisonnement *)
Lemma true_until_abs :
  forall r, true_until (cons abs r) == cons abs (true_until r).
Proof.
  intros.
  rewrite true_until_eq.
  rewrite AC_cons, 2 sconst_cons.
  rewrite fby_eq, scaseb_abs.
  apply cons_eq_compat; auto.
  unfold true_until.
  rewrite FIXP_fixp.
  revert r.
  apply fixp_ind.
  admit.
  admit.
  intros ftrue_until Hf r.
  change (fcontit ?a ?b) with (a b).
  autorewrite with cpodb; simpl.
  repeat change (?a, ?b) with (PAIR a b).
  rewrite <- (Hf r).
  rewrite AC_cons, 2 sconst_cons.
  rewrite fby_eq.
  rewrite (scaseb_abs _ r (sconst false (AC r))).
  rewrite fbyA_eq.
  reflexivity.
Admitted.


Arguments PROJ {I Di}.
Arguments FST {D1 D2}.
Arguments SND {D1 D2}.
Arguments curry {D1 D2 D3}.

(* TEST: un merge initialisant *)
Module TEST.
(* Context {A : Type}. *)

Definition expecta : forall {A}, DS (sampl A) -C-> DS (sampl A) :=
  fun _ => DSCASE _ _ (fun v => match v with
                | abs => ID _
                | pres _ => MAP (fun _ => err error_Cl)
                | err e => MAP (fun _ => err e)
                    end).

Lemma expecta_eq :
  forall A c cs,
    @expecta A (cons c cs) ==
      match c with
      | abs => cs
      | pres _ => map (fun _ => err error_Cl) cs
      | err _ => map (fun _ => c) cs
      end.
Proof.
  intros.
  unfold expecta.
  rewrite DSCASE_simpl, DScase_cons.
  destruct c; reflexivity.
Qed.


Lemma expecta_bot : forall A, @expecta A 0 == 0.
Proof.
  unfold expecta.
  split; auto.
  apply DScase_bot.
Qed.

Hint Rewrite
  fcont_comp_simpl
  fcont_comp2_simpl
  fcont_comp3_simpl
  curry_Curry
  Curry_simpl
  SND_simpl Snd_simpl
  FST_simpl Fst_simpl
  AP_simpl
  : localdb.


Definition when :  forall {A}, DS (sampl bool) -C-> DS (sampl A) -C-> DS (sampl A) :=
  fun _ => ZIP (fun c x => match c, x with
      | abs, abs => abs
      | pres true, pres v => (pres v)
      | pres false, pres v => abs
      | _, _ => err error_Cl
      end).

(* Parameter when : forall {A}, DS (sampl bool) -C-> DS (sampl A) -C-> DS (sampl A). *)
Lemma when_eq :
  forall A c cs x xs,
    @when A (cons c cs) (cons x xs) ==
      match c, x with
      | abs, abs => cons abs (when cs xs)
      | pres true, pres v => cons (pres v) (when cs xs)
      | pres false, pres v => cons abs (when cs xs)
      | _, _ => cons (err error_Cl) (when cs xs)
      end.
Proof.
  intros.
  unfold when at 1.
  rewrite zip_cons.
  destruct c as [|[]|], x; auto.
Qed.

Parameter whennot : forall {A}, DS (sampl bool) -C-> DS (sampl A) -C-> DS (sampl A).
Hypothesis whennot_eq :
  forall A c cs x xs,
    @whennot A (cons c cs) (cons x xs) ==
      match c, x with
      | abs, abs => cons abs (whennot cs xs)
      | pres false, pres v => cons (pres v) (whennot cs xs)
      | pres true, pres v => cons abs (whennot cs xs)
      | _, _ => map (fun _ => err error_Cl) xs
      end.

(* TODO: pareil pour when ?? *)
Parameter merge : forall {A}, DS (sampl bool) -C-> DS (sampl A) -C-> DS (sampl A) -C-> DS (sampl A).
  (* refine (FIXP _ _). *)
  (* apply curry, curry, curry. *)
(*   (* match goal with *) *)
(*   (* | |- _ (_ (Dprod ?pl ?pr) _) => *) *)
(*   (*     pose (fmerge := FST @_ FST @_ @FST pl pr) *) *)
(*   (*     ; pose (cs := SND @_ FST @_ @FST pl pr) *) *)
(*   (*     ; pose (xs := SND @_ @FST pl pr) *) *)
(*   (*     ; pose (ys := @SND pl pr) *) *)
(*   (* end. *) *)
(*   refine ((DSCASE _ _ @2_ _) (SND @_ FST @_ FST)). *)
(*   apply ford_fcont_shift; intro c. *)
(*   apply curry. *)
(*   match goal with *)
(*   | |- _ (_ (Dprod ?pl ?pr) _) => *)
(*       pose (fmerge := FST @_ FST @_ @FST pl pr) *)
(*       ; pose (cs := SND @_ FST @_ @FST pl pr) *)
(*       ; pose (xs := SND @_ @FST pl pr) *)
(*       ; pose (ys := @SND pl pr) *)
(*   end. *)

(*   refine *)
(*     (match c with *)
(*      | abs => CONS abs @_ ((AP _ _ @3_ fmerge) cs (expecta @_ xs) _) *)
(*                (* (AP _ _ @_expecta @_ xs) (expecta ys)) *) *)
(*      (* | pres true => app xs (merge cs (rem xs) (expecta ys)) *) *)
(*      (* | pres false => app ys (merge cs (expecta xs) (rem ys)) *) *)
(*                   (* | err e => map (fun _ => err e) xs *) *)
(*      | _ => _ *)
(*      end). *)

(* problèmes :
   - pres T/F ne vérifie pas la présence de tête de xs/ys
   - abs ne propage pas les erreurs de expecta
 *)
Hypothesis merge_eq :
  forall A c cs xs ys,
    @merge A (cons c cs) xs ys ==
      match c with
      | abs => cons abs (merge cs (expecta xs) (expecta ys))
      | pres true => app xs (merge cs (rem xs) (expecta ys))
      | pres false => app ys (merge cs (expecta xs) (rem ys))
      | err e => map (fun _ => err e) xs
      end.

Hypothesis merge_is_cons :
  forall A cs xs ys,
    is_cons (@merge A cs xs ys) -> is_cons cs.

Definition reset : DS (sampl bool) -C-> DS (sampl A) -C-> DS (sampl A).
  refine (FIXP _ _).
  apply curry, curry.
  match goal with
  | |- _ (_ (Dprod ?pl ?pr) _) =>
      pose (freset := FST @_ @FST pl pr)
      ; pose (r := SND @_ @FST pl pr)
      ; pose (x := @SND pl pr)
      ; pose (c := true_until @_ r)
  end.
  refine ((merge @3_ c) _ _).
  - (* true *)
    refine (f @_ (when @2_ c) x).
  - (* false *)
    refine ((AP _ _ @3_ freset)
              ((whennot @2_ c) r)
              ((whennot @2_ c) x)).
Defined.

Lemma merge_false :
  forall A rs (xs ys : DS (sampl A)),
    merge (sconst false rs) xs ys == ys.
Proof.
  intros.
  eapply DS_bisimulation_allin1
    with (R := fun U V => exists rs xs ys,
                   U == merge (sconst false rs) xs ys
                   /\ V == ys).
  3:eauto.
  admit.
  clear.
  intros U V Hc (rs & xs & ys & Hu & Hv).
  edestruct (@is_cons_elim _ rs) as (vr & rs' & Hrs).
  { destruct Hc as [Hc|Hc].
    - rewrite Hu in Hc.
      apply merge_is_cons in Hc.
      unfold sconst in Hc.
      now apply map_is_cons in Hc.
    - unfold sconst in Hv. rewrite Hv in Hc.
 (*      now apply map_is_cons, AC_is_cons in Hc. *)
 (* } *)
      (*  setoid_rewrite Hu. *)
(* Qed. *)
Abort. (* il faut beaucoup plus d'hypothèses sur les horloges de xs, ys etc.. *)



Lemma reset_eq :
  forall r x,
    reset r x ==
      let c := true_until r in
      merge c (f (when c x)) (reset (whennot c r) (whennot c x)).
Proof.
  intros.
  unfold reset at 1.
  rewrite FIXP_eq.
  reflexivity.
Qed.

(* Lemma reset_true : *)
(*   forall rs xs, *)
(*     reset (cons (pres true) rs) xs == 0. *)


Lemma reset_abs :
  forall rs xs,
    reset (cons abs rs) (cons abs xs) == cons abs (reset rs xs).
Proof.
  intros.
  rewrite 2 reset_eq; simpl.
  rewrite true_until_abs.
  rewrite when_eq, 2 whennot_eq.
  rewrite AbsF.
  rewrite merge_eq.
  rewrite expecta_eq.
  apply cons_eq_compat; auto.
  (* jusque là tout va bien *)
  apply fcont_stable.

  unfold reset.
  rewrite FIXP_fixp.
  revert rs xs.
  apply fixp_ind.
  admit.
  { intros; now rewrite expecta_bot. }
  intros freset Hf rs xs.
  change (fcontit ?a ?b) with (a b).
  autorewrite with localdb.
  simpl.
  setoid_rewrite <- Hf at 2.
  rewrite true_until_abs.
  rewrite when_eq, 2 whennot_eq.
  rewrite AbsF, merge_eq, 2 expecta_eq.
  reflexivity.
Admitted.


Lemma true_until_false :
  forall r,
    safe_DS r ->
    true_until (cons (pres false) r) == cons (pres true) (true_until r).
Proof.
 intros r Hsafe.
 (* dérouler la tête *)
 rewrite true_until_eq.
 rewrite AC_cons, 2 sconst_cons.
 rewrite fby_eq, scaseb_pres.
 apply cons_eq_compat; auto.
 (* induction *)
 unfold true_until.
 rewrite FIXP_fixp.
 revert dependent r.
 apply fixp_ind.
 admit.
 { intros. admit. }
 intros ftrue_until Hf rs Hsr.
 change (fcontit ?a ?b) with (a b).
 autorewrite with localdb.
 simpl.
 setoid_rewrite <- Hf at 2. 2: auto.
 rewrite AC_cons, 2 sconst_cons.
 rewrite fby_eq, (scaseb_pres _ _ _ false), fby1AP_eq.
Abort. (* FAUX ??? *)


Set Nested Proofs Allowed.
Lemma when_false :
  forall A B (xs : DS (sampl A)) (ys : DS (sampl B)),
    infinite xs ->
    safe_DS ys ->
    AC xs == AC ys ->
    when (sconst false (AC xs)) ys == DS_const abs.
Proof.
  intros * Hinf Hsafe Hac.
  apply take_Oeq; intro n.
  revert Hac Hsafe Hinf; revert xs ys; induction n; intros; auto.
  apply infinite_decomp in Hinf as (?&?& Hx &?); rewrite Hx in *.
  edestruct (@is_cons_elim _ ys) as (y &?& Hy).
  { eapply AC_is_cons; now rewrite <- Hac, AC_cons. }
  rewrite Hy, 2 AC_cons in *.
  apply Con_eq_simpl in Hac as [].
  rewrite DS_const_eq, sconst_cons.
  rewrite 2 (take_eq (S n)), app_cons, when_eq.
  inversion Hsafe.
  destruct x,y; subst; try tauto; try congruence.
  all: rewrite app_cons, 2 rem_cons; auto.
Qed.

Lemma whennot_false :
  forall A B (xs : DS (sampl A)) (ys : DS (sampl B)),
    infinite xs ->
    safe_DS ys ->
    AC xs == AC ys ->
    whennot (sconst false (AC xs)) ys == ys.
Proof.
  intros * Hinf Hsafe Hac.
  apply take_Oeq; intro n.
  revert Hac Hsafe Hinf; revert xs ys; induction n; intros; auto.
  apply infinite_decomp in Hinf as (?&?& Hx &?); rewrite Hx in *.
  edestruct (@is_cons_elim _ ys) as (y &?& Hy).
  { eapply AC_is_cons; now rewrite <- Hac, AC_cons. }
  rewrite Hy, 2 AC_cons in *.
  apply Con_eq_simpl in Hac as [].
  rewrite sconst_cons.
  rewrite 2 (take_eq (S n)), app_cons, whennot_eq.
  inversion Hsafe.
  destruct x,y; subst; try tauto; try congruence.
  all: rewrite app_cons, 2 rem_cons; auto.
Qed.

Lemma merge_false :
  forall A xs (ys : DS (sampl A)),
    infinite xs ->
    safe_DS ys ->
    xs == AC ys ->
    merge (sconst false xs) (DS_const abs) ys == ys.
Proof.
  intros * Hinf Hsafe Hxs.
  apply take_Oeq; intro n.
  revert Hsafe Hinf Hxs; revert xs ys; induction n; intros; auto.
  apply infinite_decomp in Hinf as (?&?& Hx &?); rewrite Hx in *.
  edestruct (@is_cons_elim _ ys) as (y &?& Hy).
  { eapply AC_is_cons; now rewrite <- Hxs. }
  rewrite Hy, AC_cons in *.
  apply Con_eq_simpl in Hxs as [].
  rewrite DS_const_eq, sconst_cons.
  inversion Hsafe.
  destruct x,y; subst; try tauto; try congruence; rewrite merge_eq, expecta_eq.
  - rewrite 2 (take_eq (S n)), 3 app_cons, 2 rem_cons; auto.
  - rewrite expecta_eq.
    rewrite 2 (take_eq (S n)), 2 app_cons, 2 rem_cons; auto.
Qed.

Lemma f_true_until :
  forall rs xs,
    f (when (true_until rs) xs) == when (true_until rs) (f xs).
Proof.
  (* sans doute pas facile *)
Admitted.

(* prédicat co-inductif, peut-être plus facile à manipuler ?
   équivalent de DS_bisimulation
   TODO: pareil avec firsn, nrem ?
 *)
Section DS_eq.
Variable (B : Type).
CoInductive ds_eq : DS B -> DS B -> Prop :=
| De :
    forall x y,
      first x == first y ->
      ds_eq (rem x) (rem y) ->
      ds_eq x y.

Lemma Oeq_ds_eq : forall x y, x == y -> ds_eq x y.
Proof.
  cofix Cof; intros.
  apply De; auto.
Qed.

Lemma ds_eq_Oeq : forall x y, ds_eq x y -> x == y.
Proof.
  intros.
  apply DS_bisimulation_allin1 with (R := fun U V => exists x y, ds_eq x y /\ U == x /\ V == y).
  - intros * Eq Eq1 Eq2.
    setoid_rewrite <- Eq1.
    setoid_rewrite <- Eq2.
    eauto.
  - clear.
    intros U V Hc (x & y & Eq & Hu & Hv).
    inversion_clear Eq.
    setoid_rewrite Hu.
    setoid_rewrite Hv.
    split; auto.
    exists (rem x), (rem y); auto.
  - eauto.
Qed.

Lemma ds_eq_Oeq_iff : forall x y, ds_eq x y <-> x == y.
Proof.
  split; eauto using ds_eq_Oeq, Oeq_ds_eq.
Qed.
End DS_eq.


Section DSn_eq.
Variable (B : Type).
CoInductive dsn_eq : DS B -> DS B -> Prop :=
| Den :
    forall x y n,
      take (S n) x == take (S n) y ->
      dsn_eq (nrem (S n) x) (nrem (S n) y) ->
      dsn_eq x y.

Lemma Oeq_dsn_eq : forall x y, x == y -> dsn_eq x y.
Proof.
  cofix Cof; intros.
  apply Den with (n := O); try (simpl; now auto).
  now rewrite H.
Qed.

Lemma dsn_eq_Oeq : forall x y, dsn_eq x y -> x == y.
Proof.
  intros.
  apply DS_bisimulation_allin1 with (R := fun U V => exists x y, dsn_eq x y /\ U == x /\ V == y).
  - intros * Eq Eq1 Eq2.
    setoid_rewrite <- Eq1.
    setoid_rewrite <- Eq2.
    eauto.
  - clear.
    intros U V Hc (x & y & Eq & Hu & Hv).
    inversion_clear Eq.
    setoid_rewrite Hu.
    setoid_rewrite Hv.
    clear Hu Hv.
    revert dependent x.
    revert dependent y.
    induction n; intros.
    + rewrite 2 take_1 in H; split; eauto.
    + apply IHn.
      * admit.
      * eapply Den with O.
        2:{ admit. }
        rewrite 2 take_1.
        Search first nrem.
        admit.
  - eauto.
Admitted. (* un peu chiant mais ok *)

Lemma dsn_eq_Oeq_iff : forall x y, dsn_eq x y <-> x == y.
Proof.
  split; eauto using dsn_eq_Oeq, Oeq_dsn_eq.
Qed.
End DSn_eq.


Theorem reset_match :
  forall rs xs o,
    infinite rs ->
    safe_DS rs ->
    safe_DS xs ->
    AC xs == AC rs ->
    reset rs xs == sreset fs (AC rs) (env1 xs) o.
Proof.
  intros * Hinf Hsr Hsx Hac.
  rewrite <- PROJ_simpl, sreset_eq.
  rewrite reset_eq.

  apply dsn_eq_Oeq.

  remember_ds (merge _ _ _) as U.
  remember_ds (PROJ _ _) as V.
  revert dependent xs.
  revert dependent rs.
  revert U V.
  cofix Cof; intros.

  eapply Den with (n:=O).
  - admit.
  - eapply Cof.


  eapply DS_bisimulation_allin1 with
    (R := fun U V =>
            exists rs xs ys,
              (* ys ???? *)
              let c := true_until rs in
              infinite rs /\ safe_DS rs /\ safe_DS xs /\ AC xs == AC rs
              /\ U == merge c ys (reset (whennot c rs) (whennot c xs))
              /\ V == PROJ o (sreset_aux fs (AC rs) (env1 xs) (env1 ys))
    ).
  3:{ exists rs, xs, (f xs).
      split; [auto|].
      split; [auto|].
      split; [auto|].
      split; [auto|].
      split; [|auto].
      cbv zeta.
      rewrite f_true_until.



  intros * Hinf Hsr Hsx Hac.
  rewrite reset_eq.
  rewrite <- PROJ_simpl, sreset_eq.
  assert (exists vr rs', rs == cons vr rs') as (vr & rs' & Hrs).
  admit.
  assert (exists vx xs', xs == cons vx xs') as (vx & xs' & Hxs).
  admit.
  cbv zeta.
  remember_ds (true_until rs) as cs.
  rewrite Hrs in *.
  rewrite Hxs in *.
  inversion_clear Hsr as [|?? Hvr Hsr'].
  inversion_clear Hsx as [|?? Hvx Hsx'].
  repeat rewrite AC_cons in *.
  apply Con_eq_simpl in Hac as [Hrx Hac].
  inversion Hinf as [ _ Hinf' ]; rewrite rem_cons in Hinf'.
  destruct vr as [|vr|], vx as [|vx|]; try tauto; try congruence.
  - (* vr = vx = abs *)
    rewrite true_until_abs in Hcs.
    rewrite Hcs.
    rewrite when_eq, 2 whennot_eq.
    rewrite sreset_aux_eq.
    rewrite PROJ_simpl, APP_env_eq, fs_env1.
    rewrite AbsF, merge_eq, reset_abs.
    rewrite AbsF, app_cons.
    rewrite 2 expecta_eq.
    (* coind ok ici ? *)
    admit.
  - destruct vr.
    + (* pres true *)
      rewrite true_until_true in Hcs; auto.
      rewrite Hcs.
      rewrite 2 sreset_aux_eq.
      rewrite PROJ_simpl, APP_env_eq, fs_env1, <- PROJ_simpl.
      rewrite when_eq, 2 whennot_eq.
      rewrite merge_eq.
      rewrite AbsF, expecta_eq, when_false, AbsConstF; auto.
      rewrite 2 whennot_false; auto.
      rewrite merge_false; auto.
      rewrite app_rem.
    + (* pas de reset *)
Qed.

End TEST.


(* c = true_until(r); *)
(* c = true -> true_until(r); ??? *)
(* y = merge c (f(x when c)) (reset_f((x, r) when not c)); *)

  (* reset à la lucid synchrone *)
Definition reset : DS (sampl bool) -C-> DS (sampl A) -C-> DS (sampl A).
  refine (FIXP _ _).
  apply curry, curry.
  match goal with
  | |- _ (_ (Dprod ?pl ?pr) _) =>
      pose (freset := FST _ _ @_ FST pl pr)
      ; pose (r := SND _ _ @_ FST pl pr)
      ; pose (x := SND pl pr)
      ; pose (c := true_until @_ r)
  end.
  refine ((smergeb @2_ c) _).
  refine ((PAIR @2_ _) _).
  - (* true *)
    refine (f @_ (swhenb true @2_ x) c).
  - (* false *)
    refine ((AP _ _ @3_ freset)
              ((swhenb false @2_ r) c)
              ((swhenb false @2_ x) c)).
Defined.

Lemma reset_eq :
  forall r x,
    reset r x ==
      let c := true_until r in
      smergeb c
        (f (swhenb true x c),
          reset (swhenb false r c) (swhenb false x c)).
Proof.
  intros.
  unfold reset at 1.
  rewrite FIXP_eq.
  reflexivity.
Qed.

(* propriétés :
   - xs when true == xs
   - ?
 *)


Lemma fs_env1 :
  forall xs o, fs (env1 xs) o = f xs.
Proof.
  reflexivity.
Qed.

Lemma reset_abs :
  forall rs xs,
    reset (cons abs rs) (cons abs xs) == cons abs (reset rs xs).
Proof.
  intros.
  rewrite 2 reset_eq; simpl.
  change (?a, ?b) with (PAIR a b).
  rewrite true_until_abs.
  unfold swhenb at 1 2 3.
  rewrite 3 swhen_eq.
  rewrite AbsF.
Qed.

Theorem reset_match :
  forall rs xs o,
    safe_DS rs ->
    safe_DS xs ->
    AC xs == AC rs ->
    reset rs xs == sreset fs (AC rs) (env1 xs) o.
Proof.
  intros * Hsr Hsx Hac.
  rewrite reset_eq.
  rewrite <- PROJ_simpl, sreset_eq.
  assert (exists vr rs', rs == cons vr rs') as (vr & rs' & Hrs).
  admit.
  assert (exists vx xs', xs == cons vx xs') as (vx & xs' & Hxs).
  admit.
  change (?a, ?b) with (PAIR a b).
  cbv zeta.
  remember_ds (true_until rs) as cs.
  rewrite Hrs in *.
  rewrite Hxs in *.
  inversion_clear Hsr as [|?? Hvr Hsr'].
  inversion_clear Hsx as [|?? Hvx Hsx'].
  repeat rewrite AC_cons in *.
  apply Con_eq_simpl in Hac as [Hrx Hac].
  destruct vr, vx; try tauto; try congruence.
  - (* vr = vx = abs *)
    rewrite true_until_abs in Hcs.
    rewrite Hcs.
    unfold swhenb.
    repeat rewrite swhen_eq.
    rewrite sreset_aux_eq.
    rewrite PROJ_simpl, APP_env_eq, fs_env1.
    rewrite AbsF.
  -
Qed.

End VERSION2.


(* on part d'une fonction d'environments *)
Module VERSION1.
Parameter (I A : Type).
Definition SI := fun _ : I => sampl A.
Definition DS_prod := @DS_prod I.

Parameter (f : DS_prod SI -C-> DS_prod SI).
Parameter (f_i f_o : I). (* nom de l'entrée et de la sortie dans f *)

(* environnement où tous les flots sont égaux à l'entrée *)
Definition env1 : DS (sampl A) -c> DS_prod SI :=
  Dprodi_DISTR _ _ _ (fun _ => ID _).

Definition fs : DS (sampl A) -C-> DS (sampl A) :=
  PROJ _ f_o @_ f @_ env1.


(* reset à la lucid synchrone *)
Parameter reset : DS bool -C-> DS (sampl A) -C-> DS (sampl A).

Theorem reset_match :
  forall r X, reset r (X f_i) == sreset f r X f_o.
Abort.
End VERSION1.





(* avec échantillonnage *)
Definition true_until : DS (sampl bool) -C-> DS (sampl bool).
  refine (FIXP _ _).
  apply curry.
  refine ((arrow @2_ _) _).
  - refine (sconst true @_ AC @_ SND _ _).
  - refine
      ((ZIP  (fun va vb => match va,vb with
                            | abs, abs => abs
                            | pres a, pres b => pres (andb (negb a) b)
                            | _,_ => err error_Cl
                        end) @2_ SND _ _) _).
    refine ((fby @2_ sconst false @_ AC @_ SND _ _) _).
    refine ((AP _ _ @2_ FST _ _) (SND _ _)).
Defined.

Lemma true_until_eq :
  forall rs, true_until rs ==
          arrow (sconst true (AC rs))
            (ZIP (fun va vb => match va,vb with
                            | abs, abs => abs
                            | pres a, pres b => pres (andb (negb a) b)
                            | _,_ => err error_Cl
                            end)
               rs (fby (sconst false (AC rs)) (true_until rs))).
Proof.
  intros.
  unfold true_until at 1.
  rewrite FIXP_eq.
  reflexivity.
Qed.



Context {I A : Type}.
Definition SI := fun _ : I => sampl A.

Parameter (f : DS_prod SI -C-> DS_prod SI).

(* ≈ Denot.sbool_of *)
Definition sbool_of : DS (sampl bool) -C-> DS bool :=
  MAP (fun v => match v with
             | pres true => true
             | _ => false
             end).

(* merge booléen *)
Definition smergeb := @smerge A bool bool Some bool_eq [true;false].

Lemma resetls :
  forall rs X i,
    let cs := true_until rs in
    sreset f (sbool_of rs) X i
    == smergeb rs (f env_of_np ).

Search smerge.






Section ARROW.
Context {A : Type}.

(* case booléen : if-then-else *)
Definition scaseb := @scase A bool bool Some bool_eq [true;false].

Definition arrow : DS (sampl A) -C-> DS (sampl A) -C-> DS (sampl A).
  apply curry.
  refine ((scaseb @2_ _) (ID _)).
  refine ((fby @2_ sconst true @_ AC @_ FST _ _)
            (sconst false @_ AC @_ FST _ _)).
Defined.

Lemma arrow_eq :
  forall s0 s1,
    let bs := AC s0 in
    arrow s0 s1 = scaseb (fby (sconst true bs) (sconst false bs)) (s0, s1).
Proof.
  reflexivity.
Qed.
End ARROW.




(* version booléenne conne *)
Module TRUE_UNTIL1.
Definition true_until : DS bool -C-> DS bool.
  refine (FIXP _ _).
  apply curry.
  refine (CONS true @_ _).
  refine ((ZIP andb @2_ MAP negb @_ REM _ @_ SND _ _) _).
  refine ((AP _ _ @2_ FST _ _) (REM _ @_ SND _ _)).
Defined.

Lemma true_until_eq :
  forall rs, true_until rs == cons true (ZIP andb (map negb (rem rs)) (true_until (rem rs))).
Proof.
  intro.
  unfold true_until at 1.
  rewrite FIXP_eq; auto.
Qed.
End TRUE_UNTIL1.
