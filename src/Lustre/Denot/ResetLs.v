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

Arguments PROJ {I Di}.
Arguments FST {D1 D2}.
Arguments SND {D1 D2}.

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
