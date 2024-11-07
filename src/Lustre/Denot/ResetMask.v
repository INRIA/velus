From Velus Require Import Common.CommonTactics.
Require Import Cpo.
Require Import SDfuns.

(* TODO: où mettre ça joliment ? *)
Ltac revert_all :=
  repeat match goal with
         | H:_ |- _ => revert H
         end.
Tactic Notation "remember_ds" uconstr(s) "as" ident(x) :=
  let Hx := fresh "H"x in
  remember s as x eqn:Hx;
  apply Oeq_refl_eq in Hx.

(* TODO: mettre ça dans SDfuns ? *)
Definition bool_of_sbool : sampl bool -> bool :=
  fun v => match v with
        | pres true => true
        | _ => false
        end.

(* TODO: mettre ça dans SDfuns ? *)
Lemma bool_of_sbool_pres :
  forall s, map bool_of_sbool (map pres s) == s.
Proof.
  intros.
  apply DS_bisimulation_allin1 with
    (R := fun U V => U == map bool_of_sbool (map pres V)); auto.
  { intros * -> ? <-; auto. }
  clear; intros U V Hc Hu.
  destruct (@is_cons_elim _ V) as (v & V' & Hv).
  { destruct Hc; auto.
    eapply map_is_cons, map_is_cons; now rewrite <- Hu. }
  rewrite Hv, Hu in *.
  autorewrite with cpodb; split; auto.
  unfold bool_of_sbool; cases.
Qed.


(** ** Mask de flot en version dénotationnelle *)
Section Smask.

Context {A : Type}.

Definition smaskf : (nat -O-> DS bool -C-> DS (sampl A) -C-> DS (sampl A)) -C-> (nat -O-> DS bool -C-> DS (sampl A) -C-> DS (sampl A)).
  apply ford_fcont_shift. intro k.
  apply curry.
  apply curry.
  apply (fcont_comp2 (DSCASE bool _)). 2: apply (SND _ _ @_ FST _ _).
  apply ford_fcont_shift. intro r.
  apply curry.
  match goal with
  | |- _ (_ (Dprod ?pl ?pr) _) =>
      pose (mask' := fcont_ford_shift _ _ _ (FST _ _ @_ (FST _ _ @_ (FST pl pr))));
      pose (X := SND _ _ @_ (FST pl pr));
      pose (R := SND pl pr);
      idtac
  end.
  destruct k as [|[|k]].
  - (* k = 0 *)
    destruct r.
    + apply CTE, (DS_const abs). (* r = true *)
    + apply ((APP _ @2_ X) ((AP _ _ @3_ (mask' O)) R (REM _ @_ X))).
  - (* k = 1 *)
    destruct r.
    + apply ((APP _ @2_ X) ((AP _ _ @3_ (mask' O)) R (REM _ @_ X))).
    + apply ((CONS abs) @_ ((AP _ _ @3_ (mask' 1)) R (REM _ @_ X))).
  - (* k > 1 *)
    destruct r.
    + apply ((CONS abs) @_ ((AP _ _ @3_ (mask' (S k))) R (REM _ @_ X))).
    + apply ((CONS abs) @_ ((AP _ _ @3_ (mask' (S (S k)))) R (REM _ @_ X))).
Defined.

Lemma smaskf_eq :
  forall f k r rs (xs : DS (sampl A)),
    smaskf f k (cons r rs) xs
    == match k with
       | 0 => if r
             then DS_const abs
             else app xs (f O rs (rem xs))
       | 1 => if r
             then app xs (f O rs (rem xs))
             else cons abs (f 1 rs (rem xs))
       | S (S _ as k') =>
           if r
           then cons abs (f k' rs (rem xs))
           else cons abs (f k rs (rem xs))
       end.
Proof.
  intros.
  unfold smaskf.
  setoid_rewrite fcont_comp_simpl.
  rewrite fcont_comp2_simpl.
  rewrite DSCASE_simpl.
  setoid_rewrite DScase_cons.
  setoid_rewrite fcont_comp_simpl.
  destruct k as [|[]], r; cbn; now autorewrite with cpodb.
Qed.

Definition smask : nat -O-> DS bool -C-> DS (sampl A) -C-> DS (sampl A) :=
  FIXP _ smaskf.

Lemma smask_eq :
    forall k r rs (xs : DS (sampl A)),
      smask k (cons r rs) xs
      == match k with
         | 0 => if r
               then DS_const abs
               else app xs (smask O rs (rem xs))
         | 1 => if r
               then app xs (smask O rs (rem xs))
               else cons abs (smask 1 rs (rem xs))
         | S (S _ as k') =>
             if r
             then cons abs (smask k' rs (rem xs))
             else cons abs (smask k rs (rem xs))
         end.
Proof.
  intros.
  unfold smask at 1.
  assert (Heq:=FIXP_eq smaskf).
  rewrite (ford_eq_elim Heq) at 1.
  now rewrite smaskf_eq.
Qed.

Lemma is_cons_smask :
  forall k rs xs,
    is_cons (smask k rs xs) ->
    is_cons rs.
Proof.
  unfold smask.
  intros * Hc.
  rewrite (ford_eq_elim (FIXP_eq smaskf) _) in Hc.
  now apply DScase_is_cons in Hc.
Qed.

Lemma smask_inf :
  forall k rs (xs:DS (sampl A)),
    infinite rs -> infinite xs -> infinite (smask k rs xs).
Proof.
  intros.
  remember (smask k rs xs) as sm eqn:Heq.
  apply Oeq_refl_eq in Heq.
  revert_all.
  cofix Cof; intros * rsi xsi sm Hsm.
  apply infinite_decomp in rsi as (r&rs'& Hr &?).
  apply infinite_decomp in xsi as (x&xs'& Hx &?).
  rewrite Hr, Hx, smask_eq in Hsm.
  destruct k as [|[]], r.
  rewrite Hsm; apply DS_const_inf.
  all:  constructor; [| eapply Cof; eauto 1 ];
    rewrite Hsm, ?app_cons, ?rem_cons; auto.
Qed.

Lemma take_smask_false :
  forall n R (X : DS (sampl A)),
    take n R == take n (DS_const false) ->
    take n (smask O R X) == take n X.
Proof.
  induction n; intros * Heq; auto.
  rewrite 2 (take_eq (S n)), DS_const_eq, app_cons, rem_cons in Heq.
  destruct (@is_cons_elim _ R) as (r & R' & Hr).
  { eapply app_is_cons; now rewrite Heq. }
  rewrite Hr, app_cons, rem_cons, smask_eq in *.
  apply Con_eq_simpl in Heq as []; subst.
  rewrite 2 (take_eq (S n)).
  rewrite app_app, <- (IHn R' (rem X)), app_rem_app; auto.
Qed.

End Smask.

Lemma AC_smask :
  forall A k rs (xs : DS (sampl A)),
    AC (smask k rs xs) == MAP bool_of_sbool (smask k rs (MAP pres (AC xs))).
Proof.
  intros.
  eapply DS_bisimulation_allin1
    with (R := fun U V => exists k rs xs,
                 U == AC (smask k rs xs)
                 /\ V == MAP bool_of_sbool (smask k rs (MAP pres (AC xs)))).
  3: eauto.
  { intros * ? Eq1 Eq2.
    setoid_rewrite <- Eq1.
    setoid_rewrite <- Eq2.
    eauto. }
  clear.
  intros U V Hc (k & rs & xs & Hu & Hv).
  destruct (@is_cons_elim _ rs) as (vr & rs' & Hrs).
  { rewrite Hu, Hv in Hc.
    now destruct Hc as [?%AC_is_cons%is_cons_smask
                       |?%map_is_cons%is_cons_smask]. }

  split.
  - (* first *)
    rewrite Hu, Hv, Hrs.
    clear.
    rewrite first_AC, MAP_map, first_map.
    rewrite 2 smask_eq; cases; unfold AC.
    { setoid_rewrite DS_const_eq.
      now rewrite 2 first_cons, MAP_map, 2 map_eq_cons, 2 map_bot. }
    1,2: rewrite 2 first_app_first, 3 MAP_map, 2 first_map, 2 map_comp, DS_ext.map_ext;
         eauto 1; intros; cases.
    all: rewrite 2 first_cons, MAP_map, 2 map_eq_cons, 2 map_bot; auto.
  - (* rem *)
    rewrite Hrs, smask_eq in Hu.
    rewrite Hrs, smask_eq in Hv.
    setoid_rewrite Hu.
    setoid_rewrite Hv.
    cases.
    { (* cas toujours absent *)
      exists O, (cons true 0), 0.
      setoid_rewrite DS_const_eq.
      unfold AC.
      now rewrite 4 MAP_map, 2 map_eq_cons, 2 rem_cons, 2 smask_eq. }
    (* les autres *)
    all: eexists _, rs', (rem xs).
    all: rewrite rem_AC, 4 MAP_map, 2 rem_map, ?rem_app, rem_AC, ?rem_cons; eauto.
    (* reste les is_cons *)
    all: rewrite Hu, Hv in Hc.
    all: destruct Hc as [Hc%AC_is_cons%app_is_cons
                        |Hc%map_is_cons%app_is_cons%map_is_cons%AC_is_cons];
      eauto using is_cons_map, AC_is_cons.
Qed.

(* FIXME, bien sûr *)
Lemma smask_or_ad_hoc :
  forall A k rs (xs : DS (sampl A)) bs,
    ZIP orb (AC (smask k rs xs)) (MAP bool_of_sbool (smask k rs (MAP pres bs)))
    == MAP bool_of_sbool (smask k rs (MAP pres (ZIP orb (AC xs) bs))).
Proof.
  intros.
  eapply DS_bisimulation_allin1
    with (R := fun U V => exists k rs xs bs,
                   U == ZIP orb (AC (smask k rs xs)) (MAP bool_of_sbool (smask k rs (MAP pres bs)))
                 /\ V == MAP bool_of_sbool (smask k rs (MAP pres (ZIP orb (AC xs) bs)))).
  3: eauto 10.
  { intros * ? Eq1 Eq2.
    setoid_rewrite <- Eq1.
    setoid_rewrite <- Eq2.
    eauto. }
  clear.
  intros U V Hc (k & rs & xs & bs & Hu & Hv).
  destruct (@is_cons_elim _ rs) as (vr & rs' & Hrs).
  { rewrite Hu, Hv in Hc.
    destruct Hc as [[?%AC_is_cons%is_cons_smask]%zip_is_cons
                   |?%map_is_cons%is_cons_smask]; auto. }
  split.
  - (* first *)
    rewrite Hu, Hv, Hrs.
    rewrite first_zip, first_AC, 3 MAP_map, 2 first_map.
    rewrite 3 smask_eq; cases; unfold AC.
    { setoid_rewrite DS_const_eq.
      now rewrite 2 first_cons, MAP_map, 2 map_eq_cons, 2 map_bot, zip_cons, zip_bot1. }
    1,2: rewrite 3 first_app_first, 3 MAP_map, 2 first_map, first_zip, first_map, 2 map_comp.
    1,2: rewrite zip_map, <- map_zip, zip_ext; eauto 1; intros [] []; auto.
    all: rewrite 3 first_cons, MAP_map, 2 map_eq_cons, 2 map_bot, zip_cons, zip_bot1; auto.
  - (* rem *)
    rewrite Hrs, 2 smask_eq in Hu.
    rewrite Hrs, smask_eq in Hv.
    setoid_rewrite Hu.
    setoid_rewrite Hv.
    cases.
    { (* cas toujours absent *)
      exists O, (cons true 0), 0, 0.
      setoid_rewrite DS_const_eq.
      unfold AC.
      rewrite 8 MAP_map, 2 map_eq_cons, zip_cons, 2 rem_cons, 3 smask_eq; auto. }
    (* les autres *)
    all: eexists _, rs', (rem xs), (rem bs).
    all: rewrite rem_zip, rem_AC, 8 MAP_map, 4 rem_map, ?rem_app, ?rem_zip, rem_AC, ?rem_cons; eauto.
    (* reste les is_cons *)
    all: rewrite Hu, Hv in Hc.
    all: destruct Hc as [[Hc%AC_is_cons%app_is_cons Hr%map_is_cons%app_is_cons%map_is_cons]%zip_is_cons
                        |[Hc%AC_is_cons]%map_is_cons%app_is_cons%map_is_cons%zip_is_cons];
      eauto using is_cons_map, is_cons_zip.
Qed.


(* FIXME: dans cette section on utilise I,A,SI *)
Section Env.

Context {I A : Type}.
Definition SI := @SDfuns.SI I A.


Section Smask_env.

(** ** Masque sur les environnements dénotationnels
    défini indépendamment de [smask], en utilisant plutôt
    APP_env, REM_env etc. *)

Definition smask_envf : (nat -O-> DS bool -C-> DS_prod SI -C-> DS_prod SI) -C->
                    nat -O-> DS bool -C-> DS_prod SI -C-> DS_prod SI.
  apply ford_fcont_shift; intro k.
  apply curry, curry.

  match goal with
  | |- _ (_ (Dprod ?pl ?pr) _) =>
      pose (mask := fcont_ford_shift _ _ _ (FST _ _ @_ FST pl pr));
      pose (R := SND _ _ @_ (FST pl pr));
      pose (X := SND pl pr);
      idtac
  end.

  (* on décrit l'environnement pour chaque variable *)
  apply Dprodi_DISTR; intro x.
  refine ((DSCASE bool _ @2_ _) R).
  apply ford_fcont_shift; intro r.

  (* on dégage (tl R) du contexte pour pouvoir utiliser nos alias : *)
  refine (curry (_ @_ FST _ _)).

  destruct k as [|[|k]].
  - (* k = 0 *)
    destruct r.
    (* r = true *)
    apply CTE, (DS_const abs).
    (* r = false *)
    exact ((APP _ @2_ PROJ _ x @_ X)
             (PROJ _ x @_ ((AP _ _ @3_ (mask O)) (REM _ @_ R) (REM_env @_ X)))).
  - (* k = 1 *)
    destruct r.
    (* r = true *)
    exact ((APP _ @2_ PROJ _ x @_ X)
             (PROJ _ x @_ ((AP _ _ @3_ (mask O)) (REM _ @_ R) (REM_env @_ X)))).
    (* r = false *)
    exact (CONS abs @_ (PROJ _ x @_ ((AP _ _ @3_ (mask 1)) (REM _ @_ R) (REM_env @_ X)))).
  - (* k > 1 *)
    destruct r.
    (* r = true *)
    exact (CONS abs @_ (PROJ _ x @_ ((AP _ _ @3_ (mask (S k))) (REM _ @_ R) (REM_env @_ X)))).
    (* r = false *)
    exact (CONS abs @_ (PROJ _ x @_ ((AP _ _ @3_ (mask (S (S k)))) (REM _ @_ R) (REM_env @_ X)))).
Defined.

(* FIXME: changer les Dprodi dans la définition aussi  *)
(* FIXME: comprendre le FIXME ci-dessus *)
Lemma smask_envf_eq : forall F k r R X,
    smask_envf F k (cons r R) X
    == match k with
       | 0 => if r
             then fun _ => DS_const abs
             else APP_env X (F O R (REM_env X))
       | 1 => if r
             then APP_env X (F O R (REM_env X))
             else APP_env (fun _ => DS_const abs) (F 1 R (REM_env X))
       | S (S _ as k') =>
           if r
           then APP_env (fun _ => DS_const abs) (F k' R (REM_env X))
           else APP_env (fun _ => DS_const abs) (F k R (REM_env X))
       end.
Proof.
  intros.
  apply Oprodi_eq_intro; intro x.
  unfold smask_envf.
  setoid_rewrite fcont_comp_simpl.
  setoid_rewrite fcont_comp2_simpl.
  rewrite DSCASE_simpl.
  setoid_rewrite DScase_cons.
  setoid_rewrite fcont_comp_simpl.
  rewrite DS_const_eq.
  destruct k as [|[]], r; cbn; now autorewrite with cpodb.
Qed.

Definition smask_env : nat -O-> DS bool -C-> DS_prod SI -C-> DS_prod SI :=
  FIXP _ smask_envf.

Lemma smask_env_eq : forall k r R X,
    smask_env k (cons r R) X
    == match k with
       | 0 => if r
             then fun _ => DS_const abs
             else APP_env X (smask_env O R (REM_env X))
       | 1 => if r
             then APP_env X (smask_env O R (REM_env X))
             else APP_env (fun _ => DS_const abs) (smask_env 1 R (REM_env X))
       | S (S _ as k') =>
           if r
           then APP_env (fun _ => DS_const abs) (smask_env k' R (REM_env X))
           else APP_env (fun _ => DS_const abs) (smask_env k R (REM_env X))
       end.
Proof.
  intros.
  unfold smask_env at 1.
  assert (Heq:=FIXP_eq smask_envf).
  rewrite (ford_eq_elim Heq) at 1.
  now rewrite smask_envf_eq.
Qed.

Lemma smask_env_eq_1 :
  forall rs X,
    smask_env 1 (cons true rs) X == smask_env O (cons false rs) X.
Proof.
  intros.
  rewrite 2 smask_env_eq; auto.
Qed.

Lemma is_cons_smask_env :
  forall k rs X x,
    is_cons (smask_env k rs X x) ->
    is_cons rs.
Proof.
  unfold smask_env.
  intros * Hc.
  rewrite <- PROJ_simpl, (ford_eq_elim (FIXP_eq smask_envf) _),
    PROJ_simpl in Hc.
  now apply DScase_is_cons in Hc.
Qed.

Lemma smask_env_all_inf :
  forall k R X,
    infinite R -> all_infinite X -> all_infinite (smask_env k R X).
Proof.
  intros * Hr HX x.
  remember_ds (smask_env k R X x) as t.
  revert_all; cofix Cof; intros.
  apply infinite_decomp in Hr as (r & R' & Hr &?).
  rewrite <- PROJ_simpl, Hr, smask_env_eq, PROJ_simpl in Ht.
  specialize (HX x) as Infx; inv Infx.
  cases.
  { rewrite Ht; apply DS_const_inf. }
  all: rewrite ?DMAPi_simpl, ?APP_env_eq, ?CONS_simpl in Ht.
  all: apply rem_eq_compat in Ht as Hrt.
  all: rewrite ?APP_simpl, ?rem_app, ?CONS_simpl, ?rem_cons in Hrt; auto using is_cons_DS_const.
  all: constructor; [| eapply Cof in Hrt; eauto using REM_env_inf].
  all: rewrite Ht; auto.
  all: try rewrite DS_const_eq; now apply is_cons_app.
Qed.

Lemma smask_env_inf :
  forall l k R (X:DS_prod SI),
    infinite R -> infinite_dom X l -> infinite_dom (smask_env k R X) l.
Proof.
  clear.
  intros * Hr HX x Hin.
  remember_ds (smask_env k R X x) as t.
  revert_all; cofix Cof; intros.
  apply infinite_decomp in Hr as (r & R' & Hr &?).
  rewrite <- PROJ_simpl, Hr, smask_env_eq, PROJ_simpl in Ht.
  specialize (HX x Hin) as Infx; inv Infx.
  cases.
  { rewrite Ht; apply DS_const_inf. }
  all: rewrite ?DMAPi_simpl, ?APP_env_eq, ?CONS_simpl in Ht.
  all: apply rem_eq_compat in Ht as Hrt.
  all: rewrite ?APP_simpl, ?rem_app, ?CONS_simpl, ?rem_cons in Hrt; auto.
  all: try (now apply DS_const_inf).
  all: constructor; [| eapply Cof in Hrt; eauto using REM_env_inf_dom].
  all: rewrite Ht; auto.
  all: rewrite DS_const_eq, app_cons; auto.
Qed.


(** Lien avec la définition de smask sur les flots individuels *)
Lemma smask_env_proj_eq :
  forall k R X x, smask_env k R X x == smask k R (X x).
Proof.
  intros.
  eapply DS_bisimulation_allin1 with
    (R := fun U V => exists k R X,
            U == smask_env k R X x
            /\ V == smask k R (X x)).
  3: eauto.
  { clear.
    intros * ? Eq1 Eq2.
    setoid_rewrite <- Eq1.
    setoid_rewrite <- Eq2.
    eauto. }
  clear.
  intros U V Hc (k & R & X & Hu & Hv).
  destruct (@is_cons_elim _ R) as (r & R' & Hr).
  { destruct Hc as [Hc|Hc].
    - eapply is_cons_smask_env; now rewrite <- Hu.
    - eapply is_cons_smask; now rewrite <- Hv.
  }
  rewrite <- PROJ_simpl, Hr in Hu, Hv.
  rewrite smask_eq in Hv.
  rewrite smask_env_eq in Hu.
  cases.
  { (* cas toujours absent *)
    split. now rewrite Hu, Hv; auto.
    exists O, (cons true 0), 0.
    rewrite Hu, Hv, PROJ_simpl, DS_const_eq, rem_cons.
    now rewrite <- PROJ_simpl, smask_env_eq, smask_eq, PROJ_simpl. }
  all: rewrite Hu, Hv, PROJ_simpl, APP_env_eq, PROJ_simpl in Hc.
  all: try assert (is_cons (X x)) by
    (destruct Hc as [Hc|Hc]; now apply app_is_cons in Hc).
  all: split; [
      (* first *)
      rewrite Hu, Hv, PROJ_simpl, APP_env_eq, ?first_cons, first_app_first
      ; auto; (* puis les autres *) now rewrite DS_const_eq, first_cons
    |].
  all: eexists _, R', (REM_env X).
  all: rewrite Hu, Hv, 2 PROJ_simpl, APP_env_eq, ?rem_app;
    auto using is_cons_DS_const.
Qed.

Lemma take_smask_env_false :
  forall n R X,
    take n R == take n (DS_const false) ->
    take_env n (smask_env O R X) == take_env n X.
Proof.
  induction n; intros * Heq; auto.
  rewrite 2 (take_eq (S n)), DS_const_eq, app_cons, rem_cons in Heq.
  destruct (@is_cons_elim _ R) as (r & R' & Hr).
  { eapply app_is_cons; now rewrite Heq. }
  rewrite Hr, app_cons, rem_cons, smask_env_eq in *.
  apply Con_eq_simpl in Heq as []; subst; simpl.
  rewrite 2 (take_env_eq (S n)).
  rewrite app_app_env, <- (IHn R' (REM_env X)), app_rem_take_env; auto.
Qed.

Lemma bss_smask :
  forall ins envI k rs,
    0 < length ins ->
    bss ins (smask_env k rs envI)
    == MAP bool_of_sbool (smask k rs (MAP pres (bss ins envI))).
Proof.
  induction ins as [|x[|y]]; intros * Hlen.
  inversion Hlen.
  - simpl.
    autorewrite with cpodb.
    rewrite (smask_env_proj_eq k rs envI x).
    setoid_rewrite (PROJ_simpl x envI).
apply AC_smask.
  - rewrite 2 (bss_cons x), smask_env_proj_eq, IHins; try (simpl; lia).
    (* apply smask_or_ad_hoc. *)
    clear.
    generalize (bss (y :: l) envI); intro bs.
    generalize (envI x); intro xs.
    apply smask_or_ad_hoc.
Qed.

End Smask_env.



Section Abs_align.

(** ** Liens entre smask_env et sreset *)

(** *** Entrées absentes -> sorties absentes *)

(** Propriété qui découle de la correction des horloges (cf. wf_align).
    Dans une forme un peu plus faible (absences à l'infini) mais ça
    suffit pour la correction du reset. *)
Definition abs_align (X Y : DS_prod SI) : Prop :=
  forall n, nrem_env n X == abs_env -> nrem_env n Y <= abs_env.

Lemma abs_align_abs :
  forall X, abs_align abs_env X -> X <= abs_env.
Proof.
  intros * Hal.
  apply (Hal O); reflexivity.
Qed.

Lemma abs_align_rem :
  forall X Y, abs_align X Y -> abs_align (REM_env X) (REM_env Y).
Proof.
  unfold abs_align.
  intros * Hal n.
  specialize (Hal (S n)).
  now rewrite 2 nrem_rem_env.
Qed.

Global Add Parametric Morphism : abs_align
       with signature @Oeq (DS_prod SI) ==> @Oeq (DS_prod SI) ==> Basics.impl
         as abs_align_morph.
Proof.
  unfold abs_align.
  intros * Eq1 * Eq2 Habs.
  setoid_rewrite <- Eq1.
  setoid_rewrite <- Eq2.
  auto.
Qed.

End Abs_align.

(* TODO: move ? *)
Lemma take_bool_dec :
  forall n R,
    infinite R ->
    take n R == take n (DS_const false)
    \/ exists m, m < n
           /\ take m R == take m (DS_const false)
           /\ first (nrem m R) == cons true 0.
Proof.
  clear.
  induction n; intros * Infr; auto.
  inversion_clear Infr as [Cr Infr'].
  destruct (is_cons_elim Cr) as (r & R' & Hr).
  rewrite Hr, rem_cons in *.
  destruct r.
  - (* true trouvé *)
    right.
    exists O; simpl.
    rewrite Hr, first_cons; auto with arith.
  - rewrite 2 (take_eq (S n)).
    rewrite DS_const_eq, 2 rem_cons, 2 app_cons.
    destruct (IHn R' Infr') as [Ht|(m & Hlt & Ht & Hf)].
    + rewrite Ht; auto.
    + right; exists (S m); rewrite 2 (take_eq (S m)); simpl.
      rewrite Hr, 2 rem_cons, 2 app_cons, Ht, Hf.
      auto with arith.
Qed.

(* **************************************************  *)
(* Utile ou pas ? *)
Section Smask_sreset1.

(** *** Here we explicit the hypothesis needed to prove the
    [smask_sreset] characterization. *)

(* la fonction de nœud qu'on va passer à sreset *)
Variable (f : DS_prod SI -C-> DS_prod SI).

Hypothesis InfG :
  forall envI,
    all_infinite envI ->
    all_infinite (f envI).

Hypothesis AbsG :
  forall X,
    all_infinite X ->
    f (APP_env abs_env X) == APP_env abs_env (f X).

(* FIXME: en fonction de ce qu'on arrive à prouver dans Lp.v,
   établir une version plus simple de ce prédicat *)
(* Pour l'instant ça a l'air d'être le plus faible requis *)
Hypothesis Hlp :
  forall X Y n,
    take_env n X == take_env n Y ->
    take_env n (f X) == take_env n (f Y).


(** découle de AbsG *)
Lemma forever_abs : f abs_env == abs_env.
Proof.
  clear - AbsG.
  apply env_eq_Oeq.
  (* FIXME: un sélecteur dans remember_ds ?? *)
  remember abs_env as X eqn:HX in |-*; apply Oeq_refl_eq in HX.
  remember_ds (f X) as Y.
  revert HX HY.
  revert X Y.
  cofix Cof; intros.
  rewrite abs_abs_abs in HX.
  rewrite HX, AbsG in HY; auto using abs_env_inf.
  constructor.
  - apply Cof.
    + rewrite HX, rem_app_env; eauto using all_cons_abs_env.
    + rewrite HY, HX, 2 rem_app_env; eauto using all_cons_abs_env.
  - now rewrite HX, HY, first_app_env, <- abs_abs_abs.
Qed.

(* le véritable cas de base *)
Lemma smask_sreset0 :
  forall R X,
    all_infinite X ->
    infinite R ->
    abs_align (smask_env O R X) (f (smask_env O R X)) ->
    f (smask_env O R X) == smask_env O R (sreset_aux f R X (f X)).
Proof.
  clear - InfG Hlp.
  intros * Infx Infr Habs.
  apply take_env_Oeq; intro n.
  destruct (take_bool_dec n R Infr) as [Hr | (m & Hle & Hr & Hf)].
  - rewrite take_smask_env_false, (take_sreset_aux_false _ f _ _), Hlp; auto.
    now apply take_smask_env_false.
  - pose proof (Ht := Hlp (smask_env O R X) X m (take_smask_env_false m R X Hr)).
    specialize (InfG X Infx) as Infy.
    revert Ht Habs Infy.
    generalize (f X); intros Y.
    specialize (InfG (smask_env O R X) (smask_env_all_inf _ _ _ Infr Infx)) as Infz.
    revert Infz.
    generalize (f (smask_env O R X)); intros Z.
    revert Hr Hf Infr Infx Hle.
    revert R X Y Z n.
    induction m; intros;
      inversion_clear Infr as [Cr InfR];
      destruct (is_cons_elim Cr) as (r & R' & Hr').
    + simpl in Hf.
      rewrite Hr', first_cons, smask_env_eq in *.
      apply Con_eq_simpl in Hf as []; subst.
      apply abs_align_abs, all_infinite_le_eq in Habs as ->; auto.
    + destruct n;[lia|].
      apply abs_align_rem in Habs.
      rewrite 2 (take_eq (S m)), Hr', rem_cons, smask_env_eq in *.
      rewrite DS_const_eq, 2 app_cons in Hr.
      apply Con_eq_simpl in Hr as []; subst; simpl in *.
      rewrite 2 (take_env_eq (S n)).
      rewrite rem_cons, sreset_aux_eq, 3 app_app_env, 2 rem_app_env in *.
      apply first_env_eq_compat in Ht as Hft.
      apply rem_env_eq_compat in Ht as Hrt.
      rewrite 2 (take_env_eq (S m)) in Hft, Hrt.
      rewrite 2 first_app_env in Hft.
      rewrite 2 rem_app_env in Hrt; auto using all_infinite_all_cons.
      rewrite <- (app_app_first_env Y), <- (app_app_first_env Z), Hft, IHm; auto with arith.
      all: auto using all_infinite_all_cons, REM_env_inf.
Qed.

(** Caractérisation fondamentale de la fonction de reset *)
Lemma smask_sreset :
  forall k R X,
    infinite R ->
    all_infinite X ->
    abs_align (smask_env k R X) (f (smask_env k R X)) ->
    f (smask_env k R X) == smask_env k R (sreset f R X).
Proof.
  intros * Infr Infx Hal.
  rewrite sreset_eq.
  destruct k.
  (* k = 0, cas de base *)
  { apply smask_sreset0; auto. }
  (* on va raisonner par co-induction grâce à [env_eq] *)
  remember_ds X as Xn.
  remember (_ f Xn) as Y eqn:HH.
  (* tout ce qu'on a besoin de savoir sur Xn et Y : *)
  assert (exists X n, Xn == nrem_env n X
                 /\ Y == nrem_env n (f X)
                 /\ all_infinite X) as Hy
      by (exists X, O; subst; rewrite HXn in *; split; eauto).
  clear HH HXn X.
  apply env_eq_ok.
  remember_ds (f _) as U.
  remember_ds (smask_env _ _ (_ _)) as V.
  revert HV HU Infr Infx Hy Hal.
  revert k R Xn Y U V.
  cofix Cof; intros.
  inversion_clear Infr as [Cr InfR].
  destruct (is_cons_elim Cr) as (r & R' & Hr).
  rewrite Hr in HU, HV, Hal.
  rewrite Hr, rem_cons in InfR.
  destruct Hy as (X & n & Hxn & Hy & InfX).
  rewrite Hxn in HU, HV.
  rewrite Hy in HV.
  rewrite sreset_aux_eq in HV.
  rewrite smask_env_eq in HU, HV, Hal.
  cases.
  (* encore le cas de base... *)
  { rewrite HV, HU, Hxn in *; clear HU HV Hxn.
    pose proof (Hsm := smask_sreset0 (cons false R') (nrem_env n X)).
    rewrite smask_env_eq in Hsm at 3.
    rewrite Hsm, smask_env_eq; auto using infinite_cons, Oeq_env_eq.
    now rewrite smask_env_eq. }
  all: rewrite AbsG in HU; auto using smask_env_all_inf, nrem_env_inf, REM_env_inf.
  all: constructor; [| rewrite HU, HV, 2 first_app_env; auto].
  all: apply abs_align_rem in Hal.
  all: rewrite HU, 2 rem_app_env, Hxn in Hal; eauto 1 using all_cons_abs_env.
  - eapply Cof; rewrite ?HU, ?HV, ?rem_app_env;
      eauto using all_cons_abs_env, nrem_env_inf, all_infinite_all_cons, REM_env_inf.
    exists X, (S n); eauto.
  - rewrite sreset_aux_eq in HV.
    eapply Cof; rewrite ?HU, ?HV, ?rem_app_env;
      eauto using all_cons_abs_env, nrem_env_inf, all_infinite_all_cons, REM_env_inf.
    exists (nrem_env n X), 1; eauto using nrem_env_inf.
  - eapply Cof; rewrite ?HU, ?HV, ?rem_app_env;
      eauto using all_cons_abs_env, nrem_env_inf, all_infinite_all_cons, REM_env_inf.
    exists X, (S n); eauto.
Qed.

End Smask_sreset1.



(** Relâchement de abs_align avec une inégalité *)
Section Abs_alingnLE.

Definition abs_alignLE (X Y : DS_prod SI) : Prop :=
  forall n, nrem_env n X <= abs_env -> nrem_env n Y <= abs_env.

Lemma abs_alignLE_rem :
  forall X Y, abs_alignLE X Y -> abs_alignLE (REM_env X) (REM_env Y).
Proof.
  unfold abs_alignLE.
  intros * Hal n.
  specialize (Hal (S n)).
  now rewrite 2 nrem_rem_env.
Qed.

Lemma abs_alignLE_abs :
  forall Y, abs_alignLE abs_env Y -> Y <= abs_env.
Proof.
  intros * Hal.
  apply (Hal O); reflexivity.
Qed.

Global Add Parametric Morphism : abs_alignLE
       with signature @Oeq (DS_prod SI) ==> @Oeq (DS_prod SI) ==> Basics.impl
         as abs_alignLE_morph.
Proof.
  clear.
  unfold abs_alignLE.
  intros * Eq1 ?? Eq2 Hf.
  setoid_rewrite <- Eq1.
  setoid_rewrite <- Eq2.
  auto.
Qed.

Lemma abs_alignLE_le :
  forall X X' Y, X <= X' -> abs_alignLE X Y -> abs_alignLE X' Y.
Proof.
  unfold abs_alignLE.
  intros * Le ??.
  rewrite <- Le; auto.
Qed.

(* version spécialisée avec i ??? *)
Definition abs_alignLEx (X Y : DS_prod SI) i : Prop :=
  forall n, nrem_env n X <= abs_env -> nrem n (Y i) <= abss.

Global Add Parametric Morphism : abs_alignLEx
       with signature @Oeq (DS_prod SI) ==> @Oeq (DS_prod SI) ==> @eq I ==> Basics.impl
         as abs_alignLEx_morph.
Proof.
  clear.
  unfold abs_alignLEx.
  intros * Eq1 ?? Eq2 Hf HH n.
  setoid_rewrite <- Eq1.
  setoid_rewrite <- PROJ_simpl.
  setoid_rewrite <- Eq2.
  auto.
Qed.

Lemma abs_alignLEx_abs :
  forall Y i, abs_alignLEx abs_env Y i -> Y i <= abss.
Proof.
  intros * Hal.
  apply (Hal O); reflexivity.
Qed.

Lemma abs_alignLEx_rem :
  forall X Y i, abs_alignLEx X Y i -> abs_alignLEx (REM_env X) (REM_env Y) i.
Proof.
  unfold abs_alignLEx.
  intros * Hal n.
  specialize (Hal (S n)).
  rewrite REM_env_eq, nrem_rem_env.
  auto.
Qed.

Lemma abs_alignLEx_le :
  forall X X' Y i, X <= X' -> abs_alignLEx X Y i -> abs_alignLEx X' Y i.
Proof.
  unfold abs_alignLEx.
  intros * Le ??.
  rewrite <- Le; auto.
Qed.

Lemma abs_align_proj :
  forall X Y i, abs_alignLE X Y -> abs_alignLEx X Y i.
Proof.
  clear.
  unfold abs_alignLE, abs_alignLEx.
  intros * Hal n H.
  specialize (Hal n H).
  specialize (Hal i).
  now rewrite nrem_env_eq in Hal.
Qed.

End Abs_alingnLE.


(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)
Section Smask_sreset2.

  (* la fonction de nœud qu'on va passer à sreset *)
Variable (f : DS_prod SI -C-> DS_prod SI).
Variables (ins outs: list I).

Hypothesis Hlp :
  forall X n,
    f (take_env n X) == take_env n (f X).

Hypothesis AbsG :
  forall X,
    (* TODO: on pourrait avoir une égalité avec inf_dom ???  *)
    f (APP_env abs_env X) <= APP_env abs_env (f X).

Hypothesis InfG :
  forall envI,
    infinite_dom envI ins ->
    infinite_dom (f envI) outs.

Lemma Hlp2 :
  forall X Y n,
    take_env n X == take_env n Y ->
    take_env n (f X) == take_env n (f Y).
Proof.
  intros * H.
  now rewrite <- Hlp, H, Hlp.
Qed.

(* le véritable cas de base *)
Lemma smask_sreset0' :
    forall R X,
    infinite_dom X ins ->
    infinite R ->
    abs_alignLE (smask_env O R X) (f (smask_env O R X)) ->
    forall i, List.In i outs ->
    f (smask_env O R X) i
    == smask O R (sreset_aux f R X (f X) i).
Proof.
  intros R X Infx Infr Habs i Ini.
  apply take_Oeq; intro n.
  destruct (take_bool_dec n R Infr) as [Hr | (m & Hle & Hr & Hf)].
  - (* si R est faux pour toujours *)
    setoid_rewrite take_smask_false; auto.
    rewrite <- 2 (take_env_proj _ _ i), <- 2 (PROJ_simpl i).
    rewrite (take_sreset_aux_false n f R X (f X)); auto.
    rewrite <- Hlp2; auto.
    rewrite take_smask_env_false; auto.
  - (* sinon il est vrai au bout de m instants *)
    (* on prépare une récurrence sur m *)
    pose proof (Ht := Hlp2 (smask_env O R X) X m (take_smask_env_false m R X Hr)).
    specialize (InfG X Infx) as Infy.
    apply Oprodi_eq_elim with (i := i) in Ht.
    revert Ht Habs Infy.
    generalize (f X); intros Y.
    specialize (InfG (smask_env O R X) (smask_env_inf _ _ _ _ Infr Infx)) as Infz.
    revert Infz.
    generalize (f (smask_env O R X)); intros Z.
    revert Hr Hf Infr Infx Hle Ini.
    revert R X Y Z n i.
    induction m; intros;
      inversion_clear Infr as [Cr InfR];
      destruct (is_cons_elim Cr) as (r & R' & Hr').
    + simpl in Hf.
      rewrite <- 2 (PROJ_simpl i) in *.
      rewrite Hr', smask_eq, smask_env_eq, first_cons in *.
      apply Con_eq_simpl in Hf as []; subst.
      apply abs_alignLE_abs, infinite_le_eq with (s := Z i) in Habs; auto.
      rewrite PROJ_simpl, Habs; auto.
    + destruct n;[lia|].
      rewrite <- 2 (PROJ_simpl i).
      rewrite Hr' in *.
      rewrite DS_const_eq, 2 take_cons in Hr.
      apply Con_eq_simpl in Hr as [? Hr]; subst.
      rewrite nrem_S, rem_cons in *.
      rewrite 2 (take_eq (S n)).
      rewrite sreset_aux_eq, smask_eq, app_app.
      rewrite 2 (PROJ_simpl i), APP_env_eq, 2 app_app, app_rem_app.
      (* on peut faire sauter le [rem(app(Y i))] car il est sous un [Y i] : *)
      rewrite <-  2 fcont_comp_simpl, app_rem_app, 2 fcont_comp_simpl.
      (* ensuite on montre que [app (Z i)] et [app (Y i)] sont idem :  *)
      rewrite 2 take_env_proj, 2 (take_eq (S m)), <- 2 REM_env_eq, <- 2 take_env_proj in Ht.
      apply first_eq_compat in Ht as Hft.
      rewrite 2 first_app_first in Hft.
      rewrite <- (app_app_first (Z i)), <- (app_app_first (Y i)), Hft.
      (* puis on prépare l'appel à IHm *)
      apply rem_eq_compat in Ht as Hrt.
      rewrite 2 rem_app in Hrt; [| apply Infy | apply Infz ]; auto.
      apply abs_alignLE_rem in Habs.
      rewrite smask_env_eq in Habs.
      rewrite <- REM_env_eq, IHm;
        eauto using REM_env_inf_dom, abs_alignLE_le, rem_app_env_le with arith.
Qed.

(* TEST: relâchement du abs_alignLE *)
Lemma smask_sreset0'' :
  forall R X,
    infinite_dom X ins ->
    infinite R ->
    forall i, List.In i outs ->
    abs_alignLEx (smask_env O R X) (f (smask_env O R X)) i ->
    f (smask_env O R X) i
    == smask O R (sreset_aux f R X (f X) i).
Proof.
  clear - InfG Hlp.
  intros R X Infx Infr i Ini Habs.
  apply take_Oeq; intro n.
  destruct (take_bool_dec n R Infr) as [Hr | (m & Hle & Hr & Hf)].
  - (* si R est faux pour toujours *)
    setoid_rewrite take_smask_false; auto.
    rewrite <- 2 (take_env_proj _ _ i), <- 2 (PROJ_simpl i).
    rewrite (take_sreset_aux_false n f R X (f X)); auto.
    rewrite Hlp2; auto.
    rewrite take_smask_env_false; auto.
  - (* sinon il est vrai au bout de m instants *)
    (* on prépare une récurrence sur m *)
    pose proof (Ht := Hlp2 (smask_env O R X) X m (take_smask_env_false m R X Hr)).
    specialize (InfG X Infx) as Infy.
    apply Oprodi_eq_elim with (i := i) in Ht.
    revert Ht Habs Infy.
    generalize (f X); intros Y.
    specialize (InfG (smask_env O R X) (smask_env_inf _ _ _ _ Infr Infx)) as Infz.
    revert Infz.
    generalize (f (smask_env O R X)); intros Z.
    revert Hr Hf Infr Infx Hle Ini.
    revert R X Y Z n i.
    induction m; intros;
      inversion_clear Infr as [Cr InfR];
      destruct (is_cons_elim Cr) as (r & R' & Hr').
    + simpl in Hf.
      rewrite <- 2 (PROJ_simpl i) in *.
      rewrite Hr', smask_eq, smask_env_eq, first_cons in *.
      apply Con_eq_simpl in Hf as []; subst.
      apply abs_alignLEx_abs, infinite_le_eq with (s := Z i) in Habs; auto.
      rewrite PROJ_simpl, Habs; auto.
    + destruct n;[lia|].
      rewrite <- 2 (PROJ_simpl i).
      rewrite Hr' in *.
      rewrite DS_const_eq, 2 take_cons in Hr.
      apply Con_eq_simpl in Hr as [? Hr]; subst.
      rewrite nrem_S, rem_cons in *.
      rewrite 2 (take_eq (S n)).
      rewrite sreset_aux_eq, smask_eq, app_app.
      rewrite 2 (PROJ_simpl i), APP_env_eq, 2 app_app, app_rem_app.
      (* on peut faire sauter le [rem(app(Y i))] car il est sous un [Y i] : *)
      rewrite <-  2 fcont_comp_simpl, app_rem_app, 2 fcont_comp_simpl.
      (* ensuite on montre que [app (Z i)] et [app (Y i)] sont idem :  *)
      rewrite 2 take_env_proj, 2 (take_eq (S m)), <- 2 REM_env_eq, <- 2 take_env_proj in Ht.
      apply first_eq_compat in Ht as Hft.
      rewrite 2 first_app_first in Hft.
      rewrite <- (app_app_first (Z i)), <- (app_app_first (Y i)), Hft.
      (* puis on prépare l'appel à IHm *)
      apply rem_eq_compat in Ht as Hrt.
      rewrite 2 rem_app in Hrt; [| apply Infy | apply Infz ]; auto.
      apply abs_alignLEx_rem in Habs.
      rewrite smask_env_eq in Habs.
      rewrite <- REM_env_eq, IHm;
        eauto using REM_env_inf_dom, abs_alignLEx_le, rem_app_env_le with arith.
Qed.


Lemma inf_dom_abs_env :
  forall A I (l : list I), infinite_dom (@abs_env A I) l.
Proof.
  intros * ??.
  now apply DS_const_inf.
Qed.

Lemma smask_sreset' :
  forall k R X,
    infinite R ->
    infinite_dom X ins ->
    (* remarque : pour l'instant on pourrait demander abs_align sur i uniquement,
       mais on garde la version forte en espérant avoir un truc plus propre un jour *)
    abs_alignLE (smask_env k R X) (f (smask_env k R X)) ->
    forall i, List.In i outs ->
    f (smask_env k R X) i
    == smask_env k R (sreset f R X) i.
Proof.
  intros * Infr Infx Hal i Ini.
  rewrite smask_env_proj_eq.
  rewrite <- 2 (PROJ_simpl i) , sreset_eq, 2 PROJ_simpl.
  destruct k.
  { eapply smask_sreset0'; now eauto. }
  (* TEST: *) apply abs_align_proj with (i := i) in Hal.

  (* on va raisonner par co-induction grâce à [DS_eq] *)
  remember_ds X as Xn.
  remember (_ f Xn) as Y eqn:HH.
  (* tout ce qu'on a besoin de savoir sur Xn et Y : *)
  assert (exists X n, Xn == nrem_env n X
                 /\ Y == nrem_env n (f X)
                 /\ infinite_dom X ins) as Hy
      by (exists X, O; subst; rewrite HXn in *; split; eauto).
  clear HH HXn X.
  apply ds_eq_Oeq.
  remember_ds (f _ i) as U.
  remember_ds (smask _ _ (_ _)) as V.
  revert HV HU Infr Infx Hy Hal Ini.
  revert i k R Xn Y U V.
  cofix Cof; intros.
  inversion_clear Infr as [Cr InfR].
  destruct (is_cons_elim Cr) as (r & R' & Hr).
  (* TEST *)
  unfold abs_alignLEx in Hal.
  setoid_rewrite <- HU in Hal.
  (* /TEST *)
  (* unfold abs_alignLEx. *)
  rewrite <- (PROJ_simpl i) in *.
  rewrite Hr in HU, HV(* , Hal *).
  rewrite Hr, rem_cons in InfR.
  destruct Hy as (X & n & Hxn & Hy & InfX).
  rewrite Hxn in HU, HV.
  rewrite Hy in HV.
  rewrite sreset_aux_eq in HV.
  rewrite smask_env_eq in HU(* , Hal *).
  rewrite smask_eq in HV.
  setoid_rewrite Hr in Hal.
  setoid_rewrite smask_env_eq in Hal.
  cases.
  (* encore le cas de base... *)
  { setoid_rewrite HU in Hal; setoid_rewrite Hxn in Hal.
    rewrite HV, HU, Hxn in *; clear HU HV Hxn.
    apply (smask_sreset0'' (Con false R') (nrem_env n X)) in Ini as Hsm; auto.
    2,3: rewrite ?smask_env_eq; auto using infinite_cons.
    rewrite smask_eq in Hsm.
    rewrite 2 PROJ_simpl, <- Hsm, <- 2 (PROJ_simpl i), smask_env_eq; reflexivity. }

  all: assert (infinite U) by
    (rewrite HU; eapply InfG; eauto using app_env_inf_dom, inf_dom_abs_env,
       smask_env_inf, REM_env_inf_dom, nrem_env_inf_dom).

  (* on a en fait une réécriture de AbsG dans HU *)
  all: destruct HU as [HU _]; rewrite AbsG in HU; apply infinite_le_eq in HU; auto.

  (* on simplifie dans HU et HV *)
  all: unfold abs_env, abss in HU.
  all: rewrite PROJ_simpl, APP_env_eq in HU.
  1,3: rewrite PROJ_simpl, APP_env_eq in HV.

  (* all: apply abs_alignLE_rem in Hal. *)
  (* all: rewrite rem_app_env, Hxn in Hal; eauto 1 using all_cons_abs_env. *)
  all: constructor; intros _; split; cycle 1;
    [| rewrite HU, HV; unfold abs_env, abss;
       now rewrite first_app_first, first_cons, first_DS_const ].
  - eapply Cof; rewrite ?HU, ?HV, ?rem_cons, ?rem_app; auto using is_cons_DS_const.
    + rewrite nrem_env_eq.
      eapply infinite_nrem, InfG; eauto.

    + rewrite <- Hxn.
      now apply REM_env_inf_dom.
    + exists X, (S n); eauto.
    + intros m Hle.
      specialize (Hal (S m)).
      simpl( nrem_env _ _) in Hal.
      rewrite fcont_comp_simpl, <- nrem_rem_env, rem_app_env in Hal; eauto 1 using all_cons_abs_env.
      rewrite nrem_S, HU, Hxn, rem_app in Hal; auto using is_cons_DS_const.
  - eapply Cof; rewrite ?HU, ?HV, ?rem_cons, ?rem_app; auto using is_cons_DS_const.
    + rewrite nrem_env_eq.
      eapply infinite_nrem, InfG; eauto.
    + rewrite <- Hxn.
      now apply REM_env_inf_dom.
    + exists X, (S n); eauto.
    + intros m Hle.
      specialize (Hal (S m)).
      simpl( nrem_env _ _) in Hal.
      rewrite fcont_comp_simpl, <- nrem_rem_env, rem_app_env in Hal; eauto 1 using all_cons_abs_env.
      rewrite nrem_S, HU, Hxn, rem_app in Hal; auto using is_cons_DS_const.
  - rewrite sreset_aux_eq in HV.
    eapply Cof; rewrite ?HU, ?HV, ?rem_cons, ?rem_app; auto using is_cons_DS_const.
    + rewrite PROJ_simpl, APP_env_eq, rem_app; eauto. eapply InfG; rewrite <- ?Hxn; eauto.
    + rewrite <- Hxn.
      now apply REM_env_inf_dom.
    +  exists (nrem_env n X), 1; eauto using nrem_env_inf_dom.
    + intros m Hle.
      specialize (Hal (S m)).
      simpl( nrem_env _ _) in Hal.
      rewrite fcont_comp_simpl, <- nrem_rem_env, rem_app_env in Hal; eauto 1 using all_cons_abs_env.
      rewrite nrem_S, HU, Hxn, rem_app in Hal; auto using is_cons_DS_const.
Qed.

End Smask_sreset2.


(* (* TODO: on pourrait l'utiliser partout (Abs, Lp, ???) *) *)
(* Section Env_le. *)

(*   CoInductive env_le : DS_prod SI -> DS_prod SI -> Prop := *)
(*   | Ee : *)
(*     forall X Y, *)
(*       FIRST_env X <= FIRST_env Y -> *)
(*       env_le (REM_env X) (REM_env Y) -> *)
(*       env_le X Y. *)

(*   Lemma Ole_env_le : forall X Y, X <= Y -> env_le X Y. *)
(*   Proof. *)
(*     cofix Cof; intros; apply Ee; auto. *)
(*   Qed. *)

(*   Lemma env_le_Ole : forall X Y, env_le X Y -> X <= Y. *)
(*   Proof. *)
(*     clear. *)
(*     intros * Hle i. *)
(*     remember_ds (X i) as U. *)
(*     remember_ds (Y i) as V. *)
(*     revert_all; cofix Cof; intros. *)
(*     destruct U as [|u U]. *)
(*     { constructor; rewrite <- eqEps in *; eapply Cof; eauto. } *)
(*     inversion_clear Hle as [?? Hf Hl]. *)
(*     specialize (Hf i). *)
(*     rewrite 2 FIRST_env_eq, <- HU, first_cons in Hf. *)
(*     edestruct (@is_cons_elim _ (Y i)) as (y & Yi' & Hy). *)
(*     { eapply first_is_cons, is_cons_le_compat; eauto. } *)
(*     rewrite Hy, first_cons in Hf. *)
(*     apply Con_le_simpl in Hf as []; subst. *)
(*     edestruct (cons_decomp _ y V) as (V' & Hd & ?). *)
(*     { now rewrite HV, Hy. } *)
(*     apply DSleCon with V'; auto. *)
(*     apply (Cof _ _ Hl). *)
(*     - now rewrite REM_env_eq, <- HU, rem_cons. *)
(*     - apply decomp_eqCon in Hd. *)
(*       now rewrite REM_env_eq, <- HV, Hd, rem_cons. *)
(*   Qed. *)

(*   Lemma env_le_ok : forall X Y, X <= Y <-> env_le X Y. *)
(*   Proof. *)
(*     split; auto using Ole_env_le, env_le_Ole. *)
(*   Qed. *)

(*   Global Add Parametric Morphism : env_le *)
(*          with signature @Oeq (DS_prod SI) ==> @Oeq (DS_prod SI) ==> iff *)
(*            as env_le_morph. *)
(*   Proof. *)
(*     intros * Eq1 * Eq2. *)
(*     split; intros Heq%env_le_ok; apply env_le_ok; now rewrite <- Eq1, <- Eq2 in *. *)
(*   Qed. *)

(* End Env_le. *)

(* (* TEST : smask_sreset sans infinité, avec infériorité *) *)
(* Section Smask_sreset_le. *)

(* Variable (f : DS_prod SI -C-> DS_prod SI). *)
(* Variables (ins outs: list I). *)

(* Hypothesis Hlp : *)
(*   forall X n, *)
(*     f (take_env n X) == take_env n (f X). *)

(* Corollary fbot : f 0 == 0. *)
(*   change 0 with (@take_env _ SI O 0). *)
(*   now rewrite Hlp. *)
(* Qed. *)

(* Hypothesis AbsG : *)
(*   forall X, *)
(*     f (APP_env abs_env X) <= APP_env abs_env (f X). *)

(* (* TODO: move *) *)
(* Lemma take_env_Ole : *)
(*   forall (X Y  : DS_prod SI), (forall n, take_env n X <= take_env n Y) -> X <= Y. *)
(* Proof. *)
(*   intros; intro. *)
(*   apply take_n_Ole; intro. *)
(*   specialize (H n i). *)
(*   rewrite 2 take_env_proj in *; auto. *)
(* Qed. *)


(* Lemma take_bool_dec_le : *)
(*   forall n R, *)
(*     take n R <= take n (DS_const false) *)
(*     \/ exists m, m < n *)
(*            /\ take m R == take m (DS_const false) *)
(*            /\ first (nrem m R) == cons true 0. *)
(* Proof. *)
(*   clear. *)
(*   induction n; intros; auto. *)
(*   rewrite 2 (take_eq (S n)). *)
(*   rewrite DS_const_eq at 1 2. *)
(*   rewrite rem_cons, app_cons. *)
(* Admitted. *)

(* Lemma take_smask_env_false_le : *)
(*   forall n R X, *)
(*     take n R <= take n (DS_const false) -> *)
(*     take_env n (smask_env O R X) <= take_env n X. *)
(* Proof. *)
(*   clear. *)
(*   induction n; intros * Heq; auto. *)
(*   rewrite 2 (take_eq (S n)), DS_const_eq, app_cons, rem_cons in Heq. *)
(* Admitted. *)

(* Lemma smask_sreset0_le : *)
(*   forall R X, *)
(*     abs_alignLE (smask_env O R X) (f (smask_env O R X)) -> *)
(*     f (smask_env O R X) <= smask_env O R (sreset_aux f R X (f X)). *)
(* Proof. *)
(*   clear - Hlp AbsG. *)
(*   intros * Habs. *)

(*   apply take_env_Ole; intro n. *)

(*   sreset_aux *)
(*   destruct (take_bool_dec_le n R) as [Hr | (m & Hle & Hr & Hf)]. *)
(*   - *)
(*     rewrite <- Hlp. *)
(*     rewrite take_smask_env_false_le; auto. *)
(* . *)

(*     rewrite  *)

(*     rewrite <- Hlp. *)
(*     rewrite take_smask_env_false_le; auto. *)
(*     rewrite Hlp; auto. *)

(*     rewrite (take_sreset_aux_false _ f _ _). *)

(*     rewrite take_smask_env_false, (take_sreset_aux_false _ f _ _), Hlp; auto. *)
(*     now apply take_smask_env_false. *)
(*   - pose proof (Ht := Hlp (smask_env O R X) X m (take_smask_env_false m R X Hr)). *)
(*     specialize (InfG X Infx) as Infy. *)
(*     revert Ht Habs Infy. *)
(*     generalize (f X); intros Y. *)
(*     specialize (InfG (smask_env O R X) (smask_env_all_inf _ _ _ Infr Infx)) as Infz. *)
(*     revert Infz. *)
(*     generalize (f (smask_env O R X)); intros Z. *)
(*     revert Hr Hf Infr Infx Hle. *)
(*     revert R X Y Z n. *)
(*     induction m; intros; *)
(*       inversion_clear Infr as [Cr InfR]; *)
(*       destruct (is_cons_elim Cr) as (r & R' & Hr'). *)
(*     + simpl in Hf. *)
(*       rewrite Hr', first_cons, smask_env_eq in *. *)
(*       apply Con_eq_simpl in Hf as []; subst. *)
(*       apply abs_align_abs, all_infinite_le_eq in Habs as ->; auto. *)
(*     + destruct n;[lia|]. *)
(*       apply abs_align_rem in Habs. *)
(*       rewrite 2 (take_eq (S m)), Hr', rem_cons, smask_env_eq in *. *)
(*       rewrite DS_const_eq, 2 app_cons in Hr. *)
(*       apply Con_eq_simpl in Hr as []; subst; simpl in *. *)
(*       rewrite 2 (take_env_eq (S n)). *)
(*       rewrite rem_cons, sreset_aux_eq, 3 app_app_env, 2 rem_app_env in *. *)
(*       apply first_env_eq_compat in Ht as Hft. *)
(*       apply rem_env_eq_compat in Ht as Hrt. *)
(*       rewrite 2 (take_env_eq (S m)) in Hft, Hrt. *)
(*       rewrite 2 first_app_env in Hft. *)
(*       rewrite 2 rem_app_env in Hrt; auto using all_infinite_all_cons. *)
(*       rewrite <- (app_app_first_env Y), <- (app_app_first_env Z), Hft, IHm; auto with arith. *)
(*       all: auto using all_infinite_all_cons, REM_env_inf. *)



(*   eapply DSle_rec. *)


(*   remember_ds (f (smask_env _ _ _)) as U. *)
(*   remember_ds (smask_env O R (sreset_aux f R X (f X))) as V. *)

(*   revert_all; cofix Cof; intros; intro x. *)
(*   eapply Cof in HV. *)
(*   specialize (HV x). *)
(*   Guarded. *)
(*   destruct (U x). *)
(*   { constructor. *)
(*     apply Cof. *)

(*     rewrite <- eqEps in HH. *)


(*   apply env_le_ok. *)
(*   revert_all; cofix Cof; intros. *)
(*   constructor. *)
(*   - (* first *) *)
(*     rewrite HU, HV in *. *)
(*     clear HU HV; clear U V. *)
    


(*   destruct (take_bool_dec n R Infr) as [Hr | (m & Hle & Hr & Hf)]. *)
(*   - (* si R est faux pour toujours *) *)
(*     setoid_rewrite take_smask_false; auto. *)
(*     rewrite <- 2 (take_env_proj _ _ i), <- 2 (PROJ_simpl i). *)
(*     rewrite (take_sreset_aux_false n f R X (f X)); auto. *)
(*     rewrite <- Hlp2; auto. *)
(*     rewrite take_smask_env_false; auto. *)
(*   - (* sinon il est vrai au bout de m instants *) *)
(*     (* on prépare une récurrence sur m *) *)
(*     pose proof (Ht := Hlp2 (smask_env O R X) X m (take_smask_env_false m R X Hr)). *)
(*     specialize (InfG X Infx) as Infy. *)
(*     apply Oprodi_eq_elim with (i := i) in Ht. *)
(*     revert Ht Habs Infy. *)
(*     generalize (f X); intros Y. *)
(*     specialize (InfG (smask_env O R X) (smask_env_inf _ _ _ _ Infr Infx)) as Infz. *)
(*     revert Infz. *)
(*     generalize (f (smask_env O R X)); intros Z. *)
(*     revert Hr Hf Infr Infx Hle Ini. *)
(*     revert R X Y Z n i. *)
(*     induction m; intros; *)
(*       inversion_clear Infr as [Cr InfR]; *)
(*       destruct (is_cons_elim Cr) as (r & R' & Hr'). *)
(*     + simpl in Hf. *)
(*       rewrite <- 2 (PROJ_simpl i) in *. *)
(*       rewrite Hr', smask_eq, smask_env_eq, first_cons in *. *)
(*       apply Con_eq_simpl in Hf as []; subst. *)
(*       apply abs_alignLE_abs, infinite_le_eq with (s := Z i) in Habs; auto. *)
(*       rewrite PROJ_simpl, Habs; auto. *)
(*     + destruct n;[lia|]. *)
(*       rewrite <- 2 (PROJ_simpl i). *)
(*       rewrite Hr' in *. *)
(*       rewrite DS_const_eq, 2 take_cons in Hr. *)



(*   remember_ds (f (smask_env _ _ _)) as U. *)
(*   remember_ds (smask_env O R (sreset_aux f R X (f X))) as V. *)
(*   revert_all; cofix Cof; intros. *)

(* Qed. *)

(* Lemma smask_sreset_le : *)
(*   forall k R X, *)
(*     abs_alignLE (smask_env k R X) (f (smask_env k R X)) -> *)
(*     f (smask_env k R X) <= smask_env k R (sreset f R X). *)
(* Proof. *)
(*   intros * Hal. *)
(*   rewrite sreset_eq. *)
(*   destruct k. *)
(*   (* k = 0, cas de base *) *)
(*   { apply smask_sreset0_le; auto. } *)
(*   (* on va raisonner par co-induction grâce à [env_eq] *) *)
(*   remember_ds X as Xn. *)
(*   remember (_ f Xn) as Y eqn:HH. *)
(*   (* tout ce qu'on a besoin de savoir sur Xn et Y : *) *)
(*   assert (exists X n, Xn == nrem_env n X *)
(*                  /\ Y == nrem_env n (f X) *)
(*                  /\ all_infinite X) as Hy *)
(*       by (exists X, O; subst; rewrite HXn in *; split; eauto). *)
(*   clear HH HXn X. *)
(*   apply env_eq_ok. *)
(*   remember_ds (f _) as U. *)
(*   remember_ds (smask_env _ _ (_ _)) as V. *)
(*   revert HV HU Infr Infx Hy Hal. *)
(*   revert k R Xn Y U V. *)
(*   cofix Cof; intros. *)
(*   inversion_clear Infr as [Cr InfR]. *)
(*   destruct (is_cons_elim Cr) as (r & R' & Hr). *)
(*   rewrite Hr in HU, HV, Hal. *)
(*   rewrite Hr, rem_cons in InfR. *)
(*   destruct Hy as (X & n & Hxn & Hy & InfX). *)
(*   rewrite Hxn in HU, HV. *)
(*   rewrite Hy in HV. *)
(*   rewrite sreset_aux_eq in HV. *)
(*   rewrite smask_env_eq in HU, HV, Hal. *)
(*   cases. *)
(*   (* encore le cas de base... *) *)
(*   { rewrite HV, HU, Hxn in *; clear HU HV Hxn. *)
(*     pose proof (Hsm := smask_sreset0 (cons false R') (nrem_env n X)). *)
(*     rewrite smask_env_eq in Hsm at 3. *)
(*     rewrite Hsm, smask_env_eq; auto using infinite_cons, Oeq_env_eq. *)
(*     now rewrite smask_env_eq. } *)
(*   all: rewrite AbsG in HU; auto using smask_env_all_inf, nrem_env_inf, REM_env_inf. *)
(*   all: constructor; [| rewrite HU, HV, 2 first_app_env; auto]. *)
(*   all: apply abs_align_rem in Hal. *)
(*   all: rewrite HU, 2 rem_app_env, Hxn in Hal; eauto 1 using all_cons_abs_env. *)
(*   - eapply Cof; rewrite ?HU, ?HV, ?rem_app_env; *)
(*       eauto using all_cons_abs_env, nrem_env_inf, all_infinite_all_cons, REM_env_inf. *)
(*     exists X, (S n); eauto. *)
(*   - rewrite sreset_aux_eq in HV. *)
(*     eapply Cof; rewrite ?HU, ?HV, ?rem_app_env; *)
(*       eauto using all_cons_abs_env, nrem_env_inf, all_infinite_all_cons, REM_env_inf. *)
(*     exists (nrem_env n X), 1; eauto using nrem_env_inf. *)
(*   - eapply Cof; rewrite ?HU, ?HV, ?rem_app_env; *)
(*       eauto using all_cons_abs_env, nrem_env_inf, all_infinite_all_cons, REM_env_inf. *)
(*     exists X, (S n); eauto. *)
(* Qed. *)



(* End Smask_sreset_le. *)

End Env.
