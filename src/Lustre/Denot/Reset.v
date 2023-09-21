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
    infinite rs -> infinite xs ->  infinite (smask k rs xs).
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


(** ** Liens entre smask_env et sreset *)

Section Smask_sreset.

Context {I A : Type}.
Definition SI := fun _ : I => sampl A.


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

Lemma smask_env_inf :
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
  all: rewrite Hu, Hv, PROJ_simpl, APP_env_eq, PROJ_simpl, APP_simpl in Hc.
  all: try assert (is_cons (X x)) by
    (destruct Hc as [Hc|Hc]; now apply app_is_cons in Hc).
  all: split; [
      (* first *)
      rewrite Hu, Hv, PROJ_simpl, APP_env_eq, ?first_cons, APP_simpl, first_app_first
      ; auto; (* puis les autres *) now rewrite DS_const_eq, first_cons
    |].
  all: eexists _, R', (REM_env X).
  all: rewrite Hu, Hv, 2 PROJ_simpl, APP_env_eq, APP_simpl, ?rem_app;
    auto using is_cons_DS_const.
Qed.

Lemma take_smask_false :
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

(* TODO: déplacer dans SDfuns *)
Lemma take_sreset_aux_false :
  forall n f R (X Y : DS_prod SI),
    take n R == take n (DS_const false) ->
    take_env n (sreset_aux f R X Y) == take_env n Y.
Proof.
  induction n; intros * Heq; auto.
  rewrite 2 (take_eq (S n)), DS_const_eq, app_cons, rem_cons in Heq.
  destruct (@is_cons_elim _ R) as (r & R' & Hr).
  { eapply app_is_cons; now rewrite Heq. }
  rewrite Hr, app_cons, rem_cons, sreset_aux_eq in *.
  apply Con_eq_simpl in Heq as []; subst; simpl.
  rewrite app_app_env.
  setoid_rewrite <- (IHn f R' (REM_env X)) at 2; auto.
  now rewrite app_rem_take_env.
Qed.


(* XXXXXXXXXXXXXXXXXX TODO mutualiser, où foutre ça ?? *)

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

(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)


(** *** Here we explicit the hypothesis needed to prove the
    [smask_sreset] characterization. *)
Section InNode.

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
  - rewrite take_smask_false, (take_sreset_aux_false _ f _ _), Hlp; auto.
    now apply take_smask_false.
  - pose proof (Ht := Hlp (smask_env O R X) X m (take_smask_false m R X Hr)).
    specialize (InfG X Infx) as Infy.
    revert Ht Habs Infy.
    generalize (f X); intros Y.
    specialize (InfG (smask_env O R X) (smask_env_inf _ _ _ Infr Infx)) as Infz.
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
      rewrite rem_cons, sreset_aux_eq, 3 app_app_env, 2 rem_app_env in *.
      apply first_env_eq_compat in Ht as Hft.
      apply rem_env_eq_compat in Ht as Hrt.
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
  all: rewrite AbsG in HU; auto using smask_env_inf, nrem_env_inf, REM_env_inf.
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

End InNode.

End Smask_sreset.
