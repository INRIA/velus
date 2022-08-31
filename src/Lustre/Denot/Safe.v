From Coq Require Import String Morphisms.
From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Velus Require Import Common.
From Velus Require Import CommonList.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import CoindStreams.
From Velus Require Import Clocks.
From Velus Require Import Lustre.StaticEnv.
From Velus Require Import Lustre.LSyntax Lustre.LTyping Lustre.LClocking Lustre.LSemantics.

From Velus Require Import Lustre.Denot.Cpo.
Require Import Cpo_ext CommonDS SDfuns Denot.

  (* TODO: move *)
Lemma Forall_impl_inside :
  forall {A} (P Q : A -> Prop) xs,
    (Forall (fun x => P x -> Q x) xs) ->
    Forall P xs ->
    Forall Q xs.
Proof.
  induction xs; auto.
  intros FPQ FP. inv FPQ. inv FP.
  constructor; auto.
Qed.

(* TODO: move, rename ? *)
Lemma Forall2_ignore1'': forall {A B} (P : B -> Prop) (xs : list A) ys,
    length ys = length xs ->
    Forall2 (fun _ y => P y) xs ys ->
    Forall P ys.
Proof.
  intros ?? P xs ys; revert xs.
  induction ys; intros * Hlen Hf; inv Hf; eauto.
Qed.


Module Type LDENOTSAFE
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks   : CLOCKS        Ids Op OpAux)
       (Import Senv  : STATICENV     Ids Op OpAux Cks)
       (Import Syn   : LSYNTAX Ids Op OpAux Cks Senv)
       (Import Typ   : LTYPING Ids Op OpAux Cks Senv Syn)
       (Import Cl    : LCLOCKING     Ids Op OpAux Cks Senv Syn)
       (Import CStr  : COINDSTREAMS Ids Op OpAux Cks)
       (Import Den   : LDENOT     Ids Op OpAux Cks Senv Syn CStr).


(* TODO: move, merge SDrel *)
Inductive restr_exp : exp -> Prop :=
| restr_Econst :
  forall c,
    restr_exp (Econst c)
| restr_Evar :
  forall x ann,
    restr_exp (Evar x ann)
| restr_Eunop :
  forall op e ann,
    restr_exp e ->
    restr_exp (Eunop op e ann)
| restr_Efby :
  forall e0s es anns,
    Forall restr_exp e0s ->
    Forall restr_exp es ->
    restr_exp (Efby e0s es anns).
Section Op_correct.
Variables (ins : list ident) (envI : DS_prod SI) (bs : DS bool) (env : DS_prod SI).

(* TODO: move? *)
Definition DSForall_pres {A} (P : A -> Prop) : DS (sampl A) -> Prop :=
  DSForall (fun s => match s with pres v => P v | _ => True end).

(* TODO: move? *)
Lemma DSForall_pres_impl :
  forall {A} (P Q : A -> Prop) (s : DS (sampl A)),
    DSForall_pres P s ->
    DSForall_pres (fun x => P x -> Q x) s ->
    DSForall_pres Q s.
Proof.
  intros ???.
  unfold DSForall_pres.
  cofix Cof.
  destruct s; intros Hp Himpl; inv Hp; inv Himpl; constructor; cases.
Qed.

Inductive op_correct_exp : exp -> Prop :=
| opc_Econst :
  forall c,
    op_correct_exp (Econst c)
| opc_Evar :
  forall x ann,
    op_correct_exp (Evar x ann)
| opc_Eunop :
  forall op e ann,
    op_correct_exp e ->
    (forall (* ss *) ty,
        typeof e = [ty] ->
        (* denot_exp ins e envI bs env = ss -> *)
        forall_nprod (DSForall_pres (fun v => wt_value v ty -> sem_unop op v ty <> None)) (denot_exp ins e envI bs env)
    ) ->
    op_correct_exp (Eunop op e ann)
| opc_Efby :
  forall e0s es anns,
    Forall op_correct_exp e0s ->
    Forall op_correct_exp es ->
    op_correct_exp (Efby e0s es anns)
.

Definition op_correct {PSyn prefs} (n : @node PSyn prefs) : Prop :=
  match n.(n_block) with
  | Beq (xs,es) => Forall op_correct_exp es
  | _ => True
  end.
End Op_correct.


Section node_safe.

  (* Context {PSyn : block -> Prop}. *)
  (* Context {prefs : PS.t}. *)
  (* Variable (G : @global PSyn prefs). *)
  Variable Γ : static_env.

  (* TODO: move *)
  Section SafeDS.
  Definition safe_DS : DS (sampl value) -> Prop :=
    DSForall (fun v => match v with err _ => False | _ => True end).
  Definition safe_ty : DS (sampl value) -> Prop :=
    DSForall (fun v => match v with err error_Ty => False | _ => True end).
  Definition safe_cl : DS (sampl value) -> Prop :=
    DSForall (fun v => match v with err error_Cl => False | _ => True end).
  Definition safe_op : DS (sampl value) -> Prop :=
    DSForall (fun v => match v with err error_Op => False | _ => True end).
  Lemma safe_DS_def :
    forall s, safe_ty s ->
         safe_cl s ->
         safe_op s ->
         safe_DS s.
  Proof.
    unfold safe_ty, safe_cl, safe_op, safe_DS.
    cofix Cof.
    destruct s; intros Hty Hcl Hop; inv Hty; inv Hcl; inv Hop;
      constructor; cases.
  Qed.
  End SafeDS.

    (* abstract_clock *)
  Definition AC : DS (sampl value) -C-> DS bool :=
    MAP (fun v => match v with pres _ => true | _ => false end).

  Lemma AC_cons :
    forall u U,
      AC (cons u U) == match u with
                       | pres _ => cons true (AC U)
                       | _ => cons false (AC U)
                       end.
  Proof.
    intros.
    unfold AC.
    rewrite MAP_map, map_eq_cons; cases.
  Qed.

  Lemma AC_is_cons :
    forall U, is_cons (AC U) <-> is_cons U.
  Proof.
    split; eauto using map_is_cons, is_cons_map.
  Qed.


  Section Invariants.

    (** TODO:
     * safe_enf := wc_env + wt_env + ef_env
     * safe_env env + op_correct e -> safe_DS (denot_exp env e)
     * wt_eq eq + wc_eq eq -> safe_env (FIXP (denot_equation eq))
     *    .. avec fixp_ind, admissibilité...
     *)

  Variables (ins : list ident) (envI : DS_prod SI) (bs : DS bool) (env : DS_prod SI).

  Fixpoint denot_clock ck : DS bool :=
    match ck with
    | Cbase => bs
    | Con ck x (_, k) =>
        let sx := denot_var ins envI env x in
        let cks := denot_clock ck in
        ZIP (fun x c => match x with pres (Venum e) => (e ==b k) && c | _ => false end) sx cks
    end.

  (** propriétés des flots *)

  Definition wt_DS (ty : type) (s : DS (sampl value)) :=
      (* TODO: plutôt <= ? *)
    DSForall_pres (fun v => wt_value v ty) s.

  (* c'est l'alignement, CORRECTION DES HORLOGES *)
  Definition wc_DS (ck : clock) (s : DS (sampl value)) :=
      (* TODO: plutôt <= ? *)
    denot_clock ck == AC s.

  (** propriétés des environnements *)

  Definition wt_env :=
    forall x ty,
      HasType Γ x ty ->
      wt_DS ty (denot_var ins envI env x).

  Definition wc_env :=
    forall x ck,
      HasClock Γ x ck ->
      wc_DS ck (denot_var ins envI env x).

  (* error-free *)
  Definition ef_env :=
    forall x ty,
      HasType Γ x ty ->
      safe_DS (denot_var ins envI env x).

  Definition safe_env := wc_env /\ wt_env /\ ef_env.


  (** ** Faits sur sconst  *)

  Lemma AC_sconst :
    forall c bs,
      AC (sconst c bs) == bs.
  Proof.
    intros.
    unfold AC, sconst.
    rewrite 2 MAP_map, map_comp.
    eapply DS_bisimulation_allin1
      with (R := fun U V => U == map _ V).
    3: eauto.
    { now intros ????? <- <-. }
    intros U V Hc Hu. rewrite Hu in *.
    split.
    - destruct Hc as [Hc|Hc]. apply map_is_cons in Hc.
      all: apply is_cons_elim in Hc as (?&?&Hv).
      all: rewrite Hv, map_eq_cons, 2 first_cons; destruct x; auto.
    - now rewrite rem_map.
  Qed.

  Opaque MAP. (*TODO: le faire plus tôt? *)

  Lemma wc_sconst :
    forall c, wc_DS Cbase (sconst c bs).
  Proof.
    unfold wc_DS.
    intros.
    rewrite AC_sconst; auto.
  Qed.

  Lemma wt_sconst :
    forall c, wt_DS (Tprimitive (ctype_cconst c)) (sconst (Vscalar (sem_cconst c)) bs).
  Proof.
    intro.
    unfold wt_DS, DSForall_pres, sconst.
    apply DSForall_map.
    clear; revert bs.
    cofix Cof.
    destruct bs; constructor; auto.
    cases_eqn HH; subst. inv HH.
    constructor.
    apply wt_cvalue_cconst.
  Qed.

  Lemma safe_sconst :
    forall c, safe_DS (sconst (Vscalar (sem_cconst c)) bs).
  Proof.
    intro.
    unfold safe_DS, sconst.
    apply DSForall_map.
    clear; revert bs.
    cofix Cof.
    destruct bs; constructor; auto.
    cases_eqn HH.
  Qed.

  (** ** Faits sur sunop *)

  Lemma wt_sunop :
    forall op s ty tye,
      type_unop op tye = Some ty ->
      wt_DS tye s ->
      wt_DS ty (sunop (fun v => sem_unop op v tye) s).
  Proof.
    intros * Hop Hwt.
    unfold wt_DS, DSForall_pres, sunop in *.
    apply DSForall_map.
    revert dependent s.
    cofix Cof.
    destruct s; intro Hs; constructor; inv Hs; auto.
    cases_eqn HH; inv HH0.
    eauto using pres_sem_unop.
  Qed.

  Lemma safe_ty_sunop :
    forall op s ty tye,
      type_unop op tye = Some ty ->
      wt_DS tye s ->
      safe_DS s ->
      safe_ty (sunop (fun v => sem_unop op v tye) s).
  Proof.
    intros * Hop Hwt Hsf.
    unfold wt_DS, safe_ty, safe_DS, sunop in *.
    apply DSForall_map.
    revert dependent s.
    cofix Cof.
    destruct s; intro Hs; constructor; inv Hsf; inv Hs; auto.
    cases_eqn HH.
  Qed.

  Lemma safe_cl_sunop :
    forall op s tye,
      safe_DS s ->
      safe_cl (sunop (fun v => sem_unop op v tye) s).
  Proof.
    intros * Hsf.
    unfold safe_cl, safe_DS, sunop in *.
    apply DSForall_map.
    revert dependent s.
    cofix Cof.
    destruct s; intro Hs; constructor; inv Hs; auto.
    cases_eqn HH.
  Qed.

  Lemma safe_op_sunop :
    forall op s tye,
      safe_DS s ->
      DSForall_pres (fun v => sem_unop op v tye <> None) s ->
      safe_op (sunop (fun v => sem_unop op v tye) s).
  Proof.
    intros * Hsf Hop.
    unfold safe_op, safe_DS, sunop in *.
    apply DSForall_map.
    revert dependent s.
    cofix Cof.
    destruct s; intro Hs; constructor; inv Hs; inv Hop; auto.
    cases_eqn HH.
  Qed.

  Lemma wc_sunop :
    forall op s ck tye,
      wc_DS ck s ->
      DSForall_pres (fun v => sem_unop op v tye <> None) s ->
      wc_DS ck (sunop (fun v => sem_unop op v tye) s).
  Proof.
    unfold wc_DS, DSForall_pres.
    intros * -> Hop.
    eapply DS_bisimulation_allin1
      with (R := fun U V => exists s,
                     DSForall_pres (fun v => sem_unop op v tye <> None) s
                     /\ U == AC s
                     /\ V == AC (sunop (fun v : value => sem_unop op v tye) s)).
    3: eauto.
    { intros ???? (?&?&?&?) ??. esplit; eauto. }
    clear.
    intros U V Hc (X & Hop & Hu & Hv).
    rewrite Hu, Hv in *.
    split.
    - destruct Hc as [Hc|Hc].
      all: repeat apply map_is_cons in Hc.
      all: apply is_cons_elim in Hc as (?&?& Hx).
      all: unfold AC, sunop; rewrite Hx, 3 MAP_map, 3 map_eq_cons, 2 first_cons.
      all: rewrite Hx in Hop; inv Hop; destruct x; cases_eqn HH; congruence.
    - exists (rem X).
      unfold AC, sunop in *.
      rewrite 3 MAP_map, <- 3 rem_map.
      repeat split; auto. now apply DSForall_rem.
  Qed.

  (** ** Faits sur fby1/fby *)

  Lemma wt_fby1 :
    forall ty b ov s0 s,
      (match ov with Some v => wt_value v ty | _ => True end) ->
      wt_DS ty s0 ->
      wt_DS ty s ->
      wt_DS ty (fby1s b ov s0 s).
  Proof.
    intros * Wtv Wt0 Wt.
    unfold wt_DS, DSForall_pres in *.
    remember (fby1s _ _ _ _) as t eqn:Ht. apply Oeq_refl_eq in Ht.
    revert dependent s.
    revert dependent s0.
    revert dependent ov.
    revert t b.
    cofix Cof; intros.
    destruct t.
    { constructor; rewrite <- eqEps in *; now eauto 2. }
    assert (is_cons (fby1s b ov s0 s)) as Hc by (rewrite <- Ht; auto).
    destruct b.
    - (* fby1AP *)
      apply fby1AP_cons, is_cons_elim in Hc as (?&?& Hx); rewrite Hx in *.
      fold (fby1AP ov) in Ht.
      rewrite fby1AP_eq in Ht.
      cases_eqn HH; subst; try (rewrite Ht; now apply DSForall_const).
      all: assert (is_cons s0) as Hc by (eapply fby1_cons; now rewrite <- Ht).
      all: apply is_cons_elim in Hc as (?&?&Hy); rewrite Hy in *.
      all: rewrite fby1_eq in Ht.
      all: cases_eqn HH; subst; try (rewrite Ht; now apply DSForall_const).
      all: apply Con_eq_simpl in Ht as (? & Ht); subst.
      all: inv Wt; inv Wt0; constructor; auto.
      all: unfold fby1AP in Ht; apply Cof in Ht; auto.
    - (* fby1 *)
      apply fby1_cons, is_cons_elim in Hc as (?&?& Hx); rewrite Hx in *.
      fold (fby1 ov) in Ht.
      rewrite fby1_eq in Ht.
      cases_eqn HH; subst; try (rewrite Ht; now apply DSForall_const).
      all: apply Con_eq_simpl in Ht as (? & Ht); subst.
      all: inv Wt0; constructor; auto.
      all: unfold fby1AP in Ht; apply Cof in Ht; auto.
  Qed.

  Lemma wt_fby :
    forall ty s0 s,
      wt_DS ty s0 ->
      wt_DS ty s ->
      wt_DS ty (fby s0 s).
  Proof.
    intros * Wt0 Wt.
    unfold wt_DS, DSForall_pres, fby in *.
    generalize false as b; intro.
    remember (fbys _ _ _) as t eqn:Ht. apply Oeq_refl_eq in Ht.
    revert dependent s.
    revert dependent s0.
    revert t b.
    cofix Cof; intros.
    destruct t.
    { constructor; rewrite <- eqEps in *; now eauto 2. }
    assert (is_cons (fbys b s0 s)) as Hc by (rewrite <- Ht; auto).
    destruct b.
    - (* fbyA *)
      apply fbyA_cons, is_cons_elim in Hc as (?&?& Hx); rewrite Hx in *.
      fold (@fbyA value) in Ht.
      rewrite fbyA_eq in Ht.
      cases_eqn HH; subst; try (rewrite Ht; now apply DSForall_const).
      all: assert (is_cons s0) as Hc by (eapply fby_cons; now rewrite <- Ht).
      all: apply is_cons_elim in Hc as (?&?&Hy); rewrite Hy in *.
      all: rewrite fby_eq in Ht.
      all: cases_eqn HH; subst; try (rewrite Ht; now apply DSForall_const).
      all: apply Con_eq_simpl in Ht as (? & Ht); subst.
      all: inv Wt; inv Wt0; constructor; auto.
      + unfold fbyA in Ht; apply Cof in Ht; auto.
      + rewrite Ht. now apply wt_fby1.
    - (* fby *)
      apply fby_cons, is_cons_elim in Hc as (?&?& Hx); rewrite Hx in *.
      fold (@fby value) in Ht.
      rewrite fby_eq in Ht.
      cases_eqn HH; subst; try (rewrite Ht; now apply DSForall_const).
      all: apply Con_eq_simpl in Ht as (? & Ht); subst.
      all: inv Wt0; constructor; auto.
      + unfold fbyA in Ht; apply Cof in Ht; auto.
      + rewrite Ht. now apply wt_fby1.
  Qed.

  Lemma wc_fby :
    forall ck s0 s,
      safe_DS s0 /\ wc_DS ck s0 -> (* pour une meilleure unification plus tard... *)
      safe_DS s /\ wc_DS ck s ->
      wc_DS ck (fby s0 s).
  Proof.
    unfold wc_DS.
    intro ck.
    generalize (denot_clock ck); clear ck.
    intros * [][].
    eapply DS_bisimulation_allin1
      with (R :=
              fun C F => exists s0 s,
                  safe_DS s0 /\ safe_DS s /\ C == AC s0 /\ C == AC s
                  /\ (F == AC (fby s0 s)
                     \/ (exists v, F == AC (fby1 (Some v) s0 s)))).
    3: eauto 8.
    { intros * (?&?&?&?&?&?&?) FF GG.
      setoid_rewrite <- FF.
      setoid_rewrite <- GG.
      eauto 7. }
    clear; intros C F Hcons (s0 & s & Safe0 & Safe & Hc0 & Hc & Hf).
    assert (is_cons s0 /\ is_cons s) as (Hs0 & Hs). {
      destruct Hcons as [|Hcons].
      split; apply AC_is_cons; now rewrite <- ?Hc0, <- ?Hc.
      destruct Hf as [Hf|(?&Hf)]; rewrite Hf in Hcons; apply AC_is_cons in Hcons.
      apply fby_cons in Hcons. 2: apply fby1_cons in Hcons.
      all: apply AC_is_cons in Hcons as ?; rewrite <- Hc0, Hc in *.
      all: split; auto; now apply AC_is_cons.
    }
    apply is_cons_elim in Hs0 as (v0 & s0' & Hs0), Hs as (v & s' & Hs).
    rewrite Hs, Hs0, AC_cons, Hc0 in *.
    inv Safe; inv Safe0.
    setoid_rewrite Hc0.
    destruct Hf as [Hf | (vv & Hf)].
    - (* fby *)
      rewrite fby_eq in Hf.
      cases; apply Con_eq_simpl in Hc as []; try congruence.
      (* abs *)
      + rewrite fbyA_eq, AC_cons in Hf.
        split.  { now rewrite Hf, 2 first_cons. }
        exists s0', s'.
        rewrite Hf, 2 rem_cons; auto 6.
      + rewrite fby1AP_eq, AC_cons in Hf.
        split.  { now rewrite Hf, 2 first_cons. }
        exists s0', s'.
        repeat (split; rewrite ?Hf, ?AC_cons, ?rem_cons; auto).
        right. eexists. now rewrite Hf, rem_cons.
    - (* fby1 *)
      rewrite Hs, Hs0, fby1_eq in Hf.
      cases; apply Con_eq_simpl in Hc as []; try congruence.
      all: rewrite fby1AP_eq, AC_cons in Hf.
      all: split; [ now rewrite Hf, 2 first_cons |].
      all: exists s0', s'; repeat (split; rewrite ?Hf, ?rem_cons; auto).
      all: right; eexists; now rewrite Hf, rem_cons.
  Qed.

  (* on fait tout en un, plutôt qu'en trois lemmes *)
  Lemma safe_fby1 :
    forall v s0 s,
      safe_DS s0 ->
      safe_DS s ->
      AC s0 == AC s -> (* implied by [wc_DS ck s0 /\ wc_DS ck s] *)
      safe_DS (fby1 (Some v) s0 s).
  Proof.
    unfold wc_DS.
    intros * Safe0 Safe Hac.
    remember (fby1 _ _ _) as t eqn:Ht. apply Oeq_refl_eq in Ht.
    revert dependent s.
    revert dependent s0.
    revert v t.
    cofix Cof; intros.
    destruct t.
    { constructor. rewrite <- eqEps in *. eapply Cof in Ht; eauto . }
    assert (is_cons s0) as Hs0 by (eapply fby1_cons; rewrite <- Ht; auto).
    assert (is_cons s) as Hs by now rewrite <- AC_is_cons, <- Hac, AC_is_cons.
    apply is_cons_elim in Hs0 as (v0 & s0' & Hs0), Hs as (sv & s' & Hs).
    rewrite Hs, Hs0, 2 AC_cons in *.
    inv Safe. inv Safe0.
    rewrite fby1_eq in Ht.
    cases_eqn HH; subst; try rewrite DS_const_eq in Ht; try rewrite fby1AP_eq in Ht.
    all: apply Con_eq_simpl in Ht as (? & Ht), Hac as (?&?); subst; try congruence.
    all: constructor; auto; eapply Cof in Ht; eauto.
  Qed.

  Lemma safe_fby :
    forall ck s0 s,
      safe_DS s0 /\ wc_DS ck s0 ->
      safe_DS s /\ wc_DS ck s ->
      safe_DS (fby s0 s).
  Proof.
    unfold wc_DS.
    intros *[Safe0 Ck0][Safe Ck].
    assert (AC s0 == AC s) as Hac by now rewrite <- Ck0, <- Ck.
    remember (fby _ _) as t eqn:Ht. apply Oeq_refl_eq in Ht.
    clear dependent ck.
    revert dependent s.
    revert dependent s0.
    revert t.
    cofix Cof; intros.
    destruct t.
    { constructor. rewrite <- eqEps in *. eapply Cof in Ht; eauto . }
    assert (is_cons s0) as Hs0 by (eapply fby_cons; rewrite <- Ht; auto).
    assert (is_cons s) as Hs by now rewrite <- AC_is_cons, <- Hac, AC_is_cons.
    apply is_cons_elim in Hs0 as (v0 & s0' & Hs0), Hs as (sv & s' & Hs).
    rewrite Hs, Hs0, 2 AC_cons in *.
    inv Safe. inv Safe0.
    rewrite fby_eq in Ht.
    cases_eqn HH; subst;
      try rewrite DS_const_eq in Ht;
      try rewrite fbyA_eq in Ht;
      try rewrite fby1AP_eq in Ht.
    all: apply Con_eq_simpl in Ht as (? & Ht), Hac as (?&?); subst; try congruence.
    all: constructor; auto.
    - eapply Cof in Ht; eauto.
    - rewrite Ht. eapply safe_fby1; eauto.
  Qed.

  (* TODO: merge in SDtoRel *)
  Lemma Forall_denot_exps :
    forall P ins es envI bs env,
      forall_nprod P (denot_exps ins es envI bs env)
      <-> Forall (fun e => forall_nprod  P (denot_exp ins e envI bs env)) es.
  Proof.
    induction es; intros; simpl; split; auto.
    - intro Hs. setoid_rewrite denot_exps_eq in Hs.
      apply app_forall_nprod in Hs as [].
      constructor; auto.
      now apply IHes.
    - intro Hs. inv Hs.
      setoid_rewrite denot_exps_eq.
      apply forall_nprod_app; auto.
      now apply IHes.
  Qed.

  (* TODO: généraliser... ? *)
  Lemma Forall_wt_exp :
    forall es,
      Forall (fun e => Forall2 wt_DS (typeof e) (list_of_nprod (denot_exp ins e envI bs env))) es ->
      Forall2 wt_DS (typesof es) (list_of_nprod (denot_exps ins es envI bs env)).
  Proof.
    induction 1.
    - simpl; auto.
    - rewrite denot_exps_eq; simpl.
      rewrite list_of_nprod_app.
      apply Forall2_app; auto.
  Qed.

  (* TODO: généraliser... ? *)
  Lemma Forall_wc_exp :
    forall es,
      Forall (fun e => Forall2 wc_DS (clockof e) (list_of_nprod (denot_exp ins e envI bs env))) es ->
      Forall2 wc_DS (clocksof es) (list_of_nprod (denot_exps ins es envI bs env)).
  Proof.
    induction 1.
    - simpl; auto.
    - rewrite denot_exps_eq; simpl.
      rewrite list_of_nprod_app.
      apply Forall2_app; auto.
  Qed.

  (* TODO: move, mais où? il faudrait une section pour list_of_nprod *)
  Lemma forall_nprod_Forall :
    forall P {n} (np : nprod n),
      forall_nprod P np ->
      Forall P (list_of_nprod np).
  Proof.
    induction n as [|[]]; intros * Hf.
    - constructor.
    - constructor; auto.
    - inversion Hf.
      constructor; auto.
      now apply IHn.
  Qed.

  (* TODO: idem *)
  Lemma Forall_forall_nprod :
    forall P {n} (np : nprod n),
      Forall P (list_of_nprod np) ->
      forall_nprod P np.
  Proof.
    induction n as [|[]]; intros * Hf.
    - constructor.
    - inv Hf. auto.
    - inv Hf.
      constructor; auto.
      now apply IHn.
  Qed.

  (* TODO: idem *)
  Lemma list_of_nprod_length :
    forall {n} (np : nprod n),
      length (list_of_nprod np) = n.
  Proof.
    induction n as [|[]]; auto.
    intros []; simpl.
    f_equal. apply IHn.
  Qed.

  (* TODO: pourquoi faut-il spécifier tous les types ? *)
  (* TODO: idem *)
  Lemma Forall2_lift2 :
    forall {A} (F : forall A, DS (sampl A) -C-> DS (sampl A) -C-> DS (sampl A))
      (P Q : A -> DS (sampl value) -> Prop),
      (forall a x y, P a x -> P a y -> Q a (F _ x y)) ->
      forall l {n} (l1 l2 : nprod n),
        Forall2 P l (list_of_nprod l1) ->
        Forall2 P l (list_of_nprod l2) ->
        Forall2 Q l (list_of_nprod (lift2 F l1 l2)).
  Proof.
    induction l as [|? []]; intros * Hl1 Hl2.
    - simpl_Forall.
      destruct n; simpl in *; auto; congruence.
    - destruct n as [|[]]; simpl in *; simpl_Forall.
      cbn; auto.
    - destruct n as [|[]]; auto.
      inv Hl1; simpl_Forall.
      inv Hl1; simpl_Forall.
      destruct l1 as (s1&l1), l2 as (s2&l2).
      specialize (IHl _ l1 l2).
      rewrite lift2_simpl.
      constructor.
      + inv Hl1. inv Hl2. cbn; auto.
      + inv Hl1. inv Hl2. auto.
  Qed.

  Ltac find_specialize_in H :=
    repeat multimatch goal with
      | [ v : _ |- _ ] => specialize (H v)
      end.

  Lemma safe_exp :
    safe_env ->
    forall {PSyn Prefs} (G : @global PSyn Prefs) (e : exp),
      restr_exp e ->
      wt_exp G Γ e ->
      wc_exp G Γ e ->
      op_correct_exp ins envI bs env e ->
      let ss := denot_exp ins e envI bs env in
      Forall2 wt_DS (typeof e) (list_of_nprod ss)
      /\ Forall2 wc_DS (clockof e) (list_of_nprod ss)
      /\ forall_nprod safe_DS ss.
  Proof.
    intros (WT & WC & EF).
    induction e using exp_ind2; intros Hr Hwt Hwc Hoc; inv Hr.
    - (* Econst *)
      rewrite denot_exp_eq; cbn.
      auto using wt_sconst, wc_sconst, safe_sconst.
    - (* Evar *)
      inv Hwt. inv Hwc.
      specialize (WT x). specialize (WC x). specialize (EF x).
      rewrite denot_exp_eq; cbn.
      repeat split; eauto.
    - (* Eunop *)
      apply wt_exp_wl_exp in Hwt as Hwl.
      inv Hwl. inv Hwt. inv Hwc. inv Hoc.
      find_specialize_in IHe.
      find_specialize_in H13.
      rewrite denot_exp_eq.
      revert IHe H13.
      generalize (denot_exp ins e envI bs env).
      take (typeof e = _) and rewrite it.
      take (numstreams e = _) and rewrite it.
      cbn; intros s (Wte & Wce & Efe) Hop.
      simpl_Forall.
      apply DSForall_pres_impl in Hop; auto.
      repeat split; simpl_Forall.
      + apply wt_sunop; auto.
      + apply wc_sunop; congruence.
      + (* TODO: lemme trois-en-un ? *)
        apply safe_DS_def; eauto using safe_ty_sunop, safe_cl_sunop, safe_op_sunop.
    - (* Efby *)
      apply wt_exp_wl_exp in Hwt as Hwl.
      inv Hwl. inv Hwt. inv Hwc. inv Hoc.
      apply Forall_impl_inside with (P := restr_exp) in H, H0; auto.
      apply Forall_impl_inside with (P := wt_exp _ _) in H, H0; auto.
      apply Forall_impl_inside with (P := wc_exp _ _) in H, H0; auto.
      apply Forall_impl_inside with (P := op_correct_exp _ _ _ _) in H, H0; auto.
      apply Forall_and_inv in H as [Wt0 H'], H0 as [Wt H0'].
      apply Forall_and_inv in H' as [Wc0 Sf0], H0' as [Wc Sf].
      apply Forall_wt_exp in Wt0, Wt.
      apply Forall_wc_exp in Wc0, Wc.
      apply Forall_denot_exps, forall_nprod_Forall in Sf0, Sf.
      rewrite denot_exp_eq.
      revert Wt0 Wt Wc0 Wc Sf0 Sf.
      generalize (denot_exps ins e0s envI bs env).
      generalize (denot_exps ins es envI bs env).
      rewrite annots_numstreams in *.
      simpl; intros; cases; try congruence.
      unfold eq_rect_r, eq_rect; destruct e, e0; simpl.
      take (typesof es = _) and rewrite it in *.
      take (typesof e0s = _) and rewrite it in *.
      take (Forall2 eq _ _) and apply Forall2_eq in it; rewrite <- it in *.
      take (Forall2 eq _ _) and apply Forall2_eq in it; rewrite <- it in *.
      repeat split.
      + eapply Forall2_lift2; eauto using wt_fby.
      + eapply Forall2_lift2. apply wc_fby.
        all: apply Forall2_Forall2; auto.
        all: apply Forall2_ignore1'; auto.
        all: now rewrite list_of_nprod_length, map_length.
      + eapply Forall_forall_nprod, Forall2_ignore1''.
        now rewrite list_of_nprod_length, map_length.
        eapply Forall2_lift2. apply safe_fby.
        all: apply Forall2_Forall2; eauto.
        all: apply Forall2_ignore1'; auto.
        all: now rewrite list_of_nprod_length, map_length.
  Qed.

  End Invariants.
  End node_safe.

End LDENOTSAFE.

Module LdenotsafeFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks   : CLOCKS        Ids Op OpAux)
       (Senv  : STATICENV     Ids Op OpAux Cks)
       (Syn   : LSYNTAX Ids Op OpAux Cks Senv)
       (Typ   : LTYPING Ids Op OpAux Cks Senv Syn)
       (Cl    : LCLOCKING     Ids Op OpAux Cks Senv Syn)
       (CStr  : COINDSTREAMS Ids Op OpAux Cks)
       (Den   : LDENOT     Ids Op OpAux Cks Senv Syn CStr)
<: LDENOTSAFE Ids Op OpAux Cks Senv Syn Typ Cl CStr Den.
  Include LDENOTSAFE Ids Op OpAux Cks Senv Syn Typ Cl CStr Den.
End LdenotsafeFun.
