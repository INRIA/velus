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
From Velus Require Import Lustre.LSyntax Lustre.LTyping Lustre.LClocking Lustre.LOrdered Lustre.LSemantics.

From Velus Require Import Lustre.Denot.Cpo.
Require Import Cpo_ext CommonDS SDfuns Denot.

(* TODO: virer *)
Section Take.
  Fixpoint take {A} (n : nat) (s : DS A) :=
    match n with
    | O => 0
    | S n => app s (take n (rem s))
    end.

  Lemma take_eq_compat :
    forall {A} n (s t : DS A),
      s == t ->
      take n s == take n t.
  Proof.
    induction n; intros; simpl; auto.
    rewrite H, IHn at 1; auto.
  Qed.

  Add Parametric Morphism A : take
      with signature @eq nat ==> @Oeq (DS A) ==> @Oeq (DS A)
        as take_morph.
  Proof.
    apply take_eq_compat.
  Qed.

  Lemma take_1 : forall {A} (s : DS A),
      take 1 s == first s.
  Proof.
    intros; simpl.
    apply app_bot_right_first.
  Qed.

  (* TODO: on devrait pouvoir se passer de is_cons xs ... *)
  Lemma rem_take :
    forall {A} n (xs : DS A),
      is_cons xs ->
      rem (take (S n) xs) == take n (rem xs).
  Proof.
    intros; simpl.
    rewrite rem_app; auto.
  Qed.

  (* TODO: move *)
  Lemma is_cons_first_is_cons :
    forall {A} (s t : DS A),
      is_cons s ->
      first s == first t ->
      is_cons t.
  Proof.
    intros * Hc Hf.
    apply first_is_cons.
    rewrite <- Hf.
    now apply is_cons_first.
  Qed.

  Lemma take_eq :
    forall {A} (s t : DS A),
      (forall n, take n s == take n t) ->
      s == t.
  Proof.
    intros * Hn.
    eapply DS_bisimulation_allin1
      with (R := fun U V => (forall n, take n U == take n V)); auto.
    - intros ????? H1 H2 ?. now rewrite <- H1, <- H2.
    - clear. intros U V Hc Ht.
      specialize (Ht 1) as Hf; rewrite 2 take_1 in Hf.
      split; intros; auto.
      rewrite <- 2 rem_take, Ht; destruct Hc;
        eauto using is_cons_first_is_cons.
  Qed.

End Take.


Module Type LDENOTSAFE
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks   : CLOCKS        Ids Op OpAux)
       (Import Senv  : STATICENV     Ids Op OpAux Cks)
       (Import Syn   : LSYNTAX Ids Op OpAux Cks Senv)
       (Import Typ   : LTYPING Ids Op OpAux Cks Senv Syn)
       (Import Cl    : LCLOCKING     Ids Op OpAux Cks Senv Syn)
       (Import Lord  : LORDERED Ids Op OpAux Cks Senv Syn)
       (Import CStr  : COINDSTREAMS Ids Op OpAux Cks)
       (Import Den   : LDENOT     Ids Op OpAux Cks Senv Syn Lord CStr).

  (* TODO: move *)
  Fixpoint list_of_nprod {n} (np : nprod n) {struct n} : list (DS (sampl value)) :=
    match n return nprod n -> _ with
    | O => fun _ => []
    | S m => fun np => nprod_fst np :: match m with
                     | O => []
                     | _ => list_of_nprod (nprod_skip np)
                     end
    end np.


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

Definition DSForall_pres {A} (P : A -> Prop) : DS (sampl A) -> Prop :=
  DSForall (fun s => match s with pres v => P v | _ => True end).

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
    (forall ss ty,
        typeof e = [ty] ->
        denot_exp ins e envI bs env = ss ->
        forall_nprod (DSForall_pres (fun v => wt_value v ty -> sem_unop op v ty <> None)) ss
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

  Context {PSyn : block -> Prop}.
  Context {prefs : PS.t}.
  Variable (G : @global PSyn prefs).
  Variable Γ : static_env.

  (* TODO: move *)
  Section SafeDS.
  Definition safe_val : sampl value -> Prop :=
  fun v => match v with
        | err _ => False
        | _ => True
        end.
  Definition safe_DS : DS (sampl value) -> Prop := DSForall safe_val.
  End SafeDS.

    (* abstract_clock *)
  Definition AC : DS (sampl value) -C-> DS bool :=
    MAP (fun v => match v with pres _ => true | _ => false end).

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

  (** propriétés des dénotations des expressions *)

  Definition wc_denot (e : exp) :=
    let ss := denot_exp ins e envI bs env in
    Forall2 wc_DS (clockof e) (list_of_nprod ss).

  Definition wt_denot (e : exp) :=
    let ss := denot_exp ins e envI bs env in
    Forall2 wt_DS (typeof e) (list_of_nprod ss).

  Definition ef_denot (e : exp) :=
    let ss := denot_exp ins e envI bs env in
    forall_nprod safe_DS ss.

  Definition safe_denot (e : exp) :=
    wc_denot e /\ wt_denot e /\ ef_denot e.


  (* TODO: move? *)
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

  Lemma wc_econst :
    forall c, wc_denot (Econst c).
  Proof.
    constructor; auto.
    rewrite denot_exp_eq; cbn.
    unfold wc_DS.
    now rewrite AC_sconst.
  Qed.

  (* TODO: move *)
  Lemma DSForall_map :
    forall {A B} (f : A -> B) P s,
      DSForall (fun x => P (f x)) s -> DSForall P (MAP f s).
  Proof.
    clear; intros.
    remember (MAP f s) as fs. apply Oeq_refl_eq in Heqfs.
    revert dependent s. revert fs.
    cofix Cof; intros * H Hfs.
    destruct fs.
    - constructor.
      apply Cof with s; auto. now rewrite eqEps.
    - apply symmetry, map_eq_cons_elim in Hfs as (?&? & Hs &?&?); subst.
      rewrite Hs in *; inv H.
      constructor; auto.
      apply Cof with (rem s); rewrite Hs, rem_cons; auto.
  Qed.

  Lemma wt_econst :
    forall c, wt_denot (Econst c).
  Proof.
    constructor; auto.
    rewrite denot_exp_eq; cbn.
    unfold wt_DS, DSForall_pres, sconst.
    apply DSForall_map.
    clear; revert bs.
    cofix Cof.
    destruct bs; constructor; auto.
    cases_eqn HH; subst. inv HH.
    constructor.
    apply wt_cvalue_cconst.
  Qed.

  Lemma ef_econst :
    forall c, ef_denot (Econst c).
  Proof.
    intro.
    unfold ef_denot.
    rewrite denot_exp_eq; cbn.
    unfold safe_DS, sconst.
    apply DSForall_map.
    clear; revert bs.
    cofix Cof.
    destruct bs; constructor; auto.
    cases; simpl; auto.
  Qed.

  (* TODO: move *)
  Ltac find_specialize_in H :=
    repeat multimatch goal with
      | [ v : _ |- _ ] => specialize (H v)
      end.

  Lemma safe_exp :
    safe_env ->
    forall (e : exp),
      restr_exp e ->
      wt_exp G Γ e ->
      wc_exp G Γ e ->
      op_correct_exp ins envI bs env e ->
      safe_denot e.
  Proof.
    intros (WT & WC & EF).
    induction e; intros Hr Hwt Hwc Hoc; inv Hr.
    - (* Econst *)
      unfold safe_denot.
      auto using wc_econst, wt_econst, ef_econst.
    - (* Evar *)
      inv Hwt. inv Hwc.
      specialize (WT i). specialize (WC i). specialize (EF i).
      unfold safe_denot, wc_denot, wt_denot, ef_denot.
      rewrite denot_exp_eq; cbn.
      repeat split; eauto.
    - (* Eunop *)
      (* rewrite denot_exp_eq. *)
      (* apply wt_exp_wl_exp in Hwt as Hwl. inv Hwl. *)
      (* inv Hwt. inv Hwc. inv Hoc. *)
      (* find_specialize_in IHe. *)
      (* revert IHe. *)
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
       (Lord  : LORDERED Ids Op OpAux Cks Senv Syn)
       (CStr  : COINDSTREAMS Ids Op OpAux Cks)
       (Den   : LDENOT     Ids Op OpAux Cks Senv Syn Lord CStr)
<: LDENOTSAFE Ids Op OpAux Cks Senv Syn Typ Cl Lord CStr Den.
  Include LDENOTSAFE Ids Op OpAux Cks Senv Syn Typ Cl Lord CStr Den.
End LdenotsafeFun.
