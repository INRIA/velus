From Coq Require Import String Morphisms Permutation.
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
    DSForall_pres (fun v => wt_value v ty) s.

  (* c'est l'alignement, CORRECTION DES HORLOGES?? *)
  Definition wc_DS (ck : clock) (s : DS (sampl value)) :=
    AC s <= denot_clock ck.

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

  (* Definition safe_env := wc_env /\ wt_env /\ ef_env. *)

  (* TODO: virer  wt_env, wc_env, ef_env ? *)
  Definition safe_env :=
    forall x ty ck,
      HasType Γ x ty ->
      HasClock Γ x ck ->
      let s := denot_var ins envI env x in
      wt_DS ty s
      /\ wc_DS ck s
      /\ safe_DS s.


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

  (* TODO: move to Cpo_ext *)
  Lemma Con_le_simpl : forall D a b (s t : DS_ord D),
      (Cpo_streams_type.Con a s:DS_ord D) <= Cpo_streams_type.Con b t-> a = b /\ s <= t.
  Proof.
    split.
    now apply DSleCon_hd in H.
    now apply DSleCon_tl in H.
  Qed.

  Lemma wc_sunop :
    forall op s ck tye,
      wc_DS ck s ->
      DSForall_pres (fun v => sem_unop op v tye <> None) s ->
      wc_DS ck (sunop (fun v => sem_unop op v tye) s).
  Proof.
    unfold wc_DS, DSForall_pres.
    intros * Hck Hop.
    revert Hck. generalize (denot_clock ck) as C; intros.
    remember (AC (sunop _ _)) as t eqn:Ht. apply Oeq_refl_eq in Ht.
    revert Hop Ht Hck.
    revert t s C.
    cofix Cof; intros.
    destruct t.
    - constructor.
      rewrite <- eqEps in Ht.
      eapply Cof; eauto.
    - assert (is_cons s) as Hcs
          by (do 2 eapply map_is_cons; setoid_rewrite <- Ht; auto).
      assert (is_cons C) as Hcc
          by (eapply is_cons_le_compat, AC_is_cons; eauto).
      apply uncons in Hcc as (vc & C' & Hc).
      apply is_cons_elim in Hcs as (vs & S & Hs).
      apply decomp_eqCon in Hc as Heqc.
      rewrite Hs, Heqc in * |-.
      rewrite sunop_eq, AC_cons in Ht.
      rewrite AC_cons in Hck.
      inv Hop.
      cases_eqn HH;
        apply Con_eq_simpl in Ht as [];
        apply Con_le_simpl in Hck as [];
        subst; try congruence.
      all: eapply DSleCon with (t := C'), Cof; eauto.
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

  (* TODO: utiliser xs,ys partout *)
  Lemma wc_fby1 :
    forall cs v xs ys,
      safe_DS xs ->
      AC xs <= cs ->
      safe_DS ys ->
      AC ys <= cs ->
      AC (fby1 (Some v) xs ys) <= cs.
  Proof.
    clear; intros.
    remember (AC (fby1 _ _ _)) as ts eqn:Ht. apply Oeq_refl_eq in Ht.
    revert_all.
    cofix Cof; intros * Sx Cx Sy Cy [| b t] Ht.
    { constructor. rewrite <- eqEps in Ht. eapply Cof with _ xs ys; eauto. }
    assert (is_cons xs) as Hcx by (eapply fby1_cons, AC_is_cons; now rewrite <- Ht).
    assert (is_cons cs) as Hcc by (eapply isCon_le, Cx; now apply AC_is_cons).
    apply uncons in Hcc as (vc & cs' & Hdec).
    apply decomp_eqCon in Hdec as Hc.
    apply is_cons_elim in Hcx as (vx & xs' & Hx).
    rewrite Hx, Hc, AC_cons in * |-; clear Hc Hx; clear xs.
    rewrite fby1_eq in Ht.
    cases; inv Sx; try tauto; rewrite AC_cons in *;
      apply Con_le_simpl in Cx as []; apply Con_eq_simpl in Ht as []; subst.
    all: econstructor; eauto; clear Hdec cs.
    - revert_all; intro Cof; cofix Cof'; intros * Sy [] ? Ht ??? Cx' ?.
      { constructor. rewrite <- eqEps in *. eapply Cof' with _ ys xs'; eauto. }
      assert (is_cons ys) as Hcy by (eapply fby1AP_cons, AC_is_cons; now rewrite <- Ht).
      apply is_cons_elim in Hcy as (vy & ys' & Hy).
      rewrite Hy, AC_cons in *; clear Hy ys.
      rewrite fby1AP_eq in Ht.
      cases; inv Sy; apply Con_le_simpl in Cy as []; try tauto || congruence.
      eapply Cof with _ xs' ys'; eauto.
    - revert_all; intro Cof; cofix Cof'; intros * v ys Sy [] ?? Ht ??? Cx' ?.
      { constructor. rewrite <- eqEps in *. eapply Cof' with ys xs'; eauto. }
      assert (is_cons ys) as Hcy by (eapply fby1AP_cons, AC_is_cons; now rewrite <- Ht).
      apply is_cons_elim in Hcy as (vy & ys' & Hy).
      rewrite Hy, AC_cons in *; clear Hy ys.
      rewrite fby1AP_eq in Ht.
      cases; inv Sy; apply Con_le_simpl in Cy as []; try tauto || congruence.
      eapply Cof with _ xs' ys'; eauto.
  Qed.

  (* TODO: refaire avec DSle_rec_eq ??? *)
  Lemma wc_fby :
    forall ck xs ys,
      safe_DS xs /\ wc_DS ck xs -> (* pour une meilleure unification plus tard... *)
      safe_DS ys /\ wc_DS ck ys ->
      wc_DS ck (fby xs ys).
  Proof.
    unfold wc_DS; intro ck.
    generalize (denot_clock ck); clear ck.
    clear; intros cs ??  [Sx Cx][Sy Cy].
    remember (AC (fby _ _)) as t eqn:Ht. apply Oeq_refl_eq in Ht.
    revert_all.
    cofix Cof; intros * Sx Cx Sy Cy [| b t] Ht.
    { constructor. rewrite <- eqEps in Ht. eapply Cof with xs ys; eauto. }
    assert (is_cons xs) as Hcx by (eapply fby_cons, AC_is_cons; now rewrite <- Ht).
    assert (is_cons cs) as Hcc by (eapply isCon_le, Cx; now apply AC_is_cons).
    apply uncons in Hcc as (vc & cs' & Hdec).
    apply decomp_eqCon in Hdec as Hc.
    apply is_cons_elim in Hcx as (vx & xs' & Hx).
    rewrite Hx, Hc, AC_cons in * |-; clear Hc Hx; clear xs.
    rewrite fby_eq in Ht.
    cases; inv Sx; try tauto; rewrite AC_cons in *;
      apply Con_le_simpl in Cx as []; apply Con_eq_simpl in Ht as [? Ht]; subst.
    all: econstructor; eauto; clear Hdec cs.
    - revert_all; intro Cof; cofix Cof'; intros * Sy [] ? Ht ??? Cx' ?.
      { constructor. rewrite <- eqEps in *. eapply Cof' with ys xs'; eauto. }
      assert (is_cons ys) as Hcy by (eapply fbyA_cons, AC_is_cons; now rewrite <- Ht).
      apply is_cons_elim in Hcy as (vy & ys' & Hy).
      rewrite Hy, AC_cons in *; clear Hy ys.
      rewrite fbyA_eq in Ht.
      cases; inv Sy; apply Con_le_simpl in Cy as []; try tauto || congruence.
      eapply Cof with xs' ys'; eauto.
    - revert_all; intro Cof; cofix Cof'; intros * Sy [] ?? Ht ??? Cx' ?.
      { constructor. rewrite <- eqEps in *. eapply Cof' with ys xs'; eauto. }
      assert (is_cons ys) as Hcy by (eapply fby1AP_cons, AC_is_cons; now rewrite <- Ht).
      apply uncons in Hcy as (vy & ys' & Hdec).
      apply decomp_eqCon in Hdec as Hy.
      rewrite Hy, AC_cons in *.
      rewrite fby1AP_eq in Ht.
      cases; inv Sy; apply Con_le_simpl in Cy as []; try tauto || congruence.
      change (cons b d <= cs'). (* sinon rewrite Ht ne marche pas *)
      rewrite Ht; auto using wc_fby1.
  Qed.

  (* (* on fait tout en un, plutôt qu'en trois lemmes *) *)
  (* Lemma safe_fby1 : *)
  (*   forall v s0 s, *)
  (*     safe_DS s0 -> *)
  (*     safe_DS s -> *)
  (*     AC s0 == AC s -> (* implied by [wc_DS ck s0 /\ wc_DS ck s] *) *)
  (*     safe_DS (fby1 (Some v) s0 s). *)
  (* Proof. *)
  (*   unfold wc_DS. *)
  (*   intros * Safe0 Safe Hac. *)
  (*   remember (fby1 _ _ _) as t eqn:Ht. apply Oeq_refl_eq in Ht. *)
  (*   revert dependent s. *)
  (*   revert dependent s0. *)
  (*   revert v t. *)
  (*   cofix Cof; intros. *)
  (*   destruct t. *)
  (*   { constructor. rewrite <- eqEps in *. eapply Cof in Ht; eauto . } *)
  (*   assert (is_cons s0) as Hs0 by (eapply fby1_cons; rewrite <- Ht; auto). *)
  (*   assert (is_cons s) as Hs by now rewrite <- AC_is_cons, <- Hac, AC_is_cons. *)
  (*   apply is_cons_elim in Hs0 as (v0 & s0' & Hs0), Hs as (sv & s' & Hs). *)
  (*   rewrite Hs, Hs0, 2 AC_cons in *. *)
  (*   inv Safe. inv Safe0. *)
  (*   rewrite fby1_eq in Ht. *)
  (*   cases_eqn HH; subst; try rewrite DS_const_eq in Ht; try rewrite fby1AP_eq in Ht. *)
  (*   all: apply Con_eq_simpl in Ht as (? & Ht), Hac as (?&?); subst; try congruence. *)
  (*   all: constructor; auto; eapply Cof in Ht; eauto. *)
  (* Qed. *)

  (* TODO: move *)
  Lemma DSle_cons_elim :
    forall D (x :  DS D) a (s : DS D),
      (Cpo_streams_type.Con a s : DS D) <= x ->
      exists t, x == Cpo_streams_type.Con a t /\ s <= t.
  Proof.
    intros * Hle.
    apply DSle_uncons in Hle as [? [ Hd]].
    apply decomp_eqCon in Hd; eauto.
  Qed.

   Lemma Con_le_le :
    forall {A} (x : A) xs y ys t,
      (Cpo_streams_type.Con x xs : DS A) <= t ->
      (Cpo_streams_type.Con y ys : DS A) <= t ->
      x = y.
  Proof.
    intros * Le1 Le2.
    eapply DSle_cons_elim in Le1 as (?& Hx &?), Le2 as (?& Hy &?).
    rewrite Hx in Hy.
    now apply Con_eq_simpl in Hy as [].
  Qed.

  Lemma safe_fby1 :
    forall v cs xs ys,
      safe_DS xs ->
      AC xs <= cs ->
      safe_DS ys ->
      AC ys <= cs ->
      safe_DS (fby1 (Some v) xs ys).
  Proof.
    clear; intros * Sx Cx Sy Cy.
    remember (fby1 _ _ _) as t eqn:Ht. apply Oeq_refl_eq in Ht.
    revert_all; cofix Cof; intros.
    destruct t as [| b t].
    { constructor. rewrite <- eqEps in Ht. apply Cof with v cs xs ys; auto. }
    assert (is_cons xs) as Hcx by (eapply fby1_cons; now rewrite <- Ht).
    apply is_cons_elim in Hcx as (vx & xs' & Hx).
    rewrite Hx, AC_cons in *; clear Hx xs.
    rewrite fby1_eq in Ht.
    cases; inv Sx; try tauto;
      apply Con_eq_simpl in Ht as [? Ht]; subst; constructor; auto.
    - revert_all; intro Cof; cofix Cof'; intros * Sy Cy [] xs' Cx' Ht ? Sx'.
      { constructor. rewrite <- eqEps in Ht. apply Cof' with v cs ys xs'; auto. }
      assert (is_cons ys) as Hcy by (eapply fby1AP_cons; now rewrite <- Ht).
      apply is_cons_elim in Hcy as (vy & ys' & Hy).
      rewrite Hy, AC_cons in *; clear Hy ys.
      rewrite fby1AP_eq in Ht.
      cases; inv Sy; try tauto.
      2: now eapply Con_le_le in Cx'; eauto 1.
      apply rem_le_compat in Cx', Cy.
      rewrite rem_cons in Cx', Cy.
      eapply Cof with v (rem cs) xs' ys'; auto.
    - revert_all; intro Cof; cofix Cof'; intros * ??? Sy Cy [] ? xs' Cx' Ht ? Sx'.
      { constructor. rewrite <- eqEps in Ht. apply Cof' with cs ys xs'; auto. }
      assert (is_cons ys) as Hcy by (eapply fby1AP_cons; now rewrite <- Ht).
      apply is_cons_elim in Hcy as (vy & ys' & Hy).
      rewrite Hy, AC_cons in *; clear Hy ys.
      rewrite fby1AP_eq in Ht.
      cases; inv Sy; try tauto. now eapply Con_le_le in Cx'; eauto 1.
      apply rem_le_compat in Cx', Cy.
      rewrite rem_cons in *.
      eapply Cof with a0 (rem cs) xs' ys'; auto.
  Qed.

  Lemma safe_fby :
    forall ck xs ys,
      safe_DS xs /\ wc_DS ck xs ->
      safe_DS ys /\ wc_DS ck ys ->
      safe_DS (fby xs ys).
  Proof.
    unfold wc_DS; intro ck.
    generalize (denot_clock ck); clear ck.
    clear; intros cs * [Sx Cx] [Sy Cy].
    remember (fby _ _) as t eqn:Ht. apply Oeq_refl_eq in Ht.
    revert_all; cofix Cof; intros.
    destruct t as [| b t].
    { constructor. rewrite <- eqEps in Ht. apply Cof with cs xs ys; auto. }
    assert (is_cons xs) as Hcx by (eapply fby_cons; now rewrite <- Ht).
    apply is_cons_elim in Hcx as (vx & xs' & Hx).
    rewrite Hx, AC_cons in *; clear Hx xs.
    rewrite fby_eq in Ht.
    cases; inv Sx; try tauto;
      apply Con_eq_simpl in Ht as [? Ht]; subst; constructor; auto.
    - revert_all; intro Cof; cofix Cof'; intros * Sy Cy [] xs' Cx' Ht ? Sx'.
      { constructor. rewrite <- eqEps in Ht. apply Cof' with cs ys xs'; auto. }
      assert (is_cons ys) as Hcy by (eapply fbyA_cons; now rewrite <- Ht).
      apply is_cons_elim in Hcy as (vy & ys' & Hy).
      rewrite Hy, AC_cons in *; clear Hy ys.
      rewrite fbyA_eq in Ht.
      cases; inv Sy; try tauto.
      2: now eapply Con_le_le in Cx'; eauto 1.
      apply rem_le_compat in Cx', Cy.
      rewrite rem_cons in Cx', Cy.
      eapply Cof with (rem cs) xs' ys'; auto.
    - revert_all; intro Cof; cofix Cof'; intros * Sy Cy [] v xs' Cx' Ht ? Sx'.
      { constructor. rewrite <- eqEps in Ht. apply Cof' with cs ys xs'; auto. }
      assert (is_cons ys) as Hcy by (eapply fby1AP_cons; now rewrite <- Ht).
      apply is_cons_elim in Hcy as (vy & ys' & Hy).
      rewrite Hy, AC_cons in *; clear Hy ys.
      rewrite fby1AP_eq in Ht.
      cases; inv Sy; try tauto. now eapply Con_le_le in Cx'; eauto 1.
      apply rem_le_compat in Cx', Cy.
      rewrite Ht, rem_cons in *.
      apply safe_fby1 with (rem cs); auto.
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
    intro Safe.
    induction e using exp_ind2; intros Hr Hwt Hwc Hoc; inv Hr.
    - (* Econst *)
      rewrite denot_exp_eq; cbn.
      auto using wt_sconst, wc_sconst, safe_sconst.
    - (* Evar *)
      inv Hwt. inv Hwc.
      edestruct Safe as (?&?&?); eauto.
      rewrite denot_exp_eq; cbn.
      repeat split; auto.
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

  Lemma safe_exps :
    safe_env ->
    forall {PSyn Prefs} (G : @global PSyn Prefs) (es : list exp),
      Forall restr_exp es ->
      Forall (wt_exp G Γ) es ->
      Forall (wc_exp G Γ) es ->
      Forall (op_correct_exp ins envI bs env) es ->
      let ss := denot_exps ins es envI bs env in
      Forall2 wt_DS (typesof es) (list_of_nprod ss)
      /\ Forall2 wc_DS (clocksof es) (list_of_nprod ss)
      /\ forall_nprod safe_DS ss.
  Proof.
    intro Safe.
    induction es as [|e es]; simpl; auto; intros.
    simpl_Forall.
    destruct IHes as (?&?&?); auto.
    eapply safe_exp in Safe as (?&?&?); eauto.
    setoid_rewrite denot_exps_eq.
    setoid_rewrite list_of_nprod_app.
    repeat split; auto using Forall2_app, forall_nprod_app.
  Qed.

  End Invariants.
  End node_safe.

Section Admissibility.

  (** Pour l'instant, on montre l'admissibilité de [safe_env] en tant que
      propriété de l'environnement des variables seulement (pas des entrées).
      Ça nécessite de donner les composants de safe_env sous forme de fonctions
      continues de l'environnement : DS_prod SI -C-> DS ...
      TODO: ça va peut-être changer avec l'environnement des entrées ???
   *)

  (* version continue de denot_var *)
  Definition denot_var_C ins envI x : DS_prod SI -C-> DS (sampl value) :=
    if mem_ident x ins then CTE _ _ (envI x) else PROJ _ x.

  Fact denot_var_eq :
    forall ins x envI env,
      denot_var ins envI env x = denot_var_C ins envI x env.
  Proof.
    intros.
    unfold denot_var, denot_var_C.
    cases.
  Qed.

  (* version continue de denot_clock *)
  Fixpoint denot_clock_C ins envI bs ck : DS_prod SI -C-> DS bool :=
    match ck with
    | Cbase =>  CTE _ _ bs
    | Con ck x (_, k) =>
        let sx := denot_var_C ins envI x in
        let cks := denot_clock_C ins envI bs ck in
        (ZIP (fun x c => match x with pres (Venum e) => (e ==b k) && c | _ => false end) @2_ sx) cks
    end.

  Fact denot_clock_eq :
    forall ins envI bs env ck,
      denot_clock ins envI bs env ck = denot_clock_C ins envI bs ck env.
  Proof.
    induction ck; simpl; cases.
    now rewrite IHck, denot_var_eq.
  Qed.

  (* version continue de (AC (denot_var ...)) *)
  Definition AC_var_C ins envI x : DS_prod SI -C-> DS bool :=
    AC @_ denot_var_C ins envI x.

  Fact AC_var_eq :
    forall ins x envI env,
      AC (denot_var ins envI env x) = AC_var_C ins envI x env.
  Proof.
    intros.
    unfold denot_var, AC_var_C, denot_var_C.
    cases.
  Qed.

  (* TODO: move *)
  Lemma and_impl :
    forall (A B C : Prop),
      (A -> B /\ C) <-> ((A -> B) /\ (A -> C)).
  Proof.
    firstorder.
  Qed.

  (* TODO: comment généraliser admissible_and plus joliment que ça? *)
  Lemma admissible_and3 :
  forall T U V (D:cpo) (P Q : T -> U -> V -> D -> Prop),
    admissible (fun d => forall x y z, P x y z d) ->
    admissible (fun d => forall x y z, Q x y z d) ->
    admissible (fun d => forall x y z, P x y z d /\ Q x y z d).
  Proof.
    Set Firstorder Depth 6.
    firstorder.
  Qed.

  Lemma safe_env_admissible :
    forall Γ ins envI bs,
      admissible (safe_env Γ ins envI bs).
  Proof.
    intros.
    unfold safe_env.
    apply admissiblePT.
    do 4 setoid_rewrite and_impl.
    repeat apply admissible_and3; apply admissiblePT.
    - unfold wt_env, wt_DS, DSForall_pres.
      do 4 setoid_rewrite DSForall_forall.
      setoid_rewrite denot_var_eq.
      apply DSForall_admissible3.
    - unfold wc_env, wc_DS.
      setoid_rewrite AC_var_eq.
      setoid_rewrite denot_clock_eq.
      intros ???????. (* TODO: appliquer le_admissible direct?? *)
      apply le_admissible; eauto 2.
    - unfold ef_env, safe_DS.
      do 4 setoid_rewrite DSForall_forall.
      setoid_rewrite denot_var_eq.
      apply DSForall_admissible3.
  Qed.

End Admissibility.


Lemma denot_clock_le :
  forall ins envI bs env env' ck ,
    env <= env' ->
    denot_clock ins envI bs env ck <=
      denot_clock ins envI bs env' ck.
Proof.
  intros.
  rewrite 2 denot_clock_eq.
  auto.
Qed.

(* TODO: move *)
Lemma DSForall_le :
  forall T (P : T -> Prop) s t,
    s <= t ->
    DSForall P t ->
    DSForall P s.
Proof.
  cofix Cof; destruct s; intros ? Le Hf; constructor;
    inversion Le as [|???? HH]; eauto 2.
  all: apply decomp_eqCon in HH; rewrite HH in *; inv Hf; eauto 2.
Qed.

(* op_correct est donné par hypothèse sur l'environment final,
   mais on aura besoin de l'avoir à chaque itération *)
Lemma op_correct_exp_le :
  forall ins envI bs env env',
    env <= env' ->
    forall e,
      op_correct_exp ins envI bs env' e ->
      op_correct_exp ins envI bs env e.
Proof.
  intros * Le.
  induction e using exp_ind2; intros Hop; inv Hop;
    constructor; eauto using Forall_impl_inside.
  - (* unop *)
    intros ty Hty.
    specialize (H3 ty Hty).
    rewrite forall_nprod_k_iff in *.
    intros k Hk.
    eapply DSForall_le, H3; eauto.
Qed.

Definition admissible_rev (D:cpo)(P:D->Type) :=
  forall f : natO -m> D, P (lub f) -> (forall n, P (f n)).

(* TODO: inutile *)
Lemma admissible_impl :
  forall (D : cpo) (P Q : D -> Type),
    admissible P ->
    admissible_rev _ Q ->
    admissible (fun x => Q x -> P x).
Proof.
  unfold admissible, admissible_rev.
  auto.
Qed.

(* TODO: expliquer le raisonnement avant/arrière *)
Lemma fixp_inv2 : forall (D:cpo) (F:D -m> D) (P P' Q : D -> Prop),
    (forall x, P' x -> P x) ->
    admissible P ->
    admissible_rev _ Q ->
    Q (fixp F) ->
    P' 0 ->
    (forall x, P' x -> Q x -> P' (F x)) ->
    P (fixp F).
Proof.
  intros; unfold fixp.
  apply X; intros.
  eapply proj2 with (A := P' (iter (D:=D) F n)).
  induction n; simpl; auto.
  destruct IHn.
  firstorder.
Qed.

(* TODO: move *)
Lemma list_of_nprod_nth :
  forall {n} (np : nprod n) k d,
    k < n ->
    nth k (list_of_nprod np) d = get_nth k np.
Proof.
  induction n as [|[]]; auto; intros * Hk. inv Hk.
  - destruct k as [|[]]; now inv Hk.
  - destruct k; auto.
    apply IHn; auto with arith.
Qed.

Lemma Forall2_Forall3 :
  forall {A B C} (P : A -> B -> Prop) (Q : B -> C -> Prop) xs ys zs,
    Forall2 P xs ys ->
    Forall2 Q ys zs ->
    Forall3 (fun x y z => P x y /\ Q y z) xs ys zs.
Proof.
  intros * Hp Hq.
  revert dependent zs.
  induction Hp; intros; simpl_Forall.
  constructor.
  inv Hq. constructor; auto.
Qed.

(* TODO: move *)
Lemma mem_nth_nth :
  forall x l k d,
    mem_nth l x = Some k ->
    k < length l /\ nth k l d = x.
Proof.
  induction l; simpl; intros * Hk; try congruence.
  destruct ident_eq_dec; subst; inv Hk; auto with arith.
  apply option_map_inv in H0 as (?& HH &?); subst.
  edestruct IHl; eauto with arith.
Qed.

Lemma Forall2_nth :
  forall {A B} (P : A -> B -> Prop) xs ys a b n,
    Forall2 P xs ys ->
    n < length xs ->
    P (nth n xs a) (nth n ys b).
Proof.
  intros * H HH.
  rewrite Forall2_forall2 in H.
  eapply H; eauto.
Qed.

Lemma HasClock_det :
  forall Γ x ck1 ck2,
    HasClock Γ x ck1 ->
    HasClock Γ x ck2 ->
    ck1 = ck2.
Proof.
  intros * C1 C2; inv C1; inv C2.
  (* TODO: vrai ou pas ??? *)
Admitted.

Lemma HasType_det :
  forall Γ x ty1 ty2,
    HasType Γ x ty1 ->
    HasType Γ x ty2 ->
    ty1 = ty2.
Proof.
Admitted.

Lemma mem_ident_false :
  forall x xs,
    mem_ident x xs = false ->
    In x xs ->
    False.
Proof.
  intros * Hf Hin.
  apply mem_ident_spec in Hin.
  congruence.
Qed.

Lemma mem_nth_nIn :
  forall x xs,
    mem_nth xs x = None ->
    In x xs ->
    False.
Proof.
  intros * Hf Hin.
  induction xs; simpl in *; cases.
  apply option_map_None in Hf.
  firstorder.
Qed.

Lemma IsVar_In :
  forall Γ x,
    IsVar Γ x ->
    In x (List.map fst Γ).
Proof.
  intros * Hv.
  inv Hv.
  now apply fst_InMembers.
Qed.


(** * Deuxième partie : montrer que safe_env est préservé *)
Theorem safe_equ :
  forall {PSyn Prefs} (G : @global PSyn Prefs),
  forall Γ ins envI bs xs es,
    Forall restr_exp es ->
    Permutation (List.map fst Γ) (ins ++ xs) ->
    wc_equation G Γ (xs,es) ->
    wt_equation G Γ (xs,es) ->
    safe_env Γ ins envI bs 0 ->
    let env := FIXP (DS_prod SI) (denot_equation ins (xs,es) envI bs) in
    Forall (op_correct_exp ins envI bs env) es ->
    safe_env Γ ins envI bs env.
Proof.
  intros ??????? xs es Hr Hperm Hwc Hwt S0 env Hop; subst env.
  rewrite FIXP_fixp.
  (* on a besoin de la croissance de env à chaque coup de denot_equation *)
  (* TODO: il y a peut-être plus joli : *)
  apply fixp_inv2 with
    (Q := fun env =>
             Forall (op_correct_exp ins envI bs env) es)
    (P' := fun env =>
             env <= denot_equation ins (xs,es) envI bs env
             /\ safe_env Γ ins envI bs env);
    try tauto; auto using safe_env_admissible.
  - clear. induction es; intros ? Hf ?; inv Hf; eauto using op_correct_exp_le.
  - clear Hop.
    intros env (Le & Safe) Hop.
    split; eauto using fmon_le_compat; auto.
    inv Hwt. inv Hwc. { inversion Hr as [|?? HH]; inv HH. }
    assert (length xs = list_sum (List.map numstreams es))
      by (rewrite <- annots_numstreams, <- length_typesof_annots;
          eauto using Forall2_length).
    eapply safe_exps in Safe as Ss; eauto.
    destruct Ss as (Wts & Wcs & Sfs).
    intros x ty ck Hty Hck.
    edestruct Safe as (Wc & Wt & Ef); eauto.
    eapply Permutation_in, in_app_or in Hperm; eauto using IsVar_In, HasClock_IsVar.
    unfold denot_var in *.
    setoid_rewrite denot_equation_eq.
    cases_eqn HH; simpl; try congruence.
    + (* entrée *)
      unfold wc_DS in *.
      repeat split; eauto 3 using denot_clock_le.
    + eapply mem_nth_nth with (d := xH) in HH1 as [? Hn]; rewrite <- Hn in *.
      repeat split.
      * (* wt_DS *)
        eapply Forall2_Forall3, Forall3_forall3 in Wts as (?&?& Hf); eauto.
        eapply Hf; rewrite ?list_of_nprod_nth; auto; try congruence.
        eapply HasType_det; try apply Forall2_nth; eauto.
        Unshelve. all: auto; exact 0.
      * (* wc_DS *)
        unfold wc_DS in *.
        eapply Ole_trans, denot_clock_le, Le.
        eapply Forall2_Forall3, Forall3_forall3 in Wcs as (_ & Hl & Hf); auto.
        rewrite list_of_nprod_length in Hl.
        eapply Hf; rewrite ?list_of_nprod_nth; eauto; try congruence.
        eapply HasClock_det; try apply Forall2_nth; eauto.
        Unshelve. all: eauto; exact 0.
      * apply forall_nprod_k'; auto; congruence.
    + (* erreur *)
      exfalso.
      destruct Hperm; eauto using mem_ident_false, mem_nth_nIn.
Qed.

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
