From Coq Require Import String Morphisms Permutation.
From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Velus Require Import Common.
From Velus Require Import CommonList.
From Velus Require Import CommonTyping.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import CoindStreams.
From Velus Require Import Clocks.
From Velus Require Import Lustre.StaticEnv.
From Velus Require Import Lustre.LSyntax Lustre.LTyping Lustre.LClocking Lustre.LSemantics Lustre.LOrdered.

From Velus Require Import Lustre.Denot.Cpo.
Require Import Cpo_ext CommonDS SDfuns Denot CommonList2.


(* On n'importe pas COINDSTREAMS car il définit un type env
   qui fait des conflits avec les env dénotationnels... *)
Module Type LDENOTSAFE
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks   : CLOCKS        Ids Op OpAux)
       (Import Senv  : STATICENV     Ids Op OpAux Cks)
       (Import Syn   : LSYNTAX       Ids Op OpAux Cks Senv)
       (Import Typ   : LTYPING       Ids Op OpAux Cks Senv Syn)
       (Import Cl    : LCLOCKING     Ids Op OpAux Cks Senv Syn)
       (Import Lord  : LORDERED      Ids Op OpAux Cks Senv Syn)
       (Import Den   : LDENOT        Ids Op OpAux Cks Senv Syn Lord).


Section Static_env_node.

  Lemma NoDup_senv :
    forall (nd : node),
      NoDupMembers (senv_of_inout (n_in nd ++ n_out nd)).
  Proof.
    intros.
    rewrite fst_NoDupMembers, map_fst_senv_of_inout, <-fst_NoDupMembers.
    apply n_nodup.
  Qed.

  Lemma Ty_senv :
    forall (n : node) x ty,
      HasType (senv_of_inout (n_in n)) x ty ->
      In (x,ty) (List.map (fun '(x, (ty, _, _)) => (x, ty)) (n_in n)).
  Proof.
    intros * Hty.
    pose proof (NoDup_senv n) as ND. rewrite senv_of_inout_app in ND.
    apply NoDupMembers_app_l in ND.
    inv Hty; subst.
    induction (n_in n) as [| (?&((?&?)&?)) nins]. inv H.
    inv ND. simpl in *; subst; eauto.
    destruct H as [|Hxin]; subst; eauto.
    inv H; eauto.
  Qed.

  Lemma HasClock_app_1 :
    forall (n : node) x ck,
      HasClock (senv_of_inout (n_in n ++ n_out n)) x ck ->
      In x (List.map fst (n_in n)) ->
      HasClock (senv_of_inout n.(n_in)) x ck.
  Proof.
    intros * Hck Hin; subst.
    pose proof (NoDup_senv n) as Hnd.
    rewrite senv_of_inout_app in *.
    apply HasClock_app in Hck as [|Hck]; auto.
    rewrite fst_NoDupMembers, map_app,map_fst_senv_of_inout in Hnd.
    apply HasClock_IsVar, IsVar_In in Hck.
    now destruct (NoDup_app_In _ _ _ Hnd Hin).
  Qed.

  Lemma HasType_app_1 :
    forall (n : node) x ty,
      HasType (senv_of_inout (n_in n ++ n_out n)) x ty ->
      In x (List.map fst (n_in n)) ->
      HasType (senv_of_inout n.(n_in)) x ty.
  Proof.
    intros * Hck Hin; subst.
    pose proof (NoDup_senv n) as Hnd.
    rewrite senv_of_inout_app in *.
    apply HasType_app in Hck as [|Hck]; auto.
    rewrite fst_NoDupMembers, map_app,map_fst_senv_of_inout in Hnd.
    apply HasType_IsVar, IsVar_In in Hck.
    now destruct (NoDup_app_In _ _ _ Hnd Hin).
  Qed.

  Lemma HasClock_senv :
    forall (n : node) x ck,
      HasClock (senv_of_inout (n_in n)) x ck ->
      In (x,ck) (List.map (fun '(x, (_, ck, _)) => (x, ck)) (n_in n)).
  Proof.
    intros * Hck.
    pose proof (NoDup_senv n) as ND. rewrite senv_of_inout_app in ND.
    apply NoDupMembers_app_l in ND.
    inv Hck; subst.
    induction (n_in n) as [| (?&((?&?)&?)) nins]. inv H.
    inv ND. simpl in *; subst; eauto.
    destruct H as [|Hxin]; subst; eauto.
    inv H; eauto.
  Qed.

End Static_env_node.



(** ** TODO: description *)
Section Op_correct.

Variables
  (G : global)
  (ins : list ident)
  (envG : Dprodi FI)
  (envI : DS_prod SI)
  (bs : DS bool)
  (env : DS_prod SI).

Definition DSForall_pres {A} (P : A -> Prop) : DS (sampl A) -> Prop :=
  DSForall (fun s => match s with pres v => P v | _ => True end).

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
        forall_nprod (DSForall_pres (fun v => wt_value v ty -> sem_unop op v ty <> None)) (denot_exp G ins e envG envI bs env)
    ) ->
    op_correct_exp (Eunop op e ann)
| opc_Efby :
  forall e0s es anns,
    Forall op_correct_exp e0s ->
    Forall op_correct_exp es ->
    op_correct_exp (Efby e0s es anns)
| opc_Ewhen :
  forall es x k anns,
    Forall op_correct_exp es ->
    op_correct_exp (Ewhen es x k anns)
| opc_Eapp :
  forall f es anns,
    Forall op_correct_exp es ->
    (* TODO : quelles hypothèses ? *)
    op_correct_exp (Eapp f es [] anns)
.

Definition op_correct (n : node) : Prop :=
  match n.(n_block) with
  | Beq (xs,es) => Forall op_correct_exp es
  | _ => True
  end.

End Op_correct.

(** ** Facts about op_correct  *)

Lemma op_correct_exp_cons :
  forall e nd nds tys exts ins envG envI bs env,
    ~ Is_node_in_exp nd.(n_name) e ->
    op_correct_exp (Global tys exts (nd :: nds)) ins envG envI bs env e ->
    op_correct_exp (Global tys exts (nds)) ins envG envI bs env e.
Proof.
  induction e using exp_ind2; intros * Hnin Hop; inv Hop;
    eauto using op_correct_exp.
  - (* Eunop *)
    setoid_rewrite <- denot_exp_cons in H3;
      eauto 6 using op_correct_exp, Is_node_in_exp.
  - (* Efby *)
    constructor.
    + eapply Forall_and, Forall_impl_In in H; eauto.
      intros e Hin [Hop HH].
      eapply HH; eauto. intro Hn. apply Hnin.
      constructor; left; solve_Exists.
    + eapply Forall_and, Forall_impl_In in H0; eauto.
      intros e Hin [Hop HH].
      eapply HH; eauto. intro Hn. apply Hnin.
      constructor; right; solve_Exists.
  - (* Ewhen *)
    constructor.
    eapply Forall_and, Forall_impl_In in H; eauto.
    intros e Hin [Hop HH].
    eapply HH; eauto. intro Hn. apply Hnin.
    constructor; solve_Exists.
  - (* Eapp *)
    constructor.
    eapply Forall_and, Forall_impl_In in H; eauto.
    intros e Hin [Hop HH].
    eapply HH; eauto. intro Hn. apply Hnin.
    constructor; left; solve_Exists.
Qed.

Lemma op_correct_cons :
  forall n nd nds tys exts ins envG envI bs env,
    ~ Is_node_in_block nd.(n_name) n.(n_block) ->
    op_correct (Global tys exts (nd :: nds)) ins envG envI bs env n ->
    op_correct (Global tys exts nds) ins envG envI bs env n.
Proof.
  unfold op_correct.
  intros * Hnin Hop; cases.
  eapply Forall_impl_In in Hop; eauto.
  intros * Hin.
  apply op_correct_exp_cons.
  intro.
  apply Hnin, INBeq.
  unfold Is_node_in_eq.
  solve_Exists.
Qed.

Global Add Parametric Morphism G ins : (@op_correct_exp G ins)
    with signature @Oeq (Dprodi FI) ==> @Oeq (DS_prod SI) ==> @Oeq (DS bool) ==>
                     @Oeq (DS_prod SI) ==> @eq exp ==> iff
      as op_correct_exp_morph.
Proof.
  intros * Eq1 * Eq2 * Eq3 * Eq4 e.
  induction e using exp_ind2; split; intro Hoc; inv Hoc.
  all: try now (constructor; eauto using Forall_iff).
  - take (op_correct_exp _ _ _ _ _ _ _) and apply IHe in it.
    constructor; intros; eauto.
    rewrite <- Eq1, <- Eq2, <- Eq3, <- Eq4; auto.
  - take (op_correct_exp _ _ _ _ _ _ _) and apply IHe in it.
    constructor; intros; eauto.
    rewrite Eq1, Eq2, Eq3, Eq4; auto.
  - setoid_rewrite and_comm in H.
    setoid_rewrite and_comm in H0.
    constructor; eauto using Forall_iff.
  - setoid_rewrite and_comm in H.
    constructor; eauto using Forall_iff.
  - setoid_rewrite and_comm in H.
    constructor; eauto using Forall_iff.
Qed.

Global Add Parametric Morphism G ins : (@op_correct G ins)
    with signature @Oeq (Dprodi FI) ==> @Oeq (DS_prod SI) ==> @Oeq (DS bool) ==>
                     @Oeq (DS_prod SI) ==> @eq node ==> iff
      as op_correct_morph.
Proof.
  intros * Eq1 * Eq2 * Eq3 * Eq4 *.
  unfold op_correct.
  cases; try tauto.
  split; intros * HH; simpl_Forall.
  all: eapply op_correct_exp_morph in HH; eauto.
Qed.


(** ** Safety properties of synchronous streams *)

Section Safe_DS.

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

End Safe_DS.


Section SDfuns_safe.

  Variables
    (Γ : static_env)
    (G : global)
    (ins : list ident)
    (envG : Dprodi FI)
    (envI : DS_prod SI)
    (bs : DS bool)
    (env : DS_prod SI).

  Definition sample (k : enumtag) (x : sampl value) (c : bool) : bool :=
    match x with
    | pres (Venum e) => (k =? e) && c
    | _ => false
    end.

  Fixpoint denot_clock ck : DS bool :=
    match ck with
    | Cbase => bs
    | Con ck x (_, k) =>
        let sx := denot_var ins envI env x in
        let cks := denot_clock ck in
        ZIP (sample k) sx cks
    end.

  (** A stream of values of type ty *)
  Definition ty_DS (ty : type) (s : DS (sampl value)) : Prop :=
    DSForall_pres (fun v => wt_value v ty) s.

  Add Parametric Morphism : ty_DS
      with signature eq ==> @Oeq (DS (sampl value)) ==> iff as ty_DS_Morph.
  Proof.
    unfold ty_DS.
    intros * H.
    now setoid_rewrite H.
  Qed.

  (** A stream that respects its clock (≃ alignment).
      Because the stream might not yet be fully computed, we use
      an inequality. This predicate holds in the denotational
      model because the computation of an expression denotation
      implicitly depends on the clock stream, and thus cannot
      exceed it. See [safe_exp] below.
   *)
  (* c'est exactement le ClockedStreams(T,s) de Marc *)
  Definition cl_DS (ck : clock) (s : DS (sampl value)) :=
    AC s <= denot_clock ck.

  (** Global hypothesis on the environment *)
  Definition env_correct :=
    forall x ty ck,
      HasType Γ x ty ->
      HasClock Γ x ck ->
      let s := denot_var ins envI env x in
      ty_DS ty s
      /\ cl_DS ck s
      /\ safe_DS s.


  (** Quelques résultats du type : qui peut le plus, peut le moins *)

  Lemma ty_DS_le :
    forall ty x y,
      x <= y ->
      ty_DS ty y ->
      ty_DS ty x.
  Proof.
    intros.
    now apply DSForall_le with y.
  Qed.

  Lemma cl_DS_le :
    forall ck x y,
      x <= y ->
      cl_DS ck y ->
      cl_DS ck x.
  Proof.
    unfold cl_DS.
    intros.
    apply Ole_trans with (AC y); auto.
  Qed.

  Lemma safe_DS_le :
    forall x y,
      x <= y ->
      safe_DS y ->
      safe_DS x.
  Proof.
    intros.
    now apply DSForall_le with y.
  Qed.

  Lemma Forall2_ty_DS_le :
    forall n tys (xs ys : nprod n),
      xs <= ys ->
      Forall2 ty_DS tys (list_of_nprod ys) ->
      Forall2 ty_DS tys (list_of_nprod xs).
  Proof.
    induction n as [|[]]; intros * Hle Hf; auto.
    - inv Hf; simpl_Forall; eauto using ty_DS_le.
    - destruct Hle; inv Hf; constructor; eauto using ty_DS_le.
  Qed.

  Lemma Forall2_cl_DS_le :
    forall n cks (xs ys : nprod n),
      xs <= ys ->
      Forall2 cl_DS cks (list_of_nprod ys) ->
      Forall2 cl_DS cks (list_of_nprod xs).
  Proof.
    induction n as [|[]]; intros * Hle Hf; auto.
    - inv Hf; simpl_Forall; eauto using cl_DS_le.
    - destruct Hle; inv Hf; constructor; eauto using cl_DS_le.
  Qed.

  Lemma forall_safe_le :
    forall n (xs ys : nprod n),
      xs <= ys ->
      forall_nprod safe_DS ys ->
      forall_nprod safe_DS xs.
  Proof.
    setoid_rewrite forall_nprod_k_iff.
    intros * Hle Hf k d Hk.
    eapply safe_DS_le, Hf, Hk; auto.
  Qed.

  (** ** Faits sur sconst  *)

  Lemma cl_sconst :
    forall c, cl_DS Cbase (sconst c bs).
  Proof.
    unfold cl_DS.
    intros.
    rewrite AC_sconst; auto.
  Qed.

  Lemma ty_sconst :
    forall c, ty_DS (Tprimitive (ctype_cconst c)) (sconst (Vscalar (sem_cconst c)) bs).
  Proof.
    intro.
    unfold ty_DS, DSForall_pres, sconst.
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

  Lemma ty_sunop :
    forall op s ty tye,
      type_unop op tye = Some ty ->
      ty_DS tye s ->
      ty_DS ty (sunop (fun v => sem_unop op v tye) s).
  Proof.
    intros * Hop Hwt.
    unfold ty_DS, DSForall_pres, sunop in *.
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
      ty_DS tye s ->
      safe_DS s ->
      safe_ty (sunop (fun v => sem_unop op v tye) s).
  Proof.
    intros * Hop Hwt Hsf.
    unfold ty_DS, safe_ty, safe_DS, sunop in *.
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

  Lemma cl_sunop :
    forall op s ck tye,
      cl_DS ck s ->
      DSForall_pres (fun v => sem_unop op v tye <> None) s ->
      cl_DS ck (sunop (fun v => sem_unop op v tye) s).
  Proof.
    unfold cl_DS, DSForall_pres.
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
          by (eapply map_is_cons, map_is_cons, is_cons_eq_compat; eauto).
      assert (is_cons C) as Hcc
          by (eapply is_cons_le_compat, AC_is_cons; eauto).
      apply uncons in Hcc as (vc & C' & Hc).
      apply is_cons_elim in Hcs as (vs & S & Hs).
      apply decomp_eqCon in Hc as Heqc.
      rewrite Hs, Heqc in * |-.
      rewrite sunop_eq, AC_eq in Ht.
      rewrite AC_eq in Hck.
      inv Hop.
      cases_eqn HH;
        apply Con_eq_simpl in Ht as [];
        apply Con_le_simpl in Hck as [];
        subst; try congruence.
      all: eapply DSleCon with (t := C'), Cof; eauto.
  Qed.

  (** ** Faits sur fby1/fby *)

  Lemma ty_fby1 :
    forall ty b ov xs ys,
      (match ov with Some v => wt_value v ty | _ => True end) ->
      ty_DS ty xs ->
      ty_DS ty ys ->
      ty_DS ty (fby1s b ov xs ys).
  Proof.
    intros * Wtv Wt0 Wt.
    unfold ty_DS, DSForall_pres in *.
    remember (fby1s _ _ _ _) as t eqn:Ht. apply Oeq_refl_eq in Ht.
    revert dependent ys.
    revert dependent xs.
    revert dependent ov.
    revert t b.
    cofix Cof; intros.
    destruct t.
    { constructor; rewrite <- eqEps in *; now eauto 2. }
    assert (is_cons (fby1s b ov xs ys)) as Hc by (rewrite <- Ht; auto).
    destruct b.
    - (* fby1AP *)
      apply fby1AP_cons, is_cons_elim in Hc as (?&?& Hx); rewrite Hx in *.
      fold (fby1AP ov) in Ht.
      rewrite fby1AP_eq in Ht.
      cases_eqn HH; subst; try (rewrite Ht; now apply DSForall_const).
      all: assert (is_cons xs) as Hc by (eapply fby1_cons; now rewrite <- Ht).
      all: apply is_cons_elim in Hc as (?&?&Hy); rewrite Hy in *.
      all: rewrite fby1_eq in Ht.
      all: cases_eqn HH; subst; try (rewrite Ht; now apply DSForall_const).
      all: apply Con_eq_simpl in Ht as (? & Ht); subst.
      all: inv Wt; inv Wt0; constructor; auto.
      (*  serait plus joli mais ralentit beaucoup le Qed :
          all: unfold fby1AP in Ht; apply Cof in Ht; auto. *)
      all: eapply Cof; rewrite ?Ht; unfold fby1AP; now auto.
    - (* fby1 *)
      apply fby1_cons, is_cons_elim in Hc as (?&?& Hx); rewrite Hx in *.
      fold (fby1 ov) in Ht.
      rewrite fby1_eq in Ht.
      cases_eqn HH; subst; try (rewrite Ht; now apply DSForall_const).
      all: apply Con_eq_simpl in Ht as (? & Ht); subst.
      all: inv Wt0; constructor; auto.
      all: eapply Cof; rewrite ?Ht; unfold fby1AP; now auto.
  Qed.

  Lemma ty_fby :
    forall ty xs ys,
      ty_DS ty xs ->
      ty_DS ty ys ->
      ty_DS ty (fby xs ys).
  Proof.
    intros * Wt0 Wt.
    unfold ty_DS, DSForall_pres, fby in *.
    generalize false as b; intro.
    remember (fbys _ _ _) as t eqn:Ht. apply Oeq_refl_eq in Ht.
    revert dependent ys.
    revert dependent xs.
    revert t b.
    cofix Cof; intros.
    destruct t.
    { constructor; rewrite <- eqEps in *; now eauto 2. }
    assert (is_cons (fbys b xs ys)) as Hc by (rewrite <- Ht; auto).
    destruct b.
    - (* fbyA *)
      apply fbyA_cons, is_cons_elim in Hc as (?&?& Hx); rewrite Hx in *.
      fold (@fbyA value) in Ht.
      rewrite fbyA_eq in Ht.
      cases_eqn HH; subst; try (rewrite Ht; now apply DSForall_const).
      all: assert (is_cons xs) as Hc by (eapply fby_cons; now rewrite <- Ht).
      all: apply is_cons_elim in Hc as (?&?&Hy); rewrite Hy in *.
      all: rewrite fby_eq in Ht.
      all: cases_eqn HH; subst; try (rewrite Ht; now apply DSForall_const).
      all: apply Con_eq_simpl in Ht as (? & Ht); subst.
      all: inv Wt; inv Wt0; constructor; auto.
      + unfold fbyA in Ht; apply Cof in Ht; auto.
      + rewrite Ht. now apply ty_fby1.
    - (* fby *)
      apply fby_cons, is_cons_elim in Hc as (?&?& Hx); rewrite Hx in *.
      fold (@fby value) in Ht.
      rewrite fby_eq in Ht.
      cases_eqn HH; subst; try (rewrite Ht; now apply DSForall_const).
      all: apply Con_eq_simpl in Ht as (? & Ht); subst.
      all: inv Wt0; constructor; auto.
      + unfold fbyA in Ht; apply Cof in Ht; auto.
      + rewrite Ht. now apply ty_fby1.
  Qed.

  Lemma cl_fby1 :
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
    rewrite Hx, Hc, AC_eq in * |-; clear Hc Hx; clear xs.
    rewrite fby1_eq in Ht.
    cases; inv Sx; try tauto; rewrite AC_eq in *;
      apply Con_le_simpl in Cx as []; apply Con_eq_simpl in Ht as []; subst.
    all: econstructor; eauto; clear Hdec cs.
    - revert_all; intro Cof; cofix Cof'; intros * Sy [] ? Ht ??? Cx' ?.
      { constructor. rewrite <- eqEps in *. eapply Cof' with _ ys xs'; eauto. }
      assert (is_cons ys) as Hcy by (eapply fby1AP_cons, AC_is_cons; now rewrite <- Ht).
      apply is_cons_elim in Hcy as (vy & ys' & Hy).
      rewrite Hy, AC_eq in *; clear Hy ys.
      rewrite fby1AP_eq in Ht.
      cases; inv Sy; apply Con_le_simpl in Cy as []; try tauto || congruence.
      eapply Cof with _ xs' ys'; eauto.
    - revert_all; intro Cof; cofix Cof'; intros * v ys Sy [] ?? Ht ??? Cx' ?.
      { constructor. rewrite <- eqEps in *. eapply Cof' with ys xs'; eauto. }
      assert (is_cons ys) as Hcy by (eapply fby1AP_cons, AC_is_cons; now rewrite <- Ht).
      apply is_cons_elim in Hcy as (vy & ys' & Hy).
      rewrite Hy, AC_eq in *; clear Hy ys.
      rewrite fby1AP_eq in Ht.
      cases; inv Sy; apply Con_le_simpl in Cy as []; try tauto || congruence.
      eapply Cof with _ xs' ys'; eauto.
  Qed.

  (* TODO: refaire avec DSle_rec_eq ??? *)
  Lemma cl_fby :
    forall ck xs ys,
      safe_DS xs /\ cl_DS ck xs -> (* pour une meilleure unification plus tard... *)
      safe_DS ys /\ cl_DS ck ys ->
      cl_DS ck (fby xs ys).
  Proof.
    unfold cl_DS; intro ck.
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
    rewrite Hx, Hc, AC_eq in * |-; clear Hc Hx; clear xs.
    rewrite fby_eq in Ht.
    cases; inv Sx; try tauto; rewrite AC_eq in *;
      apply Con_le_simpl in Cx as []; apply Con_eq_simpl in Ht as [? Ht]; subst.
    all: econstructor; eauto; clear Hdec cs.
    - revert_all; intro Cof; cofix Cof'; intros * Sy [] ? Ht ??? Cx' ?.
      { constructor. rewrite <- eqEps in *. eapply Cof' with ys xs'; eauto. }
      assert (is_cons ys) as Hcy by (eapply fbyA_cons, AC_is_cons; now rewrite <- Ht).
      apply is_cons_elim in Hcy as (vy & ys' & Hy).
      rewrite Hy, AC_eq in *; clear Hy ys.
      rewrite fbyA_eq in Ht.
      cases; inv Sy; apply Con_le_simpl in Cy as []; try tauto || congruence.
      eapply Cof with xs' ys'; eauto.
    - revert_all; intro Cof; cofix Cof'; intros * Sy [] ?? Ht ??? Cx' ?.
      { constructor. rewrite <- eqEps in *. eapply Cof' with ys xs'; eauto. }
      assert (is_cons ys) as Hcy by (eapply fby1AP_cons, AC_is_cons; now rewrite <- Ht).
      apply uncons in Hcy as (vy & ys' & Hdec).
      apply decomp_eqCon in Hdec as Hy.
      rewrite Hy, AC_eq in *.
      rewrite fby1AP_eq in Ht.
      cases; inv Sy; apply Con_le_simpl in Cy as []; try tauto || congruence.
      change (cons b d <= cs'). (* sinon rewrite Ht ne marche pas *)
      rewrite Ht; auto using cl_fby1.
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
    rewrite Hx, AC_eq in *; clear Hx xs.
    rewrite fby1_eq in Ht.
    cases; inv Sx; try tauto;
      apply Con_eq_simpl in Ht as [? Ht]; subst; constructor; auto.
    - revert_all; intro Cof; cofix Cof'; intros * Sy Cy [] xs' Cx' Ht ? Sx'.
      { constructor. rewrite <- eqEps in Ht. apply Cof' with v cs ys xs'; auto. }
      assert (is_cons ys) as Hcy by (eapply fby1AP_cons; now rewrite <- Ht).
      apply is_cons_elim in Hcy as (vy & ys' & Hy).
      rewrite Hy, AC_eq in *; clear Hy ys.
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
      rewrite Hy, AC_eq in *; clear Hy ys.
      rewrite fby1AP_eq in Ht.
      cases; inv Sy; try tauto. now eapply Con_le_le in Cx'; eauto 1.
      apply rem_le_compat in Cx', Cy.
      rewrite rem_cons in *.
      eapply Cof with a0 (rem cs) xs' ys'; auto.
  Qed.

  Lemma safe_fby :
    forall ck xs ys,
      safe_DS xs /\ cl_DS ck xs ->
      safe_DS ys /\ cl_DS ck ys ->
      safe_DS (fby xs ys).
  Proof.
    unfold cl_DS; intro ck.
    generalize (denot_clock ck); clear ck.
    clear; intros cs * [Sx Cx] [Sy Cy].
    remember (fby _ _) as t eqn:Ht. apply Oeq_refl_eq in Ht.
    revert_all; cofix Cof; intros.
    destruct t as [| b t].
    { constructor. rewrite <- eqEps in Ht. apply Cof with cs xs ys; auto. }
    assert (is_cons xs) as Hcx by (eapply fby_cons; now rewrite <- Ht).
    apply is_cons_elim in Hcx as (vx & xs' & Hx).
    rewrite Hx, AC_eq in *; clear Hx xs.
    rewrite fby_eq in Ht.
    cases; inv Sx; try tauto;
      apply Con_eq_simpl in Ht as [? Ht]; subst; constructor; auto.
    - revert_all; intro Cof; cofix Cof'; intros * Sy Cy [] xs' Cx' Ht ? Sx'.
      { constructor. rewrite <- eqEps in Ht. apply Cof' with cs ys xs'; auto. }
      assert (is_cons ys) as Hcy by (eapply fbyA_cons; now rewrite <- Ht).
      apply is_cons_elim in Hcy as (vy & ys' & Hy).
      rewrite Hy, AC_eq in *; clear Hy ys.
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
      rewrite Hy, AC_eq in *; clear Hy ys.
      rewrite fby1AP_eq in Ht.
      cases; inv Sy; try tauto. now eapply Con_le_le in Cx'; eauto 1.
      apply rem_le_compat in Cx', Cy.
      rewrite Ht, rem_cons in *.
      apply safe_fby1 with (rem cs); auto.
  Qed.


  (** ** Faits sur swhenv *)

  Lemma ty_swhenv :
    forall ty xs tx tn k cs,
      k < length tn ->
      ty_DS ty xs ->
      ty_DS (Tenum tx tn) cs ->
      ty_DS ty (swhenv k xs cs).
  Proof.
    intros * Hk Wtx Wtc.
    unfold ty_DS, DSForall_pres, swhenv in *.
    remember (swhen _ _ _ _ _ _) as t eqn:Ht. apply Oeq_refl_eq in Ht.
    revert dependent cs.
    revert dependent xs.
    revert t.
    cofix Cof; intros.
    destruct t.
    { constructor; rewrite <- eqEps in *; now eauto 2. }
    assert (is_cons (swhen _ _ _ k xs cs)) as Hc by (rewrite <- Ht; auto).
    apply swhen_cons in Hc as [Hx Hc].
    apply is_cons_elim in Hc as (?&?&Hc), Hx as (?&?&Hx).
    rewrite Hx, Hc in *.
    inv Wtx. inv Wtc.
    rewrite swhen_eq in Ht.
    cases_eqn HH; subst; try (rewrite Ht; now apply DSForall_const).
    all: apply Con_eq_simpl in Ht as (? & Ht); subst.
    all: constructor; auto; eapply Cof; eauto.
  Qed.

  (* TODO: refaire les autres avec DSle_rec_eq, c'est 1000 fois mieux *)
  Lemma cl_swhenv :
    forall tx tn xs ck x ty k,
      let cs := denot_var ins envI env x in
      ty_DS (Tenum tx tn) cs
      /\ safe_DS xs /\ cl_DS ck xs
      /\ safe_DS cs /\ cl_DS ck cs ->
      cl_DS (Con ck x (ty, k)) (swhenv k xs cs).
  Proof.
    unfold cl_DS, swhenv.
    intros * (Tc & Sx & Cx & Sc & Cc); simpl.
    eapply DSle_rec_eq with
      (R := fun U V => exists xs cs cks,
                ty_DS (Tenum tx tn) cs
                /\ safe_DS cs
                /\ safe_DS xs
                /\ AC cs <= cks
                /\ AC xs <= cks
                /\ U == AC (swhen _ _ _ k xs cs)
                /\ V == ZIP (sample k) cs cks).
    3: eauto 10.
    { intros * ? J K. setoid_rewrite <- J. setoid_rewrite <- K. eauto. }
    clear.
    intros u U V (xs & cs & cks & Tc & Sc & Sx & Cc & Cx & HU & HV).
    assert (is_cons xs) as Hcx.
    { eapply proj1, swhen_cons, AC_is_cons; now rewrite <- HU. }
    assert (is_cons cs) as Hcc.
    { eapply proj2, swhen_cons, AC_is_cons; now rewrite <- HU. }
    apply is_cons_elim in Hcc as (?&?&Hc), Hcx as (?&?&Hx).
    rewrite Hc, Hx in *. inv Sx. inv Sc. inv Tc.
    rewrite swhen_eq in HU.
    rewrite AC_eq in *.
    cases_eqn HH; try take (Some _ = Some _) and inv it.
    all: pose proof (Con_le_le _ _ _ _ _ _ Cx Cc); try easy.
    all: try rewrite DS_const_eq in HU; rewrite AC_eq in HU.
    all: apply Con_eq_simpl in HU as (?& Hu); subst.
    all: apply DSle_cons_elim in Cx as (? & Hcx &?).
    all: rewrite Hcx in *; rewrite zip_eq in HV; simpl in *.
    all: apply Con_le_simpl in Cc as []; cases_eqn HH.
    all: try rewrite HH2 in *; simpl in *.
    all: do 2 esplit; eauto 10.
  Qed.

  Lemma safe_swhenv :
    forall k tx tn ck xs cs,
      ty_DS (Tenum tx tn) cs
      /\ safe_DS xs /\ cl_DS ck xs
      /\ safe_DS cs /\ cl_DS ck cs ->
      safe_DS (swhenv k xs cs).
  Proof.
    unfold cl_DS, swhenv.
    intros ????.
    generalize (denot_clock ck); clear ck.
    clear; intros cks * (Tx & Sx & Cx & Sc & Cc).
    remember (swhen _ _ _ k _ _) as t eqn:Ht. apply Oeq_refl_eq in Ht.
    revert_all; cofix Cof; intros.
    destruct t as [| b t].
    { constructor. rewrite <- eqEps in Ht. apply Cof with k tx tn cks xs cs; auto. }
    assert (is_cons xs) as Hcx by (eapply proj1, swhen_cons; now rewrite <- Ht).
    assert (is_cons cs) as Hcc by (eapply proj2, swhen_cons; now rewrite <- Ht).
    apply is_cons_elim in Hcx as (vx & xs' & Hx), Hcc as (vc & cs' & Hc).
    rewrite Hx, Hc, AC_eq in *; clear Hx xs Hc cs.
    unfold swhenv in Ht; rewrite swhen_eq in Ht.
    cases_eqn HH; inv Sx; inv Sc; inv Tx; try tauto.
    all: pose proof (Con_le_le _ _ _ _ _ _ Cx Cc); try easy.
    all: apply Con_eq_simpl in Ht as [? Ht]; subst; constructor; auto.
    all: apply rem_le_compat in Cx, Cc; rewrite rem_cons in *.
    all: eapply Cof with k tx tn (rem cks) xs' cs'; auto.
  Qed.

  Lemma Forall_denot_exps :
    forall P ins es envI bs env,
      forall_nprod P (denot_exps G ins es envG envI bs env)
      <-> Forall (fun e => forall_nprod  P (denot_exp G ins e envG envI bs env)) es.
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
  Lemma Forall_ty_exp :
    forall es,
      Forall (fun e => Forall2 ty_DS (typeof e) (list_of_nprod (denot_exp G ins e envG envI bs env))) es ->
      Forall2 ty_DS (typesof es) (list_of_nprod (denot_exps G ins es envG envI bs env)).
  Proof.
    induction 1.
    - simpl; auto.
    - rewrite denot_exps_eq; simpl.
      rewrite list_of_nprod_app.
      apply Forall2_app; auto.
  Qed.

  (* TODO: généraliser... ? *)
  Lemma Forall_cl_exp :
    forall es,
      Forall (fun e => Forall2 cl_DS (clockof e) (list_of_nprod (denot_exp G ins e envG envI bs env))) es ->
      Forall2 cl_DS (clocksof es) (list_of_nprod (denot_exps G ins es envG envI bs env)).
  Proof.
    induction 1.
    - simpl; auto.
    - rewrite denot_exps_eq; simpl.
      rewrite list_of_nprod_app.
      apply Forall2_app; auto.
  Qed.

End SDfuns_safe.

Global Add Parametric Morphism ins : (denot_clock ins)
    with signature @Oeq (DS_prod SI) ==> @Oeq (DS bool) ==> @Oeq (DS_prod SI) ==> @eq clock ==> @Oeq (DS bool)
      as denot_clock_morph.
Proof.
  intros * Eq1 * Eq2 * Eq3 ck.
  induction ck as [|??? []]; simpl; auto.
  now rewrite IHck, Eq1, Eq3.
Qed.

Global Add Parametric Morphism Γ ins : (env_correct Γ ins)
       with signature @Oeq (DS_prod SI) ==> @Oeq (DS bool) ==> @Oeq (DS_prod SI) ==> iff
         as env_correct_morph.
Proof.
  unfold env_correct, ty_DS, cl_DS, DSForall_pres.
  intros * Eq1 * Eq2 * Eq3.
  split; intros Hdec * Hty Hck; destruct (Hdec _ _ _ Hty Hck) as (?&?&?).
  - rewrite <- Eq1, <- Eq3, <- Eq2; auto.
  - rewrite Eq1, Eq3, Eq2; auto.
Qed.

Section Cont_alt.

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

  Fact AC_var_eq :
    forall ins x envI env,
      AC (denot_var ins envI env x) = (AC @_ denot_var_C ins envI x) env.
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
        (ZIP (sample k) @2_ sx) cks
    end.

  Fact denot_clock_eq :
    forall ins envI bs env ck,
      denot_clock ins envI bs env ck = denot_clock_C ins envI bs ck env.
  Proof.
    induction ck; simpl; cases.
    now rewrite IHck, denot_var_eq.
  Qed.

End Cont_alt.



Section SubClock.

  (** CStr.sub_clock avec une notion de préfixe : le flot de gauche
      est plus long que celui de droite

    par ex :
     T T T F T F T T   est sub_clock de
     F T F F T ⊥

     T T T F T F ⊥   n'est pas sub_clock de
     F T F F T F T
   *)
  CoInductive sub_clock : relation (DS bool) :=
  | ScEps : forall x y,
      sub_clock x y -> sub_clock x (Eps y)
  | ScCon : forall a b s t x,
      sub_clock s t ->
      decomp a s x ->
      Bool.le b a ->
      sub_clock x (cons b t).

  Lemma le_sub_clock :
    forall x y,
      x <= y ->
      sub_clock y x.
  Proof.
    cofix Cof; destruct x; intros * Hle.
    - constructor. rewrite <- eqEps in Hle. now apply Cof.
    - apply DSle_uncons in Hle as HH.
      destruct HH as (t & Ht & Hle').
      econstructor; eauto. reflexivity.
  Qed.

  Lemma sub_clock_decomp :
    forall a s x y,
      decomp a s x ->
      sub_clock y x ->
      exists b t, decomp b t y /\ Bool.le a b /\ sub_clock t s.
  Proof.
    clear.
    intros a s x y Hdx.
    destruct Hdx as (k & Hk).
    revert dependent x. induction k; simpl in *; intros * Hk Hsub; subst.
    - inv Hsub; eauto.
    - destruct (IHk (pred x)); eauto.
      destruct x; simpl; auto. now inv Hsub.
  Qed.

  Lemma sub_clock_trans : forall x y z,
      sub_clock x y ->
      sub_clock y z ->
      sub_clock x z.
  Proof.
    clear. cofix Cof; intros * Sub1 Sub2.
    destruct z; inv Sub2.
    - constructor. eauto.
    - eapply sub_clock_decomp in Sub1 as (c & t &?&?&?); eauto.
      apply ScCon with c t; eauto using BoolOrder.le_trans.
  Qed.

  Lemma sub_clock_Oeq_compat :
    forall x y z t,
      x == y ->
      z == t ->
      sub_clock x z ->
      sub_clock y t.
  Proof.
    intros * [Le1 Le2] [Le3 Le4] Hsub.
    apply le_sub_clock in Le1, Le2, Le3, Le4.
    eauto using sub_clock_trans.
  Qed.

  Global Add Parametric Morphism : sub_clock
      with signature (@Oeq (DS bool)) ==> (@Oeq (DS bool)) ==> iff
        as sub_clock_morph.
  Proof.
    intros * Eq1 ?? Eq2.
    split; intro Hsub; eauto 2 using sub_clock_Oeq_compat.
  Qed.

  Lemma sub_clock_refl : forall s, sub_clock s s.
  Proof.
    clear. intro s.
    remember s as t. rewrite Heqt at 1. apply Oeq_refl_eq in Heqt.
    revert_all.
    cofix Cof; intros; destruct t.
    - constructor. apply Cof. now rewrite eqEps.
    - apply symmetry, decomp_eq in Heqt as (?&?& Ht).
      econstructor; eauto using BoolOrder.le_refl.
  Qed.

  Lemma sub_clock_antisym :
    forall x y,
      sub_clock x y ->
      sub_clock y x ->
      x == y.
  Proof.
    intros * Sub1 Sub2.
    eapply DS_bisimulation_allin1
      with (R := fun U V => sub_clock U V /\ sub_clock V U); auto.
    - now intros * [] <- <-.
    - clear.
      intros x y Hc [Sub1 Sub2].
      assert (exists u xs v ys, x == cons u xs /\ y == cons v ys) as HH. {
        destruct Hc as [Hc|Hc]; apply is_cons_elim in Hc as (?&?& Heq);
          rewrite Heq in *; [inv Sub2|inv Sub1].
        all: do 4 esplit; split; eauto 1; apply decomp_eqCon; eauto.
      }
      destruct HH as (?&?&?&?& Eq1 & Eq2).
      rewrite Eq1, Eq2, 2 first_cons, 2 rem_cons in *.
      inv Sub1. inv Sub2.
      apply decompCon_eq in H3, H6; inv H3; inv H6.
      unfold Bool.le in *; cases.
  Qed.

  Lemma sub_clock_le :
    forall bs xs ys,
      xs <= ys ->
      sub_clock bs ys ->
      sub_clock bs xs.
  Proof.
    clear.
    cofix Cof; intros * Le Sub.
    destruct xs.
    - constructor. rewrite <- eqEps in Le. eauto.
    - inv Le.
      apply decomp_eqCon in H1 as Hy.
      rewrite Hy in Sub. inv Sub.
      apply ScCon with a s; auto.
      eapply Cof; eauto.
  Qed.

  Lemma sub_clock_sample :
    forall bs cs xs k,
      sub_clock bs cs ->
      sub_clock bs (ZIP (sample k) xs cs).
  Proof.
    clear. intros * Hsub.
    remember (ZIP _ _ _) as zs eqn:Hz. apply Oeq_refl_eq in Hz.
    revert_all. cofix Cof; intros.
    destruct zs.
    - constructor. rewrite <- eqEps in Hz. eauto.
    - assert (is_cons xs /\ is_cons cs) as [Hcx Hcc].
      now apply symmetry, cons_is_cons, zip_is_cons in Hz.
      apply is_cons_elim in Hcc as (vc & cs' & Hc).
      apply is_cons_elim in Hcx as (vx & xs' & Hx).
      rewrite Hc, Hx, zip_eq in Hz.
      apply Con_eq_simpl in Hz as [? Hz]; subst.
      rewrite Hc in Hsub. inv Hsub.
      econstructor; eauto.
      unfold Bool.le, sample, andb, eqb in *. cases_eqn H.
  Qed.

  Lemma sub_clock_bs :
    forall ins envI bs env ck,
      sub_clock bs (denot_clock ins envI bs env ck).
  Proof.
    induction ck as [| ck Hck x (ty & k)]; simpl.
    - apply sub_clock_refl.
    - apply sub_clock_sample, Hck.
  Qed.

  Lemma sub_clock_orb :
    forall bs xs ys,
      sub_clock bs xs ->
      sub_clock bs ys ->
      sub_clock bs (ZIP orb xs ys).
  Proof.
    clear. intros * Sub1 Sub2.
    remember (ZIP _ _ _) as zs eqn:Hz. apply Oeq_refl_eq in Hz.
    revert_all. cofix Cof; intros.
    destruct zs.
    - constructor. rewrite <- eqEps in Hz.
      apply Cof with xs ys; auto.
    - assert (is_cons xs /\ is_cons ys) as [Hcx Hcy].
      now apply symmetry, cons_is_cons, zip_is_cons in Hz.
      apply is_cons_elim in Hcx as (vx & xs' & Hx).
      apply is_cons_elim in Hcy as (vy & ys' & Hy).
      rewrite Hy, Hx, zip_eq in Hz.
      apply Con_eq_simpl in Hz as [? Hz]; subst.
      rewrite Hx in Sub1. inv Sub1.
      rewrite Hy in Sub2. inv Sub2.
      match goal with
        H1: decomp _ _ _, H2: decomp _ _ _ |- _ =>
          destruct (decomp_decomp _ _ _ _ _ _ H1 H2); subst
      end.
      apply ScCon with a0 s0; auto.
      + apply Cof with xs' ys'; auto.
      + unfold Bool.le, orb in *. cases.
  Qed.

  Lemma orb_sub_clock :
    forall bs xs ys,
      sub_clock bs ys ->
      xs <= bs ->
      ZIP orb xs ys <= bs.
  Proof.
    clear. intros * Sub Le.
    remember (ZIP _ _ _) as zs eqn:Hz. apply Oeq_refl_eq in Hz.
    revert_all. cofix Cof; intros.
    destruct zs.
    - constructor. rewrite <- eqEps in Hz.
      apply Cof with xs ys; auto.
    - assert (is_cons xs /\ is_cons ys) as [Hcx Hcy].
      now apply symmetry, cons_is_cons, zip_is_cons in Hz.
      apply is_cons_elim in Hcx as (vx & xs' & Hx).
      apply is_cons_elim in Hcy as (vy & ys' & Hy).
      rewrite Hy, Hx, zip_eq in Hz.
      apply Con_eq_simpl in Hz as [? Hz]; subst.
      rewrite Hx in Le. inv Le.
      rewrite Hy in Sub. inv Sub.
      match goal with
        H1: decomp _ _ _, H2: decomp _ _ _ |- _ =>
          destruct (decomp_decomp _ _ _ _ _ _ H1 H2); subst
      end.
      apply DSleCon with s.
      + unfold Bool.le, orb in *. cases.
      + apply Cof with xs' ys'; auto.
  Qed.

End SubClock.


Section Node_safe.

  Variables
    (G : global)
    (envG : Dprodi FI).

  Hypothesis
    (WCG : wc_global G).

    (* TODO: prendre note du problème suivant dans le cahier :
      node f (x y : int) return (z : int)
      let
        z = x;
      tel
      z =  1 1 1 1 1 1 1 1 1 1 1 1 1 1 1

      node g (x y : int) return (z : int)
      let
        z = x + 0;
      tel
      z = 1 ⊥

      x   = 1 1 1 1 1 1 1 1 1 1 1 1 1 1
      y   = 0 ⊥
      bss = T ⊥
     *)

  (* Par définition, l'horloge des flots des entrées d'un nœud peut dépasser
     le bss des entrés. C'est pourquoi on quantifie sur une complétion bs de
     bss, qui correspondra en fait à la dénotation de bck (cf. WellInstantiated)
     dans le nœud appelant.
   *)
  Hypothesis Hnode :
    forall (f : ident) (envI : DS_prod SI),
      match find_node f G with
      | Some n =>
          let ins := idents n.(n_in) in
          let Γ := senv_of_inout (n.(n_in) ++ n.(n_out)) in
          forall bs,
            bss ins envI <= bs ->
            env_correct Γ ins envI bs 0 ->
            env_correct Γ ins envI bs (envG f envI)
      | _ => True
      end.

  Lemma basilus_nclockus :
    forall ins envI bs env e,
      let ss := denot_exp G ins e envG envI bs env in
      Forall2 (fun nc s => match snd nc with
                        | Some x => denot_var ins envI env x = s
                        | None => True end)
        (nclockof e) (list_of_nprod ss).
  Proof.
    intros. subst ss.
    (* on détruit les paires, c'est parfois utile *)
    destruct e; repeat match goal with p:(_*_)|- _ => destruct p end.
    all: simpl; simpl_Forall; auto.
    now setoid_rewrite denot_exp_eq.
    all:apply Forall2_forall; split;
      [now intros|now rewrite (@list_of_nprod_length (DS (sampl value)))].
    (* FIXME: sans préciser (DS (sampl value)), le rewrite ci-dessus échoue. *)
    (* Je ne comprends pas pourquoi mais apparemment appliquer le changement
       suivant semble régler le problème d'unification : *)
    (* change (DStr (sampl value)) with (tord (tcpo (DS (sampl value)))). *)
  Qed.

  Corollary nclocksof_sem :
    forall ins envI bs env es,
      let ss := denot_exps G ins es envG envI bs env in
      Forall2 (fun nc s => match snd nc with
                        | Some x => denot_var ins envI env x = s
                        | None => True end)
        (nclocksof es) (list_of_nprod ss).
  Proof.
    induction es; simpl; auto.
    setoid_rewrite denot_exps_eq.
    rewrite list_of_nprod_app.
    apply Forall2_app; auto using basilus_nclockus.
  Qed.


  (* on peut séparer env_correct en trois propositions pour faciliter
     le découpage des preuves *)
  Definition ty_env Γ ins (envI env : DS_prod SI) :=
    (forall x ty, HasType Γ x ty -> ty_DS ty (denot_var ins envI env x)).
  Definition cl_env Γ ins envI bs env :=
    (forall x ck, HasClock Γ x ck -> cl_DS ins envI bs env ck (denot_var ins envI env x)).
  Definition ef_env Γ ins (envI env : DS_prod SI) :=
    (forall x ty, HasType Γ x ty -> safe_DS (denot_var ins envI env x)).

  Lemma env_correct_decompose :
    forall Γ ins envI bs env,
      (ty_env Γ ins envI env
       /\ cl_env Γ ins envI bs env
       /\ ef_env Γ ins envI env)
      <-> env_correct Γ ins envI bs env.
  Proof.
    unfold env_correct, ty_env, cl_env, ef_env. split.
    - intros * (Ty & Cl&  Ef ) * Hty Hcl. repeat split; eauto.
    - intro H. repeat split; intros * HH; inv HH.
      all: edestruct H as (?&?&?); eauto; econstructor; eauto.
  Qed.

  (** ** Traitement des instanciations de nœuds  *)

 (* voici comment utiliser nclocksof_sem *)
  Lemma Wi_match_ss :
    forall ins envI env env',
    forall bck sub,
    forall (n : node) nn (ss : nprod nn) ncks,
      let ckins := List.map (fun '(x, (_, ck, _)) => (x, ck)) n.(n_in) in
      Forall2 (WellInstantiated bck sub) ckins ncks ->
      Forall2 (fun nc s => match snd nc with
                        | Some x => denot_var ins envI env x = s
                        | None => True
                        end) ncks (list_of_nprod ss) ->
      forall x y ck,
        sub x = Some y ->
        In (x, ck) ckins ->
        denot_var (idents (n_in n)) (env_of_np (idents (n_in n)) ss) env' x =
          denot_var ins envI env y.
  Proof.
    unfold idents.
    intros * Wi Ncs * Hsub Hin.
    destruct n.(n_nodup) as (Nd & _).
    rewrite fst_NoDupMembers, map_app in Nd; apply NoDup_app_l in Nd.
    unfold denot_var at 1.
    rewrite (proj2 (mem_ident_spec _ _)).
    2: simpl_In; esplit; split; now eauto.
    eapply Forall2_trans_ex in Ncs; eauto.
    eapply In_nth_error in Hin as (k & Kth).
    eapply nth_error_Forall2 in Ncs as (?&?&[]&?&[Sub Inst]&?); eauto.
    simpl in *; subst. cases; inv Hsub.
    erewrite env_of_np_nth with (k := k), list_of_nprod_nth_error; eauto.
    apply nth_mem_nth; auto.
    apply map_nth_error_inv in Kth as ((?&(?&?)&?)& He & HHH). inv HHH.
    now rewrite nth_error_map, He.
  Qed.

  Lemma denot_clock_inst_ins :
    forall ins envI bs env,
    forall bck sub,
    forall ncks (n:node) nn (ss : nprod nn),
      let ckins := List.map (fun '(x, (_, ck, _)) => (x, ck)) n.(n_in) in
      wc_env ckins ->
      Forall2 (WellInstantiated bck sub) ckins ncks ->
      Forall2 (cl_DS ins envI bs env) (List.map fst ncks) (list_of_nprod ss) ->
      Forall2 (fun nc s => match snd nc with
                        | Some x => denot_var ins envI env x = s
                        | None => True
                        end) ncks (list_of_nprod ss) ->
      forall env' ck x ck',
        In (x, ck) ckins ->
        instck bck sub ck = Some ck' ->
        denot_clock (idents (n_in n)) (env_of_np (List.map fst (n_in n)) ss)
          (denot_clock ins envI bs env bck) env' ck
        = denot_clock ins envI bs env ck'.
  Proof.
    intros * Hwc Hinst Hcl Ncs env'.
    induction ck; intros * Hin Hck.
    - simpl in *. now inv Hck.
    - simpl in *. cases_eqn HH. inv Hck.
      eapply wc_env_var in Hwc; eauto; inv Hwc.
      erewrite IHck, Wi_match_ss; simpl; eauto.
  Qed.

  Lemma cl_env_inst :
    forall ins envI bs env,
    forall bck sub,
    forall ncks (n : node) nn (ss : nprod nn),
      let ckins := List.map (fun '(x, (_, ck, _)) => (x, ck)) n.(n_in) in
      wc_env ckins ->
      Forall2 (WellInstantiated bck sub) ckins ncks ->
      Forall2 (fun nc s => match snd nc with
                        | Some x => denot_var ins envI env x = s
                        | None => True
                        end) ncks (list_of_nprod ss) ->
      Forall2 (cl_DS ins envI bs env) (List.map fst ncks) (list_of_nprod ss) ->
      cl_env (senv_of_inout (n_in n ++ n_out n)) (idents (n_in n)) (env_of_np (idents (n_in n)) ss) (denot_clock ins envI bs env bck) 0.
  Proof.
    clear.
    intros * Hwc Hinst Ncs Hcl x ck Hck.
    unfold idents, denot_var, cl_DS in *.
    (* seul le cas où x est une entrée nous intéresse *)
    cases_eqn Hxin. 2: unfold AC; now rewrite MAP_map, map_bot.
    rewrite mem_ident_spec in Hxin.
    apply HasClock_app_1 in Hck; auto.
    apply HasClock_senv in Hck; auto. clear Hxin.

    apply Forall2_map_1 with (f := fst) in Hcl as HH.
    apply Forall2_trans_ex with (1 := Hinst) in HH.
    apply In_nth_error in Hck as J. destruct J as (k & Kth).
    eapply nth_error_Forall2 with (1 := Kth) in HH.
    destruct HH as (?&?&?&?&[]&?). simpl in *; subst.
    eapply denot_clock_inst_ins in Hck as ->; eauto 1.
    erewrite env_of_np_nth, list_of_nprod_nth_error; eauto.
    destruct n.(n_nodup) as (Nd & _).
    rewrite fst_NoDupMembers, map_app in Nd; apply NoDup_app_l in Nd.
    apply nth_mem_nth; auto.
    rewrite nth_error_map in *.
    apply option_map_inv in Kth as (?&->&?); cases.
  Qed.

  Lemma ef_env_inst :
    forall (n : node) (ss : nprod (length (n_in n))),
      forall_nprod safe_DS ss ->
      ef_env (senv_of_inout (n_in n ++ n_out n)) (idents (n_in n))
        (env_of_np (idents (n_in n)) ss) 0.
  Proof.
    intros * Hs ?? Hty.
    unfold denot_var.
    (* seul le cas où x est une entrée nous intéresse *)
    cases_eqn Hxin. 2: apply DSForall_bot.
    apply mem_ident_nth in Hxin as (k & Hl).
    apply mem_nth_Some in Hl as Hk; eauto.
    unfold idents in Hk.
    rewrite map_length in Hk.
    erewrite env_of_np_nth; eauto.
    apply forall_nprod_k; auto.
  Qed.

  Lemma ty_env_inst :
    forall tys (n : node) nn (ss : nprod nn),
      Forall2 (fun (et : type) '(_, (t, _, _)) => et = t) tys (n_in n) ->
      Forall2 ty_DS tys (list_of_nprod ss) ->
      ty_env (senv_of_inout (n_in n ++ n_out n)) (idents (n_in n))
        (env_of_np (idents (n_in n)) ss) 0.
  Proof.
    intros * Hins Hss ?? Hty.
    destruct n.(n_nodup) as (Nd & _).
    rewrite fst_NoDupMembers, map_app in Nd; apply NoDup_app_l in Nd.
    eapply Forall2_swap_args in Hins.
    eapply Forall2_trans_ex in Hss; eauto.
    unfold denot_var.
    (* seul le cas où x est une entrée nous intéresse *)
    cases_eqn Hxin. 2: apply DSForall_bot.
    apply mem_ident_spec in Hxin as HH.
    apply HasType_app_1, Ty_senv in Hty; auto; clear HH.
    apply In_nth_error in Hty as (k & Kth).
    erewrite env_of_np_nth with (k := k).
    2: {apply nth_mem_nth; auto.
        apply map_nth_error_inv in Kth as ((?&(?&?)&?)& He & HH). inv HH.
        unfold idents. erewrite map_nth_error; now eauto. }
    apply map_nth_error_inv in Kth as ((?&(?&?)&?)&?&HH). inv HH.
    eapply nth_error_Forall2 in Hss as (?&?&?&?&?&?); eauto.
    simpl in *; subst.
    erewrite list_of_nprod_nth_error; eauto.
  Qed.

  Lemma inst_ty_env :
    forall tys (n : node) envI env,
      Forall2 (fun a '(_, (t, _, _)) => a = t) tys (n_out n) ->
      ty_env (senv_of_inout (n_in n ++ n_out n)) (idents (n_in n)) envI env ->
      Forall2 ty_DS tys (list_of_nprod (np_of_env (idents (n_out n)) env)).
  Proof.
    clear.
    intros * Hty Henv.
    unfold ty_env in *.
    apply Forall2_forall2; split.
    { unfold idents. rewrite list_of_nprod_length, map_length.
      eauto using Forall2_length. }
    intros d ? k ty ? Hk ??; subst.
    assert (lk : k < Datatypes.length (idents (n_out n))).
    { unfold idents; rewrite map_length; apply Forall2_length in Hty; lia. }
    rewrite list_of_nprod_nth, (nth_np_of_env xH); auto.
    specialize (Henv (nth k (idents (n_out n)) xH) (nth k tys d)).
    unfold denot_var in Henv.
    cases_eqn Hxin.
    { exfalso. apply mem_ident_spec in Hxin.
      destruct n.(n_nodup) as (Nd &_).
      rewrite fst_NoDupMembers, map_app in Nd.
      eapply NoDup_app_In; eauto. apply nth_In; auto. }
    apply Henv.
    rewrite senv_of_inout_app, HasType_app; right.
    clear - Hty Hk lk.
    (* merci à Basile pour la preuve : *)
    unfold senv_of_inout, idents in *.
    rewrite map_length in lk.
    unshelve eapply Forall2_nth with (n := k) in Hty; auto.
    repeat (constructor; auto using bool_velus_type).
    destruct (nth k (n_out n)) eqn:Hnth; destruct_conjs.
    econstructor.
    solve_In; eauto using nth_In.
    erewrite Hnth, map_nth', Hnth; eauto. simpl; eauto.
  Qed.

  Lemma inst_ef_env :
    forall (n : node) envI env,
      ef_env (senv_of_inout (n_in n ++ n_out n)) (idents (n_in n)) envI env ->
      forall_nprod safe_DS (np_of_env (idents (n_out n)) env).
  Proof.
    intros * He.
    apply forall_np_of_env'.
    intros x Hxin.
    unfold ef_env, idents, denot_var in *.
    assert (exists ty, HasType (senv_of_inout (n_in n ++ n_out n)) x ty) as (ty&Hty).
    { apply In_HasType. unfold idents. rewrite map_app, in_app_iff. auto. }
    destruct n.(n_nodup) as (Nd &_).
    rewrite fst_NoDupMembers, map_app in Nd.
    apply He in Hty.
    cases_eqn HH; exfalso.
    rewrite mem_ident_spec in HH.
    eapply NoDup_app_In; eauto.
  Qed.

  Lemma inst_cl_env :
    (* on a besoin des hypothèses sur les entrées car les sorties
       peuvent en dépendre et on va appeler denot_clock_inst_ins *)
    forall ins envI bs env env',
    forall bck sub,
    forall (a : list ann) (n : node) nn (ss : nprod nn) ncks,
      let ckins := List.map (fun '(x, (_, ck, _)) => (x, ck)) n.(n_in) in
      let ckouts := List.map (fun '(x, (_, ck, _)) => (x, ck)) n.(n_out) in
      wc_env ckins ->
      wc_env (ckins ++ ckouts) ->
      Forall2 (WellInstantiated bck sub) ckouts (List.map (fun '(_, ck) => (ck, None)) a) ->
      Forall2 (WellInstantiated bck sub) ckins ncks ->
      cl_env (senv_of_inout (n_in n ++ n_out n)) (idents (n_in n)) (env_of_np (idents (n_in n)) ss) (denot_clock ins envI bs env bck) env' ->
      Forall2 (cl_DS ins envI bs env) (List.map fst ncks) (list_of_nprod ss) ->
      Forall2 (fun nc s => match snd nc with
                        | Some x => denot_var ins envI env x = s
                        | None => True
                        end) ncks (list_of_nprod ss) ->
      Forall2 (cl_DS ins envI bs env) (List.map snd a) (list_of_nprod (np_of_env (idents (n_out n)) env')).
  Proof.
    clear. unfold cl_env, cl_DS.
    intros * Wci Wcio Hinsto Hinsti Hclo Hcli Ncs.
    apply Forall2_length in Hinsto as Hl; rewrite 2 map_length in Hl.
    (* même résultat que denot_clock_inst_ins mais pour les sorties : *)
    assert
      (forall ck x ck',
          In (x, ck) (List.map (fun '(x, (_, ck, _)) => (x, ck)) (n_out n)) ->
          instck bck sub ck = Some ck' ->
          denot_clock (idents (n_in n)) (env_of_np (idents (n_in n)) ss) (denot_clock ins envI bs env bck) env' ck
          = denot_clock ins envI bs env ck') as Hcks.
    { induction ck; intros * Hin Hck.
      - simpl in *. now inv Hck.
      - simpl in *. cases_eqn HH. inv Hck.
        eapply wc_env_var in Wcio; eauto using in_app_weak'.
        inv Wcio. simpl.
        rewrite in_app_iff in H3. destruct H3 as [|Hino].
        (* input, on a déjà fait : *)
        erewrite denot_clock_inst_ins, Wi_match_ss; eauto.
        (* contradiction car sub i = None *)
        eapply Forall2_in_left in Hinsto as (?& Hi &[Sub _]); eauto.
        eapply in_map_iff in Hi as ((?&?)&?&?).
        subst; simpl in *; congruence.
    }
    unfold idents, denot_var in *.
    apply Forall2_forall2.
    split. { now rewrite list_of_nprod_length, 2 map_length. }
    intros d s k ? ? Hk ??; subst.
    rewrite map_length in Hk.
    rewrite list_of_nprod_nth.
    erewrite nth_np_of_env with (d:=xH). 2: rewrite map_length; lia.
    edestruct (nth k (n_out n)) as (x,((ty,ck),i)) eqn:Kth.
    assert (Hin : In (x, (ty, ck, i)) (n_out n)).
    { rewrite <- Kth. apply nth_In. lia. }
    rewrite <- (Hcks ck x).
    2:{ rewrite in_map_iff. exists (x,(ty,ck,i)). auto. }
    2:{ eapply Forall2_nth with (n := k) in Hinsto as [_ Inst].
        erewrite 2 map_nth', Kth in Inst. erewrite map_nth'.
        cases_eqn HH; simpl in *; rewrite HH; eauto.
        all: rewrite ?map_length; lia. }
    erewrite map_nth', Kth; simpl (fst _). 2: lia.
    specialize (Hclo x ck). cases_eqn Hxin.
    2:{ eapply Hclo, senv_HasClock, in_app_weak', Hin. }
    apply mem_ident_spec in Hxin.
    exfalso. (* on y est presque *)
    eapply not_in_out, in_map_iff; eauto. repeat esplit; now eauto.
    Unshelve.
    all: repeat split; eauto using bool_velus_type; exact xH.
  Qed.

  (** À partir de flots bien formés, construire un environnement
      d'entrées bien formé. *)
  Lemma safe_inst_in :
    forall ins envI bs env,
    forall es (n : node) bck sub nn (ss : nprod nn),
      nn = length (n_in n) ->
      Forall2 (fun (et : type) '(_, (t, _, _)) => et = t) (typesof es) (n_in n) ->
      Forall2 (WellInstantiated bck sub) (List.map (fun '(x, (_, ck, _)) => (x, ck)) (n_in n)) (nclocksof es) ->
      wc_env (List.map (fun '(x, (_, ck, _)) => (x, ck)) (n_in n)) ->
      Forall2 ty_DS (typesof es) (list_of_nprod ss) ->
      Forall2 (cl_DS ins envI bs env) (List.map fst (nclocksof es)) (list_of_nprod ss) ->
      forall_nprod safe_DS ss ->
      Forall2 (fun nc s =>
               match snd nc with
               | Some x => denot_var ins envI env x = s
               | None => True
               end) (nclocksof es) (list_of_nprod ss) ->
      env_correct (senv_of_inout (n_in n ++ n_out n)) (idents (n_in n)) (env_of_np (idents (n_in n)) ss)
        (denot_clock ins envI bs env bck) 0.
  Proof.
    intros * Hn WTi WIi WCi Wt Wc Sf Ncs; subst.
    apply env_correct_decompose. repeat split.
    * eapply ty_env_inst; eauto.
    * eapply cl_env_inst; eauto.
    * apply ef_env_inst; eauto.
  Qed.

  (** ** Traitement de l'horloge de base *)

  Lemma sub_clock_bss :
    forall l bs (env : DS_prod SI),
      l <> [] ->
      (forall x, In x l -> sub_clock bs (AC (env x))) ->
      sub_clock bs (bss l env).
  Proof.
    clear.
    induction l as [| x [| y l]]; intros * Hnil Hsub.
    - congruence.
    - apply Hsub. now constructor.
    - rewrite bss_cons2.
      apply sub_clock_orb.
      + apply Hsub. now constructor.
      + apply IHl. congruence.
        { intros. apply Hsub. simpl in *. tauto. }
  Qed.

  (* ressemble à LClockedSemantics.sc_parent *)
  Lemma bss_sub :
    forall l (env : DS_prod SI) bs,
      (exists x, In x l /\ (AC (env x) <= bs)) ->
      (forall x, In x l -> sub_clock bs (AC (env x))) ->
      bss l env <= bs.
  Proof.
    clear.
    induction l as [| y [| z l]]; intros * (x & Hin & Hx) Hsub.
    - destruct Hin.
    - destruct Hin as [|HH]; subst; auto; inv HH.
    - rewrite bss_cons2.
      destruct Hin as [|Hin]; subst.
      + apply orb_sub_clock; auto.
        apply sub_clock_bss. congruence.
        { intros. apply Hsub. simpl in *. tauto. }
      + rewrite zip_comm; auto using Bool.orb_comm.
        apply orb_sub_clock.
        * apply Hsub. simpl. tauto.
        * apply IHl; eauto.
          { intros. apply Hsub. simpl in *. tauto. }
  Qed.

  Lemma bss_le_bs :
    forall (n : node) env bs,
      let Γ := senv_of_inout (n_in n ++ n_out n) in
      wc_env (List.map (fun '(x, (_, ck, _)) => (x, ck)) (n_in n)) ->
      cl_env Γ (idents (n_in n)) env bs 0 ->
      bss (idents (n_in n)) env <= bs.
  Proof.
    clear.
    intros * WCin Hcl.
    apply bss_sub.
    - pose proof (wc_env_has_Cbase _ WCin) as [i Hin].
      { rewrite map_length. exact (n_ingt0 n). }
      assert (In i (idents (n_in n))) as Hi by (unfold idents; solve_In).
      exists i; split; auto.
      specialize (Hcl i Cbase).
      unfold cl_DS, denot_var in Hcl.
      rewrite (proj2 (mem_ident_spec _ _) Hi) in Hcl.
      simpl_In.
      eapply Hcl, senv_HasClock; eauto using in_app_weak.
    - intros x Hin.
      simpl_In.
      specialize (Hcl x c).
      unfold cl_DS, denot_var in Hcl.
      rewrite (proj2 (mem_ident_spec _ _)) in Hcl.
      2: unfold idents; solve_In.
      eapply sub_clock_le.
      eapply Hcl, senv_HasClock; eauto using in_app_weak.
      apply sub_clock_bs.
  Qed.

  Ltac find_specialize_in H :=
    repeat multimatch goal with
      | [ v : _ |- _ ] => specialize (H v)
      end.

  Lemma safe_exp_ :
    forall Γ ins envI bs env,
    env_correct Γ ins envI bs env ->
    forall (e : exp),
      restr_exp e ->
      wt_exp G Γ e ->
      wc_exp G Γ e ->
      op_correct_exp G ins envG envI bs env e ->
      let ss := denot_exp G ins e envG envI bs env in
      Forall2 ty_DS (typeof e) (list_of_nprod ss)
      /\ Forall2 (cl_DS ins envI bs env) (clockof e) (list_of_nprod ss)
      /\ forall_nprod safe_DS ss.
  Proof.
    intros ????  env Safe.
    induction e using exp_ind2; intros Hr Hwt Hwc Hoc; inv Hr.
    - (* Econst *)
      rewrite denot_exp_eq; simpl; autorewrite with cpodb.
      auto using ty_sconst, cl_sconst, safe_sconst.
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
      generalize (denot_exp G ins e envG envI bs env).
      take (typeof e = _) and rewrite it.
      take (numstreams e = _) and rewrite it.
      simpl; intro s; autorewrite with cpodb.
      intros (Wte & Wce & Efe) Hop.
      apply DSForall_pres_impl in Hop; auto.
      repeat split. all: simpl_Forall; auto.
      + apply ty_sunop; auto.
      + apply cl_sunop; congruence.
      + apply safe_DS_def; eauto using safe_ty_sunop, safe_cl_sunop, safe_op_sunop.
    - (* Efby *)
      apply wt_exp_wl_exp in Hwt as Hwl.
      inv Hwl. inv Hwt. inv Hwc. inv Hoc.
      apply Forall_impl_inside with (P := restr_exp) in H, H0; auto.
      apply Forall_impl_inside with (P := wt_exp _ _) in H, H0; auto.
      apply Forall_impl_inside with (P := wc_exp _ _) in H, H0; auto.
      apply Forall_impl_inside with (P := op_correct_exp _ _ _ _ _ _) in H, H0; auto.
      apply Forall_and_inv in H as [Wt0 H'], H0 as [Wt H0'].
      apply Forall_and_inv in H' as [Wc0 Sf0], H0' as [Wc Sf].
      apply Forall_ty_exp in Wt0, Wt.
      apply Forall_cl_exp in Wc0, Wc.
      apply Forall_denot_exps, forall_nprod_Forall in Sf0, Sf.
      rewrite denot_exp_eq.
      revert Wt0 Wt Wc0 Wc Sf0 Sf.
      generalize (denot_exps G ins e0s envG envI bs env).
      generalize (denot_exps G ins es envG envI bs env).
      rewrite annots_numstreams in *.
      simpl; intros; cases; try congruence.
      unfold eq_rect_r, eq_rect; destruct e, e0; simpl.
      take (typesof es = _) and rewrite it in *.
      take (typesof e0s = _) and rewrite it in *.
      take (Forall2 eq _ _) and apply Forall2_eq in it; rewrite <- it in *.
      take (Forall2 eq _ _) and apply Forall2_eq in it; rewrite <- it in *.
      change (DStr (sampl value)) with (tord (tcpo (DS (sampl value)))). (* FIXME: voir plus haut *)
      repeat split.
      + eapply Forall2_lift2; eauto using ty_fby.
      + eapply Forall2_lift2. apply cl_fby.
        all: apply Forall2_Forall2; auto.
        all: apply Forall2_ignore1'; auto.
        all: now rewrite list_of_nprod_length, map_length.
      + eapply Forall_forall_nprod, Forall2_ignore1''.
        now rewrite list_of_nprod_length, map_length.
        eapply Forall2_lift2. apply safe_fby.
        all: apply Forall2_Forall2; eauto.
        all: apply Forall2_ignore1'; auto.
        all: now rewrite list_of_nprod_length, map_length.
    - (* Ewhen *)
      apply wt_exp_wl_exp in Hwt as Hwl.
      inv Hwl. inv Hwt. inv Hwc. inv Hoc.
      apply Forall_impl_inside with (P := restr_exp) in H; auto.
      apply Forall_impl_inside with (P := wt_exp _ _) in H; auto.
      apply Forall_impl_inside with (P := wc_exp _ _) in H; auto.
      apply Forall_impl_inside with (P := op_correct_exp _ _ _ _ _ _) in H; auto.
      apply Forall_and_inv in H as [Wt H'].
      apply Forall_and_inv in H' as [Wc Sf].
      apply Forall_ty_exp in Wt.
      apply Forall_cl_exp in Wc.
      apply Forall_denot_exps, forall_nprod_Forall in Sf.
      rewrite denot_exp_eq.
      revert Wt Wc Sf.
      generalize (denot_exps G ins es envG envI bs env).
      rewrite annots_numstreams in *.
      simpl; intros; cases; try congruence.
      unfold eq_rect_r, eq_rect; destruct e; simpl.
      eapply Forall2_Forall_eq in Wc; eauto.
      edestruct Safe as (?&?&?); eauto.
      change (DStr (sampl value)) with (tord (tcpo (DS (sampl value)))). (* FIXME: voir plus haut *)
      repeat split.
      + eapply Forall2_llift; eauto using ty_swhenv.
      + eapply Forall2_map_1.
        apply Forall2_ignore1'; rewrite ?list_of_nprod_length; auto.
        eapply Forall_llift with (P := fun s => cl_DS _ _ _ _ _ s /\ safe_DS s).
        { intros ? []. eapply cl_swhenv; eauto. }
        apply Forall_Forall; auto.
      + eapply forall_nprod_llift with (Q := fun s => cl_DS _ _ _ _ ck s /\ safe_DS s).
        { intros ? []. eapply safe_swhenv. eauto. }
        apply forall_nprod_and; auto using Forall_forall_nprod.
    - (* Eapp *)
      apply wt_exp_wl_exp in Hwt as Hwl.
      inv Hwl. inv Hwt. inv Hwc. inv Hoc.
      apply Forall_impl_inside with (P := restr_exp) in H; auto.
      apply Forall_impl_inside with (P := wt_exp _ _) in H; auto.
      apply Forall_impl_inside with (P := wc_exp _ _) in H; auto.
      apply Forall_impl_inside with (P := op_correct_exp _ _ _ _ _ _) in H; auto.
      apply Forall_and_inv in H as [Wt H'].
      apply Forall_and_inv in H' as [Wc Sf].
      apply Forall_ty_exp in Wt.
      apply Forall_cl_exp in Wc.
      apply Forall_denot_exps (* forall_nprod_Forall *) in Sf.
      pose proof (nclocksof_sem ins envI bs env es) as Ncs.
      rewrite annots_numstreams in *.
      rewrite denot_exp_eq.
      revert Wt Wc Sf Ncs.
      generalize (denot_exps G ins es envG envI bs env).
      take (list_sum _ = _) and rewrite it.
      intro ss.
      specialize (Hnode f (env_of_np (idents (n_in n)) ss)).
      take (find_node f G = _) and rewrite it in *.
      repeat take (Some _ = Some _) and inv it.
      eapply wc_find_node in WCG as (? & WCi & WCio &_); eauto.
      simpl; intros; cases; try congruence.
      rewrite clocksof_nclocksof in Wc.
      2: unfold idents in *;
      take (length a = _ ) and rewrite it, map_length in *; congruence.
      unfold eq_rect_r, eq_rect, eq_sym. cases; simpl.
      (* on choisit bien [[bck]] comme majorant de bss *)
      specialize (Hnode (denot_clock ins envI bs env bck)).
      rewrite map_app in WCio.
      apply env_correct_decompose in Hnode as (fTy & fCl & fEf).
      + (* on utilise la conclusion de Hnode *)
        repeat split.
        * eapply inst_ty_env; eauto.
          now rewrite Forall2_map_1.
        * eapply inst_cl_env; eauto.
        * eapply inst_ef_env; eauto.
      + eapply bss_le_bs, cl_env_inst; eauto.
      + eapply safe_inst_in; eauto.
  Qed.

  Corollary safe_exp :
    forall Γ ins envI bs env,
    env_correct Γ ins envI bs env ->
    forall (e : exp),
      restr_exp e ->
      wt_exp G Γ e ->
      wc_exp G Γ e ->
      op_correct_exp G ins envG envI bs env e ->
      let ss := denot_exp G ins e envG envI bs env in
      forall_nprod safe_DS ss.
  Proof.
    intros.
    edestruct safe_exp_ as (?&?&?); eauto.
  Qed.

  Lemma safe_exps_ :
    forall Γ ins envI bs env,
    env_correct Γ ins envI bs env ->
    forall (es : list exp),
      Forall restr_exp es ->
      Forall (wt_exp G Γ) es ->
      Forall (wc_exp G Γ) es ->
      Forall (op_correct_exp G ins envG envI bs env) es ->
      let ss := denot_exps G ins es envG envI bs env in
      Forall2 ty_DS (typesof es) (list_of_nprod ss)
      /\ Forall2 (cl_DS ins envI bs env) (clocksof es) (list_of_nprod ss)
      /\ forall_nprod safe_DS ss.
  Proof.
    intros * Safe.
    induction es as [|e es]; simpl; auto; intros.
    simpl_Forall.
    destruct IHes as (?&?&?); auto.
    eapply safe_exp_ in Safe as (?&?&?); eauto.
    setoid_rewrite denot_exps_eq.
    setoid_rewrite list_of_nprod_app.
    repeat split; auto using Forall2_app, forall_nprod_app.
  Qed.

  Corollary safe_exps :
    forall Γ ins envI bs env,
    env_correct Γ ins envI bs env ->
    forall (es : list exp),
      Forall restr_exp es ->
      Forall (wt_exp G Γ) es ->
      Forall (wc_exp G Γ) es ->
      Forall (op_correct_exp G ins envG envI bs env) es ->
      let ss := denot_exps G ins es envG envI bs env in
      forall_nprod safe_DS ss.
  Proof.
    intros.
    edestruct safe_exps_ as (?&?&?); eauto.
  Qed.


  (** Terrible cas des appels de nœuds aux sorties dépendantes.
      Il ne rentre pas dans le cadre de [safe_exp] car on n'a pas l'hypothèse
      [wc_exp G Γ (Eapp f es er anns)]. De toute façon, le résultat de
      [safe_exp] ne serait pas correct ici.

      Par ex. soit [f] de signature
         f (t :: ⋅) returns (c :: ⋅, y :: ⋅ on c)
      et l'équation
         b :: ⋅, x :: ⋅ on b = f(t);
      Alors par [Hnode] le deuxième flot, correspondant à celui de [y] dans
      l'environnement interne de [f] respecte bien l'horloge [⋅ on c], mais
      pas [⋅ on b] dans l'environnement de l'appelant.

      On va donc montrer la préservation de [cl_DS] mais seulement dans
      l'environnement (env') dans lequel les variables b et x ont été mises
      à jour, soit à la fin d'un tour de [denot_equation].
   *)
  Lemma safe_Eapp_dep :
    forall Γ ins envI bs env,
    forall xs f es er anns n bck sub,
      env_correct Γ ins envI bs env ->
      Forall restr_exp es ->
      Forall (wt_exp G Γ) es ->
      Forall (wc_exp G Γ) es ->
      Forall (op_correct_exp G ins envG envI bs env) es ->
      (* bazar ***************************************************)
      find_node f G = Some n ->
      NoDup (xs ++ ins) ->
      wc_env (List.map (fun '(x, (_, ck, _)) => (x, ck)) (n_in n)) ->
      wc_env (List.map (fun '(x, (_, ck, _)) => (x, ck)) (n_in n ++ n_out n)) ->
      Forall2 (fun (et : type) '(_, (t, _, _)) => et = t) (typesof es) (n_in n) ->
      Forall2 (fun a '(_, (t, _, _)) => fst a = t) anns n.(n_out) ->
      Forall2 (WellInstantiated bck sub) (List.map (fun '(x, (_, ck, _)) => (x, ck)) (n_in n)) (nclocksof es) ->
      Forall3 (fun xck ck2 x2 => WellInstantiated bck sub xck (ck2, Some x2)) (List.map (fun '(x, (_, ck, _)) => (x, ck)) n.(n_out)) (List.map snd anns) xs ->
      (* /bazar **************************************************)
      forall bs', bs' <= bs -> (* on distingue l'horloge de base réelle de celle utilisée dans env_correct *)
      let env' := denot_equation G ins (xs, [Eapp f es er anns]) envG envI bs' env in
      env <= env' -> (* vrai dans notre cas *)
      let ss := denot_exp G ins (Eapp f es er anns) envG envI bs' env in
      Forall2 ty_DS (List.map fst anns) (list_of_nprod ss)
      /\ Forall2 (cl_DS ins envI bs env') (List.map snd anns) (list_of_nprod ss)
      /\ forall_nprod safe_DS ss.
  Proof.
    intros * Hsafe Hr Hwt Hwc Hop Hfind ND Wci Wcio Wtin Wtout WIin WIout ? Hbs ? Hle.
    assert (length anns = length (n_out n)) as Hlout.
    { apply Forall3_length in WIout. now rewrite 2 map_length in WIout. }
    assert (length anns = length (idents (n_out n))) as Hlout'. (* pas une blague *)
    { unfold idents. now rewrite map_length. }
    assert (length xs = length anns) as Hl.
    { apply Forall3_length in WIout. now rewrite 2 map_length in WIout. }
    assert (Forall2 (fun x y => sub x = Some y) (idents (n_out n)) xs) as Hsub.
    { apply Forall3_ignore2, Forall2_map_1 in WIout.
      unfold idents; rewrite Forall2_map_1.
      apply Forall2_impl_In with (2 := WIout).
      intros (?&(?&?)&?) ? ?? (?&?&?); auto. }
    pose proof (nclocksof_sem ins envI bs' env es) as Ncs.
    (* on réduit un peu ss *)
    rewrite denot_exp_eq, Hfind.
    set (ses := denot_exps G ins es envG envI bs' env) in *.
    unfold eq_rect_r, eq_rect, eq_sym.
    simpl; cases; try contradiction.
    (**** début instanciation de Hnode  *)
    apply safe_exps_ with (es := es) in Hsafe as (Tys & Cls & Sfs); auto.
    apply Forall2_ty_DS_le with (xs := ses) in Tys; [|subst ses; auto].
    apply Forall2_cl_DS_le with (xs := ses) in Cls; [|subst ses; auto].
    apply forall_safe_le   with (xs := ses) in Sfs; [|subst ses; auto].
    rewrite clocksof_nclocksof in Cls.
    eapply safe_inst_in in Cls as Hs0; eauto.
    2:{ rewrite <- annots_numstreams, <- length_typesof_annots.
        eauto using Forall2_length. }
    specialize (Hnode f).
    rewrite Hfind in Hnode.
    apply Hnode in Hs0.
    2: eapply bss_le_bs, cl_env_inst; eauto.
    (**** fin instanciation de Hnode  *)
    apply env_correct_decompose in Hs0 as (Ty & Cl & Sf).
    repeat split.
    1: (* ty_DS *)
      eapply inst_ty_env; eauto; now rewrite Forall2_map_1.
    2: (* safe_DS *)
      eapply inst_ef_env; now eauto.
    (* ici on montre que l'horloge du nœud appelé correspond à celle du
       nœud appelant, mais après mise à jour de l'environnement (env') *)
    assert
      (forall ck x ck',
          In (x, ck) (List.map (fun '(x, (_, ck, _)) => (x, ck)) (n_out n)) ->
          instck bck sub ck = Some ck' ->
          denot_clock (idents (n_in n))
            (env_of_np (idents (n_in n)) ses)
            (denot_clock ins envI bs env bck)
            (envG f (env_of_np (idents (n_in n)) ses)) ck
          <= denot_clock ins envI bs env' ck') as Hcks.
    {
      (* TODO: lemme? Simplifier ? *)
      clear - Wcio WIin WIout Hle Ncs Wci Cls ND Hsub Hfind Hl Hlout'.
      induction ck as [|??? []]; intros * Hin Hck.
      - inv Hck.
        simpl (denot_clock _ _ _ _ _).
        rewrite 2 denot_clock_eq; auto.
      - simpl in Hck. cases_eqn HH. inv Hck.
        rewrite map_app in Wcio.
        eapply wc_env_var in Wcio; eauto 2 using in_app_weak'.
        inv Wcio.
        simpl (denot_clock _ _ _ _ _).
        take (In _ (_ ++ _)) and rewrite in_app_iff in it;
          destruct it as [|Hino].
        (* input, on a déjà fait : *)
        erewrite denot_clock_inst_ins, Wi_match_ss; eauto 1.
        rewrite 2 denot_var_eq, 2 denot_clock_eq; auto.
        (* cas intéressant : mise à jour d'une variable *)
        eapply IHck in Hino as Hck; eauto 1.
        assert (denot_var (idents (n_in n)) (env_of_np (idents (n_in n)) ses)
                  (envG f (env_of_np (idents (n_in n)) ses)) i
                <= denot_var ins envI env' i0); auto.
        (* maintenant il faut réduire denot_equation, et c'est long... *)
        assert (In i0 xs) as Hxs.
        { apply Forall3_ignore2 in WIout.
          eapply Forall2_in_left with (2 := Hino) in WIout as (?&?&?&[]).
          simpl in *; congruence. }
        assert (mem_ident i0 ins = false) as Hi0.
        { apply mem_ident_false. eauto using NoDup_app_In. }
        assert (mem_ident i (idents (n_in n)) = false) as Hi.
        { apply mem_ident_false. intro. apply (not_in_out n i); solve_In. }
        destruct (In_nth_error_len (idents (n_out n)) i) as (k & kle & kth).
        { unfold idents. solve_In. }
        apply nth_error_Forall2 with (1 := kth) in Hsub as (?&?& Sub).
        rewrite Sub in HH0; inv HH0.
        subst env'. unfold denot_var.
        rewrite denot_equation_eq; unfold denot_var.
        rewrite denot_exps_eq, denot_exps_nil, denot_exp_eq.
        simpl (env_of_np _ _).
        rewrite Hfind, Hi, Hi0.
        unfold eq_rect_r, eq_rect, eq_sym.
        cases; try contradiction.
        rewrite env_of_np_eq.
        setoid_rewrite nth_mem_nth; eauto 2 using NoDup_app_l.
        rewrite @nprod_app_nth1, (nth_np_of_env xH), (nth_error_nth _ _ _ kth); auto.
    }
    set (envN := envG f _) in *.
    (* TODO: la suite ressemble méchamment à la fin de inst_cl_env *)
    unfold denot_var in *.
    apply Forall2_forall2.
    change (DStr (sampl value)) with (tord (tcpo (DS (sampl value)))). (* FIXME: voir plus haut *)
    split. { now rewrite list_of_nprod_length, map_length in *. }
    intros d s k ? ? Hk ??; subst.
    rewrite map_length in Hk.
    rewrite list_of_nprod_nth; try lia.
    erewrite nth_np_of_env with (d:=xH); try lia.
    edestruct (nth k (n_out n)) as (x,((ty,ck),i)) eqn:Kth.
    assert (Hin : In (x, (ty, ck, i)) (n_out n)).
    { rewrite <- Kth. apply nth_In. lia. }
    unfold cl_DS. eapply Ole_trans, Hcks.
    2:{ rewrite in_map_iff. exists (x,(ty,ck,i)). auto. }
    2:{ eapply Forall3_nth with (n := k) in WIout as [_ Inst].
        erewrite 2 map_nth', Kth in Inst. erewrite map_nth'; eauto.
        all: rewrite ?map_length; lia. }
    unfold idents. erewrite map_nth', Kth; simpl (fst _); try lia.
    eapply Ole_trans, (Cl x ck); eauto 3 using senv_HasClock, in_app_weak'.
    unfold denot_var. cases_eqn Hxin.
    apply mem_ident_spec in Hxin.
    exfalso. (* on y est presque *)
    eapply not_in_out, in_map_iff; eauto. repeat esplit; now eauto.
    Unshelve.
    all: repeat split; eauto using bool_velus_type; exact xH.
  Qed.

  (* TODO: utiliser peut-être ailleurs *)
  Lemma denot_clock_ins :
    forall (ckins : list (ident * (type * clock * ident))) envI bs env1 env2 ck,
      let ins := List.map fst ckins in
      wc_clock (List.map (fun '(x, (_, ck, _)) => (x, ck)) ckins) ck ->
      denot_clock ins envI bs env1 ck = denot_clock ins envI bs env2 ck.
  Proof.
    intros * Wck.
    induction ck as [| ??? []]; simpl; auto.
    inv Wck.
    rewrite IHck; auto.
    unfold denot_var.
    cases_eqn Hxin.
    destruct ((proj1 (mem_ident_false _ _)) Hxin).
    subst ins. solve_In.
  Qed.

  Lemma out_Beq :
    forall (n : node) xs es x ty,
      n.(n_block) = Beq (xs, es) ->
      HasType (senv_of_inout (n_in n ++ n_out n)) x ty ->
      In x xs \/ InMembers x (n_in n).
  Proof.
    intros * Heq Hty.
    apply HasType_IsVar, IsVar_In in Hty.
    rewrite map_fst_senv_of_inout, map_app, in_app_iff in Hty.
    destruct Hty as [Hin | Hout].
    - apply fst_InMembers in Hin; auto.
    - destruct (n_defd n) as (?& Hvd & Hperm).
      rewrite Heq in Hvd. inv Hvd.
      rewrite Hperm; auto.
  Qed.

  (* Ici on distingue bien [bss ...] l'horloge de base réelle calculée
     dans la dénotation du nœud et [bs], celle utilisée par env_correct,
     qui peut être plus longue (cf. l'hypothèse [Hnode]). *)
  Lemma safe_node :
    forall n envI env bs,
      let ins := List.map fst n.(n_in) in
      let Γ := senv_of_inout (n.(n_in) ++ n.(n_out)) in
      bss (idents (n_in n)) envI <= bs ->
      (* dans le cadre d'un point fixe, l'hypothèse suivante tient : *)
      env <= denot_node G n envG envI env ->
      restr_node n ->
      wc_node G n ->
      wt_node G n ->
      op_correct G ins envG envI bs env n ->
      env_correct Γ ins envI bs env ->
      env_correct Γ ins envI bs (denot_node G n envG envI env).
  Proof.
    intros * Hbs Hle Hr (?&?& Wcb) (?&?&?& Wtb) Hop Hsafe.
    rewrite denot_node_eq in *.
    inversion Hr as [xs es Hrs Heq]; simpl.
    intros x ty ck Hty Hck.
    destruct (Hsafe x ty ck Hty Hck) as (?& Clx &?).
    unfold denot_var in *.
    cases_eqn Hxin.
    - (* x est une entrée *)
      rewrite mem_ident_spec in Hxin.
      repeat split; auto.
      subst ins Γ. unfold cl_DS in *.
      apply HasClock_app_1, HasClock_senv in Hck; auto.
      clear Hxin.
      erewrite denot_clock_ins; eauto.
      apply wc_env_var with x; auto; solve_In.
    - (* x est calculé *)
      red in Hop.
      rewrite <- Heq in *. inv Wtb. inv Wcb.
      take (_ /\ _) and destruct it as [Tys Tyxs].
      assert (length xs = list_sum (List.map numstreams es)) as Hl.
      { rewrite <- annots_numstreams, <- length_typesof_annots.
        eauto using Forall2_length. }
      assert (In x xs) as Hxs.
      { eapply out_Beq in Hty as [|Hin]; eauto.
        apply fst_InMembers in Hin.
        subst ins. exfalso. eapply mem_ident_false; eauto. }
      apply mem_ident_spec, mem_ident_nth in Hxs as [k kth].
      rewrite denot_equation_eq.
      unfold denot_var. subst ins. setoid_rewrite Hxin.
      setoid_rewrite env_of_np_eq.
      setoid_rewrite kth.
      simpl (denot_block _ _ _) in Hle.
      (* Il y a deux cas possibles dans wc_equation. Dans les deux cas, on
         montre que les [es] sont bien cadencées *dans env'*, l'environment
         mis à jour. *)
      set (bs' := bss (List.map fst (n_in n)) envI) in *.
      set (env' := denot_equation G _ _ envG envI _ env) in *.
      assert (
          let ss := denot_exps G (List.map fst (n_in n)) es envG envI bs' env in
          Forall2 ty_DS (typesof es) (list_of_nprod ss)
          /\ Forall2 (cl_DS (List.map fst (n_in n)) envI bs env') (clocksof es) (list_of_nprod ss)
          /\ forall_nprod safe_DS ss) as (esTy & esCl & esSf).
      {
        take (wc_equation _ _ _) and inv it.
        - (* cas merdique *)
          inv Hrs. inv Tys. inv Hop.
          take (restr_exp _) and inv it.
          take (op_correct_exp _ _ _ _ _ _ _) and inv it.
          take (wt_exp _ _ _) and inv it.
          take (find_node _ _ = _) and rewrite it in *.
          take (Some _ = Some _) and inv it.
          eapply wc_find_node in WCG as HHH; eauto.
          destruct HHH as (? & WCi & WCio &_).
          assert (NoDup (xs ++ List.map fst (n_in n))) as ND.
          { destruct (n_nodup n) as [ND _].
            apply fst_NoDupMembers in ND.
            pose proof (n_defd n) as (?& Vd & Hper).
            rewrite <- Heq in Vd. inv Vd.
            now rewrite Permutation_app_comm, Hper, <- map_app.
          }
          eapply safe_Eapp_dep with (er := []) in Hsafe as (Ty & Cl & Sf); eauto 3.
          simpl.
          rewrite (denot_exps_1 _ _ (Eapp f es0 [] anns)), 2 app_nil_r.
          rewrite (denot_exps_eq _ _ (Eapp f es0 [] anns) []), denot_exps_nil.
          repeat split; auto.
          apply forall_nprod_app; simpl; auto.
        - (* cas normal *)
          eapply safe_exps_ in Hrs as (Ty & Cl & Sf); eauto.
          repeat split.
          + eapply Forall2_ty_DS_le in Ty; eauto 2.
          + eapply Forall2_cl_DS_le with (xs := denot_exps _ _ _ _ _ bs' env)
              in Cl; eauto 2.
            (* comme env <= env',ça tient bien *)
            clear - Cl Hle; unfold cl_DS in *.
            setoid_rewrite denot_clock_eq.
            setoid_rewrite denot_clock_eq in Cl.
            induction Cl; constructor; eauto 3.
          + eapply forall_safe_le in Sf; eauto 2.
      }
      (* utile aussi : *)
      assert (Forall2 (HasClock Γ) xs (clocksof es)) as Clxs
          by (take (wc_equation _ _ _) and inv it; simpl; now rewrite ?app_nil_r).
      apply mem_nth_error in kth.
      repeat split.
      * (* ty_DS *)
        eapply nth_error_Forall2 in Tyxs as (?&?& Hty'); eauto.
        eapply nth_error_Forall2 in esTy as (?& Hn &?); eauto.
        subst bs'; eapply list_of_nprod_nth_error in Hn as ->.
        eapply HasType_det in Hty' as ->; auto using NoDup_senv.
      * (* cl_DS *)
        eapply nth_error_Forall2 in Clxs as (?&?& Hcl'); eauto.
        eapply nth_error_Forall2 in esCl as (?& Hn &?); eauto.
        subst bs'; eapply list_of_nprod_nth_error in Hn as ->.
        eapply HasClock_det in Hcl' as ->; eauto using NoDup_senv.
      * (* safe_DS *)
        eapply forall_nprod_k with (k := k) in esSf; eauto.
        rewrite <- Hl. apply nth_error_Some. now setoid_rewrite kth.
  Qed.

End Node_safe.


(** * Deuxième partie : montrer que env_correct est préservé *)

Section Admissibility.

  (** Pour l'instant, on montre l'admissibilité de [env_correct] en tant que
      propriété de l'environnement des variables seulement (pas des entrées).
      Ça nécessite de donner les composants de env_correct sous forme de fonctions
      continues de l'environnement : DS_prod SI -C-> DS ...
      TODO: ça va peut-être changer avec l'environnement des entrées ???
   *)

  (* TODO: comment généraliser admissible_and plus joliment que ça? *)
  Lemma admissible_and3 :
  forall T U V (D:cpo) (P Q : T -> U -> V -> D -> Prop),
    admissible (fun d => forall x y z, P x y z d) ->
    admissible (fun d => forall x y z, Q x y z d) ->
    admissible (fun d => forall x y z, P x y z d /\ Q x y z d).
  Proof.
    Local Set Firstorder Depth 10.
    firstorder.
  Qed.

  Lemma env_correct_admissible :
    forall Γ ins envI bs,
      admissible (env_correct Γ ins envI bs).
  Proof.
    intros.
    unfold env_correct.
    apply admissiblePT.
    do 4 setoid_rewrite and_impl.
    repeat apply admissible_and3; apply admissiblePT.
    - unfold ty_DS, DSForall_pres.
      do 4 setoid_rewrite DSForall_forall.
      setoid_rewrite denot_var_eq.
      apply DSForall_admissible3.
    - unfold cl_DS.
      setoid_rewrite AC_var_eq.
      setoid_rewrite denot_clock_eq.
      intros ???????. (* TODO: appliquer le_admissible direct?? *)
      apply le_admissible; eauto 2.
    - unfold safe_DS.
      do 4 setoid_rewrite DSForall_forall.
      setoid_rewrite denot_var_eq.
      apply DSForall_admissible3.
  Qed.

End Admissibility.

Section Rev.

  (** Dans la suite on souhaite utiliser fixp_ind pour établir un résultat
      sur l'environnement env := FIXP (denot_equation ...).
      Or pour appliquer safe_exp on a besoin de op_correct_exp, qui est
      supposé prouvé pour env. [fixp_inv2] permet de transporter cette
      hypothèse à chaque itération du point fixe. Il faut cependant montrer
      qu'elle est admissible "en arrière" :
   *)
Definition admissible_rev (D:cpo)(P:D->Type) :=
  forall f : natO -m> D, P (lub f) -> (forall n, P (f n)).

Lemma fixp_inv2 : forall (D:cpo) (F:D -m> D) (P P' Q : D -> Prop),
    (forall x, P' x -> P x) ->
    admissible P ->
    admissible_rev _ Q ->
    Q (fixp F) ->
    P' 0 ->
    (forall x, P' x -> Q x -> P' (F x)) ->
    P (fixp F).
Proof.
  unfold fixp; intros.
  apply X; intros.
  eapply proj2 with (A := P' (iter (D:=D) F n)).
  induction n; simpl; auto.
  destruct IHn.
  unfold admissible_rev, admissible in *.
  firstorder.
Qed.

(* fixp_ind avec hypothèse inverse et croissance comme dans [fixp_ind_le] *)
Lemma fixp_inv2_le : forall (D:cpo) (F:D -m> D) (P Q : D -> Prop),
    admissible P ->
    admissible_rev _ Q ->
    Q (fixp F) ->
    P 0 ->
    (forall x, P x -> x <= F x -> Q x -> P (F x)) ->
    P (fixp F).
Proof.
  unfold fixp; intros.
  apply X; intros.
  apply proj2 with (A := iter_ F n <= iter_ F (S n)).
  induction n; simpl; auto.
  destruct IHn.
  unfold admissible_rev, admissible in *.
  firstorder.
Qed.

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

(* op_correct est donné par hypothèse sur l'environment final,
   mais on aura besoin de l'avoir à chaque itération *)
Lemma op_correct_exp_le :
  forall G ins envG envI bs env env',
    env <= env' ->
    forall e,
      op_correct_exp G ins envG envI bs env' e ->
      op_correct_exp G ins envG envI bs env e.
Proof.
  intros * Le.
  induction e using exp_ind2; intros Hop; inv Hop;
    constructor; eauto using Forall_impl_inside.
  - (* unop *)
    intros ty Hty.
    specialize (H3 ty Hty).
    rewrite forall_nprod_k_iff in *.
    intros k d Hk.
    eapply DSForall_le, H3; eauto.
Qed.

Lemma op_correct_le :
  forall G ins envG envI bs env env' n,
    env <= env' ->
    op_correct G ins envG envI bs env' n ->
    op_correct G ins envG envI bs env n.
Proof.
  unfold op_correct.
  intros * ?; cases.
  apply Forall_impl.
  eauto using op_correct_exp_le.
Qed.

(* TODO: useless? *)
Lemma oc_exp_admissible_rev :
  forall G ins envG envI bs e,
    admissible_rev _ (fun env => op_correct_exp G ins envG envI bs env e).
Proof.
  intros ???????.
  eauto using op_correct_exp_le.
Qed.

(* TODO: useless? *)
Lemma oc_exps_admissible_rev :
  forall G ins envG envI bs es,
    admissible_rev _ (fun env => Forall (op_correct_exp G ins envG envI bs env) es).
Proof.
  intros ??????? Hf.
  induction es; intros; auto.
  inv Hf.
  constructor; eauto using op_correct_exp_le.
Qed.

Lemma oc_admissible_rev :
  forall G ins envG envI bs n,
    admissible_rev _ (fun env => op_correct G ins envG envI bs env n).
Proof.
  intros ??????? Hoc.
  eauto using op_correct_le.
Qed.

End Rev.

(* Notes sur op_correct (avec Tim) :
   TODO: comment gérer les hypothèses sur envI ??
   avec un prédicat en paramètre ?
   seulement sur le nœud main ?
 *)
(* TODO: c'est sans doute beaucoup trop fort, c'est une obligation
   impossible à prouver *)
Definition op_correct_glob (G : global) : Prop :=
  let envG := denot_global G in
  Forall (fun n =>
            (* hypothèses de typage/cadencement aussi ? *)
            let ins := List.map fst n.(n_in) in
            let Γ := senv_of_inout (n.(n_in) ++ n.(n_out)) in
            forall envI bs,
              env_correct Γ ins envI bs 0 ->
              op_correct G ins envG envI bs (envG (n_name n) envI) n)
    (nodes G).


Theorem safe_prog :
  forall (G : global),
    restr_global G ->
    wt_global G ->
    wc_global G ->
    op_correct_glob G ->
    forall f n envI,
      find_node f G = Some n ->
      let ins := List.map fst n.(n_in) in
      let Γ := senv_of_inout (n.(n_in) ++ n.(n_out)) in
      forall bs, bss ins envI <= bs ->
      env_correct Γ ins envI bs 0 ->
      env_correct Γ ins envI bs (denot_global G f envI).
Proof.
  intros * Rg Wtg Wcg Ocg * Hfind ??? Hle Hins.
  unfold op_correct_glob in Ocg.
  assert (Ordered_nodes G) as Hord.
  now apply wl_global_Ordered_nodes, wt_global_wl_global.
  remember (denot_global G) as envG eqn:HG.
  assert (forall f nd envI,
             find_node f G = Some nd ->
             envG f envI == FIXP _ (denot_node G nd envG envI)) as HenvG.
  { intros * Hf; subst.
    unfold denot_global.
    now rewrite <- PROJ_simpl, FIXP_eq, PROJ_simpl, denot_global_eq, Hf at 1. }
  clear HG. (* maintenant HenvG contient tout ce qu'on doit savoir sur envG *)
  revert dependent n. revert f envI. revert bs.
  destruct G as [tys exts nds].
  induction nds as [|a nds]; intros. inv Hfind.
  destruct (ident_eq_dec (n_name a) f); subst.
  - (* cas qui nous intéresse *)
    rewrite find_node_now in Hfind; inv Hfind; auto.
    inversion_clear Ocg as [|?? Hoc Hocs].
    specialize (Hoc envI bs Hins). revert Hoc. fold ins.
    rewrite HenvG; auto using find_node_now.
    rewrite <- denot_node_cons;
      eauto using find_node_not_Is_node_in, find_node_now.
    rewrite FIXP_fixp.
    intro Hoc.
    apply op_correct_cons in Hoc; eauto using find_node_not_Is_node_in, find_node_now.
    apply fixp_inv2_le with
      (Q := fun env =>
              op_correct {| types := tys; externs := exts; nodes := nds |} ins envG envI bs env n
    ); auto using env_correct_admissible, oc_admissible_rev.
    intros env Hsafe Hl Hoc2.
    apply Ordered_nodes_cons in Hord as Hord'.
    apply wt_global_cons in Wtg as Wtg'.
    destruct Wtg as [? Wtp] eqn:HH; clear HH. (* trouver un autre moyen de garder Wtg *)
    inv Wcg. inv Wtp. inv Rg.
    apply safe_node; auto; try tauto.
    (* reste l'hypothèse de récurrence sur les nœuds *)
    clear dependent envI. clear bs env.
    intros f2 envI2.
    cases_eqn Hfind; intros ?? bs2 Hbs2 Hins2.
    apply IHnds; auto.
    + (* montrons que op_correct tient toujours *)
      clear - Hocs Hord.
      eapply Forall_impl_In; eauto.
      intros * Hin HH * Hins.
      eapply op_correct_cons in HH; eauto using Ordered_nodes_nin.
    + (* et que HenvG aussi *)
      intros f' ndf' envI' Hfind'.
      eapply find_node_uncons with (nd := n) in Hfind' as ?; auto.
      rewrite HenvG, <- denot_node_cons; eauto using find_node_later_not_Is_node_in.
  - rewrite find_node_other in Hfind; auto.
    apply IHnds; auto.
    + now inv Rg.
    + eauto using wt_global_cons.
    + eauto using wc_global_cons.
    + clear - Ocg Hord. inv Ocg.
      eapply Forall_impl_In; eauto.
      intros * Hin HH * Hins.
      eapply op_correct_cons in HH; eauto using Ordered_nodes_nin.
    + eauto using Ordered_nodes_cons.
    + intros f' ndf' envI' Hfind'.
      eapply find_node_uncons with (nd := a) in Hfind' as ?; auto.
      rewrite HenvG, <- denot_node_cons; eauto using find_node_later_not_Is_node_in.
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
       (Lord  : LORDERED     Ids Op OpAux Cks Senv Syn)
       (Den   : LDENOT     Ids Op OpAux Cks Senv Syn Lord)
<: LDENOTSAFE Ids Op OpAux Cks Senv Syn Typ Cl Lord Den.
  Include LDENOTSAFE Ids Op OpAux Cks Senv Syn Typ Cl Lord Den.
End LdenotsafeFun.
