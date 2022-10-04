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


(* TODO: move to Vélus *)
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

(* TODO: move to Vélus *)
Lemma Forall2_Forall_eq :
  forall {A B} (P : A -> B -> Prop) a l1 l2,
    Forall (eq a) l1 ->
    Forall2 P l1 l2 ->
    Forall (P a) l2.
Proof.
  induction 2; auto.
  inv H.
  constructor; auto.
Qed.

(* TODO: move to Vélus *)
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

(* TODO: move to Vélus *)
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

(* TODO: move to Vélus *)
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

(* TODO: move to Vélus, rename ? *)
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

(* TODO: move to Vélus? *)
Lemma IsVar_In :
  forall Γ x,
    IsVar Γ x ->
    In x (List.map fst Γ).
Proof.
  intros * Hv.
  inv Hv.
  now apply fst_InMembers.
Qed.


(** ** TODO: description *)
Section Op_correct.
Variables
  (G : global)
  (ins : list ident)
  (envG : Dprodi FI)
  (envI : DS_prod SI)
  (bs : DS bool)
  (env : DS_prod SI).

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


(** ** Safety properties of synchronous streams *)
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


Section exp_safe.

  Variable Γ : static_env.
  Variables
    (G : global)
    (ins : list ident)
    (envG : Dprodi FI)
    (envI : DS_prod SI)
    (bs : DS bool)
    (env : DS_prod SI).

  (** abstract_clock *)
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

  (* TODO: renommer en ty_DS, cl_DS ?? *)

  (** A stream of values of type ty *)
  Definition ty_DS (ty : type) (s : DS (sampl value)) :=
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
  Definition cl_DS (ck : clock) (s : DS (sampl value)) :=
    AC s <= denot_clock ck.

  (** Global hypothesis on the environment *)
  Definition safe_env :=
    forall x ty ck,
      HasType Γ x ty ->
      HasClock Γ x ck ->
      let s := denot_var ins envI env x in
      ty_DS ty s
      /\ cl_DS ck s
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
    rewrite AC_cons in *.
    cases_eqn HH; try take (Some _ = Some _) and inv it.
    all: pose proof (Con_le_le _ _ _ _ _ _ Cx Cc); try easy.
    all: try rewrite DS_const_eq in HU; rewrite AC_cons in HU.
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
    rewrite Hx, Hc, AC_cons in *; clear Hx xs Hc cs.
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

(* TODO: renommer la section *)
End exp_safe.

Section ÀDÉPLACER.

  (** dans CommonList ? *)

  Lemma in_app_weak' :
    forall A (x : A) l l',
      In x l' -> In x (l ++ l').
  Proof.
    intros. apply in_app; auto.
  Qed.

  Lemma nth_In' :
    forall A n (l:list A) (x d : A),
      n < length l ->
      nth n l d = x ->
      In x l.
  Proof.
    induction n; destruct l; simpl; intros * Hn Hl; try now inv Hn.
    - intro; subst; auto.
    - eauto with arith.
  Qed.

  (* TODO: mutualiser SDtoRel *)
  Lemma NoDup_senv :
    forall (nd : node),
      NoDupMembers (senv_of_inout (n_in nd ++ n_out nd)).
  Proof.
    intros.
    (* preuve piquée dans LClockCorrectness *)
    rewrite fst_NoDupMembers, map_fst_senv_of_inout, <-fst_NoDupMembers.
    apply n_nodup.
  Qed.

  (** dans StaticEnv ? *)

  Lemma senv_of_inout_app :
    forall l1 l2,
      senv_of_inout (l1 ++ l2) = senv_of_inout l1 ++ senv_of_inout l2.
  Proof.
    unfold senv_of_inout.
    apply map_app.
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

  Lemma Cl_senv :
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

  Lemma senv_HasType :
    forall l x ty ck i,
      In (x,(ty,ck,i)) l ->
      HasType (senv_of_inout l) x ty.
  Proof.
    intros * Hin.
    unfold senv_of_inout.
    econstructor; eauto.
    apply in_map_iff.
    exists (x,(ty,ck,i)); auto. auto.
  Qed.

  Lemma senv_HasClock :
    forall l x ty ck i,
      In (x,(ty,ck,i)) l ->
      HasClock (senv_of_inout l) x ck.
  Proof.
    intros * Hin.
    unfold senv_of_inout.
    econstructor; eauto.
    apply in_map_iff.
    exists (x,(ty,ck,i)); auto. auto.
  Qed.

  Lemma In_HasType :
    forall x l, In x (idents l) ->
           exists ty, HasType (senv_of_inout l) x ty.
  Proof.
    unfold idents, senv_of_inout.
    intros * Hin.
    apply in_map_iff in Hin as ((?&(ty,?)&?)&?&?); simpl in *; subst.
    exists ty.
    econstructor.
    rewrite in_map_iff.
    esplit; split; now eauto.
    reflexivity.
  Qed.

  (** dans LSyntax ? *)
  Lemma not_in_out :
    forall (n : node) x,
      In x (List.map fst (n_in n)) ->
      In x (List.map fst (n_out n)) ->
      False.
  Proof.
    intros * Hin Hout.
    pose proof (node_NoDup n) as ND.
    rewrite map_app in ND.
    eapply NoDup_app_In; eauto.
  Qed.

  (** dans denot ? *)

  Lemma env_of_ss_nth :
    forall l n (np : nprod n) k x,
      mem_nth l x = Some k ->
      env_of_ss l np x = get_nth k np.
  Proof.
    unfold env_of_ss.
    intros.
    setoid_rewrite Dprodi_DISTR_simpl.
    cases. now inv H. congruence.
  Qed.

  Lemma nth_mem_nth :
    forall l x k,
      NoDup l ->
      nth_error l k = Some x ->
      mem_nth l x = Some k.
  Proof.
    intros * ND. revert k x.
    induction ND; simpl; intros * Hn.
    - destruct k; simpl in *; congruence.
    - cases; subst.
      + destruct k; simpl in *; auto.
        now apply nth_error_In in Hn.
      + destruct k; simpl in *. congruence.
        erewrite IHND; now auto.
  Qed.

  Lemma list_of_nprod_nth_error :
    forall n (np : nprod n) k x,
      nth_error (list_of_nprod np) k = Some x ->
      get_nth k np = x.
  Proof.
    intros * Hn.
    apply nth_error_nth with (d := 0) in Hn as Hnt.
    rewrite list_of_nprod_nth in Hnt; auto.
    erewrite <- (list_of_nprod_length np), <- nth_error_Some, Hn.
    congruence.
  Qed.

  Lemma mem_ident_nth :
    forall l x,
      mem_ident x l = true ->
      exists k, mem_nth l x = Some k.
  Proof.
    intros * Hm.
    induction l; simpl in *; try congruence.
    cases; subst.
    exists O; auto with arith.
    apply Bool.orb_prop in Hm as [Hm|Hm].
    apply ident_eqb_eq in Hm; congruence.
    destruct IHl as [? ->]; simpl; eauto with arith.
  Qed.

  Lemma nth_ss_of_env :
    forall d l env k,
      k < length l ->
      get_nth k (ss_of_env l env) = env (nth k l d).
  Proof.
    induction l as [|? []]; intros * Hl.
    - inv Hl.
    - destruct k; auto. simpl in *; lia.
    - destruct k; simpl; auto.
      setoid_rewrite IHl; now auto with arith.
  Qed.

  (* TODO: move, remplacer celui de InftyProof par lui *)
  Lemma forall_ss_of_env :
    forall (P : DS (sampl value) -> Prop) l env,
      (forall x, In x l -> P (env x)) ->
      forall_nprod P (ss_of_env l env).
  Proof.
    induction l as [|? []]; intros * Hp; eauto.
    - now simpl.
    - apply Hp; now constructor.
    - constructor.
      + apply Hp. now constructor.
      + apply IHl. clear - Hp. firstorder.
  Qed.

End ÀDÉPLACER.


(* TODO: renommer la section *)
Section Exp_safe.

  (* TODO: gérer différemment les variables de safe_env? *)
  Variables
    (* (Γ : static_env) *)
    (G : global)
    (* (ins : list ident) *)
    (envG : Dprodi FI)
    (* (envI : DS_prod SI) *)
    (* (bs : DS bool) *)
    (* (env : DS_prod SI) *)
  .

  Hypothesis WCG : wc_global G. (* TODO: vraiment ici? *)

  Hypothesis Hnode :
    forall (f : ident) (envI : DS_prod SI) (bs : DS bool) (* TODO: bss ?? *),
      match find_node f G with
      | Some n =>
          let ins := idents n.(n_in) in
          let Γ := senv_of_inout (n.(n_in) ++ n.(n_out)) in
          safe_env Γ ins envI bs 0 ->
          safe_env Γ ins envI bs (envG f envI)
      | _ => True
      end.

  Ltac find_specialize_in H :=
    repeat multimatch goal with
      | [ v : _ |- _ ] => specialize (H v)
      end.

  Lemma basilus_nclockus :
    forall ins envG envI bs env e,
      let ss := denot_exp G ins e envG envI bs env in
      Forall2 (fun nc s => match snd nc with
                        | Some x => denot_var ins envI env x = s
                        | None => True end)
        (nclockof e) (list_of_nprod ss).
  Proof.
    intros. subst ss.
    destruct e; simpl; simpl_Forall; auto.
    now setoid_rewrite denot_exp_eq.
    all:apply Forall2_forall; split; [now intros|now rewrite list_of_nprod_length].
  Qed.

  Corollary nclocksof_sem :
    forall ins envG envI bs env es,
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
        denot_var (idents (n_in n)) (env_of_ss (idents (n_in n)) ss) env' x =
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
    erewrite env_of_ss_nth with (k := k), list_of_nprod_nth_error; eauto.
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
        instck bck sub ck = Some ck' ->
        In (x, ck) ckins ->
        denot_clock (idents (n_in n)) (env_of_ss (List.map fst (n_in n)) ss)
          (denot_clock ins envI bs env bck) env' ck
        = denot_clock ins envI bs env ck'.
  Proof.
    intros * Hwc Hinst Hcl Ncs env'.
    induction ck; intros * Hck Hin.
    - simpl in *. now inv Hck.
    - simpl in *. cases_eqn HH. inv Hck.
      eapply wc_env_var in Hwc; eauto; inv Hwc.
      erewrite IHck, Wi_match_ss; simpl; eauto.
  Qed.


  (* on peut séparer safe_env en trois propositions pour faciliter
     le découpage des preuves *)
  Definition ty_env Γ ins (envI env : DS_prod SI) :=
    (forall x ty, HasType Γ x ty -> ty_DS ty (denot_var ins envI env x)).
  Definition cl_env Γ ins envI bs env :=
    (forall x ck, HasClock Γ x ck -> cl_DS ins envI bs env ck (denot_var ins envI env x)).
  Definition ef_env Γ ins (envI env : DS_prod SI) :=
    (forall x ty, HasType Γ x ty -> safe_DS (denot_var ins envI env x)).

  Lemma safe_env_decompose :
    forall Γ ins envI bs env,
      (ty_env Γ ins envI env
       /\ cl_env Γ ins envI bs env
       /\ ef_env Γ ins envI env)
      <-> safe_env Γ ins envI bs env.
  Proof.
    unfold safe_env, ty_env, cl_env, ef_env. split.
    - intros * (Ty & Cl&  Ef ) * Hty Hcl. repeat split; eauto.
    - intro H. repeat split; intros * HH; inv HH.
      all: edestruct H as (?&?&?); eauto; econstructor; eauto.
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
      cl_env (senv_of_inout (n_in n ++ n_out n)) (idents (n_in n)) (env_of_ss (idents (n_in n)) ss) (denot_clock ins envI bs env bck) 0.
  Proof.
    clear.
    intros * Hwc Hinst Ncs Hcl x ck Hck.
    unfold idents, denot_var, cl_DS in *.
    (* seul le cas où x est une entrée nous intéresse *)
    cases_eqn Hxin. 2: unfold AC; now rewrite MAP_map, map_bot.
    rewrite mem_ident_spec in Hxin.
    apply HasClock_app_1 in Hck; auto.
    apply Cl_senv in Hck; auto. clear Hxin.

    apply Forall2_map_1 with (f := fst) in Hcl as HH.
    apply Forall2_trans_ex with (1 := Hinst) in HH.
    apply In_nth_error in Hck as J. destruct J as (k & Kth).
    eapply nth_error_Forall2 with (1 := Kth) in HH.
    destruct HH as (?&?&?&?&[]&?). simpl in *; subst.
    eapply denot_clock_inst_ins in Hck as ->; eauto 1.
    erewrite env_of_ss_nth, list_of_nprod_nth_error; eauto.
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
        (env_of_ss (idents (n_in n)) ss) 0.
  Proof.
    intros * Hs ?? Hty.
    unfold denot_var.
    (* seul le cas où x est une entrée nous intéresse *)
    cases_eqn Hxin. 2: apply DSForall_bot.
    apply mem_ident_nth in Hxin as (k & Hl).
    apply mem_nth_Some in Hl as Hk; eauto.
    unfold idents in Hk.
    rewrite map_length in Hk.
    erewrite env_of_ss_nth; eauto.
    apply forall_nprod_k'; auto.
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

  Lemma ty_env_inst :
    forall tys (n : node) nn (ss : nprod nn),
      Forall2 (fun (et : type) '(_, (t, _, _)) => et = t) tys (n_in n) ->
      Forall2 ty_DS tys (list_of_nprod ss) ->
      ty_env (senv_of_inout (n_in n ++ n_out n)) (idents (n_in n))
        (env_of_ss (idents (n_in n)) ss) 0.
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
    erewrite env_of_ss_nth with (k := k).
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
      Forall2 ty_DS tys (list_of_nprod (ss_of_env (idents (n_out n)) env)).
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
    rewrite list_of_nprod_nth, (nth_ss_of_env xH); auto.
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
      forall_nprod safe_DS (ss_of_env (idents (n_out n)) env).
  Proof.
    intros * He.
    apply forall_ss_of_env.
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
      cl_env (senv_of_inout (n_in n ++ n_out n)) (idents (n_in n)) (env_of_ss (idents (n_in n)) ss) (denot_clock ins envI bs env bck) env' ->
      Forall2 (cl_DS ins envI bs env) (List.map fst ncks) (list_of_nprod ss) ->
      Forall2 (fun nc s => match snd nc with
                        | Some x => denot_var ins envI env x = s
                        | None => True
                        end) ncks (list_of_nprod ss) ->
      Forall2 (cl_DS ins envI bs env) (List.map snd a) (list_of_nprod (ss_of_env (idents (n_out n)) env')).
  Proof.
    clear. unfold cl_env, cl_DS.
    intros * Wci Wcio Hinsto Hinsti Hclo Hcli Ncs.
    apply Forall2_length in Hinsto as Hl; rewrite 2 map_length in Hl.
    (* même résultat que denot_clock_inst_ins mais pour les sorties : *)
    assert
      (forall ck x ck',
          instck bck sub ck = Some ck' ->
          In (x, ck) (List.map (fun '(x, (_, ck, _)) => (x, ck)) (n_out n)) ->
          denot_clock (idents (n_in n)) (env_of_ss (idents (n_in n)) ss) (denot_clock ins envI bs env0 bck) env' ck
          = denot_clock ins envI bs env0 ck') as Hcks.
    { induction ck; intros * Hck Hin.
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
    rewrite list_of_nprod_nth. 2: rewrite map_length; lia.
    erewrite nth_ss_of_env with (d:=xH). 2: rewrite map_length; lia.
    edestruct (nth k (n_out n)) as (x,((ty,ck),i)) eqn:Kth.
    apply nth_In' in Kth as Hin. 2: lia.
    rewrite <- (Hcks ck x).
    2:{ eapply Forall2_nth with (n := k) in Hinsto as [_ Inst].
        erewrite 2 map_nth', Kth in Inst. erewrite map_nth'.
        cases_eqn HH; simpl in *; rewrite HH; eauto.
        all: rewrite ?map_length; lia. }
    2:{ rewrite in_map_iff. exists (x,(ty,ck,i)). auto. }
    erewrite map_nth', Kth; simpl (fst _). 2: lia.
    specialize (Hclo x ck). cases_eqn Hxin.
    2:{ eapply Hclo, senv_HasClock, in_app_weak', Hin. }
    apply mem_ident_spec in Hxin.
    apply nth_In', in_map with (f := fst) in Kth. 2: lia.
    exfalso. (* on y est presque *)
    eapply not_in_out; eauto.
    Unshelve.
    all: repeat split; eauto using bool_velus_type; exact xH.
  Qed.

  Lemma safe_exp_ :
    forall Γ ins envI bs env,
    safe_env Γ ins envI bs env ->
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
      pose proof (nclocksof_sem ins envG envI bs env es) as Ncs.
      rewrite denot_exp_eq.
      revert Wt Wc Sf Ncs.
      generalize (denot_exps G ins es envG envI bs env); intro ss.
      specialize (Hnode f (env_of_ss (idents (n_in n)) ss)).
      rewrite annots_numstreams in *.
      take (find_node f G = _) and rewrite it in *.
      repeat take (Some _ = Some _) and inv it.
      eapply wc_find_node in WCG as (? & WCi & WCio &_); eauto.
      simpl; intros; cases; try congruence.
      2: unfold idents in *;
         take (length a = _ ) and rewrite it, map_length in *; congruence.
      unfold eq_rect_r, eq_rect, eq_sym. cases; simpl.
      eapply safe_env_decompose in Hnode as (fTy & fCl & fEf).
      2:{ (* instanciation de Hnode *)
        apply safe_env_decompose. repeat split.
        + eapply ty_env_inst; eauto.
        + rewrite clocksof_nclocksof in *.
          eapply cl_env_inst; eauto.
        + clear - Sf H11.
          revert dependent ss. rewrite H11.
          apply ef_env_inst; eauto. }
      repeat split.
      + eapply inst_ty_env; eauto.
        now rewrite Forall2_map_1.
      + rewrite map_app, clocksof_nclocksof in *.
        eapply inst_cl_env; eauto.
      + eapply inst_ef_env; eauto.
  Qed.

  Corollary safe_exp :
    forall Γ ins envI bs env,
    safe_env Γ ins envI bs env ->
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
    safe_env Γ ins envI bs env ->
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
    safe_env Γ ins envI bs env ->
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

End Exp_safe.


(** * Deuxième partie : montrer que safe_env est préservé *)

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

  (* TODO: move? *)
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
    Local Set Firstorder Depth 10.
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
    intros k Hk.
    eapply DSForall_le, H3; eauto.
Qed.

Lemma oc_exp_admissible_rev :
  forall G ins envG envI bs e,
    admissible_rev _ (fun env => op_correct_exp G ins envG envI bs env e).
Proof.
  intros ???????.
  eauto using op_correct_exp_le.
Qed.

Lemma oc_exps_admissible_rev :
  forall G ins envG envI bs es,
    admissible_rev _ (fun env => Forall (op_correct_exp G ins envG envI bs env) es).
Proof.
  intros ??????? Hf.
  induction es; intros; auto.
  inv Hf.
  constructor; eauto using op_correct_exp_le.
Qed.

End Rev.


Lemma HasClock_det :
  forall Γ x ck1 ck2,
    NoDupMembers Γ ->
    HasClock Γ x ck1 ->
    HasClock Γ x ck2 ->
    ck1 = ck2.
Proof.
  intros * ND C1 C2; inv C1; inv C2.
  eapply NoDupMembers_det with (t := e) in ND; eauto.
  now subst.
Qed.

Lemma HasType_det :
  forall Γ x ty1 ty2,
    NoDupMembers Γ ->
    HasType Γ x ty1 ->
    HasType Γ x ty2 ->
    ty1 = ty2.
Proof.
  intros * ND C1 C2; inv C1; inv C2.
  eapply NoDupMembers_det with (t := e) in ND; eauto.
  now subst.
Qed.

(* pour ne pas considérer le cas des variables anonymes,
   on remplace wc_equation par les prémisses de wc_Eq *)
Theorem safe_equ :
  forall G Γ ins envG envI bs xs es,
    Forall restr_exp es ->
    NoDupMembers Γ ->
    Permutation (List.map fst Γ) (ins ++ xs) ->
    (* wc_equation G Γ (xs,es) -> *)
    Forall (wc_exp G Γ) es ->
    Forall2 (HasClock Γ) xs (clocksof es) ->
    wt_equation G Γ (xs,es) ->
    safe_env Γ ins envI bs 0 ->
    let env := FIXP (DS_prod SI) (denot_equation G ins (xs,es) envG envI bs) in
    Forall (op_correct_exp G ins envG envI bs env) es ->
    safe_env Γ ins envI bs env.
Proof.
  (* FIXME *)
  intros ?????? xs es Hr Nd Hperm Hwc1 Hwc2 Hwt S0 env Hop; subst env.
  rewrite FIXP_fixp.
  (* on renforce un peu l'induction car on a besoin de la croissance de
     l'environnement à chaque coup de denot_equation *)
  (* TODO: il y a peut-être plus joli à faire *)
  apply fixp_inv2 with
    (Q := fun env =>
             Forall (op_correct_exp G ins envG envI bs env) es)
    (P' := fun env =>
             env <= denot_equation G ins (xs,es) envG envI bs env
             /\ safe_env Γ ins envI bs env);
    try tauto; auto using safe_env_admissible, oc_exps_admissible_rev.
  clear Hop.
  intros env (Le & Safe) Hop.
  split; eauto using fmon_le_compat; auto.
  inv Hwt.
  assert (length xs = list_sum (List.map numstreams es))
    by (rewrite <- annots_numstreams, <- length_typesof_annots;
        eauto using Forall2_length).
  eapply safe_exps_ in Safe as Ss; eauto.
  destruct Ss as (Wts & Wcs & Sfs).
  intros x ty ck Hty Hck.
  edestruct Safe as (Wc & Wt & Ef); eauto.
  eapply Permutation_in, in_app_or in Hperm; eauto using IsVar_In, HasClock_IsVar.
  unfold denot_var in *.
  setoid_rewrite denot_equation_eq.
  cases_eqn HH; simpl; try congruence.
  - (* entrée *)
    unfold cl_DS in *.
    repeat split; eauto 3 using denot_clock_le.
  - eapply mem_nth_Some with (d := xH) in HH1 as [? Hn]; rewrite <- Hn in *.
    repeat split.
    + (* ty_DS *)
      eapply Forall2_Forall3, Forall3_forall3 in Wts as (?&?& Hf); eauto.
      eapply Hf; rewrite ?list_of_nprod_nth; auto; try congruence.
      eapply HasType_det; try apply Forall2_nth; eauto.
      Unshelve. all: auto; exact 0.
    + (* cl_DS *)
      unfold cl_DS in *.
      eapply Ole_trans, denot_clock_le, Le.
      eapply Forall2_Forall3, Forall3_forall3 in Wcs as (_ & Hl & Hf); auto.
      rewrite list_of_nprod_length in Hl.
      eapply Hf; rewrite ?list_of_nprod_nth; eauto; try congruence.
      eapply HasClock_det; try apply Forall2_nth; eauto.
      Unshelve. all: eauto; exact 0.
    + apply forall_nprod_k'; auto; congruence.
  - (* erreur *)
    exfalso.
    destruct Hperm; eauto using mem_ident_false, mem_nth_nin.
Admitted.

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
