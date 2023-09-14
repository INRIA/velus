From Coq Require Import List.
Import ListNotations.

From Velus Require Import Common Operators Clocks StaticEnv LSyntax Denot LOrdered.
From Velus Require Import Cpo SDfuns CommonDS.

(** * Operators failure

    Some class of errors, denoted by the [error_Op] constructor of [SDfuns.error],
    cannot be prevented at compile time. It is the case for divisions by zero,
    overflows in modulo/shifting, etc. The precise behaviour of these operators is
    described in [CompCert/cfrontend/Cop.v].

    This file introduces the [op_correct] predicate that describes the (minimal?)
    set of assumptions required on a Lustre program for its denotation to be
    free of [error_Op].
 *)

Module Type OP_ERR
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks   : CLOCKS        Ids Op OpAux)
       (Import Senv  : STATICENV     Ids Op OpAux Cks)
       (Import Syn   : LSYNTAX       Ids Op OpAux Cks Senv)
       (Import Lord  : LORDERED      Ids Op OpAux Cks Senv Syn)
       (Import Den   : LDENOT        Ids Op OpAux Cks Senv Syn Lord).

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

Definition DSForall_2pres {A B} (P : A -> B -> Prop) : DS (sampl A * sampl B) -> Prop :=
  DSForall (fun v =>
              match v with
              | (pres a, pres b) => P a b
              | _ => True
              end).

Lemma DSForall_2pres_impl :
  forall {A B} (P : A -> Prop) (Q : B -> Prop) (R : A -> B -> Prop) s1 s2,
    DSForall_pres P s1 ->
    DSForall_pres Q s2 ->
    DSForall_2pres (fun x y => P x -> Q y -> R x y) (ZIP pair s1 s2) ->
    DSForall_2pres R (ZIP pair s1 s2).
Proof.
  intros *.
  unfold DSForall_2pres, DSForall_pres.
  remember_ds (ZIP _ _ _) as t.
  revert Ht. revert s1 s2 t.
  cofix Cof; intros * Ht Hps1 Hqs2 Hpq.
  destruct t as [| []].
  - constructor. rewrite <- eqEps in *; eauto.
  - apply symmetry, zip_uncons in Ht as (?&?&?&?& Hs1 & Hs2 &?& Hp).
    rewrite Hs1, Hs2 in *.
    inv Hps1. inv Hqs2. inv Hpq. inv Hp.
    constructor; eauto; cases.
Qed.


Section Op_correct.

Variables
  (G : global)
  (ins : list ident)
  (envG : Dprodi FI)
  (envI : DS_prod SI)
  (bs : DS bool)
  (env : DS_prod SI).

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
| opc_Ebinop :
  forall op e1 e2 ann,
    op_correct_exp e1 ->
    op_correct_exp e2 ->
    (forall ty1 ty2,
        typeof e1 = [ty1] ->
        typeof e2 = [ty2] ->
        let ss1 := denot_exp G ins e1 envG envI bs env in
        let ss2 := denot_exp G ins e2 envG envI bs env in
        DSForall_2pres
          (fun v1 v2 =>
             wt_value v1 ty1 ->
             wt_value v2 ty2 ->
             sem_binop op v1 ty1 v2 ty2 <> None)
          (ZIP pair (nprod_hd_def errTy ss1) (nprod_hd_def errTy ss2))
    ) ->
    op_correct_exp (Ebinop op e1 e2 ann)
| opc_Efby :
  forall e0s es anns,
    Forall op_correct_exp e0s ->
    Forall op_correct_exp es ->
    op_correct_exp (Efby e0s es anns)
| opc_Ewhen :
  forall es x k anns,
    Forall op_correct_exp es ->
    op_correct_exp (Ewhen es x k anns)
| opc_Merge :
  forall ess x anns,
    Forall (fun es => Forall op_correct_exp (snd es)) ess ->
    op_correct_exp (Emerge x ess anns)
| opc_Case :
  forall e ess anns,
    op_correct_exp e ->
    Forall (fun es => Forall op_correct_exp (snd es)) ess ->
    op_correct_exp (Ecase e ess None anns)
| opc_Case_def :
  forall e ess eds anns,
    op_correct_exp e ->
    Forall (fun es => Forall op_correct_exp (snd es)) ess ->
    Forall op_correct_exp eds ->
    op_correct_exp (Ecase e ess (Some eds) anns)
| opc_Eapp :
  forall f es er anns,
    Forall op_correct_exp es ->
    Forall op_correct_exp er ->
    op_correct_exp (Eapp f es er anns)
.

Definition op_correct_block (b : block) : Prop :=
  match b with
  | Beq (xs,es) => Forall op_correct_exp es
  | _ => True
  end.

Definition op_correct (n : node) : Prop :=
  match n.(n_block) with
  | Blocal (Scope vars blks) => Forall op_correct_block blks
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
  - (* Ebinop *)
    simpl in *.
    setoid_rewrite <- denot_exp_cons in H5;
      eauto 12 using op_correct_exp, Is_node_in_exp.
  - (* Efby *)
    constructor; simpl_Forall.
    + eapply H; eauto.
      contradict Hnin; constructor; left; solve_Exists.
    + eapply H0; eauto.
      contradict Hnin; constructor; right; solve_Exists.
  - (* Ewhen *)
    constructor.
    simpl_Forall.
    eapply H; eauto.
    contradict Hnin; constructor; solve_Exists.
  - (* Emerge *)
    constructor.
    simpl_Forall.
    eapply H; eauto.
    contradict Hnin; constructor; solve_Exists.
  - (* Case total *)
    constructor.
    + eapply IHe; eauto.
      contradict Hnin; constructor; auto.
    + simpl_Forall.
      eapply H; eauto.
      contradict Hnin; constructor; right; left; solve_Exists.
  - (* Case defaut *)
    constructor.
    + eapply IHe; eauto.
      contradict Hnin; constructor; auto.
    + simpl_Forall.
      eapply H; eauto.
      contradict Hnin; constructor; right; left; solve_Exists.
    + simpl_Forall.
      eapply H0; eauto.
      contradict Hnin; constructor; right; right; esplit; split; solve_Exists.
  - (* Eapp *)
    constructor.
    + simpl_Forall.
      eapply H; eauto.
      contradict Hnin; constructor; left; solve_Exists.
    + simpl_Forall.
      eapply H0; eauto.
      contradict Hnin; constructor; right; solve_Exists.
Qed.

Lemma op_correct_block_cons :
  forall b nd nds tys exts ins envG envI bs env,
    ~ Is_node_in_block nd.(n_name) b ->
    op_correct_block (Global tys exts (nd :: nds)) ins envG envI bs env b ->
    op_correct_block (Global tys exts (nds)) ins envG envI bs env b.
Proof.
  unfold op_correct_block.
  intros * Hnin Hop; cases.
  eapply Forall_impl_In in Hop; eauto.
  intros * Hin.
  apply op_correct_exp_cons.
  contradict Hnin.
  constructor.
  unfold Is_node_in_eq.
  solve_Exists.
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
  apply op_correct_block_cons.
  contradict Hnin.
  constructor; constructor.
  solve_Exists.
Qed.

Global Add Parametric Morphism G ins : (@op_correct_exp G ins)
    with signature @Oeq (Dprodi FI) ==> @Oeq (DS_prod SI) ==> @Oeq (DS bool) ==>
                     @Oeq (DS_prod SI) ==> @eq exp ==> Basics.impl
      as op_correct_exp_morph_impl.
Proof.
  intros * Eq1 * Eq2 * Eq3 * Eq4 e.
  induction e using exp_ind2; intro Hoc; inv Hoc.
  all: try now (constructor; eauto).
  - (* Eunop *)
    take (op_correct_exp _ _ _ _ _ _ _) and apply IHe in it.
    constructor; intros; eauto.
    rewrite <- Eq1, <- Eq2, <- Eq3, <- Eq4; auto.
  - (* Ebinop *)
    take (op_correct_exp _ _ _ _ _ _ e1) and apply IHe1 in it.
    take (op_correct_exp _ _ _ _ _ _ e2) and apply IHe2 in it.
    constructor; intros; eauto.
    subst ss1 ss2.
    rewrite <- Eq1, <- Eq2, <- Eq3, <- Eq4; auto.
  - (* Efby *)
    constructor; simpl_Forall; auto.
  - (* Ewhen *)
    constructor; simpl_Forall; auto.
  - (* Emerge *)
    constructor; simpl_Forall; auto.
  - (* Case total *)
    constructor; simpl_Forall; auto.
  - (* Case defaut *)
    constructor; simpl_Forall; auto.
  - (* Eapp *)
    constructor; simpl_Forall; auto.
Qed.

Global Add Parametric Morphism G ins : (@op_correct_exp G ins)
    with signature @Oeq (Dprodi FI) ==> @Oeq (DS_prod SI) ==> @Oeq (DS bool) ==>
                     @Oeq (DS_prod SI) ==> @eq exp ==> iff
      as op_correct_exp_morph.
Proof.
  intros.
  split; apply op_correct_exp_morph_impl; auto.
Qed.

Global Add Parametric Morphism G ins : (@op_correct_block G ins)
    with signature @Oeq (Dprodi FI) ==> @Oeq (DS_prod SI) ==> @Oeq (DS bool) ==>
                     @Oeq (DS_prod SI) ==> @eq block ==> iff
      as op_correct_block_morph.
Proof.
  intros.
  unfold op_correct_block.
  cases; try tauto.
  split; intros Hf; simpl_Forall; eapply op_correct_exp_morph in Hf; eauto.
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
  all: eapply op_correct_block_morph in HH; eauto.
Qed.


End OP_ERR.

Module OpErrFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks   : CLOCKS        Ids Op OpAux)
       (Senv  : STATICENV     Ids Op OpAux Cks)
       (Syn   : LSYNTAX Ids Op OpAux Cks Senv)
       (Lord  : LORDERED     Ids Op OpAux Cks Senv Syn)
       (Den   : LDENOT     Ids Op OpAux Cks Senv Syn Lord)
<: OP_ERR Ids Op OpAux Cks Senv Syn Lord Den.
  Include OP_ERR Ids Op OpAux Cks Senv Syn Lord Den.
End OpErrFun.
