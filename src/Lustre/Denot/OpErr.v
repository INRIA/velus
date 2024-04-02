From Coq Require Import List.
Import ListNotations.

From Velus Require Import Common Operators Clocks StaticEnv LSyntax LTyping LOrdered.
From Velus Require Import Cpo SDfuns CommonDS.
From Velus Require Import Denot Restr CheckOp.

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
       (Import Typ   : LTYPING       Ids Op OpAux Cks Senv Syn)
       (Import Restr : LRESTR        Ids Op OpAux Cks Senv Syn)
       (Import Lord  : LORDERED      Ids Op OpAux Cks Senv Syn)
       (Import Den   : LDENOT        Ids Op OpAux Cks Senv Syn Lord)
       (Import Ckop  : CHECKOP       Ids Op OpAux Cks Senv Syn).

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


Section Op_correct_node.

Variables
  (G : global)
  (ins : list ident)
  (envG : Dprodi FI)
  (envI : DS_prod SI)
  (env : DS_prod SI).

Inductive op_correct_exp : exp -> Prop :=
| opc_Econst :
  forall c,
    op_correct_exp (Econst c)
| opc_Eenum :
  forall c ty,
    op_correct_exp (Eenum c ty)
| opc_Evar :
  forall x ann,
    op_correct_exp (Evar x ann)
| opc_Eunop :
  forall op e ann,
    op_correct_exp e ->
    (forall (* ss *) ty,
        typeof e = [ty] ->
        (* denot_exp ins e envI env = ss -> *)
        forall_nprod (DSForall_pres (fun v => wt_value v ty -> sem_unop op v ty <> None)) (denot_exp G ins e envG envI env)
    ) ->
    op_correct_exp (Eunop op e ann)
| opc_Ebinop :
  forall op e1 e2 ann,
    op_correct_exp e1 ->
    op_correct_exp e2 ->
    (forall ty1 ty2,
        typeof e1 = [ty1] ->
        typeof e2 = [ty2] ->
        let ss1 := denot_exp G ins e1 envG envI env in
        let ss2 := denot_exp G ins e2 envG envI env in
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

Definition op_correct_node (n : node) : Prop :=
  match n.(n_block) with
  | Blocal (Scope vars blks) => Forall op_correct_block blks
  | _ => True
  end.

End Op_correct_node.

(* TODO: c'est trop fort pour l'instant.
   Comment ne parler que du nœud main ?
   Et propager les valeurs dans les appels de fonction ? *)
Definition op_correct_global (G : global) : Prop :=
  let envG := denot_global G in
  Forall (fun n => forall envI,
              let ins := List.map fst n.(n_in) in
              op_correct_node G ins envG envI (envG (n_name n) envI) n)
    (nodes G).


(** ** Facts about op_correct  *)

Lemma op_correct_exp_cons :
  forall e nd nds tys exts ins envG envI env,
    ~ Is_node_in_exp nd.(n_name) e ->
    op_correct_exp (Global tys exts (nd :: nds)) ins envG envI env e ->
    op_correct_exp (Global tys exts (nds)) ins envG envI env e.
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
  forall b nd nds tys exts ins envG envI env,
    ~ Is_node_in_block nd.(n_name) b ->
    op_correct_block (Global tys exts (nd :: nds)) ins envG envI env b ->
    op_correct_block (Global tys exts (nds)) ins envG envI env b.
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

Lemma op_correct_node_cons :
  forall n nd nds tys exts ins envG envI env,
    ~ Is_node_in_block nd.(n_name) n.(n_block) ->
    op_correct_node (Global tys exts (nd :: nds)) ins envG envI env n ->
    op_correct_node (Global tys exts nds) ins envG envI env n.
Proof.
  unfold op_correct_node.
  intros * Hnin Hop; cases.
  eapply Forall_impl_In in Hop; eauto.
  intros * Hin.
  apply op_correct_block_cons.
  contradict Hnin.
  constructor; constructor.
  solve_Exists.
Qed.

(** *** The other way *)

Lemma op_correct_exp_uncons :
  forall e nd nds tys exts ins envG envI env,
    ~ Is_node_in_exp nd.(n_name) e ->
    op_correct_exp (Global tys exts (nds)) ins envG envI env e ->
    op_correct_exp (Global tys exts (nd :: nds)) ins envG envI env e.
Proof.
  induction e using exp_ind2; intros * Hnin Hop; inv Hop;
    eauto using op_correct_exp.
  - (* Eunop *)
    setoid_rewrite denot_exp_cons in H3;
      eauto 6 using op_correct_exp, Is_node_in_exp.
  - (* Ebinop *)
    simpl in *.
    setoid_rewrite denot_exp_cons in H5;
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

Lemma op_correct_block_uncons :
  forall b nd nds tys exts ins envG envI env,
    ~ Is_node_in_block nd.(n_name) b ->
    op_correct_block (Global tys exts (nds)) ins envG envI env b ->
    op_correct_block (Global tys exts (nd :: nds)) ins envG envI env b.
Proof.
  unfold op_correct_block.
  intros * Hnin Hop; cases.
  eapply Forall_impl_In in Hop; eauto.
  intros * Hin.
  apply op_correct_exp_uncons.
  contradict Hnin.
  constructor.
  unfold Is_node_in_eq.
  solve_Exists.
Qed.

Lemma op_correct_node_uncons :
  forall n nd nds tys exts ins envG envI env,
    ~ Is_node_in nd.(n_name) n ->
    op_correct_node (Global tys exts nds) ins envG envI env n ->
    op_correct_node (Global tys exts (nd :: nds)) ins envG envI env n.
Proof.
  unfold op_correct_node, Is_node_in.
  intros * Hnin Hop; cases.
  eapply Forall_impl_In in Hop; eauto.
  intros * Hin.
  apply op_correct_block_uncons.
  contradict Hnin.
  constructor; constructor.
  solve_Exists.
Qed.


Global Add Parametric Morphism G ins : (@op_correct_exp G ins)
    with signature @Oeq (Dprodi FI) ==> @Oeq (DS_prod SI) ==>
                     @Oeq (DS_prod SI) ==> @eq exp ==> Basics.impl
      as op_correct_exp_morph_impl.
Proof.
  intros * Eq1 * Eq2 * Eq3 e.
  induction e using exp_ind2; intro Hoc; inv Hoc.
  all: try now (constructor; eauto).
  - (* Eunop *)
    take (op_correct_exp _ _ _ _ _ _) and apply IHe in it.
    constructor; intros; eauto.
    rewrite <- Eq1, <- Eq2, <- Eq3; auto.
  - (* Ebinop *)
    take (op_correct_exp _ _ _ _ _ e1) and apply IHe1 in it.
    take (op_correct_exp _ _ _ _ _ e2) and apply IHe2 in it.
    constructor; intros; eauto.
    subst ss1 ss2.
    rewrite <- Eq1, <- Eq2, <- Eq3; auto.
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
    with signature @Oeq (Dprodi FI) ==> @Oeq (DS_prod SI) ==>
                     @Oeq (DS_prod SI) ==> @eq exp ==> iff
      as op_correct_exp_morph.
Proof.
  intros.
  split; apply op_correct_exp_morph_impl; auto.
Qed.

Global Add Parametric Morphism G ins : (@op_correct_block G ins)
    with signature @Oeq (Dprodi FI) ==> @Oeq (DS_prod SI) ==>
                     @Oeq (DS_prod SI) ==> @eq block ==> iff
      as op_correct_block_morph.
Proof.
  intros.
  unfold op_correct_block.
  cases; try tauto.
  split; intros Hf; simpl_Forall; eapply op_correct_exp_morph in Hf; eauto.
Qed.

Global Add Parametric Morphism G ins : (@op_correct_node G ins)
    with signature @Oeq (Dprodi FI) ==> @Oeq (DS_prod SI) ==>
                     @Oeq (DS_prod SI) ==> @eq node ==> iff
      as op_correct_node_morph.
Proof.
  intros * Eq1 * Eq2 * Eq3 *.
  unfold op_correct_node.
  cases; try tauto.
  split; intros * HH; simpl_Forall.
  all: eapply op_correct_block_morph in HH; eauto.
Qed.


(** ** Correction of the [CheckOp] procedure *)

Theorem check_exp_ok :
  forall Γ G ins envG envI env,
  forall e, restr_exp e ->
       wt_exp G Γ e ->
       check_exp e = true ->
       op_correct_exp G ins envG envI env e.
Proof.
  intros *.
  induction e using exp_ind2; simpl; intros Hr Hwt Hchk; inv Hr; inv Hwt.
  - (* Econst *)
    constructor.
  - (* Eenum *)
    constructor.
  - (* Evar *)
    constructor.
  - (* Eunop *)
    destruct (typeof e) as [|? []] eqn:Hty; try congruence.
    apply andb_prop in Hchk as [F1 F2].
    constructor; auto.
    intros ty' Hty'.
    rewrite Hty' in Hty; inv Hty.
    (* c'est très très simple *)
    apply nprod_forall_Forall, Forall_forall.
    intros s Hin.
    apply DSForall_all; intros [| v |]; auto.
    intro Wtv.
    eapply check_unop_correct; eauto; simpl; auto.
    congruence.
  - (* Ebinop *)
    take (typeof e1 = _) and rewrite it in Hchk.
    take (typeof e2 = _) and rewrite it in Hchk.
    constructor.
    (* récurrence pour e1, e2 *)
    1,2: cases; repeat rewrite Bool.andb_true_iff in *; tauto.
    intros ty1' ty2' Hty1' Hty2' ss1 ss2.
    rewrite Hty1' in *; take ([_] = [_]) and inv it.
    rewrite Hty2' in *; take ([_] = [_]) and inv it.
    (* cas sur la tête de e2 *)
    cases; inv Hty2'; repeat rewrite Bool.andb_true_iff, ?Bool.orb_true_iff in *.
    (* membre droit constant *)
    { subst ss2; rewrite denot_exp_eq.
      simpl.
      unfold sconst, DSForall_2pres.
      rewrite ID_simpl, Id_simpl, MAP_map, zip_map.
      eapply DSForall_zip with (P := fun _ => True) (Q := fun _ => True); auto using DSForall_all.
      intros [] [] _ _; auto.
      intros Wt1 Wt2.
      destruct Hchk as [? []];
        eapply check_binop_correct; eauto; simpl; auto; congruence. }
    (* autres cas *)
    all: apply DSForall_all.
    all: intros [[|v1|] [|v2|]]; auto; intros Wt1 Wt2.
    all: destruct Hchk as [[Hck]].
    all: eapply check_binop_correct in Hck; eauto; congruence.
  - (* Efby *)
    apply andb_prop in Hchk as [F1 F2].
    apply forallb_Forall in F1, F2.
    constructor; simpl_Forall; auto.
  - (* Ewhen *)
    apply forallb_Forall in Hchk.
    constructor; simpl_Forall; auto.
  - (* Emerge *)
    apply forallb_Forall in Hchk.
    constructor; simpl_Forall.
    eapply forallb_Forall, Forall_forall in Hchk; eauto.
  - (* Ecase default *)
    apply andb_prop in Hchk as [F1 F2].
    apply forallb_Forall in F2.
    constructor; simpl_Forall; auto.
    eapply forallb_Forall, Forall_forall in F2; eauto.
  - (* Ecase *)
    apply andb_prop in Hchk as [F1 F3].
    apply andb_prop in F1 as [F1 F2].
    apply forallb_Forall in F2,F3.
    constructor; simpl_Forall; auto.
    eapply forallb_Forall, Forall_forall in F2; eauto.
  - (* Eapp *)
    apply andb_prop in Hchk as [F1 F2].
    apply forallb_Forall in F1, F2.
    constructor; simpl_Forall; auto.
Qed.

Lemma check_block_ok :
  forall Γ G ins envG envI env,
  forall b, restr_block b ->
       wt_block G Γ b ->
       check_block b = true ->
       op_correct_block G ins envG envI env b.
Proof.
  destruct b; simpl; intros * Hr Hwt Hc; try tauto.
  destruct e.
  eapply forallb_Forall in Hc.
  inv Hr; inv Hwt.
  simpl_Forall; eauto using check_exp_ok.
Qed.

Lemma check_node_ok :
  forall G ins envG envI env,
  forall (n : node),
    restr_node n ->
    wt_node G n ->
    check_node n = true ->
    op_correct_node G ins envG envI env n.
Proof.
  unfold check_node, check_top_block, op_correct_node.
  intros * Hr Hwt Hc.
  inv Hr; inv Hwt.
  cases.
  take (restr_top_block _) and inv it.
  take (wt_block _ _ _) and inv it.
  take (wt_scope _ _ _ _) and inv it.
  apply forallb_Forall in Hc.
  simpl_Forall; eauto using check_block_ok.
Qed.

Theorem check_global_ok :
  forall G,
    restr_global G ->
    wt_global G ->
    check_global G = true ->
    op_correct_global G.
Proof.
  unfold check_global, op_correct_global, restr_global.
  intros * Hr Hwt Hc%forallb_Forall.
  generalize (denot_global G); intro envG.
  assert (Ordered_nodes G) as Hord.
  now apply wl_global_Ordered_nodes, wt_global_wl_global.
  destruct G as [tys exts nds]; simpl in *.
  induction nds as [|nd nds]; simpl; auto.
  inv Hr. inv Hc.
  apply wt_global_uncons in Hwt as Hwtn.
  constructor; intros; auto.
  - eapply check_node_ok, op_correct_node_uncons in Hwtn; eauto.
    eapply find_node_not_Is_node_in; eauto using find_node_now.
  - eapply IHnds in H2; eauto using wt_global_cons, Ordered_nodes_cons.
    simpl_Forall.
    eapply op_correct_node_uncons in H2; eauto using Ordered_nodes_nin.
Qed.

End OP_ERR.

Module OpErrFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks   : CLOCKS        Ids Op OpAux)
       (Senv  : STATICENV     Ids Op OpAux Cks)
       (Syn   : LSYNTAX       Ids Op OpAux Cks Senv)
       (Typ   : LTYPING       Ids Op OpAux Cks Senv Syn)
       (Restr : LRESTR        Ids Op OpAux Cks Senv Syn)
       (Lord  : LORDERED      Ids Op OpAux Cks Senv Syn)
       (Den   : LDENOT        Ids Op OpAux Cks Senv Syn Lord)
       (Ckop  : CHECKOP       Ids Op OpAux Cks Senv Syn)
<: OP_ERR Ids Op OpAux Cks Senv Syn Typ Restr Lord Den Ckop.
  Include OP_ERR Ids Op OpAux Cks Senv Syn Typ Restr Lord Den Ckop.
End OpErrFun.
