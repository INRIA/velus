From Coq Require Import Datatypes List.
Import List.ListNotations.

From Velus Require Import Common.
From Velus Require Import CommonList.
From Velus Require Import CommonTyping.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Lustre.StaticEnv.
From Velus Require Import Lustre.LSyntax Lustre.LTyping Lustre.LOrdered.

From Velus Require Import Lustre.Denot.Cpo.
Require Import CommonDS SDfuns Denot OpErr CommonList2 Restr.

(** * Little static analysis to decide [op_correct] *)

Module Type CHECKOP
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
       (Import OpErr : OP_ERR        Ids Op OpAux Cks Senv Syn Lord Den).


(** All check_* functions return a boolean value:
 * - true -> cannot fail
 * - false -> we don't know
 *)


(** Legal unary operators *)
Parameter check_unop : unop -> type -> bool.
Conjecture check_unop_correct :
  forall op ty,
    check_unop op ty = true ->
    forall v, wt_value v ty ->
         sem_unop op v ty <> None.


(** There is two cases for binary operators :
 * - we know the value of the right member because it is constant;
 * - we don't know it, so we only authorize operators that never fails
 *)

(* first case *)
Parameter check_binop_val : binop -> type -> value -> type -> bool.
Conjecture check_binop_val_correct :
  forall op ty1 v2 ty2,
    check_binop_val op ty1 v2 ty2 = true ->
    forall v1, wt_value v1 ty1 ->
          wt_value v2 ty2 ->
          sem_binop op v1 ty1 v2 ty2 <> None.

(* second case *)
Parameter check_binop_any : binop -> type -> type -> bool.
Conjecture check_binop_any_correct :
  forall op ty1 ty2,
    check_binop_any op ty1 ty2 = true ->
    forall v1 v2, wt_value v1 ty1 ->
             wt_value v2 ty2 ->
             sem_binop op v1 ty1 v2 ty2 <> None.

(* true -> cannot fail
 * false -> we don't know *)
Fixpoint check_exp (e : exp) : bool :=
  match e with
  | Econst _ => true
  | Eenum _ _ => true
  | Evar _ _ => true
  | Elast _ _ => true (* restr *)
  | Eunop op e ann =>
      match typeof e with
      | [ty] => check_unop op ty && check_exp e
      | _ => true
      end
  | Ebinop op e1 (Econst c) ann => (* TODO: Enum aussi ? *)
      let ty2 := Tprimitive (ctype_cconst c) in
      match typeof e1 with
      | [ty1] => check_exp e1
                (* soit on arrive à décider avec la valeur c,
                   soit on vérifie pour toute valeur de type ty2 *)
                && (check_binop_val op ty1 (Vscalar (sem_cconst c)) ty2
                    || check_binop_any op ty1 ty2)
      | _ => true
      end
  | Ebinop op e1 e2 ann =>
      match typeof e1, typeof e2 with
      | [ty1], [ty2] => check_binop_any op ty1 ty2 && check_exp e1 && check_exp e2
      | _,_ => true
      end
  | Eextcall _ _ _ => true (* restr *)
  | Efby e0s es ann => forallb check_exp e0s && forallb check_exp es
  | Earrow e0s es ann => true (* restr *)
  | Ewhen es _ t ann => forallb check_exp es
  | Emerge _ ess ann => forallb (fun '(t,es) => forallb check_exp es) ess
  | Ecase e ess None ann => check_exp e && forallb (fun '(t,es) => forallb check_exp es) ess
  | Ecase e ess (Some des) ann => check_exp e && forallb (fun '(t,es) => forallb check_exp es) ess && forallb check_exp des
  | Eapp f es er ann => forallb check_exp es && forallb check_exp er
  end.

Definition check_block b :=
  match b with
  | Beq (_, es) => forallb check_exp es
  | _ => false
  end.

Definition check_top_block b :=
  match b with
  | Blocal (Scope locs blks) => forallb check_block blks
  | _ => false
  end.

Definition check_node (n : node) :=
  check_top_block (n_block n).

Definition check_global (G : global) := forallb check_node (nodes G).

(** Correction of the procedure *)

Theorem check_exp_ok :
  forall Γ G ins envG envI bs env,
  forall e, restr_exp e ->
       wt_exp G Γ e ->
       check_exp e = true ->
       op_correct_exp G ins envG envI bs env e.
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
    now apply check_unop_correct.
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
      destruct Hchk as [? []].
      - apply check_binop_val_correct; auto.
      - apply check_binop_any_correct; auto. }
    (* autres cas *)
    all: apply DSForall_all.
    all: intros [[|v1|] [|v2|]]; auto; intros Wt1 Wt2.
    all: apply check_binop_any_correct; auto; tauto.
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
  forall Γ G ins envG envI bs env,
  forall b, restr_block b ->
       wt_block G Γ b ->
       check_block b = true ->
       op_correct_block G ins envG envI bs env b.
Proof.
  destruct b; simpl; intros * Hr Hwt Hc; try tauto.
  destruct e.
  eapply forallb_Forall in Hc.
  inv Hr; inv Hwt.
  simpl_Forall; eauto using check_exp_ok.
Qed.

Lemma check_node_ok :
  forall G ins envG envI bs env,
  forall (n : node),
    restr_node n ->
    wt_node G n ->
    check_node n = true ->
    op_correct G ins envG envI bs env n.
Proof.
  unfold check_node, check_top_block, op_correct.
  intros * Hr Hwt Hc.
  inv Hr; inv Hwt.
  cases.
  take (restr_top_block _) and inv it.
  take (wt_block _ _ _) and inv it.
  take (wt_scope _ _ _ _) and inv it.
  apply forallb_Forall in Hc.
  simpl_Forall; eauto using check_block_ok.
Qed.

End CHECKOP.

Module CheckOpFun
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
  (OpErr : OP_ERR        Ids Op OpAux Cks Senv Syn Lord Den)
<: CHECKOP Ids Op OpAux Cks Senv Syn Typ Restr Lord Den OpErr.
  Include CHECKOP Ids Op OpAux Cks Senv Syn Typ Restr Lord Den OpErr.
End CheckOpFun.
