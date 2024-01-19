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
Require Import CommonDS SDfuns Denot OpErr CommonList2.

(* c'est une version pour tester sur de petits programmes avec velusmain
   On a juste sorti le module TEST1ETDEMI de CheckOp à toplevel ...
 *)

(** ** Petite analyse statique pour décider op_correct *)
(* TODO: move to OpErr ? *)

Module Type CHECKOPTEST
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks   : CLOCKS        Ids Op OpAux)
       (Import Senv  : STATICENV     Ids Op OpAux Cks)
       (Import Syn   : LSYNTAX       Ids Op OpAux Cks Senv)
       (* (Import Lord  : LORDERED      Ids Op OpAux Cks Senv Syn) *)
       (* (Import Den   : LDENOT        Ids Op OpAux Cks Senv Syn Lord) *)
       (* (Import OpErr : OP_ERR        Ids Op OpAux Cks Senv Syn Lord Den). *)
.
(* Analyse qui gère les opérateurs binaires aux arguments droits constants *)

Section Top.
(* pour les unop on fait comme dans l'analyse simple *)
Variable check_unop : unop -> type -> bool.
Hypothesis check_unop_correct :
  forall op ty,
    check_unop op ty = true ->
    forall v, wt_value v ty ->
         sem_unop op v ty <> None.

(* Pour les opérateurs binaires, il y a deux possibilités :
   - on connaît la valeur du membre droit, on peut essayer
     de vérifier que le calcul ne plantera jamais avec cette valeur
   - on ne la connaît pas, seules quelques opérations fonctionnent
     pour toutes les valeurs
 *)

(* premier cas *)
Variable check_binop_val : binop -> type -> value -> type -> bool.
Hypothesis check_binop_val_correct :
  forall op ty1 v2 ty2,
    check_binop_val op ty1 v2 ty2 = true ->
    forall v1, wt_value v1 ty1 ->
          wt_value v2 ty2 ->
          sem_binop op v1 ty1 v2 ty2 <> None.


(* second cas *)
Variable check_binop_any : binop -> type -> type -> bool.
Hypothesis check_binop_any_correct :
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
  | Elast _ _ => false (* restr *)
  | Eunop op e ann =>
      match typeof e with
      | [ty] => check_unop op ty && check_exp e
      | _ => false
      end
  | Ebinop op e1 (Econst c) ann => (* TODO: Enum aussi ? *)
      let ty2 := Tprimitive (ctype_cconst c) in
      match typeof e1 with
      | [ty1] => check_exp e1
                (* soit on arrive à décider avec la valeur c,
                   soit on vérifie pour toute valeur de type ty2 *)
                && (check_binop_val op ty1 (Vscalar (sem_cconst c)) ty2
                    || check_binop_any op ty1 ty2)
      | _ => false
      end
  | Ebinop op e1 e2 ann =>
      match typeof e1, typeof e2 with
      | [ty1], [ty2] => check_binop_any op ty1 ty2 && check_exp e1 && check_exp e2
      | _,_ => false
      end
  | Eextcall _ _ _ => false (* restr *)
  | Efby e0s es ann => forallb check_exp e0s && forallb check_exp es
  | Earrow e0s es ann => false (* restr *)
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

Definition check_node {PSyn Prefs} (n : @node PSyn Prefs) :=
  check_top_block (n_block n).

Definition check_global {PSyn Prefs} (G : @global PSyn Prefs) := forallb check_node (nodes G).

End Top.
(* (** Correction de la procédure *) *)

(* Theorem check_exp_ok : *)
(*   forall G ins envG envI bs env, *)
(*   forall e, check_exp e = true -> *)
(*        op_correct_exp G ins envG envI bs env e. *)
(* Proof. *)
(*   intros *. *)
(*   induction e using exp_ind2; simpl; intro Hchk; try congruence. *)
(*   - (* Econst *) *)
(*     constructor. *)
(*   - (* Eenum *) *)
(*     constructor. *)
(*   - (* Evar *) *)
(*     constructor. *)
(*   - (* Eunop *) *)
(*     destruct (typeof e) as [|ty []] eqn:Hty; try congruence. *)
(*     apply andb_prop in Hchk as [F1 F2]. *)
(*     constructor; auto. *)
(*     intros ty' Hty'. *)
(*     rewrite Hty' in Hty; inv Hty. *)
(*     (* c'est très très simple *) *)
(*     apply nprod_forall_Forall, Forall_forall. *)
(*     intros s Hin. *)
(*     apply DSForall_all; intros [| v |]; auto. *)
(*     intro Wtv. *)
(*     now apply check_unop_correct. *)
(*   - (* Ebinop *) *)
(*     destruct (typeof e1) as [|ty1 []] eqn:Hty1; try (cases; congruence). *)
(*     constructor. *)
(*     (* récurrence pour e1, e2 *) *)
(*     1,2: cases; repeat rewrite Bool.andb_true_iff in *; tauto. *)
(*     intros ty1' ty2' Hty1' Hty2' ss1 ss2. *)
(*     rewrite Hty1' in Hty1; inv Hty1. *)
(*     (* cas sur la tête de e2 *) *)
(*     cases; inv Hty2'; repeat rewrite Bool.andb_true_iff, ?Bool.orb_true_iff in *. *)
(*     (* membre droit constant *) *)
(*     { subst ss2; rewrite denot_exp_eq. *)
(*       simpl. *)
(*       unfold sconst, DSForall_2pres. *)
(*       rewrite ID_simpl, Id_simpl, MAP_map, zip_map. *)
(*       eapply DSForall_zip with (P := fun _ => True) (Q := fun _ => True); auto using DSForall_all. *)
(*       intros [] [] _ _; auto. *)
(*       intros Wt1 Wt2. *)
(*       destruct Hchk as [? []]. *)
(*       - apply check_binop_val_correct; auto. *)
(*       - apply check_binop_any_correct; auto. } *)
(*     (* autre cas *) *)
(*     all: apply DSForall_all. *)
(*     all: intros [[|v1|] [|v2|]]; auto; intros Wt1 Wt2. *)
(*     all: apply check_binop_any_correct; auto; tauto. *)
(*   - (* Efby *) *)
(*     apply andb_prop in Hchk as [F1 F2]. *)
(*     apply forallb_Forall in F1, F2. *)
(*     constructor; simpl_Forall; auto. *)
(*   - (* Ewhen *) *)
(*     apply forallb_Forall in Hchk. *)
(*     constructor; simpl_Forall; auto. *)
(*   - (* Emerge *) *)
(*     apply forallb_Forall in Hchk. *)
(*     constructor; simpl_Forall. *)
(*     eapply forallb_Forall, Forall_forall in Hchk; eauto. *)
(*   - (* Ecase *) *)
(*     destruct d; simpl in H0. *)
(*     + apply andb_prop in Hchk as [F1 F3]. *)
(*       apply andb_prop in F1 as [F1 F2]. *)
(*       apply forallb_Forall in F2,F3. *)
(*       constructor; simpl_Forall; auto. *)
(*       eapply forallb_Forall, Forall_forall in F2; eauto. *)
(*     + apply andb_prop in Hchk as [F1 F2]. *)
(*       apply forallb_Forall in F2. *)
(*       constructor; simpl_Forall; auto. *)
(*       eapply forallb_Forall, Forall_forall in F2; eauto. *)
(*   - (* Eapp *) *)
(*     apply andb_prop in Hchk as [F1 F2]. *)
(*     apply forallb_Forall in F1, F2. *)
(*     constructor; simpl_Forall; auto. *)
(* Qed. *)

(* Lemma check_block_ok : *)
(*   forall G ins envG envI bs env, *)
(*   forall b, check_block b = true -> *)
(*        op_correct_block G ins envG envI bs env b. *)
(* Proof. *)
(*   destruct b; simpl; intros * Hc; try congruence. *)
(*   destruct e. *)
(*   eapply forallb_Forall in Hc. *)
(*   simpl_Forall; auto using check_exp_ok. *)
(* Qed. *)

(* Lemma check_node_ok : *)
(*   forall G ins envG envI bs env, *)
(*   forall (n : node), *)
(*     check_node n = true -> *)
(*     op_correct G ins envG envI bs env n. *)
(* Proof. *)
(*   unfold check_node, check_top_block, op_correct. *)
(*   intros * Hc. *)
(*   cases. *)
(*   apply forallb_Forall in Hc. *)
(*   simpl_Forall; eauto using check_block_ok. *)
(* Qed. *)


End CHECKOPTEST.
Module CheckOpTestFun
  (Ids   : IDS)
  (Op    : OPERATORS)
  (OpAux : OPERATORS_AUX Ids Op)
  (Cks   : CLOCKS        Ids Op OpAux)
  (Senv  : STATICENV     Ids Op OpAux Cks)
  (Syn   : LSYNTAX       Ids Op OpAux Cks Senv)
<: CHECKOPTEST Ids Op OpAux Cks Senv Syn.
  Include CHECKOPTEST Ids Op OpAux Cks Senv Syn.
End CheckOpTestFun.
