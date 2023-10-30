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


(** ** Petite analyse statique pour décider op_correct *)
(* TODO: move to OpErr ? *)

Module Type CHECKOP
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks   : CLOCKS        Ids Op OpAux)
       (Import Senv  : STATICENV     Ids Op OpAux Cks)
       (Import Syn   : LSYNTAX       Ids Op OpAux Cks Senv)
       (Import Lord  : LORDERED      Ids Op OpAux Cks Senv Syn)
       (Import Den   : LDENOT        Ids Op OpAux Cks Senv Syn Lord)
       (Import OpErr : OP_ERR        Ids Op OpAux Cks Senv Syn Lord Den).


Module TEST2.

  (* TODO: 2 résultats
     - mq que l'analyse renvoie une sur-approx :
          Any ---> pas err error_Op
          Val v ---> si pres v' alors v' = v
          Err  ---> on s'en fout ?
     - mq ça donne op_correct ??
   *)

Inductive res : Type :=
| Any
| Err
| Val (v : value).

Parameter join : res -> res -> res.
  (* fun r1 r2 => match r1, r2 with *)
  (*           | Err, _ | _, Err => Err *)
  (*           | _, _ => Any *)
  (*           end. *)

Parameter check_unop : unop -> res -> type -> res.
Conjecture check_unop_correct :
  forall op r ty,
    check_unop op r ty <> Err ->
    sem_unop op r ty <> None.

Parameter check_binop : binop -> res -> type -> res -> type -> res.

Fixpoint check_exp (e : exp) : list res :=
  match e with
  | Econst c => [ Val (Vscalar (sem_cconst c)) ]
  | Eenum _ _ => [ Err ] (* TODO ?? *)
  | Evar _ _ => [ Any ]
  | Elast _ _ => [ Err ] (* restr *)
  | Eunop op e ann =>
      match typeof e with
      | [ty] =>
          match check_exp e with
          | [ v ] => [ check_unop op v ty ]
          | _ => [ Err ]
          end
      | _ => [ Err ]
      end
  | Ebinop op e1 e2 ann =>
      match typeof e1, typeof e2 with
      | [ty1], [ty2] =>
          match check_exp e1, check_exp e2 with
          | [ v1 ], [ v2 ] => [ check_binop op v1 ty1 v2 ty2 ]
          | _, _ => [ Err ]
          end
      | _,_ => [ Err ]
      end
  | Eextcall _ _ _ => [ Err ] (* restr *)
  | Efby e0s es ann =>
      map2 join
      (concat (List.map check_exp e0s))
      (concat (List.map check_exp es))

  | Earrow e0s es ann => [ Err ] (* restr *)
  | Ewhen es _ t ann =>
      (* on ignore la valeur de la condition *)
      concat (List.map check_exp es)
  | Emerge _ ess (tys,_) =>
      fold_left (map2 join)
        (List.map (fun '(t, es) => concat (List.map check_exp es)) ess)
        (List.map (fun _ => Any) tys) (* vrai problème : ça annihile tout espoir de Val *)
  (* | Ecase e ess None ann => check_exp e && forallb (fun '(t,es) => forallb check_exp es) ess *)
  (* | Ecase e ess (Some des) ann => check_exp e && forallb (fun '(t,es) => forallb check_exp es) ess && forallb check_exp des *)
  (* | Eapp f es er ann => forallb check_exp es && forallb check_exp er *)
  | _ => [ Err ]
  end.

Theorem check_exp_correct :
  forall G ins envG envI bs env,
  forall e, Forall (fun v => v <> Err) (check_exp e) ->
       op_correct_exp G ins envG envI bs env e.
Proof.
  intros *.
  induction e using exp_ind2; simpl; intro Hchk; try now inv Hchk.
  - (* Econst *)
    constructor.
  - (* Evar *)
    constructor.
  - (* Eunop *)
    destruct (typeof e) as [|ty []] eqn:Hty; try now inv Hchk.
    destruct (check_exp e) as [|v []] eqn:Hv; try now inv Hchk.
    inv Hchk.
    constructor. apply IHe; constructor; auto.

    apply andb_prop in Hchk as [F1 F2].
    constructor; auto.
    intros ty' Hty'.
    rewrite Hty' in Hty; inv Hty.
    (* c'est très très simple *)
    apply nprod_forall_Forall, Forall_forall.
    intros s Hin.


Qed.

End TEST2.


(* 1ère analyse, très simpliste, qui ne dépend pas des valeurs *)
Module TEST1.

(** caractérise un opérateur unaire qui n'échoue jamais sur un
    type de valeur donné *)
Parameter check_unop : unop -> type -> bool.
Conjecture check_unop_correct :
  forall op ty,
    check_unop op ty = true ->
    forall v, wt_value v ty ->
         sem_unop op v ty <> None.

(** caractérise un opérateur binaire qui n'échoue jamais sur un
    type de valeur donné *)
Parameter check_binop : binop -> type -> type -> bool.
Conjecture check_binop_correct :
  forall op ty1 ty2,
    check_binop op ty1 ty2 = true ->
    forall v1 v2, wt_value v1 ty1 ->
             wt_value v2 ty2 ->
             sem_binop op v1 ty1 v2 ty2 <> None.

(* true -> cannot fail
 * false -> we don't know *)
Fixpoint check_exp (e : exp) : bool :=
  match e with
  | Econst _ => true
  | Eenum _ _ => false (* TODO ?! *)
  | Evar _ _ => true
  | Elast _ _ => false (* restr *)
  | Eunop op e ann =>
      match typeof e with
      | [ty] => check_unop op ty && check_exp e
      | _ => false
      end
  | Ebinop op e1 e2 ann =>
      match typeof e1, typeof e2 with
      | [ty1], [ty2] => check_binop op ty1 ty2 && check_exp e1 && check_exp e2
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

Theorem check_exp_correct :
  forall G ins envG envI bs env,
  forall e, check_exp e = true ->
       op_correct_exp G ins envG envI bs env e.
Proof.
  intros *.
  induction e using exp_ind2; simpl; intro Hchk; try congruence.
  - (* Econst *)
    constructor.
  - (* Evar *)
    constructor.
  - (* Eunop *)
    destruct (typeof e) as [|ty []] eqn:Hty; try congruence.
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
    destruct (typeof e1) as [|ty1 []] eqn:Hty1, (typeof e2) as [|ty2 []] eqn:Hty2; try congruence.
    apply andb_prop in Hchk as [FF1 F3].
    apply andb_prop in FF1 as [F1 F2].
    constructor; auto.
    (* c'est très très simple *)
    intros ty1' ty2' Hty1' Hty2'.
    rewrite Hty1' in Hty1; inv Hty1.
    rewrite Hty2' in Hty2; inv Hty2.
    intros ss1 ss2.
    apply DSForall_all.
    intros [[|v1|] [|v2|]]; auto.
    intros Wt1 Wt2.
    now apply check_binop_correct.
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
  - (* Ecase *)
    destruct d; simpl in H0.
    + apply andb_prop in Hchk as [F1 F3].
      apply andb_prop in F1 as [F1 F2].
      apply forallb_Forall in F2,F3.
      constructor; simpl_Forall; auto.
      eapply forallb_Forall, Forall_forall in F2; eauto.
    + apply andb_prop in Hchk as [F1 F2].
      apply forallb_Forall in F2.
      constructor; simpl_Forall; auto.
      eapply forallb_Forall, Forall_forall in F2; eauto.
  - (* Eapp *)
    apply andb_prop in Hchk as [F1 F2].
    apply forallb_Forall in F1, F2.
    constructor; simpl_Forall; auto.
Qed.

End TEST1.

End CHECKOP.
