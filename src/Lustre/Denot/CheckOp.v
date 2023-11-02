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



(* Analyse qui gère les opérateurs binaires aux arguments droits constants *)
Module TEST1ETDEMI.

(* pour les unop on fait comme dans l'analyse simple *)
Parameter check_unop : unop -> type -> bool.
Conjecture check_unop_correct :
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
Parameter check_binop_val : binop -> type -> value -> type -> bool.
Conjecture check_binop_val_correct :
  forall op ty1 v2 ty2,
    check_binop_val op ty1 v2 ty2 = true ->
    forall v1, wt_value v1 ty1 ->
          wt_value v2 ty2 ->
          sem_binop op v1 ty1 v2 ty2 <> None.


(* second cas *)
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
  | Eenum _ _ => false (* TODO ?! *)
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
    destruct (typeof e1) as [|ty1 []] eqn:Hty1; try (cases; congruence).
    constructor.
    (* récurrence pour e1, e2 *)
    1,2: cases; repeat rewrite Bool.andb_true_iff in *; tauto.
    intros ty1' ty2' Hty1' Hty2' ss1 ss2.
    rewrite Hty1' in Hty1; inv Hty1.
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
    (* autre cas *)
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

End TEST1ETDEMI.


(* Analyse plus précise, mais qui risque d'être très compliquée *)
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


(* true => ok, false => échoue, cf. TEST1 *)
Parameter check_unop_any : unop -> type -> bool.

Conjecture check_unop_any_correct :
  forall op ty,
    check_unop_any op ty = true ->
    forall v, wt_value v ty ->
         sem_unop op v ty <> None.

(* Some v => résultat, None => échoue *)
Definition check_unop_val : unop -> value -> type -> option value := sem_unop.

Definition check_unop op r ty :=
  match r with
  | Any => if check_unop_any op ty then Any else Err
  | Val v => match check_unop_val op v ty with
            | Some v' => Val v'
            | None => Err
            end
  | Err => Err
  end.

(* Conjecture check_unop_val_spec : *)
(*   forall op v ty, match check_unop_val op v ty with *)
(*              | Val v' => sem_unop op v ty = Some v' *)
(*              | Any => forall v, wt_value v ty ->  *)
(*              end. *)

(* Conjecture check_unop_correct : *)
(*   forall op r ty, *)
(*     check_unop op r ty <> Err -> *)
(*     match r with *)
(*     | Val v => sem_unop op v ty <> None *)
(*     | _ =>  forall v, wt_value v ty -> *)
(*                 sem_unop op v ty <> None *)
(*     end. *)

Parameter check_binop : binop -> res -> type -> res -> type -> res.

Fixpoint check_exp (e : exp) : list res :=
  match e with
  | Econst c => [ Val (Vscalar (sem_cconst c)) ]
  | Eenum _ _ => [ Err ] (* TODO ?? *)
  | Evar _ _ => [ Err ]
  | Elast _ _ => [ Err ] (* restr *)
  | Eunop op e ann =>
      match typeof e with
      | [ty] =>
          match check_exp e with
          | [ r ] => [ check_unop op r ty ]
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


(*XXXXXXXXXXX pris dans Safe.v  *)
Definition ty_DS (ty : type) (s : DS (sampl value)) : Prop :=
  DSForall_pres (fun v => wt_value v ty) s.
Definition safe_op {A} : DS (sampl A) -> Prop :=
  DSForall (fun v => match v with err error_Op => False | _ => True end).
Lemma safe_op_sunop :
  forall op s tye,
    safe_op s ->
    DSForall_pres (fun v => sem_unop op v tye <> None) s ->
    safe_op (sunop (fun v => sem_unop op v tye) s).
Admitted.
(* XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX *)


Theorem check_exp_approx :
  forall G ins envG envI bs env,
  forall e,
    Forall2
      (fun r s => match r with
               | Any => safe_op s (* /\ ty_DS (typeof e) s *)
               | Val v => DSForall_pres (fun v' => v' = v) s
               | Err => True
               end)
      (check_exp e)
      (list_of_nprod (denot_exp G ins e envG envI bs env)).
Proof.
  intros *.
  induction e using exp_ind2.
  - (* Econst *)
    constructor; auto.
    rewrite denot_exp_eq.
    unfold DSForall_pres, sconst.
    apply DSForall_map, DSForall_all.
    intro; cases_eqn HH.
  - (* Eenum *)
    constructor; auto.
  - (* Evar *)
    (* TODO: plus de boulôt ici si on veut supposer Any *)
    constructor; auto.
  - (* Elast *)
    constructor; auto.
  - (* Eunop *)
    rewrite denot_exp_eq.
    revert IHe.
    gen_sub_exps.
    destruct (numstreams e) as [|[]] eqn:HH; intros; simpl.
    1,3: cases_eqn HH; apply Forall2_length in IHe;
      rewrite list_of_nprod_length in IHe; simpl in IHe; lia.
    destruct (typeof e) as [|ty []].
    1,3: constructor; auto.
    inv IHe; inv H3.
    constructor; auto.
    repeat (cases_eqn HH; simpl in *; subst); try congruence.
    + (* c'est très très simple *)
      apply safe_op_sunop; auto.
      apply DSForall_all; intros [| v |]; auto.
      (* intro Wtv. *)
      apply check_unop_any_correct; auto.
Abort.


Theorem check_exp_correct :
  forall G ins envG envI bs env,
  forall e, Forall (fun v => v <> Err) (check_exp e) ->
       op_correct_exp G ins envG envI bs env e.
Proof.
  intros *.
  induction e using exp_ind2; simpl; intro Hchk; try now inv Hchk.
  - (* Econst *)
    constructor.
  - (* Eunop *)
    destruct (typeof e) as [|ty []] eqn:Hty; try now inv Hchk.
    destruct (check_exp e) as [|v []] eqn:Hv; try now inv Hchk.
    inv Hchk.
    constructor.
    + apply IHe; constructor; auto.
    (*   intro; subst; rewrite check_unop_err in *; contradiction. *)
    (* + intros ty' Hty'. *)
    (*   apply check_unop_correct in H1. *)
    (*   apply nprod_forall_Forall, Forall_forall. *)
    (*   intros s Hin. *)
    (*   apply andb_prop in Hchk as [F1 F2]. *)
    (* constructor; auto. *)
    (* intros ty' Hty'. *)
    (* rewrite Hty' in Hty; inv Hty. *)
    (* (* c'est très très simple *) *)
    (* apply nprod_forall_Forall, Forall_forall. *)
    (* intros s Hin. *)
(* Qed. *)
Abort.

End TEST2.

End CHECKOP.
