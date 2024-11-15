From Coq Require Import Datatypes List.
Import List.ListNotations.

From Velus Require Import Common.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Lustre.StaticEnv.
From Velus Require Import Lustre.LSyntax Lustre.LTyping.

(** * Little static analysis to decide [OpErr.no_rte] *)

(* we keep it outside of [OpErr], otherwise the extraction of [check_global]
 * recursively extracts the CPO library (because of functors...) *)

Module Type CHECKOP
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks   : CLOCKS        Ids Op OpAux)
       (Import Senv  : STATICENV     Ids Op OpAux Cks)
       (Import Syn   : LSYNTAX       Ids Op OpAux Cks Senv).

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
      | [ty] => check_unop op None ty && check_exp e
      | _ => true
      end
  | Ebinop op e1 (Econst c) ann =>
      let ty2 := Tprimitive (ctype_cconst c) in
      match typeof e1 with
      | [ty1] => check_exp e1
                (* soit on arrive à décider avec la valeur c,
                   soit on vérifie pour toute valeur de type ty2 *)
                && (check_binop op None ty1 (Some (Vscalar (sem_cconst c))) ty2
                    || check_binop op None ty1 None ty2)
      | _ => true
      end
  | Ebinop op e1 e2 ann =>
      match typeof e1, typeof e2 with
      | [ty1], [ty2] => check_binop op None ty1 None ty2 && check_exp e1 && check_exp e2
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

Definition check_node {PSyn Prefs} (n : @node PSyn Prefs) :=
  check_top_block (n_block n).

Definition check_global {PSyn Prefs} (G : @global PSyn Prefs) :=
  forallb check_node (nodes G).


End CHECKOP.

Module CheckOpFun
  (Ids   : IDS)
  (Op    : OPERATORS)
  (OpAux : OPERATORS_AUX Ids Op)
  (Cks   : CLOCKS        Ids Op OpAux)
  (Senv  : STATICENV     Ids Op OpAux Cks)
  (Syn   : LSYNTAX       Ids Op OpAux Cks Senv)
<: CHECKOP Ids Op OpAux Cks Senv Syn.
  Include CHECKOP Ids Op OpAux Cks Senv Syn.
End CheckOpFun.
