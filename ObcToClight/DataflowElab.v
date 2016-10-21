Require Import Rustre.Common.
Require Import Rustre.Operators.

Require Import Rustre.Dataflow.
Require Import Rustre.Dataflow.Parser.Ast.

Require Import Rustre.ObcToClight.Interface.
Require Import Rustre.Ident.

Module Export OpAux := OperatorsAux Interface.Op.
Module Export Syn := SyntaxFun Ident.Ids Interface.Op.

Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Require Import compcert.common.Errors.
Local Open Scope error_monad_scope.

(* Elaborate an AST into a well-typed Dataflow program. *)

(* TODO: Should we just elaborate the constants in Lexer.mll ? *)

(* CompCert: cparser/Elab: elab_int_constant + cfrontend/C2C: convertIkind *)
Parameter elab_const_int : astloc -> string -> constant.
(* CompCert: cparser/Elab: elab_float_constant + cfrontend/C2C: convertIkind *)
Parameter elab_const_float : floatInfo -> constant.
(* CompCert: cparser/Elab: elab_char_constant + cfrontend/C2C: convertIkind *)
Parameter elab_const_char : astloc -> bool -> list char_code -> constant.

(* TODO: How to integrate with pos_of_str? *)
(* TODO: Should we just turn identifiers into positives in Lexer.mll? *)
Parameter ident_of_string : string -> ident.
Parameter string_of_astloc : astloc -> String.string.

Definition err_loc (loc: astloc) (m: errmsg) :=
  MSG (string_of_astloc loc) :: MSG ": " :: m.  

Module Type ELABORATION
       (Import Ids    : IDS)
       (Import Op     : OPERATORS)
       (Import OpAux  : OPERATORS_AUX Op)
       (Import Syn    : SYNTAX Ids Op)
       (Import Typing : TYPING Ids Op Syn).

  Definition elab_constant (loc: astloc) (c: Ast.constant) : constant :=
    match c with
    | CONST_BOOL false  => Cint Integers.Int.zero Ctypes.IBool Ctypes.Signed
    | CONST_BOOL true   => Cint Integers.Int.one Ctypes.IBool Ctypes.Signed
    | CONST_INT s       => elab_const_int loc s
    | CONST_FLOAT fi    => elab_const_float fi
    | CONST_CHAR wide l => elab_const_char loc wide l
    end.

  Section ElabExpressions.

    Variable env : PM.t type.

    Definition has_type (x: ident) (ty: type) : bool :=
      match PM.find x env with
      | Some ty' => ty ==b ty'
      | None => false
      end.

    Fixpoint elab_clock (loc: astloc) (ck: Ast.clock) : res clock :=
      match ck with
      | BASE => OK Cbase
      | ON ck' b xs =>
        let x := ident_of_string xs in
        if has_type x bool_type then
          do ck' <- elab_clock loc ck';
             OK (Con ck' x b)
        else Error (err_loc loc
                       (CTX x :: msg " in clock is not declared as bool."))
      end.

  End ElabExpressions.

  Lemma has_type_In:
    forall env x ty,
      has_type env x ty = true ->
      In (x, ty) (PM.elements env).
  Proof.
    intros env x ty Hhty.
    unfold has_type in Hhty.
    destruct (PM.find x env) eqn:Hfind; try discriminate.
    rewrite equiv_decb_equiv in Hhty.
    rewrite <-Hhty in Hfind.
    now apply PM.elements_correct in Hfind.
  Qed.
    
  Lemma wt_elab_clock:
    forall env loc ast_ck ck,
      elab_clock env loc ast_ck = OK ck ->
      wt_clock (PM.elements env) ck.
  Proof.
    induction ast_ck as [|ack IH]; simpl.
    now injection 1; intro; subst; auto with dftyping.
    destruct (has_type env (ident_of_string s) bool_type) eqn:Hstr.
    2:discriminate 1.
    intros ck Helab.
    monadInv Helab.
    constructor; auto.
    apply has_type_In with (1:=Hstr).
  Qed.
    

End ELABORATION.
