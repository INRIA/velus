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

Require compcert.cfrontend.Cop.

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
       (Import OpAux  : OPERATORS_AUX Interface.Op)
       (Import Syn    : SYNTAX Ids Interface.Op)
       (Import Typing : TYPING Ids Interface.Op Syn).

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

    Definition find_type (loc: astloc) (x: ident) : res type :=
      match PM.find x env with
      | None => Error (err_loc loc (CTX x :: msg " is not declared."))
      | Some ty => OK ty
      end.

    Definition assert_type (loc: astloc) (x: ident) (ty: type) : res unit :=
      do xty <- find_type loc x;
         if xty ==b ty then OK tt
         else Error (err_loc loc
                      (CTX x :: MSG " has type " :: MSG (string_of_type xty)
                             :: MSG " but type " :: MSG (string_of_type ty)
                             :: MSG " was expected." :: nil)).

    Fixpoint elab_clock (loc: astloc) (ck: Ast.clock) : res clock :=
      match ck with
      | BASE => OK Cbase
      | ON ck' b sx =>
        let x := ident_of_string sx in
        do ok <- assert_type loc x bool_type;
        do ck' <- elab_clock loc ck';
           OK (Con ck' x b)
      end.

    Definition elab_unop (op: Ast.unary_operator) : unop :=
      match op with
      | MINUS => UnaryOp Cop.Oneg
      | NOT   => UnaryOp Cop.Onotint
      | BNOT  => UnaryOp Cop.Onotbool
      end.

    Definition elab_binop (op: Ast.binary_operator) : binop :=
      match op with
      | ADD  => Cop.Oadd
      | SUB  => Cop.Osub
      | MUL  => Cop.Omul
      | DIV  => Cop.Odiv
      | MOD  => Cop.Omod
      | BAND => Cop.Oand
      | BOR  => Cop.Oor
      | LAND => Cop.Oand
      | LOR  => Cop.Oor
      | XOR  => Cop.Oxor
      | LSL  => Cop.Oshl
      | LSR  => Cop.Oshr
      | EQ   => Cop.Oeq
      | NE   => Cop.One
      | LT   => Cop.Olt
      | GT   => Cop.Ogt
      | LE   => Cop.Ole
      | GE   => Cop.Oge
      end.

    (* TODO: fix type_unop' to match completely *)
    Definition find_type_unop (loc: astloc) (op: unop) (ty: type) : res type :=
      match type_unop' op ty with
      | None => Error (err_loc loc (msg "wrong operator argument type"))
      | Some ty' => OK ty'
      end.

    Definition find_type_binop (loc: astloc) (op: binop)
                                             (ty1 ty2: type) : res type :=
      match type_binop' op ty1 ty2 with
      | None => Error (err_loc loc (msg "wrong operator argument type"))
      | Some ty' => OK ty'
      end.

    Definition elab_type (loc: astloc) (ty: Ast.type_name) : type' :=
      match ty with
      | Tint8    => Tint Ctypes.I8  Ctypes.Signed
      | Tuint8   => Tint Ctypes.I8  Ctypes.Unsigned
      | Tint16   => Tint Ctypes.I16 Ctypes.Signed
      | Tuint16  => Tint Ctypes.I16 Ctypes.Unsigned
      | Tint32   => Tint Ctypes.I32 Ctypes.Signed
      | Tuint32  => Tint Ctypes.I32 Ctypes.Unsigned
      | Tint64   => Tlong Ctypes.Signed
      | Tuint64  => Tlong Ctypes.Unsigned
      | Tfloat32 => Tfloat Ctypes.F32
      | Tfloat64 => Tfloat Ctypes.F64
      | Tbool    => Tint Ctypes.IBool Ctypes.Signed
      end.
    
    Fixpoint elab_lexp (ae: Ast.expression) : res lexp :=
      match ae with
      | CONSTANT c loc => OK (Econst (elab_constant loc c))
      | VARIABLE sx loc =>
          let x := ident_of_string sx in
          do ty <- find_type loc x;
          OK (Evar x ty)
      | WHEN ae' b sx loc =>
          let x := ident_of_string sx in
          do ok <- assert_type loc x bool_type;
          do e' <- elab_lexp ae';
          OK (Ewhen e' x b)
      | UNARY aop ae' loc =>
          let op := elab_unop aop in
          do e' <- elab_lexp ae';
          do ty' <- find_type_unop loc op (typeof e');
          OK (Eunop op e' ty')
      | CAST aty' ae' loc =>
          let ty' := elab_type loc aty' in
          do e' <- elab_lexp ae';
          OK (Eunop (CastOp ty') e' ty')
      | BINARY aop ae1 ae2 loc =>
          let op := elab_binop aop in
          do e1 <- elab_lexp ae1;
          do e2 <- elab_lexp ae2;
          do ty' <- find_type_binop loc op (typeof e1) (typeof e2);
          OK (Ebinop op e1 e2 ty')
      | _ => Error (err_loc (expression_loc ae) (msg "expression not normalized"))
      end.

  End ElabExpressions.

  Lemma find_type_In:
    forall env loc x ty,
      find_type env loc x = OK ty ->
      In (x, ty) (PM.elements env).
  Proof.
    intros ** Hfty.
    unfold find_type in Hfty.
    destruct (PM.find x env) eqn:Hfind; try discriminate.
    injection Hfty; intro; subst.
    now apply PM.elements_correct in Hfind.
  Qed.
  
  Lemma assert_type_In:
    forall env loc x ty y,
      assert_type env loc x ty = OK y ->
      In (x, ty) (PM.elements env).
  Proof.
    intros env loc x ty y Hhty.
    unfold assert_type in Hhty.
    monadInv Hhty.
    destruct (x0 ==b ty) eqn:Heq.
    2:discriminate EQ0.
    rewrite equiv_decb_equiv in Heq.
    rewrite Heq in *.
    eauto using find_type_In.
  Qed.
    
  Lemma wt_elab_clock:
    forall env loc ack ck,
      elab_clock env loc ack = OK ck ->
      wt_clock (PM.elements env) ck.
  Proof.
    induction ack as [|ack IH]; simpl.
    now injection 1; intro; subst; auto with dftyping.
    intros ck Helab.
    monadInv Helab.
    constructor; auto.
    apply assert_type_In with (1:=EQ).
  Qed.

  Lemma wt_elab_lexp:
    forall env ae e,
      elab_lexp env ae = OK e ->
      wt_lexp (PM.elements env) e.
  Proof.
    induction ae; intros e Helab; monadInv Helab; constructor;
      eauto using find_type_In, assert_type_In.
    - unfold find_type_unop in EQ1.
      rewrite type_unop'_correct in EQ1.
      now DestructCases.
    - unfold find_type_binop in EQ0.
      match goal with H:match ?e with _ => _ end = _ |- _ =>
        destruct e eqn:He; try discriminate; injection H end.
      intro; subst.
      now rewrite type_binop'_correct in He.
    - now rewrite type_castop.
  Qed.

End ELABORATION.



