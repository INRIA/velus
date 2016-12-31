Require Import Velus.Common.
Require Instantiator.

Require Import Velus.Lustre.Parser.LustreAst.
Require Import Operators.
Require Import Clocks.

Module Import Clks := Instantiator.Clks.
Module Import Syn := Instantiator.NL.Syn.
Module Import Defs := Instantiator.NL.IsD.

Import Interface.Op.
Import Instantiator.OpAux.
Import Instantiator.NL.Typ.
Import Instantiator.NL.Clo.

Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Require cfrontend.Cop.
Require cparser.Cabs.

Import Permutation.

Require Import common.Errors.
Local Open Scope error_monad_scope.

(* Elaborate an AST into a well-typed NLustre program. *)

(**
  Lexing and parsing gives a list of LustreAst declarations. Elaboration
  transforms them into NLustre declarations, whilst simultaneously ensuring
  that the resulting program is well-typed and well-clocked. Several other
  well-formedness requirements (node invariants) are also checked.

  The type and clock checking is done during elaboration for two reasons:

  - Source file location information is needed for error messages but is
    not present in the NLustre AST.

  - The NLustre AST requires type and clock annotations.

  Types and clocks are checked simultaneously. Doing both in one pass is not
  only more efficient, it also simplifies the proofs.

  Node declarations are first elaborated to produce a map from each identifier
  to its declared type and clock. A PositiveMap is used for efficiency during
  checking, but the declarations are maintained in lists as their order is
  significant. The related proofs use permutations and rewriting to switch
  between the two representations. The declaration map is then used as an
  environment for checking and annotating equations and expressions.

  The elaboration of definitions is performed by [elab_var_decls]. Multiple
  passes may be required for a list of declarations because clocks may be
  dependent on other declared variables. For example,
<<
    a : bool;
    b : bool when c;
    c : bool when a;
>>
  The function must detect and reject cyclic definitions. For example,
<<
    a : bool;
    b : bool when c;
    c : bool when b;
>>
  We pass the original list of declarations as a `fuel' argument to
  convince Coq that the function terminates. It would be possible to detect
  cyclic definitions sooner (the pass completes without treating any
  definitions), but we do not bother since this is an abnormal case.

  While the worst-case complexity of this function is not great (O(n^2)),
  you have to work pretty hard to hit (`concertina'-ed inter-dependent
  declarations), and the typical case (declarations in order of their
  dependencies) is linear.

  The [elab_var_decls] function builds the map in three cumulative steps:
  first inputs, then outputs, then locals. This is done to ensure that input
  clocks are only dependent on other inputs and that output clocks are only
  dependent on inputs or other outputs. This requirement is not yet needed as
  an invariant; possibly because we do not currently support clocked inputs
  and outputs.

 *)

Parameter elab_const_int : Cabs.cabsloc -> string -> constant.
Parameter elab_const_float : Cabs.floatInfo -> constant.
Parameter elab_const_char : Cabs.cabsloc -> bool -> list char_code -> constant.

(* CompCert: lib/Camlcoq.ml: camlstring_of_coqstring and coqstring_of_camlstring
   using Require ExtrOCamlString in the extraction file to extract Coq
   strings as an OCaml "char list". Then use the Ident.pos_of_string
   function.
   TODO: In the long run, we should try to use OCaml strings everywhere. *)
Parameter string_of_astloc : astloc -> String.string.
Parameter cabsloc_of_astloc : astloc -> Cabs.cabsloc.
Parameter cabs_floatinfo : LustreAst.floatInfo -> Cabs.floatInfo.

Definition err_loc (loc: astloc) (m: errmsg) :=
  MSG (string_of_astloc loc) :: MSG ":" :: m.

(* TODO: move elsewhere *)
Instance clock_EqDec : EqDec clock eq.
Proof.
  intros ck1 ck2. compute. change (ck1 = ck2 -> False) with (ck1 <> ck2).
  repeat decide equality.
Qed.

Local Ltac NamedDestructCases :=
  repeat progress
         match goal with
         | H:match ?e with _ => _ end = OK _ |- _ =>
           let Heq := fresh "Heq" in
           destruct e eqn:Heq; try discriminate
         | H:OK _ = OK _ |- _ => injection H; clear H; intro; subst
         end.

Definition cast_constant (loc: astloc) (c: constant) (ty: type')
                                                             : res constant :=
  match Cop.sem_cast (sem_const c) (cltype (type_const c))
                     (cltype ty) Memory.Mem.empty, ty with
  | Some (Values.Vint v),    Tint sz sg        => OK (Cint v sz sg)
  | Some (Values.Vlong v),   Tlong sg          => OK (Clong v sg)
  | Some (Values.Vfloat f),  Tfloat Ctypes.F64 => OK (Cfloat f)
  | Some (Values.Vsingle f), Tfloat Ctypes.F32 => OK (Csingle f)
  | _, _ => Error (err_loc loc (msg "failed cast of constant"))
  end.

Definition elab_constant (loc: astloc) (c: LustreAst.constant) : constant :=
  match c with
  | CONST_BOOL false  => Cint Integers.Int.zero Ctypes.IBool Ctypes.Signed
  | CONST_BOOL true   => Cint Integers.Int.one Ctypes.IBool Ctypes.Signed
  | CONST_INT s       => elab_const_int (cabsloc_of_astloc loc) s
  | CONST_FLOAT fi    => elab_const_float (cabs_floatinfo fi)
  | CONST_CHAR wide l => elab_const_char (cabsloc_of_astloc loc) wide l
  end.

Definition Is_interface_map (G: global)
           (nenv: PM.t (list type * list type)) : Prop :=
  (forall f tysin tysout,
      PM.find f nenv = Some (tysin, tysout) ->
      (exists n, find_node f G = Some n
                 /\ Forall2 (fun xtc ty=> dty xtc = ty) n.(n_in) tysin
                 /\ Forall2 (fun xtc ty=> dty xtc = ty) n.(n_out) tysout))
  /\ (forall f, PM.find f nenv = None -> Forall (fun n=> f <> n.(n_name)) G).

Lemma Is_interface_map_empty:
  Is_interface_map [] (PM.empty (list type * list type)).
Proof.
  split; setoid_rewrite PM.gempty; intros; try discriminate; auto.
Qed.    

Definition msg_of_types (ty ty': type) : errmsg :=
  MSG "expected '" :: MSG (string_of_type ty)
      :: MSG "' but got '" :: MSG (string_of_type ty') :: msg "'".

Fixpoint msg_of_clock (ck: clock) : errmsg :=
  match ck with
  | Cbase          => msg "."
  | Con ck x true  => msg_of_clock ck ++ MSG " on " :: CTX x :: nil
  | Con ck x false => msg_of_clock ck ++ MSG " onot " :: CTX x :: nil
  end.

Fixpoint msg_ident_list (xs: list ident) :=
  match xs with
  | [] => []
  | [x] => [CTX x]
  | x::xs => CTX x :: MSG ", " :: msg_ident_list xs
  end.

Definition msg_of_clocks (ck ck': clock) : errmsg :=
  MSG "expected '" :: msg_of_clock ck
      ++ MSG "' but got '" :: msg_of_clock ck' ++ msg "'".

Section ElabExpressions.

  (* Map variable names to their types and clocks. *)
  Variable env : PM.t (type * clock).

  (* Preceding dataflow program. *)
  Variable G : global.

  (* Map node names to input and output types. *)
  Variable nenv : PM.t (list type * list type).

  Hypothesis wt_cenv :
    forall x ty ck, PM.find x env = Some (ty, ck) ->
                    wt_clock (idty (PM.elements env)) ck.

  Hypothesis wt_nenv : Is_interface_map G nenv.

  Definition find_var (loc: astloc) (x: ident) : res (type * clock) :=
    match PM.find x env with
    | None => Error (err_loc loc (CTX x :: msg " is not declared."))
    | Some tc => OK tc
    end.

  Definition assert_type (loc: astloc) (x: ident) (xty ty: type) : res unit :=
    if xty ==b ty then OK tt
    else Error (err_loc loc (CTX x :: MSG ": " :: msg_of_types xty ty)).
  
  Definition assert_clock (loc: astloc) (x: ident) (xck ck: clock) : res unit :=
    if xck ==b ck then OK tt
    else Error (err_loc loc
                        ((CTX x :: MSG " has clock '" :: msg_of_clock xck)
                                ++ MSG "' but clock '" :: msg_of_clock ck
                                ++ msg "' was expected.")).
  
  Definition find_node_interface (loc: astloc) (f: ident)
    : res (list type * list type) :=
    match PM.find f nenv with
    | None => Error (err_loc loc (MSG "node " :: CTX f :: msg " not found."))
    | Some tys => OK tys
    end.

  Lemma wt_clock_find_var:
    forall loc x ty ck,
      find_var loc x = OK (ty, ck) -> wt_clock (idty (PM.elements env)) ck.
  Proof.
    intros ** Hfind.
    apply wt_cenv with (x:=x) (ty:=ty).
    unfold find_var in Hfind.
    destruct (PM.find x env); try discriminate.
    now monadInv Hfind.
  Qed.

  Lemma find_var_in:
    forall loc x ty ck,
      find_var loc x = OK (ty, ck) ->
      In (x, (ty, ck)) (PM.elements env).
  Proof.
    unfold find_var.
    intros loc x ty ck Hfind.
    NamedDestructCases.
    apply PM.elements_correct with (1:=Heq).
  Qed.

  Lemma find_var_type:
    forall loc x ty ck,
      find_var loc x = OK (ty, ck) ->
      In (x, ty) (idty (PM.elements env)).
  Proof.
    intros ** Hfind.
    apply find_var_in in Hfind.
    now apply In_idty_exists; exists ck.
  Qed.

  Lemma find_var_clock:
    forall loc x ty ck,
      find_var loc x = OK (ty, ck) ->
      In (x, ck) (idck (PM.elements env)).
  Proof.
    intros ** Hfind.
    apply find_var_in in Hfind.
    now apply In_idck_exists; exists ty.
  Qed.

  Definition elab_unop (op: LustreAst.unary_operator) : unop :=
    match op with
    | MINUS => UnaryOp Cop.Oneg
    | NOT   => UnaryOp Cop.Onotint
    | BNOT  => UnaryOp Cop.Onotbool
    end.

  Definition elab_binop (op: LustreAst.binary_operator) : binop :=
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

  Definition elab_type (ty: LustreAst.type_name) : type' :=
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

  Fixpoint elab_lexp (ae: LustreAst.expression) : res (lexp * clock) :=
    match ae with
    | CONSTANT c loc => OK (Econst (elab_constant loc c), Cbase)
    | VARIABLE x loc =>
      do (ty, ck) <- find_var loc x;
      OK (Evar x ty, ck)
    | WHEN ae' b x loc =>
      do (xty, xck) <- find_var loc x;
      do ok <- assert_type loc x xty bool_type;
      do (e', eck) <- elab_lexp ae';
      if eck ==b xck then OK (Ewhen e' x b, Con xck x b)
      else Error (err_loc loc (MSG "badly clocked when: "
                                   :: msg_of_clocks eck xck))
    | UNARY aop ae' loc =>
      let op := elab_unop aop in
      do (e', ck) <- elab_lexp ae';
      do ty' <- find_type_unop loc op (typeof e');
      OK (Eunop op e' ty', ck)
    | CAST aty' ae' loc =>
      let ty' := elab_type aty' in
      do (e', ck) <- elab_lexp ae';
      OK (Eunop (CastOp ty') e' ty', ck)
    | BINARY aop ae1 ae2 loc =>
      let op := elab_binop aop in
      do (e1, ck1) <- elab_lexp ae1;
      do (e2, ck2) <- elab_lexp ae2;
      do ty' <- find_type_binop loc op (typeof e1) (typeof e2);
      if ck1 ==b ck2 then OK (Ebinop op e1 e2 ty', ck1)
      else Error (err_loc loc (MSG "badly clocked operator: "
                                   :: msg_of_clocks ck1 ck2))
    | _ => Error (err_loc (expression_loc ae) (msg "expression not normalized"))
    end.

  Fixpoint elab_cexp (ae: LustreAst.expression) : res (cexp * clock) :=
    match ae with
    | MERGE x aet aef loc =>
      do (xty, xck) <- find_var loc x;
      do ok <- assert_type loc x xty bool_type;
      do (et, ckt) <- elab_cexp aet;
      do (ef, ckf) <- elab_cexp aef;
      if typeofc et ==b typeofc ef
      then if (ckt ==b (Con xck x true))
           then if (ckf ==b (Con xck x false))
                then OK (Emerge x et ef, xck)
                else Error (err_loc loc (MSG "badly clocked merge false branch: "
                                         :: msg_of_clocks (Con xck x false) ckf))
           else Error (err_loc loc (MSG "badly clocked merge true branch: "
                                        :: msg_of_clocks (Con xck x true) ckt))
      else Error (err_loc loc (msg "badly typed merge"))
    | IFTE ae aet aef loc =>
      do (e, ck) <- elab_lexp ae;
      do (et, ckt) <- elab_cexp aet;
      do (ef, ckf) <- elab_cexp aef;
      if (typeof e ==b bool_type) && (typeofc et ==b typeofc ef)
      then if (ckt ==b ck)
           then if (ckf ==b ck)
                then OK (Eite e et ef, ck)
                else Error (err_loc loc (MSG "badly clocked ifte false branch: "
                                             :: msg_of_clocks ck ckf))
           else Error (err_loc loc (MSG "badly clocked ifte true branch: "
                                        :: msg_of_clocks ck ckt))
      else Error (err_loc loc (msg "badly typed if/then/else"))
    | _ =>
      do (e, ck) <- elab_lexp ae;
      OK (Eexp e, ck)
    end.  
  
  Definition assert_lexp_type (loc: astloc) (e: lexp) (ty: type) : res unit :=
    if typeof e ==b ty then OK tt
    else Error (err_loc loc (MSG "badly typed argument: "
                                 :: msg_of_types ty (typeof e))).

  Fixpoint elab_lexps (loc: astloc) (ck': clock) (aes: list expression)
                      (tys: list type)
    : res (list lexp) :=
    match aes, tys with
    | nil, nil => OK nil
    | ae::aes, ty::tys =>
      do (e, ck) <- elab_lexp ae;
      if ck ==b ck'
      then do ok <- assert_lexp_type (expression_loc ae) e ty;
           do es <- elab_lexps loc ck' aes tys;
           OK (e::es)
      else Error (err_loc loc ((MSG "ill-clocked argument expression "
                                    :: msg_of_clocks ck ck')))
    | _, _ => Error (err_loc loc (msg "wrong number of arguments"))
    end.

  Fixpoint check_result_list (loc: astloc) (ck: clock)
                                           (xs: list ident) (tys: list type)
                                                                : res PS.t :=
    match xs, tys with
    | nil, nil => OK PS.empty
    | x::xs, ty::tys => do (xty, xck) <- find_var loc x;
                        do ok <- assert_type loc x xty ty;
                        do ok <- assert_clock loc x xck ck;
                        do others <- check_result_list loc ck xs tys;
                        if PS.mem x others
                        then Error (err_loc loc
                                         (msg "duplicate variable in pattern"))

                        else OK (PS.add x others)
    | _, _ => Error (err_loc loc (msg "wrong number of pattern variables"))
    end.

  Definition elab_constant_with_cast (loc: astloc) (ae: LustreAst.expression)
                                                              : res constant :=
    match ae with
    | CAST aty (CONSTANT ac _) loc =>
      cast_constant loc (elab_constant loc ac) (elab_type aty)
    | CONSTANT ac loc =>
      OK (elab_constant loc ac)
    | _ => Error (err_loc loc (msg "fbys only take (casted) constants at left."))
    end.

  Definition elab_equation (aeq: LustreAst.equation) : res equation :=
    let '(xs, ae, loc) := aeq in
    do x <- match xs with
            | x::xs => OK x
            | _ => Error (err_loc loc (msg "at least one output is required"))
            end;
    do (xty, xck) <- find_var loc x;
    match ae with
    | CALL f aes loc =>
      do (tysin, tysout) <- find_node_interface loc f;
      do es <- elab_lexps loc xck aes tysin;
      do ok <- check_result_list loc xck xs tysout;
      OK (EqApp xs xck f es)
           
    | FBY ae0 ae loc =>
      do v0 <- elab_constant_with_cast loc ae0;
      let v0ty := type_const v0 in
      do (e, eck) <- elab_lexp ae;
      do ok <- assert_type loc x xty v0ty;
      if typeof e ==b v0ty
      then if eck ==b xck
           then OK (EqFby x xck v0 e)
           else Error (err_loc loc (MSG "ill-clocked fby expression for "
                                        :: CTX x :: msg_of_clocks xck eck))
      else Error (err_loc loc (MSG "ill-typed fby expression for "
                                   :: CTX x :: msg_of_types v0ty (typeof e)))

    | _ =>
      do (e, eck) <- elab_cexp ae;
      do ok <- assert_type loc x xty (typeofc e);
      if eck ==b xck
      then OK (EqDef x xck e)
      else Error (err_loc loc (MSG "ill-clocked expression for "
                                   :: CTX x :: msg_of_clocks xck eck))
    end.
  
  (** Properties *)

  Lemma assert_type_eq:
    forall loc x xty ty r,
      assert_type loc x xty ty = OK r ->
      xty = ty.
  Proof.
    unfold assert_type.
    intros. NamedDestructCases.
    rewrite equiv_decb_equiv in Heq.
    now rewrite Heq.
  Qed.

  Lemma assert_clock_eq:
    forall loc x xck ck r,
      assert_clock loc x xck ck = OK r ->
      xck = ck.
  Proof.
    unfold assert_clock.
    intros. NamedDestructCases.
    rewrite equiv_decb_equiv in Heq.
    now rewrite Heq.
  Qed.

  Lemma wt_elab_lexp:
    forall ae e ck,
      elab_lexp ae = OK (e, ck) ->
      wt_lexp (idty (PM.elements env)) e.
  Proof.
    induction ae; intros e ck Helab; monadInv Helab;
      NamedDestructCases; try constructor; intros; subst;
      eauto using wt_lexp, find_var_type, assert_type_eq.
    - unfold find_type_unop in EQ1.
      rewrite type_unop'_correct in EQ1.
      now DestructCases.
    - unfold find_type_binop in EQ0.
      match goal with H:match ?e with _ => _ end = _ |- _ =>
                      destruct e eqn:He; try discriminate; injection H end.
      intro; subst.
      rewrite type_binop'_correct in He.
      eauto using wt_lexp.
    - now rewrite type_castop.
    - constructor; eauto.
      apply assert_type_eq in EQ1. subst.
      eauto using find_var_type.
  Qed.

  Lemma wc_elab_lexp:
    forall ae e ck,
      elab_lexp ae = OK (e, ck) ->
      wc_lexp (idck (PM.elements env)) e ck.
  Proof.
    induction ae; intros e ck Helab; monadInv Helab;
      NamedDestructCases; try constructor; intros; subst;
      repeat match goal with
             | H:(_ ==b _) = true |- _ =>
               rewrite equiv_decb_equiv in H; rewrite H in *; clear H
             | H:find_var _ _ = OK _ |- _ =>
               apply find_var_clock in H
             end;
      eauto using wc_lexp.
  Qed.

  Lemma wt_elab_lexps:
    forall loc ck aes tys es,
      elab_lexps loc ck aes tys = OK es ->
      (Forall (wt_lexp (idty (PM.elements env))) es
       /\ Forall2 (fun e ty=>typeof e = ty) es tys).
  Proof.
    induction aes; simpl; intros ** Helab; DestructCases; auto.
    monadInv Helab.
    NamedDestructCases.
    monadInv EQ0.
    apply wt_elab_lexp in EQ.
    specialize (IHaes _ _ EQ0); destruct IHaes.
    unfold assert_lexp_type in EQ1.
    NamedDestructCases. rewrite equiv_decb_equiv in Heq0.
    auto.
  Qed.

  Lemma wc_elab_lexps:
    forall loc ck aes tys es,
      elab_lexps loc ck aes tys = OK es ->
      Forall (fun e=>wc_lexp (idck (PM.elements env)) e ck) es.
  Proof.
    induction aes; simpl; intros ** Helab; DestructCases; auto.
    monadInv Helab.
    NamedDestructCases.
    monadInv EQ0.
    apply wc_elab_lexp in EQ.
    rewrite equiv_decb_equiv in Heq; rewrite Heq in *.
    eauto.
  Qed.

  Lemma wt_elab_cexp:
    forall ae e ck,
      elab_cexp ae = OK (e, ck) ->
      wt_cexp (idty (PM.elements env)) e.
  Proof.
    induction ae; intros e ck Helab;
      apply bind_inversion in Helab;
      try (destruct Helab as ((le & ck') & Helab & Hexp);
           monadInv Hexp);
      eauto using wt_elab_lexp with nltyping.
    - specialize (IHae2 _ _ EQ); clear EQ.
      specialize (IHae3 _ _ EQ1); clear EQ1.
      NamedDestructCases.
      apply andb_prop in Heq; destruct Heq as (Hg1 & Hg2).
      rewrite equiv_decb_equiv in Hg1, Hg2.
      intros; subst.
      eauto using wt_elab_lexp with nltyping.
    - apply find_var_type in Helab.
      specialize (IHae1 _ _ EQ1); clear EQ1.
      specialize (IHae2 _ _ EQ0); clear EQ0.
      NamedDestructCases.
      rewrite equiv_decb_equiv in Heq.
      apply assert_type_eq in EQ.
      intro; subst.
      eauto using assert_type_eq with nltyping.
  Qed.

  Lemma wc_elab_cexp:
    forall ae e ck,
      elab_cexp ae = OK (e, ck) ->
      wc_cexp (idck (PM.elements env)) e ck.
  Proof.
    induction ae; simpl; intros e ck HH;
      repeat match goal with H:_ = OK _ |- _ => monadInv H end;
      NamedDestructCases; intros; subst;
      repeat match goal with
             | H:(_ ==b _) = true |- _ =>
               rewrite equiv_decb_equiv in H; rewrite H in *; clear H
             | H:find_var _ _ = OK _ |- _ =>
               apply find_var_clock in H
             end;
      eauto using wc_cexp, wc_lexp, wc_elab_lexp.
  Qed.

  Lemma check_result_list_Forall2:
    forall loc ck xs txs s,
      check_result_list loc ck xs txs = OK s ->
      Forall2 (fun x tx => In (x, tx) (idty (PM.elements env))) xs txs
      /\ (forall x, PS.In x s <-> In x xs)
      /\ NoDup xs
      /\ Forall (fun x=> In (x, ck) (idck (PM.elements env))) xs.
    Proof.
    induction xs as [|x xs]; simpl.
    - repeat split; DestructCases; auto using NoDup_nil.
      now apply not_In_empty.
      contradiction.
    - intros txs s Hcheck.
      DestructCases.
      match goal with H:_ = OK _ |- _ => monadInv H end.
      NamedDestructCases.
      apply IHxs in EQ2.
      destruct EQ2 as (Hin & Hset & Hnodup & Hclk).
      apply mem_spec_false in Heq. rewrite Hset in Heq.
      apply assert_type_eq in EQ1.
      apply assert_clock_eq in EQ0.
      subst.
      repeat split; eauto using find_var_type, find_var_clock;
        try rewrite PS.add_spec, Hset;
        try destruct 1; eauto using NoDup.
    Qed.

  Lemma wt_elab_equation:
    forall aeq eq,
      elab_equation aeq = OK eq ->
      wt_equation G (idty (PM.elements env)) eq.
  Proof.
    intros aeq eq Helab.
    destruct aeq as ((xs & ae) & loc).
    destruct ae; simpl in Helab;
      repeat progress
             match goal with
             | H:bind _ _ = _ |- _ => monadInv H
             | H:bind2 _ _ = _ |- _ => monadInv H
             | H:elab_lexp _ = OK _ |- _ => apply wt_elab_lexp in H
             | H:elab_lexps _ _ _ _ = OK _ |- _ => apply wt_elab_lexps in H
             | H:find_var _ _ = OK _ |- _ =>
               pose proof (wt_clock_find_var _ _ _ _ H);
               apply find_var_type in H
             | H:assert_type _ _ _ _ = OK _ |- _ => apply assert_type_eq in H
             | H:elab_cexp _ = OK _ |- _ => apply wt_elab_cexp in H
             | H:_ ==b _ = true |- _ => rewrite equiv_decb_equiv in H
             | H:check_result_list _ _ _ _ = OK ?x |- _ =>
               apply check_result_list_Forall2 in H;
                 destruct H as (Hele & Hins & Hnodup & Hcks)
             | _ => NamedDestructCases
             end; intros; subst; auto with nltyping.
    - unfold find_type_unop in EQ3. NamedDestructCases.
      rewrite type_unop'_correct in Heq0.
      eauto with nltyping.
    - unfold find_type_binop in EQ5. NamedDestructCases.
      rewrite type_binop'_correct in Heq1.
      auto with nltyping.
    - apply andb_prop in Heq.
      destruct Heq as (Heq4 & Heq5).
      rewrite equiv_decb_equiv in Heq4, Heq5.
      auto with nltyping.
    - auto using type_castop with nltyping.
    - rename x1 into xin, x2 into xout, i into f, x3 into ein, l0 into xs,
      x0 into ck, a into loc'.
      unfold find_node_interface in EQ0. NamedDestructCases.
      destruct EQ2.
      destruct wt_nenv as (wt_nenv' & ?).
      specialize (wt_nenv' f _ _ Heq).
      destruct wt_nenv' as (n & Hfind & Hin & Hout); clear wt_nenv.
      econstructor; eauto.
      + apply Forall2_map_1 in Hout.
        apply Forall2_eq in Hout.
        rewrite <-Hout in Hele.
        now apply Forall2_map_2 in Hele.
      + apply Forall2_map_1 with (f0:=typeof) in H1.
        apply Forall2_eq in H1.
        rewrite <-H1 in Hin.
        apply Forall2_map_2, Forall2_swap_args in Hin.
        apply Forall2_impl_In with (2:=Hin).
        intros ** Htypeof. now rewrite Htypeof.
  Qed.

  Lemma wc_elab_equation:
    forall aeq eq,
      elab_equation aeq = OK eq ->
      wc_equation (idck (PM.elements env)) eq.
  Proof.
    intros aeq eq Helab.
    destruct aeq as ((xs & ae) & loc).
    destruct ae; simpl in Helab;
      repeat progress
             match goal with
             | H: _ /\ _ |- _ => destruct H
             | H:bind _ _ = _ |- _ => monadInv H
             | H:bind2 _ _ = _ |- _ => monadInv H
             | H:elab_lexp _ = OK _ |- _ => apply wc_elab_lexp in H
             | H:elab_lexps _ _ _ _ = OK _ |- _ => apply wc_elab_lexps in H
             | H:find_var _ _ = OK _ |- _ => apply find_var_clock in H
             | H:elab_cexp _ = OK _ |- _ => apply wc_elab_cexp in H
             | H:_ ==b _ = true |- _ => rewrite equiv_decb_equiv in H
             | H:equiv _ _ |- _ => rewrite <-H in *; clear H
             | H:equiv _ _ |- _ => rewrite H in *; clear H
             | H:check_result_list _ _ _ _ = OK ?x |- _ =>
               apply check_result_list_Forall2 in H; destruct H
             | _ => NamedDestructCases
             end; intros; subst;
        auto using wc_equation, wc_cexp, wc_lexp with nltyping.
  Qed.

  Fixpoint check_clock (loc: astloc) (ck: clock) : res unit :=
    match ck with
    | Cbase => OK tt
    | Con ck x b =>
      do ok <- check_clock loc ck;
      do (xty, xck) <- find_var loc x;
      if xck ==b ck then OK tt
      else Error (err_loc loc ((MSG "badly-formed clock "
                                    :: msg_of_clocks xck ck)))
    end.
  
  Lemma check_clock_spec:
    forall loc ck,
      check_clock loc ck = OK tt ->
      wc_clock (idck (PM.elements env)) ck.
  Proof.
    induction ck; simpl; intro HH; auto using wc_clock.
    monadInv HH; NamedDestructCases.
    apply find_var_clock in EQ1.
    rewrite equiv_decb_equiv in Heq. rewrite Heq in *.
    destruct x. auto.
  Qed.

End ElabExpressions.

Section ElabDeclaration.

  (* Preceding dataflow program. *)
  Variable G : global.

  (* Map node names to input and output types. *)
  Variable nenv : PM.t (list type * list type).

  Hypothesis wt_nenv : Is_interface_map G nenv.

  Definition err_incoherent_clock (loc: astloc) (x: ident) : res unit :=
    Error (err_loc loc (MSG "The declared clock of " :: CTX x
                        :: msg " is incoherent with the other declarations")).
  
  Fixpoint assert_preclock (loc: astloc) (x: ident)
           (pck: LustreAst.clock) (ck: clock) : res unit :=
    match pck, ck with
    | BASE, Cbase => OK tt
    | ON pck' py pb, Con ck' y b =>
      if py ==b y
      then if pb ==b b
           then assert_preclock loc x pck' ck'
           else err_incoherent_clock loc x
      else err_incoherent_clock loc x
    | _, _ => err_incoherent_clock loc x
    end.
  
  Fixpoint elab_var_decls_pass
           (acc: PM.t (type * clock)
                 * list (ident * (type_name * LustreAst.preclock * astloc)))
           (vds: list (ident * (type_name * LustreAst.preclock * astloc)))
    : res (PM.t (type * clock)
           * list (ident * (type_name * LustreAst.preclock * astloc))) :=
    match vds with
    | [] => OK acc
    | vd::vds =>
      let (env, notdone) := acc in
      let '(x, (sty, pck, loc)) := vd in
        match pck with
        | FULLCK BASE =>
          if PM.mem x env
          then Error (err_loc loc (CTX x :: msg " is declared more than once"))
          else elab_var_decls_pass
                 (PM.add x (elab_type sty, Cbase) env, notdone) vds
                            
        | FULLCK (ON cy' y b) =>
          match PM.find y env with
          | None => elab_var_decls_pass (env, vd::notdone) vds
          | Some (yt, cy) =>
            if PM.mem x env
            then Error (err_loc loc (CTX x :: msg " is declared more than once"))
            else do ok <- assert_type loc y yt bool_type;
                 do ok <- assert_preclock loc x cy' cy;
                 elab_var_decls_pass
                   (PM.add x (elab_type sty, Con cy y b) env, notdone) vds
          end

        | WHENCK y b =>
          match PM.find y env with
          | None => elab_var_decls_pass (env, vd::notdone) vds
          | Some (yt, cy) =>
            do ok <- assert_type loc y yt bool_type;
            if PM.mem x env
            then Error (err_loc loc (CTX x :: msg " is declared more than once"))
            else elab_var_decls_pass
                   (PM.add x (elab_type sty, Con cy y b) env, notdone) vds
          end
        end
    end.

  Lemma elab_var_decls_pass_wc_env:
    forall vds env ovds env' vds',
      wc_env (idck (PM.elements env)) ->
      elab_var_decls_pass (env, ovds) vds = OK (env', vds') ->
      wc_env (idck (PM.elements env')).
  Proof.
    induction vds as [|vd vds IH].
    now intros ** Helab; monadInv Helab.
    intros ** Hwce Helab.
    destruct vd as (x & ((ty & pck) & loc)).
    destruct pck as [ck|y yb]; [destruct ck as [|ck y yb]|]; simpl in Helab.
    - (* (x, (ty, FULLCK BASE, loc)) *)
      NamedDestructCases.
      apply PM_mem_spec_false in Heq.
      apply IH in Helab; auto.
      rewrite elements_add; auto.
      simpl; apply wc_env_add; auto.
      now rewrite InMembers_idck, <-PM_In_Members.
    - (* (x, (ty, FULLCK (ON ck y yb))) *)
      NamedDestructCases.
      2:now apply IH in Helab; auto.
      monadInv Helab.
      apply PM_mem_spec_false in Heq1.
      apply IH in EQ2; auto.
      rewrite elements_add; auto.
      simpl; apply wc_env_add; auto.
      now rewrite InMembers_idck, <-PM_In_Members.
      constructor.
      2:now apply In_idck_exists; exists t; apply PM.elements_correct.
      apply wc_env_var with (1:=Hwce) (x:=y).
      apply In_idck_exists. exists t.
      apply PM.elements_correct; auto.
    - (* (x, (ty, WHENCK y yb, loc)) *)
      NamedDestructCases.
      2:now apply IH in Helab; auto.
      monadInv Helab. NamedDestructCases.
      apply PM_mem_spec_false in Heq1.
      apply IH in EQ0; auto.
      rewrite elements_add; auto.
      simpl; apply wc_env_add; auto.
      now rewrite InMembers_idck, <-PM_In_Members.
      constructor.
      2:now apply In_idck_exists; exists t; apply PM.elements_correct.
      apply wc_env_var with (1:=Hwce) (x:=y).
      apply In_idck_exists. exists t.
      apply PM.elements_correct; auto.
  Qed.
      
  Definition all_wt_clock (env: PM.t (type * clock)) : Prop :=
    forall x ty ck, PM.find x env = Some (ty, ck) ->
                    wt_clock (idty (PM.elements env)) ck.

  Lemma all_wt_clock_empty:
    all_wt_clock (PM.empty (type * clock)).
  Proof.
    intros x ty ck Hfind.
    rewrite PM.gempty in Hfind.
    discriminate Hfind.
  Qed.
    
  Lemma all_wt_clock_add:
    forall env x ty ck,
      all_wt_clock env ->
      ~PM.In x env ->
      wt_clock (idty (PM.elements env)) ck ->
      all_wt_clock (PM.add x (ty, ck) env).
  Proof.
    intros env x ty ck Hawc Hnin Hwtc y yt yc Hfind.
    rewrite elements_add; auto; simpl.
    rewrite PM_In_Members, <-InMembers_idty in Hnin.
    destruct (ident_eq_dec y x).
    - subst. rewrite PM.gss in Hfind.
      injection Hfind; intros; subst.
      apply wt_clock_add; auto.
    - rewrite PM.gso in Hfind; auto.
      apply Hawc in Hfind.
      apply wt_clock_add; auto.
  Qed.
    
  Lemma elab_var_decls_pass_all_wt_clock:
    forall vds env ovds env' vds',
      all_wt_clock env ->
      elab_var_decls_pass (env, ovds) vds = OK (env', vds') ->
      all_wt_clock env'.
  Proof.
    induction vds as [|vd vds IH].
    now simpl; intros vd' vds' vd vds Hawc Helab; monadInv Helab.
    intros env ovds env' vds' Hawc Helab.
    destruct vd as (x & ((ty & pck) & loc)).
    destruct pck as [ck|y yb]; [destruct ck as [|ck y yb]|]; simpl in Helab.
    - (* (x, (ty, FULLCK BASE, loc)) *)
      NamedDestructCases.
      apply PM_mem_spec_false in Heq.
      apply IH in Helab; auto.
      apply all_wt_clock_add; auto with nltyping.
    - (* (x, (ty, FULLCK (ON ck y yb))) *)
      NamedDestructCases.
      2:now apply IH in Helab; auto.
      monadInv Helab.
      apply PM_mem_spec_false in Heq1.
      apply IH in EQ2; auto.
      apply all_wt_clock_add; auto.
      apply assert_type_eq in EQ; subst.
      constructor.
      2:now apply Hawc in Heq.
      apply PM.elements_correct in Heq.
      apply In_idty_exists; eauto.
    - (* (x, (ty, WHENCK y yb, loc)) *)
      NamedDestructCases.
      2:now apply IH in Helab; auto.
      monadInv Helab.
      NamedDestructCases.
      apply PM_mem_spec_false in Heq1.
      apply IH in EQ0; auto.
      apply all_wt_clock_add; auto.
      apply assert_type_eq in EQ; subst.
      constructor.
      2:now apply Hawc in Heq.
      apply PM.elements_correct in Heq.
      apply In_idty_exists; eauto.
  Qed.
  
  Lemma elab_var_decls_pass_spec:
    forall vds env ovds env' vds',
      elab_var_decls_pass (env, ovds) vds = OK (env', vds') ->
      exists vds1 vds2,
        vds' = vds2 ++ ovds
        /\ Permutation vds (vds1 ++ vds2)
        /\ NoDupMembers vds1
        /\ (forall x, InMembers x vds1 -> ~PM.In x env /\ PM.In x env')
        /\ (forall x, PM.In x env -> PM.In x env')
        /\ (forall x, PM.In x env' -> PM.In x env \/ InMembers x vds1).
  Proof.
    induction vds as [|vd vds IH].
    now intros ** Helab; monadInv Helab; exists [], []; intuition.
    intros ** Helab.
    destruct vd as (x & ((ty & pck) & loc)).
    destruct pck as [ck|y yb]; [destruct ck as [|ck y yb]|];
      simpl in Helab.
    - (* (x, (ty, FULLCK BASE, loc)) *)
      NamedDestructCases.
      apply PM_mem_spec_false in Heq.
      apply IH in Helab; clear IH.
      destruct Helab as (vds1 & vds2 & Hvds' & Hperm & Hnd
                         & Hvds1 & Henv & Henv').
      exists ((x, (ty, FULLCK BASE, loc)) :: vds1), vds2.
      repeat split; auto.
      + now rewrite Hperm.
      + constructor; auto.
        intro Hin. apply Hvds1 in Hin.
        destruct Hin as (Hnin & Hin).
        apply Hnin, PM_add_spec; auto.
      + inv H; auto.
        match goal with H:InMembers ?x vds1 |- _ =>
                        apply Hvds1 in H; destruct H as (Hnin & Hin) end.
        rewrite PM_add_spec in Hnin. intuition.
      + inv H.
        2:match goal with H:InMembers ?x vds1 |- _ =>
                          now apply Hvds1 in H; destruct H; auto end.
        apply Henv, PM_add_spec; auto.
      + intros x' Hfind.
        apply Henv, PM_add_spec; auto.
      + intros x' Hfind.
        apply Henv' in Hfind.
        destruct Hfind as [Hfind|]; simpl; auto.
        apply PM_add_spec in Hfind.
        destruct Hfind as [Hfind|Hfind]; auto.
    - (* (x, (ty, FULLCK (ON ck y yb))) *)
      NamedDestructCases.
      + (* PM.find y env = Some (yt, cy) *)
        monadInv Helab.
        apply PM_mem_spec_false in Heq1.
        apply IH in EQ2; clear IH.
        destruct EQ2 as (vds1 & vds2 & Hvds' & Hperm & Hnd
                         & Hvds1 & Henv & Henv').
        exists ((x, (ty, FULLCK (ON ck y yb), loc)) :: vds1), vds2.
        repeat split; auto.
        * now rewrite Hperm.
        * constructor; auto.
          intro Hin. apply Hvds1 in Hin.
          destruct Hin as (Hnin & Hin).
          apply Hnin, PM_add_spec; auto.
        * inv H; auto.
          match goal with H:InMembers ?x vds1 |- _ =>
                          apply Hvds1 in H; destruct H as (Hnin & Hin) end.
          rewrite PM_add_spec in Hnin. intuition.
        * inv H.
          2:match goal with H:InMembers ?x vds1 |- _ =>
                            now apply Hvds1 in H; destruct H; auto end.
          apply Henv, PM_add_spec; auto.
        * intros x' Hfind.
          apply Henv, PM_add_spec; auto.
        * intros x' Hfind.
          apply Henv' in Hfind.
          rewrite PM_add_spec in Hfind.
          simpl; intuition.
      + (* PM.find y env = None *)
        apply IH in Helab; clear IH; auto.
        destruct Helab as (vds1 & vds2 & Hvds' & Hperm & Hnd
                           & Hvds1 & Henv & Henv').
        exists vds1, (vds2 ++ [(x, (ty, FULLCK (ON ck y yb), loc))]).
        repeat split; auto.
        * rewrite <-List_shift_first; auto.
        * now rewrite <-Permutation_app_assoc, <-Hperm, cons_is_app,
          Permutation_app_comm.
        * match goal with H:InMembers _ vds1 |- _ =>
                          now apply Hvds1 in H end.
        * match goal with H:InMembers _ vds1 |- _ =>
                          now apply Hvds1 in H end.
    - (* (x, (ty, WHENCK y yb, loc)) *)
      NamedDestructCases.
      + (* PM.find y env = Some (yt, cy) *)
        monadInv Helab.
        NamedDestructCases.
        apply PM_mem_spec_false in Heq1.
        apply IH in EQ0; clear IH.
        destruct EQ0 as (vds1 & vds2 & Hvds' & Hperm & Hnd
                         & Hvds1 & Henv & Henv').
        exists ((x, (ty, WHENCK y yb, loc)) :: vds1), vds2.
        repeat split; auto.
        * now rewrite Hperm.
        * constructor; auto.
          intro Hin. apply Hvds1 in Hin.
          destruct Hin as (Hnin & Hin).
          apply Hnin, PM_add_spec; auto.
        * inv H; auto.
          match goal with H:InMembers ?x vds1 |- _ =>
                          apply Hvds1 in H; destruct H as (Hnin & Hin) end.
          rewrite PM_add_spec in Hnin. intuition.
        * inv H.
          2:match goal with H:InMembers ?x vds1 |- _ =>
                            now apply Hvds1 in H; destruct H; auto end.
          apply Henv, PM_add_spec; auto.
        * intros x' Hfind.
          apply Henv, PM_add_spec; auto.
        * intros x' Hfind.
          apply Henv' in Hfind.
          rewrite PM_add_spec in Hfind.
          simpl; intuition.
      + (* PM.find y env = None *)
        apply IH in Helab; clear IH; auto.
        destruct Helab as (vds1 & vds2 & Hvds' & Hperm & Hnd
                           & Hvds1 & Henv & Henv').
        exists vds1, (vds2 ++ [(x, (ty, WHENCK y yb, loc))]).
        repeat split; auto.
        * rewrite <-List_shift_first; auto.
        * now rewrite <-Permutation_app_assoc, <-Hperm, cons_is_app,
          Permutation_app_comm.
        * match goal with H:InMembers _ vds1 |- _ =>
                          now apply Hvds1 in H end.
        * match goal with H:InMembers _ vds1 |- _ =>
                          now apply Hvds1 in H end.
  Qed.
    
  Opaque elab_var_decls_pass.  

  Fixpoint elab_var_decls' {A: Type}
           (loc: astloc)
           (fuel : list A)
           (env: PM.t (type * clock))
           (vds: list (ident * (type_name * LustreAst.preclock * astloc)))
    : res (PM.t (type * clock)) :=
      match vds with
      | [] => OK env
      | _ =>
        match fuel with
        | [] => Error (err_loc loc (MSG "incoherent or cyclic clocks: "
                                        :: msg_ident_list (map fst vds)))
        | _::fuel' =>
          do (env', notdone) <- elab_var_decls_pass (env, []) vds;
          elab_var_decls' loc fuel' env' notdone
        end
      end.
  
  Definition elab_var_decls
             (loc: astloc) 
             (env: PM.t (type * clock))
             (vds: list (ident * (type_name * LustreAst.preclock * astloc)))
    : res (PM.t (type * clock)) :=
    elab_var_decls' loc vds env vds.

  Lemma elab_var_decls_wc_env:
    forall loc vds env env',
      wc_env (idck (PM.elements env)) ->
      elab_var_decls loc env vds = OK env' ->
      wc_env (idck (PM.elements env')).
  Proof.
    unfold elab_var_decls.
    intros loc vds. generalize vds at 1.
    intro fuel. revert vds.
    induction fuel as [|cd fuel IH].
    now simpl; intros ** Helab; NamedDestructCases.
    intros ** Hwc Helab.
    destruct vds as [|vd vds].
    now simpl in Helab; monadInv Helab.
    simpl in Helab. monadInv Helab.
    rename x into env'', x0 into vds'.
    pose proof (elab_var_decls_pass_wc_env _ _ _ _ _ Hwc EQ) as Hwc''.
    apply elab_var_decls_pass_spec in EQ; auto.
    apply IH in EQ0; auto.
  Qed.

  Lemma elab_var_decls_all_wt_clock:
    forall loc vds env env',
      all_wt_clock env ->
      elab_var_decls loc env vds = OK env' ->
      all_wt_clock env'.
  Proof.
    unfold elab_var_decls.
    intros loc vds. generalize vds at 1.
    intro fuel. revert vds.
    induction fuel as [|cd fuel IH].
    now simpl; intros; NamedDestructCases.
    intros vds env env' Hawt Helab.
    destruct vds as [|vd vds].
    now simpl in Helab; monadInv Helab.
    simpl in Helab. monadInv Helab.
    rename x into env'', x0 into vds'.
    pose proof (elab_var_decls_pass_all_wt_clock _ _ _ _ _ Hawt EQ) as Hawt''.
    apply elab_var_decls_pass_spec in EQ; auto.
    apply IH in EQ0; auto.
  Qed.

  Lemma elab_var_decls_permutation:
    forall loc vds env env',
      elab_var_decls loc env vds = OK env' ->
      Permutation (map fst vds ++ map fst (PM.elements env))
                  (map fst (PM.elements env')).
  Proof.
    unfold elab_var_decls.
    intros loc vds env env'.
    generalize vds at 1.
    intro countdown. revert vds env env'.
    induction countdown as [|cd countdown IH].
    now simpl; intros; NamedDestructCases.
    intros vds env env' Helab.
    destruct vds as [|vd vds].
    now simpl in Helab; monadInv Helab.
    simpl in Helab. monadInv Helab.
    rename x into env'', x0 into vds'.
    apply elab_var_decls_pass_spec in EQ; auto.
    apply IH in EQ0; auto; clear IH.
    destruct EQ as (vds1 & vds2 & Hvds' & Hperm & Hnd & Hvds & Henv' & Henv'').
    rewrite app_nil_r in Hvds'; subst.
    rewrite Hperm, <-EQ0, (Permutation_app_comm vds1),
            map_app, <-app_assoc; clear Hperm EQ0.
    apply Permutation_app_head.
    apply NoDup_Permutation.
    - apply NoDup_app'; try apply fst_NoDupMembers;
        auto using NoDupMembers_PM_elements.
      apply all_In_Forall.
      intros x Hin.
      apply fst_InMembers in Hin.
      rewrite <-fst_InMembers.
      apply Hvds in Hin.
      now rewrite PM_In_Members in Hin.
    - apply fst_NoDupMembers, NoDupMembers_PM_elements.
    - split; intro HH.
      + apply in_app in HH.
        destruct HH as [HH|HH].
        * apply fst_InMembers in HH.
          apply Hvds in HH.
          rewrite <-fst_InMembers.
          now setoid_rewrite PM_In_Members in HH.
        * apply fst_InMembers, InMembers_In in HH.
          destruct HH as (v & HH).
          apply In_PM_In, Henv', PM_In_Members in HH.
          now apply fst_InMembers.
      + apply in_app.
        apply fst_InMembers, InMembers_In in HH.
        destruct HH as (v & HH).
        apply In_PM_In, Henv'' in HH.
        destruct HH as [HH|HH].
        * right. now apply fst_InMembers, PM_In_Members.
        * left. now apply fst_InMembers.
  Qed.
  
  Fixpoint check_vars (loc: astloc) (defd: PS.t) (xs: idents) : res PS.t :=
    match xs with
    | nil => OK defd
    | x::xs => if PS.mem x defd
               then check_vars loc (PS.remove x defd) xs
               else Error (err_loc loc (CTX x :: msg " is improperly defined"))
    end.

  Lemma check_vars_spec:
    forall loc xs defd s,
      check_vars loc defd xs = OK s ->
      (forall x, PS.In x s -> ~In x xs)
      /\ (forall x, In x xs -> ~PS.In x s)
      /\ (forall x, PS.In x defd <-> In x xs \/ PS.In x s)
      /\ NoDup xs.
  Proof.
    induction xs as [|x xs]; simpl.
    - intros. DestructCases. intuition. apply NoDup_nil.
    - intros defd s Hchk.
      NamedDestructCases. rewrite PS.mem_spec in Heq.
      specialize (IHxs _ _ Hchk); clear Hchk;
        destruct IHxs as (IH1 & IH2 & IH3 & IH4).
      repeat split.
      + intros y HH.
        specialize (IH2 y).
        destruct 1; intuition.
        subst.
        assert (PS.In y (PS.remove y defd)) as Hir
            by (apply IH3; intuition).
        rewrite PS.remove_spec in Hir; intuition.
      + intros y.
        specialize (IH2 y).
        destruct 1 as [HH|HH]; intuition.
        subst.
        assert (PS.In y (PS.remove y defd)) as Hir
            by (apply IH3; intuition).
        rewrite PS.remove_spec in Hir; intuition.
      + rename x0 into y. intros HH.
        destruct (ident_eq_dec x y).
        now intuition.
        assert (PS.In y (PS.remove x defd)) as Hir
            by (apply PS.remove_spec; split; auto).
        apply IH3 in Hir. intuition.
      + rename x0 into y.
        destruct 1 as [[HH|HH]|HH]; subst; auto.
        * assert (PS.In y (PS.remove x defd)) as Hir
              by (apply IH3; intuition).
          rewrite PS.remove_spec in Hir; intuition.
        * assert (PS.In y (PS.remove x defd)) as Hir
              by (apply IH3; intuition).
          rewrite PS.remove_spec in Hir; intuition.
      + constructor; auto.
        intro HH.
        assert (PS.In x (PS.remove x defd)) as Hir
            by (apply IH3; intuition).
        rewrite PS.remove_spec in Hir. intuition.
  Qed.

  Fixpoint check_defined (loc: astloc) (out: PS.t) (defd: PS.t)
           (eqs: list equation) : res unit :=
    match eqs with
    | nil => if PS.is_empty defd then OK tt
             else Error (err_loc loc
                                 (MSG "some variables are not defined:"
                                      :: msg_ident_list (PS.elements defd)))
    | EqFby x _ _ _::eqs => if PS.mem x defd && (negb (PS.mem x out))
                            then check_defined loc out (PS.remove x defd) eqs
                            else if PS.mem x out
                                 then Error (err_loc loc
                                   (MSG "output variable " :: CTX x
                                        :: msg " may not be defined using fby."))
                                 else Error (err_loc loc
                                        (CTX x :: msg " is improperly defined"))
    | EqDef x _ _::eqs => if PS.mem x defd
                          then check_defined loc out (PS.remove x defd) eqs
                          else Error (err_loc loc
                                        (CTX x :: msg " is improperly defined"))
    | EqApp xs _ _ _::eqs => do defd' <- check_vars loc defd xs;
                             check_defined loc out defd' eqs
    end.
  
  Lemma check_defined_spec:
    forall eqs loc out defd,
      check_defined loc out defd eqs = OK tt ->
      (forall x, In x (vars_defined eqs) <-> PS.In x defd)
      /\ NoDup (concat (map var_defined eqs))
      /\ (forall x, In x (vars_defined (filter is_fby eqs))
                    -> ~PS.In x out).
  Proof.
    induction eqs as [|eq eqs IH]; simpl; intros loc out defd Hchk;
      NamedDestructCases.
    - rewrite PS.is_empty_spec in Heq.
      apply PSP.empty_is_empty_1 in Heq.
      setoid_rewrite Heq.
      repeat split; auto using NoDup_nil.
      + inversion 1.
      + apply not_In_empty.
    - rewrite PS.mem_spec in Heq0; simpl.
      specialize (IH _ _ _ Hchk); clear Hchk.
      destruct IH as (IH1 & IH2 & IH3).
      repeat split.
      + destruct 1 as [|HH]. now subst x.
        rewrite IH1, PS.remove_spec in HH. intuition.
      + intro Hxdef.
        destruct (var_defined eq ==b [x]) eqn:Heq1;
          rewrite Heq in Heq1; simpl in Heq1.
        rewrite equiv_decb_equiv in Heq1; injection Heq1; auto.
        rewrite not_equiv_decb_equiv in Heq1.
        right. apply IH1. apply PS.remove_spec; split; auto.
        intro HH; apply Heq1. now subst.
      + constructor; auto.
        rewrite IH1, PS.remove_spec.
        intuition.
      + intros x Hvd.
        destruct (is_fby eq); auto.
    - simpl. monadInv Hchk.
      rename x into defd', i into xs, c into ck, i0 into f, l into es.
      apply check_vars_spec in EQ.
      destruct EQ as (Hcv1 & Hcv2 & Hcv3 & Hcv4).
      specialize (IH _ _ _ EQ0); clear EQ0.
      destruct IH as (IH1 & IH2 & IH3).
      rewrite vars_defined_EqApp. setoid_rewrite in_app.
      repeat split.
      + destruct 1 as [HH|HH].
        now apply Hcv3; auto.
        apply Hcv3. apply IH1 in HH; auto.
      + intro Hxdef. apply Hcv3 in Hxdef.
        destruct Hxdef as [|HH]; auto.
        apply IH1 in HH; auto.
      + apply NoDup_app'; auto.
        apply all_In_Forall.
        intros x Hin Hinc.
        specialize (Hcv2 x). specialize (IH1 x). intuition.
      + intros x Hin.
        now apply IH3 in Hin.
    - rewrite Bool.andb_true_iff, Bool.negb_true_iff, mem_spec_false in Heq0.
      destruct Heq0 as (Hidef & Hniout).
      rewrite PS.mem_spec in Hidef. simpl.
      specialize (IH _ _ _ Hchk); clear Hchk.
      destruct IH as (IH1 & IH2 & IH3).
      repeat split.
      + destruct 1 as [|HH].
        now subst x.
        rewrite IH1, PS.remove_spec in HH.
        intuition.
      + intro Hxdef.
        destruct (var_defined eq ==b [x]) eqn:Heq1;
          rewrite Heq in Heq1; simpl in Heq1.
        rewrite equiv_decb_equiv in Heq1; injection Heq1; auto.
        rewrite not_equiv_decb_equiv in Heq1.
        right. apply IH1. apply PS.remove_spec; split; auto.
        intro HH; apply Heq1. now subst.
      + constructor; auto.
        rewrite IH1, PS.remove_spec.
        intuition.
      + intros x Hvd.
        destruct Hvd as [Hvd|]; subst; auto.
  Qed.
  
  Definition nameset {A: Type} s (xs: list (ident * A)) : PS.t :=
    List.fold_left (fun acc x => PS.add (fst x) acc) xs s.

  Definition annotate {A: Type} (env: PM.t A)
             (vd: ident * (type_name * preclock * astloc)) : res (ident * A) :=
    let '(x, (sty, pck, loc)) := vd in
    match PM.find x env with
    | None => Error (msg "internal error (annotate)")
    | Some a => OK (x, a)
    end.

  Lemma nameset_spec:
    forall {A: Type} x (xs: list (ident * A)) s,
      PS.In x (nameset s xs) <-> PS.In x s \/ In x (map fst xs).
  Proof.
    induction xs as [|yv xs IH].
    now intuition.
    destruct yv as (y & v); simpl.
    split; intro HH.
    - apply IH in HH.
      destruct HH as [HH|]; auto.
      rewrite PSP.FM.add_iff in HH.
      intuition.
    - apply IH.
      rewrite PSP.FM.add_iff.
      intuition.
  Qed.

  Lemma mmap_annotate_fst:
    forall {A} env xs (ys: list (ident * A)),
      mmap (annotate env) xs = OK ys ->
      map fst xs = map fst ys.
  Proof.
    intros ** Hmm.
    apply mmap_inversion in Hmm.
    induction Hmm as [|x xs y ys Hann IH Hmap]; auto.
    simpl. rewrite Hmap.
    destruct x as (x & ((v1 & v2) & v3)).
    simpl in *. NamedDestructCases.
    reflexivity.
  Qed.
  
  Lemma mmap_annotate_Forall:
    forall {A} xs (ys: list (ident * A)) env,
      mmap (annotate env) xs = OK ys ->
      Forall (fun yv=>PM.find (fst yv) env = Some (snd yv)) ys.
  Proof.
    induction xs as [|x xs IH].
    - simpl. intros ** Hperm Hys.
      monadInv Hys; auto.
    - simpl. intros ys env Hmm.
      monadInv Hmm.
      constructor.
      2:now apply IH.
      destruct x as (x, ((ty, pck), loc)).
      simpl in EQ. NamedDestructCases.
      simpl. now rewrite Heq.
  Qed.

  Lemma permutation_forall_elements:
    forall {A} (xs: list (ident * A)) env,
      Permutation (map fst xs) (map fst (PM.elements env)) ->
      Forall (fun yv => PM.find (fst yv) env = Some (snd yv)) xs ->
      Permutation xs (PM.elements env).
  Proof.
    intros ** Hperm Hfa.
    pose proof (NoDupMembers_PM_elements env) as Hnd.
    apply NoDup_Permutation.
    - apply fst_NoDupMembers in Hnd.
      rewrite <-Hperm in Hnd.
      apply fst_NoDupMembers in Hnd.
      now apply NoDupMembers_NoDup.
    - now apply NoDupMembers_NoDup.
    - split; intro HH.
      + apply In_Forall with (1:=Hfa) in HH.
        apply PM.elements_correct in HH.
        now rewrite <-surjective_pairing in HH.
      + destruct x as (x & v).
        assert (In x (map fst (PM.elements env))) as Hin
            by (apply fst_InMembers; apply In_InMembers with (1:=HH)).
        rewrite <-Hperm in Hin.
        apply fst_InMembers, InMembers_In in Hin.
        destruct Hin as (v' & Hin).
        apply In_Forall with (2:=Hin) in Hfa.
        apply PM.elements_complete in HH.
        simpl in Hfa. rewrite HH in Hfa.
        injection Hfa; intro; subst.
        assumption.
  Qed.

  Local Obligation Tactic :=
    Tactics.program_simpl;
      repeat progress
             match goal with
             | H:_ = bind _ _ |- _ => symmetry in H; monadInv H
             | H:(if ?b then _ else _) = _ |- _ =>
               let Hb := fresh "Hb" in
               destruct b eqn:Hb; try discriminate
             | H:OK _ = OK _ |- _ => monadInv1 H
             end.

  Local Ltac MassageElabs outputs locals inputs :=
    let Helab_out := fresh "Helab_out" in
    let Helab_var := fresh "Helab_var" in
    let Helab_in := fresh "Helab_in" in
    let Hwc_in := fresh "Hwc_in" in
    let Hwc_out := fresh "Hwc_out" in
    let Hwc_var := fresh "Hwc_var" in
    let Hwt_in := fresh "Hwt_in" in
    let Hwt_out := fresh "Hwt_out" in
    let Hwt_var := fresh "Hwt_var" in
    let env_in := fresh "env_in" in
    let env_out := fresh "env_out" in
    let env := fresh "env" in
    let Helabs := fresh "Helabs" in
    let eqs := fresh "eqs'" in
    let Hdefd  := fresh "Hdefd" in
    let Houtin := fresh "Houtin" in
    let Hin  := fresh "Hin" in
    let Hout := fresh "Hout" in
    let Hvar := fresh "Hvar" in
    let Hf_in  := fresh "Hf_in" in
    let Hf_out := fresh "Hf_out" in
    let Hf_var := fresh "Hf_var" in
    match goal with H:elab_var_decls _ _ inputs = OK ?x |- _ =>
                    (assert (Hwc_in := H);
                     apply elab_var_decls_wc_env in Hwc_in;
                     simpl; auto with nlclocking);
                    (assert (Hwt_in := H);
                     apply elab_var_decls_all_wt_clock in Hwt_in;
                     simpl; auto using all_wt_clock_empty with nlclocking);
                    apply elab_var_decls_permutation in H;
                    simpl in H; rewrite app_nil_r in H;
                    rename H into Helab_in, x into env_in end;
    match goal with H:elab_var_decls _ _ outputs = OK ?x |- _ =>
                    (assert (Hwc_out := H);
                     apply elab_var_decls_wc_env in Hwc_out;
                     simpl; auto with nlclocking);
                    (assert (Hwt_out := H);
                     apply elab_var_decls_all_wt_clock in Hwt_out;
                     simpl; auto with nlclocking);
                    apply elab_var_decls_permutation in H;
                    rewrite <-Helab_in in H;
                    rename H into Helab_out, x into env_out end;
    match goal with H:elab_var_decls _ _ locals = OK ?x |- _ =>
                    (assert (Hwc_var := H);
                     apply elab_var_decls_wc_env in Hwc_var;
                     simpl; auto with nlclocking);
                    (assert (Hwt_var := H);
                     apply elab_var_decls_all_wt_clock in Hwt_var;
                     simpl; auto with nlclocking);
                    apply elab_var_decls_permutation in H;
                    rewrite <-Helab_out in H;
                    rename H into Helab_var, x into env end;
    match goal with H:mmap (elab_equation _ _) _ = OK ?x |- _ =>
      rename H into Helabs; rename x into eqs end;
    match goal with H:check_defined _ _ _ _ = OK ?x |- _ =>
      rename H into Hdefd; destruct x end;
    match goal with H:mmap _ inputs = OK _ |- _ =>
                    assert (Hf_in := H);
                    apply mmap_annotate_Forall in Hf_in;
                    apply mmap_annotate_fst in H;
                    rename H into Hin end;
    match goal with H:mmap _ locals = OK _ |- _ =>
                    assert (Hf_var := H);
                    apply mmap_annotate_Forall in Hf_var;
                    apply mmap_annotate_fst in H;
                    rename H into Hvar end;
    match goal with H:mmap _ outputs = OK _ |- _ =>
                    assert (Hf_out := H);
                    apply mmap_annotate_Forall in Hf_out;
                    apply mmap_annotate_fst in H;
                    rename H into Hout end.

  Local Hint Resolve NoDupMembers_nil NoDup_nil.

  Program Definition elab_declaration (decl: LustreAst.declaration)
    : res {n | wt_node G n /\ wc_node n} :=
    match decl with
    | NODE name inputs outputs locals equations loc =>
      match (do env_in  <- elab_var_decls loc (PM.empty (type * clock)) inputs;
             do env_out <- elab_var_decls loc env_in outputs;
             do env     <- elab_var_decls loc env_out locals;
             do xin     <- mmap (annotate env) inputs;
             do xout    <- mmap (annotate env) outputs;
             do xvar    <- mmap (annotate env) locals;
             do eqs     <- mmap (elab_equation env nenv) equations;
             do ok      <- check_defined loc (nameset PS.empty xout)
                             (nameset (nameset PS.empty xvar) xout) eqs;
             do ok <- mmap (fun xtc=>
                              assert_clock loc (fst xtc) (dck xtc) Cbase) xin;
             do ok <- mmap (fun xtc=>
                              assert_clock loc (fst xtc) (dck xtc) Cbase) xout;
             if existsb (fun x=>PM.mem x env) Ident.Ids.reserved
             then Error (err_loc loc (msg "illegal variable name"))
             else if (length xin ==b 0) || (length xout ==b 0)
                  then Error (err_loc loc (msg "not enough inputs or outputs"))
                  else OK (xin, xout, xvar, eqs)) with
      | Error e => Error e
      | OK (xin, xout, xvar, eqs) => OK {| n_name  := name;
                                           n_in    := xin;
                                           n_out   := xout;
                                           n_vars  := xvar;
                                           n_eqs   := eqs;
                                           n_ingt0 := _;
                                           n_outgt0:= _;
                                           n_defd  := _;
                                           n_vout  := _;
                                           n_nodup := _;
                                           n_good  := _ |}
      end
    end.
  Next Obligation.
    (* 0 < length xin *)
    match goal with H:(length _ ==b 0) || _ = false |- _ =>
      rewrite Bool.orb_false_iff in H; destruct H as (Hin & Hout) end.
    apply not_equiv_decb_equiv in Hin.
    now apply NPeano.Nat.neq_0_lt_0 in Hin.
  Qed.
  Next Obligation.
    (* 0 < length xout *)
    match goal with H:(length _ ==b 0) || _ = false |- _ =>
      rewrite Bool.orb_false_iff in H; destruct H as (Hin & Hout) end.
    apply not_equiv_decb_equiv in Hout.
    now apply NPeano.Nat.neq_0_lt_0 in Hout.
  Qed.
  Next Obligation.
    (* Permutation (map var_defined eqs) (map fst (xvar ++ xout)) *)
    MassageElabs outputs locals inputs.
    apply check_defined_spec in Hdefd.
    destruct Hdefd as (Hdefd & Hnodup & Hnfby).
    repeat setoid_rewrite nameset_spec in Hdefd.
    setoid_rewrite map_app.    
    apply Permutation.NoDup_Permutation; auto.
    - pose proof (NoDupMembers_PM_elements env) as Hnd.
      apply fst_NoDupMembers in Hnd.
      rewrite <-Helab_var, app_assoc in Hnd.
      apply NoDup_app_weaken in Hnd.
      setoid_rewrite <-Hvar.
      setoid_rewrite <-Hout.
      exact Hnd.
    - setoid_rewrite Hdefd.
      setoid_rewrite PSP.FM.empty_iff.
      setoid_rewrite in_app.
      intuition.
  Qed.
  Next Obligation.
    (* ~ In i (map var_defined (filter is_fby eqs)) *)
    MassageElabs outputs locals inputs.
    apply check_defined_spec in Hdefd.
    destruct Hdefd as (Hdefd & Hnodup & Hnfby).
    intros Hi. apply Hnfby in Hi. apply Hi.
    rewrite nameset_spec.
    auto.
  Qed.
  Next Obligation.
    (* NoDupMembers (xin ++ xlocal ++ xout) *)
    MassageElabs outputs local inputs.
    pose proof (NoDupMembers_PM_elements env) as Hnd.
    apply fst_NoDupMembers in Hnd.
    rewrite <-Helab_var in Hnd.
    rewrite Permutation_app_comm, Permutation_app_assoc.
    rewrite Hvar, Hout, Hin in Hnd.
    repeat rewrite <-map_app in Hnd.
    now apply fst_NoDupMembers.
  Qed.
  Next Obligation.
    (* Forall NotReserved (xin ++ xlocal ++ xout) *)
    MassageElabs outputs locals inputs.
    unfold Ident.Ids.NotReserved.
    change (Forall (fun xty=>(fun x=>~In x Ident.Ids.reserved) (fst xty))
                   (xin ++ xvar ++ xout)).
    rewrite <-Forall_map, map_app, map_app.
    rewrite Hvar, Hin, Hout in Helab_var.
    rewrite Permutation_app_comm, Permutation_app_assoc, Helab_var.
    rewrite 2 Bool.orb_false_iff in Hb.
    destruct Hb as (Hb1 & Hb2 & ?).
    rewrite PM_mem_spec_false in Hb1, Hb2.

    apply all_In_Forall.
    intros xtx Hm Hir.
    apply fst_InMembers, PM_In_Members in Hm.
    destruct Hir as [Hir|Hir]; subst.
    now apply Hb1.
    rewrite In_singleton in Hir; subst.
    now apply Hb2.
  Qed.
  Next Obligation.
    split.
    - (* wt_node G n *)
      unfold wt_node. simpl.
      repeat match goal with H:OK _ = _ |- _ =>
        symmetry in H; monadInv1 H end.
      NamedDestructCases. intros; subst.
      MassageElabs outputs locals inputs.
      assert (Forall (fun yv=>PM.find (fst yv) env = Some (snd yv))
                     (xin ++ xvar ++ xout)) as Hf
          by repeat (apply Forall_app; split; auto).
      clear Hf_in Hf_var Hf_out.
      rewrite Hin, Hout, Hvar in Helab_var.
      apply permutation_forall_elements in Hf.
      2:now rewrite <-Helab_var, map_app, map_app,
        Permutation_app_comm, Permutation_app_assoc.
      apply Forall_forall.
      intros y Hxin.
      rewrite Hf.
      apply mmap_inversion in Helabs.
      apply Coqlib.list_forall2_in_right with (1:=Helabs) in Hxin.
      destruct Hxin as (aeq & Hxin & Helab).
      apply wt_elab_equation with (G:=G) in Helab; auto.
    - (* wc_node n *)
      constructor; simpl;      
        repeat match goal with H:OK _ = _ |- _ =>
          symmetry in H; monadInv1 H end;
        NamedDestructCases; intros; subst;
          MassageElabs outputs locals inputs;
          assert (Forall (fun yv=>PM.find (fst yv) env = Some (snd yv))
                         (xin ++ xvar ++ xout)) as Hf
              by repeat (apply Forall_app; split; auto);
          clear Hf_in Hf_var Hf_out;
          rewrite Hin, Hout, Hvar in Helab_var.
      + apply permutation_forall_elements in Hf.
        2:now rewrite <-Helab_var, map_app, map_app,
          Permutation_app_comm, Permutation_app_assoc.
        now rewrite Hf.
      + apply permutation_forall_elements in Hf.
        2:now rewrite <-Helab_var, map_app, map_app,
          Permutation_app_comm, Permutation_app_assoc.
        apply Forall_forall.
        intros y Hxin.
        rewrite Hf.
        apply mmap_inversion in Helabs.
        apply Coqlib.list_forall2_in_right with (1:=Helabs) in Hxin.
        destruct Hxin as (aeq & Hxin & Helab).
        apply wc_elab_equation in Helab; auto.
      + match goal with H:mmap (fun xtc=>assert_clock _ _ _ _) xin = _ |- _
                        => apply mmap_inversion in H; rename H into Hbase end.
        apply all_In_Forall.
        intros x Hxin.
        apply Coqlib.list_forall2_in_left with (2:=Hxin) in Hbase.
        destruct Hbase as (ok & ? & Hbase).
        now apply assert_clock_eq in Hbase.
      + match goal with H:mmap (fun xtc=>assert_clock _ _ _ _) xout = _ |- _
                        => apply mmap_inversion in H; rename H into Hbase end.
        apply all_In_Forall.
        intros x Hxin.
        apply Coqlib.list_forall2_in_left with (2:=Hxin) in Hbase.
        destruct Hbase as (ok & ? & Hbase).
        now apply assert_clock_eq in Hbase.
  Qed.

End ElabDeclaration.

Local Obligation Tactic :=
  Tactics.program_simpl;
    match goal with H:OK _ = _ |- _ =>
                    symmetry in H; monadInv H; NamedDestructCases end;
    simpl in *; unfold find_node_interface in *;
      match goal with H:match ?x with _ => _ end = Error _ |- _ =>
                      destruct x eqn:Hfind; try discriminate; clear H end.

Program Fixpoint elab_declarations'
        (G: global) (nenv: PM.t (list type * list type))
        (WTG: wt_global G /\ wc_global G) (Hnenv: Is_interface_map G nenv)
        (decls: list LustreAst.declaration)
  : res {G' | wt_global G' /\ wc_global G'} :=
  match decls with
  | nil => OK (exist _ G WTG)
  | d::ds =>
    match (do n <- elab_declaration _ _ Hnenv d;
             let loc := declaration_loc d in
             if find_node_interface nenv loc n.(n_name)
             then Error (err_loc loc (MSG "duplicate definition for "
                                          :: CTX n.(n_name) :: nil))
             else OK n) with
    | OK n => elab_declarations' (n::G)
                                 (PM.add n.(n_name)
                                         (map dty n.(n_in),
                                          map dty n.(n_out)) nenv) _ _ ds
    | Error e => Error e
    end
  end.
Next Obligation.
  split.
  - constructor; auto.
    now apply Hnenv.
  - constructor; auto.
Qed.
Next Obligation.
  split.
  - intros ** Hf.
    destruct (ident_eq_dec f n.(n_name)) as [He|Hne].
    + subst. rewrite PM.gss in Hf.
      injection Hf; intros; subst tysout tysin; clear Hf.
      exists n.
      repeat split.
      * unfold find_node, find.
        now rewrite ident_eqb_refl.
      * apply Forall2_swap_args, Forall2_map_1, Forall2_same, all_In_Forall;
          auto.
      * apply Forall2_swap_args, Forall2_map_1, Forall2_same, all_In_Forall;
          auto.
    + rewrite PM.gso in Hf; auto.
      destruct Hnenv as (Hnenv & ?).
      clear EQ.
      specialize (Hnenv _ _ _ Hf).
      destruct Hnenv as (n' & ? & ? & ?).
      exists n'. split; auto.
      unfold find_node, find.
      apply not_eq_sym, ident_eqb_neq in Hne.
      rewrite Hne; auto.
  - intros f Hf.
    destruct (ident_eq_dec f n.(n_name)) as [He|Hne].
    + subst. rewrite PM.gss in Hf. discriminate.
    + rewrite PM.gso in Hf; auto.
      constructor; auto.
      apply Hnenv; auto.
Qed.

Definition elab_declarations (decls: list LustreAst.declaration)
  : res {G | wt_global G /\ wc_global G} :=
  elab_declarations' [] (PM.empty (list type * list type))
                     (conj wtg_nil wc_global_nil)
                     Is_interface_map_empty decls.

