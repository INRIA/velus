From Coq Require Import String.
From Velus Require Instantiator.

From Velus Require Import Lustre.Parser.LustreAst.
From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.

Module Import CESyn := Instantiator.CE.Syn.
Module Import Syn := Instantiator.NL.Syn.
Module Import Defs := Instantiator.NL.IsD.

Import Interface.Op.
Import Interface.OpAux.
Import Instantiator.CE.Typ.
Import Instantiator.NL.Typ.
Import Instantiator.CE.Clo.
Import Instantiator.NL.Clo.
Import Instantiator.NL.Norm.

Import Env.Notations.

From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From compcert Require cfrontend.Cop.
From compcert Require cparser.Cabs.

From Coq Require Import Permutation.

From compcert Require Import common.Errors.
Local Open Scope error_monad_scope.

(* Elaborate an AST into a well-typed and well-clocked NLustre program. *)

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

Parameter do_add_when_to_constants : unit -> bool.

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
           (nenv: Env.t (list (ident * (type * clock))
                        * list (ident * (type * clock)))) : Prop :=
  (forall f tcin tcout,
      Env.find f nenv = Some (tcin, tcout) ->
      (exists n, find_node f G = Some n /\ tcin = n.(n_in) /\ tcout = n.(n_out)))
  /\ (forall f, Env.find f nenv = None -> Forall (fun n=> f <> n.(n_name)) G).

Lemma Is_interface_map_empty:
  Is_interface_map [] (Env.empty _).
Proof.
  split; setoid_rewrite Env.gempty; intros; try discriminate; auto.
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

Definition all_wt_clock (env: Env.t (type * clock)) : Prop :=
  forall x ty ck, Env.find x env = Some (ty, ck) ->
                  wt_clock (idty (Env.elements env)) ck.

Definition all_wc_clock (env: Env.t (type * clock)) : Prop :=
  forall x ty ck, Env.find x env = Some (ty, ck) ->
                  wc_clock (idck (Env.elements env)) ck.

Section ElabExpressions.

  (* Map variable names to their types and clocks. *)
  Variable env : Env.t (type * clock).

  (* Preceding dataflow program. *)
  Variable G : global.

  (* Map node names to input and output types. *)
  Variable nenv : Env.t (list (ident * (type * clock))
                         * list (ident * (type * clock))).

  Hypothesis wt_cenv : all_wt_clock env.

  Hypothesis wc_cenv : all_wc_clock env.

  Hypothesis wt_nenv : Is_interface_map G nenv.

  Definition find_var (loc: astloc) (x: ident) : res (type * clock) :=
    match Env.find x env with
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
    : res (list (ident * (type * clock)) * list (ident * (type * clock))) :=
    match Env.find f nenv with
    | None => Error (err_loc loc (MSG "node " :: CTX f :: msg " not found."))
    | Some tcs => OK tcs
    end.

  Lemma wt_clock_find_var:
    forall loc x ty ck,
      find_var loc x = OK (ty, ck) -> wt_clock (idty (Env.elements env)) ck.
  Proof.
    intros * Hfind.
    apply wt_cenv with (x:=x) (ty:=ty).
    unfold find_var in Hfind.
    destruct (Env.find x env); try discriminate.
    now monadInv Hfind.
  Qed.

  Lemma find_var_in:
    forall loc x ty ck,
      find_var loc x = OK (ty, ck) ->
      In (x, (ty, ck)) (Env.elements env).
  Proof.
    unfold find_var.
    intros loc x ty ck Hfind.
    NamedDestructCases.
    apply Env.elements_correct with (1:=Heq).
  Qed.

  Lemma find_var_type:
    forall loc x ty ck,
      find_var loc x = OK (ty, ck) ->
      In (x, ty) (idty (Env.elements env)).
  Proof.
    intros * Hfind.
    apply find_var_in in Hfind.
    now apply In_idty_exists; exists ck.
  Qed.

  Lemma find_var_clock:
    forall loc x ty ck,
      find_var loc x = OK (ty, ck) ->
      In (x, ck) (idck (Env.elements env)).
  Proof.
    intros * Hfind.
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

  (* Add [when]s around [e], assumed to be on the base clock, so that it
     has the given clock [ck]. *)
  Fixpoint build_whens (loc: astloc) (e: exp) (ck: clock) : exp :=
    match ck with
    | Cbase => e
    | Con ck' x b => Ewhen (build_whens loc e ck') x b
    end.

  Definition add_whens (loc: astloc) (ck: clock) (c: const) : (exp * clock) :=
    if do_add_when_to_constants tt
    then (build_whens loc (Econst c) ck, ck)
    else (Econst c, Cbase).

  Fixpoint elab_exp (eck : clock) (ae: LustreAst.expression) {struct ae}
                                                        : res (exp * clock) :=
    match ae with
    | CONSTANT c loc => OK (add_whens loc eck (elab_constant loc c))
    | VARIABLE x loc =>
      do (ty, ck) <- find_var loc x;
      OK (Evar x ty, ck)
    | WHEN [ae'] x b loc =>
      do (xty, xck) <- find_var loc x;
      do ok <- assert_type loc x xty bool_type;
      do (e', eck) <- elab_exp xck ae';
      if eck ==b xck then OK (Ewhen e' x b, Con xck x b)
      else Error (err_loc loc (MSG "badly clocked when: " :: msg_of_clocks eck xck))
    | UNARY aop [ae'] loc =>
      let op := elab_unop aop in
      do (e', ck) <- elab_exp eck ae';
      do ty' <- find_type_unop loc op (typeof e');
      OK (Eunop op e' ty', ck)
    | CAST aty' [ae'] loc =>
      let ty' := elab_type aty' in
      do (e', ck) <- elab_exp eck ae';
      OK (Eunop (CastOp ty') e' ty', ck)
    | BINARY aop [ae1] [ae2] loc =>
      let op := elab_binop aop in
      do (e1, ck1) <- elab_exp eck ae1;
      do (e2, ck2) <- elab_exp eck ae2;
      do ty' <- find_type_binop loc op (typeof e1) (typeof e2);
      if ck1 ==b ck2 then OK (Ebinop op e1 e2 ty', ck1)
      else Error (err_loc loc (MSG "badly clocked operator: "
                                   :: msg_of_clocks ck1 ck2))
    | _ => Error (err_loc (expression_loc ae) (msg "expression not normalized"))
    end.

  Fixpoint elab_cexp (eck : clock) (ae: LustreAst.expression) {struct ae}
                                                        : res (cexp * clock) :=
    match ae with
    | MERGE x [aet] [aef] loc =>
      do (xty, xck) <- find_var loc x;
      do ok <- assert_type loc x xty bool_type;
      do (et, ckt) <- elab_cexp (Con xck x true) aet;
      do (ef, ckf) <- elab_cexp (Con xck x false) aef;
      if typeofc et ==b typeofc ef
      then if (ckt ==b (Con xck x true))
           then if (ckf ==b (Con xck x false))
                then OK (Emerge x et ef, xck)
                else Error (err_loc loc (MSG "badly clocked merge false branch: "
                                         :: msg_of_clocks (Con xck x false) ckf))
           else Error (err_loc loc (MSG "badly clocked merge true branch: "
                                        :: msg_of_clocks (Con xck x true) ckt))
      else Error (err_loc loc (msg "badly typed merge"))
    | IFTE [ae] [aet] [aef] loc =>
      do (e, ck) <- elab_exp eck ae;
      do (et, ckt) <- elab_cexp eck aet;
      do (ef, ckf) <- elab_cexp eck aef;
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
      do (e, ck) <- elab_exp eck ae;
      OK (Eexp e, ck)
    end.

  Definition assert_exp_type (loc: astloc) (e: exp) (ty: type) : res unit :=
    if typeof e ==b ty then OK tt
    else Error (err_loc loc (MSG "badly typed argument: " :: msg_of_types ty (typeof e))).

  Fixpoint find_base (ock: clock) (lck: clock) : clock :=
    match ock, lck with
    | Cbase, _ => lck
    | Con ock' _ _, Cbase => Cbase
    | Con ock' _ _, Con lck' _ _ => find_base ock' lck'
    end.

  Fixpoint make_imap (s: Env.t ident)
                     (iface: list (ident * (type * clock)))
                     (args: list LustreAst.expression) : Env.t ident :=
    match iface, args with
    | (x, _)::xs, (VARIABLE y loc)::es => make_imap (Env.add x y s) xs es
    | _::xs, _::es => make_imap s xs es
    | _, _ => s
    end.

  Fixpoint make_omap (s: Env.t ident)
                     (iface: list (ident * (type * clock)))
                     (ys: list ident) : Env.t ident :=
    match iface, ys with
    | (x, _)::iface, y::ys => make_omap (Env.add x y s) iface ys
    | _, _ => s
    end.

  Fixpoint inst_clock (base: clock) (sub: Env.t ident) (loc : astloc) (ck: clock)
                                                               : res clock :=
    match ck with
    | Cbase => OK base
    | Con ck' x b =>
      do sck' <- inst_clock base sub loc ck';
      match Env.find x sub with
      | None => Error (err_loc loc (MSG "The " :: CTX x
                        :: msg " argument must be instantiated with a variable."))
      | Some y =>
        (* Check for [wt_clock] and [wc_clock], though it should be possible to
           guarantee these by proof. *)
        do (xty, xck) <- find_var loc y;
        do ok <- assert_type loc x xty bool_type;
        do ok <- assert_clock loc x xck sck';
        OK (Con sck' y b)
      end
    end.

  Fixpoint check_noops (loc: astloc) (ick: clock) (e: exp) : res unit :=
    match ick, e with
    | Cbase, _ => OK tt
    | _, Econst _ => OK tt
    | _, Evar _ _ => OK tt
    | Con ick' _ _, Ewhen e' _ _ => check_noops loc ick' e'
    | _, _ => Error (err_loc loc (msg
                         "operators are not permitted in normalized arguments"))
    end.

  Fixpoint elab_exps (loc: astloc) (instck : astloc -> clock -> res clock)
                     (iface : list (ident * (type * clock)))
                     (aes: list expression) : res (list exp) :=
    match iface, aes with
    | nil, nil => OK nil
    | (i, (ity, ick))::iface, ae::aes =>
      do ck' <- instck (expression_loc ae) ick;
      do (e, ck) <- elab_exp ck' ae;
      do _ <- check_noops loc ick e;
      if ck ==b ck'
      then do ok <- assert_exp_type (expression_loc ae) e ity;
           do es <- elab_exps loc instck iface aes;
           OK (e::es)
      else Error (err_loc loc ((MSG "ill-clocked argument expression "
                                        :: msg_of_clocks ck ck')))
    | _, _ => Error (err_loc loc (msg "wrong number of arguments"))
    end.

  Fixpoint check_result_list (loc: astloc) (instck: astloc -> clock -> res clock)
                             (iface: list (ident * (type * clock)))
                             (xs: list ident) : res PS.t :=
    match iface, xs with
    | nil, nil => OK PS.empty
    | (i, (ity, ick))::iface, x::xs =>
      do ck' <- instck loc ick;
      do (xty, xck) <- find_var loc x;
      do ok <- assert_type loc x xty ity;
      do ok <- assert_clock loc x xck ck';
      do others <- check_result_list loc instck iface xs;
      if PS.mem x others
      then Error (err_loc loc (msg "duplicate variable in pattern"))
      else OK (PS.add x others)
    | _, _ => Error (err_loc loc (msg "wrong number of pattern variables"))
    end.

  Definition elab_constant_with_cast (loc: astloc) (ae: LustreAst.expression)
                                                              : res constant :=
    match ae with
    | CAST aty [CONSTANT ac _] loc =>
      cast_constant loc (elab_constant loc ac) (elab_type aty)
    | CONSTANT ac loc =>
      OK (elab_constant loc ac)
    | _ => Error (err_loc loc
                    (msg "fbys only take single (casted) constants at left."))
    end.

  Definition elab_equation (aeq: LustreAst.equation) : res equation :=
    let '(xs, aes, loc) := aeq in
    do x <- match xs with
            | x::xs => OK x
            | _ => Error (err_loc loc (msg "at least one output is required"))
            end;
    do ae <- match aes with
             | [ae] => OK ae
             | _ => Error (err_loc loc (msg "equation not normalized"))
             end;
    do (xty, xck) <- find_var loc x;
    match ae with
    | APP f aes r loc =>
        do (tyck_in, tyck_out) <- find_node_interface loc f;
        do bck <- match tyck_out with
                 | (_, (_, yck))::_ => OK (find_base yck xck)
                 | _ => Error (err_loc loc (MSG "not enough outputs in " :: [CTX f]))
                 end;
        let isub := make_imap (Env.empty _) tyck_in aes in
        let osub := make_omap isub tyck_out xs in
        do es <- elab_exps loc (inst_clock bck isub) tyck_in aes;
        do ok <- check_result_list loc (inst_clock bck osub) tyck_out xs;
        match r with
        | [] => OK (EqApp xs bck f es None)
        | [VARIABLE r loc'] =>
            do (rty, rck) <- find_var loc' r;
            do ok <- assert_type loc' r rty bool_type;
            OK (EqApp xs bck f es (Some (r, rck)))
        | _ => Error (err_loc (expression_loc ae)
                             (msg "reset expression not normalized"))
        end

    | FBY [ae0] [ae] loc =>
      do v0 <- elab_constant_with_cast loc ae0;
      let v0ty := type_const v0 in
      do (e, eck) <- elab_exp xck ae;
      do ok <- assert_type loc x xty v0ty;
      if typeof e ==b v0ty
      then if eck ==b xck
           then OK (EqFby x xck v0 e)
           else Error (err_loc loc (MSG "ill-clocked fby expression for "
                                      :: CTX x :: MSG " "
                                      :: msg_of_clocks xck eck))
      else Error (err_loc loc (MSG "ill-typed fby expression for "
                                   :: CTX x :: msg_of_types v0ty (typeof e)))
    | FBY _ _ loc =>
      Error (err_loc (expression_loc ae) (msg "fby not normalized"))

    | _ =>
      do (e, eck) <- elab_cexp xck ae;
      do ok <- assert_type loc x xty (typeofc e);
      if eck ==b xck
      then OK (EqDef x xck e)
      else Error (err_loc loc (MSG "ill-clocked expression for "
                                   :: CTX x :: MSG " "
                                   :: msg_of_clocks xck eck))
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

  Local Ltac MonadInvLExprWithLists :=
    match goal with
    | H:elab_exp _ (UNARY _ [_] _) = OK _ |- _ => monadInv H
    | H:elab_exp _ (UNARY _ [] _) = OK _ |- _ => monadInv H
    | H:elab_exp _ (UNARY _ (_::_::_) _) = OK _ |- _ => monadInv H
    | H:elab_exp _ (UNARY _ (_::?es) _) = OK _ |- _ =>
      destruct es; MonadInvLExprWithLists
    | H:elab_exp _ (UNARY _ ?es _) = OK _ |- _ =>
      destruct es; MonadInvLExprWithLists

    | H:elab_exp _ (BINARY _ [_] [_] _) = OK _ |- _ => monadInv H
    | H:elab_exp _ (BINARY _ [] _ _) = OK _ |- _ => monadInv H
    | H:elab_exp _ (BINARY _ (_::_) [] _) = OK _ |- _ => monadInv H
    | H:elab_exp _ (BINARY _ (_::?es1) [] _) = OK _ |- _ =>
      destruct es1; MonadInvLExprWithLists
    | H:elab_exp _ (BINARY _ (_::_::_) _ _) = OK _ |- _ => monadInv H
    | H:elab_exp _ (BINARY _ _ (_::_::_) _) = OK _ |- _ => monadInv H
    | H:elab_exp _ (BINARY _ (_::?es1) (_::?es2) _) = OK _ |- _ =>
      destruct es1; destruct es2; MonadInvLExprWithLists
    | H:elab_exp _ (BINARY _ ?es1 ?es2 _) = OK _ |- _ =>
      destruct es1; destruct es2; MonadInvLExprWithLists

    | H:elab_exp _ (CAST _ [_] _) = OK _ |- _ => monadInv H
    | H:elab_exp _ (CAST _ [] _) = OK _ |- _ => monadInv H
    | H:elab_exp _ (CAST _ (_::_::_) _) = OK _ |- _ => monadInv H
    | H:elab_exp _ (CAST _ (_::?es) _) = OK _ |- _ =>
      destruct es; MonadInvLExprWithLists
    | H:elab_exp _ (CAST _ ?es _) = OK _ |- _ =>
      destruct es; MonadInvLExprWithLists

    | H:elab_exp _ (FBY [_] [_] _) = OK _ |- _ => monadInv H
    | H:elab_exp _ (FBY [] _ _) = OK _ |- _ => monadInv H
    | H:elab_exp _ (FBY (_::_) [] _) = OK _ |- _ => monadInv H
    | H:elab_exp _ (FBY (_::?es1) [] _) = OK _ |- _ =>
      destruct es1; MonadInvLExprWithLists
    | H:elab_exp _ (FBY (_::_::_) _ _) = OK _ |- _ => monadInv H
    | H:elab_exp _ (FBY _ (_::_::_) _) = OK _ |- _ => monadInv H
    | H:elab_exp _ (FBY (_::?es1) (_::?es2) _) = OK _ |- _ =>
      destruct es1; destruct es2; MonadInvLExprWithLists
    | H:elab_exp _ (FBY ?es1 ?es2 _) = OK _ |- _ =>
      destruct es1; destruct es2; MonadInvLExprWithLists

    | H:elab_exp _ (WHEN [_] _ _ _) = OK _ |- _ => monadInv H
    | H:elab_exp _ (WHEN [] _ _ _) = OK _ |- _ => monadInv H
    | H:elab_exp _ (WHEN (_::_::_) _ _ _) = OK _ |- _ => monadInv H
    | H:elab_exp _ (WHEN (_::?es) _ _ _) = OK _ |- _ =>
      destruct es; MonadInvLExprWithLists
    | H:elab_exp _ (WHEN ?es _ _ _) = OK _ |- _ =>
      destruct es; MonadInvLExprWithLists

    | H:elab_exp _ _ = OK _ |- _ => monadInv H
    end.

  Lemma wt_inst_clock:
    forall bck sub loc ck ck',
      wt_clock (idty (Env.elements env)) bck ->
      inst_clock bck sub loc ck = OK ck' ->
      wt_clock (idty (Env.elements env)) ck'.
  Proof.
    induction ck; intros ck' WT IC; inv IC; auto.
    monadInv1 H0. NamedDestructCases. monadInv1 EQ0.
    apply find_var_type in EQ1.
    apply assert_type_eq in EQ0; subst; auto.
  Qed.

  Lemma wc_inst_clock:
    forall bck sub loc ck ck',
      wc_clock (idck (Env.elements env)) bck ->
      inst_clock bck sub loc ck = OK ck' ->
      wc_clock (idck (Env.elements env)) ck'.
  Proof.
    induction ck; intros ck' WT IC; inv IC; auto.
    monadInv1 H0. NamedDestructCases. monadInv1 EQ0.
    apply find_var_clock in EQ1.
    apply assert_clock_eq in EQ2; subst; auto.
  Qed.

  Lemma wt_add_whens:
    forall vars loc eck c e ck,
      wt_clock vars eck ->
      add_whens loc eck (elab_constant loc c) = (e, ck) ->
      wt_exp vars e.
  Proof.
    unfold add_whens. destruct (do_add_when_to_constants tt).
    2:now inversion_clear 2; auto.
    induction eck; intros c e ck WTC AW. now inv AW; auto.
    inv AW. inv WTC. constructor; auto.
    eapply IHeck; eauto.
  Qed.

  Lemma wc_add_whens:
    forall vars loc eck c e ck,
      wc_clock vars eck ->
      add_whens loc eck (elab_constant loc c) = (e, ck) ->
      wc_exp vars e ck.
  Proof.
    unfold add_whens. destruct (do_add_when_to_constants tt).
    2:now inversion_clear 2; auto.
    induction eck; intros c e ck WTC AW. now inv AW; auto.
    inv AW. inv WTC. constructor; auto.
    eapply IHeck; eauto.
  Qed.

  Lemma wt_elab_exp:
    forall ae eck e ck,
      wt_clock (idty (Env.elements env)) eck ->
      elab_exp eck ae = OK (e, ck) ->
      wt_exp (idty (Env.elements env)) e.
  Proof.
    induction ae using expression_ind2;
      intros eck e ck WTC Helab; MonadInvLExprWithLists;
      NamedDestructCases; try constructor; intros; subst;
      repeat progress match goal with H:Forall _ [_] |- _ => inv H end;
      eauto using wt_exp, find_var_type, assert_type_eq.
    - unfold find_type_unop in EQ1.
      rewrite type_unop'_correct in EQ1.
      now DestructCases.
    - unfold find_type_binop in EQ0.
      match goal with H:match ?e with _ => _ end = _ |- _ =>
                      destruct e eqn:He; try discriminate; injection H end.
      intro; subst.
      rewrite type_binop'_correct in He.
      constructor; eauto.
    - now rewrite type_castop.
    - eapply wt_add_whens; eauto.
    - apply assert_type_eq in EQ1; subst.
      constructor; eauto using find_var_type, wt_clock_find_var.
  Qed.

  Lemma In_env_elements_wc_clock:
    forall x ck,
      In (x, ck) (idck (Env.elements env)) ->
      wc_clock (idck (Env.elements env)) ck.
  Proof.
    intros x ck Ix.
    apply In_idck_exists in Ix as (ty & WC).
    now apply Env.elements_complete, wc_cenv in WC.
  Qed.

  Lemma wc_elab_exp:
    forall ae eck e ck,
      wc_clock (idck (Env.elements env)) eck ->
      elab_exp eck ae = OK (e, ck) ->
      wc_exp (idck (Env.elements env)) e ck.
  Proof.
    induction ae using expression_ind2; intros eck e ck WC Helab;
      MonadInvLExprWithLists; NamedDestructCases;
        try constructor; intros; subst;
          repeat match goal with
             | H:Forall _ [_] |- _ => inv H
             | H:(_ ==b _) = true |- _ =>
               rewrite equiv_decb_equiv in H; rewrite H in *; clear H
             | H:find_var _ _ = OK _ |- _ =>
               apply find_var_clock in H
             end;
          eauto using wc_exp, wc_add_whens.
    take (forall eck e ck, wc_clock _ _ -> elab_exp _ _ = OK _ -> wc_exp _ _ _)
         and apply it in EQ0; auto.
    eauto using In_env_elements_wc_clock.
  Qed.

  Lemma wt_inst_clock_env:
    forall loc env1 env2 bck s ck sck,
      wt_clock env2 bck ->
      wt_clock env1 ck ->
      (forall x y ty,
          Env.find x s = Some y ->
          In (x, ty) env1 ->
          In (y, ty) env2) ->
      inst_clock bck s loc ck = OK sck ->
      wt_clock env2 sck.
  Proof.
    intros * Hbck Hck Hf Hinst.
    revert ck sck Hinst Hck.
    induction ck; simpl; intros sck Hm Hck.
    now inversion Hm; subst; auto.
    monadInv Hm. NamedDestructCases.
    inversion_clear Hck as [|? ? ? ? Hwtck].
    specialize (IHck _ EQ Hwtck).
    monadInv EQ0.
    eapply Hf in Heq; eauto with nltyping.
  Qed.

  Lemma wt_elab_exps:
    forall loc instck iface aes es,
      (forall loc ck ck', instck loc ck = OK ck' -> wt_clock (idty (Env.elements env)) ck') ->
      elab_exps loc instck iface aes = OK es ->
      (Forall (wt_exp (idty (Env.elements env))) es
       /\ Forall2 (fun xtc e=> typeof e = fst (snd xtc)) iface es).
  Proof.
    intros loc instck iface aes es Hinst; revert aes es.
    induction iface; simpl; intros * Helab; DestructCases; auto.
    monadInv Helab.
    NamedDestructCases.
    monadInv EQ3.
    apply wt_elab_exp in EQ1.
    - specialize (IHiface _ _ EQ3) as (? & ?).
      unfold assert_exp_type in EQ2.
      NamedDestructCases. rewrite equiv_decb_equiv in Heq0; auto.
    - now apply Hinst in EQ.
  Qed.

  Lemma inst_clock_instck:
    forall bck sub loc ck ck',
      inst_clock bck sub loc ck = OK ck' ->
      instck bck (fun x => Env.find x sub) ck = Some ck'.
  Proof.
    induction ck; simpl. now inversion 1; auto.
    intros ck' HH.
    monadInv HH. DestructCases.
    monadInv EQ0. now apply IHck in EQ as ->.
  Qed.

  Lemma make_imap_InMembers:
    forall xs aes x,
      NoDupMembers xs ->
      Env.In x (make_imap (Env.empty _) xs aes) ->
      InMembers x xs.
  Proof.
    intros xs aes x ND Ix.
    assert (forall x, InMembers x xs -> ~Env.In x (Env.empty ident)) as NI
        by (intros y Iy EE; now apply Env.Props.P.F.empty_in_iff in EE).
    cut (Env.In x (Env.empty ident) \/ InMembers x xs).
    now destruct 1 as [HH|HH]; [apply Env.Props.P.F.empty_in_iff in HH|auto].
    revert aes x ND NI Ix. generalize (Env.empty ident).
    induction xs as [|(x, (xt, xc)) xs IH]; simpl; auto.
    intros s aes y ND IME Hy. inversion_clear ND as [|??? ND1 ND2].
    destruct aes; auto.
    destruct e; try (now apply IH in Hy as [?|?]; auto).
    apply IH in Hy as [Hy|Hy]; auto.
    - destruct (ident_eq_dec x y); [now subst; auto|].
      apply Env.Props.P.F.add_neq_in_iff in Hy; auto.
    - intros z Iz EE.
      apply Env.Props.P.F.add_in_iff in EE as [EE|EE]; [now subst; auto|].
      apply IME in EE; auto.
  Qed.

  Lemma make_imap_omap_refines:
    forall n aes xs,
      make_imap (Env.empty _) n.(n_in) aes ⊑ make_omap (make_imap (Env.empty _) n.(n_in) aes) n.(n_out) xs.
  Proof.
    intros n aes xs.
    assert (forall x, InMembers x n.(n_out) -> ~Env.In x (make_imap (Env.empty _) n.(n_in) aes)) as HH.
    { pose proof n.(n_nodup) as ND.
      intros x Ix EE. apply make_imap_InMembers in EE.
      2:now apply NoDupMembers_app_l in ND.
      apply NoDupMembers_app_InMembers with (x0:=x) in ND; auto.
      apply ND, InMembers_app; auto. }
    pose proof (NoDupMembers_n_out n) as ND.
    revert HH ND. generalize (make_imap (Env.empty ident) n.(n_in) aes); clear aes.
    generalize (n.(n_out)); clear n.
    induction xs as [|x xs IH]; intros ys s HH ND;
      destruct ys as [|(y, (yt, yc)) ys]; simpl; auto.
    inversion_clear ND as [|??? ND1 ND2].
    rewrite <-IH; auto.
    now apply Env.refines_add_right; auto using inmembers_eq.
    setoid_rewrite Env.Props.P.F.add_in_iff.
    intros z Iz [H|H]; subst; auto.
    eapply HH; eauto using inmembers_cons.
  Qed.

  Lemma inst_clock_refines:
    forall s1 s2 bck loc ck ck',
      s1 ⊑ s2 ->
      inst_clock bck s1 loc ck = OK ck' ->
      inst_clock bck s2 loc ck = OK ck'.
  Proof.
    induction ck; auto.
    simpl; intros ck' RS HI.
    monadInv HI.
    apply IHck in EQ as ->; auto; simpl.
    NamedDestructCases. apply RS in Heq as (? & ? & ->).
    now subst.
  Qed.

  Lemma elab_exps_length:
    forall loc sub iface aes es,
      elab_exps loc sub iface aes = OK es ->
      length iface = length es.
  Proof.
    induction iface.
    now destruct aes; simpl; inversion 1; auto.
    destruct aes; simpl; destruct a, p.
    now inversion 1.
    intros es HH. monadInv HH. NamedDestructCases. monadInv EQ3.
    now apply IHiface in EQ3 as ->.
  Qed.

  Lemma elab_exps_In_combine:
    forall loc instck iface aes es x xt xc e,
      elab_exps loc instck iface aes = OK es ->
      In (x, (xt, xc), e) (combine iface es) ->
      exists ae ck eck, In (x, (xt, xc), ae) (combine iface aes)
                   /\ elab_exp eck ae = OK (e, ck)
                   /\ instck (expression_loc ae) xc = OK ck.
  Proof.
    induction iface as [|(x, (xt, xc)) iface IH].
    now destruct aes; inversion 1; simpl; contradiction.
    simpl; intros aes es y yt yc e EE Iy.
    NamedDestructCases. monadInv EE. NamedDestructCases. monadInv EQ3.
    apply in_inv in Iy as [Iy|Iy].
    - inv Iy.
      rewrite equiv_decb_equiv in Heq0; rewrite Heq0 in *; clear Heq0.
      destruct x3, x4.
      rename x5 into es, x0 into ck.
      exists e0, ck, ck. repeat split; auto. now constructor.
    - eapply IH in EQ3 as (ae & ck & eck & HH1 & HH2 & HH3); eauto.
      exists ae, ck, eck. repeat split; auto. now constructor 2.
  Qed.

  Lemma find_make_imap_gso:
    forall x iface aes s,
      ~InMembers x iface ->
      Env.find x (make_imap s iface aes) = Env.find x s.
  Proof.
    induction iface as [|(y, (yt, yc)) iface IH]; intros * NM; auto.
    destruct aes as [|ae aes]; auto. simpl.
    assert (~InMembers x iface) as NMx
        by (now intro IMx; apply NM; constructor 2).
    destruct ae; rewrite IH; auto.
    apply Env.gso. intro; subst.
    now apply NM; subst; constructor.
  Qed.

  Lemma find_make_imap_gss:
    forall x tc ae iface aes s,
      NoDupMembers iface ->
      In (x, tc, ae) (combine iface aes) ->
      Env.find x (make_imap s iface aes) =
      (match ae with VARIABLE y loc => Some y | _ => Env.find x s end).
  Proof.
    intros x (xt, xc) ae.
    induction iface as [|(y, (yt, yc)) iface IH]. now inversion 2.
    destruct aes as [|ae' aes]. now inversion 2.
    inversion_clear 1 as [|??? ND1 ND2].
    destruct 1 as [HH|HH].
    - inv HH. simpl.
      destruct ae; rewrite find_make_imap_gso; auto.
      now rewrite Env.gss.
    - assert (x <> y) as Nxy
          by (now intro; subst; apply in_combine_l, In_InMembers in HH).
      simpl. destruct ae'; rewrite IH; auto.
      destruct ae; try rewrite Env.gso; auto.
  Qed.

  Lemma check_noops_correct:
    forall loc t ick e,
      check_noops loc ick e = OK t ->
      noops_exp ick e.
  Proof.
    induction ick; simpl; auto.
    destruct t. destruct e; auto; inversion 1.
  Qed.

  Lemma elab_exps_noops:
    forall loc bck sub iface aes es,
      elab_exps loc (inst_clock bck sub) iface aes = OK es ->
      Forall2 noops_exp (map (fun '(_, (_, ck)) => ck) iface) es.
  Proof.
    induction iface as [|(x, (xt, xc)) iface IH].
    now destruct aes; simpl; inversion 1; auto.
    destruct aes as [|ae aes]; simpl. now inversion 1.
    intros es HH. monadInv HH. NamedDestructCases. monadInv EQ3.
    apply check_noops_correct in EQ0. constructor; auto.
    apply IH with (1:=EQ3).
  Qed.

  Lemma elab_exps_SameVar:
    forall loc bck iface aes es,
      NoDupMembers iface ->
      elab_exps loc (inst_clock bck (make_imap (Env.empty _) iface aes)) iface aes = OK es ->
      Forall2 (fun '(x, _) e => SameVar (Env.find x (make_imap (Env.empty _) iface aes)) e) iface es.
  Proof.
    intros * ND EE.
    apply all_In_Forall2. now apply elab_exps_length with (1:=EE).
    intros (x, (xt, xc)) e Ix.
    eapply elab_exps_In_combine with (2:=Ix) in EE as (ae & ck & eck & EE1 & EE2 & EE3).
    apply find_make_imap_gss with (s:=Env.empty ident) in EE1 as ->; auto.
    rewrite Env.gempty. destruct ae; auto using SameVar.
    simpl in EE2. monadInv EE2. constructor.
  Qed.

  Lemma elab_exps_wc:
    forall loc bck sub iface aes es,
      wc_clock (idck (Env.elements env)) bck ->
      elab_exps loc (inst_clock bck sub) iface aes = OK es ->
      Forall2 (fun '(x, (_, xck)) e =>
                 exists lck, wc_exp (idck (Env.elements env)) e lck
                        /\ instck bck (fun x => Env.find x sub) xck = Some lck)
              iface es.
  Proof.
    intros loc bck sub iface aes es WC; revert aes es.
    induction iface as [|(y, (yt, yc)) iface IH].
    now destruct aes; inversion 1; auto.
    destruct aes as [|ae aes]; simpl. now inversion 1.
    intros * Helab; DestructCases; auto.
    monadInv Helab. NamedDestructCases. monadInv EQ3.
    assert (WCI:=EQ); apply wc_inst_clock in WCI; auto.
    apply inst_clock_instck in EQ.
    apply wc_elab_exp in EQ1; auto.
    now rewrite equiv_decb_equiv in Heq; rewrite Heq in *; eauto.
  Qed.

  Lemma check_result_list_wc:
    forall loc bck sub oface xs s,
      check_result_list loc (inst_clock bck sub) oface xs = OK s ->
      Forall2 (fun '(y, _) x => Env.find y sub = Some x) oface xs ->
      Forall2 (fun '(y, (_, yck)) x =>
                 Env.find y sub = Some x
                 /\ exists xck, In (x, xck) (idck (Env.elements env))
                          /\ instck bck (fun x => Env.find x sub) yck = Some xck)
              oface xs.
  Proof.
    induction oface as [|(y, (yt, yc)) oface IH].
    now destruct xs; auto; inversion 1.
    destruct xs as [|x xs]. now inversion 1.
    intros s CR Hsub. simpl in CR. monadInv CR. NamedDestructCases.
    destruct x3, x4; rename x0 into ck, x1 into xt, x2 into xc, x5 into s.
    apply inst_clock_instck in EQ.
    apply find_var_clock in EQ1.
    apply assert_clock_eq in EQ2; subst.
    inv Hsub. constructor; eauto.
  Qed.

  Lemma find_make_omap_gso:
    forall x oface xs s,
      ~InMembers x oface ->
      Env.find x (make_omap s oface xs) = Env.find x s.
  Proof.
    induction oface as [|(y, (yt, yc)) oface IH]; intros * NM; auto.
    destruct xs as [|z xs]; auto. simpl.
    assert (~InMembers x oface) as NMx
        by (now intro IMx; apply NM; constructor 2).
    rewrite IH; auto.
    apply Env.gso. intro; subst.
    now apply NM; subst; constructor.
  Qed.

  Lemma find_make_omap:
    forall oface xs s,
      NoDupMembers oface ->
      length oface = length xs ->
      Forall2 (fun '(y, _) x => Env.find y (make_omap s oface xs) = Some x) oface xs.
  Proof.
    induction oface as [|(y, (yt, yc)) oface IH].
    now destruct xs; auto; inversion 2.
    destruct xs as [|x xs]. now inversion 2.
    intros s ND Hlen. inv Hlen.
    inversion_clear ND as [|??? ND1 ND2].
    constructor; eauto.
    simpl. rewrite find_make_omap_gso, Env.gss; auto.
  Qed.

  Lemma check_result_list_length:
    forall loc instck oface xs s,
      check_result_list loc instck oface xs = OK s ->
      length oface = length xs.
  Proof.
    induction oface. now destruct xs; inversion 1.
    destruct xs; simpl; destruct a, p. now inversion 1.
    intros s HH. monadInv HH. now apply IHoface in EQ3 as ->.
  Qed.

  Lemma wt_elab_cexp:
    forall ae e eck ck,
      wt_clock (idty (Env.elements env)) eck ->
      elab_cexp eck ae = OK (e, ck) ->
      wt_cexp (idty (Env.elements env)) e.
  Proof.
    induction ae using expression_ind2; intros e eck ck WTC Helab;
      try apply bind_inversion in Helab;
      try (destruct Helab as ((le & ck') & Helab & Hexp);
           monadInv Hexp);
      eauto using wt_elab_exp with nltyping.
    - destruct es; [inv Helab|]; destruct es; [|inv Helab].
      destruct ets; [inv Helab|]; destruct ets; [|inv Helab].
      destruct efs; [inv Helab|]; destruct efs; [|inv Helab].
      apply bind_inversion in Helab.
      destruct Helab as ((le & ck') & Helab & Hexp); monadInv Hexp.
      repeat match goal with H:Forall _ [_] |- _ => inv H end.
      NamedDestructCases.
      apply andb_prop in Heq; destruct Heq as (Hg1 & Hg2).
      rewrite equiv_decb_equiv in Hg1, Hg2.
      intros; subst.
      eauto using wt_elab_exp with nltyping.
    - destruct ets; [inv Helab|]; destruct ets; [|inv Helab].
      destruct efs; [inv Helab|]; destruct efs; [|inv Helab].
      repeat match goal with H:Forall _ [_] |- _ => apply Forall_inv in H end.
      simpl in Helab. monadInv Helab. NamedDestructCases.
      intro; subst e.
      take (find_var _ _ = OK _) and pose proof (find_var_clock _ _ _ _ it) as WC.
      apply In_idck_exists in WC as (? & WC).
      apply Env.elements_complete, wt_cenv in WC.
      take (find_var _ _ = OK _) and apply find_var_type in it.
      rewrite equiv_decb_equiv in Heq.
      apply assert_type_eq in EQ1; subst.
      apply H in EQ0; auto.
      apply H0 in EQ2; auto.
  Qed.

  Lemma wc_elab_cexp:
    forall ae e eck ck,
      wc_clock (idck (Env.elements env)) eck ->
      elab_cexp eck ae = OK (e, ck) ->
      wc_cexp (idck (Env.elements env)) e ck.
  Proof.
    induction ae using expression_ind2; simpl; intros e eck ck EE HH;
      try apply bind_inversion in HH;
      try (destruct HH as ((le & ck') & Helab & Hexp);
           monadInv Hexp);
      repeat match goal with
             | H:Forall _ [_] |- _ => apply Forall_inv in H
             | H:_ = OK _ |- _ => monadInv H
             | H:(_ ==b _) = true |- _ =>
               rewrite equiv_decb_equiv in H; rewrite H in *; clear H
             | H:find_var _ _ = OK _ |- _ =>
               apply find_var_clock in H
             | H:add_whens _ _ _ = _ |- _ => apply wc_add_whens with (1:=EE) in Heq
             | _ => NamedDestructCases; intros; subst
             end;
      eauto using wc_cexp, wc_exp, wc_elab_exp.
    - repeat constructor; auto.
      apply wc_elab_exp in EQ0; eauto using In_env_elements_wc_clock.
    - constructor; eauto using wc_clock, In_env_elements_wc_clock.
  Qed.

  Lemma check_result_list_Forall2:
    forall loc bck sub oface xs s,
      check_result_list loc (inst_clock bck sub) oface xs = OK s ->
      Forall2 (fun itc x => In (x, fst (snd itc)) (idty (Env.elements env))) oface xs
      /\ (forall x, PS.In x s <-> In x xs)
      /\ NoDup xs.
  Proof.
    induction oface as [|(y, (yt, yc)) oface IH]; simpl.
    - repeat split; DestructCases; auto using NoDup_nil.
      now apply not_In_empty.
      contradiction.
    - intros xs s Hcheck.
      DestructCases.
      match goal with H:_ = OK _ |- _ => monadInv H end.
      NamedDestructCases.
      apply IH in EQ3 as (Hin & Hset & Hnodup).
      apply PSE.MP.Dec.F.not_mem_iff in Heq. rewrite Hset in Heq.
      apply assert_type_eq in EQ0.
      subst.
      repeat split; eauto using find_var_type, find_var_clock;
        try rewrite PS.add_spec, Hset;
        try destruct 1; subst; eauto using NoDup with datatypes.
    Qed.

  Lemma wt_find_base:
    forall vars ick ck,
      wt_clock vars ck ->
      wt_clock vars (find_base ick ck).
  Proof.
    induction ick; auto.
    destruct ck; auto.
    inversion_clear 1; simpl; auto.
  Qed.

  Lemma wc_find_base:
    forall vars ick ck,
      wc_clock vars ck ->
      wc_clock vars (find_base ick ck).
  Proof.
    induction ick; auto.
    destruct ck; auto.
    inversion_clear 1; simpl; auto.
  Qed.

  Lemma wt_elab_equation:
    forall aeq eq,
      elab_equation aeq = OK eq ->
      wt_equation G (idty (Env.elements env)) eq.
  Proof.
    intros aeq eq Helab.
    destruct aeq as ((xs & ae) & loc).
    destruct ae; simpl in Helab.
    now monadInv Helab.
    repeat progress
             match goal with
             | H:bind _ _ = _ |- _ => monadInv H
             | H:bind2 _ _ = _ |- _ => monadInv H
             | H:elab_exp _ _ = OK _ |- _ => apply wt_elab_exp in H; auto
             | H:elab_cexp _ _ = OK _ |- _ => apply wt_elab_cexp in H; auto
             | H:find_var _ _ = OK _ |- _ =>
               pose proof (wt_clock_find_var _ _ _ _ H);
               apply find_var_type in H
             | H:assert_type _ _ _ _ = OK _ |- _ => apply assert_type_eq in H
             | H:_ ==b _ = true |- _ => rewrite equiv_decb_equiv in H
             | H:check_result_list _ _ _ _ = OK ?x |- _ =>
               apply check_result_list_Forall2 in H;
                 destruct H as (Hele & Hins & Hnodup)
             | _ => NamedDestructCases
             end; intros; subst; auto with nltyping;
      match goal with
      | H:elab_exps _ _ _ _ = OK _ |- _ =>
        apply wt_elab_exps in H as (? & ?);
          eauto using wt_inst_clock, wt_find_base
      end.
    - rename x0 into xin, l2 into xout, i into f, x5 into ein, l1 into xs,
      x2 into ck, a into loc'.
      unfold find_node_interface in EQ. NamedDestructCases.
      destruct wt_nenv as (wt_nenv' & ?).
      specialize (wt_nenv' f _ _ Heq).
      destruct wt_nenv' as (n & Hfind & Hin & Hout); clear wt_nenv.
      econstructor; eauto using wt_find_base.
      + rewrite Hout in Hele.
        apply Forall2_swap_args.
        apply Forall2_impl_In with (2:=Hele).
        intros (z, (zt, zc)) y Iz Iy Izy; auto.
      + apply Forall2_swap_args.
        rewrite Hin in H1.
        apply Forall2_impl_In with (2:=H1).
        intros (z, (zt, zc)) y Iz Iy Izy; auto.
    - rename x0 into xin, l3 into xout, i into f, x5 into ein, l1 into xs,
      x2 into ck, a into loc', i0 into r, x4 into rck.
      unfold find_node_interface in EQ. NamedDestructCases.
      destruct wt_nenv as (wt_nenv' & ?).
      specialize (wt_nenv' f _ _ Heq) as (n & Hfind & Hin & Hout); clear wt_nenv.
      econstructor; eauto using wt_find_base.
      + apply Forall2_swap_args. rewrite <-Hout.
        apply Forall2_impl_In with (2:=Hele).
        intros (z, (zt, zc)) y Iz Iy Izy; auto.
      + apply Forall2_swap_args. rewrite Hin in H2.
        apply Forall2_impl_In with (2:=H2).
        intros (z, (zt, zc)) y Iz Iy Izy; auto.
  Qed.

  Lemma find_node_interface_map:
    forall loc f tcin tcout,
      find_node_interface loc f = OK (tcin, tcout) ->
      exists n, find_node f G = Some n /\ tcin = n.(n_in) /\ tcout = n.(n_out).
  Proof.
    intros * FN. unfold find_node_interface in FN.
    destruct (Env.find f nenv) eqn:Ff; inv FN.
    now apply wt_nenv in Ff.
  Qed.

  Lemma elab_normal_args_eq:
    forall aeq eq,
      elab_equation aeq = OK eq ->
      normal_args_eq G eq.
  Proof.
    intros aeq eq Helab.
    destruct aeq as ((xs & ae) & loc).
    destruct ae; simpl in Helab;
      repeat progress
             match goal with
             | H:bind _ _ = _ |- _ => monadInv H
             | H:bind2 _ _ = _ |- _ => monadInv H
             | H:elab_exps _ _ _ _ = OK _ |- _ => apply elab_exps_noops in H
             | H:find_node_interface _ _ = OK _ |- _ =>
               apply find_node_interface_map in H as (? & ? & ? & ?)
             | _ => NamedDestructCases
             end; intros; subst; eauto using normal_args_eq.
  Qed.

  Lemma instck_refines:
    forall fb env1 env2 ck lck,
      instck fb (fun x => Env.find x env1) ck = Some lck ->
      env1 ⊑ env2 ->
      instck fb (fun x => Env.find x env2) ck = Some lck.
  Proof.
    induction ck; auto.
    simpl. destruct (instck fb (fun x => Env.find x env1) ck). 2:now inversion 1.
    intros lck HH RR. rewrite (IHck _ eq_refl RR).
    destruct (Env.find i env1) eqn:EE. 2:discriminate.
    now inv HH; apply RR in EE as (? & -> & ->).
  Qed.

  Lemma wc_elab_equation:
    forall aeq eq,
      elab_equation aeq = OK eq ->
      wc_equation G (idck (Env.elements env)) eq.
  Proof.
    intros aeq eq Helab.
    destruct aeq as ((xs & ae) & loc).
    destruct ae. now simpl in Helab; monadInv Helab.
    simpl in Helab.
    repeat progress
           match goal with
           | H: _ /\ _ |- _ => destruct H
           | H:bind _ _ = _ |- _ => monadInv H
           | H:bind2 _ _ = _ |- _ => monadInv H
           | H:find_var _ _ = OK _ |- _ => apply find_var_clock in H
           | H:elab_cexp _ _ = OK _ |- _ =>
             apply wc_elab_cexp in H; eauto using In_env_elements_wc_clock
           | H:_ ==b _ = true |- _ => rewrite equiv_decb_equiv in H
           | H:equiv _ _ |- _ => rewrite H in *; clear H
           | H:elab_exp _ _ = OK _ |- _ =>
             apply wc_elab_exp in H; eauto using In_env_elements_wc_clock
           | H:find_node_interface _ _ = OK _ |- _ =>
             apply find_node_interface_map in H as (n & Fn & Hin & Hout)
           | _ => NamedDestructCases
           end; intros; subst;
      eauto using wc_equation, wc_cexp, wc_exp with nltyping.
    - (* EqApp - no reset *)
      match goal with H:check_result_list _ (inst_clock _ ?sub') _ _ = OK _ |- _ =>
                      pose (sub := (fun x => Env.find x sub')) end.
      pose proof (check_result_list_length _ _ _ _ _ EQ3).
      apply check_result_list_wc in EQ3.
      2:apply find_make_omap; [rewrite Hout|]; auto.
      pose proof (elab_exps_SameVar _ _ _ _ _ (NoDupMembers_n_in _) EQ1).
      apply elab_exps_wc in EQ1.
      eapply CEqApp with (sub:=sub); eauto.
      + match goal with H1:Forall2 _ ?xs ?ys, H2:Forall2 _ ?xs ?ys |- Forall2 _ ?xs ?ys =>
          apply Forall2_Forall2 with (1:=H1) in H2;
            apply Forall2_impl_In with (2:=H2); clear H1 H2 end.
        intros (y, (yt, yc)) e Iy Ie ((lck & WC & IC) & SV).
        split.
        * unfold sub; clear sub. rewrite Hout.
          rewrite find_make_omap_gso; auto.
          apply In_InMembers in Iy.
          pose proof n.(n_nodup) as ND.
          rewrite Permutation_app_comm, Permutation_app_assoc in ND.
          apply NoDupMembers_app_r in ND.
          apply NoDupMembers_app_InMembers_l with (1:=ND) (2:=Iy).
        * exists lck. split; auto.
          apply instck_refines with (1:=IC).
          rewrite Hout. apply make_imap_omap_refines.
      + rewrite <-Hout in *.
        match goal with H:Forall2 _ ?xs ?ys |- Forall2 _ ?xs ?ys =>
          apply Forall2_impl_In with (2:=H); clear H end.
        intros (y, (yt, yc)) z Iy Iz' (Fy & (yck & Iz & IC)); eauto.
      + intros; discriminate.
      + eauto using wc_find_base, In_env_elements_wc_clock.
    - (* EqApp - reset (copied from above and adjusted) *)
      match goal with H:check_result_list _ (inst_clock _ ?sub') _ _ = OK _ |- _ =>
                      pose (sub := (fun x => Env.find x sub')) end.
      pose proof (check_result_list_length _ _ _ _ _ EQ3).
      apply check_result_list_wc in EQ3.
      2:apply find_make_omap; [rewrite Hout|]; auto.
      pose proof (elab_exps_SameVar _ _ _ _ _ (NoDupMembers_n_in _) EQ1).
      apply elab_exps_wc in EQ1.
      eapply CEqApp with (sub:=sub); eauto.
      + match goal with H1:Forall2 _ ?xs ?ys, H2:Forall2 _ ?xs ?ys |- Forall2 _ ?xs ?ys =>
          apply Forall2_Forall2 with (1:=H1) in H2;
            apply Forall2_impl_In with (2:=H2); clear H1 H2 end.
        intros (y, (yt, yc)) e Iy Ie ((lck & WC & IC) & SV).
        split.
        * unfold sub; clear sub. rewrite Hout.
          rewrite find_make_omap_gso; auto.
          apply In_InMembers in Iy.
          pose proof n.(n_nodup) as ND.
          rewrite Permutation_app_comm, Permutation_app_assoc in ND.
          apply NoDupMembers_app_r in ND.
          apply NoDupMembers_app_InMembers_l with (1:=ND) (2:=Iy).
        * exists lck. split; auto.
          apply instck_refines with (1:=IC).
          rewrite Hout. apply make_imap_omap_refines.
      + rewrite <-Hout in *.
        match goal with H:Forall2 _ ?xs ?ys |- Forall2 _ ?xs ?ys =>
          apply Forall2_impl_In with (2:=H); clear H end.
        intros (y, (yt, yc)) z Iy Iz' (Fy & (yck & Iz & IC)); eauto.
      + now inversion_clear 1.
      + eauto using wc_find_base, In_env_elements_wc_clock.
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
      wc_clock (idck (Env.elements env)) ck.
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
  Variable nenv : Env.t (list (ident * (type * clock))
                         * list (ident * (type * clock))).

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
           (acc: Env.t (type * clock)
                 * list (ident * (type_name * LustreAst.preclock * astloc)))
           (vds: list (ident * (type_name * LustreAst.preclock * astloc)))
    : res (Env.t (type * clock)
           * list (ident * (type_name * LustreAst.preclock * astloc))) :=
    match vds with
    | [] => OK acc
    | vd::vds =>
      let (env, notdone) := acc in
      let '(x, (sty, pck, loc)) := vd in
        match pck with
        | FULLCK BASE =>
          if Env.mem x env
          then Error (err_loc loc (CTX x :: msg " is declared more than once"))
          else elab_var_decls_pass
                 (Env.add x (elab_type sty, Cbase) env, notdone) vds

        | FULLCK (ON cy' y b) =>
          match Env.find y env with
          | None => elab_var_decls_pass (env, vd::notdone) vds
          | Some (yt, cy) =>
            if Env.mem x env
            then Error (err_loc loc (CTX x :: msg " is declared more than once"))
            else do ok <- assert_type loc y yt bool_type;
                 do ok <- assert_preclock loc x cy' cy;
                 elab_var_decls_pass
                   (Env.add x (elab_type sty, Con cy y b) env, notdone) vds
          end

        | WHENCK y b =>
          match Env.find y env with
          | None => elab_var_decls_pass (env, vd::notdone) vds
          | Some (yt, cy) =>
            do ok <- assert_type loc y yt bool_type;
            if Env.mem x env
            then Error (err_loc loc (CTX x :: msg " is declared more than once"))
            else elab_var_decls_pass
                   (Env.add x (elab_type sty, Con cy y b) env, notdone) vds
          end
        end
    end.

  Lemma elab_var_decls_pass_wc_env:
    forall vds env ovds env' vds',
      wc_env (idck (Env.elements env)) ->
      elab_var_decls_pass (env, ovds) vds = OK (env', vds') ->
      wc_env (idck (Env.elements env')).
  Proof.
    induction vds as [|vd vds IH].
    now intros ????? Helab; monadInv Helab.
    intros * Hwce Helab.
    destruct vd as (x & ((ty & pck) & loc)).
    destruct pck as [ck|y yb]; [destruct ck as [|ck y yb]|]; simpl in Helab.
    - (* (x, (ty, FULLCK BASE, loc)) *)
      NamedDestructCases.
      apply Env.Props.P.F.not_mem_in_iff in Heq.
      apply IH in Helab; auto.
      rewrite Env.elements_add; auto.
      simpl; apply wc_env_add; auto.
      now rewrite InMembers_idck, <-Env.In_Members.
    - (* (x, (ty, FULLCK (ON ck y yb))) *)
      NamedDestructCases.
      2:now apply IH in Helab; auto.
      monadInv Helab.
      apply Env.Props.P.F.not_mem_in_iff in Heq1.
      apply IH in EQ2; auto.
      rewrite Env.elements_add; auto.
      simpl; apply wc_env_add; auto.
      now rewrite InMembers_idck, <-Env.In_Members.
      constructor.
      2:now apply In_idck_exists; exists t; apply Env.elements_correct.
      apply wc_env_var with (1:=Hwce) (x:=y).
      apply In_idck_exists. exists t.
      apply Env.elements_correct; auto.
    - (* (x, (ty, WHENCK y yb, loc)) *)
      NamedDestructCases.
      2:now apply IH in Helab; auto.
      monadInv Helab. NamedDestructCases.
      apply Env.Props.P.F.not_mem_in_iff in Heq1.
      apply IH in EQ0; auto.
      rewrite Env.elements_add; auto.
      simpl; apply wc_env_add; auto.
      now rewrite InMembers_idck, <-Env.In_Members.
      constructor.
      2:now apply In_idck_exists; exists t; apply Env.elements_correct.
      apply wc_env_var with (1:=Hwce) (x:=y).
      apply In_idck_exists. exists t.
      apply Env.elements_correct; auto.
  Qed.

  Lemma all_wt_clock_empty:
    all_wt_clock (Env.empty (type * clock)).
  Proof.
    intros x ty ck Hfind.
    rewrite Env.gempty in Hfind.
    discriminate Hfind.
  Qed.

  Lemma all_wc_clock_empty:
    all_wc_clock (Env.empty (type * clock)).
  Proof.
    intros x ty ck Hfind.
    rewrite Env.gempty in Hfind.
    discriminate Hfind.
  Qed.

  Lemma all_wt_clock_add:
    forall env x ty ck,
      all_wt_clock env ->
      ~Env.In x env ->
      wt_clock (idty (Env.elements env)) ck ->
      all_wt_clock (Env.add x (ty, ck) env).
  Proof.
    intros env x ty ck Hawc Hnin Hwtc y yt yc Hfind.
    rewrite Env.elements_add; auto; simpl.
    rewrite Env.In_Members, <-InMembers_idty in Hnin.
    destruct (ident_eq_dec y x).
    - subst. rewrite Env.gss in Hfind.
      injection Hfind; intros; subst.
      apply wt_clock_add; auto.
    - rewrite Env.gso in Hfind; auto.
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
      apply Env.Props.P.F.not_mem_in_iff in Heq.
      apply IH in Helab; auto.
      apply all_wt_clock_add; auto with nltyping.
    - (* (x, (ty, FULLCK (ON ck y yb))) *)
      NamedDestructCases.
      2:now apply IH in Helab; auto.
      monadInv Helab.
      apply Env.Props.P.F.not_mem_in_iff in Heq1.
      apply IH in EQ2; auto.
      apply all_wt_clock_add; auto.
      apply assert_type_eq in EQ; subst.
      constructor.
      2:now apply Hawc in Heq.
      apply Env.elements_correct in Heq.
      apply In_idty_exists; eauto.
    - (* (x, (ty, WHENCK y yb, loc)) *)
      NamedDestructCases.
      2:now apply IH in Helab; auto.
      monadInv Helab.
      NamedDestructCases.
      apply Env.Props.P.F.not_mem_in_iff in Heq1.
      apply IH in EQ0; auto.
      apply all_wt_clock_add; auto.
      apply assert_type_eq in EQ; subst.
      constructor.
      2:now apply Hawc in Heq.
      apply Env.elements_correct in Heq.
      apply In_idty_exists; eauto.
  Qed.

  Lemma all_wc_clock_add:
    forall env x ty ck,
      all_wc_clock env ->
      ~Env.In x env ->
      wc_clock (idck (Env.elements env)) ck ->
      all_wc_clock (Env.add x (ty, ck) env).
  Proof.
    intros env x ty ck Hawc Hnin Hwtc y yt yc Hfind.
    rewrite Env.elements_add; auto; simpl.
    rewrite Env.In_Members, <-InMembers_idck in Hnin.
    destruct (ident_eq_dec y x).
    - subst. rewrite Env.gss in Hfind.
      injection Hfind; intros; subst.
      apply wc_clock_add; auto.
    - rewrite Env.gso in Hfind; auto.
      apply Hawc in Hfind.
      apply wc_clock_add; auto.
  Qed.

  Lemma elab_var_decls_pass_all_wc_clock:
    forall vds env ovds env' vds',
      all_wc_clock env ->
      elab_var_decls_pass (env, ovds) vds = OK (env', vds') ->
      all_wc_clock env'.
  Proof.
    induction vds as [|vd vds IH].
    now simpl; intros vd' vds' vd vds Hawc Helab; monadInv Helab.
    intros env ovds env' vds' Hawc Helab.
    destruct vd as (x & ((ty & pck) & loc)).
    destruct pck as [ck|y yb]; [destruct ck as [|ck y yb]|]; simpl in Helab.
    - (* (x, (ty, FULLCK BASE, loc)) *)
      NamedDestructCases.
      apply Env.Props.P.F.not_mem_in_iff in Heq.
      apply IH in Helab; auto.
      apply all_wc_clock_add; auto with nltyping.
    - (* (x, (ty, FULLCK (ON ck y yb))) *)
      NamedDestructCases.
      2:now apply IH in Helab; auto.
      monadInv Helab.
      apply Env.Props.P.F.not_mem_in_iff in Heq1.
      apply IH in EQ2; auto.
      apply all_wc_clock_add; auto.
      apply assert_type_eq in EQ; subst.
      constructor.
      eauto using In_env_elements_wc_clock.
      apply Env.elements_correct in Heq.
      apply In_idck_exists; eauto.
    - (* (x, (ty, WHENCK y yb, loc)) *)
      NamedDestructCases.
      2:now apply IH in Helab; auto.
      monadInv Helab.
      NamedDestructCases.
      apply Env.Props.P.F.not_mem_in_iff in Heq1.
      apply IH in EQ0; auto.
      apply all_wc_clock_add; auto.
      apply assert_type_eq in EQ; subst.
      constructor.
      eauto using In_env_elements_wc_clock.
      apply Env.elements_correct in Heq.
      apply In_idck_exists; eauto.
  Qed.

  Lemma elab_var_decls_pass_spec:
    forall vds env ovds env' vds',
      elab_var_decls_pass (env, ovds) vds = OK (env', vds') ->
      exists vds1 vds2,
        vds' = vds2 ++ ovds
        /\ Permutation vds (vds1 ++ vds2)
        /\ NoDupMembers vds1
        /\ (forall x, InMembers x vds1 -> ~Env.In x env /\ Env.In x env')
        /\ (forall x, Env.In x env -> Env.In x env')
        /\ (forall x, Env.In x env' -> Env.In x env \/ InMembers x vds1)
        /\ (forall x v, Env.find x env = Some v -> Env.find x env' = Some v).
  Proof.
    induction vds as [|vd vds IH].
    now intros * Helab; monadInv Helab; exists [], []; intuition.
    intros * Helab.
    destruct vd as (x & ((ty & pck) & loc)).
    destruct pck as [ck|y yb]; [destruct ck as [|ck y yb]|];
      simpl in Helab.
    - (* (x, (ty, FULLCK BASE, loc)) *)
      NamedDestructCases.
      apply Env.Props.P.F.not_mem_in_iff in Heq.
      apply IH in Helab; clear IH.
      destruct Helab as (vds1 & vds2 & Hvds' & Hperm & Hnd
                         & Hvds1 & Henv & Henv').
      exists ((x, (ty, FULLCK BASE, loc)) :: vds1), vds2.
      repeat split; auto.
      + now rewrite Hperm.
      + constructor; auto.
        intro Hin. apply Hvds1 in Hin.
        destruct Hin as (Hnin & Hin).
        apply Hnin, Env.Props.P.F.add_in_iff; auto.
      + inv H; auto.
        match goal with H:InMembers ?x vds1 |- _ =>
                        apply Hvds1 in H; destruct H as (Hnin & Hin) end.
        rewrite Env.Props.P.F.add_in_iff in Hnin. intuition.
      + inv H.
        2:match goal with H:InMembers ?x vds1 |- _ =>
                          now apply Hvds1 in H; destruct H; auto end.
        apply Henv, Env.Props.P.F.add_in_iff; auto.
      (* + intros x' Hfind. *)
      (*   apply Henv, Env.Props.P.F.add_in_iff; auto. *)
      + intros x' Hfind.
        apply Henv' in Hfind.
        destruct Hfind as [Hfind|]; simpl; auto.
        apply Env.Props.P.F.add_in_iff in Hfind.
        destruct Hfind as [Hfind|Hfind]; auto.
      + intros x' v' Hfind.
        apply Henv'. rewrite Env.gso; auto.
        intro Hx; subst.
        apply Heq. apply Env.In_find; eauto.
    - (* (x, (ty, FULLCK (ON ck y yb))) *)
      NamedDestructCases.
      + (* Env.find y env = Some (yt, cy) *)
        monadInv Helab.
        apply Env.Props.P.F.not_mem_in_iff in Heq1.
        apply IH in EQ2; clear IH.
        destruct EQ2 as (vds1 & vds2 & Hvds' & Hperm & Hnd
                         & Hvds1 & Henv & Henv').
        exists ((x, (ty, FULLCK (ON ck y yb), loc)) :: vds1), vds2.
        repeat split; auto.
        * now rewrite Hperm.
        * constructor; auto.
          intro Hin. apply Hvds1 in Hin.
          destruct Hin as (Hnin & Hin).
          apply Hnin, Env.Props.P.F.add_in_iff; auto.
        * inv H; auto.
          match goal with H:InMembers ?x vds1 |- _ =>
                          apply Hvds1 in H; destruct H as (Hnin & Hin) end.
          rewrite Env.Props.P.F.add_in_iff in Hnin. intuition.
        * inv H.
          2:match goal with H:InMembers ?x vds1 |- _ =>
                            now apply Hvds1 in H; destruct H; auto end.
          apply Henv, Env.Props.P.F.add_in_iff; auto.
        (* * intros x' Hfind. *)
        (*   apply Henv, Env.Props.P.F.add_in_iff; auto. *)
        * intros x' Hfind.
          apply Henv' in Hfind.
          rewrite Env.Props.P.F.add_in_iff in Hfind.
          simpl; intuition.
        * intros x' v' Hfind.
          apply Henv'. rewrite Env.gso; auto.
          intro Hx; subst.
          apply Heq1. apply Env.In_find; eauto.
      + (* Env.find y env = None *)
        apply IH in Helab; clear IH; auto.
        destruct Helab as (vds1 & vds2 & Hvds' & Hperm & Hnd
                           & Hvds1 & Henv & Henv' & Hfind).
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
      + (* Env.find y env = Some (yt, cy) *)
        monadInv Helab.
        NamedDestructCases.
        apply Env.Props.P.F.not_mem_in_iff in Heq1.
        apply IH in EQ0; clear IH.
        destruct EQ0 as (vds1 & vds2 & Hvds' & Hperm & Hnd
                         & Hvds1 & Henv & Henv').
        exists ((x, (ty, WHENCK y yb, loc)) :: vds1), vds2.
        repeat split; auto.
        * now rewrite Hperm.
        * constructor; auto.
          intro Hin. apply Hvds1 in Hin.
          destruct Hin as (Hnin & Hin).
          apply Hnin, Env.Props.P.F.add_in_iff; auto.
        * inv H; auto.
          match goal with H:InMembers ?x vds1 |- _ =>
                          apply Hvds1 in H; destruct H as (Hnin & Hin) end.
          rewrite Env.Props.P.F.add_in_iff in Hnin. intuition.
        * inv H.
          2:match goal with H:InMembers ?x vds1 |- _ =>
                            now apply Hvds1 in H; destruct H; auto end.
          apply Henv, Env.Props.P.F.add_in_iff; auto.
        (* * intros x' Hfind. *)
        (*   apply Henv, Env.Props.P.F.add_in_iff; auto. *)
        * intros x' Hfind.
          apply Henv' in Hfind.
          rewrite Env.Props.P.F.add_in_iff in Hfind.
          simpl; intuition.
        * intros x' v' Hfind.
          apply Henv'. rewrite Env.gso; auto.
          intro Hx; subst.
          apply Heq1. apply Env.In_find; eauto.
      + (* Env.find y env = None *)
        apply IH in Helab; clear IH; auto.
        destruct Helab as (vds1 & vds2 & Hvds' & Hperm & Hnd
                           & Hvds1 & Henv & Henv' & Hfind).
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
           (env: Env.t (type * clock))
           (vds: list (ident * (type_name * LustreAst.preclock * astloc)))
    : res (Env.t (type * clock)) :=
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
             (env: Env.t (type * clock))
             (vds: list (ident * (type_name * LustreAst.preclock * astloc)))
    : res (Env.t (type * clock)) :=
    elab_var_decls' loc vds env vds.

  Lemma elab_var_decls_refine:
    forall loc vds env env',
      elab_var_decls loc env vds = OK env' ->
      env ⊑ env'.
  Proof.
    unfold elab_var_decls.
    intros loc vds. generalize vds at 1.
    intro fuel. revert vds.
    induction fuel as [|cd fuel IH].
    now simpl; intros ??? Helab; NamedDestructCases.
    intros * Helab.
    destruct vds as [|vd vds].
    now simpl in Helab; monadInv Helab.
    simpl in Helab. monadInv Helab.
    rename x into env'', x0 into vds'.
    apply elab_var_decls_pass_spec in EQ; auto.
    apply IH in EQ0; auto.
    rewrite <-EQ0. destruct EQ as (? & ? & ? & ? & ? & ? & ? & ? & RR).
    intros y (yt, yc) Fy; eauto.
  Qed.

  Lemma elab_var_decls_wc_env:
    forall loc vds env env',
      wc_env (idck (Env.elements env)) ->
      elab_var_decls loc env vds = OK env' ->
      wc_env (idck (Env.elements env')).
  Proof.
    unfold elab_var_decls.
    intros loc vds. generalize vds at 1.
    intro fuel. revert vds.
    induction fuel as [|cd fuel IH].
    now simpl; intros ???? Helab; NamedDestructCases.
    intros * Hwc Helab.
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

  Lemma elab_var_decls_all_wc_clock:
    forall loc vds env env',
      all_wc_clock env ->
      elab_var_decls loc env vds = OK env' ->
      all_wc_clock env'.
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
    pose proof (elab_var_decls_pass_all_wc_clock _ _ _ _ _ Hawt EQ) as Hawt''.
    apply elab_var_decls_pass_spec in EQ; auto.
    apply IH in EQ0; auto.
  Qed.

  Lemma elab_var_decls_permutation:
    forall loc vds env env',
      elab_var_decls loc env vds = OK env' ->
      Permutation (map fst vds ++ map fst (Env.elements env))
                  (map fst (Env.elements env')).
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
        auto using Env.NoDupMembers_elements.
      apply Forall_forall.
      intros x Hin.
      apply fst_InMembers in Hin.
      rewrite <-fst_InMembers.
      apply Hvds in Hin.
      now rewrite Env.In_Members in Hin.
    - apply fst_NoDupMembers, Env.NoDupMembers_elements.
    - split; intro HH.
      + apply in_app in HH.
        destruct HH as [HH|HH].
        * apply fst_InMembers in HH.
          apply Hvds in HH.
          rewrite <-fst_InMembers.
          now setoid_rewrite Env.In_Members in HH.
        * apply fst_InMembers, InMembers_In in HH.
          destruct HH as (v & HH).
          apply Env.elements_In, Henv', Env.In_Members in HH.
          now apply fst_InMembers.
      + apply in_app.
        apply fst_InMembers, InMembers_In in HH.
        destruct HH as (v & HH).
        apply Env.elements_In, Henv'' in HH.
        destruct HH as [HH|HH].
        * right. now apply fst_InMembers, Env.In_Members.
        * left. now apply fst_InMembers.
  Qed.

  Fixpoint check_vars (loc: astloc) (defd: PS.t) (xs: list ident) : res PS.t :=
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
    | EqApp xs _ _ _ _::eqs => do defd' <- check_vars loc defd xs;
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
        unfold vars_defined in IH1.
        setoid_rewrite flat_map_concat_map in IH1.
        rewrite IH1, PS.remove_spec.
        intuition.
      + intros x Hvd.
        destruct (is_fby eq); auto.
    - simpl. monadInv Hchk.
      rename x into defd', l into xs, c into ck, i into f, l0 into es.
      apply check_vars_spec in EQ.
      destruct EQ as (Hcv1 & Hcv2 & Hcv3 & Hcv4).
      specialize (IH _ _ _ EQ0); clear EQ0.
      destruct IH as (IH1 & IH2 & IH3).
      simpl. setoid_rewrite in_app.
      repeat split.
      + destruct 1 as [HH|HH].
        now apply Hcv3; auto.
        apply Hcv3. apply IH1 in HH; auto.
      + intro Hxdef. apply Hcv3 in Hxdef.
        destruct Hxdef as [|HH]; auto.
        apply IH1 in HH; auto.
      + apply NoDup_app'; auto.
        apply Forall_forall.
        intros x Hin Hinc.
        specialize (Hcv2 x). specialize (IH1 x).
        unfold vars_defined in IH1.
        setoid_rewrite flat_map_concat_map in IH1.
        intuition.
      + intros x Hin.
        now apply IH3 in Hin.
    - rewrite Bool.andb_true_iff, Bool.negb_true_iff, <-PSE.MP.Dec.F.not_mem_iff in Heq0.
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
        unfold vars_defined in IH1.
        setoid_rewrite flat_map_concat_map in IH1.
        rewrite IH1, PS.remove_spec.
        intuition.
      + intros x Hvd.
        destruct Hvd as [Hvd|]; subst; auto.
  Qed.

  Definition nameset {A: Type} s (xs: list (ident * A)) : PS.t :=
    List.fold_left (fun acc x => PS.add (fst x) acc) xs s.

  Definition annotate {A: Type} (env: Env.t A)
             (vd: ident * (type_name * preclock * astloc)) : res (ident * A) :=
    let '(x, (sty, pck, loc)) := vd in
    match Env.find x env with
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
    intros * Hmm.
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
      Forall (fun yv=>Env.find (fst yv) env = Some (snd yv)) ys.
  Proof.
    induction xs as [|x xs IH].
    - simpl. intros ? Hperm Hys.
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
      Permutation (map fst xs) (map fst (Env.elements env)) ->
      Forall (fun yv => Env.find (fst yv) env = Some (snd yv)) xs ->
      Permutation xs (Env.elements env).
  Proof.
    intros * Hperm Hfa.
    pose proof (Env.NoDupMembers_elements env) as Hnd.
    apply NoDup_Permutation.
    - apply fst_NoDupMembers in Hnd.
      rewrite <-Hperm in Hnd.
      apply fst_NoDupMembers in Hnd.
      now apply NoDupMembers_NoDup.
    - now apply NoDupMembers_NoDup.
    - split; intro HH.
      + apply Forall_forall with (1:=Hfa) in HH.
        apply Env.elements_correct in HH.
        now rewrite <-surjective_pairing in HH.
      + destruct x as (x & v).
        assert (In x (map fst (Env.elements env))) as Hin
            by (apply fst_InMembers; apply In_InMembers with (1:=HH)).
        rewrite <-Hperm in Hin.
        apply fst_InMembers, InMembers_In in Hin.
        destruct Hin as (v' & Hin).
        apply Forall_forall with (2:=Hin) in Hfa.
        apply Env.elements_complete in HH.
        simpl in Hfa. rewrite HH in Hfa.
        injection Hfa; intro; subst.
        assumption.
  Qed.

  Fixpoint check_variable_names' (loc: astloc) (xs: list ident) : res unit :=
    match xs with
    | [] => OK tt
    | x :: xs =>
      if Ident.mem_str Ident.sep (Ident.pos_to_str x)
      then Error (err_loc loc
                          (MSG """" :: CTX x :: msg """ is not a valid variable name"))
      else
        match find (fun x' => ident_eqb x x') Ident.Ids.reserved with
        | None => check_variable_names' loc xs
        | Some n => Error (err_loc loc
                                  (MSG """" :: CTX n :: msg """ is not a valid variable name"))
        end
    end.

  Definition check_variable_names {A} (loc: astloc) (env: Env.t A) : res unit :=
    check_variable_names' loc (map fst (Env.elements env)).

  Lemma check_variable_names_spec:
    forall A loc (env: Env.t A),
      check_variable_names loc env = OK tt ->
      Forall Ident.Ids.ValidId (Env.elements env).
  Proof.
    unfold check_variable_names.
    intros * Hcvns.
    induction (Env.elements env) as [|(x, t)]; auto.
    unfold check_variable_names' in Hcvns.
    Arguments find: simpl never.
    simpl in Hcvns.
    destruct (Ident.mem_str Ident.sep (Ident.pos_to_str x)) eqn: E; try discriminate.
    destruct (find (fun x' : positive => ident_eqb x x') Ident.Ids.reserved) eqn: Hfind; try discriminate.
    constructor.
    - constructor.
      + unfold Ident.Ids.NotReserved.
        apply find_weak_spec in Hfind.
        clear - Hfind.
        induction (Ident.Ids.reserved); auto.
        inversion_clear Hfind as [|? ? E].
        intros [Eq|Hin].
        * simpl in *; subst.
          rewrite ident_eqb_refl in E; discriminate.
        * apply IHl; auto.
      + apply Ident.not_mem_In_str in E.
        auto.
    - now apply IHl.
  Qed.

  Definition check_node_name (loc: astloc) (n: ident) : res unit :=
    if Ident.mem_str Ident.sep (Ident.pos_to_str n)
    then Error (err_loc loc
                     (MSG """" :: CTX n :: msg """ is not a valid node name"))
    else OK tt.

  Lemma check_node_name_spec:
    forall loc n,
      check_node_name loc n = OK tt ->
      Ident.Ids.valid n.
  Proof.
    unfold check_node_name; intros.
    destruct (Ident.mem_str Ident.sep (Ident.pos_to_str n)) eqn: E; try discriminate.
    apply Ident.not_mem_In_str in E.
    auto.
  Qed.

  Fixpoint check_inst_names' (loc: astloc) (xs: list ident) : res unit :=
    match xs with
    | [] => OK tt
    | x :: xs =>
      if Ident.mem_str Ident.sep (Ident.pos_to_str x)
      then Error (err_loc loc
                          (MSG """" :: CTX x :: msg """ is not a valid variable name"))
      else check_inst_names' loc xs
    end.

  Definition check_inst_names (loc: astloc) (insts: list ident) :=
    check_inst_names' loc insts.

  Lemma check_inst_names_spec:
    forall loc insts,
      check_inst_names loc insts = OK tt ->
      Forall Ident.Ids.valid insts.
  Proof.
    unfold check_inst_names.
    intros * Hcins.
    induction insts as [|x]; auto.
    unfold check_inst_names' in Hcins.
    destruct (Ident.mem_str Ident.sep (Ident.pos_to_str x)) eqn: E; try discriminate.
    constructor.
    - apply Ident.not_mem_In_str in E; auto.
    - now apply IHinsts.
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
    let Hwc'_in := fresh "Hwc'_in" in
    let Hwt_out := fresh "Hwt_out" in
    let Hwc'_out := fresh "Hwc'_out" in
    let Hwt_var := fresh "Hwt_var" in
    let Hwc'_var := fresh "Hwc'_var" in
    let Hr_out := fresh "Hr_out" in
    let Hr_var := fresh "Hr_var" in
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
    let Hcvns := fresh "Hcvns" in
    let Hnn := fresh "Hnn" in
    let Hcins := fresh "Hcins" in
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
                    rename H into Hout end;
    match goal with H:elab_var_decls _ _ inputs = OK ?x |- _ =>
                    (assert (Hwc_in := H);
                     apply elab_var_decls_wc_env in Hwc_in;
                     simpl; auto with nlclocking);
                    (assert (Hwt_in := H);
                     apply elab_var_decls_all_wt_clock in Hwt_in;
                     simpl; auto using all_wt_clock_empty with nlclocking);
                    (assert (Hwc'_in := H);
                     apply elab_var_decls_all_wc_clock in Hwc'_in;
                     auto using all_wc_clock_empty);
                    apply elab_var_decls_permutation in H;
                    simpl in H; rewrite app_nil_r in H;
                    rename H into Helab_in, x into env_in end;
    match goal with H:elab_var_decls _ _ outputs = OK ?x |- _ =>
                    (assert (Hwc_out := H);
                     apply elab_var_decls_wc_env in Hwc_out;
                     simpl; auto with nlclocking);
                    (assert (Hr_out := H);
                     apply elab_var_decls_refine in Hr_out);
                    (assert (Hwt_out := H);
                     apply elab_var_decls_all_wt_clock in Hwt_out;
                     simpl; auto with nlclocking);
                    (assert (Hwc'_out := H);
                     apply elab_var_decls_all_wc_clock in Hwc'_out; auto);
                    apply elab_var_decls_permutation in H;
                    rewrite <-Helab_in in H;
                    rename H into Helab_out, x into env_out end;
    match goal with H:elab_var_decls _ _ locals = OK ?x |- _ =>
                    (assert (Hwc_var := H);
                     apply elab_var_decls_wc_env in Hwc_var;
                     simpl; auto with nlclocking);
                    (assert (Hr_var := H);
                     apply elab_var_decls_refine in Hr_var);
                    (assert (Hwt_var := H);
                     apply elab_var_decls_all_wt_clock in Hwt_var;
                     simpl; auto with nlclocking);
                    (assert (Hwc'_var := H);
                     apply elab_var_decls_all_wc_clock in Hwc'_var; auto);
                    apply elab_var_decls_permutation in H;
                    rewrite <-Helab_out in H;
                    rename H into Helab_var, x into env end;
    match goal with H:mmap (elab_equation _ _) _ = OK ?x |- _ =>
                    rename H into Helabs; rename x into eqs end;
    match goal with H:check_defined _ _ _ _ = OK ?x |- _ =>
                    rename H into Hdefd; destruct x end;
    match goal with H:check_variable_names _ _ = OK ?x |- _ =>
                    rename H into Hcvns; destruct x end;
    match goal with H:check_node_name _ _ = OK ?x |- _ =>
                    rename H into Hnn; destruct x end;
    match goal with H:check_inst_names _ _ = OK ?x |- _ =>
                    rename H into Hcins; destruct x end.

  Local Hint Resolve NoDupMembers_nil NoDup_nil.

  Program Definition elab_declaration (decl: LustreAst.declaration)
    : res {n | wt_node G n /\ wc_node G n /\ normal_args_node G n } :=
    match decl with
    | NODE name has_state inputs outputs locals equations loc =>
      match (do env_in  <- elab_var_decls loc (Env.empty (type * clock)) inputs;
             do env_out <- elab_var_decls loc env_in outputs;
             do env     <- elab_var_decls loc env_out locals;
             do xin     <- mmap (annotate env_in) inputs;
             do xout    <- mmap (annotate env_out) outputs;
             do xvar    <- mmap (annotate env) locals;
             do eqs     <- mmap (elab_equation env nenv) equations;
             do ok      <- check_defined loc (nameset PS.empty xout)
                             (nameset (nameset PS.empty xvar) xout) eqs;
             do ok <- check_variable_names loc env;
             do ok <- check_node_name loc name;
             do ok <- check_inst_names loc (vars_defined (filter is_app eqs));
             if (length xin ==b 0) || (length xout ==b 0)
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
    now apply PeanoNat.Nat.neq_0_lt_0 in Hin.
  Qed.
  Next Obligation.
    (* 0 < length xout *)
    match goal with H:(length _ ==b 0) || _ = false |- _ =>
      rewrite Bool.orb_false_iff in H; destruct H as (Hin & Hout) end.
    apply not_equiv_decb_equiv in Hout.
    now apply PeanoNat.Nat.neq_0_lt_0 in Hout.
  Qed.
  Next Obligation.
    (* Permutation (map var_defined eqs) (map fst (xvar ++ xout)) *)
    unfold vars_defined. setoid_rewrite flat_map_concat_map.
    MassageElabs outputs locals inputs.
    apply check_defined_spec in Hdefd.
    destruct Hdefd as (Hdefd & Hnodup & Hnfby).
    repeat setoid_rewrite nameset_spec in Hdefd.
    setoid_rewrite map_app.
    apply Permutation.NoDup_Permutation; auto.
    - pose proof (Env.NoDupMembers_elements env) as Hnd.
      apply fst_NoDupMembers in Hnd.
      rewrite <-Helab_var, app_assoc in Hnd.
      apply NoDup_app_weaken in Hnd.
      setoid_rewrite <-Hvar.
      setoid_rewrite <-Hout.
      exact Hnd.
    - unfold vars_defined in Hdefd.
      setoid_rewrite flat_map_concat_map in Hdefd.
      setoid_rewrite Hdefd.
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
    pose proof (Env.NoDupMembers_elements env) as Hnd.
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
    unfold Ident.Ids.ValidId, Ident.Ids.NotReserved.
    repeat split.
    - change (Forall (fun xty => (fun x => ~In x Ident.Ids.reserved /\ Ident.Ids.valid x) (fst xty))
                     (xin ++ xvar ++ xout)).
      rewrite <-Forall_map, map_app, map_app.
      rewrite Hvar, Hin, Hout in Helab_var.
      rewrite Permutation_app_comm, Permutation_app_assoc, Helab_var, Forall_map.
      eapply check_variable_names_spec; eauto.
    (* - eapply check_inst_names_spec; eauto. *)
    - eapply check_node_name_spec; eauto.
  Qed.
  Next Obligation.
    split; [|split].
    - (* wt_node G n *)
      unfold wt_node. simpl.
      repeat match goal with H:OK _ = _ |- _ =>
        symmetry in H; monadInv1 H end.
      NamedDestructCases. intros; subst.
      MassageElabs outputs locals inputs.
      assert (Forall (fun yv=>Env.find (fst yv) env = Some (snd yv))
                     (xin ++ xvar ++ xout)) as Hf.
      { repeat (apply Forall_app; split; auto).
        rewrite Hr_var in Hr_out.
        - apply Forall_impl_In with (2:=Hf_in).
          intros (z, ?) Iz Fz; apply Hr_out in Fz as (? & ? & ?); subst; auto.
        - apply Forall_impl_In with (2:=Hf_out).
          intros (z, ?) Iz Fz; apply Hr_var in Fz as (? & ? & ?); subst; auto. }
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
    - (* wc_node G n *)
      repeat constructor; simpl;
        repeat match goal with H:OK _ = _ |- _ =>
          symmetry in H; monadInv1 H end;
        NamedDestructCases; intros; subst;
          MassageElabs outputs locals inputs.
      + (* wc_env (idck xin) *)
        rewrite Hin in Helab_in.
        apply permutation_forall_elements in Hf_in; auto.
        now rewrite Hf_in.
      + (* wc_env (idck (xin ++ xout)) *)
        assert (Forall (fun yv=>Env.find (fst yv) env_out = Some (snd yv))
                       (xin ++ xout)) as Hf.
        { repeat (apply Forall_app; split; auto).
          apply Forall_impl_In with (2:=Hf_in).
          intros (z, ?) Iz Fz; apply Hr_out in Fz as (? & ? & ?); subst; auto. }
        apply permutation_forall_elements in Hf.
        now rewrite Hf.
        now rewrite <-Helab_out, map_app, Permutation_app_comm, Hin, Hout.
      + (* wc_env (idck (xin ++ xout ++ xvar)) *)
        assert (Forall (fun yv=>Env.find (fst yv) env = Some (snd yv))
                       (xin ++ xvar ++ xout)) as Hf.
        { rewrite Hr_var in Hr_out.
          repeat (apply Forall_app; split; auto).
          - apply Forall_impl_In with (2:=Hf_in).
            intros (z, ?) Iz Fz; apply Hr_out in Fz as (? & ? & ?); subst; auto.
          - apply Forall_impl_In with (2:=Hf_out).
            intros (z, ?) Iz Fz; apply Hr_var in Fz as (? & ? & ?); subst; auto. }
        apply permutation_forall_elements in Hf as ->; auto.
        now rewrite <-Helab_var, map_app, map_app, Hin, Hout, Hvar,
            Permutation_app_comm, Permutation_app_assoc.
      + (* Forall (wc_equation G (idck (xin ++ xvar ++ xout))) eqs' *)
        assert (Forall (fun yv=>Env.find (fst yv) env = Some (snd yv))
                       (xin ++ xvar ++ xout)) as Hf.
        { repeat (apply Forall_app; split; auto).
          - rewrite Hr_var in Hr_out.
            apply Forall_impl_In with (2:=Hf_in).
            intros (z, ?) Iz Fz; apply Hr_out in Fz as (? & ? & ?); subst; auto.
          - apply Forall_impl_In with (2:=Hf_out).
            intros (z, ?) Iz Fz; apply Hr_var in Fz as (? & ? & ?); subst; auto. }
        apply permutation_forall_elements in Hf.
        2:now rewrite <-Helab_var, map_app, map_app,
          Permutation_app_comm, Permutation_app_assoc, Hin, Hout, Hvar.
        apply Forall_forall.
        intros y Hxin.
        rewrite Hf.
        apply mmap_inversion in Helabs.
        apply Coqlib.list_forall2_in_right with (1:=Helabs) in Hxin.
        destruct Hxin as (aeq & Hxin & Helab).
        apply (wc_elab_equation _ G) in Helab; auto.
    - (* normal_args_node G  n *)
      unfold normal_args_node; simpl.
      repeat match goal with H:OK _ = _ |- _ =>
        symmetry in H; monadInv1 H end;
        NamedDestructCases; intros; subst.
      apply mmap_inversion in EQ5.
      apply Forall_forall; intros eq Hin.
      eapply Coqlib.list_forall2_in_right in EQ5 as (? & ? & EE); eauto.
      eapply elab_normal_args_eq in EE; eauto.
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
        (G: global) (nenv: Env.t (list (ident * (type * clock)) * list (ident * (type * clock))))
        (WTG: wt_global G /\ wc_global G /\ normal_args G)
        (Hnenv: Is_interface_map G nenv)
        (decls: list LustreAst.declaration)
  : res {G' | wt_global G' /\ wc_global G' /\ normal_args G'} :=
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
               (Env.add n.(n_name) (n.(n_in), n.(n_out)) nenv) _ _ ds
    | Error e => Error e
    end
  end.
Next Obligation.
  assert (wt_global (n :: G)) as WTG
      by (now constructor; auto; apply Hnenv).
  repeat split; auto using wc_global.
  apply normal_args_node_cons''; auto.
  now apply Hnenv in Hfind.
Qed.
Next Obligation.
  split.
  - intros * Hf.
    destruct (ident_eq_dec f n.(n_name)) as [He|Hne].
    + subst. rewrite Env.gss in Hf. injection Hf; intros; subst; clear Hf.
      exists n. repeat split; auto.
      unfold find_node, find.
      now rewrite ident_eqb_refl.
    + rewrite Env.gso in Hf; auto.
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
    + subst. rewrite Env.gss in Hf. discriminate.
    + rewrite Env.gso in Hf; auto.
      constructor; auto.
      apply Hnenv; auto.
Qed.

Definition elab_declarations (decls: list LustreAst.declaration)
  : res {G | wt_global G /\ wc_global G /\ normal_args G} :=
  elab_declarations' [] (Env.empty (list (ident * (type * clock))
                                    * list (ident * (type * clock))))
                     (conj wtg_nil (conj wc_global_nil I))
                     Is_interface_map_empty decls.

