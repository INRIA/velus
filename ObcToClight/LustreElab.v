Require Import String.
Require Import Omega.

Require Import ObcToClight.ObcClightCommon.
Import DoNotation.
Require Instantiator.

Require Import Velus.Lustre.Parser.LustreAst.
Require Import Velus.Common.
Require Import Velus.Environment.
Require Import Operators.
Require Import Clocks.

Module Import Syn := Instantiator.L.Syn.
(* Module Import Defs := Instantiator.NL.IsD. *)

Import Interface.Op.
Import Instantiator.OpAux.
Import Instantiator.L.Typ.
Import Instantiator.L.Clo.

Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Require cfrontend.Cop.
Require cparser.Cabs.

Import Permutation.

Require Import common.Errors.
Open Scope error_monad_scope.

(* Elaborate an AST into a well-typed and well-clocked Lustre program. *)

(**
  Lexing and parsing gives a list of LustreAst declarations. Elaboration
  transforms them into Lustre declarations, whilst simultaneously ensuring
  that the resulting program is well-typed and well-clocked. Several other
  well-formedness requirements (node invariants) are also checked.

  The type and clock checking is done during elaboration for two reasons:

  - Source file location information is needed for error messages but is
    not present in the Lustre AST.

  - The Lustre AST requires type and clock annotations.

  Types and clocks are checked simultaneously. Doing both in one pass is not
  only more efficient, it also simplifies the proofs.

  Variable declarations within nodes are elaborated to produce a map from
  each identifier to its declared type and clock. A PositiveMap is used for
  efficiency during checking, but the declarations are maintained in lists
  as their order is significant. The related proofs use permutations and
  rewriting to switch between the two representations. The declaration map
  is then used as an environment for checking and annotating equations and
  expressions.

  The elaboration of variable declarations is performed by [elab_var_decls].
  Multiple passes may be required for a list of declarations because clocks
  may be dependent on other declared variables. For example,
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

Definition err_loc {A} (loc: astloc) (m: errmsg) : res A :=
  Error (MSG (string_of_astloc loc) :: MSG ":" :: m).

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
  | _, _ => err_loc loc (msg "failed cast of constant")
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
      (exists n, find_node f G = Some n
                 /\ Forall2 eq n.(n_in) tcin
                 /\ Forall2 eq n.(n_out) tcout))
  /\ (forall f, Env.find f nenv = None -> Forall (fun n=> f <> n.(n_name)) G).

Lemma Is_interface_map_empty:
  Is_interface_map [] (Env.empty (list (ident * (type * clock))
                                 * list (ident * (type * clock)))).
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

Fixpoint msg_of_sclock (ck: sclock) : errmsg :=
  match ck with
  | Sbase          => msg "."
  | Son ck (Vnm x) true  => msg_of_sclock ck ++ MSG " on " :: CTX x :: nil
  | Son ck (Vnm x) false => msg_of_sclock ck ++ MSG " onot " :: CTX x :: nil
  | Son ck (Vidx i) true  => msg_of_sclock ck ++ MSG " on ?c" :: POS i :: nil
  | Son ck (Vidx i) false => msg_of_sclock ck ++ MSG " onot ?c" :: POS i :: nil
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

(* TODO: Replace with (wt_clocks (Env.elements env)) ? Or something like wc_env? *)
Definition all_wt_clock (env: Env.t (type * clock)) : Prop :=
  forall x ty ck, Env.find x env = Some (ty, ck) ->
                  wt_clock (idty (Env.elements env)) ck.

(* TODO: Replace with wc_env and a lemma? *)
Definition all_wc_clock (env: Env.t (type * clock)) : Prop :=
  forall x ty ck, Env.find x env = Some (ty, ck) ->
                  wc_clock (idck (Env.elements env)) ck.

Section ElabExpressions.

  (* Map variable names to their types and clocks. *)
  Variable env : Env.t (type * clock).

  (* Preceding dataflow program. *)
  Variable G : global.

  (* Map node names to input and output types and clocks. *)
  Variable nenv : Env.t (list (ident * (type * clock))
                        * list (ident * (type * clock))).

  Hypothesis wt_cenv : all_wt_clock env.

  Hypothesis wc_cenv : all_wc_clock env.

  Hypothesis wt_nenv : Is_interface_map G nenv.

  Hypothesis wf_G: wt_global G /\ wc_global G.

  Open Scope nat.

  Definition find_var (loc: astloc) (x: ident) : res (type * clock) :=
    match Env.find x env with
    | None => err_loc loc (CTX x :: msg " is not declared.")
    | Some tc => OK tc
    end.

  Definition assert_id_type (loc: astloc) (x: ident) (xty ty: type) : res unit :=
    if xty ==b ty then OK tt
    else err_loc loc (CTX x :: MSG ": " :: msg_of_types xty ty).

  Definition assert_type (loc: astloc) (xty ty: type) : res unit :=
    if xty ==b ty then OK tt else err_loc loc (msg_of_types xty ty).

  Definition assert_id_clock (loc: astloc) (x: ident) (xck ck: clock) : res unit :=
    if xck ==b ck then OK tt
    else err_loc loc ((CTX x :: MSG " has clock '" :: msg_of_clock xck)
                             ++ MSG "' but clock '" :: msg_of_clock ck
                             ++ msg "' was expected.").

  Definition assert_sclock (loc: astloc) (xck ck: sclock) : res unit :=
    if xck ==b ck then OK tt
    else err_loc loc ((MSG "expression has clock '" :: msg_of_sclock xck)
                             ++ MSG "' but clock '" :: msg_of_sclock ck
                             ++ msg "' was expected.").

  Definition find_node_interface (loc: astloc) (f: ident)
    : res (list (ident * (type * clock)) * list (ident * (type * clock))) :=
    match Env.find f nenv with
    | None => err_loc loc (MSG "node " :: CTX f :: msg " not found.")
    | Some tcs => OK tcs
    end.

  Lemma find_var_wt_clock:
    forall loc x ty ck,
      find_var loc x = OK (ty, ck) -> wt_clock (idty (Env.elements env)) ck.
  Proof.
    intros * Hfind.
    apply wt_cenv with (x:=x) (ty:=ty).
    unfold find_var in Hfind.
    destruct (Env.find x env); try discriminate.
    now monadInv Hfind.
  Qed.

  Lemma find_var_wc_clock:
    forall loc x ty ck,
      find_var loc x = OK (ty, ck) -> wc_clock (idck (Env.elements env)) ck.
  Proof.
    intros * Hfind.
    apply wc_cenv with (x:=x) (ty:=ty).
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
    | None => err_loc loc (msg "wrong operator argument type")
    | Some ty' => OK ty'
    end.

  Definition find_type_binop (loc: astloc) (op: binop)
             (ty1 ty2: type) : res type :=
    match type_binop' op ty1 ty2 with
    | None => err_loc loc (msg "wrong operator argument type")
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

  Definition err_not_singleton {A} (loc: astloc) : res A :=
    err_loc loc (msg "singleton argument expected").

  Definition single_annot (loc: astloc) (e: exp) : res (type * sclock) :=
    match e with
    | Econst c => OK (type_const c, Sbase)
    | Eapp _ _ [(ty, nck)]
    | Evar _ (ty, nck)
    | Eunop _ _ (ty, nck)
    | Ebinop _ _ _ (ty, nck)
    | Ewhen _ _ _ ([ty], nck)
    | Efby _ _ [(ty, nck)]
    | Emerge _ _ _ ([ty], nck)
    | Eite _ _ _ ([ty], nck) => OK (ty, stripname nck)
    | _ => err_not_singleton loc
    end.

  Fixpoint lannot (el : exp * astloc) : list ((type * sclock) * astloc) :=
    let (e, loc) := el in
    match e with
    | Econst c => [((type_const c, Sbase), loc)]
    | Evar _ (ty, nck)
    | Eunop _ _ (ty, nck)
    | Ebinop _ _ _ (ty, nck) => [((ty, stripname nck), loc)]
    | Ewhen _ _ _ (tys, nck)
    | Emerge _ _ _ (tys, nck)
    | Eite _ _ _ (tys, nck) =>
      let ck := stripname nck in
      map (fun ty=> ((ty, ck), loc)) tys
    | Efby _ _ anns
    | Eapp _ _ anns =>
      map (fun tc => ((fst tc, stripname (snd tc)), loc)) anns
    end.

  Definition lannots (els : list (exp * astloc))
    : list ((type * sclock) * astloc) := flat_map lannot els.

  Definition lnannot (el : exp * astloc) : list ((type * nclock) * astloc) :=
    let (e, loc) := el in
    match e with
    | Econst c => [((type_const c, Cstream Sbase), loc)]
    | Evar _ (ty, nck)
    | Eunop _ _ (ty, nck)
    | Ebinop _ _ _ (ty, nck) => [((ty, nck), loc)]
    | Ewhen _ _ _ (tys, nck)
    | Emerge _ _ _ (tys, nck)
    | Eite _ _ _ (tys, nck) =>
      map (fun ty=> ((ty, nck), loc)) tys
    | Efby _ _ anns
    | Eapp _ _ anns => map (fun tc => (tc, loc)) anns
    end.

  Definition lannots_ty {A B} (tcl : list ((type * A) * B)) : list type :=
    map (fun x=>fst (fst x)) tcl.

  Definition lnannots (els : list (exp * astloc))
    : list ((type * nclock) * astloc) := flat_map lnannot els.

  Definition hd_sclock (loc: astloc) (ls: list ((type * sclock) * astloc))
                                                                 : res sclock :=
    match ls with
    | nil => err_loc loc (msg "empty expression list")
    | l::_ => OK (snd (fst l))
    end.

  Fixpoint assert_same_clock (lck: sclock)
           (ans : list ((type * sclock) * astloc)) : res unit :=
    match ans with
    | [] => OK tt
    | an::ans' =>
      let '((ty, ck), loc) := an in
      do ok <- assert_sclock loc ck lck;
      assert_same_clock lck ans'
    end.

  Fixpoint assert_paired_types (gloc: astloc) (ck1 ck2: sclock)
           (ants anfs: list ((type * sclock) * astloc)) : res unit :=
    match ants, anfs with
    | [], [] => OK tt
    | ant::ants', anf::anfs' =>
      let '((tty, tck), tloc) := ant in
      let '((fty, fck), floc) := anf in
      do ok <- assert_sclock tloc tck ck1;
      do ok <- assert_sclock floc fck ck2;
      if tty ==b fty then assert_paired_types gloc ck1 ck2 ants' anfs'
      else err_loc gloc (MSG "expression at "
                             :: MSG (string_of_astloc tloc)
                             :: MSG " has type '" :: MSG (string_of_type tty)
                             :: MSG "' but expression at "
                             :: MSG (string_of_astloc floc)
                             :: MSG " has type '" :: MSG (string_of_type fty)
                             :: msg "'")
    | _, _ => err_loc gloc (msg "arguments are of different lengths")
    end.

  Fixpoint assert_paired_clock_types (gloc: astloc)
           (ants anfs: list ((type * nclock) * astloc)) : res unit :=
    match ants, anfs with
    | [], [] => OK tt
    | ant::ants', anf::anfs' =>
      let '((tty, tnck), tloc) := ant in
      let '((fty, fnck), floc) := anf in
      let tck := stripname tnck in
      let fck := stripname fnck in
      if tck ==b fck
      then if tty ==b fty then assert_paired_clock_types gloc ants' anfs'
           else err_loc gloc (MSG "expression at "
                           :: MSG (string_of_astloc tloc)
                           :: MSG " has type '" :: MSG (string_of_type tty)
                           :: MSG "' but expression at "
                           :: MSG (string_of_astloc floc)
                           :: MSG " has type '" :: MSG (string_of_type fty)
                           :: msg "'")
      else err_loc gloc (MSG "expression at "
                      :: MSG (string_of_astloc tloc)
                      :: MSG " has clock '" :: msg_of_sclock tck
                      ++ MSG "' but expression at "
                      :: MSG (string_of_astloc floc)
                      :: MSG " has type '" :: msg_of_sclock fck
                      ++ msg "'")
    | _, _ => err_loc gloc (msg "arguments are of different lengths")
    end.

  Fixpoint make_imap (s: Env.t ckid)
                     (iface: list (ident * (type * clock)))
                     (args: list ((type * nclock) * astloc))  : Env.t ckid :=
    match iface, args with
    | (x, _)::xs, ((_, Cnamed ni _), _)::es => make_imap (Env.add x ni s) xs es
    | _::xs, _::es => make_imap s xs es
    | _, _ => s
    end.

  Definition make_omap (st: positive * Env.t ckid)
                       (out: ident * (type * clock)) : positive * Env.t ckid :=
    let (i, s) := st in
    (i + 1, Env.add (fst out) (Vidx i) s)%positive.

  Fixpoint make_pmap (s: Env.t ident)
                     (xs: list ident)
                     (es: list ((type * nclock) * astloc)) : Env.t ident :=
    match xs, es with
    | x::xs, ((_, Cnamed (Vidx i) _), _)::es => make_pmap (Env.add i x s) xs es
    | _::xs, _::es => make_pmap s xs es
    | _, _ => s
    end.

  Fixpoint inst_clock (loc: astloc) (base: sclock) (sub: Env.t ckid) (ck: clock)
                                                               : res sclock :=
    match ck with
    | Cbase => OK base
    | Con ck' x b =>
      do sck' <- inst_clock loc base sub ck';
      match Env.find x sub with
      | None => err_loc loc
                  (MSG "The " :: CTX x
                     :: msg " argument must be instantiated with a variable.")
      | Some ni => OK (Son sck' ni b)
      end
    end.

  Fixpoint unify_clock (loc: astloc) (sub: Env.t ident) (sck: sclock)
                                                                 : res clock :=
    match sck with
    | Sbase => OK Cbase
    | Son sck' (Vnm x) b =>
      do ck' <- unify_clock loc sub sck';
      OK (Con ck' x b)
    | Son sck' (Vidx i) b =>
      do ck' <- unify_clock loc sub sck';
      match Env.find i sub with
      | None => err_loc loc (msg "dependent clock escapes scope.")
      | Some x => OK (Con ck' x b)
      end
    end.

  Fixpoint check_inputs (gloc: astloc)
                        (iface: list (type * nclock))
                        (args: list ((type * nclock) * astloc)) : res unit :=
    match iface, args with
    | nil, nil => OK tt
    | nil, _ => err_loc gloc (msg "too many arguments")
    | _, nil => err_loc gloc (msg "not enough arguments")

    | (ty, nck)::iface', ((ty', nck'), loc)::args' =>
      do ok <- assert_type loc ty' ty;
      do ok <- assert_sclock loc (stripname nck') (stripname nck);
      check_inputs gloc iface' args'
    end.

  Definition inst_annot (loc: astloc) (base: sclock) (subst: Env.t ckid)
                        (xtc: ident * (type * clock)) : res ann :=
    let '(x, (ty, ck)) := xtc in
    do sck <- inst_clock loc base subst ck;
    match Env.find x subst with
    | None => OK (ty, Cstream sck)
    | Some ni => OK (ty, Cnamed ni sck)
    end.

  Fixpoint find_base (ock: clock) (lck: sclock) : sclock :=
    match ock, lck with
    | Cbase, _ => lck
    | Con ock' _ _, Sbase => Sbase
    | Con ock' _ _, Son lck' _ _ => find_base ock' lck'
    end.

  (* Auxilliary function for when-inference. *)
  Fixpoint ast_expression_length (e: expression) : res nat :=
    match e with
    | UNARY _ _ _     => OK 1
    | BINARY _ _ _ _  => OK 1
    | CAST _ _ _      => OK 1
    | CONSTANT _ _    => OK 1
    | VARIABLE _ _    => OK 1
    | FBY es0 _ _     => mmapacc plus ast_expression_length 0 es0
    | WHEN es _ _ _   => mmapacc plus ast_expression_length 0 es
    | MERGE _ ets _ _ => mmapacc plus ast_expression_length 0 ets
    | IFTE _ ets _ _  => mmapacc plus ast_expression_length 0 ets
    | APP f _ _ loc =>
      do (tyck_in, tyck_out) <- find_node_interface loc f;
        OK (length tyck_out)
    end.

  Fixpoint approx_imap (s: Env.t ident)
                       (iface: list (ident * (type * clock)))
                       (args: list expression) {struct args} : res (Env.t ident) :=
    match iface, args with
    | (x, _)::xs, VARIABLE vx _::es =>
      approx_imap (Env.add x vx s) xs es
    | _::_, e::es =>
      do n <- ast_expression_length e;
      approx_imap s (skipn n iface) es
    | _, _ => OK s
    end.

  Function approx_base_clock (lcks: list sclock)
                             (oface: list (ident * (type * clock))) : sclock :=
    match lcks, oface with
    | lck::_, (_, (_, ck))::_ => find_base ck lck
    | _, _ => Sbase
    end.

  (* TODO: explain what this does and how it works, and why the form is important
           to the later proofs; give example of ok_clockedcapp.lus. *)
  Fixpoint approx_clock (base: sclock) (sub: Env.t ident) (ck: clock) : sclock :=
    match ck with
    | Cbase => base
    | Con ck' a v =>
      match Env.find a sub with
      | None => Son (approx_clock base sub ck') (Vidx 1) v
                (* use dummy value; stripped away later in well-clocked programs *)
      | Some x => match Env.find x env with
                  | None => Son (approx_clock base sub ck') (Vidx 1) v
                  | Some (xty, xck) => Son (sclk xck) (Vnm x) v
                  end
      end
    end.

  Fixpoint calculate_base_clock (iface: list (ident * (type * clock)))
                                (anns: list (type * nclock * astloc)) : sclock :=
    match iface, anns with
    | (_, (_, ick))::_, (_, nck, _)::_ => find_base ick (stripname nck)
    | _, _ => Sbase
    end.

  (* Add [when]s around [e], assumed to be on the base clock, so that it
     has the given clock [ck]. *)
  Fixpoint build_whens (loc: astloc) (e: exp) (tys: list type)
                                                        (sck: sclock) : exp :=
    match sck with
    | Sbase => e
    | Son sck' (Vnm x) b =>
      Ewhen [build_whens loc e tys sck'] x b (tys, Cstream sck)
    | Son sck' (Vidx _) b =>
      build_whens loc e tys sck'
       (* fall through anonymous variables: this will later give rise to
          a justified clocking error. In any case, we cannot sample on
          unnamed clocks. *)
    end.

  Definition add_whens (loc: astloc) (scks: list sclock) (c: const) : exp :=
    if do_add_when_to_constants tt
    then build_whens loc (Econst c) ([type_const c]) (hd Sbase scks)
    else Econst c.

  Definition discardname (ann : (type * nclock * astloc)) : (type * nclock) :=
    (fst (fst ann), Cstream (stripname (snd (fst ann)))).

  (* Elaborate an expression.

     Two features complicate slightly the elaboration:

     1. The need to allocate fresh anonymous clock variables requires
        that we thread an [fidx] throughout.

     2. The need to automatically add when's to resample constants so
        that they have the clock required by their context.

        We do this by passing a list of clocks, [lcks], that specify
        the clocks expected by the context. The elaboration of
        expressions is part of the elaboration of an equation, so
        initially, the [lcks] list is calculated from the declared
        clocks of the variables at left of the equation. The list is
        preserved by length-preserving constructs (unary, cast, and
        binary operators, fbys, and iftes), and reset by constructs
        that impose their own clock (when and merge). Although we pass
        a list, normally only the first element is needed since many
        constructs only expect singleton stream arguments (unary,
        cast, and binary operators) and others require that all
        arguments be on the same clock (fbys, iftes, when, merge). The
        exceptions are the head of expressions at the right-hand side
        of an equation, and the arguments of node applications.

        Node applications are problematic. We use three tricks:

        (a) An estimation of the base clock of an application [f]
            using the left-most elements of [lcks] and the first
            output clock of the interface of [f] by dropping [Con]'s
            from the latter until we reach [Cbase]. For example, given:

            lck: Cbase on x on ?
            ock:      Cbase on z

            We calculate the base clock as [Cbase on x]. The variable
            that we drop, denoted here as '?', is unimportant. We are
            just looking for the stem; the 'real' type checker will
            verify the rest.

        (b) An estimation of the input mapping from variables used
            in the interface of a node [f], and those passed directly
            in an application of [f]. This can be important because
            of interdependencies between the clocks of [f], which then
            become interdepencies between the clocks of the arguments
            of [f]. We create the mapping by 'peeking' into the AST
            arguments to find variable names; there is no need to look
            more deeply since the name of a stream is lost as soon as
            any operator is applied to the stream.

        (c) The estimated base clock and input mapping allow for a
            partial instantiation of the clocks of the inputs of a node
            interface. These clocks are then partitioned to become the
            [lcks] arguments for the elaborations of the application
            arguments. This partitioning requires knowing how many
            streams are provided by each argument (a single when,
            merge, ifte, or node application may produce several
            outputs). This information is only properly available in
            the resulting types after elaboration, we approximate it
            before elaboration by descending into the ASTs of the
            argument expressions. This approximation may be incorrect
            if there is something wrong with the program.  Such
            problems will be detected after elaboration during type
            checking.

            The approximate mapping between parameter names (in the node
            interface) and argument variables (the expressions passed to
            an instance) does not take 'anonymous' clock variables into
            account, since these are not know until after elaboration of
            the arguments and they cannot anyway be used during when
            inference (since the variable names are introduced into the
            program). This is why a variable map must be recreated from
            elaborated expressions to create the final clock of an
            instantiation.

        The inference of when's is relatively isolated in the elaboration
        routine: an extra call for constants, the passage of [lcks] arguments
        at intermediate constructions, and the above calculations for node
        applications. Importantly, it is almost completely isolated from the
        clock (and type) checking routines and the associated proofs. The
        only exception is for constants themselves; the introduced when's
        should give a well-clocked subterm. *)

  Definition elab_arg
             (elab: list sclock -> positive -> expression
                      -> res (positive * (exp * astloc)))
             (lcks_s: list sclock * positive) (ae: expression) :=
    let (lcks, s) := lcks_s in
    do (fidx', (e, loc)) <- elab lcks s ae;
    OK ((skipn (numstreams e) lcks, fidx'), (e, loc)).

  Fixpoint elab_exp' (lcks: list sclock)
                     (fidx: positive)
                     (ae: expression) {struct ae}
                                         : res (positive * (exp * astloc)) :=
    match ae with
    | CONSTANT ac loc =>
      OK (fidx, (add_whens loc lcks (elab_constant loc ac), loc))

    | VARIABLE x loc =>
      do (ty, ck) <- find_var loc x;
      OK (fidx, (Evar x (ty, Cnamed (Vnm x) (sclk ck)), loc))

    | UNARY aop [ae'] loc =>
      let op := elab_unop aop in
      do (fidx', (e, loc')) <- elab_exp' lcks fidx ae';
      do (ty, sck) <- single_annot loc' e;
      do ty' <- find_type_unop loc op ty;
      OK (fidx', (Eunop op e (ty', Cstream sck), loc))
    | UNARY _ _ loc => err_not_singleton loc

    | CAST aty' [ae'] loc =>
      let ty' := elab_type aty' in
      do (fidx', (e, loc')) <- elab_exp' lcks fidx ae';
      do (_, sck) <- single_annot loc' e;
      OK (fidx', (Eunop (CastOp ty') e (ty', Cstream sck), loc))
    | CAST _ _ loc => err_not_singleton loc

    | BINARY aop [ae1] [ae2] loc =>
      let op := elab_binop aop in
      do (fidx1, (e1, loc1)) <- elab_exp' lcks fidx ae1;
      do (ty1, sck1) <- single_annot loc1 e1;
      do (fidx2, (e2, loc2)) <- elab_exp' lcks fidx1 ae2;
      do (ty2, sck2) <- single_annot loc2 e2;
      do ty' <- find_type_binop loc op ty1 ty2;
      do ok <- assert_sclock loc sck1 sck2;
      OK (fidx2, (Ebinop op e1 e2 (ty', Cstream sck1), loc))
    | BINARY _ _ _ loc => err_not_singleton loc

    | FBY ae0s aes loc =>
      do (fidx0, e0as) <- mmaps (elab_exp' lcks) fidx ae0s;
      let ans0 := lnannots e0as in
      do (fidx', eas) <- mmaps (elab_exp' lcks) fidx0 aes;
      do ok <- assert_paired_clock_types loc ans0 (lnannots eas);

      OK (fidx', (Efby (map fst e0as) (map fst eas)
                       (map discardname ans0), loc))

    | WHEN aes' x b loc =>
      do (xty, xck) <- find_var loc x;
      let sck := sclk xck in
      do ok <- assert_id_type loc x xty bool_type;
      do (fidx', eas') <- mmaps (elab_exp' [sck]) fidx aes';
      let ans' := lannots eas' in
      do ok <- assert_same_clock sck ans';
      OK (fidx, (Ewhen (map fst eas') x b
                   (lannots_ty ans', Cstream (Son sck (Vnm x) b)), loc))

    | MERGE x aets aefs loc =>
      do (xty, xck) <- find_var loc x;
      let sck := sclk xck in
      let tck := Son sck (Vnm x) true in
      let fck := Son sck (Vnm x) false in
      do ok <- assert_id_type loc x xty bool_type;
      do (fidx1, eats) <- mmaps (elab_exp' [tck]) fidx aets;
      let ants := lannots eats in
      do (fidx', eafs) <- mmaps (elab_exp' [fck]) fidx1 aefs;
      do ok <- assert_paired_types loc tck fck ants (lannots eafs);
      OK (fidx', (Emerge x (map fst eats) (map fst eafs)
                           (lannots_ty ants, Cstream sck), loc))

    | IFTE [ae] aets aefs loc =>
      do (fidx0, (e, eloc)) <- elab_exp' lcks fidx ae;
      do (ety, eck) <- single_annot eloc e;
      do ok <- assert_type eloc ety bool_type;
      do (fidx1, eats) <- mmaps (elab_exp' lcks) fidx0 aets;
      let ants := lannots eats in
      do (fidx', eafs) <- mmaps (elab_exp' lcks) fidx1 aefs;
      do ok <- assert_paired_types loc eck eck ants (lannots eafs);
      OK (fidx', (Eite e (map fst eats) (map fst eafs)
                       (lannots_ty ants, Cstream eck), loc))
    | IFTE _ _ _ loc => err_not_singleton loc

    | APP f aes r loc =>
      do (tyck_in, tyck_out) <- find_node_interface loc f;
      (* approximate lcks list to infer whens *)
      do aimap <- approx_imap (Env.empty ident) tyck_in aes;
      let abck := approx_base_clock lcks tyck_out in
      let alcks := map (fun xtc=>approx_clock abck aimap (dck xtc)) tyck_in in
      (* elaborate and check arguments *)
      do (lfidx', eas) <- mmaps (elab_arg elab_exp') (alcks, fidx) aes;
      let fidx1 := snd lfidx' in
      let anns := lnannots eas in
      let bck := calculate_base_clock tyck_in anns in
      let isubst := make_imap (Env.empty ckid) tyck_in anns in
      let (fidx2, osubst) := fold_left make_omap tyck_out (fidx1, isubst) in
      do ianns <- mmap (inst_annot loc bck isubst) tyck_in;
      do oanns <- mmap (inst_annot loc bck osubst) tyck_out;
      do ok <- check_inputs loc ianns anns;
      OK (fidx2, (Eapp f (map fst eas) oanns, loc))
    end.

  Fixpoint check_pat (gloc: astloc)
                     (psubst: Env.t ident)
                     (xs: list ident)
                     (anns: list ((type * nclock) * astloc)) : res unit :=
    match xs, anns with
    | nil, nil => OK tt
    | x::xs', ((ty, nck), loc)::anns' =>
      do ck <- unify_clock loc psubst (stripname nck);
      do (xty, xck) <- find_var loc x;
      do ok <- assert_id_type loc x xty ty;
      do ok <- assert_id_clock loc x xck ck;
      check_pat gloc psubst xs' anns'
    | nil, _ => err_loc gloc (msg "too few variables on lhs of equation.")
    | _, nil => err_loc gloc (msg "too many variables on lhs of equation.")
    end.

  Fixpoint var_clocks (loc: astloc) (xs: list ident) : res (list sclock) :=
    match xs with
    | nil => OK nil
    | x::xs' =>
      do (_, xck) <- find_var loc x;
      do scks' <- var_clocks loc xs';
      OK (sclk xck :: scks')
    end.

  Definition elab_equation (aeq: LustreAst.equation) : res equation :=
    let '(xs, aes, loc) := aeq in
    do lcks <- var_clocks loc xs;
    do (_, els) <- mmaps (elab_arg elab_exp') (lcks, 1%positive) aes;
    let anns := lnannots els in
    do ok <- check_pat loc (make_pmap (Env.empty ident) xs anns) xs anns;
    OK (xs, map fst els).

  (** Properties *)

  Lemma assert_id_type_eq:
    forall loc x xty ty r,
      assert_id_type loc x xty ty = OK r ->
      xty = ty.
  Proof.
    unfold assert_id_type.
    intros * Hm.
    destruct (xty ==b ty) eqn:Heq. 2:now inv Hm.
    rewrite equiv_decb_equiv in Heq. auto.
  Qed.

  Lemma assert_id_clock_eq:
    forall loc x xck ck r,
      assert_id_clock loc x xck ck = OK r ->
      xck = ck.
  Proof.
    unfold assert_id_clock.
    intros. NamedDestructCases.
    rewrite equiv_decb_equiv in Heq.
    now rewrite Heq.
  Qed.

  Lemma single_annot_spec:
    forall loc e ty sck,
      single_annot loc e = (OK (ty, sck)) ->
      typeof e = [ty] /\ clockof e = [sck].
  Proof.
    intros * Hsa. destruct e; inv Hsa;
    try match goal with a: ann |- _ => destruct a end;
    try match goal with H: OK _ = OK _ |- _ => inversion H end;
    try match goal with l: lann |- _ => destruct l end;
    NamedDestructCases;
    simpl; intros; subst; auto.
  Qed.

  Lemma assert_type_spec:
    forall loc xty ty any,
      assert_type loc xty ty = OK any ->
      xty = ty.
  Proof.
    unfold assert_type; intros.
    NamedDestructCases. rewrite equiv_decb_equiv in Heq; auto.
  Qed.

  Lemma assert_id_type_spec:
    forall loc x xty ty any,
      assert_id_type loc x xty ty = OK any ->
      xty = ty.
  Proof.
    unfold assert_id_type; intros.
    NamedDestructCases. rewrite equiv_decb_equiv in Heq; auto.
  Qed.

  Lemma assert_sclock_spec:
    forall loc sck1 sck2 any,
      assert_sclock loc sck1 sck2 = OK any ->
      sck1 = sck2.
  Proof.
    unfold assert_sclock; intros.
    NamedDestructCases. rewrite equiv_decb_equiv in Heq; auto.
  Qed.

  Lemma lannot_typeof:
    forall el,
      map (fun x => fst (fst x)) (lannot el) = typeof (fst el).
  Proof.
    destruct el as (e & loc).
    destruct e;
      repeat progress match goal with
                      | a:ann |- _ => destruct a
                      | l:lann |- _ => destruct l
                      end;
      simpl; try rewrite map_map; simpl;
      try rewrite map_id; auto.
  Qed.

  Lemma lnannot_typeof:
    forall el,
      map (fun x => fst (fst x)) (lnannot el) = typeof (fst el).
  Proof.
    destruct el as (e & loc).
    destruct e;
      repeat progress match goal with
                      | a:ann |- _ => destruct a
                      | l:lann |- _ => destruct l
                      end;
      simpl; try rewrite map_map; simpl;
      try rewrite map_id; auto.
  Qed.

  Lemma lannots_ty_lannots_spec:
    forall els,
      lannots_ty (lannots els) = typesof (map fst els).
  Proof.
    induction els as [|el els IH].
    now unfold typesof; simpl.
    simpl.
    rewrite <-IH.
    unfold lannots, lannots_ty.
    now rewrite map_app, lannot_typeof.
  Qed.

  Lemma assert_paired_types_spec_types:
    forall gloc ants anfs any sck1 sck2,
      assert_paired_types gloc sck1 sck2 ants anfs = OK any ->
      map (fun x => fst (fst x)) ants = map (fun x => fst (fst x)) anfs.
  Proof.
    induction ants; simpl; intros; NamedDestructCases; auto.
    subst. monadInv H. NamedDestructCases.
    simpl.
    match goal with H:assert_paired_types _ _ _ _ _ = OK _ |- _ =>
                    apply IHants in H; rewrite H end.
    rewrite equiv_decb_equiv in Heq.
    now rewrite <-Heq.
  Qed.

  Lemma assert_paired_types_spec_clocks:
    forall gloc ants anfs any sck1 sck2,
      assert_paired_types gloc sck1 sck2 ants anfs = OK any ->
      Forall (fun x => sck1 = snd (fst x)) ants
      /\ Forall (fun x => sck2 = snd (fst x)) anfs.
  Proof.
    induction ants; simpl; intros; NamedDestructCases; auto.
    subst. monadInv H. NamedDestructCases.
    simpl.
    repeat progress match goal with
    | H:assert_paired_types _ _ _ _ _ = OK _ |- _ =>
      apply IHants in H; destruct H as (H1 & H2)
    | H:assert_sclock _ _ _ = OK _ |- _ =>
      apply assert_sclock_spec in H; subst
    end.
    split; constructor; auto; simpl.
  Qed.

  Lemma assert_paired_clock_types_spec_types:
    forall gloc ants anfs any,
      assert_paired_clock_types gloc ants anfs = OK any ->
      map (fun x => fst (fst x)) ants = map (fun x => fst (fst x)) anfs.
  Proof.
    induction ants; simpl; intros; NamedDestructCases; auto.
    subst. simpl.
    match goal with H:assert_paired_clock_types _ _ _ = OK _ |- _ =>
                    apply IHants in H; rewrite H end.
    rewrite equiv_decb_equiv in Heq5.
    now rewrite <-Heq5.
  Qed.

  Lemma assert_paired_clock_types_spec_clocks:
    forall gloc ants anfs any,
      assert_paired_clock_types gloc ants anfs = OK any ->
      map (fun x => ckstream (fst x)) ants = map (fun x => ckstream (fst x)) anfs.
  Proof.
    induction ants; simpl; intros;
      NamedDestructCases; auto; subst.
    apply IHants in H. rewrite H.
    simpl.
    rewrite equiv_decb_equiv in Heq4.
    unfold ckstream. simpl.
    now rewrite <-Heq4.
  Qed.

  Lemma wt_find_base:
    forall env sck ck,
      wt_sclock env sck ->
      wt_sclock env (find_base ck sck).
  Proof.
    induction sck; intros ck Hwt; destruct ck as [|ck' x' b']; auto with ltyping.
    inversion Hwt; now apply IHsck.
  Qed.

  Lemma wc_find_base:
    forall env sck ck,
      wc_sclock env sck ->
      wc_sclock env (find_base ck sck).
  Proof.
    induction sck; intros ck Hwc; destruct ck as [|ck' x' b']; auto with ltyping.
    inversion Hwc; now apply IHsck.
  Qed.

  Lemma wt_approx_base_clock:
    forall env lcks ck,
      Forall (wt_sclock env) lcks ->
      wt_sclock env (approx_base_clock lcks ck).
  Proof.
    destruct lcks, ck as [|xtc]; intros Hfa; auto with ltyping.
    inversion_clear Hfa.
    destruct xtc as (x & t & c).
    now apply wt_find_base.
  Qed.

  Lemma wc_approx_base_clock:
    forall env lcks ck,
      Forall (wc_sclock env) lcks ->
      wc_sclock env (approx_base_clock lcks ck).
  Proof.
    destruct lcks, ck as [|xtc]; intros Hfa; auto with lclocking.
    inversion_clear Hfa.
    destruct xtc as (x & t & c).
    now apply wc_find_base.
  Qed.

  Lemma length_lnannot_lannot:
    forall el,
      length (lnannot el) = length (lannot el).
  Proof.
    destruct el as (e & loc).
    destruct e;
      repeat match goal with a:ann |- _ => destruct a
                           | l:lann |- _ => destruct l end;
      simpl; try setoid_rewrite Coqlib.list_length_map; auto.
  Qed.

  Lemma ast_expression_length_lannots':
    forall eas es lcks n fidx fidx',
      Forall
         (fun ae =>
            forall e lcks fidx fidx' n loc,
              elab_exp' lcks fidx ae = OK (fidx', (e, loc)) ->
              ast_expression_length ae = OK n -> length (lnannot (e, loc)) = n) eas ->
      mmapacc plus ast_expression_length 0 eas = OK n ->
      mmaps (elab_exp' lcks) fidx eas = OK (fidx', es) ->
      length (lannots es) = n.
  Proof.
    induction eas; intros es lcks n fidx fidx' HH Hlen Hmm;
      monadInv Hlen; monadInv Hmm; auto.
    destruct x1 as (e & loc).
    inversion_clear HH as [|? ? HH1 HH2].
    apply HH1 with (1:=EQ1) in EQ.
    rewrite length_lnannot_lannot in EQ.
    unfold lannots.
    rewrite length_flat_map, EQ.
    rewrite <-(plus_O_n x) in EQ0.
    apply mmapacc_plus_shift in EQ0.
    destruct EQ0 as (Hf & Hle).
    eapply IHeas with (1:=HH2) (3:=EQ3) in Hf.
    unfold lannots in Hf. rewrite Hf. omega.
  Qed.

  Lemma lnannots_cons:
    forall el els,
      lnannots (el::els) = lnannot el ++ lnannots els.
  Proof. now simpl. Qed.

  Lemma lannots_cons:
    forall el els,
      lannots (el::els) = lannot el ++ lannots els.
  Proof. now simpl. Qed.

  Lemma length_lnannots_lannots:
    forall es,
      length (lnannots es) = length (lannots es).
  Proof.
    induction es as [|el els IH]; auto.
    simpl; rewrite app_length, app_length, IH.
    apply Nat.add_cancel_r.
    destruct el as (e, l);
      destruct e; try destruct a;
      try destruct l1; try destruct l2; simpl;
      try setoid_rewrite map_length; auto.
  Qed.

  (* TODO: write a tactic to do all the list destructions and bind inversions? *)
  Lemma ast_expression_length_lnannot:
    forall ae e lcks fidx fidx' n loc,
      elab_exp' lcks fidx ae = OK (fidx', (e, loc)) ->
      ast_expression_length ae = OK n ->
      length (lnannot (e, loc)) = n.
  Proof.
    clear wt_cenv wt_nenv.
    induction ae using expression_ind2;
      intros e lcks fidx fidx' n loc Helab Hlen.
    - (* UNARY *)
      monadInv Hlen. destruct es.
      now inversion Helab.
      destruct es. 2:now inversion Helab. simpl in Helab.
      now monadInv2 Helab.
    - (* BINARY *)
      monadInv Hlen. destruct es1.
      now inversion Helab.
      destruct es1. 2:now inversion Helab.
      destruct es2. now inversion Helab.
      destruct es2. 2:now inversion Helab.
      simpl in Helab. now monadInv2 Helab.
    - (* IFTE *)
      destruct es. now inversion Helab.
      destruct es. 2:now inversion Helab.
      simpl in Helab. monadInv2 Helab.
      simpl.
      unfold lannots_ty.
      repeat rewrite Coqlib.list_length_map.
      eauto using ast_expression_length_lannots'.
    - (* CAST *)
      monadInv Hlen. destruct es.
      now inversion Helab.
      destruct es. 2:now inversion Helab. simpl in Helab.
      now monadInv2 Helab.
    - (* APP *)
      monadInv Hlen. monadInv Helab.
      setoid_rewrite surjective_pairing in EQ4.
      simpl in EQ4. monadInv2 EQ4.
      rewrite EQ0 in EQ. monadInv EQ.
      simpl. rewrite Coqlib.list_length_map.
      monadInv EQ4. symmetry.
      eauto using Coqlib.list_forall2_length.
    - (* CONSTANT *)
      monadInv Hlen.
      inversion_clear Helab.
      unfold add_whens.
      case (do_add_when_to_constants tt); auto.
      destruct lcks; auto.
      induction s; auto.
      destruct c0; auto.
    - (* VARIABLE *)
      now monadInv Helab; monadInv Hlen.
    - (* FBY *)
      simpl in Hlen.
      simpl in Helab. monadInv2 Helab.
      simpl. repeat rewrite Coqlib.list_length_map.
      rewrite length_lnannots_lannots.
      eauto using ast_expression_length_lannots'.
    - (* WHEN *)
      simpl in Hlen.
      simpl in Helab. monadInv2 Helab.
      unfold lannots_ty. simpl.
      repeat rewrite Coqlib.list_length_map.
      eauto using ast_expression_length_lannots'.
    - (* MERGE *)
      simpl in Hlen.
      simpl in Helab. monadInv2 Helab.
      unfold lannots_ty. simpl.
      repeat rewrite Coqlib.list_length_map.
      eauto using ast_expression_length_lannots'.
  Qed.

  Lemma ast_expression_length_lannots:
    forall eas es lcks n fidx fidx',
      mmapacc plus ast_expression_length 0 eas = OK n ->
      mmaps (elab_exp' lcks) fidx eas = OK (fidx', es) ->
      length (lannots es) = n.
  Proof.
    intros * Hma Hmf.
    apply ast_expression_length_lannots' with (2:=Hma) (3:=Hmf).
    apply Forall_forall.
    intros ???????? Helab Hast.
    apply ast_expression_length_lnannot with (1:=Helab) (2:=Hast).
  Qed.

  Lemma find_make_imap_add:
    forall xs ys s x y vy,
      x <> y ->
      Env.find x (make_imap (Env.add y vy s) xs ys) = Env.find x (make_imap s xs ys).
  Proof.
    induction xs as [|(w, (wt, wc)) xs IH].
    - simpl. intros ????? Hnxy.
      now rewrite Env.gso with (1:=Hnxy).
    - intros * Hnxy.
      destruct ys as [|((zt, zc), zloc) ys].
      now simpl; rewrite Env.gso with (1:=Hnxy).
      destruct zc; simpl.
      + apply IH with (1:=Hnxy).
      + destruct (ident_eq_dec w y).
        * subst. now repeat rewrite IH; auto.
        * rewrite Env.add_comm; auto.
  Qed.

  Lemma find_make_imap_not_in_members:
    forall xs ys s x,
      ~InMembers x xs ->
      Env.find x (make_imap s xs ys) = Env.find x s.
  Proof.
    induction xs as [|(x, v) xs IH].
    now simpl; intuition.
    intros * Hnim.
    apply NotInMembers_cons in Hnim.
    destruct Hnim as [Hnim Hnx].
    destruct ys. reflexivity.
    destruct p as ((ty, nc), loc). destruct nc.
    now apply IH with (1:=Hnim).
    simpl.
    rewrite find_make_imap_add; auto.
  Qed.

  Lemma find_make_omap_not_in_members:
    forall xs s x,
      ~InMembers x xs ->
      Env.find x (snd (fold_left make_omap xs s)) = Env.find x (snd s).
  Proof.
    induction xs as [|(x, v) xs IH].
    now simpl; auto.
    intros * Hnim.
    apply NotInMembers_cons in Hnim.
    destruct Hnim as [Hnim Hnx].
    simpl.
    rewrite IH; auto.
    destruct s as (fidx, s).
    simpl. now rewrite Env.gso; auto.
  Qed.

  Lemma find_make_imap_skipn:
    forall n xs ys s x v,
      ~InMembers x (firstn n xs) ->
      Env.find x (make_imap s (skipn n xs) (skipn n ys)) = Some v ->
      Env.find x (make_imap s xs ys) = Some v.
  Proof.
    induction n; auto.
    destruct xs, ys; auto.
    - destruct p. simpl.
      intros.
      apply Decidable.not_or in H.
      destruct H.
      destruct (skipn n xs); auto.
      destruct p0; auto.
    - destruct p; destruct p0; destruct p0. simpl.
      destruct n0.
      + intros.
        apply Decidable.not_or in H.
        destruct H.
        apply IHn; auto.
      + intros.
        apply Decidable.not_or in H.
        destruct H.
        rewrite find_make_imap_add; auto.
  Qed.

  Lemma map_imap_InMembers:
    forall ys xs a si,
      Env.In a (make_imap si xs ys) ->
      InMembers a xs \/ Env.In a si.
  Proof.
    induction ys; destruct xs; simpl; try destruct p; auto.
    destruct a as ((ty, ck), loc).
    destruct ck; intros * Hin.
    - apply IHys in Hin. intuition.
    - apply IHys in Hin.
      destruct Hin as [Hin|Hin]; auto.
      apply Env.Props.P.F.add_in_iff in Hin.
      destruct Hin; auto.
  Qed.

  Lemma find_approx_imap_not_in_members:
    forall a aes iface sa aimap,
      ~InMembers a iface ->
      approx_imap sa iface aes = OK aimap ->
      Env.find a aimap = Env.find a sa.
  Proof.
    induction aes as [|ae aes IH]; intros iface sa aimap Hnm Hai;
      destruct iface as [|(b, (bty, bck)) iface'];
      try (now inversion_clear Hai).
    assert (Hnm':=Hnm).
    apply NotInMembers_cons in Hnm'; destruct Hnm' as (Hnm' & Hnab).
    destruct ae;
      simpl in Hai;
      (try monadInv Hai);
      (try now apply IH with (1:=Hnm'));
      (try match goal with H:approx_imap _ _ _ = OK _ |- _ =>
            apply IH with (2:=H); eauto using inmembers_skipn end).
      apply IH with (1:=Hnm') in Hai. rewrite Env.gso in Hai; auto.
  Qed.

  Lemma lnannot_add_whens:
    forall loc alcks c,
    exists sclk,
      lnannot (add_whens loc alcks c, loc) = [(type_const c, Cstream sclk, loc)].
  Proof.
    unfold add_whens.
    destruct (do_add_when_to_constants tt); simpl; eauto.
    intros loc alcks c.
    assert (forall ty sclk, build_whens loc (Econst c) [ty] sclk = Econst c
            \/ (exists e x b sclk',
                   build_whens loc (Econst c) [ty] sclk
                       = Ewhen e x b ([ty], Cstream sclk'))) as Hbw.
    - intros ty sclk.
      induction sclk as [|sclk' IH]; auto.
      destruct IH as [IH|IH]; destruct c0; simpl; auto;
        now right; eauto.
    - destruct (Hbw (type_const c) (hd Sbase alcks)) as [HH|HH].
      now setoid_rewrite HH; eauto.
      destruct HH as (e & x & b & sclk' & HH).
      setoid_rewrite HH. simpl; eauto.
  Qed.

  Lemma approx_imap_to_make_imap:
    forall aes iface eas aimap alcks fidx fidx',
      NoDupMembers iface ->
      approx_imap (Env.empty ident) iface aes = OK aimap ->
      mmaps (elab_arg elab_exp') (alcks, fidx) aes = OK (fidx', eas) ->
      (forall a x,
          Env.find a aimap = Some x ->
          Env.find a (make_imap (Env.empty ckid) iface (lnannots eas)) = Some (Vnm x)).
  Proof.
    intros aes.
    assert (forall a x, Env.find a (Env.empty ident) = Some x
                        -> Env.find a (Env.empty ckid) = Some (Vnm x)) as Hfind
        by (setoid_rewrite Env.gempty; discriminate).
    intro iface.
    assert (forall x, InMembers x iface -> ~Env.In x (Env.empty ckid)) as Hnin
      by (intros x Him Hin; rewrite Env.In_find, Env.gempty in Hin;
          destruct Hin; discriminate).
    revert Hfind iface Hnin.
    generalize (Env.empty ident) as sa.
    generalize (Env.empty ckid) as si.
    induction aes as [|ae aes IH];
      intros si sa Hafind iface Hnsa eas aimap alcks fidx (alcks', fidx')
             Hnd Hai Hmm a x Hfind.
    now monadInv Hmm; destruct iface as [|[iface' iface'']]; monadInv Hai; auto.
    destruct iface as [|[b (bty, bck)]].
    now monadInv Hai; auto.
    apply nodupmembers_cons in Hnd; destruct Hnd as [Hnin Hnd].
    destruct ae; simpl in Hai, Hmm; try monadInv Hai.
    - (* UNARY *)
      destruct l. monadInv2 Hmm. monadInv EQ.
      destruct l. 2:monadInv Hmm; monadInv EQ.
      monadInv Hmm. monadInv2 EQ. monadInv2 EQ0.
      apply IH with (1:=Hafind) (3:=Hnd) (4:=Hai) (5:=EQ1) (6:=Hfind).
      auto using inmembers_cons.
    - (* BINARY *)
      destruct l. monadInv2 Hmm; monadInv EQ.
      destruct l. 2:monadInv Hmm; monadInv EQ.
      destruct l0. monadInv Hmm; monadInv EQ.
      destruct l0. 2:monadInv Hmm; monadInv EQ.
      monadInv Hmm. monadInv2 EQ. monadInv2 EQ0.
      apply IH with (1:=Hafind) (3:=Hnd) (4:=Hai) (5:=EQ1) (6:=Hfind).
      auto using inmembers_cons.
    - (* IFTE *)
      destruct l. monadInv2 Hmm. monadInv EQ1.
      destruct l. 2:monadInv Hmm; monadInv EQ1.
      monadInv Hmm. monadInv2 EQ1. monadInv2 EQ2.
      (* clear x7 EQ2 EQ0 x6 EQ x14 EQ5 wt_nenv wt_cenv fidx EQ4.
         rename e into ae, l0 into aets, l1 into aefs, x5 into iloc, x1 into e,
         x0 into fidx0, x10 into fidx1, x2 into fidx2, x11 into ets, x3 into es,
         x8 into isck, x13 into efs, x into cid. destruct x9. *)
      rewrite lnannots_cons.
      match goal with
        Hl: mmapacc plus ast_expression_length 0 _ = OK ?len |- _ =>
        eapply find_make_imap_skipn with (n:=len) end.
      + match goal with Hai: approx_imap _ _ _ = OK _ |- _ =>
          eapply IH in Hai; eauto using inmembers_skipn, NoDupMembers_skipn end.
        match goal with H:Env.find ?x ?s = Some _ |- _ =>
          assert (Env.In x s) as Hin by (apply Env.In_find; eauto) end.
        apply map_imap_InMembers in Hin.
        destruct Hin as [Hin|Hin]; auto using InMembers_skipn_firstn.
        intro Him. apply inmembers_firstn in Him.
        apply Hnsa in Him. auto.
      + match goal with Hl: mmapacc plus ast_expression_length 0 _ = OK _,
                        Hf: mmaps (elab_exp' _) _ _ = OK _ |- _ =>
          pose proof (ast_expression_length_lannots _ _ _ _ _ _ Hl Hf); subst end.
        rewrite skipn_app.
        2:now unfold lannots_ty; simpl; repeat rewrite Coqlib.list_length_map.
        match goal with Hai: approx_imap _ _ _ = OK _,
                        Hee: mmaps (elab_arg elab_exp') _ _ = OK _ |- _ =>
          eapply IH with (1:=Hafind) (4:=Hai) (5:=Hee) (6:=Hfind);
          eauto using inmembers_skipn, NoDupMembers_skipn
        end.
    - (* CAST *)
      destruct l. monadInv2 Hmm. monadInv EQ.
      destruct l. 2:monadInv Hmm; monadInv EQ.
      monadInv Hmm. monadInv2 EQ. monadInv2 EQ0.
      apply IH with (1:=Hafind) (3:=Hnd) (4:=Hai) (5:=EQ1) (6:=Hfind).
      auto using inmembers_cons.
    - (* APP *)
      monadInv Hmm. monadInv2 EQ. monadInv2 EQ1. monadInv2 EQ.
      setoid_rewrite surjective_pairing in EQ6. simpl in EQ6.
      monadInv2 EQ6.
      rewrite lnannots_cons.
      match goal with Hl: approx_imap _ (skipn (length ?xtc) _) _ = OK _ |- _ =>
        eapply find_make_imap_skipn with (n:=length xtc) end.
      + match goal with Hai: approx_imap _ _ _ = OK _ |- _ =>
          eapply IH in Hai; eauto using inmembers_skipn, NoDupMembers_skipn end.
        match goal with H:Env.find ?x ?s = Some _ |- _ =>
          assert (Env.In x s) as Hin by (apply Env.In_find; eauto) end.
        apply map_imap_InMembers in Hin.
        destruct Hin as [Hin|Hin]; auto using InMembers_skipn_firstn.
        intro Him. apply inmembers_firstn in Him.
        apply Hnsa in Him. auto.
      + rewrite skipn_app.
        match goal with Hai: approx_imap _ _ _ = OK _,
                        Hee: mmaps (elab_arg elab_exp') _ _ = OK _ |- _ =>
          eapply IH with (1:=Hafind) (4:=Hai) (5:=Hee) (6:=Hfind);
          eauto using inmembers_skipn, NoDupMembers_skipn
        end.
        simpl. rewrite Coqlib.list_length_map.
        match goal with Hf1: find_node_interface _ _ = OK _,
                        Hf2: find_node_interface _ _ = OK _ |- _ =>
          rewrite Hf1 in Hf2; monadInv Hf2 end.
        match goal with H:mmap _ ?xtc = OK ?ann |- length ?xtc = length ?ann =>
          monadInv H end.
        eauto using Coqlib.list_forall2_length.
    - (* CONSTANT *)
      monadInv Hmm.
      match goal with H:context [add_whens ?loc _ ?const] |- _ =>
        destruct (lnannot_add_whens loc alcks const) as [wclk Haw] end.
      rewrite lnannots_cons, Haw.
      apply IH with (1:=Hafind) (3:=Hnd) (4:=Hai) (5:=EQ) in Hfind;
        auto using inmembers_cons.
    - (* VARIABLE *)
      monadInv Hmm. monadInv2 EQ. monadInv EQ0.
      simpl.
      destruct (ident_eq_dec a b) as [He|Hne].
      + subst.
        rewrite find_make_imap_not_in_members with (1:=Hnin), Env.gss.
        apply find_approx_imap_not_in_members with (1:=Hnin) in Hai.
        rewrite Env.gss in Hai. rewrite Hai in Hfind.
        now inversion Hfind.
      + eapply IH with (3:=Hnd) (4:=Hai) (5:=EQ1) (6:=Hfind).
        * intros z v. destruct (ident_eq_dec z b) as [|Hn].
          now subst; setoid_rewrite Env.gss; inversion 1.
          now setoid_rewrite Env.gso with (1:=Hn); auto.
        * intros y Him.
          rewrite Env.Props.P.F.add_in_iff. destruct 1 as [|Hin].
          now subst; apply Hnin.
          apply Hnsa with (2:=Hin).
          auto using inmembers_cons.
    - (* FBY *)
      monadInv2 Hmm. monadInv2 EQ1. monadInv EQ2.
      rewrite lnannots_cons.
      match goal with Hl: mmapacc plus ast_expression_length 0 _ = OK ?len |- _
        => eapply find_make_imap_skipn with (n:=len) end.
      + match goal with Hai: approx_imap _ _ _ = OK _ |- _ =>
          eapply IH in Hai; eauto using inmembers_skipn, NoDupMembers_skipn end.
        match goal with H:Env.find ?x ?s = Some _ |- _ =>
          assert (Env.In x s) as Hin by (apply Env.In_find; eauto) end.
        apply map_imap_InMembers in Hin.
        destruct Hin as [Hin|Hin]; auto using InMembers_skipn_firstn.
        intro Him. apply inmembers_firstn in Him.
        apply Hnsa in Him. auto.
      + match goal with Hl: mmapacc plus ast_expression_length 0 _ = OK _,
                        Hf: mmaps (elab_exp' _) _ _ = OK _ |- _ =>
          pose proof (ast_expression_length_lannots _ _ _ _ _ _ Hl Hf); subst
        end.
        rewrite skipn_app.
        2:now simpl; repeat rewrite Coqlib.list_length_map;
          rewrite length_lnannots_lannots.
        match goal with Hai: approx_imap _ _ _ = OK _,
                        Hee: mmaps (elab_arg elab_exp') _ _ = OK _ |- _ =>
          eapply IH with (1:=Hafind) (4:=Hai) (5:=Hee) (6:=Hfind);
          eauto using inmembers_skipn, NoDupMembers_skipn
        end.
    - (* WHEN *)
      monadInv2 Hmm. monadInv2 EQ1. monadInv EQ2.
      rewrite lnannots_cons.
      match goal with Hl: mmapacc plus ast_expression_length 0 _ = OK ?len |- _
        => eapply find_make_imap_skipn with (n:=len) end.
      + match goal with Hai: approx_imap _ _ _ = OK _ |- _ =>
          eapply IH in Hai; eauto using inmembers_skipn, NoDupMembers_skipn end.
        match goal with H:Env.find ?x ?s = Some _ |- _ =>
          assert (Env.In x s) as Hin by (apply Env.In_find; eauto) end.
        apply map_imap_InMembers in Hin.
        destruct Hin as [Hin|Hin]; auto using InMembers_skipn_firstn.
        intro Him. apply inmembers_firstn in Him.
        apply Hnsa in Him. auto.
      + match goal with Hl: mmapacc plus ast_expression_length 0 _ = OK _,
                        Hf: mmaps (elab_exp' _) _ _ = OK _ |- _ =>
          pose proof (ast_expression_length_lannots _ _ _ _ _ _ Hl Hf); subst end.
        rewrite skipn_app.
        2:now unfold lannots_ty; simpl; repeat rewrite Coqlib.list_length_map.
        match goal with Hai: approx_imap _ _ _ = OK _,
                        Hee: mmaps (elab_arg elab_exp') _ _ = OK _ |- _ =>
          eapply IH with (1:=Hafind) (4:=Hai) (5:=Hee) (6:=Hfind);
            eauto using inmembers_skipn, NoDupMembers_skipn end.
    - (* MERGE *)
      monadInv2 Hmm. monadInv2 EQ1. monadInv EQ2.
      rewrite lnannots_cons.
      match goal with Hl: mmapacc plus ast_expression_length 0 _ = OK ?len |- _
        => eapply find_make_imap_skipn with (n:=len) end.
      + match goal with Hai: approx_imap _ _ _ = OK _ |- _ =>
          eapply IH in Hai; eauto using inmembers_skipn, NoDupMembers_skipn end.
        match goal with H:Env.find ?x ?s = Some _ |- _ =>
          assert (Env.In x s) as Hin by (apply Env.In_find; eauto) end.
        apply map_imap_InMembers in Hin.
        destruct Hin as [Hin|Hin]; auto using InMembers_skipn_firstn.
        intro Him. apply inmembers_firstn in Him.
        apply Hnsa in Him. auto.
      + match goal with Hl: mmapacc plus ast_expression_length 0 _ = OK _,
                        Hf: mmaps (elab_exp' _) _ _ = OK _ |- _ =>
          pose proof (ast_expression_length_lannots _ _ _ _ _ _ Hl Hf); subst end.
        rewrite skipn_app.
        2:now unfold lannots_ty; simpl; repeat rewrite Coqlib.list_length_map.
        match goal with Hai: approx_imap _ _ _ = OK _,
                        Hee: mmaps (elab_arg elab_exp') _ _ = OK _ |- _ =>
          eapply IH with (1:=Hafind) (4:=Hai) (5:=Hee) (6:=Hfind);
            eauto using inmembers_skipn, NoDupMembers_skipn end.
  Qed.

  Lemma make_imap_cstream_skipn:
    forall xs ys n si,
      Forall (fun xcl=>exists sck, snd (fst xcl) = Cstream sck) (firstn n ys) ->
      make_imap si xs ys = make_imap si (skipn n xs) (skipn n ys).
  Proof.
    induction xs as [|(x, (xty, xck)) xs IH];
      destruct ys as [|((yty, yck), yloc) ys]; simpl;
      try setoid_rewrite skipn_nil;
      try setoid_rewrite firstn_nil;
      auto;
      intros n si Hfa.
    match goal with |- _ = make_imap _ ?xs [] =>
      now destruct xs; simpl; try destruct p; auto end.
    destruct n; auto.
    simpl in *.
    inversion_clear Hfa as [|? ? Hex].
    destruct Hex as (sck & Hex). simpl in Hex. subst.
    now apply IH.
  Qed.

  Lemma make_imap_notvnm_skipn:
    forall a nm xs ys n si,
      Forall (fun xcl=>match snd (fst xcl) with
                         Cnamed (Vnm _) _ => False | _ => True end)
             (firstn n ys) ->
      Env.find a (make_imap si xs ys) = Some (Vnm nm)
      -> Env.find a (make_imap si (skipn n xs) (skipn n ys)) = Some (Vnm nm).
  Proof.
    induction xs as [|(x, (xty, xck)) xs IH];
      destruct ys as [|((yty, yck), yloc) ys]; simpl;
      try setoid_rewrite skipn_nil;
      try setoid_rewrite firstn_nil;
      auto;
      intros n si Hfa Hfind.
    match goal with |- context [make_imap _ ?xs []] =>
      destruct xs; simpl; try destruct p; auto end.
    destruct n; simpl; auto.
    inversion_clear Hfa as [|? ? Hy Hfa'].
    destruct yck as [|ckid sck]; auto.
    destruct ckid. 2:contradiction.
    apply IH; auto.
    revert Hfind. clear.
    destruct (ident_eq_dec a x).
    2:now rewrite find_make_imap_add; auto.
    subst.
    assert (Env.find x (Env.add x (Vidx p) si) = Some (Vnm nm)
            -> Env.find x si = Some (Vnm nm)) as Hbase
        by (rewrite Env.gss; inversion 1).
    revert Hbase.
    generalize (Env.add x (Vidx p) si).
    revert ys si. induction xs as [|(z, (zty, zck)) xs IH]; intros ys si; auto.
    destruct ys; simpl; auto.
    repeat destruct p0.
    destruct n. now apply IH.
    intros sa Hfind.
    apply IH. intro HH.
    destruct (ident_eq_dec x z).
    now subst; rewrite Env.gss in *.
    rewrite Env.gso in *; auto.
  Qed.

  Lemma check_inputs_app:
    forall loc ys n xs,
      check_inputs loc xs ys = OK tt ->
      check_inputs loc (skipn n xs) (skipn n ys) = OK tt.
  Proof.
    induction ys as [|((yty, yck), yloc) ys IH]; intros n xs Hchk.
    now destruct xs as [|(xty, xck) xs]; repeat rewrite skipn_nil in *; auto;
      inversion Hchk.
    destruct xs as [|(xty, xck) xs]; [now inversion Hchk|].
    destruct n; auto.
    simpl. apply IH.
    now simpl in Hchk; monadInv Hchk.
  Qed.

  Lemma find_make_omap_vidx:
    forall xs s x,
      InMembers x xs ->
      exists i, Env.find x (snd (fold_left make_omap xs s)) = Some (Vidx i).
  Proof.
    intros xs (idx, s) x Hin.
    apply or_introl with (B:=exists i, Env.find x s = Some (Vidx i)) in Hin.
    revert s idx x Hin.
    induction xs as [|(x, xty) xs IH]. now inversion 1.
    intros s idx y HH.
    repeat destruct HH as [HH|HH]; apply IH; auto.
    - right. exists idx. subst. now rewrite Env.gss.
    - right. destruct (ident_eq_dec y x).
      + subst. exists idx. now rewrite Env.gss.
      + rewrite Env.gso; auto.
  Qed.

  (* TODO: add docs for this lemma and the previous big one.
     - needed to prove the induction hypothesis in (wt/wc)_elab_exp'.
       this hypothesis addresses the form of the lcks list which is
       passed down the expression tree and used to wrap constants in
       'when's. The induction hypothesis is used to show that the wrapping
       gives a well-typed/clocked expression.
     - this means that we must reason about elab_exp' without knowing that the
       terms it produces are well-typed.
       Essentially, we rely on the face that the treatment of variables
       (VARIABLE vx) is non-recursive and that facts about variables
       (that their types and clocks are good) have already been established
       in the environment.
     - the tricky part is to 'skip' over the types of expressions, each of
       which may represent a variable number of streams.
     - an alternative approach would be to explicitly check the well-formedness
       of wrapped expressions as they are created. This would greatly simplify
       the proofs (no induction hypothesis needed!), but engenders extra work
       during compilation, and this work is essentially useless, since we can
       establish (modulo quite a bit of work) that they are always well-formed.
     - Besides (slightly) more efficient elaboration, the other advantage of
       the proof-based approach is to explain and increase confidence in the
       elaboration algorithm, which is especially important since the algorithm
       may fail (return Error) without violating its correctness properties
       (that the resulting term is well-typed/clocked).
   *)

  Lemma make_imap_var_type:
    forall loc1 loc2 any isubst base aes iface eas alcks ianns fidx lfidx',
      NoDupMembers iface ->
      mmaps (elab_arg elab_exp') (alcks, fidx) aes = OK (lfidx', eas) ->
      mmap (inst_annot loc1 base isubst) iface = OK ianns ->
      check_inputs loc2 ianns (lnannots eas) = OK any ->
      (forall a x ty ack,
          Env.find a (make_imap (Env.empty ckid) iface (lnannots eas)) = Some (Vnm x) ->
          In (a, (ty, ack)) iface ->
          exists xck, Env.find x env = Some (ty, xck)).
  Proof.
    intros loc1 loc2 any isubst base aes iface. destruct any.
    assert (forall a x ty ack, Env.find a (Env.empty ckid) = Some (Vnm x) ->
                               In (a, (ty, ack)) iface ->
                               exists xck, Env.find x env = Some (ty, xck)) as Hfind
        by (setoid_rewrite Env.gempty; discriminate).
    revert iface Hfind.
    generalize (Env.empty ckid) as si.
    induction aes as [|ae aes IH];
      intros si iface Hnsa eas alcks ianns fidx (alcks', fidx')
             Hnd Helab Hianns Hchk a x ty ack Hfind Hin.
    simpl in Helab. monadInv Helab.
    now destruct iface as [|[b (bty, bck)]]; [inversion Hin|eauto].
    simpl in Helab. monadInv Helab. monadInv2 EQ.
    destruct iface as [|[b (bty, bck)]]; [now inversion Hin|].
    rename x3 into eas, x2 into fidx1, x4 into e, x5 into loc, EQ0 into Helab,
    EQ1 into Helabs.
    assert (Hnd':=Hnd).
    apply nodupmembers_cons in Hnd; destruct Hnd as [Hnin Hnd].
    destruct ae. simpl in Hchk.
    - (* UNARY *)
      destruct l. inversion Helab. destruct l. 2:inversion Helab.
      simpl in Helab. monadInv2 Helab.
      simpl in Hianns. monadInv2 Hianns.
      simpl in Hfind.
      inversion_clear Hin.
      + inversion H; subst; clear H.
        rewrite find_make_imap_not_in_members in Hfind;
          eauto with datatypes.
      + match goal with x:(type*nclock)%type |- _ => destruct x end.
        simpl in Hchk. monadInv2 Hchk.
        match goal with H1:mmap (inst_annot _ _ _) iface = _,
          H2:check_inputs _ _ _ = _, H3:In (a, _) iface |- _ =>
          apply IH with (2:=Hnd) (3:=Helabs) (4:=H1) (5:=H2) (6:=Hfind) (7:=H3)
        end.
        eauto with datatypes.
    - (* BINARY *)
      destruct l. inversion Helab. destruct l. 2:inversion Helab.
      destruct l0. inversion Helab. destruct l0. 2:inversion Helab.
      simpl in Helab. monadInv2 Helab.
      simpl in Hianns. monadInv2 Hianns.
      simpl in Hfind.
      inversion_clear Hin.
      + inversion H; subst; clear H.
        rewrite find_make_imap_not_in_members in Hfind;
          eauto with datatypes.
      + match goal with x:(type*nclock)%type |- _ => destruct x end.
        simpl in Hchk. monadInv2 Hchk.
        match goal with H1:mmap (inst_annot _ _ _) iface = _,
          H2:check_inputs _ _ _ = _, H3:In (a, _) iface |- _ =>
          apply IH with (2:=Hnd) (3:=Helabs) (4:=H1) (5:=H2) (6:=Hfind) (7:=H3)
        end.
        eauto with datatypes.
    - (* IFTE *)
      destruct l. inversion Helab. destruct l. 2:inversion Helab.
      simpl in Helab. monadInv2 Helab.
      rewrite lnannots_cons in *.
      simpl in Helabs.
      match goal with
        H:context [ skipn (length (lannots_ty (lannots ?x))) _ ] |- _ =>
        remember (length (lannots_ty (lannots x))) as len eqn:Hlen end.
      rewrite <-firstn_skipn with (n:=len) in Hin.
      apply in_app in Hin.
      rewrite make_imap_cstream_skipn with (n:=len) in Hfind.
      + rewrite skipn_app in Hfind.
        2:now rewrite Hlen; unfold lannots_ty; simpl;
          repeat rewrite Coqlib.list_length_map.
        destruct Hin as [Hin|Hin].
        * rewrite find_make_imap_not_in_members in Hfind.
          2:now eauto using InMembers_firstn_skipn, In_InMembers.
          eapply Hnsa; eauto using In_firstn.
        * apply check_inputs_app with (n:=len) in Hchk.
          rewrite skipn_app with (n:=len) in Hchk.
          2:rewrite Hlen; now unfold lannots_ty; simpl;
            repeat rewrite Coqlib.list_length_map.
          apply IH with (3:=Helabs) (5:=Hchk) (6:=Hfind) (7:=Hin);
            auto using NoDupMembers_skipn, mmap_skipn.
          intros; eapply Hnsa; eauto using In_skipn.
      + simpl. rewrite CommonList.firstn_app.
        2:now rewrite Coqlib.list_length_map; auto.
        unfold lannots_ty.
        rewrite map_map.
        repeat rewrite Forall_map.
        apply Forall_forall; intros; simpl; eauto.
    - (* CAST *)
      destruct l. inversion Helab. destruct l. 2:inversion Helab.
      simpl in Helab. monadInv2 Helab.
      simpl in Hianns. monadInv2 Hianns.
      simpl in Hfind.
      inversion_clear Hin.
      + inversion H; subst; clear H.
        rewrite find_make_imap_not_in_members in Hfind;
          eauto with datatypes.
      + match goal with x:(type*nclock)%type |- _ => destruct x end.
        simpl in Hchk. monadInv2 Hchk.
        match goal with H1:mmap (inst_annot _ _ _) iface = _,
          H2:check_inputs _ _ _ = _, H3:In (a, _) iface |- _ =>
          apply IH with (2:=Hnd) (3:=Helabs) (4:=H1) (5:=H2) (6:=Hfind) (7:=H3)
        end.
        eauto with datatypes.
    - (* APP *)
      simpl in Helab. monadInv Helab.
      setoid_rewrite surjective_pairing in EQ3.
      simpl in EQ3. monadInv EQ3.
      rewrite lnannots_cons in *.
      simpl in Helabs.
      match goal with H:context [ skipn (length ?x) _ ] |- _ =>
                      remember (length x) as len eqn:Hlen end.
      rewrite <-firstn_skipn with (n:=len) in Hin.
      apply in_app in Hin.
      apply make_imap_notvnm_skipn with (n:=len) in Hfind.
      + rewrite skipn_app in Hfind.
        2:now rewrite Hlen; unfold lannots_ty; simpl;
          repeat rewrite Coqlib.list_length_map.
        destruct Hin as [Hin|Hin].
        * rewrite find_make_imap_not_in_members in Hfind.
          2:now eauto using InMembers_firstn_skipn, In_InMembers.
          eapply Hnsa; eauto using In_firstn.
        * apply check_inputs_app with (n:=len) in Hchk.
          rewrite skipn_app with (n:=len) in Hchk.
          2:rewrite Hlen; now unfold lannots_ty; simpl;
            repeat rewrite Coqlib.list_length_map.
          apply IH with (3:=Helabs) (5:=Hchk) (6:=Hfind) (7:=Hin);
            auto using NoDupMembers_skipn, mmap_skipn.
          intros; eapply Hnsa; eauto using In_skipn.
      + simpl. rewrite CommonList.firstn_app.
        2:now rewrite Coqlib.list_length_map; auto.
        apply Forall_forall.
        intros ((zty, zck), zloc) Hzin.
        apply in_map_iff in Hzin.
        destruct Hzin as (zann & Hzeq & Hzin).
        destruct zann. inversion Hzeq; subst; clear Hzeq.
        match goal with H: context [fold_left make_omap ?xs ?s] |- _ =>
          apply mmap_inversion in H end.
        match goal with H: Coqlib.list_forall2 _ _ _ |- _ =>
           apply Coqlib.list_forall2_in_right with (2:=Hzin) in H;
             destruct EQ3 as ((y, (t, c)) & Hzin2 & Hann) end.
        simpl in Hann. monadInv Hann.
        apply In_InMembers in Hzin2.
        eapply find_make_omap_vidx in Hzin2.
        destruct Hzin2 as [idx Hzin2].
        match goal with H:_ = OK (zty, zck) |- _ =>
          now rewrite Hzin2 in H; monadInv H end.
    - (* CONSTANT *)
      monadInv Helab.
      match goal with H:context [add_whens ?loc _ ?const] |- _ =>
        destruct (lnannot_add_whens loc alcks const) as [wclk Haw] end.
      rewrite lnannots_cons, Haw in Hfind, Hchk.
      destruct ianns as [|(ity, inck) ianns]. now inversion Hchk.
      monadInv Hchk.
      inversion_clear Hin as [Hin'|Hin'].
      + inversion Hin'; subst; clear Hin'.
        simpl in Hfind.
        rewrite find_make_imap_not_in_members in Hfind; auto.
        eapply Hnsa with (1:=Hfind); eauto with datatypes.
      + apply mmap_skipn with (n:=1) in Hianns.
        match goal with H:check_inputs _ _ _ = OK _ |- _ =>
          apply IH with (2:=Hnd) (3:=Helabs) (4:=Hianns) (5:=H) (6:=Hfind) (7:=Hin')
        end.
        intros; eapply Hnsa; eauto with datatypes.
    - (* VARIABLE *)
      simpl in Helab. monadInv Helab.
      destruct ianns as [|(ity, ick) ianns]. now inversion Hchk.
      simpl in Hchk. monadInv Hchk.
      apply assert_type_spec in EQ0.
      subst.
      simpl in Helabs.
      rewrite lnannots_cons in Hfind.
      simpl in Hfind.
      simpl in Hianns. monadInv Hianns. monadInv EQ0.
      inversion_clear Hin as [Hin'|Hin'].
      + inversion Hin'; subst; clear Hin'.
        rewrite find_make_imap_not_in_members with (1:=Hnin) in Hfind.
        rewrite Env.gss in Hfind. inversion Hfind; subst; clear Hfind.
        apply find_var_in in EQ.
        exists x1.
        apply Env.elements_complete in EQ.
        destruct (Env.find a isubst).
        inversion EQ5; subst; auto.
        inversion EQ5; subst; auto.
      + rewrite find_make_imap_add in Hfind.
        2:now intro; subst; eauto using In_InMembers.
        apply IH with (2:=Hnd) (3:=Helabs) (4:=EQ4) (5:=EQ3) (6:=Hfind) (7:=Hin').
        eauto with datatypes.
    - (* FBY *)
      simpl in Helab. monadInv Helab.
      rewrite lnannots_cons in *.
      simpl in Helabs.
      match goal with
        H:context [ skipn (length (map discardname (lnannots ?x))) _ ] |- _ =>
        remember (length (map discardname (lnannots x))) as len eqn:Hlen end.
      rewrite <-firstn_skipn with (n:=len) in Hin.
      apply in_app in Hin.
      rewrite make_imap_cstream_skipn with (n:=len) in Hfind.
      + rewrite skipn_app in Hfind.
        2:now rewrite Hlen; unfold lannots_ty; simpl;
          repeat rewrite Coqlib.list_length_map.
        destruct Hin as [Hin|Hin].
        * rewrite find_make_imap_not_in_members in Hfind.
          2:now eauto using InMembers_firstn_skipn, In_InMembers.
          eapply Hnsa; eauto using In_firstn.
        * apply check_inputs_app with (n:=len) in Hchk.
          rewrite skipn_app with (n:=len) in Hchk.
          2:rewrite Hlen; now unfold lannots_ty; simpl;
            repeat rewrite Coqlib.list_length_map.
          apply IH with (3:=Helabs) (5:=Hchk) (6:=Hfind) (7:=Hin);
            auto using NoDupMembers_skipn, mmap_skipn.
          intros; eapply Hnsa; eauto using In_skipn.
      + simpl. rewrite CommonList.firstn_app.
        2:now rewrite Coqlib.list_length_map; auto.
        repeat rewrite Forall_map.
        apply Forall_forall; intros; simpl.
        match goal with ann:(type * nclock * astloc)%type |- _ =>
          destruct ann as ((wty, wck), wloc) end.
        simpl; eauto.
    - (* WHEN *)
      simpl in Helab. monadInv2 Helab.
      rewrite lnannots_cons in *.
      simpl in Helabs.
      match goal with
        H:context [ skipn (length (lannots_ty (lannots ?x))) _ ] |- _ =>
        remember (length (lannots_ty (lannots x))) as len eqn:Hlen end.
      rewrite <-firstn_skipn with (n:=len) in Hin.
      apply in_app in Hin.
      rewrite make_imap_cstream_skipn with (n:=len) in Hfind.
      + rewrite skipn_app in Hfind.
        2:now rewrite Hlen; unfold lannots_ty; simpl;
          repeat rewrite Coqlib.list_length_map.
        destruct Hin as [Hin|Hin].
        * rewrite find_make_imap_not_in_members in Hfind.
          2:now eauto using InMembers_firstn_skipn, In_InMembers.
          eapply Hnsa; eauto using In_firstn.
        * apply check_inputs_app with (n:=len) in Hchk.
          rewrite skipn_app with (n:=len) in Hchk.
          2:rewrite Hlen; now unfold lannots_ty; simpl;
            repeat rewrite Coqlib.list_length_map.
          apply IH with (3:=Helabs) (5:=Hchk) (6:=Hfind) (7:=Hin);
            auto using NoDupMembers_skipn, mmap_skipn.
          intros; eapply Hnsa; eauto using In_skipn.
      + simpl. rewrite CommonList.firstn_app.
        2:now rewrite Coqlib.list_length_map; auto.
        unfold lannots_ty.
        repeat rewrite Forall_map.
        apply Forall_forall; intros; simpl; eauto.
    - (* MERGE *)
      simpl in Helab. monadInv2 Helab.
      rewrite lnannots_cons in *.
      simpl in Helabs.
      match goal with
        H:context [ skipn (length (lannots_ty (lannots ?x))) _ ] |- _ =>
        remember (length (lannots_ty (lannots x))) as len eqn:Hlen end.
      rewrite <-firstn_skipn with (n:=len) in Hin.
      apply in_app in Hin.
      rewrite make_imap_cstream_skipn with (n:=len) in Hfind.
      + rewrite skipn_app in Hfind.
        2:now rewrite Hlen; unfold lannots_ty; simpl;
          repeat rewrite Coqlib.list_length_map.
        destruct Hin as [Hin|Hin].
        * rewrite find_make_imap_not_in_members in Hfind.
          2:now eauto using InMembers_firstn_skipn, In_InMembers.
          eapply Hnsa; eauto using In_firstn.
        * apply check_inputs_app with (n:=len) in Hchk.
          rewrite skipn_app with (n:=len) in Hchk.
          2:rewrite Hlen; now unfold lannots_ty; simpl;
            repeat rewrite Coqlib.list_length_map.
          apply IH with (3:=Helabs) (5:=Hchk) (6:=Hfind) (7:=Hin);
            auto using NoDupMembers_skipn, mmap_skipn.
          intros; eapply Hnsa; eauto using In_skipn.
      + simpl. rewrite CommonList.firstn_app.
        2:now rewrite Coqlib.list_length_map; auto.
        unfold lannots_ty.
        repeat rewrite Forall_map.
        apply Forall_forall; intros; simpl; eauto.
  Qed.

  Lemma wt_exp_lannot_all_sclock:
    forall G env e a,
      wt_exp G env e ->
      exists tsls, lannot (e, a) = tsls
                   /\ Forall (fun x=>wt_sclock env (snd (fst x))) tsls.
  Proof.
    destruct e; simpl; intros * Hwt; eexists;
      repeat split; eauto with ltyping;
        try match goal with a:ann |- _ => destruct a end;
        try now (inversion_clear Hwt;
                 try match goal with H:wt_nclock _ _ |- _ => inv H end;
                 eauto with ltyping).
    - (* Efby *)
      inversion_clear Hwt.
      apply Forall_forall.
      intros x Hin.
      apply in_map_iff in Hin.
      destruct Hin as ((wty, wnck) & Heq & Hin).
      subst. simpl.
      match goal with H:Forall (wt_nclock _) _ |- _ =>
        rewrite Forall_map in H;
          apply Forall_forall with (1:=H) in Hin end.
      auto using wt_nclock_sclock.
    - (* Ewhen *)
      match goal with la:lann |- _ => destruct la end.
      apply Forall_map.
      inversion_clear Hwt.
      apply Forall_forall.
      match goal with H:wt_nclock _ _ |- _ => inv H; now auto end.
    - (* Emerge *)
      match goal with la:lann |- _ => destruct la end.
      apply Forall_map.
      inversion_clear Hwt.
      apply Forall_forall.
      match goal with H:wt_nclock _ _ |- _ => inv H; now auto end.
    - (* Eite *)
      match goal with la:lann |- _ => destruct la end.
      apply Forall_map.
      inversion_clear Hwt.
      apply Forall_forall.
      match goal with H:wt_nclock _ _ |- _ => inv H; now auto end.
    - (* Eapp *)
      apply Forall_map.
      inversion_clear Hwt.
      eapply Forall_impl; eauto.
      intros (?, ?); inversion 1; auto.
  Qed.

  Lemma build_whens_typeof:
    forall loc e tys sck,
      typeof e = tys ->
      typeof (build_whens loc e tys sck) = tys.
  Proof.
    intros * Ht.
    induction sck; auto.
    match goal with c:ckid |- _ => destruct c end; auto.
  Qed.

  Lemma check_inputs_spec_types:
    forall loc any iface args,
      check_inputs loc iface args = OK any ->
      map fst iface = map (fun x=>fst (fst x)) args.
  Proof.
    induction iface as [|(ity, inck) iface IH].
    - destruct args.
      now simpl; auto.
      now inversion 1.
    - destruct args as [|((aty, anck), al) args].
      now inversion 1.
      simpl. intro Hchk. monadInv Hchk.
      match goal with H:assert_type _ _ _ = OK _ |- _ =>
        apply assert_type_spec in H end.
      match goal with H:check_inputs _ _ _ = OK _ |- _ =>
        rewrite IH with (1:=H) end.
      now subst.
  Qed.

  Lemma check_inputs_spec:
    forall loc any iface args,
      check_inputs loc iface args = OK any ->
      Forall2 (fun tc tc' =>
                 match tc, tc' with
                   (ty, nck), (ty', nck', _) =>
                   ty = ty'
                   /\ stripname nck = stripname nck'
                 end) iface args.
  Proof.
    induction iface as [|(ity, inck) iface IH].
    - destruct args.
      now simpl; auto using Forall2_nil.
      now inversion 1.
    - destruct args as [|((aty, anck), al) args].
      now inversion 1.
      simpl. intro Hchk. monadInv Hchk.
      apply Forall2_cons. 2:now apply IH.
      match goal with H:assert_type _ _ _ = OK _ |- _ =>
        apply assert_type_spec in H end.
      match goal with H:assert_sclock _ _ _ = OK _ |- _ =>
        apply assert_sclock_spec in H end.
      auto.
  Qed.

  Lemma lnannots_typesof:
    forall els,
      map (fun x=>fst (fst x)) (lnannots els) = typesof (map fst els).
  Proof.
    unfold lnannots, typesof.
    induction els as [|el els IH]; auto.
    simpl.
    rewrite map_app, IH.
    assert (map (fun x=>fst (fst x)) (lnannot el) = typeof (fst el)) as HH.
    2:now rewrite HH.
    clear IH els.
    destruct el as (e & loc).
    destruct e; intros;
      repeat match goal with
             | a:ann |- _ => destruct a
             | l:lann |- _ => destruct l
             end;
      simpl; try rewrite map_map;
      simpl; try rewrite map_id; auto.
  Qed.

  Lemma wt_inst_clock:
    forall loc env1 env2 bck s ck sck,
      wt_sclock env2 bck ->
      wt_clock env1 ck ->
      (forall x y ty,
          Env.find x s = Some (Vnm y) ->
          In (x, ty) env1 ->
          In (y, ty) env2) ->
      inst_clock loc bck s ck = OK sck ->
      wt_sclock env2 sck.
  Proof.
    intros * Hbck Hck Hf Hinst.
    revert ck sck Hinst Hck.
    induction ck; simpl; intros sck Hm Hck.
    now inversion Hm; subst; auto.
    monadInv Hm. NamedDestructCases.
    inversion_clear Hck as [|? ? ? ? Hwtck].
    specialize (IHck _ EQ Hwtck).
    destruct c; auto with ltyping.
    eapply Hf in Heq; eauto with ltyping.
  Qed.

  Lemma lnannot_0:
    forall e loc,
      numstreams e = 0 ->
      lnannot (e, loc) = [].
  Proof.
    destruct e; try (now inversion 1);
      try (now destruct l1; destruct l1; inversion 1);
      try (now destruct l0; destruct l0; inversion 1).
    now destruct l1; auto.
    now destruct l0; inversion 1.
  Qed.

  Lemma lnannot_Sn:
    forall e loc n,
      numstreams e = S n ->
      exists ann anns,
        lnannot (e, loc) = ann::anns.
  Proof.
    intros e loc n Hns.
    destruct e; simpl in *;
      try destruct a;
      repeat (now eexists; eauto);
      try (now destruct l1; destruct l1; inversion Hns; simpl; eauto);
      try (now destruct l0; destruct l0; inversion Hns; simpl; eauto).
    now destruct l1; inversion Hns; simpl; eauto.
    now destruct l0; inversion Hns; simpl; eauto.
  Qed.

  Lemma wt_lnannot:
    forall G env e loc,
      wt_exp G env e ->
      forall ty nck loc',
        In ((ty, nck), loc') (lnannot (e, loc)) ->
        wt_nclock env nck.
  Proof.
    intros * Hwt ty nck loc' Hin.
    destruct e;
      try destruct a as (aty, ack);
      simpl in *;
      try (inversion_clear Hwt; destruct Hin as [Hin|Hin]; inv Hin;
           now auto with ltyping);
      try (destruct l1 || destruct l0;
           apply in_map_iff in Hin;
           destruct Hin as (ty' & HH & Hin);
           inv HH; now inv Hwt).
    - (* Efby *)
      inv Hwt.
      match goal with H:Forall (wt_nclock _) _ |- _ =>
                      eapply Forall_forall in H; eauto end.
      apply in_map_iff. apply in_map_iff in Hin.
      destruct Hin as (ty' & HH & Hin).
      inv HH. eexists. now split; eauto.
    - (* Eapp *)
      apply in_map_iff in Hin.
      destruct Hin as (ty' & HH & Hin).
      inv HH. inv Hwt.
      eapply Forall_forall in Hin; eauto.
      now simpl in Hin.
  Qed.

  Lemma map_fst_discardname_types:
    forall els,
      map fst (map discardname (lnannots els)) = typesof (map fst els).
  Proof.
    assert(forall xs, map fst (map discardname xs)
                      = map (fun x=>fst (fst x)) xs) as map_fst_discardname.
    - induction xs as [|x xs IH]; auto.
      destruct x as ((xty, xnck), xloc).
      now simpl; rewrite IH.
    - induction els as [|el els IH]; auto.
      simpl.
      rewrite map_app, <-IH; repeat rewrite map_app.
      rewrite map_fst_discardname.
      destruct el as (e & loc).
      now rewrite <-lnannot_typeof.
  Qed.

  Lemma map_snd_discardname_clocks:
    forall els,
      map snd (map discardname (lnannots els)) = map Cstream (clocksof (map fst els)).
  Proof.
    induction els as [|el els IH]; auto.
    simpl. rewrite map_app, map_app, IH, map_app.
    destruct el as [e loc].
    destruct e; simpl; auto; unfold ckstream.
    - destruct a; destruct n; auto.
    - destruct a; destruct n; auto.
    - destruct a; destruct n; auto.
    - induction l1; simpl; try rewrite IHl1; auto.
    - destruct l0; simpl.
      induction l0; simpl; try rewrite IHl0; auto.
    - destruct l1; simpl.
      induction l1; simpl; try rewrite IHl1; auto.
    - destruct l1; simpl.
      induction l1; simpl; try rewrite IHl1; auto.
    - destruct l0; auto.
      destruct a; simpl. repeat rewrite map_map; auto.
  Qed.

  Lemma wt_elab_exp':
    forall ae e lcks fidx fidx' loc,
      elab_exp' lcks fidx ae = OK (fidx', (e, loc)) ->
      Forall (wt_sclock (idty (Env.elements env))) lcks ->
      wt_exp G (idty (Env.elements env)) e.
  Proof.
    induction ae using expression_ind2;
    intros e lcks fidx fidx' loc Helab Hlcks;
    inv Helab; NamedDestructCases;
    repeat progress match goal with
    | H: Forall _ [?e] |- _ => inv H
    | H1: context [elab_exp' _ _ _ = OK _],
      H2: elab_exp' _ _ _ = OK _ |- wt_exp _ _ _  =>
      apply H1 in H2; clear H1; auto
    | H:find_type_unop _ _ _ = OK _ |- _ =>
      unfold find_type_unop in H;
      rewrite type_unop'_correct in H; NamedDestructCases
    | H:find_type_binop _ _ _ _ = OK _ |- _ =>
      unfold find_type_binop in H;
      rewrite type_binop'_correct in H; NamedDestructCases
    | H:assert_type _ _ _ = OK _ |- _ => apply assert_type_spec in H
    | H:assert_id_type _ _ _ _ = OK _ |- _ => apply assert_id_type_spec in H
    | Hwt:wt_exp _ _ ?e, Hco: clockof ?e = [?c] |- _  =>
      let H := fresh "H" in (
      pose proof (wt_exp_clockof _ _ _ Hwt) as H;
      rewrite Hco in H; clear Hco; inv H)
    | H: _ = OK _ |- _ => monadInv2 H
    | H: single_annot _ _ = OK _ |- _ =>
      apply single_annot_spec in H; destruct H
    | H:assert_paired_types _ _ _ _ _ = OK _ |- _ =>
      apply assert_paired_types_spec_types in H;
      setoid_rewrite lannots_ty_lannots_spec in H
    | H:Forall _ [] |- _ => clear H
    end.
    - (* Eunop *)  eauto with ltyping.
    - (* Ebinop *) eauto with ltyping.
    - (* Eite *)
      econstructor; try rewrite lannots_ty_lannots_spec; eauto with ltyping;
        rewrite Forall_map;
        repeat progress match goal with
        | Hmm: mmaps _ _ ?aes = OK (_, ?es) |- Forall _ ?es =>
          apply mmaps_weak_spec' with (1:=Hmm); auto; intros ????? Helab
        | |- wt_exp _ _ (fst ?eloc) => destruct eloc; simpl
        | Hfa: Forall _ ?eas, Hin:In ?ea ?eas,
          Helab:elab_exp' _ _ ?ea = OK (_, (?e, _)) |- wt_exp _ _ ?e =>
          apply Forall_forall with (1:=Hfa) (2:=Hin) in Helab; now auto
        end.
    - (* Eunop (CastOp) *) eauto using type_castop with ltyping.
    - (* Eapp *)
      match goal with x:(list sclock * positive)%type |- _ =>
                      destruct x as (sclks & fidx'') end.
      match goal with x:(Env.t ident)%type |- _ => rename x into aimap end.
      setoid_rewrite surjective_pairing in EQ3.
      NamedDestructCases. simpl in *.
      monadInv EQ3.
      match goal with |- context [Eapp f (map fst ?x1) ?x2] =>
        rename x1 into els, x2 into oann end.
      match goal with H:check_inputs _ ?x _ = OK ?any |- _ =>
                      rename x into iann; destruct any end.
      unfold find_node_interface in *. NamedDestructCases.
      apply wt_nenv in Heq. destruct Heq as (n & Hfind & Hnin & Hnout).
      apply Forall2_eq in Hnin. apply Forall2_eq in Hnout. subst.
      destruct wf_G as (wt_G & wc_G).
      destruct (wt_find_node _ _ _ wt_G Hfind) as (G' & Hfind').
      match goal with EQ0:approx_imap _ _ _ = OK _,
                      EQ1:mmaps (elab_arg elab_exp') _ _ = OK _,
                      EQ2:mmap _ _ = OK iann,
                      EQ3:check_inputs _ _ _ = OK _,
                      EQ4:mmap _ _ = OK oann
                      |- _ =>
        rename EQ0 into Hai, EQ1 into Hearg, EQ2 into Hiann, EQ3 into Hchk,
               EQ4 into Hoann
      end.
      assert (Forall (wt_sclock (idty (Env.elements env)))
                     (map (fun xtc =>
                             approx_clock (approx_base_clock lcks n.(n_out))
                                          aimap (dck xtc)) n.(n_in))) as Hwtac.
      { apply Forall_forall.
        setoid_rewrite in_map_iff.
        intros ? ((z, (zty, zck)) & Hz & Hzin).
        pose proof (approx_imap_to_make_imap _ _ _ _ _ _ _
          (NoDupMembers_app_l _ _ n.(n_nodup)) Hai Hearg) as Haim.
        pose proof (make_imap_var_type _ _ _ _ _ _ _ _ _ _ _ _
          (NoDupMembers_app_l _ _ n.(n_nodup)) Hearg Hiann Hchk) as Him.
        subst. unfold dck. simpl.
        inversion Hfind' as (Hwtin & Hother). clear Hother.
        apply Forall_forall with (2:=Hzin) in Hwtin.
        unfold dck in Hwtin. simpl in Hwtin. clear Hzin.
        induction zck.
        - apply wt_approx_base_clock. now inversion Hlcks; auto.
        - simpl.
          destruct (Env.find i aimap) eqn:Hia.
          2:now inversion Hwtin; intuition.
          apply Haim in Hia.
          inversion_clear Hwtin as [|? ? ? Hiin Hwtzck].
          unfold idty in Hiin. apply in_map_iff in Hiin.
          destruct Hiin as ((w, (wty, wck)) & Hwe & Hin).
          inv Hwe. pose proof Hia as Hia'; apply Env.find_In in Hia'.
          apply map_imap_InMembers in Hia'.
          destruct Hia' as [Hia'|Hia'].
          2:now apply Env.Props.P.F.empty_in_iff in Hia'.
          eapply Him in Hia; eauto.
          destruct Hia as [? Hia].
          rewrite Hia.
          constructor; eauto using wt_sclk.
          apply Env.elements_correct in Hia.
          apply in_map_iff.
          exists (i0, (bool_type, x)); eauto using wt_sclk. }
      econstructor; eauto.
      + apply Forall_map.
        eapply mmaps_weak_spec with (1:=Hearg)
          (I:=fun s=>Forall (wt_sclock (idty (Env.elements env))) (fst s)).
        now auto.
        intros ae (lcks1, fidx1) (e, loc0) (lcks2, fidx2) Hwt Hin Helab.
        simpl. simpl in Helab. monadInv2 Helab.
        eapply Forall_forall in Hin; eauto.
        eauto using Forall_skipn.
      + apply check_inputs_spec_types in Hchk.
        rewrite lnannots_typesof in Hchk.
        rewrite <-Hchk.
        apply mmap_inversion, list_forall2_Forall2 in Hiann.
        apply Forall2_map_1, Forall2_swap_args.
        apply Forall2_impl_In with (2:=Hiann).
        intros (w, (wty, wck)) (ty, nck) Hin1 Hin2 Hann.
        simpl in Hann; monadInv Hann.
        unfold dty. simpl.
        repeat match goal with
               | H: context [Env.find ?x (make_imap ?s ?n ?xs)] |- _ =>
                 destruct (Env.find x (make_imap s n xs))
               | H: OK _ = OK _ |- _ => now inversion H
               end.
      + apply mmap_inversion, list_forall2_Forall2, Forall2_swap_args in Hoann.
        apply Forall2_impl_In with (2:=Hoann).
        intros (ty, nck) (w, (wty, wck)) Hin1 Hin2 Hann.
        simpl in Hann; monadInv Hann.
        unfold dty. simpl.
        repeat match goal with
               | H: context [Env.find ?x ?xs] |- _ => destruct (Env.find x xs)
               | H: OK _ = OK _ |- _ => now inversion H end.
      + pose proof (make_imap_var_type _ _ _ _ _ _ _ _ _ _ _ _
          (NoDupMembers_app_l _ _ n.(n_nodup)) Hearg Hiann Hchk) as Him.
        apply Forall_forall.
        intros (x, nck) Hin.
        apply mmap_inversion, list_forall2_Forall2, Forall2_swap_args in Hoann.
        apply Forall2_in_left with (2:=Hin) in Hoann.
        destruct Hoann as ((o, (oty, ock)) & Hyin & Hinst).
        simpl in Hinst. monadInv Hinst.
        destruct Hfind' as (Hwtci & Hwtco & Hwtcv & HH).
        clear Hwtci Hwtcv HH.
        apply Forall_forall with (2:=Hyin) in Hwtco.
        unfold dck in Hwtco; simpl in Hwtco.
        eapply wt_inst_clock in EQ; eauto.
        * simpl; NamedDestructCases; intro; subst; eauto with ltyping.
        * unfold calculate_base_clock.
          destruct n.(n_in) as [|(w, (wty, wck)) ws]; auto with ltyping.
          clear Hchk Hfind Hai Hiann Hyin wt_G wc_G Hwtco Him Hin EQ EQ0
                loc x nck o oty ock G' x0 iann oann.
          revert es els fidx'' sclks fidx H Hearg.
          induction es as [|e es IH].
          now simpl; intros; monadInv Hearg; auto with ltyping.
          intros. inversion_clear H as [|? ? Hwtes1 Hwtes2].
          simpl in Hearg. monadInv2 Hearg. monadInv2 EQ.
          rewrite lnannots_cons.
          destruct (numstreams x3) eqn:Hns.
          now eapply IH in Hwtes2; try rewrite lnannot_0; eauto.
          apply Hwtes1 in EQ0; auto.
          eapply lnannot_Sn in Hns.
          destruct Hns as (((rty, rck), rloc) & anns & Hns).
          rewrite Hns. simpl.
          apply wt_find_base.
          match goal with H:lnannot ?e = ?ann :: _ |- _ =>
            assert (In ann (lnannot e)) as Hain end.
          rewrite Hns; auto with datatypes.
          eapply wt_lnannot in Hain; try inv Hain; eauto.
        * intros w y wty Hfw Hwin.
          unfold idty in Hwin.
          rewrite map_app, in_app in Hwin.
          setoid_rewrite in_map_iff in Hwin.
          destruct Hwin as [((w', (wty', wck)) & Heq & Hwin)
                           |((w', (wty', wck)) & Heq & Hwin)]; inv Heq.
          { rewrite find_make_omap_not_in_members in Hfw.
            - apply Him with (2:=Hwin) in Hfw.
              destruct Hfw as (wck' & Hfw).
              apply Env.elements_correct in Hfw.
              unfold idty. apply in_map_iff.
              exists (y, (wty, wck')); auto.
            - intro Hwin'.
              apply In_InMembers in Hwin.
              apply (NoDupMembers_app_InMembers _ _ _ n.(n_nodup) Hwin).
              apply InMembers_app; auto. }
          apply In_InMembers in Hwin.
          eapply find_make_omap_vidx in Hwin.
          destruct Hwin as (i & Hwin).
          now rewrite Hwin in Hfw.
    - (* Econst *)
      unfold add_whens.
      case (do_add_when_to_constants tt); auto with ltyping.
      destruct lcks; simpl; auto with ltyping.
      inversion_clear Hlcks as [|? ? Hs Hl']; clear Hl'.
      match goal with
      | H:wt_sclock _ ?s |- _ =>
        induction s; inversion_clear Hs as [|? ? ? ? Hwt|? ? ? Hwt];
          simpl; auto with ltyping; specialize (IHs Hwt)
      end.
      constructor; auto with ltyping.
      unfold typesof.
      simpl. rewrite app_nil_r, build_whens_typeof; auto.
    - (* Evar *)
      constructor;
      eauto using find_var_wt_clock, wt_sclk, find_var_type with ltyping.
    - (* Efby *)
      econstructor;
      try rewrite Forall_map;
      try rewrite map_fst_discardname_types;
      repeat progress match goal with
      | Hmm: mmaps _ _ ?aes = OK (_, ?es) |- Forall _ ?es =>
        apply mmaps_weak_spec' with (1:=Hmm); auto; intros ????? Helab
      | |- wt_exp _ _ (fst ?eloc) => destruct eloc; simpl
      | Hfa: Forall _ ?eas, Hin:In ?ea ?eas,
        Helab:elab_exp' _ _ ?ea = OK (_, (?e, _)) |- wt_exp _ _ ?e =>
        apply Forall_forall with (1:=Hfa) (2:=Hin) in Helab; now auto
      | H:assert_paired_clock_types _ _ _ = OK _ |- _ =>
        apply assert_paired_clock_types_spec_types in H;
          setoid_rewrite lnannots_typesof in H;
          try rewrite H
      end; auto.
      apply mmaps_weak_spec' with
        (R:=fun el=>wt_exp G (idty (Env.elements env)) (fst el)) in EQ.
      2:intros ae s (e, el) s' Hin Helab;
        apply Forall_forall with (1:=H) in Hin;
        apply Hin with (1:=Helab); now auto.
      apply Forall_forall.
      intros (wty, wnck) Hin.
      apply Coqlib.list_in_map_inv in Hin.
      destruct Hin as (((wty', wnck'), wlock') & Heq & Hin).
      unfold discardname in Heq. simpl in Heq.
      inv Heq. simpl.
      unfold lnannots in Hin.
      apply In_flat_map in Hin.
      destruct Hin as ((e & l) & Hin & Hins).
      eapply Forall_forall in EQ; eauto.
      eapply wt_lnannot with (2:=Hins) in EQ.
      inv EQ; eauto with ltyping.
    - (* Ewhen *)
      econstructor; try rewrite lannots_ty_lannots_spec; eauto with ltyping;
      try rewrite Forall_map;
        repeat progress match goal with
        | Hmm: mmaps _ _ ?aes = OK (_, ?es) |- Forall _ ?es =>
          apply mmaps_weak_spec' with (1:=Hmm); auto; intros ????? Helab
        | |- wt_exp _ _ (fst ?eloc) => destruct eloc; simpl
        | Hfa: Forall _ ?eas, Hin:In ?ea ?eas,
          Helab:elab_exp' _ _ ?ea = OK (_, (?e, _)) |- wt_exp _ _ ?e =>
          apply Forall_forall with (1:=Hfa) (2:=Hin) in Helab; apply Helab
        | H: find_var _ ?x = OK _ |- In (x, _) _ =>
          subst; apply find_var_type with (1:=H)
        end;
        eauto using find_var_type, find_var_wt_clock, wt_sclk.
      subst.
      match goal with H:find_var _ _ = OK _ |- _ =>
        pose proof (find_var_type _ _ _ _ H); apply find_var_wt_clock in H end.
      eauto using wt_sclk with ltyping.
    - (* Emerge *)
      econstructor; try rewrite lannots_ty_lannots_spec; eauto with ltyping;
      try rewrite Forall_map;
        repeat progress match goal with
        | Hmm: mmaps _ _ ?aes = OK (_, ?es) |- Forall _ ?es =>
          apply mmaps_weak_spec' with (1:=Hmm); auto; intros ????? Helab
        | |- wt_exp _ _ (fst ?eloc) => destruct eloc; simpl
        | Hfa: Forall _ ?eas, Hin:In ?ea ?eas,
          Helab:elab_exp' _ _ ?ea = OK (_, (?e, _)) |- wt_exp _ _ ?e =>
          now apply Forall_forall with (1:=Hfa) (2:=Hin) in Helab
        | H: find_var _ ?x = OK _ |- In (x, _) _ =>
          subst; apply find_var_type with (1:=H)
        | H:find_var _ _ = OK _ |- _ =>
          pose proof (find_var_type _ _ _ _ H); apply find_var_wt_clock in H
        | H:In _ ets, Ha:Forall _ ets |- _ => apply Forall_forall with (1:=Ha) in H
        | H:In _ efs, Ha:Forall _ efs |- _ => apply Forall_forall with (1:=Ha) in H
        end; subst;
          eauto using wt_sclk with ltyping.
  Qed.

  Lemma lannots_clocksof:
    forall els,
      map (fun x => snd (fst x)) (lannots els) = clocksof (map fst els).
  Proof.
    induction els as [|el els IH]. now simpl.
    simpl. rewrite map_app, IH.
    destruct el as (e & l).
    destruct e;
      try destruct a; simpl; try (destruct l2 || destruct l1);
        try rewrite map_map; auto.
  Qed.

  Lemma lnannots_nclocksof:
    forall els,
      map (fun x => snd (fst x)) (lnannots els) = nclocksof (map fst els).
  Proof.
    induction els as [|el els IH]; auto.
    simpl. rewrite map_app, IH.
    destruct el as (e & l).
    destruct e; simpl;
      (try now destruct a; auto);
      auto.
    - rewrite map_map; induction l2; auto.
    - destruct l1; rewrite map_map; auto.
    - destruct l2; rewrite map_map; auto.
    - destruct l2; rewrite map_map; auto.
    - rewrite map_map; induction l1; auto.
  Qed.

  Lemma map_ckstream_lnannots_clocksof:
    forall els,
      map (fun ann=> ckstream (fst ann)) (lnannots els) = clocksof (map fst els).
  Proof.
    induction els as [|el els IH]. now simpl.
    simpl; rewrite map_app, IH.
    destruct el as (e & l).
    destruct e; simpl;
      (try now destruct a; auto);
      try rewrite map_map;
      auto.
    - destruct l1; rewrite map_map; auto.
    - destruct l2; rewrite map_map; auto.
    - destruct l2; rewrite map_map; auto.
  Qed.

  Lemma map_ckstream_discardname_lnannots_clocksof:
    forall els,
      map ckstream (map discardname (lnannots els)) = clocksof (map fst els).
  Proof.
    setoid_rewrite map_map.
    induction els as [|el els IH]. now simpl.
    simpl; rewrite map_app, IH.
    destruct el as (e & l).
    destruct e; simpl;
      (try now destruct a; auto);
      auto.
    - rewrite map_map; induction l2; auto.
    - destruct l1; rewrite map_map; auto.
    - destruct l2; rewrite map_map; auto.
    - destruct l2; rewrite map_map; auto.
    - rewrite map_map; induction l1; auto.
  Qed.

  Lemma assert_same_clock_spec:
    forall any sck anns,
      assert_same_clock sck anns = OK any ->
      Forall (fun a=>sck = snd (fst a)) anns.
  Proof.
    destruct any.
    induction anns as [|ann anns IH]. now auto.
    destruct ann as ((ty, sck'), loc).
    simpl. intro Hsame.
    monadInv Hsame.
    match goal with H:assert_sclock _ _ _ = OK ?x |- _ =>
      destruct x; apply assert_sclock_spec in H; subst end.
    auto.
  Qed.

  Open Scope positive.

  Lemma fst_fold_left_make_omap:
    forall xs fidx env,
      fst (fold_left make_omap xs (fidx, env)) =
        (match xs with [] => fidx
                     | _ => fidx + Pos.of_nat (length xs) end).
  Proof.
    induction xs as [|x xs IH]; auto.
    setoid_rewrite IH.
    intros fidx env'.
    destruct xs; auto.
    simpl. now rewrite <-Pos.add_assoc, Pos.add_1_l.
  Qed.

  Lemma fst_fold_left_make_omap1:
    forall xs fidx env,
      fidx <= fst (fold_left make_omap xs (fidx, env)).
  Proof.
    induction xs as [|x xs IH]. now simpl; p_order.
    intros fidx env'.
    apply Pos.le_trans with (2:=IH _ _).
    apply pos_le_plus1.
  Qed.

  Lemma fst_fold_left_make_omap2:
    forall xs fidx env,
      fst (fold_left make_omap xs (fidx, env)) <= fidx + Pos.of_nat (length xs).
  Proof.
    setoid_rewrite fst_fold_left_make_omap.
    destruct xs; auto using pos_le_plus1.
    intros. reflexivity.
  Qed.

  Lemma find_fold_left_make_omap:
    forall x i xs fidx env,
      Env.find x (snd (fold_left make_omap xs (fidx, env))) = Some (Vidx i) ->
      fidx <= i < fst (fold_left make_omap xs (fidx, env))
      \/ Env.find x env = Some (Vidx i).
  Proof.
    induction xs as [|z xs IH]. now inversion_clear 1; auto.
    destruct z as (z & (zty & zck)).
    simpl.
    intros fidx env' Hfind.
    apply IH in Hfind.
    destruct Hfind as [Hf|Hf].
    - left. destruct Hf as (Hf1 & Hf2).
      split; auto.
      apply Pos.le_trans with (2:=Hf1).
      apply pos_le_plus1.
    - destruct (ident_eq_dec x z).
      2:now rewrite Env.gso in Hf; auto.
      subst. rewrite Env.gss in Hf. inv Hf.
      left. split; auto using Pos.le_refl.
      rewrite fst_fold_left_make_omap.
      destruct xs; auto using pos_lt_plus1.
      apply Pos.lt_trans with (1:=pos_lt_plus1 _).
      apply Pos.lt_add_diag_r.
  Qed.

  Lemma make_imap_nil:
    forall xs env,
      make_imap env xs [] = env.
  Proof.
    destruct xs; try destruct p; simpl; auto.
  Qed.

  Lemma make_imap_app:
    forall anns' anns args env,
      make_imap env args (anns ++ anns')
      = make_imap (make_imap env (firstn (length anns) args) anns)
                  (skipn (length anns) args) anns'.
  Proof.
    induction anns as [|ann anns IH]; auto.
    intros args env'.
    destruct args; simpl; auto.
    repeat match goal with
           | p:(ident * (type * clock))%type |- _ => destruct p
           | p:(type * nclock)%type |- _ => destruct p
           | n:(nclock)%type |- _ => destruct n
           | ann:(type * nclock * astloc)%type |- _ => destruct ann
           end; rewrite IH; auto.
  Qed.

  Lemma nclockof_lnannot:
    forall els,
      nclockof (fst els) = map (fun x=>snd (fst x)) (lnannot els).
  Proof.
    destruct els as (e & loc).
    induction e; try destruct a; simpl; try rewrite map_map; auto.
    - destruct l0; rewrite map_map; auto.
    - destruct l1; rewrite map_map; auto.
    - destruct l1; rewrite map_map; auto.
  Qed.

  Lemma find_make_imap_Is_index_in_nclocks:
    forall (P: positive -> Prop) els args,
      NoDupMembers args ->
      Forall (fun el => forall i,
                  Is_index_in_nclocks i (nclockof (fst el)) -> P i) els ->
      forall x i,
        Env.find x (make_imap (Env.empty ckid) args (lnannots els)) = Some (Vidx i) ->
        P i.
  Proof.
    intros P els args Hndup Hfx x i Hfind.
    pose proof (proj1 (@Env.Props.P.F.empty_in_iff ckid x)) as Hni.
    revert Hfx x i args Hndup Hfind Hni.
    generalize (Env.empty ckid).
    induction els as [|el els IH]; intros env' Hfa x i args Hndup Hfind Hni.
    - rewrite make_imap_nil in Hfind.
      exfalso; apply Hni.
      apply Env.find_In with (1:=Hfind).
    - rewrite lnannots_cons, make_imap_app in Hfind.
      inversion_clear Hfa as [|? ? Hii Hfa'].
      pose proof (Env.find_In _ _ _ Hfind) as Hin.
      apply map_imap_InMembers in Hin.
      destruct Hin as [Hin|Hin].
      + apply IH in Hfind; auto using NoDupMembers_skipn.
        intro HH. apply map_imap_InMembers in HH.
        destruct HH as [HH|HH]; auto.
        apply InMembers_skipn_firstn with (1:=Hin) (2:=Hndup) (3:=HH).
      + apply map_imap_InMembers in Hin.
        destruct Hin as [Hin|]; [|contradiction].
        rewrite find_make_imap_not_in_members in Hfind;
          auto using InMembers_firstn_skipn.
        apply Hii.
        clear IH Hfa' Hii.
        rewrite nclockof_lnannot.
        revert Hfind Hin.
        match goal with |- context [firstn ?na args] =>
          apply NoDupMembers_firstn with (n:=na) in Hndup;
            revert Hndup; generalize (firstn na args); clear args end.
        revert env' Hni.
        induction (lnannot el) as [|ann anns IH];
          intros env' Hni args Hnd Hfind Him.
        now destruct args; apply Env.find_In in Hfind; try destruct p.
        destruct args; [now apply Env.find_In in Hfind|].
        destruct p as (z, (zty, zck)).
        destruct ann as ((aty, nck), aloc).
        inversion_clear Hnd. inversion_clear Him as [He|Hm].
        * subst. simpl in Hfind.
          destruct nck.
          apply IH in Hfind; eauto using Exists_cons_tl with lclocking.
          rewrite find_make_imap_not_in_members in Hfind; auto.
          now apply Env.find_In in Hfind.
          rewrite find_make_imap_not_in_members in Hfind; auto.
          rewrite Env.gss in Hfind.
          inv Hfind; repeat constructor.
        * destruct nck. simpl in Hfind.
          apply IH in Hfind; eauto using Exists_cons_tl with lclocking.
          simpl in Hfind. rewrite find_make_imap_add in Hfind;
                            eauto using InMembers_neq.
          apply IH in Hfind; eauto using Exists_cons_tl with lclocking.
  Qed.

  Lemma calculate_base_clock_nil:
    forall iface,
      calculate_base_clock iface [] = Sbase.
  Proof.
    destruct iface; simpl; repeat destruct p; auto.
  Qed.

  Lemma Is_index_in_calculate_base_clock:
    forall (P: positive -> Prop) els args,
      Forall (fun el => forall i,
                  Is_index_in_nclocks i (nclockof (fst el)) -> P i) els ->
      forall i, Is_index_in_sclock i (calculate_base_clock args (lnannots els))
                -> P i.
  Proof.
    intro P. induction els as [|el els IH].
    now intros ??? Hii; rewrite calculate_base_clock_nil in Hii;
      inversion Hii.
    intros args Hfa i Hii.
    inversion_clear Hfa as [|? ? Hfa1 Hfa2].
    rewrite lnannots_cons in Hii.
    rewrite nclockof_lnannot in Hfa1.
    destruct (lnannot el) as [|ann anns].
    now apply IH with (1:=Hfa2) (2:=Hii).
    destruct args as [|arg args]. now inversion Hii.
    destruct arg as (z, (zty, zck)).
    destruct ann as ((ty, nck), loc).
    simpl in Hii.
    apply Hfa1.
    constructor; simpl.
    clear IH Hfa1 Hfa2 anns loc ty z zty args el els P.
    destruct nck as [sck|? sck]; constructor; simpl in Hii.
    - revert zck Hii.
      induction sck; intros zck Hii.
      now destruct zck; simpl in Hii; inversion Hii.
      destruct zck; eauto.
      apply IHsck in Hii.
      inversion Hii; eauto using Is_index_in_sclock.
    - revert zck Hii.
      induction sck; intros zck Hii.
      now destruct zck; simpl in Hii; inversion Hii.
      destruct zck; eauto.
      apply IHsck in Hii.
      inversion Hii; eauto using Is_index_in_sclock.
  Qed.

  (* TODO: Is there a smarter way to do this?
           Some kind of recursive tactic with backtracking?
           Or an existing tactic? *)
  Local Ltac solve_trans :=
    repeat progress match goal with
                    | |- ?w <= ?x <= ?z => split
                    | |- ?w <  ?x <= ?z => split
                    | |- ?w <= ?x <  ?z => split
                    | |- ?w <  ?x <  ?z => split
                    | H: ?w <= ?x <= ?z |- _ => destruct H
                    | H: ?w <  ?x <= ?z |- _ => destruct H
                    | H: ?w <= ?x <  ?z |- _ => destruct H
                    | H: ?w <  ?x <  ?z |- _ => destruct H
                    | Hwx: ?w <= ?x, Hxz: ?x <= ?z |- ?w <= ?z =>
                      apply Pos.le_trans with (1:=Hwx) (2:=Hxz)
                    | Hwx: ?w < ?x, Hxz: ?x <= ?z |- ?w < ?z =>
                      apply Pos.lt_le_trans with (1:=Hwx) (2:=Hxz)
                    | Hwx: ?w <= ?x, Hxz: ?x < ?z |- ?w < ?z =>
                      apply Pos.le_lt_trans with (1:=Hwx) (2:=Hxz)
                    | Hwx: ?w < ?x, Hxz: ?x < ?z |- ?w < ?z =>
                      apply Pos.lt_trans with (1:=Hwx) (2:=Hxz)
                    | Hwx: ?w <= ?x, Hxy: ?x <= ?y, Hyz: ?y <= ?z |- ?w <= ?z =>
                      apply Pos.le_trans with (1:=Pos.le_trans _ _ _ Hwx Hxy) (2:=Hyz)
                    | Hwx: ?w < ?x, Hxy: ?x <= ?y, Hyz: ?y <= ?z |- ?w < ?z =>
                      apply Pos.lt_le_trans with (1:=Hwx) (2:=Pos.le_trans _ _ _ Hxy Hyz)
                    | Hwx: ?w <= ?x, Hxy: ?x < ?y, Hyz: ?y <= ?z |- ?w < ?z =>
                      apply Pos.le_lt_trans with (1:=Hwx) (2:=Pos.lt_le_trans _ _ _ Hxy Hyz)
                    | Hwx: ?w <= ?x, Hxy: ?x <= ?y, Hyz: ?y < ?z |- ?w < ?z =>
                      apply Pos.le_lt_trans with (1:=Hwx) (2:=Pos.le_lt_trans _ _ _ Hxy Hyz)
                    | _ => auto
                    end.

  (* TODO: assert within elab_exp'_indexes? *)
  Lemma mmaps_Is_index_in_nclocks:
    forall (f: positive -> expression -> res (positive * (exp * astloc))) es els s s',
      mmaps f s es = OK (s', els) ->
      (forall e el s s',
          In e es ->
          f s e = OK (s', el) ->
          (forall i, Is_index_in_nclocks i (nclockof (fst el)) -> s <= i < s') /\ s <= s') ->
      Forall (fun el => forall i, Is_index_in_nclocks i (nclockof (fst el)) -> s <= i < s') els
      /\ s <= s'.
  Proof.
    intros * Hmm Hfa.
    eapply mmaps_spec
    with (P:=fun s s' el =>
               forall i, Is_index_in_nclocks i (nclockof (fst el)) -> s <= i < s')
         (R:=Pos.le) (I:=fun _ => True) (IS:=fun _ => True) in Hmm; auto.
    - destruct Hmm as (Hels & Hss & ?).
      split; auto.
    - intuition.
    - intuition.
    - intros * Hi; split; intros ??? Hii; apply Hi in Hii; solve_trans.
    - intros e el t t' Hin ? Hf.
      specialize (Hfa e el t t' Hin Hf).
      destruct Hfa; auto.
  Qed.

  Lemma Name_only_core_approx_clock:
    forall bck sub ck,
      Name_only_core_sclock bck ->
      Name_only_core_sclock (approx_clock bck sub ck).
  Proof.
    induction ck; simpl.
    now intros; subst; auto with name_only_sclock.
    intros Hno.
    destruct (Env.find i sub) as [x|];
      try destruct (Env.find x env);
        try destruct p; subst;
          auto with name_only_sclock.
  Qed.

  Lemma Name_only_core_approx_base_clock:
    forall scks iface,
      Forall Name_only_core_sclock scks ->
      Name_only_core_sclock (approx_base_clock scks iface).
  Proof.
    destruct scks as [|sck scks].
    now auto with name_only_sclock.
    destruct iface as [|xtc iface].
    now auto with name_only_sclock.
    inversion_clear 1 as [|? ? Hno Hfa].
    destruct xtc as (x, (ty, ck)).
    simpl. clear scks Hfa. revert sck Hno.
    induction ck; auto with name_only_sclock.
    intros sck Hno.
    destruct sck; auto.
    inversion_clear Hno as [? Hno'|];
      try inversion_clear Hno';
      apply IHck; auto with name_only_sclock.
  Qed.

  Lemma Not_Is_index_in_nclocks_build_whens:
    forall loc tys sck e,
      (forall i, ~Is_index_in_nclocks i (nclockof e)) ->
      Name_only_core_sclock sck ->
      forall i, ~Is_index_in_nclocks i (nclockof (build_whens loc e tys sck)).
  Proof.
    induction sck; simpl; auto.
    match goal with |- context [Son ?scks ?c ?b] => destruct c end;
      intros e Hni Hno.
    - inversion_clear Hno as [? Hno'|]; auto.
      now inversion Hno'.
    - inversion_clear Hno as [? Hno'|].
      simpl. intros j Hij.
      apply Exists_exists in Hij.
      destruct Hij as (nck & Hin & Hij).
      apply in_map_iff in Hin.
      destruct Hin as (ty & Hnck & Hin).
      subst. inversion_clear Hij as [? Hsj| |].
      apply No_index_in_Name_only_sclock with (j:=j) in Hno'.
      contradiction.
  Qed.

  Lemma Is_index_in_nclocks_trans:
    forall {A: Type} s s' e,
        (forall i, Is_index_in_nclocks i (nclockof e) -> s <= i < s') ->
        (forall r : A * positive,
            snd r <= s ->
            forall i, Is_index_in_nclocks i (nclockof e) -> snd r <= i < s')
        /\ (forall t : A * positive,
               s' <= snd t ->
               forall i, Is_index_in_nclocks i (nclockof e) -> s <= i < snd t).
  Proof.
    intros * Hii; split.
    - intros t Hts i Hi.
      apply Hii in Hi.
      destruct Hi as (Hsi & His').
      split; auto.
      apply Pos.le_trans with (1:=Hts) (2:=Hsi).
    - intros t Hs't' i Hi.
      apply Hii in Hi.
      destruct Hi as (Hsi & His').
      split; auto.
      apply Pos.lt_le_trans with (1:=His') (2:=Hs't').
  Qed.

  Lemma elab_exp'_indexes:
    forall ae e scks s s' loc,
      Forall Name_only_core_sclock scks ->
      elab_exp' scks s ae = OK (s', (e, loc)) ->
      (forall i, Is_index_in_nclocks i (nclockof e) -> s <= i < s') /\ s <= s'.
  Proof.
    induction ae using expression_ind2; simpl; intros ?????? Hmm;
      NamedDestructCases; try monadInv2 Hmm;
        repeat progress match goal with
        | H: Forall _ [?e] |- _ => inv H
        | H1: context [elab_exp' _ _ _ = OK _],
          H2: elab_exp' _ _ _ = OK _ |- wt_exp _ _ _  =>
          apply H1 in H2; clear H1; auto
        | H:find_type_unop _ _ _ = OK _ |- _ =>
          unfold find_type_unop in H;
          rewrite type_unop'_correct in H; NamedDestructCases
        | H:find_type_binop _ _ _ _ = OK _ |- _ =>
          unfold find_type_binop in H;
          rewrite type_binop'_correct in H; NamedDestructCases
        | H:assert_sclock _ _ _ = OK _ |- _ => apply assert_sclock_spec in H
        | H: _ = OK _ |- _ => monadInv2 H
        | H: single_annot _ _ = OK _ |- _ =>
          apply single_annot_spec in H; destruct H
        | H:assert_paired_types _ _ _ _ _ = OK _ |- _ =>
          apply assert_paired_types_spec_clocks in H; destruct H
        | H:assert_paired_clock_types _ _ _ = OK _ |- _ =>
          apply assert_paired_clock_types_spec_clocks in H; destruct H
        | H:Forall _ [] |- _ => clear H
        end; subst; simpl.
    - (* Eunop *)
      repeat match goal with
             | Helab:elab_exp' _ _ _ = OK _,
               Hfa:context [elab_exp' _ _ _ = OK _] |- _ =>
               apply Hfa in Helab; destruct Helab
             | |- _ /\ s <= s' =>
               split; auto; simpl; intros
             | H:clockof ?ck = _ |- _ =>
               destruct (clockof ck) as [|x xs] eqn:Hclockof;
                 try destruct xs; try discriminate; inv H
             | H: forall i, Is_index_in_nclocks _ _ -> _ |- _ => apply H
             | H:clockof ?e = [?sclk] |- Is_index_in_nclocks ?i (nclockof ?e) =>
               apply Is_index_in_nclocks_Cstream; now rewrite Hclockof
             end; auto.
    - (* Ebinop *)
      repeat match goal with
             | Helab:elab_exp' _ _ _ = OK _,
               Hfa:context [elab_exp' _ _ _ = OK _] |- _ =>
               apply Hfa in Helab; destruct Helab
             | H1:s <= ?x, H2: ?x <= s' |- _ /\ s <= s' =>
               split; [subst; simpl; intros|now solve_trans]
             | H:clockof ?ck = _, Hty:typeof ?ck = _ |- _ =>
               let xs := fresh "xs" in
               let Hckof := fresh "Hckof" in
               destruct (clockof ck) as [|? xs] eqn:Hckof;
                 try destruct xs; try discriminate; inv H;
                 rewrite clockof_nclockof in Hckof; clear Hty
             | H: forall i, Is_index_in_nclocks _ _ -> _,
               Hii:Is_index_in_nclocks _ _ |- _ => apply H in Hii
             | Hii:Is_index_in_nclocks ?i [Cstream ?sck],
               Hms:map stripname (nclockof ?e) = [?sck] |- _ =>
               apply Is_index_in_nclocks_stripname_nclockof with (1:=Hii) in Hms
             | _ => now solve_trans
             end.
    - (* Eite *)
      match goal with Helab :elab_exp' _ _ _ = OK _, HH: _ |- _ =>
        apply HH in Helab; destruct Helab end; auto.
      match goal with H: mmaps _ _ ets = OK _ |- _ =>
        apply mmaps_Is_index_in_nclocks in H; destruct H end;
      match goal with H: mmaps _ _ efs = OK _ |- _ =>
        apply mmaps_Is_index_in_nclocks in H; destruct H end;
      intros;
      try match goal with
            Hin:In ?e ?es, Helab:elab_exp' _ _ ?e = OK (_, ?el),
            Hfa:Forall _ ?es |- _ => apply Forall_forall with (1:=Hfa) in Hin;
                                       destruct el; now apply Hin in Helab end.
      split; solve_trans.
      intros.
      match goal with H:Is_index_in_nclocks _ _ |- _ =>
        apply Exists_exists in H; destruct H as (nck & Hin & Hii) end.
      unfold lannots_ty in Hin.
      rewrite map_map in Hin.
      apply in_map_iff in Hin.
      destruct Hin as (((ty, sclk), aloc) & Hnck & Hin).
      subst.
      repeat match goal with
             | Hin:In _ (lannots ?els), Hfa:Forall _ (lannots ?els) |- _ =>
               apply Forall_forall with (2:=Hin) in Hfa; subst; simpl
             | H:clockof ?ck = _, Hty:typeof ?ck = _ |- _ =>
               let xs := fresh "xs" in
               let Hckof := fresh "Hckof" in
               destruct (clockof ck) as [|? xs] eqn:Hckof;
                 try destruct xs; try discriminate; inv H;
                 rewrite clockof_nclockof in Hckof; clear Hty
             | H: forall i, Is_index_in_nclocks _ _ -> _,
               Hii:Is_index_in_nclocks _ _ |- _ => apply H in Hii
             | Hii:Is_index_in_nclocks ?i [Cstream ?sck],
               Hms:map stripname (nclockof ?e) = [?sck] |- _ =>
               apply Is_index_in_clocks_stripname_nclockof with (1:=Hii) in Hms
             | Hfa:forall i, _ -> s <= i < _ |- _ =>
               apply Is_index_in_nclock_stripname_nclockof with (1:=Hii) in Hckof;
                 apply Hfa in Hckof; solve_trans
             end.
    - (* Eunop CastOp *)
      repeat match goal with
             | H:Forall _ [_] |- _ => inv H
             | H:single_annot _ _ = OK _ |- _ =>
               apply single_annot_spec in H; destruct H
             | Helab:elab_exp' _ _ _ = OK _,
               Hfa:context [elab_exp' _ _ _ = OK _] |- _ =>
               apply Hfa in Helab; destruct Helab
             | |- _ /\ _ => split; [simpl; intros|now auto]
             | H:clockof ?ck = _ |- _ =>
               destruct (clockof ck) as [|x xs] eqn:Hclockof;
                 try destruct xs; try discriminate; inv H
             | H: forall i, Is_index_in_nclocks _ _ -> _ |- _ => apply H
             end; auto.
      apply Is_index_in_nclocks_Cstream.
      now rewrite Hclockof.
    - (* Eapp *)
      setoid_rewrite surjective_pairing in EQ3.
      simpl in EQ3. monadInv EQ3.
      apply mmaps_spec
      with (P:=fun s s' el =>
                 forall i, Is_index_in_nclocks i (nclockof (fst el)) ->
                           snd s <= i < snd s')
           (R:=fun s s'=> snd s <= snd s')
           (I:=fun _ => True) (IS:=fun s => Forall Name_only_core_sclock (fst s))
        in EQ0; auto.
      + simpl in *.
        destruct EQ0 as (Hfa & Hle & ? & ?).
        split.
        2:now apply Pos.le_trans with (1:=Hle) (2:=fst_fold_left_make_omap1 _ _ _).
        match goal with H: s <= snd ?t |- _ => destruct t as (sclk, fidx) end.
        match goal with H:mmap (inst_annot _ _ (snd _)) _ = OK _ |- _ =>
          rename H into Hfao end.
        apply mmap_inversion in Hfao.
        apply list_forall2_Forall2 in Hfao.
        unfold find_node_interface in *. NamedDestructCases.
        apply wt_nenv in Heq. destruct Heq as (n & Hfind & Hnin & Hnout).
        apply Forall2_eq in Hnin. apply Forall2_eq in Hnout. subst.
        pose proof (find_make_imap_Is_index_in_nclocks
                      _ _ _ (NoDupMembers_app_l _ _ (n.(n_nodup))) Hfa) as Himap.
        pose proof (Is_index_in_calculate_base_clock _ _ n.(n_in) Hfa) as Hcalcb.
        intros i Hii.
        apply Exists_exists in Hii.
        destruct Hii as (nck' & Hin & Hii).
        apply in_map_iff in Hin.
        destruct Hin as ((ty, nck) & Hnck & Hin).
        simpl in Hnck; subst.
        apply Forall2_in_right with (2:=Hin) in Hfao.
        destruct Hfao as ((z, (zty, zck)) & Hzin & Hinst).
        simpl in Hinst; monadInv Hinst.
        assert (forall i, Is_index_in_sclock i x -> s <= i < fidx + Pos.of_nat (length n.(n_out))).
        { clear i Hii Hzin EQ0.
          intros i Hii. revert x i Hii EQ.
          induction zck; simpl.
          - intros. monadInv EQ.
            apply Hcalcb in Hii. simpl in Hii; destruct Hii.
            split; auto; intros.
            match goal with H:i<fidx |- _ => apply Pos.lt_trans with (1:=H) end.
            apply Pos.lt_add_r.
          - intros sck j Hij Hm.
            monadInv Hm. NamedDestructCases. inv Hij.
            2:now eapply IHzck in EQ; eauto.
            apply find_fold_left_make_omap in Heq.
            destruct Heq as [Heq|Heq].
            + destruct Heq as (Heq1 & Heq2).
              split. now apply Pos.le_trans with (1:=Hle) (2:=Heq1).
              rewrite fst_fold_left_make_omap in Heq2.
              destruct n.(n_out); auto.
              apply Pos.lt_trans with (1:=Heq2). apply Pos.lt_add_r.
            + apply Himap in Heq. destruct Heq as (Heq1 & Heq2).
              split; auto.
              apply Pos.lt_trans with (1:=Heq2). apply Pos.lt_add_r.
        }
        NamedDestructCases; intros; subst; inv Hii.
        * rewrite fst_fold_left_make_omap.
          apply find_fold_left_make_omap in Heq.
          rewrite fst_fold_left_make_omap in Heq.
          destruct Heq as [Heq|Heq].
          now destruct Heq as (Heq1 & Heq2); auto using (Pos.le_trans _ _ _ Hle Heq1).
          apply Himap in Heq; destruct Heq as (Heq1 & Heq2).
          split; auto. destruct n.(n_out); auto.
          apply (Pos.lt_trans _ _ _ Heq2). apply Pos.lt_add_r.
        * rewrite fst_fold_left_make_omap.
          destruct n.(n_out); [now inv Hzin|now auto].
        * rewrite fst_fold_left_make_omap.
          destruct n.(n_out); [now inv Hzin|now auto].
      + intuition.
      + intros a b c Hab Hbc.
        apply Pos.le_trans with (1:=Hab) (2:=Hbc).
      + apply Forall_forall.
        simpl. intros sck Hin.
        apply in_map_iff in Hin.
        destruct Hin as ((z, (zty, zck)) & Hac & Hin).
        subst. apply Name_only_core_approx_clock.
        now apply Name_only_core_approx_base_clock.
      + intros; apply Is_index_in_nclocks_trans; auto.
      + intros ae (e, eloc) (?, fidx) (?, fidx') Hin Hfa Helab.
        simpl in Helab. monadInv2 Helab.
        match goal with Helab:elab_exp' _ _ _ = OK _ |- _ =>
          apply Forall_forall with (1:=H) (2:=Hin) in Helab; destruct Helab end; auto.
        repeat (split; auto).
        now apply Forall_skipn.
    - (* Econst *)
      intros Hw Hss. subst.
      split; auto using Pos.le_refl.
      intros i Hii.
      unfold add_whens in Hii.
      destruct (do_add_when_to_constants tt).
      + destruct scks; simpl in Hii.
        * inversion Hii as [? ? Hii'|? ? Hex]; [|inversion Hex].
          inversion_clear Hii' as [? Hii''| |].
          inversion_clear Hii''.
        * inversion_clear H as [|? ? Hno Hfa].
          apply Not_Is_index_in_nclocks_build_whens with (2:=Hno) in Hii.
          contradiction.
          intros j Hij.
          inversion_clear Hij as [? ? Hij'|? ? Hex]; [|inversion Hex].
          inversion_clear Hij' as [? Hij''| |].
          inversion_clear Hij''.
      + inversion Hii as [? ? Hii'|? ? Hex].
        2:now inversion Hex.
        inversion_clear Hii' as [? Hii''| |].
        inversion_clear Hii''.
    - (* Evar *)
      split; auto using Pos.le_refl.
      simpl. inversion_clear 1 as [? ? Hii|? ? Hii]; inv Hii.
      match goal with H:Is_index_in_sclock _ (sclk _) |- _ =>
        now apply not_Is_index_in_sclk in H end.
    - (* Efby *)
      match goal with H: mmaps _ _ e0s = OK _ |- _ =>
        apply mmaps_Is_index_in_nclocks in H; destruct H end;
      match goal with H: mmaps _ _ es = OK _ |- _ =>
        apply mmaps_Is_index_in_nclocks in H; destruct H end;
      intros;
      try match goal with
            Hin:In ?e ?es, Helab:elab_exp' _ _ ?e = OK (_, ?el),
            Hfa:Forall _ ?es |- _ => apply Forall_forall with (1:=Hfa) in Hin;
                                       destruct el; now apply Hin in Helab end.
      split; solve_trans.
      intros i Hii.
      rewrite map_snd_discardname_clocks in Hii.
      match goal with H:Is_index_in_nclocks _ _ |- _ =>
        apply Exists_exists in H; destruct H as (nck & Hin & Hii) end.
      apply in_map_iff in Hin.
      destruct Hin as (sck & Hnck & Hin); subst.
      rewrite clocksof_nclocksof in Hin. apply in_map_iff in Hin.
      destruct Hin as (nck & Hsck & Hin); subst.
      match goal with Hin:In nck (nclocksof (map fst ?els)),
                      H:Forall _ ?els |- _ => rename H into Hfa end.
      rewrite <-(Forall_map (fun e => forall i,
                    Is_index_in_nclocks i (nclockof e) -> s <= i < _) _ _) in Hfa.
      apply In_nclocksof in Hin.
      destruct Hin as (e & Hin1 & Hin2).
      apply Forall_forall with (1:=Hfa) in Hin1.
      cut (s <= i < x). now intro; solve_trans.
      apply Hin1. apply Exists_exists.
      inversion_clear Hii as [? Hii'| |].
      exists nck; split; auto.
      destruct nck; eauto using Is_index_in_nclock.
    - (* Ewhen *)
      split; auto using Pos.le_refl.
      simpl; intros * Hii.
      apply Exists_exists in Hii.
      destruct Hii as (nclk & Hin & Hii).
      rewrite in_map_iff in Hin.
      destruct Hin as (ty & Hnclk & Hin).
      subst. inversion_clear Hii as [? Hiis| |].
      inversion_clear Hiis as [|? ? ? Hii].
      now apply not_Is_index_in_sclk in Hii.
    - (* Emerge *)
      match goal with H: mmaps _ _ ets = OK _ |- _ =>
        apply mmaps_Is_index_in_nclocks in H; destruct H end;
      match goal with H: mmaps _ _ efs = OK _ |- _ =>
        apply mmaps_Is_index_in_nclocks in H; destruct H end;
      intros;
      try match goal with
            Hin:In ?e ?es, Helab:elab_exp' _ _ ?e = OK (_, ?el),
            Hfa:Forall _ ?es |- _ => apply Forall_forall with (1:=Hfa) in Hin;
              destruct el; apply Hin in Helab; auto with name_only_sclock
          end.
      split; solve_trans.
      intros.
      match goal with H:Is_index_in_nclocks _ _ |- _ =>
        apply Exists_exists in H; destruct H as (nck & Hin & Hii) end.
      unfold lannots_ty in Hin.
      rewrite map_map in Hin.
      apply in_map_iff in Hin.
      destruct Hin as (((ty, sclk), aloc) & Hnck & Hin).
      subst.
      inversion_clear Hii as [? Hiis| |].
      now apply not_Is_index_in_sclk in Hiis.
  Qed.

  Lemma mmaps_elab_arg_DisjointIndexes:
    forall aes els lcks fidx lcks' fidx',
      Forall Name_only_core_sclock lcks ->
      mmaps (elab_arg elab_exp') (lcks, fidx) aes = OK ((lcks', fidx'), els) ->
      DisjointIndexes (map nclockof (map fst els)).
  Proof.
    intros * Hno Hmm.
    apply mmaps_spec
    with (P:=fun s s' el =>
               forall i, Is_index_in_nclocks i (nclockof (fst el)) ->
                         snd s <= i < snd s')
         (R:=fun s s'=> snd s <= snd s')
         (I:=fun els => DisjointIndexes (map nclockof (map fst els)))
         (IS:=fun s => Forall Name_only_core_sclock (fst s))
      in Hmm; auto.
    - intuition.
    - intuition.
    - intros w x y Hwx Hxy. solve_trans.
    - constructor.
    - intros; apply Is_index_in_nclocks_trans; auto.
    - clear lcks fidx lcks' fidx' Hno Hmm.
      intros ae (e, eloc) (?, fidx) (?, fidx') Hin Hfa Helab.
      simpl in Helab. monadInv2 Helab.
      match goal with Helab:elab_exp' _ _ _ = OK _ |- _ =>
        apply elab_exp'_indexes with (1:=Hfa) in Helab; destruct Helab end.
      repeat (split; auto).
      now apply Forall_skipn.
    - clear els lcks fidx lcks' fidx' Hno Hmm.
      intros (e, eloc) els (?, s0) (?, s1) (?, s2) Hinv Hfa Hs01 Hs12 Hfresh.
      simpl. constructor; auto.
      intros i Hii.
      apply Hinv in Hii. destruct Hii as (Hs0i & His1).
      simpl in *. repeat rewrite Forall_map.
      apply Forall_impl_In with (2:=Hfa).
      intros (e', loc) Hin Hii HH.
      apply Hii in HH. destruct HH as (Hs1i & Hsi2).
      apply Pos.lt_le_trans with (1:=His1) in Hs1i.
      now apply Pos.lt_irrefl in Hs1i.
  Qed.

  Lemma inst_clock_sinst:
    forall loc bck subst ck sck,
      inst_clock loc bck subst ck = OK sck ->
      sinst bck (fun x => Env.find x subst) ck = Some sck.
  Proof.
    induction ck; simpl. now inversion 1.
    intros sck Hmm.
    monadInv Hmm.
    apply IHck in EQ. rewrite EQ.
    destruct (Env.find i subst). 2:now monadInv EQ0.
    now inversion EQ0.
  Qed.

  Lemma inst_annot_inst_in:
    forall loc bck subst xtc ty nck,
      inst_annot loc bck subst xtc = OK (ty, nck) ->
      inst_in bck subst xtc = Some nck.
  Proof.
    intros loc bck subst (x, (ty, ck)) ty' nck.
    simpl. intro Hmm. monadInv Hmm.
    apply inst_clock_sinst in EQ. rewrite EQ.
    destruct (Env.find x subst); now inversion EQ0.
  Qed.

  (* [make_omap'] is a version of [make_omap] that does not wrap its result
     with [Vidx]. It and associated lemmas are only used in the proof of
     [wc_elab_exp']. They provide a witness for application clocking. *)

  Definition make_omap' (st: positive * Env.t positive)
                        (out: ident * (type * clock)) : positive * Env.t positive :=
    let (i, s) := st in
    (i + 1, Env.add (fst out) i s)%positive.

  Lemma find_make_omap'_not_in_members:
    forall xs s x,
      ~InMembers x xs ->
      Env.find x (snd (fold_left make_omap' xs s)) = Env.find x (snd s).
  Proof.
    induction xs as [|(x, v) xs IH].
    now simpl; auto.
    intros * Hnim.
    apply NotInMembers_cons in Hnim.
    destruct Hnim as [Hnim Hnx].
    simpl.
    rewrite IH; auto.
    destruct s as (fidx, s).
    simpl. now rewrite Env.gso; auto.
  Qed.

  Lemma find_make_omap'_add:
    forall x xs y v idx s,
      x <> y ->
      Env.find x (snd (fold_left make_omap' xs (idx, Env.add y v s)))
      = Env.find x (snd (fold_left make_omap' xs (idx, s))).
  Proof.
    induction xs as [|(w, (wt, wc)) xs IH].
    now simpl; intros; rewrite Env.gso; auto.
    intros * Hnxy.
    destruct (ident_eq_dec w y).
    - subst. simpl. now repeat rewrite IH; auto.
    - simpl. rewrite Env.add_comm; auto.
  Qed.

  Lemma InMembers_find_make_omap':
    forall xs idx s x,
      InMembers x xs ->
      Env.find x (snd (fold_left make_omap' xs (idx, s)))
      = Env.find x (snd (fold_left make_omap' xs (idx, Env.empty positive))).
  Proof.
    induction xs as [|(x, xty) xs IH]. now inversion 1.
    simpl.
    intros idx s y HH.
    destruct HH as [Heq|Him].
    2:now setoid_rewrite IH; auto.
    subst. destruct (InMembers_dec y xs ident_eq_dec) as [Him|Hnim].
    now setoid_rewrite IH; auto.
    setoid_rewrite find_make_omap'_not_in_members; auto.
    now simpl; setoid_rewrite Env.gss.
  Qed.

  Lemma InMembers_find_make_omap'_exists:
    forall xs s x,
      InMembers x xs ->
      exists i, Env.find x (snd (fold_left make_omap' xs s)) = Some i.
  Proof.
    intros xs (idx, s) x Hin.
    apply or_introl with (B:=exists i, Env.find x s = Some i) in Hin.
    revert s idx x Hin.
    induction xs as [|(x, xty) xs IH]. now inversion 1.
    intros s idx y HH.
    repeat destruct HH as [HH|HH]; apply IH; auto.
    - right. exists idx. subst. now rewrite Env.gss.
    - right. destruct (ident_eq_dec y x).
      + subst. exists idx. now rewrite Env.gss.
      + rewrite Env.gso; auto.
  Qed.

  Lemma find_make_omap'_omap:
    forall x nout isub fidx,
      (match Env.find x (snd (fold_left make_omap' nout (fidx, Env.empty positive))) with
       | Some i => Some (Vidx i)
       | None => Env.find x isub
       end) = Env.find x (snd (fold_left make_omap nout (fidx, isub))).
  Proof.
    induction nout as [|(z, (zty, zck)) nout IH].
    simpl.
    now simpl; rewrite Env.gempty.
    intros isub fidx.
    simpl. rewrite <-IH. clear IH.
    destruct (InMembers_dec x nout ident_eq_dec) as [Him|Hnim].
    - rewrite InMembers_find_make_omap'; auto.
      eapply InMembers_find_make_omap'_exists in Him.
      destruct Him as (i & Him).
      now rewrite Him.
    - setoid_rewrite find_make_omap'_not_in_members; auto.
      simpl. rewrite Env.gempty.
      destruct (ident_eq_dec x z) as [He|Hne].
      now subst; setoid_rewrite Env.gss.
      setoid_rewrite Env.gso; auto.
      now rewrite Env.gempty.
  Qed.

  Lemma inst_annot_inst_out:
    forall loc bck nout isub fidx xtc ty nck,
      inst_annot loc bck (snd (fold_left make_omap nout (fidx, isub))) xtc
                                                              = OK (ty, nck) ->
      inst_out bck (snd (fold_left make_omap' nout (fidx, Env.empty positive)))
                                                            isub xtc = Some nck.
  Proof.
    intros loc bck nout isub fidx (x, (ty, ck)) ty' nck.
    simpl. intro Hmm. monadInv Hmm.
    apply inst_clock_sinst in EQ.
    rewrite find_make_omap'_omap.
    NamedDestructCases; intros; subst.
    - erewrite sinst_extarg.
      2:now intro; eapply find_make_omap'_omap.
      now rewrite EQ.
    - erewrite sinst_extarg.
      2:now intro; eapply find_make_omap'_omap.
      now rewrite EQ.
  Qed.

  Lemma inst_annot_type:
    forall loc bck subst x xty xck ty nck,
      inst_annot loc bck subst (x, (xty, xck)) = OK (ty, nck) ->
      ty = xty.
  Proof.
    intros * Hia. monadInv Hia.
    destruct (Env.find x subst); now monadInv EQ0.
  Qed.

  Lemma inst_annot_make_imap:
    forall loc bck iface anns x xty xck ty nck,
      inst_annot loc bck (make_imap (Env.empty ckid) iface anns) (x, (xty, xck))
                                                         = OK (ty, nck) ->
      match Env.find x (make_imap (Env.empty ckid) iface anns) with
      | None => inst_annot loc bck (make_imap (Env.empty ckid) iface anns)
                          (x, (xty, xck)) = OK (xty, Cstream (stripname nck))
      | Some cid => inst_annot loc bck (make_imap (Env.empty ckid) iface anns)
                          (x, (xty, xck)) = OK (xty, Cnamed cid (stripname nck))
      end.
  Proof.
    simpl. intros * Hmm.
    now destruct (Env.find x (make_imap (Env.empty ckid) iface anns));
      monadInv Hmm; rewrite EQ.
  Qed.

  Lemma In_find_make_imap:
    forall iface args x tc ty nck loc,
      NoDupMembers iface ->
      In ((x, tc), ((ty, nck), loc)) (combine iface args) ->
      nck = match Env.find x (make_imap (Env.empty ckid) iface args) with
            | None => Cstream (stripname nck)
            | Some cid => Cnamed cid (stripname nck)
            end.
  Proof.
    intros * Hnd Hin.
    pose proof (@Env.Props.P.F.empty_in_iff ckid x) as Hni.
    revert args x tc ty nck loc Hnd Hin Hni.
    generalize (Env.empty ckid).
    induction iface as [|xtc iface IH]. contradiction.
    destruct xtc as (x, (xty, xck)).
    intros S args y ytc yty ynck yloc Hnd Hin Hnin.
    destruct args as [|arg args]. contradiction.
    destruct arg as ((ty, nck), loc).
    inversion_clear Hnd as [|? ? ? Hnd1 Hnd2].
    destruct (ident_eq_dec x y) as [Heq|Hne].
    - subst. destruct Hin as [Hin|Hin].
      + inversion_clear Hin. simpl.
        destruct ynck; match goal with |- context [Env.find ?y ?s] =>
                         destruct (Env.find y s) eqn:Heq; auto end;
        rewrite find_make_imap_not_in_members with (1:=Hnd1) in Heq.
        * apply Env.find_In, Hnin in Heq; contradiction.
        * rewrite Env.gss in Heq. inversion_clear Heq; auto.
        * rewrite Env.gss in Heq; discriminate.
      + apply NotInMembers_NotIn with (b:=ytc) in Hnd1.
        apply NotIn_combine with (1:=Hnd1) in Hin.
        contradiction.
    - destruct Hin as [|Hin]. now inv H; contradiction Hne.
      simpl. destruct nck eqn:Hnck; simpl.
      + rewrite (IH S _ _ _ _ _ _ Hnd2 Hin); auto.
        destruct (Env.find y (make_imap S iface args)); auto.
      + rewrite (IH (Env.add x c S) _ _ _ _ _ _ Hnd2 Hin); auto.
        match goal with |- context [Env.find ?y ?s] =>
          destruct (Env.find y s) eqn:Heq; auto end.
        rewrite Env.Props.P.F.add_in_iff. intuition.
  Qed.

  Lemma mmap_inst_annot_NoDup_indexes:
    forall loc bck nout oann fidx env,
      NoDupMembers nout ->
      mmap (inst_annot loc bck (snd (fold_left make_omap nout (fidx, env)))) nout = OK oann ->
      NoDup (indexes (map snd oann)).
  Proof.
    cut (forall loc bck nout oann fidx env,
            NoDupMembers nout ->
            mmap (inst_annot loc bck (snd (fold_left make_omap nout (fidx, env)))) nout = OK oann ->
            NoDup (indexes (map snd oann)) /\ (Forall (fun i=>fidx <= i) (indexes (map snd oann)))).
    now intros * HH loc bck nout oann fidx env' Hnd Hmm;
      specialize (HH _ _ _ _ _ _ Hnd Hmm); destruct HH; auto.
    induction nout as [|(x, (xty, xck)) nout IH].
    now inversion_clear 2; simpl; auto using NoDup_nil.
    intros oann fidx env' Hnd Hmm.
    inversion_clear Hnd as [|? ? ? Hnim Hnd'].
    simpl in Hmm. monadInv Hmm. monadInv EQ. clear EQ0.
    rewrite find_make_omap_not_in_members with (1:=Hnim) in EQ2.
    simpl in EQ2. rewrite Env.gss in EQ2. monadInv EQ2.
    specialize (IH _ _ _ Hnd' EQ1). destruct IH as (IH1 & IH2).
    simpl. split.
    - constructor; auto.
      intro Hin. apply Forall_forall with (1:=IH2) in Hin.
      (* ... there must be a simpler way: *)
      pose proof (pos_le_plus1 fidx) as Hle.
      apply Pos.le_antisym with (1:=Hin) in Hle.
      rewrite Pos.add_1_r in Hle.
      pose proof (Pos.succ_discr fidx) as Hne.
      apply Hne. auto.
    - constructor. now apply Pos.le_refl.
      apply Forall_impl_In with (2:=IH2).
      intros p Hin Hle.
      apply Pos.le_trans with (2:=Hle).
      apply pos_le_plus1.
  Qed.

  Lemma wc_elab_exp':
    forall ae e lcks fidx fidx' loc,
      elab_exp' lcks fidx ae = OK (fidx', (e, loc)) ->
      Forall Name_only_core_sclock lcks ->
      Forall (wc_sclock (idck (Env.elements env))) lcks ->
      wc_exp G (idck (Env.elements env)) e.
  Proof.
    induction ae using expression_ind2;
    intros e lcks fidx fidx' loc Helab Hnlcks Hlcks;
    inv Helab; NamedDestructCases;
    repeat progress match goal with
    | H: Forall _ [?e] |- _ => inv H
    | H1: context [elab_exp' _ _ _ = OK _],
      H2: elab_exp' _ _ _ = OK _ |- wt_exp _ _ _  =>
      apply H1 in H2; clear H1; auto
    | H:find_type_unop _ _ _ = OK _ |- _ =>
      unfold find_type_unop in H;
      rewrite type_unop'_correct in H; NamedDestructCases
    | H:find_type_binop _ _ _ _ = OK _ |- _ =>
      unfold find_type_binop in H;
      rewrite type_binop'_correct in H; NamedDestructCases
    | H:assert_sclock _ _ _ = OK _ |- _ => apply assert_sclock_spec in H
    | H:assert_type _ _ _ = OK _ |- _ => apply assert_type_spec in H
    | H: _ = OK _ |- _ => monadInv2 H
    | H: single_annot _ _ = OK _ |- _ =>
      apply single_annot_spec in H; destruct H
    | H:assert_paired_types _ _ _ _ _ = OK _ |- _ =>
      apply assert_paired_types_spec_clocks in H;
      setoid_rewrite lannots_ty_lannots_spec in H
    | H:Forall _ [] |- _ => clear H
    end; subst.
    - (* Eunop *)  eauto with lclocking.
    - (* Ebinop *) eauto with lclocking.
    - (* Eite *)
      match goal with
        H:assert_paired_types _ _ _ _ _ = OK _ |- _ =>
        apply assert_paired_types_spec_clocks in H;
          setoid_rewrite <-Forall_map in H;
          setoid_rewrite lannots_clocksof in H;
          destruct H
      end.
      econstructor; eauto with lclocking;
        try rewrite Forall_map;
        repeat progress match goal with
        | Hmm: mmaps _ _ ?aes = OK (_, ?es) |- Forall _ ?es =>
          apply mmaps_weak_spec' with (1:=Hmm); auto; intros ????? Helab
        | |- wc_exp _ _ (fst ?eloc) => destruct eloc; simpl
        | Hfa: Forall _ ?eas, Hin:In ?ea ?eas,
          Helab:elab_exp' _ _ ?ea = OK (_, (?e, _)) |- wc_exp _ _ ?e =>
          apply Forall_forall with (1:=Hfa) (2:=Hin) in Helab; now auto
        end.
    - (* Eunop (CastOp) *) eauto with lclocking.
    - (* Eapp *)
      setoid_rewrite surjective_pairing in EQ3.
      simpl in EQ3. monadInv2 EQ3.
      repeat match goal with
      | x:(list sclock * positive)%type |- _ => destruct x as (sclks & fidx'')
      | x:(Env.t ident)%type |- _ => rename x into aimap
      end.
      unfold find_node_interface in *. NamedDestructCases.
      apply wt_nenv in Heq. destruct Heq as (n & Hfind & Hnin & Hnout).
      apply Forall2_eq in Hnin. apply Forall2_eq in Hnout. subst.
      destruct wf_G as (wt_G & wc_G).
      destruct (wc_find_node _ _ _ wc_G Hfind) as (G' & Hfind').
      match goal with EQ0:approx_imap _ _ _ = OK _,
                      EQ1:mmaps (elab_arg elab_exp') _ _ = OK _,
                      EQ2:mmap _ n.(n_in) = OK ?i,
                      EQ3:check_inputs _ _ (lnannots ?xs) = OK ?any,
                      EQ4:mmap _ n.(n_out) = OK ?o
                      |- _ =>
        destruct any;
          rename EQ0 into Hai, EQ1 into Hearg, EQ2 into Hiann, EQ3 into Hchk,
                 EQ4 into Hoann, i into iann, o into oann, xs into els
      end.
      assert (wc_sclock (idck (Env.elements env))
                        (approx_base_clock lcks n.(n_out))) as Hwcb
          by (apply wc_approx_base_clock; inversion Hlcks; auto).
      assert (Forall (wc_sclock (idck (Env.elements env)))
                     (map (fun xtc =>
                             approx_clock (approx_base_clock lcks n.(n_out))
                                          aimap (dck xtc)) n.(n_in))) as Hwtac.
      { apply Forall_forall.
        setoid_rewrite in_map_iff.
        intros ? ((z, (zty, zck)) & Hz & Hzin).
        subst. unfold dck. simpl.
        inversion Hfind' as (Hwcin & Hother). clear Hother.
        unfold wc_env in Hwcin.
        apply Forall_forall with (x:=(z, zck)) in Hwcin.
        2:now apply In_idck_exists; eauto.
        simpl in Hwcin; clear Hzin.
        induction zck; auto.
        inv Hwcin. simpl.
        destruct (Env.find i aimap) eqn:Hia. 2:now auto with lclocking.
        match goal with H:Env.find i aimap = Some ?i0 |- _ =>
          rename i0 into i';
            destruct (Env.find i' env) eqn:Hia'; [|now auto with lclocking] end.
        match goal with H:Env.find i' env = Some ?p |- _ =>
          destruct p as (ty, ck) end.
        pose proof (wc_cenv _ _ _ Hia').
        apply Env.elements_correct in Hia'.
        econstructor; eauto using wc_sclk.
        apply In_idck_exists; eauto. }
      econstructor; eauto.
      + (* the argument expressions are well clocked *)
        apply Forall_map.
        eapply mmaps_weak_spec with (1:=Hearg)
          (I:=fun s=> Forall Name_only_core_sclock (fst s)
                      /\ Forall (wc_sclock (idck (Env.elements env))) (fst s)).
        split; auto.
        * apply Forall_forall.
          simpl. intros sck Hin.
          apply in_map_iff in Hin.
          destruct Hin as ((z, (zty, zck)) & Hac & Hin).
          subst. apply Name_only_core_approx_clock.
          now apply Name_only_core_approx_base_clock.
        * intros ae (lcks1, fidx1) (e, loc0) (lcks2, fidx2) (Hno & Hwc) Hin Helab.
          simpl. simpl in Helab. monadInv2 Helab.
          eapply Forall_forall in Hin; eauto.
          repeat split; eauto using Forall_skipn.
      + (* disjoint indexes in argument expressions *)
        eapply mmaps_elab_arg_DisjointIndexes with (2:=Hearg).
        apply Forall_forall.
        simpl. intros sck Hin.
        apply in_map_iff in Hin.
        destruct Hin as ((z, (zty, zck)) & Hac & Hin).
        subst. apply Name_only_core_approx_clock.
        now apply Name_only_core_approx_base_clock.
      + (* NoDup (indexes (map snd oann)) *)
        apply mmap_inst_annot_NoDup_indexes with (2:=Hoann).
        apply (NoDupMembers_app_r _ _ (NoDupMembers_app_r _ _ n.(n_nodup))).
      + (* typing of node application *)
        exists (calculate_base_clock n.(n_in) (lnannots els)).
        exists (make_imap (Env.empty ckid) n.(n_in) (lnannots els)).
        exists (snd (fold_left make_omap' n.(n_out) (fidx'', Env.empty positive))).
        split.
        * match goal with H:check_inputs _ _ _ = OK _ |- _ =>
            apply check_inputs_spec in H;
              pose proof (Forall2_length _ _ _ H) as Hilen1
          end.
          eapply mmap_inversion, list_forall2_Forall2 in Hiann.
          pose proof (Forall2_length _ _ _ Hiann) as Hilen2.
          apply Forall2_forall; split.
          2:now setoid_rewrite Hilen2; setoid_rewrite Hilen1;
            rewrite <-lnannots_nclocksof, map_length.
          intros (x, (xty, xck)) nck Hin.
          apply inst_annot_inst_in with (loc:=loc) (ty:=xty).
          rewrite <-lnannots_nclocksof, combine_map_snd in Hin.
          apply in_map_iff in Hin.
          destruct Hin as (((v, (vty, vck)), ((wty, wnck), wloc)) & Heq & Hin).
          simpl in Heq. inv Heq.
          rewrite (In_find_make_imap _ _ _ _ _ _ _
                                     (NoDupMembers_app_l _ _ n.(n_nodup)) Hin).
          apply Forall2_chain_In with (1:=Hiann) (2:=Hchk) in Hin.
          destruct Hin as ((zty, zck) & Hinst & Heq1 & Heq2).
          subst. apply inst_annot_make_imap in Hinst.
          rewrite Heq2 in Hinst.
          destruct (Env.find x
                     (make_imap (Env.empty ckid) (n_in n) (lnannots els))); auto.
        * simpl in *.
          eapply mmap_inversion, list_forall2_Forall2 in Hoann.
          pose proof (Forall2_length _ _ _ Hoann) as Hilen2.
          apply Forall2_forall; split.
          2:now setoid_rewrite Hilen2.
          intros (x, (xty, xck)) (ty, nck) Hin.
          apply Forall2_In with (1:=Hin) in Hoann.
          eapply inst_annot_inst_out with (1:=Hoann).
    - (* Econst *)
      unfold add_whens.
      case (do_add_when_to_constants tt); auto with lclocking.
      destruct lcks; simpl; auto with lclocking.
      inversion_clear Hnlcks as [|? ? Hns Hnl']; clear Hnl'.
      inversion_clear Hlcks as [|? ? Hs Hl']; clear Hl'.
      induction s. now simpl; auto with lclocking.
      match goal with H: context [Son _ ?ck b] |- _ => destruct ck end;
        inversion_clear Hs as [| |? ? ? ? Hwc Hin]; auto; simpl.
      now inversion_clear Hns as [? Hns'|]; apply IHs; auto; inv Hns'.
      subst; simpl.
      constructor; auto with lclocking.
      + constructor; auto. apply IHs; auto with name_only_sclock.
      + destruct ck; simpl; auto;
          rewrite clocksof_cons, Forall_app, clocksof_nil;
          simpl; split; auto with datatypes.
    - (* Evar *) eauto using find_var_clock with lclocking.
    - (* Efby *)
      econstructor;
        try rewrite Forall_map;
        try rewrite map_fst_discardname_types;
        try rewrite Forall2_eq;
        try rewrite map_ckstream_discardname_lnannots_clocksof;
        repeat progress match goal with
        | Hmm: mmaps _ _ ?aes = OK (_, ?es) |- Forall _ ?es =>
          apply mmaps_weak_spec' with (1:=Hmm); auto; intros ????? Helab
        | |- wc_exp _ _ (fst ?eloc) => destruct eloc; simpl
        | Hfa: Forall _ ?eas, Hin:In ?ea ?eas,
          Helab:elab_exp' _ _ ?ea = OK (_, (?e, _)) |- wc_exp _ _ ?e =>
          apply Forall_forall with (1:=Hfa) (2:=Hin) in Helab; now auto
        | H:assert_paired_clock_types _ _ _ = OK _ |- _ =>
          apply assert_paired_clock_types_spec_clocks in H;
          setoid_rewrite map_ckstream_lnannots_clocksof in H
        end; auto.
      apply Forall_forall. now auto with lclocking.
    - (* Ewhen *)
      econstructor;
        try rewrite Forall_map;
        repeat progress match goal with
        | Hmm: mmaps _ _ ?aes = OK (_, ?es) |- Forall _ ?es =>
          apply mmaps_weak_spec' with (1:=Hmm); auto; intros ????? Helab
        | |- wc_exp _ _ (fst ?eloc) => destruct eloc; simpl
        | Hfa: Forall _ ?eas, Hin:In ?ea ?eas,
          Helab:elab_exp' _ _ ?ea = OK (_, (?e, _)) |- wc_exp _ _ ?e =>
          apply Forall_forall with (1:=Hfa) (2:=Hin) in Helab; apply Helab;
            now eauto using wc_sclk, find_var_wc_clock, wc_cenv with name_only_sclock
        | H:assert_same_clock _ _ = OK _ |- _ =>
          apply assert_same_clock_spec in H;
            setoid_rewrite <-Forall_map in H;
            setoid_rewrite lannots_clocksof in H
        end; eauto using find_var_clock.
    - (* Emerge *)
      econstructor;
        try rewrite Forall_map;
        repeat progress match goal with
        | Hmm: mmaps _ _ ?aes = OK (_, ?es) |- Forall _ ?es =>
          apply mmaps_weak_spec' with (1:=Hmm); auto; intros ????? Helab
        | |- wc_exp _ _ (fst ?eloc) => destruct eloc; simpl
        | Hfa: Forall _ ?eas, Hin:In ?ea ?eas,
          Helab:elab_exp' _ _ ?ea = OK (_, (?e, _)) |- wc_exp _ _ ?e =>
          apply Forall_forall with (1:=Hfa) (2:=Hin) in Helab; apply Helab;
            eauto 6 using wc_sclk, find_var_wc_clock, find_var_clock
                     with name_only_sclock lclocking
        | H:assert_paired_types _ _ _ _ _ = OK _ |- _ =>
          apply assert_paired_types_spec_clocks in H;
            setoid_rewrite <-Forall_map in H;
            setoid_rewrite lannots_clocksof in H;
            destruct H
        end; eauto using find_var_clock with datatypes name_only_sclock.
  Qed.

  Lemma var_clocks_wt:
    forall loc xs lcks,
      var_clocks loc xs = OK lcks ->
      Forall (wt_sclock (idty (Env.elements env))) lcks.
  Proof.
    induction xs as [|x xs IH]. now inversion_clear 1; auto.
    simpl. intros * Hvc.
    monadInv Hvc.
    apply IH in EQ1.
    constructor; auto.
    apply find_var_wt_clock in EQ. now apply wt_sclk.
  Qed.

  Lemma check_pat_wt:
    forall loc pmap any xs anns,
      check_pat loc pmap xs anns = OK any ->
      Forall2
        (fun x els => In (x, fst (fst els)) (idty (Env.elements env))) xs anns.
  Proof.
    intros loc pmap. destruct any.
    induction xs as [|x xs IH]; intros anns Hcp.
    now destruct anns; simpl in Hcp; monadInv Hcp; auto.
    destruct anns as [|((ty, nck), loc')]; simpl in Hcp; monadInv Hcp.
    match goal with H:check_pat _ _ _ _ = OK _ |- _ => apply IH in H end.
    constructor; auto.
    match goal with H:assert_id_type _ _ _ _ = OK _ |- _ =>
      apply assert_id_type_spec in H end.
    subst; simpl. eapply find_var_type; eauto.
  Qed.

  Lemma wt_elab_equation:
    forall aeq eq,
      elab_equation aeq = OK eq ->
      wt_equation G (idty (Env.elements env)) eq.
  Proof.
    intros ((axs, aes), loc) (xs, es) Helab.
    simpl in Helab. monadInv Helab.
    match goal with H:var_clocks _ _ = OK ?x |- _ =>
      rename x into lcks, H into Hvc; apply var_clocks_wt in Hvc end.
    match goal with H:check_pat _ _ _ (lnannots ?x) = OK ?y |- _ =>
      rename x into els, H into Hcp; destruct y end.
    match goal with H:mmaps _ _ _ = OK (?x, _) |- _ =>
      destruct x as (scks, fidx); rename H into Hmm end.
    split.
    - apply Forall_map.
      match goal with H:Forall ?P lcks |- Forall ?Q els =>
        apply mmaps_weak_spec with (I:=fun s=>Forall P (fst s)) (R:=Q) in Hmm;
          destruct Hmm; auto end.
      intros ae (scks', fidx') (e, loc') (scks'', fidx'') Hlcks Hin Helab.
      simpl in Helab. monadInv2 Helab.
      split.
      now apply Forall_skipn with (1:=Hlcks).
      now apply wt_elab_exp' with (1:=EQ) (2:=Hlcks).
    - rewrite <-lnannots_typesof.
      apply Forall2_map_2.
      apply check_pat_wt with (1:=Hcp).
  Qed.

  Lemma var_clocks_wc:
    forall loc xs lcks,
      var_clocks loc xs = OK lcks ->
      Forall (wc_sclock (idck (Env.elements env))) lcks.
  Proof.
    induction xs as [|x xs IH]. now inversion_clear 1; auto.
    simpl. intros * Hvc.
    monadInv Hvc.
    apply IH in EQ1.
    constructor; auto.
    apply find_var_wc_clock in EQ. now apply wc_sclk.
  Qed.

  Lemma var_clocks_only_core:
    forall loc xs lcks,
      var_clocks loc xs = OK lcks ->
      Forall Name_only_core_sclock lcks.
  Proof.
    induction xs as [|x xs IH]. now inversion_clear 1; auto.
    simpl. intros * Hvc.
    monadInv Hvc.
    apply IH in EQ1.
    constructor; auto using Name_only_core_sclock, Name_only_sclk.
  Qed.

  Lemma make_pmap_patsub:
    forall els,
      NoDup (indexes (nclocksof (map fst els))) ->
      forall xs x,
        Env.find x (make_pmap (Env.empty ident) xs (lnannots els))
        = patsub (nclocksof (map fst els)) xs x.
  Proof.
    intros els Hnd xs y.
    pose proof (proj1 (@Env.Props.P.F.empty_in_iff ident y)) as Hniy. revert Hniy.
    generalize (Env.empty ident).
    revert Hnd y xs.
    induction els as [|els elss IHe].
    - simpl.
      intros Hndp y xs.
      induction xs as [|x xs IHx]; simpl; intros s Hni;
        apply Env.Props.P.F.not_find_in_iff in Hni; rewrite Hni;
        unfold patsub; auto.
    - intros Hnd y xs s Hniy. simpl.
      rewrite nclockof_lnannot.
      simpl in Hnd. rewrite indexes_app in Hnd.
      revert xs s Hniy.
      assert (Hnd':=Hnd). rewrite Permutation_app_comm in Hnd'.
      apply NoDup_app_weaken in Hnd'.
      specialize (IHe Hnd'). clear Hnd'.
      rewrite nclockof_lnannot in Hnd. revert Hnd.
      induction (lnannot els) as [|ann anns IHa].
      now intros; apply IHe; auto.
      intros Hnd xs s Hniy.
      destruct ann as ((ty, nck), loc).
      destruct xs as [|x xs]; simpl.
      now apply Env.Props.P.F.not_find_in_iff in Hniy; rewrite Hniy; unfold patsub.
      unfold patsub.
      destruct nck as [|cid sclk]. now rewrite IHa.
      destruct cid as [id|]. 2:now rewrite IHa.
      destruct (ident_eq_dec y id) as [He|Hne].
      + subst. simpl.
        rewrite Pos.eqb_refl. simpl.
        inversion_clear Hnd as [|? ? Hni Hnd'].
        rewrite <-lnannots_nclocksof, <-indexes_app, <-map_app in Hni.
        revert Hni. clear. revert s xs.
        induction (anns ++ lnannots elss) as [|((ty, nck), loc) xs IH].
        now destruct xs; simpl; rewrite Env.gss.
        intros s ys Hni.
        destruct ys. now simpl; rewrite Env.gss.
        simpl. destruct nck; auto.
        destruct c; auto.
        simpl in Hni.
        apply Classical_Prop.not_or_and in Hni.
        destruct Hni as (Hni1 & Hni2).
        rewrite Env.add_comm; auto.
      + simpl. assert (Hne' := Hne).
        apply Pos.eqb_neq in Hne'. rewrite Hne'.
        apply IHa.
        now inversion_clear Hnd.
        rewrite Env.Props.P.F.add_in_iff; apply Classical_Prop.and_not_or; auto.
  Qed.

  Lemma NoDup_indexes_nclocksof:
    forall es,
      Forall (wc_exp G (idck (Env.elements env))) es ->
      DisjointIndexes (map nclockof es) ->
      NoDup (indexes (nclocksof es)).
  Proof.
    induction es as [|e es IH]. now simpl; auto using NoDup_nil.
    inversion_clear 1 as [|? ? Hwc Hwcs].
    inversion_clear 1 as [|? ? Hdj Hii].
    specialize (IH Hwcs Hdj).
    simpl; rewrite indexes_app.
    apply NoDup_app'; eauto using wc_NoDup_indexes.
    apply Forall_forall.
    intros i Hin.
    apply indexes_Is_index_in_nclocks, Hii in Hin.
    revert i Hin. clear.
    induction es as [|e es IH]. now auto.
    simpl. intros i HH. inversion_clear HH as [|? ? Hni Hfa].
    apply IH in Hfa.
    simpl; rewrite indexes_app.
    intro Hin. apply in_app in Hin.
    destruct Hin as [Hin|Hin]; auto.
    now apply indexes_Is_index_in_nclocks in Hin.
  Qed.

  Lemma unify_clock_spec:
    forall loc psubst sck ck,
      unify_clock loc psubst sck = OK ck ->
      pinst (fun x => Env.find x psubst) sck = Some ck.
  Proof.
    induction sck; simpl. now inversion_clear 1.
    intros ck Hm. destruct c.
    - monadInv Hm.
      destruct (Env.find p psubst) eqn:Heq; monadInv EQ0.
      apply IHsck in EQ. rewrite EQ.
      simpl. now rewrite Heq.
    - monadInv Hm. apply IHsck in EQ. now rewrite EQ.
  Qed.

  Lemma check_pat_spec:
    forall loc any pmap xs anns,
      check_pat loc pmap xs anns = OK any ->
      Forall2 (fun x ann => exists ck,
                   pinst (fun y=> Env.find y pmap) (stripname (snd (fst ann)))
                                                                      = Some ck
                   /\ In (x, ck) (idck (Env.elements env))) xs anns.
  Proof.
    induction xs as [|x xs IH]. now destruct anns; simpl; inversion 1; auto.
    induction anns as [|((ty, nck), loc') anns IHa]. now inversion_clear 1.
    intro Hcp. simpl in Hcp. monadInv Hcp.
    constructor; auto.
    match goal with H:unify_clock _ _ _ = _ |- _ =>
      apply unify_clock_spec in H end.
    eexists. split; eauto.
    match goal with H:assert_id_clock _ _ _ _ = _ |- _ =>
      apply assert_id_clock_eq in H end.
    subst; eauto using find_var_clock.
  Qed.

  Lemma pninst_swap:
    forall f g cid,
      (forall x, f x = g x) ->
      pninst f cid = pninst g cid.
  Proof.
    intros f g cid Hext.
    destruct cid; auto.
    now simpl; rewrite Hext.
  Qed.

  Lemma pinst_swap:
    forall f g sck,
      (forall x, f x = g x) ->
      pinst f sck = pinst g sck.
  Proof.
    intros f g sck Hext.
    induction sck; auto.
    simpl. rewrite IHsck.
    now rewrite (pninst_swap _ _ _ Hext).
  Qed.

  Lemma wc_elab_equation:
    forall aeq eq,
      elab_equation aeq = OK eq ->
      wc_equation G (idck (Env.elements env)) eq.
  Proof.
    intros ((axs, aes), loc) (xs, es) Helab.
    simpl in Helab. monadInv Helab.
    match goal with H:var_clocks _ _ = OK ?x |- _ =>
      rename x into lcks, H into Hvc;
        pose proof (var_clocks_only_core _ _ _ Hvc) as Hno;
        apply var_clocks_wc in Hvc
    end.
    match goal with H:check_pat _ _ _ (lnannots ?x) = OK ?y |- _ =>
      rename x into els, H into Hcp; destruct y end.
    match goal with H:mmaps _ _ _ = OK (?x, _) |- _ =>
      destruct x as (scks, fidx); rename H into Hmm end.
    assert (Forall (wc_exp G (idck (Env.elements env))) (map fst els)) as Hwc.
    { apply Forall_map.
      match goal with H:Forall ?P1 lcks, H2:Forall ?P2 lcks |- Forall ?Q els =>
        apply mmaps_weak_spec
        with (I:=fun s=>Forall (fun x=> P1 x /\ P2 x) (fst s)) (R:=Q) in Hmm;
          destruct Hmm; auto using Forall_Forall end.
      intros ae (scks', fidx') (e, loc') (scks'', fidx'') Hlcks Hin Helab.
      simpl in Helab. monadInv2 Helab.
      split.
      now apply Forall_skipn with (1:=Hlcks).
      apply Forall_Forall' in Hlcks.
      now apply wc_elab_exp' with (1:=EQ); auto. }
    assert (DisjointIndexes (map Instantiator.L.Syn.nclockof (map fst els)))
      as Hdj by (eauto using mmaps_elab_arg_DisjointIndexes).
    repeat split; auto.
    rewrite <-map_ckstream_lnannots_clocksof.
    apply Forall2_map_2.
    apply check_pat_spec in Hcp.
    apply Forall2_impl_In with (2:=Hcp).
    intros x ((ty, nck), loc') Hix Hie.
    destruct 1 as (ck & Hck1 & Hck2).
    simpl in Hck1.
    unfold wc_patvar. simpl.
    pose proof (NoDup_indexes_nclocksof _ Hwc Hdj) as Hndi.
    rewrite <-lnannots_nclocksof. rewrite <-lnannots_nclocksof in Hndi.
    rewrite lnannots_nclocksof in Hndi.
    pose proof (make_pmap_patsub _ Hndi) as Hpat.
    erewrite pinst_swap in Hck1.
    2:now apply Hpat.
    rewrite <-lnannots_nclocksof in Hck1.
    unfold ckstream; simpl. now rewrite Hck1.
  Qed.

End ElabExpressions.

Section ElabDeclaration.

  (* Preceding dataflow program. *)
  Variable G : global.

  (* Map node names to input and output types and clocks. *)
  Variable nenv : Env.t (list (ident * (type * clock))
                        * list (ident * (type * clock))).

  Hypothesis wt_nenv : Is_interface_map G nenv.

  Definition err_incoherent_clock (loc: astloc) (x: ident) : res unit :=
    err_loc loc (MSG "The declared clock of " :: CTX x
                     :: msg " is incoherent with the other declarations").

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
          then err_loc loc (CTX x :: msg " is declared more than once")
          else elab_var_decls_pass
                 (Env.add x (elab_type sty, Cbase) env, notdone) vds

        | FULLCK (ON cy' y b) =>
          match Env.find y env with
          | None => elab_var_decls_pass (env, vd::notdone) vds
          | Some (yt, cy) =>
            if Env.mem x env
            then err_loc loc (CTX x :: msg " is declared more than once")
            else do ok <- assert_id_type loc y yt bool_type;
                 do ok <- assert_preclock loc x cy' cy;
                 elab_var_decls_pass
                   (Env.add x (elab_type sty, Con cy y b) env, notdone) vds
          end

        | WHENCK y b =>
          match Env.find y env with
          | None => elab_var_decls_pass (env, vd::notdone) vds
          | Some (yt, cy) =>
            do ok <- assert_id_type loc y yt bool_type;
            if Env.mem x env
            then err_loc loc (CTX x :: msg " is declared more than once")
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
      apply all_wt_clock_add; auto with ltyping.
    - (* (x, (ty, FULLCK (ON ck y yb))) *)
      NamedDestructCases.
      2:now apply IH in Helab; auto.
      monadInv Helab.
      apply Env.Props.P.F.not_mem_in_iff in Heq1.
      apply IH in EQ2; auto.
      apply all_wt_clock_add; auto.
      eapply assert_id_type_eq in EQ; subst.
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
      apply assert_id_type_eq in EQ; subst.
      constructor.
      2:now apply Hawc in Heq.
      apply Env.elements_correct in Heq.
      apply In_idty_exists; eauto.
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
      + intros x' Hfind.
        apply Henv, Env.Props.P.F.add_in_iff; auto.
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
        * intros x' Hfind.
          apply Henv, Env.Props.P.F.add_in_iff; auto.
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
        * intros x' Hfind.
          apply Henv, Env.Props.P.F.add_in_iff; auto.
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
        | [] => err_loc loc (MSG "incoherent or cyclic clocks: "
                                 :: msg_ident_list (map fst vds))
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

  Lemma elab_var_decls_find:
    forall loc vds env env',
      elab_var_decls loc env vds = OK env' ->
      (forall x v,
          Env.find x env = Some v ->
          Env.find x env' = Some v).
  Proof.
    unfold elab_var_decls.
    intros loc vds. generalize vds at 1.
    intro fuel. revert vds.
    induction fuel as [|cd fuel IH].
    now simpl; intros * Helab; NamedDestructCases.
    intros vds env env' Helab x v Hfind.
    destruct vds as [|vd vds].
    now simpl in Helab; monadInv Helab.
    simpl in Helab. monadInv Helab.
    rename x0 into env'', x1 into vds'.
    apply elab_var_decls_pass_spec in EQ.
    destruct EQ as (vds1 & vds2 & ? & ? & ? & ? & ? & ? & Hfind').
    apply Hfind' in Hfind.
    eapply IH in EQ0; eauto.
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
          eapply fst_InMembers, Env.In_Members, Henv', Env.elements_In; eauto.
      + apply in_app.
        apply fst_InMembers, InMembers_In in HH.
        destruct HH as (v & HH).
        apply Env.elements_In, Henv'' in HH.
        destruct HH as [HH|HH].
        * right. now apply fst_InMembers, Env.In_Members.
        * left. now apply fst_InMembers.
  Qed.

  Fixpoint check_vars (loc: astloc) (defd: PS.t) (xs: idents) : res PS.t :=
    match xs with
    | nil => OK defd
    | x::xs => if PS.mem x defd
               then check_vars loc (PS.remove x defd) xs
               else err_loc loc (CTX x :: msg " is improperly defined")
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

  Fixpoint check_defined (loc: astloc) (defd: PS.t)
                         (eqs: list equation) : res unit :=
    match eqs with
    | nil => if PS.is_empty defd then OK tt
             else err_loc loc (MSG "some variables are not defined:"
                                   :: msg_ident_list (PS.elements defd))
    | (xs, _)::eqs => do defd' <- check_vars loc defd xs;
                      check_defined loc defd' eqs
    end.

  Lemma check_defined_spec:
    forall eqs loc defd,
      check_defined loc defd eqs = OK tt ->
      (forall x, In x (vars_defined eqs) <-> PS.In x defd)
      /\ NoDup (vars_defined eqs).
  Proof.
    induction eqs as [|eq eqs IH]; simpl; intros loc defd Hchk;
      NamedDestructCases.
    - rewrite PS.is_empty_spec in Heq.
      apply PSP.empty_is_empty_1 in Heq.
      setoid_rewrite Heq.
      repeat split; auto using NoDup_nil.
      + inversion 1.
      + apply not_In_empty.
    - monadInv Hchk.
      rename x into defd', i into xs, l into es.
      apply check_vars_spec in EQ.
      destruct EQ as (Hcv1 & Hcv2 & Hcv3 & Hcv4).
      specialize (IH _ _ EQ0); clear EQ0.
      destruct IH as (IH1 & IH2).
      setoid_rewrite in_app.
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
        specialize (Hcv2 x). specialize (IH1 x). intuition.
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
    let Hfind_in := fresh "Hfind_in" in
    let Hfind_out := fresh "Hfind_out" in
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
                     simpl; auto with lclocking);
                    (assert (Hwt_in := H);
                     apply elab_var_decls_all_wt_clock in Hwt_in;
                     simpl; auto using all_wt_clock_empty with lclocking);
                    apply elab_var_decls_permutation in H;
                    simpl in H; rewrite app_nil_r in H;
                    rename H into Helab_in, x into env_in end;
    match goal with H:elab_var_decls _ _ outputs = OK ?x |- _ =>
                    (assert (Hwc_out := H);
                     apply elab_var_decls_wc_env in Hwc_out;
                     simpl; auto with lclocking);
                    (assert (Hwt_out := H);
                     apply elab_var_decls_all_wt_clock in Hwt_out;
                     simpl; auto with lclocking);
                    pose proof (elab_var_decls_find _ _ _ _ H) as Hfind_in;
                    apply elab_var_decls_permutation in H;
                    rewrite <-Helab_in in H;
                    rename H into Helab_out, x into env_out end;
    match goal with H:elab_var_decls _ _ locals = OK ?x |- _ =>
                    (assert (Hwc_var := H);
                     apply elab_var_decls_wc_env in Hwc_var;
                     simpl; auto with lclocking);
                    (assert (Hwt_var := H);
                     apply elab_var_decls_all_wt_clock in Hwt_var;
                     simpl; auto with lclocking);
                    pose proof (elab_var_decls_find _ _ _ _ H) as Hfind_out;
                    apply elab_var_decls_permutation in H;
                    rewrite <-Helab_out in H;
                    rename H into Helab_var, x into env end;
    match goal with H:mmap (elab_equation _ _) _ = OK ?x |- _ =>
      rename H into Helabs; rename x into eqs end;
    match goal with H:check_defined _ _ _ = OK ?x |- _ =>
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
  Local Open Scope nat.

  Program Definition elab_declaration (wf_G : wt_global G /\ wc_global G)
                                      (decl: LustreAst.declaration)
    : res {n | wt_node G n /\ wc_node G n} :=
    match decl with
    | NODE name b inputs outputs locals equations loc =>
      match (do env_in  <- elab_var_decls loc (Env.empty (type * clock)) inputs;
             do env_out <- elab_var_decls loc env_in outputs;
             do env     <- elab_var_decls loc env_out locals;
             do xin     <- mmap (annotate env_in) inputs;
             do xout    <- mmap (annotate env_out) outputs;
             do xvar    <- mmap (annotate env) locals;
             do eqs     <- mmap (elab_equation env nenv) equations;
             do ok      <- check_defined loc
                             (nameset (nameset PS.empty xvar) xout) eqs;
             if existsb (fun x=>Env.mem x env) Ident.Ids.reserved
             then err_loc loc (msg "illegal variable name")
             else if (length xin ==b 0) || (length xout ==b 0)
                  then err_loc loc (msg "not enough inputs or outputs")
                  else OK (xin, xout, xvar, eqs)) with
      | Error e => Error e
      | OK (xin, xout, xvar, eqs) => OK {| n_name  := name;
                                           n_hasstate := b;
                                           n_in    := xin;
                                           n_out   := xout;
                                           n_vars  := xvar;
                                           n_eqs   := eqs;
                                           n_ingt0 := _;
                                           n_outgt0:= _;
                                           n_defd  := _;
                                           n_nodup := _;
                                           n_good  := _ |}
      end
    end.
  Next Obligation.
    (* 0 < length xin *)
    match goal with H:(length _ ==b 0) || _ = false |- _ =>
      rewrite Bool.orb_false_iff in H; destruct H as (Hin & Hout) end.
    apply not_equiv_decb_equiv in Hin.
    now apply Nat.neq_0_lt_0 in Hin.
  Qed.
  Next Obligation.
    (* 0 < length xout *)
    match goal with H:(length _ ==b 0) || _ = false |- _ =>
      rewrite Bool.orb_false_iff in H; destruct H as (Hin & Hout) end.
    apply not_equiv_decb_equiv in Hout.
    now apply Nat.neq_0_lt_0 in Hout.
  Qed.
  Next Obligation.
    (* Permutation (map var_defined eqs) (map fst (xvar ++ xout)) *)
    MassageElabs outputs locals inputs.
    apply check_defined_spec in Hdefd.
    destruct Hdefd as (Hdefd & Hnodup).
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
    - setoid_rewrite Hdefd.
      setoid_rewrite PSP.FM.empty_iff.
      setoid_rewrite in_app.
      intuition.
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
    unfold Ident.Ids.NotReserved.
    change (Forall (fun xty=>(fun x=>~In x Ident.Ids.reserved) (fst xty))
                   (xin ++ xvar ++ xout)).
    rewrite <-Forall_map, map_app, map_app.
    rewrite Hvar, Hin, Hout in Helab_var.
    rewrite Permutation_app_comm, Permutation_app_assoc, Helab_var.
    rewrite 2 Bool.orb_false_iff in Hb.
    destruct Hb as (Hb1 & Hb2 & ?).
    rewrite <-Env.Props.P.F.not_mem_in_iff in Hb1, Hb2.
    apply Forall_forall.
    intros xtx Hm Hir.
    apply fst_InMembers, Env.In_Members in Hm.
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
      rewrite Hin, Hout, Hvar in Helab_var.
      assert (Forall (fun yv=>Env.find (fst yv) env = Some (snd yv))
                     (xin ++ xvar ++ xout)) as Hf.
      { repeat (apply Forall_app; split; auto).
        apply Forall_impl_In with (2:=Hf_in); auto.
        apply Forall_impl_In with (2:=Hf_out); auto. }
      apply permutation_forall_elements in Hf.
      2:now rewrite <-Helab_var, map_app, map_app,
        Permutation_app_comm, Permutation_app_assoc.
      repeat split.
      + (* wt_clocks xin xin *)
        apply Forall_forall.
        intros (x, (xty, xck)) Hxin.
        assert (Hfi:=Hf_in). apply permutation_forall_elements in Hfi.
        2:now rewrite <-Helab_in, Hin.
        apply Forall_forall with (2:=Hxin), Hwt_in in Hf_in.
        rewrite Hfi. auto.
      + (* wt_clocks (xin ++ xout) xout *)
        assert (Forall (fun yv=>Env.find (fst yv) env_out = Some (snd yv))
                       (xin ++ xout)) as Hfo.
        { apply Forall_app; split.
          apply Forall_impl_In with (2:=Hf_in); auto.
          apply Forall_impl_In with (2:=Hf_out); auto. }
        apply Forall_forall.
        intros (x, (xty, xck)) Hxin.
        apply permutation_forall_elements in Hfo.
        2:now rewrite map_app, Permutation_app_comm, <-Helab_out, Hin, Hout.
        apply Forall_forall with (2:=Hxin), Hwt_out in Hf_out.
        rewrite Hfo. auto.
      + (* wt_clocks (xin ++ xout ++ xvar) xvar *)
        apply Forall_forall.
        intros (x, (xty, xck)) Hxin.
        apply Forall_forall with (2:=Hxin), Hwt_var in Hf_var.
        rewrite (Permutation_app_comm xout), Hf. auto.
      + (* Forall (wt_equation G (idty (xin ++ xvar ++ xout))) eqs' *)
        apply mmap_inversion, list_forall2_Forall2 in Helabs.
        apply Forall_forall. intros eq Hein.
        apply Forall2_in_right with (1:=Helabs) in Hein.
        destruct Hein as (aeq & Hein & Helab).
        rewrite Hf.
        apply wt_elab_equation with (G:=G) in Helab; auto.
    - (* wc_node G n *)
      repeat constructor; simpl;
        repeat match goal with H:OK _ = _ |- _ =>
          symmetry in H; monadInv1 H end;
        NamedDestructCases; intros; subst;
        MassageElabs outputs locals inputs.
      + (* wc_env (idck xin) *)
        apply permutation_forall_elements in Hf_in.
        2:now rewrite <-Helab_in, Hin.
        now rewrite Hf_in.
      + (* wc_env (idck (xin ++ xout)) *)
        assert (Forall (fun yv=>Env.find (fst yv) env_out = Some (snd yv))
                       (xin ++ xout)) as Hf.
        { repeat (apply Forall_app; split; auto).
          apply Forall_impl_In with (2:=Hf_in); auto. }
        apply permutation_forall_elements in Hf.
        2:now rewrite <-Helab_out, map_app, Permutation_app_comm, Hin, Hout.
        now rewrite Hf.
      + (* wc_env (idck (xin ++ xout ++ xvar)) *)
        assert (Forall (fun yv=>Env.find (fst yv) env = Some (snd yv))
                       (xin ++ xvar ++ xout)) as Hf.
        { repeat (apply Forall_app; split; auto).
          apply Forall_impl_In with (2:=Hf_in); auto.
          apply Forall_impl_In with (2:=Hf_out); auto. }
        apply permutation_forall_elements in Hf.
        2:now rewrite <-Helab_var, map_app, map_app, Hin, Hout, Hvar,
          Permutation_app_comm, Permutation_app_assoc.
        now rewrite (Permutation_app_comm xout), Hf.
      + (* Forall (wc_equation G (idck (xin ++ xvar ++ xout))) eqs' *)
        assert (Forall (fun yv=>Env.find (fst yv) env = Some (snd yv))
                       (xin ++ xvar ++ xout)) as Hf.
        { repeat (apply Forall_app; split; auto).
          apply Forall_impl_In with (2:=Hf_in); auto.
          apply Forall_impl_In with (2:=Hf_out); auto. }
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
        intros x ty ck Hfind.
        apply Env.elements_correct in Hfind.
        rewrite <-Hf in Hfind. rewrite <-Hf.
        assert (exists ty, In (x, (ty, ck)) (xin ++ xvar ++ xout)) as Hidck
            by eauto.
        apply In_idck_exists in Hidck.
        apply wc_env_var with (2:=Hidck).
        now rewrite Hf.
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
        (G: global) (nenv: Env.t (list (ident * (type * clock))
                                 * list (ident * (type * clock))))
        (WTG: wt_global G /\ wc_global G) (Hnenv: Is_interface_map G nenv)
        (decls: list LustreAst.declaration)
  : res {G' | wt_global G' /\ wc_global G'} :=
  match decls with
  | nil => OK (exist _ G WTG)
  | d::ds =>
    match (do n <- elab_declaration _ _ Hnenv WTG d;
           let loc := declaration_loc d in
           if find_node_interface nenv loc n.(n_name)
           then err_loc loc (MSG "duplicate definition for "
                                 :: CTX n.(n_name) :: nil)
           else OK n) with
    | OK n => elab_declarations' (n::G)
                                 (Env.add n.(n_name)
                                         (n.(n_in), n.(n_out)) nenv) _ _ ds
    | Error e => Error e
    end
  end.
Next Obligation.
  split.
  - constructor; auto.
    now apply Hnenv.
  - constructor; auto.
    now apply Hnenv.
Qed.
Next Obligation.
  split.
  - intros * Hf.
    destruct (ident_eq_dec f n.(n_name)) as [He|Hne].
    + subst. rewrite Env.gss in Hf.
      injection Hf; intros; subst tcout tcin; clear Hf.
      exists n.
      repeat split; auto using Forall2_eq_refl.
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
  : res {G | wt_global G /\ wc_global G} :=
  elab_declarations' [] (Env.empty (list (ident * (type * clock))
                                   * list (ident * (type * clock))))
                     (conj wtg_nil wcg_nil)
                     Is_interface_map_empty decls.

Close Scope error_monad_scope.
