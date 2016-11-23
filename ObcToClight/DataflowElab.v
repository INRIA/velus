Require Import Rustre.Common.
Require Instantiator.

Require Import Rustre.Dataflow.Parser.Ast.
Require Import Operators.

Module Import Syn := Instantiator.DF.Syn.
Module Import Defs := Instantiator.DF.IsD.

Import Interface.Op.
Import Instantiator.OpAux.
Import Instantiator.DF.Typ.
Import Instantiator.DF.Clo.

Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Require cfrontend.Cop.
Require cparser.Cabs.

Require Import common.Errors.
Local Open Scope error_monad_scope.

(* Elaborate an AST into a well-typed Dataflow program. *)

Parameter elab_const_int : Cabs.cabsloc -> string -> constant.
Parameter elab_const_float : Cabs.floatInfo -> constant.
Parameter elab_const_char : Cabs.cabsloc -> bool -> list char_code -> constant.

(* CompCert: lib/Camlcoq.ml: camlstring_of_coqstring and coqstring_of_camlstring
   using Require ExtrOCamlString in the extraction file to extract Coq
   strings as an OCaml "char list". Then use the Ident.pos_of_string
   function.
   TODO: In the long run, we should try to use OCaml strings everywhere. *)
Parameter ident_of_camlstring : string -> ident.
Parameter string_of_astloc : astloc -> String.string.
Parameter cabsloc_of_astloc : astloc -> Cabs.cabsloc.
Parameter cabs_floatinfo : Ast.floatInfo -> Cabs.floatInfo.

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

Definition elab_constant (loc: astloc) (c: Ast.constant) : constant :=
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
                 /\ Forall2 (fun i ty=> snd i = ty) n.(n_in) tysin
                 /\ Forall2 (fun i ty=> snd i = ty) n.(n_out) tysout))
  /\ (forall f, PM.find f nenv = None -> Forall (fun n=> f <> n.(n_name)) G).

Lemma Is_interface_map_empty:
  Is_interface_map [] (PM.empty (list type * list type)).
Proof.
  split; setoid_rewrite PM.gempty; intros; try discriminate; auto.
Qed.    
  
Section ElabExpressions.

  (* Map variable names to types. *)
  Variable env : PM.t type.

  (* Map variable names to clocks. *)
  Variable cenv : PM.t clock.

  (* TODO: Consider combining env and cenv into a PM.t (type * clock).
           The advantage would be to avoid two lookups for every variable.
           The disadvantage is that the proofs become more complicated.
           Note also that we must anyway make two passes through the
           variable declarations, since we can only check that the clocks
           are well-typed after knowing all of the types. *)

  (* Preceding dataflow program. *)
  Variable G : global.

  (* Map node names to input and output types. *)
  Variable nenv : PM.t (list type * list type).

  Hypothesis wt_cenv :
    forall x ck, PM.find x cenv = Some ck -> wt_clock (PM.elements env) ck.

  Hypothesis wt_nenv : Is_interface_map G nenv.

  Definition find_type (loc: astloc) (x: ident) : res type :=
    match PM.find x env with
    | None => Error (err_loc loc (CTX x :: msg " is not declared."))
    | Some ty => OK ty
    end.

  Definition msg_of_types (ty ty': type) : errmsg :=
    MSG "expected '" :: MSG (string_of_type ty)
        :: MSG "' but got '" :: MSG (string_of_type ty') :: msg "'".
  
  Definition assert_type (loc: astloc) (x: ident) (ty: type) : res unit :=
    do xty <- find_type loc x;
    if xty ==b ty then OK tt
    else Error (err_loc loc (CTX x :: MSG ": " :: msg_of_types xty ty)).
  
  Definition find_clock (loc: astloc) (x: ident) : res clock :=
    match PM.find x cenv with
    | None => Error (err_loc loc (CTX x :: msg " is not declared."))
    | Some ck => OK ck
    end.

  Fixpoint msg_of_clock (ck: clock) : errmsg :=
    match ck with
    | Cbase          => msg "."
    | Con ck x true  => msg_of_clock ck ++ MSG " on " :: CTX x :: nil
    | Con ck x false => msg_of_clock ck ++ MSG " onot " :: CTX x :: nil
    end.

  Definition msg_of_clocks (ck ck': clock) : errmsg :=
    MSG "expected '" :: msg_of_clock ck
        ++ MSG "' but got '" :: msg_of_clock ck' ++ msg "'".
  
  Definition assert_clock (loc: astloc) (x: ident) (ck: clock) : res unit :=
    do ck' <- find_clock loc x;
    if ck ==b ck' then OK tt
    else Error (err_loc loc
                        ((CTX x :: MSG " has clock " :: msg_of_clock ck)
                                ++ MSG " but clock " :: msg_of_clock ck'
                                ++ msg " was expected.")).
  
  Definition find_node_interface (loc: astloc) (f: ident)
    : res (list type * list type) :=
    match PM.find f nenv with
    | None => Error (err_loc loc (MSG "node " :: CTX f :: msg " not found."))
    | Some tys => OK tys
    end.

  Lemma wt_find_clock:
    forall loc x ck,
      find_clock loc x = OK ck -> wt_clock (PM.elements env) ck.
  Proof.
    intros ** Hfind.
    apply wt_cenv with (x:=x).
    unfold find_clock in Hfind.
    destruct (PM.find x cenv); try discriminate.
    now monadInv Hfind.
  Qed.
  
  Fixpoint elab_clock (loc: astloc) (ck: Ast.clock) : res clock :=
    match ck with
    | BASE => OK Cbase
    | ON ck' b sx =>
      let x := ident_of_camlstring sx in
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

  Fixpoint elab_lexp (ae: Ast.expression) : res (lexp * clock) :=
    match ae with
    | CONSTANT c loc => OK (Econst (elab_constant loc c), Cbase)
    | VARIABLE sx loc =>
      let x := ident_of_camlstring sx in
      do ty <- find_type loc x;
      do ck <- find_clock loc x;
      OK (Evar x ty, ck)
    | WHEN ae' b sx loc =>
      let x := ident_of_camlstring sx in
      do ok <- assert_type loc x bool_type;
      do (e', eck) <- elab_lexp ae';
      do xck <- find_clock loc x;
      if eck ==b xck then OK (Ewhen e' x b, Con xck x b)
      else Error (err_loc loc (MSG "badly clocked when: "
                                   :: msg_of_clocks eck xck))
    | UNARY aop ae' loc =>
      let op := elab_unop aop in
      do (e', ck) <- elab_lexp ae';
      do ty' <- find_type_unop loc op (typeof e');
      OK (Eunop op e' ty', ck)
    | CAST aty' ae' loc =>
      let ty' := elab_type loc aty' in
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

  Fixpoint elab_cexp (ae: Ast.expression) : res (cexp * clock) :=
    match ae with
    | MERGE sx aet aef loc =>
      let x := ident_of_camlstring sx in
      do ok <- assert_type loc x bool_type;
      do ck <- find_clock loc x;
      do (et, ckt) <- elab_cexp aet;
      do (ef, ckf) <- elab_cexp aef;
      if typeofc et ==b typeofc ef
      then if (ckt ==b (Con ck x true))
           then if (ckf ==b (Con ck x false))
                then OK (Emerge x et ef, ck)
                else Error (err_loc loc (MSG "badly clocked merge false branch: "
                                         :: msg_of_clocks (Con ck x false) ckf))
           else Error (err_loc loc (MSG "badly clocked merge true branch: "
                                        :: msg_of_clocks (Con ck x true) ckt))
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
                                           (xs: list ident) (ys: list type)
                                                                : res PS.t :=
    match xs, ys with
    | nil, nil => OK PS.empty
    | x::xs, y::ys => do ok <- assert_type loc x y;
                      do ok <- assert_clock loc x ck;
                      do others <- check_result_list loc ck xs ys;
                      if PS.mem x others
                      then Error (err_loc loc
                                          (msg "duplicate variable in pattern"))

                      else OK (PS.add x others)
    | _, _ => Error (err_loc loc (msg "wrong number of pattern variables"))
    end.

  Definition elab_constant_with_cast (loc: astloc) (ae: Ast.expression)
                                                              : res constant :=
    match ae with
    | CAST aty (CONSTANT ac _) loc =>
      cast_constant loc (elab_constant loc ac) (elab_type loc aty)
    | CONSTANT ac loc =>
      OK (elab_constant loc ac)
    | _ => Error (err_loc loc (msg "fbys only take (casted) constants at left."))
    end.

  Lemma find_clock_clk_var:
    forall loc x ck,
      find_clock loc x = OK ck ->
      clk_var cenv x ck.
  Proof.
    unfold find_clock.
    intros loc x ck Hfind.
    NamedDestructCases; auto using clk_var.
  Qed.

  Definition elab_equation (aeq: Ast.equation) : res equation :=
    let '(sxs, ae, loc) := aeq in
    do xs <- OK (map ident_of_camlstring sxs);
    do x <- match xs with
            | x::xs => OK x
            | _ => Error (err_loc loc (msg "at least one output is required"))
            end;
    do ck <- find_clock loc x;
    match ae with
    | CALL sf aes loc =>
      let f := ident_of_camlstring sf in
      do (tysin, tysout) <- find_node_interface loc f;
      do es <- elab_lexps loc ck aes tysin;
      do ok <- check_result_list loc ck xs tysout;
      OK (EqApp xs ck f es)
           
    | FBY ae0 ae loc =>
      do v0 <- elab_constant_with_cast loc ae0;
      let v0ty := type_const v0 in
      do (e, eck) <- elab_lexp ae;
      do ok <- assert_type loc x v0ty;
      if typeof e ==b v0ty
      then if eck ==b ck
           then OK (EqFby x ck v0 e)
           else Error (err_loc loc (MSG "ill-clocked fby expression for "
                                        :: CTX x :: msg_of_clocks ck eck))
      else Error (err_loc loc (MSG "ill-typed fby expression for "
                                   :: CTX x :: msg_of_types v0ty (typeof e)))

    | _ =>
      do (e, eck) <- elab_cexp ae;
      do ok <- assert_type loc x (typeofc e);
      if eck ==b ck
      then OK (EqDef x ck e)
      else Error (err_loc loc (MSG "ill-clocked expression for "
                                   :: CTX x :: msg_of_clocks ck eck))
    end.
  
  Fixpoint assert_clocks (loc: astloc) (ck: clock) (ys: list ident)
    : res unit :=
    match ys with
    | nil => OK tt
    | y::ys =>
      do ok <- assert_clock loc y ck;
      assert_clocks loc ck ys
    end.
  
  Lemma assert_clock_spec:
    forall loc x ck,
      assert_clock loc x ck = OK tt ->
      clk_var cenv x ck.
  Proof.
    unfold assert_clock.
    intros ** Hack.
    monadInv1 Hack. NamedDestructCases.
    rewrite equiv_decb_equiv in Heq.
    rewrite Heq in *.
    apply find_clock_clk_var with (1:=EQ).
  Qed.
  
  Lemma assert_clocks_spec:
    forall loc ck xs,
      assert_clocks loc ck xs = OK tt ->
      clk_vars cenv xs ck.
  Proof.
    induction xs as [|x xs]; simpl; intros HH; try apply Forall_nil.
    monadInv1 HH.
    destruct x0.
    apply IHxs in EQ0.
    constructor; eauto using assert_clock_spec.
  Qed.

  (** Properties *)
  
  Lemma find_type_In:
    forall loc x ty,
      find_type loc x = OK ty ->
      In (x, ty) (PM.elements env).
  Proof.
    intros ** Hfty.
    unfold find_type in Hfty.
    destruct (PM.find x env) eqn:Hfind; try discriminate.
    injection Hfty; intro; subst.
    now apply PM.elements_correct in Hfind.
  Qed.
  
  Lemma assert_type_In:
    forall loc x ty y,
      assert_type loc x ty = OK y ->
      In (x, ty) (PM.elements env).
  Proof.
    intros loc x ty y Hhty.
    unfold assert_type in Hhty.
    monadInv Hhty.
    destruct (x0 ==b ty) eqn:Heq.
    2:discriminate EQ0.
    rewrite equiv_decb_equiv in Heq.
    rewrite Heq in *.
    eauto using find_type_In.
  Qed.
  
  Lemma wt_elab_clock:
    forall loc ack ck,
      elab_clock loc ack = OK ck ->
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
    forall ae e ck,
      elab_lexp ae = OK (e, ck) ->
      wt_lexp (PM.elements env) e.
  Proof.
    induction ae; intros e ck Helab; monadInv Helab;
      NamedDestructCases; try constructor; intros; subst;
      eauto using wt_lexp, find_type_In, assert_type_In.
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
  Qed.

  Lemma wc_elab_lexp:
    forall ae e ck,
      elab_lexp ae = OK (e, ck) ->
      clk_lexp cenv e ck.
  Proof.
    induction ae; intros e ck Helab; monadInv Helab;
      NamedDestructCases; try constructor; intros; subst;
      repeat match goal with
             | H:(_ ==b _) = true |- _ =>
               rewrite equiv_decb_equiv in H; rewrite H in *; clear H
             | H:find_clock _ _ = OK _ |- _ =>
               apply find_clock_clk_var in H
             end;
      eauto using clk_lexp.
  Qed.

  Lemma wt_elab_lexps:
    forall loc ck aes tys es,
      elab_lexps loc ck aes tys = OK es ->
      (Forall (wt_lexp (PM.elements env)) es
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
      Forall (fun e=>clk_lexp cenv e ck) es.
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
      wt_cexp (PM.elements env) e.
  Proof.
    induction ae; intros e ck Helab;
      apply bind_inversion in Helab;
      try (destruct Helab as ((le & ck') & Helab & Hexp);
           monadInv Hexp);
      eauto using wt_elab_lexp with dftyping.
    - specialize (IHae2 _ _ EQ); clear EQ.
      specialize (IHae3 _ _ EQ1); clear EQ1.
      NamedDestructCases.
      apply andb_prop in Heq; destruct Heq as (Hg1 & Hg2).
      rewrite equiv_decb_equiv in Hg1, Hg2.
      intros; subst.
      eauto using wt_elab_lexp with dftyping.
    - destruct Helab as (? & Haty & Helab).
      monadInv Helab. NamedDestructCases.
      specialize (IHae1 _ _ EQ1); clear EQ1.
      specialize (IHae2 _ _ EQ0); clear EQ0.
      rewrite equiv_decb_equiv in Heq.
      intro; subst.
      eauto using assert_type_In with dftyping.
  Qed.

  Lemma wc_elab_cexp:
    forall ae e ck,
      elab_cexp ae = OK (e, ck) ->
      clk_cexp cenv e ck.
  Proof.
    induction ae; simpl; intros e ck HH;
      repeat match goal with H:_ = OK _ |- _ => monadInv H end;
      NamedDestructCases; intros; subst;
      repeat match goal with
             | H:(_ ==b _) = true |- _ =>
               rewrite equiv_decb_equiv in H; rewrite H in *; clear H
             | H:find_clock _ _ = OK _ |- _ =>
               apply find_clock_clk_var in H
             end;
      eauto using clk_cexp, clk_lexp, wc_elab_lexp.
  Qed.

  Lemma check_result_list_Forall2:
    forall loc ck xs txs s,
      check_result_list loc ck xs txs = OK s ->
      Forall2 (fun x tx => In (x, tx) (PM.elements env)) xs txs
      /\ (forall x, PS.In x s <-> In x xs)
      /\ NoDup xs
      /\ Forall (fun x=>clk_var cenv x ck) xs.
    Proof.
    induction xs as [|x xs]; simpl.
    - repeat split; DestructCases; auto using NoDup_nil.
      now apply not_In_empty.
      contradiction.
    - intros txs s Hcheck.
      DestructCases.
      match goal with H:_ = OK _ |- _ => monadInv H end.
      NamedDestructCases.
      apply IHxs in EQ0.
      destruct EQ0 as (Hin & Hset & Hnodup & Hclk).
      apply mem_spec_false in Heq. rewrite Hset in Heq.
      apply assert_type_In in EQ.
      destruct x1. apply assert_clock_spec in EQ1.
      repeat split; eauto; try rewrite PS.add_spec, Hset;
        try destruct 1; eauto using NoDup.
    Qed.

  Lemma wt_elab_equation:
    forall aeq eq,
      elab_equation aeq = OK eq ->
      wt_equation G (PM.elements env) eq.
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
             | H:find_clock _ _ = OK _ |- _ => apply wt_find_clock in H
             | H:find_type _ _ = OK _ |- _ => apply find_type_In in H
             | H:assert_type _ _ _ = OK _ |- _ => apply assert_type_In in H
             | H:elab_cexp _ = OK _ |- _ => apply wt_elab_cexp in H
             | H:_ ==b _ = true |- _ => rewrite equiv_decb_equiv in H
             | H:check_result_list _ _ _ _ = OK ?x |- _ =>
               apply check_result_list_Forall2 in H;
                 destruct H as (Hele & Hins & Hnodup & Hcks)
             | _ => NamedDestructCases
             end; intros; subst; auto with dftyping.
    - unfold find_type_unop in EQ3. NamedDestructCases.
      rewrite type_unop'_correct in Heq1.
      auto with dftyping.
    - unfold find_type_binop in EQ5. NamedDestructCases.
      rewrite type_binop'_correct in Heq2.
      auto with dftyping.
    - apply andb_prop in Heq.
      destruct Heq as (Heq4 & Heq5).
      rewrite equiv_decb_equiv in Heq4, Heq5.
      auto with dftyping.
    - auto using type_castop with dftyping.
    - rename x1 into xin, x2 into xout, x3 into ein, xs into sxs, l0 into xs,
      x0 into ck, a into loc'.
      unfold find_node_interface in EQ0. NamedDestructCases.
      destruct EQ2.
      destruct wt_nenv as (wt_nenv' & ?).
      specialize (wt_nenv' (ident_of_camlstring s) _ _ Heq0).
      destruct wt_nenv' as (n & Hfind & Hin & Hout); clear wt_nenv.
      econstructor; eauto.
      + apply Forall2_map_1 in Hout.
        apply Forall2_eq in Hout.
        rewrite <-Hout in Hele.
        now apply Forall2_map_2 in Hele.
      + apply Forall2_map_1 with (f:=typeof) in H0.
        apply Forall2_eq in H0.
        rewrite <-H0 in Hin.
        apply Forall2_map_2, Forall2_swap_args in Hin.
        apply Forall2_impl_In with (2:=Hin).
        intros ** Htypeof. now rewrite Htypeof.
  Qed.

  Lemma Well_clocked_elab_equation:
    forall aeq eq,
      elab_equation aeq = OK eq ->
      Well_clocked_eq cenv eq.
  Proof.
    intros aeq eq Helab.
    destruct aeq as ((xs & ae) & loc).
    destruct ae; simpl in Helab;
      repeat progress
             match goal with
             | H:bind _ _ = _ |- _ => monadInv H
             | H:bind2 _ _ = _ |- _ => monadInv H
             | H:elab_lexp _ = OK _ |- _ => apply wc_elab_lexp in H
             | H:elab_lexps _ _ _ _ = OK _ |- _ => apply wc_elab_lexps in H
             | H:find_clock _ _ = OK _ |- _ => apply find_clock_clk_var in H
             | H:elab_cexp _ = OK _ |- _ => apply wc_elab_cexp in H
             | H:_ ==b _ = true |- _ => rewrite equiv_decb_equiv in H
             | H:equiv _ _ |- _ => rewrite <-H in *; clear H
             | H:equiv _ _ |- _ => rewrite H in *; clear H
             | H:check_result_list _ _ _ _ = OK ?x |- _ =>
               apply check_result_list_Forall2 in H;
                 destruct H as (Hele & Hins & Hnodup & Hcks)
             | _ => NamedDestructCases
             end; intros; subst;
        auto using Well_clocked_eq, clk_cexp, clk_lexp with dftyping.
  Qed.

  Fixpoint check_clock (loc: astloc) (ck: clock) : res unit :=
    match ck with
    | Cbase => OK tt
    | Con ck x b =>
      do ok <- check_clock loc ck;
      do xck <- find_clock loc x;
      if xck ==b ck then OK tt
      else Error (err_loc loc ((MSG "badly-formed clock "
                                    :: msg_of_clocks xck ck)))
    end.
  
  Lemma check_clock_spec:
    forall loc ck,
      check_clock loc ck = OK tt ->
      clk_clock cenv ck.
  Proof.
    induction ck; simpl; intro HH; auto using clk_clock.
    monadInv HH; NamedDestructCases.
    apply find_clock_clk_var in EQ1.
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

  Fixpoint elab_var_decls' (acc: list (ident * type) * PM.t type)
           (vds: list (string * type_name * Ast.clock * astloc))
    : res (list (ident * type) * PM.t type) :=
    match vds with
    | nil => OK acc
    | vd::vds =>
      let (rs, tyenv) := acc in
      let '(sx, sty, sck, loc) := vd in
      let x := ident_of_camlstring sx in
      let ty := elab_type loc sty in
      if PM.mem x tyenv
      then Error (err_loc loc (CTX x :: msg " is declared more than once"))
      else elab_var_decls' ((x, ty)::rs, PM.add x ty tyenv) vds
    end.

  Definition elab_var_decls (tyenv: PM.t type)
             (vds: list (string * type_name * Ast.clock * astloc))
    : res (list (ident * type) * PM.t type) :=
    elab_var_decls' ([], tyenv) vds.
  
  Lemma elab_var_decls_spec:
    forall ys xs tyenv tyenv',
      elab_var_decls tyenv ys = OK (xs, tyenv') ->
      NoDupMembers xs
      /\ (forall x ty, PM.find x tyenv = Some ty -> PM.find x tyenv' = Some ty)
      /\ (forall x ty, In (x, ty) xs \/ PM.find x tyenv = Some ty
                       <-> PM.find x tyenv' = Some ty)
      /\ (forall x ty, In (x, ty) xs -> ~PM.In x tyenv).
  Proof.
    unfold elab_var_decls.
    cut (forall ys xs tyenv xs' tyenv',
            elab_var_decls' (xs, tyenv) ys = OK (xs', tyenv') ->
            NoDupMembers xs ->
            (forall x, ~PM.In x tyenv -> ~InMembers x xs) ->
            (forall x ty, In (x, ty) xs -> PM.find x tyenv = Some ty) ->
            NoDupMembers xs'
            /\ incl xs xs'
            /\ (forall x ty, PM.find x tyenv = Some ty -> PM.find x tyenv' = Some ty)
            /\ (forall x ty, In (x, ty) xs' \/ PM.find x tyenv = Some ty
                             <-> PM.find x tyenv' = Some ty)
            /\ (forall x ty, In (x, ty) xs' ->
                             In (x, ty) xs \/ ~PM.In x tyenv)).
    { intros HH ys xs tyenv tyenv' Helab.
      specialize (HH ys nil tyenv xs tyenv' Helab NoDupMembers_nil).
      destruct HH as (HH1 & HH2 & HH3 & HH4 & HH5); intuition.
      match goal with H:In _ xs |- _ => apply HH5 in H; destruct H; auto end. }
    induction ys as [|y ys IH]; intros ** Helab Hnodup Hnin Hin.
    now simpl in Helab; monadInv1 Helab; intuition.
    simpl in Helab.
    destruct y as [[[sx sty] ?] loc].
    NamedDestructCases.
    rewrite PM.mem_find in Heq.
    destruct (PM.find (ident_of_camlstring sx) tyenv) eqn:Hnfind;
      try discriminate; clear Heq.
    assert (~InMembers (ident_of_camlstring sx) xs) as Hnxs.
    { apply Hnin. intro Hmin.
      apply PM_In_find' in Hmin.
      contradiction. }
    assert (NoDupMembers ((ident_of_camlstring sx, elab_type loc sty) :: xs))
      as Hnodup' by auto using NoDupMembers_cons.
    apply IH in Helab; clear IH; auto.
    - destruct Helab as (IH1 & IH2 & IH3 & IH4 & IH5).
      apply incl_cons' in IH2.
      destruct IH2 as [Hsxs' Hincl].
      split; auto.
      split; auto.
      split; [|split].
      + intros x ty Hfind.
        apply IH3.
        rewrite PM.gso; auto.
        intro Hsx; rewrite Hsx in Hfind.
        rewrite Hnfind in Hfind.
        discriminate Hfind.
      + intros x ty.
        split; intro HH.
        * destruct HH as [|HH].
          now apply IH4; left; auto.
          apply IH3.
          rewrite PM.gso; auto.
          intro; subst.
          rewrite Hnfind in HH.
          discriminate HH.
        * apply IH4 in HH.
          destruct HH as [|HH]; auto.
          destruct (ident_eq_dec (ident_of_camlstring sx) x) as [He|Hne].
          2: now rewrite PM.gso in HH; auto.
          subst. rewrite PM.gss in HH.
          inv HH. left; auto.
      + intros x ty Hixs.
        apply IH5 in Hixs.
        destruct Hixs as [Hixs|Hixs].
        * destruct Hixs as [He|]; auto.
          inv He. rewrite PM_In_find', Hnfind.
          intuition.
        * rewrite PM_add_spec in Hixs.
          apply Decidable.not_or in Hixs.
          intuition.
    - intros x Hnin'.
      rewrite PM_add_spec in Hnin'.
      apply Decidable.not_or in Hnin'.
      destruct Hnin' as (Hnsx & Hnin').
      apply Hnin in Hnin'.
      inversion_clear 1; now intuition.
    - intros x ty Hin'.
      apply in_inv in Hin'.
      destruct Hin' as [He|Hin'].
      now inv He; rewrite PM.gss.
      destruct (ident_eq_dec x (ident_of_camlstring sx)) as [He|Hne].
      2:now rewrite PM.gso; auto.
      subst. inversion_clear Hnodup' as [|? ? ? Hnim Hnodm].
      apply NotInMembers_NotIn with (b:=ty) in Hnim.
      contradiction.
  Qed.

  Lemma elab_var_decls_chained:
    forall ys0 ys1 xs0 xs1 tyenv0 tyenv1 tyenv2,
      elab_var_decls tyenv0 ys0 = OK (xs0, tyenv1) ->
      elab_var_decls tyenv1 ys1 = OK (xs1, tyenv2) ->
      NoDupMembers (xs1 ++ xs0)
      /\ (forall x ty, PM.find x tyenv0 = Some ty
                       -> PM.find x tyenv2 = Some ty)
      /\ (forall x ty, In (x, ty) (xs1 ++ xs0)
                       \/ PM.find x tyenv0 = Some ty
                       <-> PM.find x tyenv2 = Some ty)
      /\ (forall x ty, In (x, ty) (xs1 ++ xs0) -> ~PM.In x tyenv0).
  Proof.
    intros ** Helab0 Helab1.
    apply elab_var_decls_spec in Helab0.
    apply elab_var_decls_spec in Helab1.
    destruct Helab0 as (Hnd0 & Hf0 & Hf0' & Hni0).
    destruct Helab1 as (Hnd1 & Hf1 & Hf1' & Hni1).
    repeat split; auto.
    - apply NoDupMembers_app; auto.
      intros x Hinm1 Hinm0.
      apply InMembers_In in Hinm1. destruct Hinm1 as (tx1 & Hinm1).
      apply Hni1 in Hinm1. rewrite PM_In_find in Hinm1.
      apply Hinm1.
      apply InMembers_In in Hinm0. destruct Hinm0 as (tx0 & Hinm0).
      assert (PM.find x tyenv1 = Some tx0) as Hinm1'
          by (apply Hf0'; now left).
      eauto.
    - destruct (Hf1' x ty).
      destruct 1 as [HH|HH]; auto.
      destruct (Hf0' x ty).
      apply in_app in HH; destruct HH; auto.
    - intro HH. apply Hf1' in HH.
      rewrite in_app.
      destruct HH as [|HH]; auto.
      apply Hf0' in HH.
      destruct HH; auto.
    - intros x ty HH.
      apply in_app in HH.
      destruct HH as [HH|HH]; eauto.
      apply Hni1 in HH.
      intro Hf. rewrite PM_In_find in Hf.
      destruct Hf as (v & Hf).
      apply Hf0 in Hf.
      rewrite PM_In_find' in HH.
      apply HH. rewrite Hf.
      discriminate.
  Qed.

  Lemma elab_var_decls_2chained_nodup:
    forall ys0 ys1 ys2 xs0 xs1 xs2 tyenv0 tyenv1 tyenv2 tyenv3,
      elab_var_decls tyenv0 ys0 = OK (xs0, tyenv1) ->
      elab_var_decls tyenv1 ys1 = OK (xs1, tyenv2) ->
      elab_var_decls tyenv2 ys2 = OK (xs2, tyenv3) ->
      NoDupMembers (xs2 ++ xs1 ++ xs0).
  Proof.
    intros ** Helab0 Helab1 Helab2.
    apply elab_var_decls_chained with (1:=Helab0) in Helab1. clear Helab0.
    apply elab_var_decls_spec in Helab2.
    destruct Helab1 as (Hnd1 & Hf1 & Hf1' & Hni1).
    destruct Helab2 as (Hnd2 & Hf2 & Hf2' & Hni2).
    apply NoDupMembers_app; auto.
    intros x Hin2 Hin1_0.
    apply InMembers_In in Hin2.
    destruct Hin2 as (tx & Hin2).
    apply Hni2 in Hin2.
    apply Hin2. rewrite PM_In_find.
    apply InMembers_In in Hin1_0.
    destruct Hin1_0 as (xt & Hin1_0).
    eapply or_introl in Hin1_0.
    apply Hf1' in Hin1_0.
    eauto.
  Qed.

  Lemma elab_var_decls_2chained_perm:
    forall ys0 ys1 ys2 xs0 xs1 xs2 tyenv1 tyenv2 tyenv3,
      elab_var_decls (PM.empty type) ys0 = OK (xs0, tyenv1) ->
      elab_var_decls tyenv1 ys1 = OK (xs1, tyenv2) ->
      elab_var_decls tyenv2 ys2 = OK (xs2, tyenv3) ->
      Permutation.Permutation (PM.elements tyenv3) (xs2 ++ xs1 ++ xs0).
  Proof.
    intros ** Helab0 Helab1 Helab2.
    pose proof (elab_var_decls_2chained_nodup _ _ _ _ _ _ _ _ _ _
                                              Helab0 Helab1 Helab2) as Hnodup.
    apply Permutation.NoDup_Permutation;
      auto using NoDupMembers_NoDup, NoDupMembers_PM_elements.
    apply elab_var_decls_chained with (1:=Helab0) in Helab1. clear Helab0.
    apply elab_var_decls_spec in Helab2.
    destruct Helab1 as (Hnd1 & Hf1 & Hf1' & Hni1).
    destruct Helab2 as (Hnd2 & Hf2 & Hf2' & Hni2).
    destruct x as (x & xt).      
    split; intro HH.
    - apply PM.elements_complete in HH.
      apply Hf2' in HH.
      rewrite in_app.
      destruct HH as [|HH]; auto.
      apply Hf1' in HH.
      destruct HH as [|HH]; auto.
      rewrite PM.gempty in HH.
      discriminate.
    - apply PM.elements_correct.
      apply Hf2'.
      apply in_app in HH.
      destruct HH; auto.
      right; apply Hf1'; auto.
  Qed.

  Fixpoint check_vars {A} (loc: astloc) (defd: PM.t A) (xs: idents)
                                                         : res (PM.t A) :=
    match xs with
    | nil => OK defd
    | x::xs => if PM.mem x defd
               then check_vars loc (PM.remove x defd) xs
               else Error (err_loc loc
                                   (CTX x :: msg " is improperly defined"))
    end.

  Lemma check_vars_spec:
    forall {A} loc xs (defd: PM.t A) s,
      check_vars loc defd xs = OK s ->
      (forall x, PM.In x s -> ~In x xs)
      /\ (forall x, In x xs -> ~PM.In x s)
      /\ (forall x, PM.In x defd <-> In x xs \/ PM.In x s)
      /\ NoDup xs.
  Proof.
    induction xs as [|x xs]; simpl.
    - intros. DestructCases. intuition. apply NoDup_nil.
    - intros defd s Hchk.
      NamedDestructCases. apply PM.mem_2 in Heq.
      specialize (IHxs _ _ Hchk); clear Hchk;
        destruct IHxs as (IH1 & IH2 & IH3 & IH4).
      repeat split.
      + intros y HH.
        specialize (IH2 y).
        destruct 1; intuition.
        subst.
        assert (PM.In y (PM.remove y defd)) as Hir
            by (apply IH3; intuition).
        rewrite PM_remove_iff in Hir; intuition.
      + intros y.
        specialize (IH2 y).
        destruct 1 as [HH|HH]; intuition.
        subst.
        assert (PM.In y (PM.remove y defd)) as Hir
            by (apply IH3; intuition).
        rewrite PM_remove_iff in Hir; intuition.
      + rename x0 into y. intros HH.
        destruct (ident_eq_dec x y).
        now intuition.
        assert (PM.In y (PM.remove x defd)) as Hir
            by (apply PM_remove_iff; split; auto).
        apply IH3 in Hir. intuition.
      + rename x0 into y.
        destruct 1 as [[HH|HH]|HH]; subst; auto.
        * assert (PM.In y (PM.remove x defd)) as Hir
              by (apply IH3; intuition).
          rewrite PM_remove_iff in Hir; intuition.
        * assert (PM.In y (PM.remove x defd)) as Hir
              by (apply IH3; intuition).
          rewrite PM_remove_iff in Hir; intuition.
      + constructor; auto.
        intro HH.
        assert (PM.In x (PM.remove x defd)) as Hir
            by (apply IH3; intuition).
        rewrite PM_remove_iff in Hir. intuition.
  Qed.

  Fixpoint check_defined {A} (loc: astloc) (out: PM.t A) (defd: PM.t A)
           (eqs: list equation) : res unit :=
    match eqs with
    | nil => if PM.is_empty defd then OK tt
             else Error (err_loc loc
                     (MSG "some variables are not defined:"
                          :: concatMap (fun xv => [MSG " "; CTX (fst xv)])
                                       (PM.elements defd)))
    | EqFby x _ _ _::eqs => if PM.mem x defd && (negb (PM.mem x out))
                            then check_defined loc out (PM.remove x defd) eqs
                            else Error (err_loc loc
                                        (CTX x :: msg " is improperly defined"))
    | EqDef x _ _::eqs => if PM.mem x defd
                          then check_defined loc out (PM.remove x defd) eqs
                          else Error (err_loc loc
                                        (CTX x :: msg " is improperly defined"))
    | EqApp xs _ _ _::eqs => do defd' <- check_vars loc defd xs;
                             check_defined loc out defd' eqs
    end.
  
  Lemma check_defined_spec:
    forall {A} eqs loc (out: PM.t A) defd,
      check_defined loc out defd eqs = OK tt ->
      (forall x, In x (vars_defined eqs) <-> PM.In x defd)
      /\ NoDup (concat (map var_defined eqs))
      /\ (forall x, In x (vars_defined (filter is_fby eqs))
                    -> ~PM.In x out).
  Proof.
    induction eqs as [|eq eqs IH]; simpl; intros loc out defd Hchk;
      NamedDestructCases.
    - apply PM.is_empty_2 in Heq.
      rewrite PM.Empty_alt in Heq.
      setoid_rewrite PM_In_find.
      repeat split.
      + inversion 1.
      + destruct 1 as (v, HH).
        now rewrite (Heq x) in HH.
      + apply NoDup_nil.
      + inversion 1.
    - apply PM.mem_2 in Heq0. simpl.
      specialize (IH _ _ _ Hchk); clear Hchk.
      destruct IH as (IH1 & IH2 & IH3).
      repeat split.
      + destruct 1 as [|HH].
        now subst x.
        rewrite IH1, PM_remove_iff in HH.
        intuition.
      + intro Hxdef.
        destruct (var_defined eq ==b [x]) eqn:Heq1;
          rewrite Heq in Heq1; simpl in Heq1.
        rewrite equiv_decb_equiv in Heq1; injection Heq1; auto.
        rewrite not_equiv_decb_equiv in Heq1.
        right. apply IH1. apply PM_remove_iff; split; auto.
        intro HH; apply Heq1. now subst.
      + constructor; auto.
        rewrite IH1, PM_remove_iff.
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
    - rewrite Bool.andb_true_iff, Bool.negb_true_iff, PM_mem_spec_false in Heq0.
      destruct Heq0 as (Hidef & Hniout).
      apply PM.mem_2 in Hidef. simpl.
      specialize (IH _ _ _ Hchk); clear Hchk.
      destruct IH as (IH1 & IH2 & IH3).
      repeat split.
      + destruct 1 as [|HH].
        now subst x.
        rewrite IH1, PM_remove_iff in HH.
        intuition.
      + intro Hxdef.
        destruct (var_defined eq ==b [x]) eqn:Heq1;
          rewrite Heq in Heq1; simpl in Heq1.
        rewrite equiv_decb_equiv in Heq1; injection Heq1; auto.
        rewrite not_equiv_decb_equiv in Heq1.
        right. apply IH1. apply PM_remove_iff; split; auto.
        intro HH; apply Heq1. now subst.
      + constructor; auto.
        rewrite IH1, PM_remove_iff.
        intuition.
      + intros x Hvd.
        destruct Hvd as [Hvd|]; subst; auto.
  Qed.

  Fixpoint elab_clock_decl (tyenv: PM.t type) (acc: PM.t clock)
           (vds: list (string * type_name * Ast.clock * astloc))
    : res (PM.t clock) :=
    match vds with
    | nil => OK acc
    | vd::vds =>
      let '(sx, sty, sck, loc) := vd in
      let x := ident_of_camlstring sx in
      do ck <- elab_clock tyenv loc sck;
        elab_clock_decl tyenv (PM.add x ck acc) vds
    end.

  Lemma elab_clock_decl_spec:
    forall vds tyenv clkenv clkenv',
      elab_clock_decl tyenv clkenv vds = OK clkenv' ->
      (forall x ck, PM.find x clkenv = Some ck
                    -> wt_clock (PM.elements tyenv) ck) ->
      (forall x ck, PM.find x clkenv' = Some ck
                    -> wt_clock (PM.elements tyenv) ck).
  Proof.
    induction vds as [|vd vds IH];
      intros ** Helab Hclkenv x ck Hfind.
    - simpl in Helab. monadInv1 Helab. eauto.
    - simpl in Helab. destruct vd as (((? & ?) & ?) & ?).
      monadInv Helab.
      match goal with H:elab_clock _ _ _ = OK ?x |- _ =>
                      apply wt_elab_clock in H; rename H into WTx; rename x into ck' end.
      match goal with H:elab_clock_decl _ _ _ = OK _ |- _ =>
                      specialize (IH _ _ _ H) end.
      revert Hfind; apply IH.
      intros y yck Hfind.
      destruct (ident_eq_dec y (ident_of_camlstring s)).
      2:rewrite PM.gso in Hfind; now eauto.
      subst y. rewrite PM.gss in Hfind.
      injection Hfind; intro HH; rewrite HH in *.
      assumption.
  Qed.

  Fixpoint check_clock_env' (loc: astloc) (cenv: PM.t clock)
             (xcks: list (positive * clock)) : res unit :=
    match xcks with
    | [] => OK tt
    | (x, ck)::xcks =>
      do ok <- check_clock cenv loc ck;
      do xck <- find_clock cenv loc x;
      if (ck ==b xck) then check_clock_env' loc cenv xcks
      else Error (err_loc loc (CTX x :: MSG " has an ill-formed clock "
                                   :: msg_of_clocks xck ck))
    end.

  Lemma check_clock_env'_spec : forall loc cenv ckl,
    check_clock_env' loc cenv ckl = OK tt -> Forall (fun x_ck => clk_clock cenv (snd x_ck)) ckl.
  Proof.
    intros loc cenv ckl Hckl. induction ckl as [| [x ck] ckl]; simpl in *.
    + constructor.
    + rewrite Forall_forall.
      monadInv1 Hckl. match goal with x : unit |- _ => destruct x end.
      intros [x' ck'] Hin.
      match goal with H : find_clock cenv loc x = OK ?y |- _ => rename y into ck'' end.
      unfold find_clock in *. destruct (PM.find x cenv); inv EQ1; [].
      unfold equiv_decb in EQ2. destruct (equiv_dec ck ck'') as [Heq | Heq]; inv EQ2; [].
      clear Heq ck''. destruct Hin as [Hin | Hin].
      - rewrite <- Hin. clear Hin x' ck'.
        eauto using check_clock_spec.
      - rewrite Forall_forall in IHckl. now apply IHckl.
  Qed.

  Definition check_clock_env (loc: astloc) (cenv: PM.t clock) : res unit :=
    check_clock_env' loc cenv (PM.elements cenv).

  Lemma check_clock_env_spec:
    forall loc cenv,
      check_clock_env loc cenv = OK tt ->
      Well_clocked_env cenv.
  Proof.
    unfold check_clock_env.
    intros loc cenv Hcheck x ck Hin.
    apply check_clock_env'_spec in Hcheck. rewrite Forall_forall in Hcheck.
    apply (Hcheck (x, ck)). now apply PM.elements_correct.
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
    let Helab_locals := fresh "Helab_locals" in
    let Helab_in := fresh "Helab_in" in
    let Hclk_out := fresh "Hclk_out" in
    let Hclk_locals := fresh "Hclk_locals" in
    let Hclk_in := fresh "Hclk_in" in
    let clkenv_out := fresh "clkenv_out" in
    let clkenv_locals := fresh "clkenv_locals" in
    let clkenv := fresh "clkenv" in
    let Helabs := fresh "Helabs" in
    let eqs := fresh "eqs'" in
    let Hdefd := fresh "Hdefd" in
    let Houtin := fresh "Houtin" in
    let Hcksin := fresh "Hcksin" in
    let Hcksout := fresh "Hcksout" in
    let WCenv := fresh "WCenv" in
    match goal with H:elab_var_decls _ outputs = OK ?x |- _ =>
      rename H into Helab_out; destruct x as (xout & tyenv_out) end;
    match goal with H:elab_var_decls _ locals = OK ?x |- _ =>
      rename H into Helab_locals; destruct x as (xlocals & tyenv_locals) end;
    match goal with H:elab_var_decls _ inputs = OK ?x |- _ =>
      rename H into Helab_in; destruct x as (xin & tyenv_in) end;
    match goal with H:elab_clock_decl _ _ outputs = OK ?x |- _ =>
      rename H into Hclk_out; rename x into clkenv_out end;
    match goal with H:elab_clock_decl _ _ locals = OK ?x |- _ =>
      rename H into Hclk_locals; rename x into clkenv_locals end;
    match goal with H:elab_clock_decl _ _ inputs = OK ?x |- _ =>
      rename H into Hclk_in; rename x into clkenv end;
    match goal with H:mmap (elab_equation _ _ _) _ = OK ?x |- _ =>
      rename H into Helabs; rename x into eqs end;
    match goal with H:check_defined _ _ _ _ = OK ?x |- _ =>
      rename H into Hdefd; destruct x end;
    match goal with H:check_clock_env _ _ = OK ?x |- _ =>
      rename H into WCenv; destruct x; apply check_clock_env_spec in WCenv end;
    match goal with H1:assert_clocks _ _ _ _ = OK ?r1,
                    H2:assert_clocks _ _ _ _ = OK ?r2 |- _ =>
      rename H1 into Hcksin, H2 into Hcksout;
      destruct r1, r2;              
      apply assert_clocks_spec in Hcksin;
      apply assert_clocks_spec in Hcksout end;
    try match goal with H:In _ (map fst _) |- _ =>
      rename H into Houtin end.
  
  Local Hint Resolve NoDupMembers_nil NoDup_nil.

  Program Definition elab_declaration (decl: Ast.declaration)
    : res {n | wt_node G n /\ Well_clocked_node n} :=
    match decl with
    | NODE name inputs outputs locals equations loc =>
      match (do xout   <- elab_var_decls (PM.empty type) outputs;
             do xlocal <- elab_var_decls (snd xout) locals;
             do xin    <- elab_var_decls (snd xlocal) inputs;
             OK (fst xout, fst xlocal, fst xin,
                 snd xout, snd xlocal, snd xin)) with
      | Error e => Error e
      | OK (xout, xlocal, xin, sout, svars, tyenv) =>
        match (do env1  <- elab_clock_decl tyenv (PM.empty clock) inputs;
               do env2  <- elab_clock_decl tyenv env1 outputs;
               do ckenv <- elab_clock_decl tyenv env2 locals;
               do ok <- check_clock_env loc ckenv;
               do ok <- assert_clocks ckenv loc Cbase (map fst xin);
               do ok <- assert_clocks ckenv loc Cbase (map fst xout);
               do eqs <- mmap (elab_equation tyenv ckenv nenv) equations;
               do ok <- check_defined loc sout svars eqs;
               if existsb (fun x=>PM.mem x tyenv) Ident.Ids.reserved
               then Error (err_loc loc (msg "illegal variable name"))
               else if (length xin ==b 0) || (length xout ==b 0)
                    then Error (err_loc loc (msg "not enough inputs or outputs"))
                    else OK eqs) with
        | Error e => Error e
        | OK eqs => OK {| n_name  := ident_of_camlstring name;
                          n_in    := xin;
                          n_out   := xout;
                          n_vars  := xlocal;
                          n_eqs   := eqs;
                          n_ingt0 := _;
                          n_outgt0:= _;
                          n_defd  := _;
                          n_vout  := _;
                          n_nodup := _;
                          n_good  := _ |}
        end
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
    (* Permutation (map var_defined eqs) (map fst (xlocal ++ [(i, t)])) *)
    MassageElabs outputs locals inputs.
    simpl in *.
    apply check_defined_spec in Hdefd.
    destruct Hdefd as (Hdefd & Hnodup & Hnfby).
    destruct (elab_var_decls_chained _ _ _ _ _ _ _ Helab_out Helab_locals)
      as (Hnodup' & Helab_l1 & Helab_l2 & Helab_l3).
    apply Permutation.NoDup_Permutation; auto.
    now apply fst_NoDupMembers; auto.
    intros. rewrite Hdefd, PM_In_find, <-fst_InMembers.
    split; intro HH.
    - destruct HH as (ty & HH).
      apply Helab_l2 in HH.
      rewrite PM.gempty in HH.
      destruct HH as [HH|]; try discriminate.
      now apply In_InMembers in HH.
    - apply InMembers_In in HH.
      destruct HH as (tx & HH).
      exists tx.
      apply Helab_l2; auto.
  Qed.
  Next Obligation.
    (* ~ In i (map var_defined (filter is_fby eqs)) *)
    MassageElabs outputs locals inputs.
    simpl in *.
    apply check_defined_spec in Hdefd.
    destruct Hdefd as (Hdefd & Hnodup & Hnfby).
    intros Hi. apply Hnfby in Hi. apply Hi.
    apply elab_var_decls_spec in Helab_out.
    destruct Helab_out as (Heo1 & Heo2 & Heo3 & Heo4).
    apply fst_InMembers, InMembers_In in Houtin.
    destruct Houtin as (ty & Houtin).
    rewrite PM_In_find. exists ty.
    apply Heo3. auto with datatypes.
  Qed.
  Next Obligation.
    (* NoDupMembers (xin ++ xlocal ++ [(i, t)]) *)
    MassageElabs outputs local inputs.
    apply (elab_var_decls_2chained_nodup _ _ _ _ _ _ _ _ _ _
                                         Helab_out Helab_locals Helab_in).
  Qed.
  Next Obligation.
    (* Forall NotReserved (xin ++ xlocal ++ [(i, t)]) *)
    MassageElabs outputs locals inputs.
    simpl in *.
    rewrite 2 Bool.orb_false_iff in Hb.
    destruct Hb as (Hb1 & Hb2 & ?).
    rewrite PM_mem_spec_false in Hb1, Hb2.
    pose proof (elab_var_decls_2chained_perm
                  _ _ _ _ _ _ _ _ _ Helab_out Helab_locals Helab_in) as Hperm.
    rewrite <-Hperm.
    apply all_In_Forall.
    intros xtx Hin Hir.
    destruct xtx as (x, tx).
    apply PM.elements_complete in Hin.
    simpl in Hir.
    assert (PM.In x tyenv_in) as Hintyenv
        by (apply PM_In_find; eauto).
    repeat destruct Hir as [Hir|Hir];
      try contradiction;
      subst x; auto.
  Qed.
  Next Obligation.
    split.
    - (* wt_node G n *)
      unfold wt_node. simpl.
      repeat match goal with H:OK _ = _ |- _ => symmetry in H; monadInv1 H end.
      NamedDestructCases.
      MassageElabs outputs locals inputs.
      simpl in *.
      cut (Forall (wt_equation G (PM.elements tyenv_in)) eqs').
      + apply Forall_impl_In.
        intros.
        now rewrite <-(elab_var_decls_2chained_perm _ _ _ _ _ _ _ _ _
                                              Helab_out Helab_locals Helab_in).
      + apply mmap_inversion in Helabs.
        apply Forall_forall.
        intros y Hin.
        eapply Coqlib.list_forall2_in_right with (1:=Helabs) in Hin.
        destruct Hin as (aeq & Hin & Helab).
        apply wt_elab_equation with (G:=G) in Helab; auto.
        intros x ck Hfind.
        apply elab_clock_decl_spec with (1:=Hclk_locals) (x:=x); auto.
        apply elab_clock_decl_spec with (1:=Hclk_out).
        apply elab_clock_decl_spec with (1:=Hclk_in).
        intros ** Hnfind.
        rewrite PM.gempty in Hnfind.
        discriminate.
    - (* Well_clocked_node n *)
      cut (exists cenv,
              Forall (Well_clocked_eq cenv) eqs
              /\ clk_vars cenv (map fst xin) Cbase
              /\ clk_vars cenv (map fst xout) Cbase
              /\ Well_clocked_env cenv).
      now (destruct 1 as (cenv & WCeqs & WCin & WCout & Wcenv);
           eauto using Well_clocked_node).
      repeat match goal with H:OK _ = _ |- _ => symmetry in H; monadInv1 H end.
      NamedDestructCases.
      MassageElabs outputs locals inputs.
      simpl in *.
      exists clkenv_locals; repeat split; auto.
      apply mmap_inversion in Helabs.
      apply Forall_forall.
      intros y Hin.
      eapply Coqlib.list_forall2_in_right with (1:=Helabs) in Hin.
      destruct Hin as (aeq & Hin & Helab).
      now apply Well_clocked_elab_equation in Helab.
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
        (WTG: wt_global G /\ Well_clocked G) (Hnenv: Is_interface_map G nenv)
        (decls: list Ast.declaration)
  : res {G' | wt_global G' /\ Well_clocked G'} :=
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
                                         (map snd n.(n_in),
                                          map snd n.(n_out)) nenv) _ _ ds
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
      * match goal with |- Forall2 ?P _ _ =>
          change (Forall2 P n.(n_out) (map snd n.(n_out))) end.
        apply Forall2_swap_args, Forall2_map_1, Forall2_same, all_In_Forall;
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

Definition elab_declarations (decls: list Ast.declaration)
  : res {G | wt_global G /\ Well_clocked G} :=
  elab_declarations' [] (PM.empty (list type * list type))
                     (conj wtg_nil Well_clocked_nil)
                     Is_interface_map_empty decls.

