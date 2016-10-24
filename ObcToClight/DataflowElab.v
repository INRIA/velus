Require Import Rustre.Common.
Require Import Rustre.Operators.

Require Import Rustre.Dataflow.
Require Import Rustre.Dataflow.Parser.Ast.

Require Import Rustre.ObcToClight.Interface.
Require Import Rustre.Ident.

Module Export OpAux := OperatorsAux Interface.Op.

(* TODO: Tidy this up. Should just instantiate a Dataflow module to get
         everything. *)
Module Export Syn := SyntaxFun Ident.Ids Interface.Op.
Module Export Mems := MemoriesFun Ident.Ids Interface.Op Syn.
Module Export Defs := IsDefined Ident.Ids Interface.Op Syn Mems.

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

    (* Map variable names to types. *)
    Variable env : PM.t type.

    (* Map variable names to clocks. *)
    Variable cenv : PM.t clock.

    (* Preceding dataflow program. *)
    Variable G : global.

    (* Map node names to input and output types. *)
    Variable nenv : PM.t (list type * list type).

    Hypothesis wt_cenv :
      forall x ck, PM.find x cenv = Some ck -> wt_clock (PM.elements env) ck.

    Hypothesis wt_nenv :
      forall f n tysin tysout,
        PM.find f nenv = Some (tysin, tysout) ->
        (find_node f G = Some n
         /\ Forall2 (fun i ty=> snd i = ty) n.(n_in) tysin
         /\ Forall2 (fun i ty=> snd i = ty) [n.(n_out)] tysout).

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

    Definition find_clock (loc: astloc) (x: ident) : res clock :=
      match PM.find x cenv with
      | None => Error (err_loc loc (CTX x :: msg " is not declared."))
      | Some ck => OK ck
      end.

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

    Fixpoint elab_cexp (ae: Ast.expression) : res cexp :=
      match ae with
      | MERGE sx aet aef loc =>
        let x := ident_of_string sx in
        do ok <- assert_type loc x bool_type;
        do et <- elab_cexp aet;
        do ef <- elab_cexp aef;
           if typeofc et ==b typeofc ef
           then OK (Emerge x et ef)
           else Error (err_loc loc (msg "badly typed merge"))
      | IFTE ae aet aef loc =>
        do e <- elab_lexp ae;
        do et <- elab_cexp aet;
        do ef <- elab_cexp aef;
           if (typeof e ==b bool_type) && (typeofc et ==b typeofc ef)
           then OK (Eite e et ef)
           else Error (err_loc loc (msg "badly typed if/then/else"))
      | _ =>
        do e <- elab_lexp ae;
           OK (Eexp e)
      end.

    Definition assert_lexp_type (loc: astloc) (e: lexp) (ty: type) : res unit :=
      if typeof e ==b ty then OK tt
      else Error (err_loc loc (MSG "badly typed argument; expected "
                                :: msg (string_of_type ty))).

    Fixpoint elab_lexps (loc: astloc) (aes: list expression) (tys: list type)
                                                            : res (list lexp) :=
      match aes, tys with
      | nil, nil => OK nil
      | ae::aes, ty::tys =>
          do e <- elab_lexp ae;
          do ok <- assert_lexp_type (expression_loc ae) e ty;
          do es <- elab_lexps loc aes tys;
             OK (e::es)
      | _, _ => Error (err_loc loc (msg "wrong number of arguments"))
      end.

    Fixpoint check_lists {A B} (loc: astloc) (f : A -> B -> res unit)
                               (xs: list A) (ys: list B) : res unit :=
      match xs, ys with
      | nil, nil => OK tt
      | x::xs, y::ys => do ok <- f x y; check_lists loc f xs ys
      | _, _ => Error (err_loc loc (msg "wrong number of arguments"))
      end.

    Definition elab_equation (aeq: Ast.equation) : res equation :=
      let '(sxs, ae, loc) := aeq in
      do x <- match sxs with
              | [sx] => OK (ident_of_string sx)
              | _ => Error (err_loc loc
                               (msg "multiple outputs not currently supported"))
              end;
      do ck <- find_clock loc x;
      match ae with
      | CALL sf aes loc =>
        let f := ident_of_string sf in
        do (tysin, tysout) <- find_node_interface loc f;
        do es <- elab_lexps loc aes tysin;
        do ok <- check_lists loc (assert_type loc) [x] tysout;
        OK (EqApp x ck f es)

      | FBY av0 ae loc =>
        let v0 := elab_constant loc av0 in
        let v0ty := type_const v0 in
        do e <- elab_lexp ae;
        do ok <- assert_type loc x v0ty;
           if typeof e ==b v0ty
           then OK (EqFby x ck v0 e)
           else Error (err_loc loc (msg "badly typed fby"))

      | _ =>
        do e <- elab_cexp ae;
        do ok <- assert_type loc x (typeofc e);
           OK (EqDef x ck e)
      end.

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
      forall ae e,
        elab_lexp ae = OK e ->
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

    Lemma wt_elab_cexp:
      forall ae e,
        elab_cexp ae = OK e ->
        wt_cexp (PM.elements env) e.
    Proof.
      induction ae; intros e Helab.
      - apply bind_inversion in Helab.
        destruct Helab as (le & Helab & Hexp).
        monadInv Hexp. eauto using wt_elab_lexp with dftyping.
      - apply bind_inversion in Helab.
        destruct Helab as (le & Helab & Hexp).
        monadInv Hexp. eauto using wt_elab_lexp with dftyping.
      - monadInv Helab.
        specialize (IHae2 _ EQ1); clear EQ1.
        specialize (IHae3 _ EQ0); clear EQ0.
        destruct ((typeof x ==b bool_type) && (typeofc x0 ==b typeofc x1)) eqn:Hg;
          try discriminate.
        apply andb_prop in Hg; destruct Hg as (Hg1 & Hg2).
        rewrite equiv_decb_equiv in Hg1, Hg2.
        monadInv EQ3. eauto using wt_elab_lexp with dftyping.
      - apply bind_inversion in Helab.
        destruct Helab as (le & Helab & Hexp).
        monadInv Hexp. eauto using wt_elab_lexp with dftyping.
      - apply bind_inversion in Helab.
        destruct Helab as (le & Helab & Hexp).
        monadInv Hexp. eauto using wt_elab_lexp with dftyping.
      - apply bind_inversion in Helab.
        destruct Helab as (le & Helab & Hexp).
        monadInv Hexp. eauto using wt_elab_lexp with dftyping.
      - apply bind_inversion in Helab.
        destruct Helab as (le & Helab & Hexp).
        monadInv Hexp. eauto using wt_elab_lexp with dftyping.
      - apply bind_inversion in Helab.
        destruct Helab as (le & Helab & Hexp).
        monadInv Hexp. eauto using wt_elab_lexp with dftyping.
      - apply bind_inversion in Helab.
        destruct Helab as (le & Helab & Hexp).
        monadInv Hexp. eauto using wt_elab_lexp with dftyping.
      - monadInv Helab.
        specialize (IHae1 _ EQ1); clear EQ1.
        specialize (IHae2 _ EQ0); clear EQ0.
        destruct ((typeofc x0 ==b typeofc x1)) eqn:Hg;
          try discriminate.
        rewrite equiv_decb_equiv in Hg.
        monadInv EQ3. apply assert_type_In in EQ.
        auto with dftyping.
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
               match goal with H:bind _ _ = _ |- _ => monadInv H end.
      - admit.
      - admit.
      - admit.
      - admit.
      - admit.
      - admit.
      - admit.
      - admit.
      - admit.
      - admit.
    Qed.
    
  End ElabExpressions.

  Section ElabDeclaration.

    (* Preceding dataflow program. *)
    Variable G : global.

    (* Map node names to input and output types. *)
    Variable nenv : PM.t (list type * list type).

    Hypothesis wt_nenv :
      forall f n tysin tysout,
        PM.find f nenv = Some (tysin, tysout) ->
        (find_node f G = Some n
         /\ Forall2 (fun i ty=> snd i = ty) n.(n_in) tysin
         /\ Forall2 (fun i ty=> snd i = ty) [n.(n_out)] tysout).

    Definition elab_var_decl (acc: list (ident * type) * (PS.t * PM.t type))
               (vd: string * type_name * Ast.clock * astloc)
               : (list (ident * type) * (PS.t * PM.t type)) :=
      let '(rs, (vars, tyenv)) := acc in
      let '(sx, sty, sck, loc) := vd in
      let x := ident_of_string sx in
      let ty := elab_type loc sty in
      ((x, ty)::rs, (PS.add x vars, PM.add x ty tyenv)).

    Fixpoint check_defd (out: PS.t) (defd: PS.t) (eqs: list equation) : bool :=
      match eqs with
      | nil => PS.is_empty defd
      | eq::eqs => let x := var_defined eq in
                   if PS.mem x defd && (negb (is_fby eq && PS.mem x out))
                   then check_defd out (PS.remove x defd) eqs
                   else false
      end.

    Fixpoint elab_clock_decl (tyenv: PM.t type) (acc: PM.t clock)
               (vds: list (string * type_name * Ast.clock * astloc))
               : res (PM.t clock) :=
      match vds with
      | nil => OK acc
      | vd::vds =>
        let '(sx, sty, sck, loc) := vd in
        let x := ident_of_string sx in
        do ck <- elab_clock tyenv loc sck;
           elab_clock_decl tyenv (PM.add x ck acc) vds
      end.

    Program Definition elab_declaration (decl: Ast.declaration) : res node :=
      match decl with
      | NODE name inputs outputs locals equations loc =>
        let '(xout, sout) := fold_left elab_var_decl outputs
                                       ([], (PS.empty, PM.empty type)) in
        let '(xlocal, svars) := fold_left elab_var_decl locals ([], sout) in
        let '(xin, (allvars, tyenv)) := fold_left elab_var_decl inputs
                                                  ([], svars) in
        match elab_clock_decl tyenv (PM.empty clock)
                              (inputs ++ outputs ++ locals) with
        | OK ckenv =>
          match mmap (elab_equation tyenv ckenv nenv) equations with
          | OK eqs =>
            match check_defd (fst sout) (fst (svars)) eqs with
            | false => Error (err_loc loc (msg "a variable is not properly defined"))
            | true =>
              match existsb (fun x=>PS.mem x allvars) Ident.Ids.reserved with
              | true => Error (err_loc loc (msg "illegal variable name"))
              | false =>
                match length xin ==b 0 with
                | true => Error (err_loc loc (msg "not enough inputs"))
                | false =>
                  match xout with
                  | o::nil => OK {| n_name  := ident_of_string name;
                                    n_in    := xin;
                                    n_out   := o;
                                    n_vars  := xlocal;
                                    n_eqs   := eqs;
                                    n_ingt0 := _;
                                    n_defd  := _;
                                    n_vout  := _;
                                    n_nodup := _;
                                    n_good  := _ |}
                  | _ => Error (err_loc loc (msg "need one output"))
                  end
                end
              end
            end
          | Error e => Error e
          end
        | Error e => Error e
        end
      end.
    Next Obligation.
      (* 0 < length xin *)
      match goal with H:false = (length xin ==b 0) |- _ => rename H into Hin end.
      symmetry in Hin. apply not_equiv_decb_equiv in Hin.
      now apply NPeano.Nat.neq_0_lt_0 in Hin.
    Qed.
    Next Obligation.
      (* Permutation (map var_defined eqs) (map fst (xlocal ++ [(i, t)])) *)
      admit.
    Qed.
    Next Obligation.
      (* ~ In (fst (i, t)) (map var_defined (filter is_fby eqs)) *)
      admit.
    Qed.
    Next Obligation.
      (* NoDupMembers (xin ++ xlocal ++ [(i, t)]) *)
      admit.
    Qed.
    Next Obligation.
      (* Forall NotReserved (xin ++ xlocal ++ [(i, t)]) *)
      match goal with H:context [PS.mem _ allvars] |- _ => rename H into Hr end.
      symmetry in Hr.
      admit.
    Qed.

    Lemma wt_elab_declaration:
      forall d node,
        elab_declaration d = OK node ->
        wt_node G node.
    Admitted.

  End ElabDeclaration.

  Fixpoint elab_declarations' (nenvg: PM.t (list type * list type) * global)
                              (decls: list Ast.declaration) : res global :=
    let (nenv, g) := nenvg in
    match decls with
    | nil => OK g
    | d::ds =>
      do n <- elab_declaration nenv d;
         let loc := declaration_loc d in
         if find_node_interface nenv loc n.(n_name)
         then Error (err_loc loc (MSG "duplicate definition for "
                                      :: CTX n.(n_name) :: nil))
         else elab_declarations'
                (PM.add n.(n_name) (map snd n.(n_in),
                                    map snd [n.(n_out)]) nenv, n :: g) ds
    end.

  Definition elab_declarations (decls: list Ast.declaration) : res global :=
    elab_declarations' (PM.empty (list type * list type), []) decls.

  Lemma wt_elab_declarations:
    forall decls g,
      elab_declarations decls = OK g ->
      wt_global g.
  Admitted.
  
End ELABORATION.


