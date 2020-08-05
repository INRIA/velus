(* *********************************************************************)
(*                                                                     *)
(*                    The Velus Lustre compiler                        *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

module A = FrustreAst
module F = Frustre
module PP = Frustre_pp

let infer_clocks = ref false

let sprintf = Format.asprintf

let formatloc pp { A.ast_fname = fname; A.ast_lnum = lnum } =
  if fname <> "" then Format.fprintf pp "%s:%d" fname lnum

exception ElaborationError

let warning loc msg = Format.eprintf "%aWarning: %s" formatloc loc msg

let error loc s =
  Format.eprintf "@[%a:%s@.@]" formatloc loc s;
  raise ElaborationError

let tr_type =
  let open Ctypes in
  function
  | A.Tint8    -> F.Tint ( I8, Signed)
  | A.Tuint8   -> F.Tint ( I8, Unsigned)
  | A.Tint16   -> F.Tint (I16, Signed)
  | A.Tuint16  -> F.Tint (I16, Unsigned)
  | A.Tint32   -> F.Tint (I32, Signed)
  | A.Tuint32  -> F.Tint (I32, Unsigned)
  | A.Tint64   -> F.Tlong Signed
  | A.Tuint64  -> F.Tlong Unsigned
  | A.Tfloat32 -> F.Tfloat F32
  | A.Tfloat64 -> F.Tfloat F64
  | A.Tbool    -> F.typ_bool

let tr_uop = function
  | A.MINUS -> F.Eneg
  | A.NOT   -> F.Enotint
  | A.BNOT  -> F.Enotbool

let tr_bop = function
  | A.ADD  -> F.Eadd
  | A.SUB  -> F.Esub
  | A.MUL  -> F.Emul
  | A.DIV  -> F.Ediv
  | A.MOD  -> F.Emod
  | A.BAND -> F.Eand
  | A.BOR  -> F.Eor
  | A.LAND -> F.Eand
  | A.LOR  -> F.Eor
  | A.XOR  -> F.Exor
  | A.LSL  -> F.Eshl
  | A.LSR  -> F.Eshr
  | A.EQ   -> F.Eeq
  | A.NE   -> F.Ene
  | A.LT   -> F.Elt
  | A.GT   -> F.Egt
  | A.LE   -> F.Ele
  | A.GE   -> F.Ege

let rec tr_clock = function
  | A.BASE           -> if !infer_clocks then F.fresh_clock () else F.Sbase
  | A.ON (clk, x, b) -> F.Son (tr_clock clk, b, F.Vnm x)

let ckvar venv loc x = try (F.Env.find x venv) with Not_found ->
  error loc (sprintf "undeclared variable '%a'" PP.ident x)

let tr_preclock venv loc x = function
  | A.FULLCK (A.BASE) -> if !infer_clocks then ckvar venv loc x else F.Sbase
  | A.FULLCK ck       -> tr_clock ck
  | A.WHENCK (y, b)   -> F.(Son (ckvar venv loc y, b, Vnm y))

let cint_of_bool = function
  | true  -> Integers.Int.one
  | false -> Integers.Int.zero

(* Taken from CompCert cfrontend/C2C.ml *)
let convertIkind =
  let open Ctypes in
  function
  | C.IBool   -> (Unsigned, IBool)
  | C.IChar   -> ((if (!Machine.config).Machine.char_signed
                   then Signed else Unsigned), I8)
  | C.ISChar  -> (Signed,    I8)
  | C.IUChar  -> (Unsigned,  I8)
  | C.IInt    -> (Signed,   I32)
  | C.IUInt   -> (Unsigned, I32)
  | C.IShort  -> (Signed,   I16)
  | C.IUShort -> (Unsigned, I16)
  | C.ILong   -> (Signed,   I32)
  | C.IULong  -> (Unsigned, I32)
  (* Special-cased in convertTyp below *)
  | C.ILongLong | C.IULongLong -> assert false

(* Taken from CompCert cfrontend/C2C.ml *)
let convertInt n = Camlcoq.coqint_of_camlint(Int64.to_int32 n)

(* Taken from CompCert cfrontend/C2C.ml *)
let z_of_str hex str fst =
  let res = ref Camlcoq.Z.Z0 in
  let base = if hex then 16 else 10 in
  for i = fst to String.length str - 1 do
    let d = int_of_char str.[i] in
    let d =
      if hex && d >= int_of_char 'a' && d <= int_of_char 'f' then
        d - int_of_char 'a' + 10
      else if hex && d >= int_of_char 'A' && d <= int_of_char 'F' then
        d - int_of_char 'A' + 10
      else
        d - int_of_char '0'
    in
    assert (d >= 0 && d < base);
    res := Camlcoq.(Z.add (Z.mul (Z.of_uint base) !res) (Z.of_uint d))
  done;
  !res

(* Taken from CompCert cfrontend/C2C.ml *)
let checkFloatOverflow loc f =
  match f with
  | Binary.B754_finite _ -> ()
  | Binary.B754_zero _ ->
      warning loc "Floating-point literal is so small that it converts to 0"
  | Binary.B754_infinity _ ->
      warning loc "Floating-point literal is so large that it converts to infinity"
  | Binary.B754_nan _ ->
      warning loc "Floating-point literal converts to Not-a-Number"

(* Taken from CompCert cfrontend/C2C.ml *)
let convertFloat loc f kind =
  let mant = C.(z_of_str f.hex (f.intPart ^ f.fracPart) 0) in
  match mant with
    | Camlcoq.Z.Z0 ->
      begin match kind with
      | C.FFloat ->
          Ctyping.econst_single Floats.(Float.to_single Float.zero)
      | C.FDouble | C.FLongDouble ->
          Ctyping.econst_float Floats.Float.zero
      end
    | Camlcoq.Z.Zpos mant ->

      let sgExp = match f.C.exp.[0] with '+' | '-' -> true | _ -> false in
      let exp = z_of_str false f.C.exp (if sgExp then 1 else 0) in
      let exp = if f.C.exp.[0] = '-' then Camlcoq.Z.neg exp else exp in
      let shift_exp =
        (if f.C.hex then 4 else 1) * String.length f.C.fracPart in
      let exp = Camlcoq.(Z.sub exp (Z.of_uint shift_exp)) in

      let base = Camlcoq.P.of_int (if f.C.hex then 2 else 10) in

      begin match kind with
      | C.FFloat ->
          let f = Floats.Float32.from_parsed base mant exp in
          checkFloatOverflow loc f;
          Ctyping.econst_single f
      | C.FDouble | C.FLongDouble ->
          let f = Floats.Float.from_parsed base mant exp in
          checkFloatOverflow loc f;
          Ctyping.econst_float f
      end

    | Camlcoq.Z.Zneg _ -> assert false

let cabsloc_of_astloc loc =
  let open FrustreAst in
  let open Cabs in
  let { ast_lnum; ast_fname; ast_bol; ast_ident } = loc in
  { lineno = ast_lnum; filename = ast_fname;
    byteno = ast_bol; ident = ast_ident }

let tr_floatInfo = function
  { A.isHex_FI = h; A.integer_FI = i; A.fraction_FI = f;
    A.exponent_FI = e; A.suffix_FI = s } ->
  { Cabs.isHex_FI = h; Cabs.integer_FI = i; Cabs.fraction_FI = f;
    Cabs.exponent_FI = e; Cabs.suffix_FI = s }

let tr_const loc = function
  | A.CONST_BOOL b -> F.Cint (cint_of_bool b, Ctypes.IBool, Ctypes.Signed)

  | A.CONST_INT s -> begin
      let v, k = Elab.elab_int_constant (cabsloc_of_astloc loc) s in
      match k with
      | C.ILongLong  -> F.Clong (Camlcoq.coqint_of_camlint64 v, Ctypes.Signed)
      | C.IULongLong -> F.Clong (Camlcoq.coqint_of_camlint64 v, Ctypes.Unsigned)
      | _ -> let (sg, sz) = convertIkind k in
             F.Cint (convertInt v, sz, sg)
      end

  | A.CONST_FLOAT fi -> begin
      let f, k = Elab.elab_float_constant (tr_floatInfo fi) in
      match convertFloat loc f k with
      | Csyntax.Eval (Values.Vfloat  n, Ctypes.Tfloat(Ctypes.F64, _)) -> F.Cfloat n
      | Csyntax.Eval (Values.Vsingle n, Ctypes.Tfloat(Ctypes.F32, _)) -> F.Csingle n
      | _ -> assert false
      end

  | A.CONST_CHAR (wide, chars) ->
      let (v, _) = Elab.elab_char_constant (cabsloc_of_astloc loc) wide chars in
      F.Cint (convertInt v, I8, Unsigned)

let mke desc loc = F.({ e_desc = desc; e_loc = loc; e_typ = []; e_clk = []})

let rec tr_exp = function
  | A.UNARY (op, [e], loc) ->
      mke F.(Eunop (tr_uop op, tr_exp e)) loc
  | A.BINARY (op, [e1], [e2], loc) ->
      mke F.(Ebinop (tr_bop op, tr_exp e1, tr_exp e2)) loc
  | A.IFTE ([e], ets, efs, loc) ->
      mke F.(Eite (tr_exp e, tr_exps ets, tr_exps efs)) loc
  | A.CAST (ty, [e], loc) ->
      mke F.(Eunop (Ecast (tr_type ty), tr_exp e)) loc
  | A.APP (f, es, loc) ->
      mke F.(Eapp (f, tr_exps es, None)) loc
  | A.APPRESET (f, es, er, loc) ->
      mke F.(Eapp (f, tr_exps es, Some (tr_exp (List.hd er)))) loc
  | A.CONSTANT (c, loc) ->
      mke F.(Econst (tr_const loc c)) loc
  | A.VARIABLE (x, loc) ->
      mke F.(Evar x) loc
  | A.FBY (e0s, es, loc) ->
      mke F.(Efby (tr_exps e0s, tr_exps es)) loc
  | A.ARROW (e0s, es, loc) ->
     mke F.(Earrow (tr_exps e0s, tr_exps es)) loc
  (* | A.PRE (es, loc) ->
   *    mke F.(Epre (tr_exps es)) loc *)
  | A.WHEN (es, x, b, loc) ->
      mke F.(Ewhen (tr_exps es, x, b)) loc
  | A.MERGE (x, ets, efs, loc) ->
      mke F.(Emerge (x, tr_exps ets, tr_exps efs)) loc
  | A.UNARY _ | A.BINARY _ | A.IFTE _ | A.CAST _ -> assert false

and tr_exps x = List.map tr_exp x

let tr_equation ((xs, es), loc) = F.({
    eq_desc = (xs, tr_exps es);
    eq_loc  = loc
  })

let add_decl venv env (x, ((ty, pck), loc)) =
  let clk = tr_preclock venv loc x pck in
  try
    F.unify_clocks (F.Env.find x venv) clk;
    F.Env.add x F.({ v_typ = tr_type ty;
                     v_clk = clk;
                     v_loc = loc }) env
  with F.Unify ->
    error loc (sprintf "clock of %a is cyclic (%a)" PP.ident x PP.sclock clk)

let add_var env (x, _) =
  F.Env.add x (F.fresh_clock ()) env

let add_decls (venv, env) xs =
  let venv' = List.fold_left add_var venv xs in
  (venv', List.fold_left (add_decl venv') env xs)

let tr_decl = function
  | A.NODE (f, has_state, xin, xout, xvar, eqs, loc) ->
      try
        F.({ desc = Enodedecl {
          n_name     = f;
          n_hasstate = has_state;
          n_in       = List.map fst xin;
          n_out      = List.map fst xout;
          n_vars     = List.map fst xvar;
          n_eqs      = List.map tr_equation eqs;
          n_env      = snd
            (add_decls (add_decls (add_decls Env.(empty, empty) xin) xout) xvar)
        }; loc = loc })
      with ElaborationError ->
        (Format.eprintf "elaboration error in node '%a'@." PP.ident f;
         exit 1)

let tr_decls = List.map tr_decl

