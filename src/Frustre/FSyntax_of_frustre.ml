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

module F = Frustre
module FS = FSyntax
module C = ClockDefs

let tr_signedness = function
  | Ctypes.Signed   -> FS.Signed
  | Ctypes.Unsigned -> FS.Unsigned

let tr_intsize = function
  | Ctypes.I8    -> FS.I8
  | Ctypes.I16   -> FS.I16
  | Ctypes.I32   -> FS.I32
  | Ctypes.IBool -> FS.IBool

let tr_floatsize = function
  | Ctypes.F32 -> FS.F32
  | Ctypes.F64 -> FS.F64

let tr_type = function
  | F.Tint (sz, sg) -> FS.Tint (tr_intsize sz, tr_signedness sg)
  | F.Tlong sg      -> FS.Tlong (tr_signedness sg)
  | F.Tfloat fs     -> FS.Tfloat (tr_floatsize fs)

let tr_types = List.map tr_type

let rec tr_clock = function
  | F.Cbase -> C.Cbase
  | F.Con (ck, b, x) -> C.Con (tr_clock ck, x, b)

let tr_ckid = function
  | F.Vidx i -> (Camlcoq.P.of_int i)
  | F.Vnm x  -> x

let rec tr_sclock ck =
  match F.find_clock ck with
  | F.Sbase -> C.Cbase
  | F.Son (ck', b, id) -> C.Con (tr_sclock ck', tr_ckid id, b)
  | F.Svar _ -> assert false

let rec tr_sclock_to_clock ck =
  match F.find_clock ck with
  | F.Sbase -> C.Cbase
  | F.Son (ck', b, F.Vnm x) -> C.Con (tr_sclock_to_clock ck', x, b)
  | _ -> assert false

let tr_nclock = function
  | F.Cstream ck      -> (tr_sclock ck, None)
  | F.Cnamed (id, ck) -> (tr_sclock ck, Some (tr_ckid id))

let tr_float f =
  match Binary.coq_B2FF BinInt.Z.zero BinInt.Z.zero f with
  | Binary.F754_zero s           -> FS.F754_zero s
  | Binary.F754_infinity s       -> FS.F754_infinity s
  | Binary.F754_nan (b, pl)      -> FS.F754_nan (b, pl)
  | Binary.F754_finite (s, m, e) -> FS.F754_finite (s, m, e)

let tr_const = function
  | F.Cint (v, sz, sg) -> FS.Cint (v, tr_intsize sz, tr_signedness sg)
  | F.Clong (v, sg)    -> FS.Clong (v, tr_signedness sg)
  | F.Cfloat f         -> FS.Cfloat (tr_float f)
  | F.Csingle f        -> FS.Csingle (tr_float f)

let tr_unop = function
  | F.Eneg     -> FS.Oneg
  | F.Enotint  -> FS.Onotint
  | F.Enotbool -> FS.Onotbool
  | F.Ecast ty -> FS.Ocast (tr_type ty)

let tr_binop = function
  | F.Eadd -> FS.Oadd
  | F.Esub -> FS.Osub
  | F.Emul -> FS.Omul
  | F.Ediv -> FS.Odiv
  | F.Emod -> FS.Omod
  | F.Eand -> FS.Oand
  | F.Eor  -> FS.Oor
  | F.Exor -> FS.Oxor
  | F.Eshl -> FS.Oshl
  | F.Eshr -> FS.Oshr
  | F.Eeq  -> FS.Oeq
  | F.Ene  -> FS.One
  | F.Elt  -> FS.Olt
  | F.Egt  -> FS.Ogt
  | F.Ele  -> FS.Ole
  | F.Ege  -> FS.Oge

let tr_single_type = function
  | [ty] -> tr_type ty
  | _    -> assert false

let tr_single_nclock = function
  | [ck] -> tr_nclock ck
  | _    -> assert false

let tr_first_nclock = function
  | ck::_ -> tr_nclock ck
  | _    -> assert false

let tr_nclocks = List.map tr_nclock

let rec tr_exp { F.e_desc = e; F.e_typ = tys; F.e_clk = cks } =
  match e with
  | F.Econst c      -> FS.Econst (tr_const c)
  | F.Evar x        -> FS.Evar (x, (tr_single_type tys, tr_single_nclock cks))
  | F.Eunop (op, e) -> FS.Eunop (tr_unop op, tr_exp e,
                                 (tr_single_type tys, tr_single_nclock cks))
  | F.Ebinop (op, e1, e2) -> FS.Ebinop (tr_binop op, tr_exp e1, tr_exp e2,
                                        (tr_single_type tys, tr_single_nclock cks))
  | F.Efby (e0s, es)      -> FS.Efby (tr_exps e0s, tr_exps es,
                                List.combine (tr_types tys) (tr_nclocks cks))

  | F.Earrow (e0s, es)    -> FS.Earrow (tr_exps e0s, tr_exps es,
                                List.combine (tr_types tys) (tr_nclocks cks))
  (* | F.Epre es             -> FS.Epre (tr_exps es,
   *                               List.combine (tr_types tys) (tr_nclocks cks)) *)
  | F.Ewhen (es, x, b)    -> FS.Ewhen (tr_exps es, x, b,
                                       (tr_types tys, tr_first_nclock cks))
  | F.Emerge (x, ets, efs) -> FS.Emerge (x, tr_exps ets, tr_exps efs,
                                         (tr_types tys, tr_first_nclock cks))
  | F.Eite (e, ets, efs)  -> FS.Eite (tr_exp e, tr_exps ets, tr_exps efs,
                                      (tr_types tys, tr_first_nclock cks))
  | F.Eapp (f, es, None)        -> FS.Eapp (f, tr_exps es, None,
                                            List.combine (tr_types tys) (tr_nclocks cks))
  | F.Eapp (f, es, Some er)        -> FS.Eapp (f, tr_exps es, Some (tr_exp er),
                                               List.combine (tr_types tys) (tr_nclocks cks))

and tr_exps es = List.map tr_exp es

let tr_equation { F.eq_desc = (xs, es) } = (xs, tr_exps es)

let annotate_var env x =
  let { F.v_typ = ty; F.v_clk = ck } = F.Env.find x env in
  (x, (tr_type ty, tr_sclock_to_clock ck))

let tr_node
  { F.n_name; F.n_hasstate; F.n_in; F.n_out; F.n_vars; F.n_eqs; F.n_env } =
  {
    FS.n_name     = n_name;
    FS.n_hasstate = n_hasstate;
    FS.n_in       = List.map (annotate_var n_env) n_in;
    FS.n_out      = List.map (annotate_var n_env) n_out;
    FS.n_vars     = List.map (annotate_var n_env) n_vars;
    FS.n_eqs      = List.map tr_equation n_eqs
  }

let tr_implementation { F.desc } =
  match desc with
  | F.Enodedecl n -> tr_node n

let tr_program = List.map tr_implementation

