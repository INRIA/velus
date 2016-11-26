
(* Functions called from within the proof, e.g., VelusCorrectness *)

let obc_destination = ref (None : string option)

let fuse_obc = ref true
let do_fusion () = !fuse_obc

let print_obc_if prog =
  match !obc_destination with
  | None -> ()
  | Some f ->
      let oc = open_out f in
      Interfacelib.PrintObc.print_program
        (Format.formatter_of_out_channel oc) prog;
      close_out oc

let add_builtin p (name, (out, ins, b)) =
  let env = Env.empty in
  let id = Camlcoq.intern_string name in
  let id' = Camlcoq.coqstring_of_camlstring name in
  let targs = List.map (C2C.convertTyp env) ins
                |> Translation0.list_type_to_typelist in
  let tres = C2C.convertTyp env out in
  let sg = Ctypes.signature_of_type targs tres AST.cc_default in
  let ef =
    if name = "malloc" then AST.EF_malloc else
    if name = "free" then AST.EF_free else
    if Str.string_match C2C.re_runtime name 0 then AST.EF_runtime(id', sg) else
    if Str.string_match C2C.re_builtin name 0
    && List.mem_assoc name C2C.builtins.Builtins.functions
    then AST.EF_builtin(id', sg)
    else AST.EF_external(id', sg) in
  let decl = (id, AST.Gfun (Ctypes.External (ef, targs, tres, AST.cc_default))) in
  { p with Ctypes.prog_defs = decl :: p.Ctypes.prog_defs }

let add_builtins p =
  List.fold_left add_builtin p C2C.builtins_generic.Builtins.functions

