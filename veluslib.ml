
(* Functions called from within the proof, e.g., VelusCorrectness *)

let lustre_destination = ref (None : string option)
let snlustre_destination = ref (None : string option)
let sybloc_destination = ref (None : string option)
let obc_destination = ref (None : string option)
let sync_destination = ref (None : string option)
let main_node = ref (None : string option)
let reaction_counter = Camlcoq.intern_string "$reaction"

let fuse_obc = ref true
let do_fusion () = !fuse_obc

let do_sync () = !sync_destination <> None

(* try to automatically constants in "when"s? *)
let add_when_to_constants = ref true
let do_add_when_to_constants () = !add_when_to_constants

let expose = ref false
let do_expose () = !expose

let get_main_class decls =
  try
    let open Instantiator.Obc.Syn in
    match !main_node with
    | Some s ->
        let nm = Camlcoq.intern_string s in
        List.find (fun c->c.c_name = nm) decls
    | None -> List.hd decls
  with _ ->
    (Printf.eprintf "main class not found"; exit 1)

let get_first_method cl =
  try
    let open Instantiator.Obc.Syn in
    List.hd cl.c_methods
  with _ ->
    (Printf.eprintf "class has no methods"; exit 1)

let print_if flag print prog =
  match !flag with
  | None -> ()
  | Some f ->
      let oc = open_out f in
      print (Format.formatter_of_out_channel oc) prog;
      close_out oc

(* let print_lustre_if =
 *   print_if lustre_destination Interfacelib.PrintLustre.print_global *)

let print_snlustre_if =
  print_if snlustre_destination Interfacelib.PrintNLustre.print_global

let print_sybloc_if =
  print_if sybloc_destination Interfacelib.PrintSyBloc.print_program

let print_sync_if prog =
  match !sync_destination with
  | None -> ()
  | Some f ->
      let open Instantiator.Obc.Syn in
      let cl = get_main_class prog in
      let cl_m = get_first_method cl in
      let oc = open_out f in
      let f = Format.formatter_of_out_channel oc in
      Interfacelib.SyncFun.print f cl_m;
      (*
      PrintClight.print_function f
        (Camlcoq.intern_string "$sync")
        (Interfacelib.SyncFun.make reaction_counter cl_m);
      *)
      Format.pp_print_flush f ();
      close_out oc

let print_obc_if prog =
  print_sync_if prog;
  print_if obc_destination Interfacelib.PrintObc.print_program (List.rev prog)

let add_builtin p (name, (out, ins, b)) =
  let env = Env.empty in
  let id = Camlcoq.intern_string name in
  let id' = Camlcoq.coqstring_of_camlstring name in
  let targs = List.map (C2C.convertTyp env) ins
                |> Generation.list_type_to_typelist in
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
