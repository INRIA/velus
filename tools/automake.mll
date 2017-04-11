{
  open List
  let libs: string list ref = ref []
  let files: string list ref = ref []
}

let ident = ['A'-'Z' 'a'-'z' '_' '0'-'9'] ['A'-'Z' 'a'-'z' '0'-'9' '_' '-']*
let path = (ident '/')* ident
let blank = [' ' '\t']

rule scan = parse
  | '\n' { Lexing.new_line lexbuf; scan lexbuf }
  | '-' ident blank+ [^ '\n']* as s { libs := s :: !libs; scan lexbuf }
  | (path ".v") as s { files := s :: !files; scan lexbuf }
  | eof { () }
  | _ { scan lexbuf }

{
  let vars_defs = [
    "DOCDIR=doc";
    "COQDEP=\"$(COQBIN)coqdep\" -c";
    "COQFLAGS=-q $(COQLIBS) $(OTHERFLAGS)";
    "COQC=\"$(COQBIN)coqc\"";
    "COQEXEC=\"$(COQBIN)coqtop\" $(COQFLAGS) -batch -load-vernac-source"
  ]

  let output_endline oc s = output_string oc (s ^ "\n")

  let print oc sep first last l =
    let n = length l in
    if n = 0 then output_endline oc "" else begin
      output_string oc first;
      let rec aux = function
        | [] -> ()
        | [x] -> output_string oc x
        | x :: xs -> Printf.fprintf oc "%s%s" x sep; aux xs
      in aux l;
      output_string oc last
    end

  let print_rule oc (names, deps, cmds) =
    print oc " " "" ": " names;
    print oc " " "" "\n" deps;
    print oc "\n\t" "\t" "\n\n" cmds

  let print_var oc var =
    print oc "\\\n  " (var ^ "=") "\n\n"

  let print_section oc = Printf.fprintf oc "\n# %s\n\n"

  let file = ref ""
  let extraction = ref ""
  let extracted = ref ""
  let makefile = ref ""

  let speclist = [
    "-e", Arg.Set_string extraction, " Set the Coq extraction file, use in conjonction with '-f'.";
    "-f", Arg.Set_string extracted, " Set the extracted files directory, default: directory part of '-e'.";
    "-o", Arg.Set_string makefile, " Set the name of the produced Makefile, default: standard output."
  ]

  let usage = "automake [OPTIONS] <_CoqProject file>"

  let process file =
    let ic = open_in file in
    scan (Lexing.from_channel ic);
    close_in ic;

    let oc = if !makefile = "" then stdout else open_out !makefile in

    print_section oc "FILES";
    print_var oc "COQLIBS" (rev !libs);
    print_var oc "VFILES" (rev !files);
    output_endline oc "VOFILES:=$(VFILES:.v=.vo)";

    print_section oc "VARIABLES";
    iter (output_endline oc) vars_defs;
    output_endline oc "$(shell mkdir -p $(DOCDIR) >/dev/null)";
    output_endline oc "export $(COQEXEC)";

    let extr_dir = Filename.dirname !extraction in
    let stamp = Filename.concat extr_dir "STAMP" in
    let extracted = if !extracted = "" then extr_dir else !extracted in
    let rm_mls = "rm -f " ^ Filename.concat extracted "*.ml*" in
    let rules = [
      [".PHONY"], ["all"; "clean"; "archclean"; "depend"], [];
      ["all"], ["$(VOFILES)"], [];
      ["clean"], [], "rm -f $(VOFILES) $(DOCDIR)/*.glob .depend" :: if !extraction <> "" then
                       [rm_mls; "rm -f " ^ stamp] else [];
      ["depend"], ["$(VFILES)"], ["@echo \"Analyzing Coq dependencies\"";
                                  "$(COQDEP) -slash $(COQLIBS) $^ > .depend"];
      ["%.vo"; "%.glob"], ["%.v"], ["@echo \"COQC $*.v\"";
                                    "$(COQC) -dump-glob $(DOCDIR)/$(*F).glob $(COQFLAGS) $*"]
    ]
    in
    print_section oc "RULES";
    iter (print_rule oc) rules;
    if !extraction <> "" then
      iter (print_rule oc) [
        ["extraction"], [stamp], [];
        [stamp], ["$(VOFILES)"; !extraction], [
          rm_mls;
          "$(COQEXEC) " ^ !extraction;
          "touch " ^ stamp
        ]
      ];

    output_endline oc "-include .depend";

    if !makefile <> "" then close_out oc

  let () =
    Arg.parse speclist process usage
}
