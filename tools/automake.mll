{
  open List
  let libs: string list ref = ref []
  let files: string list ref = ref []
}

let ident = ['A'-'Z' 'a'-'z' '_' '0'-'9'] ['A'-'Z' 'a'-'z' '0'-'9' '_' '-']*
let path = (ident '/')* ident
let lib = (ident '.')* ident
let blank = [' ' '\t']
            
rule scan = parse
  | '\n' { Lexing.new_line lexbuf; scan lexbuf }
  | ("-R" blank+ ('.' | path) blank+ lib) as s { libs := s :: !libs; scan lexbuf }
  | (path ".v") as s { files := s :: !files; scan lexbuf }
  | eof { () }
  | _ { scan lexbuf }

{
  let vars_defs = [
    "DOCDIR=doc";
    "COQDEP=\"$(COQBIN)coqdep\" -c";
    "COQFLAGS=-q $(COQLIBS) $(OTHERFLAGS)";
    "COQC=\"$(COQBIN)coqc\"";
    "COQEXEC=\"$(COQBIN)coqtop\" $(COQLIBS) -batch -load-vernac-source"
  ]

  let rules = [
    ([".PHONY"], ["all"; "clean"; "archclean"; "depend"], []);
    (["all"], ["$(VOFILES)"], []);
    (["clean"], [], ["rm -f $(VOFILES) $(DOCDIR)/*.glob .depend"]);
    (["archclean"], [], ["rm -f *.cmx *.o"]);
    (["depend"], ["$(VFILES)"], ["@echo \"Analyzing Coq dependencies\""; "$(COQDEP) -slash $(COQLIBS) $^ > .depend"]);
    (["%.vo"; "%.glob"], ["%.v"], ["@echo \"COQC $*.v\""; "$(COQC) -dump-glob $(DOCDIR)/$(*F).glob $(COQFLAGS) $*"])
  ]

  let print sep first last l =
    let n = length l in
    if n = 0 then print_newline () else begin 
      print_string first;
      let rec aux = function
        | [] -> ()
        | [x] -> print_string x
        | x :: xs -> Printf.printf "%s%s" x sep; aux xs
      in aux l;
      print_string last
    end
    
  let print_rule (names, deps, cmds) =
    print " " "" ": " names;
    print " " "" "\n" deps;
    print "\n\t" "\t" "\n\n" cmds
      
  let print_var var =
    print "\\\n  " (var ^ "=") "\n\n" 

  let print_section = Printf.printf "\n# %s\n\n"
    
  let () =
    scan (Lexing.from_channel stdin);

    print_section "VARIABLES";
    iter print_endline vars_defs;
    print_endline "$(shell mkdir -p $(DOCDIR) >/dev/null)";
    
    print_section "FILES";
    print_var "COQLIBS" (rev !libs);
    print_var "VFILES" (rev !files);
    print_endline "VOFILES:=$(VFILES:.v=.vo)";

    print_section "RULES";
    iter print_rule rules;
    print_endline "-include .depend"    
}
