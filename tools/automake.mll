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
    "COQDEP=\"coqdep\" -c";
    "COQFLAGS=-q $(COQLIBS) $(OTHERFLAGS)";
    "COQC=\"coqc\"";
    "COQEXEC=\"coqtop\" $(COQLIBS) -batch -load-vernac-source"
  ]

  let files_defs = [
    "-include $(addsuffix .d,$(VFILES))";
    (* ".SECONDARY: $(addsuffix .d,$(VFILES))"; *)
    "";
    "VOFILES:=$(VFILES:.v=.vo)";
    "GLOBFILES:=$(VFILES:.v=.glob)"
  ]

  let rules = [
    ([".PHONY"], ["all"; "clean"; "archclean"], []);
    (["all"], ["$(VOFILES)"], []);
    (["clean"], [], ["@rm -f $(VOFILES) $(VFILES:.v=.v.d) $(VFILES:.v=.glob)"]);
    (["archclean"], [], ["@rm -f *.cmx *.o"]);
    (["%.vo"; "%.glob"], ["%.v"], ["@echo \"COQC $*.v\""; "@$(COQC) $(COQDEBUG) $(COQFLAGS) $*"]);
    (["%.v.d"], ["%.v"],
     ["@echo \"COQDEP $*.v\"";
      "@$(COQDEP) -slash $(COQLIBS) \"$<\" > \"$@\" || ( RV=$$?; rm -f \"$@\"; exit $${RV} )"])
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

    print_section "FILES";
    print_var "COQLIBS" (rev !libs);
    print_var "VFILES" (rev !files);
    iter print_endline files_defs;

    print_section "RULES";
    iter print_rule rules
}
