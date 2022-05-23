(* lexer.mll *)

{
let print = print_string

open Lexing

type lexical_error =
    Illegal_character
  | Unterminated_comment
  | Bad_char_constant
  | Unterminated_string;;

exception Lexical_error of lexical_error * (int * int)

let comment_depth = ref 0

let keyword_table = ((Hashtbl.create 149) : (string, string) Hashtbl.t);;

List.iter (fun (str, i) -> Hashtbl.add keyword_table str i) [
  "node",         "block";
  "returns",      "block";
  "let",          "block";
  "tel",          "block";
  "var",          "block";
  "true",         "constant";
  "false",        "constant";
  "bool",         "type";
  "int",          "type";
  "real",         "type";
  "struct",       "type";
  "void",         "type";
  "_Bool",        "type";
  "with",         "expr";
  "period",       "expr";
  "if",           "expr";
  "then",         "expr";
  "else",         "expr";
  "case",         "expr";
  "of",           "expr";
  "fby",          "expr";
  "pre",          "expr";
  "on",           "expr";
  "last",         "expr";
  "when",         "expr";
  "merge",        "expr";
  "not",          "operator";
  "and",          "operator";
  "or",           "operator";
  "quo",          "operator";
  "mod",          "operator";
  "land",         "operator";
  "lor",          "operator";
  "lxor",         "operator";
  "lsl",          "operator";
  "lsr",          "operator";
  "asr",          "operator"
]

module StringSet = Set.Make(String)

let print_empty_css () =
  print "pre.velus span.keyword { color: green; }\n";

  let default = List.fold_left (fun s e -> StringSet.add e s) StringSet.empty
    ["constructor"; "identifier"; "number"; "string"; "character"; "operator"]
  in
  let classes = Hashtbl.fold (fun _ -> StringSet.add) keyword_table default in
  StringSet.iter (fun c -> print "pre.velus span."; print c; print " { }\n")
                 (StringSet.remove "keyword" classes);

  print "pre.velus span.comment { color: gray; }\n";
  print "pre.velus span.comment span.string { color: gray; }\n";
  print "pre.velus span.comment span.character { color: gray; }\n"

(* To buffer string literals *)

let initial_string_buffer = Bytes.create 256
let string_buff = ref initial_string_buffer
let string_index = ref 0

let reset_string_buffer () =
  string_buff := initial_string_buffer;
  string_index := 0;
  ()

let store_string_char c =
  if !string_index >= Bytes.length (!string_buff) then begin
    let new_buff = Bytes.create (Bytes.length (!string_buff) * 2) in
      Bytes.blit (!string_buff) 0 new_buff 0 (Bytes.length (!string_buff));
      string_buff := new_buff
  end;
  Bytes.set (!string_buff) (!string_index) c;
  incr string_index

let get_stored_string () =
  let s = Bytes.sub (!string_buff) 0 (!string_index) in
    string_buff := initial_string_buffer;
    "\"" ^ (Bytes.to_string s) ^ "\""

let startspan c s = print "<span class=\"";
                    print c;
                    print "\">";
                    print s

let continuespan s = print s

let endspan () = print "</span>"

let printspan c s = startspan c s;
                    endspan ()
  
}

rule main = parse 
  | (['\013' '\009' '\012'] + as s)   { print s; main lexbuf }
  | (['\010' '\013' '\009' '\012'] + as s)   { print s; main lexbuf }

  | ([' ' '\010' '\013' '\009' '\012'] + as s)   { print s; main lexbuf }

  | "&"   { print "&amp;";      main lexbuf }
  | "&&"  { print "&amp;&amp;"; main lexbuf }
  | ">"   { print "&gt;";       main lexbuf }
  | ">="  { print "&gt;=";      main lexbuf }
  | "<"   { print "&lt;";       main lexbuf }
  | "<>"  { print "&lt;&gt;";   main lexbuf }
  | "<="  { print "&lt;=";      main lexbuf }

  | "->"  { print "-&gt;";      main lexbuf }
  | "=>"  { print "=&gt;";      main lexbuf }
  | "~>"  { print "~&gt;";      main lexbuf }

  | "*"   { print "∗";          main lexbuf }   (* unicode: 0x2217 *)

  | "."
  | "("
  | ")"
  | "{"
  | "}"
  | ":"
  | "="
  | "=="
  | "'"
  | "||"
  | ","
  | ";"
  | ";;"
  | "|"
  | "-"
  | "-."
  | "?"
  | "_" { print (Lexing.lexeme lexbuf); main lexbuf }

  | (['A'-'Z']('_' ? '$' ? ['A'-'Z' 'a'-'z' ''' '0'-'9']) * as id)
  { printspan "constructor" id; main lexbuf }

  | (['A'-'Z' 'a'-'z']('_' ? '$' ? ['A'-'Z' 'a'-'z' ''' '0'-'9']) * as id)
      { let s = Lexing.lexeme lexbuf in
          begin
            try
              let cs = Hashtbl.find_all keyword_table s in
              printspan (List.fold_left (fun s c ->  c ^ " " ^ s) "" cs) id
            with Not_found ->
              printspan "identifier" id
          end; main lexbuf }

  | ['0'-'9']+
  | '0' ['x' 'X'] ['0'-'9' 'A'-'F' 'a'-'f']+
  | '0' ['o' 'O'] ['0'-'7']+
  | '0' ['b' 'B'] ['0'-'1']+
  | ['0'-'9']+ ('.' ['0'-'9']*)? (['e' 'E'] ['+' '-']? ['0'-'9']+)?
      { printspan "number" (Lexing.lexeme lexbuf); main lexbuf }

  | "\""
      { reset_string_buffer();
        let string_start = lexbuf.lex_start_pos + lexbuf.lex_abs_pos in
        begin try
          string lexbuf
        with Lexical_error(Unterminated_string, (_, string_end)) ->
          raise(Lexical_error(Unterminated_string, 
                              (string_start, string_end)))
        end;
        lexbuf.lex_start_pos <- string_start - lexbuf.lex_abs_pos;
        printspan "string" (get_stored_string()); main lexbuf }

  | "'" [^ '\\' '\''] "'"
  | "'" '\\' ['\\' '\'' 'n' 't' 'b' 'r'] "'"
  | "'" '\\' ['0'-'9'] ['0'-'9'] ['0'-'9'] "'"
      { printspan "character" (Lexing.lexeme lexbuf); main lexbuf }

  | "(*"
      { let comment_start = lexbuf.lex_start_pos + lexbuf.lex_abs_pos in
        comment_depth := 1;
        begin try
          startspan "comment" "(*";
          comment lexbuf
        with Lexical_error(Unterminated_comment, (_, comment_end)) ->
          raise(Lexical_error(Unterminated_comment,
                              (comment_start, comment_end)))
        end;
        main lexbuf }

  | ['!' '?' '~']
      ['!' '%' '&' '*' '+' '-' '.' '/' ':'
          '<' '=' '>' '?' '@' '^' '|' '~'] *
  | ['=' '<' '>' '&'  '|' '&']
      ['!' '%' '&' '*' '+' '-' '.' '/' ':' '<' '=' '>'
          '?' '@' '^' '|' '~'] *
  | ['@' '^']
      ['!' '%' '&' '*' '+' '-' '.' '/' ':' '<' '=' '>'
          '?' '@' '^' '|' '~'] *
  | ['+' '-']
      ['!' '%' '&' '*' '+' '-' '.' '/' ':' '<' '=' '>'
          '?' '@' '^' '|' '~'] *
  | "**"
      ['!' '%' '&' '*' '+' '-' '.' '/' ':' '<' '=' '>'
          '?' '@' '^' '|' '~'] *
  | ['*' '/' '%']
      ['!' '%' '&' '*' '+' '-' '.' '/' ':' '<' '=' '>'
          '?' '@' '^' '|' '~'] *
      { printspan "operator" (Lexing.lexeme lexbuf); main lexbuf }

  | eof            {()}
  | _              {raise (Lexical_error (Illegal_character,
                                            (Lexing.lexeme_start lexbuf, 
                                             Lexing.lexeme_end lexbuf)))}
      
and comment = parse
    "(*"
      { comment_depth := succ !comment_depth;
        startspan "comment" "(*";
        comment lexbuf }
  | "*)"
      { comment_depth := pred !comment_depth;
        continuespan "*)"; endspan ();
        if !comment_depth > 0 then comment lexbuf }
  | "\""
      { reset_string_buffer();
        let string_start = lexbuf.lex_start_pos + lexbuf.lex_abs_pos in
        begin try
          string lexbuf
        with Lexical_error(Unterminated_string, (_, string_end)) ->
          raise(Lexical_error(Unterminated_string, 
                              (string_start, string_end)))
        end;
        printspan "string" (get_stored_string());
        comment lexbuf }
  | "''"
      { continuespan (Lexing.lexeme lexbuf); comment lexbuf }

  | "'" [^ '\\' '\''] "'"
  | "'" '\\' ['\\' '\'' 'n' 't' 'b' 'r'] "'"
  | "'" '\\' ['0'-'9'] ['0'-'9'] ['0'-'9'] "'"
      { printspan "character" (Lexing.lexeme lexbuf); comment lexbuf }

  | ">"   { print "&gt;";  comment lexbuf }
  | ">="  { print "&gt;="; comment lexbuf }
  | "<"   { print "&lt;";  comment lexbuf }
  | "<="  { print "&lt;="; comment lexbuf }

  | eof
      { raise(Lexical_error(Unterminated_comment,
                            (0,Lexing.lexeme_start lexbuf))) }
  | _
      { continuespan (Lexing.lexeme lexbuf); comment lexbuf }

and string = parse
    '"' 
      { () }
  | eof
      { raise (Lexical_error
                (Unterminated_string, (0, Lexing.lexeme_start lexbuf))) }
  | _
      { store_string_char(Lexing.lexeme_char lexbuf 0);
        string lexbuf }

{
let full_html = ref false
let stylesheet = ref ""
let pre_classes = ref ""
let empty_css = ref false
let inputs = ref ([] : string list)

let parse_arguments () =
  Arg.parse (Arg.align [
      ("--full",           Arg.Set full_html,
                           " Include header and footer.");

      ("--stylesheet",     Arg.Set_string stylesheet,
                           " Link to a stylesheet in the header.");

      ("--makestylesheet", Arg.Set empty_css,
                           " Produce an empty stylesheet.");

      ("--preclasses",     Arg.Set_string pre_classes,
                           " Specify extra classes for the <pre> element.");
    ])
    (fun f -> inputs := f :: !inputs)
    "zltohtml [filenames]: add html tags to Zélus programs."
;;

let lex_with_name addhr filename =
  if addhr then print "\n<hr/>\n";
  if List.length !inputs > 1 then (
    print "<h2>";
    print filename;
    print "</h2>\n");
  print "<pre class=\"velus ";
  print !pre_classes;
  print "\"><code>";
  main (Lexing.from_channel (open_in filename));
  print "</code></pre>"

let run_main () =
  if !full_html then begin
    print "<html>";
    if !stylesheet <> "" then
      (print "<head><link rel=\"stylesheet\" href=\"";
       print !stylesheet;
       print "\" type=\"text/css\" />");
    print "<body>\n";
  end;
  (match List.rev (!inputs) with
  | []    -> main (Lexing.from_channel stdin)
  | [f]   -> lex_with_name false f
  | f::fs -> (lex_with_name false f; List.iter (lex_with_name true) fs));
  if !full_html then
    print "\n</body></html>\n"
;;

parse_arguments ();
if !empty_css
then print_empty_css ()
else run_main ()

}
