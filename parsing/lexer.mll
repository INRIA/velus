{
exception LexError of int * int

open Parser

let incr_linenum lexbuf =
  let pos = lexbuf.Lexing.lex_curr_p in
    lexbuf.Lexing.lex_curr_p <- { pos with
      Lexing.pos_lnum = pos.Lexing.pos_lnum + 1;
      Lexing.pos_bol = pos.Lexing.pos_cnum;
    }

let keyword_table = ((Hashtbl.create 149) : (string, token) Hashtbl.t);;

List.iter (fun (str,tok) -> Hashtbl.add keyword_table str tok) [
 "node", NODE;
 "returns", RETURNS;
 "let", LET;
 "tel", TEL;
 "fby", FBY;
 "merge", MERGE;
 "when", WHEN;
 "whennot", WHENNOT;
 "on", ON;
 "true", BOOL(true); 
 "false", BOOL(false);
 "base", BASE;
 "bool", TBOOL;
 "int", TINT;
 "float", TFLOAT]
}

let digit = ['0'-'9']
let int = '-'? digit digit*
let frac = '.' digit*
let exp = ['e' 'E'] ['-' '+']? digit+
let float = digit* frac? exp?
                        
rule token = parse 
  | "--" [^ '\n']* ['\n']
                    {incr_linenum lexbuf; token lexbuf }
  | [' ' '\t']      {token lexbuf}
  | ['\n']          {incr_linenum lexbuf; token lexbuf}
  | "("             {LPAREN}
  | ")"             {RPAREN}
  | ":"             {COLON}
  | "::"            {COLONS}
  | ";"             {SEMICOL}
  | "="             {EQUAL}
  | ","             {COMMA}
  | "+"             {ADD}
  | "-"             {SUB}
  | "*"             {MUL}
  | "!"             {NOT}
  | int             { INT (int_of_string (Lexing.lexeme lexbuf)) }
  | float           { FLOAT (float_of_string (Lexing.lexeme lexbuf)) }
  | (['a'-'z']['A'-'Z''a'-'z''0'-'9''_']* as id) 
      { let s = Lexing.lexeme lexbuf in
          try
	    Hashtbl.find keyword_table s
          with Not_found ->
	    IDENT id }
  
  | eof             {EOF}
  | ""              {raise (LexError (Lexing.lexeme_start lexbuf, 
				  Lexing.lexeme_end lexbuf))}
