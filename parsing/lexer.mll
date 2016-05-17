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
 "vars", VARS;
 "let", LET;
 "tel", TEL;
 "fby", FBY;
 "merge", MERGE;
 "when", WHEN;
 "whennot", WHENNOT;
 "if", IF;
 "then", THEN;
 "else", ELSE;
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
(* let frac = '.' digit* *)
(* let exp = ['e' 'E'] ['-' '+']? digit+ *)
(* let float = digit* frac? exp? *)
(* Floating constants *)
let sign = ['-' '+']
let digit_sequence = digit+
let floating_suffix = ['f' 'l' 'F' 'L'] as suffix
let fractional_constant =
    (digit_sequence as intpart)? '.' (digit_sequence as frac)
  | (digit_sequence as intpart) '.'
let exponent_part =
    'e' ((sign? digit_sequence) as expo)
  | 'E' ((sign? digit_sequence) as expo)
let decimal_floating_constant =
    fractional_constant exponent_part? floating_suffix?
  | (digit_sequence as intpart) exponent_part floating_suffix?
                        
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
  | "/"             {DIV}
  | "!"             {NOT}
  | int             { INT (int_of_string (Lexing.lexeme lexbuf)) }
  (* | float           { FLOAT (float_of_string (Lexing.lexeme lexbuf)) } *)
  | decimal_floating_constant     { FLOAT
                                      {Cabs.isHex_FI = false;
                                       Cabs.integer_FI = intpart;
                                       Cabs.fraction_FI = frac;
                                       Cabs.exponent_FI = expo;
                                       Cabs.suffix_FI =
                                         match suffix with
                                         | None -> None
                                         | Some c -> Some (String.make 1 c)} }
  | (['a'-'z']['A'-'Z''a'-'z''0'-'9''_']* as id) 
      { let s = Lexing.lexeme lexbuf in
          try
	    Hashtbl.find keyword_table s
          with Not_found ->
	    IDENT id }
  
  | eof             {EOF}
  | ""              {raise (LexError (Lexing.lexeme_start lexbuf, 
				  Lexing.lexeme_end lexbuf))}
