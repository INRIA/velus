(***********************************************************************)
(*                                                                     *)
(*                             Heptagon                                *)
(*                                                                     *)
(* Gwenael Delaval, LIG/INRIA, UJF                                     *)
(* Leonard Gerard, Parkas, ENS                                         *)
(* Adrien Guatto, Parkas, ENS                                          *)
(* Cedric Pasteur, Parkas, ENS                                         *)
(* Marc Pouzet, Parkas, ENS                                            *)
(*                                                                     *)
(* Copyright 2012 ENS, INRIA, UJF                                      *)
(*                                                                     *)
(* This file is part of the Heptagon compiler.                         *)
(*                                                                     *)
(* Heptagon is free software: you can redistribute it and/or modify it *)
(* under the terms of the GNU General Public License as published by   *)
(* the Free Software Foundation, either version 3 of the License, or   *)
(* (at your option) any later version.                                 *)
(*                                                                     *)
(* Heptagon is distributed in the hope that it will be useful,         *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of      *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the       *)
(* GNU General Public License for more details.                        *)
(*                                                                     *)
(* You should have received a copy of the GNU General Public License   *)
(* along with Heptagon.  If not, see <http://www.gnu.org/licenses/>    *)
(*                                                                     *)
(***********************************************************************)


{
open Lexing
open Location
open Hept_parser

type lexical_error =
  | Illegal_character
  | Unterminated_comment
  | Bad_char_constant
  | Unterminated_string

exception Lexical_error of lexical_error * location;;

let comment_depth = ref 0

let keyword_table = ((Hashtbl.create 149) : (string, token) Hashtbl.t);;

List.iter (fun (str,tok) -> Hashtbl.add keyword_table str tok) [
 "node", NODE;
 "fun", FUN;
 "returns", RETURNS;
 "var", VAR;
 "val", VAL;
 "const", CONST;
 "let", LET;
 "tel", TEL;
 "end", END;
 "fby", FBY;
 "switch", SWITCH;
 "type", TYPE;
 "every", EVERY;
 "true", BOOL(true);
 "false", BOOL(false);
 "pre", PRE;
 "and", AND;
 "or", OR;
 "not", NOT;
 "open", OPEN;
 "automaton", AUTOMATON;
 "switch", SWITCH;
 "present", PRESENT;
 "reset", RESET;
 "state", STATE;
 "unless", UNLESS;
 "until", UNTIL;
 "last", LAST;
 "if", IF;
 "then", THEN;
 "else", ELSE;
 "default", DEFAULT;
 "continue", CONTINUE;
 "do", DO;
 "done", DONE;
 "in", IN;
 "contract", CONTRACT;
 "assume", ASSUME;
 "enforce", ENFORCE;
 "reachable", REACHABLE;
 "attractive", ATTRACTIVE;
 "with", WITH;
 "inlined",INLINED;
 "when", WHEN;
 "whenot", WHENOT;
 "merge", MERGE;
 "on", ON;
 "onot", ONOT;
 "map", MAP;
 "mapi", MAPI;
 "fold", FOLD;
 "foldi", FOLDI;
 "mapfold", MAPFOLD;
 "at", AT;
 "init", INIT;
 "split", SPLIT;
 "reinit", REINIT;
 "unsafe", UNSAFE;
 "external", EXTERNAL;
 "quo", INFIX3("quo");
 "mod", INFIX3("mod");
 "land", INFIX3("land");
 "lor", INFIX2("lor");
 "xor", INFIX2("xor");
 "lsl", INFIX4("lsl");
 "lsr", INFIX4("lsr");
 "asr", INFIX4("asr")
]


(* To buffer string literals *)

let string_buffer = Buffer.create 256

let reset_string_buffer () =
  Buffer.reset string_buffer

let store_string_char c =
  Buffer.add_char string_buffer c

let get_stored_string () =
  Buffer.contents string_buffer

let char_for_backslash = function
    'n' -> '\010'
  | 'r' -> '\013'
  | 'b' -> '\008'
  | 't' -> '\009'
  | c   -> c

let char_for_decimal_code lexbuf i =
  let c =
    100 * (int_of_char(Lexing.lexeme_char lexbuf i) - 48) +
     10 * (int_of_char(Lexing.lexeme_char lexbuf (i+1)) - 48) +
          (int_of_char(Lexing.lexeme_char lexbuf (i+2)) - 48) in
  char_of_int(c land 0xFF)

}


let newline = '\n' | '\r' '\n'

rule token = parse
  | newline         { new_line lexbuf; token lexbuf }
  | [' ' '\t'] +    { token lexbuf }
  | "."             {DOT}
  | "("             {LPAREN}
  | "<("            {LESS_LPAREN}
  | ")"             {RPAREN}
  | ")>"            {RPAREN_GREATER}
  | "*"             { STAR }
  | "{"             {LBRACE}
  | "}"             {RBRACE}
  | ":"             {COLON}
  | "::"            {COLONCOLON}
  | ";"             {SEMICOL}
  | "="             {EQUAL}
  | "=="            {EQUALEQUAL}
  | "<>"            {LESS_GREATER}
  | "&"             {AMPERSAND}
  | "&&"            {AMPERAMPER}
  | "||"            {BARBAR}
  | ","             {COMMA}
  | "->"            {ARROW}
  | "|"             {BAR}
  | "-"             {SUBTRACTIVE "-"}
  | "-."            {SUBTRACTIVE "-."}
  | "^"             {POWER}
  | "["             {LBRACKET}
  | "]"             {RBRACKET}
  | "[>"            {LBRACKETGREATER}
  | "<]"            {LESSRBRACKET}
  | "@"             {AROBASE}
  | ".."            {DOUBLE_DOT}
  | "<<"            {DOUBLE_LESS}
  | ">>"            {DOUBLE_GREATER}
  | "..."           {THREE_DOTS}
  | (['A'-'Z']('_' ? ['A'-'Z' 'a'-'z' ''' '0'-'9']) * as id)
      {Constructor id}
  | (['A'-'Z' 'a'-'z']('_' ? ['A'-'Z' 'a'-'z' ''' '0'-'9']) * as id)
      { let s = Lexing.lexeme lexbuf in
          begin try
      Hashtbl.find keyword_table s
          with
        Not_found -> IDENT id
    end
      }
  | ['0'-'9']+
  | '0' ['x' 'X'] ['0'-'9' 'A'-'F' 'a'-'f']+
  | '0' ['o' 'O'] ['0'-'7']+
  | '0' ['b' 'B'] ['0'-'1']+
      { INT (int_of_string(Lexing.lexeme lexbuf)) }
  | ['0'-'9']+ ('.' ['0'-'9']+)? (['e' 'E'] ['+' '-']? ['0'-'9']+)?
      { FLOAT (float_of_string(Lexing.lexeme lexbuf)) }
  | "\""
      { reset_string_buffer();
        (*let string_start = lexbuf.lex_curr_p in
        string_start_loc := Location.curr lexbuf;*)
        string lexbuf;
        (*lexbuf.lex_start_p <- string_start; *)
        STRING (get_stored_string()) }
  | "(*@ " (['A'-'Z' 'a'-'z']('_' ? ['A'-'Z' 'a'-'z' ''' '0'-'9']) * as id)
      {
  reset_string_buffer();
  let l1 = lexbuf.lex_curr_p in
  begin try
    pragma lexbuf
  with Lexical_error(Unterminated_comment, Loc(_, l2)) ->
    raise(Lexical_error(Unterminated_comment, Loc (l1, l2)))
  end;
  PRAGMA(id,get_stored_string())
      }
  | "(*"
      { let comment_start = lexbuf.lex_curr_p in
        comment_depth := 1;
        begin try
          comment lexbuf
        with Lexical_error(Unterminated_comment, (Loc (_, comment_end))) ->
          raise(Lexical_error(Unterminated_comment,
                              Loc (comment_start, comment_end)))
        end;
        token lexbuf }
   | "--" | "--%"
      { single_line_comment lexbuf }
   | ['!' '?' '~']
      ['!' '$' '%' '&' '*' '+' '-' '.' '/' ':'
    '<' '=' '>' '?' '@' '^' '|' '~'] *
      { PREFIX(Lexing.lexeme lexbuf) }
  | ['=' '<' '>' '&'  '|' '&' '$']
      ['!' '$' '%' '&' '*' '+' '-' '.' '/' ':' '<' '=' '>'
    '?' '@' '^' '|' '~'] *
      { INFIX0(Lexing.lexeme lexbuf) }
  | ['@' '^']
      ['!' '$' '%' '&' '*' '+' '-' '.' '/' ':' '<' '=' '>'
    '?' '@' '^' '|' '~'] *
      { INFIX1(Lexing.lexeme lexbuf) }
  | ['+' '-']
      ['!' '$' '%' '&' '*' '+' '-' '.' '/' ':' '<' '=' '>'
    '?' '@' '^' '|' '~'] *
      { INFIX2(Lexing.lexeme lexbuf) }
  | "**"
      ['!' '$' '%' '&' '*' '+' '-' '.' '/' ':' '<' '=' '>'
    '?' '@' '^' '|' '~'] *
      { INFIX4(Lexing.lexeme lexbuf) }
  | ['*' '/' '%']
      ['!' '$' '%' '&' '*' '+' '-' '.' '/' ':' '<' '=' '>'
    '?' '@' '^' '|' '~'] *
      { INFIX3(Lexing.lexeme lexbuf) }
  | eof            {EOF}
  | _              {raise (Lexical_error (Illegal_character,
            Loc (Lexing.lexeme_start_p lexbuf,
            Lexing.lexeme_end_p lexbuf)))}

and pragma = parse
  | newline         { new_line lexbuf; pragma lexbuf }
  | "(*"
      { let comment_start = lexbuf.lex_curr_p in
        comment_depth := 1;
        begin try
          comment lexbuf
        with Lexical_error(Unterminated_comment, Loc (_, comment_end)) ->
          raise(Lexical_error(Unterminated_comment,
                              Loc (comment_start, comment_end)))
        end;
        pragma lexbuf }
  | "@*)"
      { }
  | eof
      { raise(Lexical_error(Unterminated_comment, Loc (dummy_pos,
                            Lexing.lexeme_start_p lexbuf))) }

  | _
      { store_string_char(Lexing.lexeme_char lexbuf 0);
  pragma lexbuf }

and comment = parse
  | newline         { new_line lexbuf; comment lexbuf }
  |  "(*"
      { comment_depth := succ !comment_depth; comment lexbuf }
  | "*)"
      { comment_depth := pred !comment_depth;
        if !comment_depth > 0 then comment lexbuf }
  | "\""
      { reset_string_buffer();
        let string_start = lexbuf.lex_curr_p in
        begin try
          string lexbuf
        with Lexical_error(Unterminated_string, Loc (_, string_end)) ->
          raise(Lexical_error
            (Unterminated_string, Loc (string_start, string_end)))
        end;
        comment lexbuf }
  | "''"
      { comment lexbuf }
  | "'" [^ '\\' '\''] "'"
      { comment lexbuf }
  | "'" '\\' ['\\' '\'' 'n' 't' 'b' 'r'] "'"
      { comment lexbuf }
  | "'" '\\' ['0'-'9'] ['0'-'9'] ['0'-'9'] "'"
      { comment lexbuf }
  | eof
      { raise(Lexical_error(Unterminated_comment, Loc(dummy_pos,
                            Lexing.lexeme_start_p lexbuf))) }
  | _
      { comment lexbuf }

and single_line_comment = parse
  | newline      { new_line lexbuf; token lexbuf }
  | _            { single_line_comment lexbuf }

and string = parse
  | newline         { new_line lexbuf; string lexbuf }
  | '"'
      { () }
  | '\\' ("\010" | "\013" | "\013\010") [' ' '\009'] *
      { string lexbuf }
  | '\\' ['\\' '"'  'n' 't' 'b' 'r']
      { store_string_char(char_for_backslash(Lexing.lexeme_char lexbuf 1));
        string lexbuf }
  | '\\' ['0'-'9'] ['0'-'9'] ['0'-'9']
      { store_string_char(char_for_decimal_code lexbuf 1);
         string lexbuf }
  | eof
      { raise (Lexical_error(Unterminated_string, Loc (dummy_pos,
                              Lexing.lexeme_start_p lexbuf))) }
  | _
      { store_string_char(Lexing.lexeme_char lexbuf 0);
        string lexbuf }

(* eof *)
