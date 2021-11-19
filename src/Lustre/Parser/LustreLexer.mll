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

(* This lexer draws on the work of Jacques-Henri Jourdan for the CompCert
   project (CompCert/cparser/Lexer.mll). *)

{
open Specif
open Lexing
open LustreParser
open !Aut.GramDefs

module SSet = Set.Make(String)

let makeident str = Camlcoq.(intern_string str)

let lexicon : (string, LustreAst.astloc -> token) Hashtbl.t = Hashtbl.create 17

let tok t v = Coq_existT (t, Obj.magic v)

let () =
  List.iter (fun (key, builder) -> Hashtbl.add lexicon key builder)
    [
      ("assert",   fun loc ->  ASSERT   loc);
      ("and",      fun loc ->  AND      loc);
      (* ("bool",     fun loc ->  BOOL     (makeident "bool", loc)); *)
      ("case",     fun loc ->  CASE     loc);
      ("double",   fun loc ->  FLOAT64  loc); (* LEGACY *)
      ("else",     fun loc ->  ELSE     loc);
      ("end",      fun loc ->  END      loc);
      ("every",    fun loc ->  EVERY    loc);
      ("false",    fun loc ->  ENUM_NAME (makeident "False", loc));
      ("fby",      fun loc ->  FBY      loc);
      ("float",    fun loc ->  FLOAT32  loc); (* LEGACY *)
      ("float32",  fun loc ->  FLOAT32  loc);
      ("float64",  fun loc ->  FLOAT64  loc);
      ("if",       fun loc ->  IFTE     loc);
      ("int",      fun loc ->  INT32    loc); (* LEGACY *)
      ("int16",    fun loc ->  INT16    loc);
      ("int32",    fun loc ->  INT32    loc);
      ("int64",    fun loc ->  INT64    loc);
      ("int8",     fun loc ->  INT8     loc);
      ("land",     fun loc ->  LAND     loc);
      ("let",      fun loc ->  LET      loc);
      ("lnot",     fun loc ->  LNOT     loc);
      ("lor",      fun loc ->  LOR      loc);
      ("lsl",      fun loc ->  LSL      loc);
      ("lsr",      fun loc ->  LSR      loc);
      ("lxor",     fun loc ->  LXOR     loc);
      ("merge",    fun loc ->  MERGE    loc);
      ("mod",      fun loc ->  MOD      loc);
      ("node",     fun loc ->  NODE     loc);
      ("not",      fun loc ->  NOT      loc);
      ("of",       fun loc ->  OF       loc);
      ("on",       fun loc ->  ON       loc);
      ("onot",     fun loc ->  ONOT     loc);
      ("or",       fun loc ->  OR       loc);
      ("real",     fun loc ->  FLOAT64  loc); (* LEGACY *)
      ("reset",    fun loc ->  RESET    loc);
      ("restart",  fun loc ->  RESTART  loc);
      ("returns",  fun loc ->  RETURNS  loc);
      ("switch",   fun loc ->  SWITCH   loc);
      ("tel",      fun loc ->  TEL      loc);
      ("then",     fun loc ->  THEN     loc);
      ("true",     fun loc ->  ENUM_NAME (makeident "True", loc));
      ("type",     fun loc ->  TYPE     loc);
      ("uint",     fun loc ->  UINT32   loc); (* LEGACY *)
      ("uint16",   fun loc ->  UINT16   loc);
      ("uint32",   fun loc ->  UINT32   loc);
      ("uint64",   fun loc ->  UINT64   loc);
      ("uint8",    fun loc ->  UINT8    loc);
      ("var",      fun loc ->  VAR      loc);
      ("when",     fun loc ->  WHEN     loc);
      ("whenot",   fun loc ->  WHENOT   loc);
      ("xor",      fun loc ->  XOR      loc);
    ]

let init filename channel : Lexing.lexbuf =
  let lb = Lexing.from_channel channel in
  lb.lex_curr_p <- {lb.lex_curr_p with pos_fname = filename; pos_lnum = 1};
  lb

let currentLoc =
  let nextident = ref 0 in
  let getident () =
    nextident := !nextident + 1;
    !nextident
  in
  fun lb ->
    let p = Lexing.lexeme_start_p lb in
    LustreAst.({ ast_lnum  = p.Lexing.pos_lnum;
                 ast_fname = p.Lexing.pos_fname;
                 ast_bol   = p.Lexing.pos_bol;
                 ast_cnum  = p.Lexing.pos_cnum;
                 ast_ident = getident ();})

let string_of_loc { LustreAst.ast_fname = fname;
                    LustreAst.ast_lnum  = lnum;
                    LustreAst.ast_bol   = bol;
                    LustreAst.ast_cnum  = cnum } =
  Printf.sprintf "%s:%d:%d" fname lnum (cnum - bol + 1)

let lexing_loc { LustreAst.ast_lnum  = lnum;
                 LustreAst.ast_fname = fname;
                 LustreAst.ast_bol   = bol;
                 LustreAst.ast_cnum  = cnum } =
   Lexing.({ pos_lnum  = lnum;
             pos_fname = fname;
             pos_bol   = bol;
             pos_cnum  = cnum })

(* Error reporting *)

exception Abort

let fatal_error lb fmt =
  Format.kfprintf
    (fun _ -> raise Abort)
    Format.err_formatter
    ("@[<hov 2>%s:%d: Error:@ " ^^ fmt
      ^^ ".@]@.@[<hov 0>Fatal error; compilation aborted.@]@.")
      lb.lex_curr_p.pos_fname lb.lex_curr_p.pos_lnum

let error lb fmt =
  Format.eprintf  ("@[<hov 2>%s:%d: Error:@ " ^^ fmt ^^ ".@]@.")
      lb.lex_curr_p.pos_fname lb.lex_curr_p.pos_lnum

let warning lb fmt =
  Format.eprintf  ("@[<hov 2>%s:%d: Warning:@ " ^^ fmt ^^ ".@]@.")
      lb.lex_curr_p.pos_fname lb.lex_curr_p.pos_lnum

(* Simple character escapes *)

let convert_escape = function
  | 'a' -> 7L  (* bell *)
  | 'b' -> 8L  (* backspace  *)
  | 'e' -> 27L (* escape (GCC extension) *)
  | 'f' -> 12L (* form feed *)
  | 'n' -> 10L (* new line *)
  | 'r' -> 13L (* carriage return *)
  | 't' -> 9L  (* horizontal tab *)
  | 'v' -> 11L (* vertical tab *)
  | c   -> Int64.of_int (Char.code c)
}

(* Identifiers *)
let digit = ['0'-'9']
let hexadecimal_digit = ['0'-'9' 'A'-'F' 'a'-'f']
let lnondigit = ['_' 'a'-'z']
let unondigit = ['A'-'Z']

let hex_quad = hexadecimal_digit hexadecimal_digit
                 hexadecimal_digit hexadecimal_digit
let universal_character_name =
    "\\u" (hex_quad as n)
  | "\\U" (hex_quad hex_quad as n)

let lidentifier_nondigit =
    lnondigit
let uidentifier_nondigit =
    unondigit
let identifier_nondigit =
    lnondigit|unondigit
(*| universal_character_name*)
(*| '$'*) (* NB: We cannot accept identifiers that contains '$'
                 since we use '$' as a separator in the names of
                 Clight identifiers in target code. *)

let lidentifier = lidentifier_nondigit (identifier_nondigit|digit)*
let uidentifier = uidentifier_nondigit (identifier_nondigit|digit)*

(* Whitespaces *)
let whitespace_char_no_newline = [' ' '\t' '\012' '\r']

(* Integer constants *)
let nonzero_digit = ['1'-'9']
let decimal_constant = nonzero_digit digit*

let octal_digit = ['0'-'7']
let octal_constant = '0' octal_digit*

let hexadecimal_prefix = "0x" | "0X"
let hexadecimal_constant =
  hexadecimal_prefix hexadecimal_digit+

let unsigned_suffix = ['u' 'U']
let long_suffix = ['l' 'L']
let long_long_suffix = "ll" | "LL"
let integer_suffix =
    unsigned_suffix long_suffix?
  | unsigned_suffix long_long_suffix
  | long_suffix unsigned_suffix?
  | long_long_suffix unsigned_suffix?

let integer_constant =
    decimal_constant integer_suffix?
  | octal_constant integer_suffix?
  | hexadecimal_constant integer_suffix?

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

let hexadecimal_digit_sequence = hexadecimal_digit+
let hexadecimal_fractional_constant =
    (hexadecimal_digit_sequence as intpart)? '.' (hexadecimal_digit_sequence
                                                    as frac)
  | (hexadecimal_digit_sequence as intpart) '.'
let binary_exponent_part =
    'p' ((sign? digit_sequence) as expo)
  | 'P' ((sign? digit_sequence) as expo)
let hexadecimal_floating_constant =
    hexadecimal_prefix hexadecimal_fractional_constant
        binary_exponent_part floating_suffix?
  | hexadecimal_prefix (hexadecimal_digit_sequence as intpart)
        binary_exponent_part floating_suffix?

(* Character constants *)
let simple_escape_sequence =
  '\\' ( ['\''  '\"'  '?'  '\\'  'a'  'b'  'e'  'f'  'n'  'r'  't'  'v'] as c)
let octal_escape_sequence =
  '\\' ((octal_digit
         | octal_digit octal_digit
         | octal_digit octal_digit octal_digit) as n)
let hexadecimal_escape_sequence = "\\x" (hexadecimal_digit+ as n)
(* not used, only for reference: *)
let escape_sequence =
    simple_escape_sequence
  | octal_escape_sequence
  | hexadecimal_escape_sequence
  | universal_character_name

rule initial = parse
  | '\n'                          { new_line lexbuf; initial_linebegin lexbuf }
  | whitespace_char_no_newline +  { initial lexbuf }
  | "(*"                          { multiline_comment lexbuf; initial lexbuf }
  | "/*"                          { multiline_comment2 lexbuf; initial lexbuf }
  | "--"                          { singleline_comment lexbuf; initial lexbuf }
  | "//"                          { singleline_comment lexbuf; initial lexbuf }
  | integer_constant as s         { CONSTANT (LustreAst.CONST_INT s,
                                                    currentLoc lexbuf) }
  | decimal_floating_constant     { CONSTANT (LustreAst.CONST_FLOAT
                                      {LustreAst.isHex_FI = false;
                                       LustreAst.integer_FI = intpart;
                                       LustreAst.fraction_FI = frac;
                                       LustreAst.exponent_FI = expo;
                                       LustreAst.suffix_FI =
                                         match suffix with
                                         | None -> None
                                         | Some c -> Some (String.make 1 c) },
                                      currentLoc lexbuf) }
  | hexadecimal_floating_constant { CONSTANT (LustreAst.CONST_FLOAT
                                      {LustreAst.isHex_FI = true;
                                       LustreAst.integer_FI = intpart;
                                       LustreAst.fraction_FI = frac;
                                       LustreAst.exponent_FI = Some expo;
                                       LustreAst.suffix_FI =
                                         match suffix with
                                           | None -> None
                                           | Some c -> Some (String.make 1 c) },
                                      currentLoc lexbuf)}
  | "'"                           { let l = char_literal lexbuf.lex_start_p []
                                              lexbuf in
                                    CONSTANT
                                          (LustreAst.CONST_CHAR(false, l),
                                                    currentLoc lexbuf) }
  | "L'"                          { let l = char_literal lexbuf.lex_start_p []
                                              lexbuf in
                                   CONSTANT
                                          (LustreAst.CONST_CHAR(true, l),
                                                    currentLoc lexbuf) }
  | "<>"                          { NEQ (currentLoc lexbuf) }
  | "<="                          { LEQ (currentLoc lexbuf) }
  | ">="                          { GEQ (currentLoc lexbuf) }
  | "="                           { EQ (currentLoc lexbuf) }
  | "#"                           { HASH (currentLoc lexbuf) }
  | "<"                           { LT (currentLoc lexbuf) }
  | ">"                           { GT (currentLoc lexbuf) }
  | "+"                           { PLUS (currentLoc lexbuf) }
  | "-"                           { MINUS (currentLoc lexbuf) }
  | "*"                           { STAR (currentLoc lexbuf) }
  | "/"                           { SLASH (currentLoc lexbuf) }
  | "::"                          { COLONCOLON (currentLoc lexbuf) }
  | ":"                           { COLON (currentLoc lexbuf) }
  | "("                           { LPAREN (currentLoc lexbuf) }
  | ")"                           { RPAREN (currentLoc lexbuf) }
  | ";"                           { SEMICOLON (currentLoc lexbuf) }
  | ","                           { COMMA (currentLoc lexbuf) }
  | "."                           { DOT (currentLoc lexbuf) }
  | "|"                           { BAR (currentLoc lexbuf) }
  | "->"                          { RARROW (currentLoc lexbuf) }
  | "_"                           { UNDERSCORE (currentLoc lexbuf) }
  | lidentifier as id             {
      try Hashtbl.find lexicon id (currentLoc lexbuf)
      with Not_found -> VAR_NAME (makeident id, currentLoc lexbuf) }
  | uidentifier as id             { ENUM_NAME (makeident id, currentLoc lexbuf) }
  | eof                           { EOF (currentLoc lexbuf) }
  | _ as c                        { fatal_error lexbuf "invalid symbol %C" c }

and initial_linebegin = parse
  | '\n'                          { new_line lexbuf; initial_linebegin lexbuf }
  | whitespace_char_no_newline    { initial_linebegin lexbuf }
  | ""                            { initial lexbuf }

and char = parse
  | universal_character_name
      { try
          Int64.of_string ("0x" ^ n)
        with Failure _ ->
          error lexbuf "overflow in universal character name";
          0L
      }
  | hexadecimal_escape_sequence
      { try
          Int64.of_string ("0x" ^ n)
        with Failure _ ->
          error lexbuf "overflow in hexadecimal escape sequence";
          0L
      }
  | octal_escape_sequence
      { Int64.of_string  ("0o" ^ n) }
  | simple_escape_sequence
      { convert_escape c }
  | '\\' (_ as c)
      { error lexbuf "incorrect escape sequence '\\%c'" c;
        Int64.of_int (Char.code c) }
  | _ as c
      { Int64.of_int (Char.code c) }

and char_literal startp accu = parse
  | '\''       { lexbuf.lex_start_p <- startp;
                 List.rev accu }
  | '\n' | eof { fatal_error lexbuf "missing terminating \"'\" character" }
  | ""         { let c = char lexbuf in char_literal startp (c :: accu) lexbuf }

(* Multi-line comment terminated by "* )" *)
and multiline_comment = parse
  | "*)"   { () }
  | "(*"   { multiline_comment lexbuf;
             multiline_comment lexbuf }
  | "/*"   { multiline_comment2 lexbuf;
             multiline_comment2 lexbuf }
  | eof    { error lexbuf "unterminated comment" }
  | '\n'   { new_line lexbuf; multiline_comment lexbuf }
  | _      { multiline_comment lexbuf }

and multiline_comment2 = parse
  | "*/"   { () }
  | "/*"   { multiline_comment2 lexbuf;
             multiline_comment2 lexbuf }
  | "(*"   { multiline_comment lexbuf;
             multiline_comment lexbuf }
  | eof    { error lexbuf "unterminated comment" }
  | '\n'   { new_line lexbuf; multiline_comment2 lexbuf }
  | _      { multiline_comment2 lexbuf }

(* Single-line comment terminated by a newline *)
and singleline_comment = parse
  | '\n'   { new_line lexbuf }
  | eof    { () }
  | _      { singleline_comment lexbuf }

{

  open MenhirLibParser.Inter

  let tokens_stream filename : buffer =
    let lexbuf = init filename (open_in filename) in
    let rec loop () =
      Buf_cons (initial lexbuf, Lazy.from_fun loop)
    in
    Lazy.from_fun loop

}
