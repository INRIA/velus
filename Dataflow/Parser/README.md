

Running the parser from the OCaml top level
-------------------------------------------

First build the parser and lexer:
```
make extraction/Parser.cma Lexer.cmo
```

Then load them into the top-level:
```
rlwrap ocaml
#directory "extraction";;
#load "Parser.cma";;
#load "Lexer.cmo";;
let s = Lexer.tokens_stream "test.lus";;
let rec fn n = if n = 0 then Datatypes.O else Datatypes.S (fn (n - 1));;
let r = Parser.translation_unit_file (fn 100) s;;
let Parser.Parser.Inter.Parsed_pr (r', s') = r;;
let r'' = (Obj.magic r' : Ast.declaration list);;
```

