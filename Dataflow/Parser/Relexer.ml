
let map_token (Specif.Coq_existT (tok, l) : Parser.Aut.GramDefs.token) =
  let loc l = (Obj.magic l : Ast.astloc) in
  let open Parser.Aut.GramDefs in
  match tok with
  | AND't       -> Parser2.AND       (loc l)
  | BOOL't      -> Parser2.BOOL      (loc l)
  | COLON't     -> Parser2.COLON     (loc l)
  | COMMA't     -> Parser2.COMMA     (loc l)
  | CONSTANT't  -> Parser2.CONSTANT  (Obj.magic l : Ast.constant * Ast.astloc)
  | DOT't       -> Parser2.DOT       (loc l)
  | ELSE't      -> Parser2.ELSE      (loc l)
  | EOF't       -> Parser2.EOF
  | EQ't        -> Parser2.EQ        (loc l)
  | FALSE't     -> Parser2.FALSE     (loc l)
  | FBY't       -> Parser2.FBY       (loc l)
  | FLOAT32't   -> Parser2.FLOAT32   (loc l)
  | FLOAT64't   -> Parser2.FLOAT64   (loc l)
  | GEQ't       -> Parser2.GEQ       (loc l)
  | GT't        -> Parser2.GT        (loc l)
  | IF't        -> Parser2.IF        (loc l)
  | INT16't     -> Parser2.INT16     (loc l)
  | INT32't     -> Parser2.INT32     (loc l)
  | INT64't     -> Parser2.INT64     (loc l)
  | INT8't      -> Parser2.INT8      (loc l)
  | LAND't      -> Parser2.LAND      (loc l)
  | LEQ't       -> Parser2.LEQ       (loc l)
  | LET't       -> Parser2.LET       (loc l)
  | LNOT't      -> Parser2.LNOT      (loc l)
  | LOR't       -> Parser2.LOR       (loc l)
  | LPAREN't    -> Parser2.LPAREN    (loc l)
  | LSL't       -> Parser2.LSL       (loc l)
  | LSR't       -> Parser2.LSR       (loc l)
  | LT't        -> Parser2.LT        (loc l)
  | LXOR't      -> Parser2.LXOR      (loc l)
  | MERGE't     -> Parser2.MERGE     (loc l)
  | MINUS't     -> Parser2.MINUS     (loc l)
  | MOD't       -> Parser2.MOD       (loc l)
  | NEQ't       -> Parser2.NEQ       (loc l)
  | NODE't      -> Parser2.NODE      (loc l)
  | NOT't       -> Parser2.NOT       (loc l)
  | ON't        -> Parser2.ON        (loc l)
  | ONOT't      -> Parser2.ONOT      (loc l)
  | OR't        -> Parser2.OR        (loc l)
  | PLUS't      -> Parser2.PLUS      (loc l)
  | RETURNS't   -> Parser2.RETURNS   (loc l)
  | RPAREN't    -> Parser2.RPAREN    (loc l)
  | SEMICOLON't -> Parser2.SEMICOLON (loc l)
  | SLASH't     -> Parser2.SLASH     (loc l)
  | STAR't      -> Parser2.STAR      (loc l)
  | TEL't       -> Parser2.TEL       (loc l)
  | THEN't      -> Parser2.THEN      (loc l)
  | TRUE't      -> Parser2.TRUE      (loc l)
  | UINT16't    -> Parser2.UINT16    (loc l)
  | UINT32't    -> Parser2.UINT32    (loc l)
  | UINT64't    -> Parser2.UINT64    (loc l)
  | UINT8't     -> Parser2.UINT8     (loc l)
  | VAR't       -> Parser2.VAR       (loc l)
  | VAR_NAME't  -> Parser2.VAR_NAME (Obj.magic l : Ast.string * Ast.astloc)
  | WHEN't      -> Parser2.WHEN      (loc l)
  | WHENOT't    -> Parser2.WHENOT    (loc l)
  | XOR't       -> Parser2.XOR       (loc l)
