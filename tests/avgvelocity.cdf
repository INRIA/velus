node counter (ini:int, inc:int, restart:bool) returns (n:int)
vars c:int;
let
  c :: base = 0 fby n;
  n :: base = if restart then ini else (c + inc);
tel;

node avgvelocity (delta:int, sec:bool) returns (v:int)
vars h:int, t:int, r:int;
let
  h :: base = 0 fby v;
  v :: base = merge sec ((r when sec) / t) (h whennot sec);
  t :: base on sec = counter (0 when sec, 1 when sec, false when sec);
  r :: base = counter (0, delta, false);
tel;