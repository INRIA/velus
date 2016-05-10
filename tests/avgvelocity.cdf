node counter (initial:int, increment:int, restart:bool) returns (n:int)
vars c:int;
let
  c :: base = 0 fby n;
  n :: base = if restart then initial else (c + increment);
tel;

node avgvelocity (delta:int, sec:bool) returns (v:int)
vars h:int, t:int, r:int;
let
  h :: base = 0 fby v;
  v :: base = merge sec ((r when sec) / t) (h whennot sec);
  t :: base on sec = counter (0 when sec, 1 when sec, false when sec) : int;
  r :: base = counter (0, delta, false) : int;
tel;