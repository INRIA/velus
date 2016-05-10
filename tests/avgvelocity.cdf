node counter (initial:int, increment:int, restart:bool) returns (n:int);
let
  c :: base = 0 fby (n:int);
  n :: base = if (restart:bool) then (initial:int) else ((c:int) + (increment:int) : int);
tel;

node avgvelocity (delta:int, sec:bool) returns (v:int);
let
  h :: base = 0 fby (v:int);
  v :: base = merge (sec:bool) ((((r:int) when sec) / (t:int) : int)) ((h:int) whennot sec);
  t :: base on sec = counter ((0:int) when sec, (1:int) when sec, (false:bool) when sec) : int;
  r :: base = counter ((0:int), (delta:int), (false:bool)) : int;
tel;