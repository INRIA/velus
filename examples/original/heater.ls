(* my heater at home *)
(* $Id: heater.ls,v 1.10 2009-02-04 21:54:09 pouzet Exp $ *)
open Chrono
open Graphics

let static low = 4
let static high = 4

let static delay_on = 30 
let static delay_off = 10

(* [edge x] returns the rising edge *)
let node edge x = false -> not (pre x) & x

(* [count d t] returns [true] when [d] occurrences of [t] has been received*)
let node count d t = ok where
  rec ok = edge (false -> (pre cpt = d - 1))
  and cpt = 0 -> (if t then pre cpt + 1 else pre cpt) mod d

(* controling the heat *)
(* returns [true] when [expected_temp] does not agree with [actual_temp] *)
(* we introduce an hysteresis to avoir oscilation *)
let node heat expected_temp actual_temp = ok where
  rec ok = if actual_temp <= expected_temp - low then true
           else if actual_temp >= expected_temp + high then false
           else false -> pre ok

(* controling the heat according to a tracking error *)
(* [error = expected_temp - actual_temp] *)
(* returns [true] when [expected_temp] does not agree with [actual_temp] *)
(* we introduce an hysteresis to avoir oscilation *)
let node heat error = ok where
  rec ok = if low <= error then true
           else if - high >= error then false
           else false -> pre ok

(* the same function using two modes *)
let node heat expected_temp actual_temp = ok where
  rec automaton
	False -> 
	  do ok = false 
	  unless (actual_temp <= expected_temp - low) then True
      | True ->
	  do ok = true 
	  unless (actual_temp >= expected_temp + high) then False
      end

let node heat error = ok where
  rec automaton
	False -> 
	  do ok = false 
	  unless (low <= error) then True
      | True ->
	  do ok = true 
	  unless (- high >= error) then False
      end

(* a cyclic two mode automaton with an internal timer *)
(* [open_light = true] and [open_gas = true] for [delay_on time] *)
(* then [open_light = false] and [open_gas = false] for *)
(* [delay_off time] *)
let node command time = (open_light, open_gas) where
  rec automaton
	Open ->
	  do open_light = true
	  and open_gas = true
	  until (count delay_on time) then Silent
      | Silent ->
	  do open_light = false
	  and open_gas = false
	  until (count delay_off time) then Open
      end


(* the main command which control the opening of the light and gas *)
(* [on_heat] indicates that the water must be heated *)
(* at most three test must be made. At the end, if [on_light] is false *)
(* the system must be blocked into a security stop *)
let node light time on_heat on_light = (open_light, open_gas, nok) 
where
  rec automaton
	Off_light ->
          do nok = false
	  and open_light = false
	  and open_gas = false
	  until on_heat then Try
      | On_light ->
          do nok = false
          and open_light = false
          and open_gas = true
          until (not on_heat) then Off_light
      | Try ->
	  do
	    (open_light, open_gas) = command time
	  until on_light then On_light
          until (count 4 (edge (not open_light))) then Failure
      | Failure ->
	  do nok = true 
	  and open_light = false
	  and open_gas = false
	  done
      end

(* the main function *)
let node controller1 time restart expected_temp actual_temp on_light =
                                       (open_light, open_gas, ok, nok) where
  rec reset
	error = expected_temp - actual_temp
      and
         on_heat = heat error
      and
        (open_light, open_gas,nok) = light time on_heat on_light
      and
        ok = not nok       
      every restart

let node controller time restart expected_temp actual_temp on_light =
                                       (open_light, open_gas, ok, nok) where
  rec automaton
      S ->
	let error = expected_temp - actual_temp in
	let on_heat = heat error in
	do
	  (open_light, open_gas,nok) = light time on_heat on_light
	and
          ok = not nok
	unless restart then S
    end

