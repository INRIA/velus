(* Taken from the examples of Lucid Synchrone v3 *)
(* A cruise control *)
(* $Id: cruise.ls,v 1.9 2009/02/07 04:35:35 gerard Exp $ *)

open Data
open Graphics

let static speedInc = 5.0
let static speedMax = 150.0
let static speedMin = 30.0
let static kp = 10.0
let static ki = 0.2

let node cruiseSpeedMgt (onn, set, quickAccel, quickDecel, speed) =
  cruise_speed where
  rec
    l1 = l3 +. speedInc
  and
    l2 = l3 -. speedInc
  and 
    cruise_speed = 
      if quickDecel & (l2 >= speedMin)
      then l2
      else if quickAccel & (l1 <= speedMax)
      then l1
      else if (onn or set) & (speed <= speedMax) & (speed >= speedMin)
      then speed else l3
  and
    l3 = 0.0 -> pre cruise_speed

(* a PI regulation *)
let node regulator (cruise_speed, speed) = throttle where
  rec
      delta = cruise_speed -. speed
  and 
      throttle = delta *. kp +. aux *. ki
  and
      aux = delta +. (0.0 -> pre aux)
 
let node cruiseControl (onn, off, resume, speed, set, quickAccel, quickDecel, accel, brake) =
  (cruiseSpeed, throttleCmd) where
  rec 
    last cruiseSpeed = 0.0
  and 
    braking = brake > 0.0
  and
    accelerator = accel > 0.0
  and 
      automaton
        Off ->  
          do throttleCmd = accel until onn then On
      | On ->
          do automaton
               Regulation ->
                 let 
                     cruise_speed = 
                      cruiseSpeedMgt(onn, set, quickAccel, quickDecel, speed)
                 and
                     between = (speed >= speedMin) & (speed <= speedMax) in
                 do
                   cruiseSpeed = cruise_speed
                 and
                   automaton
                       RegulOn ->
                         do
                           throttleCmd = regulator(cruise_speed, speed)
                         until (accelerator or not between) then StandBy
                     | StandBy ->
                         do 
                           throttleCmd = accel
                         until
                           (not accelerator & between) then RegulOn
                   end
                 until braking then Interrupt
             | Interrupt ->
                                do throttleCmd = accel
                                
                                until resume then Regulation
                end
                        until off then Off
      end

type button = Up | Down

(* make an interface for continuous inputs *)
let node button init step key  = o where
  rec
      last o = init
  and 
      present 
        key(v) ->
          do match v with 
               Up -> do o = last o +. step done
             | Down -> do o = last o -. step done
             end
          done
      end

(* make the interface for manual testing *)
(* all the inputs are given through the keyboard *)
let node interface key =
  let
      match key with
        None -> do done
      | Some(v) ->
          do match v with
               'o' -> do emit onn = () done
             | 'f' -> do emit off = () done
             | 's' -> do emit set = () done
             | 'r' -> do emit resume = () done
             | 'a' -> do emit quickAccel = () done
             | 'd' -> do emit quickDecel = () done
             | '+' -> do emit speed = Up done
             | '-' -> do emit speed = Down done
             | 'b' -> do emit brake = () done
             | _ -> do done
             end
          done
      end in
  let onn = ? onn
  and off = ? off
  and set = ? set
  and resume = ? resume
  and quickAccel = ? quickAccel
  and quickDecel = ? quickDecel in
  let speed = button 0.0 2.0 speed in
  let accel = 0.0 -> speed -. pre speed in
  let brake = if ? brake then 1.0 else 0.0 in
  (onn, off, set, resume, quickAccel, quickDecel,
   speed, accel, brake)

(* plot function *)
let node plot lx ly (bx, by) (x, y) =
  plot (bx + (x mod lx)) (by + (y mod ly))

let node main () =
  (* read the keyboard *)
  let key = None -> keyboard () in
  let (onn, off, set, resume, quickAccel, quickDecel,
       speed, accel, brake) = interface key in
  let (cruiseSpeed, throttleCmd) =
    cruiseControl (onn, off, resume,
                   speed, set, quickAccel,
                   quickDecel, accel, brake) in
  print_string "cruiseSpeed = ";
  let rec nat = 0 -> if pre nat = 300 then 0 else pre nat + 1 in
  plot 300 100 (0,0) (nat, int_of_float speed);
  plot 300 100 (0,100) (nat, int_of_float accel);
  plot 300 100 (0,200) (nat, int_of_float cruiseSpeed);
  plot 300 100 (0,300) (nat, int_of_float throttleCmd);
  (* print_float cruiseSpeed; *)
  print_float cruiseSpeed;
  print_string "throttleCmd = ";
  print_float throttleCmd;
  print_newline ()

