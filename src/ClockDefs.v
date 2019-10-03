From Coq Require Import BinNums.
From Coq Require Import List.

Definition ident := positive.

(* Basic definitions around Clocks with minimal dependencies to facilitate
   extraction. Properties and lemmas are found in Clocks.v *)

Inductive clock : Type :=
| Cbase : clock                            (* base clock *)
| Con   : clock -> ident -> bool -> clock. (* subclock *)

(** ** Instantiate variable clocks from a base clock and substitution *)
Fixpoint instck (bk: clock) (sub: ident -> option ident) (ck: clock)
                                                           : option clock :=
  match ck with
  | Cbase => Some bk
  | Con ck x b => match instck bk sub ck, sub x with
                  | Some ck', Some x' => Some (Con ck' x' b)
                  | _, _ => None
                  end
  end.

(* Named clocks *)

(* Named clocks are used to track  interdependencies in clock
   annotations internal to expressions. *)

Definition nclock : Type := clock * option ident.

Definition stripname : nclock -> clock := fst.

Definition indexes (ncks : list nclock) : list positive :=
  fold_right (fun nck acc => match snd nck with None => acc | Some nm => nm::acc end)
             nil ncks.

