
From Coq Require Import BinNums.

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

(* Named clocks, as opposed to (stream) clocks, are used to track
   interdependencies in clock annotations internal to expressions. *)

Inductive ckid : Type :=
| Vidx : positive -> ckid     (* fresh clock *)
| Vnm  : ident    -> ckid.    (* named clock *)

Inductive sclock : Type :=
| Sbase : sclock                            (* base clock *)
| Son   : sclock -> ckid -> bool -> sclock. (* subclock *)

Inductive nclock : Type :=
| Cstream : sclock -> nclock             (* (unnamed) stream clock *)
| Cnamed  : ckid -> sclock -> nclock.    (* named clock: (c : s) or (i : s) *)

Fixpoint sclk (ck: clock) : sclock :=
  match ck with
  | Cbase => Sbase
  | Con ck x b => Son (sclk ck) (Vnm x) b
  end.

From Coq Require Import List.
Import ListNotations.

Fixpoint indexes (ncks: list nclock) : list positive :=
  match ncks with
  | [] => []
  | Cnamed (Vidx i) _ :: ncks => i :: indexes ncks
  | _ :: ncks => indexes ncks
  end.

Definition stripname (ck: nclock) : sclock :=
  match ck with
  | Cstream sck => sck
  | Cnamed _ sck => sck
  end.

