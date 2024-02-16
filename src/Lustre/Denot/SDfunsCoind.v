Inductive error := error_Ty | error_Cl | error_Op.

Inductive sampl (A : Type) : Type := abs | pres (a: A) | err  (e : error).
Arguments abs  {A}.
Arguments pres {A} a.
Arguments err  {A} e.

Require Import Streams.

Definition AC {A} (rs : Stream (sampl A)) :=
  map (fun v => match v with pres _ => true | _ => false end) rs.

Definition const {A} (c : A) (rs : Stream bool) : Stream (sampl A) :=
  map (fun r:bool => if r then pres c else abs) rs.

CoFixpoint fby1 {A} (v : A) (xs ys : Stream (sampl A)) : Stream (sampl A) :=
  match xs with
  | Cons abs xs => Cons abs
                    (* inline (fby1AP (Some _)) *)
                    (match ys with
                     | Cons abs ys => fby1 v xs ys
                     | Cons (err e) _ => map (fun _ => err e) xs
                     | Cons (pres _) _ => map (fun _ => err error_Cl) xs
                     end)
  | Cons (pres x) xs => Cons (pres v)
                    (* inline (fby1AP None) *)
                    (match ys with
                     | Cons (pres y) _ => fby1 y xs ys
                     | Cons abs ys => map (fun _ => err error_Cl) xs
                     | Cons (err e) _ => map (fun _ => err e) xs
                     end)
  | Cons (err e) xs => map (fun _ => err e) xs
  end.

CoFixpoint fby {A} (xs ys : Stream (sampl A)) :=
  match xs with
  | Cons abs xs => Cons abs
                    (* inline fbyA *)
                    (match ys with
                     | Cons abs ys => fby xs ys
                     | Cons (err e) _ => map (fun _ => err e) xs
                     | Cons (pres _) _ => map (fun _ => err error_Cl) xs
                     end)
  | Cons (pres v) xs => Cons (pres v)
                    (* inline (fby1AP None) *)
                    (match ys with
                     | Cons (pres y) ys => fby1 y xs ys
                     | Cons abs ys => map (fun _ => err error_Cl) xs
                     | Cons (err e) _ => map (fun _ => err e) xs
                     end)
  | Cons (err e) xs => map (fun _ => err error_Cl) xs
  end.

Fail CoFixpoint true_until (rs : Stream (sampl bool)) : Stream (sampl bool) :=
  match rs with
  | Cons (pres r) rs => if r then const false (AC rs)
                       else fby (const true (AC rs)) (true_until (Cons (pres r) rs))
  | Cons r rs => Cons r (true_until rs)
  end.
