Require Import List.
Require Import Cpo Reset SDfuns.
Import ListNotations.

(** An attempt to prove the equivalence between the reset construct
    of Lucid Synchrone and the one of Denot.SDfuns. *)

(* In "Modular Resetting of Synchronous Data-Flow Programs",
   Hamon & Pouzet encode the reset in two functions:

  let whilenot c = o where
    rec o = true -> if c then false else pre o

  let rec reset_up c x =
    let cond = whilenot c in
    merge cond
      (up (x when cond))
      (reset_up (c when not cond) (x when not cond))


  In Lustre (thèse de Lélio p.39), it gives :

  node true_until(r: bool) returns (c: bool)
  let
    c = true -> if r then false else (pre c);
  tel

  node reset_f(x: int; r: bool) returns (y: int)
  var c: bool;
  let
    c = true_until(r);
    y = merge c (f(x when c)) (reset_f((x, r) when not c));
  tel
 *)


(* en Vélus ?? :

   c = if r then false else (true fby c)

   ou bien, pour faire le même premier instant que LS :

   c = true -> if r then false else (true fby c)
 *)

(* case booléen : if-then-else *)
Definition scaseb {A} := @scase A bool bool Some bool_eq [true;false].

(* when/merge booléen *)
Definition swhenb {A} := @swhen A bool bool Some bool_eq.
Definition smergeb {A} := @smerge A bool bool Some bool_eq [true;false].

(* on part d'une fonction de flots *)
Module VERSION2.

Parameter (I A : Type).
Definition SI := fun _ : I => sampl A.
Definition DS_prod := @DS_prod I.

Parameter (f : DS (sampl A) -C-> DS (sampl A)).

(* environnement où tous les flots sont égaux à l'entrée *)
Definition env1 : DS (sampl A) -c> DS_prod SI :=
  Dprodi_DISTR _ _ _ (fun _ => ID _).

(* f appliqué aux environnements *)
Definition fs : DS_prod SI -C-> DS_prod SI := DMAPi (fun _ => f).

Definition true_until : DS (sampl bool) -C-> DS (sampl bool).
  refine (FIXP _ _).
  apply curry.
  refine ((scaseb @2_ SND _ _) _).
  refine ((PAIR _ _ @2_ _) _).
  - (* true *)
    refine (sconst false @_ AC @_ SND _ _).
  - (* false *)
    refine ((fby @2_ sconst true @_ AC @_ SND _ _) _).
    refine ((AP _ _ @2_ FST _ _) (SND _ _)).
Defined.

Lemma true_until_eq :
  forall r, true_until r == scaseb r (sconst false (AC r),
                           fby (sconst true (AC r)) (true_until r)).
Proof.
  intros.
  unfold true_until at 1.
  rewrite FIXP_eq.
  reflexivity.
Qed.

(* c = true_until(r); *)
(* y = merge c (f(x when c)) (reset_f((x, r) when not c)); *)

  (* reset à la lucid synchrone *)
Definition reset : DS (sampl bool) -C-> DS (sampl A) -C-> DS (sampl A).
  refine (FIXP _ _).
  apply curry, curry.
  match goal with
  | |- _ (_ (Dprod ?pl ?pr) _) =>
      pose (freset := FST _ _ @_ FST pl pr)
      ; pose (r := SND _ _ @_ FST pl pr)
      ; pose (x := SND pl pr)
      ; pose (c := true_until @_ r)
  end.
  refine ((smergeb @2_ c) _).
  refine ((PAIR _ _ @2_ _) _).
  - (* true *)
    refine (f @_ (swhenb true @2_ x) c).
  - (* false *)
    refine ((AP _ _ @3_ freset)
              ((swhenb false @2_ r) c)
              ((swhenb false @2_ x) c)).
Defined.

Lemma reset_eq :
  forall r x,
    reset r x ==
      let c := true_until r in
      smergeb c
        (f (swhenb true x c),
          reset (swhenb false r c)  (swhenb false x c)).
Proof.
  intros.
  unfold reset at 1.
  rewrite FIXP_eq.
  reflexivity.
Qed.

Theorem reset_match :
  forall rs xs o, reset rs xs == sreset fs (AC rs) (env1 xs) o.
Proof.
  (* TODO ! *)
Qed.

End VERSION2.


(* on part d'une fonction d'environments *)
Module VERSION1.
Parameter (I A : Type).
Definition SI := fun _ : I => sampl A.
Definition DS_prod := @DS_prod I.

Parameter (f : DS_prod SI -C-> DS_prod SI).
Parameter (f_i f_o : I). (* nom de l'entrée et de la sortie dans f *)

(* environnement où tous les flots sont égaux à l'entrée *)
Definition env1 : DS (sampl A) -c> DS_prod SI :=
  Dprodi_DISTR _ _ _ (fun _ => ID _).

Definition fs : DS (sampl A) -C-> DS (sampl A) :=
  PROJ _ f_o @_ f @_ env1.


(* reset à la lucid synchrone *)
Parameter reset : DS bool -C-> DS (sampl A) -C-> DS (sampl A).

Theorem reset_match :
  forall r X, reset r (X f_i) == sreset f r X f_o.
Abort.
End VERSION1.





(* avec échantillonnage *)
Definition true_until : DS (sampl bool) -C-> DS (sampl bool).
  refine (FIXP _ _).
  apply curry.
  refine ((arrow @2_ _) _).
  - refine (sconst true @_ AC @_ SND _ _).
  - refine
      ((ZIP  (fun va vb => match va,vb with
                            | abs, abs => abs
                            | pres a, pres b => pres (andb (negb a) b)
                            | _,_ => err error_Cl
                        end) @2_ SND _ _) _).
    refine ((fby @2_ sconst false @_ AC @_ SND _ _) _).
    refine ((AP _ _ @2_ FST _ _) (SND _ _)).
Defined.

Lemma true_until_eq :
  forall rs, true_until rs ==
          arrow (sconst true (AC rs))
            (ZIP (fun va vb => match va,vb with
                            | abs, abs => abs
                            | pres a, pres b => pres (andb (negb a) b)
                            | _,_ => err error_Cl
                            end)
               rs (fby (sconst false (AC rs)) (true_until rs))).
Proof.
  intros.
  unfold true_until at 1.
  rewrite FIXP_eq.
  reflexivity.
Qed.



Context {I A : Type}.
Definition SI := fun _ : I => sampl A.

Parameter (f : DS_prod SI -C-> DS_prod SI).

(* ≈ Denot.sbool_of *)
Definition sbool_of : DS (sampl bool) -C-> DS bool :=
  MAP (fun v => match v with
             | pres true => true
             | _ => false
             end).

(* merge booléen *)
Definition smergeb := @smerge A bool bool Some bool_eq [true;false].

Lemma resetls :
  forall rs X i,
    let cs := true_until rs in
    sreset f (sbool_of rs) X i
    == smergeb rs (f env_of_np ).

Search smerge.






Section ARROW.
Context {A : Type}.

(* case booléen : if-then-else *)
Definition scaseb := @scase A bool bool Some bool_eq [true;false].

Definition arrow : DS (sampl A) -C-> DS (sampl A) -C-> DS (sampl A).
  apply curry.
  refine ((scaseb @2_ _) (ID _)).
  refine ((fby @2_ sconst true @_ AC @_ FST _ _)
            (sconst false @_ AC @_ FST _ _)).
Defined.

Lemma arrow_eq :
  forall s0 s1,
    let bs := AC s0 in
    arrow s0 s1 = scaseb (fby (sconst true bs) (sconst false bs)) (s0, s1).
Proof.
  reflexivity.
Qed.
End ARROW.




(* version booléenne conne *)
Module TRUE_UNTIL1.
Definition true_until : DS bool -C-> DS bool.
  refine (FIXP _ _).
  apply curry.
  refine (CONS true @_ _).
  refine ((ZIP andb @2_ MAP negb @_ REM _ @_ SND _ _) _).
  refine ((AP _ _ @2_ FST _ _) (REM _ @_ SND _ _)).
Defined.

Lemma true_until_eq :
  forall rs, true_until rs == cons true (ZIP andb (map negb (rem rs)) (true_until (rem rs))).
Proof.
  intro.
  unfold true_until at 1.
  rewrite FIXP_eq; auto.
Qed.
End TRUE_UNTIL1.
