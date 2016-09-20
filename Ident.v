Require Import Rustre.Common.
Require Import String.
Require Import List.
Import List.ListNotations.

Axiom pos_to_str: ident -> string.
Axiom pos_of_str: string -> ident.

Module Export Ids <: IDS.
  Definition self := pos_of_str "self".
  Definition out := pos_of_str "out".             

  Definition step := pos_of_str "step".
  Definition reset := pos_of_str "reset".

  Definition reserved : list ident := [ self; out ].

  Definition methods  : list ident := [ step; reset ].

  Lemma reserved_nodup: NoDup reserved. Admitted.
  Lemma methods_nodup: NoDup methods. Admitted.

  Definition NotReserved {typ: Type} (xty: ident * typ) : Prop :=
    ~In (fst xty) reserved.
End Ids.