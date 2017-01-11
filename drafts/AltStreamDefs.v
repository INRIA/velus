Require Import Coq.FSets.FMapPositive.
Require Import Velus.Common.
Require Import Velus.NLustre.NLSyntax.

Inductive value :=
  | absent
  | present (v : const).
Coercion present : const >-> value.

Module PM := PositiveMap.

Definition stream := nat -> value.
Definition cstream := nat -> bool.
Definition history := PM.t stream.
Definition global := PM.t node.

(** Synchronous functions *)

(* 1. Version from velus-complete / paper.
      Model = finite lists, earliest first.
      nat3 = [0; 1; 2; 3 ] *)

Definition LList := List.list.
Definition SS := LList value.
Open Scope list.

Fixpoint fby (v0: const) (s: SS) : SS :=
  match s with
  | present v :: s => present v0 :: fby v s
  | absent :: s => absent :: fby v0 s
  | nil => nil
  end.

Definition n3 :=    present (Cint 0)
                 :: present (Cint 1)
                 :: absent
                 :: present (Cint 2)
                 :: present (Cint 3)
                 :: absent
                 :: absent
                 :: present (Cint 4)
                 :: nil.

Definition fby_0_n3 :=
                    present (Cint 0)
                 :: present (Cint 0)
                 :: absent
                 :: present (Cint 1)
                 :: present (Cint 2)
                 :: absent
                 :: absent
                 :: present (Cint 3)
                 :: nil.

Eval simpl in fby (Cint 0) n3.

Lemma fby_n31: fby (Cint 0) n3 = fby_0_n3.
Proof.
  unfold fby_0_n3; reflexivity.
Qed.

(* Definition from velus-complete (without syntax) *)
Inductive fbyS : const -> SS -> SS -> Prop :=
| fbyS0:
   forall v,
    fbyS v nil nil
| fbyS1:
   forall v xs ys,
    fbyS v xs ys ->
    fbyS v (absent::xs) (absent::ys)
| fbyS2:
   forall v v0 xs ys,
    fbyS v0 xs ys ->
    fbyS v (present v0::xs) (present v::ys).

Lemma fbyS_is_fby: forall v0 xs ys, (fbyS v0 xs ys) <-> (fby v0 xs = ys).
Proof.
  split.
  - generalize ys v0.
    clear ys v0.
    induction xs.
    + intros ys v0 H.
      inversion H.
      reflexivity.
    + intros ys v0 H.
      inversion H.
      * elim (IHxs ys0 v0 H4).
        reflexivity.
      * elim (IHxs ys0 v1 H4).
        reflexivity.
  - generalize ys v0.
    clear ys v0.
    induction xs.
    + intros ys v0 H.
      rewrite <- H.
      apply fbyS0.
    + intros ys v0.
      elim a.
      * intro H.
        rewrite <- H.
        simpl.
        apply fbyS1.
        apply IHxs.
        reflexivity.
      * intros v H.
        rewrite <- H.
        simpl.
        apply fbyS2.
        apply IHxs.
        reflexivity.
Qed.        

(* 2. Version from velus-lsni (Cedric).
      Model = finite lists, last first.
      nat3 = [3; 2; 1; 0]

   Cedric argues that the backward definition makes it easy to denote the
   previous value of a stream, and that it is rare to need to denote the
   first value of a stream. But this model is counter-intuitive and more
   complicated (see the following definition of fby). I do not understand
   the advantages.

   fbyC v0 s1 v1 s2
   "s2 is a shifted version of s1, keeping absences in place"
   v0 is the initial value
   v1 is the first present value of s2
 *)

Inductive fbyC (v0: const) : SS -> const -> SS -> Prop :=
| fbyC0:
    fbyC v0 nil    v0 nil
| fbyC1:
    forall xs w ys,
      fbyC v0 xs    w ys ->
      fbyC v0 (absent :: xs)    w (absent :: ys)
| fbyC2:
    forall u w xs ys,
      fbyC v0 xs    w ys ->
      fbyC v0 (present u :: xs)    u (present w :: ys).

(* 3. Version nat -> value with auxiliary hold function. *)

Inductive holdI (v0: const) (xs: stream) : nat -> value -> Prop :=
| holdI0:
    holdI v0 xs 0 v0
| holdI_absent:
    forall v n,
      xs n = absent ->
      holdI v0 xs n v ->
      holdI v0 xs (S n) v
| holdI_present:
    forall n,
      xs n <> absent ->
      holdI v0 xs (S n) (xs n).

Inductive fbyI (v0: const) (xs: stream) : nat -> value -> Prop :=
| fbyI_absent:
    forall n,
      xs n = absent ->
      fbyI v0 xs n absent
| fbyI_present:
    forall v n,
      xs n <> absent ->
      holdI v0 xs n v ->
      fbyI v0 xs n v.

Fixpoint holdIF (v0: const) (s: stream) (n: nat) : value :=
  match n with
  | 0 => v0
  | S m => match s m with
           | absent => holdIF v0 s m
           | hv => hv
           end
  end.

Definition fbyIF (v0: const) (s: stream) (n: nat) : value :=
  match s n with
  | absent => absent
  | _ => holdIF v0 s n
  end.

(* 4. Version nat -> value with carried next value. *)

Inductive fbyI' (v0: const) (xs: stream) : const -> nat -> value -> Prop :=
| fbyI'_absent0:
    xs 0 = absent ->
    fbyI' v0 xs v0    0 absent
| fbyI'_present0:
    forall nv,
    xs 0 = present nv ->
    fbyI' v0 xs nv    0 (present v0)
| fbyI'_absentS:
    forall n nv lv,
    xs (S n) = absent ->
    fbyI' v0 xs nv   n lv ->
    fbyI' v0 xs nv   (S n) absent
| fbyI'_presentS:
    forall n v nv lv,
    xs (S n) = present v ->
    fbyI' v0 xs nv   n lv ->
    fbyI' v0 xs v    (S n) nv.

Fixpoint fbyIF'' (v0: const) (xs: stream) (n: nat) : const * value :=
  match n with
  | 0 => match xs 0 with
         | absent => (v0, absent)
         | present v => (v, present v0)
         end
  | S m => match xs n with
           | absent => (fst (fbyIF'' v0 xs m), absent)
           | present v => (v, present (fst (fbyIF'' v0 xs m)))
           end
  end.

Definition fbyIF' (v0: const) (xs: stream) (n: nat) : value :=
  snd (fbyIF'' v0 xs n).

(* 5. Version with coinductive streams
      (for completeness) *)

Require Coq.Lists.Streams.

Definition costream := Streams.Stream value.
Definition cohd := Streams.hd (A := value).
Definition cotl := Streams.tl (A := value).
Definition Cocons := Streams.Cons (A := value).

CoFixpoint cofby (v0: const) (s: costream) : costream :=
  match cohd s with
  | present v => Cocons (present v0) (cofby v (cotl s))
  | absent => Cocons absent (cofby v0 (cotl s))
  end.

Definition whenS (c: bool) (sa: stream) (sb: stream) (n: nat) : value :=
  match sb n with
  | absent => absent
  | present vb => match vb with
                  | Cbool b => if bool_eq b c then sa n else absent
                  | _ => absent
                  end
  end.

Definition nat_stream : stream := (fun n => Cint (BinInt.Z_of_nat n)).
Definition even_ticks : stream := (fun n => Cbool (NPeano.even n)).
Definition even_stream : stream := whenS true nat_stream even_ticks.
Definition fby_even_stream : stream := fbyIF (Cint 0) even_stream.

Eval lazy in (even_stream 0, fby_even_stream 0).
Eval lazy in (even_stream 1, fby_even_stream 1).
Eval lazy in (even_stream 2, fby_even_stream 2).
Eval lazy in (even_stream 3, fby_even_stream 3).
Eval lazy in (even_stream 4, fby_even_stream 4).
Eval lazy in (even_stream 5, fby_even_stream 5).
Eval lazy in (even_stream 6, fby_even_stream 6).

