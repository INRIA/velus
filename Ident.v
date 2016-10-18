Require Import Rustre.Common.
Require Import String.
Require Import List.
Import List.ListNotations.

Axiom pos_to_str: ident -> string.
Axiom pos_of_str: string -> ident.

Axiom pos_to_str_injective:
  forall x x',
    pos_to_str x = pos_to_str x' ->
    x = x'.
Axiom pos_of_str_injective:
  forall x x',
    pos_of_str x = pos_of_str x' ->
    x = x'.

Module Export Ids <: IDS.
  Definition self := pos_of_str "self".
  Definition out := pos_of_str "out".             
  Definition main_id: ident := pos_of_str "main".
  Definition fun_id: ident  := pos_of_str "fun".
  
  Definition step := pos_of_str "step".
  Definition reset := pos_of_str "reset".

  Definition reserved : list ident := [ self; out ].

  Definition methods  : list ident := [ step; reset ].

  Lemma reserved_nodup: NoDup reserved.
  Proof.
    constructor.
    - inversion_clear 1 as [E|Hin].
      + unfold out, self in E.
        apply pos_of_str_injective in E.
        discriminate.
      + contradict Hin.
    - repeat constructor; auto.
  Qed.

  Lemma methods_nodup: NoDup methods.
  Proof.
    constructor.
    - inversion_clear 1 as [E|Hin].
      + unfold reset, step in E.
        apply pos_of_str_injective in E.
        discriminate.
      + contradict Hin.
    - repeat constructor; auto.
  Qed.

  Lemma fun_not_out: fun_id <> out.
  Proof.
    intro E; unfold fun_id, out in E.
    apply pos_of_str_injective in E.
    discriminate.    
  Qed.
  
  Definition NotReserved {typ: Type} (xty: ident * typ) : Prop :=
    ~In (fst xty) reserved.
End Ids.

Definition prefix (pre id: ident) :=
  pos_of_str (pos_to_str pre ++ "$" ++ pos_to_str id).

Definition prefix_fun (c f: ident): ident :=
  prefix fun_id (prefix c f).
Definition prefix_out (o f: ident): ident :=
  prefix out (prefix o f).
  
Lemma prefix_injective:
  forall pref id pref' id',
    prefix pref id = prefix pref' id' ->
    pref = pref' /\ id = id'.
Proof.
  unfold prefix.
  intros ** H.
  apply pos_of_str_injective in H.
  admit.
Qed.

Lemma prefix_fun_injective: 
 forall c c' f f',
   prefix_fun c f = prefix_fun c' f' -> c = c' /\ f = f'.
Proof.
  unfold prefix_fun.
  intros ** Eq.
  apply prefix_injective in Eq; destruct Eq as [E Eq]; clear E.
  now apply prefix_injective.
Qed.

Lemma prefix_out_injective: 
 forall c c' f f',
   prefix_out c f = prefix_out c' f' -> c = c' /\ f = f'.
Proof.
  unfold prefix_out.
  intros ** Eq.
  apply prefix_injective in Eq; destruct Eq as [E Eq]; clear E.
  now apply prefix_injective.
Qed.

Definition glob_id (id: ident): ident :=
  pos_of_str ("_" ++ (pos_to_str id)).
