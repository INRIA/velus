Require Import Coq.FSets.FMapPositive.
Require Import List.
Require Import Rustre.Common.
Require Import Rustre.DataflowSyntax.


Definition alls {A B} (v : B) (l : list A) := List.map (fun _ => v) l.

Fixpoint map2 {A B C} (f : A -> B -> C) l1 l2 :=
  match l1, l2 with
    | nil, _ => nil
    | _, nil => nil
    | x1 :: l1, x2 :: l2 => f x1 x2 :: map2 f l1 l2
  end.

Lemma map2_nil {A B C} : forall (f : A -> B -> C) l1 l2, map2 f l1 l2 = nil <-> l1 = nil \/ l2 = nil.
Proof. intros f [| x1 l1] [| x2 l2]; simpl; try tauto. intuition discriminate. Qed.

Lemma map2_cons {A B C} : forall (f : A -> B -> C) l1 l2 y l, map2 f l1 l2 = y :: l <->
  exists x1 l1' x2 l2', l1 = x1 :: l1' /\ l2 = x2 :: l2' /\ y = f x1 x2 /\ map2 f l1' l2' = l.
Proof.
intros f [| x1 l1] [| x2 l2] y l; simpl; split; intro Heq; decompose [and ex] Heq; try now discriminate.
- inversion Heq. subst. repeat eexists; repeat split; eassumption.
- subst. inversion_clear H; inversion_clear H0 (* FIXME: generated names *). reflexivity.
Qed.


(** *  Dataflow semantics with lists  **)

(* Idea?: clocks, expressions -> instantaneous semantics
          equations -> list semantics *)
Inductive value :=
  | abs
  | here (v : const).
Coercion here : const >-> value.

Definition venv := PositiveMap.t value.
Definition history := list venv.


Definition instant_sem_var env x c := PositiveMap.find x env = Some (here c).

Definition sem_var (H : history) (x : ident) (cl : list value) : Prop :=
  List.map (PositiveMap.find x) H = List.map (@Some _) cl.

(** **  Semantics for one instant  **)

(** ***  Clock semantics  **)

Inductive instant_sem_clock (env : venv) : clock -> bool -> Prop :=
  | base: instant_sem_clock env Cbase true
  | on_tick: forall ck x b,
      instant_sem_clock env ck true ->
      PositiveMap.find x env = Some (here (Cbool b)) -> 
      instant_sem_clock env (Con ck x b) true
  | on_abs1 : forall ck x b,
      instant_sem_clock env ck false ->
      instant_sem_clock env (Con ck x b) false
  | on_abs2 : forall ck x c c',
      instant_sem_clock env ck true ->
      PositiveMap.find x env = Some (here c') -> 
      Cbool c <> c' ->
      instant_sem_clock env (Con ck x c) false.

(** ***  Expression semantics  **)

Inductive instant_sem_laexp (env : venv) : laexp -> value -> Prop :=
  | Stick : forall ck ce c,
      instant_sem_lexp env ce c ->
      instant_sem_clock env ck true ->
      instant_sem_laexp env (LAexp ck ce) c
  | Sabs : forall ck ce,
      instant_sem_lexp env ce abs ->
      instant_sem_clock env ck false ->
      instant_sem_laexp env (LAexp ck ce) abs

with instant_sem_lexp (env : venv) : lexp -> value -> Prop :=
  | Sconst : forall c, instant_sem_lexp env (Econst c) c
  | Svar : forall x c,
      instant_sem_var env x c ->
      instant_sem_lexp env (Evar x) c
  | Swhen_eq : forall s x b c,
      instant_sem_var env x  (Cbool b) ->
      instant_sem_laexp env s c ->
      instant_sem_lexp env (Ewhen s x b) c
  | Swhen_abs : forall s x b b',
      instant_sem_var env x (Cbool b') -> b <> b' ->
      instant_sem_lexp env (Ewhen s x b) abs.

Inductive instant_sem_caexp (env : venv) : caexp -> value -> Prop :=
  | SCtick : forall ck ce c,
      instant_sem_cexp env ce c ->
      instant_sem_clock env ck true ->
      instant_sem_caexp env (CAexp ck ce) c
  | SCabs : forall ck ce,
      instant_sem_cexp env ce abs ->
      instant_sem_clock env ck false ->
      instant_sem_caexp env (CAexp ck ce) abs

with instant_sem_cexp (env : venv) : cexp -> value -> Prop :=
  | Smerge_true : forall x t f c,
      instant_sem_var env x (Cbool true) ->
      instant_sem_caexp env t c ->
      instant_sem_cexp env (Emerge x t f) c
  | Smerge_false : forall x t f c,
      instant_sem_var env x (Cbool false) ->
      instant_sem_caexp env f c ->
      instant_sem_cexp env (Emerge x t f) c
  | Sexp : forall e c,
      instant_sem_lexp env e c ->
      instant_sem_cexp env (Eexp e) c.

(** **  Lifting to lists  **)

Inductive sem_clock : history -> clock -> list bool -> Prop :=
  | Snil_ck : forall ck, sem_clock nil ck nil
  | Scons_ck : forall env H ck b bl, 
      instant_sem_clock env ck b -> sem_clock H ck bl -> sem_clock (env :: H) ck (b :: bl).

Inductive sem_laexp : history -> laexp -> list value -> Prop :=
  | Snil_laexp : forall cae, sem_laexp nil cae nil
  | Scons_laexp : forall env H cae c cl,
      instant_sem_laexp env cae c -> sem_laexp H cae cl -> sem_laexp (env :: H) cae (c :: cl).

Inductive sem_lexp : history -> lexp -> list value -> Prop :=
  | Snil_lexp : forall ce, sem_lexp nil ce nil
  | Scons_lexp : forall env H ce c cl,
      instant_sem_lexp env ce c -> sem_lexp H ce cl -> sem_lexp (env :: H) ce (c :: cl).

Inductive sem_caexp : history -> caexp -> list value -> Prop :=
  | Snil_caexp : forall cae, sem_caexp nil cae nil
  | Scons_caexp : forall env H cae c cl,
      instant_sem_caexp env cae c -> sem_caexp H cae cl -> sem_caexp (env :: H) cae (c :: cl).

Inductive sem_cexp : history -> cexp -> list value -> Prop :=
  | Snil_cexp : forall cae, sem_cexp nil cae nil
  | Scons_cexp : forall env H ce c cl,
      instant_sem_cexp env ce c -> sem_cexp H ce cl -> sem_cexp (env :: H) ce (c :: cl).


(** Alternative definition by a forall on lists *)
Fixpoint for_all2 {A B} (P : A -> B -> Prop) l1 l2 :=
  match l1, l2 with
    | nil, nil => True
    | x1 :: l1, x2 :: l2 => P x1 x2 /\ for_all2 P l1 l2
    | _ :: _, nil => False
    | nil, _ :: _ => False
  end.

Lemma for_all2_length {A B} : forall (P : A -> B -> Prop) l1 l2, for_all2 P l1 l2 -> length l1 = length l2.
Proof.
intros P l1. induction l1 as [| x1 l1]; intros l2 Hall.
- destruct l2; trivial. now elim Hall.
- destruct l2; try now elim Hall. simpl in *. f_equal. now apply IHl1.
Qed.

Definition sem_clock' : history -> clock -> list bool -> Prop :=
  fun H ck bl => for_all2 (fun env => instant_sem_clock env ck) H bl.

Definition sem_laexp' : history -> laexp -> list value -> Prop :=
  fun H cae cl => for_all2 (fun env => instant_sem_laexp env cae) H cl.

Definition sem_lexp' : history -> lexp -> list value -> Prop :=
  fun H ce cl => for_all2 (fun env => instant_sem_lexp env ce) H cl.

Definition sem_caexp' : history -> caexp -> list value -> Prop :=
  fun H cae cl => for_all2 (fun env => instant_sem_caexp env cae) H cl.

Definition sem_cexp' : history -> cexp -> list value -> Prop :=
  fun H ce cl => for_all2 (fun env => instant_sem_cexp env ce) H cl.

(** Equivalence of both definitions *)

Ltac solve_equiv :=
  intro H; induction H as [| env H IHH]; intros cae bl;
  [ split; intro Hsem;
    [ inversion_clear Hsem; exact I
    | apply for_all2_length in Hsem; destruct bl; constructor || discriminate ]
  | split; intro Hsem;
    [ inversion_clear Hsem; rewrite IHH in *; now split
    | assert (Hnil : bl <> nil) by (intro; subst; apply for_all2_length in Hsem; discriminate);
      destruct bl as [| b bl]; try (now elim Hnil); [];
      destruct Hsem; constructor; trivial; now rewrite IHH ] ].

Lemma sem_clock_equiv : forall H ck bl, sem_clock H ck bl <-> sem_clock' H ck bl.
Proof. solve_equiv. Qed.

Lemma sem_laexp_equiv : forall H cae cl, sem_laexp H cae cl <-> sem_laexp' H cae cl.
Proof. solve_equiv. Qed.

Lemma sem_lexp_equiv : forall H cae cl, sem_lexp H cae cl <-> sem_lexp' H cae cl.
Proof. solve_equiv. Qed.

Lemma sem_caexp_equiv : forall H cae cl, sem_caexp H cae cl <-> sem_caexp' H cae cl.
Proof. solve_equiv. Qed.

Lemma sem_cexp_equiv : forall H cae cl, sem_cexp H cae cl <-> sem_cexp' H cae cl.
Proof. solve_equiv. Qed.


(** **  Semantics of equations  **)

(** Now we need ot take into account the fby operator.
    Version of the paper: head of the list = first instant. *)
Fixpoint fby (v : const) (s : list value) : list value :=
  match s with
  | here v' :: s => here v :: fby v' s
  | abs :: s => abs :: fby v s
  | nil => nil
  end.

(* Maybe we should transform "(exists ...) -> ..." into "forall (... -> ...)" *)
Inductive sem_equation (G : global) : history -> equation -> Prop :=
  | SEqDef : forall H x cae,
      (exists v, sem_lexp H (Evar x) v /\ sem_caexp H cae v) ->
      sem_equation G H (EqDef x cae)
  | SEqApp : forall H x f arg input output eqs, (* I did not check this one *)
      PositiveMap.find f G = Some (mk_node f input output eqs) ->
      (exists H' vi vo, (* local context (history), input values and output values *)
          sem_laexp H arg vi (* arg evaluate to vi *)
       /\ sem_lexp H (Evar x) vo (* x evaluates to vo *)
       /\ sem_lexp H' (Evar input.(v_name)) vi (* in the local context, input evaluates to vi *)
       /\ sem_lexp H' (Evar output.(v_name)) vo  (* in the local context, output evaluates to vo *)
       /\ List.Forall (sem_equation G H') eqs) (* in the local context, the equations have correct semantics *)
      -> sem_equation G H (EqApp x f arg)
  | SEqFby : forall H x v y,
      (exists cl, sem_var H y.(v_name) cl /\ sem_lexp H (Evar x) (fby v cl)) ->
      sem_equation G H (EqFby x v y).
