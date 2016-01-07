Require Import Rustre.Common.


Open Scope bool_scope.
Import List.ListNotations.
Open Scope list_scope.

(**

  Minimp is a minimal object-oriented programming language exposing
  two methods: [step] and [reset].

 *)

(** * Imperative language *)

(** ** Syntax *)

Inductive exp : Set :=
| Var : ident -> exp
| State : ident -> exp
| Const : const -> exp
| Op : operator -> list exp -> exp.

Implicit Type e: exp.

Inductive stmt : Set :=
  | Assign : ident -> exp -> stmt
  | AssignSt : ident -> exp -> stmt
  | Ifte : exp -> stmt -> stmt -> stmt
  | Step_ap : ident -> ident -> ident -> exp -> stmt
           (* y = Step_ap class object arg *)
  | Reset_ap : ident -> ident -> stmt
           (* Reset_ap class object *)
  | Comp : stmt -> stmt -> stmt
  | Repeat : nat -> stmt -> stmt
  | Skip.

Implicit Type s: stmt.


Record obj_dec : Set := mk_obj_dec {
  obj_inst  : ident;
  obj_class : ident
}.

(* TODO: lots of fields are not strictly necessary *)
Record class : Set := mk_class {
  c_name   : ident;

  c_input  : ident;
  c_output : ident;

  c_mems   : list ident;       (* TODO: should track type of each *)
  c_objs   : list obj_dec;

  c_step   : stmt;
  c_reset  : stmt
}.

Implicit Type c: class.

Definition program : Type := list class.

Implicit Type p: program.

Definition find_class (n: ident) : program -> option (class * list class) :=
  fix find p :=
    match p with
    | [] => None
    | c :: p' => if ident_eqb c.(c_name) n then Some (c, p') else find p'
    end.

(*
(* We need a custom induction recursion principle. *)
Definition exp_eqb (e1: exp) (e2: exp) : bool :=
  match e1, e2 with
  | Var x1, Var x2 => ident_eqb x1 x2
  | State s1, State s2 => ident_eqb s1 s2
  | Const c1, Const c2 => const_eqb c1 c2
  | Op op1 es1, Op op2 es2 => op_eqb op1 op2 && exps_eqb es1 es2
  | _, _ => false
  end.

Lemma exp_eqb_eq:
  forall e1 e2,
    exp_eqb e1 e2 = true <-> e1 = e2.
Proof.
  split.
  - destruct e1, e2; simpl; intro H0;
    (try discriminate || (apply ident_eqb_eq in H0
                          || apply const_eqb_eq in H0;
                          rewrite H0; reflexivity)).
  - destruct e1, e2; simpl; intro Heq; try discriminate.
    || (injection H0; intro H1; rewrite H1;
        apply ident_eqb_eq || apply const_eqb_eq; reflexivity).
Qed.

Lemma exp_eqb_neq:
  forall e1 e2,
    exp_eqb e1 e2 = false <-> e1 <> e2.
Proof.
  split; intro HH.
  - intro Heq; apply exp_eqb_eq in Heq; rewrite Heq in HH; discriminate.
  - apply Bool.not_true_iff_false.
    intro Htrue; apply exp_eqb_eq in Htrue; intuition.
Qed.

Lemma exp_eq_dec: forall (e1: exp) (e2: exp), {e1 = e2}+{e1 <> e2}.
Proof.
  intros e1 e2.
  destruct (exp_eqb e1 e2) eqn:Heq; [left|right].
  apply exp_eqb_eq; assumption.
  intro H; apply exp_eqb_eq in H.
  rewrite Heq in H; discriminate.
Qed.
*)