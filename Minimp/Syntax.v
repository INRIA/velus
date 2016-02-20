Require Import Rustre.Nelist.
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
| Op : operator -> nelist exp -> exp.

Definition exp_ind2 : forall P : exp -> Prop,
  (forall i, P (Var i)) ->
  (forall i, P (State i)) ->
  (forall c, P (Const c)) ->
  (forall op es (IHes : Nelist.Forall P es), P (Op op es)) ->
  forall e, P e.
Proof.
intros P Hvar Hstate Hcons Hop. fix 1.
intros e. destruct e as [i | i | c | op es].
+ apply Hvar.
+ apply Hstate.
+ apply Hcons.
+ apply Hop. now induction es as [e | e es]; constructor.
Defined.

Implicit Type e: exp.

Inductive stmt : Set :=
  | Assign : ident -> exp -> stmt
  | AssignSt : ident -> exp -> stmt
  | Ifte : exp -> stmt -> stmt -> stmt
  | Step_ap : ident -> ident -> ident -> nelist exp -> stmt
           (* y = Step_ap class object arg *)
  | Reset_ap : ident -> ident -> stmt
           (* Reset_ap class object *)
  | Comp : stmt -> stmt -> stmt
  | Skip.

Implicit Type s: stmt.


Record obj_dec : Set := mk_obj_dec {
  obj_inst  : ident;
  obj_class : ident
}.

(* TODO: lots of fields are not strictly necessary *)
Record class : Set := mk_class {
  c_name   : ident;

  c_input  : nelist ident;
  c_output : ident;

  c_mems   : list ident;       (* TODO: should track type of each -> LR: use arity/arrows? *)
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


(* We need a custom recursion principle. *)
Definition exp_eqb : exp -> exp -> bool.
Proof.
fix 1.
intros e1 e2.
refine (match e1, e2 with
  | Var x1, Var x2 => ident_eqb x1 x2
  | State s1, State s2 => ident_eqb s1 s2
  | Const c1, Const c2 => const_eqb c1 c2
  | Op op1 es1, Op op2 es2 => op_eqb op1 op2 && _
  | _, _ => false
  end).
clear e1 e2. revert es2. induction es1 as [e1 | e1 es1]; intros [e2 | e2 es2].
- exact (exp_eqb e1 e2).
- exact false.
- exact false.
- exact (exp_eqb e1 e2 && IHes1 es2).
Defined.

Lemma exp_eqb_eq:
  forall e1 e2,
    exp_eqb e1 e2 = true <-> e1 = e2.
Proof.
induction e1 using exp_ind2; intros e2; destruct e2; simpl; try now split; intro; discriminate.
+ rewrite ident_eqb_eq. now split; intro Heq; inversion Heq.
+ rewrite ident_eqb_eq. now split; intro Heq; inversion Heq.
+ rewrite const_eqb_eq. now split; intro Heq; inversion Heq.
+ rewrite Bool.andb_true_iff, op_eqb_true_iff.
  split; intro Heq. 
  - destruct Heq as [? Heq]; subst; split || f_equal; trivial; [].
    revert n Heq. induction es as [| e1 es1]; intros [| e2 es2] Heq; simpl in Heq; try discriminate; [|].
    * inversion_clear IHes. rewrite H in Heq. now subst.
    * rewrite Bool.andb_true_iff in Heq. inversion_clear IHes.
      specialize (IHes1 H0 es2). rewrite H in Heq.
      destruct Heq as [? Heq]; subst; f_equal.
      apply IHes1. simpl. apply Heq.
  - inversion Heq. subst. split; trivial. clear Heq. induction n; simpl; [|].
    * inversion_clear IHes. now rewrite H.
    * inversion_clear IHes. rewrite Bool.andb_true_iff, H. split; trivial. now apply IHn.
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
