Require Import Rustre.Nelist.
Require Import Rustre.Common.


Open Scope bool_scope.
Import List.ListNotations.
Open Scope list_scope.

(** * Minimp syntax *)

(**

  Minimp is a minimal object-oriented programming language exposing
  two methods: [step] and [reset].

 *)
Module Type SYNTAX (Op : OPERATORS).
  
  Inductive exp : Type :=
  | Var : ident -> exp                       (* variable  *)
  | State : ident -> exp                     (* state variable  *)
  | Const : Op.val -> exp                    (* constant *)
  | Unop : Op.unary_op -> exp -> exp          (* unary operator *)
  | Binop : Op.binary_op -> exp -> exp -> exp. (* binary operator *)
  
  Implicit Type e: exp.

  Inductive stmt : Type :=
  | Assign : ident -> exp -> stmt                         (* x = e *)
  | AssignSt : ident -> exp -> stmt                       (* self.x = e *)
  | Ifte : exp -> stmt -> stmt -> stmt                     (* if e then s1 else s2 *)
  | Step_ap : ident -> ident -> ident -> nelist exp -> stmt (* y = (C x).step(es) *)
  | Reset_ap : ident -> ident -> stmt                     (* (C x).reset() *)
  | Comp : stmt -> stmt -> stmt                           (* s1; s2 *)
  | Skip.

  Implicit Type s: stmt.


  Record obj_dec : Type :=
    mk_obj_dec {
        obj_inst  : ident;
        obj_class : ident
      }.

  (* TODO: lots of fields are not strictly necessary *)
  Record class : Type :=
    mk_class {
        c_name   : ident;

        c_input  : nelist ident;
        c_output : ident;

        c_mems   : list ident;       (* TODO: should track type of each *)
        c_objs   : list obj_dec;

        c_step   : stmt;
        c_reset  : stmt
      }.

  Implicit Type cl: class.

  Definition program : Type := list class.

  Implicit Type p: program.

  Definition find_class (n: ident) : program -> option (class * list class) :=
    fix find p :=
      match p with
      | [] => None
      | c :: p' => if ident_eqb c.(c_name) n then Some (c, p') else find p'
      end.

  (** ** Induction principle for [exp] *)

  (* Print exp_ind. *)

  (* Definition exp_ind2 : forall P : exp -> Prop, *)
  (*   (forall i, P (Var i)) -> *)
  (*   (forall i, P (State i)) -> *)
  (*   (forall c, P (Const c)) -> *)
  (*   (forall op es (IHes : Nelist.Forall P es), P (Op op es)) -> *)
  (*   forall e, P e. *)
  (* Proof. *)
  (* intros P Hvar Hstate Hcons Hop. fix 1. *)
  (* intros e. destruct e as [i | i | c | op es]. *)
  (* + apply Hvar. *)
  (* + apply Hstate. *)
  (* + apply Hcons. *)
  (* + apply Hop. now induction es as [e | e es]; constructor. *)
  (* Defined. *)

  (** ** Decidable equality *)

  (* XXX: use [exp_ind2] *)
  Definition exp_eqb : exp -> exp -> bool.
  Proof.
    fix 1.
    intros e1 e2.
    refine (match e1, e2 with
            | Var x1, Var x2 => ident_eqb x1 x2
            | State s1, State s2 => ident_eqb s1 s2
            | Const c1, Const c2 => Op.val_eqb c1 c2
            (* | Op op1 es1, Op op2 es2 => op_eqb op1 op2 && _ *)
            | Unop op1 e1', Unop op2 e2' => Op.unop_eqb op1 op2 && _
            | Binop op1 e11 e12, Binop op2 e21 e22 => Op.binop_eqb op1 op2 && _ 
            | _, _ => false
            end).
    - exact (exp_eqb e1' e2').
    - exact (exp_eqb e11 e21 && exp_eqb e12 e22).
      (*   clear e1 e2. revert es2. induction es1 as [e1 | e1 es1]; intros [e2 | e2 es2]. *)
      (* - exact (exp_eqb e1 e2). *)
      (* - exact false. *)
      (* - exact false. *)
      (* - exact (exp_eqb e1 e2 && IHes1 es2). *)
  Defined.

  Lemma exp_eqb_eq:
    forall e1 e2,
      exp_eqb e1 e2 = true <-> e1 = e2.
  Proof.
    induction e1 (* using exp_ind2 *); intros e2; destruct e2; simpl; try now split; intro; discriminate.
    - rewrite ident_eqb_eq. now split; intro Heq; inversion Heq.
    - rewrite ident_eqb_eq. now split; intro Heq; inversion Heq.
    - rewrite Op.val_eqb_true_iff. now split; intro Heq; inversion Heq.
    - rewrite Bool.andb_true_iff, Op.unop_eqb_true_iff.
      split; intro Heq. 
      + f_equal; try apply IHe1; apply Heq.
      (* auto. destruct Heq as [? Heq]; subst; split || f_equal; trivial; []. *)
      (*   revert n Heq. induction es as [| e1 es1]; intros [| e2 es2] Heq; simpl in Heq; try discriminate; [|]. *)
      (*   * inversion_clear IHes. rewrite H in Heq. now subst. *)
      (*   * rewrite Bool.andb_true_iff in Heq. inversion_clear IHes. *)
      (*     specialize (IHes1 H0 es2). rewrite H in Heq. *)
      (*     destruct Heq as [? Heq]; subst; f_equal. *)
      (*     apply IHes1. simpl. apply Heq. *)
      + now inversion Heq; subst; rewrite IHe1. (* trivial. split; trivial. clear Heq. induction n; simpl; [|]. *)
    (* * inversion_clear IHes. now rewrite H. *)
    (* * inversion_clear IHes. rewrite Bool.andb_true_iff, H. split; trivial. now apply IHn. *)
    - rewrite 2 Bool.andb_true_iff, Op.binop_eqb_true_iff.
      split; intro Heq.
      + f_equal. apply Heq. apply IHe1_1, Heq. apply IHe1_2, Heq.
      + now inversion Heq; subst; rewrite IHe1_1, IHe1_2.
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


End SYNTAX.
