Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.NLustre.NLExprSyntax.
Require Import Velus.Clocks.

Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Module Type SBSYNTAX
       (Import Ids     : IDS)
       (Import Op      : OPERATORS)
       (Import Clks    : CLOCKS       Ids)
       (Import ExprSyn : NLEXPRSYNTAX     Op).

  (** ** Equations *)

  Inductive equation :=
  | EqDef       : ident -> clock -> cexp -> equation
  | EqNext      : ident -> clock -> lexp -> equation
  | EqReset     : ident -> clock -> ident -> equation
  (* <trans s> =ck reset block<last s> *)
  | EqCall      : ident -> idents -> clock -> bool -> ident -> list lexp -> equation.
  (* <next s> y1, ..., yn =ck block<if b then trans s else last s>(e1, ..., em) *)

  Record block :=
    Block {
        b_name  : ident;
        b_in    : list (ident * type);
        b_vars  : list (ident * type);
        b_lasts : list (ident * const);
        b_blocks: list (ident * ident);
        b_out   : list (ident * type);
        b_eqs   : list equation

        (* b_ingt0 : 0 < length b_in; *)
        (* b_outgt0 : 0 < length b_out *)
      }.

  Fixpoint find_const (x: ident) (xs: list (ident * const)) : option const :=
    match xs with
    | [] => None
    | y :: xs =>
      let (y, c) := y in
      if ident_eqb y x then Some c else find_const x xs
    end.

  Definition find_init (x: ident) (bl: block) :=
    find_const x bl.(b_lasts).

  Definition bl_vars (bl: block): list (ident * type) :=
    bl.(b_in) ++ bl.(b_out) ++ bl.(b_vars).

  Definition program := list block.

  Fixpoint find_block (b: ident) (P: program) : option (block * program) :=
   match P with
   | [] => None
   | bl :: P =>
     if ident_eqb bl.(b_name) b
     then Some (bl, P) else find_block b P
   end.

  (** Properties of block lookups *)

  Lemma find_block_none:
    forall b bl P,
      find_block b (bl :: P) = None
      <-> (bl.(b_name) <> b /\ find_block b P = None).
  Proof.
    intros.
    simpl; destruct (ident_eqb (b_name bl) b) eqn: E.
    - split; intro HH; try discriminate.
      destruct HH.
      apply ident_eqb_eq in E; contradiction.
    - apply ident_eqb_neq in E; split; intro HH; tauto.
  Qed.

  Remark find_block_app:
    forall b P bl P',
      find_block b P = Some (bl, P') ->
      exists P'',
        P = P'' ++ bl :: P'
        /\ find_block b P'' = None.
  Proof.
    intros ** Hfind.
    induction P; inversion Hfind as [H].
    destruct (ident_eqb (b_name a) b) eqn: E.
    - inversion H; subst.
      exists nil; auto.
    - specialize (IHP H).
      destruct IHP as (P'' & HP'' & Hnone).
      rewrite HP''.
      exists (a :: P''); split; auto.
      simpl; rewrite E; auto.
  Qed.

  Remark find_block_name:
    forall b P bl P',
      find_block b P = Some (bl, P') ->
      bl.(b_name) = b.
  Proof.
    intros ** Hfind.
    induction P; inversion Hfind as [H].
    destruct (ident_eqb (b_name a) b) eqn: E.
    - inversion H; subst.
      now apply ident_eqb_eq.
    - now apply IHP.
  Qed.

  Remark find_block_In:
    forall b P bl P',
      find_block b P = Some (bl, P') ->
      In bl P.
  Proof.
    intros ** Hfind.
    induction P; inversion Hfind as [H].
    destruct (ident_eqb (b_name a) b) eqn: E.
    - inversion H; subst.
      apply in_eq.
    - apply in_cons; auto.
  Qed.

  Lemma find_block_app':
    forall b P P',
      find_block b (P ++ P') =
      match find_block b P with
      | None => find_block b P'
      | Some (bl, P'') => Some (bl, P'' ++ P')
      end.
  Proof.
    induction P as [|bl P]; simpl; auto.
    intro; destruct (ident_eqb bl.(b_name) b); auto.
  Qed.

  Lemma not_In_find_block:
    forall b P,
      ~In b (map b_name P) ->
      find_block b P = None.
  Proof.
    induction P as [|bl]; auto.
    simpl; intro Hnin.
    apply Decidable.not_or in Hnin.
    destruct Hnin as (Hnin1 & Hnin2).
    rewrite (IHP Hnin2).
    apply ident_eqb_neq in Hnin1.
    now rewrite Hnin1.
  Qed.

End SBSYNTAX.

Module SBSyntaxFun
       (Ids  : IDS)
       (Op   : OPERATORS)
       (Clks : CLOCKS          Ids)
       (ExprSyn : NLEXPRSYNTAX     Op)
       <: SBSYNTAX Ids Op Clks ExprSyn.
  Include SBSYNTAX Ids Op Clks ExprSyn.
End SBSyntaxFun.
