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

  Inductive Is_block_in_eq : ident -> equation -> Prop :=
  | Is_block_inEqCall:
      forall s ys ck rst f es,
        Is_block_in_eq f (EqCall s ys ck rst f es)
  | Is_block_inEqReset:
      forall s ck f,
        Is_block_in_eq f (EqReset s ck f).

  Definition Is_block_in (f: ident) (eqs: list equation) : Prop :=
    List.Exists (Is_block_in_eq f) eqs.

  Record block :=
    Block {
        b_name  : ident;
        b_in    : list (ident * type);
        b_vars  : list (ident * type);
        b_lasts : list (ident * const);
        b_blocks: list (ident * ident);
        b_out   : list (ident * type);
        b_eqs   : list equation;

        (* b_ingt0 : 0 < length b_in; *)
        (* b_outgt0 : 0 < length b_out *)
        b_nodup_lasts: NoDupMembers b_lasts;
        b_nodup_blocks: NoDupMembers b_blocks;
        b_blocks_in_eqs: forall f, (exists i, In (i, f) b_blocks) <-> Is_block_in f b_eqs
      }.

  (* TODO: in Common *)
  (* Fixpoint assoc {A} (x: ident) (xs: list (ident * A)) : option A := *)
  (*   match xs with *)
  (*   | [] => None *)
  (*   | y :: xs => *)
  (*     let (y, c) := y in *)
  (*     if ident_eqb y x then Some c else assoc x xs *)
  (*   end. *)

  (* Definition find_last (x: ident) (bl: block) := *)
  (*   assoc x bl.(b_lasts). *)

  (* Definition find_subblock (x: ident) (bl: block) := *)
  (*   assoc x bl.(b_blocks). *)

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

  Remark find_block_other:
    forall b P bl bl' P',
      bl.(b_name) <> b ->
      (find_block b (bl :: P) = Some (bl', P')
       <-> find_block b P = Some (bl', P')).
  Proof.
    intros ** Hnb.
    apply ident_eqb_neq in Hnb.
    simpl; rewrite Hnb; reflexivity.
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

  Lemma find_block_split:
    forall b P bl P',
      find_block b P = Some (bl, P') ->
      exists P1,
        P = P1 ++ bl :: P'.
  Proof.
    induction P as [|bl']; simpl; try discriminate.
    intros ** Find.
    destruct (ident_eqb (b_name bl') b) eqn:E.
    - inv Find; exists []; auto.
    - apply IHP in Find as (P2 & Eq).
      exists (bl' :: P2); rewrite Eq; auto.
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

  Lemma not_Is_block_in_cons:
    forall b eq eqs,
      ~ Is_block_in b (eq :: eqs) <-> ~Is_block_in_eq b eq /\ ~Is_block_in b eqs.
  Proof.
    split; intro HH.
    - split; intro; apply HH; unfold Is_block_in; intuition.
    - destruct HH; inversion_clear 1; intuition.
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
