Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.Clocks.
(* Require Import PArith. *)
(* Require Import Coq.Sorting.Permutation. *)

Require Import List.
Import List.ListNotations.
Open Scope list_scope.


Module Type SBSYNTAX
       (Import Ids  : IDS)
       (Import Op   : OPERATORS)
       (Import Clks : CLOCKS Ids).

  (** ** Expressions *)

  Inductive lexp :=
  | Econst : const -> lexp
  | Evar   : ident -> type -> lexp
  | Ewhen  : lexp -> ident -> bool -> lexp
  | Eunop  : unop -> lexp -> type -> lexp
  | Ebinop : binop -> lexp -> lexp -> type -> lexp.

  (** ** Control expressions *)

  Inductive cexp :=
  | Emerge : ident -> cexp -> cexp -> cexp
  | Eite   : lexp -> cexp -> cexp -> cexp
  | Eexp   : lexp -> cexp.

  (** ** Equations *)

  Inductive equation :=
  | EqDef : ident -> clock -> cexp -> equation
  | EqFby : ident -> clock -> const -> lexp -> equation
  | EqReset : clock -> ident -> ident -> ident -> equation (* reinit block instance on r *)
  | EqCall: idents -> clock -> ident -> ident -> list lexp -> equation.
  (* y1, ..., yn = block instance (e1, ..., em) *)

  Record block :=
    Block {
        b_name  : ident;
        b_in    : list (ident * type);
        b_vars  : list (ident * type);
        b_blocks: list (ident * ident);
        b_out   : list (ident * type);
        b_eqs   : list equation;

        b_ingt0 : 0 < length b_in
      }.

  Definition bl_vars (bl: block): list (ident * type) :=
    bl.(b_in) ++ bl.(b_out) ++ bl.(b_vars).

  Definition program := list block.

  Fixpoint typeof (le: lexp): type :=
    match le with
    | Econst c => type_const c
    | Evar _ ty
    | Eunop _ _ ty
    | Ebinop _ _ _ ty => ty
    | Ewhen e _ _ => typeof e
    end.

  (* Fixpoint find_mode (m: ident) (ms: list mode): option mode := *)
  (*   match ms with *)
  (*   | [] => None *)
  (*   | mo :: ms => *)
  (*     if ident_eqb mo.(m_name) m *)
  (*     then Some mo else find_mode m ms *)
  (*   end. *)

  (* Remark find_mode_In: *)
  (*   forall m ms mo, *)
  (*     find_mode m ms = Some mo -> *)
  (*     In mo ms. *)
  (* Proof. *)
  (*   intros ** Hfind. *)
  (*   induction ms; inversion Hfind as [H]. *)
  (*   destruct (ident_eqb (m_name a) m) eqn: E. *)
  (*   - inversion H; subst. *)
  (*     apply in_eq. *)
  (*   - auto using in_cons. *)
  (* Qed. *)

  (* Remark find_mode_name: *)
  (*   forall m ms mo, *)
  (*     find_mode m ms = Some mo -> *)
  (*     mo.(m_name) = m. *)
  (* Proof. *)
  (*   intros ** Hfind. *)
  (*   induction ms; inversion Hfind as [H]. *)
  (*   destruct (ident_eqb (m_name a) m) eqn: E. *)
  (*   - inversion H; subst. *)
  (*     now apply ident_eqb_eq. *)
  (*   - now apply IHms. *)
  (* Qed. *)

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
       (Clks : CLOCKS Ids)
       <: SBSYNTAX Ids Op Clks.
  Include SBSYNTAX Ids Op Clks.
End SBSyntaxFun.
