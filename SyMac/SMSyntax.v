Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.Clocks.
(* Require Import PArith. *)
(* Require Import Coq.Sorting.Permutation. *)

Require Import List.
Import List.ListNotations.
Open Scope list_scope.


Module Type SMSYNTAX
       (Import Ids  : IDS)
       (Import Op   : OPERATORS)
       (Import Clks : CLOCKS Ids).

  (** ** Expressions *)

  Inductive lexp :=
  | Econst : const -> lexp
  | Evar   : ident -> type -> lexp
  | Emem   : ident -> type -> lexp
  | Ewhen  : lexp -> ident -> bool -> lexp
  | Eunop  : unop -> lexp -> type -> lexp
  | Ebinop : binop -> lexp -> lexp -> type -> lexp.

  (** ** Control expressions *)

  Inductive cexp :=
  | Emerge : ident -> cexp -> cexp -> cexp
  | Eite   : lexp -> cexp -> cexp -> cexp
  | Eexp   : lexp -> cexp.

  (** ** Equations *)

  Inductive rank :=
  | Inter (n: nat): rank
  | Last        : rank.

  Inductive equation :=
  | EqDef : ident -> clock -> cexp -> equation
  | EqPost: ident -> clock -> cexp -> equation
  | EqCall: idents -> clock -> ident -> ident -> ident -> rank -> list lexp -> equation.
  (* y1, ..., yn = class instance mode rank (e1, ..., em) *)

  Record mode :=
    Mode {
        m_name: ident;
        m_in  : list (ident * type);
        m_vars: list (ident * type);
        m_out : list (ident * type);
        m_eqs : list equation
      }.

  Record machine :=
    Machine {
        ma_name  : ident;
        ma_mems  : list (ident * const);
        ma_machs : list (ident * ident);
        ma_modes : list mode
        (* ma_policy: list (ident * nat) *)
      }.

  Definition program := list machine.

  Fixpoint typeof (le: lexp): type :=
    match le with
    | Econst c => type_const c
    | Evar _ ty
    | Emem _ ty
    | Eunop _ _ ty
    | Ebinop _ _ _ ty => ty
    | Ewhen e _ _ => typeof e
    end.

  (* Fixpoint find_rank (m: ident) (pol: list (ident * nat)): option nat := *)
  (*   match pol with *)
  (*   | [] => None *)
  (*   | p :: pol => *)
  (*     if ident_eqb (fst p) m *)
  (*     then Some (snd p) else find_rank m pol *)
  (*   end. *)

  Fixpoint find_mode (m: ident) (ms: list mode): option mode :=
    match ms with
    | [] => None
    | mo :: ms =>
      if ident_eqb mo.(m_name) m
      then Some mo else find_mode m ms
    end.

  Remark find_mode_In:
    forall m ms mo,
      find_mode m ms = Some mo ->
      In mo ms.
  Proof.
    intros ** Hfind.
    induction ms; inversion Hfind as [H].
    destruct (ident_eqb (m_name a) m) eqn: E.
    - inversion H; subst.
      apply in_eq.
    - auto using in_cons.
  Qed.

  Remark find_mode_name:
    forall m ms mo,
      find_mode m ms = Some mo ->
      mo.(m_name) = m.
  Proof.
    intros ** Hfind.
    induction ms; inversion Hfind as [H].
    destruct (ident_eqb (m_name a) m) eqn: E.
    - inversion H; subst.
      now apply ident_eqb_eq.
    - now apply IHms.
  Qed.

  Fixpoint find_machine (m: ident) (P: program) : option (machine * program) :=
   match P with
   | [] => None
   | ma :: P =>
     if ident_eqb ma.(ma_name) m
     then Some (ma, P) else find_machine m P
   end.

  (** Properties of machine lookups *)

  Lemma find_machine_none:
    forall m ma P,
      find_machine m (ma :: P) = None
      <-> (ma.(ma_name) <> m /\ find_machine m P = None).
  Proof.
    intros.
    simpl; destruct (ident_eqb (ma_name ma) m) eqn: E.
    - split; intro HH; try discriminate.
      destruct HH.
      apply ident_eqb_eq in E; contradiction.
    - apply ident_eqb_neq in E; split; intro HH; tauto.
  Qed.

  Remark find_machine_app:
    forall m P ma P',
      find_machine m P = Some (ma, P') ->
      exists P'',
        P = P'' ++ ma :: P'
        /\ find_machine m P'' = None.
  Proof.
    intros ** Hfind.
    induction P; inversion Hfind as [H].
    destruct (ident_eqb (ma_name a) m) eqn: E.
    - inversion H; subst.
      exists nil; auto.
    - specialize (IHP H).
      destruct IHP as (P'' & HP'' & Hnone).
      rewrite HP''.
      exists (a :: P''); split; auto.
      simpl; rewrite E; auto.
  Qed.

  Remark find_machine_name:
    forall m P ma P',
      find_machine m P = Some (ma, P') ->
      ma.(ma_name) = m.
  Proof.
    intros ** Hfind.
    induction P; inversion Hfind as [H].
    destruct (ident_eqb (ma_name a) m) eqn: E.
    - inversion H; subst.
      now apply ident_eqb_eq.
    - now apply IHP.
  Qed.

  Remark find_machine_In:
    forall m P ma P',
      find_machine m P = Some (ma, P') ->
      In ma P.
  Proof.
    intros ** Hfind.
    induction P; inversion Hfind as [H].
    destruct (ident_eqb (ma_name a) m) eqn: E.
    - inversion H; subst.
      apply in_eq.
    - apply in_cons; auto.
  Qed.

  Lemma find_machine_app':
    forall m P P',
      find_machine m (P ++ P') =
      match find_machine m P with
      | None => find_machine m P'
      | Some (ma, P'') => Some (ma, P'' ++ P')
      end.
  Proof.
    induction P as [|ma P]; simpl; auto.
    intro; destruct (ident_eqb ma.(ma_name) m); auto.
  Qed.

  Lemma not_In_find_machine:
    forall m P,
      ~In m (map ma_name P) ->
      find_machine m P = None.
  Proof.
    induction P as [|ma]; auto.
    simpl; intro Hnin.
    apply Decidable.not_or in Hnin.
    destruct Hnin as (Hnin1 & Hnin2).
    rewrite (IHP Hnin2).
    apply ident_eqb_neq in Hnin1.
    now rewrite Hnin1.
  Qed.

End SMSYNTAX.

Module SMSyntaxFun
       (Ids  : IDS)
       (Op   : OPERATORS)
       (Clks : CLOCKS Ids)
       <: SMSYNTAX Ids Op Clks.
  Include SMSYNTAX Ids Op Clks.
End SMSyntaxFun.
