From Velus Require Import Common.
From Velus Require Import Operators.
From Velus Require Import Clocks.

(** * The core dataflow expresion syntax *)

Module Type CESYNTAX
       (Import Ids  : IDS)
       (Import Op   : OPERATORS)
       (Import OpAux: OPERATORS_AUX Ids Op)
       (Import Cks  : CLOCKS        Ids Op OpAux).

  (** ** Expressions *)

  Inductive exp : Type :=
  | Econst : cconst -> exp
  | Eenum  : enumtag -> type -> exp
  | Evar   : ident -> type -> exp
  | Elast  : ident -> type -> exp
  | Ewhen  : exp -> (ident * type) -> enumtag -> exp
  | Eunop  : unop -> exp -> type -> exp
  | Ebinop : binop -> exp -> exp -> type -> exp.

  (** ** Control expressions *)

  Inductive cexp : Type :=
  | Emerge : ident * type -> list cexp -> type -> cexp
  | Ecase  : exp -> list (option cexp) -> cexp -> cexp
  | Eexp   : exp -> cexp.

  Inductive rhs : Type :=
  | Eextcall : ident -> list exp -> ctype -> rhs
  | Ecexp  : cexp -> rhs.

  Section cexp_ind2.

    Variable P : cexp -> Prop.

    Hypothesis MergeCase:
      forall x l t,
        List.Forall P l ->
        P (Emerge x l t).

    Hypothesis CaseCase:
      forall c l d,
        List.Forall (fun oce => P (or_default d oce)) l ->
        P (Ecase c l d).

    Hypothesis ExpCase:
      forall e,
        P (Eexp e).

    Fixpoint cexp_ind2 (e : cexp) : P e.
    Proof.
      destruct e.
      - apply MergeCase.
        induction l; auto.
      - apply CaseCase.
        induction l as [|[|]]; auto.
      - apply ExpCase.
    Defined.

  End cexp_ind2.

  Section cexp_ind2'.

    Variable P : cexp -> Prop.

    Hypothesis MergeCase:
      forall x l t,
        List.Forall P l ->
        P (Emerge x l t).

    Hypothesis CaseCase:
      forall c l d,
        P d ->
        List.Forall (or_default_with True P) l ->
        P (Ecase c l d).

    Hypothesis ExpCase:
      forall e,
        P (Eexp e).

    Fixpoint cexp_ind2' (e : cexp) : P e.
    Proof.
      destruct e.
      - apply MergeCase.
        induction l; auto.
      - apply CaseCase; auto.
        induction l as [|[|]]; constructor; simpl; auto.
      - apply ExpCase.
    Defined.

  End cexp_ind2'.

  Fixpoint typeof (le: exp): type :=
    match le with
    | Econst c => Tprimitive (ctype_cconst c)
    | Eenum _ ty
    | Evar _ ty
    | Elast _ ty
    | Eunop _ _ ty
    | Ebinop _ _ _ ty => ty
    | Ewhen e _ _ => typeof e
    end.

  Fixpoint typeofc (ce: cexp): type :=
    match ce with
    | Emerge _ _ ty => ty
    | Ecase _ _ e   => typeofc e
    | Eexp e        => typeof e
    end.

  Definition typeofr (r: rhs): type :=
    match r with
    | Eextcall _ _ cty => Tprimitive cty
    | Ecexp e         => typeofc e
    end.

  (** Predicate used in [normal_args] in NLustre and Stc. *)
  Fixpoint noops_exp (ck: clock) (e : exp) : Prop :=
    match ck with
    | Cbase => True
    | Con ck' _ _ =>
      match e with
      | Econst _ | Eenum _ _ | Evar _ _ => True
      | Ewhen e' _ _ => noops_exp ck' e'
      | _ => False
      end
    end.

End CESYNTAX.

Module CESyntaxFun
       (Ids  : IDS)
       (Op   : OPERATORS)
       (OpAux: OPERATORS_AUX Ids Op)
       (Cks  : CLOCKS        Ids Op OpAux) <: CESYNTAX Ids Op OpAux Cks.
  Include CESYNTAX Ids Op OpAux Cks.
End CESyntaxFun.
