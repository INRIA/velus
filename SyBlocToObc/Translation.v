Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.Clocks.

Require Import Velus.CoreExpr.CESyntax.
Require Import Velus.SyBloc.SBSyntax.

Require Import Velus.Obc.ObcSyntax.

Require Import List.
Import List.ListNotations.
Require Import Morphisms.

Open Scope list.

(** * Translation *)

Module Type TRANSLATION
       (Import Ids    : IDS)
       (Import Op     : OPERATORS)
       (Import OpAux  : OPERATORS_AUX Op)
       (Import Clks   : CLOCKS    Ids)
       (Import CESyn  : CESYNTAX      Op)
       (Import SynSB  : SBSYNTAX  Ids Op       Clks CESyn)
       (Import SynObc : OBCSYNTAX Ids Op OpAux).

  Section Translate.

    Variable memories : PS.t.

    Definition tovar (xt: ident * type) : exp :=
      let (x, ty) := xt in
      if PS.mem x memories then State x ty else Var x ty.

    Definition bool_var (x: ident) : exp := tovar (x, bool_type).

    Fixpoint Control (ck: clock) (s: stmt) : stmt :=
      match ck with
      | Cbase          => s
      | Con ck x true  => Control ck (Ifte (bool_var x) s Skip)
      | Con ck x false => Control ck (Ifte (bool_var x) Skip s)
      end.

    Fixpoint translate_lexp (e: lexp) : exp :=
      match e with
      | Econst c           => Const c
      | Evar x ty          => tovar (x, ty)
      | Ewhen e c x        => translate_lexp e
      | Eunop op e ty      => Unop op (translate_lexp e) ty
      | Ebinop op e1 e2 ty => Binop op (translate_lexp e1) (translate_lexp e2) ty
      end.

    Fixpoint translate_cexp (x: ident) (e: cexp) : stmt :=
      match e with
      | Emerge y t f =>
        Ifte (bool_var y) (translate_cexp x t) (translate_cexp x f)
      | Eite b t f =>
        Ifte (translate_lexp b) (translate_cexp x t) (translate_cexp x f)
      | Eexp l =>
        Assign x (translate_lexp l)
      end.

    Definition translate_eqn (eqn: equation) : stmt :=
      match eqn with
      | EqDef x ck ce =>
        Control ck (translate_cexp x ce)
      | EqNext x ck le =>
        Control ck (AssignSt x (translate_lexp le))
      | EqCall s xs ck rst f es =>
        Control ck (Call xs f s step (map translate_lexp es))
      | EqReset s ck f =>
        Control ck (Call [] f s reset [])
      end.

  (*   (** Remark: eqns ordered in reverse order of execution for coherence with *)
  (*      [Is_well_sch]. *) *)

    Definition translate_eqns (eqns: list equation) : stmt :=
      fold_left (fun i eq => Comp (translate_eqn eq) i) eqns Skip.

  End Translate.

  Lemma ValidIds_idty:
    forall A B (xs: list (ident * (A * B))),
    Forall ValidId xs ->
    Forall ValidId (idty xs).
  Proof.
    induction 1; constructor; auto.
  Qed.

  Program Definition step_method (b: block) : method :=
    let memids := map fst b.(b_lasts) in
    let mems := ps_from_list memids in
    {| m_name := step;
       m_in   := idty b.(b_in);
       m_vars := idty b.(b_vars);
       m_out  := idty b.(b_out);
       m_body := translate_eqns mems b.(b_eqs)
    |}.
  Next Obligation.
    rewrite <-2 idty_app;
      apply NoDupMembers_idty, b_nodup_vars.
  Qed.
  Next Obligation.
    rewrite <-2 idty_app;
      apply ValidIds_idty, b_good.
  Qed.

  Definition reset_mems (mems: list (ident * (const * clock))) : stmt :=
    fold_left (fun s xc => Comp s (AssignSt (fst xc) (Const (fst (snd xc))))) mems Skip.

  Definition reset_insts (insts: list (ident * ident)) : stmt :=
    fold_left (fun s xf => Comp s (Call [] (snd xf) (fst xf) reset [])) insts Skip.

  Definition translate_reset (b: block) : stmt :=
    Comp (reset_mems b.(b_lasts)) (reset_insts b.(b_blocks)).

  Hint Constructors NoDupMembers.

  Program Definition reset_method (b: block) : method :=
    {| m_name := reset;
       m_in   := [];
       m_vars := [];
       m_out  := [];
       m_body := translate_reset b
    |}.

  Program Definition translate_block (b: block) : class :=
    {| c_name    := b.(b_name);
       c_mems    := map (fun xc => (fst xc, type_const (fst (snd xc)))) b.(b_lasts);
       c_objs    := b.(b_blocks);
       c_methods := [ step_method b; reset_method b ]
    |}.
  Next Obligation.
    rewrite map_map; simpl; apply b_nodup_lasts_blocks.
  Qed.
  Next Obligation.
    constructor; auto using NoDup.
    inversion_clear 1; auto.
    now apply reset_not_step.
  Qed.
  Next Obligation.
    pose proof b.(b_good) as (?&?& Blocks &?).
    split; auto.
    clear - Blocks.
    induction Blocks as [|?? Valid]; constructor; auto.
    apply Valid.
  Qed.

  Definition translate (P: SynSB.program) : program :=
    map translate_block P.

  Lemma exists_step_method:
    forall block,
      find_method step (translate_block block).(c_methods) = Some (step_method block).
  Proof.
    intro; simpl; rewrite ident_eqb_refl; eauto.
  Qed.

  Lemma exists_reset_method:
    forall block,
      find_method reset (translate_block block).(c_methods)
      = Some (reset_method block).
  Proof.
    assert (ident_eqb step reset = false) as Hsr.
    { apply ident_eqb_neq.
      apply PositiveOrder.neq_sym; apply reset_not_step.
    }
    simpl; now rewrite Hsr, ident_eqb_refl.
  Qed.

  Lemma find_method_stepm_out:
    forall block stepm,
      find_method step (translate_block block).(c_methods) = Some stepm ->
      stepm.(m_out) = idty block.(b_out).
  Proof.
    intros ??; simpl.
    rewrite ident_eqb_refl.
    inversion 1; auto.
  Qed.

  Lemma find_method_stepm_in:
    forall block stepm,
      find_method step (translate_block block).(c_methods) = Some stepm ->
      stepm.(m_in) = idty block.(b_in).
  Proof.
    intros ??; simpl.
    rewrite ident_eqb_refl.
    inversion 1; auto.
  Qed.

  Lemma find_class_translate:
    forall b P cls P',
      find_class b (translate P) = Some (cls, P') ->
      exists block P',
        find_block b P = Some (block, P')
        /\ cls = translate_block block.
  Proof.
    induction P as [|block P]; [now inversion 1|].
    intros ** Hfind; simpl in Hfind.
    destruct (equiv_dec block.(b_name) b) as [Heq|Hneq].
    - rewrite Heq, ident_eqb_refl in Hfind.
      inv Hfind.
      exists block, P. split; auto.
      simpl. now rewrite Heq, ident_eqb_refl.
    - apply ident_eqb_neq in Hneq. rewrite Hneq in Hfind.
      apply IHP in Hfind as (block' & P'' & Hfind & Hcls).
      exists block', P''. simpl. rewrite Hneq. auto.
  Qed.

  Lemma find_block_translate:
    forall b P block P',
      find_block b P = Some (block, P') ->
      exists cls prog',
        find_class b (translate P) = Some (cls, prog')
        /\ cls = translate_block block
        /\ prog' = translate P'.
  Proof.
    induction P as [|block P]; [now inversion 1|].
    intros ** Hfind; simpl in Hfind.
    destruct (equiv_dec block.(b_name) b) as [Heq|Hneq].
    - rewrite Heq, ident_eqb_refl in Hfind.
      injection Hfind; intros; subst block0 P'.
      exists (translate_block block), (translate P).
      split; [|split]; auto.
      simpl. now rewrite Heq, ident_eqb_refl.
    - apply ident_eqb_neq in Hneq. rewrite Hneq in Hfind.
      apply IHP in Hfind as (cls & prog' & Hfind & Hcls).
      exists cls, prog'. split; auto. simpl. now rewrite Hneq.
  Qed.

End TRANSLATION.

Module TranslationFun
       (Import Ids    : IDS)
       (Import Op     : OPERATORS)
       (Import OpAux  : OPERATORS_AUX Op)
       (Import Clks   : CLOCKS    Ids)
       (Import CESyn  : CESYNTAX      Op)
       (Import SynSB  : SBSYNTAX  Ids Op       Clks CESyn)
       (Import SynObc : OBCSYNTAX Ids Op OpAux)
       <: TRANSLATION Ids Op OpAux Clks CESyn SynSB SynObc.
  Include TRANSLATION Ids Op OpAux Clks CESyn SynSB SynObc.
End TranslationFun.