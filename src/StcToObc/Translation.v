From Velus Require Import Common.
From Velus Require Import CommonProgram.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.

From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import Stc.StcSyntax.

From Velus Require Import Obc.ObcSyntax.

From Coq Require Import List.
From Coq Require Import Lia.
Import List.ListNotations.
From Coq Require Import Morphisms.

Open Scope list.

(** * Translation *)

Module Type TRANSLATION
       (Import Ids    : IDS)
       (Import Op     : OPERATORS)
       (Import OpAux  : OPERATORS_AUX Ids Op)
       (Import Cks    : CLOCKS    Ids Op OpAux)
       (Import CESyn  : CESYNTAX  Ids Op OpAux Cks)
       (Import SynStc : STCSYNTAX Ids Op OpAux Cks CESyn)
       (Import SynObc : OBCSYNTAX Ids Op OpAux).

  Section Translate.

    Variable memories : PS.t.
    Variable clkvars  : Env.t clock.

    Definition tovar (xt: ident * type) : exp :=
      let (x, ty) := xt in
      if PS.mem x memories then State x ty else Var x ty.

    Fixpoint skip_branches_with_aux (acc: list (option stmt)) (n i: enumtag) (s: stmt): list (option stmt) :=
      match n with
      | 0 => acc
      | S n => skip_branches_with_aux ((if n ==b i then Some s else None) :: acc) n i s
      end.

    Definition skip_branches_with := skip_branches_with_aux [].

    Fixpoint Control (ck: clock) (s: stmt) : stmt :=
      match ck with
      | Cbase      => s
      | Con ck x (Tenum t tn, c) =>
        Control ck (Switch (tovar (x, Tenum t tn)) (skip_branches_with (length tn) c s) Skip)
      | _ => Skip
      end.

    Fixpoint translate_exp (e: CESyn.exp) : exp :=
      match e with
      | Econst c           => Const c
      | Eenum c ty         => Enum c ty
      | Evar x ty          => tovar (x, ty)
      | Ewhen e c x        => translate_exp e
      | Eunop op e ty      => Unop op (translate_exp e) ty
      | Ebinop op e1 e2 ty => Binop op (translate_exp e1) (translate_exp e2) ty
      end.

    Fixpoint translate_cexp (x: ident) (e: cexp) : stmt :=
      match e with
      | Emerge yt es _ =>
        Switch (tovar yt) (map (fun e => Some (translate_cexp x e)) es) Skip
      | Ecase b es d =>
        Switch (translate_exp b) (map (option_map (translate_cexp x)) es) (translate_cexp x d)
      | Eexp l =>
        Assign x (translate_exp l)
      end.

    Definition var_on_base_clock (ck: clock) (x: ident) : bool :=
      negb (PS.mem x memories)
      && match Env.find x clkvars with
         | Some ck' => clock_eq ck ck'
         | None => false
         end.

    Definition translate_arg (ck: clock) (e : CESyn.exp) : exp :=
      match e with
      | Evar x ty =>
        if var_on_base_clock ck x
        then Valid x ty
        else translate_exp e
      | _ => translate_exp e
      end.

    Definition translate_tc (tc: trconstr) : stmt :=
      match tc with
      | TcDef x ck (Ecexp ce) =>
        Control ck (translate_cexp x ce)
      | TcDef x ck (Eextcall f es ty) =>
        Control ck (ExternCall x f (map translate_exp es) ty)
      | TcReset x ckr _ (Op.Const c0) =>
        Control ckr (AssignSt x (Const c0))
      | TcReset x ckr ty (Op.Enum t) =>
        Control ckr (AssignSt x (Enum t ty))
      | TcNext x ck _ le =>
        Control ck (AssignSt x (translate_exp le))
      | TcStep s xs ck rst f es =>
        Control ck (Call xs f s step (map (translate_arg ck) es))
      | TcInstReset s ck f =>
        Control ck (Call [] f s reset [])
      end.

    (*   (** Remark: tcs ordered in reverse order of execution for coherence with *)
     (*      [Is_well_sch]. *) *)

    Definition translate_tcs (tcs: list trconstr) : stmt :=
      fold_left (fun i tc => Comp (translate_tc tc) i) tcs Skip.

  End Translate.

  Program Definition step_method (s: system) : method :=
    let memids := map fst s.(s_nexts) in
    let mems := ps_from_list memids in
    let typvars := Env.adds_with fst s.(s_out)
                                         (Env.adds_with fst s.(s_vars)
                                                                (Env.from_list_with fst s.(s_in)))
    in
    let clkvars := Env.adds_with snd s.(s_out)
                                         (Env.adds_with snd s.(s_vars)
                                                                (Env.from_list_with snd s.(s_in)))
    in
    {| m_name := step;
       m_in   := idfst s.(s_in);
       m_vars := idfst s.(s_vars);
       m_out  := idfst s.(s_out);
       m_body := translate_tcs mems clkvars s.(s_tcs)
    |}.
  Next Obligation.
    rewrite <-2 idfst_app;
      apply NoDupMembers_idfst, s_nodup_vars.
  Qed.
  Next Obligation.
    split; auto.
    - rewrite <-2 idfst_app, map_fst_idfst. apply s_good.
    - apply step_atom.
  Qed.

  (* TODO: I don't know why tuple pattern version won't be considered "convertible" by Coq.
           It make me wanna finish chicken species. *)
  Definition reset_mems (inits: list (ident * (const * type * clock))) : stmt :=
    fold_left (fun s init =>
                 Comp s (AssignSt (fst init) (match fst (fst (snd init)) with
                                     | Op.Const c => Const c
                                     | Op.Enum c  => Enum c (snd (fst (snd init)))
                                     end)))
              inits Skip.

  Definition reset_insts (insts: list (ident * ident)) : stmt :=
    fold_left (fun s inst => Comp s (Call [] (snd inst) (fst inst) reset [])) insts Skip.

  Definition translate_reset (b: system) : stmt :=
    Comp (reset_mems b.(s_nexts)) (reset_insts b.(s_subs)).

  Program Definition reset_method (b: system) : method :=
    {| m_name := reset;
       m_in   := [];
       m_vars := [];
       m_out  := [];
       m_body := translate_reset b
    |}.
  Next Obligation. constructor. Qed.
  Next Obligation.
     split; auto.
     apply reset_atom.
  Qed.

  Program Definition translate_system (b: system) : class :=
    {| c_name    := b.(s_name);
       c_mems    := map (fun xc => (fst xc, snd (fst (snd xc)))) b.(s_nexts);
       c_objs    := b.(s_subs);
       c_methods := [ step_method b; reset_method b ]
    |}.
  Next Obligation.
    rewrite map_map; simpl; apply s_nodup_resets_subs.
  Qed.
  Next Obligation.
    constructor; auto using NoDup.
    inversion_clear 1; auto.
    now apply reset_not_step.
  Qed.
  Next Obligation.
    pose proof b.(s_good) as (?&?& Subs &?).
    split; auto.
  Qed.

  Global Program Instance translate_system_transform_unit: TransformUnit system class :=
    { transform_unit := translate_system }.

  Global Program Instance translate_transform_state_unit: TransformStateUnit system class.

  Lemma exists_step_method:
    forall s,
      find_method step (translate_system s).(c_methods) = Some (step_method s).
  Proof.
    intro; simpl; rewrite ident_eqb_refl; eauto.
  Qed.

  Lemma exists_reset_method:
    forall s,
      find_method reset (translate_system s).(c_methods)
      = Some (reset_method s).
  Proof.
    assert (ident_eqb step reset = false) as Hsr.
    { apply ident_eqb_neq.
      apply PositiveOrder.neq_sym; apply reset_not_step.
    }
    simpl; now rewrite Hsr, ident_eqb_refl.
  Qed.

  Lemma find_method_stepm_out:
    forall s stepm,
      find_method step (translate_system s).(c_methods) = Some stepm ->
      stepm.(m_out) = idfst s.(s_out).
  Proof.
    intros ??; simpl.
    rewrite ident_eqb_refl.
    inversion 1; auto.
  Qed.

  Lemma find_method_stepm_in:
    forall s stepm,
      find_method step (translate_system s).(c_methods) = Some stepm ->
      stepm.(m_in) = idfst s.(s_in).
  Proof.
    intros ??; simpl.
    rewrite ident_eqb_refl.
    inversion 1; auto.
  Qed.

  Global Program Instance program_program_without_units : TransformProgramWithoutUnits SynStc.program program :=
    { transform_program_without_units := fun p => Program p.(SynStc.types) p.(SynStc.externs) [] }.

  Definition translate: SynStc.program -> program := transform_units.

  Fact skip_branches_with_aux_app:
    forall n i s acc,
      skip_branches_with_aux acc n i s = skip_branches_with n i s ++ acc.
  Proof.
    unfold skip_branches_with.
    induction n; intros; simpl; auto.
    rewrite IHn, cons_is_app; symmetry; rewrite IHn.
    now rewrite app_assoc.
  Qed.

  Fact skip_branches_with_0:
    forall i s,
      skip_branches_with 0 i s = [].
  Proof. reflexivity. Qed.

  Fact skip_branches_with_S:
    forall n i s,
      skip_branches_with (S n) i s =
      skip_branches_with n i s ++ [if n ==b i then Some s else None].
  Proof.
    intros; unfold skip_branches_with at 1; simpl.
    now rewrite skip_branches_with_aux_app.
  Qed.

  Fact skip_branches_with_length:
    forall n i s,
      length (skip_branches_with n i s) = n.
  Proof.
    induction n; intros; simpl; auto.
    rewrite skip_branches_with_S, app_length, IHn; simpl; lia.
  Qed.

  Fact nth_error_skip_branches_with:
    forall n i j s,
      nth_error (skip_branches_with n i s) j =
      if Compare_dec.le_lt_dec n j then None
      else Some (if Nat.eq_dec j i then Some s else None).
  Proof.
    induction n; intros.
    - unfold skip_branches_with; simpl.
      apply nth_error_nil.
    - destruct (Compare_dec.le_lt_dec (S n) j) as [|LT].
      + apply nth_error_None.
        now rewrite skip_branches_with_length.
      + rewrite skip_branches_with_S.
        rewrite Nat.lt_succ_r in LT. apply Nat.lt_eq_cases in LT as [|].
        * rewrite nth_error_app1.
          -- rewrite IHn.
             destruct (Compare_dec.le_lt_dec n j); auto; lia.
          -- now rewrite skip_branches_with_length.
        * subst; rewrite nth_error_app2; rewrite skip_branches_with_length; auto.
          rewrite Nat.sub_diag; simpl; auto.
          destruct (Nat.eq_dec n i) as [|Neq]; subst.
          -- now rewrite equiv_decb_refl.
          -- apply not_equiv_decb_equiv in Neq; now rewrite Neq.
  Qed.

  Fact skip_branches_with_In:
    forall n i s,
      i < n ->
      In (Some s) (skip_branches_with n i s).
  Proof.
    induction n; intros * Lt; try lia.
    rewrite skip_branches_with_S.
    rewrite Nat.lt_succ_r in Lt. apply Compare_dec.le_lt_eq_dec in Lt as [|].
    - apply in_app; auto.
    - subst; apply in_app; rewrite equiv_decb_refl; right; constructor; auto.
  Qed.

  Lemma skip_branches_with_In_det:
    forall n e s s',
      In (Some s') (skip_branches_with n e s) ->
      s' = s.
  Proof.
    induction n; intros * Hin.
    - rewrite skip_branches_with_0 in Hin; contradiction.
    - rewrite skip_branches_with_S in Hin.
      apply in_app in Hin as [|Hin]; eauto.
      inv Hin; try contradiction.
      cases.
  Qed.

End TRANSLATION.

Module TranslationFun
       (Ids    : IDS)
       (Op     : OPERATORS)
       (OpAux  : OPERATORS_AUX Ids Op)
       (Cks    : CLOCKS    Ids Op OpAux)
       (CESyn  : CESYNTAX  Ids Op OpAux Cks)
       (SynStc : STCSYNTAX Ids Op OpAux Cks CESyn)
       (SynObc : OBCSYNTAX Ids Op OpAux)
<: TRANSLATION Ids Op OpAux Cks CESyn SynStc SynObc.
  Include TRANSLATION Ids Op OpAux Cks CESyn SynStc SynObc.
End TranslationFun.
