From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Coq Require Import Recdef.
From Velus Require Import Common.
From Velus Require Import CommonProgram.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Environment.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import NLustre.NLSyntax.

(** Remove duplicate registers in an NLustre program *)

Module Type EI
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX   Ids Op)
       (Import Cks   : CLOCKS      Ids Op OpAux)
       (Import CESyn : CESYNTAX    Ids Op OpAux Cks)
       (Import Syn   : NLSYNTAX    Ids Op OpAux Cks CESyn).

  Section inline_exp.
    Variable x : ident.
    Variable ex : exp.

    Fixpoint inline_in_exp e :=
      match e with
      | Evar x' _ => if x ==b x' then ex else e
      | Ewhen e xt k => Ewhen (inline_in_exp e) xt k
      | Eunop op e1 ty => Eunop op (inline_in_exp e1) ty
      | Ebinop op e1 e2 ty => Ebinop op (inline_in_exp e1) (inline_in_exp e2) ty
      | _ => e
      end.
  End inline_exp.

  Section inline_cexp.
    Variable x : ident.
    Variable ex : cexp.

    Definition try_inline_in_exp e :=
      match ex with
      | Eexp ex => inline_in_exp x ex e
      | _ => e
      end.

    Fixpoint inline_in_cexp e :=
      match e with
      | Emerge xt es ty => Emerge xt (List.map inline_in_cexp es) ty
      | Ecase e es d =>
          Ecase (try_inline_in_exp e)
            (List.map (option_map inline_in_cexp) es)
            (inline_in_cexp d)
      | Eexp (Evar x' _) => if x ==b x' then ex else e
      | Eexp e => Eexp (try_inline_in_exp e)
      end.

    Definition inline_in_equation equ :=
      match equ with
      | EqDef x' ck (Ecexp e) => EqDef x' ck (Ecexp (inline_in_cexp e))
      | EqDef x' ck (Eextcall f es cty) =>
          EqDef x' ck (Eextcall f (List.map try_inline_in_exp es) cty)
      | _ => equ
      end.

    Definition inline_in_equations := List.map inline_in_equation.

  End inline_cexp.

  (* Heuristics part 1 : inline all equations where the variable is only used once *)
  Section nb_usage.
    Variable x : ident.

    Fixpoint nb_usage_in_exp e :=
      match e with
      | Evar x' _ => if (x ==b x') then 1 else 0
      | Ewhen e (x', _) _ => nb_usage_in_exp e
      | Eunop _ e1 _ => nb_usage_in_exp e1
      | Ebinop _ e1 e2 _ => nb_usage_in_exp e1 + nb_usage_in_exp e2
      | _ => 0
      end.

    Fixpoint nb_usage_in_cexp e :=
      match e with
      | Emerge (x', _) es _ => fold_left (fun n e => n + nb_usage_in_cexp e) es 0
      | Ecase e es d =>
          nb_usage_in_exp e
          + fold_left (fun n e => n + or_default_with 0 nb_usage_in_cexp e) es 0
          + nb_usage_in_cexp d
      | Eexp e => nb_usage_in_exp e
      end.

    Definition nb_usage_in_equation eq :=
      match eq with
      | EqDef _ _ (Eextcall _ es _) =>
          fold_left (fun n e => n + nb_usage_in_exp e) es 0
      | EqDef _ _ (Ecexp ce) => nb_usage_in_cexp ce
      | EqApp xs _ _ es xr =>
          fold_left (fun n e => n + nb_usage_in_exp e) es 0
      | EqFby _ _ _ _ _
      | EqLast _ _ _ _ _ => 0
      end.

    Definition nb_usage_in_equations eqs :=
      fold_left (fun n e => n + nb_usage_in_equation e) eqs 0.
  End nb_usage.

  (* Heuristics 2 : inline all equations where the calculation is "free"
     (read variable, possibly with when) *)
  Section always_inline.
    Variable x : ident.

    Fixpoint always_inline_exp e :=
      match e with
      | Evar _ _ | Elast _ _ => true
      | Ewhen e _ _ => always_inline_exp e
      | _ => false
      end.

    Definition always_inline_cexp ce :=
      match ce with
      | Eexp e => always_inline_exp e
      | _ => false
      end.

    Definition always_inline_rhs e :=
      match e with
      | Ecexp ce => always_inline_cexp ce
      | _ => false
      end.

    Definition always_inline_eq eq :=
      match eq with
      | EqDef x' _ e => (negb (x' ==b x)) || (always_inline_rhs e)
      | _ => true
      end.

    Definition always_inline eqs :=
      forallb always_inline_eq eqs.
  End always_inline.

  Definition inlinable vars (eqs: list equation) : list (ident * cexp) :=
    let vars' := PSP.of_list (map_filter (fun '(x, (_, islast)) => if (islast : bool) then None else Some x) vars) in
    (* Variables that are defined with a cexp *)
    let inl := map_filter
                 (fun equ => match equ with
                          | EqDef x _ (Ecexp ce) =>
                              if PS.mem x vars' then Some (x, ce) else None
                          | _ => None
                          end) eqs in
    filter
      (fun '(x, e) =>
         ((nb_usage_in_equations x eqs =? 1) || (always_inline x eqs)) (* Heuristics *)
         && forallb (fun '(_, (ck, islast)) => if (Is_free_in_clock_dec x ck) then false else true) vars
      )
      inl.

  Definition inline_all_possible vars eqs :=
    let toinline := inlinable vars eqs in
    List.fold_left (fun eqs '(x, ce) => inline_in_equations x ce eqs) toinline eqs.

  Lemma inline_all_possible_vars : forall vars eqs,
      vars_defined (inline_all_possible vars eqs) = vars_defined eqs.
  Proof.
    intros.
    unfold inline_all_possible.
    rewrite <-fold_left_rev_right.
    induction (rev _) as [|(?&?)]; simpl; auto.
    unfold inline_in_equations, vars_defined in *.
    rewrite <-IHl, 2 flat_map_concat_map, map_map.
    f_equal. eapply map_ext. intros [??[]| | |]; simpl; auto.
  Qed.

  Lemma inline_all_possible_vars_fby : forall vars eqs,
      vars_defined (filter is_fby (inline_all_possible vars eqs)) = vars_defined (filter is_fby eqs).
  Proof.
    intros.
    unfold inline_all_possible.
    rewrite <-fold_left_rev_right.
    induction (rev _) as [|(?&?)]; simpl; auto.
    unfold inline_in_equations, vars_defined in *.
    rewrite <-IHl, 2 flat_map_concat_map.
    f_equal.
    clear - i. induction (fold_right _ _ _); simpl; auto.
    destruct a as [??[]| | |]; simpl; auto.
  Qed.

  Lemma inline_all_possible_vars_def_cexp : forall vars eqs,
      vars_defined (filter is_def_cexp (inline_all_possible vars eqs)) = vars_defined (filter is_def_cexp eqs).
  Proof.
    intros.
    unfold inline_all_possible.
    rewrite <-fold_left_rev_right.
    induction (rev _) as [|(?&?)]; simpl; auto.
    unfold inline_in_equations, vars_defined in *.
    rewrite <-IHl, 2 flat_map_concat_map.
    f_equal.
    clear - i. induction (fold_right _ _ _); simpl; auto.
    destruct a as [??[]| | |]; simpl; auto.
  Qed.

  Lemma inline_all_possible_lasts : forall lasts eqs,
      lasts_defined (inline_all_possible lasts eqs) = lasts_defined eqs.
  Proof.
    intros.
    unfold inline_all_possible.
    rewrite <-fold_left_rev_right.
    induction (rev _) as [|(?&?)]; simpl; auto.
    unfold inline_in_equations, lasts_defined in *.
    rewrite <-IHl, 2 flat_map_concat_map, map_map.
    f_equal. eapply map_ext. intros [??[]| | |]; simpl; auto.
  Qed.

  (** ** Transformation of the node and global *)

  Definition inline_all_possible' vars eqs:
    { res | inline_all_possible vars eqs = res }.
  Proof.
    econstructor. reflexivity.
  Defined.

  Definition idck (vars : list (ident * (type * clock * bool))) :=
    List.map (fun x => (fst x, (snd (fst (snd x)), snd (snd x)))) vars.

  Program Definition exp_inlining_node (n : node) : node :=
    let eqs' := inline_all_possible' (idck n.(n_vars)) n.(n_eqs) in
    {| n_name := n.(n_name);
       n_in := n.(n_in);
       n_out := n.(n_out);
       n_vars := n.(n_vars);
       n_eqs := eqs';
    |}.
  Next Obligation. exact n.(n_ingt0). Qed.
  Next Obligation. exact n.(n_outgt0). Qed.
  Next Obligation.
    rewrite inline_all_possible_vars. exact n.(n_defd).
  Qed.
  Next Obligation.
    rewrite inline_all_possible_lasts. exact n.(n_lastd1).
  Qed.
  Next Obligation.
    rewrite inline_all_possible_vars_def_cexp. eapply n.(n_lastd2); eauto.
  Qed.
  Next Obligation.
    rewrite inline_all_possible_vars_fby. eapply n.(n_vout); eauto.
  Qed.
  Next Obligation. exact n.(n_nodup). Qed.
  Next Obligation. exact n.(n_good). Qed.

  Local Program Instance exp_inlining_node_transform_unit: TransformUnit node node :=
    { transform_unit := exp_inlining_node }.

  Local Program Instance exp_inlining_without_units: TransformProgramWithoutUnits global global :=
    { transform_program_without_units := fun g => Global g.(types) g.(externs) [] }.

  Definition exp_inlining : global -> global := transform_units.

  (** *** Some properties *)

  Lemma find_node_exp_inlining_forward : forall G f n,
      find_node f G = Some n ->
      find_node f (exp_inlining G) = Some (exp_inlining_node n).
  Proof.
    unfold exp_inlining, find_node.
    intros * Hfind.
    apply option_map_inv in Hfind as ((?&?)&Hfind&?); subst.
    apply find_unit_transform_units_forward in Hfind.
    rewrite Hfind; auto.
  Qed.

  Lemma find_node_exp_inlining_backward : forall G f n,
      find_node f (exp_inlining G) = Some n ->
      exists n0, find_node f G = Some n0 /\ n = exp_inlining_node n0.
  Proof.
    unfold exp_inlining, find_node.
    intros * Hfind.
    apply option_map_inv in Hfind as ((?&?)&Hfind&?); subst.
    apply find_unit_transform_units_backward in Hfind as (?&?&Hfind&?&?); subst.
    exists x. repeat split; auto.
    rewrite Hfind; auto.
  Qed.

  Lemma exp_inlining_iface_eq : forall G,
      global_iface_eq G (exp_inlining G).
  Proof.
    intros. repeat (split; auto). intros.
    destruct (find_node _ _) eqn:Hfind.
    - erewrite find_node_exp_inlining_forward; eauto.
      constructor; simpl.
      repeat (split; auto).
    - destruct (find_node f (exp_inlining _)) eqn:Hfind'; try constructor.
      exfalso.
      apply find_node_exp_inlining_backward in Hfind' as (?&?&_); congruence.
  Qed.

End EI.

Module EIFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX   Ids Op)
       (Cks   : CLOCKS      Ids Op OpAux)
       (CESyn : CESYNTAX    Ids Op OpAux Cks)
       (Syn   : NLSYNTAX    Ids Op OpAux Cks CESyn)
<: EI Ids Op OpAux Cks CESyn Syn.
  Include EI Ids Op OpAux Cks CESyn Syn.
End EIFun.
