From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Velus Require Import Common.
From Velus Require Import CommonTyping.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import VelusMemory.
From Velus Require Import Obc.ObcSyntax.
From Velus Require Import Obc.ObcSemantics.
From Velus Require Import Obc.ObcInvariants.
From Velus Require Import Obc.ObcTyping.
(* From Velus Require Import Obc.Equiv. *)

Module Type OBCDEADCODE
  (Import Ids   : IDS)
  (Import Op    : OPERATORS)
  (Import OpAux : OPERATORS_AUX Ids Op)
  (Import SynObc: OBCSYNTAX     Ids Op OpAux)
  (Import ComTyp: COMMONTYPING  Ids Op OpAux)
  (Import SemObc: OBCSEMANTICS  Ids Op OpAux SynObc)
  (Import InvObc: OBCINVARIANTS Ids Op OpAux SynObc        SemObc)
  (Import TypObc: OBCTYPING     Ids Op OpAux SynObc ComTyp SemObc).
  (* (Import Equ   : EQUIV         Ids Op OpAux SynObc ComTyp SemObc TypObc). *)

  (** ** Dead Updates Elimination
      Remove instruction of the form state.x = state.x
   *)

  Fixpoint deadcode_stmt (s: stmt): stmt :=
    match s with
    | AssignSt x (State y _ _) _ =>
        if x ==b y then Skip else s
    | Switch e ss sd =>
        Switch e (map (option_map deadcode_stmt) ss) (deadcode_stmt sd)
    | Comp s1 s2 =>
        Comp (deadcode_stmt s1) (deadcode_stmt s2)
    | _ => s
    end.

  Definition deadcode_method (m: method): method :=
    mk_method (m_name m) (m_in m) (m_vars m) (m_out m)
              (deadcode_stmt (m_body m))
              (m_nodupvars m) (m_good m).

  Lemma map_m_name_deadcode_methods:
    forall methods,
      map m_name (map deadcode_method methods) = map m_name methods.
  Proof.
    intros. now rewrite map_map.
  Qed.

  Program Definition deadcode_class (c: class): class :=
    mk_class (c_name c) (c_mems c) (c_objs c)
             (map deadcode_method (c_methods c))
             (c_nodup c) _ (c_good c).
  Next Obligation.
    rewrite map_m_name_deadcode_methods. exact (c_nodupm c).
  Qed.

  Global Program Instance deadcode_class_transform_unit: TransformUnit class class :=
    { transform_unit := deadcode_class }.

  Global Program Instance deadcode_class_transform_state_unit: TransformStateUnit class class.

  Definition deadcode_program : program -> program := transform_units.

  Lemma deadcode_find_class:
    forall p id c p',
      find_class id p = Some (c, p') ->
      find_class id (deadcode_program p) = Some (deadcode_class c, deadcode_program p').
  Proof.
    intros * Find; apply find_unit_transform_units_forward in Find; auto.
  Qed.

  Lemma deadcode_find_method:
    forall f fm cls,
      find_method f cls.(c_methods) = Some fm ->
      find_method f (deadcode_class cls).(c_methods) = Some (deadcode_method fm).
  Proof.
    destruct cls; simpl.
    induction c_methods0 as [|m ms]; inversion 1.
    simpl.
    destruct (ident_eq_dec m.(m_name) f) as [He|Hne].
    - rewrite He, ident_eqb_refl in *.
      now injection H1; intro; subst.
    - apply ident_eqb_neq in Hne.
      rewrite Hne in *.
      inv c_nodupm0; auto.
  Qed.

  Lemma deadcode_find_method':
    forall id c m,
      find_method id (deadcode_class c).(c_methods) = Some m ->
      exists m', m = deadcode_method m'
            /\ find_method id c.(c_methods) = Some m'.
  Proof.
    intros * Find.
    destruct c as [? ? ? meths ? Nodup]; simpl in *.
    induction meths as [|m']; simpl in *; try discriminate.
    inv Nodup; auto.
    destruct (ident_eqb (m_name m') id); auto.
    inv Find.
    exists m'; auto.
  Qed.

  (** ** Semantic preservation *)

  Lemma deadcode_stmt_eval prog : forall s menv env menv' env',
      stmt_eval prog menv env s (menv', env') ->
      stmt_eval prog menv env (deadcode_stmt s) (menv', env').
  Proof.
    induction s using stmt_ind2'; intros * Sem; simpl; auto.
    - (* AssignSt *)
      cases_eqn Eq; auto.
      rewrite equiv_decb_equiv in Eq0. inv Eq0.
      inv Sem. take (exp_eval _ _ _ _) and inv it.
      unfold add_val. destruct menv0.
      rewrite Env.gsident; auto. constructor.
    - (* Switch *)
      inv Sem. econstructor; eauto.
      + take (nth_error _ _ = _) and rewrite nth_error_map, it; simpl; eauto.
      + take (nth_error _ _ = _) and apply nth_error_In in it.
        simpl_Forall.
        destruct s0; simpl in *; eauto.
    - (* Comp *)
      inv Sem. econstructor; eauto.
  Qed.

  Lemma deadcode_call:
    forall p n me me' f xss rs,
      stmt_call_eval p me n f xss me' rs ->
      stmt_call_eval (deadcode_program p) me n f xss me' rs.
  Proof.
    cut ((forall p me ve stmt e',
             stmt_eval p me ve stmt e' ->
             stmt_eval (deadcode_program p) me ve stmt e')
         /\ (forall p me clsid f vs me' rvs,
                stmt_call_eval p me clsid f vs me' rvs ->
                stmt_call_eval (deadcode_program p) me clsid f vs me' rvs)).
    now destruct 1 as (Hf1 & Hf2); intros; apply Hf2; auto.
    apply stmt_eval_call_ind; intros; eauto using stmt_eval.
    take (find_class _ _ = _) and rename it into Find.
    take (find_method _ _ = _) and rename it into Findm.
    apply deadcode_find_class in Find.
    apply deadcode_find_method in Findm.
    econstructor; eauto.
    - apply deadcode_stmt_eval; auto.
  Qed.

  Corollary deadcode_loop_call:
    forall f c ins outs prog me,
      loop_call prog c f ins outs 0 me ->
      loop_call (deadcode_program prog) c f ins outs 0 me.
  Proof.
    intros ?????; generalize 0%nat.
    cofix COINDHYP.
    intros n me Hdo.
    destruct Hdo.
    econstructor; eauto using deadcode_call.
  Qed.

  (** ** Typing preservation *)

  Lemma wt_exp_deadcode:
    forall p Γm Γv e,
      wt_exp p Γm Γv e ->
      wt_exp (deadcode_program p) Γm Γv e.
  Proof.
    induction e; inversion_clear 1; eauto using wt_exp.
  Qed.

  Lemma deadcode_stmt_wt:
    forall p insts Γm Γv s,
      wt_stmt p insts Γm Γv s ->
      wt_stmt (deadcode_program p) insts Γm Γv (deadcode_stmt s).
  Proof.
    induction s using stmt_ind2'; intros * Stmt; inv Stmt; simpl;
      eauto using wt_exp_deadcode with obctyping.
    - (* AssignSt *)
      cases; eauto using wt_exp_deadcode with obctyping.
    - (* Switch *)
      econstructor; eauto using wt_exp_deadcode.
      + now rewrite length_map.
      + intros * In. simpl_In. simpl_Forall. eauto.
    - (* Call *)
      econstructor; eauto using deadcode_find_class, deadcode_find_method.
      simpl_Forall; auto using wt_exp_deadcode.
    - (* ExtCall *)
      econstructor; eauto.
      simpl_Forall; auto using wt_exp_deadcode.
  Qed.

  Lemma deadcode_program_wt:
    forall p,
      wt_program p ->
      wt_program (deadcode_program p).
  Proof.
    intros * WT.
    eapply transform_units_wt_program in WT; eauto; simpl.
    inversion_clear 1 as (Hos & Hms).
    constructor; simpl_Forall.
    - apply not_None_is_Some in Hos as ((?&?)&Hfind).
      apply deadcode_find_class in Hfind.
      setoid_rewrite Hfind.
      discriminate.
    - simpl_In. simpl_Forall.
      inv Hms. econstructor; eauto.
      eapply deadcode_stmt_wt; eauto.
  Qed.

  Lemma deadcode_program_wt_memory:
    forall me p c,
      wt_memory me p c.(c_mems) c.(c_objs) ->
      wt_memory me (deadcode_program p) (deadcode_class c).(c_mems) (deadcode_class c).(c_objs).
  Proof.
    intros * WT.
    pose proof transform_units_wt_memory' as Spec; simpl in Spec.
    apply Spec in WT; auto.
  Qed.

  (** ** Preservation of [Can_write_in]. *)

  Lemma deadcode_stmt_Can_write_in_var:
    forall s x,
      Can_write_in_var x s <-> Can_write_in_var x (deadcode_stmt s).
  Proof.
    induction s using stmt_ind2'; simpl; try reflexivity; intros.
    - (* AssignSt *)
      cases; try reflexivity.
      split; intros CwI; inv CwI.
    - (* Switch *)
      rewrite ? Can_write_in_var_Switch.
      split; intros Ex; solve_Exists; simpl_Forall.
      1,2:take (option _) and destruct it; [apply H|apply IHs]; auto.
    - (* Comp *)
      rewrite ? Can_write_in_var_Comp, IHs1, IHs2.
      reflexivity.
  Qed.

  Lemma deadcode_program_cannot_write_inputs:
    forall p,
      Forall_methods (fun m => Forall (fun x => ~ Can_write_in_var x (m_body m)) (map fst (m_in m))) p ->
      Forall_methods (fun m => Forall (fun x => ~ Can_write_in_var x (m_body m)) (map fst (m_in m)))
                     (deadcode_program p).
  Proof.
    intros * HH.
    unfold Forall_methods in *. simpl_Forall. simpl_In. simpl_Forall.
    now rewrite <-deadcode_stmt_Can_write_in_var.
  Qed.

  (** ** Preservation of [No_Overwrites] *)

  Lemma deadcode_stmt_No_Overwrites:
    forall s,
      No_Overwrites s ->
      No_Overwrites (deadcode_stmt s).
  Proof.
    induction s using stmt_ind2'; intros * NO; auto; simpl; inv NO.
    - (* AssignSt *)
      cases; constructor.
    - (* Switch *)
      constructor. simpl_Forall.
      take (option _) and destruct it; auto.
    - (* Comp *)
      constructor; auto.
      1,2:intros *; rewrite <- ? deadcode_stmt_Can_write_in_var; auto.
  Qed.

  Lemma deadcode_program_No_Overwrites:
    forall p,
      Forall_methods (fun m => No_Overwrites (m_body m)) p ->
      Forall_methods (fun m => No_Overwrites (m_body m)) (deadcode_program p).
  Proof.
    intros * HH.
    unfold Forall_methods in *. simpl_Forall. simpl_In. simpl_Forall.
    apply deadcode_stmt_No_Overwrites; auto.
  Qed.

End OBCDEADCODE.

Module ObcDeadCodeFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (SynObc: OBCSYNTAX     Ids Op OpAux)
       (ComTyp: COMMONTYPING  Ids Op OpAux)
       (SemObc: OBCSEMANTICS  Ids Op OpAux SynObc)
       (InvObc: OBCINVARIANTS Ids Op OpAux SynObc         SemObc)
       (TypObc: OBCTYPING     Ids Op OpAux SynObc ComTyp SemObc)
       (* (Equ   : EQUIV         Ids Op OpAux SynObc ComTyp SemObc TypObc) *)
       <: OBCDEADCODE Ids Op OpAux SynObc ComTyp SemObc InvObc TypObc (* Equ *).
  Include OBCDEADCODE Ids Op OpAux SynObc ComTyp SemObc InvObc TypObc (* Equ *).
End ObcDeadCodeFun.
