Require Import List.
Import List.ListNotations.
Open Scope list_scope.
Require Import Coq.Sorting.Permutation.

Require Import Coq.FSets.FMapPositive.

Require Import Velus.Common.
Require Import Velus.Environment.
Require Import Velus.Operators.
Require Import Velus.RMemory.
Require Import Velus.Clocks.
Require Import Velus.CoreExpr.

Require Export NLustre.NLSyntax.
Require Export NLustre.IsFree.
Require Export NLustre.IsDefined.
Require Export NLustre.IsVariable.
Require Export NLustre.Memories.
Require Export NLustre.NLSemantics.
Require Export NLustre.MemSemantics.
Require Export NLustre.NLOrdered.
Require Export NLustre.NoDup.
Require Export NLustre.NLClocking.
Require Export NLustre.NLClockingSemantics.
Require Export NLustre.NLTyping.
Require Export NLustre.IsFree.

(** * Interpreter for NLustre *)

Module Type NLINTERPRETER
       (Import Ids      : IDS)
       (Import Op       : OPERATORS)
       (Import OpAux    : OPERATORS_AUX    Op)
       (Import Str      : STREAM           Op OpAux)
       (Import CE       : COREEXPR     Ids Op OpAux Str)
       (Import NLSyn    : NLSYNTAX     Ids Op       CE.Syn)
       (Import NLOrd    : NLORDERED    Ids Op       CE.Syn NLSyn)
       (Import NLSem    : NLSEMANTICS  Ids Op OpAux CE.Syn NLSyn Str NLOrd CE.Sem)
       (Import NLTyp    : NLTYPING     Ids Op       CE.Syn NLSyn     NLOrd CE.Typ)
       (Import Mem      : MEMORIES     Ids Op       CE.Syn NLSyn)
       (Import IsD      : ISDEFINED    Ids Op       CE.Syn NLSyn           Mem)
       (Import IsV      : ISVARIABLE   Ids Op       CE.Syn NLSyn           Mem IsD)
       (Import IsF      : ISFREE       Ids Op       CE.Syn NLSyn CE.IsF)
       (Import NoD      : NODUP        Ids Op       CE.Syn NLSyn           Mem IsD IsV)
       (Import NLClo    : NLCLOCKING   Ids Op       CE.Syn NLSyn     NLOrd Mem IsD     CE.IsF IsF CE.Clo)
       (Import NLCloSem : NLCLOCKINGSEMANTICS Ids Op OpAux CE.Syn NLSyn Str NLOrd CE.Sem NLSem Mem IsD CE.IsF IsF CE.Clo NLClo CE.CloSem)
       (Import MemSem   : MEMSEMANTICS Ids Op OpAux CE.Syn NLSyn Str NLOrd CE.Sem NLSem Mem IsD IsV CE.IsF IsF NoD CE.Clo NLClo CE.CloSem NLCloSem).

  Definition updates_env (R : Sem.env) : list positive -> list value -> option Sem.env :=
    fix go (xs : list positive) (vs : list value) : option Sem.env :=
      match xs, vs with
      | x::xs, v::vs => option_map (Env.add x v) (go xs vs)
      |    [],    [] => Some R
      |     _,     _ => None
      end.

  Definition init_eq (init_memory : ident -> memory val)
                     (eq : equation) (M' : memory val) : memory val :=
    match eq with
    | EqDef x ck ce => M'
    | EqApp xs ck f es r =>
      match hd_error xs with
      | Some x => add_inst x (init_memory f) M'
      | _ => M'
      end
    | EqFby x ck c0 e => add_val x (sem_const c0) M'
    end.
  
  Fixpoint init_memory (G : global) (f : ident) : memory val :=
    match G with
    | n::G' =>
      if n.(n_name) ==b f
      then fold_right (init_eq (init_memory G')) (empty_memory _) n.(n_eqs)
      else init_memory G' f
    | []    => empty_memory _
    end.

  Definition next_from_equation
             (base : bool) (R : Sem.env) (eq : equation) (M' : memory val)
    : option (memory val) :=
    match eq with
    | EqDef x ck ce => Some M'
    | EqApp xs ck f es r => Some M'
    | EqFby x ck c0 e =>
      match interp_laexp_instant base R ck e with
      | Some (present v) => Some (add_val x v M')
      | Some absent => Some M'
      | None => None
      end
    end.

  Definition interp_equation
             (interp_node : ident -> list value -> bool -> memory val ->
                            option (memory val * list value))
             (init_node : ident -> memory val)
             (base : bool)
             (M : memory val)
             (eq : equation) (RM' : Sem.env * memory val)
    : option (Sem.env * memory val) :=
    let '(R, M') := RM' in
    match eq with
    | EqDef x ck ce => option_map (fun v=> (Env.add x v R, M') )
                                  (interp_caexp_instant base R ck ce)

    | EqApp xs ck f es r =>
      match hd_error xs with
      | Some x =>
        let I :=
            match r with
            | None => find_inst x M
            | Some r =>
              match interp_var_instant R r with
              | Some (present v) =>
                if v ==b true_val then Some (init_node f)
                else if v ==b false_val then find_inst x M
                     else None
              | _ => None
              end
            end
        in
        match I, interp_lexps_instant base R es with
        | Some Mi, Some vs =>
          match interp_node f vs (existsb (fun x => x <>b absent) vs) Mi with
          | Some (Mi', rvs) =>
            option_map (fun env' => (env', add_inst x Mi' M')) (updates_env R xs rvs)
          | None => None
          end
        | _, _ => None
        end
      | _ => None
      end

    | EqFby x ck c0 e =>
      match interp_clock_instant base R ck, find_val x M with
      | Some b, Some v => Some (Env.add x (if b then present v else absent) R, M')
      | _, _ => None
      end
    end.
  
  Fixpoint interp_node (G : global) (f : ident) (vs : list value) (base : bool) (M : memory val)
    : option (memory val * list value) :=
    match G with
    | n::G' =>
      if n.(n_name) ==b f then
        match
          ofold_right (interp_equation (interp_node G') (init_memory G') base M)
                      (option_map (fun env => (env, empty_memory _))
                                  (updates_env (Env.empty _) (map fst n.(n_in)) vs))
                      n.(n_eqs)
        with
        | Some (env', M') =>
          match ofold_right (next_from_equation base env') (Some M') n.(n_eqs),
                omap (fun x => Env.find x env') (map fst n.(n_out))
          with
          | Some M'', Some rvs => Some (M'', rvs)
          | _, _ => None
          end
        | None => None
        end
      else interp_node G' f vs base M

    | []    => None
    end.

  Inductive Is_required_by_eq : ident -> equation -> Prop :=
  | IRBEqDef:
      forall x ck ce i,
        Is_free_in_caexp i ck ce ->
        Is_required_by_eq i (EqDef x ck ce)
  | IRBEqApp:
      forall x f ck les i r,
        Is_free_in_laexps i ck les \/ (r = Some i) ->
        Is_required_by_eq i (EqApp x ck f les r)
  | IRBEqFby:
      forall x v ck le i,
        Is_free_in_clock i ck ->
        Is_required_by_eq i (EqFby x ck v le).

  Hint Constructors Is_required_by_eq.

  Inductive Is_causal (inputs : list ident) : list equation -> Prop :=
  | ICnil:
      Is_causal inputs []
  | ICcons: forall eq eqs,
      Is_causal inputs eqs ->
      (forall x, Is_required_by_eq x eq ->
                 Is_defined_in_eqs x eqs \/ In x inputs) ->
      Is_causal inputs (eq :: eqs).

  Hint Constructors Is_causal.

  Inductive Ops_defined_in_eq (base : bool) (R : env) : equation -> Prop :=
  | ODEqDef:
      forall x ck ce,
        Ops_defined_in_cexp base R ce ->
        Ops_defined_in_eq base R (EqDef x ck ce)
  | ODEqApp:
      forall x ck f les r,
        Forall (Ops_defined_in_lexp base R) les ->
        Ops_defined_in_eq base R (EqApp x ck f les r)
  | ODEqFby:
      forall x v ck le,
        Ops_defined_in_lexp base R le ->
        Ops_defined_in_eq base R (EqFby x ck v le).

  (** Properties of [init_memory] *)

  Lemma init_memory_cons:
    forall n G f,
      n.(n_name) <> f ->
      init_memory (n :: G) f = init_memory G f.
  Proof.
    intros * Hnf. simpl.
    apply not_equiv_decb_equiv in Hnf. now setoid_rewrite Hnf.
  Qed.

  Lemma find_values_init_memory_skip_cons:
    forall S IM eq eqs x,
      ~In x (gather_mem_eq eq) ->
      Env.find x (values (fold_right (init_eq IM) S (eq :: eqs)))
      = Env.find x (values (fold_right (init_eq IM) S eqs)).
  Proof.
    destruct eq; simpl; auto.
    - destruct (hd_error i); auto.
    - intros eqs x nDef. rewrite Env.gso; auto.
  Qed.

  Lemma find_values_init_memory_skip:
    forall S IM eqs x,
      ~In x (gather_mems eqs) ->
      Env.find x (values (fold_right (init_eq IM) S eqs)) = Env.find x (values S).
  Proof.    
    induction eqs as [|eq eqs IH]; auto.
    intros * HH. rewrite In_gather_mems_cons in HH.
    apply Decidable.not_or in HH as (? & ?).
    rewrite find_values_init_memory_skip_cons, IH; auto.
  Qed.

  Lemma find_instances_init_memory_skip_cons:
    forall S IM eq eqs x,
      ~InMembers x (gather_inst_eq eq) ->
      Env.find x (instances (fold_right (init_eq IM) S (eq :: eqs)))
      = Env.find x (instances (fold_right (init_eq IM) S eqs)).
  Proof.
    destruct eq; simpl; auto.
    destruct i; auto. simpl.
    intros * HH. apply Decidable.not_or in HH as (HH & ?).
    rewrite Env.gso; auto.
  Qed.
  
  Lemma find_instances_init_memory_skip:
    forall S IM eqs i,
      ~InMembers i (gather_insts eqs) ->
      Env.find i (instances (fold_right (init_eq IM) S eqs)) = Env.find i (instances S).
  Proof.    
    induction eqs as [|eq eqs IH]; auto.
    intros * HH. rewrite In_gather_insts_cons in HH.
    apply Decidable.not_or in HH as (? & ?).
    rewrite find_instances_init_memory_skip_cons, IH; auto.
  Qed.

  Lemma init_memory_correct:
    forall G f xss M M' yss,
      Ordered_nodes G ->
      msem_node G f xss M M' yss ->
      init_memory G f ≋ M 0.
  Proof.
    induction G as [|n G IH]. now inversion 2; discriminate.
    intros f xss M M' yss OnG MSEM.
    destruct (ident_eq_dec n.(n_name) f).
    2:now apply msem_node_cons in MSEM; try (inv OnG; rewrite init_memory_cons); eauto.
    inversion MSEM as [??????? n' Hbk Fn Sin Sout Sck Meqs Mc Mc']; subst; clear MSEM.
    simpl in *. rewrite equiv_decb_refl, ident_eqb_refl in *. symmetry in Fn; inv Fn.
    setoid_rewrite <-msem_equations_cons with (1:=OnG) in Meqs;
      [|eauto using Not_Is_node_in_self].
    clear Sin Sout Sck Mc'.
    pose proof (NoDup_var_defined_n_eqs n) as ND.
    split.
    - (* values (M 0) *)
      intro x. destruct (In_gather_mems_dec x n.(n_eqs)) as [D|nD].
      2:{ rewrite find_values_init_memory_skip with (1:=nD), Env.gempty.
          specialize (Mc 0) as (Mc1 & Mc2).
          assert (forall x, ~In x (gather_mems n.(n_eqs)) -> find_val x (M 0) = None) as Vc
              by (intro; rewrite <-None_eq_dne; apply flip_impl with (1:=Mc2 _)).
          setoid_rewrite Vc; auto. }
      clear Mc.
      induction n.(n_eqs) as [|eq eqs IHeqs]; [now inv D|];
        apply Forall_cons2 in Meqs as (Meq & Meqs).
      apply NoDup_In_gather_mems with (1:=ND) in D as [(D & nD)|(nD & D)];
        apply NoDup_vars_defined_cons in ND.
      2:now rewrite find_values_init_memory_skip_cons with (1:=nD), IHeqs; auto.
      destruct eq; [contradiction|contradiction|].
      simpl in *. destruct D; try contradiction; subst.
      rewrite Env.gss. inv Meq.
      match goal with [ H: mfby _ _ _ _ _ _ |- _ ] => destruct H as (F0 & ?) end.
      now setoid_rewrite F0.
    - (* instances (M 0) *)
      apply Env.Env_equiv_orel. intro i.
      destruct (In_gather_insts_dec i n.(n_eqs)) as [D|nD].
      2:{ rewrite find_instances_init_memory_skip with (1:=nD), Env.gempty.
          specialize (Mc 0) as (Mc1 & Mc2).
          assert (forall x, ~InMembers x (gather_insts n.(n_eqs)) -> find_inst x (M 0) = None) as Vc
              by (intro; rewrite <-None_eq_dne; apply flip_impl with (1:=Mc1 _)).
          setoid_rewrite Vc; now auto. }
      clear Mc.
      induction n.(n_eqs) as [|eq eqs IHeqs]; [now inv D|];
        apply Forall_cons2 in Meqs as (Meq & Meqs).
      apply NoDup_In_gather_insts with (1:=ND) in D as [(D & nD)|(nD & D)];
        apply NoDup_vars_defined_cons in ND.
      2:now rewrite find_instances_init_memory_skip_cons with (1:=nD), IHeqs; auto.
      destruct eq; [contradiction| |contradiction].
      simpl in *. destruct i0; inv D; try contradiction.
      simpl. rewrite Env.gss. inversion_clear OnG as [|?? OnG'].
      inv Meq.
      + (* without reset *)
        match goal with [ H:hd_error _ = Some _ |- _ ] => inv H end.
        match goal with [ Hm: msem_node G _ _ _ _ _ |- _ ] =>
                        specialize (IH _ _ _ _ _ OnG' Hm) end.
        rewrite IH.
        match goal with [ H:sub_inst_n x M Mx |- _ ] => rewrite <-(H 0) end.
        reflexivity.
      + (* with reset *)
        match goal with [ H:hd_error _ = Some _ |- _ ] => inv H end.
        match goal with [ H:sub_inst_n x M Mx |- _ ] => rename H into M_Mx end.
        specialize (M_Mx 0). unfold find_inst in M_Mx; rewrite M_Mx.
        match goal with [ H:msem_reset _ _ _ _ _ _ _ |- _ ] =>
                        inversion_clear H as [?????? Insts] end.
        specialize (Insts 0) as (Mk & Mk' & Msem & MM1 & MM2).
        specialize (IH _ _ _ _ _ OnG' Msem) as ->.
        now specialize (MM1 0 eq_refl) as ->.
  Qed.

  (* TODO: Do we need causality of all nodes? *)
  Lemma interp_node_correct:
    forall G f xss M M' yss,
      msem_node G f xss M M' yss
      <->
      (forall n N,
          N ≋ M n ->
          exists N',
            interp_node G f (xss n) true N = Some (N', yss n)
            /\ N' ≋ M' n).
  Proof.
  Admitted.

  Definition mem_inv : memory val -> Prop := (fun M => True).
  (* TODO: well-formedness of memory tree:
           all fby's are defined with the correct type
           all instances exist and mem_inv holds for each
           anything else?
           May need to count the number of resets of each node to determine
           which instance applies (use existentials to avoid having to
           store a value somewhere). *)
  
  Lemma interp_node_instant_good:
    forall G f base xs N,
      Ordered_nodes G ->
      wt_global G ->
      wc_global G ->
      (* TODO: well_typed xs /\ well_clocked xs *)
      (* TODO: Ops_defined in nodes, recursively *)
      (* TODO: Causality of all nodes *)
      mem_inv N ->
      exists N' ys,
        interp_node G f xs base N = Some (N', ys).
  Proof.
  Admitted.

End NLINTERPRETER.

Module NLInterpreterFun
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX   Op)
       (Import Str   : STREAM          Op OpAux)
       (Import CE    : COREEXPR    Ids Op OpAux Str)
       (Import NLSyn : NLSYNTAX    Ids Op       CE.Syn)
       (Import NLOrd : NLORDERED   Ids Op       CE.Syn NLSyn)
       (Import NLSem : NLSEMANTICS Ids Op OpAux CE.Syn NLSyn Str NLOrd CE.Sem)
       (Import NLTyp : NLTYPING    Ids Op       CE.Syn NLSyn     NLOrd CE.Typ)
       (Import Mem   : MEMORIES    Ids Op       CE.Syn NLSyn)
       (Import IsD   : ISDEFINED   Ids Op       CE.Syn NLSyn                     Mem)
       (Import IsF   : ISFREE      Ids Op       CE.Syn NLSyn CE.IsF)
       (Import NLClk : NLCLOCKING  Ids Op       CE.Syn NLSyn     NLOrd Mem IsD CE.IsF IsF CE.Clo)
       <: NLINTERPRETER Ids Op OpAux Str CE NLSyn NLOrd NLSem NLTyp Mem IsD IsF NLClk.
  Include NLINTERPRETER Ids Op OpAux Str CE NLSyn NLOrd NLSem NLTyp Mem IsD IsF NLClk.
End NLInterpreterFun.

