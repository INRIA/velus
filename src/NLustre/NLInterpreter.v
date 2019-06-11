From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Coq Require Import Setoid Relations RelationPairs Morphisms.

From Coq Require Import Sorting.Permutation.
From Coq Require Import FSets.FMapPositive.

From Velus Require Import Common.
From Velus Require Import Environment.
From Velus Require Import Operators.
From Velus Require Import RMemory.
From Velus Require Import Clocks.
From Velus Require Import CoreExpr.

From Velus Require Export NLustre.NLSyntax.
From Velus Require Export NLustre.IsFree.
From Velus Require Export NLustre.IsDefined.
From Velus Require Export NLustre.IsVariable.
From Velus Require Export NLustre.Memories.
From Velus Require Export NLustre.NLSemantics.
From Velus Require Export NLustre.MemSemantics.
From Velus Require Export NLustre.NLOrdered.
From Velus Require Export NLustre.NoDup.
From Velus Require Export NLustre.NLClocking.
From Velus Require Export NLustre.NLClockingSemantics.
From Velus Require Export NLustre.NLTyping.
From Velus Require Export NLustre.IsFree.

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

  Open Scope option_monad_scope.
  Import Env.Notations.

  (** Reasoning with [obind] and [orel] *)

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
    (base : bool) (M : memory val) (R : Sem.env) (eq : equation) (M' : memory val)
    : option (memory val) :=
    match eq with
    | EqDef x ck ce => Some M'
    | EqApp xs ck f es r => Some M'
    | EqFby x ck c0 e =>
      do v <- interp_laexp_instant base R ck e;
      match v with
      | present c => Some (add_val x c M')
      | absent => option_map (fun c => add_val x c M') (find_val x M)
      end
    end.

  Definition maybe_reset (init_node : ident -> memory val) (f : ident)
                         (M : memory val) (x :ident) (rv : option value)
                         : option (memory val) :=
    match rv with
    | Some (present v) =>
         if v ==b true_val then Some (init_node f)
         else if v ==b false_val then find_inst x M
              else None
    | Some absent => find_inst x M
    | _ => None
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
    | EqDef x ck ce =>
      do v <- interp_caexp_instant base R ck ce;
      Some (Env.add x v R, M')

    | EqApp xs ck f es r =>
      do x <- hd_error xs;
      do Mi <- match r with
             | None => find_inst x M
             | Some r => maybe_reset init_node f M x (interp_var_instant R r)
             end;
      do vs <- interp_lexps_instant base R es;
      do (Mi', rvs) <- interp_node f vs (clock_of_instant vs) Mi;
      do env' <- updates_env R xs rvs;
      Some (env', add_inst x Mi' M')

    | EqFby x ck c0 e =>
      do c <- interp_clock_instant base R ck;
      if c then
        do v <- find_val x M;
        Some (Env.add x (present v) R, M')
      else Some (Env.add x absent R, M')
    end.

  Fixpoint interp_node (G : global) (f : ident) (vs : list value) (base : bool) (M : memory val)
    : option (memory val * list value) :=
    match G with
    | n::G' =>
      if n.(n_name) ==b f then
        do env <- updates_env (Env.empty _) (map fst n.(n_in)) vs;
        do (env', M') <- ofold_right (interp_equation (interp_node G')
                                                     (init_memory G') base M)
           (Some (env, empty_memory _)) n.(n_eqs);
        do M'' <- ofold_right (next_from_equation base M env') (Some M') n.(n_eqs);
        do rvs <- omap (fun x => Env.find x env') (map fst n.(n_out));
        Some (M'', rvs)
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
                 Is_defined_in x eqs \/ In x inputs) ->
      Is_causal inputs (eq :: eqs).

  Hint Constructors Is_causal.

  Definition Causal (n : node) : Prop :=
    Is_causal (map fst n.(n_in)) n.(n_eqs).

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
      take (mfby _ _ _ _ _ _) and destruct it as (F0 & ?).
      now setoid_rewrite F0.
    - (* instances (M 0) *)
      apply Env.Equiv_orel. intro i.
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
        take (hd_error _ = Some _) and inv it.
        take (msem_node G _ _ _ _ _) and specialize (IH _ _ _ _ _ OnG' it).
        rewrite IH.
        take (sub_inst_n x M Mx) and rewrite <-(it 0).
        reflexivity.
      + (* with reset *)
        take (hd_error _ = Some _) and inv it.
        take (sub_inst_n x M Mx) and rename it into M_Mx.
        specialize (M_Mx 0). unfold find_inst in M_Mx; rewrite M_Mx.
        take (msem_reset _ _ _ _ _ _ _) and inversion_clear it as [?????? Insts].
        specialize (Insts 0) as (Mk & Mk' & Msem & MM1 & MM2).
        specialize (IH _ _ _ _ _ OnG' Msem) as ->.
        now specialize (MM1 0 eq_refl) as ->.
  Qed.

  Lemma sem_vars_updates_env:
    forall R nins xss os env,
      sem_vars_instant R nins xss ->
      env ⊑ R ->
      Env.dom env os ->
      (forall x, In x nins -> ~Env.In x env) ->
      exists env', updates_env env nins xss = Some env'
              /\ env ⊑ env'
              /\ env' ⊑ R
              /\ Env.dom env' (os ++ nins).
  Proof.
    induction nins as [|x nins IH]; simpl; intros v os env Sv Henv Denv Nex.
    now inv Sv; eexists; repeat split; eauto.
    inversion Sv as [|x' vs nins' xss' Svs Sxss']; subst.
    assert (forall x, In x nins -> ~Env.In x env) as Nex' by auto.
    specialize (IH _ _ _ Sxss' Henv Denv Nex') as (env0 & Uenv0 & Menv & Menv0 & In0).
    setoid_rewrite Uenv0; simpl.
    eexists; split; [reflexivity|].
    repeat split.
    - apply Env.refines_add_right with (3:=Menv); auto.
    - apply Env.refines_add_left with (v2:=vs); auto.
    - setoid_rewrite <-Permutation_middle.
      now apply Env.dom_add_cons.
  Qed.

  Global Instance maybe_reset_Proper:
    Proper (eq ==> eq ==> equal_memory ==> eq ==> eq ==> orel equal_memory)
           maybe_reset.
  Proof.
    intros f' f Ef x' x Ex M' M EM y y' Ey vo' vo Evo; subst.
    unfold maybe_reset. destruct vo; [|reflexivity].
    destruct v. now setoid_rewrite EM.
    destruct (c ==b true_val); [reflexivity|].
    destruct (c ==b false_val); [|reflexivity].
    now rewrite EM.
  Qed.

  Global Instance updates_env_Proper:
    Proper (Env.Equal ==> eq ==> eq ==> orel Env.Equal) updates_env.
  Proof.
    intros E' E EE xs' xs Exs vs' vs Evs; subst.
    revert vs. induction xs; simpl; destruct vs; auto. now rewrite EE.
    now rewrite IHxs.
  Qed.

  Global Instance interp_equation_Proper_Equal
    f `{Proper _ (eq ==> eq ==> eq ==> equal_memory ==> orel (equal_memory * eq)) f} :
    Proper (eq ==> eq ==> equal_memory ==> eq
               ==> Env.Equal * equal_memory
               ==> orel (Env.Equal * equal_memory)) (interp_equation f).
  Proof.
    intros i' i Ei b' b Eb M' M EM eq' eq Eeq (R', N') (R, N) (ER, EN); subst.
    assert (Env.Equal R' R) as HRR by auto; clear ER.
    assert (equal_memory N' N) as HNN by auto; clear EN.
    destruct eq; simpl; solve_orel_obinds.
  Qed.

  Global Instance next_from_equation_Proper:
    Proper (eq ==> equal_memory ==> Env.Equal ==> eq ==> equal_memory ==> orel equal_memory)
           next_from_equation.
  Proof.
    intros b' b Eb M' M EM e' e Ee eq' eq Eeq N' N EN; subst.
    destruct eq; simpl; try (rewrite EN; reflexivity); auto.
    solve_orel_obinds. apply orel_option_map.
    now setoid_rewrite EN.
  Qed.

  Global Instance interp_node_Proper:
    Proper (eq ==> eq ==> eq ==> eq ==> equal_memory ==> orel (equal_memory * eq))
           interp_node.
  Proof.
    intros G' G EG; subst.
    induction G; intros f' f Ef xs' xs Exs b' b Eb M1 M2 EM; subst; simpl; auto.
    split_orel_obinds.
    - assert (Proper (eq ==> eq ==> equal_memory ==> eq
                         ==> Env.Equal * equal_memory
                                         ==> orel (Env.Equal * equal_memory))
                     (interp_equation (interp_node G)))
        by (now apply interp_equation_Proper_Equal).
      now setoid_rewrite EM.
    - now rewrite_orel_obinds.
    - apply orel_omap. now take (Env.Equal _ _) and setoid_rewrite it.
    - now rewrite (IHG f f eq_refl xs xs eq_refl b b eq_refl _ _ EM).
  Qed.

  (*
  Definition myrs n :=
    match n with
    | 3 | 6 | 9 => true
    | _ => false
    end.

  Eval compute in (map (count myrs) [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10]).

  Eval compute in (map (mask None 1 myrs (fun x => Some x))
                       [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10]).
   *)

  Lemma msem_node_maybe_reset:
    forall {G i f x M Mx Mk Mk' ys rs ls xss},
      Ordered_nodes G ->
      sub_inst_n x M Mx ->
      memory_masked (count rs i) rs Mx Mk ->
      reset_of ys rs ->
      msem_node G f (mask (all_absent (ls 0)) (count rs i) rs ls) Mk Mk' xss ->
      maybe_reset (init_memory G) f (M i) x (Some (ys i)) ⌈≋⌉ Some (Mk i).
  Proof.
    intros * OG M_Mx Mx_Mk Ryr MSN.
    unfold maybe_reset.
    specialize (Ryr i). specialize (M_Mx i) as ->. specialize (Mx_Mk i).
    destruct (ys i).
    - inversion Ryr as (Ryr'). rewrite <-Ryr' in Mx_Mk.
      now rewrite (Mx_Mk eq_refl).
    - simpl in Ryr. unfold val_to_bool in Ryr.
      destruct (c ==b true_val).
      + inversion Ryr as (Ryr').
        rewrite init_memory_correct; eauto.
        symmetry. rewrite msem_node_absent_until with (2:=MSN) (n0:=i); auto.
        intros n Hni. rewrite mask_opaque; auto using all_absent_spec.
        apply count_reset_gt with (rs:=rs) in Hni; auto.
        now apply PeanoNat.Nat.lt_neq.
      + destruct (c ==b false_val); [|discriminate].
         inversion Ryr as (Ryr'). rewrite <-Ryr' in Mx_Mk.
         now rewrite (Mx_Mk eq_refl).
  Qed.

  Lemma msem_equation_interp_equation:
    forall G bk H M M' inputs f__node i eqs env N,
      Proper (eq ==> eq ==> eq ==> equal_memory ==> orel (equal_memory * eq)) f__node ->
      (forall f xs M M' rvs,
          msem_node G f xs M M' rvs ->
          orel (equal_memory * eq)
               (f__node f (xs i) (clock_of_instant (xs i)) (M i))
               (Some ((M' i), rvs i))) ->
      Ordered_nodes G ->
      Is_causal inputs eqs ->
      NoDup (vars_defined eqs ++ inputs) ->
      env ⊑ (restr_hist H i) ->
      Env.dom env inputs ->
      N.(instances) ⊑⟨equal_memory⟩ (M' i).(instances) ->
      Env.dom N.(instances) nil ->
      Forall (msem_equation G bk H M M') eqs ->
      exists env' N',
        orel (Env.Equal * equal_memory)
             (ofold_right (interp_equation f__node (init_memory G) (bk i) (M i)) (Some (env, N)) eqs)
             (Some (env', N'))
        /\ N.(instances) ⊑⟨equal_memory⟩ N'.(instances)
        /\ N'.(instances) ⊑⟨equal_memory⟩ (M' i).(instances)
        /\ Env.dom N'.(instances) (map fst (gather_insts eqs))
        /\ N'.(values) = N.(values)
        /\ env ⊑ env'
        /\ env' ⊑ (restr_hist H i)
        /\ Env.dom env' (vars_defined eqs ++ inputs).
  Proof.
    induction eqs as [|equ eqs IH].
    - simpl; intros; exists env0, N. repeat split; eauto; reflexivity.
    - intros env0 N Pf__node Hf__node OG IC NDD Henv0 Hin Hinsts0 DN Meqs.
      rewrite ofold_right_cons; simpl.
      apply Forall_cons2 in Meqs as (Meq & Meqs).
      inversion_clear IC. take (Is_causal _ _) and rename it into IC.
      simpl. simpl in NDD; rewrite <-app_assoc in NDD.
      apply NoDup_app'_iff in NDD as (ND1 & ND2 & ND3).
      specialize (IH _ _ Pf__node Hf__node OG IC ND2 Henv0 Hin Hinsts0 DN Meqs)
        as (env' & N' & Hfold & Hinsts1 & Hinsts2 & Iin & Hvalues & Henv1 & Henv2 & Inx).
      setoid_rewrite (orel_obind_head Hfold); [simpl|typeclasses eauto].
      assert (forall x, Is_required_by_eq x equ -> Env.In x env') as ReqIn.
      { intros x Rx.
        take (forall x, Is_required_by_eq x equ -> _) and apply it in Rx as [|Ix];
          rewrite (Env.dom_use Inx); apply in_or_app; auto.
        take (Is_defined_in x eqs) and apply Is_defined_in_vars_defined in it; auto. }
      inv Meq; simpl.
      + (* EqDef *)
        take (sem_caexp _ _ _ _ _) and specialize (it i); pose (Sce:=it).
        apply sem_caexp_instant_switch_env with (R':=env') in Sce;
          [|now solve_switch_env_obligation].
        apply interp_caexp_instant_correct in Sce as ->; simpl.
        do 2 eexists; split; [reflexivity|].
        repeat split; eauto using Env.dom_add_cons.
        * apply Env.refines_add_right; auto. intro Ix.
          rewrite Henv1, (Env.dom_use Inx) in Ix.
          inversion_clear ND3 as [|?? Nx]; auto.
        * apply Env.refines_add_left with (v2:=xs i); auto.
          take (sem_var _ _ _) and specialize (it i); auto.
      + (* EqApp - no reset *)
        take (hd_error xs = Some _) and rewrite it.
        take (sem_lexps _ _ _ _) and rename it into Se; specialize (Se i).
        rewrite sem_lexps_instant_switch_env with (R':=env') in Se;
          [|now solve_switch_env_obligation].
        apply interp_lexps_instant_correct in Se as ->.
        take (sub_inst_n x M Mx) and rename it into MMx.
        simpl. setoid_rewrite (MMx i); simpl.
        take (msem_node _ _ _ _ _ _) and specialize (Hf__node _ _ _ _ _ it).
        setoid_rewrite (orel_obind2_head Hf__node); [simpl|solve_orel_obinds].
        take (sem_vars H xs xss) and specialize (it i).
        apply sem_vars_updates_env with (2:=Henv2) (3:=Inx) in it
          as (env'' & -> & Henv1'' & Henv''2 & Ix); simpl.
        2:{ intros y Iy Ny. rewrite Forall_forall in ND3. apply ND3 in Iy.
            now apply Env.dom_use with (1:=Inx) in Ny. }
        do 2 eexists. split; [reflexivity|]. repeat split; eauto.
        * transitivity (instances N'); auto.
          apply Env.refines_add_right; auto.
          intro IxN. apply Env.dom_use with (1:=Iin) in IxN.
          simpl in ND3; rewrite Forall_forall in ND3.
          take (hd_error xs = Some x) and apply hd_error_In, ND3 in it.
          apply it. apply fst_InMembers, gather_insts_Is_defined_in,
                    Is_defined_in_vars_defined in IxN.
          apply in_or_app; auto.
        * apply Env.refines_add_left with (v2:=Mx' i); auto.
          take (sub_inst_n x M' Mx') and apply it. reflexivity.
        * destruct xs; take (hd_error _ = Some _) and inv it.
          now apply Env.dom_add_cons.
        * transitivity env'; auto.
        * setoid_rewrite Permutation_app_assoc.
          now setoid_rewrite Permutation_app_comm.
      + (* EqApp - reset *)
        take (hd_error xs = Some _) and rewrite it.
        (* handle reset signal *)
        take (sem_var H y ys) and rename it into Sy; specialize (Sy i).
        apply sem_var_instant_switch_env with (R':=env') in Sy;
          [|now solve_switch_env_obligation].
        apply interp_var_instant_correct in Sy as ->.
        take (msem_reset _ _ _ _ _ _ _) and inversion_clear it as [?????? MSr].
        specialize (MSr (count rs i)) as (Mk & Mk' & Snr & SMk & SMk').
        take (sub_inst_n x M Mx) and rename it into Msub.
        take (reset_of ys rs) and rename it into Ryr.
        pose proof (msem_node_maybe_reset OG Msub SMk Ryr Snr) as Mmr.
        setoid_rewrite (orel_obind_head Mmr); [clear Mmr|now solve_orel_obinds; subst].
        (* adapt EqApp-no-reset case *)
        take (sem_lexps _ _ _ _) and rename it into Se; specialize (Se i).
        rewrite sem_lexps_instant_switch_env with (R':=env') in Se;
          [|now solve_switch_env_obligation].
        apply interp_lexps_instant_correct in Se as ->.
        take (msem_node _ _ _ _ _ _) and apply Hf__node in it.
        repeat rewrite (mask_transparent _ _ _ _ _ eq_refl) in it.
        simpl; setoid_rewrite (orel_obind2_head it);
          [clear it; simpl|solve_orel_obinds].
        take (sem_vars H xs xss) and specialize (it i).
        apply sem_vars_updates_env with (2:=Henv2) (3:=Inx) in it
          as (env'' & -> & Henv1'' & Henv''2 & Ix).
        2:{ intros z Iz Nz. rewrite Forall_forall in ND3. apply ND3 in Iz.
            now apply Env.dom_use with (1:=Inx) in Nz. }
        simpl. do 2 eexists. split; [reflexivity|]. repeat split; eauto.
        * transitivity (instances N'); auto.
          apply Env.refines_add_right; auto.
          intro IxN. apply Env.dom_use with (1:=Iin) in IxN.
          simpl in ND3; rewrite Forall_forall in ND3.
          take (hd_error xs = Some x) and apply hd_error_In, ND3 in it.
          apply it. apply fst_InMembers, gather_insts_Is_defined_in,
                    Is_defined_in_vars_defined in IxN.
          apply in_or_app; auto.
        * apply Env.refines_add_left with (v2:=Mk' i); auto; [|reflexivity].
          specialize (SMk' i eq_refl) as <-.
          take (sub_inst_n x M' Mx') and apply it.
        * destruct xs; take (hd_error _ = Some _) and inv it.
          now apply Env.dom_add_cons.
        * transitivity env'; auto.
        * setoid_rewrite Permutation_app_assoc.
          now setoid_rewrite Permutation_app_comm.
      + (* EqFby *)
        take (sem_laexp _ _ _ _ _) and rename it into Se.
        take (mfby _ _ _ _ _ _) and destruct it as (M1 & M2 & M3).
        specialize (M3 i). destruct (find_val x (M i)) eqn:FM; [|contradiction].
        specialize (Se i); simpl in Se.
        inv Se; take (sem_lexp_instant _ _ _ _) and rename it into Se;
          take (sem_clock_instant _ _ _ _) and rename it into Sck;
          rewrite sem_clock_instant_switch_env with (R':=env') in Sck;
          [apply interp_clock_instant_correct in Sck as ->
          |now solve_switch_env_obligation]; simpl.
        * (* present *)
          take (present _ = _) and rewrite <-it in M3; destruct M3 as (Fv & Hv).
          { do 2 eexists. split; [reflexivity|].
            repeat split; eauto using Env.dom_add_cons.
            * apply Env.refines_add_right; auto. intro Ix.
              rewrite Henv1, (Env.dom_use Inx) in Ix.
              inversion_clear ND3 as [|?? Nx]; auto.
            * apply Env.refines_add_left with (v2:=xs i); auto.
              take (sem_var _ _ _) and specialize (it i); auto. }
        * (* absent *)
          take (absent = _) and rewrite <-it in M3; destruct M3 as (Fv & Hv).
          { do 2 eexists. split; [reflexivity|].
            repeat split; eauto using Env.dom_add_cons.
            * apply Env.refines_add_right; auto. intro Ix.
              rewrite Henv1, (Env.dom_use Inx) in Ix.
              inversion_clear ND3 as [|?? Nx]; auto.
            * apply Env.refines_add_left with (v2:=xs i); auto.
              take (sem_var _ _ _) and specialize (it i); auto. }
  Qed.

  Lemma msem_equation_next_from_equation:
    forall G bk H M M' i eqs env N,
      env ⊑ (restr_hist H i) ->
      (forall x, Exists (Is_free_in_eq x) eqs -> Env.In x env) ->
      Env.dom N.(values) nil ->
      Forall (msem_equation G bk H M M') eqs ->
      exists N', orel (equal_memory)
                 (ofold_right (next_from_equation (bk i) (M i) env) (Some N) eqs)
                 (Some N')
            /\ N.(values) ⊑ N'.(values)
            /\ N'.(values) ⊑ (M' i).(values)
            /\ Env.dom N'.(values) (gather_mems eqs)
            /\ N'.(instances) = N.(instances).
  Proof.
    induction eqs as [|equ eqs IH]; intros env N.
    - simpl; exists N; intuition auto.
      take (Env.dom _ nil) and apply Env.dom_equal_empty in it as ->; auto.
    - intros Eenv Denv DN Meqs. apply Forall_cons2 in Meqs as (Meq & Meqs).
      assert (forall x, Exists (Is_free_in_eq x) eqs -> Env.In x env) as Denv'
          by (intros x Dx; apply Denv; now constructor 2).
      specialize (IH _ _ Eenv Denv' DN Meqs) as (N' & Hfold & LN' & UN' & DN' & IN').
      rewrite ofold_right_altdef; simpl.
      setoid_rewrite Hfold; simpl.
      inv Meq; simpl; try (now eexists; split; [reflexivity|]; repeat split; auto).
      (* EqFby *)
      take (sem_laexp _ _ _ _ _) and rename it into Sle.
      specialize (Sle i); simpl in Sle.
      apply sem_laexp_instant_switch_env with (R':=env) in Sle.
      2:{ intros z FRz.
          symmetry; apply orel_eq, Env.refines_orel_find; destruct FRz; auto. }
      apply interp_laexp_instant_correct in Sle as ->; simpl.
      take (mfby _ _ _ _ _ _) and destruct it as (MF0 & MF1 & MF2).
      specialize (MF2 i).
      destruct (find_val x (M i)) eqn:Mix; try contradiction.
      apply Env.dom_equal_empty in DN; setoid_rewrite DN.
      destruct (ls i); destruct MF2 as (MF2 & MF3);
        unfold add_val; unfold find_val in MF2; simpl.
      + (* absent *)
        eexists; split; [reflexivity|]; repeat split; auto; simpl.
        * setoid_rewrite UN'.
          apply Env.refines_find_add_left with (2:=MF2); auto.
        * now apply Env.dom_add_cons.
      + (* present *)
        eexists; split; [reflexivity|]; repeat split; auto; simpl.
        * setoid_rewrite UN'.
          apply Env.refines_find_add_left with (2:=MF2); auto.
        * now apply Env.dom_add_cons.
  Qed.

  Lemma wt_node_env_dom_Is_free_In:
    forall {A} G (env : Env.t A) n,
      wt_node G n ->
      Env.dom env (map fst (n.(n_in) ++ n.(n_vars) ++ n.(n_out))) ->
      forall x, Exists (Is_free_in_eq x) n.(n_eqs) -> Env.In x env.
  Proof.
    intros * WTG Denv x FRx.
    apply Exists_exists in FRx as (eq & Ieq & FRx).
    eapply Forall_forall in WTG; eauto. clear Ieq.
    apply Env.dom_use with (x0:=x) in Denv as ->.
    apply fst_InMembers.
    inv WTG; inv FRx; try take (_ \/ _) and destruct it; try discriminate.
    - eauto using Is_free_in_wt_caexp.
    - eauto using Is_free_in_wt_laexps.
    - eauto using Is_free_in_wt_laexps.
    - take (Some _ = Some _) and inv it; eauto using idty_InMembers.
    - eauto using Is_free_in_wt_laexp.
  Qed.

  (* NB: We use the typing predicate only to ensure that each free variable in
         a defining expression is defined by an equation in the same node. *)
  Lemma interp_node_correct:
    forall G f xss M M' yss,
      Ordered_nodes G ->
      Forall Causal G ->
      wt_global G ->
      msem_node G f xss M M' yss
      <-> (forall n, orel (equal_memory * eq)
                   (interp_node G f (xss n) (clock_of_instant (xss n)) (M n))
                   (Some (M' n, yss n))).
  Proof.
    induction G as [|n G IHG].
    { split. now inversion 1; take (find_node f [] = _) and inversion it.
      intro HH. specialize (HH 0). inv HH. }
    intros f xss M M' yss OnG CnG WTnG.
    split; [intros Msem|intros Hinterp].
    - (* msem_node -> interp_node *)
      intro i. simpl.
      destruct (ident_eq_dec n.(n_name) f).
      2:{ apply msem_node_cons with (1:=OnG) in Msem; auto.
          take (n.(n_name) <> f) and apply not_equiv_decb_equiv in it.
          setoid_rewrite it. inv OnG. inv WTnG; inv CnG. rewrite IHG in Msem; auto. }
      take (n.(n_name) = f) and setoid_rewrite (proj2 (equiv_decb_equiv _ _) it).
      inversion_clear Msem as [????????? Fn SVi SVo SCV Meqs MC MC'].
      simpl in Fn. take (n.(n_name) = f) and apply ident_eqb_eq in it.
      setoid_rewrite it in Fn; inv Fn.
      apply <- msem_equations_cons in Meqs; auto.
      2:now intro Ini; inversion OnG as [|??? Hn]; apply Hn in Ini as [??]; auto.
      specialize (SVi i).
      eapply sem_vars_updates_env with (2:=Env.refines_empty eq (restr_hist H i))
        (3:=Env.dom_empty) in SVi as (env' & Hupd & Lenv' & Uenv' & Denv').
      2:now setoid_rewrite Env.Props.P.F.empty_in_iff.
      setoid_rewrite Hupd; clear Hupd; simpl.
      simpl in Denv'. inversion_clear OnG as [|??? Hn].
      pose (Meqs':=Meqs);
      apply msem_equation_interp_equation with (f__node:=interp_node G)
        (N:=empty_memory _) (6:=Uenv') (7:=Denv') in Meqs'
        as (env'' & N' & Hinterp & I1 & I2 & DN' & VN' & Lenv'' & Uenv'' & Denv'');
      simpl; auto.
      + setoid_rewrite (orel_obind2_head Hinterp).
        2:now solve_orel_obinds; apply orel_omap;
          take (Env.Equal _ _) and setoid_rewrite it.
        eapply msem_equation_next_from_equation with (1:=Uenv'') (N:=N') in Meqs
          as (N'' & Hnext & LN'' & UN'' & DN'' & IN''); simpl; auto.
        2:{ intros; inv WTnG. eapply wt_node_env_dom_Is_free_In; eauto.
            now rewrite n_defd, Permutation_app_comm, <-map_app in Denv''. }
        setoid_rewrite (orel_obind_head Hnext); [simpl|now solve_orel_obinds].
        specialize (SVo i).
         destruct (Env.omap_find (map fst n0.(n_out)) env'') as (rvs & Homap & HH).
        { apply Forall_forall; intros x Ix.
          apply Env.dom_use with (1:=Denv''), in_or_app; left.
          rewrite n_defd, map_app; apply in_or_app; auto. }
        setoid_rewrite Homap; simpl.
        constructor; split; compute.
        * (* N'' ≋ M' i *)
          { rewrite <-IN'' in I2, DN'.
            revert UN'' DN'' MC' I2 DN'; clear; intros VN DVN MC IN DIN.
            specialize (MC i). destruct MC as (MC1 & MC2). split.
            - apply Env.Equal_Equiv, Env.Equiv_refines; split; auto.
              intros x v Fx; exists v; split; auto.
              apply Env.dom_use with (x0:=x) in DVN.
              apply orel_eq. setoid_rewrite (Env.refines_orel_find _ _ _ _ VN).
              now rewrite Fx.
              apply DVN, MC2. now setoid_rewrite Fx.
            - apply Env.Equiv_refines. now typeclasses eauto. split; auto.
              intros x v Fx.
              apply Env.dom_use with (x0:=x) in DIN.
              apply Env.refines_orel_find with (x0:=x) in IN; auto.
              rewrite Fx in IN; apply Env.orel_find_Some in IN as (v' & Evv & Fx');
                symmetry in Evv; eauto.
              apply DIN, fst_InMembers, MC1. now setoid_rewrite Fx. }
        * (* rvs = yss i *)
          revert HH SVo Uenv'' Denv''; clear; intros FArvs SV Renv'' Denv''.
          unfold sem_vars_instant in SV.
          apply Forall2_swap_args, Forall2_trans_ex with (2:=SV) in FArvs.
          apply Forall2_eq, Forall2_impl_In with (2:=FArvs).
          intros rv ys Irv Iys (o & Io & Fo & So).
          apply Renv'' in Fo as (rv' & Erv & Fo); congruence.
        * rewrite VN'; simpl; auto.
      + typeclasses eauto.
      + intros; apply IHG; inv WTnG; inv CnG; auto.
      + now inv CnG.
      + rewrite n_defd, <-map_app, <-fst_NoDupMembers, Permutation_app_comm.
        apply n_nodup.

    - (* interp_node -> msem_node *)
      admit.

  Admitted.

  (*
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
      Forall Causal G ->
      wt_global G ->
      wc_global G ->
      (* TODO: well_typed xs /\ well_clocked xs *)
      (* TODO: Ops_defined in nodes, recursively *)
      mem_inv N ->
      exists N' ys,
        interp_node G f xs base N = Some (N', ys).
  Proof.
  Admitted.
  *)

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
