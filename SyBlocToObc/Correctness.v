Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.Clocks.
Require Import Velus.RMemory.

Require Import Velus.NLustre.NLExprSyntax.
Require Import Velus.NLustre.Stream.
Require Import Velus.NLustre.NLExprSemantics.
Require Import Velus.SyBloc.SBSyntax.
Require Import Velus.SyBloc.SBSemantics.

Require Import Velus.Obc.ObcSyntax.
Require Import Velus.Obc.ObcSemantics.

Require Import Velus.NLustre.NLSyntax.
Require Export Velus.NLustre.IsFree.

Require Import Velus.SyBlocToObc.Translation.

Require Import List.
Import List.ListNotations.
Require Import Setoid.

(* Open Scope positive. *)
Open Scope nat.
Open Scope list.

Module Type CORRECTNESS
       (Import Ids     : IDS)
       (Import Op      : OPERATORS)
       (Import OpAux   : OPERATORS_AUX       Op)
       (Import Clks    : CLOCKS          Ids)
       (Import ExprSyn : NLEXPRSYNTAX        Op)
       (SynNL          : NLSYNTAX        Ids Op       Clks ExprSyn)
       (Import SynSB   : SBSYNTAX        Ids Op       Clks ExprSyn)
       (Import Str     : STREAM              Op OpAux)
       (Import ExprSem : NLEXPRSEMANTICS Ids Op OpAux Clks ExprSyn              Str)
       (Import SemSB   : SBSEMANTICS     Ids Op OpAux Clks ExprSyn SynSB        Str ExprSem)
       (Import SynObc  : OBCSYNTAX       Ids Op OpAux)
       (Import SemObc  : OBCSEMANTICS    Ids Op OpAux                    SynObc)
       (Import Trans   : TRANSLATION     Ids Op OpAux Clks ExprSyn SynSB SynObc)
       (Import IsF     : ISFREE          Ids Op       Clks ExprSyn SynNL).

  Ltac cases :=
    repeat match goal with
           | H: context [ match negb ?x with _ => _ end ] |- _ => destruct x; simpl; try solve [inv H; auto]
           | H: context [ match ?x with _ => _ end ] |- _ => destruct x; try solve [inv H; auto]
           | |- context [ match negb ?x with _ => _ end ] => destruct x; simpl
           | |- context [ match ?x with _ => _ end ] => destruct x
           end; auto.

  (* Section MemoryCorres. *)

  (*   Variable P: SynSB.program. *)

  (*   Inductive Memory_Corres: ident -> state -> menv -> Prop := *)
  (*     MemC: *)
  (*       forall b S me bl P', *)
  (*         find_block b P = Some (bl, P') -> *)
  (*         Forall (Memory_Corres_eq S me) bl.(b_eqs) -> *)
  (*         Memory_Corres b S me *)

  (*   with Memory_Corres_eq: state -> menv -> equation -> Prop := *)
  (*        | MemC_EqDef: *)
  (*            forall S me x ck e, *)
  (*              Memory_Corres_eq S me (EqDef x ck e) *)
  (*        | MemC_EqNext: *)
  (*            forall S me x ck e, *)
  (*              (forall v, find_val x S = Some v -> *)
  (*                    find_val x me = Some v) -> *)
  (*              Memory_Corres_eq S me (EqNext x ck e) *)
  (*        | MemC_EqReset: *)
  (*            forall S me s ck b, *)
  (*              (forall Ss, sub_inst s S Ss -> *)
  (*                     exists me', sub_inst s me me' *)
  (*                            /\ me' ≋ Ss) -> *)
  (*              Memory_Corres_eq S me (EqReset s ck b) *)
  (*        | MemC_EqCall: *)
  (*          forall S me s xs ck rst b es, *)
  (*            (forall Ss, sub_inst s S Ss -> *)
  (*                   exists me', sub_inst s me me' *)
  (*                          /\ Memory_Corres b Ss me') -> *)
  (*            Memory_Corres_eq S me (EqCall s xs ck rst b es). *)

  (*   Definition Memory_Corres_eqs (S: state) (me: menv) (eqs: list equation) := *)
  (*     Forall (Memory_Corres_eq S me) eqs. *)

  (*   Section MemoryCorresMult. *)

  (*     Variable P_block: ident -> state -> menv -> Prop. *)
  (*     Variable P_equation: state -> menv -> equation -> Prop. *)

  (*     Hypothesis EqDef_case: *)
  (*       forall S me x ck e, *)
  (*         P_equation S me (EqDef x ck e). *)

  (*     Hypothesis EqNext_case: *)
  (*       forall S me x ck e, *)
  (*         (forall v, find_val x S = Some v -> *)
  (*               find_val x me = Some v) -> *)
  (*         P_equation S me (EqNext x ck e). *)

  (*     Hypothesis EqReset_case: *)
  (*       forall S me s ck b me', *)
  (*         sub_inst s me me' -> *)
  (*         initial_state P b me' -> *)
  (*         P_equation S me (EqReset s ck b). *)

  (*     Hypothesis EqCall_case: *)
  (*       forall S me s xs ck rst b es, *)
  (*         (forall Ss, sub_inst s S Ss -> *)
  (*                exists me', sub_inst s me me' *)
  (*                       /\ Memory_Corres b Ss me' *)
  (*                       /\ P_block b Ss me') -> *)
  (*         P_equation S me (EqCall s xs ck rst b es). *)

  (*     Hypothesis MemC_case: *)
  (*       forall b S me bl P', *)
  (*         find_block b P = Some (bl, P') -> *)
  (*         Forall (Memory_Corres_eq S me) bl.(b_eqs) -> *)
  (*         Forall (P_equation S me) bl.(b_eqs) -> *)
  (*         P_block b S me. *)

  (*     Fixpoint Memory_Corres_mult *)
  (*              (b: ident) (S: state) (me: menv) *)
  (*              (Hmc: Memory_Corres b S me): *)
  (*       P_block b S me *)
  (*     with Memory_Corres_eq_mult *)
  (*            (S: state) (me: menv) (eq: equation) *)
  (*            (Hmceq: Memory_Corres_eq S me eq): *)
  (*            P_equation S me eq. *)
  (*     Proof. *)
  (*       - destruct Hmc. eauto. *)
  (*         eapply MemC_case; eauto. *)
  (*         match goal with H: Forall _ _ |- _ => induction H; auto end. *)
  (*       - destruct Hmceq as [| | |???????? Spec]; eauto. *)
  (*         apply EqCall_case. *)
  (*         intros ** Sub; apply Spec in Sub as (?&?&?); eauto. *)
  (*     Qed. *)

  (*   End MemoryCorresMult. *)

  (* End MemoryCorres. *)


  Definition equiv_env (in_domain: ident -> Prop) (R: env) (mems: PS.t) (me: menv) (ve: venv) : Prop :=
    forall x c,
      in_domain x ->
      sem_var_instant R x (present c) ->
      if PS.mem x mems
      then find_val x me = Some c
      else Env.find x ve = Some c.

  Lemma equiv_env_map:
    forall (in_dom1 in_dom2: ident -> Prop) R mems me ve,
      (forall x, in_dom2 x -> in_dom1 x) ->
      equiv_env in_dom1 R mems me ve ->
      equiv_env in_dom2 R mems me ve.
  Proof.
    unfold equiv_env; intros ** Eq ????; apply Eq; auto.
  Qed.

  Ltac weaken_equiv_env_with tac :=
    match goal with
      H: equiv_env ?in_dom1 ?R ?mems ?me ?ve
      |- equiv_env ?in_dom2 ?R ?mems ?me ?ve =>
      eapply equiv_env_map; [|exact H]; tac
    end.

  Tactic Notation "weaken_equiv_env" "with" tactic(tac) :=
    weaken_equiv_env_with tac.

  Tactic Notation "weaken_equiv_env" :=
    weaken_equiv_env with constructor (now auto).

  Hint Extern 4 (equiv_env _ _ _ _ _) => weaken_equiv_env.

  Ltac split_env_assumption :=
    match goal with
    | Equiv: context Is_free_in_lexp [_],
             Hvar: sem_var_instant _ _ _ |- _ =>
      apply Equiv in Hvar; [|solve [constructor; auto]]
    | Equiv: context Is_free_in_clock [_],
             Hvar: sem_var_instant _ _ _ |- _ =>
      apply Equiv in Hvar; [|solve [constructor; auto]]
    end.

  Inductive Is_defined_in_eq: ident -> equation -> Prop :=
  | DefEqDef:
      forall x ck e,
        Is_defined_in_eq x (EqDef x ck e)
  | DefEqNext:
      forall x ck e,
        Is_defined_in_eq x (EqNext x ck e)
  | DefEqCall:
      forall x s xs ck rst b es,
        In x xs ->
        Is_defined_in_eq x (EqCall s xs ck rst b es).

  Definition Is_defined_in_eqs (x: ident) (eqs: list equation) : Prop :=
    Exists (Is_defined_in_eq x) eqs.

  Lemma not_Is_defined_in_eq_EqDef:
    forall y x ck e,
      ~ Is_defined_in_eq y (EqDef x ck e) -> x <> y.
  Proof.
    intros ** NIsDef E; subst; apply NIsDef; auto using Is_defined_in_eq.
  Qed.

  Lemma not_Is_defined_in_eq_EqNext:
    forall y x ck e,
      ~ Is_defined_in_eq y (EqNext x ck e) -> x <> y.
  Proof.
    intros ** NIsDef E; subst; apply NIsDef; auto using Is_defined_in_eq.
  Qed.

  Lemma not_Is_defined_in_eq_EqCall:
    forall x s xs ck rst b es,
      ~ Is_defined_in_eq x (EqCall s xs ck rst b es) -> ~ In x xs.
  Proof.
    intros ** NIsDef Hin; apply NIsDef; auto using Is_defined_in_eq.
  Qed.

  Lemma not_Is_defined_in_cons:
    forall x eq eqs,
      ~ Is_defined_in_eqs x (eq :: eqs)
      <-> ~ Is_defined_in_eq x eq /\ ~ Is_defined_in_eqs x eqs.
  Proof.
    split.
    - intro Hndef; split; intro His_def;
        eapply Hndef; constructor (assumption).
    - intros [Hdef_eq Hdef_eqs] Hdef_all.
      inv Hdef_all; eauto.
  Qed.

  Inductive Is_variable_in_eq: ident -> equation -> Prop :=
  | VarEqDef:
      forall x ck e,
        Is_variable_in_eq x (EqDef x ck e)
  | VarEqCall:
      forall x s xs ck rst b es,
        In x xs ->
        Is_variable_in_eq x (EqCall s xs ck rst b es).

  Definition Is_variable_in_eqs (x: ident) (eqs: list equation) : Prop :=
    Exists (Is_variable_in_eq x) eqs.

  Inductive Is_state_in_eq: ident -> nat -> equation -> Prop :=
  | StateEqReset:
      forall s ck b,
        Is_state_in_eq s 0 (EqReset s ck b)
  | StateEqCall:
      forall s xs ck rst b es,
        Is_state_in_eq s 1 (EqCall s xs ck rst b es).

  Inductive Is_free_in_eq: ident -> equation -> Prop :=
  | FreeEqDef:
      forall x ck e y,
        Is_free_in_caexp y ck e ->
        Is_free_in_eq y (EqDef x ck e)
  | FreeEqNext:
      forall x ck e y,
        Is_free_in_laexp y ck e ->
        Is_free_in_eq y (EqNext x ck e)
  | FreeEqReset:
      forall s ck b x,
        Is_free_in_clock x ck ->
        Is_free_in_eq x (EqReset s ck b)
  | FreeEqCall:
      forall s x ck rst b es y,
        Is_free_in_laexps y ck es ->
        Is_free_in_eq y (EqCall s x ck rst b es).

  Inductive Is_well_sch (inputs: list ident) (mems: PS.t): list equation -> Prop :=
  | WSchNil:
      Is_well_sch inputs mems []
  | WSchEq:
      forall eq eqs,
        Is_well_sch inputs mems eqs ->
        (forall x,
            Is_free_in_eq x eq ->
            if PS.mem x mems
            then ~ Is_defined_in_eqs x eqs
            else Is_variable_in_eqs x eqs \/ In x inputs) ->
        (forall x, Is_defined_in_eq x eq -> ~ Is_defined_in_eqs x eqs) ->
        (forall s k,
            Is_state_in_eq s k eq ->
            Forall (fun eq => forall k', Is_state_in_eq s k' eq -> k' < k) eqs) ->
        Is_well_sch inputs mems (eq :: eqs).

  Definition Is_state_in_eqs (s: ident) (k: nat) (eqs: list equation) : Prop :=
    Exists (Is_state_in_eq s k) eqs.

  Definition Reset_in (s: ident) := Is_state_in_eqs s 0.

  Definition Step_in (s: ident) := Is_state_in_eqs s 1.

  Inductive Is_last_in_eq: ident -> equation -> Prop :=
    LastEqNext:
      forall x ck e,
        Is_last_in_eq x (EqNext x ck e).

  Definition Is_last_in_eqs (x: ident) (eqs: list equation) : Prop :=
    Exists (Is_last_in_eq x) eqs.

  Lemma Is_last_in_eq_defined_not_variable:
    forall x eq,
      Is_last_in_eq x eq <-> Is_defined_in_eq x eq /\ ~ Is_variable_in_eq x eq.
  Proof.
    destruct eq; split; inversion_clear 1;
      try match goal with H: Is_defined_in_eq _ _ |- _ => inv H end;
      try match goal with H: ~ Is_variable_in_eq _ _ |- _ => exfalso; apply H; constructor end;
      eauto using Is_last_in_eq.
    split; eauto using Is_defined_in_eq.
    inversion 1.
  Qed.

  Lemma Is_last_in_eqs_defined_not_variable:
    forall x eqs,
      Is_last_in_eqs x eqs
      <-> Exists (fun eq => Is_defined_in_eq x eq /\ ~ Is_variable_in_eq x eq) eqs.
  Proof.
    unfold Is_last_in_eqs.
    intros; rewrite 2 Exists_exists; split.
    - intros (?&?& Last); apply Is_last_in_eq_defined_not_variable in Last as ();
        eauto.
    - intros (?&?& DefNVar); apply Is_last_in_eq_defined_not_variable in DefNVar;
        eauto.
  Qed.

  Definition Memory_Corres
             (eqs: list equation)
             (S: state) (I: transient_states) (S': state)
             (me: menv) : Prop :=
    (forall x,
        (Is_last_in_eqs x eqs ->
         forall v,
           find_val x S' = Some v ->
           find_val x me = Some v)
        /\ (~ Is_last_in_eqs x eqs ->
           forall v,
             find_val x S = Some v ->
             find_val x me = Some v))
    /\
    (forall s,
        (~ Step_in s eqs /\ ~ Reset_in s eqs ->
         forall Ss,
           sub_inst s S Ss ->
           exists me',
             sub_inst s me me'
             /\ me' ≋ Ss)
        /\ (~ Step_in s eqs /\ Reset_in s eqs ->
           forall Is,
             Env.find s I = Some Is ->
             exists me',
               sub_inst s me me'
               /\ me' ≋ Is)
        /\ (Step_in s eqs ->
           forall Ss',
             sub_inst s S' Ss' ->
             exists me',
               sub_inst s me me'
               /\ me' ≋ Ss')).

  (* Lemma Memory_Corres_eqs_add_val: *)
  (*   forall P S me x v eqs, *)
  (*     find_val x S = Some v -> *)
  (*     Memory_Corres_eqs P S me eqs -> *)
  (*     Memory_Corres_eqs P S (add_val x v me) eqs. *)
  (* Proof. *)
  (*   unfold Memory_Corres_eqs. *)
  (*   induction eqs as [|eq]; auto. *)
  (*   intros Find; inversion_clear 1 as [|?? Corres]. *)
  (*   constructor; auto. *)
  (*   destruct eq; inv Corres; econstructor; eauto. *)
  (*   intros ** Find'. *)
  (*   destruct (ident_eq_dec i x). *)
  (*   - subst; rewrite find_val_gss; congruence. *)
  (*   - rewrite find_val_gso; auto. *)
  (* Qed. *)

  Inductive Is_present_in (mems: PS.t) (me: menv) (ve: venv): clock -> Prop :=
  | IsCbase:
      Is_present_in mems me ve Cbase
  | IsCon:
      forall ck x v b,
        Is_present_in mems me ve ck ->
        exp_eval me ve (tovar mems (x, bool_type)) v ->
        val_to_bool v = Some b ->
        Is_present_in mems me ve (Con ck x b).

  Inductive Is_absent_in (mems: PS.t) (me: menv) (ve: venv): clock -> Prop :=
  | IsAbs1:
      forall ck x v,
        Is_absent_in mems me ve ck ->
        Is_absent_in mems me ve (Con ck x v)
  | IsAbs2:
      forall ck x v b,
        Is_present_in mems me ve ck ->
        exp_eval me ve (tovar mems (x, bool_type)) v ->
        val_to_bool v = Some b ->
        Is_absent_in mems me ve (Con ck x (negb b)).

  Hint Constructors Is_present_in Is_absent_in.

  Ltac chase_skip :=
    match goal with
      H: stmt_eval _ _ _ Skip _ |- _ => inv H
    end.

  Lemma stmt_eval_Control_fwd:
    forall prog me ve mems ck s me' ve',
      stmt_eval prog me ve (Control mems ck s) (me', ve') ->
      (Is_present_in mems me ve ck
       /\ stmt_eval prog me ve s (me', ve'))
      \/
      (Is_absent_in mems me ve ck
       /\ me' = me /\ ve' = ve).
  Proof.
    intros ** StEval.
    revert dependent s.
    induction ck; intuition.
    simpl in *; cases; apply IHck in StEval as [[Hp Hs]|[Hp [Hmenv Henv]]];
      intuition; inv Hs.
    - cases; intuition; eauto.
      chase_skip.
      assert (true = negb false) as -> by reflexivity;
        eauto.
    - cases; intuition; eauto.
      chase_skip.
      assert (false = negb true) as -> by reflexivity;
        eauto.
  Qed.

  (* Conjunction required for simultaneous induction. *)
  Fact stmt_eval_Control:
    forall prog mems me ve ck s,
      (Is_absent_in mems me ve ck ->
       stmt_eval prog me ve (Control mems ck s) (me, ve))
      /\
      (forall me' ve',
          Is_present_in mems me ve ck ->
          stmt_eval prog me ve s (me', ve') ->
          stmt_eval prog me ve (Control mems ck s) (me', ve')).
  Proof.
    Hint Constructors stmt_eval.
    intros; revert s; induction ck; split; auto.
    - inversion 1.
    - inversion_clear 1 as [??? Hp|???? Hp]; simpl;
        cases; apply IHck with (1 := Hp); eauto.
    - inversion_clear 1 as [|???? Hp]; simpl; intros;
        cases; apply IHck with (1 := Hp); eauto.
  Qed.

  (** If the clock is absent, then the controlled statement evaluates as
  a [Skip].  *)

  Lemma stmt_eval_Control_absent:
    forall prog mems me ve ck s,
      Is_absent_in mems me ve ck ->
      stmt_eval prog me ve (Control mems ck s) (me, ve).
  Proof. apply stmt_eval_Control. Qed.

  (** If the clock is present, then the controlled statement evaluates
  as the underlying one.  *)

  Lemma stmt_eval_Control_present:
    forall prog mems me ve ck s me' ve',
      Is_present_in mems me ve ck ->
      stmt_eval prog me ve s (me', ve') ->
      stmt_eval prog me ve (Control mems ck s) (me', ve').
  Proof. apply stmt_eval_Control. Qed.

  (* Lemma stmt_call_eval_cons: *)
  (*   forall prog c' c me f vs me' rvs, *)
  (*     c_name c <> c' -> *)
  (*     (stmt_call_eval (c :: prog) me c' f vs me' rvs *)
  (*      <-> stmt_call_eval prog me c' f vs me' rvs). *)
  (* Proof. *)
  (*   intros ** Neq; rewrite <-ident_eqb_neq in Neq; split; intros Sem. *)
  (*   - inversion_clear Sem as [??????????? Find]. *)
  (*     simpl in Find; rewrite Neq in Find; eauto using stmt_call_eval. *)
  (*   - inv Sem; econstructor; eauto. *)
  (*     simpl; rewrite Neq; auto. *)
  (* Qed. *)

  Section Expr.

    Variable (mems: PS.t).

    Lemma typeof_correct:
      forall e,
        typeof (translate_lexp mems e) = ExprSyn.typeof e.
    Proof.
      induction e; intros; simpl; auto; cases.
    Qed.

    Variable (R: env).
    Variable (me: menv) (ve: venv).

    Lemma lexp_correct:
      forall e c,
        sem_lexp_instant true R e (present c) ->
        equiv_env (fun x => Is_free_in_lexp x e) R mems me ve ->
        exp_eval me ve (translate_lexp mems e) c.
    Proof.
      induction e; inversion_clear 1; simpl; intros; auto.
      - constructor; congruence.
      - split_env_assumption; cases; eauto using exp_eval.
      - econstructor; eauto; now rewrite typeof_correct.
      - econstructor; eauto; now rewrite 2 typeof_correct.
    Qed.
    Hint Resolve lexp_correct.

    Corollary lexps_correct:
      forall es cs,
        sem_lexps_instant true R es (map present cs) ->
        equiv_env (fun x => Exists (Is_free_in_lexp x) es) R mems me ve ->
        Forall2 (exp_eval me ve) (map (translate_lexp mems) es) cs.
    Proof.
      setoid_rewrite Forall2_map_1; setoid_rewrite Forall2_map_2;
        intros; eapply Forall2_impl_In; eauto.
      intros; apply lexp_correct; auto.
      weaken_equiv_env with (setoid_rewrite Exists_exists; eauto).
    Qed.
    Hint Resolve lexps_correct.

    Lemma cexp_correct:
      forall e c prog x,
        sem_cexp_instant true R e (present c) ->
        equiv_env (fun x => Is_free_in_cexp x e) R mems me ve ->
        stmt_eval prog me ve (translate_cexp mems x e) (me, Env.add x c ve).
    Proof.
      induction e;
        inversion 1 as [???? Hvar|???? Hvar| | | |];
        subst; simpl; intros; eauto using stmt_eval.
      - split_env_assumption.
        econstructor; eauto.
        + unfold bool_var, tovar; cases; eauto using exp_eval.
        + apply val_to_bool_true.
        + simpl; auto.
      - split_env_assumption.
        econstructor; eauto.
        + unfold bool_var, tovar; cases; eauto using exp_eval.
        + apply val_to_bool_false.
        + simpl; auto.
      - econstructor; eauto; cases.
    Qed.
    Hint Resolve cexp_correct.

  End Expr.

  Lemma clock_correct_true:
    forall base R mems me ve ck,
      equiv_env (fun x => Is_free_in_clock x ck) R mems me ve ->
      sem_clock_instant base R ck true ->
      Is_present_in mems me ve ck.
  Proof.
    intros until ve.
    induction ck; eauto.
    inversion_clear 2; subst.
    econstructor; eauto.
    unfold tovar; split_env_assumption.
    cases; eauto using exp_eval.
  Qed.

  Lemma clock_correct_false:
    forall R mems me ve ck,
      equiv_env (fun x => Is_free_in_clock x ck) R mems me ve ->
      sem_clock_instant true R ck false ->
      Is_absent_in mems me ve ck.
  Proof.
    intros until ve.
    induction ck as [|?? x]; [now inversion 2|].
    intro Henv.
    inversion_clear 1; auto.
    econstructor 2; eauto.
    - eapply clock_correct_true; eauto.
      weaken_equiv_env.
    - unfold tovar; split_env_assumption.
      cases; eauto using exp_eval.
  Qed.

  Corollary stmt_eval_Control_absent':
    forall R ck prog me ve mems s,
      equiv_env (fun x => Is_free_in_clock x ck) R mems me ve ->
      sem_clock_instant true R ck false ->
      stmt_eval prog me ve (Control mems ck s) (me, ve).
  Proof.
    intros; eapply stmt_eval_Control_absent, clock_correct_false; eauto.
  Qed.

  Corollary stmt_eval_Control_present':
    forall base R ck prog me ve mems s me' ve',
      equiv_env (fun x : ident => Is_free_in_clock x ck) R mems me ve ->
      sem_clock_instant base R ck true ->
      stmt_eval prog me ve s (me', ve') ->
      stmt_eval prog me ve (Control mems ck s) (me', ve').
  Proof.
    intros; apply stmt_eval_Control_present; auto.
    eapply clock_correct_true; eauto.
  Qed.

  Lemma Comp_spec:
    forall prog s s' me ve me' ve',
      stmt_eval prog me ve (Comp s s') (me', ve') <->
      (exists me'' ve'',
          stmt_eval prog me ve s (me'', ve'')
          /\ stmt_eval prog me'' ve'' s' (me', ve')).
  Proof.
    split.
    - inversion 1; eauto.
    - intros (?&?&?&?); eauto using stmt_eval.
  Qed.

  Lemma Comp_Skip_right:
    forall prog me ve s me' ve',
      stmt_eval prog me ve (Comp s Skip) (me', ve')
      <-> stmt_eval prog me ve s (me', ve').
  Proof.
    split; eauto using stmt_eval.
    inversion_clear 1; now chase_skip.
  Qed.

  Lemma Comp_Skip_left:
    forall prog me ve s me' ve',
      stmt_eval prog me ve (Comp Skip s) (me', ve')
      <-> stmt_eval prog me ve s (me', ve').
  Proof.
    split; eauto using stmt_eval.
    inversion_clear 1; now chase_skip.
  Qed.

  Lemma reset_mems_not_in:
    forall mems prog me ve me' ve' x,
      stmt_eval prog me ve (reset_mems mems) (me', ve') ->
      ~ InMembers x mems ->
      find_val x me' = find_val x me.
  Proof.
    unfold reset_mems.
    induction mems as [|(x, c)]; intros ** StEval Notin; simpl in StEval.
    - chase_skip; auto.
    - apply NotInMembers_cons in Notin as ().
      apply stmt_eval_fold_left_lift in StEval as (?&?& Hcomp & StEval);
        rewrite Comp_Skip_left in Hcomp; inv Hcomp.
      eapply IHmems in StEval; eauto.
      rewrite find_val_gso in StEval; auto.
  Qed.

  (* Lemma InMembers_rev: *)
  (*   forall A B (l: list (A * B)) x, *)
  (*     InMembers x l <-> *)
  (*     InMembers x (rev l). *)
  (* Proof. *)
  (* Admitted. *)

  (* Lemma NoDupMembers_rev: *)
  (*   forall A B (l: list (A * B)), *)
  (*     NoDupMembers l <-> *)
  (*     NoDupMembers (rev l). *)
  (* Proof. *)
  (* Admitted. *)

  Lemma reset_mems_spec:
    forall mems prog me ve,
      NoDupMembers mems ->
      (forall x, find_val x me <> None -> InMembers x mems) ->
      exists me',
        stmt_eval prog me ve (reset_mems mems) (me', ve)
        /\ (forall x c,
              In (x, c) mems ->
              find_val x me' = Some (sem_const c))
        /\ forall x v,
            find_val x me' = Some v ->
            exists c, v = sem_const c /\ In (x, c) mems.
  Proof.
    induction mems as [|(x, c)]; inversion_clear 1; simpl; intros ** Spec.
    - exists me; intuition; eauto.
      exfalso; eapply Spec.
      apply not_None_is_Some; eauto.
    - edestruct IHl with (me := me); eauto.
      intros ** Find.
      apply Spec in Find as [E|]; auto.



    SearchAbout fold_left fold_right.
    destruct mems as [|(x, c)]; simpl; intros ** Nodup Spec.
    - exists me; intuition; eauto using stmt_eval.
      exfalso; eapply Spec.
      apply not_None_is_Some; eauto.
    - setoid_rewrite stmt_eval_fold_left_lift; setoid_rewrite Comp_Skip_left.


      assert (forall y, find_val y (add_val x (sem_const c) me) <> None -> x = y \/ InMembers y mems) as Spec'.
      { intros ** Find.
        destruct (ident_eq_dec y x); auto.
        rewrite find_val_gso in Find; auto.
      }
      clear Spec.
      inversion_clear Nodup as [|??? Notin Nodup'].
      (* SearchAbout not InMembers.  *)
      revert dependent me.
      induction mems as [|(x', c')]; simpl; intros;
        inversion_clear Nodup'; try apply NotInMembers_cons in Notin as ().
      + setoid_rewrite Comp_Skip_left.
        eexists; split; eauto using stmt_eval, exp_eval.
        split.
        * intros ** [E|?]; try contradiction.
          inv E; apply find_val_gss.
        * intros ** Find.
          assert (x = x0 \/ False) as [|]
              by (apply Spec', not_None_is_Some; eauto);
            try contradiction.
          subst; rewrite find_val_gss in Find; inv Find; eauto.
      + setoid_rewrite stmt_eval_fold_left_lift.
        edestruct IHmems with (me := add_val x' (sem_const c') (add_val x (sem_const c) me)) as (?&?&?) ; auto.
        * intros ** Find.
          destruct (ident_eq_dec y x); auto.
          rewrite find_val_gso in Find; auto.


           destruct (ident_eq_dec x0 x).
           - subst; rewrite find_val_gss in Find; inv Find; eauto.
           - rewrite find_val_gso in Find; eauto.
        econstructor; eauto.
    - exists me; intuition; eauto using stmt_eval.
      exfalso; eapply Spec.
      apply not_None_is_Some; eauto.
    - setoid_rewrite stmt_eval_fold_left_lift.
      edestruct IHmems with (me := add_val x (sem_const c) me) as (?&?&?) ; auto.
      + intros y Find.
        destruct (ident_eq_dec y x).
        * subst; rewrite find_val_gss in Find.
        Focus 2.
      eexists; split; eauto.
      + do 2 eexists; split; eauto using stmt_eval, exp_eval.
      + intros ** [E|]; auto.
        inv E.
        erewrite reset_mems_not_in; eauto.
        apply find_val_gss.
  Qed.

  Lemma reset_insts_not_in:
    forall insts prog me ve me' ve' x,
      stmt_eval prog me ve (reset_insts insts) (me', ve') ->
      ~ InMembers x insts ->
      find_inst x me' = find_inst x me.
  Proof.
    unfold reset_insts.
    induction insts as [|(x, b)]; intros ** StEval Notin; simpl in StEval.
    - chase_skip; auto.
    - apply NotInMembers_cons in Notin as ().
      apply stmt_eval_fold_left_lift in StEval as (?&?& Hcomp & StEval);
        rewrite Comp_Skip_left in Hcomp; inv Hcomp.
      eapply IHinsts in StEval; eauto.
      rewrite find_inst_gso in StEval; auto.
  Qed.

  Lemma translate_reset_eqns_spec:
    forall P me bl,
      (forall x b, In (x, b) bl.(b_blocks) -> exists bl P', find_block b P = Some (bl, P')) ->
      (forall me' b' bl' P',
          find_block b' P = Some (bl', P') ->
          exists me'',
            stmt_call_eval (translate P) me' b' reset [] me'' []
            /\ initial_state P b' me'') ->
      exists me',
        stmt_eval (translate P) me vempty (translate_reset_eqns bl) (me', vempty)
        /\ reset_lasts bl me'
        /\ (forall x b',
              In (x, b') bl.(b_blocks) ->
              exists me'',
                sub_inst x me' me''
                /\ initial_state P b' me'').
  Proof.
    intros ** WD IH.
    pose proof (b_nodup_lasts_blocks bl) as Nodup_lasts;
      pose proof Nodup_lasts as Nodup_blocks;
      apply NoDup_app_weaken, fst_NoDupMembers in Nodup_lasts;
      apply NoDup_comm, NoDup_app_weaken, fst_NoDupMembers in Nodup_blocks.
    unfold translate_reset_eqns.
    unfold reset_insts.

    setoid_rewrite Comp_spec.
    cut (exists me'' ve'',
            stmt_eval (translate P) me vempty (reset_mems (b_lasts bl)) (me'', ve'')
            /\ reset_lasts bl me''
            /\ exists me',
                stmt_eval (translate P) me'' ve''
                          (fold_left (fun s xf => Comp s (Call [] (snd xf) (fst xf) reset []))
                                     (b_blocks bl) Skip) (me', vempty)
                /\ (forall x b',
                      In (x, b') (b_blocks bl) ->
                      exists me'', sub_inst x me' me'' /\ initial_state P b' me'')).
    - intros (me'' & ve'' &?& RstLasts & me' & StEval &?).
      exists me'; intuition; eauto.
      clear - RstLasts StEval.
      revert dependent me''; revert ve''.
      induction (b_blocks bl) as [|(x, b)]; intros; simpl in *.
      + now chase_skip.
      + apply stmt_eval_fold_left_lift in StEval as (?&?& StEval & StEval').
        rewrite Comp_Skip_left in StEval; inv StEval.
        apply IHl in StEval'; auto.
    - destruct (reset_mems_spec (b_lasts bl) (translate P) me vempty)
        as (me'' & StEval & RstLasts); auto.
      exists me'', vempty; intuition; eauto.
      clear StEval RstLasts Nodup_lasts.
      revert me''; generalize vempty.
      induction (b_blocks bl) as [|(x, b')]; simpl; intros; inv Nodup_blocks.
      + exists me''; intuition; eauto using stmt_eval.
      + setoid_rewrite stmt_eval_fold_left_lift; setoid_rewrite Comp_Skip_left.
        edestruct WD as (?&?&?); try left; eauto.
        edestruct IH with (b' := b') as (me0 &?&?); eauto.
        edestruct IHl as (?&?&?); auto.
        * intros ** Hin; eapply WD; right; eauto.
        *{ eexists; split.
           - do 2 eexists; split; eauto using stmt_eval.
           - intros ** [E|Hin]; eauto.
             inv E.
             unfold sub_inst.
             eexists.
             erewrite reset_insts_not_in; eauto.
             rewrite find_inst_gss; eauto.
         }
  Qed.

  Lemma reset_spec:
    forall P me b bl P',
      Ordered_blocks P ->
      find_block b P = Some (bl, P') ->
      exists me',
        stmt_call_eval (translate P) me b reset [] me' []
        /\ initial_state P b me'.
  Proof.
    induction P as [|node]; try (now inversion 1); intros ** Ord Find.
    pose proof Find as Find'.
    simpl in Find.
    inv Ord.
    destruct (ident_eqb (b_name node) b) eqn: Eq.
    - inv Find.
      pose proof Find'.
      apply find_block_translate in Find' as (?&?&?&?&?); subst.
      edestruct translate_reset_eqns_spec with (bl := bl) as (?&?&?&?); eauto.
      + intros ** Hin; eapply Forall_forall in Hin; eauto.
        destruct Hin; auto.
      + eexists; split; eauto using initial_state.
        econstructor; eauto.
        * apply exists_reset_method.
        * eauto.
        * simpl; auto.
    - simpl in Find'; rewrite Eq in Find';
        eapply (IHP me) in Find' as (me' & Rst &?); auto.
      exists me'; split.
      + inv Rst.
        econstructor; eauto.
        simpl; rewrite Eq; auto.
      + apply initial_state_tail; auto.
        apply ident_eqb_neq; auto.
  Qed.

  Lemma Memory_Corres_Def:
    forall x ck ce S I S' me eqs,
      Memory_Corres eqs S I S' me ->
      Memory_Corres (EqDef x ck ce :: eqs) S I S' me.
  Proof.
    intros ** (Lasts & Insts); split; [split|split; [|split]].
    - inversion_clear 1 as [?? Last|]; eauto.
      + inv Last.
      + apply Lasts; auto.
    - intro NLast; apply Lasts.
      intro; apply NLast; right; auto.
    - intros (Nstep & Nrst).
      apply Insts; split.
      + intro; apply Nstep; right; auto.
      + intro; apply Nrst; right; auto.
    - intros (Nstep & Rst).
      apply Insts; split.
      + intro; apply Nstep; right; auto.
      + inversion_clear Rst as [?? IsSt|]; auto.
        inv IsSt.
    - intros Step.
      apply Insts; inversion_clear Step as [?? IsSt|]; auto.
      inv IsSt.
  Qed.

  Lemma Memory_Corres_Next_present:
    forall x ck e S I S' me eqs c,
      Memory_Corres eqs S I S' me ->
      find_val x S' = Some c ->
      Memory_Corres (EqNext x ck e :: eqs) S I S' (add_val x c me).
  Proof.
    intros ** (Lasts & Insts); split; [split|split; [|split]].
    - inversion_clear 1 as [?? Last|?? Last]; eauto.
      + inv Last.
        rewrite find_val_gss; congruence.
      + intros.
        destruct (ident_eq_dec x0 x).
        * subst; rewrite find_val_gss; congruence.
        * rewrite find_val_gso; auto.
          apply Lasts with (1 := Last); auto.
    - intros NLast **.
      rewrite find_val_gso.
      + apply Lasts; auto.
        intro; apply NLast; right; auto.
      + intro; subst; apply NLast; left; constructor.
    - intros (Nstep & Nrst).
      unfold sub_inst; setoid_rewrite find_inst_add_val.
      apply Insts; split.
      + intro; apply Nstep; right; auto.
      + intro; apply Nrst; right; auto.
    - intros (Nstep & Rst).
      unfold sub_inst; setoid_rewrite find_inst_add_val.
      apply Insts; split.
      + intro; apply Nstep; right; auto.
      + inversion_clear Rst as [?? IsSt|]; auto.
        inv IsSt.
    - intros Step.
      unfold sub_inst; setoid_rewrite find_inst_add_val.
      apply Insts; inversion_clear Step as [?? IsSt|]; auto.
      inv IsSt.
  Qed.

  Definition is_last_in_eq_b (x: ident) (eq: equation) : bool :=
    match eq with
    | EqNext y ck e => ident_eqb x y
    | _ => false
    end.

  Definition is_last_in_eqs_b (x: ident) (eqs: list equation) : bool :=
    existsb (is_last_in_eq_b x) eqs.

  Fact Is_last_in_eq_reflect:
    forall x eq,
      Is_last_in_eq x eq <-> is_last_in_eq_b x eq = true.
  Proof.
    destruct eq; simpl; split;
      try discriminate; try now inversion 1.
    - inversion_clear 1; apply ident_eqb_refl.
    - rewrite ident_eqb_eq; intro; subst; constructor.
  Qed.

  Corollary Is_last_in_eqs_reflect:
    forall x eqs,
      Is_last_in_eqs x eqs <-> is_last_in_eqs_b x eqs = true.
  Proof.
    setoid_rewrite existsb_exists; setoid_rewrite Exists_exists.
    split; intros (?&?& Last); apply Is_last_in_eq_reflect in Last; eauto.
  Qed.

  Lemma Is_last_in_eqs_dec:
    forall x eqs,
      { Is_last_in_eqs x eqs } + { ~ Is_last_in_eqs x eqs }.
  Proof.
    intros;
      eapply Bool.reflect_dec, Bool.iff_reflect, Is_last_in_eqs_reflect.
  Qed.

  Lemma Memory_Corres_Next_absent:
    forall x ck e S I S' me eqs,
      Memory_Corres eqs S I S' me ->
      find_val x S' = find_val x S ->
      Memory_Corres (EqNext x ck e :: eqs) S I S' me.
  Proof.
    intros ** (Lasts & Insts) Eq; split; [split|split; [|split]].
    - inversion_clear 1 as [?? Last|?? Last]; eauto.
      + inv Last.
        destruct (Is_last_in_eqs_dec x eqs).
        * apply Lasts; auto.
        * setoid_rewrite Eq.
          apply Lasts; auto.
      + apply Lasts; auto.
    - intros NLast.
      apply Lasts; intro; apply NLast; right; auto.
    - intros (Nstep & Nrst).
      apply Insts; split.
      + intro; apply Nstep; right; auto.
      + intro; apply Nrst; right; auto.
    - intros (Nstep & Rst).
      apply Insts; split.
      + intro; apply Nstep; right; auto.
      + inversion_clear Rst as [?? IsSt|]; auto.
        inv IsSt.
    - intros Step.
      apply Insts; inversion_clear Step as [?? IsSt|]; auto.
      inv IsSt.
  Qed.

  Lemma Memory_Corres_Reset_present:
    forall s ck b S I S' Is me eqs me',
      Memory_Corres eqs S I S' me ->
      Env.find s I = Some Is ->
      me' ≋ Is ->
      ~ Step_in s eqs ->
      Memory_Corres (EqReset s ck b :: eqs) S I S' (add_inst s me' me).
  Proof.
    intros ** (Lasts & Insts) ???; split; [split|split; [|split]].
    - inversion_clear 1 as [?? Last|]; eauto.
      + inv Last.
      + apply Lasts; auto.
    - intro NLast; apply Lasts.
      intro; apply NLast; right; auto.
    - intros (Nstep & Nrst).
      unfold sub_inst.
      assert (s0 <> s) as Neq
          by (intro; subst; apply Nrst; left; constructor).
      apply find_inst_gso with (m := me) (m' := me') in Neq.
      setoid_rewrite Neq.
      apply Insts; split.
      + intro; apply Nstep; right; auto.
      + intro; apply Nrst; right; auto.
    - intros (Nstep & Rst).
      unfold sub_inst.
      inversion_clear Rst as [?? Rst'|].
      + inv Rst'.
        setoid_rewrite find_inst_gss.
        intros; exists me'; intuition; congruence.
      + intros.
        destruct (ident_eq_dec s0 s).
        * subst; rewrite find_inst_gss; exists me'; intuition; congruence.
        * rewrite find_inst_gso; auto.
          apply (proj1 (proj2 (Insts s0))); auto.
          split; auto.
          intro; apply Nstep; right; auto.
    - intros Step.
      inversion_clear Step as [?? Step'|].
      + inv Step'.
      + intros.
        unfold sub_inst.
        destruct (ident_eq_dec s0 s).
        * subst; intuition.
        * rewrite find_inst_gso; auto.
          apply Insts; auto.
  Qed.

  Lemma equation_cons_correct:
    forall eq eqs P R S I S' me ve inputs mems,
      sem_equation P true R S I S' eq ->
      Is_well_sch inputs mems (eq :: eqs) ->
      Memory_Corres eqs S I S' me ->
      equiv_env (fun x => Is_free_in_eq x eq) R mems me ve ->
      exists me' ve',
        stmt_eval (translate P) me ve (translate_eqn mems eq) (me', ve')
        /\ Memory_Corres (eq :: eqs) S I S' me'.
  Proof.
    inversion_clear 1 as [????????? Hexp|
                          ???????????? Hexp|
                          ???????????? Init|
                          ??????????????? Hexps];
      intros; simpl.

    - inv Hexp; exists me; eexists; split;
        try solve [eapply stmt_eval_Control_absent'; eauto; auto];
        try apply Memory_Corres_Def; auto.
      eapply stmt_eval_Control_present'; eauto; auto.
      eapply cexp_correct; eauto.

    - inv Hexp; eexists; exists ve; split;
        try solve [eapply stmt_eval_Control_absent'; eauto; auto].
      + eapply stmt_eval_Control_present'; eauto using stmt_eval, lexp_correct; auto.
      + apply Memory_Corres_Next_present; auto.
      + apply Memory_Corres_Next_absent; auto; congruence.

    - destruct r.
      + pose proof Init.
        inversion_clear Init as [????? Find Rst].
        edestruct reset_spec as (?&?&?); eauto. admit.
        do 2 eexists; split.
        * eapply stmt_eval_Control_present'; eauto; auto.
        * eapply Memory_Corres_Reset_present; eauto.
          admit.
      + exists me, ve; split; try eapply stmt_eval_Control_absent'; eauto; auto.
        admit.

    - inv Hexps.
      + admit.
      + exists me, ve; split; try eapply stmt_eval_Control_absent'; eauto; auto.
        constructor; auto.
        constructor.
        intros.
        match goal with
        | H: sub_inst ?s ?S' _, H': sub_inst ?s ?S' _ |- _ =>
          unfold sub_inst in H, H'; rewrite H in H'; inv H'; auto
        end.
        admit.

  Qed.


  Lemma stmt_eval_translate_cexp_menv_inv:
    forall prog me ve mems x me' ve' e,
      stmt_eval prog me ve (translate_cexp mems x e) (me', ve') ->
      me' = me.
  Proof.
    induction e; simpl; inversion_clear 1; auto; cases.
  Qed.

  Lemma not_Is_defined_in_eq_stmt_eval_menv_inv:
    forall eq x P me ve mems me' ve',
      ~ Is_defined_in_eq x eq ->
      stmt_eval (translate P) me ve (translate_eqn mems eq) (me', ve') ->
      find_val x me' = find_val x me.
  Proof.
    destruct eq; simpl; intros ** NIsDef StEval;
      apply stmt_eval_Control_fwd in StEval;
      destruct StEval as [(?& StEval)|(?&?&?)]; try congruence.
    - now apply stmt_eval_translate_cexp_menv_inv in StEval as ->.
    - inv StEval.
      apply not_Is_defined_in_eq_EqNext in NIsDef.
      rewrite find_val_gso; auto.
    - inv StEval; apply find_val_add_inst.
    - inv StEval; apply find_val_add_inst.
  Qed.

  Corollary not_Is_defined_in_eqs_stmt_eval_menv_inv:
    forall eqs x P me ve mems me' ve',
      ~ Is_defined_in_eqs x eqs ->
      stmt_eval (translate P) me ve (translate_eqns mems eqs) (me', ve') ->
      find_val x me' = find_val x me.
  Proof.
    unfold translate_eqns.
    induction eqs as [|eq]; simpl; intros ** NIsDef StEval.
    - now inv StEval.
    - apply stmt_eval_fold_left_shift in StEval as (me'' & ve'' &?& Hcomp);
        rewrite Comp_Skip_right in Hcomp.
      apply not_Is_defined_in_cons in NIsDef as (?& Spec).
      eapply IHeqs with (me' := me'') in Spec; eauto.
      rewrite <-Spec.
      eapply not_Is_defined_in_eq_stmt_eval_menv_inv; eauto.
  Qed.

  (* Lemma _stmt_eval_menv_inv: *)
  (*   forall eq x P me ve mems me' ve', *)
  (*     (* ~ Is_defined_in_eq x eq -> *) *)
  (*     stmt_eval (translate P) me ve (translate_eqn mems eq) (me', ve') -> *)
  (*     find_inst x me' = find_inst x me. *)
  (* Proof. *)
  (*   destruct eq; simpl; intros ** (* NIsDef *) StEval; *)
  (*     apply stmt_eval_Control_fwd in StEval; *)
  (*     destruct StEval as [(?& StEval)|(?&?&?)]; try congruence. *)
  (*   - now apply stmt_eval_translate_cexp_menv_inv in StEval as ->. *)
  (*   - inv StEval; apply find_inst_add_val.  *)
  (*   - inv StEval. ; apply find_val_add_inst. *)
  (*   - inv StEval; apply find_val_add_inst. *)
  (* Qed. *)


  (* Lemma _stmt_eval_menv_inv: *)
  (*   forall eqs x P me ve mems me' ve', *)
  (*     (* ~ Is_defined_in_eqs x eqs -> *) *)
  (*     stmt_eval (translate P) me ve (translate_eqns mems eqs) (me', ve') -> *)
  (*     find_inst x me' = find_inst x me. *)
  (* Proof. *)
  (*   unfold translate_eqns. *)
  (*   induction eqs as [|eq]; simpl; intros ** NIsDef StEval. *)
  (*   - now inv StEval. *)
  (*   - apply stmt_eval_fold_left_shift in StEval as (me'' & ve'' &?& Hcomp); *)
  (*       rewrite Comp_Skip_right in Hcomp. *)
  (*     (* apply not_Is_defined_in_cons in NIsDef as (?& Spec). *) *)
  (*     eapply IHeqs with (me' := me'') in Spec; eauto. *)
  (*     rewrite <-Spec. *)
  (*     eapply not_Is_defined_in_eq_stmt_eval_menv_inv; eauto. *)
  (* Qed. *)

  Lemma foo:
    forall P S me ve me' ve' eqs eq mems inputs,
      Memory_Corres_eq P S me eq ->
      Is_well_sch inputs mems (eq :: eqs) ->
      stmt_eval (translate P) me ve (translate_eqns mems eqs) (me', ve') ->
      Memory_Corres_eq P S me' eq.
  Proof.
    induction 1 as [|????? Spec|????? Spec|???????? Spec]
                   (* |] *)
                   (*   using Memory_Corres_eq_mult with (P_block := fun b S me => True) *);
      try intros ** Wsch StEval; auto using Memory_Corres_eq.
    - constructor.
      intros ** Find; apply Spec in Find.
      inv Wsch.
      erewrite not_Is_defined_in_eqs_stmt_eval_menv_inv;
        eauto using Is_defined_in_eq.
    - constructor.
      intros ** Sub; apply Spec in Sub.
      admit.
    - constructor.
      intros ** Sub; apply Spec in Sub as (me'' &?&?).
      exists me''; split; auto.
      inv Wsch.
    intros.

    destruct eq.

  Admitted.


  Lemma equations_cons_correct:
    forall eq eqs P R S I S' me ve me' ve' inputs mems,
      sem_equation P true R S I S' eq ->
      Is_well_sch inputs mems (eq :: eqs) ->
      Memory_Corres_eqs P S' me' eqs ->
      Memory_Corres_eq P S me eq ->
      equiv_env (fun x => Is_free_in_eq x eq) R mems me' ve' ->
      stmt_eval (translate P) me ve (translate_eqns mems eqs) (me', ve') ->
      exists me'' ve'',
        stmt_eval (translate P) me ve (translate_eqns mems (eq :: eqs)) (me'', ve'')
        /\ Memory_Corres_eqs P S' me'' (eq :: eqs).
  Proof.
    intros.
    edestruct equation_cons_correct as (me'' & ve'' &?&?); eauto.
    exists me'', ve''; split; auto.
    unfold translate_eqns; simpl; rewrite stmt_eval_fold_left_shift.
    exists me', ve'; split; eauto using stmt_eval.
  Qed.

  Lemma equations_correct:
    forall eqs P R S I S' me ve inputs mems,
      Forall (sem_equation P true R S I S') eqs ->
      Is_well_sch inputs mems eqs ->
      Memory_Corres_eqs P S me eqs ->
      exists me' ve',
        stmt_eval (translate P) me ve (translate_eqns mems eqs) (me', ve')
        /\ Memory_Corres_eqs P S' me' eqs.
  Proof.
    induction eqs; simpl;
      intros ** Heqs Wsch Corres; inv Heqs; inv Wsch; inv Corres.
    - do 4 econstructor.
    - edestruct IHeqs as (me' & ve' &?&?); eauto.
      eapply equations_cons_correct; eauto using Is_well_sch.
      admit.
  Qed.

  Theorem correctness:
    forall P b S xs ys S' me,
      sem_block P b S (map present xs) (map present ys) S' ->
      Memory_Corres P b S me ->
      exists me',
        stmt_call_eval (translate P) me b step xs me' ys
        /\ Memory_Corres P b S' me'.
  Proof.
    intros ** Sem Corres.
    inversion_clear Sem as [?????????? Clock Find ????? Heqs IHeqs].
    inversion_clear Corres as [????? Find']; rewrite Find' in Find; inv Find.
    assert (Is_well_sch (map fst (b_in bl)) (ps_from_list (map fst (b_lasts bl))) (b_eqs bl)) by admit.
    assert (base = true) by (apply Clock; rewrite present_list_spec; eauto); subst.
    edestruct equations_correct with (ve := Env.adds (map fst (m_in (step_method bl))) xs vempty)
      as (me' & ve' &?&?); eauto.
    exists me'; split; eauto using Memory_Corres.
    apply find_block_translate in Find' as (?&?&?&?&?); subst.
    econstructor; eauto.
    - apply exists_step_method.
    - instantiate (1 := ve').
      admit.
    - admit.
  Qed.


End CORRECTNESS.
