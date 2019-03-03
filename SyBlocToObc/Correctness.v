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
           | H: context [ match negb ?x with _ => _ end ] |- _ =>
             destruct x; simpl; try solve [inv H; auto]
           | H: context [ match ?x with _ => _ end ] |- _ =>
             destruct x; try solve [inv H; auto]
           | |- context [ match negb ?x with _ => _ end ] =>
             destruct x; simpl
           | |- context [ match ?x with _ => _ end ] =>
             destruct x
           end; auto.

  Ltac cases_eqn E :=
    repeat match goal with
           | H: context [ match negb ?x with _ => _ end ] |- _ =>
             let E := fresh E in
             destruct x eqn: E; simpl; try solve [inv H; auto]
           | H: context [ match ?x with _ => _ end ] |- _ =>
             let E := fresh E in
             destruct x eqn: E; try solve [inv H; auto]
           | |- context [ match negb ?x with _ => _ end ] =>
             let E := fresh E in
             destruct x eqn: E; simpl
           | |- context [ match ?x with _ => _ end ] =>
             let E := fresh E in
             destruct x eqn: E
           end; auto.

  Definition equiv_env
             (in_domain: ident -> Prop) (R: env) (mems: PS.t) (me: menv) (ve: venv) : Prop :=
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

  Definition is_variable_in_eq_b (x: ident) (eq: equation) : bool :=
    match eq with
    | EqDef x' _ _ => ident_eqb x x'
    | EqCall _ xs _ _ _ _ => existsb (ident_eqb x) xs
    | _ => false
    end.

  Fact Is_variable_in_eq_reflect:
    forall x eq,
      Is_variable_in_eq x eq <-> is_variable_in_eq_b x eq = true.
  Proof.
    destruct eq; simpl; split;
      try discriminate; try now inversion 1.
    - inversion_clear 1; apply ident_eqb_refl.
    - rewrite ident_eqb_eq; intro; subst; constructor.
    - inversion_clear 1.
      apply existsb_exists; eexists; split; eauto.
      apply ident_eqb_refl.
    - rewrite existsb_exists; intros (?&?& E).
      apply ident_eqb_eq in E; subst.
      constructor; auto.
  Qed.

  Lemma Is_variable_in_eq_dec:
    forall x eq,
      { Is_variable_in_eq x eq } + { ~ Is_variable_in_eq x eq }.
  Proof.
    intros;
      eapply Bool.reflect_dec, Bool.iff_reflect, Is_variable_in_eq_reflect.
  Qed.

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

  Definition Is_free_in_eqs (x: ident) (eqs: list equation) : Prop :=
    Exists (Is_free_in_eq x) eqs.

  Definition step_with_reset (s: ident) (eq: equation) : bool :=
    match eq with
    | EqCall s' _ _ true _ _ => ident_eqb s s'
    | _ => false
    end.

  Definition is_step_in_eq_b (s: ident) (eq: equation) : bool :=
    match eq with
    | EqCall s' _ _ _ _ _ => ident_eqb s s'
    | _ => false
    end.

  Definition is_step_in_eqs_b (s: ident) (eqs: list equation) : bool :=
    existsb (is_step_in_eq_b s) eqs.

  Definition is_reset_in_eq_b (s: ident) (eq: equation) : bool :=
    match eq with
    | EqReset s' _ _ => ident_eqb s s'
    | _ => false
    end.

  Definition is_reset_in_eqs_b (s: ident) (eqs: list equation) : bool :=
    existsb (is_reset_in_eq_b s) eqs.

  Fact Step_in_eq_reflect:
    forall s eq,
      Is_state_in_eq s 1 eq <-> is_step_in_eq_b s eq = true.
  Proof.
    destruct eq; simpl; split;
      try discriminate; try now inversion 1.
    - inversion_clear 1; apply ident_eqb_refl.
    - rewrite ident_eqb_eq; intro; subst; constructor.
  Qed.

  Corollary Step_in_reflect:
    forall s eqs,
      Step_in s eqs <-> is_step_in_eqs_b s eqs = true.
  Proof.
    setoid_rewrite existsb_exists; setoid_rewrite Exists_exists.
    split; intros (?&?& Step); apply Step_in_eq_reflect in Step; eauto.
  Qed.

  Lemma Step_in_dec:
    forall s eqs,
      { Step_in s eqs } + { ~ Step_in s eqs }.
  Proof.
    intros;
      eapply Bool.reflect_dec, Bool.iff_reflect, Step_in_reflect.
  Qed.

  Fact Reset_in_eq_reflect:
    forall s eq,
      Is_state_in_eq s 0 eq <-> is_reset_in_eq_b s eq = true.
  Proof.
    destruct eq; simpl; split;
      try discriminate; try now inversion 1.
    - inversion_clear 1; apply ident_eqb_refl.
    - rewrite ident_eqb_eq; intro; subst; constructor.
  Qed.

  Corollary Reset_in_reflect:
    forall s eqs,
      Reset_in s eqs <-> is_reset_in_eqs_b s eqs = true.
  Proof.
    setoid_rewrite existsb_exists; setoid_rewrite Exists_exists.
    split; intros (?&?& Step); apply Reset_in_eq_reflect in Step; eauto.
  Qed.

  Lemma Reset_in_dec:
    forall s eqs,
      { Reset_in s eqs } + { ~ Reset_in s eqs }.
  Proof.
    intros;
      eapply Bool.reflect_dec, Bool.iff_reflect, Reset_in_reflect.
  Qed.

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
        (forall s, if step_with_reset s eq then Reset_in s eqs else ~ Reset_in s eqs) ->
        Is_well_sch inputs mems (eq :: eqs).

  Lemma Is_last_in_eq_defined_not_variable:
    forall x eq,
      Is_last_in_eq x eq <-> Is_defined_in_eq x eq /\ ~ Is_variable_in_eq x eq.
  Proof.
    destruct eq; split; inversion_clear 1;
      try match goal with H: Is_defined_in_eq _ _ |- _ => inv H end;
      try match goal with H: ~ Is_variable_in_eq _ _ |- _ =>
                          exfalso; apply H; constructor end;
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

  Definition value_corres (x: ident) (S: state) (me: menv) : Prop :=
    find_val x S = find_val x me.

  Definition state_corres (s: ident) (S: state) (me: menv) : Prop :=
    (forall Ss,
        sub_inst s S Ss ->
        exists me',
          sub_inst s me me'
          /\ me' ≋ Ss)
    /\ forall me',
      sub_inst s me me' ->
      exists Ss,
        sub_inst s S Ss
        /\ me' ≋ Ss.

  Definition transient_state_corres (s: ident) (I: transient_states) (me: menv) : Prop :=
    (forall Is,
        Env.find s I = Some Is ->
        exists me',
          sub_inst s me me'
          /\ me' ≋ Is)
    /\ forall me',
      sub_inst s me me' ->
      exists Is,
        Env.find s I = Some Is
        /\ me' ≋ Is.

  Definition Memory_Corres_eqs
             (eqs: list equation)
             (S: state) (I: transient_states) (S': state)
             (me: menv) : Prop :=
    (forall x,
        (Is_last_in_eqs x eqs -> value_corres x S' me)
        /\
        (~ Is_last_in_eqs x eqs -> value_corres x S me))
    /\
    (forall s,
        (~ Step_in s eqs /\ ~ Reset_in s eqs ->
         state_corres s S me)
        /\
        (~ Step_in s eqs /\ Reset_in s eqs ->
         transient_state_corres s I me)
        /\
        (Step_in s eqs ->
         state_corres s S' me)).


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

  (* Lemma reset_mems_not_in: *)
  (*   forall mems prog me ve me' ve' x, *)
  (*     stmt_eval prog me ve (reset_mems mems) (me', ve') -> *)
  (*     ~ InMembers x mems -> *)
  (*     find_val x me' = find_val x me. *)
  (* Proof. *)
  (*   unfold reset_mems. *)
  (*   induction mems as [|(x, c)]; intros ** StEval Notin; simpl in StEval. *)
  (*   - chase_skip; auto. *)
  (*   - apply NotInMembers_cons in Notin as (). *)
  (*     apply stmt_eval_fold_left_lift in StEval as (?&?& Hcomp & StEval); *)
  (*       rewrite Comp_Skip_left in Hcomp; inv Hcomp. *)
  (*     eapply IHmems in StEval; eauto. *)
  (*     rewrite find_val_gso in StEval; auto. *)
  (* Qed. *)

  Section BuildMemWith.

    Context {A B V: Type}.
    Variable f: A -> V.
    Variable g: ident * B -> memory V.

    Definition build_mem_with_spec
               (xs: list (ident * A)) (ys: list (ident * B)) (m: memory V): memory V :=
      let (xs, vs) := split xs in
      let (ys', ws) := split ys in
      Mem (Env.adds xs (map f vs) (values m)) (Env.adds ys' (map g ys) (instances m)).

    Lemma build_mem_with_spec_values:
      forall xs ys m,
        values (build_mem_with_spec xs ys m) =
        let (xs, vs) := split xs in
        Env.adds xs (map f vs) (values m).
    Proof.
      intros; unfold build_mem_with_spec; destruct (split xs), (split ys); auto.
    Qed.

    Lemma build_mem_with_spec_instances:
      forall xs ys m,
        instances (build_mem_with_spec xs ys m) =
        let (ys', ws) := split ys in
        Env.adds ys' (map g ys) (instances m).
    Proof.
      intros; unfold build_mem_with_spec; destruct (split xs), (split ys); auto.
    Qed.

  End BuildMemWith.

  Add Parametric Morphism A B V f xs ys m: (fun g => @build_mem_with_spec A B V f g xs ys m)
      with signature (fun g g' => forall x, g x ≋ g' x) ==> equal_memory
        as build_mem_with_spec_rec_equal_memory.
  Proof.
    intros g g' E.
    unfold build_mem_with_spec.
    induction ys as [|(y, b)]; simpl; try reflexivity.
    destruct (split ys); simpl.
    unfold Env.adds. simpl.
    destruct (split xs); simpl.
    constructor; try reflexivity.
    simpl.
    inversion_clear IHys as [??? Insts].
    unfold Env.adds in Insts; simpl in Insts.
    now rewrite E, Insts.
  Qed.

  Fixpoint reset_state_spec (P: SynSB.program) (me: menv) (b: ident) : menv :=
    let reset_state_spec_aux (P: SynSB.program) (me: menv) (xb: ident * ident) :=
        reset_state_spec P match find_inst (fst xb) me with
                           | Some me' => me'
                           | None => mempty
                           end (snd xb)
    in
    match P with
    | [] => me
    | bl :: P =>
      if ident_eqb (b_name bl) b
      then build_mem_with_spec sem_const (reset_state_spec_aux P me) (b_lasts bl) (b_blocks bl) me
      else reset_state_spec P me b
    end.

  Definition reset_state_spec_aux (P: SynSB.program) (me: menv) (xb: ident * ident) : menv :=
    reset_state_spec P match find_inst (fst xb) me with
                       | Some me' => me'
                       | None => mempty
                       end (snd xb).

  Lemma reset_state_spec_find_Some:
    forall P me b P' bl,
      find_block b P = Some (bl, P') ->
      reset_state_spec P me b = build_mem_with_spec sem_const
                                                    (reset_state_spec_aux P' me)
                                                    (b_lasts bl) (b_blocks bl)
                                                    me.
  Proof.
    intros ** Find.
    induction P as [|bl'].
    - inv Find.
    - simpl in *.
      destruct (ident_eqb (b_name bl') b); auto.
      inv Find; auto.
  Qed.

  Lemma reset_state_spec_find_None:
    forall P me b,
      find_block b P = None ->
      reset_state_spec P me b = me.
  Proof.
    intros ** Find.
    induction P as [|bl']; simpl in *; auto.
    destruct (ident_eqb (b_name bl') b); try discriminate; auto.
  Qed.

  Lemma find_val_reset_state_spec:
    forall P me b bl P',
      find_block b P = Some (bl, P') ->
      (forall x, find_val x me <> None -> InMembers x (b_lasts bl)) ->
      reset_lasts bl (reset_state_spec P me b).
  Proof.
    intros ** Spec_me.
    unfold reset_lasts, find_val in *.
    erewrite reset_state_spec_find_Some; eauto.
    rewrite build_mem_with_spec_values.
    pose proof (b_nodup_lasts bl) as Nodup;
      apply fst_NoDupMembers in Nodup.
    split; intros ** Hx.
    - destruct (split (b_lasts bl)) eqn: E.
      rewrite <-split_fst_map, E in Nodup; auto.
      apply Env.In_find_adds; auto.
      rewrite combine_map_snd.
      pose proof (split_combine (b_lasts bl)) as Eq.
      rewrite E in Eq.
      apply in_map_iff.
      setoid_rewrite Eq.
      exists (x, c); auto.
    - destruct (Env.find x (values me)) eqn: Find.
      + assert (InMembers x (b_lasts bl)) as Hin
            by (apply Spec_me; rewrite Find; discriminate).
        clear Spec_me.
        induction (b_lasts bl) as [|(x', c')]; simpl in *.
        * inv Hin.
        *{ destruct (split l) eqn: El.
           destruct Hin; simpl in *.
           - subst; rewrite Env.find_gsss in Hx.
             inv Hx; eauto.
           - inversion_clear Nodup as [|?? Notin].
             rewrite Env.find_gsso in Hx.
             + apply IHl in Hx as (c &?&?); eauto.
             + intro; subst; apply Notin, fst_InMembers; auto.
         }
      + destruct (split (b_lasts bl)) eqn: E.
        rewrite <-split_fst_map, E in Nodup; auto.
        apply Env.find_adds_In in Hx; auto.
        rewrite combine_map_snd in Hx.
        pose proof (split_combine (b_lasts bl)) as Eq.
        rewrite E in Eq.
        apply in_map_iff in Hx as ((?&?)& E' & Hin).
        inv E'; setoid_rewrite Eq in Hin.
        exists c; auto.
  Qed.

  Lemma reset_state_spec_other:
    forall P b me bl,
      b <> b_name bl ->
      reset_state_spec (bl :: P) me b = reset_state_spec P me b.
  Proof.
    intros.
    destruct (find_block b P) as [[]|] eqn: Find.
    - symmetry; erewrite reset_state_spec_find_Some; eauto.
      erewrite <-find_block_other in Find; eauto.
      erewrite reset_state_spec_find_Some; eauto.
    - symmetry; rewrite reset_state_spec_find_None; auto.
      rewrite <-find_block_other with (bl := bl) in Find; eauto.
      rewrite reset_state_spec_find_None; auto.
  Qed.

  Lemma reset_state_spec_other_app:
    forall P P' b me bl,
      find_block b P = None ->
      b <> b_name bl ->
      reset_state_spec (P ++ bl :: P') me b = reset_state_spec P' me b.
  Proof.
    intros.
    destruct (find_block b P') as [[]|] eqn: Find.
    - symmetry; erewrite reset_state_spec_find_Some; eauto.
      erewrite <-find_block_other_app in Find; eauto.
      erewrite reset_state_spec_find_Some; eauto.
    - symmetry; rewrite reset_state_spec_find_None; auto.
      rewrite <-find_block_other_app with (P := P) (bl := bl) in Find; eauto.
      rewrite reset_state_spec_find_None; auto.
  Qed.

  Inductive correct_domain: SynSB.program -> ident -> menv -> Prop :=
    correct_domain_intro:
      forall P b me bl P',
        find_block b P = Some (bl, P') ->
        (forall x,
            find_val x me <> None ->
            InMembers x (b_lasts bl)) ->
        (forall x me',
            sub_inst x me me' ->
            exists b',
              In (x, b') (b_blocks bl)
              /\ correct_domain P' b' me') ->
        correct_domain P b me.

  Lemma correct_domain_empty:
    forall P b bl P',
      find_block b P = Some (bl, P') ->
      correct_domain P b mempty.
  Proof.
    intros ** Find.
    econstructor; eauto.
    - setoid_rewrite find_val_gempty; intuition.
    - unfold sub_inst; setoid_rewrite find_inst_gempty; congruence.
  Qed.

  Lemma correct_domain_other:
    forall me P b bl,
      b <> b_name bl ->
      (correct_domain (bl :: P) b me <-> correct_domain P b me).
  Proof.
    split; inversion_clear 1 as [????? Find]; econstructor; eauto.
    - rewrite find_block_other in Find; eauto.
    - rewrite find_block_other; eauto.
  Qed.

  Lemma correct_domain_other_app:
    forall me P P' b bl,
      find_block b P = None ->
      b <> b_name bl ->
      (correct_domain (P ++ bl :: P') b me <-> correct_domain P' b me).
  Proof.
    split; inversion_clear 1 as [????? Find]; econstructor; eauto.
    - rewrite find_block_other_app in Find; eauto.
    - rewrite find_block_other_app; eauto.
  Qed.

  Lemma initial_reset_state_spec:
    forall P me b,
      Ordered_blocks P ->
      correct_domain P b me ->
      initial_state P b (reset_state_spec P me b).
  Proof.
    induction P as [|node]; intros ** Ord CorrDom;
      inversion_clear CorrDom as [????? Find Spec_lasts Spec_insts];
      try now inv Find.
    econstructor; eauto.

    - split; eapply find_val_reset_state_spec; eauto.

    - intros ** Hin.
      unfold sub_inst, find_inst.
      erewrite reset_state_spec_find_Some; eauto.
      rewrite build_mem_with_spec_instances.
      pose proof (b_nodup_blocks bl) as Nodup;
        rewrite fst_NoDupMembers in Nodup.
      destruct (split (b_blocks bl)) as (l, l') eqn: Eq.
      exists (reset_state_spec_aux P' me (x, b')); split.
      + apply Environment.Env.In_find_adds.
        * assert (l = map fst (b_blocks bl)) as ->
              by (now rewrite <-split_fst_map, Eq); auto.
        * rewrite combine_map_snd.
          apply in_map_iff.
          exists (x, (x, b')); split; auto.
          clear - Hin Eq.
          revert dependent l; revert l'.
          induction (b_blocks bl) as [|(y, c) bls]; intros;
            simpl in *; try contradiction.
          destruct (split bls).
          inv Eq; simpl.
          destruct Hin as [E|]; eauto.
          inv E; auto.
      + simpl in Find.
        apply fst_NoDupMembers in Nodup.
        destruct (ident_eqb (b_name node) b) eqn: E.
        * inv Find.
          inversion_clear Ord as [|??? Blocks].
          eapply Forall_forall in Blocks as (?&?&?&Find'); eauto.
          eapply IHP; eauto.
          simpl; destruct (find_inst x me) eqn: Find_me;
            try eapply correct_domain_empty; eauto.
          apply Spec_insts in Find_me as (b'' &?&?).
          assert (b' = b'') as -> by (eapply NoDupMembers_det; eauto); auto.
        * pose proof Ord as Ord'.
          inversion_clear Ord as [|?? Ord'' Blocks]; clear Blocks.
          apply find_block_app in Find as (P1 & HP &?).
          rewrite HP in *.
          apply Ordered_blocks_split in Ord''.
          eapply Forall_forall in Ord'' as (?&?&?&?& Find'); eauto.
          simpl in *.
          rewrite <-find_block_other_app with (P := P1) (bl := bl) in Find'; auto.
          unfold reset_state_spec_aux.
          erewrite <-reset_state_spec_other_app, <-initial_state_other_app; eauto.
          inv Ord'.
          eapply IHP; eauto.
          simpl; destruct (find_inst x me) eqn: Find_me;
            try eapply correct_domain_empty; eauto.
          rewrite correct_domain_other_app; auto.
          apply Spec_insts in Find_me as (b'' &?&?).
          assert (b' = b'') as -> by (eapply NoDupMembers_det; eauto); auto.

    - unfold sub_inst, find_inst.
      erewrite reset_state_spec_find_Some; eauto.
      rewrite build_mem_with_spec_instances.
      pose proof (b_nodup_lasts_blocks bl) as NoDup.
      apply NoDup_comm, NoDup_app_weaken in NoDup.
      destruct (split (b_blocks bl)) as (l, l') eqn: Eq.
      intros ** Find'.
      apply Env.find_adds_In_spec in Find' as [Hin|(Notin & Find')].
      + rewrite combine_map_snd in Hin.
        apply in_map_iff in Hin as ((?& x' & b')& E & Hin); simpl in *; inv E.
        assert (x = x').
        { clear - Eq Hin.
          revert dependent l; revert l'.
          induction (b_blocks bl) as [|(y, c) bls]; intros;
            simpl in *.
          - inv Eq; contradiction.
          - destruct (split bls); inv Eq.
            destruct Hin as [E|]; eauto.
            inv E; auto.
        }
        subst x'.
        exists b'.
        clear - Hin Eq.
        revert dependent l; revert l'.
        induction (b_blocks bl) as [|(y, c) bls]; intros;
          simpl in *.
        * inv Eq; contradiction.
        * destruct (split bls).
            inv Eq; simpl.
            destruct Hin as [E|]; eauto.
            inv E; auto.
      + apply Spec_insts in Find' as (?&?&?); eauto.
      + assert (l = map fst (b_blocks bl)) as ->
            by (now rewrite <-split_fst_map, Eq); auto.
  Qed.

  Definition add_mems (mems: list (ident * const)) (me: menv) : menv :=
    Mem (fold_left (fun vs xc => Env.add (fst xc) (sem_const (snd xc)) vs) mems (values me)) (instances me).

  Lemma add_inst_add_mems:
    forall x me me' xs,
      add_inst x me' (add_mems xs me) = add_mems xs (add_inst x me' me).
  Proof. reflexivity. Qed.

  Lemma find_inst_add_mems:
    forall x me xs,
      find_inst x (add_mems xs me) = find_inst x me.
  Proof. reflexivity. Qed.

  Lemma add_mems_cons:
    forall x c xs me,
      add_mems ((x, c) :: xs) me = add_mems xs (add_val x (sem_const c) me).
  Proof. reflexivity. Qed.

  Lemma add_mems_nil:
    forall me,
      add_mems [] me = me.
  Proof. destruct me; reflexivity. Qed.

  Lemma add_mems_gss:
    forall x c xs me,
      ~ InMembers x xs ->
      find_val x (add_mems ((x, c) :: xs) me) = Some (sem_const c).
  Proof.
    intros ** Notin; rewrite add_mems_cons.
    revert me; induction xs as [|()]; intros.
    - now rewrite add_mems_nil, find_val_gss.
    - apply NotInMembers_cons in Notin as ().
      rewrite add_mems_cons, add_val_comm; auto.
  Qed.

  Lemma find_val_add_mems_in:
    forall x c xs me,
      NoDupMembers xs ->
      In (x, c) xs ->
      find_val x (add_mems xs me) = Some (sem_const c).
  Proof.
    intros ** Nodup Hin.
    revert me; induction xs as [|()]; intros.
    - inversion Hin.
    - inv Nodup.
      destruct Hin as [E|?].
      + inv E.
        now apply add_mems_gss.
      + rewrite add_mems_cons; auto.
  Qed.

  Lemma find_val_add_mems_inv:
    forall x xs me v,
      find_val x (add_mems xs me) = Some v ->
      (NoDupMembers xs -> InMembers x xs -> exists c, v = sem_const c /\ In (x, c) xs)
      /\
      (~ InMembers x xs -> find_val x me = Some v).
  Proof.
    intros ** Find; split; [intros ** Nodup Hin|intros ** Hin].
    - revert dependent me; induction xs as [|(x', c)]; intros;
        inv Hin; inv Nodup.
      + rewrite add_mems_gss in Find; auto; inv Find.
        exists c; intuition.
      + rewrite add_mems_cons in Find.
        edestruct IHxs as (?&?&?); eauto.
        eexists; intuition; eauto; right; auto.
    - revert dependent me; induction xs as [|(x', c')]; intros.
      + now rewrite add_mems_nil in Find.
      + rewrite add_mems_cons in Find.
        apply NotInMembers_cons in Hin as ().
        apply IHxs in Find; auto.
        rewrite find_val_gso in Find; auto.
  Qed.

  Lemma reset_mems_spec:
    forall mems prog me ve,
      stmt_eval prog me ve (reset_mems mems) (add_mems mems me, ve).
  Proof.
    unfold reset_mems.
    induction mems as [|(x, c)]; simpl; intros.
    - rewrite add_mems_nil; eauto using stmt_eval.
    - rewrite stmt_eval_fold_left_lift; setoid_rewrite Comp_Skip_left.
      do 2 eexists; split; eauto using stmt_eval, exp_eval.
      rewrite add_mems_cons; auto.
  Qed.

  Lemma translate_reset_comp:
    forall prog me ve bl me' ve',
      stmt_eval prog me ve (translate_reset bl) (me', ve')
      <-> stmt_eval prog me ve (reset_mems bl.(b_lasts)) (add_mems bl.(b_lasts) me, ve)
        /\ stmt_eval prog (add_mems bl.(b_lasts) me) ve (reset_insts bl.(b_blocks)) (me', ve').
  Proof.
    unfold translate_reset; split.
    - inversion_clear 1 as [| | |????????? StEval| |].
      pose proof (reset_mems_spec (b_lasts bl) prog me ve) as StEval'.
      eapply stmt_eval_det with (2 := StEval') in StEval as (); subst.
      split; auto.
    - intros (); eauto using stmt_eval.
  Qed.

  Lemma add_mems_reset_lasts:
    forall bl me,
      (forall x, find_val x me <> None -> InMembers x (b_lasts bl)) ->
      reset_lasts bl (add_mems bl.(b_lasts) me).
  Proof.
    unfold reset_lasts; intro.
    pose proof (b_nodup_lasts bl) as Nodup.
    intros ** Spec; split.
    - intros; now apply find_val_add_mems_in.
    - intros ** Find; apply find_val_add_mems_inv in Find.
      destruct (in_dec ident_eq_dec x (map fst (b_lasts bl))) as [Hin|Hin];
        rewrite <-fst_InMembers in Hin; pose proof Hin as Hin';
          apply Find in Hin; auto.
      exfalso; apply Hin', Spec, not_None_is_Some; eauto.
  Qed.

  (* Lemma not_InMembers_In_split: *)
  (*   forall A B (xvs: list (A * B)) xs vs x, *)
  (*     split xvs = (xs, vs) -> *)
  (*     ~ InMembers x xvs -> *)
  (*     ~ In x xs. *)
  (* Proof. *)
  (*   intros ** Eq Notin Hin; apply Notin; clear Notin. *)
  (*   revert dependent xs; revert vs. *)
  (*   induction xvs as [|()]; simpl; intros. *)
  (*   + inv Eq; contradiction. *)
  (*   + destruct (split xvs); inv Eq. *)
  (*     destruct Hin; auto. *)
  (*     right; eauto. *)
  (* Qed. *)

  (* Lemma fuu: *)
  (*   forall P me ve bl me' ve', *)
  (*     stmt_eval (translate P) me ve (reset_mems bl.(b_lasts)) (me', ve') -> *)
  (*     reset_lasts bl me'. *)
  (* Proof. *)
  (*   SearchAbout stmt_eval. *)
  (*   unfold translate_reset. *)
  (*   intros. *)
  (*   apply translate_reset_comp in H. *)

  Lemma reset_lasts_reset_insts:
    forall blocks prog me ve me' ve' bl,
      stmt_eval prog me ve (reset_insts blocks) (me', ve') ->
      reset_lasts bl me ->
      reset_lasts bl me'.
  Proof.
    unfold reset_insts.
    induction blocks; simpl.
    - inversion_clear 1; auto.
    - intros ** StEval Lasts.
      apply stmt_eval_fold_left_lift in StEval as (?&?& StEval & StEvals).
      eapply IHblocks in StEvals; eauto.
      rewrite Comp_Skip_left in StEval; inv StEval.
      now apply reset_lasts_add_inst.
  Qed.

  Lemma reset_insts_same_venv:
    forall blocks prog me ve me' ve',
      stmt_eval prog me ve (reset_insts blocks) (me', ve') ->
      ve' = ve.
  Proof.
    unfold reset_insts.
    induction blocks; simpl.
    - inversion_clear 1; auto.
    - intros ** StEval.
      apply stmt_eval_fold_left_lift in StEval as (?&?& StEval & StEvals).
      eapply IHblocks in StEvals; eauto.
      rewrite Comp_Skip_left in StEval; inv StEval.
      apply Env.adds_nil_l.
  Qed.

  Lemma call_reset_inv:
    forall b P bl P' me me' rvs,
      find_block b P = Some (bl, P') ->
      stmt_call_eval (translate P) me b reset [] me' rvs ->
      stmt_eval (translate P') me vempty (translate_reset bl) (me', vempty)
      /\ rvs = [].
  Proof.
    intros ** Find Rst.
    apply find_block_translate in Find as (?&?& Find &?&?); subst.
    inversion_clear Rst as [??????????? Find' Find_m StEval Ret].
    rewrite Find in Find'; inv Find'.
    rewrite exists_reset_method in Find_m; inv Find_m; simpl in *.
    inv Ret; intuition.
    rewrite Env.adds_nil_nil in StEval.
    apply translate_reset_comp in StEval as (?& Insts).
    rewrite translate_reset_comp; intuition.
    assert (ve' = vempty) as <- by (eapply reset_insts_same_venv; eauto); auto.
  Qed.

  Lemma call_reset_reset_lasts:
    forall me' P me b bl P',
      find_block b P = Some (bl, P') ->
      (forall x, find_val x me <> None -> InMembers x (b_lasts bl)) ->
      stmt_call_eval (translate P) me b reset [] me' [] ->
      reset_lasts bl me'.
  Proof.
    intros ** Find Spec Rst.
    eapply call_reset_inv in Rst as (Rst); eauto;
      apply translate_reset_comp in Rst as ().
    eapply reset_lasts_reset_insts; eauto.
    apply add_mems_reset_lasts; auto.
  Qed.

  Lemma reset_insts_not_InMembers:
    forall blocks prog me ve me' ve' x,
      stmt_eval prog me ve (reset_insts blocks) (me', ve') ->
      ~ InMembers x blocks ->
      find_inst x me' = find_inst x me.
  Proof.
    unfold reset_insts.
    induction blocks as [|(x', c')].
    - inversion 1; auto.
    - intros ** StEval Notin; apply NotInMembers_cons in Notin as (); simpl in *.
      apply stmt_eval_fold_left_lift in StEval as (?&?& StEval & StEvals).
      eapply IHblocks in StEvals; eauto.
      rewrite Comp_Skip_left in StEval; inv StEval.
      rewrite StEvals, find_inst_gso; auto.
  Qed.

  Lemma reset_insts_in:
    forall bl P P' me ve me' ve' x b b',
      find_block b P = Some (bl, P') ->
      stmt_eval (translate P') me ve (reset_insts bl.(b_blocks)) (me', ve') ->
      In (x, b') bl.(b_blocks) ->
      find_block b' P' <> None ->
      exists me_x,
        stmt_call_eval (translate P') (match find_inst x me with
                                       | Some om => om
                                       | None => mempty
                                       end)
                       b' reset [] me_x []
        /\ sub_inst x me' me_x.
  Proof.
    unfold reset_insts.
    intro; pose proof (b_nodup_blocks bl) as Nodup.
    induction bl.(b_blocks) as [|(x', b'')]; simpl; try now inversion 2.
    intros ** Find StEval Hin Find'; inversion_clear Nodup as [|??? Notin].
    apply stmt_eval_fold_left_lift in StEval as (me_x' &?& StEval & StEvals).
    destruct Hin as [E|].
    - inv E.
      unfold sub_inst.
      erewrite reset_insts_not_InMembers with (me' := me'); eauto.
      rewrite Comp_Skip_left in StEval; inv StEval.
      match goal with H: Forall2 _ _ _ |- _ => inv H end.
      rewrite find_inst_gss.
      assert (rvs = []) as <-; eauto.
      apply not_None_is_Some in Find' as (()).
      eapply call_reset_inv; eauto.
    - assert (find_inst x me = find_inst x me_x') as ->; eauto.
      rewrite Comp_Skip_left in StEval; inv StEval.
      rewrite find_inst_gso; auto.
      intro; subst; eapply Notin, In_InMembers; eauto.
  Qed.

  Lemma Ordered_blocks_find_In_blocks:
    forall P b bl P',
      Ordered_blocks P ->
      find_block b P = Some (bl, P') ->
      forall x b,
        In (x, b) bl.(b_blocks) ->
        exists bl P'', find_block b P' = Some (bl, P'').
  Proof.
    induction P as [|block]; try now inversion 2.
    intros ** Ord Find ?? Hin.
    inv Ord.
    simpl in Find.
    destruct (ident_eqb (b_name block) b) eqn: E; eauto.
    inv Find.
    eapply Forall_forall in Hin; eauto.
    destruct Hin; eauto.
  Qed.

  Lemma Ordered_blocks_find_block:
    forall P b bl P',
      Ordered_blocks P ->
      find_block b P = Some (bl, P') ->
      Ordered_blocks P'.
  Proof.
    induction P as [|block]; try now inversion 2.
    intros ** Ord Find.
    inv Ord.
    simpl in Find.
    destruct (ident_eqb (b_name block) b) eqn: E; eauto.
    inv Find; auto.
  Qed.

  Lemma sub_inst_reset_insts_inv:
    forall blocks prog me ve me' ve' x me_x,
      stmt_eval prog me ve (reset_insts blocks) (me', ve') ->
      sub_inst x me' me_x ->
      InMembers x blocks
      \/ sub_inst x me me_x.
  (* Proof. *)
  (*   intros ** Find; split; [intros ** Nodup Hin|intros ** Hin]. *)
  (*   - revert dependent me; induction xs as [|(x', c)]; intros; *)
  (*       inv Hin; inv Nodup. *)
  (*     + rewrite add_mems_gss in Find; auto; inv Find. *)
  (*       exists c; intuition. *)
  (*     + rewrite add_mems_cons in Find. *)
  (*       edestruct IHxs as (?&?&?); eauto. *)
  (*       eexists; intuition; eauto; right; auto. *)
  (*   - revert dependent me; induction xs as [|(x', c')]; intros. *)
  (*     + now rewrite add_mems_nil in Find. *)
  (*     + rewrite add_mems_cons in Find. *)
  (*       apply NotInMembers_cons in Hin as (). *)
  (*       apply IHxs in Find; auto. *)
  (*       rewrite find_val_gso in Find; auto. *)
  (* Qed. *)
    Admitted.

  Lemma call_reset_initial_state:
    forall me' P me b bl P',
      Ordered_blocks P ->
      find_block b P = Some (bl, P') ->
      stmt_call_eval (translate P) me b reset [] me' [] ->
      correct_domain P b me ->
      initial_state P b me'.
  Proof.
    induction me' as [? IH] using memory_ind';
      intros ** Ord Find Rst Correct.
    inversion_clear Correct as [????? Find' ? Correct']; rewrite Find' in Find; inv Find.
    pose proof Ord as Ord'.
    eapply Ordered_blocks_find_block in Ord'; eauto.
    econstructor; eauto.
    - eapply call_reset_reset_lasts; eauto.
    - intros ** Hin.
      eapply call_reset_inv in Rst as (Rst); eauto;
        apply  translate_reset_comp in Rst as ().
      eapply Ordered_blocks_find_In_blocks in Ord as (?&?& Find); eauto.
      pose proof Hin as Hin'.
      eapply reset_insts_in in Hin as (me_x & ? & ?); eauto.
      + exists me_x; split; auto.
        eapply IH; eauto.
        rewrite find_inst_add_mems.
        destruct (find_inst x me) eqn: E.
        * edestruct Correct' as (b'' &?&?); eauto.
          assert (b' = b'') as ->; auto.
          eapply NoDupMembers_det in Hin'; eauto.
          apply b_nodup_blocks.
        * eapply correct_domain_empty; eauto.
      + apply not_None_is_Some; eauto.
    - intros ** Sub.
      eapply call_reset_inv in Rst as (Rst); eauto;
        apply  translate_reset_comp in Rst as ().
      eapply sub_inst_reset_insts_inv in Sub as [|Sub]; eauto.
      + apply InMembers_In; auto.
      + apply Correct' in Sub as (?&?&?); eauto.
  Qed.

  Lemma reset_insts_spec:
    forall bl P b me ve,
      (forall x b, In (x, b) bl.(b_blocks) ->
              exists bl P', find_block b P = Some (bl, P')) ->
      (forall me' b' bl' P',
          find_block b' P = Some (bl', P') ->
          exists me'',
            stmt_call_eval (translate P) me' b' reset [] me'' []
            /\ (correct_domain P b' me' -> initial_state P b' me'')) ->
      b_name bl = b ->
      exists me',
        stmt_eval (translate P) (add_mems (b_lasts bl) me) ve
                  (reset_insts Skip (b_blocks bl)) (me', ve)
        /\ (correct_domain (bl :: P) b (add_mems (b_lasts bl) me) -> initial_state (bl :: P) b me').
  Proof.
    unfold reset_insts.
    intros ** WD IH E.
    pose proof (b_nodup_blocks bl) as Nodup.
    apply ident_eqb_eq in E.
    revert me ve.
    induction (b_blocks bl) as [|(x, b') bls]; simpl; intros;
      inversion_clear Nodup as [|??? Notin Nodup'].
    - eexists; split; eauto using stmt_eval.
      unfold build_mem_with_spec; simpl.
      unfold add_mems; rewrite Env.adds_nil_nil.
      unfold Env.adds; reflexivity.
    - setoid_rewrite stmt_eval_fold_left_lift; setoid_rewrite Comp_Skip_left.
      assert (exists bl' P', find_block b' P = Some (bl', P')) as (?&?&?)
        by (eapply WD; left; eauto).
      edestruct IH as (me0 &?& Eq0); eauto.
      edestruct IHbls as (?&?& Eq); auto.
      + intros; eapply WD; right; eauto.
      + eexists; split.
        * do 2 eexists; split; eauto.
          rewrite add_inst_add_mems; eauto.
        *{ rewrite Eq.
           unfold build_mem_with_spec.
           simpl; destruct (split (b_lasts bl)), (split bls) eqn: E.
           rewrite Env.adds_cons_cons; try eapply not_InMembers_In_split; eauto.
           constructor; simpl; try reflexivity.
           rewrite find_inst_add_mems in Eq0.
           clear - Eq0 E Nodup' Notin.
           revert dependent l1; revert l2.
           induction bls as [|(y, b)]; simpl; intros.
           - inv E.
             rewrite 2 Env.adds_nil_nil.
             now rewrite Eq0.
           - destruct (split bls); inv E.
             apply NotInMembers_cons in Notin as ().
             inversion_clear Nodup' as [|???? Nodup''].
             edestruct IHbls as (Hins & Maps); eauto.
             split.
             + setoid_rewrite Env.In_find.
               intro; destruct (ident_eq_dec k y).
               * subst; rewrite 2 Env.find_gsss; eauto; split; eauto.
               * rewrite 2 Env.find_gsso; auto; simpl.
                 setoid_rewrite <-Env.In_find; auto.
             + setoid_rewrite Env.Props.P.F.find_mapsto_iff.
               intro; destruct (ident_eq_dec k y).
               * subst; rewrite 2 Env.find_gsss.
                 do 2 inversion_clear 1.
                 unfold reset_state_spec_aux.
                 rewrite find_inst_gso; auto.
                 reflexivity.
               * rewrite 2 Env.find_gsso; auto; simpl.
                 setoid_rewrite <-Env.Props.P.F.find_mapsto_iff.
                 apply Maps.
         }
  Qed.

  Lemma translate_reset_spec:
    forall P b me ve bl,
      (forall x b, In (x, b) bl.(b_blocks) -> exists bl P', find_block b P = Some (bl, P')) ->
      (forall me' b' bl' P',
          find_block b' P = Some (bl', P') ->
          exists me'',
            stmt_call_eval (translate P) me' b' reset [] me'' []
            /\ (correct_domain P b me' -> initial_state P b' me'')) ->
      b_name bl = b ->
      exists me',
        stmt_eval (translate P) me ve (translate_reset bl) (me', ve)
        /\ (correct_domain (bl :: P) b me -> initial_state (bl :: P) b me').
  Proof.
    intros.
    pose proof (b_nodup_lasts bl) as Nodup_lasts.
    setoid_rewrite translate_reset_comp.
    edestruct reset_insts_spec as (me' & ?&?); eauto.
    exists me'; split; eauto.
    do 2 eexists; split; eauto.
    now apply reset_mems_spec.
  Qed.

 Lemma reset_spec:
    forall P me b bl P',
      Ordered_blocks P ->
      find_block b P = Some (bl, P') ->
      exists me',
        stmt_call_eval (translate P) me b reset [] me' []
        /\ (correct_domain P b me ->
           initial_state P b me').
  Proof.
    induction P as [|node]; try (now inversion 1); intros ** Ord Find.
    pose proof Find as Find'.
    simpl in Find.
    inv Ord.
    destruct (ident_eqb (b_name node) b) eqn: Eq.
    - inv Find.
      pose proof Find'.
      apply find_block_translate in Find' as (?&?&?&?&?); subst.
      apply ident_eqb_eq in Eq.
      admit.
      (* edestruct translate_reset_spec with (bl := bl) as (?&?&?); eauto. *)
      (* + intros ** Hin; eapply Forall_forall in Hin; eauto. *)
      (*   destruct Hin; auto. *)
      (* + eexists; split; eauto. *)
      (*   econstructor; eauto. *)
      (*   * apply exists_reset_method. *)
      (*   * eauto. *)
      (*   * simpl; auto. *)
    - simpl in Find'; rewrite Eq in Find';
        eapply (IHP me) in Find' as (me' & Rst & Init); auto.
      exists me'; split.
      + inv Rst.
        econstructor; eauto.
        simpl; rewrite Eq; auto.
      + apply ident_eqb_neq in Eq.
        intros Correct; apply initial_state_other; auto.
        apply Init.
        apply correct_domain_other in Correct; auto.
  Qed.

 Lemma reset_spec:
    forall P me b bl P',
      Ordered_blocks P ->
      find_block b P = Some (bl, P') ->
      exists me',
        stmt_call_eval (translate P) me b reset [] me' []
        /\ me' ≋ reset_state_spec P me b.
  Proof.
    induction P as [|node]; try (now inversion 1); intros ** Ord Find.
    pose proof Find as Find'.
    simpl in Find.
    inv Ord.
    destruct (ident_eqb (b_name node) b) eqn: Eq.
    - inv Find.
      pose proof Find'.
      apply find_block_translate in Find' as (?&?&?&?&?); subst.
      apply ident_eqb_eq in Eq.
      edestruct translate_reset_spec with (bl := bl) as (?&?&?); eauto.
      + intros ** Hin; eapply Forall_forall in Hin; eauto.
        destruct Hin; auto.
      + eexists; split; eauto.
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
      + apply ident_eqb_neq in Eq.
        rewrite reset_state_spec_other; auto.
  Qed.

  Lemma Memory_Corres_eqs_Def:
    forall x ck ce S I S' me eqs,
      Memory_Corres_eqs eqs S I S' me ->
      Memory_Corres_eqs (EqDef x ck ce :: eqs) S I S' me.
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

  Lemma Memory_Corres_eqs_Next_present:
    forall x ck e S I S' me eqs c,
      Memory_Corres_eqs eqs S I S' me ->
      find_val x S' = Some c ->
      Memory_Corres_eqs (EqNext x ck e :: eqs) S I S' (add_val x c me).
  Proof.
    intros ** (Lasts & Insts); split; [split|split; [|split]].
    - inversion_clear 1 as [?? Last|?? Last]; eauto; unfold value_corres.
      + inv Last; rewrite find_val_gss; auto.
      + intros.
        destruct (ident_eq_dec x0 x).
        * subst; rewrite find_val_gss; auto.
        * rewrite find_val_gso; auto;
            apply Lasts with (1 := Last); auto.
    - intros NLast **; unfold value_corres.
      assert (x0 <> x)
        by (intro; subst; apply NLast; left; constructor).
      assert ( ~ Is_last_in_eqs x0 eqs)
        by (intro; apply NLast; right; auto).
      rewrite find_val_gso; auto;
        apply Lasts; auto.
    - intros (Nstep & Nrst).
      assert (~ Step_in s eqs) by (intro; apply Nstep; right; auto).
      assert (~ Reset_in s eqs) by (intro; apply Nrst; right; auto).
      split; unfold sub_inst; setoid_rewrite find_inst_add_val;
        apply Insts; auto.
    - intros (Nstep & Rst).
      assert (~ Step_in s eqs) by (intro; apply Nstep; right; auto).
      assert (Reset_in s eqs)
        by (inversion_clear Rst as [?? IsSt|]; auto; inv IsSt).
      split; unfold sub_inst; setoid_rewrite find_inst_add_val;
        apply Insts; auto.
    - intros Step.
      assert (Step_in s eqs)
        by (inversion_clear Step as [?? IsSt|]; auto; inv IsSt).
      split; unfold sub_inst; setoid_rewrite find_inst_add_val;
        apply Insts; auto.
  Qed.

  Lemma Memory_Corres_eqs_Next_absent:
    forall x ck e S I S' me eqs,
      Memory_Corres_eqs eqs S I S' me ->
      find_val x S' = find_val x S ->
      Memory_Corres_eqs (EqNext x ck e :: eqs) S I S' me.
  Proof.
    intros ** (Lasts & Insts) Eq; split; [split|split; [|split]].
    - inversion_clear 1 as [?? Last|?? Last]; eauto; unfold value_corres.
      + inv Last.
        destruct (Is_last_in_eqs_dec x eqs).
        * apply Lasts; auto.
        * setoid_rewrite Eq; apply Lasts; auto.
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

  Lemma Memory_Corres_eqs_Reset_present:
    forall s ck b S I S' Is me eqs me',
      Memory_Corres_eqs eqs S I S' me ->
      Env.find s I = Some Is ->
      me' ≋ Is ->
      ~ Step_in s eqs ->
      Memory_Corres_eqs (EqReset s ck b :: eqs) S I S' (add_inst s me' me).
  Proof.
    intros ** (Lasts & Insts) ??; split; [split|split; [|split]].
    - inversion_clear 1 as [?? Last|]; eauto.
      + inv Last.
      + apply Lasts; auto.
    - intro NLast; apply Lasts.
      intro; apply NLast; right; auto.
    - intros (Nstep & Nrst).
      assert (s0 <> s)
        by (intro; subst; apply Nrst; left; constructor).
      assert (~ Step_in s0 eqs) by (intro; apply Nstep; right; auto).
      assert (~ Reset_in s0 eqs) by (intro; apply Nrst; right; auto).
      split; unfold sub_inst; rewrite find_inst_gso; auto;
        apply Insts; auto.
    - intros (Nstep & Rst).
      inversion_clear Rst as [?? Rst'|].
      + inv Rst'.
        split; unfold sub_inst; setoid_rewrite find_inst_gss.
        * intros; exists me'; intuition; congruence.
        * inversion 1; subst; intros; exists Is; eauto.
      + destruct (ident_eq_dec s0 s).
        *{ split; subst; unfold sub_inst; rewrite find_inst_gss.
           - exists me'; intuition; congruence.
           - inversion 1; subst; intros; exists Is; eauto.
         }
        * assert (~ Step_in s0 eqs) by (intro; apply Nstep; right; auto).
          split; unfold sub_inst; rewrite find_inst_gso; auto;
            apply (proj1 (proj2 (Insts s0))); auto.
    - intros Step.
      inversion_clear Step as [?? Step'|].
      + inv Step'.
      + destruct (ident_eq_dec s0 s).
        * split; subst; intuition.
        * split; unfold sub_inst; rewrite find_inst_gso; auto;
            apply Insts; auto.
  Qed.

  Lemma Memory_Corres_eqs_Reset_absent:
    forall s ck b S I S' Is Ss me eqs,
      Memory_Corres_eqs eqs S I S' me ->
      Env.find s I = Some Is ->
      sub_inst s S Ss ->
      Is ≋ Ss ->
      ~ Reset_in s eqs ->
      Memory_Corres_eqs (EqReset s ck b :: eqs) S I S' me.
  Proof.
    intros ** (Lasts & Insts) Find_I Find_S E; split; [split|split; [|split]].
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
      inversion_clear Rst as [?? Rst'|].
      + inv Rst'.
        assert (~ Step_in s eqs) by (intro; apply Nstep; right; auto).
        split; unfold sub_inst.
        * intros ** Find.
          rewrite Find in Find_I; inv Find_I.
          setoid_rewrite E.
          apply (proj1 (Insts s)); auto.
        * assert (state_corres s S me) as StCorr by (apply Insts; auto).
          intros ** Find; apply StCorr in Find as (?& Find & ?).
          unfold sub_inst in *; rewrite Find in Find_S; inv Find_S.
          exists Is; split; eauto.
          now rewrite E.
      + apply Insts; split; auto.
        intro; apply Nstep; right; auto.
    - intros Step.
      inversion_clear Step as [?? Step'|].
      + inv Step'.
      + apply Insts; eauto.
  Qed.

  Lemma Memory_Corres_eqs_Call_present:
    forall s ys ck (rst: bool) b es S I S' Ss' eqs me me',
      Memory_Corres_eqs eqs S I S' me ->
      sub_inst s S' Ss' ->
      me' ≋ Ss' ->
      Memory_Corres_eqs (EqCall s ys ck rst b es :: eqs) S I S' (add_inst s me' me).
  Proof.
    intros ** (Lasts & Insts) Find_S' E;
      split; [split|split; [|split]].
    - inversion_clear 1 as [?? Last|]; eauto.
      + inv Last.
      + apply Lasts; auto.
    - intro NLast; apply Lasts.
      intro; apply NLast; right; auto.
    - intros (Nstep & Nrst).
      assert (s0 <> s) as Neq
          by (intro; subst; apply Nstep; left; constructor).
      assert (~ Step_in s0 eqs) by (intro; apply Nstep; right; auto).
      assert (~ Reset_in s0 eqs) by (intro; apply Nrst; right; auto).
      split; unfold sub_inst; rewrite find_inst_gso; auto;
        apply Insts; auto.
    - intros (Nstep & Rst).
      assert (s0 <> s) as Neq
          by (intro; subst; apply Nstep; left; constructor).
      assert (~ Step_in s0 eqs) by (intro; apply Nstep; right; auto).
      inversion_clear Rst as [?? Rst'|]; try inv Rst'.
      split; unfold sub_inst; rewrite find_inst_gso; auto;
        apply Insts; auto.
    - intros Step.
      inversion_clear Step as [?? Step'|].
      + inv Step'.
        split; unfold sub_inst; rewrite find_inst_gss.
        * exists me'; intuition; congruence.
        * inversion 1; subst; exists Ss'; intuition.
      + destruct (ident_eq_dec s0 s).
        *{ split; subst; unfold sub_inst; rewrite find_inst_gss.
           - exists me'; intuition; congruence.
           - inversion 1; subst; exists Ss'; intuition.
         }
        * split; unfold sub_inst; rewrite find_inst_gso; auto;
            apply Insts; auto.
  Qed.

  Lemma Memory_Corres_eqs_Call_absent:
    forall s ys ck (rst: bool) b es S I S' Is Ss' eqs me,
      Memory_Corres_eqs eqs S I S' me ->
      Env.find s I = Some Is ->
      (rst = false -> exists Ss, sub_inst s S Ss /\ Is ≋ Ss) ->
      sub_inst s S' Ss' ->
      Ss' ≋ Is ->
      ~ Step_in s eqs /\ (if rst then Reset_in s eqs else ~ Reset_in s eqs) ->
      Memory_Corres_eqs (EqCall s ys ck rst b es :: eqs) S I S' me.
  Proof.
    intros ** (Lasts & Insts) Find_I Find_S Find_S' E NstepRst;
      split; [split|split; [|split]].
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
      + inversion_clear Rst as [?? Rst'|]; auto.
        inv Rst'.
    - intros Step.
      inversion_clear Step as [?? Step'|].
      + inv Step'.
        destruct rst.
        *{ apply Insts in Find_I as (me' & Sub &?); auto.
           split; intros ** Sub'; unfold sub_inst in *.
           - rewrite Find_S' in Sub'; inv Sub'.
             exists me'; rewrite E; auto.
           - rewrite Sub' in Sub; inv Sub.
             exists Ss'; rewrite E at 2; auto.
         }
        *{ destruct Find_S as (Ss & Find_S &?); auto.
           apply Insts in Find_S as (me' & Sub &?); auto.
           split; intros ** Sub'; unfold sub_inst in *.
           - rewrite Find_S' in Sub'; inv Sub'.
             exists me'; split; auto.
             transitivity Ss; auto.
             transitivity Is; symmetry; auto.
           - rewrite Sub' in Sub; inv Sub.
             exists Ss'; split; auto.
             transitivity Ss; auto.
             transitivity Is; symmetry; auto.
         }
      + apply Insts; eauto.
  Qed.

  Lemma Reset_not_Step_in:
    forall eqs inputs mems s ck b,
      Is_well_sch inputs mems (EqReset s ck b :: eqs) ->
      ~ Step_in s eqs.
  Proof.
    inversion_clear 1 as [|????? States].
    unfold Step_in, Is_state_in_eqs.
    rewrite Exists_exists.
    intros (eq' & Hin & IsStin).
    assert (Forall (fun eq => forall k', Is_state_in_eq s k' eq -> k' < 0) eqs)
      by (apply States; auto using Is_state_in_eq).
    eapply Forall_forall in Hin; eauto.
    apply Hin in IsStin.
    omega.
  Qed.

  Lemma Reset_not_Reset_in:
    forall eqs inputs mems s ck b,
      Is_well_sch inputs mems (EqReset s ck b :: eqs) ->
      ~ Reset_in s eqs.
  Proof.
    inversion_clear 1 as [|????? States].
    unfold Reset_in, Is_state_in_eqs.
    rewrite Exists_exists.
    intros (eq' & Hin & IsStin).
    assert (Forall (fun eq => forall k', Is_state_in_eq s k' eq -> k' < 0) eqs)
      by (apply States; auto using Is_state_in_eq).
    eapply Forall_forall in Hin; eauto.
    apply Hin in IsStin.
    omega.
  Qed.

  Lemma Step_not_Step_Reset_in:
    forall eqs inputs mems s ys ck rst b es,
      Is_well_sch inputs mems (EqCall s ys ck rst b es :: eqs) ->
      ~ Step_in s eqs
      /\ if rst then Reset_in s eqs else ~ Reset_in s eqs.
  Proof.
    inversion_clear 1 as [|????? States StepReset].
    unfold Step_in, Reset_in, Is_state_in_eqs.
    split.
    - rewrite Exists_exists.
      intros (eq' & Hin & IsStin).
      assert (Forall (fun eq => forall k', Is_state_in_eq s k' eq -> k' < 1) eqs)
        by (apply States; auto using Is_state_in_eq).
      eapply Forall_forall in Hin; eauto.
      apply Hin in IsStin.
      omega.
    - destruct rst; specialize (StepReset s);
        simpl in StepReset; auto.
      rewrite ident_eqb_refl in StepReset; auto.
  Qed.

  Lemma foo:
    forall eqs S I S' me s Is me' P b bl P',
      Memory_Corres_eqs eqs S I S' me ->
      ~ Step_in s eqs /\ ~ Reset_in s eqs ->
      find_inst s me = Some me' ->
      Env.find s I = Some Is ->
  (* Equiv : equiv_env (fun x : ident => Is_free_in_eq x (EqReset s ck b)) R mems me ve *)
      initial_state P b Is ->
  (* bl : block *)
  (* P' : SynSB.program *)
      find_block b P = Some (bl, P') ->
  (* Rst : reset_lasts bl Is *)
  (* H2 : forall x b' : ident, *)
  (*      In (x, b') (b_blocks bl) -> *)
  (*      exists S0' : memory val, sub_inst x Is S0' /\ initial_state P' b' S0' *)
  (* H3 : forall (x : ident) (S0' : memory val), *)
  (*      sub_inst x Is S0' -> *)
  (*      exists b' : ident, In (x, b') (b_blocks bl) /\ initial_state P' b' S0' *)
  (* me' : menv *)
  (* H4 : stmt_call_eval (translate P) *)
  (*        match find_inst s me with *)
  (*        | Some om => om *)
  (*        | None => mempty *)
  (*        end b reset [] me' [] *)
  (* Eq : me' *)
  (*      ≋ reset_state_spec P match find_inst s me with *)
  (*                           | Some om => om *)
  (*                           | None => mempty *)
  (*                           end b *)
  (* ============================ *)
      correct_domain P b me'.
  Proof.
    intros ** Corres NstpNrst Find_me Find_I Init ?.
    econstructor; eauto.
    - intros ** Find.
      destruct Corres as (? & Insts).
      apply Insts in NstpNrst as (Corres & Corres').
      apply Corres' in Find_me.
      (* apply Corres in *)
      (* destruct H0. *)
      admit.
    - admit.
  Admitted.

  (* Lemma fuu: *)
  (*   forall eqs x ck e inputs mems, *)
  (*     Is_well_sch' inputs mems (EqNext x ck e :: eqs) -> *)
  (*     ~ Is_free_in_eqs x eqs. *)
  (* Proof. *)
  (*   (* inversion_clear 1.  *) *)
  (*   induction eqs; intros ** WSCH Free. *)
  (*   - intros; inversion Free. *)
  (*   - inversion_clear WSCH. *)
  (*     inversion_clear H.  *)
  (*     inversion_clear Free. *)
  (*     + apply H5 in H.  *)
  (*       admit. *)
  (*     + eapply IHeqs; eauto using Is_well_sch'. *)
  (*       econstructor; eauto.  *)
  (*     inversion_clear  *)
  (*     SearchAbout not Exists.  *)
  (*   induction eqs. *)


  Lemma equiv_env_Is_free_in_eqs_cons:
    forall eq eqs R mems me ve,
      equiv_env (fun x => Is_free_in_eqs x (eq :: eqs)) R mems me ve ->
      equiv_env (fun x => Is_free_in_eq x eq) R mems me ve.
  Proof.
    eauto.
  Qed.

  Lemma Forall2_in_left_combine:
  forall A B (P : A -> B -> Prop) (xs : list A) (ys : list B) x,
    Forall2 P xs ys ->
    In x xs ->
    exists y, In (x, y) (combine xs ys) /\ P x y.
  Proof.
    induction 1; inversion_clear 1.
    - subst; exists y; simpl; intuition.
    - simpl; destruct IHForall2; auto.
      eexists; intuition; eauto.
  Qed.

  Lemma equation_cons_correct:
    forall eq eqs P R S I S' me ve inputs mems,
      (forall b S xs ys S' me,
          sem_block P b S (map present xs) (map present ys) S' ->
          me ≋ S ->
          exists me',
            stmt_call_eval (translate P) me b step xs me' ys
            /\ me' ≋ S') ->
      sem_equation P true R S I S' eq ->
      Ordered_blocks P ->
      Is_well_sch inputs mems (eq :: eqs) ->
      Memory_Corres_eqs eqs S I S' me ->
      equiv_env (fun x => Is_free_in_eq x eq) R mems me ve ->
      exists me' ve',
        stmt_eval (translate P) me ve (translate_eqn mems eq) (me', ve')
        /\ Memory_Corres_eqs (eq :: eqs) S I S' me'
        /\ forall x c,
            Is_variable_in_eq x eq ->
            sem_var_instant R x (present c) ->
            Env.find x ve' = Some c.
  Proof.
    intros ** IH Sem Ord Wsch Corres Equiv;
      inversion Sem as [????????? Hexp Hvar|
                        ??????????? Hvar Hexp|
                        ???????????? Init|
                        ??????????????? Hexps Find_S Find_I Hblock Hvars];
      subst; simpl.

    - inv Hexp; exists me; eexists; split;
        try solve [eapply stmt_eval_Control_absent'; eauto; auto].
      + eapply stmt_eval_Control_present'; eauto; auto.
        eapply cexp_correct; eauto.
      + split.
        * apply Memory_Corres_eqs_Def; auto.
        * inversion_clear 1; intros Hvar'.
          eapply sem_var_instant_det in Hvar; eauto.
          inv Hvar; apply Env.gss.
      + split.
        * apply Memory_Corres_eqs_Def; auto.
        * inversion_clear 1; intros Hvar'.
          eapply sem_var_instant_det in Hvar; eauto.
          discriminate.

    - inv Hexp; eexists; exists ve; split;
        try solve [eapply stmt_eval_Control_absent'; eauto; auto].
      + eapply stmt_eval_Control_present'; eauto using stmt_eval, lexp_correct; auto.
      + split; try inversion 1.
        apply Memory_Corres_eqs_Next_present; auto.
      + split; try inversion 1.
        apply Memory_Corres_eqs_Next_absent; auto; congruence.

    - destruct r.
      + pose proof Init.
        inversion_clear Init as [????? Find Rst].
        edestruct reset_spec as (me' &?& Eq); eauto.
        do 2 eexists; split.
        * eapply stmt_eval_Control_present'; eauto; auto.
        *{ split; try inversion 1.
           eapply Memory_Corres_eqs_Reset_present; eauto.
           - eapply initial_state_det; eauto.
             rewrite Eq.
             apply initial_reset_state_spec; auto.
             admit.
           - eapply Reset_not_Step_in; eauto.
         }
      + exists me, ve; split; try eapply stmt_eval_Control_absent'; eauto; auto.
        split; try inversion 1.
        destruct Init as (?&?&?).
        eapply Memory_Corres_eqs_Reset_absent; eauto.
        eapply Reset_not_Reset_in; eauto.

    - apply Step_not_Step_Reset_in in Wsch.
      inv Hexps.
      + assert (exists cs', os = map present cs') as (cs' & ?).
        { apply present_list_spec.
          apply sem_block_present in Hblock; auto.
          apply present_list_spec; eauto.
        }
        subst.
        eapply IH in Hblock as (me' &?&?).
        *{ do 2 eexists; split.
           - eapply stmt_eval_Control_present'; eauto; auto.
             econstructor; eauto using lexps_correct.
           - split.
             + eapply Memory_Corres_eqs_Call_present; eauto.
             + inversion_clear 1; intros Hvar.
               apply Env.In_find_adds.
               * admit.
               * eapply Forall2_in_left_combine in Hvars as (?& Hin &?); eauto.
                 eapply sem_var_instant_det in Hvar; eauto; inv Hvar.
                 rewrite combine_map_snd, in_map_iff in Hin.
                 destruct Hin as ((?&?)&E&?); inv E; auto.
         }
        *{ destruct rst; apply Corres in Wsch as (Inst).
           - apply Inst in Find_I as (?& -> &?); auto.
           - destruct Find_S as (?& Find_S & E); auto.
             apply Inst in Find_S as (?& -> &?); rewrite E; auto.
         }
      + exists me, ve; split; try eapply stmt_eval_Control_absent'; eauto; auto.
        split.
        * apply sem_block_absent in Hblock as (); try apply all_absent_spec.
          eapply Memory_Corres_eqs_Call_absent; eauto.
        * assert (os = all_absent os) as Abs.
          { inversion_clear Hblock as [???????????????? Abs].
            apply absent_list_spec, Abs, all_absent_spec; auto.
          }
          rewrite Abs in Hvars.
          inversion_clear 1; intros Hvar.
          eapply Forall2_in_left in Hvars as (v & Hin &?); eauto.
          eapply sem_var_instant_det in Hvar; eauto; subst v.
          clear - Hin; exfalso.
          induction os; inv Hin; try discriminate; auto.
  Qed.

  Lemma stmt_eval_translate_cexp_menv_inv:
    forall prog me ve mems x me' ve' e,
      stmt_eval prog me ve (translate_cexp mems x e) (me', ve') ->
      me' = me.
  Proof.
    induction e; simpl; inversion_clear 1; auto; cases.
  Qed.

  Lemma stmt_eval_translate_cexp_venv_inv:
    forall prog me ve mems x me' ve' e,
      stmt_eval prog me ve (translate_cexp mems x e) (me', ve') ->
      exists c, ve' = Env.add x c ve.
  Proof.
    induction e; inversion_clear 1; cases; eauto.
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

  Lemma not_Is_defined_in_eq_stmt_eval_venv_inv:
    forall eq x P me ve mems me' ve',
      ~ Is_defined_in_eq x eq ->
      stmt_eval (translate P) me ve (translate_eqn mems eq) (me', ve') ->
      Env.find x ve' = Env.find x ve.
  Proof.
    intros ** Hnd Heval.
    destruct eq; simpl in Heval;
      apply stmt_eval_Control_fwd in Heval;
      destruct Heval as [[Hipi Heval]|[Habs [Hmenv Henv]]];
      subst; auto.
    - apply stmt_eval_translate_cexp_venv_inv in Heval as (?&?); subst.
      apply not_Is_defined_in_eq_EqDef in Hnd.
      rewrite Env.gso; auto.
    - inv Heval; auto.
    - inv Heval.
      rewrite Env.adds_nil_l; auto.
    - inv Heval.
      rewrite Env.find_In_gsso; auto.
      intro; apply Hnd; constructor; auto.
  Qed.

  Corollary not_Is_defined_in_eqs_stmt_eval_venv_inv:
    forall eqs x P me ve mems me' ve',
      ~ Is_defined_in_eqs x eqs ->
      stmt_eval (translate P) me ve (translate_eqns mems eqs) (me', ve') ->
      Env.find x ve' = Env.find x ve.
  Proof.
    unfold translate_eqns.
    induction eqs as [|eq]; simpl; intros ** NIsDef StEval.
    - now inv StEval.
    - apply stmt_eval_fold_left_shift in StEval as (me'' & ve'' &?& Hcomp);
        rewrite Comp_Skip_right in Hcomp.
      apply not_Is_defined_in_cons in NIsDef as (?& Spec).
      eapply IHeqs with (ve' := ve'') in Spec; eauto.
      rewrite <-Spec.
      eapply not_Is_defined_in_eq_stmt_eval_venv_inv; eauto.
  Qed.

  (* Lemma _stmt_eval_menv_inv: *)
  (*   forall eq x P me ve mems me' ve', *)
  (*     ~ Is_defined_in_eq x eq -> *)
  (*     stmt_eval (translate P) me ve (translate_eqn mems eq) (me', ve') -> *)
  (*     find_inst x me' = find_inst x me. *)
  (* Proof. *)
  (*   destruct eq; simpl; intros ** (* NIsDef *) StEval; *)
  (*     apply stmt_eval_Control_fwd in StEval; *)
  (*     destruct StEval as [(?& StEval)|(?&?&?)]; try congruence. *)
  (*   - now apply stmt_eval_translate_cexp_menv_inv in StEval as ->. *)
  (*   - inv StEval; apply find_inst_add_val. *)
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

  (* Lemma foo: *)
  (*   forall P S me ve me' ve' eqs eq mems inputs, *)
  (*     Memory_Corres_eq P S me eq -> *)
  (*     Is_well_sch inputs mems (eq :: eqs) -> *)
  (*     stmt_eval (translate P) me ve (translate_eqns mems eqs) (me', ve') -> *)
  (*     Memory_Corres_eq P S me' eq. *)
  (* Proof. *)
  (*   induction 1 as [|????? Spec|????? Spec|???????? Spec] *)
  (*                  (* |] *) *)
  (*                  (*   using Memory_Corres_eq_mult with (P_block := fun b S me => True) *); *)
  (*     try intros ** Wsch StEval; auto using Memory_Corres_eq. *)
  (*   - constructor. *)
  (*     intros ** Find; apply Spec in Find. *)
  (*     inv Wsch. *)
  (*     erewrite not_Is_defined_in_eqs_stmt_eval_menv_inv; *)
  (*       eauto using Is_defined_in_eq. *)
  (*   - constructor. *)
  (*     intros ** Sub; apply Spec in Sub. *)
  (*     admit. *)
  (*   - constructor. *)
  (*     intros ** Sub; apply Spec in Sub as (me'' &?&?). *)
  (*     exists me''; split; auto. *)
  (*     inv Wsch. *)
  (*   intros. *)

  (*   destruct eq. *)

  (* Admitted. *)


  (* Lemma equations_cons_correct: *)
  (*   forall eq eqs P R S I S' me ve me' ve' inputs mems, *)
  (*     (forall b S xs ys S' me, *)
  (*         sem_block P b S (map present xs) (map present ys) S' -> *)
  (*         me ≋ S -> *)
  (*         exists me', *)
  (*           stmt_call_eval (translate P) me b step xs me' ys *)
  (*           /\ me' ≋ S') -> *)
  (*     sem_equation P true R S I S' eq -> *)
  (*     Ordered_blocks P -> *)
  (*     Is_well_sch' inputs mems (eq :: eqs) -> *)
  (*     Memory_Corres_eqs eqs S I S' me' -> *)
  (*     (* equiv_env (fun x => Is_free_in_eqs x (eq :: eqs)) R mems me' ve' -> *) *)
  (*     stmt_eval (translate P) me ve (translate_eqns mems eqs) (me', ve') -> *)
  (*     exists me'' ve'', *)
  (*       stmt_eval (translate P) me ve (translate_eqns mems (eq :: eqs)) (me'', ve'') *)
  (*       /\ Memory_Corres_eqs (eq :: eqs) S I S' me'' *)
  (*       /\ equiv_env (fun x => Is_free_in_eqs x (eq :: eqs)) R mems me'' ve''. *)
  (* Proof. *)
  (*   intros ** WSCH Corres StEval. *)
  (*   assert (equiv_env (fun x => Is_free_in_eq x eq) R mems me' ve'). *)
  (*   { inversion_clear WSCH as [|??? FreeSpec]. *)
  (*     intros x v Free Hvar; apply FreeSpec in Free. *)
  (*     cases_eqn E. *)
  (*     - destruct Corres. erewrite not_Is_defined_in_eqs_stmt_eval_menv_inv; eauto. *)
  (*   edestruct equation_cons_correct as (me'' & ve'' &?&?); eauto. *)
  (*   exists me'', ve''; split; auto. *)
  (*   unfold translate_eqns; simpl; rewrite stmt_eval_fold_left_shift. *)
  (*   exists me', ve'; split; eauto using stmt_eval. *)
  (* Qed. *)

  Lemma value_corres_equal_memory:
    forall x S me,
      S ≋ me ->
      value_corres x S me.
  Proof.
    intros ** E; unfold value_corres; now rewrite E.
  Qed.

  Lemma state_corres_equal_memory:
    forall s S me,
      S ≋ me ->
      state_corres s S me.
  Proof.
    intros ** E; split; unfold sub_inst; intros ** Find;
      pose proof (find_inst_equal_memory s E) as E';
      rewrite Find in E'.
    - destruct (find_inst s me); try contradiction.
      exists m; intuition.
    - destruct (find_inst s S); try contradiction.
      exists m; intuition.
  Qed.

  Lemma Memory_Corres_eqs_empty_equal_memory:
    forall S I S' me,
      S ≋ me ->
      Memory_Corres_eqs [] S I S' me.
  Proof.
    split.
    - split; intros Last.
      + inv Last.
      + now apply value_corres_equal_memory.
    - split; [|split]; intros StpRst.
      + now apply state_corres_equal_memory.
      + destruct StpRst as (?& Rst); inv Rst.
      + inv StpRst.
  Qed.

  Lemma Is_well_sch_app:
    forall mems inputs eqs eqs',
      Is_well_sch mems inputs (eqs ++ eqs') ->
      Is_well_sch mems inputs eqs'.
  Proof.
    induction eqs; auto; simpl.
    inversion 1; auto.
  Qed.

  Lemma sem_equations_is_last_in:
    forall eqs P base R S I S' x v,
      Forall (sem_equation P base R S I S') eqs ->
      Is_last_in_eqs x eqs ->
      sem_var_instant R x (present v) ->
      find_val x S = Some v.
  Proof.
    induction eqs; inversion_clear 1 as [|?? Sem];
      inversion_clear 1 as [?? Last|]; eauto; intros.
    inv Last; inv Sem.
    cases; congruence.
  Qed.

  (* Lemma Memory_Corres_cons: *)
  (*   forall eqs eq S I S' me, *)
  (*     Memory_Corres_eqs (eq :: eqs) S I S' me -> *)
  (*     Memory_Corres_eqs eqs S I S' me. *)
  (* Proof. *)
  (*   intros ** (Lasts & Blocks); split. *)
  (*   - split; intros ** NLast. *)
  (*     + apply Lasts; right; auto.  *)
  (*     + destruct eq; try now apply Lasts; inversion_clear 1 as [?? Last|]; auto; inv Last. *)
  (*       destruct (ident_eq_dec x i). *)
  (*       subst. *)
  (*       apply Lasts.  *)
  (*       admit. *)
  (*       apply Lasts; inversion_clear 1 as [?? Last|]; auto; inv Last; congruence.   *)

  (*       destruct (Is_last_in_eqs_dec x eqs). *)
  (*       * admit. *)
  (*       * apply Lasts; setoid_rewrite Exists_app'; intros [|]; auto.   SearchAbout Exists app. *)

  (* Lemma translate_eqn_equiv_env_Is_free: *)
  (*   forall eq R mems me ve in_domain prog me' ve', *)
  (*     equiv_env in_domain R mems me ve -> *)
  (*     stmt_eval prog me ve (translate_eqn mems eq) (me', ve') -> *)
  (*     equiv_env (fun x => Is_variable_in_eq x eq \/ in_domain x) R mems me' ve'. *)
  (* Proof. *)
  (*   intros * Equiv StEval. *)
  (*   destruct eq; simpl in *; apply stmt_eval_Control_fwd in StEval. *)
  (*   - destruct StEval. *)
  (*     SearchAbout translate_cexp.  *)

  (*   SearchAbout Control.  *)

  Lemma not_Is_variable_in_eq_stmt_eval_env_inv:
    forall prog x eq me ve mems me' ve',
      ~ Is_variable_in_eq x eq ->
      stmt_eval prog me ve (translate_eqn mems eq) (me', ve') ->
      Env.find x ve' = Env.find x ve.
  Proof.
    intros ** Hnd Heval.
    destruct eq; simpl in Heval;
      apply stmt_eval_Control_fwd in Heval;
      destruct Heval as [[Hipi Heval]|[Habs [Hmenv Henv]]];
      subst; auto.
    - apply stmt_eval_translate_cexp_venv_inv in Heval as (?&?); subst.
      rewrite Env.gso; auto.
      intro; subst; apply Hnd; constructor.
    - inv Heval; auto.
    - inv Heval.
      rewrite Env.adds_nil_l; auto.
    - inv Heval.
      rewrite Env.find_In_gsso; auto.
      intro; apply Hnd; constructor; auto.
  Qed.

  Lemma equations_app_correct:
    forall eqs' eqs P R S I S' me ve inputs mems,
      (forall b S xs ys S' me,
          sem_block P b S (map present xs) (map present ys) S' ->
          me ≋ S ->
          exists me',
            stmt_call_eval (translate P) me b step xs me' ys
            /\ me' ≋ S') ->
      Forall (sem_equation P true R S I S') (eqs ++ eqs') ->
      Ordered_blocks P ->
      Is_well_sch inputs mems (eqs ++ eqs') ->
      (forall x, PS.In x mems -> Is_last_in_eqs x (eqs ++ eqs')) ->
      (forall x, In x inputs -> ~ Is_defined_in_eqs x (eqs ++ eqs')) ->
      (forall x c,
          In x inputs ->
          sem_var_instant R x (present c) ->
          Env.find x ve = Some c) ->
      me ≋ S ->
      exists me' ve',
        stmt_eval (translate P) me ve (translate_eqns mems eqs') (me', ve')
        /\ Memory_Corres_eqs eqs' S I S' me'
        /\ forall x c,
            Is_variable_in_eqs x eqs' ->
            sem_var_instant R x (present c) ->
            Env.find x ve' = Some c.
  Proof.
    induction eqs' as [|eq]; simpl;
      intros ** Heqs Ord Wsch SpecLast SpecInput EquivInput Corres.
    - exists me, ve. split; eauto using stmt_eval; split; auto.
      + now apply Memory_Corres_eqs_empty_equal_memory.
      + inversion 1.
    - pose proof Wsch as Wsch'; apply Is_well_sch_app in Wsch'.
      pose proof Heqs as Heqs'; apply Forall_app_weaken in Heqs'; inv Heqs'.
      rewrite List_shift_first in Wsch, Heqs, SpecLast, SpecInput.
      edestruct IHeqs' with (ve := ve) (me := me) as (me' & ve' &?&?&?); eauto.
      edestruct equation_cons_correct with (ve := ve') (me := me') as (me'' & ve'' &?&?&?);
        eauto using Is_well_sch.
      + intros x v Free Hvar.
        inversion_clear Wsch' as [|??? FreeSpec].
        apply FreeSpec in Free.
        cases_eqn E.
        * erewrite not_Is_defined_in_eqs_stmt_eval_menv_inv; eauto.
          rewrite Corres.
          eapply sem_equations_is_last_in in Heqs; eauto.
        * destruct Free as [|Input]; auto.
          assert (~ Is_defined_in_eqs x eqs')
            by (intro; eapply SpecInput, Exists_app; eauto).
          erewrite not_Is_defined_in_eqs_stmt_eval_venv_inv; eauto.
      + exists me'', ve''; split; [|split]; auto.
        * unfold translate_eqns; simpl.
          rewrite stmt_eval_fold_left_shift; setoid_rewrite Comp_Skip_right; eauto.
        * intros x v IsVar Hvar.
          destruct (Is_variable_in_eq_dec x eq) as [|Nvar]; auto.
          erewrite not_Is_variable_in_eq_stmt_eval_env_inv; eauto.
          inv IsVar; auto.
          contradiction.
  Qed.

  Lemma equations_correct:
    forall eqs P R S I S' me ve inputs mems,
      (forall b S xs ys S' me,
          sem_block P b S (map present xs) (map present ys) S' ->
          me ≋ S ->
          exists me',
            stmt_call_eval (translate P) me b step xs me' ys
            /\ me' ≋ S') ->
      Forall (sem_equation P true R S I S') eqs ->
      Ordered_blocks P ->
      Is_well_sch inputs mems eqs ->
      (forall x, PS.In x mems -> Is_last_in_eqs x eqs) ->
      (forall x, In x inputs -> ~ Is_defined_in_eqs x eqs) ->
      (forall x c,
          In x inputs ->
          sem_var_instant R x (present c) ->
          Env.find x ve = Some c) ->
      me ≋ S ->
      exists me' ve',
        stmt_eval (translate P) me ve (translate_eqns mems eqs) (me', ve')
        /\ Memory_Corres_eqs eqs S I S' me'
        /\ forall x c,
            Is_variable_in_eqs x eqs ->
            sem_var_instant R x (present c) ->
            Env.find x ve' = Some c.
  Proof.
    intros; eapply equations_app_correct with (eqs := []); eauto.
  Qed.

  Lemma Memory_Corres_eqs_equal_memory:
    forall P R eqs S I S' me lasts blocks,
      Memory_Corres_eqs eqs S I S' me ->
      Forall (sem_equation P true R S I S') eqs ->
      state_closed S lasts blocks ->
      state_closed S' lasts blocks ->
      (forall x, In x lasts <-> Is_last_in_eqs x eqs) ->
      (forall s, In s blocks <-> exists k, Is_state_in_eqs s k eqs) ->
      (forall s, Reset_in s eqs -> Step_in s eqs) ->
      me ≋ S'.
  Proof.
    intros ** (Lasts & Insts) Heqs Closed Closed' SpecLast SpecInst WSCH.
    split.
    - intro x; destruct (Is_last_in_eqs_dec x eqs) as [Last|Nlast].
      + apply Lasts in Last; auto.
      + assert (find_val x S = None).
        { apply not_Some_is_None; intros ** Find;
            apply Nlast, SpecLast, Closed.
          apply not_None_is_Some; eauto.
        }
        assert (find_val x S' = None) as E'.
        { apply not_Some_is_None; intros ** Find;
            apply Nlast, SpecLast, Closed'.
          apply not_None_is_Some; eauto.
        }
        unfold value_corres, find_val in *.
        apply Lasts in Nlast.
        rewrite E'; rewrite <-Nlast; auto.
    - split.
      + setoid_rewrite Env.In_find; intro s.
        destruct (Step_in_dec s eqs) as [Step|Nstep].
        *{ apply Insts in Step as (Inst & Inst').
           unfold sub_inst, find_inst in *; split; intros (?&?).
           - edestruct Inst' as (?&?&?); eauto.
           - edestruct Inst as (?&?&?); eauto.
         }
        *{ destruct (Reset_in_dec s eqs) as [Rst|Nrst].
           - apply WSCH in Rst; contradiction.
           - assert (~ exists k, Is_state_in_eqs s k eqs) as Nstate.
             { intros (?& State).
               apply Exists_exists in State as (?&?& State).
               inv State.
               - apply Nrst, Exists_exists; eauto using Is_state_in_eq.
               - apply Nstep, Exists_exists; eauto using Is_state_in_eq.
             }
             assert (state_corres s S me) as (?& Inst') by (apply Insts; auto).
             assert (find_inst s S = None).
             { apply not_Some_is_None; intros ** Find;
                 apply Nstate, SpecInst, Closed.
               apply not_None_is_Some; eauto.
             }
             assert (find_inst s S' = None) as E'.
             { apply not_Some_is_None; intros ** Find;
                 apply Nstate, SpecInst, Closed'.
               apply not_None_is_Some; eauto.
             }
             unfold sub_inst in *.
             assert (find_inst s me = None) as E.
             { apply not_Some_is_None; intros ** Find;
                 apply Inst' in Find as (?&?&?).
               congruence.
             }
             setoid_rewrite E'; setoid_rewrite E; reflexivity.
         }
      + setoid_rewrite Env.Props.P.F.find_mapsto_iff.
        intros s me_s Ss' Find Find'.
        destruct (Step_in_dec s eqs) as [Step|Nstep].
        * apply Insts in Step as (Inst).
          unfold sub_inst, find_inst in *.
          apply Inst in Find' as (?& Find' &?).
          rewrite Find' in Find; inv Find; auto.
        *{ destruct (Reset_in_dec s eqs) as [Rst|Nrst].
           - apply WSCH in Rst; contradiction.
           - assert (~ (Step_in s eqs \/ Reset_in s eqs)) as NstpRst by tauto.
             assert (~ exists k, Is_state_in_eqs s k eqs) as Nstate.
             { intros (?& State).
               apply Exists_exists in State as (?&?& State).
               inv State.
               - apply Nrst, Exists_exists; eauto using Is_state_in_eq.
               - apply Nstep, Exists_exists; eauto using Is_state_in_eq.
             }
             exfalso.
             apply Nstate, SpecInst, Closed'.
             apply not_None_is_Some; eauto.
         }
  Qed.

  Lemma ps_from_list_In:
    forall xs x,
      PS.In x (ps_from_list xs) -> In x xs.
  Proof.
    induction xs; simpl.
    - apply not_In_empty.
    - intros ** Hin.
      rewrite <-add_ps_from_list_cons in Hin.
      apply PSE.MP.Dec.F.add_iff in Hin as []; auto.
  Qed.

  (* Lemma Is_defined_not_Is_last_Is_variable_in_eqs: *)
  (*   forall eqs x, *)
  (*     Is_defined_in_eqs x eqs -> *)
  (*     ~ Is_last_in_eqs x eqs -> *)
  (*     Is_variable_in_eqs x eqs. *)
  (* Proof. *)
  (*   induction eqs; inversion_clear 1 as [?? Def|Def]; intros NLast. *)
  (*   - inv Def. *)
  (*     + left; constructor; auto. *)
  (*     + exfalso; apply NLast. *)
  (*       left; constructor; auto. *)
  (*     + left; constructor; auto. *)
  (*   - right; apply IHeqs; auto. *)
  (*     intro; apply NLast; right; auto. *)
  (* Qed. *)

  Theorem correctness:
    forall P b S xs ys S' me,
      Ordered_blocks P ->
      sem_block P b S (map present xs) (map present ys) S' ->
      me ≋ S ->
      exists me',
        stmt_call_eval (translate P) me b step xs me' ys
        /\ me' ≋ S'.
  Proof.
    induction P as [|block]; intros ** Ord Sem E;
      inversion_clear Sem as [?????????? Clock Find ? Outs ???? Heqs]; try now inv Find.
    pose proof Find as Find'.
    simpl in Find.
    destruct (ident_eqb (b_name block) b) eqn: Eq.
    - inv Find.
      assert (Is_well_sch (map fst (b_in bl)) (ps_from_list (map fst (b_lasts bl))) (b_eqs bl)) by admit.
      assert (base = true) by (apply Clock; rewrite present_list_spec; eauto); subst.
      apply sem_equations_cons in Heqs; auto.
      + inv Ord.
        edestruct equations_correct with (ve := Env.adds (map fst (m_in (step_method bl))) xs vempty)
          as (me' & ve' &?&?& Equiv); eauto.
        * intros; apply b_lasts_in_eqs, fst_InMembers, ps_from_list_In; auto.
        * intros; apply b_ins_not_def, fst_InMembers; auto.
        *{ intros ** Hin Hvar; apply Env.In_find_adds; simpl.
           - pose proof (b_nodup bl) as Nodup.
             apply NoDup_app_weaken in Nodup; auto.
           - eapply Forall2_in_left_combine in Hin; eauto.
             destruct Hin as (?& Hin &?); eapply sem_var_instant_det in Hvar; eauto.
             subst; rewrite combine_map_snd, in_map_iff in Hin.
             destruct Hin as ((?&?)& E' &?); inv E'; auto.
         }
         *{ exists me'; split.
            - apply find_block_translate in Find' as (?&?&?&?&?); subst.
              econstructor; eauto.
              + apply exists_step_method.
              + eauto.
              + simpl.
                unfold sem_vars_instant in Outs; rewrite Forall2_map_2 in Outs.
                apply Forall2_forall in Outs as (Outs & Length).
                apply Forall2_forall; split; auto.
                intros ** Hin.
                apply Equiv; auto.
                apply b_vars_out_in_eqs, InMembers_app.
                right; apply in_combine_l, fst_InMembers in Hin; auto.
            - eapply Memory_Corres_eqs_equal_memory; eauto.
              + setoid_rewrite <-fst_InMembers; apply b_lasts_in_eqs.
              + setoid_rewrite <-fst_InMembers; apply b_states_in_eqs.
              + apply b_no_single_reset.
          }
      + eapply find_block_not_Is_block_in; eauto.
    - apply sem_equations_cons in Heqs; auto.
      + inv Ord.
        edestruct IHP as (me' &?&?); eauto using sem_block.
        exists me'; split; auto.
        apply stmt_call_eval_cons; auto.
        simpl; apply ident_eqb_neq; auto.
      + eapply find_block_later_not_Is_block_in; eauto.
  Qed.

End CORRECTNESS.
