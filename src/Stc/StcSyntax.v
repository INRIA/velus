From Velus Require Import Common.
From Velus Require Import CommonProgram.
From Velus Require Import Operators.
From Velus Require Import CoreExpr.CESyntax.
From Velus Require Import Clocks.

From Coq Require Import Permutation.
From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Module Type STCSYNTAX
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks   : CLOCKS        Ids Op OpAux)
       (Import CESyn : CESYNTAX      Ids Op OpAux Cks).

  (** ** Transition constraints *)

  Inductive resetconstr :=
  | ResState    : ident -> type -> const -> resetconstr
  | ResInst     : ident -> ident -> resetconstr.

  Inductive updateconstr :=
  | UpdLast     : ident -> cexp -> updateconstr
  | UpdNext     : ident -> exp -> updateconstr
  | UpdInst     : ident -> list ident -> ident -> list exp -> updateconstr.

  Inductive trconstr :=
  | TcDef       : clock -> ident -> rhs -> trconstr
  | TcReset     : clock -> resetconstr -> trconstr
  | TcUpdate    : clock -> list clock -> updateconstr -> trconstr.

  Definition variables_tc (tc: trconstr): list ident :=
    match tc with
    | TcDef _ x _ => [x]
    | TcUpdate _ _ (UpdInst _ xs _ _) => xs
    | _ => []
    end.

  Definition variables := flat_map variables_tc.

  Inductive Is_reset_state_in_tc: ident -> clock -> trconstr -> Prop :=
    ResetTcReset:
      forall x ck ty ro,
        Is_reset_state_in_tc x ck (TcReset ck (ResState x ty ro)).

  Definition Is_reset_state_in (x: ident) (ck: clock) (tcs: list trconstr) : Prop :=
    Exists (Is_reset_state_in_tc x ck) tcs.

  Inductive Last_with_reset_in_tc: ident -> list clock -> trconstr -> Prop :=
  | Last_with_reset_in_tc_intro:
      forall x ck ckrs e,
        Last_with_reset_in_tc x ckrs (TcUpdate ck ckrs (UpdLast x e)).
  Global Hint Constructors Last_with_reset_in_tc : stcsyntax.

  Definition Last_with_reset_in (s: ident) (ckrs: list clock) (tcs: list trconstr) : Prop :=
    Exists (Last_with_reset_in_tc s ckrs) tcs.

  Definition last_consistency (tcs: list trconstr) : Prop :=
    forall s ckrs,
      Last_with_reset_in s ckrs tcs ->
      (forall ckr, In ckr ckrs <-> Is_reset_state_in s ckr tcs).

  Inductive Next_with_reset_in_tc: ident -> list clock -> trconstr -> Prop :=
  | Next_with_reset_in_tc_intro:
      forall x ck ckrs e,
        Next_with_reset_in_tc x ckrs (TcUpdate ck ckrs (UpdNext x e)).
  Global Hint Constructors Next_with_reset_in_tc : stcsyntax.

  Definition Next_with_reset_in (s: ident) (ckrs: list clock) (tcs: list trconstr) : Prop :=
    Exists (Next_with_reset_in_tc s ckrs) tcs.

  Definition next_consistency (tcs: list trconstr) : Prop :=
    forall s ckrs,
      Next_with_reset_in s ckrs tcs ->
      (forall ckr, In ckr ckrs <-> Is_reset_state_in s ckr tcs).

  Inductive Is_reset_inst_in_tc: ident -> clock -> trconstr -> Prop :=
  | SubTcReset:
      forall s ck b,
        Is_reset_inst_in_tc s ck (TcReset ck (ResInst s b)).

  Definition Is_reset_inst_in (s: ident) (ck : clock) := Exists (Is_reset_inst_in_tc s ck).

  Inductive Is_update_inst_in_tc: ident -> trconstr -> Prop :=
  | SubTcUpd:
      forall s xs ck ckrs b es,
        Is_update_inst_in_tc s (TcUpdate ck ckrs (UpdInst s xs b es)).

  Definition Is_update_inst_in (s: ident) := Exists (Is_update_inst_in_tc s).

  Inductive Inst_with_reset_in_tc: ident -> list clock -> trconstr -> Prop :=
    Inst_with_reset_in_tc_intro:
      forall s ck ckrs ys f es,
        Inst_with_reset_in_tc s ckrs (TcUpdate ck ckrs (UpdInst s ys f es)).
  Global Hint Constructors Inst_with_reset_in_tc : stcsyntax.

  Definition Inst_with_reset_in (s: ident) (ckrs: list clock) (tcs: list trconstr) : Prop :=
    Exists (Inst_with_reset_in_tc s ckrs) tcs.

  Definition inst_consistency (tcs: list trconstr) : Prop :=
    forall s ckrs,
      Inst_with_reset_in s ckrs tcs ->
      (forall ckr, In ckr ckrs <-> Is_reset_inst_in s ckr tcs).

  Fixpoint state_resets_of (tcs: list trconstr) : list ident :=
    match tcs with
    | [] => []
    | TcReset ck (ResState x _ _) :: tcs => x :: (state_resets_of tcs)
    | _ :: tcs => state_resets_of tcs
    end.

  Fixpoint lasts_of (tcs: list trconstr) : list (ident * type) :=
    match tcs with
    | [] => []
    | TcUpdate _ _ (UpdLast x e) :: tcs => (x, typeofc e) :: (lasts_of tcs)
    | _ :: tcs => lasts_of tcs
    end.

  Fixpoint nexts_of (tcs: list trconstr) : list (ident * type) :=
    match tcs with
    | [] => []
    | TcUpdate _ _ (UpdNext x e) :: tcs => (x, typeof e) :: (nexts_of tcs)
    | _ :: tcs => nexts_of tcs
    end.

  Fixpoint inst_resets_of (tcs: list trconstr) : list (ident * ident) :=
    match tcs with
    | [] => []
    | TcReset _ (ResInst s b) :: tcs => (s, b) :: inst_resets_of tcs
    | _ :: tcs => inst_resets_of tcs
    end.

  Fixpoint insts_of (tcs: list trconstr) : list (ident * ident) :=
    match tcs with
    | [] => []
    | TcUpdate _ _ (UpdInst s _ b _) :: tcs => (s, b) :: insts_of tcs
    | _ :: tcs => insts_of tcs
    end.

  Definition mems_of_states {A B C} : list (ident * (A * B * C)) -> list (ident * B) :=
    map (fun x => (fst x, snd (fst (snd x)))).

  Record system {prefs: PS.t} :=
    System {
        s_name   : ident;                           (* name *)
        s_in     : list (ident * (type * clock));   (* inputs *)
        s_vars   : list (ident * (type * clock));   (* local variables *)
        s_lasts  : list (ident * (const * type * clock));  (* last state variables *)
        s_nexts  : list (ident * (const * type * clock));  (* next state variables *)
        s_subs   : list (ident * ident);            (* sub-instances *)
        s_out    : list (ident * (type * clock));   (* outputs *)
        s_tcs    : list trconstr;                   (* transition constraints *)

        s_ingt0            : 0 < length s_in;

        s_nodup            : NoDup (map fst s_in ++ map fst s_vars ++ map fst s_out ++ map fst s_lasts ++ map fst s_nexts);
        s_nodup_states_subs: NoDup (map fst s_lasts ++ map fst s_nexts ++ map fst s_subs);

        s_vars_out_in_tcs  : Permutation (map fst s_vars ++ map fst s_out) (variables s_tcs);

        s_lasts_in_tcs     : Permutation (map fst s_lasts) (map fst (lasts_of s_tcs));
        s_last_consistency : last_consistency s_tcs;

        s_nexts_in_tcs     : Permutation (map fst s_nexts) (map fst (nexts_of s_tcs));
        s_next_consistency : next_consistency s_tcs;

        s_state_reset_incl  : incl (state_resets_of s_tcs) (map fst (lasts_of s_tcs++nexts_of s_tcs));

        s_subs_in_tcs      : forall f, In f (map snd s_subs)
                                  <-> In f (map snd (insts_of s_tcs ++ inst_resets_of s_tcs));
        s_subs_insts_of    : Permutation s_subs (insts_of s_tcs);
        s_inst_consistency: inst_consistency s_tcs;
        s_inst_reset_incl  : incl (inst_resets_of s_tcs) (insts_of s_tcs);

        s_good             : Forall (AtomOrGensym prefs) (map fst (s_in ++ s_vars ++ s_out))
                             /\ Forall (AtomOrGensym prefs) (map fst s_lasts)
                             /\ Forall (AtomOrGensym prefs) (map fst s_nexts)
                             /\ Forall (AtomOrGensym prefs) (map fst s_subs)
                             /\ atom s_name
      }.

  Global Instance system_unit {prefs} : ProgramUnit (@system prefs) :=
    { name := s_name; }.

  Global Instance system_state_unit {prefs} : ProgramStateUnit (@system prefs) type :=
    { state_variables := fun s => mems_of_states (s_lasts s ++ s_nexts s);
      instance_variables := s_subs }.

  Lemma inst_in_Inst_with_reset_in:
    forall tcs s,
      Is_update_inst_in s tcs ->
      exists rst, Inst_with_reset_in s rst tcs.
  Proof.
    induction 1 as [?? Step|].
    - inv Step. exists ckrs; left; constructor.
    - destruct IHExists.
      eexists; right; eauto.
  Qed.

  Lemma inst_in_insts_of:
    forall tcs s,
      Is_update_inst_in s tcs <-> InMembers s (insts_of tcs).
  Proof.
    induction tcs as [|tc]; simpl.
    - split; inversion 1.
    - intros.
      unfold Is_update_inst_in in *.
      rewrite Exists_cons, IHtcs.
      cases; intuition; try take (Is_update_inst_in_tc _ _) and inv it.
      + constructor; auto.
      + now right.
      + take (InMembers _ _) and inv it; auto.
        left; constructor.
  Qed.

  Lemma s_nodup_lasts {prefs}:
    forall (b: @system prefs), NoDupMembers b.(s_lasts).
  Proof.
    intro; pose proof (s_nodup b) as Nodup.
    apply fst_NoDupMembers.
    solve_NoDup_app.
  Qed.

  Lemma s_nodup_nexts {prefs}:
    forall (b: @system prefs), NoDupMembers b.(s_nexts).
  Proof.
    intro; pose proof (s_nodup b) as Nodup.
    apply fst_NoDupMembers.
    solve_NoDup_app.
  Qed.

  Lemma s_nodup_lasts_nexts {prefs}:
    forall (b: @system prefs), NoDupMembers (b.(s_lasts) ++ b.(s_nexts)).
  Proof.
    intro; pose proof (s_nodup b) as Nodup.
    apply fst_NoDupMembers.
    solve_NoDup_app.
  Qed.

  Lemma s_nodup_subs {prefs}:
    forall (b: @system prefs), NoDupMembers b.(s_subs).
  Proof.
    intro; pose proof (s_nodup_states_subs b) as Nodup.
    apply NoDup_app_r, NoDup_app_r in Nodup.
    apply fst_NoDupMembers; auto.
  Qed.

  Lemma s_nodup_vars {prefs}:
    forall (b: @system prefs), NoDupMembers (s_in b ++ s_vars b ++ s_out b).
  Proof.
    intro; pose proof (s_nodup b) as Nodup.
    rewrite 2 app_assoc in Nodup.
    apply NoDup_app_weaken in Nodup.
    rewrite <-2 map_app, <-app_assoc in Nodup.
    apply fst_NoDupMembers; auto.
  Qed.

  Lemma s_nodup_variables {prefs}:
    forall (b: @system prefs), NoDup (variables b.(s_tcs)).
  Proof.
    intro; rewrite <-s_vars_out_in_tcs, <-map_app.
    apply fst_NoDupMembers.
    eapply NoDupMembers_app_r, s_nodup_vars.
  Qed.

  Record program {prefs} :=
    Program {
        types : list type;
        externs : list (ident * (list ctype * ctype));
        systems : list (@system prefs)
      }.
  Arguments Program {_}.

  Global Program Instance program_program {prefs}: CommonProgram.Program (@system prefs) (@program prefs) :=
    { units := systems;
      update := fun p => Program p.(types) p.(externs) }.

  Definition find_system {prefs} : ident -> (@program prefs) -> option (system * program) :=
    find_unit.

  Remark find_system_other {prefs}:
    forall b P (bl: @system prefs) types externs,
      bl.(s_name) <> b ->
      find_system b (Program types externs (bl :: P)) = find_system b (Program types externs P).
  Proof.
    intros; eapply find_unit_other; simpl; eauto.
    intro; auto.
  Qed.

  Lemma Inst_with_reset_in_Is_update_inst_in:
    forall tcs s rst,
      Inst_with_reset_in s rst tcs ->
      Is_update_inst_in s tcs.
  Proof.
    induction 1 as [?? Step|].
    - inv Step; left; constructor.
    - right; auto.
  Qed.

  Lemma Last_with_reset_in_cons_not_last:
    forall tcs tc s rst,
      (forall s ck ckrs e, tc <> TcUpdate ck ckrs (UpdLast s e)) ->
      (Last_with_reset_in s rst (tc :: tcs) <-> Last_with_reset_in s rst tcs).
  Proof.
    intros * Neq; split.
    - inversion_clear 1 as [?? Step|]; auto.
      inv Step; exfalso; eapply Neq; eauto.
    - right; auto.
  Qed.

  Lemma Next_with_reset_in_cons_not_next:
    forall tcs tc s rst,
      (forall s ck ckrs e, tc <> TcUpdate ck ckrs (UpdNext s e)) ->
      (Next_with_reset_in s rst (tc :: tcs) <-> Next_with_reset_in s rst tcs).
  Proof.
    intros * Neq; split.
    - inversion_clear 1 as [?? Step|]; auto.
      inv Step; exfalso; eapply Neq; eauto.
    - right; auto.
  Qed.

  Lemma Inst_with_reset_in_cons_not_step:
    forall tcs tc s rst,
      (forall s ck ckrs ys f es, tc <> TcUpdate ck ckrs (UpdInst s ys f es)) ->
      (Inst_with_reset_in s rst (tc :: tcs) <-> Inst_with_reset_in s rst tcs).
  Proof.
    intros * Neq; split.
    - inversion_clear 1 as [?? Step|]; auto.
      inv Step; exfalso; eapply Neq; eauto.
    - right; auto.
  Qed.

  Lemma insts_of_In':
    forall tcs s b,
      In (s, b) (insts_of tcs) ->
      exists xs ck ckrs es, In (TcUpdate ck ckrs (UpdInst s xs b es)) tcs.
  Proof.
    induction tcs as [|[]]; simpl; try contradiction; intros * Hin;
      try now edestruct IHtcs as (?&?&?&?&?); eauto 6.
    cases; [| |destruct Hin as [E|]].
    1,2,4:edestruct IHtcs as (?&?&?&?&?); eauto 6.
    inv E; eauto 6.
  Qed.

  Lemma inst_resets_of_app:
    forall tcs tcs',
      inst_resets_of (tcs ++ tcs') = inst_resets_of tcs ++ inst_resets_of tcs'.
  Proof.
    induction tcs as [|[]]; intros; simpl; cases; simpl; try f_equal; auto.
  Qed.

  Definition is_update_inst_in_tc_b (s: ident) (tc: trconstr) : bool :=
    match tc with
    | TcUpdate _ _ (UpdInst s' _ _ _) => ident_eqb s s'
    | _ => false
    end.

  Definition is_update_inst_in_tcs_b (s: ident) (tcs: list trconstr) : bool :=
    existsb (is_update_inst_in_tc_b s) tcs.

  Definition is_reset_inst_in_tc_b (s: ident) (ck: clock) (tc: trconstr) : bool :=
    match tc with
    | TcReset ck' (ResInst s' _) => ident_eqb s s' && clock_eq ck ck'
    | _ => false
    end.

  Definition is_reset_inst_in_tcs_b (s: ident) (ck: clock) (tcs: list trconstr) : bool :=
    existsb (is_reset_inst_in_tc_b s ck) tcs.

  Fact is_update_inst_in_tc_reflect:
    forall s tc,
      Is_update_inst_in_tc s tc <-> is_update_inst_in_tc_b s tc = true.
  Proof.
    destruct tc; simpl; cases; simpl; split;
      try discriminate; try now inversion 1.
    - inversion_clear 1; apply ident_eqb_refl.
    - rewrite ident_eqb_eq; intros; subst; constructor.
  Qed.

  Corollary is_update_inst_in_reflect:
    forall s tcs,
      Is_update_inst_in s tcs <-> is_update_inst_in_tcs_b s tcs = true.
  Proof.
    setoid_rewrite existsb_exists; setoid_rewrite Exists_exists.
    split; intros (?&?& Step); apply is_update_inst_in_tc_reflect in Step; eauto.
  Qed.

  Lemma Is_update_inst_in_dec:
    forall s tcs,
      { Is_update_inst_in s tcs } + { ~ Is_update_inst_in s tcs }.
  Proof.
    intros;
      eapply Bool.reflect_dec, Bool.iff_reflect, is_update_inst_in_reflect.
  Qed.

  Fact Is_reset_inst_in_tc_reflect:
    forall s ck tc,
      Is_reset_inst_in_tc s ck tc <-> is_reset_inst_in_tc_b s ck tc = true.
  Proof.
    destruct tc; simpl; cases; simpl; split;
      try discriminate; try now inversion 1.
    - inversion_clear 1.
      rewrite Bool.andb_true_iff; split.
      apply ident_eqb_refl.
      rewrite clock_eq_spec; auto.
    - rewrite Bool.andb_true_iff, ident_eqb_eq, clock_eq_spec.
      intros (?&?); subst; constructor.
  Qed.

  Corollary Is_reset_inst_in_reflect:
    forall s ck tcs,
      Is_reset_inst_in s ck tcs <-> is_reset_inst_in_tcs_b s ck tcs = true.
  Proof.
    setoid_rewrite existsb_exists; setoid_rewrite Exists_exists.
    split; intros (?&?& Step); apply Is_reset_inst_in_tc_reflect in Step; eauto.
  Qed.

  Lemma Is_reset_inst_in_dec:
    forall s ck tcs,
      { Is_reset_inst_in s ck tcs } + { ~ Is_reset_inst_in s ck tcs }.
  Proof.
    intros;
      eapply Bool.reflect_dec, Bool.iff_reflect, Is_reset_inst_in_reflect.
  Qed.

  Lemma variables_app:
    forall tcs tcs',
      variables (tcs ++ tcs') = variables tcs ++ variables tcs'.
  Proof.
    unfold variables.
    induction tcs as [|[]]; simpl; intros; auto with datatypes.
    - rewrite <-app_assoc; f_equal; auto.
  Qed.

  Lemma insts_of_app:
    forall tcs tcs',
      insts_of (tcs ++ tcs') = insts_of tcs ++ insts_of tcs'.
  Proof.
    unfold insts_of.
    induction tcs as [|[]]; simpl; cases; simpl; intros; auto with datatypes.
  Qed.

  Lemma state_resets_of_app:
    forall tcs tcs',
      state_resets_of (tcs ++ tcs') = state_resets_of tcs ++ state_resets_of tcs'.
  Proof.
    induction tcs as [|[]]; simpl; cases; simpl; auto; setoid_rewrite IHtcs; auto.
  Qed.

  Lemma lasts_of_app:
    forall tcs tcs',
      lasts_of (tcs ++ tcs') = lasts_of tcs ++ lasts_of tcs'.
  Proof.
    induction tcs as [|[]]; simpl; cases; simpl; auto; setoid_rewrite IHtcs; auto.
  Qed.

  Lemma nexts_of_app:
    forall tcs tcs',
      nexts_of (tcs ++ tcs') = nexts_of tcs ++ nexts_of tcs'.
  Proof.
    induction tcs as [|[]]; simpl; cases; simpl; auto; setoid_rewrite IHtcs; auto.
  Qed.

  Lemma reset_insts_of_In:
    forall x tcs,
      (exists ck, Is_reset_inst_in x ck tcs) <-> In x (map fst (inst_resets_of tcs)).
  Proof.
    induction tcs as [|[]]; simpl; cases; simpl; intros.
    - setoid_rewrite Exists_nil.
      split; [intros (?&?)|intros ?]; eauto using Cbase.
    - setoid_rewrite <-IHtcs.
      split; intros (ck&?); exists ck; try right; eauto.
      inversion_clear H as [?? Reset|]; try inv Reset; auto.
    - setoid_rewrite <-IHtcs; split; intros (ck&?); exists ck; try right; eauto.
      inversion_clear H as [?? Reset|]; try inv Reset; auto.
    - setoid_rewrite <-IHtcs; split.
      + intros (?&H). inversion_clear H as [?? Reset|]; try inv Reset; eauto.
      + intros [E|(ck&?)]; subst.
        * exists c; left; constructor.
        * exists ck; right; auto.
    - setoid_rewrite <-IHtcs; split; intros (ck&?); exists ck; try right; eauto.
      inversion_clear H as [?? Reset|]; try inv Reset; auto.
  Qed.

  Lemma insts_of_In:
    forall x tcs,
      Is_update_inst_in x tcs <-> In x (map fst (insts_of tcs)).
  Proof.
    induction tcs as [|[]]; simpl; cases; simpl.
    all:try now (setoid_rewrite <-IHtcs; split; try right; auto;
                 inversion_clear 1 as [?? Last|]; try inv Last; auto).
    - now setoid_rewrite Exists_nil.
    - setoid_rewrite <-IHtcs; split.
      + inversion_clear 1 as [?? Last|]; try inv Last; auto.
      + intros [E|?].
        * subst; left; constructor.
        * right; auto.
  Qed.

  Lemma mems_of_states_fst:
    forall {A B C} (lasts : list (ident * (A * B * C))),
      map fst (mems_of_states lasts) = map fst lasts.
  Proof.
    induction lasts; simpl; auto; f_equal; auto.
  Qed.

  (** * IsVariable inductive *)

  Inductive Is_variable_in_tc: ident -> trconstr -> Prop :=
  | VarTcDef:
      forall ck x e,
        Is_variable_in_tc x (TcDef ck x e)
  | VarTcStep:
      forall x ck ckrs i xs f es,
        In x xs ->
        Is_variable_in_tc x (TcUpdate ck ckrs (UpdInst i xs f es)).

  Global Hint Constructors Is_variable_in_tc : stcdef.

  Definition Is_variable_in (x: ident) (tcs: list trconstr) : Prop :=
    Exists (Is_variable_in_tc x) tcs.

  Lemma Is_variable_in_tc_variables_tc:
    forall tc x,
      Is_variable_in_tc x tc <-> In x (variables_tc tc).
  Proof.
    unfold variables.
    intros *; destruct tc; simpl; cases; simpl; split; intro H; try inv H; auto.
    - constructor.
    - inv H0.
    - constructor; auto.
  Qed.

  Corollary Is_variable_in_variables:
    forall tcs x,
      Is_variable_in x tcs <-> In x (variables tcs).
  Proof.
    unfold variables.
    induction tcs; simpl.
    - split; try contradiction; inversion 1.
    - intro; setoid_rewrite Exists_cons.
      rewrite in_app, Is_variable_in_tc_variables_tc, <-IHtcs.
      tauto.
  Qed.

  Definition is_variable_in_tc_b (x: ident) (tc: trconstr) : bool :=
    match tc with
    | TcDef _ x' _ => ident_eqb x x'
    | TcUpdate _ _ (UpdInst _ xs _ _) => existsb (ident_eqb x) xs
    | _ => false
    end.

  Fact Is_variable_in_tc_reflect:
    forall x tc,
      Is_variable_in_tc x tc <-> is_variable_in_tc_b x tc = true.
  Proof.
    destruct tc; simpl; cases; simpl; split;
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

  Lemma Is_variable_in_tc_dec:
    forall x tc,
      { Is_variable_in_tc x tc } + { ~ Is_variable_in_tc x tc }.
  Proof.
    intros;
      eapply Bool.reflect_dec, Bool.iff_reflect, Is_variable_in_tc_reflect.
  Qed.

  Lemma not_Is_variable_in_cons:
    forall x tc tcs,
      ~ Is_variable_in x (tc :: tcs)
      <-> ~ Is_variable_in_tc x tc /\ ~ Is_variable_in x tcs.
  Proof.
    split.
    - intro Hndef; split; intro His_def;
        eapply Hndef; now constructor.
    - intros [Hdef_tc Hdef_tcs] Hdef_all.
      inv Hdef_all; eauto.
  Qed.

  Lemma s_ins_not_var {prefs}:
    forall (s: @system prefs) x,
      InMembers x s.(s_in) ->
      ~ Is_variable_in x s.(s_tcs).
  Proof.
    intros * Hin Hvar.
    rewrite Is_variable_in_variables, <- s_vars_out_in_tcs in Hvar.
    pose proof (s_nodup s) as Nodup.
    eapply (NoDup_app_In x) in Nodup.
    - apply Nodup; rewrite app_assoc, in_app.
      repeat rewrite in_app_iff in *.
      destruct Hvar; auto.
    - apply fst_InMembers; auto.
  Qed.

  (** * IsLast inductive *)

  Inductive Is_update_last_in_tc: ident -> trconstr -> Prop :=
  | LastTcLast:
      forall x ck ckrs e,
        Is_update_last_in_tc x (TcUpdate ck ckrs (UpdLast x e)).

  Definition Is_update_last_in (x : ident) (tcs : list trconstr) :=
    Exists (Is_update_last_in_tc x) tcs.

  Lemma not_Is_update_last_in_cons:
    forall x tc tcs,
      ~ Is_update_last_in x (tc :: tcs) <-> ~ Is_update_last_in_tc x tc /\ ~ Is_update_last_in x tcs.
  Proof.
    split; intros HH.
    - split; intro; apply HH; unfold Is_update_last_in; intuition.
    - destruct HH; inversion_clear 1; intuition.
  Qed.

  Lemma last_of_In:
    forall x tc,
      Is_update_last_in_tc x tc <-> In x (map fst (lasts_of [tc])).
  Proof.
    destruct tc; simpl; cases; simpl; split; intros H; inv H; auto using Is_update_last_in_tc.
    inv H0.
  Qed.

  Lemma lasts_of_In:
    forall x tcs,
      Is_update_last_in x tcs <-> In x (map fst (lasts_of tcs)).
  Proof.
    induction tcs as [|[]]; simpl; cases; simpl.
    all:try now (setoid_rewrite <-IHtcs; split; try right; auto;
                 inversion_clear 1 as [?? Last|]; try inv Last; auto).
    - now setoid_rewrite Exists_nil.
    - setoid_rewrite <-IHtcs; split.
      + inversion_clear 1 as [?? Last|]; try inv Last; auto.
      + intros [E|?].
        * subst; left; constructor.
        * right; auto.
  Qed.

  Definition is_update_last_in_tc_b (x: ident) (tc: trconstr) : bool :=
    match tc with
    | TcUpdate _ _ (UpdLast y _) => ident_eqb x y
    | _ => false
    end.

  Definition is_update_last_in_b (x: ident) (tcs: list trconstr) : bool :=
    existsb (is_update_last_in_tc_b x) tcs.

  Fact Is_update_last_in_tc_reflect:
    forall x tc,
      Is_update_last_in_tc x tc <-> is_update_last_in_tc_b x tc = true.
  Proof.
    destruct tc; simpl; cases; simpl; split;
      try discriminate; try now inversion 1.
    - inversion_clear 1; apply ident_eqb_refl.
    - rewrite ident_eqb_eq; intro; subst; constructor.
  Qed.

  Corollary Is_update_last_in_reflect:
    forall x tcs,
      Is_update_last_in x tcs <-> is_update_last_in_b x tcs = true.
  Proof.
    setoid_rewrite existsb_exists; setoid_rewrite Exists_exists.
    split; intros (?&?& Last); apply Is_update_last_in_tc_reflect in Last; eauto.
  Qed.

  Lemma Is_update_last_in_dec:
    forall x tcs,
      { Is_update_last_in x tcs } + { ~ Is_update_last_in x tcs }.
  Proof.
    intros;
      eapply Bool.reflect_dec, Bool.iff_reflect, Is_update_last_in_reflect.
  Qed.

  Lemma not_Is_update_last_in_tc_TcLast:
    forall y x ck ckrs le,
      ~ Is_update_last_in_tc y (TcUpdate ck ckrs (UpdLast x le)) -> x <> y.
  Proof.
    intros * NIsLast E; subst; apply NIsLast ; auto using Is_update_last_in_tc.
  Qed.

  Lemma s_ins_not_last {prefs}:
    forall (s: @system prefs) x,
      InMembers x s.(s_in) ->
      ~ Is_update_last_in x s.(s_tcs).
  Proof.
    intros * Hin Hlast.
    pose proof (s_nodup s) as Nodup.
    eapply (NoDup_app_In x) in Nodup.
    - apply lasts_of_In in Hlast.
      rewrite <-s_lasts_in_tcs in Hlast.
      apply Nodup. repeat rewrite in_app_iff. auto.
    - apply fst_InMembers; auto.
  Qed.

  Lemma Last_with_reset_in_Is_update_last_in:
    forall tcs s rst,
      Last_with_reset_in s rst tcs ->
      Is_update_last_in s tcs.
  Proof.
    induction 1 as [?? Last|].
    - inv Last; left; constructor.
    - right; auto.
  Qed.

  (** * IsNext inductive *)

  Inductive Is_update_next_in_tc: ident -> trconstr -> Prop :=
  | NextTcNext:
      forall x ck ckrs e,
        Is_update_next_in_tc x (TcUpdate ck ckrs (UpdNext x e)).

  Definition Is_update_next_in (x : ident) (tcs : list trconstr) :=
    Exists (Is_update_next_in_tc x) tcs.

  Lemma not_Is_update_next_in_cons:
    forall x tc tcs,
      ~ Is_update_next_in x (tc :: tcs) <-> ~ Is_update_next_in_tc x tc /\ ~ Is_update_next_in x tcs.
  Proof.
    split; intros HH.
    - split; intro; apply HH; unfold Is_update_next_in; intuition.
    - destruct HH; inversion_clear 1; intuition.
  Qed.

  Lemma next_of_In:
    forall x tc,
      Is_update_next_in_tc x tc <-> In x (map fst (nexts_of [tc])).
  Proof.
    destruct tc; simpl; cases; simpl; split; intros H; inv H; auto using Is_update_next_in_tc.
    inv H0.
  Qed.

  Lemma nexts_of_In:
    forall x tcs,
      Is_update_next_in x tcs <-> In x (map fst (nexts_of tcs)).
  Proof.
    induction tcs as [|[]]; simpl; cases; simpl.
    all:try now (setoid_rewrite <-IHtcs; split; try right; auto;
                 inversion_clear 1 as [?? Next|]; try inv Next; auto).
    - now setoid_rewrite Exists_nil.
    - setoid_rewrite <-IHtcs; split.
      + inversion_clear 1 as [?? Next|]; try inv Next; auto.
      + intros [E|?].
        * subst; left; constructor.
        * right; auto.
  Qed.

  Definition is_update_next_in_tc_b (x: ident) (tc: trconstr) : bool :=
    match tc with
    | TcUpdate _ _ (UpdNext y _) => ident_eqb x y
    | _ => false
    end.

  Definition is_update_next_in_b (x: ident) (tcs: list trconstr) : bool :=
    existsb (is_update_next_in_tc_b x) tcs.

  Fact Is_update_next_in_tc_reflect:
    forall x tc,
      Is_update_next_in_tc x tc <-> is_update_next_in_tc_b x tc = true.
  Proof.
    destruct tc; simpl; cases; simpl; split;
      try discriminate; try now inversion 1.
    - inversion_clear 1; apply ident_eqb_refl.
    - rewrite ident_eqb_eq; intro; subst; constructor.
  Qed.

  Corollary Is_update_next_in_reflect:
    forall x tcs,
      Is_update_next_in x tcs <-> is_update_next_in_b x tcs = true.
  Proof.
    setoid_rewrite existsb_exists; setoid_rewrite Exists_exists.
    split; intros (?&?& Next); apply Is_update_next_in_tc_reflect in Next; eauto.
  Qed.

  Lemma Is_update_next_in_dec:
    forall x tcs,
      { Is_update_next_in x tcs } + { ~ Is_update_next_in x tcs }.
  Proof.
    intros;
      eapply Bool.reflect_dec, Bool.iff_reflect, Is_update_next_in_reflect.
  Qed.

  Lemma not_Is_update_next_in_tc_TcNext:
    forall y x ck ckrs le,
      ~ Is_update_next_in_tc y (TcUpdate ck ckrs (UpdNext x le)) -> x <> y.
  Proof.
    intros * NIsNext E; subst; apply NIsNext ; auto using Is_update_next_in_tc.
  Qed.

  Lemma s_ins_not_next {prefs}:
    forall (s: @system prefs) x,
      InMembers x s.(s_in) ->
      ~ Is_update_next_in x s.(s_tcs).
  Proof.
    intros * Hin Hnext.
    pose proof (s_nodup s) as Nodup.
    eapply (NoDup_app_In x) in Nodup.
    - apply nexts_of_In in Hnext.
      rewrite <-s_nexts_in_tcs in Hnext.
      apply Nodup. repeat rewrite in_app_iff. auto.
    - apply fst_InMembers; auto.
  Qed.

  Lemma Next_with_reset_in_Is_update_next_in:
    forall tcs s rst,
      Next_with_reset_in s rst tcs ->
      Is_update_next_in s tcs.
  Proof.
    induction 1 as [?? Next|].
    - inv Next; left; constructor.
    - right; auto.
  Qed.

  (** * IsResetLast inductive *)

  Lemma not_Is_reset_state_in_cons:
    forall x ck tc tcs,
      ~ Is_reset_state_in x ck (tc :: tcs) <-> ~ Is_reset_state_in_tc x ck tc /\ ~ Is_reset_state_in x ck tcs.
  Proof.
    split; intros HH.
    - split; intro; apply HH; unfold Is_reset_state_in; intuition.
    - destruct HH; inversion_clear 1; intuition.
  Qed.

  Lemma not_Is_reset_state_in_cons':
    forall x tc tcs,
      ~ (exists ck, Is_reset_state_in x ck (tc :: tcs)) <-> ~ (exists ck, Is_reset_state_in_tc x ck tc) /\ ~ (exists ck, Is_reset_state_in x ck tcs).
  Proof.
    split; intros HH.
    - split; intros (?&H); apply HH; unfold Is_reset_state_in; eauto.
    - destruct HH; intros (?&HH); inversion_clear HH; eauto.
  Qed.

  Lemma reset_state_of_In:
    forall x tc,
      (exists ck, Is_reset_state_in_tc x ck tc) <-> In x (state_resets_of [tc]).
  Proof.
    destruct tc; simpl; cases; simpl; (split; [intros (?&H)|intro H]); inv H; eauto using Is_reset_state_in_tc.
    inv H0.
  Qed.

  Lemma reset_states_of_In:
    forall tcs x,
      (exists ck, Is_reset_state_in x ck tcs) <-> In x (state_resets_of tcs).
  Proof.
    induction tcs as [|[]]; simpl; cases; simpl; intros.
    - setoid_rewrite Exists_nil.
      split; [intros (?&?)|intros ?]; eauto using Cbase.
    - setoid_rewrite <-IHtcs.
      split; intros (ck&?); exists ck; try right; eauto.
      inversion_clear H as [?? Reset_State|]; try inv Reset_State; auto.
    - setoid_rewrite <-IHtcs; split.
      + intros (?&H). inversion_clear H as [?? Reset_State|]; try inv Reset_State; eauto.
      + intros [E|(ck&?)]; subst.
        * exists c; left; constructor.
        * exists ck; right; auto.
    - setoid_rewrite <-IHtcs; split; intros (ck&?); exists ck; try right; eauto.
      inversion_clear H as [?? Reset_State|]; try inv Reset_State; auto.
    - setoid_rewrite <-IHtcs; split; intros (ck&?); exists ck; try right; eauto.
      inversion_clear H as [?? Reset_State|]; try inv Reset_State; auto.
  Qed.

  Definition is_reset_state_in_tc_b (x: ident) (ck: clock) (tc: trconstr) : bool :=
    match tc with
    | TcReset ck' (ResState y _ _) => ident_eqb x y && clock_eq ck ck'
    | _ => false
    end.

  Definition is_reset_state_in_b (x: ident) (ck: clock) (tcs: list trconstr) : bool :=
    existsb (is_reset_state_in_tc_b x ck) tcs.

  Fact Is_reset_state_in_tc_reflect:
    forall x ck tc,
      Is_reset_state_in_tc x ck tc <-> is_reset_state_in_tc_b x ck tc = true.
  Proof.
    destruct tc; simpl; cases; simpl; split;
      try discriminate; try now inversion 1.
    - inversion_clear 1.
      rewrite Bool.andb_true_iff; split.
      apply ident_eqb_refl.
      rewrite clock_eq_spec; auto.
    - rewrite Bool.andb_true_iff, ident_eqb_eq, clock_eq_spec.
      intros (?&?); subst; constructor.
  Qed.

  Corollary Is_reset_state_in_reflect:
    forall x ck tcs,
      Is_reset_state_in x ck tcs <-> is_reset_state_in_b x ck tcs = true.
  Proof.
    setoid_rewrite existsb_exists; setoid_rewrite Exists_exists.
    split; intros (?&?& Reset_State); apply Is_reset_state_in_tc_reflect in Reset_State; eauto.
  Qed.

  Lemma Is_reset_state_in_dec:
    forall x ck tcs,
      { Is_reset_state_in x ck tcs } + { ~ Is_reset_state_in x ck tcs }.
  Proof.
    intros;
      eapply Bool.reflect_dec, Bool.iff_reflect, Is_reset_state_in_reflect.
  Qed.

  Lemma not_Is_reset_state_in_tc_TcReset_State:
    forall y x ck ty ro,
      ~ (exists ck', Is_reset_state_in_tc y ck' (TcReset ck (ResState x ty ro))) -> x <> y.
  Proof.
    intros * NIsReset_State E; subst; apply NIsReset_State; eauto using Is_reset_state_in_tc.
  Qed.

  Lemma s_ins_not_reset_state {prefs}:
    forall (s: @system prefs) x ck,
      InMembers x s.(s_in) ->
      ~ Is_reset_state_in x ck s.(s_tcs).
  Proof.
    intros * Hin Hreset_state.
    pose proof (s_nodup s) as Nodup.
    eapply (NoDup_app_In x) in Nodup.
    - assert (In x (state_resets_of (s_tcs s))) as Hreset_state' by (apply reset_states_of_In; eauto).
      apply s_state_reset_incl in Hreset_state'.
      rewrite map_app, <-s_lasts_in_tcs, <-s_nexts_in_tcs in Hreset_state'.
      apply Nodup. rewrite app_assoc, in_app; auto.
    - apply fst_InMembers; auto.
  Qed.

  (** * IsDefined inductive *)

  Inductive Is_defined_in_tc: ident -> trconstr -> Prop :=
  | DefTcDef:
      forall x ck e,
        Is_defined_in_tc x (TcDef ck x e)
  | DefTcLast:
      forall x ck ckrs e,
        Is_defined_in_tc x (TcUpdate ck ckrs (UpdLast x e))
  | DefTcInst:
      forall x ck ckrs i xs f es,
        In x xs ->
        Is_defined_in_tc x (TcUpdate ck ckrs (UpdInst i xs f es)).

  Global Hint Constructors Is_defined_in_tc : stcdef.

  Definition Is_defined_in (x: ident) (tcs: list trconstr) : Prop :=
    Exists (Is_defined_in_tc x) tcs.

  Lemma Is_defined_Is_variable_Is_last_in_tc:
    forall tc x,
      Is_defined_in_tc x tc <->
      Is_variable_in_tc x tc \/ Is_update_last_in_tc x tc.
  Proof.
    split; [intros []|intros [[]|[]]];
      auto using Is_defined_in_tc, Is_variable_in_tc, Is_update_last_in_tc.
  Qed.

  Lemma Is_defined_Is_variable_Is_last_in:
    forall tcs x,
      Is_defined_in x tcs <->
      Is_variable_in x tcs \/ Is_update_last_in x tcs.
  Proof.
    intros *. unfold Is_defined_in, Is_variable_in, Is_update_last_in.
    split; intros.
    - apply Exists_or_inv. solve_Exists. now apply Is_defined_Is_variable_Is_last_in_tc.
    - apply Exists_or in H. solve_Exists. now apply Is_defined_Is_variable_Is_last_in_tc.
  Qed.

  Corollary Is_variable_in_Is_defined_in:
    forall x tcs,
      Is_variable_in x tcs ->
      Is_defined_in x tcs.
  Proof.
    intros * Hvar.
    rewrite Is_defined_Is_variable_Is_last_in; auto.
  Qed.

  Corollary Is_last_in_Is_defined_in:
    forall x tcs,
      Is_update_last_in x tcs ->
      Is_defined_in x tcs.
  Proof.
    intros * Hvar.
    rewrite Is_defined_Is_variable_Is_last_in; auto.
  Qed.

  Lemma Is_variable_in_tc_Is_defined_in_tc:
    forall x tc,
      Is_variable_in_tc x tc ->
      Is_defined_in_tc x tc.
  Proof.
    destruct tc; inversion_clear 1; auto with stcdef.
  Qed.

  Global Hint Resolve Is_variable_in_Is_defined_in Is_last_in_Is_defined_in Is_variable_in_tc_Is_defined_in_tc : stcdef.

  Lemma s_ins_not_def {prefs}:
    forall (s: @system prefs) x,
      InMembers x s.(s_in) ->
      ~ Is_defined_in x s.(s_tcs).
  Proof.
    intros * Hin Hdef.
    pose proof (s_nodup s) as Nodup.
    eapply (NoDup_app_In x) in Nodup.
    - apply Is_defined_Is_variable_Is_last_in in Hdef as [Var|Last];
        apply Nodup; rewrite app_assoc, in_app.
      + apply Is_variable_in_variables in Var; rewrite <-s_vars_out_in_tcs in Var;
          auto.
      + apply lasts_of_In in Last; rewrite <-s_lasts_in_tcs in Last; auto.
        right. apply in_app; auto.
    - apply fst_InMembers; auto.
  Qed.

  Lemma not_Is_defined_in_tc_TcDef:
    forall y x ck e,
      ~ Is_defined_in_tc y (TcDef ck x e) -> x <> y.
  Proof.
    intros * NIsDef E; subst; apply NIsDef; auto using Is_defined_in_tc.
  Qed.

  Lemma not_Is_defined_in_cons:
    forall x tc tcs,
      ~ Is_defined_in x (tc :: tcs)
      <-> ~ Is_defined_in_tc x tc /\ ~ Is_defined_in x tcs.
  Proof.
    split.
    - intro Hndef; split; intro His_def;
        eapply Hndef; now constructor.
    - intros [Hdef_tc Hdef_tcs] Hdef_all.
      inv Hdef_all; eauto.
  Qed.

  Definition defined_tc (tc: trconstr): list ident :=
    match tc with
    | TcDef _ x _ => [x]
    | TcUpdate _ _ (UpdLast x _) => [x]
    | TcUpdate _ _ (UpdInst _ xs _ _) => xs
    | _ => []
    end.

  Definition defined := flat_map defined_tc.

  Lemma Is_defined_in_defined_tc:
    forall x tc,
      Is_defined_in_tc x tc <-> In x (defined_tc tc).
  Proof.
    destruct tc; simpl; cases; simpl; split; try inversion_clear 1; subst;
      auto using Is_defined_in_tc; try contradiction.
  Qed.

  Lemma Is_defined_in_defined:
    forall x tcs,
      Is_defined_in x tcs <-> In x (defined tcs).
  Proof.
    unfold defined.
    induction tcs; simpl.
    - split; inversion 1.
    - split; rewrite in_app.
      + inversion_clear 1.
        * left; apply Is_defined_in_defined_tc; auto.
        * right; apply IHtcs; auto.
      + intros [?|?].
        * left; apply Is_defined_in_defined_tc; auto.
        * right; apply IHtcs; auto.
  Qed.

  Lemma system_output_defined_in_tcs {prefs}:
    forall (s: @system prefs) x,
      In x (map fst s.(s_out)) ->
      Is_defined_in x s.(s_tcs).
  Proof.
    intros * Ho.
    cut (In x (map fst s.(s_vars) ++ map fst s.(s_out))).
    - intro Hvo; apply Is_variable_in_Is_defined_in, Is_variable_in_variables.
      now rewrite <-s_vars_out_in_tcs.
    - apply in_or_app; auto.
  Qed.

  Lemma Is_defined_in_In:
    forall x tcs,
      Is_defined_in x tcs ->
      exists tc, In tc tcs /\ Is_defined_in_tc x tc.
  Proof.
    induction tcs as [|tc]. now inversion 1.
    inversion_clear 1 as [? ? Hdef|? ? Hex].
    - exists tc; split; auto with datatypes.
    - apply Exists_exists in Hex as (tc' & Hin & Hdef).
      exists tc'; split; auto with datatypes.
  Qed.

  Lemma s_defined {prefs} :
    forall (s: @system prefs),
      Permutation.Permutation (defined (s_tcs s)) (variables (s_tcs s) ++ map fst (lasts_of (s_tcs s))).
  Proof.
    unfold defined, variables; intro;
      induction (s_tcs s) as [|[]]; simpl; cases; simpl; auto.
    - now apply Permutation.Permutation_cons_app.
    - now rewrite <-app_assoc; apply Permutation.Permutation_app_head.
  Qed.

  Lemma s_nodup_variables_lasts_nexts {prefs} : forall (s: @system prefs),
      NoDup (variables (s_tcs s) ++ map fst (s_lasts s ++ s_nexts s)).
  Proof.
    intros.
    rewrite <-s_vars_out_in_tcs, map_app, <- ? app_assoc.
    pose proof (s_nodup s) as Nd. solve_NoDup_app.
  Qed.

  Lemma s_nodup_defined {prefs} :
    forall (s: @system prefs), NoDup (defined (s_tcs s)).
  Proof.
    intros; eapply Permutation.Permutation_NoDup.
    - apply Permutation.Permutation_sym, s_defined.
    - rewrite <-s_lasts_in_tcs, <-s_vars_out_in_tcs.
      rewrite <-app_assoc.
      eapply NoDup_app_weaken with (ys:=map fst _). rewrite Permutation.Permutation_app_comm.
      eapply NoDup_app_weaken with (ys:=map fst _). rewrite <-3 app_assoc.
      apply s_nodup.
  Qed.

  Lemma incl_defined_lasts:
    forall tcs, incl (map fst (lasts_of tcs)) (defined tcs).
  Proof.
    induction tcs; intros ? Hin; simpl in *; [inv Hin|].
    apply in_app.
    destruct a; simpl in *; cases; simpl in *; auto.
    destruct Hin; auto.
  Qed.

  Lemma nodup_defined_nodup_lasts:
    forall tcs, NoDup (defined tcs) -> NoDup (lasts_of tcs).
  Proof.
    induction tcs; intros; simpl in *. constructor.
    cases; simpl in *; auto.
    - inv H; auto.
    - inv H; constructor; auto.
      intro Hin. apply H2, incl_defined_lasts; auto.
      eapply in_map_iff. exists (i, typeofc c0); eauto.
    - apply NoDup_app_r in H; auto.
  Qed.

  Lemma defined_app:
    forall tcs tcs',
      defined (tcs ++ tcs') = defined tcs ++ defined tcs'.
  Proof.
    unfold defined.
    induction tcs as [|[]]; simpl; intros; auto with datatypes.
    - rewrite <-app_assoc; f_equal; auto.
  Qed.

  (** * IsSystem inductive *)

  Inductive Is_system_in_tc : ident -> trconstr -> Prop :=
  | Is_system_inTcUpdate:
      forall s ck ckrs ys f es,
        Is_system_in_tc f (TcUpdate ck ckrs (UpdInst s ys f es))
  | Is_system_inTcReset:
      forall s ck f,
        Is_system_in_tc f (TcReset ck (ResInst s f)).

  Definition Is_system_in (f: ident) (tcs: list trconstr) : Prop :=
    Exists (Is_system_in_tc f) tcs.

  Lemma not_Is_system_in_cons:
    forall b tc tcs,
      ~ Is_system_in b (tc :: tcs) <-> ~Is_system_in_tc b tc /\ ~Is_system_in b tcs.
  Proof.
    split; intro HH.
    - split; intro; apply HH; unfold Is_system_in; intuition.
    - destruct HH; inversion_clear 1; intuition.
  Qed.

  Lemma steps_iresets_of_Is_system_in:
    forall tcs b,
      Is_system_in b tcs <-> In b (map snd (insts_of tcs ++ inst_resets_of tcs)).
  Proof.
    induction tcs as [|[]]; simpl; cases; simpl.
    all:try now (setoid_rewrite <-IHtcs; split; try (right; auto);
                 inversion_clear 1 as [?? IsSystem|]; auto; inv IsSystem).
    - split; try contradiction; inversion 1.
    - split; rewrite map_app, in_app; simpl.
      + inversion_clear 1 as [?? IsSystem|?? Systems]; try inv IsSystem; auto.
        apply IHtcs in Systems.
        rewrite map_app, in_app in Systems; destruct Systems; auto.
      + intros [?|[?|?]].
        * right; apply IHtcs; rewrite map_app, in_app; auto.
        * subst; left; constructor.
        * right; apply IHtcs; rewrite map_app, in_app; auto.
    - split; rewrite map_app, in_app; simpl.
      + inversion_clear 1 as [?? IsSystem|?? Systems]; try inv IsSystem; auto.
        apply IHtcs in Systems.
        rewrite map_app, in_app in Systems; destruct Systems; auto.
      + intros [?|[?|?]].
        * subst; left; constructor.
        * right; apply IHtcs; rewrite map_app, in_app; auto.
        * right; apply IHtcs; rewrite map_app, in_app; auto.
  Qed.

End STCSYNTAX.

Module StcSyntaxFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks   : CLOCKS        Ids Op OpAux)
       (CESyn : CESYNTAX      Ids Op OpAux Cks)
       <: STCSYNTAX Ids Op OpAux Cks CESyn.
  Include STCSYNTAX Ids Op OpAux Cks CESyn.
End StcSyntaxFun.
