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

  Inductive trconstr :=
  | TcDef       : ident -> clock -> cexp -> trconstr
  | TcReset     : ident -> clock -> type -> const -> trconstr
  | TcNext      : ident -> clock -> list clock -> exp -> trconstr
  | TcInstReset : ident -> clock -> ident -> trconstr
  | TcStep      : ident -> list ident -> clock -> list clock -> ident -> list exp -> trconstr.

  Definition variables_tc (tc: trconstr): list ident :=
    match tc with
    | TcDef x _ _ => [x]
    | TcStep _ xs _ _ _ _ => xs
    | _ => []
    end.

  Definition variables := flat_map variables_tc.

  Inductive Is_reset_in_tc: ident -> clock -> trconstr -> Prop :=
    ResetTcReset:
      forall x ck ty ro,
        Is_reset_in_tc x ck (TcReset x ck ty ro).

  Definition Is_reset_in (x: ident) (ck: clock) (tcs: list trconstr) : Prop :=
    Exists (Is_reset_in_tc x ck) tcs.

  Inductive Next_with_reset_in_tc: ident -> list clock -> trconstr -> Prop :=
  | Next_with_reset_in_tc_intro:
      forall s ck ckrs es,
        Next_with_reset_in_tc s ckrs (TcNext s ck ckrs es).
  Hint Constructors Next_with_reset_in_tc.

  Definition Next_with_reset_in (s: ident) (ckrs: list clock) (tcs: list trconstr) : Prop :=
    Exists (Next_with_reset_in_tc s ckrs) tcs.

  Inductive Is_ireset_in_tc: ident -> clock -> trconstr -> Prop :=
  | SubTcIIreset:
      forall s ck b,
        Is_ireset_in_tc s ck (TcInstReset s ck b).

  Inductive Is_step_in_tc: ident -> trconstr -> Prop :=
  | SubTcStep:
      forall s xs ck rst b es,
        Is_step_in_tc s (TcStep s xs ck rst b es).

  Definition reset_consistency (tcs: list trconstr) : Prop :=
    forall s ckrs,
      Next_with_reset_in s ckrs tcs ->
      (forall ckr, In ckr ckrs <-> Is_reset_in s ckr tcs).

  Definition Is_ireset_in (s: ident) (ck : clock) := Exists (Is_ireset_in_tc s ck).

  Definition Is_step_in (s: ident) := Exists (Is_step_in_tc s).

  Inductive Step_with_ireset_in_tc: ident -> list clock -> trconstr -> Prop :=
    Step_with_ireset_in_tc_intro:
      forall s ys ck ckrs f es,
        Step_with_ireset_in_tc s ckrs (TcStep s ys ck ckrs f es).
  Hint Constructors Step_with_ireset_in_tc.

  Definition Step_with_ireset_in (s: ident) (ckrs: list clock) (tcs: list trconstr) : Prop :=
    Exists (Step_with_ireset_in_tc s ckrs) tcs.

  Definition ireset_consistency (tcs: list trconstr) : Prop :=
    forall s ckrs,
      Step_with_ireset_in s ckrs tcs ->
      (forall ckr, In ckr ckrs <-> Is_ireset_in s ckr tcs).

  Fixpoint resets_of (tcs: list trconstr) : list ident :=
    match tcs with
    | [] => []
    | TcReset x ck _ _ :: tcs => x :: (resets_of tcs)
    | _ :: tcs => resets_of tcs
    end.

  Fixpoint nexts_of (tcs: list trconstr) : list (ident * type) :=
    match tcs with
    | [] => []
    | TcNext x _ _ e :: tcs => (x, typeof e) :: (nexts_of tcs)
    | _ :: tcs => nexts_of tcs
    end.

  Fixpoint steps_of (tcs: list trconstr) : list (ident * ident) :=
    match tcs with
    | [] => []
    | TcStep s _ _ _ b _ :: tcs => (s, b) :: steps_of tcs
    | _ :: tcs => steps_of tcs
    end.

  Fixpoint iresets_of (tcs: list trconstr) : list (ident * ident) :=
    match tcs with
    | [] => []
    | TcInstReset s _ b :: tcs => (s, b) :: iresets_of tcs
    | _ :: tcs => iresets_of tcs
    end.

  Definition mems_of_nexts {A B C} : list (ident * (A * B * C)) -> list (ident * B) :=
    map (fun x => (fst x, snd (fst (snd x)))).

  Record system :=
    System {
        s_name : ident;                           (* name *)
        s_in   : list (ident * (type * clock));   (* inputs *)
        s_vars : list (ident * (type * clock));   (* local variables *)
        s_nexts: list (ident * (const * type * clock));  (* state variables *)
        s_subs : list (ident * ident);            (* sub-instances *)
        s_out  : list (ident * (type * clock));   (* outputs *)
        s_tcs  : list trconstr;                   (* transition constraints *)

        s_ingt0            : 0 < length s_in;

        s_nodup            : NoDup (map fst s_in ++ map fst s_vars ++
                                        map fst s_out ++ map fst s_nexts);
        s_nodup_resets_subs : NoDup (map fst s_nexts ++ map fst s_subs);

        s_subs_in_tcs      : forall f, In f (map snd s_subs)
                                       <-> In f (map snd (steps_of s_tcs ++ iresets_of s_tcs));
        s_subs_steps_of    : Permutation s_subs (steps_of s_tcs);

        s_nexts_in_tcs     : Permutation (mems_of_nexts s_nexts) (nexts_of s_tcs);
        s_reset_consistency : reset_consistency s_tcs;
        s_reset_incl        : incl (resets_of s_tcs) (map fst (nexts_of s_tcs));

        s_vars_out_in_tcs  : Permutation (map fst s_vars ++ map fst s_out) (variables s_tcs);

        s_ireset_consistency: ireset_consistency s_tcs;
        s_ireset_incl       : incl (iresets_of s_tcs) (steps_of s_tcs);

        s_good             : Forall (AtomOrGensym (PSP.of_list gensym_prefs)) (map fst (s_in ++ s_vars ++ s_out))
                             /\ Forall (AtomOrGensym (PSP.of_list gensym_prefs)) (map fst s_nexts)
                             /\ Forall (AtomOrGensym (PSP.of_list gensym_prefs)) (map fst s_subs)
                             /\ atom s_name
      }.

  Global Instance system_unit: ProgramUnit system :=
    { name := s_name; }.

  Global Instance system_state_unit: ProgramStateUnit system type :=
    { state_variables := fun s => map (fun x => (fst x, snd (fst (snd x)))) (s_nexts s);
      instance_variables := s_subs }.

  Lemma s_nexts_in_tcs_fst:
    forall s,
      Permutation (map fst s.(s_nexts)) (map fst (nexts_of s.(s_tcs))).
  Proof.
    intro; rewrite <-s_nexts_in_tcs.
    induction (s_nexts s); simpl; auto.
  Qed.

  Lemma Step_in_Step_with_reset_in:
    forall tcs s,
      Is_step_in s tcs ->
      exists rst, Step_with_ireset_in s rst tcs.
  Proof.
    induction 1 as [?? Step|].
    - inv Step; exists rst; left; constructor.
    - destruct IHExists.
      eexists; right; eauto.
  Qed.

  Lemma Step_in_steps_of:
    forall tcs s,
      Is_step_in s tcs <-> InMembers s (steps_of tcs).
  Proof.
    induction tcs as [|tc]; simpl.
    - split; inversion 1.
    - intros.
      unfold Is_step_in in *.
      rewrite Exists_cons, IHtcs.
      destruct tc; intuition; try take (Is_step_in_tc _ _) and inv it.
      + constructor; auto.
      + now right.
      + take (InMembers _ _) and inv it; auto.
        left; constructor.
  Qed.

  Lemma s_nodup_nexts:
    forall b, NoDupMembers b.(s_nexts).
  Proof.
    intro; pose proof (s_nodup b) as Nodup.
    apply fst_NoDupMembers.
    rewrite 2 app_assoc in Nodup.
    rewrite Permutation_app_comm in Nodup.
    apply NoDup_app_weaken in Nodup; auto.
  Qed.

  Lemma s_nodup_subs:
    forall b, NoDupMembers b.(s_subs).
  Proof.
    intro; pose proof (s_nodup_resets_subs b) as Nodup.
    rewrite Permutation_app_comm in Nodup.
    apply NoDup_app_weaken in Nodup.
    apply fst_NoDupMembers; auto.
  Qed.

  Lemma s_nodup_vars:
    forall b, NoDupMembers (s_in b ++ s_vars b ++ s_out b).
  Proof.
    intro; pose proof (s_nodup b) as Nodup.
    rewrite 2 app_assoc in Nodup.
    apply NoDup_app_weaken in Nodup.
    rewrite <-2 map_app, <-app_assoc in Nodup.
    apply fst_NoDupMembers; auto.
  Qed.

  Lemma s_nodup_variables:
    forall b, NoDup (variables b.(s_tcs)).
  Proof.
    intro; rewrite <-s_vars_out_in_tcs, <-map_app.
    apply fst_NoDupMembers.
    eapply NoDupMembers_app_r, s_nodup_vars.
  Qed.

  Record program := Program {
                        enums : list (ident * nat);
                        systems : list system
                      }.

  Global Program Instance program_program: CommonProgram.Program system program :=
    { units := systems;
      update := fun p => Program p.(enums) }.

  Definition find_system : ident -> program -> option (system * program) :=
    find_unit.

  Remark find_system_other:
    forall b P bl enums,
      bl.(s_name) <> b ->
      find_system b (Program enums (bl :: P)) = find_system b (Program enums P).
  Proof.
    intros; eapply find_unit_other; simpl; eauto.
    intro; auto.
  Qed.

  Lemma Step_with_ireset_in_Is_step_in:
    forall tcs s rst,
      Step_with_ireset_in s rst tcs ->
      Is_step_in s tcs.
  Proof.
    induction 1 as [?? Step|].
    - inv Step; left; constructor.
    - right; auto.
  Qed.

  Lemma Next_with_reset_in_cons_not_next:
    forall tcs tc s rst,
      (forall s ck ckrs e, tc <> TcNext s ck ckrs e) ->
      (Next_with_reset_in s rst (tc :: tcs) <-> Next_with_reset_in s rst tcs).
  Proof.
    intros * Neq; split.
    - inversion_clear 1 as [?? Step|]; auto.
      inv Step; exfalso; eapply Neq; eauto.
    - right; auto.
  Qed.

  Lemma Step_with_ireset_in_cons_not_step:
    forall tcs tc s rst,
      (forall s ys ck rst f es, tc <> TcStep s ys ck rst f es) ->
      (Step_with_ireset_in s rst (tc :: tcs) <-> Step_with_ireset_in s rst tcs).
  Proof.
    intros * Neq; split.
    - inversion_clear 1 as [?? Step|]; auto.
      inv Step; exfalso; eapply Neq; eauto.
    - right; auto.
  Qed.

  Lemma steps_of_In':
    forall tcs s b,
      In (s, b) (steps_of tcs) ->
      exists xs ck rst es, In (TcStep s xs ck rst b es) tcs.
  Proof.
    induction tcs as [|[]]; simpl; try contradiction; intros * Hin;
      try now edestruct IHtcs as (?&?&?&?&?); eauto 6.
    destruct Hin as [E|].
    - inv E; eauto 6.
    - edestruct IHtcs as (?&?&?&?&?); eauto 6.
  Qed.

  Lemma iresets_of_app:
    forall tcs tcs',
      iresets_of (tcs ++ tcs') = iresets_of tcs ++ iresets_of tcs'.
  Proof.
    induction tcs as [|[]]; intros; simpl; try f_equal; auto.
  Qed.

  Definition is_step_in_tc_b (s: ident) (tc: trconstr) : bool :=
    match tc with
    | TcStep s' _ _ _ _ _ => ident_eqb s s'
    | _ => false
    end.

  Definition is_step_in_tcs_b (s: ident) (tcs: list trconstr) : bool :=
    existsb (is_step_in_tc_b s) tcs.

  Definition is_ireset_in_tc_b (s: ident) (ck: clock) (tc: trconstr) : bool :=
    match tc with
    | TcInstReset s' ck' _ => ident_eqb s s' && clock_eq ck ck'
    | _ => false
    end.

  Definition is_ireset_in_tcs_b (s: ident) (ck: clock) (tcs: list trconstr) : bool :=
    existsb (is_ireset_in_tc_b s ck) tcs.

  Fact Is_step_in_tc_reflect:
    forall s tc,
      Is_step_in_tc s tc <-> is_step_in_tc_b s tc = true.
  Proof.
    destruct tc; simpl; split;
      try discriminate; try now inversion 1.
    - inversion_clear 1; apply ident_eqb_refl.
    - rewrite ident_eqb_eq; intros; subst; constructor.
  Qed.

  Corollary Is_step_in_reflect:
    forall s tcs,
      Is_step_in s tcs <-> is_step_in_tcs_b s tcs = true.
  Proof.
    setoid_rewrite existsb_exists; setoid_rewrite Exists_exists.
    split; intros (?&?& Step); apply Is_step_in_tc_reflect in Step; eauto.
  Qed.

  Lemma Is_step_in_dec:
    forall s tcs,
      { Is_step_in s tcs } + { ~ Is_step_in s tcs }.
  Proof.
    intros;
      eapply Bool.reflect_dec, Bool.iff_reflect, Is_step_in_reflect.
  Qed.

  Fact Is_ireset_in_tc_reflect:
    forall s ck tc,
      Is_ireset_in_tc s ck tc <-> is_ireset_in_tc_b s ck tc = true.
  Proof.
    destruct tc; simpl; split;
      try discriminate; try now inversion 1.
    - inversion_clear 1.
      rewrite Bool.andb_true_iff; split.
      apply ident_eqb_refl.
      rewrite clock_eq_spec; auto.
    - rewrite Bool.andb_true_iff, ident_eqb_eq, clock_eq_spec.
      intros (?&?); subst; constructor.
  Qed.

  Corollary Is_ireset_in_reflect:
    forall s ck tcs,
      Is_ireset_in s ck tcs <-> is_ireset_in_tcs_b s ck tcs = true.
  Proof.
    setoid_rewrite existsb_exists; setoid_rewrite Exists_exists.
    split; intros (?&?& Step); apply Is_ireset_in_tc_reflect in Step; eauto.
  Qed.

  Lemma Is_ireset_in_dec:
    forall s ck tcs,
      { Is_ireset_in s ck tcs } + { ~ Is_ireset_in s ck tcs }.
  Proof.
    intros;
      eapply Bool.reflect_dec, Bool.iff_reflect, Is_ireset_in_reflect.
  Qed.

  Lemma variables_app:
    forall tcs tcs',
      variables (tcs ++ tcs') = variables tcs ++ variables tcs'.
  Proof.
    unfold variables.
    induction tcs as [|[]]; simpl; intros; auto.
    - rewrite <-app_assoc; f_equal; auto.
  Qed.

  Lemma steps_of_app:
    forall tcs tcs',
      steps_of (tcs ++ tcs') = steps_of tcs ++ steps_of tcs'.
  Proof.
    unfold steps_of.
    induction tcs as [|[]]; simpl; intros; auto.
  Qed.

  Lemma nexts_of_app:
    forall tcs tcs',
      nexts_of (tcs ++ tcs') = nexts_of tcs ++ nexts_of tcs'.
  Proof.
    induction tcs as [|[]]; simpl; auto; setoid_rewrite IHtcs; auto.
  Qed.

  Lemma iresets_of_In:
    forall x tcs,
      (exists ck, Is_ireset_in x ck tcs) <-> In x (map fst (iresets_of tcs)).
  Proof.
    induction tcs as [|[]]; simpl; intros.
    - setoid_rewrite Exists_nil.
      split; [intros (?&?)|intros ?]; eauto using Cbase.
    - setoid_rewrite <-IHtcs.
      split; intros (ck&?); exists ck; try right; eauto.
      inversion_clear H as [?? Reset|]; try inv Reset; auto.
    - setoid_rewrite <-IHtcs; split; intros (ck&?); exists ck; try right; eauto.
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

  Lemma steps_of_In:
    forall x tcs,
      Is_step_in x tcs <-> In x (map fst (steps_of tcs)).
  Proof.
    induction tcs as [|[]]; simpl.
    - now setoid_rewrite Exists_nil.
    - setoid_rewrite <-IHtcs; split; try right; auto.
      inversion_clear 1 as [?? Next|]; try inv Next; auto.
    - setoid_rewrite <-IHtcs; split; try right; auto.
      inversion_clear 1 as [?? Next|]; try inv Next; auto.
    - setoid_rewrite <-IHtcs; split; try right; auto.
      inversion_clear 1 as [?? Next|]; try inv Next; auto.
    - setoid_rewrite <-IHtcs; split; try right; auto.
      inversion_clear 1 as [?? Next|]; try inv Next; auto.
    - setoid_rewrite <-IHtcs; split.
      + inversion_clear 1 as [?? Next|]; try inv Next; auto.
      + intros [E|?].
        * subst; left; constructor.
        * right; auto.
  Qed.

  Fact s_nexts_of_mems_of_nexts:
    forall s, incl (nexts_of (s_tcs s)) (mems_of_nexts (s_nexts s)).
  Proof.
    intros ???; now rewrite s_nexts_in_tcs.
  Qed.

  Lemma mems_of_nexts_fst:
    forall {A B C} (nexts : list (ident * (A * B * C))),
      map fst (mems_of_nexts nexts) = map fst nexts.
  Proof.
    induction nexts; simpl; auto; f_equal; auto.
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
