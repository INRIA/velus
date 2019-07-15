From Velus Require Import Common.
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
       (Import CESyn : CESYNTAX Op).

  (** ** Transition constraints *)

  Inductive trconstr :=
  | TcDef  : ident -> clock -> cexp -> trconstr
  | TcNext : ident -> clock -> exp -> trconstr
  | TcReset: ident -> clock -> ident -> trconstr
  | TcCall : ident -> idents -> clock -> bool -> ident -> list exp -> trconstr.

  Definition variables_tc (tc: trconstr): idents :=
    match tc with
    | TcDef x _ _ => [x]
    | TcCall _ xs _ _ _ _ => xs
    | _ => []
    end.

  Definition variables := flat_map variables_tc.

  Inductive Is_sub_in_tc: ident -> nat -> trconstr -> Prop :=
  | SubTcReset:
      forall s ck b,
        Is_sub_in_tc s 0 (TcReset s ck b)
  | SubTcCall:
      forall s xs ck rst b es,
        Is_sub_in_tc s 1 (TcCall s xs ck rst b es).

  Definition Is_sub_in (s: ident) (k: nat) (tcs: list trconstr) : Prop :=
    Exists (Is_sub_in_tc s k) tcs.

  Definition Reset_in (s: ident) := Is_sub_in s 0.

  Definition Step_in (s: ident) := Is_sub_in s 1.

  Inductive Step_with_reset_in_tc: ident -> bool -> trconstr -> Prop :=
    Step_with_reset_in_tc_intro:
      forall s ys ck rst f es,
        Step_with_reset_in_tc s rst (TcCall s ys ck rst f es).

  Definition Step_with_reset_in (s: ident) (rst: bool) (tcs: list trconstr) : Prop :=
    Exists (Step_with_reset_in_tc s rst) tcs.

  Fixpoint lasts_of (tcs: list trconstr) : list ident :=
    match tcs with
    | [] => []
    | TcNext x _ _ :: tcs => x :: (lasts_of tcs)
    | _ :: tcs => lasts_of tcs
    end.

  Fixpoint calls_of (tcs: list trconstr) : list (ident * ident) :=
    match tcs with
    | [] => []
    | TcCall s _ _ _ b _ :: tcs => (s, b) :: calls_of tcs
    | _ :: tcs => calls_of tcs
    end.

  Fixpoint resets_of (tcs: list trconstr) : list (ident * ident) :=
    match tcs with
    | [] => []
    | TcReset s _ b :: tcs => (s, b) :: resets_of tcs
    | _ :: tcs => resets_of tcs
    end.

  Record system :=
    System {
        s_name  : ident;
        s_in    : list (ident * (type * clock));
        s_vars  : list (ident * (type * clock));
        s_lasts : list (ident * (const * clock));
        s_subs: list (ident * ident);
        s_out   : list (ident * (type * clock));
        s_tcs   : list trconstr;

        s_ingt0 : 0 < length s_in;

        s_nodup : NoDup (map fst s_in ++ map fst s_vars ++ map fst s_out ++ map fst s_lasts);
        s_nodup_lasts_subs: NoDup (map fst s_lasts ++ map fst s_subs);

        s_subs_in_tcs: forall f, In f (map snd s_subs) <-> In f (map snd (calls_of s_tcs ++ resets_of s_tcs));
        s_subs_calls_of: Permutation s_subs (calls_of s_tcs);

        s_lasts_in_tcs: Permutation (map fst s_lasts) (lasts_of s_tcs);
        s_vars_out_in_tcs: Permutation (map fst s_vars ++ map fst s_out) (variables s_tcs);

        s_no_single_reset: forall s, Reset_in s s_tcs -> Step_with_reset_in s true s_tcs;
        s_reset_in: forall s rst, Step_with_reset_in s rst s_tcs ->
                             if rst then Reset_in s s_tcs else ~ Reset_in s s_tcs;
        s_reset_incl: incl (resets_of s_tcs) (calls_of s_tcs);

        s_good: Forall ValidId (s_in ++ s_vars ++ s_out)
                /\ Forall ValidId s_lasts
                /\ Forall ValidId s_subs
                /\ valid s_name
      }.

  Lemma s_nodup_lasts:
    forall b, NoDupMembers b.(s_lasts).
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
    intro; pose proof (s_nodup_lasts_subs b) as Nodup.
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

  Definition program := list system.

  Fixpoint find_system (b: ident) (P: program) : option (system * program) :=
   match P with
   | [] => None
   | bl :: P =>
     if ident_eqb bl.(s_name) b
     then Some (bl, P) else find_system b P
   end.

  (** Properties of system lookups *)

  Remark find_system_app:
    forall b P bl P',
      find_system b P = Some (bl, P') ->
      exists P'',
        P = P'' ++ bl :: P'
        /\ find_system b P'' = None.
  Proof.
    intros * Hfind.
    induction P; inversion Hfind as [H].
    destruct (ident_eqb (s_name a) b) eqn: E.
    - inversion H; subst.
      exists nil; auto.
    - specialize (IHP H).
      destruct IHP as (P'' & HP'' & Hnone).
      rewrite HP''.
      exists (a :: P''); split; auto.
      simpl; rewrite E; auto.
  Qed.

  Remark find_system_name:
    forall b P bl P',
      find_system b P = Some (bl, P') ->
      bl.(s_name) = b.
  Proof.
    intros * Hfind.
    induction P; inversion Hfind as [H].
    destruct (ident_eqb (s_name a) b) eqn: E.
    - inversion H; subst.
      now apply ident_eqb_eq.
    - now apply IHP.
  Qed.

  Remark find_system_other:
    forall b P bl,
      bl.(s_name) <> b ->
      find_system b (bl :: P) = find_system b P.
  Proof.
    intros * Hnb.
    apply ident_eqb_neq in Hnb.
    simpl; rewrite Hnb; reflexivity.
  Qed.

  Remark find_system_In:
    forall b P bl P',
      find_system b P = Some (bl, P') ->
      In bl P.
  Proof.
    intros * Hfind.
    induction P; inversion Hfind as [H].
    destruct (ident_eqb (s_name a) b) eqn: E.
    - inversion H; subst.
      apply in_eq.
    - apply in_cons; auto.
  Qed.

  Lemma find_system_app':
    forall b P P',
      find_system b (P ++ P') =
      match find_system b P with
      | None => find_system b P'
      | Some (bl, P'') => Some (bl, P'' ++ P')
      end.
  Proof.
    induction P as [|bl P]; simpl; auto.
    intro; destruct (ident_eqb bl.(s_name) b); auto.
  Qed.

  Lemma Step_with_reset_in_Step_in:
    forall tcs s rst,
      Step_with_reset_in s rst tcs ->
      Step_in s tcs.
  Proof.
    induction 1 as [?? Step|].
    - inv Step; left; constructor.
    - right; auto.
  Qed.

  Lemma Step_with_reset_in_cons_not_call:
    forall tcs tc s rst,
      (forall s ys ck rst f es, tc <> TcCall s ys ck rst f es) ->
      (Step_with_reset_in s rst (tc :: tcs) <-> Step_with_reset_in s rst tcs).
  Proof.
    intros * Neq; split.
    - inversion_clear 1 as [?? Step|]; auto.
      inv Step; exfalso; eapply Neq; eauto.
    - right; auto.
  Qed.

  Lemma Step_with_reset_in_cons_call:
    forall tcs s (rst: bool) s' ys ck rst' f es,
      s <> s' ->
      (Step_with_reset_in s rst (TcCall s' ys ck rst' f es :: tcs) <-> Step_with_reset_in s rst tcs).
  Proof.
    intros * Neq; split.
    - inversion_clear 1 as [?? Step|]; auto.
      inv Step; congruence.
    - right; auto.
  Qed.

  Lemma calls_of_In:
    forall tcs s b,
      In (s, b) (calls_of tcs) ->
      exists xs ck rst es, In (TcCall s xs ck rst b es) tcs.
  Proof.
    induction tcs as [|[]]; simpl; try contradiction; intros * Hin;
      try now edestruct IHtcs as (?&?&?&?&?); eauto 6.
    destruct Hin as [E|].
    - inv E; eauto 6.
    - edestruct IHtcs as (?&?&?&?&?); eauto 6.
  Qed.

  Lemma calls_of_Is_sub_in:
    forall tcs s,
      InMembers s (calls_of tcs) -> exists k, Is_sub_in s k tcs.
  Proof.
    intros * Hin; exists 1.
    induction tcs as [|[]]; simpl in *; try contradiction;
      try (now right; apply IHtcs; auto).
    destruct Hin as [E|].
    - subst; left; constructor.
    - right; apply IHtcs; auto.
  Qed.

  Lemma resets_of_app:
    forall tcs tcs',
      resets_of (tcs ++ tcs') = resets_of tcs ++ resets_of tcs'.
  Proof.
    induction tcs as [|[]]; intros; simpl; try f_equal; auto.
  Qed.

  Definition is_step_in_tc_b (s: ident) (tc: trconstr) : bool :=
    match tc with
    | TcCall s' _ _ _ _ _ => ident_eqb s s'
    | _ => false
    end.

  Definition is_step_in_tcs_b (s: ident) (tcs: list trconstr) : bool :=
    existsb (is_step_in_tc_b s) tcs.

  Definition is_reset_in_tc_b (s: ident) (tc: trconstr) : bool :=
    match tc with
    | TcReset s' _ _ => ident_eqb s s'
    | _ => false
    end.

  Definition is_reset_in_tcs_b (s: ident) (tcs: list trconstr) : bool :=
    existsb (is_reset_in_tc_b s) tcs.

  Fact Step_in_tc_reflect:
    forall s tc,
      Is_sub_in_tc s 1 tc <-> is_step_in_tc_b s tc = true.
  Proof.
    destruct tc; simpl; split;
      try discriminate; try now inversion 1.
    - inversion_clear 1; apply ident_eqb_refl.
    - rewrite ident_eqb_eq; intros; subst; constructor.
  Qed.

  Corollary Step_in_reflect:
    forall s tcs,
      Step_in s tcs <-> is_step_in_tcs_b s tcs = true.
  Proof.
    setoid_rewrite existsb_exists; setoid_rewrite Exists_exists.
    split; intros (?&?& Step); apply Step_in_tc_reflect in Step; eauto.
  Qed.

  Lemma Step_in_dec:
    forall s tcs,
      { Step_in s tcs } + { ~ Step_in s tcs }.
  Proof.
    intros;
      eapply Bool.reflect_dec, Bool.iff_reflect, Step_in_reflect.
  Qed.

  Fact Reset_in_tc_reflect:
    forall s tc,
      Is_sub_in_tc s 0 tc <-> is_reset_in_tc_b s tc = true.
  Proof.
    destruct tc; simpl; split;
      try discriminate; try now inversion 1.
    - inversion_clear 1; apply ident_eqb_refl.
    - rewrite ident_eqb_eq; intros; subst; constructor.
  Qed.

  Corollary Reset_in_reflect:
    forall s tcs,
      Reset_in s tcs <-> is_reset_in_tcs_b s tcs = true.
  Proof.
    setoid_rewrite existsb_exists; setoid_rewrite Exists_exists.
    split; intros (?&?& Step); apply Reset_in_tc_reflect in Step; eauto.
  Qed.

  Lemma Reset_in_dec:
    forall s tcs,
      { Reset_in s tcs } + { ~ Reset_in s tcs }.
  Proof.
    intros;
      eapply Bool.reflect_dec, Bool.iff_reflect, Reset_in_reflect.
  Qed.

  Lemma variables_app:
    forall tcs tcs',
      variables (tcs ++ tcs') = variables tcs ++ variables tcs'.
  Proof.
    unfold variables.
    induction tcs as [|[]]; simpl; intros; auto.
    - f_equal; auto.
    - rewrite <-app_assoc; f_equal; auto.
  Qed.

  Lemma not_Is_sub_in_cons:
    forall s tc tcs,
      (forall k, ~ Is_sub_in s k (tc :: tcs)) <-> (forall k, ~ Is_sub_in_tc s k tc) /\ (forall k, ~ Is_sub_in s k tcs).
  Proof.
    split; intros HH.
    - split; intros ? ?; eapply HH; unfold Is_sub_in; eauto.
    - intro; destruct HH; inversion_clear 1; intuition; eauto.
  Qed.

End STCSYNTAX.

Module StcSyntaxFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (CESyn : CESYNTAX Op)
       <: STCSYNTAX Ids Op CESyn.
  Include STCSYNTAX Ids Op CESyn.
End StcSyntaxFun.
