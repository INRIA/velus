Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.CoreExpr.CESyntax.
Require Import Velus.Clocks.

Require Import Permutation.
Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Module Type SBSYNTAX
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import CESyn : CESYNTAX Op).

  (** ** Equations *)

  Inductive equation :=
  | EqDef       : ident -> clock -> cexp -> equation
  | EqNext      : ident -> clock -> lexp -> equation
  | EqReset     : ident -> clock -> ident -> equation
  (* <trans s> =ck reset block<last s> *)
  | EqCall      : ident -> idents -> clock -> bool -> ident -> list lexp -> equation.
  (* <next s> y1, ..., yn =ck block<if b then trans s else last s>(e1, ..., em) *)

  Definition variables_eq (eq: equation): idents :=
    match eq with
    | EqDef x _ _ => [x]
    | EqCall _ xs _ _ _ _ => xs
    | _ => []
    end.

  Definition variables := flat_map variables_eq.

  Inductive Is_state_in_eq: ident -> nat -> equation -> Prop :=
  | StateEqReset:
      forall s ck b,
        Is_state_in_eq s 0 (EqReset s ck b)
  | StateEqCall:
      forall s xs ck rst b es,
        Is_state_in_eq s 1 (EqCall s xs ck rst b es).

  Definition Is_state_in (s: ident) (k: nat) (eqs: list equation) : Prop :=
    Exists (Is_state_in_eq s k) eqs.

  Definition Reset_in (s: ident) := Is_state_in s 0.

  Definition Step_in (s: ident) := Is_state_in s 1.

  Inductive Step_with_reset_in_eq: ident -> bool -> equation -> Prop :=
    Step_with_reset_in_eq_intro:
      forall s ys ck rst f es,
        Step_with_reset_in_eq s rst (EqCall s ys ck rst f es).

  Definition Step_with_reset_in (s: ident) (rst: bool) (eqs: list equation) : Prop :=
    Exists (Step_with_reset_in_eq s rst) eqs.

  Fixpoint lasts_of (eqs: list equation) : list ident :=
    match eqs with
    | [] => []
    | EqNext x _ _ :: eqs => x :: (lasts_of eqs)
    | _ :: eqs => lasts_of eqs
    end.

  Fixpoint calls_of (eqs: list equation) : list (ident * ident) :=
    match eqs with
    | [] => []
    | EqCall s _ _ _ b _ :: eqs => (s, b) :: calls_of eqs
    | _ :: eqs => calls_of eqs
    end.

  Fixpoint resets_of (eqs: list equation) : list (ident * ident) :=
    match eqs with
    | [] => []
    | EqReset s _ b :: eqs => (s, b) :: resets_of eqs
    | _ :: eqs => resets_of eqs
    end.

  Record block :=
    Block {
        b_name  : ident;
        b_in    : list (ident * (type * clock));
        b_vars  : list (ident * (type * clock));
        b_lasts : list (ident * (const * clock));
        b_blocks: list (ident * ident);
        b_out   : list (ident * (type * clock));
        b_eqs   : list equation;

        b_ingt0 : 0 < length b_in;

        b_nodup : NoDup (map fst b_in ++ map fst b_vars ++ map fst b_out ++ map fst b_lasts);
        b_nodup_lasts_blocks: NoDup (map fst b_lasts ++ map fst b_blocks);

        b_blocks_in_eqs: forall f, In f (map snd b_blocks) <-> In f (map snd (calls_of b_eqs ++ resets_of b_eqs));
        b_blocks_calls_of: Permutation b_blocks (calls_of b_eqs);

        b_lasts_in_eqs: Permutation (map fst b_lasts) (lasts_of b_eqs);
        b_vars_out_in_eqs: Permutation (map fst b_vars ++ map fst b_out) (variables b_eqs);

        b_no_single_reset: forall s, Reset_in s b_eqs -> Step_with_reset_in s true b_eqs;
        b_reset_in: forall s rst, Step_with_reset_in s rst b_eqs ->
                             if rst then Reset_in s b_eqs else ~ Reset_in s b_eqs;
        b_reset_incl: incl (resets_of b_eqs) (calls_of b_eqs);

        b_good: Forall ValidId (b_in ++ b_vars ++ b_out)
                /\ Forall ValidId b_lasts
                /\ Forall ValidId b_blocks
                /\ valid b_name
      }.

  Lemma b_nodup_lasts:
    forall b, NoDupMembers b.(b_lasts).
  Proof.
    intro; pose proof (b_nodup b) as Nodup.
    apply fst_NoDupMembers.
    rewrite 2 app_assoc in Nodup.
    rewrite Permutation_app_comm in Nodup.
    apply NoDup_app_weaken in Nodup; auto.
  Qed.

  Lemma b_nodup_blocks:
    forall b, NoDupMembers b.(b_blocks).
  Proof.
    intro; pose proof (b_nodup_lasts_blocks b) as Nodup.
    rewrite Permutation_app_comm in Nodup.
    apply NoDup_app_weaken in Nodup.
    apply fst_NoDupMembers; auto.
  Qed.

  Lemma b_nodup_vars:
    forall b, NoDupMembers (b_in b ++ b_vars b ++ b_out b).
  Proof.
    intro; pose proof (b_nodup b) as Nodup.
    rewrite 2 app_assoc in Nodup.
    apply NoDup_app_weaken in Nodup.
    rewrite <-2 map_app, <-app_assoc in Nodup.
    apply fst_NoDupMembers; auto.
  Qed.

  Lemma b_nodup_variables:
    forall b, NoDup (variables b.(b_eqs)).
  Proof.
    intro; rewrite <-b_vars_out_in_eqs, <-map_app.
    apply fst_NoDupMembers.
    eapply NoDupMembers_app_r, b_nodup_vars.
  Qed.

  Definition program := list block.

  Fixpoint find_block (b: ident) (P: program) : option (block * program) :=
   match P with
   | [] => None
   | bl :: P =>
     if ident_eqb bl.(b_name) b
     then Some (bl, P) else find_block b P
   end.

  (** Properties of block lookups *)

  Remark find_block_app:
    forall b P bl P',
      find_block b P = Some (bl, P') ->
      exists P'',
        P = P'' ++ bl :: P'
        /\ find_block b P'' = None.
  Proof.
    intros * Hfind.
    induction P; inversion Hfind as [H].
    destruct (ident_eqb (b_name a) b) eqn: E.
    - inversion H; subst.
      exists nil; auto.
    - specialize (IHP H).
      destruct IHP as (P'' & HP'' & Hnone).
      rewrite HP''.
      exists (a :: P''); split; auto.
      simpl; rewrite E; auto.
  Qed.

  Remark find_block_name:
    forall b P bl P',
      find_block b P = Some (bl, P') ->
      bl.(b_name) = b.
  Proof.
    intros * Hfind.
    induction P; inversion Hfind as [H].
    destruct (ident_eqb (b_name a) b) eqn: E.
    - inversion H; subst.
      now apply ident_eqb_eq.
    - now apply IHP.
  Qed.

  Remark find_block_other:
    forall b P bl,
      bl.(b_name) <> b ->
      find_block b (bl :: P) = find_block b P.
  Proof.
    intros * Hnb.
    apply ident_eqb_neq in Hnb.
    simpl; rewrite Hnb; reflexivity.
  Qed.

  Remark find_block_In:
    forall b P bl P',
      find_block b P = Some (bl, P') ->
      In bl P.
  Proof.
    intros * Hfind.
    induction P; inversion Hfind as [H].
    destruct (ident_eqb (b_name a) b) eqn: E.
    - inversion H; subst.
      apply in_eq.
    - apply in_cons; auto.
  Qed.

  Lemma find_block_app':
    forall b P P',
      find_block b (P ++ P') =
      match find_block b P with
      | None => find_block b P'
      | Some (bl, P'') => Some (bl, P'' ++ P')
      end.
  Proof.
    induction P as [|bl P]; simpl; auto.
    intro; destruct (ident_eqb bl.(b_name) b); auto.
  Qed.

  Lemma Step_with_reset_in_Step_in:
    forall eqs s rst,
      Step_with_reset_in s rst eqs ->
      Step_in s eqs.
  Proof.
    induction 1 as [?? Step|].
    - inv Step; left; constructor.
    - right; auto.
  Qed.

  Lemma Step_with_reset_in_cons_not_call:
    forall eqs eq s rst,
      (forall s ys ck rst f es, eq <> EqCall s ys ck rst f es) ->
      (Step_with_reset_in s rst (eq :: eqs) <-> Step_with_reset_in s rst eqs).
  Proof.
    intros * Neq; split.
    - inversion_clear 1 as [?? Step|]; auto.
      inv Step; exfalso; eapply Neq; eauto.
    - right; auto.
  Qed.

  Lemma Step_with_reset_in_cons_call:
    forall eqs s (rst: bool) s' ys ck rst' f es,
      s <> s' ->
      (Step_with_reset_in s rst (EqCall s' ys ck rst' f es :: eqs) <-> Step_with_reset_in s rst eqs).
  Proof.
    intros * Neq; split.
    - inversion_clear 1 as [?? Step|]; auto.
      inv Step; congruence.
    - right; auto.
  Qed.

  Lemma calls_of_In:
    forall eqs s b,
      In (s, b) (calls_of eqs) ->
      exists xs ck rst es, In (EqCall s xs ck rst b es) eqs.
  Proof.
    induction eqs as [|[]]; simpl; try contradiction; intros * Hin;
      try now edestruct IHeqs as (?&?&?&?&?); eauto 6.
    destruct Hin as [E|].
    - inv E; eauto 6.
    - edestruct IHeqs as (?&?&?&?&?); eauto 6.
  Qed.

  Lemma calls_of_Is_state_in:
    forall eqs s,
      InMembers s (calls_of eqs) -> exists k, Is_state_in s k eqs.
  Proof.
    intros * Hin; exists 1.
    induction eqs as [|[]]; simpl in *; try contradiction;
      try (now right; apply IHeqs; auto).
    destruct Hin as [E|].
    - subst; left; constructor.
    - right; apply IHeqs; auto.
  Qed.

  Lemma resets_of_app:
    forall eqs eqs',
      resets_of (eqs ++ eqs') = resets_of eqs ++ resets_of eqs'.
  Proof.
    induction eqs as [|[]]; intros; simpl; try f_equal; auto.
  Qed.

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
    - rewrite ident_eqb_eq; intros; subst; constructor.
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
    - rewrite ident_eqb_eq; intros; subst; constructor.
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

  Lemma variables_app:
    forall eqs eqs',
      variables (eqs ++ eqs') = variables eqs ++ variables eqs'.
  Proof.
    unfold variables.
    induction eqs as [|[]]; simpl; intros; auto.
    - f_equal; auto.
    - rewrite <-app_assoc; f_equal; auto.
  Qed.

  Lemma not_Is_state_in_cons:
    forall s eq eqs,
      (forall k, ~ Is_state_in s k (eq :: eqs)) <-> (forall k, ~ Is_state_in_eq s k eq) /\ (forall k, ~ Is_state_in s k eqs).
  Proof.
    split; intros HH.
    - split; intros ? ?; eapply HH; unfold Is_state_in; eauto.
    - intro; destruct HH; inversion_clear 1; intuition; eauto.
  Qed.

End SBSYNTAX.

Module SBSyntaxFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (CESyn : CESYNTAX Op)
       <: SBSYNTAX Ids Op CESyn.
  Include SBSYNTAX Ids Op CESyn.
End SBSyntaxFun.
