Require Import Velus.Common.
Require Import Velus.Operators.
Require Import Velus.NLustre.NLExprSyntax.
Require Import Velus.Clocks.

Require Import Permutation.
Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Module Type SBSYNTAX
       (Import Ids     : IDS)
       (Import Op      : OPERATORS)
       (Import Clks    : CLOCKS       Ids)
       (Import ExprSyn : NLEXPRSYNTAX     Op).

  (** ** Equations *)

  Inductive equation :=
  | EqDef       : ident -> clock -> cexp -> equation
  | EqNext      : ident -> clock -> lexp -> equation
  | EqReset     : ident -> clock -> ident -> equation
  (* <trans s> =ck reset block<last s> *)
  | EqCall      : ident -> idents -> clock -> bool -> ident -> list lexp -> equation.
  (* <next s> y1, ..., yn =ck block<if b then trans s else last s>(e1, ..., em) *)

  Inductive Is_last_in_eq: ident -> equation -> Prop :=
    LastEqNext:
      forall x ck e,
        Is_last_in_eq x (EqNext x ck e).

  Definition Is_last_in (x: ident) (eqs: list equation) : Prop :=
    Exists (Is_last_in_eq x) eqs.

  Inductive Is_block_in_eq : ident -> equation -> Prop :=
  | Is_block_inEqCall:
      forall s ys ck rst f es,
        Is_block_in_eq f (EqCall s ys ck rst f es)
  | Is_block_inEqReset:
      forall s ck f,
        Is_block_in_eq f (EqReset s ck f).

  Definition Is_block_in (f: ident) (eqs: list equation) : Prop :=
    Exists (Is_block_in_eq f) eqs.

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

  Definition Is_defined_in (x: ident) (eqs: list equation) : Prop :=
    Exists (Is_defined_in_eq x) eqs.

  Inductive Is_variable_in_eq: ident -> equation -> Prop :=
  | VarEqDef:
      forall x ck e,
        Is_variable_in_eq x (EqDef x ck e)
  | VarEqCall:
      forall x s xs ck rst b es,
        In x xs ->
        Is_variable_in_eq x (EqCall s xs ck rst b es).

  Definition Is_variable_in (x: ident) (eqs: list equation) : Prop :=
    Exists (Is_variable_in_eq x) eqs.

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

  Fixpoint lasts_of (eqs: list equation) : list ident :=
    match eqs with
    | [] => []
    | EqNext x _ _ :: eqs => x :: (lasts_of eqs)
    | _ :: eqs => lasts_of eqs
    end.

  Lemma lasts_of_in:
    forall eqs x,
      Is_last_in x eqs <-> In x (lasts_of eqs).
  Proof.
    induction eqs as [|[]]; simpl.
    - now setoid_rewrite Exists_nil.
    - setoid_rewrite <-IHeqs; split; try right; auto.
      inversion_clear 1 as [?? Last|]; try inv Last; auto.
    - setoid_rewrite <-IHeqs; split.
      + inversion_clear 1 as [?? Last|]; try inv Last; auto.
      + intros [E|?].
        * subst; left; constructor.
        * right; auto.
    - setoid_rewrite <-IHeqs; split; try right; auto.
      inversion_clear 1 as [?? Last|]; try inv Last; auto.
    - setoid_rewrite <-IHeqs; split; try right; auto.
      inversion_clear 1 as [?? Last|]; try inv Last; auto.
  Qed.

  Fixpoint states_of (eqs: list equation) : list ident :=
    match eqs with
    | [] => []
    | EqReset s _ _ :: eqs => s :: states_of eqs
    | EqCall s _ _ _ _ _ :: eqs => s :: states_of eqs
    | _ :: eqs => states_of eqs
    end.

  Lemma states_of_in:
    forall eqs s,
      (exists k, Is_state_in s k eqs) <-> In s (states_of eqs).
  Proof.
    induction eqs as [|[]]; simpl.
    - setoid_rewrite Exists_nil; split; try contradiction; intros ** (); eauto.
    - setoid_rewrite <-IHeqs; split; intros ** (); try (eexists; right; eauto).
      inversion_clear 1 as [?? Block|]; try inv Block; eauto.
    - setoid_rewrite <-IHeqs; split; intros ** (); try (eexists; right; eauto).
      inversion_clear 1 as [?? Block|]; try inv Block; eauto.
    - setoid_rewrite <-IHeqs; split.
      + intros ** (); inversion_clear 1 as [?? Block|]; try inv Block; eauto.
      + intros [E|(?&?)].
        * subst; eexists; left; constructor.
        * eexists; right; eauto.
    - setoid_rewrite <-IHeqs; split.
      + intros ** (); inversion_clear 1 as [?? Block|]; try inv Block; eauto.
      + intros [E|(?&?)].
        * subst; eexists; left; constructor.
        * eexists; right; eauto.
  Qed.

  Record block :=
    Block {
        b_name  : ident;
        b_in    : list (ident * type);
        b_vars  : list (ident * type);
        b_lasts : list (ident * const);
        b_blocks: list (ident * ident);
        b_out   : list (ident * type);
        b_eqs   : list equation;

        b_ingt0 : 0 < length b_in;
        (* b_outgt0 : 0 < length b_out *)
        b_nodup : NoDup (map fst b_in ++ map fst b_lasts ++ map fst b_vars ++ map fst b_out);
        b_nodup_lasts_blocks: NoDup (map fst b_lasts ++ map fst b_blocks);

        b_blocks_in_eqs: forall f, (exists i, In (i, f) b_blocks) <-> Is_block_in f b_eqs;
        (* b_lasts_in_eqs: forall x, InMembers x b_lasts <-> Is_last_in_eqs x b_eqs; *)
        b_lasts_in_eqs: Permutation (map fst b_lasts) (lasts_of b_eqs);
        b_vars_out_in_eqs: forall x, InMembers x (b_vars ++ b_out) <-> Is_variable_in x b_eqs;
        (* b_out_not_last: forall x, InMembers x b_out -> ~ Is_last_in_eqs x b_eqs; *)

        (* b_states_in_eqs: forall s, InMembers s b_blocks <-> (exists k, Is_state_in s k b_eqs); *)
        b_states_in_eqs: Permutation (map fst b_blocks) (states_of b_eqs);

        b_no_single_reset: forall s, Reset_in s b_eqs -> Step_in s b_eqs;

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
    apply NoDup_comm, NoDup_app_weaken, NoDup_app_weaken in Nodup; auto.
  Qed.

  Lemma b_nodup_lasts_of:
    forall b, NoDup (lasts_of b.(b_eqs)).
  Proof.
    setoid_rewrite <-b_lasts_in_eqs;
      setoid_rewrite <-fst_NoDupMembers.
    apply b_nodup_lasts.
  Qed.

  Lemma b_nodup_blocks:
    forall b, NoDupMembers b.(b_blocks).
  Proof.
    intro; pose proof (b_nodup_lasts_blocks b) as Nodup.
    apply NoDup_comm, NoDup_app_weaken in Nodup.
    apply fst_NoDupMembers; auto.
  Qed.

  Lemma b_nodup_states_of:
    forall b, NoDup (states_of b.(b_eqs)).
  Proof.
    setoid_rewrite <-b_states_in_eqs;
      setoid_rewrite <-fst_NoDupMembers.
    apply b_nodup_blocks.
  Qed.

  Lemma b_nodup_vars:
    forall b, NoDupMembers (b_in b ++ b_vars b ++ b_out b).
  Proof.
    intro; pose proof (b_nodup b) as Nodup.
    apply NoDup_comm in Nodup.
    rewrite <-app_assoc in Nodup.
    apply NoDup_comm, NoDup_app_weaken in Nodup.
    apply NoDup_comm in Nodup.
    rewrite app_assoc in Nodup.
    rewrite <-2 map_app, <-app_assoc in Nodup.
    apply fst_NoDupMembers; auto.
  Qed.

  Lemma Is_defined_Is_variable_Is_last_in:
    forall eqs x,
      Is_defined_in x eqs ->
      Is_variable_in x eqs \/ Is_last_in x eqs.
  Proof.
    induction eqs; inversion_clear 1 as [?? Def|?? Defs].
    - inv Def.
      + left; left; constructor; auto.
      + right; left; constructor; auto.
      + left; left; constructor; auto.
    - apply IHeqs in Defs as [].
      + left; right; auto.
      + right; right; auto.
  Qed.

  Lemma b_ins_not_def:
    forall b x,
      InMembers x b.(b_in) ->
      ~ Is_defined_in x b.(b_eqs).
  Proof.
    intros ** Hin Hdef.
    pose proof (b_nodup b) as Nodup.
    eapply (NoDup_app_In x) in Nodup.
    - apply Is_defined_Is_variable_Is_last_in in Hdef as [Var|Last];
        apply Nodup, in_app.
      + apply b_vars_out_in_eqs in Var.
        right; rewrite <-map_app; apply fst_InMembers; auto.
      + apply lasts_of_in in Last; rewrite <-b_lasts_in_eqs in Last; auto.
    - apply fst_InMembers; auto.
  Qed.

  (* TODO: in Common *)
  (* Fixpoint assoc {A} (x: ident) (xs: list (ident * A)) : option A := *)
  (*   match xs with *)
  (*   | [] => None *)
  (*   | y :: xs => *)
  (*     let (y, c) := y in *)
  (*     if ident_eqb y x then Some c else assoc x xs *)
  (*   end. *)

  (* Definition find_last (x: ident) (bl: block) := *)
  (*   assoc x bl.(b_lasts). *)

  (* Definition find_subblock (x: ident) (bl: block) := *)
  (*   assoc x bl.(b_blocks). *)

  Definition program := list block.

  Fixpoint find_block (b: ident) (P: program) : option (block * program) :=
   match P with
   | [] => None
   | bl :: P =>
     if ident_eqb bl.(b_name) b
     then Some (bl, P) else find_block b P
   end.

  (** Properties of block lookups *)

  Lemma find_block_none:
    forall b bl P,
      find_block b (bl :: P) = None
      <-> (bl.(b_name) <> b /\ find_block b P = None).
  Proof.
    intros.
    simpl; destruct (ident_eqb (b_name bl) b) eqn: E.
    - split; intro HH; try discriminate.
      destruct HH.
      apply ident_eqb_eq in E; contradiction.
    - apply ident_eqb_neq in E; split; intro HH; tauto.
  Qed.

  Remark find_block_app:
    forall b P bl P',
      find_block b P = Some (bl, P') ->
      exists P'',
        P = P'' ++ bl :: P'
        /\ find_block b P'' = None.
  Proof.
    intros ** Hfind.
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
    intros ** Hfind.
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
    intros ** Hnb.
    apply ident_eqb_neq in Hnb.
    simpl; rewrite Hnb; reflexivity.
  Qed.

  Remark find_block_other_app:
    forall P b bl P',
      find_block b P = None ->
      bl.(b_name) <> b ->
      find_block b (P ++ bl :: P') = find_block b P'.
  Proof.
    induction P as [|bl']; simpl app.
    - intros; apply find_block_other; auto.
    - intros ** Find E.
      simpl in *.
      destruct (ident_eqb (b_name bl') b); try discriminate; auto.
  Qed.

  Remark find_block_In:
    forall b P bl P',
      find_block b P = Some (bl, P') ->
      In bl P.
  Proof.
    intros ** Hfind.
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

  Lemma find_block_split:
    forall b P bl P',
      find_block b P = Some (bl, P') ->
      exists P1,
        P = P1 ++ bl :: P'.
  Proof.
    induction P as [|bl']; simpl; try discriminate.
    intros ** Find.
    destruct (ident_eqb (b_name bl') b) eqn:E.
    - inv Find; exists []; auto.
    - apply IHP in Find as (P2 & Eq).
      exists (bl' :: P2); rewrite Eq; auto.
  Qed.

  Lemma not_In_find_block:
    forall b P,
      ~In b (map b_name P) ->
      find_block b P = None.
  Proof.
    induction P as [|bl]; auto.
    simpl; intro Hnin.
    apply Decidable.not_or in Hnin.
    destruct Hnin as (Hnin1 & Hnin2).
    rewrite (IHP Hnin2).
    apply ident_eqb_neq in Hnin1.
    now rewrite Hnin1.
  Qed.

  Lemma not_Is_block_in_cons:
    forall b eq eqs,
      ~ Is_block_in b (eq :: eqs) <-> ~Is_block_in_eq b eq /\ ~Is_block_in b eqs.
  Proof.
    split; intro HH.
    - split; intro; apply HH; unfold Is_block_in; intuition.
    - destruct HH; inversion_clear 1; intuition.
  Qed.

  Lemma not_Is_last_in_cons:
    forall x eq eqs,
      ~ Is_last_in x (eq :: eqs) <-> ~ Is_last_in_eq x eq /\ ~ Is_last_in x eqs.
  Proof.
    split; intros HH.
    - split; intro; apply HH; unfold Is_last_in; intuition.
    - destruct HH; inversion_clear 1; intuition.
  Qed.

  Lemma not_Is_state_in_cons:
    forall s k eq eqs,
      ~ Is_state_in s k (eq :: eqs) <-> ~ Is_state_in_eq s k eq /\ ~ Is_state_in s k eqs.
  Proof.
    split; intros HH.
    - split; intro; apply HH; unfold Is_state_in; intuition.
    - destruct HH; inversion_clear 1; intuition.
  Qed.

  Lemma not_Is_state_in_cons':
    forall s eq eqs,
      (forall k, ~ Is_state_in s k (eq :: eqs)) <-> (forall k, ~ Is_state_in_eq s k eq) /\ (forall k, ~ Is_state_in s k eqs).
  Proof.
    split; intros HH.
    - split; intros ? ?; eapply HH; unfold Is_state_in; eauto.
    - intro; destruct HH; inversion_clear 1; intuition; eauto.
  Qed.

End SBSYNTAX.

Module SBSyntaxFun
       (Ids  : IDS)
       (Op   : OPERATORS)
       (Clks : CLOCKS          Ids)
       (ExprSyn : NLEXPRSYNTAX     Op)
       <: SBSYNTAX Ids Op Clks ExprSyn.
  Include SBSYNTAX Ids Op Clks ExprSyn.
End SBSyntaxFun.
