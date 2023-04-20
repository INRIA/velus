From Coq Require Import String.
From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.
From Coq Require Import Permutation.
From Coq Require Import Setoid Morphisms.

From compcert Require Import common.Errors.

From Velus Require Import Common Environment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import AcyGraph.
From Velus Require Import FunctionalEnvironment.
From Velus Require Import Lustre.StaticEnv.
From Velus Require Import Lustre.LSyntax.

(** * Lustre causality *)

Module Type LCAUSALITY
       (Import Ids : IDS)
       (Import Op : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks : CLOCKS Ids Op OpAux)
       (Import Senv : STATICENV Ids Op OpAux Cks)
       (Import Syn : LSYNTAX Ids Op OpAux Cks Senv).

  (** ** Causality definition *)

  (** Variables that appear in the nth stream of an expression, to the left of fbys. *)
  Inductive Is_used_inst (Γ : static_env) (cx : ident) : nat -> exp -> Prop :=
  | IUIvar : forall x a,
      HasCaus Γ x cx ->
      Is_used_inst Γ cx 0 (Evar x a)
  | IUIlast : forall x a,
      HasLastCaus Γ x cx ->
      Is_used_inst Γ cx 0 (Elast x a)
  | IUIunop : forall op e a,
      Is_used_inst Γ cx 0 e ->
      Is_used_inst Γ cx 0 (Eunop op e a)
  | IUIbinop : forall op e1 e2 a,
      Is_used_inst Γ cx 0 e1
      \/ Is_used_inst Γ cx 0 e2 ->
      Is_used_inst Γ cx 0 (Ebinop op e1 e2 a)
  | IUIextcall : forall f es a,
      (exists k, Exists (Is_used_inst Γ cx k) es) ->
      Is_used_inst Γ cx 0 (Eextcall f es a)
  | IUIfby : forall e0s es a k,
      Is_used_inst_list Γ cx k e0s ->
      Is_used_inst Γ cx k (Efby e0s es a)
  | IUIarrow : forall e0s es a k,
      Is_used_inst_list Γ cx k e0s
      \/ Is_used_inst_list Γ cx k es ->
      Is_used_inst Γ cx k (Earrow e0s es a)
  | IUIwhen : forall es x tx b a k,
      (k < length (fst a) /\ HasCaus Γ x cx)
      \/ Is_used_inst_list Γ cx k es ->
      Is_used_inst Γ cx k (Ewhen es (x, tx) b a)
  | IUImerge : forall x es ty a k,
      (k < length (fst a) /\ HasCaus Γ x cx)
      \/ Exists (fun es => Is_used_inst_list Γ cx k (snd es)) es ->
      Is_used_inst Γ cx k (Emerge (x, ty) es a)
  | IUIcase : forall e es d a k,
      (k < length (fst a) /\ Is_used_inst Γ cx 0 e)
      \/ Exists (fun es => Is_used_inst_list Γ cx k (snd es)) es
      \/ (exists d0, d = Some d0 /\ Is_used_inst_list Γ cx k d0) ->
      Is_used_inst Γ cx k (Ecase e es d a)
  | IUIapp : forall f es er a k,
      k < length a ->
      (exists k', Exists (Is_used_inst Γ cx k') es)
      \/ (Exists (Is_used_inst Γ cx 0) er) ->
      Is_used_inst Γ cx k (Eapp f es er a)

  with Is_used_inst_list (Γ : static_env) (cx : ident) : nat -> list exp -> Prop :=
  | IUILnow : forall k e es,
      k < numstreams e ->
      Is_used_inst Γ cx k e ->
      Is_used_inst_list Γ cx k (e::es)
  | IUILlater : forall k e es,
      k >= numstreams e ->
      Is_used_inst_list Γ cx (k - numstreams e) es ->
      Is_used_inst_list Γ cx k (e::es).

  Local Hint Constructors Is_used_inst Is_used_inst_list : lcaus.

  Definition idcaus {A B} (l : list (ident * (A * B * ident))) : list (ident * ident) :=
    map (fun '(x, (_, _, cx)) => (x, cx)) l.

  Fact idcaus_app {A B} : forall (l1 l2 : list (ident * (A * B * ident))),
      idcaus (l1 ++ l2) = idcaus l1 ++ idcaus l2.
  Proof. apply map_app. Qed.

  Fact map_fst_idcaus {A B} : forall (l1 : list (ident * (A * B * ident))),
      map fst (idcaus l1) = map fst l1.
  Proof.
    induction l1 as [|(?&(?&?)&?)]; intros; simpl; f_equal; auto.
  Qed.

  Global Hint Unfold idcaus : list.

  Lemma NoDupMembers_idcaus {A B} : forall (xs : list (ident * (A * B * ident))),
      NoDupMembers (idcaus xs) <-> NoDupMembers xs.
  Proof.
    intros *.
    now rewrite fst_NoDupMembers, map_fst_idcaus, <-fst_NoDupMembers.
  Qed.

  Fact idcaus_of_senv_ins : forall xs,
      idcaus_of_senv (senv_of_ins xs) = idcaus xs.
  Proof.
    intros *. unfold idcaus_of_senv, senv_of_ins, idcaus.
    erewrite map_map, map_ext, map_filter_nil, app_nil_r. reflexivity.
    - simpl_Forall. auto.
    - intros; destruct_conjs; auto.
  Qed.

  Definition replace_idcaus (caus : list (ident * ident)) (Γ: static_env) :=
    List.map (fun '(x, ann) => (x, or_default_with ann (ann_with_caus ann) (assoc_ident x caus))) Γ.
  Global Hint Unfold replace_idcaus : list.

  Lemma replace_idcaus_HasCaus1 : forall caus Γ x cx1 cx2,
      NoDupMembers caus ->
      In (x, cx2) caus ->
      HasCaus Γ x cx1 ->
      HasCaus (replace_idcaus caus Γ) x cx2.
  Proof.
    intros * Hnd Hin Hca.
    inv Hca; econstructor; solve_In.
    erewrite assoc_ident_true; eauto.
    reflexivity.
  Qed.

  Lemma replace_idcaus_HasCaus2 : forall caus Γ x cx,
      ~InMembers x caus ->
      HasCaus Γ x cx ->
      HasCaus (replace_idcaus caus Γ) x cx.
  Proof.
    intros * Hin Hca.
    inv Hca; econstructor; solve_In.
    apply assoc_ident_false in Hin. rewrite Hin; auto.
  Qed.

  Lemma replace_idcaus_HasCaus3 : forall caus Γ x cx,
      HasCaus (replace_idcaus caus Γ) x cx ->
      HasCaus Γ x cx \/ In (x, cx) caus.
  Proof.
    unfold replace_idcaus.
    intros * Hca. inv Hca; simpl_In.
    destruct (assoc_ident x caus) eqn:Hassc; simpl; eauto with senv.
    apply assoc_ident_In in Hassc; auto.
  Qed.

  Fact ann_with_caus_causl_last : forall a o,
      causl_last (or_default_with a (ann_with_caus a) o) = causl_last a.
  Proof.
    intros. destruct o; simpl; auto.
  Qed.

  Lemma replace_idcaus_IsVar: forall caus Γ x,
      IsVar (replace_idcaus caus Γ) x <-> IsVar Γ x.
  Proof.
    split; intros * Hl; inv Hl; simpl_In; econstructor;
      rewrite fst_InMembers in *; solve_In; eauto.
  Qed.

  Lemma replace_idcaus_HasType: forall caus Γ x ty,
      HasType (replace_idcaus caus Γ) x ty <-> HasType Γ x ty.
  Proof.
    split; intros * Hl; inv Hl; simpl_In; econstructor; solve_In; eauto.
    1,2:destruct (assoc_ident _ _); auto.
  Qed.

  Lemma replace_idcaus_HasClock: forall caus Γ x ck,
      HasClock (replace_idcaus caus Γ) x ck <-> HasClock Γ x ck.
  Proof.
    split; intros * Hl; inv Hl; simpl_In; econstructor; solve_In; eauto.
    1,2:destruct (assoc_ident _ _); auto.
  Qed.

  Lemma replace_idcaus_IsLast: forall caus Γ x,
      IsLast (replace_idcaus caus Γ) x <-> IsLast Γ x.
  Proof.
    split; intros * Hl; inv Hl; simpl_In; econstructor; solve_In; eauto.
    all:now rewrite ann_with_caus_causl_last in *.
  Qed.

  Lemma replace_idcaus_HasLastCaus : forall caus Γ x ck,
      HasLastCaus (replace_idcaus caus Γ) x ck <-> HasLastCaus Γ x ck.
  Proof.
    split; intros * Hl; inv Hl; simpl_In; econstructor; solve_In; eauto.
    1,2:destruct (assoc_ident _ _); auto.
  Qed.

  Lemma map_fst_replace_idcaus : forall caus Γ,
      map fst (replace_idcaus caus Γ) = map fst Γ.
  Proof.
    intros. unfold replace_idcaus.
    erewrite map_map, map_ext; auto. intros; destruct_conjs; auto.
  Qed.

  Global Hint Rewrite -> replace_idcaus_IsVar replace_idcaus_HasType replace_idcaus_HasClock replace_idcaus_IsLast replace_idcaus_HasLastCaus : list.
  Global Hint Rewrite -> map_fst_replace_idcaus.

  Lemma replace_idcaus_HasCaus_incl caus : forall Γ Γ',
      (forall x cx, HasCaus Γ x cx -> HasCaus Γ' x cx) ->
      (forall x cx, HasCaus (replace_idcaus caus Γ) x cx -> HasCaus (replace_idcaus caus Γ') x cx).
  Proof.
    intros * Hincl * Hca.
    inv Hca; simpl_In.
    assert (HasCaus Γ' x a.(causl)) as Hca' by eauto with senv. inv Hca'.
    econstructor. solve_In.
    destruct (assoc_ident _ _); auto.
  Qed.

  Lemma replace_idcaus_HasLastCaus_incl caus : forall Γ Γ',
      (forall x cx, HasLastCaus Γ x cx -> HasLastCaus Γ' x cx) ->
      (forall x cx, HasLastCaus (replace_idcaus caus Γ) x cx -> HasLastCaus (replace_idcaus caus Γ') x cx).
  Proof.
    intros * Hincl * Hca.
    inv Hca; simpl_In.
    eapply Hincl. econstructor; eauto.
    destruct (assoc_ident _ _); simpl; auto.
  Qed.

  Fact replace_idcaus_In_snd : forall Γ caus cx,
      In cx (map snd (idcaus_of_senv (replace_idcaus caus Γ))) ->
      In cx (map snd (idcaus_of_senv Γ)) \/ In cx (map snd caus).
  Proof.
    intros * Hin. unfold idcaus_of_senv in *. simpl_app.
    repeat rewrite in_app_iff in *. destruct Hin; simpl_In.
    - destruct (assoc_ident i caus) eqn:Hassc; simpl.
      + apply assoc_ident_In in Hassc. right; solve_In.
      + left; left; solve_In.
    - left; right. rewrite ann_with_caus_causl_last in Hf0. solve_In.
      2:rewrite Hf0; simpl; auto. auto.
  Qed.

  Lemma replace_idcaus_NoDup : forall Γ caus xs,
      NoDupMembers Γ ->
      NoDup (map snd (idcaus_of_senv Γ ++ caus ++ xs)) ->
      NoDup (map snd (idcaus_of_senv (replace_idcaus caus Γ) ++ xs)).
  Proof.
    intros * Hnd1 Hnd. simpl_app.
    apply NoDup_app'; eauto using NoDup_app_r.
    - rewrite app_assoc in Hnd. apply NoDup_app_l in Hnd.
      unfold idcaus_of_senv in *. simpl_app. apply NoDup_app'.
      2:{ apply NoDup_app_r, NoDup_app_l in Hnd.
          erewrite map_filter_map, map_filter_ext; eauto.
          intros; destruct_conjs. now rewrite ann_with_caus_causl_last. }
      2:{ simpl_Forall. intros Hnin.
          simpl_In. rewrite ann_with_caus_causl_last in Hf0.
          rewrite Permutation_swap in Hnd. eapply NoDup_app_In in Hnd. 2:solve_In; rewrite Hf0; simpl; eauto.
          eapply Hnd; simpl. rewrite in_app_iff.
          destruct (assoc_ident _ _) eqn:Hassc; simpl in *.
          - apply assoc_ident_In in Hassc. right. solve_In.
          - left. clear Hin. solve_In. }
      rewrite Permutation_swap in Hnd. apply NoDup_app_r in Hnd.
      induction Γ as [|(?&?)]; simpl in *. constructor.
      inv Hnd1. inv Hnd. constructor; auto. clear IHΓ.
      intros Hnin. simpl_In.
      destruct (assoc_ident i0 _) eqn:Hassc1, (assoc_ident i _) eqn:Hassc2; simpl in *; subst.
      + apply assoc_ident_In in Hassc1. apply assoc_ident_In in Hassc2.
        eapply NoDup_snd_det in Hassc1; eauto using NoDup_app_r; subst.
        eapply H1. solve_In.
      + apply H2, in_app_iff.
        apply assoc_ident_In in Hassc1. right. solve_In.
      + apply assoc_ident_In in Hassc2.
        rewrite <-map_app in H4. eapply NoDup_snd_det in H4; try rewrite in_app_iff; [|left|right]; eauto. 2:solve_In.
        subst. apply assoc_ident_false in Hassc1.
        apply Hassc1. solve_In.
      + apply H2, in_app_iff.
        rewrite <-H5. left. solve_In.
    - simpl_Forall.
      rewrite app_assoc in Hnd. eapply NoDup_app_In in Hnd; eauto.
      rewrite in_app_iff. apply replace_idcaus_In_snd; solve_In.
  Qed.

  Inductive Is_defined_in_scope {A} (Pdef : static_env -> A -> Prop) Γ (cx: ident) : scope A -> Prop :=
  | DefScope1 : forall locs blks,
      Pdef (Γ++senv_of_decls locs) blks ->
      Is_defined_in_scope Pdef Γ cx (Scope locs blks).

  Inductive Is_defined_in_branch {A} (Pdef : static_env -> A -> Prop) Γ (cx: ident) : branch A -> Prop :=
  | DefBranch1 : forall caus blks,
      Pdef (replace_idcaus caus Γ) blks ->
      Is_defined_in_branch Pdef Γ cx (Branch caus blks)
  | DefBranch2 : forall caus blks x,
      InMembers x caus ->
      HasCaus Γ x cx ->
      Is_defined_in_branch Pdef Γ cx (Branch caus blks).

  Inductive Is_defined_in Γ (cx : ident) : block -> Prop :=
  | DefEq : forall x xs es,
      In x xs ->
      HasCaus Γ x cx ->
      Is_defined_in Γ cx (Beq (xs, es))
  | DefLast : forall x e,
      HasLastCaus Γ x cx ->
      Is_defined_in Γ cx (Blast x e)
  | DefReset : forall blocks er,
      Exists (Is_defined_in Γ cx) blocks ->
      Is_defined_in Γ cx (Breset blocks er)
  | DefSwitch : forall ec branches,
      Exists (fun blks => Is_defined_in_branch (fun Γ => Exists (Is_defined_in Γ cx)) Γ cx (snd blks)) branches ->
      Is_defined_in Γ cx (Bswitch ec branches)
  | DefAuto : forall type ini states ck,
      Exists (fun blks => Is_defined_in_branch
                         (fun Γ blks => Is_defined_in_scope
                                       (fun Γ blks => Exists (Is_defined_in Γ cx) (fst blks))
                                       Γ cx (snd blks))
                         Γ cx (snd blks)) states ->
      Is_defined_in Γ cx (Bauto type ck ini states)
  | DefLocal : forall scope,
      Is_defined_in_scope (fun Γ => Exists (Is_defined_in Γ cx)) Γ cx scope ->
      Is_defined_in Γ cx (Blocal scope).

  Inductive depends_on_scope {A} (P_dep : _ -> _ -> _ -> _ -> Prop) Γ (cx cy : ident) : scope A -> Prop :=
  | DepOnScope1 : forall locs blks Γ',
      Γ' = Γ ++ senv_of_decls locs ->
      P_dep Γ' cx cy blks ->
      depends_on_scope P_dep Γ cx cy (Scope locs blks).

  Inductive depends_on_branch {A} (P_dep : _ -> _ -> _ -> _ -> Prop) Γ (cx cy : ident) : branch A -> Prop :=
  | DepOnBranch1 : forall caus blks,
      P_dep (replace_idcaus caus Γ) cx cy blks ->
      depends_on_branch P_dep Γ cx cy (Branch caus blks)
  | DepOnBranch2 : forall caus blks x,
      HasCaus Γ x cx ->
      In (x, cy) caus ->
      depends_on_branch P_dep Γ cx cy (Branch caus blks).

  Inductive depends_on Γ (cx cy : ident) : block -> Prop :=
  | DepOnEq : forall xs es k x,
      nth_error xs k = Some x ->
      HasCaus Γ x cx ->
      Is_used_inst_list Γ cy k es ->
      depends_on Γ cx cy (Beq (xs, es))

  | DepOnLast: forall x e,
      HasLastCaus Γ x cx ->
      Is_used_inst Γ cy 0 e ->
      depends_on Γ cx cy (Blast x e)

  | DepOnReset1 : forall blocks er,
      Exists (depends_on Γ cx cy) blocks ->
      depends_on Γ cx cy (Breset blocks er)
  | DepOnReset2 : forall blocks er,
      Is_defined_in Γ cx (Breset blocks er) ->
      Is_used_inst Γ cy 0 er ->
      depends_on Γ cx cy (Breset blocks er)

  | DepOnSwitch1 : forall ec branches,
      Exists (fun blks => depends_on_branch (fun Γ cx cy => Exists (depends_on Γ cx cy)) Γ cx cy (snd blks)) branches ->
      depends_on Γ cx cy (Bswitch ec branches)
  | DepOnSwitch2 : forall ec branches,
      Is_defined_in Γ cx (Bswitch ec branches) ->
      Is_used_inst Γ cy 0 ec ->
      depends_on Γ cx cy (Bswitch ec branches)

  | DepOnAuto1 : forall type ini states ck,
      Exists (fun blks => depends_on_branch
                         (fun Γ ck cy blks => depends_on_scope
                                             (fun Γ cx cy blks => Exists (depends_on Γ cx cy) (fst blks))
                                             Γ cx cy (snd blks))
                         Γ cx cy (snd blks)) states ->
      depends_on Γ cx cy (Bauto type ck ini states)
  | DepOnAuto2 : forall type ini oth states ck y,
      Is_defined_in Γ cx (Bauto type ck (ini, oth) states) ->
      Is_free_in_clock y ck ->
      HasCaus Γ y cy ->
      depends_on Γ cx cy (Bauto type ck (ini, oth) states)
  | DepOnAuto3 : forall type ini oth states ck,
      Is_defined_in Γ cx (Bauto type ck (ini, oth) states) ->
      Exists (fun '(e, _) => Is_used_inst Γ cy 0 e) ini ->
      depends_on Γ cx cy (Bauto type ck (ini, oth) states)
  | DepOnAuto4 : forall type ini oth states ck,
      Is_defined_in Γ cx (Bauto type ck (ini, oth) states) ->
      Exists (fun '(_, Branch _ (unl, _)) => Exists (fun '(e, _) => Is_used_inst Γ cy 0 e) unl) states ->
      depends_on Γ cx cy (Bauto type ck (ini, oth) states)

  | DepOnLocal : forall scope,
      depends_on_scope (fun Γ cx cy => Exists (depends_on Γ cx cy)) Γ cx cy scope ->
      depends_on Γ cx cy (Blocal scope).

  Inductive depends_on_node {PSyn prefs} (cx cy : ident) : @node PSyn prefs -> Prop :=
  | DepOnNode1 : forall n,
      depends_on (senv_of_ins (n_in n) ++ senv_of_decls (n_out n)) cx cy (n_block n) ->
      depends_on_node cx cy n.

  Ltac inv_scope :=
    match goal with
    | H:Is_defined_in_scope _ _ _ _ |- _ => inv H
    | H:depends_on_scope _ _ _ _ _ |- _ => inv H
    end;
    destruct_conjs; subst.

  Ltac inv_branch :=
    match goal with
    | H:Is_defined_in_branch _ _ _ _ |- _ => inv H
    | H:depends_on_branch _ _ _ _ _ |- _ => inv H
    end;
    destruct_conjs; subst.

  Ltac inv_block :=
    match goal with
    | H:Is_defined_in _ _ _ |- _ => inv H
    | H:depends_on _ _ _ _ |- _ => inv H
    end.

  Section incl.
    Fact Is_used_inst_list_incl' : forall Γ Γ' es,
      Forall (fun e => forall cx k, Is_used_inst Γ cx k e -> Is_used_inst Γ' cx k e) es ->
      forall cx k, Is_used_inst_list Γ cx k es ->
              Is_used_inst_list Γ' cx k es.
    Proof.
      intros * Hf * Hex.
      induction Hex; inv Hf; [left|right]; auto.
    Qed.

    Lemma Is_used_inst_incl : forall Γ Γ' e,
        (forall x cx, HasCaus Γ x cx -> HasCaus Γ' x cx) ->
        (forall x cx, HasLastCaus Γ x cx -> HasLastCaus Γ' x cx) ->
        forall cx k, Is_used_inst Γ cx k e ->
                Is_used_inst Γ' cx k e.
    Proof.
      intros * Hc1 Hc2.
      induction e using exp_ind2; intros * Hfree; inv Hfree; constructor;
        repeat (match goal with
                | H: _ \/ _ |- _ \/ _ => destruct H; [left|right]
                | H: _ /\ _ |- _ /\ _ => destruct H; split; auto
                | H: Exists _ _ |- Exists _ _ => solve_Exists; simpl_Forall
                | H: exists _, Exists _ _ |- _ => destruct H as (x&?); exists x
                | H : exists _, _ /\ _ |- exists _, _ /\ _ => destruct H as (x&?&?); subst; esplit; split
                | H: Is_used_inst_list _ _ _ _ |- _ => eapply Is_used_inst_list_incl' in H; eauto
                end);
        eauto using Is_used_inst.
    Qed.

    Fact Is_defined_in_scope_incl {A} P_def : forall locs (blk: A) Γ Γ' cx,
        (forall x cx, HasCaus Γ x cx -> HasCaus Γ' x cx) ->
        (forall x cx, HasLastCaus Γ x cx -> HasLastCaus Γ' x cx) ->
        Is_defined_in_scope P_def Γ cx (Scope locs blk) ->
        (forall Γ Γ',
            (forall x cx, HasCaus Γ x cx -> HasCaus Γ' x cx) ->
            (forall x cx, HasLastCaus Γ x cx -> HasLastCaus Γ' x cx) ->
            P_def Γ blk ->
            P_def Γ' blk) ->
        Is_defined_in_scope P_def Γ' cx (Scope locs blk).
    Proof.
      intros * Hc Hcl Hdef Hind; inv_scope.
      econstructor. eapply Hind; [| |eauto].
      - intros *. rewrite 2 HasCaus_app. intros [|]; eauto.
      - intros *. rewrite 2 HasLastCaus_app. intros [|]; eauto.
    Qed.

    Fact Is_defined_in_branch_incl {A} P_def : forall caus (blk: A) Γ Γ' cx,
        (forall x cx, HasCaus Γ x cx -> HasCaus Γ' x cx) ->
        (forall x cx, HasLastCaus Γ x cx -> HasLastCaus Γ' x cx) ->
        Is_defined_in_branch P_def Γ cx (Branch caus blk) ->
        (forall Γ Γ',
            (forall x cx, HasCaus Γ x cx -> HasCaus Γ' x cx) ->
            (forall x cx, HasLastCaus Γ x cx -> HasLastCaus Γ' x cx) ->
            P_def Γ blk ->
            P_def Γ' blk) ->
        Is_defined_in_branch P_def Γ' cx (Branch caus blk).
    Proof.
      intros * Hc Hcl Hdef Hind; inv_branch.
      - econstructor. eapply Hind; eauto using replace_idcaus_HasCaus_incl, replace_idcaus_HasLastCaus_incl.
      - eapply DefBranch2; eauto.
    Qed.

    Lemma Is_defined_in_incl : forall blk Γ Γ',
        (forall x cx, HasCaus Γ x cx -> HasCaus Γ' x cx) ->
        (forall x cx, HasLastCaus Γ x cx -> HasLastCaus Γ' x cx) ->
        forall cx, Is_defined_in Γ cx blk -> Is_defined_in Γ' cx blk.
    Proof.
      induction blk using block_ind2; intros * Hc Hcl * Hdef; inv Hdef; econstructor;
        repeat
          match goal with
          | s:scope _ |- _ => destruct s
          | |- Is_defined_in_scope _ _ _ _ => eapply Is_defined_in_scope_incl; eauto; intros
          | s:branch _ |- _ => destruct s
          | |- Is_defined_in_branch _ _ _ _ => eapply Is_defined_in_branch_incl; eauto; intros
          | _ => solve_Exists; simpl_Forall
          end; eauto using Is_defined_in.
    Qed.

    Fact depends_on_scope_incl {A} (P_dep : _ -> _ -> _ -> A -> Prop) : forall locs blks Γ Γ',
        (forall x cx, HasCaus Γ x cx -> HasCaus Γ' x cx) ->
        (forall x cx, HasLastCaus Γ x cx -> HasLastCaus Γ' x cx) ->
        (forall Γ Γ' cx cy,
            (forall x cx, HasCaus Γ x cx -> HasCaus Γ' x cx) ->
            (forall x cx, HasLastCaus Γ x cx -> HasLastCaus Γ' x cx) ->
            P_dep Γ cx cy blks -> P_dep Γ' cx cy blks) ->
        forall cx cy, depends_on_scope P_dep Γ cx cy (Scope locs blks) ->
                 depends_on_scope P_dep Γ' cx cy (Scope locs blks).
    Proof.
      intros * Hca Hla Hp * Hdep. inv_scope.
      - eapply DepOnScope1; eauto.
        eapply Hp in H2; eauto; intros *.
        rewrite 2 HasCaus_app; intros [|]; eauto.
        rewrite 2 HasLastCaus_app; intros [|]; eauto.
    Qed.

    Fact depends_on_branch_incl {A} (P_dep : _ -> _ -> _ -> A -> Prop) : forall caus blks Γ Γ',
        (forall x cx, HasCaus Γ x cx -> HasCaus Γ' x cx) ->
        (forall x cx, HasLastCaus Γ x cx -> HasLastCaus Γ' x cx) ->
        (forall Γ Γ' cx cy,
            (forall x cx, HasCaus Γ x cx -> HasCaus Γ' x cx) ->
            (forall x cx, HasLastCaus Γ x cx -> HasLastCaus Γ' x cx) ->
            P_dep Γ cx cy blks -> P_dep Γ' cx cy blks) ->
        forall cx cy, depends_on_branch P_dep Γ cx cy (Branch caus blks) ->
                 depends_on_branch P_dep Γ' cx cy (Branch caus blks).
    Proof.
      intros * Hca Hla Hp * Hdep. inv_branch.
      - eapply DepOnBranch1; eauto.
        eapply Hp in H0; eauto; intros *; eauto using replace_idcaus_HasCaus_incl, replace_idcaus_HasLastCaus_incl.
      - eapply DepOnBranch2; eauto.
    Qed.

    Lemma depends_on_incl : forall blk Γ Γ',
        (forall x cx, HasCaus Γ x cx -> HasCaus Γ' x cx) ->
        (forall x cx, HasLastCaus Γ x cx -> HasLastCaus Γ' x cx) ->
        forall cx cy, depends_on Γ cx cy blk -> depends_on Γ' cx cy blk.
    Proof.
      induction blk using block_ind2; intros * Hc1 Hc2 * Hdep; inv_block.
      - (* equation *)
        econstructor; eauto.
        eapply Is_used_inst_list_incl'; eauto. simpl_Forall; eauto using Is_used_inst_incl.
      - (* last *)
        econstructor; eauto.
        eapply Is_used_inst_incl; eauto.
      - (* reset *)
        econstructor. solve_Exists. simpl_Forall; eauto.
      - eapply DepOnReset2; eauto using Is_used_inst_incl, Is_defined_in_incl.
      - (* switch *)
        econstructor. solve_Exists.
        destruct b. eapply depends_on_branch_incl; eauto.
        intros; solve_Exists; simpl_Forall; eauto.
      - eapply DepOnSwitch2; eauto using Is_used_inst_incl, Is_defined_in_incl.
      - (* automaton *)
        econstructor. solve_Exists.
        destruct b. eapply depends_on_branch_incl; eauto. intros; destruct_conjs.
        destruct s; destruct_conjs. eapply depends_on_scope_incl; eauto.
        intros; solve_Exists; simpl_Forall; eauto.
      - eapply DepOnAuto2; solve_Exists; eauto using Is_defined_in_incl.
      - eapply DepOnAuto3; solve_Exists; eauto using Is_used_inst_incl, Is_defined_in_incl.
      - eapply DepOnAuto4; solve_Exists; eauto using Is_defined_in_incl.
        + destruct b as [?(?&?)]; solve_Exists; eauto using Is_used_inst_incl.
      - (* local *)
        constructor. eapply depends_on_scope_incl; eauto.
        intros; solve_Exists; simpl_Forall; eauto.
    Qed.
  End incl.

  Definition idcaus_of_decls locs :=
    idcaus_of_senv (senv_of_decls locs).

  Global Hint Unfold idcaus_of_decls : list.

  Definition idcaus_of_scope {A} f_idcaus (s : scope A) :=
    let 'Scope locs blks := s in
    idcaus_of_decls locs ++ f_idcaus blks.

  Definition idcaus_of_branch {A} f_idcaus (b : branch A) :=
    let 'Branch caus blks := b in
    caus ++ f_idcaus blks.

  Fixpoint idcaus_of_locals blk :=
    match blk with
    | Beq _ | Blast _ _ => []
    | Breset blocks _ => flat_map idcaus_of_locals blocks
    | Bswitch _ branches => flat_map (fun '(_, b) => idcaus_of_branch (flat_map idcaus_of_locals) b) branches
    | Bauto _ _ _ states => flat_map (fun '(_, b) => idcaus_of_branch (fun '(_, s) => idcaus_of_scope (fun '(blks, _) => flat_map idcaus_of_locals blks) s) b) states
    | Blocal s => idcaus_of_scope (flat_map idcaus_of_locals) s
    end.

  Global Hint Unfold idcaus_of_locals : list.

  Definition graph_of_node {PSyn prefs v a} (n : @node PSyn prefs) (g : AcyGraph v a) : Prop :=
    PS.Equal (vertices g)
             (PSP.of_list (map snd (idcaus (n_in n) ++ idcaus_of_decls (n_out n) ++ idcaus_of_locals (n_block n))))
    /\ (forall cx cy, depends_on_node cx cy n -> is_edge g cy cx).

  Definition node_causal {PSyn prefs} (n : @node PSyn prefs) :=
    NoDup (map snd (idcaus (n_in n) ++ idcaus_of_decls (n_out n) ++ idcaus_of_locals (n_block n))) /\
    exists v a (g : AcyGraph v a), graph_of_node n g.

  (* Some properties *)

  Lemma node_causal_NoDup {PSyn prefs} : forall (nd : @node PSyn prefs),
      node_causal nd ->
      NoDup (map snd (idcaus (n_in nd) ++ idcaus_of_decls (n_out nd))).
  Proof.
    intros * (Hnd&_). rewrite app_assoc, map_app in Hnd.
    now apply NoDup_app_l in Hnd.
  Qed.

  Fact Is_used_inst_list_length' Γ : forall es x k,
      Forall (fun e => forall x k, Is_used_inst Γ x k e -> k < Datatypes.length (annot e)) es ->
      Is_used_inst_list Γ x k es ->
      k < length (annots es).
  Proof.
    induction es; intros * Hf Hfree; inv Hfree; simpl;
      rewrite app_length, length_annot_numstreams.
    - (* now ! *)
      apply PeanoNat.Nat.lt_lt_add_r; auto.
    - (* later *)
      inv Hf.
      specialize (IHes _ _ H4 H3).
      apply PeanoNat.Nat.lt_sub_lt_add_l in IHes; auto.
  Qed.

  Lemma Is_used_inst_length {PSyn prefs} (G: @global PSyn prefs) Γ : forall e x k,
      wl_exp G e ->
      Is_used_inst Γ x k e ->
      k < length (annot e).
  Proof.
    Local Ltac solve_forall2 Ha :=
      setoid_rewrite <- Ha;
      eapply Is_used_inst_list_length'; eauto;
      simpl_Forall; eauto.

    induction e using exp_ind2; intros * Hwl Hfree; inv Hfree; inv Hwl; simpl; auto.
    - (* extcall *)
      destruct_conjs. lia.
    - (* fby *)
      solve_forall2 H8.
    - (* arrow *)
      destruct H3 as [?|?]; auto. solve_forall2 H8. solve_forall2 H9.
    - (* when *)
      rewrite map_length. destruct H2 as [[? ?]|?]; auto.
      solve_forall2 H7.
    - (* merge *)
      rewrite map_length. destruct H2 as [[? ?]|?]; auto.
      simpl_Exists; simpl_Forall.
      solve_forall2 H7.
    - (* case *)
      rewrite map_length. destruct H3 as [[? ?]|[Hex|(?&?&Hex)]]; subst; simpl in *; auto.
      + simpl_Exists; simpl_Forall.
        erewrite <-H11; eauto.
        eapply Is_used_inst_list_length'; eauto. simpl_Forall; eauto.
      + specialize (H13 _ eq_refl). specialize (H12 _ eq_refl).
        solve_forall2 H13.
  Qed.

  Corollary Is_used_inst_list_length {PSyn prefs} (G: @global PSyn prefs) Γ : forall es x k,
      Forall (wl_exp G) es ->
      Is_used_inst_list Γ x k es ->
      k < length (annots es).
  Proof.
    intros * Hwl Hfree.
    eapply Is_used_inst_list_length'; eauto.
    eapply Forall_impl; eauto. intros.
    eapply Is_used_inst_length; eauto.
  Qed.

  Lemma Is_used_inst_list_Exists Γ : forall es x k,
      Is_used_inst_list Γ x k es ->
      exists k', Exists (Is_used_inst Γ x k') es.
  Proof.
    induction es; intros * Hfree; inv Hfree.
    - exists k. left; auto.
    - specialize (IHes _ _ H3) as [k' ?].
      exists k'. right; auto.
  Qed.

  Lemma Is_used_inst_In_snd Γ : forall e x k,
      Is_used_inst Γ x k e ->
      exists y, HasCaus Γ y x \/ HasLastCaus Γ y x.
  Proof.
    induction e using exp_ind2; intros * Hfree; inv Hfree;
      repeat match goal with
             | H: _ \/ _ |- _ => destruct H; destruct_conjs
             | H: Is_used_inst_list _ _ _ _ |- _ =>
                 eapply Is_used_inst_list_Exists in H as (?&?)
             | _ => simpl_Exists; simpl_Forall; subst
             end; eauto.
  Qed.

  Corollary Is_used_inst_list_In_snd Γ : forall es x k,
      Is_used_inst_list Γ x k es ->
      exists y, HasCaus Γ y x \/ HasLastCaus Γ y x.
  Proof.
    intros * Hfree.
    eapply Is_used_inst_list_Exists in Hfree as (?&Hex).
    eapply Exists_exists in Hex as (?&_&Hfree).
    eapply Is_used_inst_In_snd in Hfree; eauto.
  Qed.

  Local Hint Constructors Is_defined_in : lcaus.

  Lemma Is_defined_scope_Is_defined_scope {A} P_def1 (P_def2: _ -> _ -> Prop) :
    forall locs (blk: A) x cx Γ,
      HasCaus Γ x cx ->
      Syn.Is_defined_in_scope P_def1 (Var x) (Scope locs blk) ->
      (forall Γ,
          HasCaus Γ x cx ->
          P_def1 blk ->
          P_def2 Γ blk) ->
      Is_defined_in_scope P_def2 Γ cx (Scope locs blk).
  Proof.
    intros * Hca Hdef Hind; inv Hdef.
    constructor. apply Hind; eauto. rewrite HasCaus_app; auto.
  Qed.

  Lemma Is_defined_branch_Is_defined_branch {A} P_def1 (P_def2: _ -> _ -> Prop) :
    forall caus (blk: A) x cx Γ,
      HasCaus Γ x cx ->
      Syn.Is_defined_in_branch P_def1 (Branch caus blk) ->
      (forall Γ,
          HasCaus Γ x cx ->
          P_def1 blk ->
          P_def2 Γ blk) ->
      Is_defined_in_branch P_def2 Γ cx (Branch caus blk).
  Proof.
    intros * Hca Hdef Hind; inv Hdef.
    destruct (InMembers_dec x caus ident_eq_dec).
    - eapply DefBranch2; eauto.
    - constructor.
      eapply Hind in H0; eauto using replace_idcaus_HasCaus2.
  Qed.

  Lemma Is_defined_in_Is_defined_in : forall blk x cx Γ,
      HasCaus Γ x cx ->
      Syn.Is_defined_in (Var x) blk ->
      Is_defined_in Γ cx blk.
  Proof.
    induction blk using block_ind2; intros * Hin Hdep;
      inv Hdep; inv_VarsDefined; eauto with lcaus.
    all:simpl_Exists; simpl_Forall; econstructor; solve_Exists.
    all:try (destruct b; destruct_conjs; eapply Is_defined_branch_Is_defined_branch; eauto); intros.
    all:try destruct s; try (destruct_conjs; eapply Is_defined_scope_Is_defined_scope; eauto); intros.
    all:repeat simpl_Exists; simpl_Forall; solve_Exists.
  Qed.

  Lemma Is_defined_scope_last_Is_defined_scope {A} P_def1 (P_def2: _ -> _ -> Prop) :
    forall locs (blk: A) x cx Γ,
      HasLastCaus Γ x cx ->
      Syn.Is_defined_in_scope P_def1 (Last x) (Scope locs blk) ->
      (forall Γ,
          HasLastCaus Γ x cx ->
          P_def1 blk ->
          P_def2 Γ blk) ->
      Is_defined_in_scope P_def2 Γ cx (Scope locs blk).
  Proof.
    intros * Hca Hdef Hind; inv Hdef.
    constructor. apply Hind; eauto. rewrite HasLastCaus_app; auto.
  Qed.

  Lemma Is_defined_in_last_Is_defined_in : forall blk x cx Γ,
      HasLastCaus Γ x cx ->
      Syn.Is_defined_in (Last x) blk ->
      Is_defined_in Γ cx blk.
  Proof.
    induction blk using block_ind2; intros * Hin Hdep;
      inv Hdep; inv_VarsDefined; eauto with lcaus.
    all:simpl_Exists; simpl_Forall; econstructor; solve_Exists.
    all:try destruct s; try (destruct_conjs; eapply Is_defined_scope_last_Is_defined_scope; eauto); intros.
    all:repeat simpl_Exists; simpl_Forall; solve_Exists.
  Qed.

  (** ** Causality check *)

  Section collect_used.

    Variable cenv cenvl : Env.t ident.

    Definition assemble_brs_used_inst_list {A} pss (tys : list A) :=
      List.fold_left (fun ps1 ps2 => List.map (fun '(ps1, ps2) => PS.union ps1 ps2) (List.combine ps1 ps2))
                     pss (List.map (fun _ => PS.empty) tys).

    Definition collect_used_var cenv (x : ident) : ident :=
      or_default xH (Env.find x cenv).

    Fixpoint collect_used_clock (ck : clock) : PS.t :=
      match ck with
      | Cbase => PS.empty
      | Con ck x _ => PS.add (collect_used_var cenv x) (collect_used_clock ck)
      end.

    Fixpoint collect_used_inst (e : exp) {struct e} : list PS.t :=
      let collect_used_inst_list (es : list exp) := flat_map collect_used_inst es in
      match e with
      | Econst _ | Eenum _ _ => [PS.empty]
      | Evar x _ => [PS.singleton (collect_used_var cenv x)]
      | Elast x _ => [PS.singleton (collect_used_var cenvl x)]
      | Eunop _ e _ => (collect_used_inst e)
      | Ebinop _ e1 e2 _ =>
        let ps1 := collect_used_inst e1 in
        let ps2 := collect_used_inst e2 in
        List.map (fun '(ps1, ps2) => PS.union ps1 ps2) (List.combine ps1 ps2)
      | Eextcall _ es _ =>
          [PSUnion (collect_used_inst_list es)]
      | Efby e0s _ _ =>
        collect_used_inst_list e0s
      | Earrow e0s es _ =>
        let ps1 := collect_used_inst_list e0s in
        let ps2 := collect_used_inst_list es in
        List.map (fun '(ps1, ps2) => PS.union ps1 ps2) (List.combine ps1 ps2)
      | Ewhen es (x, _) _ _ =>
        let cx := collect_used_var cenv x in
        List.map (fun ps => PS.add cx ps) (collect_used_inst_list es)
      | Emerge (x, _) es (tys, _) =>
        let ps := assemble_brs_used_inst_list (List.map (fun es => collect_used_inst_list (snd es)) es) tys in
        List.map (PS.add (collect_used_var cenv x)) ps
      | Ecase e es d (tys, _) =>
        let ps0 := collect_used_inst e in
        let psd := or_default_with (List.map (fun _ => PS.empty) tys) collect_used_inst_list d in
        let ps1 := assemble_brs_used_inst_list (psd::List.map (fun es => collect_used_inst_list (snd es)) es) tys in
        List.map (PS.union (nth 0 ps0 PS.empty)) ps1
      | Eapp _ es er a =>
        let ps := PSUnion (collect_used_inst_list er ++ collect_used_inst_list es) in
        List.map (fun _ => ps) a
      end.

    Definition collect_used_inst_list (es : list exp) :=
      flat_map collect_used_inst es.

  End collect_used.

  Definition unions_fuse envs := List.fold_left (Env.union_fuse PS.union) envs (@Env.empty _).

  Definition collect_depends_scope {A} (f_coll : _ -> _ -> A -> Env.t PS.t) (cenv cenvl : Env.t ident) (s : scope A) :=
    let 'Scope locs blks := s in
    let cenv' := Env.adds' (map (fun '(x, (_, _, cx, _)) => (x, cx)) locs) cenv in
    let cenvl' := Env.adds' (map_filter (fun '(x, (_, _, _, o)) => option_map (fun cx => (x, cx)) o) locs) cenvl in
    f_coll cenv' cenvl' blks.

  Definition collect_depends_branch {A} (f_coll : _ -> _ -> A -> Env.t PS.t) (cenv cenvl : Env.t ident) (s : branch A) :=
    let 'Branch caus blks := s in
    let cenv' := Env.mapi (fun x cx => or_default cx (assoc_ident x caus)) cenv in
    let deps1 := f_coll cenv' cenvl blks in
    let deps2 := Env.from_list (map (fun '(x, cx) => (or_default x (Env.find x cenv), PS.singleton cx)) caus) in
    Env.union_fuse PS.union deps1 deps2.

  Fixpoint collect_depends_on (cenv cenvl : Env.t ident) (d : block) : Env.t PS.t :=
    match d with
    | Beq (xs, es) =>
      Env.from_list
        (List.combine
           (List.map (collect_used_var cenv) xs)
           (collect_used_inst_list cenv cenvl es))
    | Blast x e =>
        let pr := collect_used_inst cenv cenvl e in
        let cx := collect_used_var cenvl x in
        Env.add cx (nth 0 pr PS.empty) (Env.empty _)
    | Breset blocks er =>
      let pr := collect_used_inst cenv cenvl er in
      Env.map (fun ps => PS.union (nth 0 pr PS.empty) ps)
              (unions_fuse (map (collect_depends_on cenv cenvl) blocks))
    | Bswitch ec branches =>
      let pc := collect_used_inst cenv cenvl ec in
      Env.map (fun ps => PS.union (nth 0 pc PS.empty) ps)
              (unions_fuse (map (fun blks =>
                                   collect_depends_branch
                                     (fun cenv cenvl blks => unions_fuse (map (collect_depends_on cenv cenvl) blks)) cenv cenvl (snd blks)) branches))
    | Bauto _ ck (ini, oth) states =>
        let pc1 := collect_used_clock cenv ck in
        let pc2 := PSUnion (map (fun '(e, _) => nth 0 (collect_used_inst cenv cenvl e) PS.empty) ini) in
        let pc3 := PSUnion (map (fun '(_, Branch _ (unl, _)) => PSUnion (map (fun '(e, _) => nth 0 (collect_used_inst cenv cenvl e) PS.empty) unl)) states) in
        let pc := PS.union pc1 (PS.union pc2 pc3) in
        Env.map (fun ps => PS.union pc ps)
                (unions_fuse (map (fun '(_, br) =>
                                     collect_depends_branch
                                       (fun cenv cenvl '(_, blks) =>
                                          collect_depends_scope
                                            (fun cenv cenvl blks => unions_fuse (map (collect_depends_on cenv cenvl) (fst blks)))
                                            cenv cenvl blks) cenv cenvl br) states))
    | Blocal scope =>
        collect_depends_scope (fun cenv' cenvl' blks => unions_fuse (map (collect_depends_on cenv' cenvl') blks))
                              cenv cenvl scope
    end.

  Definition build_graph {PSyn prefs} (n : @node PSyn prefs) : Env.t PS.t :=
    let cenv := Env.from_list (idcaus (n_in n) ++ map (fun '(x, (_, _, cx, _)) => (x, cx)) (n_out n)) in
    let cenvl := Env.from_list (map_filter (fun '(x, (_, _, _, o)) => option_map (fun cx => (x, cx)) o) (n_out n)) in
    let indeps := Env.from_list (map (fun '(_, (_, _, cx)) => (cx, PS.empty)) (n_in n)) in
    let blkdeps := collect_depends_on cenv cenvl (n_block n) in
    unions_fuse [indeps; blkdeps].

  Section msgs_of_labels.
    (** Generate an error message for each causality label in the block/node *)

    Definition msgs_of_decl (x : decl) :=
      let '(x, (_, _, cx, o)) := x in
      (cx, [CTX x])::
        (match o with
         | None => []
         | Some clx => [(clx, [MSG "last "; CTX x])]
         end).

    Definition msg_of_caus (tag : ident) (x : ident * ident) :=
      let '(x, cx) := x in
      (cx, CTX x::MSG "(" :: CTX tag :: msg ")").

    Definition enum_nth_constructor (ty : type) k :=
      match ty with
      | Tenum _ tys => List.nth k tys xH
      | _ => xH (* Should not happen *)
      end.

    Fixpoint msgs_of_local_labels (blk : block) : Env.t errmsg :=
      match blk with
      | Beq _ | Blast _ _ => Env.empty _
      | Breset blks _ => Env.unions (map msgs_of_local_labels blks)
      | Bswitch e brs =>
          let ty := List.hd bool_velus_type (typeof e) in
          Env.unions (map (fun '(k, Branch caus blks) =>
                             let tag := enum_nth_constructor ty k in
                             Env.adds' (map (msg_of_caus tag) caus)
                               (Env.unions (map msgs_of_local_labels blks))) brs)
      | Bauto _ _ _ states =>
          Env.unions (map (fun '((_, tag), Branch caus (_, Scope locs (blks, _))) =>
                             Env.adds'
                                  (map (msg_of_caus tag) caus++flat_map msgs_of_decl locs)
                                  (Env.unions (map msgs_of_local_labels blks))
                        ) states)
      | Blocal (Scope locs blks) =>
          Env.adds' (flat_map msgs_of_decl locs)
            (Env.unions (map msgs_of_local_labels blks))
      end.

    Definition msgs_of_ins (x : ident * (type * clock * ident)) :=
      let '(x, (_, _, cx)) := x in
      (cx, [CTX x]).

    Definition msgs_of_labels {PSyn prefs} (n : @node PSyn prefs) : Env.t errmsg :=
      Env.adds' (map msgs_of_ins (n_in n) ++ flat_map msgs_of_decl (n_out n))
        (msgs_of_local_labels (n_block n)).

  End msgs_of_labels.

  Definition check_node_causality {PSyn prefs} (n : @node PSyn prefs) : res unit :=
    let idcaus := (map snd (idcaus (n_in n) ++ idcaus_of_decls (n_out n) ++ idcaus_of_locals (n_block n))) in
    let graph := build_graph n in
    if check_nodup idcaus
       && PS.equal (PSP.of_list idcaus) (PSP.of_list (map fst (Env.elements graph))) then
      match build_acyclic_graph (Env.map PSP.to_list graph) (fun _ => msgs_of_labels n) with
      | OK _ => OK tt
      | Error msg => Error (MSG "Node " :: (CTX (n_name n)) :: MSG " : " :: msg)
      end
    else Error (MSG "Node " :: (CTX (n_name n)) :: MSG " has duplicated causality annotations" :: nil).

  Definition check_causality {PSyn prefs} (G : @global PSyn prefs) :=
    mmap check_node_causality (nodes G).

  Fact collect_used_inst_list_length' cenv cenv' : forall es,
      Forall (fun e => length (collect_used_inst cenv cenv' e) = length (annot e)) es ->
      length (collect_used_inst_list cenv cenv' es) = length (annots es).
  Proof.
    induction es; intros * Hf; inv Hf; simpl; auto.
    repeat rewrite app_length. f_equal; auto.
  Qed.

  Fact assemble_brs_used_inst_list_length {A} : forall pss (tys : list A),
      Forall (fun ps => length ps = length tys) pss ->
      length (assemble_brs_used_inst_list pss tys) = length tys.
  Proof.
    unfold assemble_brs_used_inst_list.
    intros * Hlen.
    assert (Forall (fun ps => Datatypes.length ps = Datatypes.length (map (fun _ => PS.empty) tys)) pss) as Hlen'.
    { eapply Forall_impl; [|eauto]; intros.
      rewrite map_length; auto. } clear Hlen.
    replace (Datatypes.length tys) with (Datatypes.length (map (fun _ => PS.empty) tys))
      by (rewrite map_length; auto).
    revert Hlen'. generalize (map (fun _ => PS.empty) tys). clear tys.
    induction pss; intros; inv Hlen'; simpl; auto.
    rewrite IHpss; eauto.
    - rewrite map_length, combine_length, H1. apply Nat.min_id.
    - eapply Forall_impl; [|eauto].
      intros ? Heq.
      rewrite map_length, combine_length, Heq, H1.
      symmetry. apply Nat.min_id.
  Qed.

  Lemma collect_used_inst_length {PSyn prefs} : forall (G: @global PSyn prefs) cenv cenv' e,
      wl_exp G e ->
      length (collect_used_inst cenv cenv' e) = length (annot e).
  Proof.
    Local Ltac solve_forall H :=
      eapply Forall_Forall in H; eauto;
      clear - H;
      eapply Forall_impl; eauto; intros ? [? ?]; auto.

    induction e using exp_ind2; intros Hwl; inv Hwl; destruct_conjs; simpl; try reflexivity.
    - (* unop *)
      rewrite <- length_annot_numstreams in H4. rewrite IHe; auto.
    - (* binop *)
      rewrite <- length_annot_numstreams in H6, H7.
      rewrite map_length, combine_length, IHe1, IHe2, H6, H7; auto.
    - (* fby *)
      setoid_rewrite collect_used_inst_list_length'; auto.
      solve_forall H.
    - (* arrow *)
      rewrite map_length, combine_length.
      setoid_rewrite collect_used_inst_list_length'.
      rewrite H7, H8. apply PeanoNat.Nat.min_id.
      solve_forall H. solve_forall H0.
    - (* when *)
      rewrite map_length, map_length.
      setoid_rewrite collect_used_inst_list_length'; auto.
      solve_forall H.
    - (* merge *)
      rewrite map_length, assemble_brs_used_inst_list_length, map_length; auto.
      rewrite Forall_map.
      rewrite Forall_forall in *; intros.
      erewrite <- H6; eauto.
      setoid_rewrite collect_used_inst_list_length'; eauto.
      specialize (H _ H0). specialize (H5 _ H0).
      solve_forall H.
    - (* case *)
      rewrite map_length, assemble_brs_used_inst_list_length, map_length; auto.
      constructor.
      + destruct d; simpl in *. 2:now rewrite map_length.
        erewrite <-H12; eauto. eapply collect_used_inst_list_length'.
        eapply Forall_impl_In; [|eapply H0]; intros.
        eapply Forall_forall in H11; eauto.
      + rewrite Forall_map.
        rewrite Forall_forall in *; intros.
        erewrite <-H10; eauto.
        specialize (H _ H1); simpl in H. specialize (H9 _ H1).
        eapply collect_used_inst_list_length'.
        eapply Forall_impl_In; [|eauto]. intros ? Hin ?.
        eapply Forall_forall in H; eauto.
    - (* app *) rewrite map_length; auto.
  Qed.

  Corollary collect_used_inst_list_length {PSyn prefs} : forall (G: @global PSyn prefs) cenv cenv' es,
      Forall (wl_exp G) es ->
      length (collect_used_inst_list cenv cenv' es) = length (annots es).
  Proof.
    intros * Hwl.
    eapply collect_used_inst_list_length'.
    eapply Forall_impl; eauto. intros ? ?.
    eapply collect_used_inst_length; eauto.
  Qed.

  Section collect_used_spec.

    Variable Γ : static_env.
    Variable cenv' cenvl' : Env.t ident.

    Hypothesis Heq : forall x cx, Env.find x cenv' = Some cx <-> HasCaus Γ x cx.
    Hypothesis Heql : forall x cx, Env.find x cenvl' = Some cx <-> HasLastCaus Γ x cx.

    Lemma collect_used_var_correct : forall x cx,
        InMembers x Γ ->
        collect_used_var cenv' x = cx ->
        HasCaus Γ x cx.
    Proof.
      intros * Hinm Hcoll.
      unfold collect_used_var in Hcoll. rewrite <-Heq.
      assert (exists cx, HasCaus Γ x cx) as (?&Hhas).
      { apply InMembers_In in Hinm; simpl_In. destruct Hinm.
        esplit. econstructor; eauto. }
      rewrite <-Heq in Hhas. setoid_rewrite Hhas in Hcoll; simpl in *; subst; auto.
    Qed.

    Hypothesis Hnd1 : NoDupMembers Γ.

    Lemma collect_used_var_complete : forall x cx,
        HasCaus Γ x cx ->
        collect_used_var cenv' x = cx.
    Proof.
      intros * Hin.
      unfold collect_used_var. apply Heq in Hin.
      setoid_rewrite Hin. reflexivity.
    Qed.

    Lemma collect_used_last_complete : forall x cx,
        HasLastCaus Γ x cx ->
        collect_used_var cenvl' x = cx.
    Proof.
      intros * Hin.
      unfold collect_used_var. apply Heql in Hin.
      setoid_rewrite Hin. reflexivity.
    Qed.

    Lemma collect_used_inst_list_spec' {PSyn prefs} : forall (G: @global PSyn prefs) es x k,
        Forall (wl_exp G) es ->
        Forall (wx_exp Γ) es ->
        Forall (fun e => forall k, wl_exp G e -> wx_exp Γ e ->
                           Is_used_inst Γ x k e ->
                           PS.In x (nth k (collect_used_inst cenv' cenvl' e) PS.empty)) es ->
        Is_used_inst_list Γ x k es ->
        PS.In x (List.nth k (collect_used_inst_list cenv' cenvl' es) PS.empty).
    Proof.
      induction es; intros * Hwl Hwx Hf Hfree; inv Hwl; inv Hwx; inv Hf. inv Hfree. simpl.
      assert (length (collect_used_inst cenv' cenvl' a) = numstreams a) as Hlen.
      { erewrite collect_used_inst_length, length_annot_numstreams; eauto. }
      inv Hfree.
      * rewrite app_nth1. apply H5; eauto. congruence.
      * rewrite app_nth2. apply IHes; eauto. 1,2:congruence.
    Qed.

    Lemma psunion_collect_used_list_spec' {PSyn prefs} : forall (G: @global PSyn prefs) es x,
        Forall (wl_exp G) es ->
        Forall (wx_exp Γ) es ->
        Forall (fun e => forall k, wl_exp G e ->
                           wx_exp Γ e->
                           Is_used_inst Γ x k e ->
                           PS.In x (nth k (collect_used_inst cenv' cenvl' e) PS.empty)) es ->
        (exists k', Exists (Is_used_inst Γ x k') es) ->
        PS.In x (PSUnion (collect_used_inst_list cenv' cenvl' es)).
    Proof.
      induction es; intros * Hwl Hwx Hf (?&Hex); inv Hwl; inv Hwx; inv Hf. inv Hex. simpl.
      rewrite PSUnion_In_app.
      inv Hex; auto.
      + assert (Hk:=H0).
        eapply Is_used_inst_length in Hk; eauto; erewrite <- collect_used_inst_length in Hk; eauto.
        apply H5 in H0; auto.
        left. eapply In_In_PSUnion; eauto.
        eapply nth_In; eauto.
      + right. apply IHes; eauto.
    Qed.

    Fact ps_In_k_lt : forall x l k,
        PS.In x (nth k l PS.empty) ->
        k < length l.
    Proof.
      induction l; intros * Hin; simpl in *.
      - exfalso. eapply not_In_empty. destruct k; eauto.
      - destruct k; eauto.
        + apply PeanoNat.Nat.lt_0_succ.
        + rewrite <-Nat.succ_lt_mono; auto.
    Qed.

    Lemma Exists_Exists_Is_free {PSyn prefs} : forall (G: @global PSyn prefs) es x k,
      Forall (wl_exp G) es ->
      Forall (fun e => numstreams e = 1) es ->
      Exists (Is_used_inst Γ x k) es ->
      Exists (Is_used_inst Γ x 0) es.
    Proof.
      intros * Wl Num Free.
      simpl_Exists; simpl_Forall.
      assert (k = 0) as Hk'; subst; eauto.
      take (Is_used_inst _ _ _ _) and eapply Is_used_inst_length in it; eauto. 2:solve_Exists.
      rewrite length_annot_numstreams, Num in it.
      apply PeanoNat.Nat.lt_1_r; auto.
    Qed.
    Local Hint Resolve Exists_Exists_Is_free : lcaus.

    Fact assemble_brs_used_inst_list_spec: forall x k pss (tys : list type),
        Forall (fun ps => length ps = length tys) pss ->
        Exists (fun ps => PS.In x (List.nth k ps PS.empty)) pss ->
        PS.In x (List.nth k (assemble_brs_used_inst_list pss tys) PS.empty).
    Proof.
      unfold assemble_brs_used_inst_list.
      intros * Hlen.
      assert (forall base : list PS.t,
                 Forall (fun ps => length ps = length base) pss ->
                 PS.In x
                       (nth k (fold_left (fun ps1 ps2 : list PS.t => map (fun '(ps0, ps3) => PS.union ps0 ps3)
                                                                      (combine ps1 ps2)) pss base) PS.empty) <->
                 Exists (fun ps : list PS.t => PS.In x (nth k ps PS.empty)) pss \/ PS.In x (nth k base PS.empty)).
      { clear Hlen tys. intros * Hlen; split; revert base Hlen.
        - induction pss; simpl; intros; inv Hlen; auto.
          apply IHpss in H as [H|H]; auto.
          2:{ clear - H2 H3. eapply Forall_impl; [|eauto].
              intros ? Heq. now rewrite map_length, combine_length, Heq, H2, Nat.min_id. }
          rewrite map_nth' with (d':=(PS.empty, PS.empty)) in H.
          2:{ eapply ps_In_k_lt in H; rewrite map_length in H; auto. }
          rewrite combine_nth in H; auto.
          apply PS.union_spec in H as [H|H]; auto.
        - induction pss; simpl; intros; inv Hlen; auto.
          + destruct H; auto.
            inv H.
          + eapply IHpss; eauto.
            1:{ clear - H2 H3. eapply Forall_impl; [|eauto].
                intros ? Heq. now rewrite map_length, combine_length, Heq, H2, Nat.min_id. }
            rewrite map_nth' with (d':=(PS.empty, PS.empty)).
            2:{ rewrite combine_length.
                destruct H. inv H.
                - apply ps_In_k_lt in H1. now rewrite <-H2, Nat.min_id.
                - simpl_Exists; simpl_Forall. apply ps_In_k_lt in H1.
                  now rewrite H2, Nat.min_id, <-H3.
                - apply ps_In_k_lt in H. now rewrite H2, Nat.min_id.
            }
            rewrite combine_nth; auto.
            rewrite PS.union_spec; auto.
            destruct H; auto.
            inv H; auto.
      }
      intros Hex. rewrite H; eauto.
      simpl_Forall. now rewrite map_length.
    Qed.

    Fact collect_used_inst_spec {PSyn prefs}: forall (G: @global PSyn prefs) x e k,
        wl_exp G e ->
        wx_exp Γ e ->
        Is_used_inst Γ x k e ->
        PS.In x (List.nth k (collect_used_inst cenv' cenvl' e) PS.empty).
    Proof with eauto with lcaus.
      induction e using exp_ind2;
        (intros * Hwl Hwx Hfree;
         specialize (Is_used_inst_length G Γ _ _ _ Hwl Hfree) as Hlen1;
         specialize (collect_used_inst_length G cenv' cenvl' _ Hwl) as Hlen2;
         try destruct a as [ty [ck name]];
         inv Hwl; inv Hwx; inv Hfree; simpl in *;
         try rewrite <- length_annot_numstreams in *; idtac).
      - (* var *)
        apply PSF.singleton_2; auto.
        eapply collect_used_var_complete; eauto.
      - (* last *)
        apply PSF.singleton_2; auto.
        eapply collect_used_last_complete; eauto.
      - (* unop *)
        eapply IHe; eauto.
      - (* binop *)
        erewrite <- collect_used_inst_length with (cenv:=cenv') (cenv':=cenvl') in H6, H7; eauto.
        repeat singleton_length.
        destruct H2 as [?|?].
        * apply PSF.union_2. eapply IHe1 in H; eauto.
        * apply PSF.union_3. eapply IHe2 in H; eauto.
      - (* extcall *)
        eapply psunion_collect_used_list_spec'; eauto.
      - (* fby *)
        erewrite <- collect_used_inst_list_length with (cenv:=cenv') (cenv':=cenvl') in H7, H8; eauto.
        eapply collect_used_inst_list_spec'; eauto.
      - (* arrow *)
        erewrite <- collect_used_inst_list_length in H7, H8; eauto.
        erewrite map_nth' with (d':=(PS.empty, PS.empty)).
        2:(erewrite <- map_length, Hlen2; eauto).
        rewrite combine_nth. 2:setoid_rewrite H7; setoid_rewrite H8; auto.
        repeat rewrite PS.union_spec.
        destruct H5; [left|right]; eapply collect_used_inst_list_spec'; eauto.
      - (* when *)
        erewrite <- collect_used_inst_list_length with (cenv:=cenv') (cenv':=cenvl') in H6; eauto.
        erewrite map_nth' with (d':=PS.empty).
        2:(erewrite <- map_length, Hlen2; eapply Hlen1; eauto).
        destruct H4 as [(_&?)|?]; subst.
        * apply PSF.add_1; auto.
          eapply collect_used_var_complete; eauto.
        * apply PSF.add_2. eapply collect_used_inst_list_spec'; eauto.
      - (* merge *)
        assert (Forall (fun ps : list PS.t => Datatypes.length ps = Datatypes.length tys)
                       (map (fun es0 => flat_map (collect_used_inst cenv' cenvl') (snd es0)) es)) as Hlen'.
        { clear - H5 H6. rewrite Forall_map, Forall_forall in *; intros.
          erewrite <- H6; eauto.
          eapply collect_used_inst_list_length; eauto. }
        erewrite map_nth' with (d':=PS.empty).
        2:(erewrite <- map_length, Hlen2; eauto).
        apply PSF.add_iff.
        destruct H3 as [(_&?)|Hfree]; subst; eauto using collect_used_var_complete.
        right.
        apply assemble_brs_used_inst_list_spec; auto. solve_Exists. simpl_Forall.
        eapply collect_used_inst_list_spec'; eauto.
      - (* case *)
        assert (Forall (fun ps : list PS.t => Datatypes.length ps = Datatypes.length tys)
                       (or_default_with (map (fun _ : type => PS.empty) tys)
                                        (fun es0 : list exp => flat_map (collect_used_inst cenv' cenvl') es0) d ::
                                        map (fun es0 => flat_map (collect_used_inst cenv' cenvl') (snd es0)) es)) as Hlen'.
        { constructor.
          - destruct d; simpl in *. 2:now rewrite map_length.
            erewrite <-H12; eauto.
            eapply collect_used_inst_list_length; eauto.
          - rewrite Forall_map, Forall_forall in *; intros.
            erewrite <- H10; eauto.
            eapply collect_used_inst_list_length; eauto. }
        erewrite map_nth' with (d':=PS.empty).
        2:(erewrite <- map_length, Hlen2; eauto).
        apply PS.union_spec.
        destruct H3 as [(_&Hfree)|[Hfree|(?&?&Hfree)]]; subst; simpl in *.
        2,3:right; apply assemble_brs_used_inst_list_spec; auto.
        * left. apply IHe; auto.
        * right. solve_Exists. simpl_Forall.
          eapply collect_used_inst_list_spec'; eauto.
        * left. eapply collect_used_inst_list_spec'; eauto.
      - (* app *)
        erewrite map_nth'; eauto. 2:exact (Tenum xH [], Cbase).
        rewrite PSUnion_In_app.
        destruct H15.
        * right. eapply psunion_collect_used_list_spec'; eauto.
        * left. eapply psunion_collect_used_list_spec'; eauto.
    Qed.

    Corollary collect_used_inst_list_spec {PSyn prefs} : forall (G: @global PSyn prefs) es x k,
        Forall (wl_exp G) es ->
        Forall (wx_exp Γ) es ->
        Is_used_inst_list Γ x k es ->
        PS.In x (List.nth k (collect_used_inst_list cenv' cenvl' es) PS.empty).
    Proof.
      intros * Hwl Hwx.
      eapply collect_used_inst_list_spec'; eauto.
      eapply Forall_impl; eauto; intros.
      eapply collect_used_inst_spec; eauto.
    Qed.

  End collect_used_spec.

  Lemma unions_fuse_PS_In : forall x envs,
      Env.In x (unions_fuse envs) <-> Exists (Env.In x) envs.
  Proof.
    intros x envs.
    unfold unions_fuse.
    replace envs with (rev (rev envs)); auto using rev_involutive.
    rewrite fold_right_rev_left, <-Exists_rev.
    induction (rev envs); split; intros * Hin; simpl in *.
    - apply Env.Props.P.F.empty_in_iff in Hin; inv Hin.
    - inv Hin.
    - apply Env.union_fuse_In in Hin as [Hin|Hin]; auto.
      right. apply IHl; auto.
    - apply Env.union_fuse_In.
      inv Hin; auto.
      left. apply IHl; auto.
  Qed.

  Fact equiv_env_scope : forall Γ locs cenv',
      NoDupMembers locs ->
      (forall x, InMembers x locs -> ~In x (map fst Γ)) ->
      (forall x cx, Env.find x cenv' = Some cx <-> HasCaus Γ x cx) ->
      (forall x cx, Env.find x (Env.adds' (map (fun '(x1, (_, _, cx1, _)) => (x1, cx1)) locs) cenv') = Some cx
               <-> HasCaus (Γ ++ senv_of_decls locs) x cx).
  Proof.
    intros * Hnd1 Hnd2 Heq *. rewrite HasCaus_app. split; intros Hin.
    - apply Env.find_adds'_In in Hin as [Hin|Hin].
      + simpl_In. right. econstructor. solve_In. eauto.
      + left. now apply Heq.
    - destruct Hin as [Hin|Hin].
      + rewrite Env.gsso', Heq; auto.
        intros Hinm. simpl_In.
        eapply Hnd2; eauto using In_InMembers. inv Hin; solve_In.
      + apply Env.In_find_adds'. 2:(inv Hin; solve_In).
        apply NoDupMembers_map; auto. intros; destruct_conjs; auto.
  Qed.

  Fact equiv_env_last_scope : forall Γ locs cenv',
      NoDupMembers locs ->
      (forall x, InMembers x locs -> ~In x (map fst Γ)) ->
      (forall x cx, Env.find x cenv' = Some cx <-> HasLastCaus Γ x cx) ->
      (forall x cx, Env.find x (Env.adds' (map_filter (fun '(x2, (_, _, _, o)) => option_map (fun cx0 => (x2, cx0)) o) locs) cenv') = Some cx
               <-> HasLastCaus (Γ ++ senv_of_decls locs) x cx).
  Proof.
    intros * Hnd1 Hnd2 Heq *. rewrite HasLastCaus_app. split; intros Hin.
    - apply Env.find_adds'_In in Hin as [Hin|Hin].
      + simpl_In. right. econstructor. solve_In. simpl. eauto.
      + left. eapply Heq; eauto.
    - destruct Hin as [Hin|Hin].
      + rewrite Env.gsso', Heq; auto.
        intros Hinm. simpl_In.
        eapply Hnd2; eauto using In_InMembers. inv Hin; solve_In.
      + apply Env.In_find_adds'. 2:(inv Hin; solve_In).
        apply NoDupMembers_map_filter; auto.
        intros; destruct_conjs; auto. destruct o; simpl; auto.
  Qed.

  Lemma collect_depends_scope_dom {A} P_vd P_nd (P_wl: A -> _) P_wx f_coll P_def
        {PSyn prefs} (G: @global PSyn prefs) :
    forall locs blks xs Γ cenv' cenvl' cx,
      NoDupMembers Γ ->
      (forall x cx, Env.find x cenv' = Some cx <-> HasCaus Γ x cx) ->
      (forall x cx, Env.find x cenvl' = Some cx <-> HasLastCaus Γ x cx) ->
      incl xs (map fst Γ) ->
      VarsDefinedCompScope P_vd (Scope locs blks) xs ->
      NoDupScope P_nd (map fst Γ) (Scope locs blks) ->
      wl_scope P_wl G (Scope locs blks) ->
      wx_scope P_wx Γ (Scope locs blks) ->
      Is_defined_in_scope P_def Γ cx (Scope locs blks) ->
      (forall Γ xs cenv' cenvl',
          NoDupMembers Γ ->
          (forall x cx, Env.find x cenv' = Some cx <-> HasCaus Γ x cx) ->
          (forall x cx, Env.find x cenvl' = Some cx <-> HasLastCaus Γ x cx) ->
          incl xs (map fst Γ) ->
          P_vd blks xs ->
          P_nd (map fst Γ) blks ->
          P_wl blks ->
          P_wx Γ blks ->
          P_def Γ blks ->
          Env.In cx (f_coll cenv' cenvl' blks)) ->
      (forall Γ Γ',
          (forall x, IsVar Γ x -> IsVar Γ' x) ->
          (forall x, IsLast Γ x -> IsLast Γ' x) ->
          P_wx Γ blks -> P_wx Γ' blks) ->
      Env.In cx (collect_depends_scope f_coll cenv' cenvl' (Scope locs blks)).
  Proof.
    intros * Hnd Hc Hcl Hincl Hvd Hndloc Hwl Hwx Hdef Hp Hwxincl.
    inv Hvd. inv Hndloc. inv Hwl. inv Hwx. subst Γ'.
    assert (NoDupMembers (Γ ++ senv_of_decls locs)) as Hnd' by (auto using NoDupScope_NoDupMembers).
    inv Hdef.
    eapply Hp in H6; eauto.
    + now apply equiv_env_scope.
    + now apply equiv_env_last_scope.
    + rewrite map_app, map_fst_senv_of_decls.
      apply incl_appl'; auto.
    + now rewrite map_app, map_fst_senv_of_decls.
  Qed.

  Fact equiv_env_branch : forall Γ caus cenv',
      (forall x cx, Env.find x cenv' = Some cx <-> HasCaus Γ x cx) ->
      (forall x cx, Env.find x (Env.mapi (fun x cx => or_default cx (assoc_ident x caus)) cenv') = Some cx
               <-> HasCaus (replace_idcaus caus Γ) x cx).
  Proof.
    intros * Heq *. split; intros Hin.
    - rewrite Env.gmapi in Hin. inv_equalities.
      eapply Heq in Hf. inv Hf. econstructor; solve_In.
      destruct (assoc_ident _ _); auto.
    - rewrite Env.gmapi. inv Hin; simpl_In.
      assert (HasCaus Γ x a.(causl)) as Hca by eauto with senv.
      apply Heq in Hca; auto. rewrite Hca; simpl.
      destruct (assoc_ident _ _); auto.
  Qed.

  Fact equiv_env_last_branch : forall Γ caus cenv',
      (forall x cx, Env.find x cenv' = Some cx <-> HasLastCaus Γ x cx) ->
      (forall x cx, Env.find x cenv' = Some cx
               <-> HasLastCaus (replace_idcaus caus Γ) x cx).
  Proof.
    intros * Heq *.
    now rewrite replace_idcaus_HasLastCaus, Heq.
  Qed.

  Lemma collect_depends_branch_dom {A} P_vd P_nd (P_wl: A -> _) P_wx f_coll P_def
        {PSyn prefs} (G: @global PSyn prefs) :
    forall caus blks xs Γ cenv' cenvl' cx,
      NoDupMembers Γ ->
      (forall x cx, Env.find x cenv' = Some cx <-> HasCaus Γ x cx) ->
      (forall x cx, Env.find x cenvl' = Some cx <-> HasLastCaus Γ x cx) ->
      incl xs (map fst Γ) ->
      VarsDefinedCompBranch P_vd (Branch caus blks) xs ->
      NoDupBranch P_nd (Branch caus blks) ->
      wl_branch P_wl (Branch caus blks) ->
      wx_branch P_wx (Branch caus blks) ->
      Is_defined_in_branch P_def Γ cx (Branch caus blks) ->
      (forall Γ' xs cenv' cenvl',
          NoDupMembers Γ' ->
          (forall x cx, Env.find x cenv' = Some cx <-> HasCaus Γ' x cx) ->
          (forall x cx, Env.find x cenvl' = Some cx <-> HasLastCaus Γ' x cx) ->
          incl xs (map fst Γ') ->
          (forall x, IsVar Γ x <-> IsVar Γ' x) ->
          (forall x, IsLast Γ x -> IsLast Γ' x) ->
          P_vd blks xs ->
          P_nd blks ->
          P_wl blks ->
          P_wx blks ->
          P_def Γ' blks ->
          Env.In cx (f_coll cenv' cenvl' blks)) ->
      Env.In cx (collect_depends_branch f_coll cenv' cenvl' (Branch caus blks)).
  Proof.
    intros * Hnd Hc Hcl Hincl Hvd Hndloc Hwl Hwx Hdef Hp.
    inv Hvd. inv Hndloc. inv Hwl. inv Hwx.
    assert (NoDupMembers (replace_idcaus caus Γ)) as Hnd'.
    { apply NoDupMembers_map; auto. }
    simpl. repeat rewrite Env.union_fuse_In.
    inv Hdef.
    - eapply Hp in H5; eauto.
      + now apply equiv_env_branch.
      + now apply equiv_env_last_branch.
      + now rewrite map_fst_replace_idcaus.
      + intros. now rewrite replace_idcaus_IsVar.
      + intros. now apply replace_idcaus_IsLast.
    - right. simpl_In.
      apply Env.In_from_list. solve_In.
      apply Hc in H8. rewrite H8; simpl; auto.
  Qed.

  Lemma collect_depends_on_dom {PSyn prefs} (G: @global PSyn prefs) : forall blk xs Γ cenv' cenvl' cx,
      NoDupMembers Γ ->
      (forall x cx, Env.find x cenv' = Some cx <-> HasCaus Γ x cx) ->
      (forall x cx, Env.find x cenvl' = Some cx <-> HasLastCaus Γ x cx) ->
      VarsDefinedComp blk xs ->
      incl xs (map fst Γ) ->
      NoDupLocals (map fst Γ) blk ->
      wl_block G blk ->
      wx_block Γ blk ->
      Is_defined_in Γ cx blk ->
      Env.In cx (collect_depends_on cenv' cenvl' blk).
  Proof.
    Opaque collect_depends_scope.
    induction blk using block_ind2; intros * Hnd Hc Hcl Hvars Hincl Hndloc Hwl Hwx Hdef;
      inv Hvars; inv Hndloc; inv Hwl; inv Hwx; simpl.
    - (* equation *)
      destruct eq; simpl.
      rewrite Env.In_from_list, fst_InMembers, combine_map_fst'.
      2:{ inv H0. erewrite map_length, collect_used_inst_list_length; eauto. }
      inv Hdef.
      eapply collect_used_var_complete in H4; eauto.
      solve_In.
    - (* last *)
      inv Hdef.
      eapply collect_used_last_complete in H0; eauto. subst.
      apply Env.In_add1.
    - (* reset *)
      rewrite Env.Props.P.F.map_in_iff, unions_fuse_PS_In.
      + inv Hdef; solve_Exists; simpl_Forall; inv_VarsDefined.
        eapply H; eauto.
        etransitivity; eauto using incl_concat.
    - (* switch *)
      erewrite Env.Props.P.F.map_in_iff, unions_fuse_PS_In, Exists_map.
      inv Hdef. solve_Exists. simpl_Forall.
      destruct b.
      eapply collect_depends_branch_dom; eauto.
      intros. rewrite unions_fuse_PS_In. simpl in *.
      solve_Exists; inv_VarsDefined; simpl_Forall.
      + solve_Exists. eapply H; eauto.
        * etransitivity; eauto. rewrite <-H21; eauto using incl_concat.
        * eapply NoDupLocals_incl; [|eauto]. apply IsVar_incl_fst, H14.
        * eapply wx_block_incl with (Γ:=Γ); eauto. apply H14.
    - (* automaton *)
      erewrite Env.Props.P.F.map_in_iff, unions_fuse_PS_In, Exists_map.
      inv Hdef. solve_Exists. simpl_Forall.
      destruct b as [?(?&[?(?&?)])].
      eapply collect_depends_branch_dom; eauto. intros; simpl in *; destruct_conjs.
      eapply collect_depends_scope_dom; eauto.
      1:{ eapply NoDupScope_incl. 3:eauto. 2:apply IsVar_incl_fst, H12.
          intros; simpl in *; simpl_Forall; eauto using NoDupLocals_incl. }
      1:{ eapply wx_scope_incl. 4:eauto. all:eauto. apply H12.
          intros; simpl in *; simpl_Forall; destruct_conjs; split; simpl_Forall; eauto using wx_exp_incl, wx_block_incl. }
      2:{ intros; simpl in *; destruct_conjs; split; simpl_Forall; eauto using wx_exp_incl, wx_block_incl. }
      intros. rewrite unions_fuse_PS_In. simpl in *.
      solve_Exists; inv_VarsDefined; simpl_Forall.
      + eapply H; eauto.
        etransitivity; eauto. rewrite <-H35; eauto using incl_concat.
    - (* locals *)
      eapply collect_depends_scope_dom; eauto.
      + inv Hdef; eauto.
      + intros. rewrite unions_fuse_PS_In. simpl in *.
        solve_Exists; inv_VarsDefined; simpl_Forall.
        * eapply H; eauto.
          etransitivity; eauto. rewrite <-H13; eauto using incl_concat.
      + intros; simpl in *. simpl_Forall; eauto using wx_block_incl.
  Qed.

  Lemma unions_fuse_Subset : forall x envs e ps,
      In e envs ->
      Env.find x e = Some ps ->
      exists ps', Env.find x (unions_fuse envs) = Some ps' /\ PS.Subset ps ps'.
  Proof.
    intros x envs.
    unfold unions_fuse.
    replace envs with (rev (rev envs)); auto using rev_involutive.
    setoid_rewrite fold_right_rev_left. setoid_rewrite <-In_rev.
    induction (rev envs); intros * Hin Hfind; simpl in *. inv Hin.
    rewrite Env.union_fuse_spec. inv Hin.
    - rewrite Hfind.
      destruct (Env.find _ _); do 2 esplit; eauto. 2:reflexivity.
      apply PSP.union_subset_2.
    - eapply IHl in H as (?&Hfind'&Hsub); eauto.
      rewrite Hfind'.
      destruct (Env.find x a); do 2 esplit; eauto.
      etransitivity; eauto. apply PSP.union_subset_1.
  Qed.

  Lemma collect_used_var_nodup: forall xs cenv',
      Forall (fun x => Env.In x cenv') xs ->
      NoDup xs ->
      NoDup (map snd (Env.elements cenv')) ->
      NoDup (map (collect_used_var cenv') xs).
  Proof.
    induction xs; intros * Hf Hxs Hcenv'; inv Hf; inv Hxs; simpl.
    - constructor.
    - destruct H1 as (?&Hfind).
      unfold collect_used_var, Env.MapsTo in *. rewrite Hfind; simpl.
      constructor; eauto.
      contradict H3.
      simpl_In.
      eapply Forall_forall in H2 as (?&Hfind'); eauto. unfold Env.MapsTo in *.
      rewrite Hfind' in Hfind; simpl in Hfind; subst.
      eapply Env.NoDup_snd_elements with (x1:=a) (x2:=x0) in Hcenv'; eauto; subst; auto.
  Qed.

  Fact NoDup_locals_inv : forall blks blk xs,
      In blk blks ->
      NoDup (map snd (xs ++ flat_map idcaus_of_locals blks)) ->
      NoDup (map snd (xs ++ idcaus_of_locals blk)).
  Proof.
    intros * Hin Hnd.
    repeat rewrite map_app in *.
    eapply nodup_app_map_flat_map; eauto.
  Qed.

  Fact NoDup_locals_inv2 {A B} (f_idcaus : B -> list (ident * ident)) : forall (brs : list (A * B)) k blks xs,
      In (k, blks) brs ->
      NoDup (map snd (xs ++ flat_map (fun '(_, blks) => f_idcaus blks) brs)) ->
      NoDup (map snd (xs ++ f_idcaus blks)).
  Proof.
    intros * Hin Hnd.
    repeat rewrite map_app in *.
    eapply nodup_app_map_flat_map with (ys:=map snd brs); eauto. solve_In.
    erewrite flat_map_concat_map, map_map, <-flat_map_concat_map, flat_map_ext; eauto.
    intros; destruct_conjs; auto.
  Qed.

  Fact NoDup_locals_inv3 {A B T} (f_idcaus : B -> list (ident * ident)) : forall (brs : list (A * (T * B))) k trans blks xs,
      In (k, (trans, blks)) brs ->
      NoDup (map snd (xs ++ flat_map (fun '(_, (_, blks)) => f_idcaus blks) brs)) ->
      NoDup (map snd (xs ++ f_idcaus blks)).
  Proof.
    intros * Hin Hnd.
    repeat rewrite map_app in *.
    eapply nodup_app_map_flat_map with (ys:=map (fun x => snd (snd x)) brs); eauto. solve_In.
    erewrite flat_map_concat_map, map_map, <-flat_map_concat_map, flat_map_ext; eauto.
    intros; destruct_conjs; auto.
  Qed.

  Fact map_fst_map_filter : forall (locs : list decl),
      map fst (map_filter (fun '(x0, (_, _, _, o)) => option_map (fun cx => (x0, cx)) o) locs) =
      map_filter (fun '(x0, (_, _, o)) => option_map (fun _ => x0) o) locs.
  Proof.
    intros.
    erewrite map_map_filter, map_filter_ext; eauto.
    intros; destruct_conjs. destruct o as [|]; auto.
  Qed.

  Fact collect_used_clock_spec : forall Γ cenv x cx ck,
      (forall x cx, Env.find x cenv = Some cx <-> HasCaus Γ x cx) ->
      Is_free_in_clock x ck ->
      HasCaus Γ x cx ->
      PS.In cx (collect_used_clock cenv ck).
  Proof.
    induction ck; intros * Href Hfree Hcaus; inv Hfree; simpl; eauto using PSF.add_2.
    eapply PSF.add_1, collect_used_var_complete; eauto.
  Qed.

  Fact find_caus_NoDupMembers cenv : forall caus,
    NoDup (map snd (Env.elements cenv)) ->
    NoDupMembers caus ->
    Forall (fun '(x, _) => Env.In x cenv) caus ->
    NoDupMembers (map (fun '(x, cx) => (or_default x (Env.find x cenv), PS.singleton cx)) caus).
  Proof.
    intros * Hnd1 Hnd2 Hf.
    induction caus; inv Hnd2; inv Hf; simpl. constructor.
    destruct H3 as (?&Hfind). unfold Env.MapsTo in Hfind. rewrite Hfind; simpl.
    constructor; auto.
    intros * Hinm. simpl_In. simpl_Forall.
    destruct H4 as (?&Hfind2). unfold Env.MapsTo in Hfind2. rewrite Hfind2 in Hfind; simpl in *.
    eapply Env.NoDup_snd_elements in Hfind; eauto; subst.
    take (~ _) and eapply it; solve_In.
  Qed.

  Fact find_caus_NoDup cenv : forall (caus: list (ident * ident)),
      NoDup (map snd cenv) ->
      NoDupMembers cenv ->
      Forall (fun '(_, x) => ~In x (map snd caus)) cenv ->
      NoDup (map snd caus) ->
      NoDup (map snd (map (fun '(x0, y0) => (x0, or_default y0 (assoc_ident x0 caus))) cenv)).
  Proof.
    intros * Hnd1 Hnd3 Hf Hnd2.
    induction cenv as [|(?&?)]; inv Hnd1; inv Hnd3; inv Hf; simpl; constructor; auto.
    intros Hnin; simpl_In; simpl_Forall.
    destruct (assoc_ident i caus) eqn:Has1, (assoc_ident i1 caus) eqn:Has2;
      repeat (match goal with
              | H:assoc_ident _ _ = Some _ |- _ => apply assoc_ident_In in H
              | H:assoc_ident _ _ = None |- _ => apply assoc_ident_false in H
              end); simpl in *; subst.
    - eapply NoDup_snd_det in Has1; eauto; subst.
      eapply H3. solve_In.
    - eapply H6. solve_In.
    - eapply H4. solve_In.
    - eapply H1. solve_In.
  Qed.

  Lemma collect_depends_scope_spec {A} f_idcaus P_vd P_nd P_wl P_wx P_dep f_dep {PSyn prefs} (G: @global PSyn prefs) :
    forall x y locs (blks: A) xs Γ cenv' cenvl',
      NoDupMembers Γ ->
      (forall x cx, Env.find x cenv' = Some cx <-> HasCaus Γ x cx) ->
      (forall x cx, Env.find x cenvl' = Some cx <-> HasLastCaus Γ x cx) ->
      NoDup (map snd (Env.elements cenv' ++ Env.elements cenvl' ++ idcaus_of_scope f_idcaus (Scope locs blks))) ->
      VarsDefinedCompScope P_vd (Scope locs blks) xs ->
      NoDup xs ->
      Forall (fun x => Env.In x cenv') xs ->
      NoDupScope P_nd (map fst Γ) (Scope locs blks) ->
      wl_scope P_wl G (Scope locs blks) ->
      wx_scope P_wx Γ (Scope locs blks) ->
      depends_on_scope P_dep Γ x y (Scope locs blks) ->
      (forall xs Γ cenv' cenvl',
          NoDupMembers Γ ->
          (forall x cx, Env.find x cenv' = Some cx <-> HasCaus Γ x cx) ->
          (forall x cx, Env.find x cenvl' = Some cx <-> HasLastCaus Γ x cx) ->
          NoDup (map snd (Env.elements cenv' ++ Env.elements cenvl' ++ f_idcaus blks)) ->
          P_vd blks xs ->
          NoDup xs ->
          Forall (fun x => Env.In x cenv') xs ->
          P_nd (map fst Γ) blks ->
          P_wl blks ->
          P_wx Γ blks ->
          P_dep Γ x y blks ->
          exists s, Env.MapsTo x s (f_dep cenv' cenvl' blks) /\ PS.In y s) ->
      exists s, Env.MapsTo x s (collect_depends_scope f_dep cenv' cenvl' (Scope locs blks)) /\ PS.In y s.
  Proof.
    Transparent collect_depends_scope.
    intros * Hnd1 Henv Henvl Hnd4 Hvars Hndvars Hvarsenv Hndl Hwl Hwx Hdep Hind;
      simpl; inv Hvars; inv Hndl; inv Hwl; inv Hwx; inv Hdep; subst Γ'.

    simpl_Exists. inv_VarsDefined. take (P_dep _ _ _ _) and rename it into Hdep.
    eapply Hind with (xs:=xs ++ map fst locs) in Hdep as (?&Hfind&Hpsin); eauto.
    + apply NoDupScope_NoDupMembers; auto.
    + eapply equiv_env_scope; eauto.
    + eapply equiv_env_last_scope; eauto.
    + rewrite 2 Env.elements_adds. simpl_app.
      2,3:apply NoDupMembers_app; eauto using Env.NoDupMembers_elements.
      * eapply Permutation_NoDup, Hnd4. unfold idcaus_of_senv. simpl_app. symmetry.
        apply Permutation_app_head. rewrite Permutation_swap. apply Permutation_app_head.
        erewrite 3 map_map, map_ext, map_filter_map, map_filter_ext. reflexivity.
        1,2:intros; destruct_conjs; auto.
      * apply NoDupMembers_map_filter; auto.
        intros; destruct_conjs. destruct o as [|]; simpl; auto.
      * intros * Hin1 Hin2. simpl_In.
        apply Env.elements_In in Hin0 as (?&Find).
        apply Henvl in Find; inv Find.
        eapply H5; solve_In.
      * apply NoDupMembers_map; auto. intros; destruct_conjs; auto.
      * intros * Hin1 Hin2. simpl_In.
        apply Env.elements_In in Hin as (?&Find).
        apply Henv in Find; inv Find.
        eapply H5; solve_In.
    + apply NoDup_app'; auto.
      * now eapply fst_NoDupMembers.
      * simpl_Forall. intros Hin2. inv Hvarsenv. eapply Henv in H3. inv H3.
        eapply H5. apply fst_InMembers; eauto. solve_In.
    + simpl_Forall.
      apply Env.In_adds_spec'.
      apply in_app_or in H as [Hin'|Hin']; [right|left].
      * simpl_Forall; eauto.
      * solve_In.
    + rewrite map_app, map_fst_senv_of_decls; auto.
  Qed.

  Lemma collect_depends_branch_spec {A} f_idcaus P_vd P_nd P_wl P_wx P_dep f_dep {PSyn prefs} (G: @global PSyn prefs) :
    forall x y caus (blks: A) xs Γ cenv' cenvl',
      NoDupMembers Γ ->
      (forall x cx, Env.find x cenv' = Some cx <-> HasCaus Γ x cx) ->
      (forall x cx, Env.find x cenvl' = Some cx <-> HasLastCaus Γ x cx) ->
      NoDup (map snd (Env.elements cenv' ++ Env.elements cenvl' ++ idcaus_of_branch f_idcaus (Branch caus blks))) ->
      VarsDefinedCompBranch P_vd (Branch caus blks) xs ->
      NoDup xs ->
      Forall (fun x => Env.In x cenv') xs ->
      NoDupBranch P_nd (Branch caus blks) ->
      wl_branch P_wl (Branch caus blks) ->
      wx_branch P_wx (Branch caus blks) ->
      depends_on_branch P_dep Γ x y (Branch caus blks) ->
      (forall xs Γ' cenv' cenvl',
          NoDupMembers Γ' ->
          (forall x cx, Env.find x cenv' = Some cx <-> HasCaus Γ' x cx) ->
          (forall x cx, Env.find x cenvl' = Some cx <-> HasLastCaus Γ' x cx) ->
          (forall x, IsVar Γ x <-> IsVar Γ' x) ->
          (forall x, IsLast Γ x -> IsLast Γ' x) ->
          NoDup (map snd (Env.elements cenv' ++ Env.elements cenvl' ++ f_idcaus blks)) ->
          P_vd blks xs ->
          NoDup xs ->
          Forall (fun x => Env.In x cenv') xs ->
          P_nd blks ->
          P_wl blks ->
          P_wx blks ->
          P_dep Γ' x y blks ->
          exists s, Env.MapsTo x s (f_dep cenv' cenvl' blks) /\ PS.In y s) ->
      exists s, Env.MapsTo x s (collect_depends_branch f_dep cenv' cenvl' (Branch caus blks)) /\ PS.In y s.
  Proof.
    Transparent collect_depends_branch.
    intros * Hnd1 Henv Henvl Hnd4 Hvars Hndvars Hvarsenv Hndl Hwl Hwx Hdep Hind;
      simpl; inv Hvars; inv Hndl; inv Hwl; inv Hwx; inv Hdep.

    - (* sub-blocks *)
      simpl_Exists. inv_VarsDefined. take (P_dep _ _ _ _) and rename it into Hdep.
      eapply Hind with (xs:=xs) (Γ':=replace_idcaus _ Γ) (cenv':=Env.mapi _ _) in Hdep as (?&Hfind&Hpsin); eauto.
      + unfold Env.MapsTo. rewrite Env.union_fuse_spec, Hfind.
        destruct (Env.find x (Env.from_list _)).
        all:repeat esplit; try reflexivity.
        all:repeat rewrite PSF.union_iff; eauto.
      + apply NoDupMembers_map; auto.
      + eapply equiv_env_branch; eauto.
      + eapply equiv_env_last_branch; eauto.
      + intros. now rewrite replace_idcaus_IsVar.
      + intros. now rewrite replace_idcaus_IsLast.
      + rewrite Env.mapi_elements.
        simpl_app. apply NoDup_app'.
        * apply find_caus_NoDup; eauto using Env.NoDupMembers_elements, NoDup_app_l, NoDup_app_r.
          simpl_Forall. eapply NoDup_app_In in Hnd4; [|solve_In]. contradict Hnd4.
          repeat rewrite in_app_iff; auto.
        * clear - Hnd4.
          eapply NoDup_app_r in Hnd4. rewrite (Permutation_app_comm (map snd caus)), app_assoc in Hnd4; eauto using NoDup_app_l.
        * simpl_Forall.
          destruct (assoc_ident k caus) eqn:Hcaus; simpl in *.
          -- apply assoc_ident_In in Hcaus. intros Hin.
             rewrite (Permutation_app_comm (map snd caus)) in Hnd4.
             repeat rewrite app_assoc in Hnd4.
             eapply NoDup_app_In in Hnd4. eapply Hnd4; solve_In.
             simpl. unfold idcaus_of_senv. simpl_app.
             repeat rewrite in_app_iff in *. destruct Hin as [|]; auto.
          -- eapply NoDup_app_In in Hnd4; [|solve_In]. contradict Hnd4.
             repeat rewrite in_app_iff in *. destruct Hnd4 as [|]; auto.
      + simpl_Forall.
        rewrite Env.Props.P.F.mapi_in_iff. eauto.

    - (* caus *)
      assert (exists s,
                 Env.find x (Env.from_list (map (fun '(x1, cx) =>
                                                   (or_default x1 (Env.find x1 cenv'), PS.singleton cx)) caus)) = Some s
                 /\ PS.In y s) as (?&Hfind&Hps).
      { repeat esplit; eauto. subst.
        apply Env.find_In_from_list.
        - solve_In.
          apply Henv in H7. rewrite H7; simpl; auto.
        - apply find_caus_NoDupMembers; auto.
          + simpl_app; eauto using NoDup_app_l.
          + simpl_Forall. eapply In_InMembers, fst_InMembers, H3 in H. simpl_Forall; auto.
        - now apply PSF.singleton_2.
      }
      unfold Env.MapsTo. rewrite Env.union_fuse_spec, Hfind. clear Hfind.
      destruct (Env.find _ (f_dep _ _ _)); subst; eauto.
      all:do 2 esplit; eauto; repeat rewrite PSF.union_iff; auto.
  Qed.

  Lemma collect_depends_on_spec {PSyn prefs} : forall (G: @global PSyn prefs) x y blk xs Γ cenv' cenvl',
      NoDupMembers Γ ->
      (forall x cx, Env.find x cenv' = Some cx <-> HasCaus Γ x cx) ->
      (forall x cx, Env.find x cenvl' = Some cx <-> HasLastCaus Γ x cx) ->
      NoDup (map snd (Env.elements cenv' ++ Env.elements cenvl' ++ idcaus_of_locals blk)) ->
      VarsDefinedComp blk xs ->
      NoDup xs ->
      Forall (fun x => Env.In x cenv') xs ->
      NoDupLocals (map fst Γ) blk ->
      wl_block G blk ->
      wx_block Γ blk ->
      depends_on Γ x y blk ->
      exists s, Env.MapsTo x s (collect_depends_on cenv' cenvl' blk) /\ PS.In y s.
  Proof.
    Opaque collect_depends_scope collect_depends_branch.
    induction blk using block_ind2; intros * Hnd1 Henv Henvl Hnd4 Hvars Hndvars Hvarsenv Hndl Hwl Hwx Hdep;
      simpl; inv Hvars; inv Hndl; inv Hwl; inv Hwx; inv Hdep.

    - (* equation *)
      inv H0. inv H2.
      eapply collect_used_inst_list_spec in H4; eauto.
      repeat esplit; eauto.
      erewrite <-collect_used_inst_list_length in H5; eauto.
      apply Env.find_In_from_list.
      2:{ rewrite fst_NoDupMembers, combine_map_fst'; eauto.
          2:rewrite map_length; eauto.
          eapply collect_used_var_nodup; eauto.
          solve_NoDup_app.
      }
      erewrite In_combine_nth_error.
      repeat esplit; eauto.
      + erewrite map_nth_error; eauto.
        erewrite collect_used_var_complete; eauto with senv.
      + eapply nth_error_nth'.
        erewrite <-H5. eapply nth_error_Some; intro; congruence.

    - (* last *)
      do 2 esplit.
      + erewrite collect_used_last_complete; eauto.
        now apply Env.add_1.
      + eapply collect_used_inst_spec; eauto.

    - (* reset block (sub-blocks) *)
      simpl_Exists. simpl_Forall. inv_VarsDefined.
      eapply H with (cenv':=cenv') (cenvl':=cenvl') in Hdef as (?&?&?); eauto.
      2:{ rewrite app_assoc in *. eapply NoDup_locals_inv; eauto. }
      2:eapply NoDup_concat; eauto.
      2:{ eapply Forall_incl; eauto.
          eapply incl_concat; eauto. }
      eapply unions_fuse_Subset in H0 as (?&Hfind&Hsub). 2:eapply in_map_iff; eauto.
      repeat esplit.
      + unfold Env.MapsTo. now rewrite Env.Props.P.F.map_o, Hfind.
      + eapply PSF.union_iff; eauto.
    - (* reset block (reset expr) *)
      clear H.
      eapply collect_depends_on_dom, Env.map_2, unions_fuse_PS_In, Exists_exists in H7 as (?&Hin1&(?&Hfind2)); eauto.
      2,4,5,6:econstructor; eauto.
      2:{ intros ? Hin. eapply Forall_forall in Hvarsenv; eauto.
          inv Hvarsenv. eapply Henv in H. inv H. solve_In. }
      eapply unions_fuse_Subset in Hfind2 as (?&Hfind&Hsub); eauto.
      repeat esplit.
      + unfold Env.MapsTo. erewrite Env.Props.P.F.map_o. setoid_rewrite Hfind. reflexivity.
      + eapply collect_used_inst_spec in H10; eauto.
        eapply PSF.union_iff; eauto.

    - (* switch (sub-blocks) *)
      setoid_rewrite Env.Props.P.F.map_mapsto_iff.
      simpl_Exists. destruct b. simpl_Forall.
      eapply collect_depends_branch_spec in H1 as (?&Hfind&Hpsin); eauto.
      + eapply unions_fuse_Subset in Hfind as (?&Hfind&Hsub).
        unfold Env.MapsTo. rewrite Hfind; simpl. 2:solve_In.
        do 2 esplit; eauto.
        now apply PSF.union_3, Hsub.
      + rewrite app_assoc, map_app in *.
        eapply nodup_app_map_flat_map; eauto. eapply in_map_iff with (f:=snd); do 2 esplit; eauto. auto.
        erewrite flat_map_concat_map, map_map with (l:=branches), map_ext with (l:=branches), <-flat_map_concat_map; eauto.
        intros; destruct_conjs; auto.
      + intros; simpl in *. simpl_Exists. inv_VarsDefined. simpl_Forall.
        eapply H with (xs:=xs1) (cenv':=cenv'0) (cenvl':=cenvl'0) in H20 as (?&Hinc&Hpsin); eauto.
        * eapply unions_fuse_Subset in Hinc as (?&Hfind&Hsub). 2:eapply in_map_iff; eauto.
          unfold Env.MapsTo.
          repeat esplit; try reflexivity. eauto.
          now apply Hsub.
        * rewrite app_assoc in *. eapply NoDup_locals_inv; eauto.
        * eapply NoDup_concat; eauto. now take (Permutation _ _) and rewrite it.
        * take (Permutation _ _) and rewrite <-it in H18. apply Forall_concat in H18.
          simpl_Forall; auto.
        * eapply NoDupLocals_incl; [|eauto]. apply IsVar_incl_fst, H13.
        * eapply wx_block_incl; [| |eauto]; eauto. apply H13.
    - (* switch (condition) *)
      clear H.
      eapply collect_depends_on_dom, Env.map_2, unions_fuse_PS_In, Exists_exists in H9 as (?&Hin1&(?&Hfind2)); eauto.
      2,4,5,6:econstructor; eauto.
      2:{ intros ? Hin. eapply Forall_forall in Hvarsenv; eauto.
          inv Hvarsenv. eapply Henv in H. inv H. solve_In. }
      eapply unions_fuse_Subset in Hfind2 as (?&Hfind&Hsub); eauto.
      repeat esplit.
      + unfold Env.MapsTo. erewrite Env.Props.P.F.map_o. now setoid_rewrite Hfind.
      + eapply collect_used_inst_spec in H10; eauto.
        eapply PSF.union_iff; eauto.

    - (* automaton (sub-blocks) *)
      simpl_Exists. destruct b as [?(?&[?(?&?)])]; destruct_conjs. simpl_Forall.
      eapply collect_depends_branch_spec in H1 as (?&Hfind&Hpsin); eauto.
      + eapply unions_fuse_Subset in Hfind as (?&Hfind&Hsub).
        unfold Env.MapsTo. rewrite Env.Props.P.F.map_o, Hfind; simpl. 2:solve_In.
        do 2 esplit; eauto.
        now apply PSF.union_3, Hsub.
      + rewrite app_assoc, map_app in *.
        eapply nodup_app_map_flat_map; eauto. eapply in_map_iff with (f:=fun x => (snd x)); do 2 esplit; eauto. auto.
        erewrite flat_map_concat_map, map_map with (l:=states), map_ext with (l:=states), <-flat_map_concat_map; eauto.
        intros; destruct_conjs; auto.
      + intros; simpl in *. destruct_conjs.
        eapply collect_depends_scope_spec with (f_idcaus:=fun '(_, blks) => flat_map _ _) in H23 as (?&Hfind&Hpsin); simpl in *; eauto.
        * eapply NoDupScope_incl. 3:eauto. intros; simpl in *; simpl_Forall; eauto using NoDupLocals_incl.
          apply IsVar_incl_fst, H10.
        * eapply wx_scope_incl. 4:eauto. all:eauto. apply H10.
          intros; destruct_conjs; split; simpl_Forall; eauto using wx_exp_incl, wx_block_incl.
        * intros. simpl_Exists. inv_VarsDefined. simpl_Forall.
          take (depends_on _ _ _ _) and eapply H with (xs:=xs2) in it as (?&Hinc&Hpsin); eauto.
          -- eapply unions_fuse_Subset in Hinc as (?&Hfind&Hsub). 2:eapply in_map_iff; eauto.
             unfold Env.MapsTo.
             repeat esplit; try reflexivity. eauto.
             now apply Hsub.
          -- rewrite app_assoc in *. eapply NoDup_locals_inv; eauto.
          -- eapply NoDup_concat; eauto. now take (Permutation _ _) and rewrite it.
          -- take (Permutation _ _) and rewrite <-it in H32. apply Forall_concat in H32.
             simpl_Forall; auto.
    - (* automaton (clock) *)
      clear H.
      eapply collect_depends_on_dom, Env.map_2, unions_fuse_PS_In, Exists_exists in H7 as (?&Hin1&(?&Hfind2)); eauto.
      2,4,5,6:econstructor; eauto.
      2:{ intros ? Hin. eapply Forall_forall in Hvarsenv; eauto.
          inv Hvarsenv. eapply Henv in H. inv H. solve_In. }
      eapply unions_fuse_Subset in Hfind2 as (?&Hfind&Hsub); eauto.
      repeat esplit.
      + unfold Env.MapsTo. erewrite Env.Props.P.F.map_o. now setoid_rewrite Hfind.
      + eapply collect_used_clock_spec in H16; eauto.
        repeat esplit; eauto. rewrite 2 PSF.union_iff; eauto.
    - (* automaton (initial state) *)
      clear H.
      eapply collect_depends_on_dom, Env.map_2, unions_fuse_PS_In, Exists_exists in H3 as (?&Hin1&(?&Hfind2)); eauto.
      2,4,5,6:econstructor; eauto.
      2:{ intros ? Hin. eapply Forall_forall in Hvarsenv; eauto.
          inv Hvarsenv. eapply Henv in H. inv H. solve_In. }
      eapply unions_fuse_Subset in Hfind2 as (?&Hfind&Hsub); eauto.
      repeat esplit.
      + unfold Env.MapsTo. erewrite Env.Props.P.F.map_o. now setoid_rewrite Hfind.
      + simpl_Exists; simpl_Forall.
        eapply collect_used_inst_spec in H16; eauto.
        repeat esplit; eauto. rewrite 3 PSF.union_iff. left; right; left; auto.
        eapply In_In_PSUnion; eauto. solve_In.
    - (* automaton (strong transitions) *)
      clear H.
      eapply collect_depends_on_dom, Env.map_2, unions_fuse_PS_In, Exists_exists in H3 as (?&Hin1&(?&Hfind2)); eauto.
      2,4,5,6:econstructor; eauto.
      2:{ intros ? Hin. eapply Forall_forall in Hvarsenv; eauto.
          inv Hvarsenv. eapply Henv in H. inv H. solve_In. }
      eapply unions_fuse_Subset in Hfind2 as (?&Hfind&Hsub); eauto.
      repeat esplit.
      + unfold Env.MapsTo. erewrite Env.Props.P.F.map_o. now setoid_rewrite Hfind.
      + repeat simpl_Exists; simpl_Forall.
        take (wx_branch _ _) and inv it. take (wl_branch _ _) and inv it. destruct_conjs.
        simpl_Exists. simpl_Forall.
        eapply collect_used_inst_spec in H; eauto.
        repeat esplit; eauto. rewrite 3 PSF.union_iff. left; right; right; auto.
        eapply In_In_PSUnion. 2:solve_In. simpl.
        eapply In_In_PSUnion. 2:solve_In. simpl. eauto.

    - (* local block *)
      eapply collect_depends_scope_spec; eauto.
      intros; simpl in *. simpl_Exists. inv_VarsDefined. simpl_Forall.
      take (depends_on _ _ _ _) and rename it into Hdep.
      eapply H with (xs:=xs1) in Hdep as (?&Hinc&Hpsin); eauto.
      + eapply unions_fuse_Subset in Hinc as (?&Hfind&Hsub). 2:eapply in_map_iff; eauto.
        unfold Env.MapsTo.
        repeat esplit; try reflexivity. eauto.
        now apply Hsub.
      + rewrite app_assoc in *. eapply NoDup_locals_inv; eauto.
      + eapply NoDup_concat; eauto. now take (Permutation _ _) and rewrite it.
      + take (Permutation _ _) and rewrite <-it in H11. apply Forall_concat in H11.
        simpl_Forall; auto.
  Qed.

  Local Hint Constructors Is_defined_in : lcaus.

  Fact Is_free_in_clock_In Γ : forall x ck,
      wx_clock Γ ck ->
      Is_free_in_clock x ck ->
      IsVar Γ x.
  Proof.
    induction ck; intros * Hwx Hf; inv Hwx; inv Hf; auto.
  Qed.

  Lemma Is_used_inst_In Γ Γ' : forall e k x cx,
      NoDup (map snd (idcaus_of_senv Γ)) ->
      HasCaus Γ x cx \/ HasLastCaus Γ x cx ->
      wx_exp Γ' e ->
      Is_used_inst Γ cx k e ->
      IsVar Γ' x.
  Proof.
    induction e using exp_ind2; intros * Hnd Hin Hwx Hfree; inv Hwx; inv Hfree; eauto;
      repeat match goal with
             | H: _ \/ _ |- _ => destruct H
             | Hc1: HasCaus Γ _ ?cx, Hc2: HasCaus Γ _ ?cx |- _ =>
                 eapply HasCaus_snd_det in Hc1; eauto; subst
             | Hc1: HasLastCaus Γ _ ?cx, Hc2: HasLastCaus Γ _ ?cx |- _ =>
                 eapply HasLastCaus_snd_det in Hc1; eauto; subst
             | Hc1: HasCaus Γ _ ?cx, Hc2: HasLastCaus Γ _ ?cx |- _ =>
                 exfalso; eauto using NoDup_HasCaus_HasLastCaus
             | H: Is_used_inst_list _ _ _ _ |- _ => apply Is_used_inst_list_Exists in H as (?&?)
             | H: forall _, Some _ = Some _ -> _ |- _ => specialize (H _ eq_refl)
             | _ => simpl_Exists; simpl_Forall; subst
             end; eauto using IsLast_IsVar.
  Qed.

  Lemma depends_scope_In {A} f_idcaus P_vd P_nd P_wx P_dep : forall locs (blks: A) Γ Γ' xs cy x cx,
      NoDupMembers Γ ->
      NoDup (map snd (idcaus_of_senv Γ ++ idcaus_of_scope f_idcaus (Scope locs blks))) ->
      incl xs (map fst Γ') ->
      HasCaus Γ x cx \/ HasLastCaus Γ x cx ->
      VarsDefinedCompScope P_vd (Scope locs blks) xs ->
      NoDupScope P_nd (map fst Γ) (Scope locs blks) ->
      wx_scope P_wx Γ' (Scope locs blks) ->
      depends_on_scope P_dep Γ cy cx (Scope locs blks) ->
      (forall Γ Γ' xs,
          NoDupMembers Γ ->
          NoDup (map snd (idcaus_of_senv Γ ++ f_idcaus blks)) ->
          incl xs (map fst Γ') ->
          HasCaus Γ x cx \/ HasLastCaus Γ x cx ->
          P_vd blks xs ->
          P_nd (map fst Γ) blks ->
          P_wx Γ' blks ->
          P_dep Γ cy cx blks ->
          IsVar Γ' x) ->
      IsVar Γ' x.
  Proof.
    intros * Hnd1 Hnd Hincl Hin Hnd2 Hvd Hwx Hdep Hind; inv Hwx; inv Hdep; inv Hnd2; inv Hvd; simpl in *; subst Γ'0.
    eapply Hind with (Γ':=Γ' ++ _) (xs:=xs ++ _) in H3; eauto.
    + apply IsVar_app in H3 as [|]; auto. exfalso.
      inv H. rewrite InMembers_senv_of_decls in H0.
      eapply H7; eauto.
      destruct Hin as [Hin|Hin]; inv Hin; solve_In.
    + apply NoDupMembers_app; auto.
      * now apply NoDupMembers_senv_of_decls.
      * intros * Hin1 Hin2. rewrite fst_InMembers in Hin1. rewrite InMembers_senv_of_decls in Hin2.
        eapply H7; eauto.
    + rewrite idcaus_of_senv_app, <-app_assoc.
      eapply Permutation_NoDup; [|eauto]. solve_Permutation_app.
    + rewrite map_app, map_fst_senv_of_decls.
      apply incl_appl'; auto.
    + rewrite HasCaus_app, HasLastCaus_app.
      destruct Hin; auto using replace_idcaus_HasCaus2.
    + rewrite map_app, map_fst_senv_of_decls; auto.
  Qed.

  Lemma depends_branch_In {A} f_idcaus P_vd P_nd P_wx P_dep : forall caus (blks: A) Γ1 Γ2 xs cy x cx,
      NoDupMembers Γ1 ->
      NoDup (map snd (idcaus_of_senv Γ1 ++ idcaus_of_branch f_idcaus (Branch caus blks))) ->
      incl xs (map fst Γ2) ->
      HasCaus Γ1 x cx \/ HasLastCaus Γ1 x cx ->
      VarsDefinedCompBranch P_vd (Branch caus blks) xs ->
      NoDupBranch P_nd (Branch caus blks) ->
      wx_branch P_wx (Branch caus blks) ->
      depends_on_branch P_dep Γ1 cy cx (Branch caus blks) ->
      (forall Γ1' xs,
          NoDupMembers Γ1' ->
          NoDup (map snd (idcaus_of_senv Γ1' ++ f_idcaus blks)) ->
          incl xs (map fst Γ2) ->
          HasCaus Γ1' x cx \/ HasLastCaus Γ1' x cx ->
          (forall x, IsVar Γ1 x <-> IsVar Γ1' x) ->
          (forall x, IsLast Γ1 x -> IsLast Γ1' x) ->
          P_vd blks xs ->
          P_nd blks ->
          P_wx blks ->
          P_dep Γ1' cy cx blks ->
          IsVar Γ2 x) ->
      IsVar Γ2 x.
  Proof.
    intros * Hnd1 Hnd Hincl Hin Hnd2 Hvd Hwx Hdep Hind; inv Hwx; inv Hdep; inv Hnd2; inv Hvd; simpl in *.
    - (* sub-blocks *)
      destruct (InMembers_dec x caus ident_eq_dec).
      1:{ constructor. now apply fst_InMembers, Hincl, H5, fst_InMembers. }
      eapply Hind with (xs:=xs) in H1; eauto.
      + now apply NoDupMembers_map.
      + apply replace_idcaus_NoDup; auto.
      + rewrite replace_idcaus_HasLastCaus.
        destruct Hin; auto using replace_idcaus_HasCaus2.
      + intros. now rewrite replace_idcaus_IsVar.
      + intros. now rewrite replace_idcaus_IsLast.
    - (* renamed caus *)
      apply idcaus_of_senv_In in Hin.
      eapply NoDup_snd_det in Hnd. 2,3:repeat rewrite in_app_iff. 2:left; eauto. 2:right; eauto.
      subst.
      constructor. apply fst_InMembers, Hincl, H6. solve_In.
  Qed.

  Lemma depends_on_In : forall blk Γ Γ' xs cy x cx,
      NoDupMembers Γ ->
      NoDup (map snd (idcaus_of_senv Γ ++ idcaus_of_locals blk)) ->
      incl xs (map fst Γ') ->
      HasCaus Γ x cx \/ HasLastCaus Γ x cx ->
      VarsDefinedComp blk xs ->
      NoDupLocals (map fst Γ) blk ->
      wx_block Γ' blk ->
      depends_on Γ cy cx blk ->
      IsVar Γ' x.
  Proof.
    induction blk using block_ind2; intros * Hnd1 Hnd Hincl Hin Hvd Hnd2 Hwx Hdep;
      inv Hwx; inv Hdep; inv Hvd; inv Hnd2; simpl in *.
    - (* equation *)
      rewrite app_nil_r in Hnd.
      eapply Is_used_inst_list_Exists in H3 as (?&Hfree). simpl_Exists. simpl_Forall.
      eapply Is_used_inst_In in Hfree; eauto.

    - (* last *)
      rewrite app_nil_r in Hnd.
      eapply Is_used_inst_In in H4; eauto.

    - (* reset *)
      simpl_Exists; simpl_Forall. inv_VarsDefined.
      eapply H with (xs:=xs); eauto.
      + eapply NoDup_locals_inv; eauto.
      + etransitivity; eauto using incl_concat.
    - rewrite map_app in Hnd.
      eapply Is_used_inst_In in H5; eauto using NoDup_app_l.

    - (* switch *)
      rename H1 into Hdef. simpl_Exists. simpl_Forall.
      destruct b. eapply depends_branch_In with (Γ2:=Γ'); eauto.
      + rewrite map_app in *.
        eapply nodup_app_map_flat_map; eauto. eapply in_map_iff with (f:=snd); do 2 esplit; eauto. auto.
        erewrite flat_map_concat_map, map_map with (l:=branches), map_ext with (l:=branches), <-flat_map_concat_map; eauto.
        intros; destruct_conjs; auto.
      + intros; simpl in *. simpl_Exists. simpl_Forall. inv_VarsDefined.
        eapply H with (xs:=xs1); eauto.
        * rewrite map_app in *. eapply nodup_app_map_flat_map; eauto.
        * etransitivity; [|eauto]. rewrite <-H15; eauto using incl_concat.
        * eapply NoDupLocals_incl; [|eauto]. apply IsVar_incl_fst, H9.
    - rewrite map_app in Hnd.
      eapply Is_used_inst_In in H3; eauto using NoDup_app_l.

    - (* automaton *)
      simpl_Exists. simpl_Forall.
      destruct b as [?(?&[?(?&?)])]. eapply depends_branch_In; eauto.
      + rewrite map_app in *.
        eapply nodup_app_map_flat_map; eauto. eapply in_map_iff with (f:=fun x => snd x); do 2 esplit; eauto. auto.
        erewrite flat_map_concat_map, map_map with (l:=states), map_ext with (l:=states), <-flat_map_concat_map; eauto.
        intros; destruct_conjs; auto.
      + intros; simpl in *. destruct_conjs.
        eapply depends_scope_In with (f_idcaus:=fun '(_, blks) => flat_map _ _) in H17; simpl in *; eauto.
        1:{ eapply NoDupScope_incl. 3:eauto. intros; simpl in *; simpl_Forall; eauto using NoDupLocals_incl.
          apply IsVar_incl_fst, H12. }
        intros; simpl in *.
        simpl_Exists. simpl_Forall. inv_VarsDefined.
        eapply H with (xs:=xs2); eauto.
        * rewrite map_app in *. eapply nodup_app_map_flat_map; eauto.
        * etransitivity; [|eauto]. take (Permutation _ xs1) and rewrite <-it; eauto using incl_concat.
    - rewrite map_app in Hnd.
      simpl_Exists. simpl_Forall.
      eapply Is_free_in_clock_In in H10; eauto.
      assert (x = y); subst; auto.
      destruct Hin.
      + eapply HasCaus_snd_det; eauto using NoDup_app_l.
      + exfalso. eapply NoDup_HasCaus_HasLastCaus; eauto using NoDup_app_l.
    - rewrite map_app in Hnd.
      simpl_Exists. simpl_Forall.
      eapply Is_used_inst_In in H10; eauto using NoDup_app_l.
    - rewrite map_app in Hnd.
      simpl_Exists. destruct b as [?(?&[?(?&?)])]. simpl_Exists. simpl_Forall.
      take (wx_branch _ _) and inv it. destruct_conjs. simpl_Forall.
      eapply Is_used_inst_In in H10; eauto using NoDup_app_l.

    - (* local *)
      eapply depends_scope_In; eauto.
      intros; simpl in *. simpl_Exists. simpl_Forall. inv_VarsDefined.
      eapply H with (xs:=xs1); eauto.
      + rewrite map_app in *. eapply nodup_app_map_flat_map; eauto.
      + etransitivity; [|eauto]. rewrite <-H12; eauto using incl_concat.
  Qed.

  Global Hint Constructors Is_defined_in Is_defined_in_scope Is_defined_in_branch : lcaus.
  Global Hint Constructors depends_on depends_on_scope depends_on_branch : lcaus.

  Lemma depends_scope_def {A} P_dep (P_def: _ -> _ -> Prop) cy cx : forall locs (blk: A) Γ,
      depends_on_scope P_dep Γ cy cx (Scope locs blk) ->
      (forall Γ, P_dep Γ cy cx blk -> P_def Γ blk) ->
      Is_defined_in_scope P_def Γ cy (Scope locs blk).
  Proof.
    intros * Hdep Hind; inv Hdep.
    econstructor; eauto.
  Qed.

  Lemma depends_branch_def {A} P_dep (P_def: _ -> _ -> Prop) cy cx : forall caus (blk: A) Γ,
      depends_on_branch P_dep Γ cy cx (Branch caus blk) ->
      (forall Γ, P_dep Γ cy cx blk -> P_def Γ blk) ->
      Is_defined_in_branch P_def Γ cy (Branch caus blk).
  Proof.
    intros * Hdep Hind; inv Hdep.
    - constructor; auto.
    - eapply DefBranch2; eauto using In_InMembers.
  Qed.

  Lemma depends_on_def cy cx : forall blk Γ,
      depends_on Γ cy cx blk ->
      Is_defined_in Γ cy blk.
  Proof.
    induction blk using block_ind2; intros * Hdep; inv Hdep; auto.
    - (* equation *)
      econstructor; eauto using nth_error_In.
    - (* last *)
      econstructor; eauto.
    - (* reset *)
      econstructor. solve_Exists. simpl_Forall. eauto.
    - (* switch *)
      simpl_Exists. destruct b.
      eapply depends_branch_def in H1.
      + econstructor. solve_Exists.
      + intros * Hex. solve_Exists. simpl_Forall. eauto.
    - (* automaton *)
      simpl_Exists. destruct b as [?(?&[?(?&?)])].
      eapply depends_branch_def in H1.
      + econstructor. solve_Exists.
      + intros * Hdep; simpl in *.
        eapply depends_scope_def in Hdep; eauto.
        intros * Hex. solve_Exists. simpl_Forall. eauto.
    - (* local *)
      eapply depends_scope_def in H1.
      + econstructor. solve_Exists.
      + intros * Hex. solve_Exists. simpl_Forall. eauto.
  Qed.

  Lemma build_graph_find {prefs} : forall (G: @global complete prefs) n x y,
      wl_node G n ->
      wx_node n ->
      NoDup (map snd (idcaus (n_in n) ++ idcaus_of_decls (n_out n) ++ idcaus_of_locals (n_block n))) ->
      depends_on_node x y n ->
      exists ys, (Env.find x (build_graph n)) = Some ys /\ PS.In y ys.
  Proof.
    intros * Hwl Hwx Hndcaus Hdep. inv Hwl. inv Hwx. subst Γ.
    pose proof (node_NoDupMembers n) as Hnd.
    pose proof (n_syn n) as Syn. inversion_clear Syn as [??? Hdef Hperm].
    unfold build_graph.
    assert (NoDupMembers (idcaus (n_in n) ++ map (fun '(x2, (_, _, cx, _)) => (x2, cx)) (n_out n))) as Hnd1.
    { unfold senv_of_ins, senv_of_decls in Hnd. rewrite fst_NoDupMembers, map_app, 2 map_map in Hnd.
      unfold idcaus. erewrite fst_NoDupMembers, map_app, 2 map_map, map_ext, map_ext with (l:=n_out n); eauto.
      1,2:unfold decl in *; intros; destruct_conjs; auto. }
    assert (NoDupMembers (map_filter (fun '(x2, (_, _, _, o)) => option_map (fun cx0 => (x2, cx0)) o) (n_out n))) as Hnd2.
    { apply NoDupMembers_map_filter.
      - intros; destruct_conjs; auto. destruct o as [|]; simpl; auto.
      - eapply fst_NoDupMembers, NoDup_app_r, n_nodup. }

    assert (forall x cx,
               Env.find x (Env.from_list (idcaus (n_in n) ++ map (fun '(x, (_, _, cx, _)) => (x, cx)) (n_out n))) = Some cx
               <-> HasCaus (senv_of_ins (n_in n) ++ senv_of_decls (n_out n)) x cx
           ) as Henv.
    { split; intros Hin.
      - apply Env.from_list_find_In, in_app_iff in Hin as [Hin|Hin]; simpl_In;
          [left|right]; econstructor; solve_In; auto.
      - inv Hin. apply Env.find_In_from_list; auto.
        apply in_app_iff. apply in_app_iff in H1 as [|]; [left|right]; solve_In.
    }
    assert (forall x cx,
               Env.find x (Env.from_list (map_filter (fun '(x1, (_, _, _, o)) => option_map (fun cx => (x1, cx)) o) (n_out n))) = Some cx
               <-> HasLastCaus (senv_of_ins (n_in n) ++ senv_of_decls (n_out n)) x cx
           ) as Henvl.
    { split; intros Hin.
      - apply Env.from_list_find_In in Hin; simpl_In.
        right. econstructor. solve_In. auto.
      - inv Hin. apply Env.find_In_from_list; auto.
        apply in_app_iff in H1 as [In|In]; simpl_In; [congruence|].
        solve_In.
    }

    inv Hdep.
    (* dependency from block *)
    eapply collect_depends_on_spec in H1 as (?&Hx&Hy); eauto using node_NoDupLocals.
    + eapply unions_fuse_Subset in Hx as (?&Hfind&Hin). erewrite Hfind; eauto.
      auto with datatypes.
    + rewrite 2 Env.elements_from_list; auto.
      unfold idcaus_of_decls, idcaus_of_senv in *. simpl_app.
      erewrite map_map with (l:=n_out n), map_filter_map, map_ext with (l:=n_out n), map_filter_ext in Hndcaus; eauto.
      1,2:unfold decl; intros; destruct_conjs; auto.
    + rewrite Hperm. eapply NoDup_app_r, n_nodup.
    + rewrite Hperm. simpl_Forall.
      apply Env.In_from_list, InMembers_app, or_intror. solve_In.
  Qed.

  (** We prove that the [check_node_causality] function only succeeds if
      the node is indeed causal.
      This is a simple consequence of [build_graph_find] and [build_acyclic_graph_spec].
   *)
  Lemma check_node_causality_correct {prefs} : forall (G: @global complete prefs) n,
      wl_node G n ->
      wx_node n ->
      check_node_causality n = OK tt ->
      node_causal n.
  Proof.
    intros * Hwl Hwx Hcheck.
    unfold check_node_causality in Hcheck.
    cases_eqn Heq. inv Hcheck.
    apply Bool.andb_true_iff in Heq as (NoDup&Equal).
    eapply check_nodup_correct in NoDup.
    apply PSF.equal_2 in Equal.
    eapply build_acyclic_graph_spec in Heq0 as (a&(Hv&Ha)&Graph).

    split; auto.
    exists t. exists a. exists Graph. split.
    - rewrite Equal. intros x. rewrite <- Hv.
      rewrite Env.Props.P.F.map_in_iff, In_of_list_InMembers, Env.In_Members.
      reflexivity.
    - intros x y Hdep.
      apply Ha.
      eapply build_graph_find in Hwl as (ys & Find & In); eauto.
      exists (PSP.to_list ys).
      rewrite Env.Props.P.F.map_o, Find; split; auto.
      apply In_PS_elements; auto.
  Qed.

  Corollary check_causality_correct {prefs} : forall (G: @global complete prefs) tts,
      wl_global G ->
      wx_global G ->
      check_causality G = OK tts ->
      Forall node_causal (nodes G).
  Proof.
    unfold wl_global, wx_global, CommonTyping.wt_program, CommonProgram.units, check_causality; simpl.
    intros G.
    induction (nodes G); intros * Hwl Hwx Hcheck; auto.
    inv Hwl. inv Hwx.
    unfold check_causality in Hcheck; simpl in Hcheck.
    apply bind_inversion in Hcheck as [? [? Hcheck]].
    constructor.
    + destruct x. destruct H1. eapply check_node_causality_correct in H; eauto.
    + apply bind_inversion in Hcheck as [? [? Hcheck]]; eauto.
  Qed.

  (** ** Induction lemmas over a causal node *)

  Section exp_causal_ind.
    Context {PSyn : list decl -> block -> Prop}.
    Context {prefs : PS.t}.
    Variable G : @global PSyn prefs.

    Variable Γ : static_env.

    Variable P_var : ident -> Prop.
    Variable P_exp : exp -> nat -> Prop.

    Inductive P_exps : list exp -> nat -> Prop :=
    | P_exps_now e es k :
        k < numstreams e ->
        P_exp e k ->
        P_exps (e::es) k
    | P_exps_later e es k :
        k >= numstreams e ->
        P_exps es (k-numstreams e) ->
        P_exps (e::es) k.

    Lemma Pexp_Pexps : forall es k,
        Forall (fun e => forall k, k < numstreams e
                           -> (forall x, Is_used_inst Γ x k e -> P_var x)
                           -> P_exp e k) es ->
        (forall x, Is_used_inst_list Γ x k es -> P_var x) ->
        k < length (annots es) ->
        P_exps es k.
    Proof.
      induction es; intros * Hf Hfree Hk; inv Hf; simpl in *. inv Hk.
      destruct (Nat.ltb k (numstreams a)) eqn:Hltb.
      - rewrite PeanoNat.Nat.ltb_lt in Hltb.
        constructor; eauto with lcaus.
      - eapply PeanoNat.Nat.ltb_ge in Hltb.
        eapply P_exps_later; eauto.
        eapply IHes; eauto with lcaus.
        rewrite app_length, length_annot_numstreams in Hk.
        lia.
    Qed.

    Hypothesis EconstCase : forall c,
        P_exp (Econst c) 0.

    Hypothesis EenumCase : forall k ty,
        P_exp (Eenum k ty) 0.

    Hypothesis EvarCase : forall x cx ann,
        HasCaus Γ x cx ->
        P_var cx ->
        P_exp (Evar x ann) 0.

    Hypothesis ElastCase : forall x cx ann,
        HasLastCaus Γ x cx ->
        P_var cx ->
        P_exp (Elast x ann) 0.

    Hypothesis EunopCase : forall op e1 ann,
        P_exp e1 0 ->
        P_exp (Eunop op e1 ann) 0.

    Hypothesis EbinopCase : forall op e1 e2 ann,
        P_exp e1 0 ->
        P_exp e2 0 ->
        P_exp (Ebinop op e1 e2 ann) 0.

    Hypothesis EextcallCase : forall f es ann,
        (forall k, k < length (annots es) -> P_exps es k) ->
        P_exp (Eextcall f es ann) 0.

    (* We're reasoning on causality, so we only get the hypothesis on the lhs *)
    Hypothesis EfbyCase : forall e0s es ann k,
        k < length ann ->
        P_exps e0s k ->
        P_exp (Efby e0s es ann) k.

    Hypothesis EarrowCase : forall e0s es ann k,
        k < length ann ->
        P_exps e0s k ->
        P_exps es k ->
        P_exp (Earrow e0s es ann) k.

    Hypothesis EwhenCase : forall es x tx cx b ann k,
        k < length (fst ann) ->
        P_exps es k ->
        HasCaus Γ x cx ->
        P_var cx ->
        P_exp (Ewhen es (x, tx) b ann) k.

    Hypothesis EmergeCase : forall x cx tx es ann k,
        k < length (fst ann) ->
        HasCaus Γ x cx ->
        P_var cx ->
        Forall (fun es => P_exps (snd es) k) es ->
        P_exp (Emerge (x, tx) es ann) k.

    Hypothesis EcaseCase : forall e es d ann k,
        k < length (fst ann) ->
        P_exp e 0 ->
        Forall (fun es => P_exps (snd es) k) es ->
        LiftO True (fun d => P_exps d k) d ->
        P_exp (Ecase e es d ann) k.

    Hypothesis EappCase : forall f es er ann k,
        k < length ann ->
        (forall k, k < length (annots es) -> P_exps es k) ->
        (forall k, k < length (annots er) -> P_exps er k) ->
        P_exp (Eapp f es er ann) k.

    (* Exp-level induction *)
    Fixpoint exp_causal_ind e {struct e} : forall k,
        wl_exp G e ->
        wx_exp Γ e ->
        (forall x, Is_used_inst Γ x k e -> P_var x) ->
        k < numstreams e ->
        P_exp e k.
    Proof with eauto with senv lcaus.
      Local Ltac solve_forall' es :=
        match goal with
        | Hwl: Forall (wl_exp _) es, Hwx: Forall (wx_exp _) es, Hind : forall e k, wl_exp _ e -> _ |- _ =>
          clear - Hind Hwl Hwx;
          induction es; inv Hwl; inv Hwx; constructor; auto
        end.

      intros * Hwl Hwx Hfree Hnum; destruct e; inv Hwl; inv Hwx; simpl in *;
        repeat match goal with
               | H: _ < 1 |- _ => apply PeanoNat.Nat.lt_1_r in H; subst
               end; eauto.
      - (* var *)
        inv H0. apply InMembers_In in H as (?&?).
        eapply EvarCase, Hfree...
      - (* last *)
        inv H0. destruct (causl_last e) eqn:Hfind; try congruence.
        eapply ElastCase, Hfree...
      - (* unop *)
        apply EunopCase.
        eapply exp_causal_ind... rewrite H4; auto.
      - (* binop *)
        apply EbinopCase.
        1,2:eapply exp_causal_ind... rewrite H6; auto. rewrite H7; auto.
      - (* extcall *)
        apply EextcallCase.
        + intros k' Hk'. eapply Pexp_Pexps; eauto.
          * solve_forall' l.
          * intros ? Hfree'. eapply Hfree.
            constructor; eauto.
            eapply Is_used_inst_list_Exists in Hfree' as [? ?]; eauto.
      - (* fby *)
        eapply EfbyCase; eauto.
        + eapply Pexp_Pexps... 2:congruence.
          solve_forall' l.
      - (* arrow *)
        eapply EarrowCase; eauto.
        1,2:eapply Pexp_Pexps; auto with lcaus; try congruence.
        solve_forall' l. solve_forall' l0.
      - (* when *)
        inv H1. apply InMembers_In in H as (?&?).
        eapply EwhenCase... 2:eapply Hfree...
        eapply Pexp_Pexps... 2:congruence.
        solve_forall' l.
      - (* merge *)
        inv H1. apply InMembers_In in H as (?&?).
        eapply EmergeCase... eapply Hfree...
        assert (forall x, Exists (fun es => Is_used_inst_list Γ x k (snd es)) l -> P_var x) as Hfree' by auto with lcaus.
        clear Hfree H3.
        induction l; inv H4; inv H5; inv H7; constructor; auto.
        eapply Pexp_Pexps; eauto. 2:congruence.
        clear - exp_causal_ind H2 H5.
        destruct a. induction l; inv H2; inv H5; constructor; auto.
      - (* case *)
        apply EcaseCase; eauto.
        + eapply exp_causal_ind... rewrite H4; auto.
        + assert (forall x, Exists (fun es => Is_used_inst_list Γ x k (snd es)) l -> P_var x) as Hfree' by auto with lcaus.
          clear Hfree H5.
          induction l; inv H7; inv H8; inv H12; constructor; auto.
          eapply Pexp_Pexps; eauto. 2:congruence.
          clear - exp_causal_ind H1 H8.
          destruct a. induction l; inv H1; inv H8; constructor; auto.
        + destruct o; simpl in *; auto.
          specialize (H9 _ eq_refl). specialize (H10 _ eq_refl). specialize (H13 _ eq_refl).
          eapply Pexp_Pexps; eauto. 3:congruence. 2:intros; eapply Hfree; constructor; eauto.
          clear Hfree H10.
          induction l0; inv H9; inv H13; constructor; auto.
      - (* app *)
        apply EappCase; auto.
        + intros k' Hk'. eapply Pexp_Pexps; eauto.
          * solve_forall' l.
          * intros ? Hfree'. eapply Hfree.
            constructor; eauto.
            eapply Is_used_inst_list_Exists in Hfree' as [? ?]; eauto.
        + intros k' Hk'. eapply Pexp_Pexps; eauto.
          * solve_forall' l0.
          * intros ? Hfree'. eapply Hfree.
            constructor; eauto.
            eapply Is_used_inst_list_Exists in Hfree' as [? ?]; eauto.
            right. solve_Exists. simpl_Forall.
            rewrite <-length_annot_numstreams in H6.
            take (Is_used_inst _ _ _ _) and rename it into Hfree1.
            assert (Hfree2:=Hfree1). eapply Is_used_inst_length in Hfree1; eauto.
            rewrite H6 in Hfree1. destruct x0; auto. lia.
    Qed.

  End exp_causal_ind.

  (** More flexible induction principle *)
  Section node_causal_ind.
    Context {PSyn : list decl -> block -> Prop}.
    Context {prefs : PS.t}.
    Variable n : @node PSyn prefs.

    Variable P_vars : list ident -> Prop.

    Lemma causal_ind {v a} : forall (g : AcyGraph v a),
        graph_of_node n g ->
        P_vars [] ->
        (forall x xs,
            In x (map snd (idcaus (n_in n) ++ idcaus_of_decls (n_out n))) \/ In x (map snd (idcaus_of_locals (n_block n))) ->
            P_vars xs ->
            (forall y, depends_on_node x y n -> In y xs) ->
            P_vars (x::xs)) ->
        exists lord, Permutation lord (PS.elements (vertices g)) /\ P_vars lord.
    Proof.
      intros * [Hv Ha] Hnil Hdep.
      specialize (has_TopoOrder g) as (xs'&Heq&Hpre).
      do 2 esplit. rewrite Heq, Permutation_PS_elements_of_list. reflexivity.
      1:{ eapply TopoOrder_NoDup; eauto. }
      assert (incl xs' (map snd (idcaus (n_in n) ++ idcaus_of_decls (n_out n) ++ (idcaus_of_locals (n_block n))))) as Hincl.
      { rewrite Hv in Heq.
        repeat rewrite <- ps_from_list_ps_of_list in Heq.
        intros ? Hin. rewrite <- ps_from_list_In in *.
        now rewrite Heq. }
      clear Heq.
      induction xs'; auto.
      apply incl_cons' in Hincl as (Hin&Hincl). inversion_clear Hpre as [|?? (?&?&Hin') Hpre'].
      eapply Hdep; eauto.
      - now rewrite app_assoc, map_app, in_app_iff in Hin.
      - intros * Hdep'. eapply Hin'. left.
        eapply Ha; eauto.
    Qed.

    Corollary node_causal_ind :
        node_causal n ->
        P_vars [] ->
        (forall x xs,
            In x (map snd (idcaus (n_in n) ++ idcaus_of_decls (n_out n))) \/ In x (map snd (idcaus_of_locals (n_block n))) ->
            P_vars xs ->
            (forall y, depends_on_node x y n -> In y xs) ->
            P_vars (x::xs)) ->
        exists lord, Permutation lord (map snd (idcaus (n_in n) ++ idcaus_of_decls (n_out n) ++ idcaus_of_locals (n_block n)))
                /\ P_vars lord.
    Proof.
      intros * (Hnd&?&?&g&Hcaus) Hnil Hdep.
      assert (Hvars:=Hcaus). eapply causal_ind in Hvars as (?&Perm&Vars); eauto.
      destruct Hcaus as (Heq&_).
      do 2 esplit; [|eauto].
      rewrite Perm, Heq, Permutation_PS_elements_of_list; auto.
    Qed.
  End node_causal_ind.

End LCAUSALITY.

Module LCausalityFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks   : CLOCKS Ids Op OpAux)
       (Senv  : STATICENV Ids Op OpAux Cks)
       (Syn   : LSYNTAX Ids Op OpAux Cks Senv)
       <: LCAUSALITY Ids Op OpAux Cks Senv Syn.
  Include LCAUSALITY Ids Op OpAux Cks Senv Syn.
End LCausalityFun.
