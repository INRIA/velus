Require Import Rustre.Common.
Require Import PArith.

Import List.ListNotations.
Open Scope list_scope.

(** * Dataflow language *)

Inductive clock : Set :=
| Cbase : clock                          (* base clock *)
| Con : clock -> ident -> bool -> clock. (* subclock *)

Implicit Type ck : clock.

(** ** Syntax *)

Inductive lexp : Type :=
  | Econst : const -> lexp
  | Evar : ident -> lexp
  | Ewhen : lexp -> ident -> bool -> lexp.
(* External operators are missing *)

Inductive laexp : Type :=
  | LAexp : clock -> lexp -> laexp.

Implicit Type le: lexp.
Implicit Type lae: laexp.

Inductive cexp : Type :=
  | Emerge : ident -> cexp -> cexp -> cexp 
  | Eexp : lexp -> cexp.

Inductive caexp : Type :=
  | CAexp : clock -> cexp -> caexp.

Implicit Type ce: cexp.
Implicit Type cae: caexp.

(** ** Equations *)

Inductive equation : Type :=
  | EqDef : ident -> caexp -> equation
  | EqApp : ident -> ident -> laexp -> equation
  | EqFby : ident -> const -> laexp -> equation.

Implicit Type eqn: equation.

(** ** Node *)

Record node : Type := mk_node {
  n_name : ident;
  n_input : ident;
  n_output : ident;
  n_eqs : list equation }.

Implicit Type N: node.

(** ** Program *)

Definition global := list node.

Implicit Type G: global.

Definition find_node (f : ident) : global -> option node :=
  List.find (fun n=> ident_eqb n.(n_name) f).


Fixpoint memory_eq (mems: PS.t) (eq: equation) {struct eq} : PS.t :=
  match eq with
  | EqFby x _ _ => PS.add x mems
  | _ => mems
  end.

Definition memories (eqs: list equation) : PS.t :=
  List.fold_left memory_eq eqs PS.empty.

Lemma In_fold_left_memory_eq:
  forall x eqs m,
    PS.In x (List.fold_left memory_eq eqs m)
    <-> PS.In x (List.fold_left memory_eq eqs PS.empty) \/ PS.In x m.
Proof.
  induction eqs as [|eq].
  - split; auto.
    destruct 1 as [H|].
    apply not_In_empty in H; contradiction.
    auto.
  - split.
    + intro H.
      simpl; rewrite IHeqs.
      simpl in H; apply IHeqs in H; destruct H; auto.
      destruct eq; auto.
      apply PS.add_spec in H.
      destruct H.
      rewrite H; left; right; apply PS.add_spec; intuition.
      intuition.
    + destruct 1 as [H|H].
      * simpl in H; rewrite IHeqs in H; apply IHeqs; destruct H; auto.
        right.
        destruct eq; try (apply not_In_empty in H; contradiction).
        simpl; apply PS.add_spec.
        apply PS.add_spec in H; destruct H;
        try apply not_In_empty in H; intuition.
      * apply IHeqs; right; destruct eq; auto.
        apply PS.add_spec; auto.
Qed.

Fixpoint defined_eq (defs: PS.t) (eq: equation) {struct eq} : PS.t :=
  match eq with
  | EqDef x _   => PS.add x defs
  | EqApp x _ _ => PS.add x defs
  | EqFby x _ _ => PS.add x defs
  end.

Definition defined (eqs: list equation) : PS.t :=
  List.fold_left defined_eq eqs PS.empty.

Inductive Is_defined_in_eq : ident -> equation -> Prop :=
| DefEqDef: forall x e,   Is_defined_in_eq x (EqDef x e)
| DefEqApp: forall x f e, Is_defined_in_eq x (EqApp x f e)
| DefEqFby: forall x v e, Is_defined_in_eq x (EqFby x v e).

Definition Is_defined_in (x: ident) (eqs: list equation) : Prop :=
  List.Exists (Is_defined_in_eq x) eqs.

Inductive no_dup_defs : list equation -> Prop :=
| NoDupDefs_nil : no_dup_defs nil
| NoDupDefs_cons : forall eq eqs,
                     (forall x, Is_defined_in_eq x eq
                                -> ~Is_defined_in x eqs)
                     -> no_dup_defs eqs
                     -> no_dup_defs (eq::eqs).

Lemma Is_defined_in_eq_dec:
  forall x eq, {Is_defined_in_eq x eq}+{~Is_defined_in_eq x eq}.
Proof.
  intros x eq.
  destruct eq as [y cae|y f lae|y v0 lae];
    (destruct (ident_eq_dec x y) as [xeqy|xneqy];
     [ rewrite xeqy; left; constructor
     | right; inversion 1; auto]).
Qed.

Lemma In_fold_left_defined_eq:
  forall x eqs m,
    PS.In x (List.fold_left defined_eq eqs m)
    <-> PS.In x (List.fold_left defined_eq eqs PS.empty) \/ PS.In x m.
Proof.
  induction eqs as [|eq].
  - split; auto.
    destruct 1 as [H|].
    apply not_In_empty in H; contradiction.
    auto.
  - split.
    + intro H.
      simpl; rewrite IHeqs.
      simpl in H; apply IHeqs in H; destruct H; auto.
      destruct eq;
      apply PS.add_spec in H;
      destruct H;
      try (rewrite H; left; right; apply PS.add_spec); intuition.
    + destruct 1 as [H|H].
      * simpl in H; rewrite IHeqs in H; apply IHeqs; destruct H; auto.
        right.
        destruct eq;
        simpl; apply PS.add_spec;
        apply PS.add_spec in H; destruct H;
        intuition;
        apply not_In_empty in H; contradiction.
      * apply IHeqs; right; destruct eq;
        apply PS.add_spec; auto.
Qed.

Lemma Is_defined_in_defined:
  forall x eqs,
    PS.In x (defined eqs)
    <-> Is_defined_in x eqs.
Proof.
  unfold defined, Is_defined_in.
  induction eqs as [ | eq ].
  - rewrite List.Exists_nil; split; intro H;
    try apply not_In_empty in H; contradiction.
  - simpl.
    rewrite In_fold_left_defined_eq.
    split.
    + rewrite List.Exists_cons.
      destruct 1. intuition.
      destruct eq;
      (simpl in H; apply PS.add_spec in H; destruct H;
       [ rewrite H; left; constructor
       | apply not_In_empty in H; contradiction]).
    + intro H; apply List.Exists_cons in H; destruct H.
      inversion H; destruct eq; (right; apply PS.add_spec; intuition).
      left; apply IHeqs; apply H.
Qed.

Lemma Is_defined_in_dec:
  forall x eqs, {Is_defined_in x eqs}+{~Is_defined_in x eqs}.
Proof.
  intros x eqs.
  apply Bool.reflect_dec with (b := PS.mem x (defined eqs)).
  apply Bool.iff_reflect.
  rewrite PS.mem_spec.
  symmetry.
  apply Is_defined_in_defined.
Qed.

Lemma In_memory_eq_In_defined_eq:
  forall x eq S,
    PS.In x (memory_eq S eq)
    -> PS.In x (defined_eq S eq).
Proof.
  intros x eq S HH.
  destruct eq; try (apply PS.add_spec; now intuition).
  apply PS.add_spec in HH.
  destruct HH as [HH|HH].
  - rewrite HH; apply PS.add_spec; left; reflexivity.
  - apply PS.add_spec; right; exact HH.
Qed.

Lemma In_fold_left_memory_eq_defined_eq:
  forall x eqs S,
    PS.In x (List.fold_left memory_eq eqs S)
    -> PS.In x (List.fold_left defined_eq eqs S).
Proof.
  intros x eqs.
  induction eqs as [|eq eqs IH]; [now intuition|].
  intros S HH.
  apply IH in HH; clear IH.
  apply In_fold_left_defined_eq in HH.
  simpl. apply In_fold_left_defined_eq.
  destruct HH as [HH|HH].
  - left; exact HH.
  - right; now apply In_memory_eq_In_defined_eq with (1:=HH).
Qed.

Lemma Is_defined_in_cons:
  forall x eq eqs,
    Is_defined_in x (eq :: eqs) ->
    Is_defined_in_eq x eq
    \/ (~Is_defined_in_eq x eq /\ Is_defined_in x eqs).
Proof.
  intros x eq eqs Hdef.
  apply List.Exists_cons in Hdef.
  destruct (Is_defined_in_eq_dec x eq); intuition.
Qed.

Lemma not_Is_defined_in_cons:
  forall x eq eqs,
    ~Is_defined_in x (eq :: eqs)
    <-> ~Is_defined_in_eq x eq /\ ~Is_defined_in x eqs.
Proof.
  intros x eq eqs. split.
  intro H0; unfold Is_defined_in in H0; auto.
  destruct 1 as [H0 H1]; intro H; apply Is_defined_in_cons in H; intuition.
Qed.

Lemma not_Is_defined_in_eq_EqDef:
  forall x i cae,
    ~ Is_defined_in_eq x (EqDef i cae) -> x <> i.
Proof.
  intros x i cae H0 xeqi.
  rewrite xeqi in H0.
  assert (Is_defined_in_eq i (EqDef i cae)) by constructor.
  contradiction.
Qed.

Lemma not_Is_defined_in_eq_EqApp:
  forall x i f lae,
    ~ Is_defined_in_eq x (EqApp i f lae) -> x <> i.
Proof.
  intros x i f lae H0 xeqi.
  rewrite xeqi in H0.
  assert (Is_defined_in_eq i (EqApp i f lae)) by constructor.
  contradiction.
Qed.

Lemma not_Is_defined_in_eq_EqFby:
  forall x i v0 lae,
    ~ Is_defined_in_eq x (EqFby i v0 lae) -> x <> i.
Proof.
  intros x i v0 lae H0 xeqi.
  rewrite xeqi in H0.
  assert (Is_defined_in_eq i (EqFby i v0 lae)) by constructor.
  contradiction.
Qed.


Fixpoint variable_eq (vars: PS.t) (eq: equation) {struct eq} : PS.t :=
  match eq with
  | EqDef x _   => PS.add x vars
  | EqApp x _ _ => PS.add x vars
  | EqFby _ _ _ => vars
  end.

Definition variables (eqs: list equation) : PS.t :=
  List.fold_left variable_eq eqs PS.empty.

Inductive Is_variable_in_eq : ident -> equation -> Prop :=
| VarEqDef: forall x e,   Is_variable_in_eq x (EqDef x e)
| VarEqApp: forall x f e, Is_variable_in_eq x (EqApp x f e).

Definition Is_variable_in (x: ident) (eqs: list equation) : Prop :=
  List.Exists (Is_variable_in_eq x) eqs.

Lemma Is_variable_in_eq_dec:
  forall x eq, {Is_variable_in_eq x eq}+{~Is_variable_in_eq x eq}.
Proof.
  intros x eq.
  destruct eq as [y cae|y f lae|y v0 lae];
    match goal with
    | |- context Is_variable_in_eq [EqFby _ _ _] => right; inversion 1
    | _ => (destruct (ident_eq_dec x y) as [xeqy|xneqy];
            [ rewrite xeqy; left; constructor
            | right; inversion 1; auto])
    end.
Qed.

Lemma Is_variable_in_Is_defined_in:
  forall x eqs,
    Is_variable_in x eqs
    -> Is_defined_in x eqs.
Proof.
  induction eqs as [|eq eqs IH]; [now inversion 1|].
  inversion_clear 1 as [Hin ? Hivi|]; [|constructor 2; intuition].
  destruct eq; inversion_clear Hivi; repeat constructor.
Qed.

Lemma Is_variable_in_cons:
  forall x eq eqs,
    Is_variable_in x (eq :: eqs) ->
    Is_variable_in_eq x eq
    \/ (~Is_variable_in_eq x eq /\ Is_variable_in x eqs).
Proof.
  intros x eq eqs Hdef.
  apply List.Exists_cons in Hdef.
  destruct (Is_variable_in_eq_dec x eq); intuition.
Qed.

Lemma not_Is_variable_in_cons:
  forall x eq eqs,
    ~Is_variable_in x (eq :: eqs)
    <-> ~Is_variable_in_eq x eq /\ ~Is_variable_in x eqs.
Proof.
  intros x eq eqs. split.
  intro H0; unfold Is_variable_in in H0; auto.
  destruct 1 as [H0 H1]; intro H; apply Is_variable_in_cons in H; intuition.
Qed.

Lemma In_fold_left_variable_eq:
  forall x eqs m,
    PS.In x (List.fold_left variable_eq eqs m)
    <-> PS.In x (List.fold_left variable_eq eqs PS.empty) \/ PS.In x m.
Proof. (* TODO: There must be a way to get auto to do all of this? *)
  induction eqs as [|eq].
  - split; auto.
    destruct 1 as [H|].
    apply not_In_empty in H; contradiction.
    auto.
  - split; [ intro H; simpl; rewrite IHeqs
           | destruct 1 as [H|H]; apply IHeqs];
    solve [
        simpl in H; apply IHeqs in H; destruct H;
        [ intuition
        | destruct eq; try (apply PS.add_spec in H; destruct H);
          match goal with
          | H:x=_ |- _ => rewrite H; simpl; rewrite PS.add_spec; intuition
          | _ => apply not_In_empty in H; contradiction
          | _ => intuition
          end ]
      | right; destruct eq; try apply PS.add_spec; intuition
      ].
Qed.

Lemma Is_variable_in_variables:
  forall x eqs,
    PS.In x (variables eqs)
    <-> Is_variable_in x eqs.
Proof.
  unfold variables, Is_variable_in.
  induction eqs as [ eq | eq ].
  - rewrite List.Exists_nil; split; intro H;
    try apply not_In_empty in H; contradiction.
  - simpl.
    rewrite In_fold_left_variable_eq.
    split.
    + rewrite List.Exists_cons.
      destruct 1. intuition.
      destruct eq; try (apply not_In_empty in H; intuition);
      (simpl in H; apply PS.add_spec in H; destruct H;
       [ rewrite H; left; constructor
       | apply not_In_empty in H; contradiction ]).
    + intro H; apply List.Exists_cons in H; destruct H.
      destruct eq; try inversion H;
      (right; apply PS.add_spec; intuition).
      left; apply IHeqs; apply H.
Qed.

Lemma Is_variable_in_dec:
  forall x eqs, {Is_variable_in x eqs}+{~Is_variable_in x eqs}.
Proof.
  intros x eqs.
  apply Bool.reflect_dec with (b := PS.mem x (variables eqs)).
  apply Bool.iff_reflect.
  rewrite PS.mem_spec.
  symmetry.
  apply Is_variable_in_variables.
Qed.

Lemma not_Is_defined_in_eq_not_Is_variable_in_eq:
  forall x eq, ~Is_defined_in_eq x eq -> ~Is_variable_in_eq x eq.
Proof.
  Hint Constructors Is_defined_in_eq.
  intros x eq Hnidi.
  destruct eq; inversion 1; subst; intuition.
Qed.

Lemma not_Is_defined_in_not_Is_variable_in:
  forall x eqs, ~Is_defined_in x eqs -> ~Is_variable_in x eqs.
Proof.
  Hint Constructors Is_defined_in_eq.
  induction eqs as [|eq].
  - intro H; contradict H; inversion H.
  - intro H; apply not_Is_defined_in_cons in H; destruct H as [H0 H1].
    apply IHeqs in H1; apply not_Is_variable_in_cons.
    split; [ now apply not_Is_defined_in_eq_not_Is_variable_in_eq
           | now apply H1].
Qed.

Lemma Is_defined_in_memories:
  forall x eqs,
    PS.In x (memories eqs) -> Is_defined_in x eqs.
Proof.
  unfold memories, Is_defined_in.
  induction eqs as [ eq | eq ].
  - simpl; intro; not_In_empty.
  - intro HH; simpl in HH.
    apply In_fold_left_memory_eq in HH.
    rewrite List.Exists_cons.
    destruct HH as [HH|HH].
    + right; now apply IHeqs with (1:=HH).
    + left. apply In_memory_eq_In_defined_eq in HH.
      destruct eq; apply PS.add_spec in HH; destruct HH as [HH|HH];
      (rewrite HH; now constructor) || not_In_empty.
Qed.

Inductive NoDup_defs : list equation -> Prop :=
| NDDNil: NoDup_defs nil
| NDDEqDef:
    forall x e eqs,
      NoDup_defs eqs ->
      ~Is_defined_in x eqs ->
      NoDup_defs (EqDef x e :: eqs)
| NDDEqApp:
    forall x f e eqs,
      NoDup_defs eqs ->
      ~Is_defined_in x eqs ->
      NoDup_defs (EqApp x f e :: eqs)
| NDDEqFby:
    forall x v e eqs,
      NoDup_defs eqs ->
      ~Is_defined_in x eqs ->
      NoDup_defs (EqFby x v e :: eqs).

Lemma NoDup_defs_cons:
  forall eq eqs,
    NoDup_defs (eq :: eqs) -> NoDup_defs eqs.
Proof.
  intros eq eqs Hndd.
  destruct eq; inversion_clear Hndd; assumption.
Qed.

Lemma not_Is_variable_in_memories:
  forall x eqs,
    PS.In x (memories eqs)
    -> NoDup_defs eqs
    -> ~Is_variable_in x eqs.
Proof.
  (* TODO: Too complicated! Find a simpler proof. *)
  intros x eqs Hinm Hndd.
  pose proof (Is_defined_in_memories _ _ Hinm) as Hdin.
  unfold memories, Is_variable_in in *.
  induction eqs as [eq|eq eqs IH].
  - simpl in *; intro; not_In_empty.
  - apply Is_defined_in_cons in Hdin.
    inversion Hndd
      as [|y e ? Hndds Hndi|y f e ? Hndds Hndi|y v0 e ? Hndds Hndi];
      subst; clear Hndd.
    + destruct Hdin as [Hdin|[Hndin Hdins]].
      simpl in Hinm.
      intro He; apply List.Exists_cons in He; destruct He as [He|He].
      apply Is_defined_in_memories in Hinm.
      inversion He; subst; clear He.
      contradiction.

      inversion Hdin; subst; clear Hdin.
      apply Is_variable_in_Is_defined_in in He.
      contradiction.

      simpl in Hinm.
      apply IH with (2:=Hndds) (3:=Hdins) in Hinm.
      intro He; apply List.Exists_cons in He; destruct He as [He|He].
      inversion He; subst; clear He.
      apply Hndin; now constructor.
      contradiction.
    + destruct Hdin as [Hdin|[Hndin Hdins]].
      simpl in Hinm.
      intro He; apply List.Exists_cons in He; destruct He as [He|He].
      apply Is_defined_in_memories in Hinm.
      inversion He; subst; clear He.
      contradiction.

      inversion Hdin; subst; clear Hdin.
      apply Is_variable_in_Is_defined_in in He.
      contradiction.

      simpl in Hinm.
      apply IH with (2:=Hndds) (3:=Hdins) in Hinm.
      intro He; apply List.Exists_cons in He; destruct He as [He|He].
      inversion He; subst; clear He.
      apply Hndin; now constructor.
      contradiction.
    + destruct Hdin as [Hdin|[Hndin Hdins]].
      simpl in Hinm.
      intro He; apply List.Exists_cons in He; destruct He as [He|He].
      inversion He; subst; clear He.
      inversion Hdin; subst; clear Hdin.

      apply Is_variable_in_Is_defined_in in He.
      contradiction.

      simpl in Hinm.
      apply In_fold_left_memory_eq in Hinm.
      destruct Hinm as [Hinm|Hinm].
      apply IH with (2:=Hndds) (3:=Hdins) in Hinm.
      intro He; apply List.Exists_cons in He; destruct He as [He|He].

      inversion He; subst; clear He.
      contradiction.

      apply PS.add_spec in Hinm.
      destruct Hinm as [Hinm|Hinm]; [|now not_In_empty].
      rewrite Hinm in *.
      exfalso; apply Hndin; now constructor.
Qed.

Inductive Is_node_in_eq : ident -> equation -> Prop :=
| INI: forall x f e, Is_node_in_eq f (EqApp x f e).

Definition Is_node_in (f: ident) (eqs: list equation) : Prop :=
  List.Exists (Is_node_in_eq f) eqs.

Inductive Ordered_nodes : global -> Prop :=
| ONnil: Ordered_nodes nil
| ONcons:
    forall nd nds,
      Ordered_nodes nds
      -> (forall f, Is_node_in f nd.(n_eqs) ->
                    f <> nd.(n_name)
                    /\ List.Exists (fun n=> f = n.(n_name)) nds)
      -> List.Forall (fun nd'=> nd.(n_name) <> nd'.(n_name)) nds
      -> Ordered_nodes (nd::nds).

Lemma not_Is_node_in_cons:
  forall n eq eqs,
    ~ Is_node_in n (eq::eqs) <-> ~Is_node_in_eq n eq /\ ~Is_node_in n eqs.
Proof.
  intros n eq eqs.
  split; intro HH.
  - split; intro; apply HH; unfold Is_node_in; intuition.
  - destruct HH; inversion_clear 1; intuition.
Qed.

Lemma Is_node_in_Forall:
  forall n eqs,
    ~Is_node_in n eqs <-> List.Forall (fun eq=>~Is_node_in_eq n eq) eqs.
Proof.
  induction eqs as [|eq eqs IH];
    [split; [now constructor|now inversion 2]|].
  split; intro HH.
  - apply not_Is_node_in_cons in HH.
    destruct HH as [Heq Heqs].
    constructor; [exact Heq|apply IH with (1:=Heqs)].
  - apply not_Is_node_in_cons.
    inversion_clear HH as [|? ? Heq Heqs].
    apply IH in Heqs.
    intuition.
Qed.

Lemma Ordered_nodes_append:
  forall G G',
    Ordered_nodes (G ++ G')
    -> Ordered_nodes G'.
Proof.
  induction G as [|nd G IH]; [intuition|].
  intros G' HnGG.
  apply IH; inversion_clear HnGG; assumption.
Qed.

Lemma find_node_Exists:
  forall f G, find_node f G <> None <-> List.Exists (fun n=> f = n.(n_name)) G.
Proof.
  induction G as [|node G IH].
  - split; intro Hfn.
    exfalso; apply Hfn; reflexivity.
    apply List.Exists_nil in Hfn; contradiction.
  - destruct (ident_eq_dec node.(n_name) f) as [He|Hne]; simpl.
    + assert (He' := He); apply BinPos.Pos.eqb_eq in He'.
      unfold ident_eqb; rewrite He'.
      split; intro HH; [clear HH|discriminate 1].
      constructor.
      symmetry; exact He.
    + assert (Hne' := Hne); apply BinPos.Pos.eqb_neq in Hne'.
      unfold ident_eqb; rewrite Hne'.
      split; intro HH; [ apply IH in HH; constructor 2; exact HH |].
      apply List.Exists_cons in HH.
      destruct HH as [HH|HH]; [symmetry in HH; contradiction|].
      apply IH; exact HH.
Qed.

Lemma find_node_tl:
  forall f node G,
    node.(n_name) <> f
    -> find_node f (node::G) = find_node f G.
Proof.
  intros f node G Hnf.
  unfold find_node.
  unfold List.find at 1.
  apply Pos.eqb_neq in Hnf.
  unfold ident_eqb.
  rewrite Hnf.
  reflexivity.
Qed.

Lemma find_node_split:
  forall f G node,
    find_node f G = Some node
    -> exists bG aG,
      G = bG ++ node :: aG.
Proof.
  induction G as [|nd G IH]; [unfold find_node, List.find; discriminate|].
  intro nd'.
  intro Hfind.
  unfold find_node in Hfind; simpl in Hfind.
  destruct (ident_eqb (n_name nd) f) eqn:Heq.
  - injection Hfind; intro He; rewrite <-He in *; clear Hfind He.
    exists []; exists G; reflexivity.
  - apply IH in Hfind.
    destruct Hfind as [bG [aG Hfind]].
    exists (nd::bG); exists aG; rewrite Hfind; reflexivity.
Qed.

Lemma Ordered_nodes_cons_find_node_None:
  forall node G,
    Ordered_nodes (node::G)
    -> find_node node.(n_name) G = None.
Proof.
  intros node G Hord.
  inversion_clear Hord as [|? ? Hord' H0 Hfa]; clear H0.
  induction G as [|eq G IH]; [trivial|].
  simpl.
  destruct (ident_eqb eq.(n_name) node.(n_name)) eqn:Heq;
    apply Forall_cons2 in Hfa;
    destruct Hfa as [Hneq H0].
  - apply Peqb_true_eq in Heq.
    rewrite Heq in Hneq.
    exfalso; apply Hneq; reflexivity.
  - apply IH; inversion_clear Hord'; assumption.
Qed.

Lemma find_node_later_names_not_eq:
  forall f nd G nd',
    Ordered_nodes (nd::G)
    -> find_node f (G) = Some nd'
    -> f <> nd.(n_name).
Proof.
  intros f nd G nd' Hord Hfind.
  pose proof (Ordered_nodes_cons_find_node_None _ _ Hord) as Hnone.
  intro Heq.
  rewrite Heq, Hnone in Hfind.
  discriminate.
Qed.

Lemma find_node_later_not_Is_node_in:
  forall f nd G nd',
    Ordered_nodes (nd::G)
    -> find_node f G = Some nd'
    -> ~Is_node_in nd.(n_name) nd'.(n_eqs).
Proof.
  intros f nd G nd' Hord Hfind Hini.
  apply find_node_split in Hfind.
  destruct Hfind as [bG [aG HG]].
  rewrite HG in Hord.
  inversion_clear Hord as [|? ? Hord' H0 Hnin]; clear H0.
  apply Ordered_nodes_append in Hord'.
  inversion_clear Hord' as [| ? ? Hord Heqs Hnin'].
  apply Heqs in Hini.
  destruct Hini as [H0 HH]; clear H0.
  rewrite Forall_app in Hnin.
  destruct Hnin as [H0 Hnin]; clear H0.
  inversion_clear Hnin as [|? ? H0 HH']; clear H0.
  apply List.Exists_exists in HH.
  destruct HH as [node [HaG Heq]].
  rewrite List.Forall_forall in HH'.
  apply HH' in HaG.
  contradiction.
Qed.

Lemma find_node_not_Is_node_in:
  forall f nd G,
    Ordered_nodes G
    -> find_node f G = Some nd
    -> ~Is_node_in nd.(n_name) nd.(n_eqs).
Proof.
  intros f nd G Hord Hfind.
  apply find_node_split in Hfind.
  destruct Hfind as [bG [aG HG]].
  rewrite HG in Hord.
  apply Ordered_nodes_append in Hord.
  inversion_clear Hord as [|? ? Hord' Heqs Hnin].
  intro Hini.
  apply Heqs in Hini.
  destruct Hini as [HH H0]; clear H0.
  apply HH; reflexivity.
Qed.

Lemma find_node_name:
  forall f G fnode,
    find_node f G = Some fnode -> fnode.(n_name) = f.
Proof.
  induction G as [|node G IH]; [now inversion 1|].
  destruct node as [name input output eqs].
  destruct (ident_eqb name f) eqn:Hfn;
    assert (Hfn':=Hfn);
    [apply Pos.eqb_eq in Hfn'; rewrite Hfn' in *|apply Pos.eqb_neq in Hfn'];
    simpl; rewrite Hfn.
  - injection 1; intro Heq; rewrite <-Heq; reflexivity.
  - intros fnode Hfnode.
    apply IH with (1:=Hfnode).
Qed.

