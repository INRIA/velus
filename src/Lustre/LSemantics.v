From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Coq Require Import Streams.
From Coq Require Import Sorting.Permutation.
From Coq Require Import Setoid.
From Coq Require Import Morphisms.

From Coq Require Import FSets.FMapPositive.
From Velus Require Import Common.
From Velus Require Import CommonProgram.
From Velus Require Import CommonList.
From Velus Require Import FunctionalEnvironment.
From Velus Require Import Operators.
From Velus Require Import Clocks.
From Velus Require Import Lustre.StaticEnv.
From Velus Require Import Lustre.LSyntax.
From Velus Require Import Lustre.LOrdered.
From Velus Require Import CoindStreams.

(** * Lustre semantics *)

Module Type LSEMANTICS
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks   : CLOCKS        Ids Op OpAux)
       (Import Senv  : STATICENV     Ids Op OpAux Cks)
       (Import Syn   : LSYNTAX       Ids Op OpAux Cks Senv)
       (Import Lord  : LORDERED      Ids Op OpAux Cks Senv Syn)
       (Import Str   : COINDSTREAMS  Ids Op OpAux Cks).

  CoInductive fby1 {A : Type} : A -> Stream (synchronous A) -> Stream (synchronous A) -> Stream (synchronous A) -> Prop :=
  | Fby1A:
      forall v xs ys rs,
        fby1 v xs ys rs ->
        fby1 v (absent ⋅ xs) (absent ⋅ ys) (absent ⋅ rs)
  | Fby1P:
      forall v w s xs ys rs,
        fby1 s xs ys rs ->
        fby1 v (present w ⋅ xs) (present s ⋅ ys) (present v ⋅ rs).

  CoInductive fby {A : Type} : Stream (synchronous A) -> Stream (synchronous A) -> Stream (synchronous A) -> Prop :=
  | FbyA:
      forall xs ys rs,
        fby xs ys rs ->
        fby (absent ⋅ xs) (absent ⋅ ys) (absent ⋅ rs)
  | FbyP:
      forall x y xs ys rs,
        fby1 y xs ys rs ->
        fby (present x ⋅ xs) (present y ⋅ ys) (present x ⋅ rs).

  CoInductive arrow1: Stream svalue -> Stream svalue -> Stream svalue -> Prop :=
  | Arrow1A: forall xs ys rs,
      arrow1 xs ys rs ->
      arrow1 (absent ⋅ xs) (absent ⋅ ys) (absent ⋅ rs)
  | Arrow1P: forall x y xs ys rs,
      arrow1 xs ys rs ->
      arrow1 (present x ⋅ xs) (present y ⋅ ys) (present y ⋅ rs).

  CoInductive arrow: Stream svalue -> Stream svalue -> Stream svalue -> Prop :=
  | ArrowA: forall xs ys rs,
      arrow xs ys rs ->
      arrow (absent ⋅ xs) (absent ⋅ ys) (absent ⋅ rs)
  | ArrowP: forall x y xs ys rs,
      arrow1 xs ys rs ->
      arrow (present x ⋅ xs) (present y ⋅ ys) (present x ⋅ rs).

  Inductive lustre_var := Var (x : ident) | Last (x : ident).

  Global Program Instance var_eq_dec : EqDec lustre_var eq.
  Next Obligation.
    destruct x, y.
    2,3:right; intros Eq; inv Eq.
    1,2:(destruct (ident_eq_dec x x0); subst;
         [left;reflexivity|right; intros Eq; inv Eq; congruence]).
  Qed.

  Global Program Instance var_fenv_key : FEnv.fenv_key lustre_var.

  Definition history : Type := @history lustre_var.
  Definition var_history (H : history) : @Str.history ident :=
    fun x => H (Var x).

  Section NodeSemantics.
    Context {PSyn : block -> Prop}.
    Context {prefs : PS.t}.
    Variable G : @global PSyn prefs.

    (** Inductive property on the branches of a merge / case *)
    Section Forall2Brs.
      Variable P : exp -> list (Stream svalue) -> Prop.

      Inductive Forall2Brs : list (enumtag * list exp) -> list (list (enumtag * Stream svalue)) -> Prop :=
      | F2Tnil : forall vs,
          Forall (fun vs => vs = []) vs ->
          Forall2Brs [] vs
      | F2Tcons : forall c es brs vs1 vs2 vs3,
          Forall2 P es vs1 ->
          Forall2Brs brs vs2 ->
          Forall3 (fun v1 vs2 vs3 => vs3 = (c, v1)::vs2) (concat vs1) vs2 vs3 ->
          Forall2Brs ((c, es)::brs) vs3.

    End Forall2Brs.

    (* Definition mask_hist k rs H := (mask_hist k rs (fst H), mask_hist k rs (snd H)). *)
    (* Definition when_hist e Hi cs Hi' := *)
    (*   when_hist e (fst Hi) cs (fst Hi') *)
    (*   /\ when_hist e (snd Hi) cs (snd Hi'). *)
    (* Definition select_hist e k stres Hi Hi' := *)
    (*   select_hist e k stres (fst Hi) (fst Hi') *)
    (*   /\ select_hist e k stres (snd Hi) (snd Hi'). *)

    Definition dom (H : history) Γ :=
      (forall x, FEnv.In (Var x) H <-> IsVar Γ x) /\ (forall x, FEnv.In (Last x) H <-> IsLast Γ x).

    Definition dom_ub (H : history) Γ :=
      (forall x, FEnv.In (Var x) H -> IsVar Γ x) /\ (forall x, FEnv.In (Last x) H -> IsLast Γ x).

    Definition dom_lb (H : history) Γ :=
      (forall x, IsVar Γ x -> FEnv.In (Var x) H) /\ (forall x, IsLast Γ x -> FEnv.In (Last x) H).

    Section sem_scope.
      Context {A : Type}.

      Variable sem_exp : history -> exp -> list (Stream svalue) -> Prop.
      Variable sem_block : history -> A -> Prop.

      Inductive sem_scope : history -> Stream bool -> (scope A) -> Prop :=
      | Sscope : forall Hi Hi' bs locs blks,
          (* Domain of the internal history *)
          dom Hi' (senv_of_locs locs) ->

          (* Last declarations *)
          (forall x ty ck cx e0 clx,
              In (x, (ty, ck, cx, Some (e0, clx))) locs ->
              exists vs0 vs1 vs,
                sem_exp (Hi + Hi') e0 [vs0]
                /\ sem_var Hi' (Var x) vs1
                /\ fby vs0 vs1 vs
                /\ sem_var Hi' (Last x) vs) ->

          sem_block (Hi + Hi') blks ->
          sem_scope Hi bs (Scope locs blks).
    End sem_scope.

    Section sem_branch.
      Context {A : Type}.

      Variable sem_block : A -> Prop.

      Inductive sem_branch : (branch A) -> Prop :=
      | Sbranch : forall caus blks,
          sem_block blks ->
          sem_branch (Branch caus blks).
    End sem_branch.

    Inductive sem_exp
      : history -> Stream bool -> exp -> list (Stream svalue) -> Prop :=
    | Sconst:
      forall H b c cs,
        cs ≡ const b c ->
        sem_exp H b (Econst c) [cs]

    | Senum:
      forall H b k ty es,
        es ≡ enum b k ->
        sem_exp H b (Eenum k ty) [es]

    | Svar:
      forall H b x s ann,
        sem_var H (Var x) s ->
        sem_exp H b (Evar x ann) [s]

    | Slast:
      forall H b x s ann,
        sem_var H (Last x) s ->
        sem_exp H b (Elast x ann) [s]

    | Sunop:
      forall H b e op ty s o ann,
        sem_exp H b e [s] ->
        typeof e = [ty] ->
        lift1 op ty s o ->
        sem_exp H b (Eunop op e ann) [o]

    | Sbinop:
      forall H b e1 e2 op ty1 ty2 s1 s2 o ann,
        sem_exp H b e1 [s1] ->
        sem_exp H b e2 [s2] ->
        typeof e1 = [ty1] ->
        typeof e2 = [ty2] ->
        lift2 op ty1 ty2 s1 s2 o ->
        sem_exp H b (Ebinop op e1 e2 ann) [o]

    | Sextcall:
      forall H b f es tyout ck tyins ss vs,
        Forall2 (fun ty cty => ty = Tprimitive cty) (typesof es) tyins ->
        Forall2 (sem_exp H b) es ss ->
        liftn (fun ss => sem_extern f tyins ss tyout) (concat ss) vs ->
        sem_exp H b (Eextcall f es (tyout, ck)) [vs]

    | Sfby:
      forall H b e0s es anns s0ss sss os,
        Forall2 (sem_exp H b) e0s s0ss ->
        Forall2 (sem_exp H b) es sss ->
        Forall3 fby (concat s0ss) (concat sss) os ->
        sem_exp H b (Efby e0s es anns) os

    | Sarrow:
      forall H b e0s es anns s0ss sss os,
        Forall2 (sem_exp H b) e0s s0ss ->
        Forall2 (sem_exp H b) es sss ->
        Forall3 arrow (concat s0ss) (concat sss) os ->
        sem_exp H b (Earrow e0s es anns) os

    | Swhen:
      forall H b x tx s k es lann ss os,
        Forall2 (sem_exp H b) es ss ->
        sem_var H (Var x) s ->
        Forall2 (fun s' => when k s' s) (concat ss) os ->
        sem_exp H b (Ewhen es (x, tx) k lann) os

    | Smerge:
      forall H b x tx s es lann vs os,
        sem_var H (Var x) s ->
        Forall2Brs (sem_exp H b) es vs ->
        Forall2 (merge s) vs os ->
        sem_exp H b (Emerge (x, tx) es lann) os

    | ScaseTotal:
      forall H b e s es tys ck vs os,
        sem_exp H b e [s] ->
        Forall2Brs (sem_exp H b) es vs ->
        Forall3 (case s) vs (List.map (fun _ => None) tys) os ->
        sem_exp H b (Ecase e es None (tys, ck)) os

    (** In the default case, we need to ensure that the values taken by the condition stream
        still corresponds to the constructors;
        otherwise, we could not prove that the NLustre program has a semantics.
        For instance, consider the program

        type t = A | B | C

        case e of
        | A -> 1
        | B -> 2
        | _ -> 42

        its normalized form (in NLustre) is

        case e of [Some 1;Some 2;None] 42

        If the condition `e` takes the value `3`, then the first program has a semantics
        (we take the default branch) but not the NLustre program (see NLCoindSemantics.v).

        We could prove that the stream produced by `e` being well-typed is a
        property of any well-typed, causal program, but the proof would be as
        hard as the alignment proof (see LClockSemantics.v).
        Instead we take this as an hypothesis, that will have to be filled when
        proving the existence of the semantics. This would be necessary to establish
        the semantics of operators anyway, so this shouldn't add any cost.
     *)
    | ScaseDefault:
      forall H b e s es d lann vs vd os,
        sem_exp H b e [s] ->
        wt_streams [s] (typeof e) ->
        Forall2Brs (sem_exp H b) es vs ->
        Forall2 (sem_exp H b) d vd ->
        Forall3 (case s) vs (List.map Some (concat vd)) os ->
        sem_exp H b (Ecase e es (Some d) lann) os

    | Sapp:
      forall H b f es er lann ss os rs bs,
        Forall2 (sem_exp H b) es ss ->
        Forall2 (fun e r => sem_exp H b e [r]) er rs ->
        bools_ofs rs bs ->
        (forall k, sem_node f (List.map (maskv k bs) (concat ss)) (List.map (maskv k bs) os)) ->
        sem_exp H b (Eapp f es er lann) os

    with sem_equation: history -> Stream bool -> equation -> Prop :=
      Seq:
        forall H b xs es ss,
          Forall2 (sem_exp H b) es ss ->
          Forall2 (fun x => sem_var H (Var x)) xs (concat ss) ->
          sem_equation H b (xs, es)

    with sem_transitions: history -> Stream bool -> list (exp * (enumtag * bool)) -> (enumtag * bool) -> Stream (synchronous (enumtag * bool)) -> Prop :=
    | Stransdef : forall H bs default stres,
        stres ≡ const_stres bs default ->
        sem_transitions H bs [] default stres
    | Strans : forall H bs e C r trans default vs bs' stres1 stres,
        sem_exp H bs e [vs] ->
        bools_of vs bs' ->
          sem_transitions H bs trans default stres1 ->
          stres ≡ choose_first (const_stres bs' (C, r)) stres1 ->
          sem_transitions H bs ((e, (C, r))::trans) default stres

    with sem_block: history -> Stream bool -> block -> Prop :=
    | Sbeq:
      forall H b eq,
        sem_equation H b eq ->
        sem_block H b (Beq eq)

    | Sreset:
      forall H b blocks er sr r,
        sem_exp H b er [sr] ->
        bools_of sr r ->
        (forall k, Forall (sem_block (mask_hist k r H) (maskb k r b)) blocks) ->
        sem_block H b (Breset blocks er)

    | Sswitch:
      forall Hi b ec branches sc,
        sem_exp Hi b ec [sc] ->
        wt_streams [sc] (typeof ec) ->
        Forall (fun blks =>
                  exists Hi', when_hist (fst blks) Hi sc Hi'
                         /\ let bi := fwhenb (fst blks) b sc in
                           sem_branch (Forall (sem_block Hi' bi)) (snd blks)) branches ->
        sem_block Hi b (Bswitch ec branches)

    | SautoWeak:
      forall H bs ini oth states ck bs' stres0 stres1 stres,
        sem_clock (var_history H) bs ck bs' ->
        sem_transitions H bs' (List.map (fun '(e, t) => (e, (t, false))) ini) (oth, false) stres0 ->
        fby stres0 stres1 stres ->
        Forall (fun state =>
                  let tag := fst (fst state) in
                  forall k, exists Hik, select_hist tag k stres H Hik
                              /\ let bik := fselectb tag k stres bs in
                                sem_branch
                                  (fun blks =>
                                     sem_scope (fun Hi' => sem_exp Hi' bik)
                                       (fun Hi' blks =>
                                          Forall (sem_block Hi' bik) (fst blks)
                                          /\ sem_transitions Hi' bik (snd blks) (tag, false) (fselect absent tag k stres stres1)
                                       ) Hik bik (snd blks)) (snd state)
               ) states ->
        sem_block H bs (Bauto Weak ck (ini, oth) states)

    | SautoStrong:
      forall H bs ini states ck bs' stres stres1,
        sem_clock (var_history H) bs ck bs' ->
        fby (const_stres bs' (ini, false)) stres1 stres ->
        Forall (fun state =>
                  let tag := fst (fst state) in
                  forall k, exists Hik, select_hist tag k stres H Hik
                              /\ let bik := fselectb tag k stres bs in
                                sem_branch
                                  (fun blks =>
                                     sem_transitions Hik bik (fst blks) (tag, false) (fselect absent tag k stres stres1)
                                  ) (snd state)
               ) states ->
        Forall (fun state =>
                  let tag := fst (fst state) in
                  forall k, exists Hik, select_hist tag k stres1 H Hik
                              /\ let bik := fselectb tag k stres1 bs in
                                sem_branch
                                  (fun blks =>
                                     sem_scope (fun Hi' => sem_exp Hi' bik)
                                       (fun Hi' blks => Forall (sem_block Hi' bik) (fst blks))
                                       Hik bik (snd blks)) (snd state)
               ) states ->
        sem_block H bs (Bauto Strong ck ([], ini) states)

    | Slocal:
      forall Hi bs scope,
        sem_scope (fun Hi' => sem_exp Hi' bs) (fun Hi' => Forall (sem_block Hi' bs)) Hi bs scope ->
        sem_block Hi bs (Blocal scope)

    with sem_node: ident -> list (Stream svalue) -> list (Stream svalue) -> Prop :=
    | Snode:
      forall f ss os n H b,
          find_node f G = Some n ->
          Forall2 (fun x => sem_var H (Var x)) (idents n.(n_in)) ss ->
          Forall2 (fun x => sem_var H (Var x)) (idents n.(n_out)) os ->
          sem_block H b n.(n_block) ->
          b = clocks_of ss ->
          sem_node f ss os.

  End NodeSemantics.

  Ltac inv_exp :=
    match goal with
    | H:sem_exp _ _ _ _ _ |- _ => inv H
    end.

  Ltac inv_scope :=
    match goal with
    | H:sem_scope _ _ _ _ _ |- _ => inv H
    end;
    destruct_conjs; subst.

  Ltac inv_branch :=
    match goal with
    | H:sem_branch _ _ |- _ => inv H
    end;
    destruct_conjs; subst.

  Ltac inv_block :=
    match goal with
    | H:sem_block _ _ _ _ |- _ => inv H
    end.

  (** ** Some properties *)

  Lemma var_history_In : forall x H,
      FEnv.In x (var_history H) <-> FEnv.In (Var x) H.
  Proof.
    unfold FEnv.In, var_history.
    intros; reflexivity.
  Qed.

  Lemma sem_var_history : forall H x vs,
      sem_var (var_history H) x vs <-> sem_var H (Var x) vs.
  Proof.
    unfold var_history.
    split; intros Hv; inv Hv; econstructor; eauto.
  Qed.

  Lemma var_history_mask : forall k rs H,
      FEnv.Equiv (@EqSt _) (var_history (mask_hist k rs H)) (mask_hist k rs (var_history H)).
  Proof.
    intros * ?. unfold var_history, mask_hist, FEnv.map; reflexivity.
  Qed.

  Lemma dom_dom_ub : forall H Γ,
      dom H Γ ->
      dom_ub H Γ.
  Proof.
    intros * (D1&D2).
    split; intros; [apply D1|apply D2]; auto.
  Qed.

  Lemma dom_dom_lb : forall H Γ,
      dom H Γ ->
      dom_lb H Γ.
  Proof.
    intros * (D1&D2).
    split; intros; [apply D1|apply D2]; auto.
  Qed.

  Lemma dom_map : forall f H Γ,
      dom (FEnv.map f H) Γ <-> dom H Γ.
  Proof.
    intros. unfold dom.
    now setoid_rewrite FEnv.map_in_iff.
  Qed.

  Lemma dom_ub_map : forall f H Γ,
      dom_ub (FEnv.map f H) Γ <-> dom_ub H Γ.
  Proof.
    intros. unfold dom_ub.
    now setoid_rewrite FEnv.map_in_iff.
  Qed.

  Lemma dom_lb_map : forall f H Γ,
      dom_lb (FEnv.map f H) Γ <-> dom_lb H Γ.
  Proof.
    intros. unfold dom_lb.
    now setoid_rewrite FEnv.map_in_iff.
  Qed.

  Lemma dom_ub_refines {R} : forall Hi1 Hi2 xs,
      FEnv.refines R Hi1 Hi2 ->
      dom_ub Hi2 xs ->
      dom_ub Hi1 xs.
  Proof.
    intros * Ref Dom.
    split; intros ? In; eapply FEnv.In_refines, Dom in In; eauto.
  Qed.

  Lemma dom_ub_incl : forall H xs1 xs2,
      List.incl xs1 xs2 ->
      dom_ub H xs1 ->
      dom_ub H xs2.
  Proof.
    intros * Hincl (?&?).
    split; intros * Hin; eauto using IsVar_incl, IsLast_incl.
  Qed.

  Lemma dom_ub_incl' : forall H xs1 xs2,
      (forall x, IsVar xs1 x -> IsVar xs2 x) ->
      (forall x, IsLast xs1 x -> IsLast xs2 x) ->
      dom_ub H xs1 ->
      dom_ub H xs2.
  Proof.
    intros * V L (?&?).
    split; intros * Hin; eauto.
  Qed.

  Definition vars_of_senv (Γ : static_env) :=
    flat_map (fun '(x, ann) => (Var x)::if isSome ann.(causl_last) then [Last x] else []) Γ.

  Fact vars_of_senv_Var : forall Γ x,
      In (Var x) (vars_of_senv Γ) <-> IsVar Γ x.
  Proof.
    unfold vars_of_senv.
    split; intros * In; [econstructor|inv In]; simpl_In.
    - destruct Hinf as [Hinf|Hinf]; cases; inv Hinf; try now inv H.
      solve_In.
    - solve_In. simpl. auto.
  Qed.

  Fact vars_of_senv_Last : forall Γ x,
      In (Last x) (vars_of_senv Γ) <-> IsLast Γ x.
  Proof.
    unfold vars_of_senv.
    split; intros * In; [|inv In]; simpl_In.
    - destruct Hinf as [Hinf|Hinf]; cases_eqn Eq; inv Hinf; inv H.
      apply isSome_true in Eq; destruct_conjs; subst.
      econstructor. eauto. congruence.
    - solve_In; simpl. right. destruct (causl_last _); try congruence. simpl; auto with datatypes.
  Qed.

  Lemma vars_of_senv_NoLast : forall Γ,
      (forall x, ~IsLast Γ x) ->
      vars_of_senv Γ = List.map (fun '(x, _) => Var x) Γ.
  Proof.
    induction Γ as [|(?&?)]; intros * NL; simpl in *; auto.
    rewrite IHΓ.
    2:{ intros * L; inv L; eapply NL.
        econstructor. right; eauto. auto. }
    cases_eqn Eq; auto.
    exfalso. eapply NL. econstructor; eauto with datatypes.
    intros contra; rewrite contra in Eq; inv Eq.
  Qed.

  Lemma dom_fenv_dom : forall H Γ,
      dom H Γ <-> FEnv.dom H (vars_of_senv Γ).
  Proof.
    intros.
    unfold dom, FEnv.dom.
    split; [intros (Var&Last)|intros Eq].
    - destruct x; [rewrite Var, vars_of_senv_Var|rewrite Last, vars_of_senv_Last]; reflexivity.
    - setoid_rewrite Eq.
      setoid_rewrite vars_of_senv_Var. setoid_rewrite vars_of_senv_Last.
      split; reflexivity.
  Qed.

  (** ** Properties of Forall2Brs *)

  Lemma Forall2Brs_impl_In (P1 P2 : _ -> _ -> Prop) : forall es vs,
      (forall x y, List.Exists (fun es => In x (snd es)) es -> P1 x y -> P2 x y) ->
      Forall2Brs P1 es vs ->
      Forall2Brs P2 es vs.
  Proof.
    intros * HP Hf.
    induction Hf; econstructor; eauto.
    eapply Forall2_impl_In; [|eauto]; intros ?? Hin1 Hin2 HP1.
    eapply HP; eauto.
  Qed.

  Lemma Forall2Brs_fst P : forall es vs,
      Forall2Brs P es vs ->
      Forall (fun vs => List.map fst vs = List.map fst es) vs.
  Proof.
    intros * Hf.
    induction Hf; simpl.
    - eapply Forall_impl; [|eauto]; intros; simpl in *; subst; auto.
    - eapply Forall3_ignore1 in H0.
      clear - H0 IHHf.
      induction H0; inv IHHf; constructor; eauto.
      destruct H as (?&?&?); subst; simpl. f_equal; auto.
  Qed.

  Lemma Forall2Brs_length1 (P : _ -> _ -> Prop) : forall es vs,
      Forall (fun es => Forall (fun e => forall v, P e v -> length v = numstreams e) (snd es)) es ->
      Forall2Brs P es vs ->
      Forall (fun es => length (annots (snd es)) = length vs) es.
  Proof.
    intros * Hf Hf2.
    induction Hf2; inv Hf; simpl in *; constructor; simpl.
    - apply Forall3_length in H0 as (?&?).
      rewrite <-H1, <-H0.
      unfold annots. rewrite flat_map_concat_map. eapply concat_length_eq.
      rewrite Forall2_map_1. eapply Forall2_impl_In; [|eauto]; intros.
      eapply Forall_forall in H3; eauto.
      rewrite length_annot_numstreams, H3; eauto.
    - eapply Forall_impl; [|eapply IHHf2; eauto]; intros (?&?) Hlen; simpl in *.
      rewrite Hlen. apply Forall3_length in H0 as (?&?); auto.
  Qed.

  Lemma Forall2Brs_length2 (P : _ -> _ -> Prop) : forall es vs,
      Forall2Brs P es vs ->
      Forall (fun vs => length vs = length es) vs.
  Proof.
    intros * Hf.
    induction Hf; simpl in *.
    - eapply Forall_impl; [|eauto]; intros; simpl in *; subst; auto.
    - clear - H0 IHHf.
      eapply Forall3_ignore1 in H0.
      induction H0; inv IHHf; constructor; auto.
      destruct H as (?&?&?); subst; simpl. f_equal; auto.
  Qed.

  Lemma Forall2Brs_map_1 (P : _ -> _ -> Prop) f : forall es vs,
      Forall2Brs (fun e => P (f e)) es vs <->
      Forall2Brs P (List.map (fun '(i, es) => (i, List.map f es)) es) vs.
  Proof.
    induction es; split; intros * Hf; inv Hf; simpl. 1,2:constructor; auto.
    - econstructor; eauto.
      rewrite Forall2_map_1; auto.
      rewrite <-IHes; eauto.
    - destruct a; inv H. econstructor; eauto.
      erewrite <-Forall2_map_1; auto.
      rewrite IHes; eauto.
  Qed.

  Lemma Forall2Brs_map_2 (P : _ -> _ -> Prop) f : forall es vs,
      Forall2Brs (fun e vs => P e (List.map f vs)) es vs ->
      Forall2Brs P es (List.map (List.map (fun '(i, v) => (i, f v))) vs).
  Proof.
    induction es; intros * Hf; inv Hf; simpl.
    - constructor. rewrite Forall_map.
      eapply Forall_impl; [|eauto]; intros; simpl in *; subst; auto.
    - econstructor; eauto.
      + eapply Forall2_map_2; eauto.
      + rewrite <-concat_map, Forall3_map_1, Forall3_map_2, Forall3_map_3.
        eapply Forall3_impl_In; [|eauto]; intros; simpl in *; subst; auto.
  Qed.

  (** ** properties of the [global] environment *)

  Ltac sem_cons :=
    intros; simpl_Forall; solve_Exists;
    unfold Is_node_in_eq in *;
    match goal with
    | H: Forall2Brs _ ?l1 ?l2 |- Forall2Brs _ ?l1 ?l2 =>
        eapply Forall2Brs_impl_In in H; eauto; intros; sem_cons
    | H: forall _, _ -> _ -> _ -> sem_exp _ _ _ ?e _ |- sem_exp _ _ _ ?e _ => eapply H; eauto
    | H: forall _ _, _ -> _ -> _ -> sem_block _ _ _ ?e |- sem_block _ _ _ ?e => eapply H; eauto
    | H: forall (_ : ident) (xs ys : list (Stream svalue)), _ -> _ -> sem_node _ _ _ _ |- sem_node _ _ _ _ =>
        eapply H; eauto using Is_node_in_exp; econstructor; sem_cons
    | Hname: n_name ?nd <> _, Hfind: find_node _ {| types := _; nodes := ?nd :: _ |} = _ |- _ =>
        rewrite find_node_other in Hfind; auto
    | Hname: n_name ?nd <> _ |- find_node _ {| types := _; nodes := ?nd :: _ |} = _ =>
        rewrite find_node_other; auto
    | Hname: n_name ?nd <> _ |- ~_ => idtac
    | H: ~Is_node_in_exp _ (Eapp _ _ _ _) |- _ <> _ => contradict H; subst; eapply INEapp2
    | H: ~_ |- ~_ => contradict H; try constructor; sem_cons
    | |- _ \/ _ => solve [left;sem_cons|right;sem_cons]
    | |- exists d, Some _ = Some d /\ List.Exists _ d =>
        do 2 esplit; [reflexivity|sem_cons]
    | k: nat,H: forall (_ : nat), _ |- _ => specialize (H k); sem_cons
    | H: Forall2 _ ?xs _ |- Forall2 _ ?xs _ =>
        eapply Forall2_impl_In in H; eauto; intros; sem_cons
    | |- exists _, when_hist _ _ _ _ /\ _ =>
        do 2 esplit; [auto|sem_cons]
    | |- exists _, select_hist _ _ _ _ _ /\ _ =>
        do 2 esplit; [auto|sem_cons]
    | H: forall _ _ _ _ _ _, In _ _ -> exists _ _ _, _ /\ _ /\ _ /\ _ |- exists _ _ _, _ /\ _ /\ _ /\ _ =>
        edestruct H as (?&?&?&?&?&?&?); eauto;
        do 3 esplit; split; [|split; [|split]]; eauto; sem_cons
    | H:sem_branch _ _ |- _ =>
        inv H; destruct_conjs
    | |- sem_branch _ _ => econstructor; eauto
    | |- Is_node_in_branch _ _ => econstructor; sem_cons
    | H:sem_scope _ _ _ _ _ |- sem_scope _ _ _ _ _ =>
        inv H; destruct_conjs; econstructor; eauto
    | |- Is_node_in_scope _ _ _ => econstructor; sem_cons
    | |- _ /\ _ => split; sem_cons
    | |- exists _ _, _ /\ _ /\ _ =>
        do 2 esplit; split; [|split]; eauto; sem_cons
    | _ => auto
    end.

  Section sem_cons.
    Context {PSyn prefs} (nd : @node PSyn prefs) (nds : list (@node PSyn prefs)).
    Context (typs : list type) (externs : list (ident * (list ctype * ctype))).

    Lemma sem_exp_cons1' :
      forall H bk e vs,
        (forall f xs ys, Is_node_in_exp f e -> sem_node (Global typs externs (nd::nds)) f xs ys -> sem_node (Global typs externs nds) f xs ys) ->
        sem_exp (Global typs externs (nd::nds)) H bk e vs ->
        ~Is_node_in_exp nd.(n_name) e ->
        sem_exp (Global typs externs nds) H bk e vs.
    Proof.
      induction e using exp_ind2; intros * Hnodes Hsem Hnf; inv Hsem; econstructor; eauto;
        repeat sem_cons.
    Qed.

    Lemma sem_transitions_cons1' :
      forall H bk trs def sts,
        (forall f xs ys, List.Exists (fun '(e, _) => Is_node_in_exp f e) trs -> sem_node (Global typs externs (nd::nds)) f xs ys -> sem_node (Global typs externs nds) f xs ys) ->
        sem_transitions (Global typs externs (nd::nds)) H bk trs def sts ->
        ~List.Exists (fun '(e, _) => Is_node_in_exp (n_name nd) e) trs ->
        sem_transitions (Global typs externs nds) H bk trs def sts.
    Proof.
      induction trs; intros * Hnodes Hsem Hnf; inv Hsem; econstructor; eauto;
        repeat sem_cons.
      eapply sem_exp_cons1'; eauto.
    Qed.

    Lemma sem_block_cons1' :
      forall blk H bk,
        (forall f xs ys, Is_node_in_block f blk -> sem_node (Global typs externs (nd::nds)) f xs ys -> sem_node (Global typs externs nds) f xs ys) ->
        sem_block (Global typs externs (nd::nds)) H bk blk ->
        ~Is_node_in_block nd.(n_name) blk ->
        sem_block (Global typs externs nds) H bk blk.
    Proof.
      induction blk using block_ind2; intros * Hnodes Hsem Hnf; inv Hsem; econstructor; eauto;
        repeat
          match goal with
          | H: sem_equation _ _ _ _ |- sem_equation _ _ _ _ => inv H; econstructor; eauto
          | |- sem_exp _ _ _ _ _ => eapply sem_exp_cons1'
          | |- sem_transitions _ _ _ _ _ _ => eapply sem_transitions_cons1'
          | H: forall _ _, _ -> _ -> _ -> sem_block _ _ _ ?blk |- sem_block _ _ _ ?blk => eapply H
          | _ => repeat sem_cons
          end.
    Qed.

  End sem_cons.

  Lemma sem_node_cons1 {PSyn prefs} :
    forall (nd : @node PSyn prefs) nds typs externs f xs ys,
      Ordered_nodes (Global typs externs (nd::nds)) ->
      sem_node (Global typs externs (nd::nds)) f xs ys ->
      nd.(n_name) <> f ->
      sem_node (Global typs externs nds) f xs ys.
  Proof.
    intros * Hord Hsem Hnf.
    assert (exists n, find_node f (Global typs externs0 (nd::nds)) = Some n) as (?&Hfind) by (inv Hsem; eauto).
    revert Hnf xs ys Hsem.
    eapply ordered_nodes_ind with (P_node:=fun f => n_name nd <> f -> forall xs ys, sem_node _ f xs ys -> sem_node _ f xs ys); eauto.
    intros * Hfind' Hind Hnf * Hsem.
    inv Hsem. take (find_node _ _ = Some n0) and rewrite Hfind' in it; inv it. econstructor; eauto.
    - rewrite find_node_other in Hfind'; auto.
    - eapply sem_block_cons1'; intros; eauto.
      eapply Hind; eauto. intro contra; subst.
      1,2:(rewrite find_node_other with (1:=Hnf) in Hfind';
           eapply find_node_later_not_Is_node_in; eauto).
  Qed.

  Corollary sem_block_cons1 {PSyn prefs} :
    forall (nd : @node PSyn prefs) nds typs externs blk Hi bs,
      Ordered_nodes (Global typs externs (nd::nds)) ->
      sem_block (Global typs externs (nd::nds)) Hi bs blk ->
      ~Is_node_in_block nd.(n_name) blk ->
      sem_block (Global typs externs nds) Hi bs blk.
  Proof.
    intros * Hord Hsem Hnin.
    eapply sem_block_cons1'; eauto.
    intros. eapply sem_node_cons1; eauto.
    destruct (ident_eq_dec (n_name nd) f); subst; congruence.
  Qed.

  Add Parametric Morphism {A} (v : A) : (fby1 v)
      with signature @EqSt _ ==> @EqSt _ ==> @EqSt _ ==> Basics.impl
        as fby1_EqSt.
  Proof.
    revert v.
    cofix Cofix.
    intros v cs cs' Ecs xs xs' Exs ys ys' Eys H.
    destruct cs' as [[]], xs' as [[]], ys' as [[]];
      inv H; inv Ecs; inv Exs; inv Eys; simpl in *;
        try discriminate.
    + constructor. eapply Cofix; eauto.
    + inv H4. econstructor. eapply Cofix; eauto. now inv H2.
  Qed.

  Add Parametric Morphism {A} : (@fby A)
      with signature @EqSt _ ==> @EqSt _ ==> @EqSt _ ==> Basics.impl
        as fby_EqSt.
  Proof.
    cofix Cofix.
    intros cs cs' Ecs xs xs' Exs ys ys' Eys H.
    destruct cs' as [[]], xs' as [[]], ys' as [[]];
      inv H; inv Ecs; inv Exs; inv Eys; simpl in *;
        try discriminate.
    + constructor; eapply Cofix; eauto.
    + inv H4. inv H. econstructor. inv H2.
      rewrite <- H1. rewrite <- H3. rewrite <- H5. assumption.
  Qed.

  Add Parametric Morphism : arrow1
      with signature @EqSt _ ==> @EqSt _ ==> @EqSt _ ==> Basics.impl
        as arrow1_EqSt.
  Proof.
    cofix Cofix.
    intros cs cs' Ecs xs xs' Exs ys ys' Eys H.
    destruct cs' as [[]], xs' as [[]], ys' as [[]];
      inv H; inv Ecs; inv Exs; inv Eys; simpl in *;
        try discriminate.
    + constructor; eapply Cofix; eauto.
    + inv H. inv H2. inv H4. econstructor.
      eapply Cofix; eauto.
  Qed.

  Add Parametric Morphism : arrow
      with signature @EqSt _ ==> @EqSt _ ==> @EqSt _ ==> Basics.impl
        as arrow_EqSt.
  Proof.
    cofix Cofix.
    intros cs cs' Ecs xs xs' Exs ys ys' Eys H.
    destruct cs' as [[]], xs' as [[]], ys' as [[]];
      inv H; inv Ecs; inv Exs; inv Eys; simpl in *;
        try discriminate.
    + constructor; eapply Cofix; eauto.
    + inv H. inv H2. inv H4. econstructor.
      rewrite <- H1, <- H3, <- H5; auto.
  Qed.

  Add Parametric Morphism k : (when k)
      with signature @EqSt svalue ==> @EqSt svalue ==> @EqSt svalue ==> Basics.impl
        as when_EqSt.
  Proof.
    revert k.
    cofix Cofix.
    intros k cs cs' Ecs xs xs' Exs ys ys' Eys H.
    destruct cs' as [[]], xs' as [[]], ys' as [[]];
      inv H; inv Ecs; inv Exs; inv Eys; simpl in *;
        try discriminate.
    + constructor; eapply Cofix; eauto.
    + inv H. inv H3. inv H5. constructor; auto. eapply Cofix; eauto.
    + inv H. inv H2. inv H4. econstructor. eapply Cofix; eauto.
  Qed.

  Add Parametric Morphism : const
      with signature @EqSt bool ==> eq ==> @EqSt svalue
        as const_EqSt.
  Proof.
    cofix Cofix; intros b b' Eb.
    unfold_Stv b; unfold_Stv b';
      constructor; inv Eb; simpl in *; try discriminate; auto.
  Qed.

  Add Parametric Morphism : enum
      with signature @EqSt bool ==> eq ==> @EqSt svalue
        as enum_EqSt.
  Proof.
    cofix Cofix; intros b b' Eb.
    unfold_Stv b; unfold_Stv b';
      constructor; inv Eb; simpl in *; try discriminate; auto.
  Qed.

  Add Parametric Morphism : (@sem_var lustre_var)
      with signature FEnv.Equiv (@EqSt _) ==> eq ==> @EqSt svalue ==> Basics.impl
        as sem_var_EqSt.
  Proof.
    intros H H' EH x xs xs' E; intro Sem; inv Sem.
    specialize (EH x). rewrite H1 in EH. inv EH.
    econstructor; eauto.
    now rewrite <-E, H2, H4.
  Qed.

  Definition history_equiv (Hi1 Hi2 : history) : Prop := FEnv.Equiv (@EqSt _) Hi1 Hi2.

  Global Instance history_equiv_refl : Reflexive history_equiv.
  Proof. intros ??. reflexivity. Qed.

  Add Parametric Morphism {PSyn prefs} (G : @global PSyn prefs) : (sem_exp G)
      with signature history_equiv ==> @EqSt bool ==> eq ==> @EqSts svalue ==> Basics.impl
        as sem_exp_morph.
  Proof.
    intros H H' EH b b' Eb e xs xs' Exs Hsem. revert xs xs' Hsem Exs.
    induction e using exp_ind2; intros; inv Hsem; unfold EqSts in *; simpl_Forall.
    - econstructor. now rewrite <-Eb, <-H2.
    - econstructor. now rewrite <-Eb, <-H2.
    - constructor.  now rewrite <-EH, <-H2.
    - constructor. now rewrite <-EH, <-H2.
    - econstructor; eauto.
      + eapply IHe; eauto. reflexivity.
      + now take (_ ≡ y) and rewrite <-it.
    - econstructor; eauto.
      + eapply IHe1; eauto; reflexivity.
      + eapply IHe2; eauto; reflexivity.
      + now take (_ ≡ y) and rewrite <-it.
    - eapply Sextcall with (ss:=ss); eauto.
      + simpl_Forall; eauto.
        take (forall xs xs', _ -> _ -> _) and eapply it; eauto; reflexivity.
      + now take (_ ≡ y) and rewrite <-it.
    - eapply Sfby with (s0ss:=s0ss) (sss:=sss); simpl_Forall.
      1,2:take (forall xs xs', _ -> _ -> _) and eapply it; eauto; reflexivity.
      eapply Forall3_EqSt; eauto. solve_proper.
    - eapply Sarrow with (s0ss:=s0ss) (sss:=sss); simpl_Forall.
      1,2:take (forall xs xs', _ -> _ -> _) and eapply it; eauto; reflexivity.
      eapply Forall3_EqSt; eauto. solve_proper.
    - eapply Swhen with (ss:=ss); eauto; simpl_Forall.
      + take (forall xs xs', _ -> _ -> _) and eapply it; eauto; reflexivity.
      + rewrite <-EH; eauto.
      + eapply Forall2_EqSt; eauto. solve_proper.
    - econstructor; eauto.
      + rewrite <-EH; eauto.
      + instantiate (1:=vs).
        eapply Forall2Brs_impl_In; [|eauto]; intros.
        simpl_Exists. simpl_Forall. eapply H0; eauto. reflexivity.
      + eapply Forall2_EqSt; eauto. solve_proper.
    - econstructor; eauto.
      + eapply IHe; eauto. reflexivity.
      + eapply Forall2Brs_impl_In; [|eauto]; intros.
        simpl_Exists. simpl_Forall. eapply H0; eauto. reflexivity.
      + eapply Forall3_EqSt_Proper; eauto. solve_proper.
    - eapply ScaseDefault with (vd:=vd); eauto.
      + eapply IHe; eauto. reflexivity.
      + eapply Forall2Brs_impl_In; [|eauto]; intros.
        simpl_Exists. simpl_Forall. eapply H0; eauto. reflexivity.
      + simpl_Forall. eapply H1; eauto. reflexivity.
      + eapply Forall3_EqSt_Proper; eauto. solve_proper.
    - eapply Sapp with (ss:=ss) (rs:=rs); eauto; simpl_Forall.
      1,2:take (forall xs xs', _ -> _ -> _) and eapply it; eauto; reflexivity.
      intro k; take (forall k, _) and specialize (it k); inv it.
      econstructor; eauto.
      simpl_Forall. eapply Forall2_EqSt; eauto. solve_proper.
  Qed.

  Add Parametric Morphism {PSyn prefs} (G : @global PSyn prefs) : (sem_equation G)
      with signature history_equiv ==> @EqSt bool ==> eq ==> Basics.impl
        as sem_equation_morph.
  Proof.
    unfold Basics.impl; intros H H' EH xs xs' Exss eq Hsem.
    inversion_clear Hsem as [????? Hseme Hsemv]. econstructor; eauto.
    - eapply Forall2_impl_In; [|eauto]; intros.
      rewrite <-EH, <-Exss; eauto.
    - eapply Forall2_impl_In; [|eauto]; intros.
      now rewrite <-EH.
  Qed.

  Add Parametric Morphism {PSyn prefs} (G: @global PSyn prefs) : (sem_transitions G)
      with signature history_equiv ==> @EqSt bool ==> eq ==> eq ==> @EqSt _ ==> Basics.impl
        as sem_transitions_morph.
  Proof.
    intros H H' EH ?? Eb ???? Estres Hsem.
    revert dependent y3.
    induction Hsem; intros * Heq; econstructor; eauto.
    - rewrite <-Heq, <-Eb; auto.
    - now rewrite <-EH, <-Eb.
    - eapply IHHsem; eauto. reflexivity.
    - now rewrite <-Heq.
  Qed.

  Add Parametric Morphism : var_history
      with signature history_equiv ==> FEnv.Equiv (@EqSt _)
        as var_history_morph.
  Proof.
    intros * Eq id; unfold var_history; simpl; auto.
  Qed.

  Add Parametric Morphism {PSyn prefs} (G : @global PSyn prefs) : (sem_block G)
      with signature history_equiv ==> @EqSt bool ==> eq ==> Basics.impl
        as sem_block_morph.
  Proof.
    intros H H' EH b b' Eb blk.
    revert H H' b b' EH Eb; induction blk using block_ind2; intros * EH Eb Hsem; inv Hsem.
    - constructor. now rewrite <-EH, <-Eb.
    - econstructor; eauto.
      + now rewrite <-EH, <-Eb.
      + intros k. specialize (H8 k); simpl_Forall. eapply H; eauto.
        * now rewrite EH.
        * now rewrite <-Eb.
    - econstructor; eauto.
      + now rewrite <-EH, <-Eb.
      + simpl_Forall. take (sem_branch _ _) and inv it.
        do 2 esplit. 2:econstructor; eauto.
        * rewrite <-EH; eauto.
        * simpl_Forall. eapply H; eauto. reflexivity. now rewrite <-Eb.
    - econstructor; eauto.
      + rewrite <-EH, <-Eb; eauto.
      + now rewrite <-EH.
      + simpl_Forall. specialize (H11 k) as (Hik&?). destruct_conjs.
        inv_branch. inv_scope.
        exists Hik. split; [|econstructor; econstructor; eauto; repeat split]; eauto.
        * now rewrite <-EH.
        * intros * Hin. edestruct H5 as (?&?&?&?&?&?&?); eauto.
          do 3 esplit. repeat (split; eauto).
          now rewrite <-Eb.
        * simpl_Forall. eapply H; eauto. reflexivity. now rewrite <-Eb.
        * now rewrite <-Eb.
    - econstructor; eauto.
      + rewrite <-EH, <-Eb; eauto.
      + simpl_Forall. specialize (H10 k) as (Hik&?). destruct_conjs.
        exists Hik. split.
        * now rewrite <-EH.
        * inv_branch. constructor. now rewrite <-Eb.
      + simpl_Forall. specialize (H11 k) as (Hik&?). destruct_conjs.
        inv_branch. inv_scope.
        exists Hik. split; [|econstructor; econstructor; eauto; repeat split]; eauto.
        * now rewrite <-EH.
        * intros * Hin. edestruct H5 as (?&?&?&?&?&?&?); eauto.
          do 3 esplit. repeat (split; eauto).
          now rewrite <-Eb.
        * simpl_Forall. eapply H; eauto. reflexivity. now rewrite <-Eb.
    - constructor. inv_scope.
      eapply Sscope with (Hi':=Hi'); eauto.
      + intros. edestruct H7; eauto. destruct_conjs.
        do 3 esplit; eauto. repeat split; eauto.
        eapply sem_exp_morph; eauto. 2:reflexivity.
        apply FEnv.union_Equiv; auto; reflexivity.
      + simpl_Forall.
        eapply H; eauto.
        apply FEnv.union_Equiv; auto; reflexivity.
  Qed.

  Add Parametric Morphism {PSyn prefs} (G : @global PSyn prefs) : (sem_node G)
      with signature eq ==> @EqSts svalue ==> @EqSts svalue ==> Basics.impl
        as sem_node_morph.
  Proof.
    unfold Basics.impl; intros f xss xss' Exss yss yss' Eyss Sem.
    induction Sem.
    subst.
    econstructor; try reflexivity; eauto. instantiate (1 := H).
    + eapply Forall2_trans_ex in Exss; [|eauto].
      simpl_Forall. take (_ ≡ _) and now rewrite <-it.
    + eapply Forall2_trans_ex in Eyss; [|eauto].
      simpl_Forall. take (_ ≡ _) and now rewrite <-it.
    + now rewrite <-Exss.
  Qed.

  Ltac inv_scope' := (Syn.inv_scope || inv_scope).
  Ltac inv_branch' := (Syn.inv_branch || inv_branch).
  Ltac inv_block' := (Syn.inv_block || inv_block).

  (** ** All the defined variables have a semantic *)

  Fact sem_var_In {K} : forall H x vs,
      @sem_var K H x vs ->
      FEnv.In x H.
  Proof.
    intros * Hv. inv Hv.
    econstructor; eauto.
  Qed.

  Corollary sem_vars_In : forall H xs vs,
      Forall2 (fun x => sem_var H (Var x)) xs vs ->
      Forall (fun x => FEnv.In (Var x) H) xs.
  Proof.
    intros * Hvs.
    induction Hvs; constructor; eauto using sem_var_In.
  Qed.

  Lemma sem_block_defined {PSyn prefs} (G: @global PSyn prefs) : forall blk H bs x,
      sem_block G H bs blk ->
      Is_defined_in x blk ->
      FEnv.In (Var x) H.
  Proof.
    induction blk using block_ind2; intros * Hsem Hdef; repeat inv_block'.
    - (* equation *)
      take (sem_equation _ _ _ _) and inv it.
      eapply Forall2_ignore2, Forall_forall in H7 as (?&?&?); eauto using sem_var_In.
    - (* reset *)
      specialize (H9 0).
      simpl_Exists; simpl_Forall.
      eapply H in H9; eauto.
      setoid_rewrite FEnv.map_in_iff in H9; eauto.
    - (* switch *)
      simpl_Exists; simpl_Forall.
      repeat inv_branch'.
      simpl_Exists. simpl_Forall.
      eapply FEnv.In_refines; eauto.
    - (* automaton *)
      simpl_Exists; simpl_Forall. specialize (H12 0); destruct_conjs.
      repeat inv_branch'. repeat inv_scope'.
      simpl_Exists. simpl_Forall.
      eapply FEnv.In_refines; eauto.
      eapply H, FEnv.union_In in H4 as [|Hin']; eauto.
      exfalso. take (~ _) and eapply it.
      take (dom _ _) and apply it in Hin'. inv Hin'. solve_In.
    - (* automaton *)
      simpl_Exists; simpl_Forall. specialize (H12 0); destruct_conjs.
      repeat inv_branch'. repeat inv_scope'.
      simpl_Exists. simpl_Forall.
      eapply FEnv.In_refines; eauto.
      eapply H, FEnv.union_In in H14 as [|Hin']; eauto.
      exfalso. take (~ _) and eapply it.
      take (dom _ _) and apply it in Hin'. inv Hin'. solve_In.
    - (* local *)
      repeat inv_scope'. simpl_Exists; simpl_Forall.
      eapply H, FEnv.union_In in H10 as [|Hin']; eauto.
      exfalso. take (~ _) and eapply it.
      take (dom _ _) and apply it in Hin'. inv Hin'. solve_In.
  Qed.

  Corollary Forall_sem_block_defined {PSyn prefs} (G: @global PSyn prefs) : forall blks x H bs,
      Forall (sem_block G H bs) blks ->
      List.Exists (Is_defined_in x) blks ->
      FEnv.In (Var x) H.
  Proof.
    intros * Hsem Hdef; simpl_Exists; simpl_Forall.
    eapply sem_block_defined; eauto.
  Qed.

  Lemma sem_scope_defined {PSyn prefs} (G: @global PSyn prefs) : forall locs blks Hi bs x,
      sem_scope (fun Hi => sem_exp G Hi bs) (fun Hi => Forall (sem_block G Hi bs)) Hi bs (Scope locs blks) ->
      Is_defined_in_scope (List.Exists (Is_defined_in x)) x (Scope locs blks) ->
      FEnv.In (Var x) Hi.
  Proof.
    intros * Hsem Hdef; inv Hsem; inv Hdef.
    eapply Forall_sem_block_defined, FEnv.union_In in H5 as [|Hin']; eauto.
    exfalso. take (~ _) and eapply it.
    take (dom _ _) and apply it in Hin'. inv Hin'. solve_In.
  Qed.

  Corollary sem_scope_defined1 {PSyn prefs} (G: @global PSyn prefs) :
    forall locs blks Hi bs Γ xs x,
      sem_scope (fun Hi => sem_exp G Hi bs) (fun Hi => Forall (sem_block G Hi bs)) Hi bs (Scope locs blks) ->
      VarsDefinedScope (fun blks ys => exists xs, Forall2 VarsDefined blks xs /\ Permutation (concat xs) ys) (Scope locs blks) xs ->
      NoDupScope (fun Γ => Forall (NoDupLocals Γ)) Γ (Scope locs blks) ->
      incl xs Γ ->
      In x xs ->
      FEnv.In (Var x) Hi.
  Proof.
    intros * Hsem Hdef Hnd Hincl Hinxs.
    eapply sem_scope_defined; eauto.
    eapply VarsDefinedScope_Is_defined; eauto.
    - eapply NoDupScope_incl; eauto.
      intros; simpl in *. simpl_Forall.
      eapply NoDupLocals_incl; eauto.
    - intros; simpl in *. destruct_conjs.
      eapply Forall_VarsDefined_Is_defined; eauto.
      simpl_Forall. 1,2:now rewrite H2.
  Qed.

  Corollary sem_scope_defined2 {A} {PSyn prefs} (G: @global PSyn prefs) :
    forall locs (blks: _ * A) Hi bs Γ xs x,
      sem_scope (fun Hi => sem_exp G Hi bs) (fun Hi blks => Forall (sem_block G Hi bs) (fst blks)) Hi bs (Scope locs blks) ->
      VarsDefinedScope (fun blks ys => exists xs, Forall2 VarsDefined (fst blks) xs /\ Permutation (concat xs) ys) (Scope locs blks) xs ->
      NoDupScope (fun Γ blks => Forall (NoDupLocals Γ) (fst blks)) Γ (Scope locs blks) ->
      incl xs Γ ->
      In x xs ->
      FEnv.In (Var x) Hi.
  Proof.
    intros * Hsem Hdef Hnd Hincl Hinxs.
    eapply sem_scope_defined1; eauto.
    - inv Hsem; econstructor; eauto.
    - inv Hdef; econstructor; eauto.
    - inv Hnd; econstructor; eauto.
  Qed.

  Lemma sem_branch_defined {PSyn prefs} (G: @global PSyn prefs) : forall caus blks Hi bs x,
      sem_branch (Forall (sem_block G Hi bs)) (Branch caus blks) ->
      Is_defined_in_branch (List.Exists (Is_defined_in x)) (Branch caus blks) ->
      FEnv.In (Var x) Hi.
  Proof.
    intros * Hsem Hdef; inv Hsem; inv Hdef.
    eapply Forall_sem_block_defined in H1; eauto.
  Qed.

  Corollary sem_branch_defined1 {PSyn prefs} (G: @global PSyn prefs) :
    forall caus blks Hi bs Γ xs x,
      sem_branch (Forall (sem_block G Hi bs)) (Branch caus blks) ->
      VarsDefinedBranch (fun blks ys => exists xs, Forall2 VarsDefined blks xs /\ Permutation (concat xs) ys) (Branch caus blks) xs ->
      NoDupBranch (Forall (NoDupLocals Γ)) (Branch caus blks) ->
      incl xs Γ ->
      In x xs ->
      FEnv.In (Var x) Hi.
  Proof.
    intros * Hsem Hdef Hnd Hincl Hinxs.
    eapply sem_branch_defined; eauto.
    eapply VarsDefinedBranch_Is_defined; eauto.
    - intros; simpl in *. destruct_conjs.
      eapply Forall_VarsDefined_Is_defined; eauto.
      simpl_Forall. 1,2:rewrite H1; eauto using NoDupLocals_incl.
  Qed.

  Corollary sem_branch_defined2 {A} {PSyn prefs} (G: @global PSyn prefs) :
    forall caus (blks: (A * scope (_ * A))) Hi bs Γ xs x,
      sem_branch
        (fun blks =>
           sem_scope (fun Hi => sem_exp G Hi bs)
             (fun Hi blks => Forall (sem_block G Hi bs) (fst blks)) Hi bs (snd blks))
        (Branch caus blks) ->
      VarsDefinedBranch
        (fun blks => VarsDefinedScope (fun blks ys => exists xs, Forall2 VarsDefined (fst blks) xs /\ Permutation (concat xs) ys) (snd blks))
        (Branch caus blks) xs ->
      NoDupBranch
        (fun blks => NoDupScope (fun Γ blks => Forall (NoDupLocals Γ) (fst blks)) Γ (snd blks))
        (Branch caus blks) ->
      incl xs Γ ->
      In x xs ->
      FEnv.In (Var x) Hi.
  Proof.
    intros * Hsem Hdef Hnd Hincl Hinxs.
    destruct blks as [?(?&?)]. inv Hsem. inv Hdef. inv Hnd.
    eapply sem_scope_defined2; eauto.
  Qed.

  (** ** Preservation of the semantics while refining an environment *)
  (** If a new environment [refines] the previous one, it gives the same semantics
      to variables and therefore expressions, equations dans nodes *)

  Fact refines_eq_EqSt {K A} : forall (H H': @FEnv.t K _) ,
      FEnv.refines eq H H' ->
      FEnv.refines (@EqSt A) H H'.
  Proof.
    intros * Href ?? Hfind.
    eapply Href in Hfind as (?&?&Hfind); subst.
    rewrite Hfind. do 2 esplit; eauto.
    reflexivity.
  Qed.

  Fact sem_var_refines {K} : forall (H H' : @FEnv.t K _) id v,
      H ⊑ H' ->
      sem_var H id v ->
      sem_var H' id v.
  Proof.
    intros H H' id v Href Hsem.
    destruct Hsem. eapply Href in H0 as (?&?&Hfind).
    econstructor; eauto.
    etransitivity; eauto.
  Qed.

  Lemma sem_var_refines_inv {K} : forall env (Hi1 Hi2: @FEnv.t K _) x vs,
      List.In x env ->
      FEnv.dom_lb Hi1 env ->
      (forall vs, sem_var Hi1 x vs -> sem_var Hi2 x vs) ->
      sem_var Hi2 x vs ->
      sem_var Hi1 x vs.
  Proof.
    intros * Hin Hdom Href Hvar.
    eapply Hdom in Hin as (vs'&Hfind).
    assert (sem_var Hi1 x vs') as Hvar' by (econstructor; eauto; reflexivity).
    specialize (Href _ Hvar').
    eapply sem_var_det in Href; eauto.
    now rewrite Href.
  Qed.

  Lemma sem_var_refines' {K} : forall (Hi1 Hi2: @FEnv.t K _) x vs,
      FEnv.In x Hi1 ->
      Hi1 ⊑ Hi2 ->
      sem_var Hi2 x vs ->
      sem_var Hi1 x vs.
  Proof.
    intros * Hin Href Hv2.
    inv Hin. econstructor; eauto.
    eapply Href in H as (?&Heq&Hfind').
    inv Hv2. rewrite Hfind' in H0; inv H0.
    rewrite Heq; auto.
  Qed.

  Corollary sem_var_refines'' {K} : forall env (Hi1 Hi2: @FEnv.t K _) x vs,
      List.In x env ->
      FEnv.dom_lb Hi1 env ->
      Hi1 ⊑ Hi2 ->
      sem_var Hi2 x vs ->
      sem_var Hi1 x vs.
  Proof.
    intros * Hin Hdom Href Hvar.
    eapply sem_var_refines' in Hvar; eauto.
  Qed.

  Lemma sem_clock_refines : forall H H' ck bs bs',
      H ⊑ H' ->
      sem_clock H bs ck bs' ->
      sem_clock H' bs ck bs'.
  Proof.
    induction ck; intros * Href Hck; inv Hck.
    - constructor; auto.
    - econstructor; eauto using sem_var_refines.
  Qed.

  Lemma sem_clock_refines' : forall vars H H' ck bs bs',
      wx_clock vars ck ->
      (forall x vs, IsVar vars x -> sem_var H x vs -> sem_var H' x vs) ->
      sem_clock H bs ck bs' ->
      sem_clock H' bs ck bs'.
  Proof.
    induction ck; intros * Hwx Href Hck; inv Hwx; inv Hck;
      econstructor; eauto.
  Qed.

  Fact sem_exp_refines {PSyn prefs} : forall (G : @global PSyn prefs) b e H H' v,
      H ⊑ H' ->
      sem_exp G H b e v ->
      sem_exp G H' b e v.
  Proof with eauto with datatypes.
    induction e using exp_ind2; intros * Href Hsem; inv Hsem;
      econstructor; eauto using sem_var_refines; simpl_Forall; eauto.
    1-3:(eapply Forall2Brs_impl_In; [|eauto]; intros;
         simpl_Exists; simpl_Forall; eauto).
  Qed.

  Fact sem_equation_refines {PSyn prefs} : forall (G : @global PSyn prefs) H H' b equ,
      H ⊑ H' ->
      sem_equation G H b equ ->
      sem_equation G H' b equ.
  Proof with eauto.
    intros * Href Hsem. inv Hsem; simpl in *.
    apply Seq with (ss:=ss); simpl_Forall;
      eauto using sem_exp_refines, sem_var_refines.
  Qed.

  Fact sem_transitions_refines {PSyn prefs} : forall (G : @global PSyn prefs) H H' b trans default stres,
      H ⊑ H' ->
      sem_transitions G H b trans default stres ->
      sem_transitions G H' b trans default stres.
  Proof with eauto.
    induction trans; intros * Href Hsem; inv Hsem;
      econstructor; eauto using sem_exp_refines.
  Qed.

  Fact var_history_refines : forall Hi1 Hi2,
      Hi1 ⊑ Hi2 ->
      (var_history Hi1) ⊑ (var_history Hi2).
  Proof.
    unfold var_history.
    intros * Ref ?? Find; eauto.
  Qed.

  Fact var_history_refines' : forall Hi1 Hi2,
      (forall x vs, sem_var Hi1 (Var x) vs -> sem_var Hi2 (Var x) vs) ->
      (var_history Hi1) ⊑ (var_history Hi2).
  Proof.
    unfold var_history.
    intros * Ref ?? Find; eauto.
    assert (sem_var Hi1 (Var x) v) as Hv by (econstructor; eauto; reflexivity).
    eapply Ref in Hv. inv Hv. eauto.
  Qed.

  Fact sem_block_refines {PSyn prefs} : forall (G: @global PSyn prefs) d H H' b,
      H ⊑ H' ->
      sem_block G H b d ->
      sem_block G H' b d.
  Proof.
    induction d using block_ind2; intros * Href Hsem; inv Hsem.
    - (* equation *)
      econstructor; eauto using sem_equation_refines.
    - (* reset *)
      econstructor; eauto using sem_exp_refines.
      intros k. specialize (H8 k).
      rewrite Forall_forall in *. intros ? Hin.
      eapply H. 1,3:eauto.
      eapply FEnv.refines_map; eauto.
      intros ?? Heq. rewrite Heq. reflexivity.
    - (* switch *)
      econstructor; eauto using sem_exp_refines.
      + simpl_Forall. do 2 esplit; [|eauto].
        intros ?? Hfind. apply H2 in Hfind as (?&Hwhen&Hfind').
        apply Href in Hfind' as (?&?&?). do 2 esplit; [|eauto].
        now rewrite <-H5.
    - (* automaton (weak transitions) *)
      eapply SautoWeak; eauto using sem_clock_refines, var_history_refines, sem_transitions_refines.
      simpl_Forall. specialize (H11 k); destruct_conjs.
      inv_branch. inv_scope.
      esplit; split; eauto. 2:do 2 econstructor; eauto; repeat (split; eauto); eauto.
      intros ?? Hfind. apply H2 in Hfind as (?&Hwhen&Hfind').
      apply Href in Hfind' as (?&?&?). do 2 esplit; [|eauto].
      take (_ ≡ _) and now rewrite <-it.
    - (* automaton (strong transitions) *)
      eapply SautoStrong; eauto using sem_clock_refines, var_history_refines, sem_transitions_refines.
      + simpl_Forall. specialize (H10 k); destruct_conjs.
        esplit; split; eauto.
        intros ?? Hfind. apply H2 in Hfind as (?&Hwhen&Hfind').
        apply Href in Hfind' as (?&?&?). do 2 esplit; [|eauto].
        take (_ ≡ _) and now rewrite <-it.
      + simpl_Forall. specialize (H11 k); destruct_conjs.
        inv_branch. inv_scope.
        esplit; split; eauto. 2:do 2 econstructor; eauto; repeat (split; eauto); eauto.
        intros ?? Hfind. apply H2 in Hfind as (?&Hwhen&Hfind').
        apply Href in Hfind' as (?&?&?). do 2 esplit; [|eauto].
        take (_ ≡ _) and now rewrite <-it.
    - (* locals *)
      constructor.
      inv H4. econstructor; [| |eauto]; eauto.
      + intros. edestruct H7 as (?&?&?&?&?&?&?); eauto.
        repeat (esplit; eauto).
        eapply sem_exp_refines; [|eauto]; eauto using FEnv.union_refines1, EqStrel_Reflexive.
      + simpl_Forall. eapply H; eauto using FEnv.union_refines1, EqStrel_Reflexive.
  Qed.

  Section props.
    Context {PSyn : block -> Prop}.
    Context {prefs : PS.t}.
    Variable (G : @global PSyn prefs).

    (** The number of streams generated by an expression [e] equals [numstreams e] *)

    Fact sem_exp_numstreams : forall H b e v,
        wl_exp G e ->
        sem_exp G H b e v ->
        length v = numstreams e.
    Proof with eauto.
      induction e using exp_ind2; intros v Hsem Hwl; inv Hwl; inv Hsem; simpl; auto.
      - (* fby *)
        take (Forall3 _ _ _ _) and eapply Forall3_length in it as (Hlen1&Hlen2).
        rewrite <- H12. setoid_rewrite <-Hlen2.
        unfold annots; rewrite flat_map_concat_map.
        apply concat_length_eq.
        rewrite Forall2_map_2, Forall2_swap_args.
        simpl_Forall.
        rewrite length_annot_numstreams. eapply H1; eauto.
      - (* arrow *)
        take (Forall3 _ _ _ _) and eapply Forall3_length in it as (Hlen1&Hlen2).
        rewrite <- H12, <-Hlen2.
        unfold annots; rewrite flat_map_concat_map.
        apply concat_length_eq.
        rewrite Forall2_map_2, Forall2_swap_args.
        simpl_Forall.
        rewrite length_annot_numstreams. eapply H1; eauto.
      - (* when *)
        take (Forall2 _ _ _) and eapply Forall2_length in it as Hlen1.
        rewrite <-H7, <-Hlen1.
        unfold annots; rewrite flat_map_concat_map.
        apply concat_length_eq.
        rewrite Forall2_map_2, Forall2_swap_args.
        simpl_Forall.
        rewrite length_annot_numstreams. eapply H0; eauto.
      - (* merge *)
        take (Forall2Brs _ _ _) and eapply Forall2Brs_length1 in it; eauto.
        2:simpl_Forall; eauto.
        destruct es as [|(?&?)]; try congruence. simpl_Forall.
        take (Forall2 _ _ _) and apply Forall2_length in it. congruence.
      - (* case *)
        take (Forall2Brs _ _ _) and eapply Forall2Brs_length1 in it; eauto.
        2:simpl_Forall; eauto.
        destruct es as [|(?&?)]; try congruence. simpl_Forall.
        take (Forall3 _ _ _ _) and apply Forall3_length in it as (?&?). congruence.
      - (* case *)
        take (Forall2Brs _ _ _) and eapply Forall2Brs_length1 in it; eauto.
        2:simpl_Forall; eauto.
        destruct es as [|(?&?)]; try congruence. simpl_Forall.
        take (Forall3 _ _ _ _) and apply Forall3_length in it as (?&?). congruence.
      - (* app  *)
        specialize (H13 0). inv H13.
        simpl_Forall. take (Forall2 _ _ v) and (apply Forall2_length in it).
        rewrite H3 in H14; inv H14.
        repeat rewrite map_length in *. setoid_rewrite map_length in it. congruence.
    Qed.

    Corollary sem_exps_numstreams : forall H b es vs,
        Forall (wl_exp G) es ->
        Forall2 (sem_exp G H b) es vs ->
        length (concat vs) = length (annots es).
    Proof.
      intros * Hwt Hsem.
      assert (Forall2 (fun v e => length v = numstreams e) vs es) as Hf.
      { rewrite Forall2_swap_args. simpl_Forall.
        eapply sem_exp_numstreams; eauto. }
      clear Hwt Hsem.
      induction Hf; simpl.
      - reflexivity.
      - repeat rewrite app_length.
        f_equal; auto.
        rewrite length_annot_numstreams. assumption.
    Qed.

    Lemma sem_vars_mask_inv {K} : forall k r (H: @FEnv.t K _) xs vs,
        Forall2 (sem_var (Str.mask_hist k r H)) xs vs ->
        exists vs', Forall2 (sem_var H) xs vs' /\ EqSts vs (List.map (maskv k r) vs').
    Proof.
      intros * Hvars.
      induction Hvars; simpl.
      - exists []; simpl; split; eauto. constructor.
      - destruct IHHvars as (vs'&Hvars'&Heqs).
        eapply sem_var_mask_inv in H0 as (v'&Hvar'&Heq).
        exists (v'::vs'). split; constructor; auto.
    Qed.

    Fact sem_block_sem_var : forall blk x Hi bs,
        Is_defined_in x blk ->
        sem_block G Hi bs blk ->
        exists vs, sem_var Hi (Var x) vs.
    Proof.
      intros * Hdef Hsem.
      eapply sem_block_defined in Hsem as (?&?); eauto.
      do 2 esplit; eauto. reflexivity.
    Qed.

    Corollary sem_block_dom_lb : forall blk xs Hi bs,
        VarsDefined blk xs ->
        NoDupLocals xs blk ->
        sem_block G Hi bs blk ->
        FEnv.dom_lb Hi (List.map Var xs).
    Proof.
      intros * Hvars Hnd Hsem ? Hin. simpl_In.
      eapply VarsDefined_Is_defined in Hin0; eauto.
      eapply sem_block_sem_var in Hin0 as (?&Hvar); eauto.
      simpl in *; eauto using sem_var_In.
    Qed.

    Corollary Forall_sem_block_dom_lb : forall blks xs ys Hi bs,
        Forall2 VarsDefined blks xs ->
        Forall (NoDupLocals ys) blks ->
        Forall (sem_block G Hi bs) blks ->
        Permutation (concat xs) ys ->
        FEnv.dom_lb Hi (List.map Var ys).
    Proof.
      intros * Hvars Hnd Hsem Hperm ? Hin.
      rewrite <-Hperm in Hin. simpl_In.
      eapply Forall_VarsDefined_Is_defined in Hin0; eauto.
      2:{ simpl_Forall. eapply NoDupLocals_incl; [|eauto]. now rewrite Hperm. }
      simpl_Exists; simpl_Forall.
      eapply sem_block_sem_var in Hin0 as (?&Hvar); eauto.
      simpl in *; eauto using sem_var_In.
    Qed.

  End props.

  (** ** Restriction *)

  Definition restrict (H : history) Γ :=
    FEnv.restrict H (vars_of_senv Γ).

  Lemma restrict_dom_ub : forall H Γ,
      dom_ub (restrict H Γ) Γ.
  Proof.
    intros *; split; intros * In.
    1,2:apply FEnv.restrict_In in In as (_&In).
    - now apply vars_of_senv_Var.
    - now apply vars_of_senv_Last.
  Qed.

  Fact sem_var_restrict {K} `{FEnv.fenv_key K} : forall vars (H: @FEnv.t K _) id v,
      List.In id vars ->
      sem_var H id v ->
      sem_var (FEnv.restrict H vars) id v.
  Proof.
    intros * HIn Hsem.
    inv Hsem.
    econstructor; eauto.
    apply FEnv.restrict_find; auto.
  Qed.

  Fact sem_var_restrict_inv {K} `{FEnv.fenv_key K} : forall vars (H: @FEnv.t K _) id v,
      sem_var (FEnv.restrict H vars) id v ->
      List.In id vars /\ sem_var H id v.
  Proof.
    intros * Hvar; split.
    - eapply FEnv.restrict_dom_ub.
      inv Hvar. econstructor; eauto.
    - eapply sem_var_refines; [|eauto].
      eapply FEnv.restrict_refines;
        auto using EqStrel_Transitive, EqStrel_Reflexive.
  Qed.

  Fact sem_clock_restrict : forall Γ xs ck H bs bs',
      (forall x, IsVar Γ x -> In x xs) ->
      wx_clock Γ ck ->
      sem_clock H bs ck bs' ->
      sem_clock (FEnv.restrict H xs) bs ck bs'.
  Proof.
    intros * Var Hwx Hsem.
    eapply sem_clock_refines'; [eauto| |eauto].
    intros ?? Hinm Hvar.
    eapply sem_var_restrict; eauto.
  Qed.

  Fact var_history_restrict : forall H Γ,
      FEnv.Equiv (@EqSt _) (var_history (restrict H Γ))
        (FEnv.restrict (var_history H) (List.map fst Γ)).
  Proof.
    unfold var_history, restrict, FEnv.restrict.
    intros * ?.
    cases_eqn Eq; try reflexivity.
    1,2:exfalso.
    1,2:(take (existsb _ _ = true) and apply existsb_exists in it as (?&In&Eq1);
         rewrite equiv_decb_equiv in Eq1; inv Eq1).
    1,2:(take (existsb _ _ = false) and eapply existsb_Forall, forallb_Forall in it).
    - rewrite vars_of_senv_Var in In. inv In; simpl_In. simpl_Forall. rewrite equiv_decb_refl in it; inv it.
    - simpl_In. eapply Forall_forall in it. 2:eapply vars_of_senv_Var; econstructor; eauto using In_InMembers.
      rewrite equiv_decb_refl in it; inv it.
  Qed.

  Fact sem_clock_var_history_restrict : forall Γ ck H bs bs',
      wx_clock Γ ck ->
      sem_clock (var_history H) bs ck bs' ->
      sem_clock (var_history (restrict H Γ)) bs ck bs'.
  Proof.
    intros * Var Sem.
    rewrite var_history_restrict.
    eapply sem_clock_restrict; eauto.
    intros * V. inv V. now apply fst_InMembers.
  Qed.

  Fact sem_exp_restrict {PSyn prefs} : forall (G : @global PSyn prefs) Γ H b e vs,
      wx_exp Γ e ->
      sem_exp G H b e vs ->
      sem_exp G (restrict H Γ) b e vs.
  Proof with eauto with datatypes.
    induction e using exp_ind2; intros vs Hwt Hsem; inv Hwt; inv Hsem;
      econstructor; eauto; simpl_Forall; eauto.
    1-4:(eapply sem_var_restrict; eauto; try eapply vars_of_senv_Var; try eapply vars_of_senv_Last; eauto).
    1-3:(eapply Forall2Brs_impl_In; [|eauto]; intros ?? Hin Hse;
         simpl_Exists; simpl_Forall; eauto).
    specialize (H8 _ eq_refl). simpl_Forall; eauto.
  Qed.

  Lemma sem_equation_restrict {PSyn prefs} : forall (G : @global PSyn prefs) Γ H b eq,
      wx_equation Γ eq ->
      sem_equation G H b eq ->
      sem_equation G (restrict H Γ) b eq.
  Proof with eauto with datatypes.
    intros ???? [xs es] Hwc Hsem.
    destruct Hwc as (?&?). inv Hsem.
    econstructor. instantiate (1:=ss).
    + simpl_Forall; eauto using sem_exp_restrict.
    + simpl_Forall; eauto.
      eapply sem_var_restrict; eauto. eapply vars_of_senv_Var; eauto.
  Qed.

  Fact sem_transitions_restrict {PSyn prefs} : forall (G : @global PSyn prefs) Γ H b trans default stres,
      Forall (fun '(e, _) => wx_exp Γ e) trans ->
      sem_transitions G H b trans default stres ->
      sem_transitions G (restrict H Γ) b trans default stres.
  Proof with eauto.
    induction trans; intros * Hwx Hsem; inv Hwx; inv Hsem;
      econstructor; eauto using sem_exp_restrict.
  Qed.

  Definition vars_of_locs (locs : list (ident * (type * clock * ident * option (exp * ident)))) :=
    vars_of_senv (senv_of_locs locs).

  Fact vars_of_locs_Var : forall locs x,
      In (Var x) (vars_of_locs locs) <-> IsVar (senv_of_locs locs) x.
  Proof.
    intros. apply vars_of_senv_Var.
  Qed.

  Fact vars_of_locs_Last : forall locs x,
      In (Last x) (vars_of_locs locs) <-> IsLast (senv_of_locs locs) x.
  Proof.
    intros. apply vars_of_senv_Last.
  Qed.

  Lemma sem_scope_restrict {A} (wx_block : _ -> _ -> Prop) (sem_block : _ -> _ -> Prop) {PSyn prefs} (G: @global PSyn prefs) :
    forall Γ Hi bs locs (blks : A),
      (forall Γ Hi Hi',
          wx_block Γ blks ->
          sem_block Hi blks ->
          FEnv.Equiv (@EqSt _) Hi' (restrict Hi Γ) ->
          sem_block Hi' blks) ->
      wx_scope wx_block Γ (Scope locs blks) ->
      sem_scope (fun Hi' => sem_exp G Hi' bs) sem_block Hi bs (Scope locs blks) ->
      sem_scope (fun Hi' => sem_exp G Hi' bs) sem_block (restrict Hi Γ) bs (Scope locs blks).
  Proof.
    intros * Hp Hwx Hsem; inv Hwx; inv Hsem.
    assert (FEnv.Equiv (@EqSt _) (restrict (Hi + Hi') (Γ ++ senv_of_locs locs))
              (restrict Hi Γ + Hi')) as Heq.
    { simpl. symmetry.
      intros ?. unfold FEnv.union, restrict, FEnv.restrict, vars_of_senv.
      rewrite <-flat_map_app, existsb_app.
      destruct (Hi' x) eqn:HHi', (existsb _ _) eqn:Hex; simpl; try reflexivity.
      - replace (existsb _ _) with true; [constructor; reflexivity|].
        symmetry. rewrite existsb_exists. do 2 esplit; [|eapply equiv_decb_refl].
        apply FEnv.find_In in HHi'.
        destruct x; [apply H1, vars_of_locs_Var in HHi'|apply H1, vars_of_locs_Last in HHi']; auto.
      - replace (existsb _ _) with false. constructor.
        symmetry. rewrite existsb_Forall, forallb_Forall. simpl_Forall.
        apply Bool.negb_true_iff, not_equiv_decb_equiv. intros Eq; inv Eq.
        apply FEnv.not_find_In in HHi'.
        destruct x; [apply vars_of_locs_Var, H1 in H; eauto|apply vars_of_locs_Last, H1 in H; eauto].
    }
    eapply Sscope with (Hi':=Hi'); eauto.
    - intros * Hin. edestruct H6 as (?&?&?&?&?&?&?); eauto. simpl_Forall.
      repeat (esplit; eauto).
      eapply sem_exp_restrict in H. 2:eauto.
      eapply sem_exp_morph; eauto; try reflexivity.
    - eapply Hp in H7; eauto. now symmetry.
  Qed.

  Lemma sem_block_restrict {PSyn prefs} : forall (G: @global PSyn prefs) blk Γ H b,
      wx_block Γ blk ->
      sem_block G H b blk ->
      sem_block G (restrict H Γ) b blk.
  Proof.
    induction blk using block_ind2; intros * Hwc Hsem; inv Hwc; inv Hsem.
    - (* equation *)
      econstructor.
      eapply sem_equation_restrict; eauto.
    - (* reset *)
      econstructor; eauto using sem_exp_restrict.
      intros k; specialize (H10 k).
      rewrite Forall_forall in *. intros ? Hin.
      eapply sem_block_refines; try eapply H; eauto.
      setoid_rewrite <-FEnv.restrict_map; auto using EqStrel_Reflexive.
      reflexivity.
    - (* switch *)
      econstructor; eauto using sem_exp_restrict.
      simpl_Forall. do 2 esplit.
      + intros ?? Hfind. apply FEnv.restrict_find_inv in Hfind as (Hin&Hfind).
        eapply H2 in Hfind as (?&Hwhen&Hfind').
        do 2 esplit; eauto using FEnv.restrict_find.
      + destruct b0. repeat inv_branch'. econstructor.
        simpl_Forall; eauto.
    - (* automaton (weak transitions) *)
      econstructor; eauto.
      + eapply sem_clock_var_history_restrict; eauto.
      + eapply sem_transitions_restrict; eauto. simpl_Forall; auto.
      + simpl_Forall. specialize (H16 k); destruct_conjs.
        esplit; split.
        * intros ?? Hfind. apply FEnv.restrict_find_inv in Hfind as (Hin&Hfind).
          eapply H2 in Hfind as (?&Hwhen&Hfind').
          do 2 esplit; eauto using FEnv.restrict_find.
        * repeat inv_branch'. constructor.
          destruct s; destruct_conjs. eapply sem_scope_restrict; eauto.
          intros; split; simpl_Forall; destruct_conjs.
          -- eapply sem_block_morph, H; eauto; try reflexivity. now symmetry.
          -- eapply sem_transitions_morph, sem_transitions_restrict; eauto; try reflexivity.
             now symmetry.
    - (* automaton (strong transitions) *)
      econstructor; eauto.
      + eapply sem_clock_var_history_restrict; eauto.
      + simpl_Forall. specialize (H15 k); destruct_conjs.
        esplit; split.
        * intros ?? Hfind. apply FEnv.restrict_find_inv in Hfind as (Hin&Hfind).
          eapply H2 in Hfind as (?&Hwhen&Hfind').
          do 2 esplit; eauto using FEnv.restrict_find.
        * repeat inv_branch'. constructor. eapply sem_transitions_restrict; eauto.
      + simpl_Forall. specialize (H16 k); destruct_conjs.
        esplit; split.
        * intros ?? Hfind. apply FEnv.restrict_find_inv in Hfind as (Hin&Hfind).
          eapply H2 in Hfind as (?&Hwhen&Hfind').
          do 2 esplit; eauto using FEnv.restrict_find.
        * repeat inv_branch'. constructor.
          destruct s; destruct_conjs. eapply sem_scope_restrict; eauto.
          intros; simpl_Forall.
          -- eapply sem_block_morph, H; eauto; try reflexivity. now symmetry.
    - (* locals *)
      constructor. eapply sem_scope_restrict; eauto.
      intros; simpl_Forall.
      eapply sem_block_morph, H; eauto; try reflexivity. now symmetry.
  Qed.

  (** ** Alignment *)

  (** fby keeps the synchronization *)

  Lemma ac_fby1 {A} :
    forall xs ys rs,
      @fby A xs ys rs -> abstract_clock xs ≡ abstract_clock rs.
  Proof.
    cofix Cofix.
    intros * Hfby.
    unfold_Stv xs; inv Hfby; econstructor; simpl; eauto.
    clear - H3. revert H3. revert y xs ys0 rs0.
    cofix Cofix.
    intros * Hfby1.
    unfold_Stv xs; inv Hfby1; econstructor; simpl; eauto.
  Qed.

  Lemma ac_fby2 {A} :
    forall xs ys rs,
      @fby A xs ys rs -> abstract_clock ys ≡ abstract_clock rs.
  Proof.
    cofix Cofix. intros * Hfby.
    unfold_Stv ys; inv Hfby; econstructor; simpl; eauto.
    clear - H3. revert H3. revert v ys xs0 rs0.
    cofix Cofix. intros * Hfby1.
    unfold_Stv ys; inv Hfby1; econstructor; simpl; eauto.
  Qed.

  Lemma fby_aligned {A} : forall bs (xs ys zs: Stream (synchronous A)),
      fby xs ys zs ->
      (aligned xs bs \/ aligned ys bs \/ aligned zs bs) ->
      (aligned xs bs /\ aligned ys bs /\ aligned zs bs).
  Proof with eauto.
    intros bs xs ys zs Hfby.
    specialize (ac_fby1 _ _ _ Hfby) as Hac1. specialize (ac_fby2 _ _ _ Hfby) as Hac2.
    specialize (ac_aligned xs) as Hs1. specialize (ac_aligned ys) as Hs2. specialize (ac_aligned zs) as Hs3.
    intros [Hsync|[Hsync|Hsync]]; repeat split; auto;
      match goal with
      | Hal: aligned ?xs bs, Hal2: aligned ?xs (abstract_clock ?xs) |- _ =>
          eapply aligned_EqSt in Hal2; eauto; rewrite Hal2;
          (rewrite Hac1||rewrite Hac2||idtac); eauto;
          ((now rewrite <-Hac1)||(now rewrite <-Hac2))
      end.
  Qed.

  Lemma ac_arrow1 : forall xs ys rs,
      arrow xs ys rs -> abstract_clock xs ≡ abstract_clock rs.
  Proof.
    cofix Cofix.
    intros * Harrow.
    unfold_Stv xs; inv Harrow; econstructor; simpl; eauto.
    clear - H3. revert H3. revert xs ys0 rs0.
    cofix Cofix.
    intros * Harrow1.
    unfold_Stv xs; inv Harrow1; econstructor; simpl; eauto.
  Qed.

  Lemma ac_arrow2 : forall xs ys rs,
      arrow xs ys rs -> abstract_clock ys ≡ abstract_clock rs.
  Proof.
    cofix Cofix.
    intros * Harrow.
    unfold_Stv ys; inv Harrow; econstructor; simpl; eauto.
    clear - H3. revert H3. revert xs0 ys rs0.
    cofix Cofix.
    intros * Harrow1.
    unfold_Stv ys; inv Harrow1; econstructor; simpl; eauto.
  Qed.

  Lemma arrow_aligned : forall bs xs ys zs,
      arrow xs ys zs ->
      (aligned xs bs \/ aligned ys bs \/ aligned zs bs) ->
      (aligned xs bs /\ aligned ys bs /\ aligned zs bs).
  Proof with eauto.
    intros bs xs ys zs Hfby.
    specialize (ac_arrow1 _ _ _ Hfby) as Hac1. specialize (ac_arrow2 _ _ _ Hfby) as Hac2.
    specialize (ac_aligned xs) as Hs1. specialize (ac_aligned ys) as Hs2. specialize (ac_aligned zs) as Hs3.
    intros [Hsync|[Hsync|Hsync]]; repeat split; auto;
      match goal with
      | Hal: aligned ?xs bs, Hal2: aligned ?xs (abstract_clock ?xs) |- _ =>
          eapply aligned_EqSt in Hal2; eauto; rewrite Hal2;
          (rewrite Hac1||rewrite Hac2||idtac); eauto;
          ((now rewrite <-Hac1)||(now rewrite <-Hac2))
      end.
  Qed.

  (** ** Typing of the state machines state stream *)

  Lemma sem_transitions_wt_state {PSyn prefs A} (G : @global PSyn prefs) (states : list ((enumtag * ident) * A)) :
    forall Hi bs trans default stres,
      Permutation.Permutation (List.map fst (List.map fst states)) (seq 0 (Datatypes.length states)) ->
      Forall (fun '(_, (t, _)) => InMembers t (List.map fst states)) trans ->
      In (fst default) (seq 0 (Datatypes.length states)) ->
      sem_transitions G Hi bs trans default stres ->
      SForall (fun v => match v with present (e, _) => e < length states | _ => True end) stres.
  Proof.
    induction trans; intros * Hperm Hwt1 Hwt2 Hsem; inv Hwt1; inv Hsem.
    - apply SForall_forall; intros.
      apply eqst_ntheq with (n:=n) in H0. setoid_rewrite Str_nth_map in H0.
      eapply eq_ind with (P:=fun x => match x with absent => True | present (e0, _) => _ end).
      2:symmetry; apply H0. destruct (bs # n); simpl; auto.
      destruct default0. apply in_seq in Hwt2; simpl in *. lia.
    - apply IHtrans in H8; auto.
      apply SForall_forall; intros.
      apply eqst_ntheq with (n:=n) in H11. rewrite choose_first_nth in H11. setoid_rewrite Str_nth_map in H11.
      apply SForall_forall with (n:=n) in H8.
      eapply eq_ind with (P:=fun x => match x with absent => True | present (e0, _) => _ end).
      2:symmetry; apply H11. destruct (bs' # n); simpl; auto.
      rewrite fst_InMembers, Hperm in H1. apply in_seq in H1. lia.
  Qed.

  Fact fby1_SForall {A} (P : _ -> Prop) : forall n v xs ys zs,
      @fby1 A v xs ys zs ->
      P (present v) ->
      SForall P xs ->
      (forall m, m < n -> P (ys # m)) ->
      P zs # n.
  Proof.
    induction n; intros * Hfby Hp Hf Hlt; inv Hfby; inv Hf.
    1,2:rewrite Str_nth_0; auto.
    1,2:rewrite Str_nth_S_tl; simpl.
    - eapply IHn; eauto.
      intros m Hlt'. specialize (Hlt (S m)).
      rewrite Str_nth_S_tl in Hlt. apply Hlt; lia.
    - eapply IHn; eauto.
      + specialize (Hlt 0). apply Hlt. lia.
      + intros m Hlt'. specialize (Hlt (S m)).
        rewrite Str_nth_S_tl in Hlt. apply Hlt; lia.
  Qed.

  Corollary fby_SForall {A} (P : _ -> Prop) : forall n xs ys zs,
      @fby A xs ys zs ->
      SForall P xs ->
      (forall m, m < n -> P (ys # m)) ->
      P zs # n.
  Proof.
    induction n; intros * Hfby Hf Hlt; inv Hfby; inv Hf.
    1,2:rewrite Str_nth_0; auto.
    1,2:rewrite Str_nth_S_tl; simpl.
    - eapply IHn; eauto.
      intros m Hlt'. specialize (Hlt (S m)).
      rewrite Str_nth_S_tl in Hlt. apply Hlt; lia.
    - eapply fby1_SForall; eauto.
      + specialize (Hlt 0). apply Hlt. lia.
      + intros m Hlt'. specialize (Hlt (S m)).
        rewrite Str_nth_S_tl in Hlt. apply Hlt; lia.
  Qed.

  Corollary sem_automaton_wt_state1 {PSyn prefs A} (G : @global PSyn prefs) (states : list ((enumtag * ident) * branch (list transition * scope (A * list transition)))) :
    forall Hi bs bs' ini oth stres0 stres1 stres,
      Permutation.Permutation (List.map fst (List.map fst states)) (seq 0 (Datatypes.length states)) ->
      Forall (fun '(_, t) => InMembers t (List.map fst states)) ini ->
      In oth (seq 0 (Datatypes.length states)) ->
      Forall (fun '(_, Branch _ (_, Scope _ (_, trans))) =>
                Forall (fun '(e, (t, _)) => InMembers t (List.map fst states)) trans) states ->
      sem_transitions G Hi bs' (List.map (fun '(e, t) => (e, (t, false))) ini) (oth, false) stres0 ->
      fby stres0 stres1 stres ->
      Forall (fun '((sel, _), Branch _ (_, Scope _ (_, trans))) =>
               forall k, exists Hik,
                 (let bik := fselectb sel k stres bs in
                  sem_transitions G Hik bik trans
                    (sel, false) (fselect absent sel k stres stres1))) states ->
      SForall (fun v => match v with present (e, _) => e < length states | _ => True end) stres.
  Proof.
    intros * Hperm Hwtini Hwtoth Hwtst Hsemini Hfby Hsemst.
    eapply sem_transitions_wt_state in Hsemini as Hwt0; eauto.
    2:simpl_Forall; auto.
    assert (Forall (fun state => forall k, SForall (fun v => match v with present (e, _) => e < length states | _ => True end)
                                           (fselect absent (fst (fst state)) k stres stres1)) states) as Hwt1.
    { simpl_Forall. destruct b as [?(?&[?(?&?)])]. specialize (Hsemst k); destruct_conjs.
      eapply sem_transitions_wt_state in H0; eauto.
      rewrite <-Hperm; auto. solve_In. }
    clear - Hperm Hwt0 Hwt1 Hfby.
    apply SForall_forall; intros n.
    induction n using Wf_nat.lt_wf_ind.
    apply Wf_nat.lt_wf_ind with (n:=n).
    intros n' Hrec.
    eapply fby_SForall; eauto.
    intros * Hlt. specialize (Hrec _ Hlt).
    destruct (stres # m) as [|(?&?)] eqn:Hres.
    - apply ac_fby2, eqst_ntheq with (n:=m) in Hfby.
      rewrite 2 ac_nth in Hfby. rewrite Hres in Hfby.
      destruct (stres1 # m) eqn:Hres1; try congruence.
      eapply eq_ind with (P:=fun x => match x with absent => True | present (e0, _) => _ end).
      2:symmetry; apply Hres1. simpl; auto.
    - eapply eq_ind with (P:=fun x => match x with absent => True | present (e0, _) => _ end) in Hrec; [|eauto].
      simpl in *.
      assert (In e (List.map fst (List.map fst states))) as Hin.
      { rewrite Hperm. apply in_seq. lia. }
      simpl_In. simpl_Forall.
      specialize (Hwt1 ((count (fwhenb e (stres_res stres) (stres_st stres))) # m)).
      apply SForall_forall with (n:=m) in Hwt1.
      unfold fselect in Hwt1. rewrite mask_nth, Nat.eqb_refl, fwhen_nth in Hwt1.
      unfold stres_st in Hwt1. rewrite Str_nth_map, Hres, equiv_decb_refl in Hwt1.
      auto.
  Qed.

  Corollary sem_automaton_wt_state2 {PSyn prefs A} (G : @global PSyn prefs) (states : list ((enumtag * ident) * branch (list transition * scope (A * list transition)))) :
    forall bs bs' ini stres1 stres,
      Permutation.Permutation (List.map fst (List.map fst states)) (seq 0 (Datatypes.length states)) ->
      In ini (seq 0 (Datatypes.length states)) ->
      Forall (fun '(_, Branch _ (trans, _)) =>
                Forall (fun '(e, (t, _)) => InMembers t (List.map fst states)) trans) states ->
      fby (const_stres bs' (ini, false)) stres1 stres ->
      Forall (fun '((sel, _), Branch _ (trans, _)) =>
               forall k, exists Hik,
                 (let bik := fselectb sel k stres bs in
                  sem_transitions G Hik bik trans
                    (sel, false) (fselect absent sel k stres stres1))) states ->
      SForall (fun v => match v with present (e, _) => e < length states | _ => True end) stres.
  Proof.
    intros * Hperm Hwtoth Hwtst Hfby Hsemst.
    assert (SForall (fun s : synchronous (nat * bool) => match s with
                                                 | absent => True
                                                 | present (e, _) => e < length states
                                                 end) (const_stres bs' (ini, false))) as Hwt0.
    { apply SForall_forall. intros.
      unfold const_stres.
      rewrite Str_nth_map. destruct (bs' # n); simpl; auto.
      apply in_seq in Hwtoth. lia. }
    assert (Forall (fun state => forall k, SForall (fun v => match v with present (e, _) => e < length states | _ => True end)
                                           (fselect absent (fst (fst state)) k stres stres1)) states) as Hwt1.
    { simpl_Forall. destruct b as [?(?&[?(?&?)])]. specialize (Hsemst k); destruct_conjs.
      eapply sem_transitions_wt_state in H0; eauto.
      rewrite <-Hperm; auto. solve_In. }
    clear - Hperm Hwt0 Hwt1 Hfby.
    apply SForall_forall; intros n.
    induction n using Wf_nat.lt_wf_ind.
    apply Wf_nat.lt_wf_ind with (n:=n).
    intros n' Hrec.
    eapply fby_SForall; eauto.
    intros * Hlt. specialize (Hrec _ Hlt).
    destruct (stres # m) as [|(?&?)] eqn:Hres.
    - apply ac_fby2, eqst_ntheq with (n:=m) in Hfby.
      rewrite 2 ac_nth in Hfby. rewrite Hres in Hfby.
      destruct (stres1 # m) eqn:Hres1; try congruence.
    - assert (In n0 (List.map fst (List.map fst states))) as Hin.
      { rewrite Hperm. apply in_seq. lia. }
      simpl_In. simpl_Forall.
      specialize (Hwt1 ((count (fwhenb n0 (stres_res stres) (stres_st stres))) # m)).
      apply SForall_forall with (n:=m) in Hwt1.
      unfold fselect in Hwt1. rewrite mask_nth, Nat.eqb_refl, fwhen_nth in Hwt1.
      eapply eq_ind with (P:=fun x => match x with absent => True | present (e0, _) => _ end) in Hwt1.
      2:{ unfold stres_st. rewrite Str_nth_map. setoid_rewrite Hres. rewrite equiv_decb_refl. reflexivity. }
      assumption.
  Qed.

  Corollary sem_automaton_wt_state3 {PSyn prefs A} (G : @global PSyn prefs) (states : list ((enumtag * ident) * branch (list transition * scope (A * list transition)))) :
    forall bs bs' ini stres1 stres,
      Permutation.Permutation (List.map fst (List.map fst states)) (seq 0 (Datatypes.length states)) ->
      In ini (seq 0 (Datatypes.length states)) ->
      Forall (fun '(_, Branch _ (trans, _)) =>
                Forall (fun '(e, (t, _)) => InMembers t (List.map fst states)) trans) states ->
      fby (const_stres bs' (ini, false)) stres1 stres ->
      Forall (fun '((sel, _), Branch _ (trans, _)) =>
               forall k, exists Hik,
                 (let bik := fselectb sel k stres bs in
                  sem_transitions G Hik bik trans
                    (sel, false) (fselect absent sel k stres stres1))) states ->
      SForall (fun v => match v with present (e, _) => e < length states | _ => True end) stres1.
  Proof.
    intros * Hperm Hwtoth Hwtst Hfby Hsemst.
    assert (SForall (fun s : synchronous (nat * bool) => match s with
                                                 | absent => True
                                                 | present (e, _) => e < length states
                                                 end) (const_stres bs' (ini, false))) as Hwt0.
    { apply SForall_forall. intros.
      unfold const_stres.
      rewrite Str_nth_map. destruct (bs' # n); simpl; auto.
      apply in_seq in Hwtoth. lia. }
    assert (Forall (fun state => forall k, SForall (fun v => match v with present (e, _) => e < length states | _ => True end)
                                           (fselect absent (fst (fst state)) k stres stres1)) states) as Hwt1.
    { simpl_Forall. destruct b as [?(?&[?(?&?)])]; destruct_conjs. specialize (Hsemst k); destruct_conjs.
      eapply sem_transitions_wt_state in H0; eauto.
      rewrite <-Hperm; auto. solve_In. }
    eapply sem_automaton_wt_state2 in Hfby as Hwt2; eauto.
    apply SForall_forall; intros n. eapply SForall_forall with (n:=n) in Hwt2.
    apply ac_fby2, eqst_ntheq with (n:=n) in Hfby. rewrite 2 ac_nth in Hfby.
    destruct (stres1 # n) eqn:Hstres1, (stres # n) eqn:Hstres; auto; try congruence.
    destruct v0, v.
    assert (In n0 (List.map fst (List.map fst states))) as Hin.
    { rewrite Hperm. apply in_seq. lia. }
    simpl_In. simpl_Forall.
    specialize (Hwt1 ((count (fwhenb n0 (stres_res stres) (stres_st stres))) # n)).
    apply SForall_forall with (n:=n) in Hwt1.
    unfold fselect in Hwt1. rewrite mask_nth, Nat.eqb_refl, fwhen_nth in Hwt1.
    eapply eq_ind with (P:=fun x => match x with absent => True | present (e0, _) => _ end) in Hwt1.
    2:{ unfold stres_st. rewrite Str_nth_map. setoid_rewrite Hstres. rewrite equiv_decb_refl. reflexivity. }
    rewrite Hstres1 in Hwt1.
    assumption.
  Qed.

End LSEMANTICS.

Module LSemanticsFun
       (Ids   : IDS)
       (Op    : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks   : CLOCKS        Ids Op OpAux)
       (Senv  : STATICENV     Ids Op OpAux Cks)
       (Syn   : LSYNTAX       Ids Op OpAux Cks Senv)
       (Lord  : LORDERED      Ids Op OpAux Cks Senv Syn)
       (Str   : COINDSTREAMS  Ids Op OpAux Cks)
<: LSEMANTICS Ids Op OpAux Cks Senv Syn Lord Str.
  Include LSEMANTICS Ids Op OpAux Cks Senv Syn Lord Str.
End LSemanticsFun.
