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

  Definition history : Type := @history var_last.
  Definition var_history (H : history) : @Str.history ident :=
    fun x => H (Var x).

  Section NodeSemantics.
    Context {PSyn : list decl -> block -> Prop}.
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

    Definition dom (H : history) Γ :=
      (forall x, FEnv.In (Var x) H <-> IsVar Γ x) /\ (forall x, FEnv.In (Last x) H <-> IsLast Γ x).

    Definition dom_ub (H : history) Γ :=
      (forall x, FEnv.In (Var x) H -> IsVar Γ x) /\ (forall x, FEnv.In (Last x) H -> IsLast Γ x).

    Definition dom_lb (H : history) Γ :=
      (forall x, IsVar Γ x -> FEnv.In (Var x) H) /\ (forall x, IsLast Γ x -> FEnv.In (Last x) H).

    Section sem_scope.
      Context {A : Type}.

      Variable sem_exp : history -> Stream bool -> exp -> list (Stream svalue) -> Prop.

      Inductive sem_last_decl (Hi Hi' : history) (bs : Stream bool) : (ident * (type * clock * ident * option (exp * ident))) -> Prop :=
      | sem_nolast : forall x ty ck cx,
          sem_last_decl Hi Hi' bs (x, (ty, ck, cx, None))
      | sem_last : forall x ty ck cx e0 clx vs0 vs1 vs,
          sem_exp (Hi + Hi') bs e0 [vs0] ->
          sem_var Hi' (Var x) vs1 ->
          fby vs0 vs1 vs ->
          sem_var Hi' (Last x) vs ->
          sem_last_decl Hi Hi' bs (x, (ty, ck, cx, Some (e0, clx))).

      Variable sem_block : history -> A -> Prop.

      Inductive sem_scope : history -> Stream bool -> (scope A) -> Prop :=
      | Sscope : forall Hi Hi' bs locs blks,
          (* Domain of the internal history *)
          dom Hi' (senv_of_decls locs) ->

          (* Last declarations *)
          Forall (sem_last_decl Hi Hi' bs) locs ->

          sem_block (Hi + Hi') blks ->
          sem_scope Hi bs (Scope locs blks).
    End sem_scope.

    Section sem_branch.
      Context {A : Type}.

      Variable sem_block : A -> Prop.

      Variable must_def : ident -> Prop.
      Variable is_def : ident -> A -> Prop.

      Inductive sem_branch : history -> (branch A) -> Prop :=
      | Sbranch : forall Hi caus blks,
          sem_block blks ->
          (* completion *)
          (forall x, must_def x -> ~is_def x blks -> exists vs, sem_var Hi (Last x) vs /\ sem_var Hi (Var x) vs) ->
          sem_branch Hi (Branch caus blks).
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
                           sem_branch (Forall (sem_block Hi' bi))
                             (fun x => Is_defined_in x (Bswitch ec branches))
                             (fun x => List.Exists (Is_defined_in x))
                             Hi' (snd blks)) branches ->
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
                                     sem_scope sem_exp
                                       (fun Hi' blks =>
                                          Forall (sem_block Hi' bik) (fst blks)
                                          /\ sem_transitions Hi' bik (snd blks) (tag, false) (fselect absent tag k stres stres1)
                                       ) Hik bik (snd blks))
                                  (fun x => Is_defined_in x (Bauto Weak ck (ini, oth) states))
                                  (fun x '(_, s) => Is_defined_in_scope (fun '(blks, _) => List.Exists (Is_defined_in x) blks) x s)
                                  Hik (snd state)
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
                                     sem_transitions Hik bik (fst blks) (tag, false) (fselect absent tag k stres stres1))
                                  (fun x => Is_defined_in x (Bauto Strong ck ([], ini) states))
                                  (fun x '(_, s) => Is_defined_in_scope (fun '(blks, _) => List.Exists (Is_defined_in x) blks) x s)
                                  Hik (snd state)
               ) states ->
        Forall (fun state =>
                  let tag := fst (fst state) in
                  forall k, exists Hik, select_hist tag k stres1 H Hik
                              /\ let bik := fselectb tag k stres1 bs in
                                sem_branch
                                  (fun blks =>
                                     sem_scope sem_exp
                                       (fun Hi' blks => Forall (sem_block Hi' bik) (fst blks))
                                       Hik bik (snd blks))
                                  (fun x => Is_defined_in x (Bauto Strong ck ([], ini) states))
                                  (fun x '(_, s) => Is_defined_in_scope (fun '(blks, _) => List.Exists (Is_defined_in x) blks) x s)
                                  Hik (snd state)
               ) states ->
        sem_block H bs (Bauto Strong ck ([], ini) states)

    | Slocal:
      forall Hi bs scope,
        sem_scope sem_exp (fun Hi' => Forall (sem_block Hi' bs)) Hi bs scope ->
        sem_block Hi bs (Blocal scope)

    with sem_node: ident -> list (Stream svalue) -> list (Stream svalue) -> Prop :=
    | Snode:
      forall f ss os n H,
          find_node f G = Some n ->
          Forall2 (fun x => sem_var H (Var x)) (List.map fst n.(n_in)) ss ->
          Forall2 (fun x => sem_var H (Var x)) (List.map fst n.(n_out)) os ->
          let bs := clocks_of ss in
          Forall (sem_last_decl sem_exp (FEnv.empty _) H bs) n.(n_out) ->
          sem_block H bs n.(n_block) ->
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
    | H:sem_branch _ _ _ _ _ |- _ => inv H
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

  Add Parametric Morphism : (@sem_var var_last)
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

  Add Parametric Morphism {PSyn prefs} (G: @global PSyn prefs) : (sem_last_decl (sem_exp G))
      with signature history_equiv ==> history_equiv ==> @EqSt bool ==> eq ==> Basics.impl
        as sem_last_decls_morph.
  Proof.
    intros Hi1 Hi2 EH Hi1' Hi2' EH' ?? Eb ? Hsem.
    inv Hsem; econstructor; eauto.
    2-3:now rewrite <-EH'.
    eapply sem_exp_morph; eauto. 2:reflexivity.
    apply FEnv.union_Equiv; auto.
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
      + simpl_Forall. take (sem_branch _ _ _ _ _) and inv it.
        do 2 esplit. 2:econstructor; eauto.
        * rewrite <-EH; eauto.
        * simpl_Forall. eapply H; eauto. reflexivity. now rewrite <-Eb.
    - econstructor; eauto.
      + rewrite <-EH, <-Eb; eauto.
      + now rewrite <-EH.
      + simpl_Forall. specialize (H11 k) as (Hik&?). destruct_conjs.
        inv_branch. inv_scope.
        exists Hik. split; [|econstructor; eauto; econstructor; eauto; repeat split].
        * now rewrite <-EH.
        * simpl_Forall. now rewrite <-Eb.
        * simpl_Forall. eapply H; eauto. reflexivity. now rewrite <-Eb.
        * now rewrite <-Eb.
    - econstructor; eauto.
      + rewrite <-EH, <-Eb; eauto.
      + simpl_Forall. specialize (H10 k) as (Hik&?). destruct_conjs.
        exists Hik. split.
        * now rewrite <-EH.
        * inv_branch. constructor; auto. now rewrite <-Eb.
      + simpl_Forall. specialize (H11 k) as (Hik&?). destruct_conjs.
        inv_branch. inv_scope.
        exists Hik. split; [|econstructor; eauto; econstructor; eauto; repeat split]; eauto.
        * now rewrite <-EH.
        * simpl_Forall. now rewrite <-Eb.
        * simpl_Forall. eapply H; eauto. reflexivity. now rewrite <-Eb.
    - constructor. inv_scope.
      eapply Sscope with (Hi':=Hi'); eauto.
      + simpl_Forall. now rewrite <-EH, <-Eb.
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
    + simpl_Forall. take (sem_last_decl _ _ _ _ _) and inv it; econstructor; eauto.
      subst bs. now rewrite <-Exss.
    + now rewrite <-Exss.
  Qed.

  Ltac inv_scope' := (Syn.inv_scope || inv_scope).
  Ltac inv_branch' := (Syn.inv_branch || inv_branch).
  Ltac inv_block' := (Syn.inv_block || inv_block).

  (** Custom induction schemes *)

  Section sem_exp_ind2.
    Context {prefs PSyn} (G: @global prefs PSyn).

    Variable P_exp : history -> Stream bool -> exp -> list (Stream svalue) -> Prop.
    Variable P_equation : history -> Stream bool -> equation -> Prop.
    Variable P_transitions : history -> Stream bool -> list (exp * (enumtag * bool)) -> (enumtag * bool) -> Stream (synchronous (enumtag * bool)) -> Prop.
    Variable P_block : history -> Stream bool -> block -> Prop.
    Variable P_node : ident -> list (Stream svalue) -> list (Stream svalue) -> Prop.

    Hypothesis ConstCase:
      forall H b c cs,
        cs ≡ const b c ->
        P_exp H b (Econst c) [cs].

    Hypothesis EnumCase:
      forall H b k ty es,
        es ≡ enum b k ->
        P_exp H b (Eenum k ty) [es].

    Hypothesis VarCase:
      forall H b x s ann,
        sem_var H (Var x) s ->
        P_exp H b (Evar x ann) [s].

    Hypothesis LastCase:
      forall H b x s ann,
        sem_var H (Last x) s ->
        P_exp H b (Elast x ann) [s].

    Hypothesis UnopCase:
      forall H b e op ty s o ann,
        sem_exp G H b e [s] ->
        P_exp H b e [s] ->
        typeof e = [ty] ->
        lift1 op ty s o ->
        P_exp H b (Eunop op e ann) [o].

    Hypothesis BinopCase:
      forall H b e1 e2 op ty1 ty2 s1 s2 o ann,
        sem_exp G H b e1 [s1] ->
        P_exp H b e1 [s1] ->
        sem_exp G H b e2 [s2] ->
        P_exp H b e2 [s2] ->
        typeof e1 = [ty1] ->
        typeof e2 = [ty2] ->
        lift2 op ty1 ty2 s1 s2 o ->
        P_exp H b (Ebinop op e1 e2 ann) [o].

    Hypothesis ExtcallCase:
      forall H b f es tyout ck tyins ss vs,
        Forall2 (fun cty ty => cty = Tprimitive ty) (typesof es) tyins ->
        Forall2 (sem_exp G H b) es ss ->
        Forall2 (P_exp H b) es ss ->
        liftn (fun ss => sem_extern f tyins ss tyout) (concat ss) vs ->
        P_exp  H b (Eextcall f es (tyout, ck)) [vs].

    Hypothesis FbyCase:
      forall H b e0s es anns s0ss sss os,
        Forall2 (sem_exp G H b) e0s s0ss ->
        Forall2 (P_exp H b) e0s s0ss ->
        Forall2 (sem_exp G H b) es sss ->
        Forall2 (P_exp H b) es sss ->
        Forall3 fby (concat s0ss) (concat sss) os ->
        P_exp H b (Efby e0s es anns) os.

    Hypothesis ArrowCase:
      forall H b e0s es anns s0ss sss os,
        Forall2 (sem_exp G H b) e0s s0ss ->
        Forall2 (P_exp H b) e0s s0ss ->
        Forall2 (sem_exp G H b) es sss ->
        Forall2 (P_exp H b) es sss ->
        Forall3 arrow (concat s0ss) (concat sss) os ->
        P_exp H b (Earrow e0s es anns) os.

    Hypothesis WhenCase:
      forall H b x tx s k es lann ss os,
        Forall2 (sem_exp G H b) es ss ->
        Forall2 (P_exp H b) es ss ->
        sem_var H (Var x) s ->
        Forall2 (fun s' => when k s' s) (concat ss) os ->
        P_exp H b (Ewhen es (x, tx) k lann) os.

    Hypothesis MergeCase:
      forall H b x tx s es lann vs os,
        sem_var H (Var x) s ->
        Forall2Brs (sem_exp G H b) es vs ->
        Forall2Brs (P_exp H b) es vs ->
        Forall2 (merge s) vs os ->
        P_exp H b (Emerge (x, tx) es lann) os.

    Hypothesis CaseTotalCase:
      forall H b e s es tys ck vs os,
        sem_exp G H b e [s] ->
        P_exp H b e [s] ->
        Forall2Brs (sem_exp G H b) es vs ->
        Forall2Brs (P_exp H b) es vs ->
        Forall3 (case s) vs (List.map (fun _ => None) tys) os ->
        P_exp H b (Ecase e es None (tys, ck)) os.

    Hypothesis CaseDefaultCase:
      forall H b e s es d lann vs vd os,
        sem_exp G H b e [s] ->
        P_exp H b e [s] ->
        wt_streams [s] (typeof e) ->
        Forall2Brs (sem_exp G H b) es vs ->
        Forall2Brs (P_exp H b) es vs ->
        Forall2 (sem_exp G H b) d vd ->
        Forall2 (P_exp H b) d vd ->
        Forall3 (case s) vs (List.map Some (concat vd)) os ->
        P_exp H b (Ecase e es (Some d) lann) os.

    Hypothesis AppCase:
      forall H b f es er lann ss os sr bs,
        Forall2 (sem_exp G H b) es ss ->
        Forall2 (P_exp H b) es ss ->
        Forall2 (fun e r => sem_exp G H b e [r]) er sr ->
        Forall2 (fun e r => P_exp H b e [r]) er sr ->
        bools_ofs sr bs ->
        (forall k, sem_node G f (List.map (maskv k bs) (concat ss)) (List.map (maskv k bs) os)
              /\ P_node f (List.map (maskv k bs) (concat ss)) (List.map (maskv k bs) os)) ->
        P_exp H b (Eapp f es er lann) os.

    Hypothesis Equation:
      forall H b xs es ss,
        Forall2 (sem_exp G H b) es ss ->
        Forall2 (P_exp H b) es ss ->
        Forall2 (fun x => sem_var H (Var x)) xs (concat ss) ->
        P_equation H b (xs, es).

    Hypothesis BeqCase:
      forall H b eq,
        sem_equation G H b eq ->
        P_equation H b eq ->
        P_block H b (Beq eq).

    Hypothesis BresetCase:
      forall H b blocks er sr r,
        sem_exp G H b er [sr] ->
        P_exp H b er [sr] ->
        bools_of sr r ->
        (forall k, Forall (sem_block G (mask_hist k r H) (maskb k r b)) blocks /\
                Forall (P_block (mask_hist k r H) (maskb k r b)) blocks) ->
        P_block H b (Breset blocks er).

    Hypothesis BswitchCase:
      forall Hi b ec branches sc,
        sem_exp G Hi b ec [sc] ->
        P_exp Hi b ec [sc] ->
        wt_streams [sc] (typeof ec) ->
        Forall (fun blks => exists Hi', when_hist (fst blks) Hi sc Hi'
                                /\ let bi := fwhenb (fst blks) b sc in
                                  sem_branch
                                    (fun blks => Forall (sem_block G Hi' bi) blks
                                              /\ Forall (P_block Hi' bi) blks)
                                    (fun x : ident => Is_defined_in x (Bswitch ec branches))
                                    (fun x : ident => List.Exists (Is_defined_in x)) Hi' (snd blks)) branches ->
        P_block Hi b (Bswitch ec branches).

    Hypothesis TransDefCase:
      forall Hi bs default stres,
        stres ≡ const_stres bs default ->
        P_transitions Hi bs [] default stres.

    Hypothesis TransCase:
      forall Hi bs e C r trans default vs bs' stres1 stres,
        sem_exp G Hi bs e [vs] ->
        P_exp Hi bs e [vs] ->
        bools_of vs bs' ->
        sem_transitions G Hi bs trans default stres1 ->
        P_transitions Hi bs trans default stres1 ->
        stres ≡ choose_first (const_stres bs' (C, r)) stres1 ->
        P_transitions Hi bs ((e, (C, r))::trans) default stres.

    Hypothesis BautoWeakCase:
      forall Hi bs ini oth states ck bs' stres0 stres1 stres,
        sem_clock (var_history Hi) bs ck bs' ->
        sem_transitions G Hi bs' (List.map (fun '(e, t) => (e, (t, false))) ini) (oth, false) stres0 ->
        P_transitions Hi bs' (List.map (fun '(e, t) => (e, (t, false))) ini) (oth, false) stres0 ->
        fby stres0 stres1 stres ->
        Forall (fun '((tag, _), br) =>
                  forall k, exists Hik,
                    select_hist tag k stres Hi Hik
                    /\ let bik := fselectb tag k stres bs in
                      sem_branch
                        (fun '(_, scope) =>
                           sem_scope
                             (fun Hi' bik e vs => sem_exp G Hi' bik e vs /\ P_exp Hi' bik e vs)
                             (fun Hi' blks => Forall (sem_block G Hi' bik) (fst blks)
                                           /\ Forall (P_block Hi' bik) (fst blks)
                                           /\ sem_transitions G Hi' bik (snd blks) (tag, false) (fselect absent tag k stres stres1)
                                           /\ P_transitions Hi' bik (snd blks) (tag, false) (fselect absent tag k stres stres1)
                             ) Hik bik scope)
                        (fun x => Is_defined_in x (Bauto Weak ck (ini, oth) states))
                        (fun x '(_, s) => Is_defined_in_scope (fun '(blks, _) => List.Exists (Is_defined_in x) blks) x s)
                        Hik br) states ->
        P_block Hi bs (Bauto Weak ck (ini, oth) states).

    Hypothesis BautoStrongCase:
      forall Hi bs ini states ck bs' stres0 stres1,
        sem_clock (var_history Hi) bs ck bs' ->
        fby (const_stres bs' (ini, false)) stres1 stres0 ->
        Forall (fun '((tag, _), br) =>
                  forall k, exists Hik, select_hist tag k stres0 Hi Hik
                              /\ let bik := fselectb tag k stres0 bs in
                                sem_branch
                                  (fun '(unl, _) =>
                                     sem_transitions G Hik bik unl (tag, false) (fselect absent tag k stres0 stres1)
                                     /\ P_transitions Hik bik unl (tag, false) (fselect absent tag k stres0 stres1))
                                  (fun x => Is_defined_in x (Bauto Strong ck ([], ini) states))
                                  (fun x '(_, s) => Is_defined_in_scope (fun '(blks, _) => List.Exists (Is_defined_in x) blks) x s)
                                  Hik br) states ->
        Forall (fun '((tag, _), br) =>
                  forall k, exists Hik,
                    select_hist tag k stres1 Hi Hik
                    /\ let bik := fselectb tag k stres1 bs in
                      sem_branch
                        (fun '(_, scope) =>
                           sem_scope
                             (fun Hi' bik e vs => sem_exp G Hi' bik e vs /\ P_exp Hi' bik e vs)
                             (fun Hi' blks => Forall (sem_block G Hi' bik) (fst blks)
                                           /\ Forall (P_block Hi' bik) (fst blks)
                             ) Hik bik scope)
                        (fun x => Is_defined_in x (Bauto Strong ck ([], ini) states))
                        (fun x '(_, s) => Is_defined_in_scope (fun '(blks, _) => List.Exists (Is_defined_in x) blks) x s)
                        Hik br) states ->
        P_block Hi bs (Bauto Strong ck ([], ini) states).

    Hypothesis BlocalCase:
      forall Hi bs scope,
        sem_scope (fun Hi' bs e vs => sem_exp G Hi' bs e vs /\ P_exp Hi' bs e vs)
          (fun Hi' blks => Forall (sem_block G Hi' bs) blks /\ Forall (P_block Hi' bs) blks)
          Hi bs scope ->
        P_block Hi bs (Blocal scope).

    Hypothesis Node:
      forall f ss os n H,
        find_node f G = Some n ->
        Forall2 (fun x => sem_var H (Var x)) (List.map fst n.(n_in)) ss ->
        Forall2 (fun x => sem_var H (Var x)) (List.map fst n.(n_out)) os ->
        let bs := clocks_of ss in
        Forall (sem_last_decl (fun Hi' bs e vs => sem_exp G Hi' bs e vs /\ P_exp Hi' bs e vs) (FEnv.empty _) H bs) n.(n_out) ->
        sem_block G H bs n.(n_block) ->
        P_block H bs n.(n_block) ->
        P_node f ss os.

    Local Ltac SolveForall :=
      match goal with
      | H: Forall ?P1 ?l |- Forall ?P2 ?l =>
          induction H; eauto
      | H: Forall2 ?P1 ?l1 ?l2 |- Forall2 ?P2 ?l1 ?l2 =>
          induction H; eauto
      | _ => idtac
      end.

    Fixpoint sem_exp_ind2
      (H: history) (b: Stream bool) (e: exp) (ss: list (Stream svalue))
      (Sem: sem_exp G H b e ss)
      {struct Sem}
      : P_exp H b e ss
    with sem_equation_ind2
           (H: history) (b: Stream bool) (e: equation)
           (Sem: sem_equation G H b e)
           {struct Sem}
      : P_equation H b e
    with sem_transitions_ind2
           (H: history) (b: Stream bool) trans default stres
           (Sem: sem_transitions G H b trans default stres)
           {struct Sem}
      : P_transitions H b trans default stres
    with sem_block_ind2
           (H: history) (b: Stream bool) (d: block)
           (Sem: sem_block G H b d)
           {struct Sem}
      : P_block H b d
    with sem_node_ind2
           (f: ident) (ss os: list (Stream svalue))
           (Sem: sem_node G f ss os)
           {struct Sem}
      : P_node f ss os.
    Proof.
      - inv Sem.
        + apply ConstCase; eauto.
        + apply EnumCase; eauto.
        + apply VarCase; auto.
        + apply LastCase; auto.
        + eapply UnopCase; eauto.
        + eapply BinopCase; eauto.
        + eapply ExtcallCase; eauto. clear H1 H3; SolveForall.
        + eapply FbyCase; eauto; clear H3; SolveForall.
        + eapply ArrowCase; eauto; clear H3; SolveForall.
        + eapply WhenCase; eauto; clear H3; SolveForall.
        + eapply MergeCase; eauto; clear H3; SolveForall.
          induction H2; econstructor; eauto. clear IHForall2Brs H2 H3. SolveForall.
        + eapply CaseTotalCase; eauto; clear H3.
          induction H2; econstructor; eauto. clear IHForall2Brs H2 H3. SolveForall.
        + eapply CaseDefaultCase; eauto.
          * clear - sem_exp_ind2 H3.
            induction H3; econstructor; eauto. clear IHForall2Brs H1 H3. SolveForall.
          * clear - sem_exp_ind2 H4.
            SolveForall.
        + eapply AppCase; eauto; clear H3 H4; SolveForall.
      - inv Sem.
        eapply Equation with (ss:=ss); eauto; clear H2; SolveForall.
      - inv Sem.
        + eapply TransDefCase; eauto.
        + eapply TransCase; eauto.
      - inv Sem.
        + eapply BeqCase; eauto.
        + eapply BresetCase; eauto.
          intros k. specialize (H3 k). split; eauto. SolveForall.
        + eapply BswitchCase; eauto.
          revert H2. generalize (Bswitch ec branches) as blk. intros.
          SolveForall. constructor; auto.
          destruct_conjs. inv H4. do 2 esplit; eauto.
          econstructor; eauto. split; auto. clear H6.
          simpl. SolveForall.
        + eapply BautoWeakCase; eauto.
          revert H4. generalize (Bauto Weak ck (ini, oth) states) as blk. intros.
          SolveForall. destruct_conjs. constructor; auto.
          intros k. specialize (H0 k). destruct_conjs.
          inv_branch'. inv_scope'.
          do 2 esplit; eauto.
          do 2 (econstructor; eauto). 2:split; [|split; [|split]]; eauto.
          * clear - sem_exp_ind2 H8. SolveForall. constructor; auto.
            inv H; econstructor; eauto.
          * clear H7. simpl. SolveForall.
        + eapply BautoStrongCase; eauto.
          * clear - H3 sem_transitions_ind2.
            revert H3. generalize (Bauto Strong ck ([], ini) states) as blk. intros.
            SolveForall. destruct_conjs. constructor; auto.
            intros k. specialize (H0 k). destruct_conjs. inv_branch'. destruct_conjs.
            do 2 esplit; eauto. econstructor; eauto.
          * clear H3. revert H4. generalize (Bauto Strong ck ([], ini) states) as blk. intros.
            SolveForall. destruct_conjs. constructor; auto.
            intros k. specialize (H0 k). destruct_conjs.
            inv_branch'. inv_scope'.
            do 2 esplit; eauto. do 2 (econstructor; eauto).
            2:split; auto; simpl.
            -- clear - sem_exp_ind2 H7. SolveForall. constructor; auto.
               inv H; econstructor; eauto.
            -- clear H6. SolveForall.
        + eapply BlocalCase; eauto.
          inv H0. econstructor; eauto. 2:split; auto; SolveForall.
          clear - sem_exp_ind2 H2. SolveForall. constructor; auto.
          inv H0; econstructor; eauto.
      - inv Sem.
        eapply Node; eauto.
        clear - sem_exp_ind2 H3. SolveForall. constructor; auto.
        take (sem_last_decl _ _ _ _ _) and inv it; econstructor; eauto.
    Qed.

  End sem_exp_ind2.
  
  (** ** properties of the [global] environment *)

  Ltac sem_cons :=
    intros; simpl_Forall; solve_Exists;
    unfold Is_node_in_eq in *;
    match goal with
    | H: Forall2Brs _ ?l1 ?l2 |- Forall2Brs _ ?l1 ?l2 =>
        eapply Forall2Brs_impl_In in H; eauto; intros; sem_cons
    | H: _ -> ?R |- ?R => eapply H; eauto
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
    | H:sem_last_decl _ _ _ _ _ |- sem_last_decl _ _ _ _ _ =>
        inv H; destruct_conjs; econstructor; eauto
    | H:sem_branch _ _ _ _ _ |- _ =>
        inv H; destruct_conjs
    | |- sem_branch _ _ _ _ _ => econstructor; eauto
    | |- Is_node_in_branch _ _ => econstructor; sem_cons
    | H:sem_scope _ _ _ _ _ |- sem_scope _ _ _ _ _ =>
        inv H; destruct_conjs; econstructor; eauto
    | |- Is_node_in_scope _ _ _ => econstructor; sem_cons
    | |- _ /\ _ => split; sem_cons
    | |- exists _ _, _ /\ _ /\ _ =>
        do 2 esplit; split; [|split]; eauto; sem_cons
    | _ => auto
    end.

  Definition exp_cons1 {PSyn prefs} typs exts (nd: @node PSyn prefs) (nds: list (@node PSyn prefs)) H bs e ss :=
    ~ Is_node_in_exp nd.(n_name) e -> sem_exp (Global typs exts nds) H bs e ss.
  Definition equation_cons1 {PSyn prefs} typs exts (nd: @node PSyn prefs) (nds: list (@node PSyn prefs)) H bs equ :=
    ~ Is_node_in_eq nd.(n_name) equ -> sem_equation (Global typs exts nds) H bs equ.
  Definition transitions_cons1 {PSyn prefs} typs exts (nd: @node PSyn prefs) (nds: list (@node PSyn prefs)) H bs trans default stres :=
    ~ List.Exists (fun '(e, _) => Is_node_in_exp nd.(n_name) e) trans -> sem_transitions (Global typs exts nds) H bs trans default stres.
  Definition block_cons1 {PSyn prefs} typs exts (nd: @node PSyn prefs) (nds: list (@node PSyn prefs)) H bs blk :=
    ~ Is_node_in_block nd.(n_name) blk -> sem_block (Global typs exts nds) H bs blk.
  Definition node_cons1 {PSyn prefs} typs exts (nd: @node PSyn prefs) (nds: list (@node PSyn prefs)) f xs ys :=
    nd.(n_name) <> f -> sem_node (Global typs exts nds) f xs ys.
  Global Hint Unfold exp_cons1 equation_cons1 transitions_cons1 block_cons1 node_cons1 : lsem.

  Lemma sem_exp_cons1 {PSyn prefs} :
    forall typs exts (nd : @node PSyn prefs) nds Hi bs e ss,
      Ordered_nodes (Global typs exts (nd::nds)) ->
      sem_exp (Global typs exts (nd::nds)) Hi bs e ss ->
      exp_cons1 typs exts nd nds Hi bs e ss.
  Proof.
    intros * Hord Hsem.
    eapply sem_exp_ind2
      with (P_exp := exp_cons1 typs exts nd nds)
           (P_equation := equation_cons1 typs exts nd nds)
           (P_transitions := transitions_cons1 typs exts nd nds)
           (P_block := block_cons1 typs exts nd nds)
           (P_node := node_cons1 typs exts nd nds). 25:eauto.
    all:autounfold with lsem in *; econstructor; eauto; repeat sem_cons.
    - intros contra. eapply find_node_later_not_Is_node_in; eauto. left; solve_Exists.
    - intros contra. eapply find_node_later_not_Is_node_in; eauto. right; auto.
  Qed.

  Lemma sem_block_cons1 {PSyn prefs} :
    forall typs exts (nd : @node PSyn prefs) nds Hi bs blk,
      Ordered_nodes (Global typs exts (nd::nds)) ->
      sem_block (Global typs exts (nd::nds)) Hi bs blk ->
      block_cons1 typs exts nd nds Hi bs blk.
  Proof.
    intros * Hord Hsem.
    eapply sem_block_ind2
      with (P_exp := exp_cons1 typs exts nd nds)
           (P_equation := equation_cons1 typs exts nd nds)
           (P_transitions := transitions_cons1 typs exts nd nds)
           (P_block := block_cons1 typs exts nd nds)
           (P_node := node_cons1 typs exts nd nds). 25:eauto.
    all:autounfold with lsem in *; econstructor; eauto; repeat sem_cons.
    - intros contra. eapply find_node_later_not_Is_node_in; eauto. left; solve_Exists.
    - intros contra. eapply find_node_later_not_Is_node_in; eauto. right; auto.
  Qed.

  Lemma sem_node_cons1 {PSyn prefs} :
    forall typs exts (nd : @node PSyn prefs) nds f xs ys,
      Ordered_nodes (Global typs exts (nd::nds)) ->
      sem_node (Global typs exts (nd::nds)) f xs ys ->
      node_cons1 typs exts nd nds f xs ys.
  Proof.
    intros * Hord Hsem.
    eapply sem_node_ind2
      with (P_exp := exp_cons1 typs exts nd nds)
           (P_equation := equation_cons1 typs exts nd nds)
           (P_transitions := transitions_cons1 typs exts nd nds)
           (P_block := block_cons1 typs exts nd nds)
           (P_node := node_cons1 typs exts nd nds). 25:eauto.
    all:autounfold with lsem in *; econstructor; eauto; repeat sem_cons.
    - intros contra. eapply find_node_later_not_Is_node_in; eauto. left; solve_Exists.
    - intros contra. eapply find_node_later_not_Is_node_in; eauto. right; auto.
  Qed.

  Corollary sem_node_cons1' {PSyn prefs} : forall typs exts (n nd: @node PSyn prefs) nds Hi bs,
      Ordered_nodes (Global typs exts (nd::nds)) ->
      ~Is_node_in nd.(n_name) n ->
      sem_block (Global typs exts (nd::nds)) Hi bs (n_block n) ->
      Forall (sem_last_decl (sem_exp (Global typs exts (nd::nds))) (FEnv.empty (Stream svalue)) Hi bs) (n_out n) ->
      sem_block (Global typs exts nds) Hi bs (n_block n)
      /\ Forall (sem_last_decl (sem_exp (Global typs exts nds)) (FEnv.empty (Stream svalue)) Hi bs) (n_out n).
  Proof.
    intros * Hord Hnin Hsem1 Hsem2.
    split.
    - eapply sem_block_cons1; eauto.
      contradict Hnin. now right.
    - simpl_Forall. inv Hsem2; econstructor; eauto.
      eapply sem_exp_cons1; eauto.
      contradict Hnin. left; solve_Exists.
  Qed.

  Definition exp_cons2 {PSyn prefs} typs exts (nd: @node PSyn prefs) (nds: list (@node PSyn prefs)) H bs e ss :=
    ~ Is_node_in_exp nd.(n_name) e -> sem_exp (Global typs exts (nd::nds)) H bs e ss.
  Definition equation_cons2 {PSyn prefs} typs exts (nd: @node PSyn prefs) (nds: list (@node PSyn prefs)) H bs equ :=
    ~ Is_node_in_eq nd.(n_name) equ -> sem_equation (Global typs exts (nd::nds)) H bs equ.
  Definition transitions_cons2 {PSyn prefs} typs exts (nd: @node PSyn prefs) (nds: list (@node PSyn prefs)) H bs trans default stres :=
    ~ List.Exists (fun '(e, _) => Is_node_in_exp nd.(n_name) e) trans -> sem_transitions (Global typs exts (nd::nds)) H bs trans default stres.
  Definition block_cons2 {PSyn prefs} typs exts (nd: @node PSyn prefs) (nds: list (@node PSyn prefs)) H bs blk :=
    ~ Is_node_in_block nd.(n_name) blk -> sem_block (Global typs exts (nd::nds)) H bs blk.
  Definition node_cons2 {PSyn prefs} typs exts (nd: @node PSyn prefs) (nds: list (@node PSyn prefs)) f xs ys :=
    nd.(n_name) <> f -> sem_node (Global typs exts (nd::nds)) f xs ys.
  Global Hint Unfold exp_cons2 equation_cons2 transitions_cons2 block_cons2 node_cons2 : lsem.

  Lemma sem_exp_cons2 {PSyn prefs} :
    forall typs exts (nd : @node PSyn prefs) nds Hi bs e ss,
      Ordered_nodes (Global typs exts (nd::nds)) ->
      sem_exp (Global typs exts nds) Hi bs e ss ->
      exp_cons2 typs exts nd nds Hi bs e ss.
  Proof.
    intros * Hord Hsem.
    eapply sem_exp_ind2
      with (P_exp := exp_cons2 typs exts nd nds)
           (P_equation := equation_cons2 typs exts nd nds)
           (P_transitions := transitions_cons2 typs exts nd nds)
           (P_block := block_cons2 typs exts nd nds)
           (P_node := node_cons2 typs exts nd nds). 25:eauto.
    all:autounfold with lsem in *; econstructor; eauto; repeat sem_cons.
    - intros contra. eapply find_node_later_not_Is_node_in; eauto. left; solve_Exists.
    - intros contra. eapply find_node_later_not_Is_node_in; eauto. right; auto.
  Qed.

  Lemma sem_block_cons2 {PSyn prefs} :
    forall typs exts (nd : @node PSyn prefs) nds Hi bs blk,
      Ordered_nodes (Global typs exts (nd::nds)) ->
      sem_block (Global typs exts nds) Hi bs blk ->
      block_cons2 typs exts nd nds Hi bs blk.
  Proof.
    intros * Hord Hsem.
    eapply sem_block_ind2
      with (P_exp := exp_cons2 typs exts nd nds)
           (P_equation := equation_cons2 typs exts nd nds)
           (P_transitions := transitions_cons2 typs exts nd nds)
           (P_block := block_cons2 typs exts nd nds)
           (P_node := node_cons2 typs exts nd nds). 25:eauto.
    all:autounfold with lsem in *; econstructor; eauto; repeat sem_cons.
    - intros contra. eapply find_node_later_not_Is_node_in; eauto. left; solve_Exists.
    - intros contra. eapply find_node_later_not_Is_node_in; eauto. right; auto.
  Qed.

  Lemma sem_node_cons2 {PSyn prefs} :
    forall typs exts (nd : @node PSyn prefs) nds f xs ys,
      Ordered_nodes (Global typs exts (nd::nds)) ->
      sem_node (Global typs exts nds) f xs ys ->
      node_cons2 typs exts nd nds f xs ys.
  Proof.
    intros * Hord Hsem.
    eapply sem_node_ind2
      with (P_exp := exp_cons2 typs exts nd nds)
           (P_equation := equation_cons2 typs exts nd nds)
           (P_transitions := transitions_cons2 typs exts nd nds)
           (P_block := block_cons2 typs exts nd nds)
           (P_node := node_cons2 typs exts nd nds). 25:eauto.
    all:autounfold with lsem in *; econstructor; eauto; repeat sem_cons.
    - intros contra. eapply find_node_later_not_Is_node_in; eauto. left; solve_Exists.
    - intros contra. eapply find_node_later_not_Is_node_in; eauto. right; auto.
  Qed.

  Lemma sem_node_cons_iff {PSyn prefs} :
    forall (n : @node PSyn prefs) nds types externs f xs ys,
      Ordered_nodes (Global types externs (n::nds)) ->
      n_name n <> f ->
      sem_node (Global types externs nds) f xs ys <->
      sem_node (Global types externs (n::nds)) f xs ys.
  Proof.
    intros * Hord Hname.
    split; intros Hsem.
    - eapply sem_node_cons2; eauto.
    - eapply sem_node_cons1; eauto.
  Qed.

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
      eapply H, FEnv.union_In in H15 as [|Hin']; eauto.
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
      sem_scope (sem_exp G) (fun Hi => Forall (sem_block G Hi bs)) Hi bs (Scope locs blks) ->
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
      sem_scope (sem_exp G) (fun Hi => Forall (sem_block G Hi bs)) Hi bs (Scope locs blks) ->
      VarsDefinedCompScope (fun blks ys => exists xs, Forall2 VarsDefinedComp blks xs /\ Permutation (concat xs) ys) (Scope locs blks) xs ->
      NoDupScope (fun Γ => Forall (NoDupLocals Γ)) Γ (Scope locs blks) ->
      incl xs Γ ->
      In x xs ->
      FEnv.In (Var x) Hi.
  Proof.
    intros * Hsem Hdef Hnd Hincl Hinxs.
    eapply sem_scope_defined; eauto.
    eapply VarsDefinedCompScope_Is_defined; eauto.
    - eapply NoDupScope_incl; eauto.
      intros; simpl in *. simpl_Forall.
      eapply NoDupLocals_incl; eauto.
    - intros; simpl in *. destruct_conjs.
      eapply Forall_VarsDefinedComp_Is_defined; eauto.
      simpl_Forall. 1,2:now rewrite H2.
  Qed.

  Corollary sem_scope_defined2 {A} {PSyn prefs} (G: @global PSyn prefs) :
    forall locs (blks: _ * A) Hi bs Γ xs x,
      sem_scope (sem_exp G) (fun Hi blks => Forall (sem_block G Hi bs) (fst blks)) Hi bs (Scope locs blks) ->
      VarsDefinedCompScope (fun blks ys => exists xs, Forall2 VarsDefinedComp (fst blks) xs /\ Permutation (concat xs) ys) (Scope locs blks) xs ->
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

  Lemma sem_branch_defined {PSyn prefs} (G: @global PSyn prefs) must_def is_def : forall caus blks Hi bs x,
      sem_branch (Forall (sem_block G Hi bs)) must_def is_def Hi (Branch caus blks) ->
      Is_defined_in_branch (List.Exists (Is_defined_in x)) (Branch caus blks) ->
      FEnv.In (Var x) Hi.
  Proof.
    intros * Hsem Hdef; inv Hsem; inv Hdef.
    eapply Forall_sem_block_defined in H0; eauto.
  Qed.

  Corollary sem_branch_defined1 {PSyn prefs} (G: @global PSyn prefs) :
    forall caus ec branches blks Hi bs Γ xs x,
      sem_branch (Forall (sem_block G Hi bs))
        (fun x => Is_defined_in x (Bswitch ec branches))
        (fun x => List.Exists (Is_defined_in x))
        Hi (Branch caus blks) ->
      VarsDefinedCompBranch (fun blks ys => exists xs, Forall2 VarsDefinedComp blks xs /\ Permutation (concat xs) ys) (Branch caus blks) xs ->
      NoDupBranch (Forall (NoDupLocals Γ)) (Branch caus blks) ->
      incl xs Γ ->
      In x xs ->
      FEnv.In (Var x) Hi.
  Proof.
    intros * Hsem Hdef Hnd Hincl Hinxs.
    eapply sem_branch_defined; eauto.
    eapply VarsDefinedCompBranch_Is_defined; eauto.
    - intros; simpl in *. destruct_conjs.
      eapply Forall_VarsDefinedComp_Is_defined; eauto.
      simpl_Forall. 1,2:rewrite H1; eauto using NoDupLocals_incl.
  Qed.

  Corollary sem_branch_defined2 {A} {PSyn prefs} (G: @global PSyn prefs) must_def is_def :
    forall caus (blks: (A * scope (_ * A))) Hi bs Γ xs x,
      sem_branch
        (fun blks =>
           sem_scope (sem_exp G)
             (fun Hi blks => Forall (sem_block G Hi bs) (fst blks)) Hi bs (snd blks))
        must_def is_def Hi (Branch caus blks) ->
      VarsDefinedCompBranch
        (fun blks => VarsDefinedCompScope (fun blks ys => exists xs, Forall2 VarsDefinedComp (fst blks) xs /\ Permutation (concat xs) ys) (snd blks))
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
      esplit; split; eauto. 2:do 2 (econstructor; eauto); repeat (split; eauto); eauto.
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
        esplit; split; eauto. 2:do 2 (econstructor; eauto); repeat (split; eauto); eauto.
        intros ?? Hfind. apply H2 in Hfind as (?&Hwhen&Hfind').
        apply Href in Hfind' as (?&?&?). do 2 esplit; [|eauto].
        take (_ ≡ _) and now rewrite <-it.
    - (* locals *)
      constructor.
      inv H4. econstructor; [| |eauto]; eauto.
      + simpl_Forall. take (sem_last_decl _ _ _ _ _) and inv it; econstructor; eauto.
        eapply sem_exp_refines; [|eauto]; eauto using FEnv.union_refines1, EqStrel_Reflexive.
      + simpl_Forall. eapply H; eauto using FEnv.union_refines1, EqStrel_Reflexive.
  Qed.

  Section props.
    Context {PSyn : list decl -> block -> Prop}.
    Context {prefs : PS.t}.
    Variable (G : @global PSyn prefs).

    (** The number of streams generated by an expression [e] equals [numstreams e] *)

    Fact sem_exp_numstreams : forall H b e v,
        wl_exp G e ->
        sem_exp G H b e v ->
        length v = numstreams e.
    Proof with eauto.
      induction e using exp_ind2; intros v Hsem Hwl; inv Hwl; inv Hsem; simpl; auto.
      all:
        unfold annots in *; try rewrite flat_map_concat_map in *;
        repeat
            (match goal with
             | H:forall _, Some _ = Some _ -> _ |- _ => specialize (H _ eq_refl)
             | H:Forall3 _ _ _ ?v |- length ?v = _ =>
                 apply Forall3_length in H as (Hlen1&Hlen2); setoid_rewrite <-Hlen2
             | H:Forall2 _ _ ?v |- length ?v = _ =>
                 apply Forall2_length in H as Hlen1; setoid_rewrite <-Hlen1
             | H:Forall2Brs _ _ _ |- _ => apply Forall2Brs_length1 in H; [|now simpl_Forall; eauto]
             | H:_ = ?l |- _ = ?l => rewrite <-H
             | H:?l = _ |- _ = ?l => rewrite <-H; try reflexivity
             | H:?es <> [] |- _ => destruct es; simpl in *; try congruence; clear H; simpl_Forall
             | |- length (List.map _ _) = _ => rewrite map_length
             | |- length (concat _) = length (concat _) => apply concat_length_eq; simpl_Forall
             end).
      1-3:apply Forall2_swap_args; simpl_Forall; rewrite length_annot_numstreams; eauto.
      - (* case default *)
        rewrite flat_map_concat_map. apply concat_length_eq; simpl_Forall.
        apply Forall2_swap_args; simpl_Forall; rewrite length_annot_numstreams; eauto.
      - (* app  *)
        take (forall k, _) and specialize (it 0). inv it.
        simpl_Forall. take (Forall2 _ _ v) and (apply Forall2_length in it).
        rewrite H3 in H14; inv H14.
        repeat rewrite map_length in *. setoid_rewrite H16. auto.
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

    Lemma sem_exp_sem_var : forall H b e vs,
        wl_exp G e ->
        sem_exp G H b e vs ->
        Forall2 (fun '(_, o) s => LiftO True (fun x : ident => sem_var H (Var x) s) o) (nclockof e) vs.
    Proof.
      intros * Hwl Hsem.
      assert (length vs = length (annot e)) as Hlen.
      { rewrite length_annot_numstreams. eapply sem_exp_numstreams; eauto. }
      inv Hwl; inv Hsem; simpl in *; repeat constructor; repeat rewrite map_length in *.
      all:simpl_Forall; simpl; auto.
      all:apply Forall2_forall; split; auto.
    Qed.

    Corollary sem_exps_sem_var : forall H b es vs,
        Forall (wl_exp G) es ->
        Forall2 (sem_exp G H b) es vs ->
        Forall2 (fun '(_, o) s => LiftO True (fun x : ident => sem_var H (Var x) s) o) (nclocksof es) (concat vs).
    Proof.
      induction es; intros * Hwc Hsem; inv Hwc; inv Hsem; simpl; auto.
      apply Forall2_app; auto.
      eapply sem_exp_sem_var; eauto.
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
    vars_of_senv (senv_of_decls locs).

  Fact vars_of_locs_Var : forall locs x,
      In (Var x) (vars_of_locs locs) <-> IsVar (senv_of_decls locs) x.
  Proof.
    intros. apply vars_of_senv_Var.
  Qed.

  Fact vars_of_locs_Last : forall locs x,
      In (Last x) (vars_of_locs locs) <-> IsLast (senv_of_decls locs) x.
  Proof.
    intros. apply vars_of_senv_Last.
  Qed.

  Lemma sem_scope_restrict {A} (wx_block : _ -> _ -> Prop) (sem_block : _ -> _ -> Prop) (P_vd : _ -> _ -> Prop) (P_nd : _ -> _ -> Prop) {PSyn prefs} (G: @global PSyn prefs) :
    forall Γ xs Hi bs locs (blks : A),
      (forall Γ xs Hi Hi',
          P_vd blks xs ->
          P_nd xs blks ->
          wx_block Γ blks ->
          sem_block Hi blks ->
          FEnv.Equiv (@EqSt _) Hi' (restrict Hi Γ) ->
          sem_block Hi' blks) ->
      VarsDefinedCompScope P_vd (Scope locs blks) xs ->
      NoDupScope P_nd xs (Scope locs blks) ->
      wx_scope wx_block Γ (Scope locs blks) ->
      sem_scope (sem_exp G) sem_block Hi bs (Scope locs blks) ->
      sem_scope (sem_exp G) sem_block (restrict Hi Γ) bs (Scope locs blks).
  Proof.
    intros * Hp VD ND Hwx Hsem; inv VD; inv ND; inv Hwx; inv Hsem.
    assert (FEnv.Equiv (@EqSt _) (restrict (Hi + Hi') (Γ ++ senv_of_decls locs))
              (restrict Hi Γ + Hi')) as Heq.
    { simpl. symmetry.
      intros ?. unfold FEnv.union, restrict, FEnv.restrict, vars_of_senv.
      rewrite <-flat_map_app, existsb_app.
      destruct (Hi' x) eqn:HHi', (existsb _ _) eqn:Hex; simpl; try reflexivity.
      - replace (existsb _ _) with true; [constructor; reflexivity|].
        symmetry. rewrite existsb_exists. do 2 esplit; [|eapply equiv_decb_refl].
        apply FEnv.find_In in HHi'.
        destruct x; [apply H3, vars_of_locs_Var in HHi'|apply H3, vars_of_locs_Last in HHi']; auto.
      - replace (existsb _ _) with false. constructor.
        symmetry. rewrite existsb_Forall, forallb_Forall. simpl_Forall.
        apply Bool.negb_true_iff, not_equiv_decb_equiv. intros Eq; inv Eq.
        apply FEnv.not_find_In in HHi'.
        destruct x; [apply vars_of_locs_Var, H3 in H; eauto|apply vars_of_locs_Last, H3 in H; eauto].
    }
    eapply Sscope with (Hi':=Hi'); eauto.
    - simpl_Forall. take (sem_last_decl _ _ _ _ _) and inv it; econstructor; eauto.
      eapply sem_exp_morph, sem_exp_restrict; eauto; try reflexivity.
    - eapply Hp in H7; eauto. now symmetry.
  Qed.

  Lemma sem_block_restrict {PSyn prefs} : forall (G: @global PSyn prefs) blk Γ xs H b,
      VarsDefinedComp blk xs ->
      NoDupLocals xs blk ->
      wx_block Γ blk ->
      sem_block G H b blk ->
      sem_block G (restrict H Γ) b blk.
  Proof.
    induction blk using block_ind2; intros * VD ND Hwc Hsem;
      assert (Hwx:=Hwc); assert (VD':=VD); assert (ND':=ND); inv VD'; inv ND'; inv Hwc; inv Hsem.
    - (* equation *)
      econstructor.
      eapply sem_equation_restrict; eauto.
    - (* reset *)
      econstructor; eauto using sem_exp_restrict.
      intros k; specialize (H12 k).
      simpl_Forall. inv_VarsDefined.
      eapply sem_block_refines; try eapply H; eauto.
      2:{ eapply NoDupLocals_incl; [|eauto]; eauto using incl_concat. }
      setoid_rewrite <-FEnv.restrict_map; auto using EqStrel_Reflexive.
      reflexivity.
    - (* switch *)
      econstructor; eauto using sem_exp_restrict.
      simpl_Forall. do 2 esplit.
      + intros ?? Hfind. apply FEnv.restrict_find_inv in Hfind as (Hin&Hfind).
        eapply H2 in Hfind as (?&Hwhen&Hfind').
        do 2 esplit; eauto using FEnv.restrict_find.
      + destruct b0. repeat inv_branch'. econstructor.
        * simpl_Forall; inv_VarsDefined. eapply H; eauto.
          eapply NoDupLocals_incl; [|eauto]; take (Permutation _ _) and rewrite <-it; eauto using incl_concat.
        * intros * Hdef Hndef. exfalso. eapply Hndef.
          eapply VarsDefinedComp_Is_defined' in Hdef; eauto.
          eapply Forall_VarsDefinedComp_Is_defined; eauto. 2:take (Permutation _ _) and now rewrite it.
          simpl_Forall. eapply NoDupLocals_incl; [|eauto]; take (Permutation _ _) and now rewrite <-it.
    - (* automaton (weak transitions) *)
      econstructor; eauto.
      + eapply sem_clock_var_history_restrict; eauto.
      + eapply sem_transitions_restrict; eauto. simpl_Forall; auto.
      + simpl_Forall. specialize (H19 k); destruct_conjs.
        esplit; split.
        * intros ?? Hfind. apply FEnv.restrict_find_inv in Hfind as (Hin&Hfind).
          eapply H2 in Hfind as (?&Hwhen&Hfind').
          do 2 esplit; eauto using FEnv.restrict_find.
        * repeat inv_branch'. destruct s; destruct_conjs. constructor.
          2:{ intros * Def NDef. exfalso. eapply NDef.
              eapply VarsDefinedComp_Is_defined' in Def; eauto.
              eapply VarsDefinedCompScope_Is_defined; eauto.
              intros; destruct_conjs. eapply Forall_VarsDefinedComp_Is_defined; eauto.
              1,2:simpl_Forall; take (Permutation _ _) and rewrite it; auto. }
          eapply sem_scope_restrict; eauto.
          intros; split; simpl_Forall; inv_VarsDefined; destruct_conjs.
          -- eapply sem_block_morph, H; eauto; try reflexivity. now symmetry.
             eapply NoDupLocals_incl; [|eauto]; take (Permutation _ _) and rewrite <-it; eauto using incl_concat.
          -- eapply sem_transitions_morph, sem_transitions_restrict; eauto; try reflexivity.
             now symmetry.
    - (* automaton (strong transitions) *)
      econstructor; eauto.
      + eapply sem_clock_var_history_restrict; eauto.
      + simpl_Forall. specialize (H18 k); destruct_conjs.
        esplit; split.
        * intros ?? Hfind. apply FEnv.restrict_find_inv in Hfind as (Hin&Hfind).
          eapply H2 in Hfind as (?&Hwhen&Hfind').
          do 2 esplit; eauto using FEnv.restrict_find.
        * repeat inv_branch'. destruct s; destruct_conjs. constructor.
          2:{ intros * Def NDef. exfalso. eapply NDef.
              eapply VarsDefinedComp_Is_defined' in Def; eauto.
              eapply VarsDefinedCompScope_Is_defined; eauto.
              intros; destruct_conjs. eapply Forall_VarsDefinedComp_Is_defined; eauto.
              1,2:simpl_Forall; take (Permutation _ _) and rewrite it; auto. }
          eapply sem_transitions_restrict; eauto.
      + simpl_Forall. specialize (H19 k); destruct_conjs.
        esplit; split.
        * intros ?? Hfind. apply FEnv.restrict_find_inv in Hfind as (Hin&Hfind).
          eapply H2 in Hfind as (?&Hwhen&Hfind').
          do 2 esplit; eauto using FEnv.restrict_find.
        * repeat inv_branch'. destruct s; destruct_conjs. constructor.
          2:{ intros * Def NDef. exfalso. eapply NDef.
              eapply VarsDefinedComp_Is_defined' in Def; eauto.
              eapply VarsDefinedCompScope_Is_defined; eauto.
              intros; destruct_conjs. eapply Forall_VarsDefinedComp_Is_defined; eauto.
              1,2:simpl_Forall; take (Permutation _ _) and rewrite it; auto. }
          eapply sem_scope_restrict; eauto.
          intros; simpl_Forall; inv_VarsDefined.
          eapply sem_block_morph, H; eauto; try reflexivity. now symmetry.
          eapply NoDupLocals_incl; [|eauto]; take (Permutation _ _) and rewrite <-it; eauto using incl_concat.
    - (* locals *)
      constructor. eapply sem_scope_restrict; eauto.
      intros; simpl_Forall; inv_VarsDefined.
      eapply sem_block_morph, H; eauto; try reflexivity. now symmetry.
      eapply NoDupLocals_incl; [|eauto]; take (Permutation _ _) and rewrite <-it; eauto using incl_concat.
  Qed.

  (** dom and co *)

  Lemma local_hist_dom : forall Γ locs (H H' : FEnv.t (Stream svalue)),
      dom H Γ ->
      dom H' (@senv_of_decls exp locs) ->
      dom (H + H') (Γ ++ senv_of_decls locs).
  Proof.
    intros * (D1&DL1) (D2&DL2).
    split; intros; rewrite FEnv.union_In;
      [rewrite IsVar_app, D1, D2|rewrite IsLast_app, DL1, DL2];
      reflexivity.
  Qed.

  Lemma local_hist_dom_ub : forall Γ locs (H H' : FEnv.t (Stream svalue)),
      dom_ub H Γ ->
      dom H' (@senv_of_decls exp locs) ->
      dom_ub (H + H') (Γ ++ senv_of_decls locs).
  Proof.
    intros * (D1&DL1) (D2&DL2).
    split; intros ?; rewrite FEnv.union_In;
      [rewrite IsVar_app, <-D2|rewrite IsLast_app, <-DL2];
      intros [|]; auto.
  Qed.

  Lemma local_hist_dom_lb : forall Γ locs (H H' : FEnv.t (Stream svalue)),
      dom_lb H Γ ->
      dom H' (@senv_of_decls exp locs) ->
      dom_lb (H + H') (Γ ++ senv_of_decls locs).
  Proof.
    intros * (D1&DL1) (D2&DL2).
    split; intros ?; rewrite FEnv.union_In;
      [rewrite IsVar_app, <-D2|rewrite IsLast_app, <-DL2];
      intros [|]; auto.
  Qed.

  Lemma local_hist_dom_ub_refines : forall Γ locs (H H': FEnv.t (Stream svalue)),
      (forall x, InMembers x locs -> ~IsVar Γ x) ->
      dom_ub H Γ ->
      dom H' (@senv_of_decls exp locs) ->
      H ⊑ H + H'.
  Proof.
    intros * Hnd (D1&DL1) (D2&DL2) ?? Hfind.
    do 2 esplit; [reflexivity|].
    apply FEnv.union2, FEnv.not_find_In; auto.
    destruct x;
      [rewrite D2|rewrite DL2];
      intros contra; [apply IsVar_senv_of_decls in contra|apply IsLast_senv_of_decls in contra];
      eapply Hnd; eauto; [eapply D1|eapply IsLast_IsVar, DL1];
      econstructor; eauto.
  Qed.

  Corollary local_hist_dom_refines : forall Γ locs (H H': FEnv.t (Stream svalue)),
      (forall x, InMembers x locs -> ~IsVar Γ x) ->
      dom H Γ ->
      dom H' (@senv_of_decls exp locs) ->
      H ⊑ H + H'.
  Proof.
  Proof.
    intros * Hnd Hdom1 Hdom2.
    eapply local_hist_dom_ub_refines; eauto using dom_dom_ub.
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

  (** ** Semantic inclusion *)
  Section sem_ref.
    Context {PSyn1 PSyn2 : list decl -> block -> Prop}.
    Context {pref1 pref2 : PS.t}.

    (** We develop a notion of refinement over globals :
        [node_sem_refines G G' f] means that if [f] exists and has a given semantic in [G],
        then it also exists and has the same semantic in [G'].
        This is just a shorthand definition, but is useful when proving the correctness
        of transformation passes over the Lustre AST.
     *)
    Definition node_sem_refines (G : @global PSyn1 pref1) (G' : @global PSyn2 pref2) f : Prop :=
      forall ins outs, sem_node G f ins outs -> sem_node G' f ins outs.

    Definition global_sem_refines (G : @global PSyn1 pref1) (G' : @global PSyn2 pref2) : Prop :=
      forall f, node_sem_refines G G' f.

    Hint Constructors sem_exp : core.

    Fact sem_ref_sem_exp : forall G G' H b e vs,
        global_sem_refines G G' ->
        sem_exp G H b e vs ->
        sem_exp G' H b e vs.
    Proof with eauto with datatypes.
      induction e using exp_ind2; intros * Href Hsem;
        inv Hsem...
      - (* extcall *)
        econstructor...
        simpl_Forall...
      - (* fby *)
        econstructor...
        + simpl_Forall...
        + simpl_Forall...
      - (* arrow *)
        econstructor...
        + simpl_Forall...
        + simpl_Forall...
      - (* when *)
        econstructor...
        simpl_Forall...
      - (* merge *)
        econstructor...
        eapply Forall2Brs_impl_In; [|eauto]; intros ?? Hin Hse.
        simpl_Exists; simpl_Forall...
      - (* case *)
        econstructor...
        eapply Forall2Brs_impl_In; [|eauto]; intros ?? Hin Hse.
        simpl_Exists; simpl_Forall...
      - (* case (default) *)
        econstructor...
        + eapply Forall2Brs_impl_In; [|eauto]; intros ?? Hin Hse.
          simpl_Exists; simpl_Forall...
        + eapply Forall2_impl_In; [|eauto]; intros ?? Hin1 Hin2 Hse.
          simpl in *. simpl_Forall...
      - (* app *)
        econstructor... instantiate (1:=ss).
        + simpl_Forall...
        + simpl_Forall...
        + intros k. specialize (H13 k).
          specialize (Href f (List.map (maskv k bs) (concat ss)) (List.map (maskv k bs) vs)).
          eapply Href; eauto.
    Qed.

    Fact sem_ref_sem_equation : forall G G' H b eq,
        global_sem_refines G G' ->
        sem_equation G H b eq ->
        sem_equation G' H b eq.
    Proof.
      intros G G' H b [xs es] Href Hsem.
      inv Hsem.
      econstructor; eauto.
      eapply Forall2_impl_In; [|eauto]; intros.
      eapply sem_ref_sem_exp; eauto.
    Qed.

    Fact sem_ref_sem_transitions : forall G G' H b trans def stres,
        global_sem_refines G G' ->
        sem_transitions G H b trans def stres ->
        sem_transitions G' H b trans def stres.
    Proof.
      induction trans; intros * Href Hsem; inv Hsem;
        econstructor; eauto using sem_ref_sem_exp.
    Qed.

    Fact sem_ref_sem_block : forall G G' blk H b,
        global_sem_refines G G' ->
        sem_block G H b blk ->
        sem_block G' H b blk.
    Proof.
      induction blk using block_ind2; intros * Href Hsem;
        inv Hsem.
      - (* equation *)
        constructor; eauto using sem_ref_sem_equation.
      - (* reset *)
        econstructor; eauto using sem_ref_sem_exp.
        intros k. specialize (H8 k).
        rewrite Forall_forall in *; eauto.
      - (* switch *)
        econstructor; eauto using sem_ref_sem_exp.
        simpl_Forall; do 2 esplit; eauto.
        inv_branch'; econstructor; eauto.
        simpl_Forall; eauto.
      - (* automaton (weak) *)
        econstructor; eauto using sem_ref_sem_transitions.
        simpl_Forall. specialize (H11 k); destruct_conjs.
        do 2 esplit; eauto.
        inv_branch'; inv_scope'; do 2 (econstructor; eauto).
        + simpl_Forall. take (sem_last_decl _ _ _ _ _) and inv it; econstructor; eauto using sem_ref_sem_exp.
        + destruct_conjs. split; simpl_Forall; eauto using sem_ref_sem_transitions.
      - (* automaton (strong) *)
        econstructor; eauto.
        + simpl_Forall. specialize (H10 k); destruct_conjs.
          inv_branch'. do 2 esplit; eauto. econstructor; eauto using sem_ref_sem_transitions.
        + simpl_Forall. specialize (H11 k); destruct_conjs.
          do 2 esplit; eauto.
          inv_branch'; inv_scope'; do 2 (econstructor; eauto).
          * simpl_Forall. take (sem_last_decl _ _ _ _ _) and inv it; econstructor; eauto using sem_ref_sem_exp.
          * destruct_conjs. simpl_Forall; eauto.
      - (* local *)
        constructor. inv_scope'; econstructor; eauto.
        + simpl_Forall. take (sem_last_decl _ _ _ _ _) and inv it; econstructor; eauto using sem_ref_sem_exp.
        + simpl_Forall; eauto.
    Qed.

    Fact global_sem_ref_nil : forall enms1 enms2 exts1 exts2,
      global_sem_refines (Global enms1 exts1 []) (Global enms2 exts2 []).
    Proof.
      intros * f ins outs Hsem.
      inv Hsem. unfold find_node in H0; simpl in H0; inv H0.
    Qed.

    Fact global_sem_ref_cons : forall enms1 enms2 exts1 exts2 nds nds' n n' f,
        Ordered_nodes (Global enms1 exts1 (n::nds)) ->
        Ordered_nodes (Global enms2 exts2 (n'::nds')) ->
        n_name n = f ->
        n_name n' = f ->
        global_sem_refines (Global enms1 exts1 nds) (Global enms2 exts2 nds') ->
        node_sem_refines (Global enms1 exts1 (n::nds)) (Global enms2 exts2 (n'::nds')) f ->
        global_sem_refines (Global enms1 exts1 (n::nds)) (Global enms2 exts2 (n'::nds')).
    Proof with eauto.
      intros * Hord1 Hord2 Hname1 Hname2 Hglob Hnode f0 ins outs Hsem.
      destruct (ident_eq_dec (n_name n) f0); subst.
      + specialize (Hnode ins outs).
        eapply Hnode; eauto.
      + setoid_rewrite <-sem_node_cons_iff...
        eapply Hglob.
        setoid_rewrite sem_node_cons_iff...
        congruence.
    Qed.

  End sem_ref.

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
