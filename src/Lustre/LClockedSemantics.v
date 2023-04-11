From Coq Require Import Streams.
From Coq Require Import List.
Import List.ListNotations.
Open Scope list_scope.

From Coq Require Import Sorting.Permutation.
From Coq Require Import Setoid.
From Coq Require Import Morphisms.

From Coq Require Import FSets.FMapPositive.
From Velus Require Import Common.
From Velus Require Import CommonList.
From Velus Require Import FunctionalEnvironment.
From Velus Require Import Operators.
From Velus Require Import CoindStreams IndexedStreams.
From Velus Require Import CoindIndexed.
From Velus Require Import Clocks.
From Velus Require Import Lustre.StaticEnv.
From Velus Require Import Lustre.LSyntax Lustre.LClocking Lustre.LOrdered.
From Velus Require Import Lustre.LSemantics.

Module Type LCLOCKEDSEMANTICS
       (Import Ids   : IDS)
       (Import Op    : OPERATORS)
       (Import OpAux : OPERATORS_AUX Ids Op)
       (Import Cks   : CLOCKS        Ids Op OpAux)
       (Import Senv  : STATICENV     Ids Op OpAux Cks)
       (Import Syn   : LSYNTAX Ids Op OpAux Cks Senv)
       (Import Clo   : LCLOCKING Ids Op OpAux Cks Senv Syn)
       (Import Lord  : LORDERED Ids Op OpAux Cks Senv Syn)
       (Import CStr  : COINDSTREAMS Ids Op OpAux Cks)
       (Import Sem   : LSEMANTICS Ids Op OpAux Cks Senv Syn Lord CStr).

  Import CStr.
  Module IStr := IndexedStreamsFun Ids Op OpAux Cks.
  Module Import CIStr := CoindIndexedFun Ids Op OpAux Cks CStr IStr.

  Lemma history_tl_same_find {K} : forall (H H' : @history K) vars,
      Forall (fun x => orel (EqSt (A:=svalue)) (H x) (H' x)) vars ->
      Forall (fun x => orel (EqSt (A:=svalue)) ((history_tl H) x) ((history_tl H') x)) vars.
  Proof.
    intros * Hsem.
    eapply Forall_impl; [|eauto]. intros; simpl in *.
    simpl_fenv. inv H0; simpl; constructor.
    now rewrite H3.
  Qed.

  Import List.

  Lemma sem_clock_same_find : forall H H' vars ck bs bs',
      wc_clock vars ck ->
      Forall (fun x => orel (EqSt (A:=svalue)) (H' x) (H x)) (map fst vars) ->
      sem_clock H bs ck bs' ->
      sem_clock H' bs ck bs'.
  Proof.
    induction ck; intros * Hwc Hf Hsem; inv Hwc; inv Hsem.
    - constructor; auto.
    - econstructor; eauto.
      simpl_Forall. inv H9. rewrite H1 in Hf. inv Hf.
      econstructor. symmetry in H0; apply H0.
      now rewrite H3, H7.
  Qed.

  (** ** Clocked semantics *)
  (** We add an alignment predicate to the node case of the semantics, which checks that
      every flow in the node is aligned with its clock.
      We also add this constraint for the anonymous outputs of a node.
      This forces us to constrain anonymous streams to appear in history.
      We also constrain the domain of the history to be closed, that is only
      contain the named and anonymous streams of the node.
   *)
  Section ClockedSemantics.
    Definition sc_vars Γ H bs :=
      (forall x ck xs, HasClock Γ x ck -> sem_var H (Var x) xs -> sem_clock (var_history H) bs ck (abstract_clock xs))
      /\ (forall x ck xs, HasClock Γ x ck -> IsLast Γ x -> sem_var H (Last x) xs -> sem_clock (var_history H) bs ck (abstract_clock xs)).

    Definition clocked_node H bs (env : static_env) :=
      dom H env /\ sc_vars env H bs.

    Context {PSyn : list decl -> block -> Prop}.
    Context {prefs : PS.t}.
    Variable G : @global PSyn prefs.

    Section sem_scope.

      Context {A : Type}.
      Variable sem_block : Sem.history -> A -> Prop.

      Inductive sem_scope_ck : Sem.history -> Stream bool -> (scope A) -> Prop :=
      | Sscope : forall Hi Hi' bs locs blks,
          dom Hi' (senv_of_decls locs) ->
          sc_vars (senv_of_decls locs) (Hi + Hi') bs ->
          sem_block (Hi + Hi') blks ->
          sem_scope_ck Hi bs (Scope locs blks).
    End sem_scope.

    Section sem_branch.
      Context {A : Type}.

      Variable sem_block : A -> Prop.

      Inductive sem_branch_ck : (branch A) -> Prop :=
      | Sbranch : forall caus blks,
          sem_block blks ->
          sem_branch_ck (Branch caus blks).
    End sem_branch.

    Inductive sem_exp_ck : Sem.history -> Stream bool -> exp -> list (Stream svalue) -> Prop :=
    | Sconst:
        forall H bs c cs,
          cs ≡ const bs c ->
          sem_exp_ck H bs (Econst c) [cs]

    | Senum:
        forall H b k ty es,
          es ≡ enum b k ->
          sem_exp_ck H b (Eenum k ty) [es]

    | Svar:
        forall H b x s ann,
          sem_var H (Var x) s ->
          sem_exp_ck H b (Evar x ann) [s]

    | Slast:
      forall H b x s ann,
        sem_var H (Last x) s ->
        sem_exp_ck H b (Elast x ann) [s]

    | Sunop:
        forall H b e op ty s o ann,
          sem_exp_ck H b e [s] ->
          typeof e = [ty] ->
          lift1 op ty s o ->
          sem_exp_ck H b (Eunop op e ann) [o]

    | Sbinop:
        forall H b e1 e2 op ty1 ty2 s1 s2 o ann,
          sem_exp_ck H b e1 [s1] ->
          sem_exp_ck H b e2 [s2] ->
          typeof e1 = [ty1] ->
          typeof e2 = [ty2] ->
          lift2 op ty1 ty2 s1 s2 o ->
          sem_exp_ck H b (Ebinop op e1 e2 ann) [o]

    | Sextcall:
      forall H b f es tyout ck tyins ss vs,
        Forall2 (fun ty cty => ty = Tprimitive cty) (typesof es) tyins ->
        Forall2 (sem_exp_ck H b) es ss ->
        liftn (fun ss => sem_extern f tyins ss tyout) (concat ss) vs ->
        sem_exp_ck H b (Eextcall f es (tyout, ck)) [vs]

    | Sfby:
        forall H b e0s es anns s0ss sss os,
          Forall2 (sem_exp_ck H b) e0s s0ss ->
          Forall2 (sem_exp_ck H b) es sss ->
          Forall3 fby (concat s0ss) (concat sss) os ->
          sem_exp_ck H b (Efby e0s es anns) os

    | Sarrow:
        forall H b e0s es anns s0ss sss os,
          Forall2 (sem_exp_ck H b) e0s s0ss ->
          Forall2 (sem_exp_ck H b) es sss ->
          Forall3 arrow (concat s0ss) (concat sss) os ->
          sem_exp_ck H b (Earrow e0s es anns) os

    | Swhen:
        forall H b x tx s k es lann ss os,
          Forall2 (sem_exp_ck H b) es ss ->
          sem_var H (Var x) s ->
          Forall2 (fun s' => when k s' s) (concat ss) os ->
          sem_exp_ck H b (Ewhen es (x, tx) k lann) os

    | Smerge:
        forall H b x tx s es lann vs os,
          sem_var H (Var x) s ->
          Forall2Brs (sem_exp_ck H b) es vs ->
          Forall2 (merge s) vs os ->
          sem_exp_ck H b (Emerge (x, tx) es lann) os

    | ScaseTotal:
        forall H b e s es tys ck vs os,
          sem_exp_ck H b e [s] ->
          Forall2Brs (sem_exp_ck H b) es vs ->
          Forall2 (fun vs => case s vs None) vs os ->
          sem_exp_ck H b (Ecase e es None (tys, ck)) os

    | ScaseDefault:
        forall H b e s es d lann vs vd os,
          sem_exp_ck H b e [s] ->
          wt_streams [s] (typeof e) ->
          Forall2Brs (sem_exp_ck H b) es vs ->
          Forall2 (sem_exp_ck H b) d vd ->
          Forall3 (case s) vs (List.map Some (concat vd)) os ->
          sem_exp_ck H b (Ecase e es (Some d) lann) os

    | Sapp:
        forall H b f es er lann ss os rs bs,
          Forall2 (sem_exp_ck H b) es ss ->
          Forall2 (fun e r => sem_exp_ck H b e [r]) er rs ->
          bools_ofs rs bs ->
          (forall k, sem_node_ck f (List.map (maskv k bs) (concat ss)) (List.map (maskv k bs) os)) ->
          sem_exp_ck H b (Eapp f es er lann) os

    with sem_equation_ck: Sem.history -> Stream bool -> equation -> Prop :=
      Seq:
        forall H b xs es ss,
          Forall2 (sem_exp_ck H b) es ss ->
          Forall2 (fun x => sem_var H (Var x)) xs (concat ss) ->
          sem_equation_ck H b (xs, es)

    with sem_transitions_ck : Sem.history -> Stream bool -> list (exp * (enumtag * bool)) -> (enumtag * bool) -> Stream (synchronous (enumtag * bool)) -> Prop :=
    | Stransdef : forall H bs default stres,
        stres ≡ const_stres bs default ->
        sem_transitions_ck H bs [] default stres
    | Strans : forall H bs e C r trans default vs bs' stres1 stres,
        sem_exp_ck H bs e [vs] ->
        bools_of vs bs' ->
        sem_transitions_ck H bs trans default stres1 ->
        stres ≡ first_of (C, r) bs' stres1 ->
        sem_transitions_ck H bs ((e, (C, r))::trans) default stres

    with sem_block_ck: Sem.history -> Stream bool -> block -> Prop :=
    | Sbeq:
      forall H b eq,
        sem_equation_ck H b eq ->
        sem_block_ck H b (Beq eq)

    | Slastd:
      forall H bs x e vs0 vs1 vs,
        sem_exp_ck H bs e [vs0] ->
        sem_var H (Var x) vs1 ->
        fby vs0 vs1 vs ->
        sem_var H (Last x) vs ->
        sem_block_ck H bs (Blast x e)

    | Sreset:
      forall H b blocks er sr r,
        sem_exp_ck H b er [sr] ->
        bools_of sr r ->
        (forall k, Forall (sem_block_ck (mask_hist k r H) (maskb k r b)) blocks) ->
        sem_block_ck H b (Breset blocks er)

    | Sswitch:
      forall Hi b ec branches sc,
        sem_exp_ck Hi b ec [sc] ->
        wt_streams [sc] (typeof ec) ->
        Forall (fun blks =>
                  exists Hi', when_hist (fst blks) Hi sc Hi'
                         /\ let bi := fwhenb (fst blks) b sc in
                           sem_branch_ck (Forall (sem_block_ck Hi' bi)) (snd blks)) branches ->
        sem_block_ck Hi b (Bswitch ec branches)

    | SautoWeak:
      forall H bs ini oth states ck bs' stres0 stres1 stres,
        sem_clock (var_history H) bs ck bs' ->
        sem_transitions_ck H bs' (List.map (fun '(e, t) => (e, (t, false))) ini) (oth, false) stres0 ->
        fby stres0 stres1 stres ->
        Forall (fun state =>
                  let tag := fst (fst state) in
                  forall k, exists Hik, select_hist tag k stres H Hik
                              /\ let bik := fselectb tag k stres bs in
                                sem_branch_ck
                                  (fun blks =>
                                     sem_scope_ck
                                       (fun Hi' blks =>
                                          Forall (sem_block_ck Hi' bik) (fst blks)
                                          /\ sem_transitions_ck Hi' bik (snd blks) (tag, false) (fselect absent tag k stres stres1)
                                       ) Hik bik (snd blks)) (snd state)
               ) states ->
        sem_block_ck H bs (Bauto Weak ck (ini, oth) states)

    | SautoStrong:
      forall H bs ini states ck bs' stres stres1,
        sem_clock (var_history H) bs ck bs' ->
        fby (const_stres bs' (ini, false)) stres1 stres ->
        Forall (fun state =>
                  let tag := fst (fst state) in
                  forall k, exists Hik, select_hist tag k stres H Hik
                              /\ let bik := fselectb tag k stres bs in
                                sem_branch_ck
                                  (fun blks =>
                                     sem_transitions_ck Hik bik (fst blks) (tag, false) (fselect absent tag k stres stres1)
                                  ) (snd state)
               ) states ->
        Forall (fun state =>
                  let tag := fst (fst state) in
                  forall k, exists Hik, select_hist tag k stres1 H Hik
                              /\ let bik := fselectb tag k stres1 bs in
                                sem_branch_ck
                                  (fun blks =>
                                     sem_scope_ck
                                       (fun Hi' blks => Forall (sem_block_ck Hi' bik) (fst blks)
                                       ) Hik bik (snd blks)) (snd state)
               ) states ->
        sem_block_ck H bs (Bauto Strong ck ([], ini) states)

    | Slocal:
      forall Hi bs scope,
        sem_scope_ck (fun Hi' => Forall (sem_block_ck Hi' bs)) Hi bs scope ->
        sem_block_ck Hi bs (Blocal scope)

    with sem_node_ck: ident -> list (Stream svalue) -> list (Stream svalue) -> Prop :=
      Snode:
        forall f ss os n H,
          find_node f G = Some n ->
          Forall2 (fun x => sem_var H (Var x)) (List.map fst n.(n_in)) ss ->
          Forall2 (fun x => sem_var H (Var x)) (List.map fst n.(n_out)) os ->
          let bs := clocks_of ss in
          sem_block_ck H bs n.(n_block) ->
          clocked_node H bs (senv_of_ins n.(n_in) ++ senv_of_decls n.(n_out)) ->
          sem_node_ck f ss os.

  End ClockedSemantics.

  Global Hint Constructors sem_exp_ck sem_equation_ck sem_scope_ck sem_branch_ck sem_block_ck : lcsem.

  Ltac inv_exp :=
    match goal with
    | H:sem_exp_ck _ _ _ _ _ |- _ => inv H
    end.

  Ltac inv_scope :=
    match goal with
    | H:sem_scope_ck _ _ _ _ |- _ => inv H
    end;
    destruct_conjs; subst.

  Ltac inv_branch :=
    match goal with
    | H:sem_branch_ck _ _ |- _ => inv H
    end;
    destruct_conjs; subst.

  Ltac inv_block :=
    match goal with
    | H:sem_block_ck _ _ _ _ |- _ => inv H
    end.

  Ltac inv_exp' := (Syn.inv_exp || Clo.inv_exp || Sem.inv_exp || inv_exp).
  Ltac inv_scope' := (Syn.inv_scope || Clo.inv_scope || Sem.inv_scope || inv_scope).
  Ltac inv_branch' := (Syn.inv_branch || Clo.inv_branch || Sem.inv_branch || inv_branch).
  Ltac inv_block' := (Syn.inv_block || Clo.inv_block || Sem.inv_block || inv_block).

  (** Custom induction schemes *)

  Section sem_exp_ind2.
    Context {prefs PSyn} (G: @global prefs PSyn).

    Variable P_exp : Sem.history -> Stream bool -> exp -> list (Stream svalue) -> Prop.
    Variable P_equation : Sem.history -> Stream bool -> equation -> Prop.
    Variable P_transitions : Sem.history -> Stream bool -> list (exp * (enumtag * bool)) -> (enumtag * bool) -> Stream (synchronous (enumtag * bool)) -> Prop.
    Variable P_block : Sem.history -> Stream bool -> block -> Prop.
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
        sem_exp_ck G H b e [s] ->
        P_exp H b e [s] ->
        typeof e = [ty] ->
        lift1 op ty s o ->
        P_exp H b (Eunop op e ann) [o].

    Hypothesis BinopCase:
      forall H b e1 e2 op ty1 ty2 s1 s2 o ann,
        sem_exp_ck G H b e1 [s1] ->
        P_exp H b e1 [s1] ->
        sem_exp_ck G H b e2 [s2] ->
        P_exp H b e2 [s2] ->
        typeof e1 = [ty1] ->
        typeof e2 = [ty2] ->
        lift2 op ty1 ty2 s1 s2 o ->
        P_exp H b (Ebinop op e1 e2 ann) [o].

    Hypothesis ExtcallCase:
      forall H b f es tyout ck tyins ss vs,
        Forall2 (fun cty ty => cty = Tprimitive ty) (typesof es) tyins ->
        Forall2 (sem_exp_ck G H b) es ss ->
        Forall2 (P_exp H b) es ss ->
        liftn (fun ss => sem_extern f tyins ss tyout) (concat ss) vs ->
        P_exp  H b (Eextcall f es (tyout, ck)) [vs].

    Hypothesis FbyCase:
      forall H b e0s es anns s0ss sss os,
        Forall2 (sem_exp_ck G H b) e0s s0ss ->
        Forall2 (P_exp H b) e0s s0ss ->
        Forall2 (sem_exp_ck G H b) es sss ->
        Forall2 (P_exp H b) es sss ->
        Forall3 fby (concat s0ss) (concat sss) os ->
        P_exp H b (Efby e0s es anns) os.

    Hypothesis ArrowCase:
      forall H b e0s es anns s0ss sss os,
        Forall2 (sem_exp_ck G H b) e0s s0ss ->
        Forall2 (P_exp H b) e0s s0ss ->
        Forall2 (sem_exp_ck G H b) es sss ->
        Forall2 (P_exp H b) es sss ->
        Forall3 arrow (concat s0ss) (concat sss) os ->
        P_exp H b (Earrow e0s es anns) os.

    Hypothesis WhenCase:
      forall H b x tx s k es lann ss os,
        Forall2 (sem_exp_ck G H b) es ss ->
        Forall2 (P_exp H b) es ss ->
        sem_var H (Var x) s ->
        Forall2 (fun s' => when k s' s) (concat ss) os ->
        P_exp H b (Ewhen es (x, tx) k lann) os.

    Hypothesis MergeCase:
      forall H b x tx s es lann vs os,
        sem_var H (Var x) s ->
        Forall2Brs (sem_exp_ck G H b) es vs ->
        Forall2Brs (P_exp H b) es vs ->
        Forall2 (merge s) vs os ->
        P_exp H b (Emerge (x, tx) es lann) os.

    Hypothesis CaseTotalCase:
      forall H b e s es tys ck vs os,
        sem_exp_ck G H b e [s] ->
        P_exp H b e [s] ->
        Forall2Brs (sem_exp_ck G H b) es vs ->
        Forall2Brs (P_exp H b) es vs ->
        Forall2 (fun vs => case s vs None) vs os ->
        P_exp H b (Ecase e es None (tys, ck)) os.

    Hypothesis CaseDefaultCase:
      forall H b e s es d lann vs vd os,
        sem_exp_ck G H b e [s] ->
        P_exp H b e [s] ->
        wt_streams [s] (typeof e) ->
        Forall2Brs (sem_exp_ck G H b) es vs ->
        Forall2Brs (P_exp H b) es vs ->
        Forall2 (sem_exp_ck G H b) d vd ->
        Forall2 (P_exp H b) d vd ->
        Forall3 (case s) vs (List.map Some (concat vd)) os ->
        P_exp H b (Ecase e es (Some d) lann) os.

    Hypothesis AppCase:
      forall H b f es er lann ss os sr bs,
        Forall2 (sem_exp_ck G H b) es ss ->
        Forall2 (P_exp H b) es ss ->
        Forall2 (fun e r => sem_exp_ck G H b e [r]) er sr ->
        Forall2 (fun e r => P_exp H b e [r]) er sr ->
        bools_ofs sr bs ->
        (forall k, sem_node_ck G f (List.map (maskv k bs) (concat ss)) (List.map (maskv k bs) os)
              /\ P_node f (List.map (maskv k bs) (concat ss)) (List.map (maskv k bs) os)) ->
        P_exp H b (Eapp f es er lann) os.

    Hypothesis Equation:
      forall H b xs es ss,
        Forall2 (sem_exp_ck G H b) es ss ->
        Forall2 (P_exp H b) es ss ->
        Forall2 (fun x => sem_var H (Var x)) xs (concat ss) ->
        P_equation H b (xs, es).

    Hypothesis BeqCase:
      forall H b eq,
        sem_equation_ck G H b eq ->
        P_equation H b eq ->
        P_block H b (Beq eq).

    Hypothesis BlastdCase:
      forall H bs x e vs0 vs1 vs,
        sem_exp_ck G H bs e [vs0] ->
        P_exp H bs e [vs0] ->
        sem_var H (Var x) vs1 ->
        fby vs0 vs1 vs ->
        sem_var H (Last x) vs ->
        P_block H bs (Blast x e).

    Hypothesis BresetCase:
      forall H b blocks er sr r,
        sem_exp_ck G H b er [sr] ->
        P_exp H b er [sr] ->
        bools_of sr r ->
        (forall k, Forall (sem_block_ck G (mask_hist k r H) (maskb k r b)) blocks /\
                Forall (P_block (mask_hist k r H) (maskb k r b)) blocks) ->
        P_block H b (Breset blocks er).

    Hypothesis BswitchCase:
      forall Hi b ec branches sc,
        sem_exp_ck G Hi b ec [sc] ->
        P_exp Hi b ec [sc] ->
        wt_streams [sc] (typeof ec) ->
        Forall (fun blks => exists Hi', when_hist (fst blks) Hi sc Hi'
                                /\ let bi := fwhenb (fst blks) b sc in
                                  sem_branch_ck (fun blks => Forall (sem_block_ck G Hi' bi) blks
                                                       /\ Forall (P_block Hi' bi) blks
                                    ) (snd blks)) branches ->
        P_block Hi b (Bswitch ec branches).

    Hypothesis TransDefCase:
      forall Hi bs default stres,
        stres ≡ const_stres bs default ->
        P_transitions Hi bs [] default stres.

    Hypothesis TransCase:
      forall Hi bs e C r trans default vs bs' stres1 stres,
        sem_exp_ck G Hi bs e [vs] ->
        P_exp Hi bs e [vs] ->
        bools_of vs bs' ->
        sem_transitions_ck G Hi bs trans default stres1 ->
        P_transitions Hi bs trans default stres1 ->
        stres ≡ first_of (C, r) bs' stres1 ->
        P_transitions Hi bs ((e, (C, r))::trans) default stres.

    Hypothesis BautoWeakCase:
      forall Hi bs ini oth states ck bs' stres0 stres1 stres,
        sem_clock (var_history Hi) bs ck bs' ->
        sem_transitions_ck G Hi bs' (List.map (fun '(e, t) => (e, (t, false))) ini) (oth, false) stres0 ->
        P_transitions Hi bs' (List.map (fun '(e, t) => (e, (t, false))) ini) (oth, false) stres0 ->
        fby stres0 stres1 stres ->
        Forall (fun '((tag, _), br) =>
                  forall k, exists Hik,
                    select_hist tag k stres Hi Hik
                    /\ let bik := fselectb tag k stres bs in
                      sem_branch_ck
                        (fun '(_, scope) =>
                           sem_scope_ck
                             (fun Hi' blks => Forall (sem_block_ck G Hi' bik) (fst blks)
                                           /\ Forall (P_block Hi' bik) (fst blks)
                                           /\ sem_transitions_ck G Hi' bik (snd blks) (tag, false) (fselect absent tag k stres stres1)
                                           /\ P_transitions Hi' bik (snd blks) (tag, false) (fselect absent tag k stres stres1)
                             ) Hik bik scope)
                        br) states ->
        P_block Hi bs (Bauto Weak ck (ini, oth) states).

    Hypothesis BautoStrongCase:
      forall Hi bs ini states ck bs' stres0 stres1,
        sem_clock (var_history Hi) bs ck bs' ->
        fby (const_stres bs' (ini, false)) stres1 stres0 ->
        Forall (fun '((tag, _), br) =>
                  forall k, exists Hik, select_hist tag k stres0 Hi Hik
                              /\ let bik := fselectb tag k stres0 bs in
                                sem_branch_ck
                                  (fun '(unl, _) =>
                                     sem_transitions_ck G Hik bik unl (tag, false) (fselect absent tag k stres0 stres1)
                                     /\ P_transitions Hik bik unl (tag, false) (fselect absent tag k stres0 stres1)
                                  ) br
          ) states ->
        Forall (fun '((tag, _), br) =>
                  forall k, exists Hik,
                    select_hist tag k stres1 Hi Hik
                    /\ let bik := fselectb tag k stres1 bs in
                      sem_branch_ck
                        (fun '(_, scope) =>
                           sem_scope_ck
                             (fun Hi' blks => Forall (sem_block_ck G Hi' bik) (fst blks)
                                           /\ Forall (P_block Hi' bik) (fst blks)
                             ) Hik bik scope)
                        br) states ->
        P_block Hi bs (Bauto Strong ck ([], ini) states).

    Hypothesis BlocalCase:
      forall Hi bs scope,
        sem_scope_ck
          (fun Hi' blks => Forall (sem_block_ck G Hi' bs) blks /\ Forall (P_block Hi' bs) blks)
          Hi bs scope ->
        P_block Hi bs (Blocal scope).

    Hypothesis Node:
      forall f ss os n H,
        find_node f G = Some n ->
        Forall2 (fun x => sem_var H (Var x)) (List.map fst n.(n_in)) ss ->
        Forall2 (fun x => sem_var H (Var x)) (List.map fst n.(n_out)) os ->
        let bs := clocks_of ss in
        sem_block_ck G H bs n.(n_block) ->
        P_block H bs n.(n_block) ->
        clocked_node H bs (senv_of_ins n.(n_in) ++ senv_of_decls n.(n_out)) ->
        P_node f ss os.

    Local Ltac SolveForall :=
      match goal with
      | H: Forall ?P1 ?l |- Forall ?P2 ?l =>
          induction H; eauto
      | H: Forall2 ?P1 ?l1 ?l2 |- Forall2 ?P2 ?l1 ?l2 =>
          induction H; eauto
      | _ => idtac
      end.

    Fixpoint sem_exp_ck_ind2
      (H: Sem.history) (b: Stream bool) (e: exp) (ss: list (Stream svalue))
      (Sem: sem_exp_ck G H b e ss)
      {struct Sem}
      : P_exp H b e ss
    with sem_equation_ck_ind2
           (H: Sem.history) (b: Stream bool) (e: equation)
           (Sem: sem_equation_ck G H b e)
           {struct Sem}
      : P_equation H b e
    with sem_transitions_ind2
           (H: Sem.history) (b: Stream bool) trans default stres
           (Sem: sem_transitions_ck G H b trans default stres)
           {struct Sem}
      : P_transitions H b trans default stres
    with sem_block_ck_ind2
           (H: Sem.history) (b: Stream bool) (d: block)
           (Sem: sem_block_ck G H b d)
           {struct Sem}
      : P_block H b d
    with sem_node_ck_ind2
           (f: ident) (ss os: list (Stream svalue))
           (Sem: sem_node_ck G f ss os)
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
          * clear - sem_exp_ck_ind2 H3.
            induction H3; econstructor; eauto. clear IHForall2Brs H1 H3. SolveForall.
          * clear - sem_exp_ck_ind2 H4.
            SolveForall.
        + eapply AppCase; eauto; clear H3 H4; SolveForall.
      - inv Sem.
        eapply Equation with (ss:=ss); eauto; clear H2; SolveForall.
      - inv Sem.
        + eapply TransDefCase; eauto.
        + eapply TransCase; eauto.
      - inv Sem.
        + eapply BeqCase; eauto.
        + eapply BlastdCase; eauto.
        + eapply BresetCase; eauto.
          intros k. specialize (H3 k). split; eauto. SolveForall.
        + eapply BswitchCase; eauto.
          SolveForall. constructor; auto.
          destruct_conjs. inv H4. do 2 esplit; eauto.
          econstructor; eauto. split; auto.
          simpl. SolveForall.
        + eapply BautoWeakCase; eauto.
          SolveForall; destruct_conjs. constructor; auto.
      intros k. specialize (H0 k). destruct_conjs.
      inv_branch'. inv_scope'.
      do 2 esplit; eauto.
      do 2 econstructor; eauto. split; [|split; [|split]]; eauto.
      * simpl. SolveForall.
      + eapply BautoStrongCase; eauto.
        * clear - H3 sem_transitions_ind2. SolveForall. destruct_conjs. constructor; auto.
          intros k. specialize (H0 k). destruct_conjs. take (sem_branch_ck _ _) and inv it. destruct_conjs.
          do 2 esplit; eauto. econstructor; eauto.
        * clear H3. SolveForall. destruct_conjs. constructor; auto.
          intros k. specialize (H0 k). destruct_conjs.
          inv_branch'. inv_scope'.
          do 2 esplit; eauto. do 2 econstructor; eauto.
          split; auto; simpl.
          SolveForall.
      + eapply BlocalCase; eauto.
        inv H0. econstructor; eauto. split; auto; SolveForall.
      - inv Sem.
        eapply Node; eauto.
    Qed.

  End sem_exp_ind2.

  Lemma sem_block_defined {PSyn prefs} (G: @global PSyn prefs) : forall blk H bs x,
      sem_block_ck G H bs blk ->
      Syn.Is_defined_in x blk ->
      FEnv.In x H.
  Proof.
    induction blk using block_ind2; intros * Hsem Hdef; inv Hsem; inv Hdef.
    - (* equation *)
      inv H4. eapply Forall2_ignore2, Forall_forall in H8 as (?&?&?); eauto using sem_var_In.
    - (* last *)
      eauto using sem_var_In.
    - (* reset *)
      simpl_Exists.
      specialize (H8 0). simpl_Forall.
      eapply H in H8; eauto. now setoid_rewrite FEnv.map_in_iff in H8.
    - (* switch *)
      simpl_Exists; simpl_Forall.
      repeat inv_branch'.
      simpl_Exists. simpl_Forall.
      eapply FEnv.In_refines; eauto.
    - (* automaton (weak) *)
      simpl_Exists; simpl_Forall. specialize (H11 0); destruct_conjs.
      repeat inv_branch'. repeat inv_scope'.
      simpl_Exists. simpl_Forall.
      eapply FEnv.In_refines; eauto.
      eapply H, FEnv.union_In in H4 as [|Hin']; eauto.
      exfalso. take (~ _) and eapply it.
      take (dom _ _) and apply it in Hin'. inv Hin'. solve_In.
    - (* automaton (strong) *)
      simpl_Exists; simpl_Forall. specialize (H11 0); destruct_conjs.
      repeat inv_branch'. repeat inv_scope'.
      simpl_Exists. simpl_Forall.
      eapply FEnv.In_refines; eauto.
      take (sem_block_ck _ _ _ _) and eapply H, FEnv.union_In in it as [|Hin']; eauto.
      exfalso. take (~ _) and eapply it.
      take (dom _ _) and apply it in Hin'. inv Hin'. solve_In.
    - (* local *)
      repeat inv_scope'. simpl_Exists; simpl_Forall.
      take (sem_block_ck _ _ _ _) and eapply H, FEnv.union_In in it as [|Hin']; eauto.
      exfalso. take (~ _) and eapply it.
      destruct x; take (dom _ _) and apply it in Hin'; inv Hin'; solve_In.
  Qed.

  Section sem_refines.
    Context {PSyn prefs} (G: @global PSyn prefs).

    Fact sem_exp_refines : forall b e H H' v,
        H ⊑ H' ->
        sem_exp_ck G H b e v ->
        sem_exp_ck G H' b e v.
    Proof with eauto with datatypes.
      induction e using exp_ind2; intros * Href Hsem; inv Hsem;
        econstructor; eauto using sem_var_refines; simpl_Forall; eauto.
      1-3:(eapply Forall2Brs_impl_In; [|eauto]; intros;
           simpl_Exists; simpl_Forall; eauto).
    Qed.

    Fact sem_equation_refines : forall H H' b equ,
        H ⊑ H' ->
        sem_equation_ck G H b equ ->
        sem_equation_ck G H' b equ.
    Proof with eauto.
      intros * Href Hsem. inv Hsem.
      apply Seq with (ss:=ss); simpl_Forall;
        eauto using sem_exp_refines, sem_var_refines.
    Qed.

    Fact sc_vars_refines : forall Γ H H' b,
        H ⊑ H' ->
        (forall x, IsVar Γ x -> FEnv.In (Var x) H' -> FEnv.In (Var x) H) ->
        (forall x, IsLast Γ x -> FEnv.In (Last x) H' -> FEnv.In (Last x) H) ->
        sc_vars Γ H b ->
        sc_vars Γ H' b.
    Proof.
      intros * Href Var Last (Hsc1&Hsc2).
      split; intros; simpl; eauto using sem_clock_refines.
      1,2:eapply sem_clock_refines; eauto using var_history_refines.
      + eapply Hsc1; eauto.
        eapply sem_var_refines'; eauto using sem_var_In, HasClock_IsVar.
      + eapply Hsc2; eauto.
        eapply sem_var_refines'; eauto using sem_var_In.
    Qed.

    Fact sem_transitions_refines : forall H H' b trans default stres,
        H ⊑ H' ->
        sem_transitions_ck G H b trans default stres ->
        sem_transitions_ck G H' b trans default stres.
    Proof with eauto.
      induction trans; intros * Href Hsem; inv Hsem;
        econstructor; eauto using sem_exp_refines.
    Qed.

    Lemma sem_scope_refines {A} P_sem : forall locs (blk: A) H H' bs,
        H ⊑ H' ->
        sem_scope_ck P_sem H bs (Scope locs blk) ->
        (forall H H',
            H ⊑ H' ->
            P_sem H blk ->
            P_sem H' blk) ->
        sem_scope_ck P_sem H' bs (Scope locs blk).
    Proof.
      intros * Href Hsem Hind; inv Hsem.
      assert (H + Hi' ⊑ H' + Hi') as Href2.
      { eapply FEnv.union_refines1; eauto using EqStrel_Reflexive. }
      econstructor; eauto.
      take (sc_vars _ _ _) and destruct it as (Hsc1&Hsc2).
      split; intros; simpl.
      1,2:eapply sem_clock_refines; eauto using var_history_refines.
      + eapply Hsc1; eauto. apply sem_var_union3'.
        apply sem_var_union' in H1 as [(?&?)|]; eauto.
        exfalso. eapply H1, H2. take (HasClock _ _ _) and inv it; eauto with senv.
      + eapply Hsc2; eauto. apply sem_var_union3'.
        apply sem_var_union' in H3 as [(?&?)|]; eauto.
        exfalso. eapply H3, H2; eauto.
    Qed.

    Lemma sem_block_refines : forall blk H H' bs,
        H ⊑ H' ->
        sem_block_ck G H bs blk ->
        sem_block_ck G H' bs blk.
    Proof.
      induction blk using block_ind2; intros * Href Hsem;
        inv Hsem.
      - (* eq *)
        constructor; eauto using sem_equation_refines.
      - (* last *)
        econstructor; eauto using sem_exp_refines, sem_var_refines.
      - (* reset *)
        econstructor; eauto using sem_exp_refines.
        intros k. specialize (H8 k).
        simpl_Forall.
        eapply H; [|eauto]; eauto using refines_mask.
      - (* switch *)
        econstructor; eauto using sem_exp_refines.
        simpl_Forall.
        do 2 esplit; eauto.
        intros ?? Hfind. apply H2 in Hfind as (?&Hfilter&Hfind').
        apply Href in Hfind' as (?&?&?). do 2 esplit; [|eauto].
        now rewrite <-H5.
      - (* automaton (weak) *)
        econstructor; eauto using sem_clock_refines, var_history_refines, sem_transitions_refines.
        simpl_Forall. specialize (H11 k); destruct_conjs.
        do 2 esplit; [|eauto].
        intros ?? Hfind. apply H2 in Hfind as (?&Hfilter&Hfind').
        apply Href in Hfind' as (?&?&?). do 2 esplit; [|eauto].
        now rewrite <-H4.
      - (* automaton (strong) *)
        econstructor; eauto using sem_clock_refines, var_history_refines, sem_transitions_refines.
        + simpl_Forall. specialize (H10 k); destruct_conjs.
          do 2 esplit; eauto.
          intros ?? Hfind. apply H2 in Hfind as (?&Hfilter&Hfind').
          apply Href in Hfind' as (?&?&?). do 2 esplit; [|eauto].
          now rewrite <-H4.
        + simpl_Forall. specialize (H11 k); destruct_conjs.
          do 2 esplit; [|eauto].
          intros ?? Hfind. apply H2 in Hfind as (?&Hfilter&Hfind').
          apply Href in Hfind' as (?&?&?). do 2 esplit; [|eauto].
          now rewrite <-H4.
      - (* local *)
        constructor. eapply sem_scope_refines; eauto.
        intros; simpl_Forall; eauto.
    Qed.

    Corollary sem_scope_refines1 : forall locs blk H H' bs,
        H ⊑ H' ->
        sem_scope_ck
          (fun Hi => Forall (sem_block_ck G Hi bs)) H bs (Scope locs blk) ->
        sem_scope_ck
          (fun Hi => Forall (sem_block_ck G Hi bs)) H' bs (Scope locs blk).
    Proof.
      intros.
      eapply sem_scope_refines; eauto.
      intros; simpl_Forall; eauto using sem_block_refines.
    Qed.

    Corollary sem_scope_refines2 : forall locs blk def stres H H' bs,
        H ⊑ H' ->
        sem_scope_ck
          (fun Hi blks => Forall (sem_block_ck G Hi bs) (fst blks)
                       /\ sem_transitions_ck G Hi bs (snd blks) def stres) H bs (Scope locs blk) ->
        sem_scope_ck
          (fun Hi blks => Forall (sem_block_ck G Hi bs) (fst blks)
                       /\ sem_transitions_ck G Hi bs (snd blks) def stres) H' bs (Scope locs blk).
    Proof.
      intros.
      eapply sem_scope_refines; eauto.
      intros; destruct_conjs.
      split; simpl_Forall; eauto using sem_block_refines, sem_transitions_refines.
    Qed.

    Corollary sem_scope_refines3 {T} : forall locs (blk: _ * T) H H' bs,
        H ⊑ H' ->
        sem_scope_ck
          (fun Hi blks => Forall (sem_block_ck G Hi bs) (fst blks)) H bs (Scope locs blk) ->
        sem_scope_ck
          (fun Hi blks => Forall (sem_block_ck G Hi bs) (fst blks)) H' bs (Scope locs blk).
    Proof.
      intros.
      eapply sem_scope_refines; eauto.
      intros; destruct_conjs.
      simpl_Forall; eauto using sem_block_refines.
    Qed.

  End sem_refines.

  Local Hint Constructors Sem.sem_exp Sem.sem_equation Sem.sem_block : lcsem.

  Lemma sc_vars_app : forall Γ1 Γ2 Hi bs,
      (forall x, InMembers x Γ1 -> ~InMembers x Γ2) ->
      sc_vars Γ1 Hi bs ->
      sc_vars Γ2 Hi bs ->
      sc_vars (Γ1 ++ Γ2) Hi bs.
  Proof.
    intros * Hnd (Hsc1&Hsc2) (Hsc3&Hsc4).
    split; intros * Hck; [|intros Hca]; rewrite HasClock_app in Hck.
    - destruct Hck; eauto.
    - rewrite IsLast_app in Hca.
      destruct Hca, Hck; eauto; exfalso.
      1,2:eapply Hnd; inv H; inv H0; eauto using In_InMembers.
  Qed.

  Lemma sc_vars_incl : forall Γ1 Γ2 Hi bs,
      incl Γ2 Γ1 ->
      sc_vars Γ1 Hi bs ->
      sc_vars Γ2 Hi bs.
  Proof.
    intros * Hincl (Hsc1&Hsc2).
    split; intros; eauto with senv.
  Qed.

  Lemma local_hist_sc_vars : forall (Γ Γ': static_env) locs H H' bs,
      incl (map fst Γ') (map fst Γ) ->
      (forall x, InMembers x locs -> ~IsVar Γ x) ->
      dom_ub H Γ ->
      dom H' (senv_of_decls locs) ->
      sc_vars Γ' H bs ->
      sc_vars (senv_of_decls locs) (H + H') bs ->
      sc_vars (Γ' ++ senv_of_decls locs) (H + H') bs.
  Proof.
    intros * Hincl Hnd Hdom1 Hdom2 Hsc1 Hsc2.
    assert (H ⊑ H + H') as Href1 by eauto using local_hist_dom_ub_refines.
    apply sc_vars_app; auto.
    - intros * Hin1 Hin2. rewrite InMembers_senv_of_decls in Hin2.
      eapply Hnd; eauto. constructor. rewrite fst_InMembers in *; eauto.
    - destruct Hsc1 as (Hsc1&Hsc1l). split.
      + intros * Hck Hv. eapply sem_clock_refines, Hsc1; eauto using var_history_refines.
        apply sem_var_union in Hv as [Hv|Hv]; auto.
        apply sem_var_In, Hdom2, IsVar_senv_of_decls in Hv.
        inv Hck. exfalso. eapply Hnd; eauto. econstructor. rewrite fst_InMembers. eapply Hincl; solve_In.
      + intros * Hck Hlast Hv. eapply sem_clock_refines, Hsc1l; eauto using var_history_refines.
        apply sem_var_union in Hv as [Hv|Hv]; auto.
        apply sem_var_In, Hdom2, IsLast_senv_of_decls in Hv.
        inv Hck. exfalso. eapply Hnd; eauto. econstructor. rewrite fst_InMembers. eapply Hincl; solve_In.
  Qed.

  (** Morphism properties *)

  Local Hint Constructors sem_exp : lcsem.

  Add Parametric Morphism : sc_vars
      with signature @Permutation _ ==> history_equiv ==> @EqSt bool ==> Basics.impl
        as sc_vars_morph.
  Proof.
    intros ?? Hperm ?? EH ?? Heq2 (?&?).
    split; intros.
    - rewrite <-Hperm in H1.
      rewrite <-EH in *; eauto. rewrite <-Heq2; eauto.
    - rewrite <-Hperm in H1. rewrite <-Hperm in H2.
      rewrite <-EH in *; eauto. rewrite <-Heq2; eauto.
  Qed.

  Add Parametric Morphism : clocked_node
      with signature eq ==> @EqSt _ ==> eq ==> Basics.impl
        as clocked_node_morph.
  Proof.
    intros H bs bs' Hb ? (Hdom&Hsc).
    split; auto.
    rewrite <-Hb; auto.
  Qed.

  Local Hint Resolve clocked_node_morph_Proper : lcsem.

  Add Parametric Morphism {PSyn prefs} (G: @global PSyn prefs) : (sem_exp_ck G)
      with signature history_equiv ==> @EqSt bool ==> eq ==> @EqSts svalue ==> Basics.impl
        as sem_exp_ck_morph.
  Proof.
    intros H H' EH b b' Eb e xs xs' Exs Hsem. revert xs xs' Hsem Exs.
    induction e using exp_ind2; intros; inv Hsem; unfold EqSts in *; simpl_Forall.
    - econstructor. now rewrite <-Eb, <-H2.
    - econstructor. now rewrite <-Eb, <-H2.
    - constructor. now rewrite <-EH, <-H2.
    - constructor. now rewrite <-EH, <-H2.
    - econstructor; eauto.
      + eapply IHe; eauto. reflexivity.
      + now take (_ ≡ y) and rewrite <-it.
    - econstructor; eauto.
      + eapply IHe1; eauto; reflexivity.
      + eapply IHe2; eauto; reflexivity.
      + now take (_ ≡ y) and rewrite <-it.
    - eapply Sextcall with (ss:=ss); simpl_Forall; eauto.
      + eapply H0; eauto; reflexivity.
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
      + eapply Forall2_EqSt_Proper; eauto. solve_proper.
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

  Add Parametric Morphism {PSyn prefs} (G: @global PSyn prefs) : (sem_equation_ck G)
      with signature history_equiv ==> @EqSt bool ==> eq ==> Basics.impl
        as sem_equation_ck_morph.
  Proof.
    unfold Basics.impl; intros H H' EH xs xs' Exss eq Hsem.
    inversion_clear Hsem as [????? Hseme Hsemv]. econstructor; eauto.
    - eapply Forall2_impl_In; [|eauto]; intros.
      eapply sem_exp_ck_morph; eauto. reflexivity.
    - eapply Forall2_impl_In; [|eauto]; intros.
      now rewrite <-EH.
  Qed.

  Add Parametric Morphism {PSyn prefs} (G: @global PSyn prefs) : (sem_transitions_ck G)
      with signature history_equiv ==> @EqSt bool ==> eq ==> eq ==> @EqSt _ ==> Basics.impl
        as sem_transitions_ck_morph.
  Proof.
    intros H H' EH ?? Eb ???? Estres Hsem.
    revert dependent y3.
    induction Hsem; intros * Heq; econstructor; eauto.
    - rewrite <-Heq, <-Eb; auto.
    - now rewrite <-EH, <-Eb.
    - eapply IHHsem; eauto. reflexivity.
    - now rewrite <-Heq.
  Qed.

  Fact sem_scope_ck_morph {A} P_blk1 (P_blk2: _ -> _ -> Prop) {PSyn prefs} (G: @global PSyn prefs) :
    forall Hi1 Hi2 bs1 bs2 locs (blks: A),
      sem_scope_ck P_blk1 Hi1 bs1 (Scope locs blks) ->
      history_equiv Hi1 Hi2 ->
      bs1 ≡ bs2 ->
      (forall Hi1 Hi2, history_equiv Hi1 Hi2 -> P_blk1 Hi1 blks -> P_blk2 Hi2 blks) ->
      sem_scope_ck P_blk2 Hi2 bs2 (Scope locs blks).
  Proof.
    intros * Hsem EH Eb Hind; inv Hsem.
    assert (history_equiv (Hi1+Hi') (Hi2+Hi')) as EH'.
    { apply FEnv.union_Equiv; auto; reflexivity. }
    econstructor; eauto.
    - now rewrite <-EH', <-Eb.
  Qed.

  Add Parametric Morphism {PSyn prefs} (G: @global PSyn prefs) : (sem_block_ck G)
      with signature history_equiv ==> @EqSt bool ==> eq ==> Basics.impl
        as sem_block_ck_morph.
  Proof.
    unfold Basics.impl. intros H H' EH bs bs' Hbs b Hsem. revert H' bs' EH Hbs.
    eapply sem_block_ck_ind2
      with (P_block := fun H bs b => forall H' bs', history_equiv H H' -> bs ≡ bs' -> sem_block_ck G H' bs' b)
           (P_exp := fun _ _ _ _ => True)
           (P_equation := fun _ _ _ => True)
           (P_transitions := fun _ _ _ _ _ => True)
           (P_node := fun _ _ _ => True); intros; eauto;
      take (_ ≡ _) and rename it into Eb; take (history_equiv _ _) and rename it into EH.
    - constructor. eapply sem_equation_ck_morph; eauto.
    - econstructor; eauto.
      all:rewrite <-EH; auto. now rewrite <-Eb.
    - econstructor; eauto.
      + eapply sem_exp_ck_morph; eauto. reflexivity.
      + intros k. specialize (H4 k) as (Hsem1&Hsem1').
        eapply Forall_Forall in Hsem1; eauto. clear Hsem1'.
        eapply Forall_impl; [|eauto].
        intros ? (?&?). eapply H4; eauto.
        * now rewrite <-EH.
        * now rewrite <-Eb.
    - econstructor; eauto.
      + now rewrite <-EH, <-Eb.
      + simpl_Forall. inv_branch'.
        do 2 esplit. 2:econstructor; eauto.
        * rewrite <-EH at 1. eauto.
        * simpl_Forall. eapply H6; eauto. reflexivity. now rewrite <-Eb.
    - econstructor; eauto.
      + rewrite <-EH, <-Eb; eauto.
      + now rewrite <-EH.
      + simpl_Forall. specialize (H4 k) as (Hik&?). destruct_conjs.
        inv_branch'. inv_scope'.
        exists Hik. split; [|do 2 econstructor]; eauto.
        * now rewrite <-EH.
        * now rewrite <-Eb.
        * split; simpl_Forall. eapply H9; eauto. reflexivity. 1,2:now rewrite <-Eb.
    - econstructor; eauto.
      + now rewrite <-EH, <-Eb.
      + simpl_Forall. specialize (H2 k) as (Hik&?). destruct_conjs. inv_branch'.
        do 2 esplit; eauto. 2:econstructor; rewrite <-Eb; eauto.
        now rewrite <-EH.
      + simpl_Forall. specialize (H3 k) as (Hik&?). destruct_conjs.
        inv_branch'. inv_scope'.
        exists Hik. split; [|do 2 econstructor]; eauto.
        * now rewrite <-EH.
        * now rewrite <-Eb.
        * simpl_Forall. eapply H8; eauto. reflexivity. now rewrite <-Eb.
    - constructor.
      inv_scope'.
      assert (history_equiv (Hi+Hi') (H'+Hi')) as EH'.
      { apply FEnv.union_Equiv; auto. reflexivity. }
      econstructor; eauto.
      + now rewrite <-EH', <-Eb.
      + simpl_Forall; eauto.
  Qed.

  Add Parametric Morphism {PSyn prefs} (G: @global PSyn prefs) : (sem_node_ck G)
      with signature eq ==> @EqSts svalue ==> @EqSts svalue ==> Basics.impl
        as sem_node_ck_morph.
  Proof.
    unfold Basics.impl; intros f xss xss' Exss yss yss' Eyss Sem.
    induction Sem.
    subst.
    econstructor; try reflexivity; eauto.
    + eapply Forall2_trans_ex in Exss; [|eauto].
      simpl_Forall. take (_ ≡ _) and rewrite <-it; eauto.
    + eapply Forall2_trans_ex in Eyss; [|eauto].
      simpl_Forall. take (_ ≡ _) and rewrite <-it; eauto.
    + now rewrite <-Exss.
    + eapply clocked_node_morph; eauto.
      now rewrite <-Exss.
  Qed.

  Section sem_restrict.
    Context {PSyn prefs} (G: @global PSyn prefs).

    Hypothesis HwcG : wc_global G.

    Fact sem_exp_restrict : forall Γ H b e vs,
        wx_exp Γ e ->
        sem_exp_ck G H b e vs ->
        sem_exp_ck G (restrict H Γ) b e vs.
    Proof.
      induction e using exp_ind2; intros vs Hwt Hsem; inv Hwt; inv Hsem;
        econstructor; eauto; simpl_Forall; eauto.
      1-4:(eapply sem_var_restrict; eauto; try eapply vars_of_senv_Var; try eapply vars_of_senv_Last; eauto).
      1-3:(eapply Forall2Brs_impl_In; [|eauto]; intros ?? Hin Hse;
           simpl_Exists; simpl_Forall; eauto).
      specialize (H8 _ eq_refl). simpl_Forall; eauto.
    Qed.

    Lemma sem_equation_restrict : forall Γ H b eq,
        wx_equation Γ eq ->
        sem_equation_ck G H b eq ->
        sem_equation_ck G (restrict H Γ) b eq.
    Proof with eauto with datatypes.
      intros ??? [xs es] Hwc Hsem.
      destruct Hwc as (?&?). inv Hsem.
      econstructor. instantiate (1:=ss).
      + simpl_Forall; eauto using sem_exp_restrict.
      + simpl_Forall. inv H1. eapply sem_var_restrict...
        now apply vars_of_senv_Var.
    Qed.

    Fact sc_vars_restrict : forall locs Γ H bs,
        incl (map fst locs) (map fst Γ) ->
        Forall (wc_clock (idck Γ)) (map snd (idck locs)) ->
        sc_vars locs H bs ->
        sc_vars locs (restrict H Γ) bs.
    Proof.
      intros * Hincl Hwc1 (?&?).
      split; auto; simpl_Forall; intros.
      - eapply sem_var_restrict_inv in H3 as (_&Hv).
        eapply sem_clock_var_history_restrict; [|eauto].
        apply wc_clock_wx_clock. inv H2.
        eapply Forall_forall in Hwc1; eauto. 2:solve_In. auto.
      - eapply sem_var_restrict_inv in H4 as (_&Hv).
        eapply sem_clock_var_history_restrict; [|eauto].
        apply wc_clock_wx_clock. inv H2.
        eapply Forall_forall in Hwc1; eauto. 2:solve_In. auto.
    Qed.

    Fact sem_transitions_restrict : forall Γ H b trans default stres,
        Forall (fun '(e, _) => wx_exp Γ e) trans ->
        sem_transitions_ck G H b trans default stres ->
        sem_transitions_ck G (restrict H Γ) b trans default stres.
    Proof with eauto.
      induction trans; intros * Hwx Hsem; inv Hwx; inv Hsem;
        econstructor; eauto using sem_exp_restrict.
    Qed.

    Lemma sem_scope_restrict {A} (P_wc: _ -> _ -> Prop) (sem_block : _ -> _ -> Prop) :
      forall Γ Hi bs locs (blks : A),
        wc_env (idck Γ) ->
        wc_scope P_wc G Γ (Scope locs blks) ->
        sem_scope_ck sem_block Hi bs (Scope locs blks) ->
        (forall Γ Hi Hi',
            wc_env (idck Γ) ->
            P_wc Γ blks ->
            sem_block Hi blks ->
            FEnv.Equiv (@EqSt _) Hi' (restrict Hi Γ) ->
            sem_block Hi' blks) ->
        sem_scope_ck sem_block (restrict Hi Γ) bs (Scope locs blks).
    Proof.
      intros * Hwenv Hwc Hsem Hind; inv Hwc; subst Γ'; inv Hsem.
      assert (FEnv.Equiv (@EqSt _) (restrict (Hi + Hi') (Γ ++ senv_of_decls locs))
              (restrict Hi Γ + Hi')) as Heq.
      { simpl. symmetry.
        intros ?. unfold FEnv.union, restrict, FEnv.restrict, vars_of_senv.
        rewrite flat_map_app, existsb_app.
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
      - eapply sc_vars_morph, sc_vars_restrict. 6:eauto.
        5:{ simpl_Forall. simpl_In. simpl_Forall. eauto. } all:try reflexivity.
        2:solve_incl_app.
        apply Heq.
      - eapply Hind with (Γ:=Γ++senv_of_decls locs) in H7; eauto.
        + unfold idck. rewrite map_app. apply wc_env_app; auto.
          simpl_Forall. simpl_In. simpl_Forall. rewrite <-map_app. eauto.
        + now symmetry.
    Qed.

    Lemma sem_block_restrict : forall blk Γ H b,
        wc_env (idck Γ) ->
        wc_block G Γ blk ->
        sem_block_ck G H b blk ->
        sem_block_ck G (restrict H Γ) b blk.
    Proof with eauto with lclocking.
      induction blk using block_ind2; intros * Hwenv1 Hwc Hsem; inv Hwc; inv Hsem.
      - (* equation *)
        econstructor.
        eapply sem_equation_restrict...
      - (* last *)
        econstructor; eauto using sem_exp_restrict with lclocking.
        all:(eapply sem_var_restrict; eauto; try eapply vars_of_senv_Var; try eapply vars_of_senv_Last; eauto).
        eauto using IsLast_IsVar.
      - (* reset *)
        econstructor; eauto.
        + eapply sem_exp_restrict...
        + intros k; specialize (H11 k).
          simpl_Forall.
          eapply sem_block_refines; try eapply H; eauto.
          now setoid_rewrite <-FEnv.restrict_map.
      - (* switch *)
        econstructor; eauto.
        + eapply sem_exp_restrict...
        + simpl_Forall. repeat (Clo.inv_branch || inv_branch). do 2 esplit.
          2:{ simpl_Forall. constructor. simpl_Forall. eapply H with (Γ:=Γ'); eauto.
              eapply Forall_forall. intros (?&?) Hin. simpl_In. edestruct H6 as (?&Heq); eauto with senv; subst.
              rewrite Heq. constructor. }
          intros ?? Hfind. apply FEnv.restrict_find_inv in Hfind as (Hin&Hfind).
          eapply H2 in Hfind as (?&Hfilter&Hfind').
          do 2 esplit; eauto. apply FEnv.restrict_find; auto.
          destruct x0; [rewrite vars_of_senv_Var in *|rewrite vars_of_senv_Last in *]; eauto.
          inv Hin. simpl_In. edestruct H6 as (?&?); eauto with senv.
      - (* automaton (weak) *)
        econstructor; eauto.
        + eapply sem_clock_var_history_restrict; eauto with lclocking.
        + eapply sem_transitions_restrict; eauto. simpl_Forall.
          eapply wx_exp_incl with (Γ:=Γ'); eauto with lclocking.
          intros * Hv. inv Hv. apply fst_InMembers in H4; simpl_In.
          edestruct H8 as (?&?); eauto with senv.
        + simpl_Forall. specialize (H18 k); destruct_conjs.
          esplit; split.
          2:{ repeat (Clo.inv_branch || inv_branch). constructor.
              destruct s. eapply sem_scope_restrict with (Γ:=Γ') in H12; eauto.
              - eapply Forall_forall. intros (?&?) Hin. simpl_In. edestruct H8 as (?&Heq); eauto with senv; subst.
                rewrite Heq. constructor.
              - intros; simpl in *; destruct_conjs.
                split; simpl_Forall; eauto.
                + eapply sem_block_ck_morph, H; eauto; try reflexivity. symmetry; apply H15.
                + eapply sem_transitions_ck_morph, sem_transitions_restrict; eauto; try reflexivity.
                  symmetry; apply H15.
                  simpl_Forall; eauto with lclocking. }
          intros ?? Hfind. apply FEnv.restrict_find_inv in Hfind as (Hin&Hfind).
          eapply H2 in Hfind as (?&Hfilter&Hfind').
          do 2 esplit; eauto. apply FEnv.restrict_find; auto.
          destruct x0; [rewrite vars_of_senv_Var in *|rewrite vars_of_senv_Last in *]; eauto.
          inv Hin. simpl_In. edestruct H8 as (?&?); eauto with senv.
      - (* automaton (strong) *)
        econstructor; eauto.
        + eapply sem_clock_var_history_restrict; eauto with lclocking.
        + simpl_Forall. specialize (H17 k); destruct_conjs.
          do 2 esplit.
          2:{ repeat (Clo.inv_branch || inv_branch). constructor.
              eapply sem_transitions_restrict; [|eauto]; simpl_Forall; eauto with lclocking. }
          intros ?? Hfind. apply FEnv.restrict_find_inv in Hfind as (Hin&Hfind).
          eapply H2 in Hfind as (?&Hfilter&Hfind').
          do 2 esplit; eauto. apply FEnv.restrict_find; auto.
          destruct x0; [rewrite vars_of_senv_Var in *|rewrite vars_of_senv_Last in *]; eauto.
          inv Hin. simpl_In. edestruct H8 as (?&?); eauto with senv.
        + simpl_Forall. specialize (H18 k); destruct_conjs.
          esplit; split.
          2:{ repeat (Clo.inv_branch || inv_branch). constructor.
              destruct s. eapply sem_scope_restrict with (Γ:=Γ') in H11; eauto.
              - eapply Forall_forall. intros (?&?) Hin. simpl_In. edestruct H8 as (?&Heq); eauto with senv; subst.
                rewrite Heq. constructor.
              - intros; simpl in *; destruct_conjs. simpl_Forall.
                eapply sem_block_ck_morph, H; eauto; try reflexivity. symmetry; apply H13. }
          intros ?? Hfind. apply FEnv.restrict_find_inv in Hfind as (Hin&Hfind).
          eapply H2 in Hfind as (?&Hfilter&Hfind').
          do 2 esplit; eauto. apply FEnv.restrict_find; auto.
          destruct x0; [rewrite vars_of_senv_Var in *|rewrite vars_of_senv_Last in *]; eauto.
          inv Hin. simpl_In. edestruct H8 as (?&?); eauto with senv.
      - (* locals *)
        constructor. eapply sem_scope_restrict; eauto.
        intros; simpl_Forall.
        eapply sem_block_ck_morph, H; eauto; try reflexivity. symmetry; apply H6.
    Qed.

    Corollary sem_scope_restrict2 : forall locs blk def stres Γ H bs,
        wc_env (idck Γ) ->
        wc_scope (fun Γ blks => Forall (wc_block G Γ) (fst blks)
                             /\ Forall (fun '(e, (_, _)) => wc_exp G Γ e /\ clockof e = [Cbase]) (snd blks))
                 G Γ (Scope locs blk) ->
        sem_scope_ck (fun Hi blks => Forall (sem_block_ck G Hi bs) (fst blks)
                                  /\ sem_transitions_ck G Hi bs (snd blks) def stres) H bs (Scope locs blk) ->
        sem_scope_ck (fun Hi blks => Forall (sem_block_ck G Hi bs) (fst blks)
                                  /\ sem_transitions_ck G Hi bs (snd blks) def stres)
                     (restrict H Γ) bs (Scope locs blk).
    Proof.
      intros.
      eapply sem_scope_restrict; eauto.
      intros; destruct_conjs.
      split; simpl_Forall; eauto;
        [eapply sem_block_ck_morph, sem_block_restrict
        |eapply sem_transitions_ck_morph, sem_transitions_restrict]; eauto; try (symmetry; apply H6); try reflexivity.
      simpl_Forall; eauto with lclocking.
    Qed.

    Corollary sem_scope_restrict3 : forall locs (blk: _ * list transition) Γ H bs,
        wc_env (idck Γ) ->
        wc_scope (fun Γ blks => Forall (wc_block G Γ) (fst blks)
                             /\ Forall (fun '(e, (_, _)) => wc_exp G Γ e /\ clockof e = [Cbase]) (snd blks))
                 G Γ (Scope locs blk) ->
        sem_scope_ck (fun Hi blks => Forall (sem_block_ck G Hi bs) (fst blks)) H bs (Scope locs blk) ->
        sem_scope_ck (fun Hi blks => Forall (sem_block_ck G Hi bs) (fst blks))
                     (restrict H Γ) bs (Scope locs blk).
    Proof.
      intros.
      eapply sem_scope_restrict; eauto.
      intros; destruct_conjs. simpl_Forall.
      eapply sem_block_ck_morph, sem_block_restrict; eauto; [symmetry; apply H6|reflexivity].
    Qed.

  End sem_restrict.

  (** ** Properties of the [global] environment *)

  Ltac sem_cons :=
    match goal with
    | H:sem_scope_ck _ _ _ _ |- sem_scope_ck _ _ _ _ =>
        inv H; destruct_conjs; econstructor; eauto
    | H:sem_branch_ck _ _ |- _ => inv H; destruct_conjs
    | |- sem_branch_ck _ _ => econstructor; eauto
    | _ => Sem.sem_cons
    end.

  Definition exp_ck_cons1 {PSyn prefs} typs exts (nd: @node PSyn prefs) (nds: list (@node PSyn prefs)) H bs e ss :=
    ~ Is_node_in_exp nd.(n_name) e -> sem_exp_ck (Global typs exts nds) H bs e ss.
  Definition equation_ck_cons1 {PSyn prefs} typs exts (nd: @node PSyn prefs) (nds: list (@node PSyn prefs)) H bs equ :=
    ~ Is_node_in_eq nd.(n_name) equ -> sem_equation_ck (Global typs exts nds) H bs equ.
  Definition transitions_ck_cons1 {PSyn prefs} typs exts (nd: @node PSyn prefs) (nds: list (@node PSyn prefs)) H bs trans default stres :=
    ~ List.Exists (fun '(e, _) => Is_node_in_exp nd.(n_name) e) trans -> sem_transitions_ck (Global typs exts nds) H bs trans default stres.
  Definition block_ck_cons1 {PSyn prefs} typs exts (nd: @node PSyn prefs) (nds: list (@node PSyn prefs)) H bs blk :=
    ~ Is_node_in_block nd.(n_name) blk -> sem_block_ck (Global typs exts nds) H bs blk.
  Definition node_ck_cons1 {PSyn prefs} typs exts (nd: @node PSyn prefs) (nds: list (@node PSyn prefs)) f xs ys :=
    nd.(n_name) <> f -> sem_node_ck (Global typs exts nds) f xs ys.
  Global Hint Unfold exp_ck_cons1 equation_ck_cons1 transitions_ck_cons1 block_ck_cons1 node_ck_cons1 : lsem.

  Lemma sem_exp_ck_cons1 {PSyn prefs} :
    forall typs exts (nd : @node PSyn prefs) nds Hi bs e ss,
      Ordered_nodes (Global typs exts (nd::nds)) ->
      sem_exp_ck (Global typs exts (nd::nds)) Hi bs e ss ->
      exp_ck_cons1 typs exts nd nds Hi bs e ss.
  Proof.
    intros * Hord Hsem.
    eapply sem_exp_ck_ind2
      with (P_exp := exp_ck_cons1 typs exts nd nds)
           (P_equation := equation_ck_cons1 typs exts nd nds)
           (P_transitions := transitions_ck_cons1 typs exts nd nds)
           (P_block := block_ck_cons1 typs exts nd nds)
           (P_node := node_ck_cons1 typs exts nd nds). 26:eauto.
    all:autounfold with lsem in *; econstructor; eauto; repeat sem_cons.
    - intros contra. eapply find_node_later_not_Is_node_in; eauto.
  Qed.

  Lemma sem_block_ck_cons1 {PSyn prefs} :
    forall typs exts (nd : @node PSyn prefs) nds Hi bs blk,
      Ordered_nodes (Global typs exts (nd::nds)) ->
      sem_block_ck (Global typs exts (nd::nds)) Hi bs blk ->
      block_ck_cons1 typs exts nd nds Hi bs blk.
  Proof.
    intros * Hord Hsem.
    eapply sem_block_ck_ind2
      with (P_exp := exp_ck_cons1 typs exts nd nds)
           (P_equation := equation_ck_cons1 typs exts nd nds)
           (P_transitions := transitions_ck_cons1 typs exts nd nds)
           (P_block := block_ck_cons1 typs exts nd nds)
           (P_node := node_ck_cons1 typs exts nd nds). 26:eauto.
    all:autounfold with lsem in *; econstructor; eauto; repeat sem_cons.
    - intros contra. eapply find_node_later_not_Is_node_in; eauto.
  Qed.

  Lemma sem_node_ck_cons1 {PSyn prefs} :
    forall typs exts (nd : @node PSyn prefs) nds f xs ys,
      Ordered_nodes (Global typs exts (nd::nds)) ->
      sem_node_ck (Global typs exts (nd::nds)) f xs ys ->
      node_ck_cons1 typs exts nd nds f xs ys.
  Proof.
    intros * Hord Hsem.
    eapply sem_node_ck_ind2
      with (P_exp := exp_ck_cons1 typs exts nd nds)
           (P_equation := equation_ck_cons1 typs exts nd nds)
           (P_transitions := transitions_ck_cons1 typs exts nd nds)
           (P_block := block_ck_cons1 typs exts nd nds)
           (P_node := node_ck_cons1 typs exts nd nds). 26:eauto.
    all:autounfold with lsem in *; econstructor; eauto; repeat sem_cons.
    - intros contra. eapply find_node_later_not_Is_node_in; eauto.
  Qed.

  Definition exp_ck_cons2 {PSyn prefs} typs exts (nd: @node PSyn prefs) (nds: list (@node PSyn prefs)) H bs e ss :=
    ~ Is_node_in_exp nd.(n_name) e -> sem_exp_ck (Global typs exts (nd::nds)) H bs e ss.
  Definition equation_ck_cons2 {PSyn prefs} typs exts (nd: @node PSyn prefs) (nds: list (@node PSyn prefs)) H bs equ :=
    ~ Is_node_in_eq nd.(n_name) equ -> sem_equation_ck (Global typs exts (nd::nds)) H bs equ.
  Definition transitions_ck_cons2 {PSyn prefs} typs exts (nd: @node PSyn prefs) (nds: list (@node PSyn prefs)) H bs trans default stres :=
    ~ List.Exists (fun '(e, _) => Is_node_in_exp nd.(n_name) e) trans -> sem_transitions_ck (Global typs exts (nd::nds)) H bs trans default stres.
  Definition block_ck_cons2 {PSyn prefs} typs exts (nd: @node PSyn prefs) (nds: list (@node PSyn prefs)) H bs blk :=
    ~ Is_node_in_block nd.(n_name) blk -> sem_block_ck (Global typs exts (nd::nds)) H bs blk.
  Definition node_ck_cons2 {PSyn prefs} typs exts (nd: @node PSyn prefs) (nds: list (@node PSyn prefs)) f xs ys :=
    nd.(n_name) <> f -> sem_node_ck (Global typs exts (nd::nds)) f xs ys.
  Global Hint Unfold exp_ck_cons2 equation_ck_cons2 transitions_ck_cons2 block_ck_cons2 node_ck_cons2 : lsem.

  Lemma sem_exp_ck_cons2 {PSyn prefs} :
    forall typs exts (nd : @node PSyn prefs) nds Hi bs e ss,
      Ordered_nodes (Global typs exts (nd::nds)) ->
      sem_exp_ck (Global typs exts nds) Hi bs e ss ->
      exp_ck_cons2 typs exts nd nds Hi bs e ss.
  Proof.
    intros * Hord Hsem.
    eapply sem_exp_ck_ind2
      with (P_exp := exp_ck_cons2 typs exts nd nds)
           (P_equation := equation_ck_cons2 typs exts nd nds)
           (P_transitions := transitions_ck_cons2 typs exts nd nds)
           (P_block := block_ck_cons2 typs exts nd nds)
           (P_node := node_ck_cons2 typs exts nd nds). 26:eauto.
    all:autounfold with lsem in *; econstructor; eauto; repeat sem_cons.
    - intros contra. eapply find_node_later_not_Is_node_in; eauto.
  Qed.

  Lemma sem_block_ck_cons2 {PSyn prefs} :
    forall typs exts (nd : @node PSyn prefs) nds Hi bs blk,
      Ordered_nodes (Global typs exts (nd::nds)) ->
      sem_block_ck (Global typs exts nds) Hi bs blk ->
      block_ck_cons2 typs exts nd nds Hi bs blk.
  Proof.
    intros * Hord Hsem.
    eapply sem_block_ck_ind2
      with (P_exp := exp_ck_cons2 typs exts nd nds)
           (P_equation := equation_ck_cons2 typs exts nd nds)
           (P_transitions := transitions_ck_cons2 typs exts nd nds)
           (P_block := block_ck_cons2 typs exts nd nds)
           (P_node := node_ck_cons2 typs exts nd nds). 26:eauto.
    all:autounfold with lsem in *; econstructor; eauto; repeat sem_cons.
    - intros contra. eapply find_node_later_not_Is_node_in; eauto.
  Qed.

  Lemma sem_node_ck_cons2 {PSyn prefs} :
    forall typs exts (nd : @node PSyn prefs) nds f xs ys,
      Ordered_nodes (Global typs exts (nd::nds)) ->
      sem_node_ck (Global typs exts nds) f xs ys ->
      node_ck_cons2 typs exts nd nds f xs ys.
  Proof.
    intros * Hord Hsem.
    eapply sem_node_ck_ind2
      with (P_exp := exp_ck_cons2 typs exts nd nds)
           (P_equation := equation_ck_cons2 typs exts nd nds)
           (P_transitions := transitions_ck_cons2 typs exts nd nds)
           (P_block := block_ck_cons2 typs exts nd nds)
           (P_node := node_ck_cons2 typs exts nd nds). 26:eauto.
    all:autounfold with lsem in *; econstructor; eauto; repeat sem_cons.
    - intros contra. eapply find_node_later_not_Is_node_in; eauto.
  Qed.

  Lemma sem_node_ck_cons_iff {PSyn prefs} :
    forall (n : @node PSyn prefs) nds types externs f xs ys,
      Ordered_nodes (Global types externs (n::nds)) ->
      n_name n <> f ->
      sem_node_ck (Global types externs nds) f xs ys <->
      sem_node_ck (Global types externs (n::nds)) f xs ys.
  Proof.
    intros * Hord Hname.
    split; intros Hsem.
    - eapply sem_node_ck_cons2; eauto.
    - eapply sem_node_ck_cons1; eauto.
  Qed.

  (** Build the alignment proof *)

  Lemma sc_when :
    forall H b x ty k ck xs ys rs,
      sem_var H x xs ->
      sem_clock H b ck (abstract_clock ys) ->
      when k ys xs rs ->
      sem_clock H b (Con ck x (ty, k)) (abstract_clock rs).
  Proof.
    intros * Hv Hsemck Hwhen.
    econstructor; eauto.
    - apply ac_when in Hwhen. now rewrite Hwhen.
    - apply enums_of_nth; intros n.
      eapply when_spec in Hwhen as [(Hy&Hx&Hr)|[(?&?&Hy&Hx&?&Hr)|(?&Hy&Hx&Hr)]].
      + left. intuition; eauto.
        setoid_rewrite ac_nth. setoid_rewrite Hr; auto.
      + right; right. eexists. intuition; eauto.
        setoid_rewrite ac_nth. setoid_rewrite Hr; auto.
      + right; left. intuition; auto.
        setoid_rewrite ac_nth. setoid_rewrite Hr; auto.
  Qed.

  Lemma sc_merge :
    forall H b ck x tx xs vs ss,
      vs <> [] ->
      sem_var H x xs ->
      Forall (fun vs => sem_clock H b (Con ck x (tx, (fst vs))) (abstract_clock (snd vs))) vs ->
      merge xs vs ss ->
      sem_clock H b ck (abstract_clock ss).
  Proof.
    intros * Hlen Hsemv Hsv Hmerge.
    inv Hsv; try congruence. inv H0; auto.
    apply ac_merge in Hmerge. rewrite <-Hmerge.
    rewrite <-H12 in H9.
    eapply sem_var_det in Hsemv; eauto. rewrite <-Hsemv; auto.
  Qed.

  Global Hint Constructors Is_free_in_clock : clocks lcsem.

  Lemma sc_parent :
    forall H b ck lck ss,
      Forall2 (sem_clock H b) lck (map abstract_clock ss) ->
      In ck lck ->
      Forall (fun ck' => ck' = ck \/ clock_parent ck ck') lck ->
      sem_clock H b ck (clocks_of ss).
  Proof.
    intros * Hsc Hin Hparent.
    pose proof (Forall2_in_left _ _ _ _ Hsc Hin) as [s (Hins & Hsc0)].
    rewrite Forall2_map_2 in Hsc. simpl_In.
    assert (
        Forall (fun s' => sub_clock (abstract_clock x) (abstract_clock s')) ss
      ) as Hf. {
      apply Forall_forall; intros * Hx0.
      pose proof (Forall2_in_right _ _ _ _ Hsc Hx0) as [? (Hx1&Hsc1)].
      eapply Forall_forall in Hx1; eauto. destruct Hx1.
      subst.
      apply sem_clock_det with (2 := Hsc1) in Hsc0. now rewrite Hsc0.
      eapply sub_clock_parent; eauto.
    }
    apply sub_clock_sclocksof in Hf; auto. now rewrite Hf.
  Qed.

  Lemma wc_env_free_in_clock :
    forall x i ck vars,
      wc_env vars ->
      In (x, ck) vars ->
      Is_free_in_clock i ck ->
      exists ick, In (i, ick) vars.
  Proof.
    intros * WC Ix Hfree.
    revert x Ix. induction ck; inv Hfree;
    intros; eapply Forall_forall in WC; eauto; inv WC; eauto.
  Qed.

  Fact sc_has_base {PSyn prefs} : forall H b bck sub (n : @node PSyn prefs) ncks ss,
      wc_env (map (fun '(x, (_, ck, _)) => (x, ck)) (n_in n)) ->
      Forall2 (fun nck => sem_clock H b (stripname nck)) ncks (map abstract_clock ss) ->
      Forall2 (WellInstantiated bck sub) (map (fun '(x, (_, ck, _)) => (x, ck)) (n_in n)) ncks ->
      sem_clock H b bck (clocks_of ss).
  Proof.
    intros * WCin Hscin WIi.
    pose proof (wc_env_has_Cbase _ WCin) as [i Hin].
    { rewrite map_length. exact (n_ingt0 n). }
    apply WellInstantiated_parent in WIi as Hp.
    change (Forall (fun ck => (fun x => x = bck \/ clock_parent bck x) (fst ck))
                   ncks) in Hp.
    rewrite <- Forall_map in Hp.
    eapply sc_parent; eauto.
    now rewrite Forall2_map_1.
    pose proof (Forall2_in_left _ _ _ _ WIi Hin) as [?(?&?& H14)].
    simpl in H14. inv H14. now apply in_map.
  Qed.

  Lemma sc_inst_mask:
    forall H' b b' ck ck' bck sub cks rs,
      instck bck sub ck = Some ck' ->
      sem_clock H' b' bck b ->
      (forall k, exists H, sem_clock H (maskb k rs b) ck (maskb k rs cks) /\
                 (forall x x',
                     Is_free_in_clock x ck ->
                     sub x = Some x' ->
                     orel (fun v1 v2 => EqSt v1 (maskv k rs v2)) (H x) (H' x'))) ->
      sem_clock H' b' ck' cks.
  Proof with eauto with lcsem.
    intros * Hinst Hbck Hk.
    rewrite sem_clock_equiv in *. unfold tr_Stream in *.
    intros n. specialize (Hbck n); simpl in Hbck.
    specialize (Hk ((count rs) # n)) as [H [Hck Henv]].
    rewrite sem_clock_equiv in Hck. unfold tr_Stream in Hck.
    specialize (Hck n); simpl in Hck.
    repeat rewrite maskb_nth in Hck.
    repeat rewrite Nat.eqb_refl in Hck.
    assert (forall x x', Is_free_in_clock x ck -> sub x = Some x' -> orel (@eq svalue) ((CIStr.tr_history H n) x) ((CIStr.tr_history H' n) x')) as Henv'.
    { intros * Hfree Hsub. specialize (Henv x x' Hfree Hsub).
      eapply tr_history_find_orel_unmask with (n:=n) in Henv.
      assert (relation_equivalence eq (fun v1 v2 => v1 = (if (count rs) # n =? (count rs) # n then v2 else @absent value))) as Heq.
      { intros x1 x2.
        rewrite Nat.eqb_refl.
        constructor; auto. }
      rewrite Heq; auto.
    } clear Henv.
    revert H H' b b' ck' bck cks sub Hinst Hck Hbck Henv'.
    induction ck; intros.
    - inv Hinst. inv Hck; auto.
    - inversion Hinst as [Hcase]. cases_eqn Hcase. inv Hcase.
      inv Hck.
      1,2:econstructor;eauto. 5:eapply IStr.Son_abs2; eauto.
      2,4,6:(unfold IStr.sem_var_instant in *;
             specialize (Henv' i i0 (FreeCon1 _ _ _) Hcase1); rewrite H5 in Henv';
             inv Henv'; auto).
      * rewrite H4 in *; eapply IHck in Hcase0...
      * rewrite H4 in *; eapply IHck in Hcase0...
      * eapply IHck with (cks:=Streams.const true) in Hcase0...
        rewrite const_nth in Hcase0; auto. rewrite const_nth; eauto.
  Qed.

  Lemma sc_inst_unmask:
    forall H H' b b' ck ck' bck sub cks k rs,
      instck bck sub ck = Some ck' ->
      sem_clock H' b' ck' cks ->
      sem_clock H' b' bck b ->
      (forall x x',
          Is_free_in_clock x ck ->
          sub x = Some x' ->
          orel (fun v1 v2 => EqSt v1 (maskv k rs v2)) (H x) (H' x')) ->
      sem_clock H (maskb k rs b) ck (maskb k rs cks).
  Proof with eauto with lcsem.
    intros * Hinst Hck Hbck Henv.
    rewrite sem_clock_equiv in *.
    intros n. specialize (Hck n). specialize (Hbck n).
    assert (forall x x' n, Is_free_in_clock x ck -> sub x = Some x' -> orel (fun v1 v2 => v1 = (if (CStr.count rs) # n =? k then v2 else absent)) ((CIStr.tr_history H n) x) ((CIStr.tr_history H' n) x')) as Henv'.
    { intros * Hfree Hsub. specialize (Henv x x' Hfree Hsub).
      eapply tr_history_find_orel_unmask in Henv; eauto. } clear Henv.
    unfold tr_Stream in *.
    revert H H' b b' ck' bck cks sub Hinst Hck Hbck Henv'.
    induction ck; intros; simpl in *.
    - inv Hinst.
      repeat rewrite maskb_nth in *. destruct (_ =? k); auto with indexedstreams.
      eapply IStr.sem_clock_instant_det in Hck; eauto.
      rewrite Hck; auto with indexedstreams.
    - inversion Hinst as [Hcase]. cases_eqn Hcase. inv Hcase.
      repeat rewrite maskb_nth in *; destruct (_ =? k) eqn:Hcount.
      + inv Hck.
        1,2:econstructor;eauto. 5:eapply IStr.Son_abs2; eauto.
        2,4,6:(unfold IStr.sem_var_instant in *;
               specialize (Henv' i i0 n (FreeCon1 _ _ _) Hcase1); rewrite H5 in Henv';
               inv Henv'; auto; rewrite Hcount; auto).
        * rewrite H4 in *; eapply IHck with (b':=b') in Hcase0; eauto...
          repeat rewrite maskb_nth, Hcount, <- H4 in Hcase0. rewrite <- H4; auto.
        * rewrite H4 in *; eapply IHck with (b':=b') in Hcase0...
          repeat rewrite maskb_nth, Hcount in Hcase0; eauto.
        * assert (Htrue:=H4). apply IStr.sem_clock_instant_true_inv in H4; eauto.
          eapply IHck with (b:=b) (b':=b') (cks:=Streams.const true) in Hcase0...
          repeat rewrite maskb_nth, Hcount in Hcase0. rewrite const_nth in Hcase0; eauto.
          rewrite const_nth; eauto.
      + inv Hck.
        1,2,3:econstructor; eauto.
        2,4,6:(unfold IStr.sem_var_instant in *;
               specialize (Henv' _ _ n (FreeCon1 _ _ _) Hcase1); rewrite H5 in Henv';
               inv Henv'; auto; rewrite Hcount; auto).
        1,3:eapply IHck with (b':=b') (b:=b) (cks:=Streams.const true) in Hcase0...
        1-5:repeat rewrite maskb_nth, Hcount in *; repeat rewrite const_nth in *; auto.
        eapply IHck in Hcase0... 2:rewrite <-H4; eauto.
        repeat rewrite maskb_nth, Hcount in Hcase0; eauto.
  Qed.

  Lemma inst_in_eqst_mask:
    forall H Hi xs ys vs i ck bck sub k rs,
      In (i, ck) xs ->
      Forall2 (WellInstantiated bck sub) xs ys ->
      Forall2 (sem_var Hi) (map fst xs) (map (maskv k rs) vs) ->
      Forall2 (fun '(_, o) s => LiftO True (fun x => sem_var H x s) o) ys vs ->
      forall i',
        sub i = Some i' ->
        orel (fun v1 v2 => v1 ≡ maskv k rs v2) (Hi i) (H i').
  Proof.
    intros * Hin WI Hsvi Hsvo i Sub.
    rewrite Forall2_map_1, Forall2_map_2 in Hsvi.
    rewrite Forall2_swap_args in Hsvo.
    eapply Forall2_trans_ex with (1:=Hsvi) in Hsvo. clear Hsvi.
    eapply Forall2_Forall2 in WI; eauto. clear Hsvo.
    eapply Forall2_forall2 in WI as [? WI].
    eapply In_nth in Hin as [n' [Hlen Hin]].
    destruct (nth n' ys (Cbase, None)) eqn:Hy.
    specialize (WI (xH, Cbase) (Cbase, None) _ _ _ Hlen Hin Hy) as ((?&?&?&?)&Hinst).
    simpl in H2; inv H2. rewrite H5.
    inv Hinst; simpl in *. rewrite Sub in H2; inv H2.
    simpl in H3; inv H3. rewrite H7.
    constructor. symmetry. rewrite <- H8; eauto.
  Qed.

  (* When function call parameters are well instantiated and have
     the [sem_clock] property, we obtain the same property inside
     the node (Hi = "H inside").
   *)
  Corollary sc_inside_mask {PSyn prefs} :
    forall H Hi b es ss0 bck sub (n : @node PSyn prefs) k rs,
      Forall2 (fun '(_, o) (s : Stream svalue) => LiftO True (fun x1 : ident => sem_var H (Var x1) s) o) (nclocksof es) (concat ss0) ->
      wc_env (map (fun '(x, (_, ck, _)) => (x, ck)) (n_in n)) ->
      Forall2 (sem_clock (var_history H) b) (clocksof es) (map abstract_clock (concat ss0)) ->
      Forall2 (WellInstantiated bck sub) (map (fun '(x, (_, ck, _)) => (x, ck)) (n_in n)) (nclocksof es) ->
      Forall2 (fun x => sem_var Hi (Var x)) (idents (n_in n)) (map (maskv k rs) (concat ss0)) ->
      Forall2 (fun xc => sem_clock (var_history Hi) (clocks_of (map (maskv k rs) (concat ss0))) (snd xc))
              (map (fun '(x, (_, ck, _)) => (x, ck)) (n_in n)) (map abstract_clock (map (maskv k rs) (concat ss0))).
  Proof.
    intros * Hse WCin Hscin WIi Hsv.

    rewrite Forall2_map_2 in Hscin. rewrite Forall2_map_2 in Hsv. repeat rewrite Forall2_map_2.
    rewrite clocksof_nclocksof, Forall2_map_1 in Hscin.
    apply Forall2_trans_ex with (1 := WIi) in Hscin as H1.
    eapply Forall2_impl_In; eauto.
    intros (x & ck) xs  Hxin ? ((yck & ny) & Hyin & (Hsub & Hinst) & Hsc).
    simpl in *.
    rewrite ac_mask, clocks_of_mask.
    eapply sc_inst_unmask; eauto.
    - eapply sc_has_base; eauto. simpl_Forall. auto.
    - clear - Hxin WCin WIi Hse Hsv.
      intros i i' Free Sub.
      pose proof (wc_env_free_in_clock _ _ _ _ WCin Hxin Free) as [].
      eapply inst_in_eqst_mask; eauto.
      unfold idents in Hsv. simpl_Forall.
      1,2:eapply Forall2_impl_In; eauto; intros; destruct_conjs.
      2:destruct o; simpl; auto. 1,2:apply sem_var_history; auto.
  Qed.

  Definition def_stream b := enum b 0.

  Lemma sc_outside_mask {PSyn1 PSyn2 prefs1 prefs2} :
    forall (G : @global PSyn1 prefs1) H es b Γ ncks ss0 ss bck sub (n : @node PSyn2 prefs2) rs,
      Forall (wc_exp G Γ) es ->
      Forall2 (fun '(_, o1) s => LiftO True (fun x0 : ident => sem_var H (Var x0) s) o1) (nclocksof es) (concat ss0) ->
      Forall2 (fun '(_, o) s => LiftO True (fun x0 => sem_var H (Var x0) s) o) ncks ss ->
      wc_env (map (fun '(x, (_, ck, _)) => (x, ck)) (n_in n)) ->
      wc_env (map (fun '(x, (_, ck, _)) => (x, ck)) (n_in n) ++ map (fun '(x, (_, ck, _, _)) => (x, ck)) (n_out n)) ->
      Forall2 (sem_clock (var_history H) b) (clocksof es) (map abstract_clock (concat ss0)) ->
      Forall2 (WellInstantiated bck sub) (map (fun '(x, (_, ck, _)) => (x, ck)) (n_in n)) (nclocksof es) ->
      Forall2 (WellInstantiated bck sub) (map (fun '(x, (_, ck, _, _)) => (x, ck)) (n_out n)) ncks ->
      (forall k, exists Hi,
            Forall2 (fun xc => sem_clock (var_history Hi) (clocks_of (map (maskv k rs) (concat ss0))) (snd xc))
                    (map (fun '(x, (_, ck, _, _)) => (x, ck)) (n_out n)) (map abstract_clock (map (maskv k rs) ss)) /\
            Forall2 (fun x => sem_var Hi (Var x)) (map fst (n_in n)) (map (maskv k rs) (concat ss0)) /\
            Forall2 (fun x => sem_var Hi (Var x)) (map fst (n_out n)) (map (maskv k rs) ss)) ->
      Forall2 (sem_clock (var_history H) b) (map fst ncks) (map abstract_clock ss).
  Proof.
    intros * Hwc Hsvar Hse2 WCin WCinout Hscin WIi WIo Hk.

    rewrite clocksof_nclocksof, Forall2_map_1, Forall2_map_2 in Hscin.
    rewrite Forall2_map_1, Forall2_map_2.
    assert (length ncks = length (n_out n)) as Hlen1.
    { apply Forall2_length in WIo. now rewrite map_length in WIo. }
    assert (length ncks = length ss) as Hlen2.
    { specialize (Hk 0) as (?&_&_&Hf).
      unfold idents in Hf. simpl_Forall. apply Forall2_length in Hf.
      now rewrite Hlen1. }
    eapply Forall2_forall2; split; eauto.
    intros [? ?] ? ? [? ?] ? Hlen Hnth1 Hnth2; simpl; subst.
    eapply sc_inst_mask; eauto.
    - eapply Forall2_forall2 in WIo as [? WIo]. setoid_rewrite map_length in WIo.
      rewrite Hlen1 in Hlen.
      specialize (WIo (xH, Cbase) _ _ _ _ Hlen eq_refl Hnth1).
      inv WIo; eauto.
    - eapply sc_has_base; eauto. rewrite Forall2_map_2; eauto.
    - intros k.
      specialize (Hk k) as (Hi&?&?&?).
      exists (var_history Hi). split.
      + eapply Forall2_forall2 in H0 as [? Hck].
        rewrite Hlen1 in Hlen. setoid_rewrite map_length in Hck.
        specialize (Hck (xH, Cbase) (abstract_clock (def_stream b)) _ _ _ Hlen eq_refl eq_refl).
        erewrite clocks_of_mask in Hck.
        setoid_rewrite map_nth' with (l:=map _ _) (d':=Streams.const absent) in Hck. erewrite map_nth' with (l:=ss), ac_mask in Hck; eauto.
        2:rewrite map_length. 1,2:congruence.
      + intros i i' Free Sub.
        destruct (nth n0 (map (fun '(x, (_, ck, _, _)) => (x, ck)) (n_out n)) (1%positive, Cbase)) as (yck, ny) eqn:Hy.
        assert (In (yck, ny) (map (fun '(x, (_, ck, _)) => (x, ck)) (n_in n) ++ map (fun '(x, (_, ck, _, _)) => (x, ck)) (n_out n))) as Hyin2.
        { apply in_or_app. right.
          rewrite <- Hy. apply nth_In. rewrite map_length. now setoid_rewrite <-Hlen1. }
        pose proof (wc_env_free_in_clock _ _ _ _ WCinout Hyin2 Free) as [].
        eapply inst_in_eqst_mask with (vs:=(concat ss0++ss)). 1,5:eauto.
        * eapply Forall2_app; eauto.
        * unfold idents in *. simpl_Forall. apply Forall2_app; simpl_Forall; eauto.
          1,2:eapply sem_var_history; eauto.
        * eapply Forall2_app; simpl_Forall.
          1,2:destruct a as (?&[]); simpl in *; auto; apply sem_var_history; auto.
  Qed.

  Lemma sem_clock_refines'' : forall H H' ck bs bs',
      (forall x vs, Is_free_in_clock x ck -> sem_var H x vs -> sem_var H' x vs) ->
      sem_clock H bs ck bs' ->
      sem_clock H' bs ck bs'.
  Proof with eauto with lcsem.
    induction ck; intros * Href Hsem; inv Hsem.
    - constructor; auto.
    - econstructor; eauto.
      + eapply IHck; eauto.
        intros. apply Href; auto. constructor; auto.
      + apply Href; auto. constructor; auto.
  Qed.

  Lemma sc_vars_subclock Γ Γ' : forall Hi bs bs' ck,
      sem_clock (var_history Hi) bs ck bs' ->
      (forall x ck', HasClock Γ' x ck' -> HasClock Γ x ck /\ ck' = Cbase) ->
      (forall x, IsLast Γ' x -> IsLast Γ x) ->
      sc_vars Γ Hi bs ->
      sc_vars Γ' Hi bs'.
  Proof.
    intros * Hsemck Hck Hla (Hinv1&Hinv2).
    split.
    - intros * Hasck Hv. edestruct Hck as (Hasck'&?); eauto; subst.
      eapply Hinv1 in Hv; eauto.
      eapply sem_clock_det in Hsemck; eauto. constructor; symmetry; auto.
    - intros * Hasck Hasl Hv. edestruct Hck as (Hasck'&?); eauto; subst.
      eapply Hinv2 in Hv; eauto.
      eapply sem_clock_det in Hsemck; eauto. constructor; symmetry; auto.
  Qed.

  (** ** more `mask` properties *)

  Lemma history_mask_count : forall r H n,
      FEnv.Equiv eq (CIStr.tr_history (mask_hist (count r) # n r H) n) (CIStr.tr_history H n).
  Proof.
    intros * ?. simpl_fenv.
    destruct (H x); simpl; constructor.
    unfold tr_Stream; rewrite maskv_nth, Nat.eqb_refl; auto with datatypes.
  Qed.

  Corollary sem_var_instant_mask_hist_count: forall H n r x v,
      IStr.sem_var_instant (CIStr.tr_history H n) x v <->
        IStr.sem_var_instant (CIStr.tr_history (mask_hist ((count r) # n) r H) n) x v.
  Proof.
    intros.
    split; intros; eapply IStr.sem_var_instant_morph; eauto.
    symmetry. 1,2:eapply history_mask_count.
  Qed.

  Lemma sem_clock_mask : forall H bs ck bs' k r,
      sem_clock H bs ck bs' ->
      sem_clock (mask_hist k r H) (maskb k r bs) ck (maskb k r bs').
  Proof.
    induction ck; intros * Hck; inv Hck.
    - constructor. now rewrite H1.
    - econstructor; eauto using sem_var_mask.
      + now rewrite ac_mask, H9.
      + apply enums_of_nth; intros. repeat rewrite maskv_nth; repeat rewrite maskb_nth.
        destruct (_ =? _); auto.
        apply enums_of_nth with (n:=n) in H10; auto.
  Qed.

  Lemma sem_clock_unmask : forall H bs ck bs' r,
      (forall k, sem_clock (mask_hist k r H) (maskb k r bs) ck (maskb k r bs')) ->
      sem_clock H bs ck bs'.
  Proof.
    setoid_rewrite sem_clock_equiv.
    intros * Hck ?.
    specialize (Hck ((count r) # n) n); simpl in Hck.
    unfold tr_Stream in *.
    repeat rewrite maskb_nth, Nat.eqb_refl in Hck.
    revert bs' Hck.
    induction ck; intros; inv Hck.
    - constructor.
    - eapply sem_var_instant_mask_hist_count in H5.
      econstructor; eauto. rewrite H4; eapply IHck; congruence.
    - eapply sem_var_instant_mask_hist_count in H5.
      econstructor; eauto. rewrite H4; eapply IHck; congruence.
    - eapply sem_var_instant_mask_hist_count in H5.
      eapply IStr.Son_abs2; eauto.
      specialize (IHck (Streams.const true)).
      repeat rewrite const_nth in IHck. auto.
  Qed.

  Lemma sc_vars_mask : forall Γ H b r k,
      sc_vars Γ H b ->
      sc_vars Γ (mask_hist k r H) (maskb k r b).
  Proof.
    intros * (Hinv1&Hinv2).
    split; [intros * Hck Hv|intros * Hck Hl Hv];
      apply sem_var_mask_inv in Hv as (?&Hv&Heq); rewrite Heq, ac_mask; simpl;
      eapply sem_clock_mask; eauto.
  Qed.

  Lemma sc_vars_unmask : forall Γ H b r,
      (forall k, sc_vars Γ (mask_hist k r H) (maskb k r b)) ->
      sc_vars Γ H b.
  Proof.
    intros * Hinv.
    split; [intros * Hck Hv|intros * Hck Hl Hv];
      eapply sem_clock_unmask; intros k;
      destruct (Hinv k) as (Hinv1&Hinv2); rewrite <-ac_mask;
      [eapply Hinv1|eapply Hinv2]; simpl; eauto using sem_var_mask.
  Qed.

  Lemma sem_clock_filter : forall Hi Hi' bs ck k sc,
      sem_clock Hi bs ck (abstract_clock sc) ->
      sem_clock Hi' (fwhenb k bs sc) Cbase (fwhenb k (abstract_clock sc) sc).
  Proof.
    intros * Hsemck.
    constructor.
    eapply ntheq_eqst. intros. rewrite 2 fwhenb_nth, ac_nth.
    destruct (_ ==b _) eqn:Heqsc; auto.
    apply svalue_eqb_eq in Heqsc. setoid_rewrite Heqsc.
    eapply sem_clock_equiv in Hsemck. specialize (Hsemck n). repeat rewrite tr_Stream_nth in Hsemck.
    setoid_rewrite ac_nth in Hsemck. setoid_rewrite Heqsc in Hsemck. apply IStr.sem_clock_instant_true_inv in Hsemck; auto.
  Qed.

  Lemma sc_vars_when : forall Γ Γ' Hi Hi'  bs ck e sc,
      sc_vars Γ Hi bs ->
      sem_clock (var_history Hi) bs ck (abstract_clock sc) ->
      (forall x ck', HasClock Γ' x ck' -> HasClock Γ x ck /\ ck' = Cbase) ->
      (forall x, IsLast Γ' x -> IsLast Γ x) ->
      when_hist e Hi sc Hi' ->
      sc_vars Γ' Hi' (fwhenb e bs sc).
  Proof.
    intros * (Hsc1&Hsc2) Hsemck Hclocks Hlasts When.
    split.
    - intros * Hck Hv.
      edestruct Hclocks as (?&?); eauto; subst.
      eapply sem_var_when_inv in Hv as (?&Hv&Hwhen); eauto.
      apply when_fwhen in Hwhen. rewrite Hwhen, ac_fwhen.
      constructor. apply fwhenb_both_slower.
      + eapply sc_slower; eauto using ac_aligned.
      + eapply Hsc1 in Hv; eauto.
        eapply sem_clock_det in Hsemck; eauto. rewrite Hsemck; eauto using ac_slower.
    - intros * Hck Hla Hv.
      edestruct Hclocks as (?&?); eauto; subst.
      eapply sem_var_when_inv in Hv as (?&Hv&Hwhen); eauto.
      apply when_fwhen in Hwhen. rewrite Hwhen, ac_fwhen.
      constructor. apply fwhenb_both_slower.
      + eapply sc_slower; eauto using ac_aligned.
      + eapply Hsc2 in Hv; eauto.
        eapply sem_clock_det in Hsemck; eauto. rewrite Hsemck; eauto using ac_slower.
  Qed.

  Lemma sem_clock_select : forall Hi Hi' bs ck e k sc,
      sem_clock Hi bs ck (abstract_clock sc) ->
      sem_clock Hi' (fselectb e k sc bs) Cbase (fselectb e k sc (abstract_clock sc)).
  Proof.
    intros * Hsemck.
    constructor.
    eapply ntheq_eqst. intros. setoid_rewrite maskb_nth. rewrite 2 fwhenb_nth, ac_nth.
    destruct (_ ==b _) eqn:Heqsc, (_ =? _); auto.
    apply svalue_eqb_eq in Heqsc. setoid_rewrite Str_nth_map in Heqsc.
    destruct (sc # n) as [|(?&?)] eqn:Hscn; simpl in *; try congruence.
    eapply sem_clock_equiv in Hsemck. specialize (Hsemck n). repeat rewrite tr_Stream_nth in Hsemck.
    setoid_rewrite ac_nth in Hsemck. setoid_rewrite Hscn in Hsemck.
    apply IStr.sem_clock_instant_true_inv in Hsemck; auto.
  Qed.

  Lemma sc_vars_select : forall Γ Γ' Hi Hi' bs ck e k sc,
      sc_vars Γ Hi bs ->
      sem_clock (var_history Hi) bs ck (abstract_clock sc) ->
      (forall x ck', HasClock Γ' x ck' -> HasClock Γ x ck /\ ck' = Cbase) ->
      (forall x, IsLast Γ' x -> IsLast Γ x) ->
      select_hist e k sc Hi Hi' ->
      sc_vars Γ' Hi' (fselectb e k sc bs).
  Proof.
    intros * (Hsc1&Hsc2) Hsemck Hclocks Hlasts When.
    split.
    - intros * Hck Hv.
      edestruct Hclocks as (?&?); eauto; subst.
      eapply sem_var_select_inv in Hv as (?&Hv&Hselect); eauto.
      apply select_fselect in Hselect. rewrite Hselect, ac_fselect.
      constructor. apply fselectb_both_slower.
      + take (sem_clock _ _ _ _) and eapply sc_slower in it. 2:rewrite <-stres_st_ac; eauto using ac_aligned.
        eapply slower_ac_morph; [|eauto]. apply stres_st_ac.
      + eapply Hsc1 in Hv; eauto.
        eapply sem_clock_det in Hsemck; eauto. rewrite Hsemck; eauto using ac_slower.
    - intros * Hck Hla Hv.
      edestruct Hclocks as (?&?); eauto; subst.
      eapply sem_var_select_inv in Hv as (?&Hv&Hselect); eauto.
      apply select_fselect in Hselect. rewrite Hselect, ac_fselect.
      constructor. apply fselectb_both_slower.
      + take (sem_clock _ _ _ _) and eapply sc_slower in it. 2:rewrite <-stres_st_ac; eauto using ac_aligned.
        eapply slower_ac_morph; [|eauto]. apply stres_st_ac.
      + eapply Hsc2 in Hv; eauto.
        eapply sem_clock_det in Hsemck; eauto. rewrite Hsemck; eauto using ac_slower.
  Qed.

  Lemma sc_vars_slower_hist : forall Γ H b,
      sc_vars Γ H b ->
      dom_ub H Γ ->
      slower_hist H b.
  Proof.
    intros * Hsc Hdom ?? Hfind.
    assert (FEnv.In x H) as Henvin by (econstructor; eauto).
    assert (sem_var H x vs) as Hv by (econstructor; eauto; reflexivity).
    destruct x; eapply Hdom in Henvin; inv Henvin; simpl_In.
    1,2:eapply Hsc in Hv; eauto with senv.
    1,2:eapply sc_slower; eauto; eapply ac_aligned.
  Qed.

  (** ** Alignment of streams produced by expressions *)
  Section props.
    Context {PSyn : list decl -> block -> Prop}.
    Context {prefs : PS.t}.
    Variable (G : @global PSyn prefs).

    (** The number of streams generated by an expression [e] equals [numstreams e] *)

    Fact sem_exp_ck_numstreams : forall H b e v,
        wl_exp G e ->
        sem_exp_ck G H b e v ->
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

    Corollary sem_exps_ck_numstreams : forall H b es vs,
        Forall (wl_exp G) es ->
        Forall2 (sem_exp_ck G H b) es vs ->
        length (concat vs) = length (annots es).
    Proof.
      intros * Hwt Hsem.
      assert (Forall2 (fun v e => length v = numstreams e) vs es) as Hf.
      { rewrite Forall2_swap_args. simpl_Forall.
        eapply sem_exp_ck_numstreams; eauto. }
      clear Hwt Hsem.
      induction Hf; simpl.
      - reflexivity.
      - repeat rewrite app_length.
        f_equal; auto.
        rewrite length_annot_numstreams. assumption.
    Qed.

    Lemma sem_exp_sem_var : forall H b e vs,
        wl_exp G e ->
        sem_exp_ck G H b e vs ->
        Forall2 (fun '(_, o) s => LiftO True (fun x : ident => sem_var H (Var x) s) o) (nclockof e) vs.
    Proof.
      intros * Hwl Hsem.
      assert (length vs = length (annot e)) as Hlen.
      { rewrite length_annot_numstreams. eapply sem_exp_ck_numstreams; eauto. }
      inv Hwl; inv Hsem; simpl in *; repeat constructor; repeat rewrite map_length in *.
      all:simpl_Forall; simpl; auto.
      all:apply Forall2_forall; split; auto.
    Qed.

    Corollary sem_exps_sem_var : forall H b es vs,
        Forall (wl_exp G) es ->
        Forall2 (sem_exp_ck G H b) es vs ->
        Forall2 (fun '(_, o) s => LiftO True (fun x : ident => sem_var H (Var x) s) o) (nclocksof es) (concat vs).
    Proof.
      induction es; intros * Hwc Hsem; inv Hwc; inv Hsem; simpl; auto.
      apply Forall2_app; auto.
      eapply sem_exp_sem_var; eauto.
    Qed.

  End props.

  Lemma sc_outside_mask' {PSyn prefs} :
    forall (G: @global PSyn prefs) f n H b Γ ncks es rs ss vs bck sub,
      wc_global G ->
      find_node f G = Some n ->
      Forall (wc_exp G Γ) es ->
      Forall2 (sem_exp_ck G H b) es ss ->
      (forall k, sem_node_ck G f (map (maskv k rs) (concat ss)) (map (maskv k rs) vs)) ->
      Forall2 (fun '(_, o) (s : Stream svalue) => LiftO True (fun x0 : ident => sem_var H (Var x0) s) o) ncks vs ->
      Forall2 (sem_clock (var_history H) b) (clocksof es) (map abstract_clock (concat ss)) ->
      Forall2 (WellInstantiated bck sub) (map (fun '(x, (_, ck, _)) => (x, ck)) (n_in n)) (nclocksof es) ->
      Forall2 (WellInstantiated bck sub) (map (fun '(x, (_, ck, _, _)) => (x, ck)) (n_out n)) ncks ->
      Forall2 (sem_clock (var_history H) b) (map fst ncks) (map abstract_clock vs).
  Proof.
    intros * HwcG Hfind Hwc Hseme Hsem Hvars Hcki Hwi Hwo.
    eapply sc_outside_mask with (rs:=rs) (es:=es); eauto.
    2,3:eapply wc_find_node in HwcG as (?&HwcN); eauto; inv HwcN; eauto.
    - eapply sem_exps_sem_var in Hseme; eauto with lclocking.
    - intros k.
      specialize (Hsem k). inv Hsem. rewrite Hfind in H1; inv H1.
      exists H0. repeat split; eauto.
      take (clocked_node _ _ _) and destruct it as (?&Hinv). clear - H3 Hinv. destruct Hinv as (Hinv&_).
      unfold idents, idck, idty in *. simpl_Forall.
      eapply Hinv in H2; eauto.
      econstructor; simpl_app; try (rewrite in_app_iff; right; solve_In). auto.
  Qed.

  Fact sc_exps' {PSyn prefs} : forall (G : @global PSyn prefs) H b Γ es ss,
      Forall
         (fun e => forall vs,
              wc_exp G Γ e ->
              sem_exp_ck G H b e vs ->
              Forall2 (sem_clock (var_history H) b) (clockof e) (map abstract_clock vs)) es ->

      Forall (wc_exp G Γ) es ->
      Forall2 (sem_exp_ck G H b) es ss ->
      Forall2 (sem_clock (var_history H) b) (clocksof es) (map abstract_clock (concat ss)).
  Proof.
    intros * Hf Hwc Hsem.
    assert (length es = length ss) as Hlength by (eapply Forall2_length in Hsem; eauto).
    eapply Forall2_ignore2' in Hwc; eauto.
    eapply Forall2_Forall2 in Hsem; eauto. clear Hwc.
    unfold clocksof. rewrite flat_map_concat_map, Forall2_map_2.
    apply Forall2_concat. simpl_Forall.
    setoid_rewrite Forall2_map_2 in Hf; eauto.
  Qed.

  Lemma Forall2Brs_sc_exp1 {PSyn prefs} (G: @global PSyn prefs) : forall H b Γ ck x tx es vs,
    Forall (fun es =>
              Forall (fun e => forall vs,
                          wc_exp G Γ e ->
                          sem_exp_ck G H b e vs ->
                          Forall2 (sem_clock (var_history H) b) (clockof e) (map abstract_clock vs)) (snd es)) es ->
    Forall (fun es => Forall (wc_exp G Γ) (snd es)) es ->
    Forall (fun '(i, es) => Forall (eq (Con ck x (tx, i))) (clocksof es)) es ->
    Forall2Brs (sem_exp_ck G H b) es vs ->
    Forall (Forall (fun '(i, v) => sem_clock (var_history H) b (Con ck x (tx, i)) (abstract_clock v))) vs.
  Proof.
    induction es; intros * Hf Hwc Hck Hse; inv Hf; inv Hwc; inv Hck; inv Hse; auto.
    { eapply Forall_impl; [|eauto]; intros; simpl in *; subst; auto. }
    eapply IHes in H3. 2-4:eauto.
    eapply sc_exps' in H2; eauto. rewrite Forall2_map_2 in H2.
    clear - H2 H3 H6 H11. simpl in *.
    revert vs vs2 H11 H2 H3 H6. generalize (concat vs1) (clocksof es0). clear vs1 es0.
    intros vs0 cks vs1 vs2 Hf. revert cks.
    induction Hf; intros * Hck1 Hck2 Hck3; inv Hck1; inv Hck2; inv Hck3; auto.
    constructor; eauto.
  Qed.

  Lemma sc_exp {PSyn prefs} (G: @global PSyn prefs) : forall Γ H b e vs,
      wc_global G ->
      sc_vars Γ H b ->
      wc_exp G Γ e ->
      sem_exp_ck G H b e vs ->
      Forall2 (sem_clock (var_history H) b) (clockof e) (map abstract_clock vs).
  Proof.
    intros * HwcG Hinv. revert vs.
    induction e using exp_ind2; intros * Hwc Hsem;
      inv Hwc; inv Hsem; simpl.
    - (* const *)
      constructor; auto.
      rewrite H4, ac_const. now constructor.
    - (* enum *)
      constructor; auto.
      rewrite H6, ac_enum. now constructor.
    - (* var *)
      constructor; auto. inv H1.
      eapply Hinv in H7; eauto with senv.
    - (* last *)
      constructor; auto.
      eapply Hinv in H8; eauto.
    - (* unop *)
      eapply IHe in H8; eauto. rewrite H4 in H8; simpl in H8.
      rewrite <-ac_lift1; eauto.
    - (* binop *)
      eapply IHe1 in H9; eauto. rewrite H6 in H9; simpl in H9.
      rewrite <-ac_lift2; eauto.
    - (* extcall *)
      eapply sc_exps', Forall2_ignore2 in H0; eauto. simpl_Forall.
      take (liftn _ _ _) and apply ac_liftn in it.
      destruct (clocksof es); try congruence; simpl_Forall; simpl_In; simpl_Forall.
      now rewrite <-it.
    - (* fby *)
      rewrite Forall2_eq in H7. rewrite H7.
      eapply sc_exps' in H0; eauto.
      clear - H15 H0. revert H0. generalize (clocksof e0s).
      induction H15; intros ? Hsem; simpl in *; inv Hsem; constructor; auto.
      rewrite <- ac_fby1; eauto.
    - (* arrow *)
      rewrite Forall2_eq in H7. rewrite H7.
      eapply sc_exps' in H0; eauto.
      clear - H15 H0. revert H0. generalize (clocksof e0s).
      induction H15; intros ? Hsem; simpl in *; inv Hsem; constructor; auto.
      rewrite <- ac_arrow1; eauto.
    - (* when *)
      eapply sc_exps' in H0; eauto.
      erewrite Forall_eq with (l2:=clocksof es) in H0; eauto.
      clear - H15 H16 H0. revert tys H0.
      repeat setoid_rewrite Forall2_map_1.
      induction H16; intros * Hsem; simpl in *; inv Hsem; constructor; eauto.
      eapply sc_when; eauto. now apply sem_var_history.
    - (* merge *)
      simpl_Forall.
      assert (length vs0 = length tys) as Hlen1.
      { eapply Forall2Brs_length1 in H15.
        2:{ simpl_Forall. eapply sem_exp_ck_numstreams; eauto with lclocking. }
        destruct es as [|(?&?)]; try congruence. simpl in *.
        inv H15; simpl in *.
        inv H8. rewrite H10, length_clocksof_annots; auto.
      }
      assert (Hlen2:=H15). eapply Forall2Brs_length2 in Hlen2.
      eapply Forall2Brs_sc_exp1 in H15; eauto.
      eapply Forall2_forall2 in H16 as (Hlen3&Hmerge).
      eapply Forall2_forall2; split; auto; intros.
      setoid_rewrite <-Hlen3. congruence.
      eapply sc_merge in Hmerge. 1,3:eauto. eapply sem_var_history; eauto. 4,5:eauto. 3:simpl in *; congruence.
      + eapply Forall_forall in Hlen2; [|eapply nth_In; rewrite Hlen1; eauto].
        instantiate (1:=[]). instantiate (1:=[]) in Hlen2.
        destruct (nth n vs0 []), es; simpl in *; try congruence; auto.
      + eapply Forall_forall in H15; [|eapply nth_In]; eauto.
        eapply Forall_impl; [|eauto]; intros (?&?) ?; eauto.
        setoid_rewrite Hlen1; auto.
    - (* case *)
      assert (length vs0 = length tys) as Hlen1.
      { eapply Forall2Brs_length1 in H21.
        2:{ simpl_Forall. eapply sem_exp_ck_numstreams; eauto with lclocking. }
        destruct es as [|(?&?)]; try congruence. simpl in *.
        inv H21; simpl in *.
        inv H11. rewrite H15, length_clocksof_annots; auto.
      }
      rewrite Forall2_map_1, Forall2_map_2.
      eapply Forall2_forall2 in H22 as (?&Hcase).
      eapply Forall2_forall2; split; intros.
      setoid_rewrite <-H2; congruence.
      eapply ac_case in Hcase. rewrite <-Hcase.
      3:instantiate (2:=[]). all:eauto. 2:rewrite Hlen1; auto.
      eapply IHe in H20; eauto.
      rewrite H7 in H20; simpl in H20. inv H20; auto.
    - (* case *)
      assert (length vs0 = length tys) as Hlen1.
      { eapply Forall2Brs_length1 in H21.
        2:{ eapply Forall_forall; intros (?&?) ?. eapply Forall_forall; intros.
            eapply sem_exp_ck_numstreams; eauto.
            do 2 (eapply Forall_forall in H9; eauto with lclocking). }
        destruct es as [|(?&?)]; try congruence. simpl in *.
        inv H21; simpl in *.
        inv H11. rewrite H15, length_clocksof_annots; auto.
      }
      rewrite Forall2_map_1, Forall2_map_2.
      eapply Forall3_forall3 in H23 as (?&?&Hcase).
      eapply Forall2_forall2; split; intros.
      setoid_rewrite <-H3; congruence.
      eapply ac_case in Hcase. rewrite <-Hcase.
      3:instantiate (2:=[]). 4:instantiate (2:=None). 3-5:eauto; reflexivity. 2:rewrite Hlen1; auto.
      eapply IHe in H16; eauto.
      rewrite H7 in H16; simpl in H16. inv H16; auto.
    - (* app *)
      erewrite map_ext, <-map_map.
      eapply sc_outside_mask' with (es:=es); eauto. 3:intros (?&?); simpl; auto.
      + rewrite Forall2_map_1. apply Forall2_forall. split.
        * intros (?&?) ??; simpl in *; auto.
        * rewrite Forall2_map_2 in H10. eapply Forall2_length in H10. rewrite <-H10.
          rewrite map_length.
          specialize (H19 0). inv H19.
          rewrite Forall2_map_2 in H5. apply Forall2_length in H5.
          setoid_rewrite map_length in H5; auto. rewrite H3 in H8; inv H8; auto.
      + eapply sc_exps'; eauto.
  Qed.

  Corollary sc_exps {PSyn prefs} (G: @global PSyn prefs) : forall Γ H b es vss,
      wc_global G ->
      sc_vars Γ H b ->

      Forall (wc_exp G Γ) es ->
      Forall2 (sem_exp_ck G H b) es vss ->
      Forall2 (sem_clock (var_history H) b) (clocksof es) (map abstract_clock (concat vss)).
  Proof.
    intros * HwcG Hsc Hwc Hsem.
    eapply sc_exps'; eauto.
    eapply Forall_forall; intros; eauto using sc_exp.
  Qed.

  Corollary sc_exps2 {PSyn prefs} (G: @global PSyn prefs) : forall Γ H b es vss,
      wc_global G ->
      sc_vars Γ H b ->

      Forall (wc_exp G Γ) es ->
      Forall2 (fun e v => sem_exp_ck G H b e [v]) es vss ->
      Forall2 (sem_clock (var_history H) b) (clocksof es) (map abstract_clock vss).
  Proof.
    induction es; intros * HwcG Hsc Hwc Hsem; inv Hwc; inv Hsem; simpl; auto.
    eapply sc_exp in H4; eauto. simpl in H4. inv H4; inv H8; simpl.
    constructor; eauto.
  Qed.

  Fact const_stres_ac {A} : forall bs (x : A),
      abstract_clock (const_stres bs x) ≡ bs.
  Proof.
    intros *.
    apply ntheq_eqst; intros n. rewrite ac_nth. setoid_rewrite Str_nth_map.
    destruct (bs # n); auto.
  Qed.

  Fact first_of_ac {A} : forall (v : A) bs ys,
      (* slower ys bs -> *)
      (forall n, bs # n = true -> ys # n <> absent) ->
      abstract_clock (first_of v bs ys) ≡ abstract_clock ys.
  Proof.
    intros * Fast.
    apply ntheq_eqst; intros n.
    rewrite 2 ac_nth, first_of_nth.
    destruct (bs # n) eqn:Hb; auto.
    specialize (Fast _ Hb).
    destruct (ys # n); auto. congruence.
  Qed.

  Lemma sc_transitions {PSyn prefs} (G: @global PSyn prefs) Γ : forall Hi bs' trans def stres,
      wc_global G ->
      sc_vars Γ Hi bs' ->

      Forall (fun '(e, _) => wc_exp G Γ e /\ clockof e = [Cbase]) trans ->
      sem_transitions_ck G Hi bs' trans def stres ->
      abstract_clock stres ≡ bs'.
  Proof.
    induction trans; intros * HwG Hsc Hwc Hsem;
      inv Hwc; inv Hsem; destruct_conjs.
    - rewrite H0, const_stres_ac. reflexivity.
    - eapply IHtrans in H8 as Ac; eauto.
      rewrite H11, first_of_ac; eauto.
      intros * Bs'.
      eapply sc_exp in H4; eauto.
      take (clockof _ = _) and rewrite it in H4. simpl in *. simpl_Forall. inv H6.
      rewrite H1 in Ac.
      apply eqst_ntheq with (n:=n) in Ac. rewrite 2 ac_nth in Ac.
      apply bools_of_nth with (n:=n) in H5 as [(Hv&Hb)|[(Hv&Hx)|(?&Hb)]]; try congruence.
      setoid_rewrite Hv in Ac. cases; congruence.
  Qed.

  Fact wc_global_Ordered_nodes {PSyn prefs} : forall (G: @global PSyn prefs),
      wc_global G ->
      Ordered_nodes G.
  Proof.
    intros G Hwt.
    apply wl_global_Ordered_nodes; auto with lclocking.
  Qed.

  (** ** Another version of semantic inclusion *)
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
      forall ins outs, sem_node_ck G f ins outs -> sem_node_ck G' f ins outs.

    Definition global_sem_refines (G : @global PSyn1 pref1) (G' : @global PSyn2 pref2) : Prop :=
      forall f, node_sem_refines G G' f.

    Hint Constructors sem_exp_ck : core.

    Fact sem_ref_sem_exp : forall G G' H b e vs,
        global_sem_refines G G' ->
        sem_exp_ck G H b e vs ->
        sem_exp_ck G' H b e vs.
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
          specialize (Href f (map (maskv k bs) (concat ss)) (map (maskv k bs) vs)).
          eapply Href; eauto.
    Qed.

    Fact sem_ref_sem_equation : forall G G' H b eq,
        global_sem_refines G G' ->
        sem_equation_ck G H b eq ->
        sem_equation_ck G' H b eq.
    Proof.
      intros G G' H b [xs es] Href Hsem.
      inv Hsem.
      econstructor; eauto.
      eapply Forall2_impl_In; [|eauto]; intros.
      eapply sem_ref_sem_exp; eauto.
    Qed.

    Fact sem_ref_sem_transitions : forall G G' H b trans def stres,
        global_sem_refines G G' ->
        sem_transitions_ck G H b trans def stres ->
        sem_transitions_ck G' H b trans def stres.
    Proof.
      induction trans; intros * Href Hsem; inv Hsem;
        econstructor; eauto using sem_ref_sem_exp.
    Qed.

    Fact sem_ref_sem_block : forall G G' blk H b,
        global_sem_refines G G' ->
        sem_block_ck G H b blk ->
        sem_block_ck G' H b blk.
    Proof.
      induction blk using block_ind2; intros * Href Hsem;
        inv Hsem.
      - (* equation *)
        constructor; eauto using sem_ref_sem_equation.
      - (* last *)
        econstructor; eauto using sem_ref_sem_exp.
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
        inv_branch'; inv_scope'; do 2 econstructor; eauto.
        + destruct_conjs. split; simpl_Forall; eauto using sem_ref_sem_transitions.
      - (* automaton (strong) *)
        econstructor; eauto.
        + simpl_Forall. specialize (H10 k); destruct_conjs.
          inv_branch'. do 2 esplit; eauto. econstructor; eauto using sem_ref_sem_transitions.
        + simpl_Forall. specialize (H11 k); destruct_conjs.
          do 2 esplit; eauto.
          inv_branch'; inv_scope'; do 2 econstructor; eauto.
          * destruct_conjs. simpl_Forall; eauto.
      - (* local *)
        constructor. inv_scope'; econstructor; eauto.
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
      + setoid_rewrite <-sem_node_ck_cons_iff...
        eapply Hglob.
        setoid_rewrite sem_node_ck_cons_iff...
        congruence.
    Qed.

  End sem_ref.

  (** ** Execution of a node with absent inputs *)

  Lemma sem_var_instant_absent: forall H x v,
      IStr.sem_var_instant H x v ->
      IStr.sem_var_instant (FEnv.map (fun _ => absent) H) x absent.
  Proof.
    intros * Var. unfold IStr.sem_var_instant in *.
    simpl_fenv. now rewrite Var.
  Qed.
  Global Hint Resolve sem_var_instant_absent : lcsem.

  Lemma sem_clock_false: forall H ck b b',
      IStr.sem_clock b H ck b' ->
      IStr.sem_clock (fun _ => false) (fun n => FEnv.map (fun _ => absent) (H n)) ck (fun _ => false).
  Proof.
    intros * Sem n. specialize (Sem n).
    revert Sem. generalize (b n) (b' n). clear b b'.
    induction ck; intros * Sem; inv Sem; eauto using IStr.sem_clock_instant with lcsem.
  Qed.

  Section sem_node_absent.
    Context {PSyn : list decl -> block -> Prop}.
    Context {prefs : PS.t}.

    Import List.

    Lemma Forall2_sem_exp_absent: forall (f : list (Stream svalue) -> list (Stream svalue)) (G : @global PSyn prefs) H b es ss,
        Forall2 (fun e vs => sem_exp_ck G H b e (f vs)) es ss ->
        Forall2 (sem_exp_ck G H b) es (map f ss).
    Proof.
      intros * Sem. simpl_Forall; auto.
    Qed.
    Hint Resolve Forall2_sem_exp_absent : lcsem.

    Lemma sem_var_absent {K}: forall (H: @FEnv.t K _) x v,
        sem_var H x v ->
        sem_var (FEnv.map (fun _ => Streams.const absent) H) x (Streams.const absent).
    Proof.
      intros * Var. inv Var.
      econstructor; eauto. 2:reflexivity.
      simpl_fenv. now rewrite H1.
    Qed.
    Hint Resolve sem_var_absent : lcsem.

    Lemma sem_var_absent_inv {K} : forall (H: @FEnv.t K _) x v,
        sem_var (FEnv.map (fun _ => Streams.const absent) H) x v ->
        exists v', sem_var H x v' /\ v ≡ Streams.const absent.
    Proof.
      intros * Var. inv Var. simpl_fenv.
      do 2 esplit; eauto. econstructor; eauto. reflexivity.
    Qed.

    Lemma sem_clock_absent: forall H bs ck bs',
        sem_clock H bs ck bs' ->
        sem_clock (FEnv.map (fun _ => Streams.const absent) H) (Streams.const false) ck (Streams.const false).
    Proof.
      intros * Hck.
      rewrite sem_clock_equiv in *.
      apply sem_clock_false in Hck.
      intros n. specialize (Hck n); simpl in *.
      setoid_rewrite FEnv.map_map. setoid_rewrite FEnv.map_map in Hck. 2,3:auto using eq_Reflexive.
      now rewrite 2 tr_Stream_const.
    Qed.

    Lemma clocks_of_false: forall ss,
      clocks_of (map (fun _ : Stream svalue => Streams.const absent) ss) ≡ Streams.const false.
    Proof.
      intros *.
      eapply ntheq_eqst. intros n.
      rewrite clocks_of_nth, const_nth.
      induction ss; simpl; auto.
      rewrite const_nth; simpl; auto.
    Qed.

    Lemma fby_absent {A}:
      @fby A (Streams.const absent) (Streams.const absent) (Streams.const absent).
    Proof.
      cofix CoFix.
      rewrite CommonStreams.const_Cons. constructor; auto.
    Qed.

    Lemma arrow_absent:
      arrow (Streams.const absent) (Streams.const absent) (Streams.const absent).
    Proof.
      cofix CoFix.
      rewrite CommonStreams.const_Cons. constructor; auto.
    Qed.

    Fact clocked_node_absent: forall H bs vars,
        clocked_node H bs vars ->
        clocked_node (FEnv.map (fun _ => Streams.const absent) H) (Streams.const false) vars.
    Proof.
      unfold clocked_node.
      intros * (Hdom&Hsc).
      split.
      - simpl. unfold dom in *. now setoid_rewrite FEnv.map_in_iff.
      - destruct Hsc as (Hsc1&Hsc2). split; intros.
        + apply sem_var_absent_inv in H1 as (?&?&Heq).
          rewrite Heq, ac_Streams_const.
          eapply sem_clock_absent; eauto.
        + apply sem_var_absent_inv in H2 as (?&?&Heq).
          rewrite Heq, ac_Streams_const.
          eapply sem_clock_absent; eauto.
    Qed.

    Fact sem_scope_absent {A} P_blk1 (P_blk2: _ -> _ -> Prop) :
      forall locs (blks: A) Hi bs,
        sem_scope_ck P_blk1 Hi bs (Scope locs blks) ->
        (forall Hi1 Hi2,
            P_blk1 Hi1 blks ->
            FEnv.Equiv (@EqSt _) Hi2 (FEnv.map (fun _ => Streams.const absent) Hi1) ->
            P_blk2 Hi2 blks) ->
        sem_scope_ck P_blk2
                     (FEnv.map (fun _ => Streams.const absent) Hi) (Streams.const false) (Scope locs blks).
    Proof.
      intros * Hsem Hblk. inv Hsem.
      eapply Sscope with (Hi':=FEnv.map (fun _ => Streams.const absent) Hi'); eauto.
      - intros. unfold dom. setoid_rewrite FEnv.map_in_iff. auto.
      - take (sc_vars _ _ _) and destruct it as (Hsc1&Hsc2). split; intros.
        + rewrite <-FEnv.union_map in *; eauto using EqStrel_Reflexive.
          apply sem_var_absent_inv in H0 as (?&?&Heq).
          rewrite Heq, ac_Streams_const.
          eapply sem_clock_absent; eauto.
        + rewrite <-FEnv.union_map in *; eauto using EqStrel_Reflexive.
          apply sem_var_absent_inv in H2 as (?&?&Heq).
          rewrite Heq, ac_Streams_const.
          eapply sem_clock_absent; eauto.
      - take (P_blk1 _ _) and eapply Hblk in it; eauto; simpl.
        rewrite FEnv.union_map; eauto using EqStrel_Reflexive; try reflexivity.
    Qed.

    Lemma sem_block_absent:
      forall (G : @global PSyn prefs) H bs bck,
        sem_block_ck G H bs bck ->
        sem_block_ck G (FEnv.map (fun _ => Streams.const absent) H) (Streams.const false) bck.
    Proof with eauto with lcsem.
      intros * Sem.
      eapply sem_block_ck_ind2
        with (P_exp := fun H _ e vs => sem_exp_ck G (FEnv.map (fun _ => Streams.const absent) H)
                                                (Streams.const false) e (List.map (fun _ => Streams.const absent) vs))
             (P_equation := fun H _ eq => sem_equation_ck G (FEnv.map (fun _ => Streams.const absent) H) (Streams.const false) eq)
             (P_transitions := fun H _ trans def _ => sem_transitions_ck G (FEnv.map (fun _ => Streams.const absent) H)
                                                                      (Streams.const false) trans def (Streams.const absent))
             (P_block := fun H _ bck => sem_block_ck G (FEnv.map (fun _ => Streams.const absent) H) (Streams.const false) bck)
             (P_node := fun f xs ys => sem_node_ck G f (map (fun _ => Streams.const absent) xs) (map (fun _ => Streams.const absent) ys));

        simpl in *; subst; intros; eauto.
      - (* Econst *)
        simpl. constructor.
        apply ntheq_eqst. intros n.
        rewrite const_nth. symmetry.
        apply const_false, const_nth.
      - (* Eenum *)
        simpl. constructor.
        apply ntheq_eqst. intros n.
        rewrite const_nth. symmetry.
        apply enum_false, const_nth.
      - (* Evar *)
        econstructor. eapply sem_var_absent; eauto.
      - (* Elast *)
        econstructor. eapply sem_var_absent; eauto.
      - (* Eunop *)
        econstructor; eauto.
        eapply lift1_spec; intros.
        left. split; apply const_nth.
      - (* Ebinop *)
        econstructor; eauto.
        eapply lift2_spec; intros.
        left. repeat split; apply const_nth.
      - (* Eextcall *)
        econstructor; eauto.
        erewrite Forall2_map_2; eapply Forall2_impl_In; [|eauto]; intros ???? Hsem; eapply Hsem; eauto.
        eapply liftn_spec; intros.
        left. split; [apply Forall_concat|]; simpl_Forall; apply const_nth.
      - (* Efby *)
        econstructor.
        1,2:erewrite Forall2_map_2; eapply Forall2_impl_In; [|eauto]; intros ???? Hsem; eapply Hsem; eauto.
        repeat rewrite <-concat_map. rewrite Forall3_map_1, Forall3_map_2, Forall3_map_3.
        eapply Forall3_impl_In; [|eauto]. intros * _ _ _ _. eapply fby_absent.
      - (* Earrow *)
        econstructor.
        1,2:erewrite Forall2_map_2; eapply Forall2_impl_In; [|eauto]; intros ???? Hsem; eapply Hsem; eauto.
        repeat rewrite <-concat_map. rewrite Forall3_map_1, Forall3_map_2, Forall3_map_3.
        eapply Forall3_impl_In; [|eauto]. intros * _ _ _ _. apply arrow_absent.
      - (* Ewhen *)
        econstructor. 2:eapply sem_var_absent; eauto.
        erewrite Forall2_map_2; eapply Forall2_impl_In; [|eauto]; intros ???? Hsem; eapply Hsem; eauto.
        rewrite <-concat_map. simpl_Forall.
        apply when_spec. intros n.
        left. repeat split; apply const_nth.
      - (* Emerge *)
        econstructor...
        + clear H2.
          eapply Forall2Brs_map_2, Forall2Brs_impl_In; [|eauto]; intros; simpl in *; eauto.
        + rewrite Forall2_map_1, Forall2_map_2.
          eapply Forall2_impl_In; [|eauto]; intros.
          eapply merge_spec. intros n. left.
          repeat split.
          2: rewrite Forall_map; apply Forall_forall; intros (?&?) Hin.
          1-3:apply const_nth.
      - (* case *)
        econstructor...
        + clear H3.
          eapply Forall2Brs_map_2, Forall2Brs_impl_In; [|eauto]; intros; simpl in *; eauto.
        + simpl_Forall.
          eapply case_spec. intros n. left.
          repeat split.
          2:simpl_Forall.
          1-3:apply const_nth.
      - (* case (default) *)
        econstructor...
        + inv H3; inv H13. constructor; auto.
          apply SForall_forall; intros. rewrite const_nth. constructor.
        + clear H4.
          eapply Forall2Brs_map_2, Forall2Brs_impl_In; [|eauto]; intros; simpl in *; eauto.
        + rewrite Forall3_map_1, <-concat_map, 2 Forall3_map_2, Forall3_map_3. rewrite Forall3_map_2 in H8.
          eapply Forall3_impl_In; [|eauto]; intros.
          eapply case_spec. intros n. left.
          repeat split.
          2:simpl_Forall.
          1-4:apply const_nth.
      - (* Eapp *)
        econstructor.
        1,2:erewrite Forall2_map_2; eapply Forall2_impl_In; [|eauto]; intros ???? Hsem; eapply Hsem; eauto.
        eauto using bools_ofs_absent.
        + intros k. specialize (H6 k) as (?&SemN).
          repeat rewrite List.map_map in *.
          eapply sem_node_ck_morph; try eapply SemN; eauto.
          rewrite <-concat_map, List.map_map.
          1,2:eapply map_st_EqSt_Proper; try reflexivity.
          1,2:intros * Eq; symmetry; apply mask_absent.
      - (* Equation *)
        econstructor; eauto with lcsem.
        rewrite <-concat_map. simpl_Forall.
        eapply sem_var_absent; eauto.
      - (* Beq *)
        econstructor; eauto.
      - (* Blast *)
        econstructor; eauto using fby_absent, sem_var_absent.
      - (* Breset *)
        econstructor. eapply H2; eauto.
        apply bools_of_absent.
        intros k. specialize (H4 k) as (_&Hsem').
        eapply Forall_impl; [|eauto]; intros; simpl in *.
        rewrite maskb_absent.
        eapply sem_block_ck_morph; eauto. 2:reflexivity.
        rewrite mask_hist_absent, mask_hist_absent'; reflexivity.
      - (* Bswitch *)
        econstructor; eauto.
        + inv H2; inv H7.
          constructor; auto.
          eapply SForall_forall; intros. rewrite const_nth. constructor.
        + simpl_Forall. do 2 esplit; eauto.
          2:{ inv_branch'. econstructor. simpl_Forall; eauto.
              rewrite fwhenb_absent; eauto. }
          eapply when_hist_absent; eauto.
      - (* default transition *)
        constructor. apply ntheq_eqst; intros.
        setoid_rewrite Str_nth_map. rewrite 2 const_nth. auto.
      - (* transition *)
        econstructor; eauto using bools_of_absent.
        apply ntheq_eqst; intros.
        rewrite first_of_nth. rewrite 2 const_nth; auto.
      - (* Bauto (weak) *)
        econstructor; eauto using sem_clock_absent, fby_absent.
        simpl_Forall. specialize (H4 k); destruct_conjs.
        do 2 esplit; eauto.
        2:{ inv_branch'. econstructor. destruct s. eapply sem_scope_absent in H7; eauto.
            eapply sem_scope_ck_morph with (P_blk1:=fun Hi blks => Forall (sem_block_ck _ _ _) (fst blks) /\ sem_transitions_ck _ _ _ (snd blks) _ _); eauto.
            - reflexivity.
            - now rewrite fselectb_absent.
            - intros; destruct_conjs; split.
              + simpl_Forall.
                eapply sem_block_ck_morph; eauto. reflexivity.
              + eapply sem_transitions_ck_morph; eauto. 1,2:reflexivity.
            - intros; destruct_conjs; split.
              + simpl_Forall.
                eapply sem_block_ck_morph.
                symmetry; eauto. 1,2:reflexivity. now rewrite fselectb_absent.
              + eapply sem_transitions_ck_morph.
                symmetry; eauto. 1-4:reflexivity. now rewrite fselect_absent, fselectb_absent.
        }
        eapply select_hist_absent; eauto.
      - (* Bauto (strong) *)
        econstructor; eauto using sem_clock_absent, fby_absent.
        + assert (const_stres (Streams.const false) (ini, false) ≡ Streams.const absent) as Habs.
          2:rewrite Habs; apply fby_absent.
          apply ntheq_eqst; intros.
          setoid_rewrite Str_nth_map. rewrite 2 const_nth. auto.
        + simpl_Forall. specialize (H2 k); destruct_conjs.
          do 2 esplit.
          * eapply select_hist_absent; eauto.
          * inv_branch'. econstructor. now rewrite fselectb_absent, fselect_absent.
        + simpl_Forall. specialize (H3 k); destruct_conjs.
          do 2 esplit; eauto.
          2:{ inv_branch'. econstructor. destruct s. eapply sem_scope_absent in H6; eauto.
              eapply sem_scope_ck_morph with (P_blk1:=fun Hi blks => Forall (sem_block_ck _ _ _) (fst blks)); eauto.
              - reflexivity.
              - now rewrite fselectb_absent.
              - intros; destruct_conjs.
                + simpl_Forall.
                  eapply sem_block_ck_morph; eauto. reflexivity.
              - intros; destruct_conjs.
                + simpl_Forall.
                  eapply sem_block_ck_morph.
                  symmetry; eauto. 1,2:reflexivity. now rewrite fselectb_absent.
          }
          eapply select_hist_absent; eauto.
      - (* Blocal *)
        econstructor. destruct scope0.
        eapply sem_scope_absent in H0; eauto.
        + intros; destruct_conjs.
          simpl_Forall.
          eapply sem_block_ck_morph.
          symmetry; eauto. 1,2:reflexivity. auto.
      - (* Node *)
        econstructor; eauto.
        1,2:(rewrite Forall2_map_2; eapply Forall2_impl_In; [|eauto];
             intros; eapply sem_var_absent; simpl in *; eauto).
        + rewrite clocks_of_false; auto.
        + rewrite clocks_of_false.
          eapply clocked_node_absent in H6; eauto.
    Qed.

  End sem_node_absent.

  (** Additional properties *)

  Lemma sem_clock_when_const : forall H bs bs' bs'' cs ck id x tx c,
      sem_clock H bs ck bs' ->
      sem_clock H bs (Con ck id (tx, x)) bs'' ->
      sem_var H id cs ->
      when x (const bs' c) cs (const bs'' c).
  Proof.
    intros * Hcl1 Hcl2 Hvar.
    inv Hcl2. eapply sem_clock_det in Hcl1; eauto.
    eapply sem_var_det in Hvar; eauto. rewrite <-Hcl1. rewrite Hvar in H11, H10.
    rewrite <-H10, when_spec. intros n. repeat rewrite const_nth'. repeat rewrite ac_nth.
    apply enums_of_nth with (n:=n) in H11 as [(Hc&Hx)|[(Hc&Hx)|(?&Hc&?&Hx)]];
      setoid_rewrite Hc; setoid_rewrite Hx; eauto.
    - right; right. eexists. intuition; eauto.
    - right; left. do 2 eexists. intuition; eauto.
  Qed.

  Lemma sem_clock_when_enum : forall H bs bs' bs'' cs ck id x tx c,
      sem_clock H bs ck bs' ->
      sem_clock H bs (Con ck id (tx, x)) bs'' ->
      sem_var H id cs ->
      when x (enum bs' c) cs (enum bs'' c).
  Proof.
    intros * Hcl1 Hcl2 Hvar.
    inv Hcl2. eapply sem_clock_det in Hcl1; eauto.
    eapply sem_var_det in Hvar; eauto. rewrite <-Hcl1. rewrite Hvar in H11, H10.
    rewrite <-H10, when_spec. intros n. repeat rewrite enum_nth'. repeat rewrite ac_nth.
    apply enums_of_nth with (n:=n) in H11 as [(Hc&Hx)|[(Hc&Hx)|(?&Hc&?&Hx)]];
      setoid_rewrite Hc; setoid_rewrite Hx; eauto.
    - right; right. eexists. intuition; eauto.
    - right; left. do 2 eexists. intuition; eauto.
  Qed.

End LCLOCKEDSEMANTICS.

Module LClockedSemanticsFun
       (Ids : IDS)
       (Op : OPERATORS)
       (OpAux : OPERATORS_AUX Ids Op)
       (Cks : CLOCKS Ids Op OpAux)
       (Senv  : STATICENV Ids Op OpAux Cks)
       (Syn : LSYNTAX Ids Op OpAux Cks Senv)
       (Clo : LCLOCKING Ids Op OpAux Cks Senv Syn)
       (Lord : LORDERED Ids Op OpAux Cks Senv Syn)
       (CStr : COINDSTREAMS Ids Op OpAux Cks)
       (Sem : LSEMANTICS Ids Op OpAux Cks Senv Syn Lord CStr)
<: LCLOCKEDSEMANTICS Ids Op OpAux Cks Senv Syn Clo Lord CStr Sem.
  Include LCLOCKEDSEMANTICS Ids Op OpAux Cks Senv Syn Clo Lord CStr Sem.
End LClockedSemanticsFun.
